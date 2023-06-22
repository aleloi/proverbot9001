from __future__ import annotations
from typing import List, Optional, Iterable
from dataclasses import dataclass, field
from typeguard import typechecked
import copy

import parse_serapi.parse as psp
from parse_serapi.ast import *

import coq_serapy as serapi_instance

DEBUG = False

@typechecked
@dataclass
class Proof:
    goal: str = ''                                    # what are we to prove?
    tac:  Optional[Node] = None
    tac_str: str = ''
    kids: List[Proof]  = field(default_factory=list)  # proofs of kids
    par:  Optional[Proof] = None                      # backlink to parent.
    n_goals: int = 0              # num goals generated after
                                  # executing 'tac'. For keeping track
                                  # of what happens after '}'.

    # run AFTER 'coq.run_stmt('{')' ?
    def go_down(self, coq: serapi_instance.SerapiInstance):
        #breakpoint()
        if DEBUG: print(f"[proof] Going down, tac was={self.tac}")

        # breakpoint()

        #assert self.goal != ''
        #assert self.tac != ''
        #goals = [o.goal for o in coq.proof_context.fg_goals]

        coq.run_stmt('{')
        #assert coq.goals == goals[0]  - not true for second kid

        self.kids.append(Proof(goal=coq.goals, par=self))
        return self.kids[-1]
        #node = node.kids[-1]

    # Note: we never put 'Qed' in the proof tree. There should be a
    # special case for `self.n_goals == 0` if we do.
    def run_stmt(self, command, coq):
        # breakpoint()
        if DEBUG: print(f"[proof] Running command {command}")
        assert command.strip() not in ['Defined.', 'Qed.']
        if self.tac != None:
            breakpoint()
        # assert self.goal == ''
        command = command.rstrip(" \t\n\r").lstrip(" \t\n\r")
        #command_ast
        coq.run_stmt(command)
        raw_ast = coq.get_AST()
        node = psp.SmallTreeParser.parse_from_raw_ast(
            command, raw_ast)
        self.tac = node
        self.tac_str = command

        # where do we record the new goal?
        self.n_goals = coq.count_fg_goals()

        if self.n_goals == 1:
            self.kids.append(Proof(goal=coq.goals, par=self))
            if DEBUG: print(f"[proof] Exactly one new kid with goal {coq.goals}")
            return self.kids[-1]
        else:
            if DEBUG:  print(f"[proof] {coq.count_fg_goals()} new kids")
            return self


    def go_up(self, coq: serapi_instance.SerapiInstance):
        #breakpoint()
        if DEBUG: print(f"[proof] going up, last tac was: {self.tac}")
        assert coq.goals == ''
        assert coq.proof_context.fg_goals == []
        coq.run_stmt('}')

        pos = self
        while pos.n_goals <= 1:
                assert pos.par != None
                pos = pos.par
        return pos

    def pretty_print(self, indent=' '):
        mx_len = 20
        goal_long = '...' if len(self.goal) > mx_len else ''
        print(f"{indent}{self.tac}.    (* {self.goal[:mx_len]}{goal_long}  *)")
        if len(self.kids) == 1:
            self.kids[0].pretty_print(indent)
        elif len(self.kids) > 1:
            lb, rb = '{', '}'

            for kid in self.kids:
                print(f"{indent}{lb}")
                kid.pretty_print(indent + "  ")
                print(f"{indent}{rb}")
        if self.par == None:
            print('Qed.')

    def pretty_print2(self):
        for x in self.yield_stmts():
            print(x)

    @staticmethod
    def transform_s(root: Proof, coq: serapi_instance.SerapiInstance,
                    verbose: int = 0) -> Proof:
        """
        Goes back and forth though the proof?

        Returns the final thing?
        """
        command_stack = []
        def run_stmt(stmt: str):
            command_stack.append(stmt)
            coq.run_stmt(stmt)

        # not sure what I need yet.
        # def cancel_stmt?

        def transform(node: Proof) -> Tuple[Proof, bool]:
            """
            Returns new node plus whether something changed?
            """
            @typechecked
            def transform_kids(kids: List[Proof]) -> bool:
                changed = False
                for i, kid in enumerate(kids):
                    run_stmt("{")
                    kid, change = transform(kid)
                    changed |= change
                    kids[i] = kid
                    run_stmt("}")
                return changed

            assert coq.goals == node.goal, f"coq says '{coq.goals}', we think '{node.goal}'"
            match node:

                # last by
                case Proof(tac=LastBy(tac=A, by=B), kids=kids):
                    res = Proof(tac=A, tac_str=A.get_coq_str(), par=node.par,
                                goal=node.goal, kids=kids)
                    for kid in kids:
                        kid.par = res
                    run_stmt(res.tac_str)
                    transform_kids(kids)
                    run_stmt("{")
                    last_kid = Proof.generate_proof(B, coq, verbose)
                    last_kid.par = res
                    run_stmt("}")
                    kids.append(last_kid)
                    return (res, True)

                case Proof(tac=LastFirst(tac=A), kids=kids):
                    res = Proof(tac=A, tac_str=A.get_coq_str(), goal=node.goal,
                                par=node.par, kids=[kids[-1]] + kids[:-1])
                    for kid in res.kids:
                        kid.par = res
                    run_stmt(res.tac_str)
                    transform_kids(res.kids)
                    return (res, True)

                case Proof(tac=FirstBy(tac=A, by=B), kids=kids):
                    res = Proof(tac=A, tac_str=A.get_coq_str(), par=node.par,
                                kids=kids, goal=node.goal)

                    run_stmt(res.tac_str)
                    run_stmt("{")
                    first_kid = Proof.generate_proof(B, coq, verbose)
                    first_kid.par = res
                    run_stmt("}")

                    for kid in kids:
                        kid.par = res
                    transform_kids(kids)
                    res.kids = [first_kid] + res.kids
                    return (res, True)

                case Proof(tac=Then(t1=A, t2=B), kids=kids):
                    # breakpoint()
                    proof_map = {kid.goal: kid for kid in kids}
                    A_node = Proof(tac=A, tac_str=A.get_coq_str(), goal=node.goal,
                                par=node.par)
                    # goals_before = coq.count_fg_goals()
                    run_stmt("{")  # A_node
                    run_stmt(A.get_coq_str())
                    kids = A_node.kids

                    # I think fg goals goes down to 0 when node.goal is proven.
                    while coq.count_fg_goals() > 0:
                        run_stmt("{")  # kid of A_node
                        # Possibly deep copy problems here? We get
                        # several refs to 'B'
                        kids.append(B_node := Proof(tac=copy.deepcopy(B),
                                                 tac_str=B.get_coq_str(),
                                                 goal=coq.goals, par=A_node))
                        run_stmt(B.get_coq_str())
                        while coq.count_fg_goals() > 0:
                            assert coq.goals in proof_map
                            # Check that they come in order? And that
                            # there is one of each?
                            B_kid = copy.deepcopy(proof_map[coq.goals])
                            B_kid.par = B_node
                            B_node.kids.append(B_kid)
                            run_stmt("{")  # Kid of B_node
                            for cmd in B_kid.yield_stmts():
                                run_stmt(cmd)
                            run_stmt("}")  # End of B_node kid
                        run_stmt("}")  # End of A_node kid
                    run_stmt("}")  # End of A_node
                    #breakpoint()
                    return A_node, True

                case Proof(tac=Rewrite(args=[arg1, *rest]), kids=kids,
                           goal=goal) if len(rest) > 0:
                    rw_then = Rewrite(args=[arg1], coq=f"rewrite {arg1}")
                    for rw_arg in rest:
                        rw_arg_node = Rewrite(args=[rw_arg],
                                              coq=f"rewrite {rw_arg}")
                        rw_then = Then(
                            t1=rw_then,
                            t2=rw_arg_node,
                            coq=f"({rw_then.coq}) ; ({rw_arg_node.coq})")
                    res = Proof(tac=rw_then, kids=kids,
                                tac_str=rw_then.get_coq_str(),
                                goal=goal, par=node.par
                                )
                    for kid in kids:
                        kid.par = res

                    # Just assuming that the (;)-rewrite will have the
                    # same kids in the same order.
                    run_stmt(res.tac_str)
                    transform_kids(kids)
                    #breakpoint()
                    return res, True


                # Wasn't so simple: should make it into `Thens` based
                # on the []-pattern?
                #
                # case Proof(tac=Intro(tac=before, items=items)) if before != Node('move'):
                #     _, after = node.tac.coq.split('=>')

                #     move_after_coq = f'move => {after}'
                #     new_tac = Then(t1 = before,
                #                    t2 = Intro(tac=Node('move'), items=items,
                #                               coq=move_after_coq),
                #                    coq = f'({before.coq}) ; {move_after_coq} ')
                #     print(f"[proof, intro] made '{node.tac}' into '{new_tac}'.")
                #     print(f"[proof, intro] made '{node.tac.coq}' into '{new_tac.coq}'.")
                #     print(f"[proof, intro] made '{node.tac_str}' into '{new_tac.get_coq_str()}'")
                #     node.tac = new_tac
                #     node.tac_str = new_tac.get_coq_str()

                #     run_stmt(node.tac_str)
                #     transform_kids(node.kids)
                #     return node, True

                # Default:
                case Proof(tac=A, kids=kids, tac_str=tac_str):
                    # breakpoint()
                    run_stmt(tac_str)
                    changed = transform_kids(kids)
                    return node, changed #transform_kids(kids)

        while True:
            root, changed = transform(root)
            run_stmt("Qed.")
            print("Changed proof to")
            for stm in root.yield_stmts():
                print(stm)
            print()
            if not changed:
                break
            while command_stack:
                # revert to start
                command_stack.pop()
                coq.cancel_last()
        return root



    # def transform(self, coq: serapi_instance.SerapiInstance, verbose: int = 0):
    #     """Does SSR-simplifying transformation of itself and its subtree.
    #     Pre: coq state is just before this tree.
    #     Post: coq has proven the goal of this tree; coq state is immediately
    #          after this subtree
    #     """
    #     #breakpoint()
    #     def transform_kids(kids):
    #         for kid in kids:
    #             for i, kid in enumerate(kids):
    #                 coq.run_stmt("{")
    #                 res.kids[i] = kid.transform(coq, verbose)
    #                 coq.run_stmt("}")

    #     assert coq.goals == self.goal
    #     match self:
    #         # case Proof(tac=Rewrite(args=rargs), kids=kids):




    #         # Stupid inheritance... Check that this is a terminal Node
    #         case Proof(tac=Node(), kids=kids, tac_str=tac_str):
    #             #breakpoint()
    #             coq.run_stmt(tac_str)
    #             for i, kid in enumerate(kids):
    #                 kids[i] = kid.transform(coq, verbose)
    #             return self
    #         case _: assert False, "not implemented"

    #     # Also run the `Qed.` to close the proof.
    #     if self.par is None:
    #         coq.run_stmt('Qed.')

    def yield_stmts(self, indent="  ") -> Iterable[str]:
        yield indent + self.tac_str
        if len(self.kids) == 1:
            yield from self.kids[0].yield_stmts(indent)
        else:
            for kid in self.kids:
                yield indent + "{"
                yield from kid.yield_stmts(indent + "  ")
                yield indent + "}"
        if self.par == None:
            yield 'Qed.'

    # Right abstraction? re-do?
    @staticmethod
    def generate_proof(tac: Node, coq: serapi_instance.SerapiInstance,
                       verbose: int = 0) -> Proof:
        """
        Generates a short Proof tree from simple tactic that is assumed to
        close a goal.
        """
        #goal: str = coq.goals
        res = Proof(goal=coq.goals)
        match tac:
            case Then(): assert False
            case Thens(): assert False
            case LastFirst(): assert False
            case LastBy(): assert False
            case FirstBy(): assert False
            case By(tac=by_tac):
                coq.run_stmt("{")
                res = Proof.generate_proof(by_tac, coq, verbose)
                assert coq.proof_context.fg_goals == []
                coq.run_stmt("}")
                return res
            case _:
                tac_str = tac.get_coq_str()
                coq.run_stmt(tac_str)
                res.tac_str = tac_str
                res.tac = tac
                return res
