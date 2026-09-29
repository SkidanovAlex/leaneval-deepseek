import Mathlib
import Submission.Work.IntLib.AddSub.Defs
import Submission.Work.IntLib.AddSub.EvKit

/-!
# `IntLib` / add–sub: which stacks each word touches

`cmdTouches` bounds for the programs of `AddSub.Defs`, used with `Ev.frame` to transport
facts about untouched stacks.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace AddSub

open HvdH

theorem cmdTouches_asw_drain (a b : Stk) (T : Glyph) (r rF : Reg) :
    cmdTouches (asw_drain a b T r rF) ⊆ {a, b} := by
  intro j hj
  simp only [asw_drain, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_stripLoop (out : Stk) : cmdTouches (asw_stripLoop out) ⊆ {out} := by
  intro j hj
  simp only [asw_stripLoop, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_addLoop (a b out : Stk) :
    cmdTouches (asw_addLoop a b out) ⊆ {a, b, out} := by
  intro j hj
  simp only [asw_addLoop, asw_addBody, asw_addTree, asw_leaf, seqs, cmdTouches,
    Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_subLoop (a b o1 o2 : Stk) :
    cmdTouches (asw_subLoop a b o1 o2) ⊆ {a, b, o1, o2} := by
  intro j hj
  simp only [asw_subLoop, asw_subBody, asw_subTree, asw_leaf, seqs, cmdTouches,
    Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_finish (sg out : Stk) :
    cmdTouches (asw_finish sg out) ⊆ {sg, out, 0} := by
  intro j hj
  simp only [asw_finish, asw_stripLoop, asw_drain, seqs, cmdTouches, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_clearAt (k : Stk) (M : Glyph) (r rF : Reg) :
    cmdTouches (asw_clearAt k M r rF) ⊆ {k} := by
  intro j hj
  simp only [asw_clearAt, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_flipCmd : cmdTouches asw_flipCmd ⊆ (∅ : Finset Stk) := by
  intro j hj
  simp only [asw_flipCmd, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_same : cmdTouches asw_same ⊆ ({0, sA, sB, sO1, sSgA, sSgB} : Finset Stk) := by
  intro j hj
  simp only [asw_same, asw_addLoop, asw_addBody, asw_addTree, asw_leaf, asw_finish,
    asw_stripLoop, asw_drain, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_diff :
    cmdTouches asw_diff ⊆ ({0, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) := by
  intro j hj
  simp only [asw_diff, asw_subLoop, asw_subBody, asw_subTree, asw_leaf, asw_finish,
    asw_stripLoop, asw_drain, asw_clearAt, seqs, cmdTouches, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_dispatch :
    cmdTouches asw_dispatch ⊆ ({0, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) := by
  intro j hj
  simp only [asw_dispatch, asw_same, asw_addLoop, asw_addBody, asw_addTree, asw_leaf, asw_finish,
    asw_stripLoop, asw_drain, asw_diff, asw_subLoop, asw_subBody, asw_subTree, asw_clearAt, seqs,
    cmdTouches, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty]
    at hj ⊢
  tauto

theorem cmdTouches_asw_cleanup :
    cmdTouches asw_cleanup ⊆ ({sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) := by
  intro j hj
  simp only [asw_cleanup, asw_clear, asw_clearAt, seqs, cmdTouches, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_setup (fp : Cmd) :
    cmdTouches (asw_setup fp) ⊆
      (({0, sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) ∪ cmdTouches fp) := by
  intro j hj
  simp only [asw_setup, asw_drain, seqs, cmdTouches, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert, Finset.notMem_empty] at hj ⊢
  tauto

theorem cmdTouches_asw_prog (flip : Bool) :
    cmdTouches (asw_prog flip) ⊆ ({0, sBuf, sA, sB, sO1, sO2, sSgA, sSgB} : Finset Stk) := by
  cases flip
  · show cmdTouches (seqs [asw_setup .skip, asw_dispatch, asw_cleanup]) ⊆ _
    intro j hj
    simp only [asw_setup, asw_dispatch, asw_same, asw_diff, asw_addLoop, asw_addBody, asw_addTree,
      asw_leaf, asw_finish, asw_stripLoop, asw_subLoop, asw_subBody, asw_subTree, asw_cleanup,
      asw_clear, asw_clearAt, asw_drain, seqs, cmdTouches, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty] at hj ⊢
    tauto
  · show cmdTouches (seqs [asw_setup asw_flipCmd, asw_dispatch, asw_cleanup]) ⊆ _
    intro j hj
    simp only [asw_setup, asw_flipCmd, asw_dispatch, asw_same, asw_diff, asw_addLoop, asw_addBody,
      asw_addTree, asw_leaf, asw_finish, asw_stripLoop, asw_subLoop, asw_subBody, asw_subTree,
      asw_cleanup, asw_clear, asw_clearAt, asw_drain, seqs, cmdTouches, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty] at hj ⊢
    tauto

end AddSub
end Work.IntLib
