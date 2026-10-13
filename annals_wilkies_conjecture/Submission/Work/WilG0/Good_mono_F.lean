import Mathlib
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.API

namespace Work.WilG0

/-! `Good S F d` is a `Prop` defined by recursion on the shape `s`.  Every clause of the
recursion is monotone in the format `F`: the polynomial clause is `True`, the `mem` clause is
membership in `S.Ω F D m`, monotone in `F` by `SOMin.mono_F`, and the logical clauses
(`neg`, `and`, `or`, `ex`) are monotone because their subterms are.  So the whole predicate is
monotone in `F`, which is `Good_mono_F`. -/

theorem Good_mono_F {S : WilkiesDesign.SOMin} {n : ℕ} (s : WilkiesDesign.CG.OShape n) {F F' : ℕ} (h : F ≤ F')
    {d : s.Data} (hd : s.Good S F d) : s.Good S F' d := by
  induction s with
  | poly n => exact trivial
  | mem n m ι => exact Omega_mono_F h hd
  | neg s ih => exact ih hd
  | and s t ihs iht => exact ⟨ihs hd.1, iht hd.2⟩
  | or s t ihs iht => exact ⟨ihs hd.1, iht hd.2⟩
  | ex s ih => exact ih hd

end Work.WilG0
