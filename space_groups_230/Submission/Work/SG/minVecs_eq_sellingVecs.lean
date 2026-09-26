import Mathlib
import Submission.Work.SG.SellingDefs
import Submission.Work.SG.minVecDefs
import Submission.Work.SG.norm_formula
import Submission.Work.SG.parity_sq_le
import Submission.Work.SG.parity_sq_eq_iff

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped Matrix BigOperators

/-! ### The analytic core -/

/-- The parity lower bound is a lower bound for the whole mod-2 class. -/
theorem Lb_le_qf {Q W : IMat} (hsym : Q.transpose = Q) (hob : ObSbase Q W)
    {y y' : IVec} (h : modEq y y') : Lb Q W y ≤ qf Q (W.mulVec y') := by
  rw [norm_formula Q W hsym y']
  simp only [Lb, parity]
  exact Finset.sum_le_sum fun p hp => by
    have hlt : p.1 < p.2 := mem_pairSet.mp hp
    have hq : 0 ≤ sQ Q W p.1 p.2 := sQ_nonneg hob (ne_of_lt hlt)
    exact mul_le_mul_of_nonneg_left
      (parity_sq_le _ _ _ _ (modEq_cons0 h p.1) (modEq_cons0 h p.2)) hq

/-- The lower bound is attained at the parity vector. -/
theorem Lb_attain {Q W : IMat} (hsym : Q.transpose = Q) (y : IVec) :
    qf Q (W.mulVec (fun i => y i % 2)) = Lb Q W y := by
  rw [norm_formula Q W hsym (fun i => y i % 2)]
  simp only [Lb, parity]
  exact Finset.sum_congr rfl fun p _ => by
    rw [parity_cons0_mod y p.1, parity_cons0_mod y p.2]
    congr 1
    exact emod_two_sub_sq (cons0 y p.1) (cons0 y p.2)

/-- Equality in the parity lower bound is exactly the Selling condition on the support graph. -/
theorem qf_eq_Lb_iff {Q W : IMat} (hsym : Q.transpose = Q) (hob : ObSbase Q W) (y : IVec) :
    qf Q (W.mulVec y) = Lb Q W y ↔
      ∀ p : Fin 4 × Fin 4, p.1 < p.2 → bf Q (sb W p.1) (sb W p.2) < 0 →
        |cons0 y p.1 - cons0 y p.2| ≤ 1 := by
  have hterm : ∀ p : Fin 4 × Fin 4, p ∈ pairSet →
      sQ Q W p.1 p.2 * (if parity y p.1 = parity y p.2 then 0 else 1)
        ≤ sQ Q W p.1 p.2 * (cons0 y p.1 - cons0 y p.2) ^ 2 := by
    intro p hp
    have hlt : p.1 < p.2 := mem_pairSet.mp hp
    refine mul_le_mul_of_nonneg_left ?_ (sQ_nonneg hob (ne_of_lt hlt))
    exact parity_sq_le (cons0 y p.1) (cons0 y p.2) (cons0 y p.1) (cons0 y p.2)
      (by simp) (by simp)
  constructor
  · intro hEq p hlt hbf
    rw [norm_formula Q W hsym y] at hEq
    unfold Lb at hEq
    have hpt := ((Finset.sum_eq_sum_iff_of_le hterm).mp hEq.symm) p (mem_pairSet.mpr hlt)
    have hpos : 0 < sQ Q W p.1 p.2 := sQ_pos_iff.mpr hbf
    have hcancel : (if parity y p.1 = parity y p.2 then 0 else 1)
        = (cons0 y p.1 - cons0 y p.2) ^ 2 := mul_left_cancel₀ (ne_of_gt hpos) hpt
    exact (parity_sq_eq_iff (cons0 y p.1) (cons0 y p.2)).mp hcancel.symm
  · intro hsel
    rw [norm_formula Q W hsym y]
    simp only [Lb, parity]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hlt : p.1 < p.2 := mem_pairSet.mp hp
    have hq : 0 ≤ sQ Q W p.1 p.2 := sQ_nonneg hob (ne_of_lt hlt)
    rcases lt_or_eq_of_le hq with hpos | hzero
    · have hbf : bf Q (sb W p.1) (sb W p.2) < 0 := sQ_pos_iff.mp hpos
      congr 1
      exact (parity_sq_eq_iff (cons0 y p.1) (cons0 y p.2)).mpr (hsel p hlt hbf)
    · rw [← hzero]; ring

/-! ### The target theorem -/

/-- **Coset-minimal vectors of an obtuse superbase.** For a symmetric form `Q` whose superbase in
the basis `W` is obtuse, the vectors `≠ 0` that minimise `v ↦ vᵀ(WᵀQW)v` in their class mod
`2ℤ³` are exactly the vectors `sellingVecs (suppGraph Q W)` of the support graph.

Route: put `q m n := - bf Q (sb W m) (sb W n) ≥ 0` (`hob`), so that by the *norm formula*
`qf Q (W.mulVec y) = ∑_{m<n} q m n * (x m - x n)^2` where `x = cons0 y`
(use `qf_conj`, `mulVec_eq_linComb4`, `bf_linComb4`, `sb_sum_zero`, `bf_comm`).
For the same class mod 2 (same parities `ε m = x m % 2`) each term satisfies
`q m n * (x' m - x' n)^2 ≥ q m n * (if ε m = ε n then 0 else 1)`, and the lower bound is attained
at the parity vector `cons0 (fun i => (cons0 y i.succ) % 2)`.  Hence `y ∈ minVecs ...` iff equality
holds in the lower bound, iff every pair `m < n` with `q m n > 0` (i.e. every edge of
`suppGraph Q W`, see `mem_suppGraph`) has `|x m - x n| ≤ 1` — which is `sellingVecs`. -/
theorem minVecs_eq_sellingVecs (Q W : IMat) (hsym : Q.transpose = Q) (hob : ObSbase Q W) :
    minVecs (W.transpose * Q * W) = sellingVecs (suppGraph Q W) := by
  ext y
  simp only [minVecs, Set.mem_ofPred_eq, sellingVecs]
  constructor
  · rintro ⟨hne, hmin⟩
    have hLb : qf (W.transpose * Q * W) y = Lb Q W y := by
      refine le_antisymm ?_ ?_
      · have hy'' := hmin (fun i => y i % 2) (modEq_emod_two y)
        simp only [qf_conj] at hy''
        rw [Lb_attain hsym y] at hy''
        simpa only [qf_conj] using hy''
      · rw [qf_conj]
        exact Lb_le_qf hsym hob (modEq_refl y)
    refine ⟨hne, fun e he => ?_⟩
    have hcond := (qf_eq_Lb_iff hsym hob y).mp (by rw [← qf_conj]; exact hLb)
    rw [mem_suppGraph] at he
    have := hcond e he.1 he.2
    rwa [cons0_eq_cons] at this
  · rintro ⟨hne, hsel⟩
    refine ⟨hne, fun y' hy' => ?_⟩
    have hcond : ∀ p : Fin 4 × Fin 4, p.1 < p.2 →
        bf Q (sb W p.1) (sb W p.2) < 0 → |cons0 y p.1 - cons0 y p.2| ≤ 1 := by
      intro p hlt hbf
      have hmem : p ∈ suppGraph Q W := mem_suppGraph.mpr ⟨hlt, hbf⟩
      have hh := hsel p hmem
      rw [← cons0_eq_cons] at hh
      exact hh
    rw [qf_conj, (qf_eq_Lb_iff hsym hob y).mpr hcond, qf_conj]
    exact Lb_le_qf hsym hob hy'

end Work.SG
