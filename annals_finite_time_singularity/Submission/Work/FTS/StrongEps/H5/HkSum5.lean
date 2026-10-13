/-
# `H5/HkSum5` — the level-`5` finite-sum closure of `HkMem`

The level-four version `ClassCRHS.HkSumOpenClosure` (`Submission/Work/FTS/StrongEps/ClassCRHS/HkSumOpenClosure.lean`)
transfers `HkMem α 4`-honesty and an `ℋ⁴`-norm bound from a finite sum `∑_{k<n} F k` to any
function agreeing with it on the open quadrant, at the price of the factor `√(2^n)`.  This is the
step that carries the twenty `NBlk` pieces back to `N α (F_tot α w) (Φs + Φg)`, and it is needed at
level `5` for the `ℋ⁵`-chapter.  The proof is the same: `HkMem_of_majorant` is level-general, the
pointwise domination is `GalFields.RHS.HkIntegrand_finset_sum_le` (level-general), and the norm
bound is `GalFields.RHS.HkNorm_finset_sum_le` together with `HkSq_congr_open`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-`5` finite-sum closure**: a function agreeing on the open quadrant with the sum
`∑_{k<n} F k` of `ℋ⁵`-honest, `SmoothOpen` summands is `ℋ⁵`-honest, with the norm bound
`Xn5 α g ≤ √(2^n) ∑_k Xn5 α (F k)`. -/
theorem HkSumOpenClosure5 {α : ℝ} (hα : 0 < α) {n : ℕ} {g : Fn}
    {F : ℕ → Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5 g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsm : ∀ k ∈ Finset.range n, Work.FTS.EllipticEst.SmoothOpen (F k))
    (hm : ∀ k ∈ Finset.range n, Work.Spaces.HkMem α 5 (F k))
    (hag : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      g z θ = ∑ k ∈ Finset.range n, F k z θ) :
    Work.Spaces.HkMem α 5 g ∧
      Work.Spaces.HkNorm α 5 g ≤ Real.sqrt ((2 : ℝ) ^ n) * ∑ k ∈ Finset.range n,
        Work.Spaces.HkNorm α 5 (F k) := by
  classical
  set M : ℝ → ℝ → ℝ := fun z θ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
      Work.Spaces.HkIntegrand α 5 (F k) z θ with hM
  have hMnn : ∀ z θ : ℝ, 0 ≤ M z θ := by
    intro z θ
    show 0 ≤ (2 : ℝ) ^ n * ∑ k ∈ Finset.range n, Work.Spaces.HkIntegrand α 5 (F k) z θ
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => Work.Spaces.HkIntegrand_nonneg α 5 (F k) z θ)
  -- ### membership
  have hmem : Work.Spaces.HkMem α 5 g := by
    refine Work.FTS.LocData.HkMem_of_majorant (f := g) (M := M) α 5 hcont ?_ ?_ ?_
    · intro z hz
      show IntegrableOn (fun θ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
        Work.Spaces.HkIntegrand α 5 (F k) z θ) Work.Spaces.Iθ
      have hsum : Integrable (fun θ : ℝ => ∑ k ∈ Finset.range n,
          Work.Spaces.HkIntegrand α 5 (F k) z θ) (volume.restrict Work.Spaces.Iθ) :=
        integrable_finsetSum (Finset.range n) (fun k hk => (hm k hk).1 z hz)
      exact hsum.const_mul _
    · show IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
        Work.Spaces.HkIntegrand α 5 (F k) z θ) Work.Spaces.Iz
      have hsum : Integrable (fun z : ℝ => ∑ k ∈ Finset.range n,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 (F k) z θ)
          (volume.restrict Work.Spaces.Iz) :=
        integrable_finsetSum (Finset.range n) (fun k hk => (hm k hk).2)
      have hbase : Integrable (fun z : ℝ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 (F k) z θ)
          (volume.restrict Work.Spaces.Iz) := hsum.const_mul _
      refine hbase.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
      intro k hk
      exact (hm k hk).1 z hz
    · intro z hz θ hθ
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
      · subst hz0
        rw [Work.FTS.LocData.HkIntegrand_zero_fst]
        exact hMnn 0 θ
      · by_cases hs : Real.sin (2 * θ) = 0
        · rw [Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α 5 g hα hs]
          exact hMnn z θ
        · have hθpos : 0 < θ := by
            rcases lt_or_eq_of_le (show (0 : ℝ) ≤ θ from hθ.1) with h | h
            · exact h
            · exact absurd (by rw [← h, mul_zero, Real.sin_zero]) hs
          have hθlt : θ < Real.pi / 2 := by
            rcases lt_or_eq_of_le hθ.2 with h | h
            · exact h
            · exact absurd (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hs
          have hgeq : Work.Spaces.HkIntegrand α 5 g z θ
              = Work.Spaces.HkIntegrand α 5
                  (fun z θ => ∑ k ∈ Finset.range n, F k z θ) z θ :=
            Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := 5)
              (fun z θ hz hθ hlt => hag z θ hz hθ hlt) z θ hzpos hθpos hθlt
          rw [hgeq]
          have hle := Work.FTS.GalFields.RHS.HkIntegrand_finset_sum_le α 5 hα
            (Finset.range n) hsm z hz θ hθ
          simp only [Finset.card_range] at hle
          exact hle
  refine ⟨hmem, ?_⟩
  -- ### the norm bound
  have hXn : Work.Spaces.HkNorm α 5 g
      = Work.Spaces.HkNorm α 5 (fun z θ => ∑ k ∈ Finset.range n, F k z θ) := by
    show Work.Spaces.HkNorm α 5 g = _
    rw [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 5 hag,
      Work.Spaces.HkNorm]
  rw [hXn]
  simpa only [Finset.card_range] using
    Work.FTS.GalFields.RHS.HkNorm_finset_sum_le α 5 hα (Finset.range n) hsm hm

end Work.FTS.StrongEps.H5
