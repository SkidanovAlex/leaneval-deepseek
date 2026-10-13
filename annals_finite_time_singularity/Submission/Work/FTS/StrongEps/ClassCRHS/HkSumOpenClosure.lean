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

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

/-! A finite sum `∑_{k<n} F k` agreeing with `g` on the open quadrant transfers both
`ℋ⁴`-membership and the `ℋ⁴`-norm bound to `g`, at the price of the factor `√(2^n)` of
`Work.FTS.GalFields.RHS.HkNorm_finset_sum_le`.  Please put the declaration in namespace
`Work.FTS.StrongEps.ClassCRHS` (file
`Submission/Work/FTS/StrongEps/ClassCRHS/HkSumOpenClosure.lean`), as the sibling
`StarAtomsFK` does, so it is usable as
`Work.FTS.StrongEps.ClassCRHS.HkSumOpenClosure`.

Route (all tools already on disk): `HkMem α 4 g` follows from
`Work.FTS.LocData.HkMem_of_majorant α 4` applied to `g` with the majorant
`M z θ = (2:ℝ)^n * ∑ k ∈ Finset.range n, HkIntegrand α 4 (F k) z θ` — slices and `z`-integral
integrable from `hm`; domination at interior points from `hag` +
`Work.FTS.EllipticEst.HkIntegrand_congr` + `HkIntegrand_finset_sum_le`, at `z = 0` from
`Work.FTS.LocData.HkIntegrand_zero_fst`, at `sin (2θ) = 0` from
`Work.FTS.EllipticEst.RegQ.HkIntegrand_zero_sin_fts` (nonnegativity of `M` from
`HkIntegrand_nonneg`). The norm bound is `HkNorm_finset_sum_le` together with
`HkSq_congr_open α 4 hag` (`Xn α g = HkNorm α 4 g` definitionally). -/
theorem HkSumOpenClosure {α : ℝ} (hα : 0 < α) {n : ℕ} {g : Work.FTS.Galerkin.Fn}
    {F : ℕ → Work.FTS.Galerkin.Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsm : ∀ k ∈ Finset.range n, Work.FTS.EllipticEst.SmoothOpen (F k))
    (hm : ∀ k ∈ Finset.range n, Work.Spaces.HkMem α 4 (F k))
    (hag : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      g z θ = ∑ k ∈ Finset.range n, F k z θ) :
    Work.Spaces.HkMem α 4 g ∧
      Work.FTS.Nonlin.Xn α g ≤ Real.sqrt ((2 : ℝ) ^ n) * ∑ k ∈ Finset.range n,
        Work.FTS.Nonlin.Xn α (F k) := by
  classical
  set M : ℝ → ℝ → ℝ := fun z θ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
      Work.Spaces.HkIntegrand α 4 (F k) z θ with hM
  have hMnn : ∀ z θ : ℝ, 0 ≤ M z θ := by
    intro z θ
    show 0 ≤ (2 : ℝ) ^ n * ∑ k ∈ Finset.range n, Work.Spaces.HkIntegrand α 4 (F k) z θ
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => Work.Spaces.HkIntegrand_nonneg α 4 (F k) z θ)
  -- ### membership
  have hmem : Work.Spaces.HkMem α 4 g := by
    refine Work.FTS.LocData.HkMem_of_majorant (f := g) (M := M) α 4 hcont ?_ ?_ ?_
    · -- integrable `θ`-slices of the majorant
      intro z hz
      show IntegrableOn (fun θ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
        Work.Spaces.HkIntegrand α 4 (F k) z θ) Work.Spaces.Iθ
      have hsum : Integrable (fun θ : ℝ => ∑ k ∈ Finset.range n,
          Work.Spaces.HkIntegrand α 4 (F k) z θ) (volume.restrict Work.Spaces.Iθ) :=
        integrable_finsetSum (Finset.range n) (fun k hk => (hm k hk).1 z hz)
      exact hsum.const_mul _
    · -- integrable `z`-integral of the majorant
      show IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
        Work.Spaces.HkIntegrand α 4 (F k) z θ) Work.Spaces.Iz
      have hsum : Integrable (fun z : ℝ => ∑ k ∈ Finset.range n,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (F k) z θ)
          (volume.restrict Work.Spaces.Iz) :=
        integrable_finsetSum (Finset.range n) (fun k hk => (hm k hk).2)
      have hbase : Integrable (fun z : ℝ => (2 : ℝ) ^ n * ∑ k ∈ Finset.range n,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (F k) z θ)
          (volume.restrict Work.Spaces.Iz) := hsum.const_mul _
      refine hbase.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
      intro k hk
      exact (hm k hk).1 z hz
    · -- pointwise domination on the closed quadrant
      intro z hz θ hθ
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
      · subst hz0
        rw [Work.FTS.LocData.HkIntegrand_zero_fst]
        exact hMnn 0 θ
      · by_cases hs : Real.sin (2 * θ) = 0
        · rw [Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α 4 g hα hs]
          exact hMnn z θ
        · have hθpos : 0 < θ := by
            rcases lt_or_eq_of_le (show (0 : ℝ) ≤ θ from hθ.1) with h | h
            · exact h
            · exact absurd (by rw [← h, mul_zero, Real.sin_zero]) hs
          have hθlt : θ < Real.pi / 2 := by
            rcases lt_or_eq_of_le hθ.2 with h | h
            · exact h
            · exact absurd (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring,
                Real.sin_pi]) hs
          have hgeq : Work.Spaces.HkIntegrand α 4 g z θ
              = Work.Spaces.HkIntegrand α 4
                  (fun z θ => ∑ k ∈ Finset.range n, F k z θ) z θ :=
            Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := 4)
              (fun z θ hz hθ hlt => hag z θ hz hθ hlt) z θ hzpos hθpos hθlt
          rw [hgeq]
          have hle := Work.FTS.GalFields.RHS.HkIntegrand_finset_sum_le α 4 hα
            (Finset.range n) hsm z hz θ hθ
          simp only [Finset.card_range] at hle
          exact hle
  refine ⟨hmem, ?_⟩
  -- ### the norm bound
  have hXn : Work.FTS.Nonlin.Xn α g
      = Work.Spaces.HkNorm α 4 (fun z θ => ∑ k ∈ Finset.range n, F k z θ) := by
    show Work.Spaces.HkNorm α 4 g = _
    rw [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 4 hag,
      Work.Spaces.HkNorm]
  rw [hXn]
  simpa only [Finset.card_range] using
    Work.FTS.GalFields.RHS.HkNorm_finset_sum_le α 4 hα (Finset.range n) hsm hm

end Work.FTS.StrongEps.ClassCRHS
