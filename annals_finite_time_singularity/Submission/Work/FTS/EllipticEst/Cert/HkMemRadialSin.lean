import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Cert.Defs
import Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_radial_sin
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.OpenCore
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin
import Submission.Work.FTS.EllipticEst.GbarSin.continuousOn_HkIntegrand_radial_sin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! ## The two gadgets

The proof of `HkMemRadialSin` needs two elementary facts:

* the radial iterate `radIter` of `OpenQAux` (the exact `D_z`-iterate of a function of `z`
  alone, appearing in the separated form `HkExp`) is the *same* operator as the one-variable
  `rDzIter` of `GbarSetup` (the one appearing in the hypotheses `hint`, `hcont`);
* the separated integrand `HkExp α k R z θ` is dominated, uniformly in `θ ∈ Iθ`, by the
  radial majorant `(1 + angKsum k)·w(z)²·Σ_{j≤k} (rDzIter j R z)²` — the same computation as
  `Cert.GbarSin.gbar_HkIntegrand_target_le`, with the angular constant `angK i` bounding
  `angA α i θ = (D_θ^i sin 2θ)² sin(2θ)^{-γ}` and `1` bounding `angZ θ = sin(2θ)^{2-η}`. -/

/-- **`radIter` and `rDzIter` are the same operator.**  Both compute the `j`-th iterate of
`g ↦ z ∂_z g`; `radIter` is defined through the two-variable `D_z` (`OpenQAux`), `rDzIter`
directly (`GbarSetup`). -/
theorem radIter_eq_rDzIter (R : ℝ → ℝ) (j : ℕ) :
    Work.FTS.EllipticEst.radIter R j = Work.FTS.EllipticEst.rDzIter j R := by
  induction j with
  | zero => rfl
  | succ n ih =>
      funext z
      rw [Work.FTS.EllipticEst.radIter_succ, ih]
      simp only [Work.FTS.EllipticEst.rDzIter_succ, Work.FTS.EllipticEst.rDz]

/-- The radial majorant of the `ℋ^k`-integrand of a separated function `R(z)·sin 2θ`:
`(1 + angKsum k)·w(z)²·Σ_{j≤k}(D_z^j R)(z)²`.  Its `θ`-slices are constant, and its slice
integral is integrable as soon as the weighted squares `w²·(D_z^j R)²`, `j ≤ k`, are. -/
def radialMajorant (k : ℕ) (R : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (1 + FstarHkOpen.angKsum k) * ((Work.Spaces.w z) ^ 2 *
    ∑ j ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.rDzIter j R z) ^ 2)

/-- **The pointwise domination of the separated integrand by the radial majorant.**  On the
closed angular interval the angular factors of `HkExp` are bounded by constants
(`angZ θ ≤ 1`, `angA α i θ ≤ angK i`), so the double sum is bounded by
`(Σ_i angK i)·Σ_j (D_z^j R)²`; collecting the two sums gives the claim. -/
theorem HkExp_le_radialMajorant (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    HkExp α k R z θ ≤ radialMajorant k R z θ := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  -- the `w²`-factor is distributed inside the `j`-sum of the majorant
  have hW : (Work.Spaces.w z) ^ 2 *
        ∑ j ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.rDzIter j R z) ^ 2
      = ∑ j ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter j R z) ^ 2 :=
    Finset.mul_sum _ _ _
  -- the pure `D_z`-sum
  have hS1 : (∑ i ∈ Finset.range (k + 1),
        (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
      ≤ ∑ j ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter j R z) ^ 2 :=
    Finset.sum_le_sum fun i _ => by
      calc (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ
          ≤ (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (angZ_le_one hθ)
              (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        _ = (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.radIter R i z) ^ 2 := by ring
        _ = (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter i R z) ^ 2 := by
            rw [radIter_eq_rDzIter R i]
  -- the mixed sum
  have hS2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
        else 0)
      ≤ (∑ i ∈ Finset.range (k + 1), FstarHkOpen.angK i) *
          (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter j R z) ^ 2) := by
    have hinner : ∀ i ∈ Finset.range (k + 1),
        (∑ j ∈ Finset.range (k + 1), if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
          else 0)
        ≤ FstarHkOpen.angK i * (∑ j ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter j R z) ^ 2) := by
      intro i _
      have hb : (∑ j ∈ Finset.range (k + 1), if 1 ≤ i ∧ i + j ≤ k then
            (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
            else 0)
          ≤ ∑ j ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter j R z) ^ 2
                * FstarHkOpen.angK i := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos hc]
          calc (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
              ≤ (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2
                  * FstarHkOpen.angK i :=
                mul_le_mul_of_nonneg_left (angA_le_angK α i hgam1 hgam2 hθ)
                  (mul_nonneg (sq_nonneg _) (sq_nonneg _))
            _ = (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.radIter R j z) ^ 2
                  * FstarHkOpen.angK i := by ring
            _ = (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter j R z) ^ 2
                  * FstarHkOpen.angK i := by rw [radIter_eq_rDzIter R j]
        · rw [if_neg hc]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (FstarHkOpen.angK_pos i).le
      refine hb.trans (le_of_eq ?_)
      rw [← Finset.sum_mul]
      ring
    exact (Finset.sum_le_sum hinner).trans (le_of_eq (by rw [Finset.sum_mul]))
  rw [HkExp, radialMajorant, FstarHkOpen.angKsum, hW]
  refine (add_le_add hS1 hS2).trans (le_of_eq ?_)
  ring

/-- **Membership in `ℋ^k` of a separated function `R(z)·sin 2θ`.**
Route: `HkIntegrand α k (fun z θ => R z * Real.sin (2*θ))` equals the explicit separated form
`HkExp α k R` on `Iθ` (`Cert.HkIntegrand_radial_sin`, proved), which is dominated by
`Kang k · w(z)² · Σ_{j≤k} (rDzIter j R z)²` (same computation as
`Cert.GbarSin.gbar_HkIntegrand_target_le` with `Gbar α F` replaced by `R`).  Apply
`Work.FTS.LocData.HkMem_of_majorant` with the majorant `M z θ = C·w(z)²·Σ_{j≤k}(rDzIter j R z)²`
(constant θ-slices; slice integral integrable by `hint`).  `hcont` makes the integrand
continuous on the open quadrant (it equals `HkExp α k R`). -/
theorem HkMemRadialSin (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hint : ∀ j ≤ k, MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter j R z) ^ 2)
      Work.Spaces.Iz)
    (hcont : ∀ j ≤ k, ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.rDzIter j R z)
      (Set.Ioi 0)) :
    Work.Spaces.HkMem α k (fun z θ => R z * Real.sin (2 * θ)) := by
  have hα1 : α ≤ 1 := by linarith
  have hIθ : (MeasureTheory.volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- the `θ`-slices of the majorant are constant in `θ`
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => radialMajorant k R z θ) Work.Spaces.Iθ := by
    intro z _
    refine (MeasureTheory.integrableOn_const
      (C := radialMajorant k R z 0) hIθ).congr_fun (fun θ _ => ?_) measurableSet_Icc
    rw [radialMajorant, radialMajorant]
  -- the `z`-integral of the slices of the majorant is integrable, by `hint`
  have hMz : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, radialMajorant k R z θ) Work.Spaces.Iz := by
    have hsum : MeasureTheory.Integrable (fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.rDzIter j R z) ^ 2)
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) :=
      MeasureTheory.integrable_finsetSum (Finset.range (k + 1))
        (fun j hj => hint j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, radialMajorant k R z θ)
        = fun z => (π / 2) * ((1 + FstarHkOpen.angKsum k) *
            ((Work.Spaces.w z) ^ 2 * ∑ j ∈ Finset.range (k + 1),
              (Work.FTS.EllipticEst.rDzIter j R z) ^ 2)) := by
      funext z
      rw [show (fun θ : ℝ => radialMajorant k R z θ)
          = fun _ : ℝ => (1 + FstarHkOpen.angKsum k) * ((Work.Spaces.w z) ^ 2 *
              ∑ j ∈ Finset.range (k + 1),
                (Work.FTS.EllipticEst.rDzIter j R z) ^ 2) from by
        funext θ
        rw [radialMajorant]]
      rw [Work.FTS.EllipticEst.Cert.GbarSin.gbar_integral_Iθ_const]
    rw [hfun]
    have h' : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2 *
        ∑ j ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.rDzIter j R z) ^ 2)
        ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) :=
      hsum.congr (Filter.Eventually.of_forall fun z =>
        (Finset.mul_sum (Finset.range (k + 1))
          (fun j => (Work.FTS.EllipticEst.rDzIter j R z) ^ 2)
          ((Work.Spaces.w z) ^ 2)).symm)
    exact (h'.const_mul (1 + FstarHkOpen.angKsum k)).const_mul (π / 2)
  refine Work.FTS.LocData.HkMem_of_majorant (α := α) (k := k)
    (f := fun z θ => R z * Real.sin (2 * θ)) (M := radialMajorant k R)
    (Work.FTS.EllipticEst.GbarSin.continuousOn_HkIntegrand_radial_sin α k R hcont)
    hMslice hMz ?_
  intro z hz θ hθ
  rw [HkIntegrand_radial_sin α k R z θ hθ]
  exact HkExp_le_radialMajorant α k R hα hα1 z θ hθ

end Work.FTS.EllipticEst.Cert
