import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- The open interval `Ioo 0 (π/2)` is conull in `Iθ = [0,π/2]`: it differs from `Iθ`
only by the two endpoints, which form a null set.  This is what makes the hypotheses
"on `Ioo 0 (π/2)`" sufficient for statements about `∫ θ in Iθ, ·`. -/
private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo 0 (π / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

/-- The square of the mixed weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is
`w z² · sin(2θ)^{-γ}`; this is the identity which converts a slot of `HkIntegrand`
into the corresponding explicit weighted square. -/
private lemma Wt_sq_eq (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The pointwise comparison for a pure `D_z`-slot: if `θw θ ≤ sin(2θ)^{-η}` then the
weighted square `w² θw (D_z^i f)²` is dominated by the `i`-th slot of `HkIntegrand`.
Only interior angles are needed (there the exponent identity `(w/s^{η/2})² = w² s^{-η}`
is available). -/
private lemma zSlot_pointwise (α : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) (hi : i ≤ 6)
    (θw : ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hle : θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :
    (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hmain : (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
      ≤ (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ (le_of_lt hs) (by norm_num [Work.Spaces.eta])]
    calc (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * (θw θ * (Work.Spaces.DzIter i f z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.DzIter i f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
  exact hmain.trans (Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ i hi)

/-- The pointwise comparison for a mixed slot: if `θw θ ≤ sin(2θ)^{-γ}` then the
weighted square `w² θw (D_z^j D_θ^i f)²` is dominated by the `(i,j)`-slot of
`HkIntegrand`. -/
private lemma mSlot_pointwise (α : ℝ) (f : ℝ → ℝ → ℝ) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 6) (θw : ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hle : θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :
    (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hmain : (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    calc (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * (θw θ * (Work.Spaces.mixed j i f z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [mul_pow, Wt_sq_eq α z θ hs]
          ring
  exact hmain.trans (Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i j hi hij)

theorem intSlotLeHkSq (α : ℝ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 6 f) :
    (∀ i : ℕ, i ≤ 6 → ∀ θw : ℝ → ℝ,
      (∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ θw θ) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f) ∧
    (∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 → ∀ θw : ℝ → ℝ,
      (∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ θw θ) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 6 f) := by
  have hIoo := ae_mem_Ioo_Iθ
  constructor
  · intro i hi θw hnn hle
    have hnn' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ θw θ :=
      hIoo.mono fun θ hθ => hnn θ hθ
    have hle' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      hIoo.mono fun θ hθ => hle θ hθ
    have hinner_nn : ∀ z, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2) :=
      fun z => hnn'.mono fun θ h1 =>
        mul_nonneg (mul_nonneg (sq_nonneg _) h1) (sq_nonneg _)
    have hinner_le : ∀ z, (fun θ =>
          (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Work.Spaces.HkIntegrand α 6 f z θ) :=
      fun z => (hIoo.and hle').mono fun θ hθ => zSlot_pointwise α f i hi θw z θ hθ.1 hθ.2
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae (hinner_nn z)) h.2 ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      MeasureTheory.integral_mono_of_nonneg (hinner_nn z) (h.1 z hz) (hinner_le z)
  · intro j i hi hij θw hnn hle
    have hnn' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ θw θ :=
      hIoo.mono fun θ hθ => hnn θ hθ
    have hle' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      hIoo.mono fun θ hθ => hle θ hθ
    have hinner_nn : ∀ z, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2) :=
      fun z => hnn'.mono fun θ h1 =>
        mul_nonneg (mul_nonneg (sq_nonneg _) h1) (sq_nonneg _)
    have hinner_le : ∀ z, (fun θ =>
          (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Work.Spaces.HkIntegrand α 6 f z θ) :=
      fun z => (hIoo.and hle').mono fun θ hθ =>
        mSlot_pointwise α f i j hi hij θw z θ hθ.1 hθ.2
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae (hinner_nn z)) h.2 ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      MeasureTheory.integral_mono_of_nonneg (hinner_nn z) (h.1 z hz) (hinner_le z)

end Work.FTS.StrongPersist.H6Pair6Aux
