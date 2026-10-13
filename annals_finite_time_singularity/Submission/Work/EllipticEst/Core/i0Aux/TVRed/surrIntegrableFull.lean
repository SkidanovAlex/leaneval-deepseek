/-
Copyright: work module for the Elgindi finite-time singularity project.

# The fourth conjunct of `surrIntegrable`: integrability of `(ℓ')² q² thEta`

The lemma `Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrable` asks for the integrability on
`Iθ = [0, π/2]` of four weighted squares built from the trace-matching surrogate
`ℓ = surrFun ψ F₀ F₁ L`:

* `ℓ² thEta`, `(ℓ')² thEta`, `(ℓ'')² thEta` — these are *global* bounds (the three
  functions are bounded by `|F₀| + |F₁|`, `C (|F₀|+|F₁|)/L` and `C (|F₀|+|F₁|)/L²`), and
  they are provided by `TVRed.tvh_surr_integrable` (no upper bound on `L` is needed);
* `(ℓ')² q² thEta` with `qTh θ = 2 η cot 2θ` — this is the conjunct that makes the
  statement carry the scale hypothesis `L ≤ π/4`.

The fourth conjunct is genuinely different: `qTh` blows up at the endpoints `θ = 0, π/2`
(like `1/θ`), and `qTh θ ^ 2 * thEta θ ~ θ^{-2-η}` is *not* integrable near `0`, since
`thEta θ = sin(2θ)^{-η}` with `η = 99/100 < 1`.  The saving grace is the **support** of
`ℓ'`: the bump satisfies `ψ = 1` on `(-∞, 1/4]` and `ψ = 0` on `[1/2, ∞)`, so its derivative
is supported in `(1/4, 1/2)`; hence `ℓ'` is supported in the two shells `(L/4, L/2)` and
`(π/2 - L/2, π/2 - L/4)`.  For `L ≤ π/4` both shells keep a distance `L/4` from the
endpoints, where

  `sin 2θ ≥ sin(L/2) > 0`,  hence  `qTh θ ^ 2 * thEta θ ≤ (2η)² sin(L/2)^{-(2+η)}`,

while `|ℓ' θ| ≤ C (|F₀| + |F₁|)/L`.  Therefore

  `(ℓ')² q² thEta ≤ Q * thEta`,  `Q := (C (|F₀|+|F₁|)/L)² (2η)² sin(L/2)^{-(2+η)}`,

and `thEta` is integrable on `Iθ`.

The one structural ingredient that is not already in `TVRed/BumpFacts.lean` is that the
bump's derivative vanishes on the *closed* half-lines `(-∞, 1/4]` and `[1/2, ∞)`; the fields
`IsBump.deriv_eq_zero_left/right` only give the open versions.  Since `deriv ψ` is
continuous (`ContDiff.continuous_deriv`) the closed version follows by uniqueness of limits,
and it is what makes the support statement hold on *all* of `Iθ` rather than only almost
everywhere — the pointwise comparison `|g θ| ≤ Q * thEta θ` of
`tvh_integrableOn_of_abs_le` is required at every point.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypAux
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvh_surr_integrable
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

variable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}

/-! ## 1. The bump's derivative vanishes on the closed outer half-lines -/

/-- `deriv ψ = 0` on the closed left half-line `(-∞, 1/4]`.  (`IsBump.deriv_eq_zero_left`
gives the open version; `deriv ψ` is continuous, so the endpoint follows.) -/
lemma tvh_deriv_eq_zero_le (hψ : IsBump ψ C) {x : ℝ} (hx : x ≤ 1 / 4) : deriv ψ x = 0 := by
  have hcont : Continuous (deriv ψ) := hψ.contDiff.continuous_deriv (by norm_num)
  have hne : Filter.NeBot (nhdsWithin x (Set.Iio x)) := nhdsWithin_Iio_neBot (le_refl x)
  have h2 : Filter.Tendsto (deriv ψ) (nhdsWithin x (Set.Iio x)) (nhds 0) := by
    refine Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℝ)) ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hψ.deriv_eq_zero_left y (lt_of_lt_of_le hy hx)).symm
  exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h2

/-- `deriv ψ = 0` on the closed right half-line `[1/2, ∞)`. -/
lemma tvh_deriv_eq_zero_ge (hψ : IsBump ψ C) {x : ℝ} (hx : 1 / 2 ≤ x) : deriv ψ x = 0 := by
  have hcont : Continuous (deriv ψ) := hψ.contDiff.continuous_deriv (by norm_num)
  have hne : Filter.NeBot (nhdsWithin x (Set.Ioi x)) := nhdsWithin_Ioi_neBot (le_refl x)
  have h2 : Filter.Tendsto (deriv ψ) (nhdsWithin x (Set.Ioi x)) (nhds 0) := by
    refine Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℝ)) ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hψ.deriv_eq_zero_right y (lt_of_le_of_lt hx hy)).symm
  exact tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h2

/-! ## 2. The surrogate's derivative vanishes on the closed outer intervals -/

/-- `ℓ' = 0` on `[0, L/4]`. -/
lemma tvh_deriv_surr_eq_zero_of_le (hψ : IsBump ψ C) (hL : 0 < L)
    (hLp : L ≤ Real.pi / 4) {θ : ℝ} (hθ : θ ≤ L / 4) :
    deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv ψ (θ / L) = 0 := by
    apply tvh_deriv_eq_zero_le hψ
    rw [div_le_iff₀ hL]; linarith
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv_eq_zero_right
    rw [lt_div_iff₀ hL]
    linarith [hθ, hLp, Real.pi_pos]
  rw [h1, h2]
  ring

/-- `ℓ' = 0` on `[π/2 - L/4, π/2]`. -/
lemma tvh_deriv_surr_eq_zero_of_ge (hψ : IsBump ψ C) (hL : 0 < L)
    (hLp : L ≤ Real.pi / 4) {θ : ℝ} (hθ : Real.pi / 2 - L / 4 ≤ θ) :
    deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv ψ (θ / L) = 0 := by
    apply hψ.deriv_eq_zero_right
    rw [lt_div_iff₀ hL]
    linarith [hθ, hLp, Real.pi_pos]
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply tvh_deriv_eq_zero_le hψ
    rw [div_le_iff₀ hL]
    linarith [hθ]
  rw [h1, h2]
  ring

/-! ## 3. The lower bound on `sin 2θ` on the shells -/

/-- On the shell `(L/4, π/2 - L/4)` with `L ≤ π/4`, one has `sin(L/2) ≤ sin 2θ`.
(Both `2θ` and `π - 2θ` lie in `[L/2, π/2]`, and `sin` is increasing there.) -/
lemma tvh_sin_two_ge_sin (hL : 0 < L) (hLp : L ≤ Real.pi / 4) {θ : ℝ}
    (h1 : L / 4 < θ) (h2 : θ < Real.pi / 2 - L / 4) :
    Real.sin (L / 2) ≤ Real.sin (2 * θ) := by
  rcases le_or_gt (2 * θ) (Real.pi / 2) with hc | hc
  · exact le_of_lt (Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := L / 2) (y := 2 * θ) (by linarith [Real.pi_pos]) hc (by linarith))
  · have hlt : L / 2 < Real.pi - 2 * θ := by linarith
    have hle : Real.pi - 2 * θ ≤ Real.pi / 2 := by linarith
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := L / 2) (y := Real.pi - 2 * θ) (by linarith [Real.pi_pos]) hle hlt
    rw [Real.sin_pi_sub] at h
    exact le_of_lt h

/-! ## 4. The bound `q² thEta ≤ (2η)² sin(L/2)^{-(2+η)}` -/

/-- On the shell, `qTh θ ^ 2 * thEta θ ≤ (2η)² sin(L/2)^{-(2+η)}`: the exploding factor `cot`
is dominated by `sin(L/2)^{-1}` and the weight by `sin(L/2)^{-η}`. -/
lemma tvh_cot_sq_mul_thEta_le (hL : 0 < L) (hLp : L ≤ Real.pi / 4) {θ : ℝ}
    (h1 : L / 4 < θ) (h2 : θ < Real.pi / 2 - L / 4) :
    (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [h2, Real.pi_pos])
  have hLsinpos : 0 < Real.sin (L / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hLp, Real.pi_pos])
  have hle : Real.sin (L / 2) ≤ Real.sin (2 * θ) := tvh_sin_two_ge_sin hL hLp h1 h2
  have hexp : (-(2 + Work.Spaces.eta) : ℝ)
      = (-(2 : ℝ)) + (-(Work.Spaces.eta)) := by ring
  have hrp : (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
      = (Real.sin (2 * θ) ^ 2)⁻¹ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [hexp, Real.rpow_add hspos, Real.rpow_neg hspos.le (2 : ℝ),
      Real.rpow_two (Real.sin (2 * θ))]
  have hcot1 : Real.cot (2 * θ) ^ 2 = Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ) ^ 2)⁻¹ := by
    rw [Real.cot_eq_cos_div_sin, div_pow, div_eq_mul_inv]
  have key : Real.cot (2 * θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      = Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    rw [hcot1, hrp]
    simp only [Work.FTS.EllipticEst.thEta]
    ring
  rw [key]
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
    Real.rpow_nonneg hspos.le _
  calc Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))
      ≤ 1 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right (Real.cos_sq_le_one (2 * θ)) hnn
    _ = (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := one_mul _
    _ ≤ (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_nonpos hLsinpos hle (by linarith [Work.Spaces.eta_pos])

/-! ## 5. Continuity of `qTh` on the open interval -/

/-- `qTh θ = 2 η cot(2θ)` is continuous on `(0, π/2)`, where `sin(2θ) ≠ 0`. -/
lemma tvh_continuousOn_qTh : ContinuousOn qTh (Set.Ioo 0 (Real.pi / 2)) := by
  have hq : qTh = fun θ : ℝ => 2 * Work.Spaces.eta * (Real.cos (2 * θ) / Real.sin (2 * θ)) := by
    funext θ
    rw [show qTh θ = 2 * Work.Spaces.eta * Real.cot (2 * θ) from rfl, Real.cot_eq_cos_div_sin]
  rw [hq]
  have hc : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hs : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have hdiv : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) / Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := hc.div hs hne
  exact continuousOn_const.mul hdiv

/-! ## 6. The fourth conjunct -/

/-- `(ℓ')² q² thEta` is integrable on `Iθ` for `0 < L ≤ π/4`. -/
theorem tvh_surr_deriv_qTh_integrable (hψ : IsBump ψ C) (hL : 0 < L)
    (hLp : L ≤ Real.pi / 4) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have hsL : 0 < Real.sin (L / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hLp, Real.pi_pos])
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = (C * (|F₀| + |F₁|) / L) ^ 2
      * (2 * Work.Spaces.eta) ^ 2 * (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) :=
    ⟨_, rfl⟩
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt hsL) _)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 *
        Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((tvh_aesm_of_continuousOn
        (tvh_continuous_deriv_surr hψ (ne_of_gt hL)).continuousOn).pow 2).mul
      ((tvh_aesm_of_continuousOn tvh_continuousOn_qTh).pow 2)).mul tvh_aesm_thEta
  refine tvh_integrableOn_of_abs_le (tvh_integrableOn_const_mul_thEta Q) haesm ?_
  intro θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  have hfac : 0 ≤ (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [abs_of_nonneg (mul_nonneg hfac hσ)]
  refine mul_le_mul_of_nonneg_right ?_ hσ
  have hderiv : (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (deriv_surr_bound hψ hL θ) 2
  have hb2nn : 0 ≤ (C * (|F₀| + |F₁|) / L) ^ 2 := sq_nonneg _
  rcases le_or_gt θ (L / 4) with hle1 | hlt
  · rw [tvh_deriv_surr_eq_zero_of_le hψ hL hLp hle1]
    simpa using hQnn
  · rcases le_or_gt (Real.pi / 2 - L / 4) θ with hle2 | hgt
    · rw [tvh_deriv_surr_eq_zero_of_ge hψ hL hLp hle2]
      simpa using hQnn
    · have hL4 : 0 < L / 4 := by positivity
      have hL2 : 0 < L / 2 := by positivity
      have hone : (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta θ := by
        have h := Real.rpow_le_rpow_of_nonpos
          (x := Real.sin (2 * θ)) (y := 1) (z := -(Work.Spaces.eta))
          (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hgt, hL, Real.pi_pos]))
          (Real.sin_le_one (2 * θ)) (by linarith [Work.Spaces.eta_pos])
        simpa only [Work.FTS.EllipticEst.thEta, Real.one_rpow] using h
      have hcot : (Real.cot (2 * θ)) ^ 2
          ≤ (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) :=
        calc (Real.cot (2 * θ)) ^ 2 = (Real.cot (2 * θ)) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
              mul_le_mul_of_nonneg_left hone (sq_nonneg _)
          _ ≤ (Real.sin (L / 2)) ^ (-(2 + Work.Spaces.eta)) :=
              tvh_cot_sq_mul_thEta_le hL hLp hlt hgt
      have hq2 : (qTh θ) ^ 2 = (2 * Work.Spaces.eta) ^ 2 * (Real.cot (2 * θ)) ^ 2 := by
        rw [show qTh θ = 2 * Work.Spaces.eta * Real.cot (2 * θ) from rfl, mul_pow]
      calc (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2
          = (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 *
              ((2 * Work.Spaces.eta) ^ 2 * (Real.cot (2 * θ)) ^ 2) := by rw [hq2]
        _ = ((deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (2 * Work.Spaces.eta) ^ 2)
              * (Real.cot (2 * θ)) ^ 2 := by ring
        _ ≤ Q := by
            rw [hQdef]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_right hderiv (sq_nonneg (2 * Work.Spaces.eta)))
              hcot (sq_nonneg (Real.cot (2 * θ)))
              (mul_nonneg hb2nn (sq_nonneg (2 * Work.Spaces.eta)))

/-! ## 7. The four-conjunct statement -/

/-- All four conjuncts of `surrIntegrable`: the first three are global bounds
(`TVRed.tvh_surr_integrable`), the fourth is `tvh_surr_deriv_qTh_integrable`. -/
theorem tvh_surr_integrable4 (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (surrFun ψ F₀ F₁ L θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * (qTh θ) ^ 2 *
          Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  obtain ⟨h1, h2, h3⟩ := tvh_surr_integrable (ψ := ψ) (C := C) (F₀ := F₀) (F₁ := F₁)
    (L := L) hψ hL
  exact ⟨h1, h2, h3, tvh_surr_deriv_qTh_integrable (ψ := ψ) (C := C) (F₀ := F₀) (F₁ := F₁)
    (L := L) hψ hL hLp⟩

end

end Work.EllipticEst.Core.i0Aux.TVRed
