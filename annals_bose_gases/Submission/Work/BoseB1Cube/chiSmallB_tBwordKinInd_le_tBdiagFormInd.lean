import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.cubeKinPeel
import Submission.Work.BoseFixB1S.cubeSpectral_uniformBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.chiSmallB_tBwordKinInd_le_tBdiagFormInd`

The `chiSmallB` twin of the PROVED `Work.BoseFixB1S.mfSpecLeKinB1` — the *symbol monotonicity*

    `[‖p‖ − c]₊² ≤ ‖p‖²`   (`0 ≤ c`)

in the slot `p`-integral of the FS-faithful `p`-diagonal kinetic form, at the sliding window
`χ = chiSmallB M ℓ d u` (the cosine-`M`-th-power bump, `M ≥ 4`, i.e. `C³`) and the sliding box
`A = dlBox ℓ d u`.

## Route

* `tBwordKinInd a A V χ c Ψ = tBdiagFormInd a A V χ (fsKinCoeff c) Ψ` by definition, and
  `fsKinCoeff c r = (max (r−c) 0)² ≤ r²` for `r ≥ 0`, `c ≥ 0`;
* since `tsupport χ ⊆ dlBox ℓ d u`, FS's box indicator factors out of the amplitude
  (`Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm`), so both words are the corpus's
  `Work.SmallBoxTBWord.tBdiagForm`, whose slots are compared by `integral_mono_of_nonneg`;
* the only integrability input is that of the `‖p‖²`-weighted slot integrand at the `boxQ`-state,
  which is supplied by the decay of the windowed amplitude applied to the *whole* mean-free state
  `Q_{B,i}Φ` (`Work.BoseFixB1S.win.tBamp_decay_three`, the `C³`-window decay) — no bound on the box
  mean is needed, and the volume `V` enters only as the normalisation constant of `boxQ`.
-/

namespace Work.BoseB1Cube

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. Integrability of the dominating `p`-integrand at the `chiSmallB` window -/

/-- **Integrability of the `‖p‖²`-weighted `p`-integrand of the sliding box, at the
`chiSmallB` window.**  This is the `chiSmallB` twin of `Work.SmallBoxTBWord.tBampForm_integrable`
(which needs a `C^∞` window): the window here is only `C³` (`M ≥ 4`), so the proof runs on
`Work.BoseFixB1S.win.tBamp_decay_three` instead of `tBamp_decay`.

The state is FS's mean-free projection `Q_{B,i}Φ = Φ − P_{B,i}Φ`, which — unlike the
indicator-carrying `boxQInd` — is `C^∞` on the compact box `dlBox ℓ d u`, so the decay estimate
applies to it directly and the box mean never has to be bounded. -/
theorem chiSmallB_tBdiagForm_pIntegrable {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) {V : ℝ} {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin N) :
    MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * ((ℓ ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox N ℓ,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
          (Work.SmallBoxTBWord.boxQ V (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)) := by
  classical
  rcases N with _ | n
  · exact i.elim0
  · set χ : E3 → ℝ := Submission.BoseGases.chiSmallB M ℓ d u with hχdef
    set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
    have hM1 : 1 ≤ M := by omega
    have hAcomp : IsCompact A := Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u
    have hχc3 : ContDiff ℝ 3 χ := Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hℓ hd u
    have hχcs : HasCompactSupport χ :=
      HasCompactSupport.of_support_subset_isCompact hAcomp
        (Work.BoseFixB1S.win.support_chiSmallB_subset_dlBox hM1 hℓ hd u)
    have hboxQ : ContDiff ℝ (⊤ : ENat) (Work.SmallBoxTBWord.boxQ V A i Φ) :=
      Work.SmallBoxTBWord.boxQ_contDiff_of_compact hAcomp V i hΦ
    have hcont : Continuous (fun p : E3 =>
        ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Φ) i x‖ ^ 2) :=
      Work.SmallBoxTBWord.continuous_integral_tBamp_sq (N := n + 1) hℓ hχc3.continuous hχcs
        hboxQ.continuous i
    obtain ⟨D, hD0, hD⟩ :=
      Work.BoseFixB1S.win.tBamp_decay_three (N := n + 1) (a := ℓ) hℓ hχc3 hχcs hboxQ
    haveI : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ, Submission.BoseGases.abox_volume (n + 1) ℓ hℓ.le]
          exact ENNReal.ofReal_lt_top⟩
    have hreal : ((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)).real Set.univ = (ℓ ^ 3) ^ (n + 1) := by
      rw [Measure.real_def, Measure.restrict_apply_univ,
        Submission.BoseGases.abox_volume (n + 1) ℓ hℓ.le,
        ENNReal.toReal_ofReal (by positivity)]
    -- the box integral of the squared amplitude is bounded by the decay constant
    have hIntBound : ∀ p : E3, (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Φ) i x‖ ^ 2)
        ≤ (D / (1 + ‖p‖) ^ 3) ^ 2 * (ℓ ^ 3) ^ (n + 1) := by
      intro p
      set Dp : ℝ := (D / (1 + ‖p‖) ^ 3) ^ 2 with hDp
      have hle : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
          (Submission.BoseGases.abox (n + 1) ℓ)),
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Φ) i x‖ ^ 2 ≤ Dp := by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) ℓ)]
        filter_upwards with x hx
        rw [hDp]
        exact pow_le_pow_left₀ (norm_nonneg _) (hD x hx i p) 2
      have hmono := integral_mono_of_nonneg
        (μ := (volume : Measure (Submission.BoseGases.X (n + 1))).restrict
          (Submission.BoseGases.abox (n + 1) ℓ))
        (f := fun x : Submission.BoseGases.X (n + 1) =>
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Φ) i x‖ ^ 2)
        (g := fun _ : Submission.BoseGases.X (n + 1) => Dp)
        (Eventually.of_forall (fun x => sq_nonneg _)) (integrable_const Dp) hle
      calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Φ) i x‖ ^ 2)
          = ∫ x, ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Φ) i x‖ ^ 2
              ∂((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
                (Submission.BoseGases.abox (n + 1) ℓ)) := rfl
        _ ≤ ∫ _x, Dp ∂((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
                (Submission.BoseGases.abox (n + 1) ℓ)) := hmono
        _ = Dp * (ℓ ^ 3) ^ (n + 1) := by rw [integral_const, smul_eq_mul, hreal, mul_comm]
        _ = (D / (1 + ‖p‖) ^ 3) ^ 2 * (ℓ ^ 3) ^ (n + 1) := by rw [hDp]
    -- the `p`-integrand is dominated by an integrable radial profile
    have hkey : ∀ p : E3, ‖p‖ ^ 2 * ((ℓ ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Φ) i x‖ ^ 2)
        ≤ (D ^ 2 * (ℓ ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by
      intro p
      have h1 : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
      calc ‖p‖ ^ 2 * ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ V A i Φ) i x‖ ^ 2)
          ≤ ‖p‖ ^ 2 * ((ℓ ^ 3)⁻¹ * ((D / (1 + ‖p‖) ^ 3) ^ 2 * (ℓ ^ 3) ^ (n + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hIntBound p) h1) (sq_nonneg _)
        _ = (D ^ 2 * (ℓ ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6) := by
            rw [div_pow, ← pow_mul, pow_succ]
            norm_num
            field_simp
            ring
    have hdom : Integrable (fun p : E3 => (D ^ 2 * (ℓ ^ 3) ^ n) * (‖p‖ ^ 2 / (1 + ‖p‖) ^ 6)) :=
      (Commons.Measure.Integral.integrable_norm_sq_div_one_add_pow 6 le_rfl).const_mul _
    refine hdom.mono' ?_ ?_
    · exact ((continuous_norm.pow 2).mul (continuous_const.mul hcont)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _))))]
      exact hkey p

/-! ## 2. The target -/

theorem chiSmallB_tBwordKinInd_le_tBdiagFormInd {M : ℕ} (hM : 4 ≤ M) {ℓ d c : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hc : 0 ≤ c) (u : EuclideanSpace ℝ (Fin 3)) {V : ℝ} {N : ℕ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u) V
        (Submission.BoseGases.chiSmallB M ℓ d u) c Φ
      ≤ Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u) V
        (Submission.BoseGases.chiSmallB M ℓ d u) (fun r : ℝ => r ^ 2) Φ := by
  have hM1 : 1 ≤ M := by omega
  -- the sliding window vanishes off the sliding box
  have hχsupp : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiSmallB M ℓ d u z = 0 :=
    fun z hz => Work.BoseFixB1S.win.chiSmallB_eq_zero_of_not_mem_dlBox hM1 hℓ hd u z hz
  -- remove the box indicator on both sides
  have hL := Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (a := ℓ)
    (A := Submission.BoseGases.dlBox ℓ d u) (volA := V)
    (χ := Submission.BoseGases.chiSmallB M ℓ d u) (Submission.BoseGases.fsKinCoeff c) Φ hχsupp
  have hR := Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (a := ℓ)
    (A := Submission.BoseGases.dlBox ℓ d u) (volA := V)
    (χ := Submission.BoseGases.chiSmallB M ℓ d u) (fun r : ℝ => r ^ 2) Φ hχsupp
  unfold Work.UBBInputs8.tBwordKinInd
  rw [hL, hR]
  unfold Work.SmallBoxTBWord.tBdiagForm
  rcases N with _ | m
  · -- `N = 0`: both words are empty sums
    simp
  · -- `N = m + 1`: slotwise symbol comparison
    have hintG : ∀ i : Fin (m + 1), MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * ((ℓ ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
              (Work.SmallBoxTBWord.boxQ V (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2)) :=
      fun i => chiSmallB_tBdiagForm_pIntegrable hM hℓ hd u hΦ i
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt Work.SmallBoxTBWord.twoPiInv3_pos)
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => ?_))
      (hintG i) (Filter.Eventually.of_forall (fun p => ?_))
    · exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3))
          (integral_nonneg (fun x => sq_nonneg _)))
    · exact mul_le_mul_of_nonneg_right (Work.SmallBoxTBWord.fsKinCoeff_le_sq_all hc)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3))
          (integral_nonneg (fun x => sq_nonneg _)))

end

end Work.BoseB1Cube
