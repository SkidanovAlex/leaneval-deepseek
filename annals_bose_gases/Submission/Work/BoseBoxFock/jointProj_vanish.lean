import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.thetaSector_vanish
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open Submission.BoseGases

/-- **The joint `θ`-sectors with `n₊`-eigenvalue beyond `𝓜` vanish.**
`Work.BoseBox.SpectralNPlusLe ℓ M Φ` bounds every moment of the excitation number `n₊` at `Φ`,
and `moment_expansion` (`Submission/Work/BoseBoxFock/thetaSector_vanish.lean`) diagonalises those
moments over the joint slot sectors: `∫ n₊^{2k}Φ·Φ = Σ_W (W.card)^{2k} ∫ (jointProj ℓ W Φ)²`.
Isolating the single sector `W` from that sum and letting `k → ∞` (the ratio
`M/(W.card) < 1`) forces its mass to vanish.  This is the analytic heart of the `ExcWindow`
step of `box_to_model` (it is the `ha` step of the proof of `thetaSector_vanish`, extracted as a
standalone statement). -/
theorem jointProj_vanish (ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) {M : ℝ} (hM : 0 ≤ M)
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    (W : Finset ℕ) (hW : W ⊆ Finset.range n) (hcard : M < (W.card : ℝ)) :
    ∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 = 0 := by
  set a : ℝ := ∫ x in Submission.BoseGases.abox n ℓ,
    (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 with hadef
  set B : ℝ := ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 with hBdef
  have ha_nonneg : 0 ≤ a := integral_nonneg (fun x => sq_nonneg _)
  have hpos : 0 < (W.card : ℝ) := lt_of_le_of_lt hM hcard
  -- For every even moment `2k` the sector inequality gives
  -- `(W.card)^{2k} · a ≤ M^{2k} · B`, hence `a ≤ B · (M / W.card)^{2k}`.
  have hkey : ∀ k : ℕ, a ≤ B * (M / (W.card : ℝ)) ^ (2 * k) := by
    intro k
    have hm := hmom (2 * k)
    rw [moment_expansion ℓ hℓ hΦ k] at hm
    have hsingle := Finset.single_le_sum
      (s := (Finset.range n).powerset)
      (f := fun V => (V.card : ℝ) ^ (2 * k) *
        ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.BoseFixB2.jointProj ℓ V Φ x) ^ 2)
      (fun V _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg V.card) _)
        (integral_nonneg (fun x => sq_nonneg _)))
      (Finset.mem_powerset.mpr hW)
    have h1 : (W.card : ℝ) ^ (2 * k) * a ≤ M ^ (2 * k) * B := le_trans hsingle hm
    have hdiv : a ≤ M ^ (2 * k) * B / (W.card : ℝ) ^ (2 * k) :=
      (le_div_iff₀ (pow_pos hpos _)).mpr (by rw [mul_comm]; exact h1)
    calc a ≤ M ^ (2 * k) * B / (W.card : ℝ) ^ (2 * k) := hdiv
      _ = B * (M / (W.card : ℝ)) ^ (2 * k) := by rw [div_pow]; ring
  have hr : (M / (W.card : ℝ)) ^ 2 < 1 := by
    have h0 : 0 ≤ M / (W.card : ℝ) := div_nonneg hM (le_of_lt hpos)
    have h1 : M / (W.card : ℝ) < 1 := (div_lt_one hpos).mpr hcard
    nlinarith
  have hpow : Filter.Tendsto (fun k : ℕ => ((M / (W.card : ℝ)) ^ 2) ^ k)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg (div_nonneg hM (le_of_lt hpos)) 2) hr
  have hlim : Filter.Tendsto (fun k : ℕ => B * ((M / (W.card : ℝ)) ^ 2) ^ k)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  have hle : a ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun k => by simpa [pow_mul] using hkey k)
  exact le_antisymm hle ha_nonneg

end Work.BoseBoxFock
