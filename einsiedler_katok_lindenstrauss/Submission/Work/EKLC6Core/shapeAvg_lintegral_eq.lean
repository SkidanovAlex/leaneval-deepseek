import Mathlib
import Submission.Work.EKLC6Core.AtomInfoSetup

/-!
# `EKLC6Core.shapeAvg_lintegral_eq` — the shape average is the conditional expectation

For a leaf-wise system `ν = μ_x^U`, a plaque algebra `(Z, S.m)` and an exponent vector `t`,
the `ν x`-average of `g` over the pull-back shape `Wsh t S U x` of the atom of
`comap (aDiag t ·) S.m` reproduces the integral of `g`:

`∫⁻ x, (∫⁻ u in Wsh t S U x, g (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) ∂μ = ∫⁻ x, g x ∂μ`.

This is the `condexp` field of `IsLeafwise` (`condExp_betaAlg_eq`) combined with
`∫ x, μ[f | m] x ∂μ = ∫ x, f x ∂μ` (`integral_condExp`).

The proof truncates `g` at height `n` (the truncations are bounded, so the real-valued
conditional expectation applies), uses
`∫ u, h(u • x) ∂νx = (∫⁻ u, ofReal (h (u • x)) ∂νx).toReal` and the `ℝ≥0∞`-bridge
`ofReal (a.toReal / b.toReal) = a / b`, and passes to the limit `n → ∞` with the monotone
convergence theorem (for the integral over `x` this needs only *a.e.* measurability of the shape
averages, which is provided by the a.e. identification with `ofReal ∘ 𝔼[·|β]`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The `ℝ≥0∞`-bridge: `ofReal (a.toReal / b.toReal) = a / b` for `a ≠ ⊤` and
`0 < b < ⊤`. -/
theorem ofReal_toReal_div_eq {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ 0) (hbt : b ≠ ⊤) :
    ENNReal.ofReal (a.toReal / b.toReal) = a / b := by
  have hbpos : 0 < b.toReal := ENNReal.toReal_pos hb hbt
  rw [ENNReal.ofReal_div_of_pos hbpos]
  rw [ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hbt]

/-- **The shape average integrates back to `g`.** -/
theorem shapeAvg_lintegral_eq {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (t : Fin 3 → ℝ) (hmp : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ)
    {S : Work.EKLRelCross.MSAlg} {Z : Set X3} (hA : IsPlaqueAlgebra U Z S.m) (hZ : μ Zᶜ = 0)
    (g : X3 → ENNReal) (hg : Measurable g) :
    ∫⁻ x, (∫⁻ u in Wsh t S U x, g (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) ∂μ
      = ∫⁻ x, g x ∂μ := by
  classical
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hAZ : MeasurableSet Z := hA.1 Z hA.2.2.1
  have hTZ : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have hX'ae : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  have hTZae : ∀ᵐ x ∂μ, x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z := by
    rw [MeasureTheory.ae_iff]; exact hTZ
  have hden : ∀ᵐ x ∂μ, ν x (Wsh t S U x) ≠ 0 ∧ ν x (Wsh t S U x) ≠ ⊤ := by
    filter_upwards [hX'ae, hTZae] with x hx hxTZ
    obtain ⟨h1, h2⟩ := mass_Wsh (S := S) hU hL hA t hx hxTZ
    exact ⟨ne_of_gt h1, ne_of_lt h2⟩
  have hβborel : betaAlg t S ≤ borel X3 := by
    rw [betaAlg_def]
    exact (MeasurableSpace.comap_mono hA.1).trans
      (measurable_iff_comap_le.mp (continuous_const_smul (aDiag t)).measurable)
  -- truncations of `g`
  set gn : ℕ → X3 → ENNReal := fun n x => g x ⊓ (n : ENNReal) with hgn
  set hn : ℕ → X3 → ℝ := fun n x => (gn n x).toReal with hhn
  have hgn_meas : ∀ n, Measurable (gn n) := fun n => hg.min measurable_const
  have hhn_meas : ∀ n, Measurable (hn n) := fun n => (hgn_meas n).ennreal_toReal
  have hhn_nonneg : ∀ n x, 0 ≤ hn n x := fun n x => ENNReal.toReal_nonneg
  have hhn_le : ∀ n x, hn n x ≤ (n : ℝ) := fun n x => by
    rw [hhn]
    exact ENNReal.toReal_mono (ENNReal.natCast_lt_top n).ne (by simp only [hgn]; exact inf_le_right)
  have hofReal_hn : ∀ n x, ENNReal.ofReal (hn n x) = gn n x := fun n x => by
    rw [hhn]
    exact ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top (ENNReal.natCast_lt_top n).ne (by simp only [hgn]; exact inf_le_right))
  have hgmono : Monotone gn := fun m n hmn x => inf_le_inf_left _ (by exact_mod_cast hmn)
  -- the a.e. identification with the real conditional expectation
  have hae : ∀ n, ∀ᵐ x ∂μ, (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x))
      = ENNReal.ofReal (condExp (betaAlg t S) μ (hn n) x) := by
    intro n
    have hbddh : ∃ C, ∀ y : X3, |hn n y| ≤ C :=
      ⟨(n : ℝ), fun y => by rw [abs_of_nonneg (hhn_nonneg n y)]; exact hhn_le n y⟩
    filter_upwards [condExp_betaAlg_eq hU hL hA t hmp hZ (hn n) (hhn_meas n) hbddh, hden]
      with x hx hd
    rw [hx]
    have hgen : ∫ u in Wsh t S U x, hn n (u • x) ∂(ν x)
        = (∫⁻ u in Wsh t S U x, ENNReal.ofReal (hn n (u • x)) ∂(ν x)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun u => hhn_nonneg n (u • x))
        (((hhn_meas n).comp (continuous_id.smul continuous_const).measurable).aestronglyMeasurable)
    have hcongr : (∫⁻ u in Wsh t S U x, ENNReal.ofReal (hn n (u • x)) ∂(ν x))
        = ∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x) :=
      MeasureTheory.lintegral_congr fun u => hofReal_hn n (u • x)
    have hnum : ∫ u in Wsh t S U x, hn n (u • x) ∂(ν x)
        = (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)).toReal := by
      rw [hgen, hcongr]
    rw [hnum]
    refine (ofReal_toReal_div_eq ?_ hd.1 hd.2).symm
    have hAle : ∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)
        ≤ (n : ENNReal) * ν x (Wsh t S U x) := by
      calc ∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)
          ≤ ∫⁻ u in Wsh t S U x, (n : ENNReal) ∂(ν x) :=
            MeasureTheory.lintegral_mono (fun u => by simp only [hgn]; exact inf_le_right)
        _ = (n : ENNReal) * ν x (Wsh t S U x) := MeasureTheory.setLIntegral_const (Wsh t S U x) (n : ENNReal)
    exact ne_of_lt (lt_of_le_of_lt hAle
      (ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) (lt_top_iff_ne_top.mpr hd.2)))
  -- the bounded case
  have hbdd : ∀ n, ∫⁻ x, (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) ∂μ
      = ∫⁻ x, gn n x ∂μ := by
    intro n
    have hfin : (∫⁻ x, gn n x ∂μ) ≠ ⊤ := by
      have hb : ∫⁻ x, gn n x ∂μ ≤ (n : ENNReal) := by
        calc ∫⁻ x, gn n x ∂μ ≤ ∫⁻ x, (n : ENNReal) ∂μ :=
              MeasureTheory.lintegral_mono (f := gn n) (g := fun _ => (n : ENNReal))
                (fun x => by simp only [hgn]; exact inf_le_right)
          _ = (n : ENNReal) := by rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
      exact ne_of_lt (lt_of_le_of_lt hb (ENNReal.natCast_lt_top n))
    have hne : (∫⁻ x, ENNReal.ofReal (condExp (betaAlg t S) μ (hn n) x) ∂μ) ≠ ⊤ := by
      have hint : Integrable (hn n) μ :=
        Integrable.of_bound (hhn_meas n).aestronglyMeasurable (n : ℝ)
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hhn_nonneg n x)]
            exact hhn_le n x)
      have hb : ∫⁻ x, ENNReal.ofReal (condExp (betaAlg t S) μ (hn n) x) ∂μ ≤ (n : ENNReal) := by
        calc ∫⁻ x, ENNReal.ofReal (condExp (betaAlg t S) μ (hn n) x) ∂μ
            = ∫⁻ x, (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) ∂μ :=
              (MeasureTheory.lintegral_congr_ae (hae n)).symm
          _ ≤ ∫⁻ x, (n : ENNReal) ∂μ := by
              refine MeasureTheory.lintegral_mono_ae ?_
              filter_upwards [hden] with x hd
              rw [ENNReal.div_le_iff hd.1 hd.2]
              calc ∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)
                  ≤ ∫⁻ u in Wsh t S U x, (n : ENNReal) ∂(ν x) :=
                    MeasureTheory.lintegral_mono fun u => by simp only [hgn]; exact inf_le_right
                _ = (n : ENNReal) * ν x (Wsh t S U x) := MeasureTheory.setLIntegral_const _ _
          _ = (n : ENNReal) := by rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
      exact ne_of_lt (lt_of_le_of_lt hb (ENNReal.natCast_lt_top n))
    calc ∫⁻ x, (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) ∂μ
        = ∫⁻ x, ENNReal.ofReal (condExp (betaAlg t S) μ (hn n) x) ∂μ :=
          MeasureTheory.lintegral_congr_ae (hae n)
      _ = ENNReal.ofReal (∫ x, condExp (betaAlg t S) μ (hn n) x ∂μ) := by
          rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
            (condExp_nonneg (m := betaAlg t S) (μ := μ) (f := hn n)
              (Filter.Eventually.of_forall fun y => hhn_nonneg n y))
            (aestronglyMeasurable_condExp (μ := μ) (m := betaAlg t S) (f := hn n))]
          rw [ENNReal.ofReal_toReal hne]
      _ = ENNReal.ofReal (∫ x, hn n x ∂μ) := by
          rw [MeasureTheory.integral_condExp hβborel]
      _ = ENNReal.ofReal ((∫⁻ x, gn n x ∂μ).toReal) := by
          congr 1
          rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
            (Filter.Eventually.of_forall fun x => hhn_nonneg n x)
            (hhn_meas n).aestronglyMeasurable]
          congr 1
          exact MeasureTheory.lintegral_congr fun x => hofReal_hn n x
      _ = ∫⁻ x, gn n x ∂μ := ENNReal.ofReal_toReal hfin
  -- pass to the limit
  have hsup : ∀ x : X3, (⨆ n, gn n x) = g x := by
    intro x
    refine le_antisymm (iSup_le fun n => by simp only [hgn]; exact inf_le_left) ?_
    rcases eq_or_ne (g x) ⊤ with h | h
    · refine le_of_eq ?_
      rw [h]
      have hconst : (fun n : ℕ => gn n x) = fun n : ℕ => ((n : ℕ) : ENNReal) := by
        funext n
        rw [show gn n x = g x ⊓ ((n : ℕ) : ENNReal) from rfl, h, top_inf_eq]
      rw [hconst, ENNReal.iSup_natCast]
    · obtain ⟨n, hn⟩ := exists_nat_gt (g x).toReal
      refine le_iSup_of_le n ?_
      rw [show gn n x = g x ⊓ ((n : ℕ) : ENNReal) from rfl]
      refine le_inf le_rfl ?_
      rw [show ((n : ℕ) : ENNReal) = ENNReal.ofReal (n : ℝ) by simp,
        ENNReal.le_ofReal_iff_toReal_le h (by positivity)]
      exact le_of_lt hn
  have hshapeavg : ∀ x : X3, (∫⁻ u in Wsh t S U x, g (u • x) ∂(ν x)) / (ν x (Wsh t S U x))
      = ⨆ n, (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) := by
    intro x
    rw [← ENNReal.iSup_div]
    congr 1
    have h1 : (∫⁻ u in Wsh t S U x, g (u • x) ∂(ν x))
        = ∫⁻ u in Wsh t S U x, (⨆ n, gn n (u • x)) ∂(ν x) :=
      MeasureTheory.lintegral_congr fun u => (hsup (u • x)).symm
    rw [h1]
    rw [MeasureTheory.lintegral_iSup (f := fun (n : ℕ) (u : SL3) => gn n (u • x))
      (fun n => (hgn_meas n).comp (continuous_id.smul continuous_const).measurable)
      (fun m n hmn => fun u : SL3 => hgmono hmn (u • x))]
  have haemeas : ∀ n, AEMeasurable
      (fun x : X3 => (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x))) μ := by
    intro n
    refine AEMeasurable.congr
      (f := fun x : X3 => ENNReal.ofReal (condExp (betaAlg t S) μ (hn n) x)) ?_ ?_
    · exact ((aestronglyMeasurable_condExp (μ := μ) (m := betaAlg t S) (f := hn n)).aemeasurable).ennreal_ofReal
    · filter_upwards [hae n] with x hx
      exact hx.symm
  have hmonoae : ∀ᵐ x ∂μ, Monotone
      (fun n => (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x))) := by
    refine Filter.Eventually.of_forall fun x m n hmn => ?_
    refine ENNReal.div_le_div_right ?_ _
    exact MeasureTheory.lintegral_mono fun u => hgmono hmn (u • x)
  calc ∫⁻ x, (∫⁻ u in Wsh t S U x, g (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) ∂μ
      = ∫⁻ x, ⨆ n, (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) ∂μ :=
        MeasureTheory.lintegral_congr hshapeavg
    _ = ⨆ n, ∫⁻ x, (∫⁻ u in Wsh t S U x, gn n (u • x) ∂(ν x)) / (ν x (Wsh t S U x)) ∂μ :=
        lintegral_iSup' haemeas hmonoae
    _ = ⨆ n, ∫⁻ x, gn n x ∂μ := by rw [funext hbdd]
    _ = ∫⁻ x, g x ∂μ := by
        rw [MeasureTheory.lintegral_congr (g := fun x : X3 => ⨆ n, gn n x)
          (fun x => (hsup x).symm), MeasureTheory.lintegral_iSup hgn_meas hgmono]

end Work.EKLC6Core

end
