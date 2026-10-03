import Mathlib

open MeasureTheory Set intervalIntegral

namespace Work.FIChain

/-! **The mean-value extraction along a bounded measurable weight.**  If `Ψ : ℝ → ℝ` is
measurable, nonnegative, and bounded above on `[Z, e·Z]` (`Z > 0`), then some point of `[Z, e·Z]`
attains (at most) the `dz/z`-average of `Ψ`:

`∃ z₁ ∈ [Z, e·Z], Ψ z₁ ≤ ∫_Z^{eZ} Ψ z dz/z`.

This is the single-`z` extraction that the FI endgame's deviation step needs: the companion's §8
controls `S₃` only through a `z`-average, whereas the consumer needs one `z₁`.  Nothing analytic is
involved — `0 ≤ Ψ/z ≤ C/Z` on the interval makes `Ψ(·)/·` integrable there, so if `Ψ` were `> Q`
everywhere with `Q := ∫_Z^{eZ}Ψ z dz/z`, then `(Ψ − Q)/z` would be a nonnegative measurable
function, positive on the whole interval `(Z, e·Z]` of positive measure, yet with
`∫_Z^{eZ}(Ψ − Q)/z dz = Q − Q·(∫_Z^{eZ}dz/z) = 0`, contradicting positivity of the integral
(`MeasureTheory.integral_eq_zero_iff_of_nonneg_ae` / `MeasureTheory.setIntegral_pos_iff_support`).

Instantiated at `Ψ z = K + ∫_Y^{eY}|s3RemPlus(λ,x,z,sc·y,sc·z,Cₘ)|/y` (with `sc x Bstar = 2^{Jc}`,
`Cₘ = ⌊zc^{1-η}⌋`) it gives the `hS3` input of `Work.FIChain.S3avgFix_le_of_zavg` for the fixed
scale `Bstar`, since there `Ψ` is measurable by `Work.FIChain.measurable_s3halves_joint` together
with measurability of parametric integrals, and `|s3RemPlus|` is bounded by
`Work.FIChain.abs_s3RemPlus_le_crude`. -/

theorem exists_z1_le_of_measurable_zavg {Ψ : ℝ → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hmeas : Measurable Ψ) (hnn : ∀ z : ℝ, 0 ≤ Ψ z)
    (hbdd : ∃ C : ℝ, ∀ z ∈ Set.Icc Z (Real.exp 1 * Z), Ψ z ≤ C) :
    ∃ z₁ ∈ Set.Icc Z (Real.exp 1 * Z),
      Ψ z₁ ≤ ∫ z in Z..(Real.exp 1 * Z), Ψ z / z := by
  obtain ⟨C, hC⟩ := hbdd
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr Real.zero_lt_one
  have hZb : Z < Real.exp 1 * Z := by
    have h := mul_lt_mul_of_pos_right he1 hZ
    simpa using h
  have hZb_le : Z ≤ Real.exp 1 * Z := hZb.le
  set Q : ℝ := ∫ z in Z..(Real.exp 1 * Z), Ψ z / z with hQdef
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hC0 : 0 ≤ C := (hnn Z).trans (hC Z ⟨le_rfl, hZb_le⟩)
  have hmeasuro : MeasurableSet (Set.uIoc Z (Real.exp 1 * Z)) := measurableSet_uIoc
  have hfin : volume (Set.uIoc Z (Real.exp 1 * Z)) < ⊤ := by
    rw [Set.uIoc_of_le hZb_le, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have haesm : AEStronglyMeasurable (fun z : ℝ => Ψ z / z)
      (volume.restrict (Set.uIoc Z (Real.exp 1 * Z))) :=
    (hmeas.div measurable_id).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂volume.restrict (Set.uIoc Z (Real.exp 1 * Z)), ‖Ψ z / z‖ ≤ C / Z := by
    refine ae_restrict_of_forall_mem hmeasuro ?_
    intro z hz
    rw [Set.uIoc_of_le hZb_le] at hz
    have hzIcc : z ∈ Set.Icc Z (Real.exp 1 * Z) := ⟨hz.1.le, hz.2⟩
    have hzpos : 0 < z := lt_of_lt_of_le hZ hz.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hnn z), abs_of_pos hzpos]
    calc Ψ z / z = Ψ z * (1 / z) := by ring
      _ ≤ C * (1 / Z) :=
        mul_le_mul (hC z hzIcc) (one_div_le_one_div_of_le hZ hz.1.le) (by positivity) hC0
      _ = C / Z := by ring
  have hf_int : IntervalIntegrable (fun z : ℝ => Ψ z / z) volume Z (Real.exp 1 * Z) := by
    rw [intervalIntegrable_iff]
    exact IntegrableOn.of_bound hfin haesm (C / Z) hbound
  have hQmeas : AEStronglyMeasurable (fun z : ℝ => Q / z)
      (volume.restrict (Set.uIoc Z (Real.exp 1 * Z))) :=
    (measurable_const.div measurable_id).aestronglyMeasurable
  have hQbound : ∀ᵐ z ∂volume.restrict (Set.uIoc Z (Real.exp 1 * Z)), ‖Q / z‖ ≤ |Q| / Z := by
    refine ae_restrict_of_forall_mem hmeasuro ?_
    intro z hz
    rw [Set.uIoc_of_le hZb_le] at hz
    have hzpos : 0 < z := lt_of_lt_of_le hZ hz.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hzpos]
    exact div_le_div_of_nonneg_left (abs_nonneg Q) hZ hz.1.le
  have hg_int : IntervalIntegrable (fun z : ℝ => Q / z) volume Z (Real.exp 1 * Z) := by
    rw [intervalIntegrable_iff]
    exact IntegrableOn.of_bound hfin hQmeas (|Q| / Z) hQbound
  have hsub_int : IntervalIntegrable (fun z : ℝ => Ψ z / z - Q / z) volume Z (Real.exp 1 * Z) :=
    hf_int.sub hg_int
  have hg_int' : IntervalIntegrable (fun z : ℝ => (Ψ z - Q) / z) volume Z (Real.exp 1 * Z) :=
    IntervalIntegrable.congr (fun z _ => (sub_div (Ψ z) Q z).symm) hsub_int
  have hlog : ∫ z in Z..(Real.exp 1 * Z), (1 : ℝ) / z = 1 := by
    rw [integral_one_div_of_pos hZ (mul_pos (Real.exp_pos 1) hZ)]
    rw [show Real.exp 1 * Z / Z = Real.exp 1 from by
      rw [mul_div_assoc, div_self hZ.ne', mul_one]]
    exact Real.log_exp 1
  have h3 : (∫ z in Z..(Real.exp 1 * Z), Q / z) = Q := by
    calc (∫ z in Z..(Real.exp 1 * Z), Q / z)
        = Q * (∫ z in Z..(Real.exp 1 * Z), (1 : ℝ) / z) := by
          rw [← intervalIntegral.integral_const_mul Q (fun z : ℝ => (1 : ℝ) / z)]
          apply intervalIntegral.integral_congr
          intro z hz
          ring
      _ = Q := by rw [hlog, mul_one]
  have hcong : (∫ z in Z..(Real.exp 1 * Z), (fun z : ℝ => (Ψ z - Q) / z) z)
      = (∫ z in Z..(Real.exp 1 * Z), (fun z : ℝ => Ψ z / z - Q / z) z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    exact sub_div (Ψ z) Q z
  have hsub_split :
      (∫ z in Z..(Real.exp 1 * Z), (fun z : ℝ => Ψ z / z - Q / z) z)
        = (∫ z in Z..(Real.exp 1 * Z), Ψ z / z) - (∫ z in Z..(Real.exp 1 * Z), Q / z) :=
    intervalIntegral.integral_sub hf_int hg_int
  have hres : (∫ z in Z..(Real.exp 1 * Z), (fun z : ℝ => Ψ z / z - Q / z) z) = 0 := by
    rw [hsub_split, hQdef.symm, h3, sub_self]
  have hzero : (∫ z in Z..(Real.exp 1 * Z), (fun z : ℝ => (Ψ z - Q) / z) z) = 0 := by
    rw [hcong, hres]
  have hpos : 0 < (∫ z in Z..(Real.exp 1 * Z), (fun z : ℝ => (Ψ z - Q) / z) z) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hg_int' ?_ hZb
    intro z hz
    have hzIcc : z ∈ Set.Icc Z (Real.exp 1 * Z) := ⟨hz.1.le, hz.2.le⟩
    have hlt : Q < Ψ z := hcon z hzIcc
    exact div_pos (by linarith) (lt_trans hZ hz.1)
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

end Work.FIChain
