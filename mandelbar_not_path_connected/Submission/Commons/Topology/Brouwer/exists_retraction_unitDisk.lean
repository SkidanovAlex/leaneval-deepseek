import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Topology.Brouwer

open scoped RealInnerProductSpace

/-- Expansion of `normSq` of `z + t•d` for a real scalar `t`. -/
private lemma normSq_add_mul_real (z d : ℂ) (t : ℝ) :
    Complex.normSq (z + (t : ℂ) * d) =
      Complex.normSq z + 2 * t * ((starRingEnd ℂ z * d).re) + t ^ 2 * Complex.normSq d := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Real part of `conj z * (z - fz)` in terms of `normSq`. -/
private lemma conj_mul_sub_re (z fz : ℂ) :
    (starRingEnd ℂ z * (z - fz)).re = Complex.normSq z - (starRingEnd ℂ z * fz).re := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The nonnegative root of the quadratic `A t² + 2 c t - B = 0`, given in closed form. -/
private lemma quad_root (c A B t : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (ht : t = (Real.sqrt (c ^ 2 + A * B) - c) / A) :
    A * t ^ 2 + 2 * c * t - B = 0 := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hnn : 0 ≤ c ^ 2 + A * B := by positivity
  have hsq : (Real.sqrt (c ^ 2 + A * B)) ^ 2 = c ^ 2 + A * B := Real.sq_sqrt hnn
  rw [ht]
  field_simp
  nlinarith [hsq]

/-- A continuous self-map of the closed unit disk in `ℂ` without fixed points yields a
retraction of the disk onto its boundary circle: a continuous map from the disk to the
sphere that fixes the sphere pointwise.  (Explicit formula: from `f z` shoot the ray
through `z` to the boundary.) -/
theorem exists_retraction_unitDisk (f : C(Metric.closedBall (0 : ℂ) 1, Metric.closedBall (0 : ℂ) 1))
    (hf : ∀ x, f x ≠ x) :
    ∃ ρ : C(Metric.closedBall (0 : ℂ) 1, Metric.sphere (0 : ℂ) 1),
      ∀ (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) 1) (hz1 : z ∈ Metric.sphere (0:ℂ) 1),
        ρ ⟨z, hz⟩ = ⟨z, hz1⟩ := by
  let D := Metric.closedBall (0 : ℂ) 1
  let zf : D → ℂ := fun x => (x : ℂ)
  let ff : D → ℂ := fun x => ((f x : D) : ℂ)
  let df : D → ℂ := fun x => zf x - ff x
  let cf : D → ℝ := fun x => (starRingEnd ℂ (zf x) * df x).re
  let Af : D → ℝ := fun x => Complex.normSq (df x)
  let Bf : D → ℝ := fun x => 1 - Complex.normSq (zf x)
  let tf : D → ℝ := fun x => (Real.sqrt (cf x ^ 2 + Af x * Bf x) - cf x) / Af x
  let φ : D → ℂ := fun x => zf x + (tf x : ℂ) * df x
  have hzf : Continuous zf := continuous_subtype_val
  have hff : Continuous ff := by
    simpa only [ff] using Continuous.subtype_val f.continuous
  have hdf : Continuous df := hzf.sub hff
  have hcf : Continuous cf := by
    change Continuous (fun x : D => (starRingEnd ℂ (zf x) * df x).re)
    exact Complex.continuous_re.comp ((Complex.continuous_conj.comp hzf).mul hdf)
  have hAf : Continuous Af := by
    change Continuous (fun x : D => Complex.normSq (df x))
    exact Complex.continuous_normSq.comp hdf
  have hBf : Continuous Bf := by
    change Continuous (fun x : D => 1 - Complex.normSq (zf x))
    exact continuous_const.sub (Complex.continuous_normSq.comp hzf)
  have hdf_ne : ∀ x : D, df x ≠ 0 := by
    intro x h
    apply hf x
    apply Subtype.ext
    have h' : (x : ℂ) - ((f x : D) : ℂ) = 0 := by simpa only [df, zf, ff] using h
    exact (sub_eq_zero.mp h').symm
  have hAne : ∀ x : D, Af x ≠ 0 := by
    intro x h
    have h' : Complex.normSq (df x) = 0 := by simpa only [Af] using h
    exact hdf_ne x (Complex.normSq_eq_zero.mp h')
  have hApos : ∀ x : D, 0 < Af x := by
    intro x
    exact lt_of_le_of_ne (Complex.normSq_nonneg (df x)) (Ne.symm (hAne x))
  have hBnonneg : ∀ x : D, 0 ≤ Bf x := by
    intro x
    have hle : ‖zf x‖ ≤ 1 := by
      simpa only [zf] using mem_closedBall_zero_iff.mp x.2
    have hsq : Complex.normSq (zf x) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [hle, norm_nonneg (zf x)]
    simpa only [Bf] using sub_nonneg.mpr hsq
  have htf : Continuous tf := by
    change Continuous (fun x : D => (Real.sqrt (cf x ^ 2 + Af x * Bf x) - cf x) / Af x)
    exact ((Real.continuous_sqrt.comp ((hcf.pow 2).add (hAf.mul hBf))).sub hcf).div hAf hAne
  have hφ : Continuous φ := by
    change Continuous (fun x : D => zf x + (tf x : ℂ) * df x)
    exact hzf.add ((Complex.continuous_ofReal.comp htf).mul hdf)
  have hmem : ∀ x : D, φ x ∈ Metric.sphere (0 : ℂ) 1 := by
    intro x
    rw [mem_sphere_zero_iff_norm]
    have hq : Af x * (tf x) ^ 2 + 2 * cf x * tf x - Bf x = 0 :=
      quad_root (cf x) (Af x) (Bf x) (tf x) (hApos x) (hBnonneg x) rfl
    have hns : Complex.normSq (φ x) = 1 := by
      have hval : φ x = zf x + (tf x : ℂ) * df x := by simp only [φ]
      rw [hval, normSq_add_mul_real]
      simp only [cf, Af, Bf] at hq ⊢
      nlinarith [hq]
    have h2 : ‖φ x‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]; exact hns
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact h
    · have := norm_nonneg (φ x); rw [h] at this; norm_num at this
  have hfix : ∀ x : D, ‖zf x‖ = 1 → φ x = zf x := by
    intro x hx1
    have hff_le : ‖ff x‖ ≤ 1 := by
      simpa only [ff] using mem_closedBall_zero_iff.mp (f x).2
    have hbound : (starRingEnd ℂ (zf x) * ff x).re ≤ 1 := by
      have h1 : (starRingEnd ℂ (zf x) * ff x).re ≤ ‖starRingEnd ℂ (zf x) * ff x‖ :=
        Complex.re_le_norm _
      rw [norm_mul, Complex.norm_conj, hx1, one_mul] at h1
      linarith
    have hcf_nonneg : 0 ≤ cf x := by
      have heq : cf x = Complex.normSq (zf x) - (starRingEnd ℂ (zf x) * ff x).re := by
        simpa only [cf, df] using conj_mul_sub_re (zf x) (ff x)
      have hzsq : Complex.normSq (zf x) = 1 := by
        rw [Complex.normSq_eq_norm_sq, hx1]; norm_num
      rw [heq, hzsq]; linarith
    have hBf0 : Bf x = 0 := by
      have : Complex.normSq (zf x) = 1 := by rw [Complex.normSq_eq_norm_sq, hx1]; norm_num
      simp only [Bf]; rw [this]; ring
    have htf0 : tf x = 0 := by
      simp only [tf]
      rw [hBf0, mul_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg hcf_nonneg, sub_self,
        zero_div]
    have hφx : φ x = zf x + (tf x : ℂ) * df x := by simp only [φ]
    rw [hφx, htf0]; simp
  refine ⟨⟨fun x => ⟨φ x, hmem x⟩, hφ.subtype_mk hmem⟩, ?_⟩
  intro z hz hz1
  apply Subtype.ext
  have hz1' : ‖zf ⟨z, hz⟩‖ = 1 := by
    simpa only [zf] using mem_sphere_zero_iff_norm.mp hz1
  simpa only [ContinuousMap.coe_mk] using hfix ⟨z, hz⟩ hz1'

end Commons.Topology.Brouwer
