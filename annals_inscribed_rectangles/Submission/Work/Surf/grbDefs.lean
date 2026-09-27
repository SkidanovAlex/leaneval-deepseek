import Mathlib
import Submission.Work.Surf.defs
import Submission.Work.Drive.Surf.Model
import Submission.Work.Drive.ParityDegreeDefs
import Submission.Work.Drive.CrossingDefs

/-!
# Preliminaries for `Work.Surf.exists_good_ray_boundary_odd`

The coordinate identification `gEu : 𝔼² → ℝ × ℝ` between `EuclideanSpace ℝ (Fin 2)` and the product
model in which the winding-number machinery lives, and the *honest* direction `gDir z = arg z / 2π`
of a nonzero plane vector, with the fundamental fact that two nonzero vectors have the same honest
direction exactly when they are positive multiples of each other.

These are private copies (in the namespace `Work.Surf.GRB`) of results that other agents are
developing in parallel elsewhere in the workspace; duplicating them keeps this development
independent of files under construction.
-/

namespace Work.Surf.GRB

open Set

noncomputable section

/-! ## The coordinate identification -/

/-- The coordinate identification `𝔼² → ℝ × ℝ`, as a continuous linear map. -/
noncomputable def gEu : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).prod (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))

lemma gEu_apply (x : EuclideanSpace ℝ (Fin 2)) : gEu x = (x 0, x 1) := rfl

/-- The inverse coordinate identification. -/
noncomputable def gEuInv (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p.1, p.2]

@[simp] lemma gEuInv_apply_zero (p : ℝ × ℝ) : (gEuInv p) 0 = p.1 := rfl

@[simp] lemma gEuInv_apply_one (p : ℝ × ℝ) : (gEuInv p) 1 = p.2 := rfl

lemma gEu_gEuInv (p : ℝ × ℝ) : gEu (gEuInv p) = p := by
  rw [gEu_apply]
  ext <;> simp [gEuInv]

lemma gEuInv_gEu (x : EuclideanSpace ℝ (Fin 2)) : gEuInv (gEu x) = x := by
  rw [gEu_apply]
  ext i
  fin_cases i <;> simp [gEuInv]

lemma gEu_injective : Function.Injective gEu := fun x y h => by
  have h2 : gEuInv (gEu x) = gEuInv (gEu y) := congrArg gEuInv h
  rwa [gEuInv_gEu, gEuInv_gEu] at h2

lemma gEu_eq_iff {x y : EuclideanSpace ℝ (Fin 2)} : gEu x = gEu y ↔ x = y :=
  ⟨fun h => gEu_injective h, fun h => by rw [h]⟩

/-- The cross product in the two models: same formula. -/
lemma gCross_eu (x y : EuclideanSpace ℝ (Fin 2)) :
    Work.Drive.cross2 (gEu x) (gEu y) = Work.Drive.det2 x y := by
  rw [gEu_apply, gEu_apply]
  simp [Work.Drive.cross2, Work.Drive.det2]

/-- The derivative commutes with the coordinate identification. -/
lemma gDeriv_eu {a : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a) (s : ℝ) :
    deriv (fun t => gEu (a t)) s = gEu (deriv a s) := by
  have hd : DifferentiableAt ℝ a s := (ha.differentiable (by norm_num)).differentiableAt
  have h1 : fderiv ℝ (fun t => gEu (a t)) s = gEu.comp (fderiv ℝ a s) := by
    rw [show (fun t => gEu (a t)) = gEu ∘ a from rfl]
    rw [fderiv_comp s gEu.differentiableAt hd, ContinuousLinearMap.fderiv]
  rw [deriv, deriv, h1]
  simp [ContinuousLinearMap.comp_apply]

lemma gEu_mem_sqBox {x : EuclideanSpace ℝ (Fin 2)} :
    gEu x ∈ Work.Drive.sqBox ↔ x ∈ sqBox := by
  rw [gEu_apply]; rfl

lemma gEu_mem_sqBoxBdry {x : EuclideanSpace ℝ (Fin 2)} :
    gEu x ∈ Work.Drive.sqBoxBdry ↔ x ∈ sqBdry := by
  rw [gEu_apply]; rfl

/-! ## The honest direction -/

/-- The complexification of a plane vector (the product model). -/
def gToC (z : ℝ × ℝ) : ℂ := ⟨z.1, z.2⟩

lemma gToC_add (z z' : ℝ × ℝ) : gToC (z + z') = gToC z + gToC z' := by
  apply Complex.ext <;> simp [gToC, Complex.add_re, Complex.add_im]

lemma gToC_sub (z z' : ℝ × ℝ) : gToC (z - z') = gToC z - gToC z' := by
  apply Complex.ext <;> simp [gToC, Complex.sub_re, Complex.sub_im]

lemma gToC_smul (r : ℝ) (z : ℝ × ℝ) : gToC (r • z) = r * gToC z := by
  apply Complex.ext <;> simp [gToC, Complex.mul_re, Complex.mul_im] <;> ring

lemma gToC_eq_zero_iff {z : ℝ × ℝ} : gToC z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h1 : z.1 = 0 := by have := congrArg Complex.re h; simpa [gToC] using this
    have h2 : z.2 = 0 := by have := congrArg Complex.im h; simpa [gToC] using this
    exact Prod.ext h1 h2
  · intro h; rw [h]; rfl

lemma gToC_ne_zero_iff {z : ℝ × ℝ} : gToC z ≠ 0 ↔ z ≠ 0 :=
  not_congr gToC_eq_zero_iff

lemma gToC_injective : Function.Injective gToC := by
  intro z z' h
  have h1 : gToC (z - z') = 0 := by rw [gToC_sub, h, sub_self]
  exact sub_eq_zero.mp (gToC_eq_zero_iff.mp h1)

/-- The rescaling homeomorphism `ℝ/2πℤ → ℝ/ℤ`, `x ↦ x / 2π`. -/
noncomputable def gRescale : Real.Angle ≃ₜ UnitAddCircle :=
  AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero

lemma gRescale_apply_mk (x : ℝ) :
    gRescale ((x : ℝ) : Real.Angle) = ((x / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
  change (AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero)
      ((x : ℝ) : AddCircle (2 * Real.pi)) = _
  rw [AddCircle.homeomorphAddCircle_apply_mk]
  congr 1
  rw [mul_one, div_eq_mul_inv]

/-- The honest direction `arg z / 2π ∈ ℝ/ℤ` of a plane vector. -/
noncomputable def gDir (z : ℝ × ℝ) : UnitAddCircle :=
  ((Complex.arg (gToC z) / (2 * Real.pi) : ℝ) : UnitAddCircle)

lemma gDir_eq_rescale (z : ℝ × ℝ) :
    gDir z = gRescale ((Complex.arg (gToC z) : ℝ) : Real.Angle) := by
  rw [gDir, gRescale_apply_mk]

lemma gToC_continuous : Continuous gToC := by
  have h : Continuous fun z : ℝ × ℝ => (z.1 : ℂ) + (z.2 : ℂ) * Complex.I := by fun_prop
  refine h.congr (fun z => ?_)
  apply Complex.ext <;> simp [gToC]

lemma gContinuousAt_gDir {z : ℝ × ℝ} (hz : z ≠ 0) : ContinuousAt gDir z := by
  have h1 : ContinuousAt (fun y : ℝ × ℝ => ((Complex.arg (gToC y) : ℝ) : Real.Angle)) z :=
    (Complex.continuousAt_arg_coe_angle (gToC_ne_zero_iff.mpr hz)).comp gToC_continuous.continuousAt
  exact (gRescale.continuous.continuousAt.comp h1).congr
    (Filter.Eventually.of_forall (fun y => (gDir_eq_rescale y).symm))

/-- **The honest direction determines the ray.** -/
theorem gDir_eq_iff {z w : ℝ × ℝ} (hz : z ≠ 0) (hw : w ≠ 0) :
    gDir z = gDir w ↔ ∃ r : ℝ, 0 < r ∧ z = r • w := by
  have hzw : gToC z ≠ 0 := gToC_ne_zero_iff.mpr hz
  have hww : gToC w ≠ 0 := gToC_ne_zero_iff.mpr hw
  have hiff : gDir z = gDir w ↔
      ((Complex.arg (gToC z) : ℝ) : Real.Angle) = ((Complex.arg (gToC w) : ℝ) : Real.Angle) := by
    rw [gDir_eq_rescale, gDir_eq_rescale, gRescale.injective.eq_iff]
  rw [hiff]
  constructor
  · intro h
    set ζ : ℂ := gToC z / gToC w with hζdef
    have hζne : ζ ≠ 0 := div_ne_zero hzw hww
    have hdiv : ((Complex.arg ζ : ℝ) : Real.Angle) = 0 := by
      rw [hζdef, Complex.arg_div_coe_angle hzw hww, h, sub_self]
    obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.mp hdiv
    rw [zsmul_eq_mul] at hn
    have hle := Complex.arg_le_pi ζ
    have hlt := Complex.neg_pi_lt_arg ζ
    have hn0 : n = 0 := by
      rcases lt_trichotomy n 0 with hneg | heq | hpos
      · exfalso
        have hn1 : (n : ℝ) ≤ -1 := by
          have : n ≤ -1 := by omega
          exact_mod_cast this
        have h2 : (n : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) := by nlinarith [Real.pi_pos]
        rw [← hn] at hlt
        linarith
      · exact heq
      · exfalso
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
          have : (1 : ℤ) ≤ n := by omega
          exact_mod_cast this
        have h2 : 1 * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) := by nlinarith [Real.pi_pos]
        rw [← hn] at hle
        linarith
    have harg0 : ζ.arg = 0 := by
      rw [hn0] at hn
      simpa using hn.symm
    obtain ⟨hre, him⟩ := Complex.arg_eq_zero_iff.mp harg0
    have hζreal : ζ = (ζ.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hratio : gToC z = (ζ.re : ℂ) * gToC w := by
      have h2 : ζ = (ζ.re : ℂ) := hζreal
      rw [hζdef, div_eq_iff hww] at h2
      exact h2
    have hre_ne : ζ.re ≠ 0 := by
      intro h0
      exact hζne (by rw [hζreal, h0]; simp)
    refine ⟨ζ.re, lt_of_le_of_ne hre (Ne.symm hre_ne), ?_⟩
    rw [← gToC_injective.eq_iff, gToC_smul]
    exact hratio
  · rintro ⟨r, hr, rfl⟩
    have harg : Complex.arg (gToC (r • w)) = Complex.arg (gToC w) := by
      rw [gToC_smul]
      exact Complex.arg_real_mul (gToC w) hr
    rw [harg]

end

end Work.Surf.GRB
