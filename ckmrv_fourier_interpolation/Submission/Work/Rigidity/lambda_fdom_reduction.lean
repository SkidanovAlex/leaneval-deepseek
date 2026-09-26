/-
# Reduction to the fundamental domain of `Γ(2)`

Every point of the upper half plane is `Γ(2)`-equivalent to a point of the closed fundamental
domain `FDom = {τ | |Re τ| ≤ 1, ‖τ‖² ≥ |Re τ|}`.

Two classical observations do the work.

* The imaginary part of `γ • τ = (a τ + b)/(c τ + d)` is `Im τ / ‖c τ + d‖²`, and the
  denominator depends only on the bottom row `(c, d)` of `γ`.  Since the set of bottom rows
  `(c, d)` for which `‖c τ + d‖ ≤ 1` is finite -- equivalently, `(c, d) ↦ ‖c τ + d‖` is proper
  (Mathlib: `ModularGroup.tendsto_normSq_coprime_pair`) -- the imaginary part attains a
  maximum on the `Γ(2)`-orbit of `τ`.
* Take `γ₀` maximizing `Im`, and move the real part into `[-1, 1]` with the translation
  `[[1, 2k], [0, 1]] ∈ Γ(2)`.  If the resulting point `z = x + iy` satisfied `x² + y² < |x|`,
  then applying `[[1, 0], [2, 1]]` (for `x < 0`) or `[[1, 0], [-2, 1]]` (for `x > 0`) -- both in
  `Γ(2)` -- would strictly increase the imaginary part: in the two cases
  `‖2z ± 1‖² = 4 (x² + y² ∓ x) + 1 < 1`, so that `Im (δ • z) = Im z / ‖2z ± 1‖² > Im z`.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaFiberDefs

namespace Work.Rigidity

open UpperHalfPlane ModularGroup Matrix Filter
open scoped MatrixGroups

noncomputable section

/-! ## The squared norm of the denominator of `γ` -/

/-- `bq γ τ = ‖c τ + d‖²` for the bottom row `(c, d)` of `γ`.  By
`ModularGroup.im_smul_eq_div_normSq`, this is the denominator in `Im (γ • τ) = Im τ / bq γ τ`. -/
def bq (γ : SL(2,ℤ)) (τ : ℍ) : ℝ := Complex.normSq ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ))

lemma fdom_im_smul_eq (γ : SL(2,ℤ)) (τ : ℍ) : (γ • τ).im = τ.im / bq γ τ := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  simp only [bq]

lemma fdom_bq_pos (γ : SL(2,ℤ)) (τ : ℍ) : 0 < bq γ τ := by
  have h := normSq_denom_pos γ τ.im_ne_zero
  rw [ModularGroup.denom_apply] at h
  simpa only [bq] using h

lemma fdom_bq_eA (k : ℤ) (τ : ℍ) : bq (eA k) τ = 1 := by
  simp [bq, eA]

lemma fdom_bq_eB (k : ℤ) (τ : ℍ) :
    bq (eB k) τ = Complex.normSq (2*(k:ℂ)*(τ:ℂ) + 1) := by
  simp [bq, eB]

/-! ## The imaginary part is maximized on the `Γ(2)`-orbit -/

/-- **The imaginary part attains its maximum on the `Γ(2)`-orbit.**  Only the bottom row of `γ`
enters `Im (γ • τ)`, and the bottom rows with `‖c τ + d‖ ≤ 1` are finite. -/
lemma fdom_exists_max_im_gamma2 (τ : ℍ) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, ∀ γ' ∈ CongruenceSubgroup.Gamma 2,
      (γ' • τ).im ≤ (γ • τ).im := by
  let f : (Fin 2 → ℤ) → ℝ := fun p => Complex.normSq ((p 0 : ℂ) * (τ : ℂ) + (p 1 : ℂ))
  let S : Set (Fin 2 → ℤ) := {p | (∃ g ∈ CongruenceSubgroup.Gamma 2, g 1 = p) ∧ f p ≤ 1}
  have hne : S.Nonempty := by
    refine ⟨![0,1], ⟨1, one_mem _, ?_⟩, ?_⟩
    · ext i; fin_cases i <;> simp
    · simp [f]
  obtain ⟨p₀, hp₀S, hmin⟩ := (tendsto_normSq_coprime_pair τ).exists_within_forall_le hne
  obtain ⟨γ₀, hγ₀mem, hp₀row⟩ := hp₀S.1
  refine ⟨γ₀, hγ₀mem, fun γ' hγ' => ?_⟩
  have hf' : f (γ' 1) = bq γ' τ := by simp only [f, bq]
  have hf₀ : f p₀ = bq γ₀ τ := by rw [← hp₀row]; simp only [f, bq]
  rw [fdom_im_smul_eq, fdom_im_smul_eq]
  by_cases hcase : f (γ' 1) ≤ 1
  · have hle : f p₀ ≤ f (γ' 1) := hmin (γ' 1) ⟨⟨γ', hγ', rfl⟩, hcase⟩
    rw [hf', hf₀] at hle
    rw [div_le_div_iff_of_pos_left τ.im_pos (fdom_bq_pos γ' τ) (fdom_bq_pos γ₀ τ)]
    exact hle
  · have hlt : 1 < f (γ' 1) := lt_of_not_ge hcase
    rw [hf'] at hlt
    have h1 : τ.im / bq γ' τ < τ.im := by
      rw [div_lt_iff₀ (fdom_bq_pos γ' τ)]; nlinarith [τ.im_pos]
    have h2 : τ.im ≤ τ.im / bq γ₀ τ := by
      rw [le_div_iff₀ (fdom_bq_pos γ₀ τ)]
      have : bq γ₀ τ ≤ 1 := by rw [← hf₀]; exact hp₀S.2
      nlinarith [τ.im_pos, this]
    linarith

/-! ## The translation `[[1, 2k], [0, 1]]` -/

lemma fdom_eA_smul_coe (k : ℤ) (z : ℍ) : (((eA k) • z : ℍ) : ℂ) = (z : ℂ) + (2*k : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [eA]

lemma fdom_eA_smul_re (k : ℤ) (z : ℍ) : ((eA k) • z).re = z.re + 2*k := by
  rw [← UpperHalfPlane.coe_re, fdom_eA_smul_coe]
  simp [UpperHalfPlane.coe_re, Complex.add_re]

lemma fdom_eA_smul_im (k : ℤ) (z : ℍ) : ((eA k) • z).im = z.im := by
  rw [← UpperHalfPlane.coe_im, fdom_eA_smul_coe]
  simp [UpperHalfPlane.coe_im, Complex.add_im]

/-- Any real number can be moved into `[-1, 1]` by an even integer translation. -/
lemma fdom_exists_abs_add_two_mul_le_one (x : ℝ) : ∃ k : ℤ, |x + 2*k| ≤ 1 := by
  refine ⟨⌈(-1 - x)/2⌉, ?_⟩
  have h1 : (-1 - x)/2 ≤ ((⌈(-1 - x)/2⌉ : ℤ) : ℝ) := Int.le_ceil _
  have h2 : ((⌈(-1 - x)/2⌉ : ℤ) : ℝ) < (-1 - x)/2 + 1 := Int.ceil_lt_add_one _
  rw [abs_le]
  constructor <;> linarith

/-! ## The two imaginary-part-increasing shears -/

lemma fdom_im_smul_eB_one (z : ℍ) :
    ((eB 1) • z).im = z.im / Complex.normSq (2*(z:ℂ) + 1) := by
  rw [fdom_im_smul_eq, fdom_bq_eB]
  rw [show (2 * ((1:ℤ):ℂ) * (z:ℂ) + 1) = 2*(z:ℂ) + 1 from by push_cast; ring]

lemma fdom_im_smul_eB_neg_one (z : ℍ) :
    ((eB (-1)) • z).im = z.im / Complex.normSq (1 - 2*(z:ℂ)) := by
  rw [fdom_im_smul_eq, fdom_bq_eB]
  rw [show (2 * ((-1:ℤ):ℂ) * (z:ℂ) + 1) = 1 - 2*(z:ℂ) from by push_cast; ring]

lemma fdom_normSq_two_mul_add_one_pos (z : ℍ) : 0 < Complex.normSq (2*(z:ℂ) + 1) := by
  rw [Complex.normSq_pos]
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith [z.im_pos]

lemma fdom_normSq_one_sub_two_mul_pos (z : ℍ) : 0 < Complex.normSq (1 - 2*(z:ℂ)) := by
  rw [Complex.normSq_pos]
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith [z.im_pos]

/-- If `x = Re z < 0` and `‖z‖² < |x|` then the shear `[[1, 0], [2, 1]]` increases `Im`. -/
lemma fdom_normSq_two_mul_add_one_lt_one (z : ℍ) (h : Complex.normSq (z:ℂ) < |z.re|)
    (hx : z.re < 0) : Complex.normSq (2*(z:ℂ) + 1) < 1 := by
  have hx' : Complex.normSq (z:ℂ) < -z.re := by rwa [abs_of_neg hx] at h
  have h1 : Complex.normSq ((z:ℂ)) = z.re^2 + z.im^2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
  have h2 : Complex.normSq (2*(z:ℂ) + 1) = (2*z.re + 1)^2 + (2*z.im)^2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [h1] at hx'
  rw [h2]
  nlinarith [z.im_pos]

/-- If `x = Re z > 0` and `‖z‖² < |x|` then the shear `[[1, 0], [-2, 1]]` increases `Im`. -/
lemma fdom_normSq_one_sub_two_mul_lt_one (z : ℍ) (h : Complex.normSq (z:ℂ) < |z.re|)
    (hx : 0 < z.re) : Complex.normSq (1 - 2*(z:ℂ)) < 1 := by
  have hx' : Complex.normSq (z:ℂ) < z.re := by rwa [abs_of_pos hx] at h
  have h1 : Complex.normSq ((z:ℂ)) = z.re^2 + z.im^2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
  have h2 : Complex.normSq (1 - 2*(z:ℂ)) = (1 - 2*z.re)^2 + (2*z.im)^2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [h1] at hx'
  rw [h2]
  nlinarith [z.im_pos]

lemma fdom_lt_div_of_lt_one {y q : ℝ} (hy : 0 < y) (hq : 0 < q) (hq1 : q < 1) :
    y < y / q := by
  rw [lt_div_iff₀ hq]
  nlinarith

/-- The shear `[[1, 0], [2, 1]] ∈ Γ(2)` strictly increases the imaginary part of a point
`z` with `Re z < 0` and `‖z‖² < |Re z|`. -/
lemma fdom_im_smul_eB_one_gt (z : ℍ) (h : Complex.normSq (z:ℂ) < |z.re|) (hx : z.re < 0) :
    z.im < ((eB 1) • z).im := by
  rw [fdom_im_smul_eB_one]
  exact fdom_lt_div_of_lt_one z.im_pos (fdom_normSq_two_mul_add_one_pos z)
    (fdom_normSq_two_mul_add_one_lt_one z h hx)

/-- The shear `[[1, 0], [-2, 1]] ∈ Γ(2)` strictly increases the imaginary part of a point
`z` with `Re z > 0` and `‖z‖² < |Re z|`. -/
lemma fdom_im_smul_eB_neg_one_gt (z : ℍ) (h : Complex.normSq (z:ℂ) < |z.re|) (hx : 0 < z.re) :
    z.im < ((eB (-1)) • z).im := by
  rw [fdom_im_smul_eB_neg_one]
  exact fdom_lt_div_of_lt_one z.im_pos (fdom_normSq_one_sub_two_mul_pos z)
    (fdom_normSq_one_sub_two_mul_lt_one z h hx)

/-! ## The reduction -/

/-- **Reduction to the fundamental domain.**  Every point of `ℍ` is `Γ(2)`-equivalent to a
point of the closed fundamental domain `FDom = {|Re τ| ≤ 1, ‖τ‖² ≥ |Re τ|}`. -/
theorem lambda_fdom_reduction (τ : UpperHalfPlane) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ ∈ Work.Rigidity.FDom := by
  obtain ⟨γ₀, hγ₀mem, hmax⟩ := fdom_exists_max_im_gamma2 τ
  obtain ⟨k, hk⟩ := fdom_exists_abs_add_two_mul_le_one (γ₀ • τ).re
  refine ⟨eA k * γ₀, mul_mem (eA_mem_Gamma k) hγ₀mem, ?_⟩
  rw [mul_smul]
  set z : ℍ := eA k • (γ₀ • τ) with hzdef
  have hzre : z.re = (γ₀ • τ).re + 2*k := by rw [hzdef]; exact fdom_eA_smul_re k (γ₀ • τ)
  have hzim : z.im = (γ₀ • τ).im := by rw [hzdef]; exact fdom_eA_smul_im k (γ₀ • τ)
  have hmaxz : ∀ γ' ∈ CongruenceSubgroup.Gamma 2, (γ' • τ).im ≤ z.im := by
    intro γ' hγ'; rw [hzim]; exact hmax γ' hγ'
  refine ⟨?_, ?_⟩
  · show |(z : ℂ).re| ≤ 1
    rw [UpperHalfPlane.coe_re, hzre]
    exact hk
  · show ‖(z : ℂ)‖ ^ 2 ≥ |(z : ℂ).re|
    rw [UpperHalfPlane.coe_re]
    by_contra hcon
    simp only [ge_iff_le, not_le] at hcon
    rw [← Complex.normSq_eq_norm_sq] at hcon
    have hxne : z.re ≠ 0 := by
      intro h
      rw [h, abs_zero] at hcon
      linarith [Complex.normSq_nonneg (z : ℂ)]
    rcases lt_or_gt_of_ne hxne with hneg | hpos
    · -- `Re z < 0`: the shear `[[1, 0], [2, 1]]` increases the imaginary part
      have hlt : z.im < ((eB 1) • z).im := fdom_im_smul_eB_one_gt z hcon hneg
      have hle : ((eB 1) • z).im ≤ z.im := by
        have h1 := hmaxz (eB 1 * (eA k * γ₀))
          (mul_mem (eB_mem_Gamma 1) (mul_mem (eA_mem_Gamma k) hγ₀mem))
        rw [mul_smul, mul_smul, ← hzdef] at h1
        exact h1
      linarith
    · -- `Re z > 0`: the shear `[[1, 0], [-2, 1]]` increases the imaginary part
      have hlt : z.im < ((eB (-1)) • z).im := fdom_im_smul_eB_neg_one_gt z hcon hpos
      have hle : ((eB (-1)) • z).im ≤ z.im := by
        have h1 := hmaxz (eB (-1) * (eA k * γ₀))
          (mul_mem (eB_mem_Gamma (-1)) (mul_mem (eA_mem_Gamma k) hγ₀mem))
        rw [mul_smul, mul_smul, ← hzdef] at h1
        exact h1
      linarith

end

end Work.Rigidity
