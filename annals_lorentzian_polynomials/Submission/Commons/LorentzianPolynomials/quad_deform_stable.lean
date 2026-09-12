import Mathlib
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LinearAlgebra.Matrix.perron_vector_of_nonneg_symm_card_pos_le_one_pos

open Finsupp Matrix MvPolynomial UpperHalfPlane
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Commons.LorentzianPolynomials

noncomputable section

open Commons.LinearAlgebra.Matrix

/-- The matrix of the deformed quadratic form: `A` perturbed by the operation
`θ·X_i·∂_j` (diagonal entries doubled in the Hessian convention). -/
def quadDeformMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (θ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a b => A a b + θ * (if a = i then A j b else 0) + θ * (if b = i then A a j else 0)

/-- The linear map `z ↦ z + θ·z_i·e_j` (a shear, mapping the upper half plane to itself
when `θ ≥ 0`). -/
def quadShear {n : ℕ} (i j : Fin n) (θ : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun a => x a + (if a = j then θ * x i else 0)

lemma quadShear_decomp {n : ℕ} (i j : Fin n) (θ : ℝ) (x : Fin n → ℝ) :
    quadShear i j θ x = x + (θ * x i) • evec j := by
  funext a
  by_cases ha : a = j
  · subst a
    simp [quadShear, evec]
  · simp [quadShear, evec, ha]

lemma quadReal_add_matrix {n : ℕ} (M1 M2 : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadReal (M1 + M2) x x = quadReal M1 x x + quadReal M2 x x := by
  classical
  rw [quadReal_mulVec, quadReal_mulVec, quadReal_mulVec]
  rw [Matrix.add_mulVec]
  rw [dotProduct_add]

lemma quadReal_of_if_left_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (θ : ℝ) (x : Fin n → ℝ) :
    quadReal (fun a b : Fin n => θ * (if a = p then A q b else 0)) x x =
      θ * x p * (∑ b : Fin n, A q b * x b) := by
  classical
  unfold quadReal
  dsimp
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_eq_single p]
  · simp
    ring
  · intro a ha hap
    simp [hap]
  · intro hnp
    simp at hnp

lemma quadReal_of_if_right_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n)
    (θ : ℝ) (x : Fin n → ℝ) :
    quadReal (fun a b : Fin n => θ * (if b = p then A a q else 0)) x x =
      θ * x p * (∑ a : Fin n, A a q * x a) := by
  classical
  unfold quadReal
  dsimp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single p]
  · simp
    ring
  · intro b hb hbp
    simp [hbp]
  · intro hnp
    simp at hnp

lemma quadReal_smul_right' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) :
    quadReal A x (c • y) = c * quadReal A x y := by
  rw [quadReal_mulVec A x (c • y), quadReal_mulVec A x y]
  simp [Matrix.mulVec_smul, smul_eq_mul]

lemma quadReal_smul_left' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) :
    quadReal A (c • x) y = c * quadReal A x y := by
  rw [quadReal_mulVec A (c • x) y, quadReal_mulVec A x y]
  simp [smul_eq_mul]

/-- The quadratic form of the deformed matrix is the pullback of that of `A` along the
shear, minus the `θ²·A_jj·X_i²` correction. -/
lemma quadReal_quadDeformMat_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (θ : ℝ) (x : Fin n → ℝ) :
    quadReal (quadDeformMat A i j θ) x x =
      quadReal A (quadShear i j θ x) (quadShear i j θ x) - θ ^ 2 * A j j * (x i) ^ 2 := by
  classical
  let c : ℝ := θ * x i
  have hmain : quadReal A (x + c • evec j) (x + c • evec j) =
      quadReal A x x + c * quadReal A x (evec j) +
        c * quadReal A (evec j) x + c ^ 2 * quadReal A (evec j) (evec j) := by
    rw [quadReal_add_left A x (c • evec j) (x + c • evec j)]
    rw [quadReal_add_right A x x (c • evec j)]
    rw [quadReal_add_right A (c • evec j) x (c • evec j)]
    rw [quadReal_smul_right' A c x (evec j)]
    rw [quadReal_smul_left' A c (evec j) x]
    rw [quadReal_smul_left' A c (evec j) (c • evec j)]
    rw [quadReal_smul_right' A c (evec j) (evec j)]
    ring
  have hxe : quadReal A x (evec j) = ∑ a : Fin n, A a j * x a := by
    dsimp [quadReal, evec]
    simp
  have hex : quadReal A (evec j) x = ∑ b : Fin n, A j b * x b := by
    dsimp [quadReal, evec]
    simp
  have hL : quadReal (quadDeformMat A i j θ) x x =
      quadReal A x x + θ * x i * (∑ b : Fin n, A j b * x b) +
        θ * x i * (∑ a : Fin n, A a j * x a) := by
    let M1 : Matrix (Fin n) (Fin n) ℝ := fun a b : Fin n => θ * (if a = i then A j b else 0)
    let M2 : Matrix (Fin n) (Fin n) ℝ := fun a b : Fin n => θ * (if b = i then A a j else 0)
    have hmat : quadDeformMat A i j θ = A + M1 + M2 := by
      ext a b
      unfold quadDeformMat M1 M2
      rfl
    rw [hmat]
    rw [quadReal_add_matrix, quadReal_add_matrix]
    rw [quadReal_of_if_left_mul A i j θ x]
    rw [quadReal_of_if_right_mul A i j θ x]
  rw [hL]
  rw [quadShear_decomp i j θ x]
  rw [hmain, hxe, hex, quadReal_single]
  dsimp [c]
  ring

/-- The deformed matrix is symmetric when `A` is. -/
lemma quadDeformMat_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (θ : ℝ)
    (hA : A.IsSymm) : (quadDeformMat A i j θ).IsSymm := by
  classical
  refine Matrix.IsSymm.ext ?_
  intro a b
  by_cases hai : a = i
  · by_cases hbi : b = i
    · subst a; subst b; unfold quadDeformMat; ring
    · subst a
      unfold quadDeformMat
      simp [hbi]
      rw [hA.apply b i]
      rw [hA.apply b j]
  · by_cases hbi : b = i
    · subst b
      unfold quadDeformMat
      simp [hai]
      rw [hA.apply a i]
      rw [hA.apply a j]
    · unfold quadDeformMat
      simp [hai, hbi]
      rw [hA.apply b a]

lemma quadDeformMat_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (θ : ℝ)
    (hAnn : ∀ a b : Fin n, 0 ≤ A a b) (hθ : 0 ≤ θ) :
    ∀ a b : Fin n, 0 ≤ quadDeformMat A i j θ a b := by
  classical
  intro a b
  have h1 : 0 ≤ θ * (if a = i then A j b else 0) := by
    by_cases hai : a = i
    · simp [hai]
      exact mul_nonneg hθ (hAnn j b)
    · simp [hai]
  have h2 : 0 ≤ θ * (if b = i then A a j else 0) := by
    by_cases hbi : b = i
    · simp [hbi]
      exact mul_nonneg hθ (hAnn a j)
    · simp [hbi]
  unfold quadDeformMat
  nlinarith [hAnn a b, h1, h2]

lemma quadReal_self_expand {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
    (a b : ℝ) :
    quadReal M (a • u + b • v) (a • u + b • v) =
      a ^ 2 * quadReal M u u + a * b * quadReal M u v +
        a * b * quadReal M v u + b ^ 2 * quadReal M v v := by
  classical
  rw [quadReal_add_left M (a • u) (b • v) (a • u + b • v)]
  rw [quadReal_add_right M (a • u) (a • u) (b • v)]
  rw [quadReal_add_right M (b • v) (a • u) (b • v)]
  rw [quadReal_smul_left' M a u (a • u)]
  rw [quadReal_smul_right' M a u u]
  rw [quadReal_smul_left' M a u (b • v)]
  rw [quadReal_smul_right' M b u v]
  rw [quadReal_smul_left' M b v (a • u)]
  rw [quadReal_smul_right' M a v u]
  rw [quadReal_smul_left' M b v (b • v)]
  rw [quadReal_smul_right' M b v v]
  ring

lemma quadStable_of_negOnKernel {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hF : F.IsSymm) (hFnn : ∀ a b : Fin n, 0 ≤ F a b) (hFne : F ≠ 0)
    (hquad : ∀ x : Fin n → ℝ, (∑ a : Fin n, w a * x a) = 0 → quadReal F x x ≤ 0) :
    ∀ z : Fin n → UpperHalfPlane, quadComplex F (fun i : Fin n => (z i : ℂ)) ≠ 0 := by
  classical
  intro z hz0
  let wc : Fin n → ℂ := fun i => (z i : ℂ)
  let xr : Fin n → ℝ := fun i => (wc i).re
  let xi : Fin n → ℝ := fun i => (wc i).im
  have hparts := quadComplex_eq_zero_parts F wc hz0
  have hxx_sub : quadReal F xr xr - quadReal F xi xi = 0 := by simpa [xr, xi] using hparts.1
  have hcross_sum : quadReal F xr xi + quadReal F xi xr = 0 := by simpa [xr, xi] using hparts.2
  have hxx_eq : quadReal F xr xr = quadReal F xi xi := by linarith
  have hcross : quadReal F xr xi = 0 := by
    have hs := quadReal_symm F hF xr xi
    linarith
  have hxi_pos : ∀ i : Fin n, 0 < xi i := by
    intro i
    dsimp [xi, wc]
    simpa [UpperHalfPlane.coe_im] using UpperHalfPlane.im_pos (z i)
  have hQyy : 0 < quadReal F xi xi := quad_pos_of_nonneg F hFnn hFne hxi_pos
  have hQxx_pos : 0 < quadReal F xr xr := by linarith
  by_cases hk : (∑ a : Fin n, w a * xi a) = 0
  · have hle := hquad xi hk
    linarith
  · let α : ℝ := (∑ a : Fin n, w a * xr a) / (∑ a : Fin n, w a * xi a)
    let h : Fin n → ℝ := fun a => xr a - α * xi a
    have hxr : xr = α • xi + h := by
      funext a
      dsimp [h, α]
      ring
    have hk2 : (∑ a : Fin n, w a * h a) = 0 := by
      have hden : (∑ a : Fin n, w a * xi a) ≠ 0 := hk
      have hmul : α * (∑ a : Fin n, w a * xi a) = ∑ a : Fin n, w a * xr a := by
        dsimp [α]
        rw [div_mul_eq_mul_div]
        field_simp [hden]
      dsimp [h]
      calc
        (∑ a : Fin n, w a * (xr a - α * xi a))
            = (∑ a : Fin n, w a * xr a) - (∑ a : Fin n, w a * (α * xi a)) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro a ha
              ring
        _ = (∑ a : Fin n, w a * xr a) - α * (∑ a : Fin n, w a * xi a) := by
              congr 1
              calc
                (∑ a : Fin n, w a * (α * xi a)) = ∑ a : Fin n, α * (w a * xi a) := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  ring
                _ = α * (∑ a : Fin n, w a * xi a) := by rw [Finset.mul_sum]
        _ = 0 := by rw [hmul]; ring
    have hhh_le : quadReal F h h ≤ 0 := hquad h hk2
    have hcross_h : quadReal F h xi = -α * quadReal F xi xi := by
      have hsplit := quadReal_add_left F (α • xi) h xi
      have hmain2 : quadReal F (α • xi + h) xi = α * quadReal F xi xi + quadReal F h xi := by
        rw [hsplit]
        rw [quadReal_smul_left' F α xi xi]
      have hxr' : quadReal F xr xi = α * quadReal F xi xi + quadReal F h xi := by
        rw [hxr]
        exact hmain2
      linarith
    have hxx_le : quadReal F xr xr ≤ 0 := by
      have hexp := quadReal_self_expand F xi h α 1
      have hxr2 : quadReal F xr xr =
          α ^ 2 * quadReal F xi xi + α * quadReal F xi h +
            α * quadReal F h xi + quadReal F h h := by
        rw [hxr]
        simpa using hexp
      have hsymm_ih : quadReal F xi h = quadReal F h xi := quadReal_symm F hF xi h
      rw [hsymm_ih, hcross_h] at hxr2
      have hneg : -(α ^ 2) * quadReal F xi xi ≤ 0 := by
        nlinarith [sq_nonneg α, hQyy]
      nlinarith
    linarith

/-- The coefficient of a monomial in `θ·X_i·∂_j f` is a single cross term. -/
lemma coeff_deform_pderiv {n : ℕ} (f : H n 2) (i j : Fin n) (θ : ℝ) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m ((C θ) * X i * pderiv j f.1) =
      ∑ b : Fin n, θ * f.hessian j b *
        (if m = Finsupp.single i 1 + Finsupp.single b 1 then (1 : ℝ) else 0) := by
  classical
  rw [hessian_aeval_eq_pderiv_eq_sum_hessian n f j]
  rw [Finset.mul_sum]
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hterm : (C θ) * X i * (C (f.hessian j b) * X b) =
      C (θ * f.hessian j b) * (X i * X b) := by
    calc
      (C θ : MvPolynomial (Fin n) ℝ) * X i * (C (f.hessian j b) * X b)
          = C θ * C (f.hessian j b) * (X i * X b) := by ring
      _ = C (θ * f.hessian j b) * (X i * X b) := by
            rw [← MvPolynomial.C_mul]
  rw [hterm]
  rw [MvPolynomial.coeff_C_mul]
  rw [coeff_X_mul_X m i b]

/-- Square-monomial coefficient of the deformation term. -/
lemma coeff_deform_pderiv_sq {n : ℕ} (f : H n 2) (i j k : Fin n) (θ : ℝ) :
    MvPolynomial.coeff (Finsupp.single k 2) ((C θ) * X i * pderiv j f.1) =
      θ * (if k = i then f.hessian j i else 0) := by
  classical
  rw [coeff_deform_pderiv f i j θ (Finsupp.single k 2)]
  by_cases hki : k = i
  · subst k
    rw [Finset.sum_eq_single i]
    · rw [single_one_add_single_one i]
      simp
    · intro b hb hbi
      have hne : ¬ (Finsupp.single i 2 = Finsupp.single i 1 + Finsupp.single b 1) := by
        intro h
        have hb2 : i = i ∧ b = i := (single_add_single_eq_single_two_iff i b i).mp h.symm
        exact hbi hb2.2
      simp [hne]
    · intro hni
      simp at hni
  · simp [hki]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : ¬ (Finsupp.single k 2 = Finsupp.single i 1 + Finsupp.single b 1) := by
      intro h
      have hb2 : i = k ∧ b = k := (single_add_single_eq_single_two_iff i b k).mp h.symm
      exact hki hb2.1.symm
    simp [hne]

/-- Cross-monomial coefficient of the deformation term. -/
lemma coeff_deform_pderiv_cross_left {n : ℕ} (f : H n 2) (i j b : Fin n) (θ : ℝ)
    (hb_ne_i : b ≠ i) :
    MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single b 1) ((C θ) * X i * pderiv j f.1) =
      θ * f.hessian j b := by
  classical
  rw [coeff_deform_pderiv f i j θ (Finsupp.single i 1 + Finsupp.single b 1)]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' hb' hb'b
    have hne : ¬ (Finsupp.single i 1 + Finsupp.single b 1 =
        Finsupp.single i 1 + Finsupp.single b' 1) := by
      intro h
      have hval := congrArg (fun t : Fin n →₀ ℕ => t b) h
      simp [Finsupp.add_apply, hb_ne_i, hb'b] at hval
    simp [hne]
  · intro hnb
    simp at hnb

lemma coeff_deform_pderiv_cross_right {n : ℕ} (f : H n 2) (i j a : Fin n) (θ : ℝ)
    (ha_ne_i : a ≠ i) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single i 1) ((C θ) * X i * pderiv j f.1) =
      θ * f.hessian j a := by
  classical
  rw [coeff_deform_pderiv f i j θ (Finsupp.single a 1 + Finsupp.single i 1)]
  rw [Finset.sum_eq_single a]
  · rw [add_comm (Finsupp.single i 1) (Finsupp.single a 1)]
    simp
  · intro b' hb' hb'a
    have hne : ¬ (Finsupp.single a 1 + Finsupp.single i 1 =
        Finsupp.single i 1 + Finsupp.single b' 1) := by
      intro h
      have hval := congrArg (fun t : Fin n →₀ ℕ => t a) h
      simp [Finsupp.add_apply, ha_ne_i, hb'a] at hval
    simp [hne]
  · intro hna
    simp at hna

lemma coeff_deform_pderiv_cross_none {n : ℕ} (f : H n 2) (i j a b : Fin n) (θ : ℝ)
    (hab : a ≠ b) (ha_ne_i : a ≠ i) (hb_ne_i : b ≠ i) :
    MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) ((C θ) * X i * pderiv j f.1) = 0 := by
  classical
  rw [coeff_deform_pderiv f i j θ (Finsupp.single a 1 + Finsupp.single b 1)]
  apply Finset.sum_eq_zero
  intro b' hb'
  have hne : ¬ (Finsupp.single a 1 + Finsupp.single b 1 =
      Finsupp.single i 1 + Finsupp.single b' 1) := by
    intro h
    by_cases hb'b : b' = b
    · have hval := congrArg (fun t : Fin n →₀ ℕ => t a) h
      simp [Finsupp.add_apply, ha_ne_i, hb'b, hab] at hval
    · have hval := congrArg (fun t : Fin n →₀ ℕ => t b) h
      simp [Finsupp.add_apply, hb_ne_i, hb'b] at hval
  simp [hne]


/-- The deformation preserves degree-two homogeneity. -/
lemma homogeneous_quadDeform {n : ℕ} (i j : Fin n) (θ : ℝ) (q : MvPolynomial (Fin n) ℝ)
    (hqhom : q.IsHomogeneous 2) :
    (q + (C θ) * X i * pderiv j q).IsHomogeneous 2 := by
  have hp : (pderiv j q).IsHomogeneous (2 - 1) :=
    MvPolynomial.IsHomogeneous.pderiv (φ := q) hqhom
  have hp1 : (pderiv j q).IsHomogeneous 1 := by simpa using hp
  have hXi : (X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) i
  have hC : (C θ : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) θ
  have hmul1 : ((C θ) * X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
    simpa using (MvPolynomial.IsHomogeneous.mul (φ := (C θ : MvPolynomial (Fin n) ℝ)) hC (ψ := (X i : MvPolynomial (Fin n) ℝ)) hXi)
  have hmul2 : ((C θ) * X i * pderiv j q).IsHomogeneous 2 := by
    simpa using (MvPolynomial.IsHomogeneous.mul (φ := ((C θ) * X i)) hmul1 (ψ := (pderiv j q)) hp1)
  simpa using (MvPolynomial.IsHomogeneous.add (φ := q) hqhom (ψ := ((C θ) * X i * pderiv j q)) hmul2)

/-- The Hessian of the deformed polynomial is the deformed Hessian matrix. -/
lemma hessian_quadDeform {n : ℕ} (f : H n 2) (f' : H n 2) (i j : Fin n) (θ : ℝ)
    (hf' : f'.1 = f.1 + (C θ) * X i * pderiv j f.1) :
    f'.hessian = quadDeformMat f.hessian i j θ := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    have hsymm := hessian_symm n f
    calc
      f'.hessian a a = 2 * MvPolynomial.coeff (Finsupp.single a 2) f'.1 := hessian_apply_sq n f' a
      _ = 2 * (MvPolynomial.coeff (Finsupp.single a 2) f.1 +
          MvPolynomial.coeff (Finsupp.single a 2) ((C θ) * X i * pderiv j f.1)) := by
            rw [hf', MvPolynomial.coeff_add]
      _ = f.hessian a a + 2 * (θ * (if a = i then f.hessian j i else 0)) := by
            rw [coeff_deform_pderiv_sq f i j a θ, hessian_apply_sq n f a]
            ring
      _ = quadDeformMat f.hessian i j θ a a := by
            unfold quadDeformMat
            by_cases hai : a = i
            · subst a
              simp
              rw [hsymm.apply i j]
              ring
            · simp [hai]
  · by_cases hai : a = i
    · subst a
      have hbne : b ≠ i := by
        intro hbi
        subst b
        exact hab rfl
      calc
        f'.hessian i b = MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single b 1) f'.1 := hessian_apply_cross n f' hab
        _ = MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single b 1) f.1 +
            MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single b 1) ((C θ) * X i * pderiv j f.1) := by
              rw [hf', MvPolynomial.coeff_add]
        _ = f.hessian i b + θ * f.hessian j b := by
              rw [hessian_apply_cross n f hab]
              rw [coeff_deform_pderiv_cross_left f i j b θ hbne]
        _ = quadDeformMat f.hessian i j θ i b := by
              unfold quadDeformMat
              simp [hbne]
    · by_cases hbi : b = i
      · subst b
        have hsymm := hessian_symm n f
        calc
          f'.hessian a i = MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single i 1) f'.1 := hessian_apply_cross n f' hab
          _ = MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single i 1) f.1 +
              MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single i 1) ((C θ) * X i * pderiv j f.1) := by
                rw [hf', MvPolynomial.coeff_add]
          _ = f.hessian a i + θ * f.hessian j a := by
                rw [hessian_apply_cross n f hab]
                rw [coeff_deform_pderiv_cross_right f i j a θ hai]
          _ = quadDeformMat f.hessian i j θ a i := by
                unfold quadDeformMat
                simp [hai]
                rw [hsymm.apply a j]
                simp
      · calc
          f'.hessian a b = MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) f'.1 := hessian_apply_cross n f' hab
          _ = MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) f.1 +
              MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) ((C θ) * X i * pderiv j f.1) := by
                rw [hf', MvPolynomial.coeff_add]
          _ = f.hessian a b := by
                rw [hessian_apply_cross n f hab]
                rw [coeff_deform_pderiv_cross_none f i j a b θ hab hai hbi]
                ring
          _ = quadDeformMat f.hessian i j θ a b := by
                unfold quadDeformMat
                simp [hai, hbi]


lemma quadShear_kernel_sum {n : ℕ} (u : Fin n → ℝ) (i j : Fin n) (θ : ℝ)
    (x : Fin n → ℝ) :
    (∑ a : Fin n, u a * quadShear i j θ x a) =
      ∑ a : Fin n, (u a + (if a = i then θ * u j else 0)) * x a := by
  classical
  calc
    (∑ a : Fin n, u a * quadShear i j θ x a)
        = ∑ a : Fin n, u a * (x a + (if a = j then θ * x i else 0)) := rfl
    _ = ∑ a : Fin n, (u a * x a + u a * (if a = j then θ * x i else 0)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [mul_add]
    _ = (∑ a : Fin n, u a * x a) +
        (∑ a : Fin n, u a * (if a = j then θ * x i else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ a : Fin n, u a * x a) + θ * x i * u j := by
          congr 1
          rw [Finset.sum_eq_single j]
          · simp
            ring
          · intro a ha haj
            simp [haj]
          · intro hnj
            simp at hnj
    _ = ∑ a : Fin n, (u a + (if a = i then θ * u j else 0)) * x a := by
          apply Eq.symm
          calc
            (∑ a : Fin n, (u a + (if a = i then θ * u j else 0)) * x a)
                = ∑ a : Fin n, (u a * x a + (if a = i then θ * u j else 0) * x a) := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    rw [add_mul]
            _ = (∑ a : Fin n, u a * x a) +
                (∑ a : Fin n, (if a = i then θ * u j else 0) * x a) := by
                    rw [Finset.sum_add_distrib]
            _ = (∑ a : Fin n, u a * x a) + θ * u j * x i := by
                    congr 1
                    rw [Finset.sum_eq_single i]
                    · simp
                    · intro a ha hai
                      simp [hai]
                    · intro hni
                      simp at hni
            _ = (∑ a : Fin n, u a * x a) + θ * x i * u j := by ring

/-- If a homogeneous quadratic `q` is stable with nonnegative coefficients then
`q + θ·X_i·(∂_j q)` is stable, for `θ ≥ 0` and any indices `i, j`.
This is the degree-two case of Brändén–Huh Proposition 2.12 (deform). -/
lemma quad_deform_stable {n : ℕ} (i j : Fin n) (θ : ℝ) (q : MvPolynomial (Fin n) ℝ)
    (hqhom : q.IsHomogeneous 2) (hstab : IsStable q)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ q.coeff m) (hθ : 0 ≤ θ) :
    IsStable (q + (C θ) * X i * pderiv j q) := by
  classical
  by_cases hn : 0 < n
  · let f : H n 2 := ⟨q, hqhom⟩
    let f' : H n 2 := ⟨q + (C θ) * X i * pderiv j q, homogeneous_quadDeform i j θ q hqhom⟩
    have hstabQ : IsStable f.1 := by simpa [f] using hstab
    have hnnf : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
      intro m
      simpa [f] using hnn m
    have hfS : f ∈ S n 2 := by
      dsimp [S]
      exact ⟨hstabQ, hnnf⟩
    have hstabM : f.hessian ∈ stableQuadM n := hessian_mem_stableQuadM_of_mem_S n f hfS
    rcases hstabM with ⟨hAsymm, hAnn, hAcard⟩
    have hdeform : f'.hessian = quadDeformMat f.hessian i j θ := by
      apply hessian_quadDeform f f' i j θ
      rfl
    have hFstab : quadDeformMat f.hessian i j θ = 0 ∨
        ∀ z : Fin n → UpperHalfPlane,
          quadComplex (quadDeformMat f.hessian i j θ) (fun a : Fin n => (z a : ℂ)) ≠ 0 := by
      by_cases hA0 : f.hessian = 0
      · left
        ext a b
        unfold quadDeformMat
        simp [hA0]
      · right
        rcases perron_vector_of_nonneg_symm_card_pos_le_one_pos hn f.hessian hAsymm hAnn hAcard
          with ⟨u, lam, hu_nn, hu_norm, hlam_nn, hu_eig, hquadA, hsupp⟩
        let F : Matrix (Fin n) (Fin n) ℝ := quadDeformMat f.hessian i j θ
        let w : Fin n → ℝ := fun a => u a + (if a = i then θ * u j else 0)
        have hFsymm : F.IsSymm := quadDeformMat_symm f.hessian i j θ hAsymm
        have hFnn : ∀ a b : Fin n, 0 ≤ F a b := quadDeformMat_nonneg f.hessian i j θ hAnn hθ
        have hFne : F ≠ 0 := by
          intro hF0
          apply hA0
          ext a b
          have hFab0 : F a b = 0 := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a b) hF0
          have ht1 : 0 ≤ θ * (if a = i then f.hessian j b else 0) := by
            by_cases hai : a = i
            · simp [hai]
              exact mul_nonneg hθ (hAnn j b)
            · simp [hai]
          have ht2 : 0 ≤ θ * (if b = i then f.hessian a j else 0) := by
            by_cases hbi : b = i
            · simp [hbi]
              exact mul_nonneg hθ (hAnn a j)
            · simp [hbi]
          unfold F quadDeformMat at hFab0
          have hleA : f.hessian a b ≤ 0 := by nlinarith
          exact le_antisymm hleA (hAnn a b)
        have hquadF : ∀ x : Fin n → ℝ, (∑ a : Fin n, w a * x a) = 0 →
            quadReal F x x ≤ 0 := by
          intro x hx
          have hAy : quadReal f.hessian (quadShear i j θ x) (quadShear i j θ x) ≤ 0 := by
            rw [quadReal_eq_sum_mul_left f.hessian (quadShear i j θ x)]
            apply hquadA
            rw [quadShear_kernel_sum u i j θ x]
            simpa [w] using hx
          have hid := quadReal_quadDeformMat_eq f.hessian i j θ x
          have hneg : 0 ≤ θ ^ 2 * f.hessian j j * (x i) ^ 2 := by
            exact mul_nonneg (mul_nonneg (sq_nonneg θ) (hAnn j j)) (sq_nonneg (x i))
          dsimp [F]
          nlinarith
        exact quadStable_of_negOnKernel F w hFsymm hFnn hFne hquadF
    -- convert the matrix statement to stability of the polynomial
    have hqeq : q + (C θ) * X i * pderiv j q = f'.1 := by
      rfl
    rw [hqeq]
    rw [IsStable]
    rcases hFstab with hF0 | hFnv
    · left
      have hf0 : f' = 0 := by
        rw [← quadricOfMatrix_hessian n f']
        rw [hdeform]
        rw [hF0]
        simp [quadricOfMatrix]
      exact congrArg (fun x : H n 2 => x.1) hf0
    · right
      intro z
      have hz : quadComplex (quadDeformMat f.hessian i j θ) (fun a : Fin n => (z a : ℂ)) ≠ 0 := hFnv z
      have hsum_ne : (∑ a : Fin n, ∑ b : Fin n,
          f'.hessian a b * (z a : ℂ) * (z b : ℂ)) ≠ 0 := by
        rw [hdeform]
        simpa [quadComplex] using hz
      intro hae0
      have hq := hessian_aeval_eq n f' (fun a : Fin n => (z a : ℂ))
      have hae0' : MvPolynomial.aeval (fun a : Fin n => (z a : ℂ)) f'.1 = 0 := by
        simpa [Function.comp_def] using hae0
      have hsum0 : (∑ a : Fin n, ∑ b : Fin n,
          f'.hessian a b * (z a : ℂ) * (z b : ℂ)) = 0 := by
        rw [← hq, hae0']
        simp
      exact hsum_ne hsum0
  · exfalso
    have hn0 : n = 0 := by omega
    have : i.val < 0 := by simpa [hn0] using i.isLt
    omega

end

end Commons.LorentzianPolynomials
