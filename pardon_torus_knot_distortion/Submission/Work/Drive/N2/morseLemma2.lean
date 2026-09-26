import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.hadamard2
import Submission.Work.Drive.N2.exists_local_diffeomorph

/-!
# The Morse normal form in the plane

The assembly: Hadamard's expansion gives a smooth decomposition of `g - g x₀` as a quadratic
form in two smooth coefficient functions; completing the square and applying the inverse function
theorem produces the local coordinates `φ` with `g = g x₀ + s₁ (φ y 0)² + s₂ (φ y 1)²`.

The two analytic inputs (`hadamard2`, `exists_pair_bilinForm`, `exists_local_diffeomorph`) are
proved in the sibling modules of this directory.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Work.Drive.N2

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## Coordinates on the plane -/

/-- The `i`-th coordinate functional on the plane. -/
def co (i : Fin 2) : Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) i).comp
    ((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] lemma co_apply (i : Fin 2) (z : Plane) : co i z = z i := rfl

/-- The first basis vector of the plane. -/
def e0 : Plane := WithLp.toLp 2 ![1, 0]
/-- The second basis vector of the plane. -/
def e1 : Plane := WithLp.toLp 2 ![0, 1]

lemma e_decomp (z : Plane) : z = (z 0) • e0 + (z 1) • e1 := by
  ext i; fin_cases i <;> simp [e0, e1]

/-- The vector with coordinates `(p, q)`. -/
def V (p q : ℝ) : Plane := WithLp.toLp 2 ![p, q]
/-- The vector with coordinates `(-q, p)`. -/
def Wv (p q : ℝ) : Plane := WithLp.toLp 2 ![-q, p]

@[simp] lemma V_apply_zero (p q : ℝ) : V p q 0 = p := rfl
@[simp] lemma V_apply_one (p q : ℝ) : V p q 1 = q := rfl
@[simp] lemma Wv_apply_zero (p q : ℝ) : Wv p q 0 = -q := rfl
@[simp] lemma Wv_apply_one (p q : ℝ) : Wv p q 1 = p := rfl

/-- First coordinate in the basis `(V p q, Wv p q)`. -/
def coef0 (p q lam : ℝ) : Plane →L[ℝ] ℝ := (1 / lam) • (p • co 0 + q • co 1)
/-- Second coordinate in the basis `(V p q, Wv p q)`. -/
def coef1 (p q lam : ℝ) : Plane →L[ℝ] ℝ := (1 / lam) • ((-q) • co 0 + p • co 1)

@[simp] lemma coef0_apply (p q lam : ℝ) (z : Plane) :
    coef0 p q lam z = (p * z 0 + q * z 1) / lam := by
  simp [coef0]; ring

@[simp] lemma coef1_apply (p q lam : ℝ) (z : Plane) :
    coef1 p q lam z = (-q * z 0 + p * z 1) / lam := by
  simp [coef1]; ring

lemma vec_decomp (p q lam : ℝ) (hlam : lam = p ^ 2 + q ^ 2) (hpq : p ^ 2 + q ^ 2 ≠ 0)
    (z : Plane) : z = coef0 p q lam z • V p q + coef1 p q lam z • Wv p q := by
  subst hlam
  ext i; fin_cases i <;>
    · simp [V, Wv, coef0, coef1]
      field_simp
      try ring

@[simp] lemma coef0_V (p q : ℝ) (hpq : p ^ 2 + q ^ 2 ≠ 0) :
    coef0 p q (p ^ 2 + q ^ 2) (V p q) = 1 := by
  rw [coef0_apply, V_apply_zero, V_apply_one]
  field_simp

@[simp] lemma coef1_V (p q : ℝ) (hpq : p ^ 2 + q ^ 2 ≠ 0) :
    coef1 p q (p ^ 2 + q ^ 2) (V p q) = 0 := by
  rw [coef1_apply, V_apply_zero, V_apply_one]
  field_simp
  try ring

@[simp] lemma coef0_W (p q : ℝ) (hpq : p ^ 2 + q ^ 2 ≠ 0) :
    coef0 p q (p ^ 2 + q ^ 2) (Wv p q) = 0 := by
  rw [coef0_apply, Wv_apply_zero, Wv_apply_one]
  field_simp
  try ring

@[simp] lemma coef1_W (p q : ℝ) (hpq : p ^ 2 + q ^ 2 ≠ 0) :
    coef1 p q (p ^ 2 + q ^ 2) (Wv p q) = 1 := by
  rw [coef1_apply, Wv_apply_zero, Wv_apply_one]
  field_simp
  try ring

/-! ## A good frame for a symmetric nondegenerate bilinear form -/

private lemma minSmoothness_two_le_infty : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [minSmoothness]
  split_ifs with h
  · exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  · exact absurd (inferInstance : IsRCLikeNormedField ℝ) h

/-- In the plane a symmetric injective bilinear form is nonzero somewhere on the diagonal. -/
private theorem pair_bilinForm_aux {B : Plane →L[ℝ] Plane →L[ℝ] ℝ}
    (hsymm : ∀ u w, B u w = B w u) (hinj : Function.Injective B) :
    ∃ v : Plane, v ≠ 0 ∧ B v v ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hzero : B = 0 := by
    ext u w
    have h1 : B (u + w) (u + w) = 0 := by
      rcases eq_or_ne (u + w) 0 with h | h
      · rw [h]; simp
      · exact hcon (u + w) h
    have h2 : B u u = 0 := by
      rcases eq_or_ne u 0 with h | h
      · rw [h]; simp
      · exact hcon u h
    have h3 : B w w = 0 := by
      rcases eq_or_ne w 0 with h | h
      · rw [h]; simp
      · exact hcon w h
    have hexp : B (u + w) (u + w) = B u u + B w u + (B u w + B w w) := by
      simp only [map_add, add_apply]
      try abel
    rw [hexp, h2, h3, hsymm w u] at h1
    simp only [ContinuousLinearMap.zero_apply]
    linarith
  obtain ⟨u, hu⟩ : ∃ u : Plane, u ≠ 0 := ⟨e0, by simp [e0]⟩
  refine hu (hinj ?_)
  rw [hzero]
  simp

/-- For a symmetric injective bilinear form on the plane there are `p, q` with `(p,q) ≠ 0` such
that the vector `V p q` satisfies `B v v ≠ 0` and the Gram determinant of the pair
`(V p q, Wv p q)` does not vanish. -/
theorem exists_frame {B : Plane →L[ℝ] Plane →L[ℝ] ℝ}
    (hsymm : ∀ u w, B u w = B w u) (hinj : Function.Injective B) :
    ∃ p q : ℝ, p ^ 2 + q ^ 2 ≠ 0 ∧ B (V p q) (V p q) ≠ 0 ∧
      B (V p q) (V p q) * B (Wv p q) (Wv p q) - (B (V p q) (Wv p q)) ^ 2 ≠ 0 := by
  obtain ⟨v, hvne, hβ⟩ := pair_bilinForm_aux hsymm hinj
  set p : ℝ := v 0 with hp
  set q : ℝ := v 1 with hq
  have hpq : p ^ 2 + q ^ 2 ≠ 0 := by
    rintro h0
    have hp0 : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq0 : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    refine hvne (by
      have h1 : v 0 = 0 := by rw [← hp, hp0]
      have h2 : v 1 = 0 := by rw [← hq, hq0]
      ext i
      fin_cases i <;> simp [h1, h2])
  have hVv : V p q = v := by
    ext i
    fin_cases i <;> simp [hp, hq]
  have hβ' : B (V p q) (V p q) ≠ 0 := by rw [hVv]; exact hβ
  refine ⟨p, q, hpq, hβ', ?_⟩
  rintro hdet0
  have hfac : B (V p q) (V p q) * B (Wv p q) (Wv p q) - (B (V p q) (Wv p q)) ^ 2 = 0 := hdet0
  set u : Plane := (-(B (V p q) (Wv p q))) • V p q + (B (V p q) (V p q)) • Wv p q with hu
  have huV : B u (V p q) = 0 := by
    rw [hu]
    simp only [map_add, map_smul, add_apply, smul_apply]
    rw [hsymm (Wv p q) (V p q)]
    ring
  have huW : B u (Wv p q) = 0 := by
    rw [hu]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    nlinarith [hfac]
  have hBu : B u = 0 := by
    ext z
    have hz := vec_decomp p q (p ^ 2 + q ^ 2) rfl hpq z
    have hzz : B u z = B u (coef0 p q (p ^ 2 + q ^ 2) z • V p q
        + coef1 p q (p ^ 2 + q ^ 2) z • Wv p q) := congrArg (fun w => B u w) hz
    rw [hzz, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, huV, huW]
    simp only [ContinuousLinearMap.zero_apply, mul_zero, add_zero]
  have hu0 : u = 0 := hinj (by rw [hBu, map_zero])
  have hcoef1u : coef1 p q (p ^ 2 + q ^ 2) u = B (V p q) (V p q) := by
    rw [hu, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      coef1_V p q hpq, coef1_W p q hpq]
    ring
  rw [hu0] at hcoef1u
  simp only [map_zero] at hcoef1u
  exact hβ' hcoef1u.symm

/-! ## Two derivative computations -/

/-- Derivative of `√(s₁ a) * (ξ₀ + (b/a) ξ₁)`, where `ξ_k` are linear coordinates. -/
lemma hasFDerivAt_sqrt_mul_shear (a b : Plane → ℝ) (x₀ : Plane) (s₁ : ℝ)
    (c₀ c₁ : Plane →L[ℝ] ℝ) (ha : DifferentiableAt ℝ a x₀)
    (hb : DifferentiableAt ℝ (fun x => b x / a x) x₀) (hpos : 0 < s₁ * a x₀) :
    HasFDerivAt (fun x : Plane => Real.sqrt (s₁ * a x) *
        (c₀ x - c₀ x₀ + (b x / a x) * (c₁ x - c₁ x₀)))
      (Real.sqrt (s₁ * a x₀) • (c₀ + (b x₀ / a x₀) • c₁)) x₀ := by
  have hξ0 : HasFDerivAt (fun x : Plane => c₀ x - c₀ x₀) c₀ x₀ :=
    (ContinuousLinearMap.hasFDerivAt c₀).sub_const _
  have hξ1 : HasFDerivAt (fun x : Plane => c₁ x - c₁ x₀) c₁ x₀ :=
    (ContinuousLinearMap.hasFDerivAt c₁).sub_const _
  have hQ : HasFDerivAt (fun x : Plane =>
        c₀ x - c₀ x₀ + (b x / a x) * (c₁ x - c₁ x₀))
      (c₀ + (b x₀ / a x₀) • c₁) x₀ := by
    have h := hξ0.add (hb.hasFDerivAt.mul hξ1)
    have hz : (c₁ x₀ - c₁ x₀) = 0 := sub_self _
    rw [hz, zero_smul, add_zero] at h
    exact h
  have hsq : HasFDerivAt (fun x : Plane => Real.sqrt (s₁ * a x))
      ((1 / (2 * Real.sqrt (s₁ * a x₀))) • (s₁ • fderiv ℝ a x₀)) x₀ :=
    (ha.hasFDerivAt.const_mul s₁).sqrt (by positivity)
  have h := hsq.mul hQ
  have hz : (c₀ x₀ - c₀ x₀ + (b x₀ / a x₀) * (c₁ x₀ - c₁ x₀)) = 0 := by ring
  rw [hz, zero_smul, add_zero] at h
  exact h

/-- Derivative of `√(s₂ d) * ξ₁`. -/
lemma hasFDerivAt_sqrt_mul (d : Plane → ℝ) (x₀ : Plane) (s₂ : ℝ) (c₁ : Plane →L[ℝ] ℝ)
    (hd : DifferentiableAt ℝ d x₀) (hpos : 0 < s₂ * d x₀) :
    HasFDerivAt (fun x : Plane => Real.sqrt (s₂ * d x) * (c₁ x - c₁ x₀))
      (Real.sqrt (s₂ * d x₀) • c₁) x₀ := by
  have hsq : HasFDerivAt (fun x : Plane => Real.sqrt (s₂ * d x))
      ((1 / (2 * Real.sqrt (s₂ * d x₀))) • (s₂ • fderiv ℝ d x₀)) x₀ :=
    (hd.hasFDerivAt.const_mul s₂).sqrt (by positivity)
  have hξ1 : HasFDerivAt (fun x : Plane => c₁ x - c₁ x₀) c₁ x₀ :=
    (ContinuousLinearMap.hasFDerivAt c₁).sub_const _
  have h := hsq.mul hξ1
  have hz : (c₁ x₀ - c₁ x₀) = 0 := sub_self _
  rw [hz, zero_smul, add_zero] at h
  exact h

/-! ## The main construction -/



theorem morse_of_hadamard (g : Plane → ℝ) (x₀ : Plane)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hnondeg : Function.Injective (fderiv ℝ (fderiv ℝ g) x₀))
    (h : Fin 2 → Fin 2 → (Plane → ℝ))
    (hsmooth : ∀ i j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i j))
    (hsymm : ∀ i j x, h i j x = h j i x)
    (hexp : ∀ x, g x = g x₀ + ∑ i, ∑ j, (x i - x₀ i) * (x j - x₀ j) * h i j x)
    (hval : ∀ v, ∑ i, ∑ j, v i * v j * h i j x₀
      = (1 / 2) * (fderiv ℝ (fderiv ℝ g) x₀ v v)) :
    ∃ (φ : OpenPartialHomeomorph Plane Plane) (s₁ s₂ : ℝ),
      x₀ ∈ φ.source ∧ φ x₀ = 0 ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : Plane → Plane) φ.source ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ.symm φ.target ∧
      (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
      ∀ y ∈ φ.source, g y = g x₀ + s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2 := by
  set B : Plane →L[ℝ] (Plane →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ g) x₀ with hB
  have hBsymm : ∀ u w, B u w = B w u := by
    intro u w
    rw [hB]
    exact hg.contDiffAt.isSymmSndFDerivAt minSmoothness_two_le_infty u w
  obtain ⟨p, q, hpq, hβ, hdet⟩ := exists_frame hBsymm (by rw [hB]; exact hnondeg)
  -- the smooth coefficient functions of the quadratic form in the new coordinates
  set aa : Plane → ℝ := fun x => ∑ i : Fin 2, ∑ j : Fin 2,
    (V p q i) * (V p q j) * h i j x with haa
  set bb : Plane → ℝ := fun x => ∑ i : Fin 2, ∑ j : Fin 2,
    (V p q i) * (Wv p q j) * h i j x with hbb
  set cc : Plane → ℝ := fun x => ∑ i : Fin 2, ∑ j : Fin 2,
    (Wv p q i) * (Wv p q j) * h i j x with hcc
  have haa_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) aa := by rw [haa]; fun_prop
  have hbb_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bb := by rw [hbb]; fun_prop
  have hcc_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cc := by rw [hcc]; fun_prop
  have hval' : ∀ v : Plane, ∑ i, ∑ j, v i * v j * h i j x₀ = (1 / 2) * B v v := by
    intro v; rw [hval v, hB]
  have haa0 : aa x₀ = (1 / 2) * B (V p q) (V p q) := by rw [haa]; exact hval' (V p q)
  have hcc0 : cc x₀ = (1 / 2) * B (Wv p q) (Wv p q) := by rw [hcc]; exact hval' (Wv p q)
  have hbb0 : bb x₀ = (1 / 2) * B (V p q) (Wv p q) := by
    have h3 : (∑ i, ∑ j, ((V p q + Wv p q) i) * ((V p q + Wv p q) j) * h i j x₀)
        = (1 / 2) * B (V p q + Wv p q) (V p q + Wv p q) := hval' _
    have h4 : (∑ i, ∑ j, ((V p q + Wv p q) i) * ((V p q + Wv p q) j) * h i j x₀)
        = aa x₀ + 2 * bb x₀ + cc x₀ := by
      rw [haa, hbb, hcc]
      simp only [Fin.sum_univ_two, Pi.add_apply, WithLp.ofLp_add]
      rw [hsymm 1 0 x₀]
      ring
    have h5 : B (V p q + Wv p q) (V p q + Wv p q)
        = B (V p q) (V p q) + 2 * B (V p q) (Wv p q) + B (Wv p q) (Wv p q) := by
      simp only [map_add, add_apply, hBsymm (Wv p q) (V p q)]
      ring
    linarith [h3, h4, h5, haa0, hcc0]
  have haa0_ne : aa x₀ ≠ 0 := by
    rw [haa0]; exact mul_ne_zero (by norm_num) hβ
  set dd : Plane → ℝ := fun x => cc x - (bb x) ^ 2 / aa x with hdd
  have hdd0 : dd x₀ = (B (V p q) (V p q) * B (Wv p q) (Wv p q)
      - (B (V p q) (Wv p q)) ^ 2) / (2 * B (V p q) (V p q)) := by
    rw [hdd]
    simp only
    rw [haa0, hbb0, hcc0]
    field_simp
    try ring
  have hdd0_ne : dd x₀ ≠ 0 := by
    rw [hdd0]
    exact div_ne_zero hdet (by positivity)
  -- the signs
  set s₁ : ℝ := if 0 < aa x₀ then 1 else -1 with hs₁
  set s₂ : ℝ := if 0 < dd x₀ then 1 else -1 with hs₂
  have hs₁_pm : s₁ = 1 ∨ s₁ = -1 := by rw [hs₁]; split <;> simp
  have hs₂_pm : s₂ = 1 ∨ s₂ = -1 := by rw [hs₂]; split <;> simp
  have hs₁_pos : 0 < s₁ * aa x₀ := by
    rw [hs₁]; split_ifs with hh
    · simpa using hh
    · have hneg : aa x₀ < 0 := lt_of_le_of_ne (not_lt.mp hh) haa0_ne
      simpa using neg_pos.mpr hneg
  have hs₂_pos : 0 < s₂ * dd x₀ := by
    rw [hs₂]; split_ifs with hh
    · simpa using hh
    · have hneg : dd x₀ < 0 := lt_of_le_of_ne (not_lt.mp hh) hdd0_ne
      simpa using neg_pos.mpr hneg
  -- the open set on which the construction works
  set U : Set Plane := {x | 0 < s₁ * aa x} ∩ {x | 0 < s₁ * s₂ * (cc x * aa x - (bb x) ^ 2)}
    with hU
  have hUopen : IsOpen U := by
    rw [hU]
    exact (isOpen_lt continuous_const (continuous_const.mul haa_sm.continuous)).inter
      (isOpen_lt continuous_const (continuous_const.mul
        ((hcc_sm.continuous.mul haa_sm.continuous).sub ((hbb_sm.continuous.pow 2)))))
  have hx₀U : x₀ ∈ U := by
    rw [hU]
    refine ⟨hs₁_pos, ?_⟩
    have hprod : 0 < (s₁ * aa x₀) * (s₂ * dd x₀) := mul_pos hs₁_pos hs₂_pos
    have hident : aa x₀ * dd x₀ = cc x₀ * aa x₀ - (bb x₀) ^ 2 := by
      rw [hdd]; field_simp
    have : (s₁ * aa x₀) * (s₂ * dd x₀) = s₁ * s₂ * (cc x₀ * aa x₀ - (bb x₀) ^ 2) := by
      rw [← hident]; ring
    rwa [this] at hprod
  -- coordinates `ξ₀, ξ₁` and the two functions `uu, ww`
  set xi0 : Plane → ℝ := fun x => coef0 p q (p ^ 2 + q ^ 2) (x - x₀) with hxi0
  set xi1 : Plane → ℝ := fun x => coef1 p q (p ^ 2 + q ^ 2) (x - x₀) with hxi1
  have hxi0_eq : ∀ x, xi0 x = coef0 p q (p ^ 2 + q ^ 2) x - coef0 p q (p ^ 2 + q ^ 2) x₀ := by
    intro x; simp only [hxi0]; rw [map_sub]
  have hxi1_eq : ∀ x, xi1 x = coef1 p q (p ^ 2 + q ^ 2) x - coef1 p q (p ^ 2 + q ^ 2) x₀ := by
    intro x; simp only [hxi1]; rw [map_sub]
  have hxi0_0 : xi0 x₀ = 0 := by rw [hxi0]; simp
  have hxi1_0 : xi1 x₀ = 0 := by rw [hxi1]; simp
  set uu : Plane → ℝ := fun x => Real.sqrt (s₁ * aa x) * (xi0 x + (bb x / aa x) * xi1 x)
    with huu
  set ww : Plane → ℝ := fun x => Real.sqrt (s₂ * dd x) * xi1 x with hww
  set F : Plane → Plane := fun x => (uu x) • e0 + (ww x) • e1 with hF
  -- smoothness on `U`
  have hdd_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dd U := by
    rw [hdd]
    refine (hcc_sm.contDiffOn).sub ((hbb_sm.contDiffOn).pow 2 |>.div (haa_sm.contDiffOn) ?_)
    intro x hx
    have h1 : 0 < s₁ * aa x := hx.1
    intro h0
    rw [h0, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hU_s₁aa : ∀ x ∈ U, 0 < s₁ * aa x := fun x hx => hx.1
  have hU_aa : ∀ x ∈ U, aa x ≠ 0 := by
    intro x hx h0
    have := hU_s₁aa x hx
    rw [h0, mul_zero] at this
    exact lt_irrefl 0 this
  have hs₁_ne : s₁ ≠ 0 := by rcases hs₁_pm with h | h <;> rw [h] <;> norm_num
  have hU_dd : ∀ x ∈ U, 0 < s₂ * dd x := by
    intro x hx
    have haapos : 0 < s₁ * aa x := hx.1
    have hax : aa x ≠ 0 := hU_aa x hx
    have hC : 0 < s₁ * s₂ * (cc x * aa x - (bb x) ^ 2) := hx.2
    have hident : aa x * dd x = cc x * aa x - (bb x) ^ 2 := by
      rw [hdd]
      field_simp
      try ring
    have h2 : s₂ * dd x = (s₁ * s₂ * (cc x * aa x - (bb x) ^ 2)) / (s₁ * aa x) := by
      rw [← hident]
      field_simp
      try ring
    rw [h2]
    exact div_pos hC haapos
  have hxi0_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) xi0 U := by
    rw [show xi0 = fun x => coef0 p q (p ^ 2 + q ^ 2) x - coef0 p q (p ^ 2 + q ^ 2) x₀ from
      funext hxi0_eq]
    exact ((ContinuousLinearMap.contDiff (coef0 p q (p ^ 2 + q ^ 2))).contDiffOn).sub
      contDiffOn_const
  have hxi1_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) xi1 U := by
    rw [show xi1 = fun x => coef1 p q (p ^ 2 + q ^ 2) x - coef1 p q (p ^ 2 + q ^ 2) x₀ from
      funext hxi1_eq]
    exact ((ContinuousLinearMap.contDiff (coef1 p q (p ^ 2 + q ^ 2))).contDiffOn).sub
      contDiffOn_const
  have hdiv_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => bb x / aa x) U :=
    (hbb_sm.contDiffOn).div (haa_sm.contDiffOn) (fun x hx => hU_aa x hx)
  have hsqrt_sm₁ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Real.sqrt (s₁ * aa x)) U :=
    ContDiffOn.sqrt (contDiffOn_const.mul haa_sm.contDiffOn)
      (fun x hx => ne_of_gt (hU_s₁aa x hx))
  have huu_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) uu U := by
    rw [huu]
    exact hsqrt_sm₁.mul (hxi0_sm.add (hdiv_sm.mul hxi1_sm))
  have hsqrt_sm₂ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Real.sqrt (s₂ * dd x)) U :=
    ContDiffOn.sqrt (contDiffOn_const.mul hdd_sm) (fun x hx => ne_of_gt (hU_dd x hx))
  have hww_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ww U := by
    rw [hww]
    exact hsqrt_sm₂.mul hxi1_sm
  have hF_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U := by
    rw [hF]
    exact ((huu_sm.smul contDiffOn_const).add (hww_sm.smul contDiffOn_const))
  -- value of `F` at `x₀`
  have hF0 : F x₀ = 0 := by
    rw [hF]
    simp [huu, hww, hxi0_0, hxi1_0]
  -- the key identity
  have hcoord : ∀ x : Plane, ∀ i : Fin 2,
      x i - x₀ i = xi0 x * (V p q i) + xi1 x * (Wv p q i) := by
    intro x i
    have hz := vec_decomp p q (p ^ 2 + q ^ 2) rfl hpq (x - x₀)
    have := congrArg (fun z : Plane => z i) hz
    rw [hxi0, hxi1]
    simpa using this
  have hkey : ∀ x : Plane, g x - g x₀
      = aa x * (xi0 x) ^ 2 + 2 * bb x * (xi0 x) * (xi1 x) + cc x * (xi1 x) ^ 2 := by
    intro x
    rw [hexp x, haa, hbb, hcc]
    simp only [Fin.sum_univ_two]
    rw [hcoord x 0, hcoord x 1, hsymm 1 0 x]
    ring
  -- the identity on `U`
  have hkeyU : ∀ x ∈ U, g x = g x₀ + s₁ * (uu x) ^ 2 + s₂ * (ww x) ^ 2 := by
    intro x hx
    have haapos : 0 < s₁ * aa x := hx.1
    have hddpos : 0 < s₂ * dd x := hU_dd x hx
    have haane : aa x ≠ 0 := hU_aa x hx
    have hsq1 : Real.sqrt (s₁ * aa x) ^ 2 = s₁ * aa x := Real.sq_sqrt (le_of_lt haapos)
    have hsq2 : Real.sqrt (s₂ * dd x) ^ 2 = s₂ * dd x := Real.sq_sqrt (le_of_lt hddpos)
    have hs1sq : s₁ ^ 2 = 1 := by rcases hs₁_pm with h1 | h1 <;> rw [h1] <;> norm_num
    have hs2sq : s₂ ^ 2 = 1 := by rcases hs₂_pm with h1 | h1 <;> rw [h1] <;> norm_num
    have hsq : (uu x) ^ 2 = s₁ * (aa x * (xi0 x + (bb x / aa x) * xi1 x) ^ 2) := by
      rw [huu, mul_pow, hsq1]
      ring
    have hsq' : (ww x) ^ 2 = s₂ * (dd x * (xi1 x) ^ 2) := by
      rw [hww, mul_pow, hsq2]
      ring
    have halg : aa x * (xi0 x) ^ 2 + 2 * bb x * (xi0 x) * (xi1 x) + cc x * (xi1 x) ^ 2
        = aa x * (xi0 x + (bb x / aa x) * xi1 x) ^ 2 + dd x * (xi1 x) ^ 2 := by
      rw [hdd]; field_simp; try ring
    have e1 : s₁ * (uu x) ^ 2 = aa x * (xi0 x + (bb x / aa x) * xi1 x) ^ 2 := by
      rw [hsq, ← mul_assoc, ← sq, hs1sq, one_mul]
    have e2 : s₂ * (ww x) ^ 2 = dd x * (xi1 x) ^ 2 := by
      rw [hsq', ← mul_assoc, ← sq, hs2sq, one_mul]
    have hfin : aa x * (xi0 x + (bb x / aa x) * xi1 x) ^ 2 + dd x * (xi1 x) ^ 2
        = s₁ * (uu x) ^ 2 + s₂ * (ww x) ^ 2 := by
      rw [← e1, ← e2]
    have h := hkey x
    rw [halg, hfin] at h
    linarith [h]
  -- the derivative at `x₀`
  have hdiff_aa : DifferentiableAt ℝ aa x₀ := haa_sm.contDiffAt.differentiableAt (by simp)
  have hdiff_bb : DifferentiableAt ℝ bb x₀ := hbb_sm.contDiffAt.differentiableAt (by simp)
  have hdiff_dd : DifferentiableAt ℝ dd x₀ := (hdd_sm.contDiffAt (hUopen.mem_nhds hx₀U)).differentiableAt (by simp)
  have hdiff_div : DifferentiableAt ℝ (fun x => bb x / aa x) x₀ :=
    (hdiv_sm.contDiffAt (hUopen.mem_nhds hx₀U)).differentiableAt (by simp)
  have huu_deriv : HasFDerivAt uu
      (Real.sqrt (s₁ * aa x₀) •
        (coef0 p q (p ^ 2 + q ^ 2) + (bb x₀ / aa x₀) • coef1 p q (p ^ 2 + q ^ 2))) x₀ := by
    have h := hasFDerivAt_sqrt_mul_shear aa bb x₀ s₁ (coef0 p q (p ^ 2 + q ^ 2))
      (coef1 p q (p ^ 2 + q ^ 2)) hdiff_aa hdiff_div hs₁_pos
    rw [show uu = fun x : Plane => Real.sqrt (s₁ * aa x) *
        (coef0 p q (p ^ 2 + q ^ 2) x - coef0 p q (p ^ 2 + q ^ 2) x₀
          + (bb x / aa x) * (coef1 p q (p ^ 2 + q ^ 2) x - coef1 p q (p ^ 2 + q ^ 2) x₀))
        from by funext x; simp only [huu, hxi0_eq, hxi1_eq]]
    exact h
  have hww_deriv : HasFDerivAt ww
      (Real.sqrt (s₂ * dd x₀) • coef1 p q (p ^ 2 + q ^ 2)) x₀ := by
    have h := hasFDerivAt_sqrt_mul dd x₀ s₂ (coef1 p q (p ^ 2 + q ^ 2)) hdiff_dd hs₂_pos
    rw [show ww = fun x : Plane => Real.sqrt (s₂ * dd x) *
        (coef1 p q (p ^ 2 + q ^ 2) x - coef1 p q (p ^ 2 + q ^ 2) x₀)
        from by funext x; simp only [hww, hxi1_eq]]
    exact h
  set Lc : Plane →L[ℝ] Plane :=
    (Real.sqrt (s₁ * aa x₀) • (coef0 p q (p ^ 2 + q ^ 2)
        + (bb x₀ / aa x₀) • coef1 p q (p ^ 2 + q ^ 2))).smulRight e0
    + (Real.sqrt (s₂ * dd x₀) • coef1 p q (p ^ 2 + q ^ 2)).smulRight e1 with hLc
  have hF_deriv : HasFDerivAt F Lc x₀ := by
    rw [hF, hLc]
    exact (huu_deriv.smul_const e0).add (hww_deriv.smul_const e1)
  -- `Lc` is invertible
  set Li : Plane →L[ℝ] Plane :=
    ((1 / Real.sqrt (s₁ * aa x₀)) • co 0
      - ((bb x₀ / aa x₀) * (1 / Real.sqrt (s₂ * dd x₀))) • co 1).smulRight (V p q)
    + ((1 / Real.sqrt (s₂ * dd x₀)) • co 1).smulRight (Wv p q) with hLi
  have hsqrt1 : Real.sqrt (s₁ * aa x₀) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs₁_pos)
  have hsqrt2 : Real.sqrt (s₂ * dd x₀) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs₂_pos)
  have haa0' : aa x₀ ≠ 0 := haa0_ne
  have hLi_right : ∀ z : Plane, Lc (Li z) = (z 0) • e0 + (z 1) • e1 := by
    intro z
    rw [hLc, hLi]
    ext i; fin_cases i <;>
      · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply, coef0_apply, coef1_apply, co_apply,
          e0, e1, V, Wv]
        simp
        field_simp
        try ring
  have hLi_left : ∀ y : Plane, Li (Lc y)
      = coef0 p q (p ^ 2 + q ^ 2) y • V p q + coef1 p q (p ^ 2 + q ^ 2) y • Wv p q := by
    intro y
    rw [hLc, hLi]
    ext i; fin_cases i <;>
      · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply, coef0_apply, coef1_apply, co_apply,
          e0, e1, V, Wv]
        simp
        field_simp
        try ring
  have hLi_left' : ∀ y : Plane, Li (Lc y) = y := by
    intro y
    rw [hLi_left y, ← vec_decomp p q (p ^ 2 + q ^ 2) rfl hpq y]
  have hc1 : ∀ z : Plane, z = (z 0) • e0 + (z 1) • e1 := e_decomp
  have hbij : Function.Bijective Lc :=
    ⟨fun a b hab => by
        have := congrArg Li hab
        rwa [hLi_left', hLi_left'] at this,
      fun z => ⟨Li z, by rw [hLi_right]; exact (hc1 z).symm⟩⟩
  let L : Plane ≃L[ℝ] Plane :=
    (LinearEquiv.ofBijective Lc.toLinearMap hbij).toContinuousLinearEquiv
  have hLcoe : (L : Plane →L[ℝ] Plane) = Lc := rfl
  have hL_deriv : HasFDerivAt F (L : Plane →L[ℝ] Plane) x₀ := by
    rw [hLcoe]; exact hF_deriv
  -- apply the inverse function theorem
  obtain ⟨φ, hx₀φ, hφU, hφF, -, hφ_sm, hφsymm_sm⟩ := by
    exact exists_local_diffeomorph F U x₀ hUopen hx₀U hF_sm L hL_deriv
  refine ⟨φ, s₁, s₂, hx₀φ, ?_, hφ_sm, hφsymm_sm, hs₁_pm, hs₂_pm, ?_⟩
  · rw [hφF x₀ hx₀φ, hF0]
  · intro y hy
    have hykey := hkeyU y (hφU hy)
    have h1 : φ y = F y := hφF y hy
    have h2 : uu y = φ y 0 := by rw [h1, hF]; simp [e0, e1]
    have h3 : ww y = φ y 1 := by rw [h1, hF]; simp [e0, e1]
    rw [← h2, ← h3]
    exact hykey

/-- **The Morse lemma in the plane.** -/
theorem morseLemma2 : Work.Drive.Morse.MorseLemma2 := by
  intro g x₀ hg hcrit hnondeg
  obtain ⟨h, hsmooth, hsymm, hexp, hval⟩ := hadamard2 g x₀ hg hcrit
  exact morse_of_hadamard g x₀ hg hnondeg h hsmooth hsymm hexp hval

end Work.Drive.N2
