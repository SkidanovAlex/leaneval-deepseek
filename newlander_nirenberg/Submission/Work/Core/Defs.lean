import ChallengeDeps

open LeanEval.Geometry.NewlanderNirenberg
open Set
open scoped ContDiff

namespace Submission

variable {n : ℕ}

/-- `ℂⁿ`, viewed as a real vector space, is the target of the holomorphic charts. -/
abbrev F (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The standard complex structure on `ℂⁿ`: multiplication by `i`. -/
noncomputable def Jstd (n : ℕ) : F n → F n →L[ℝ] F n :=
  fun _ => Complex.I • (1 : F n →L[ℝ] F n)

@[simp] lemma Jstd_apply (n : ℕ) (z v : F n) : Jstd n z v = Complex.I • v := by
  simp [Jstd]

lemma Jstd_sq (n : ℕ) (z v : F n) : Jstd n z (Jstd n z v) = -v := by
  simp [smul_smul]

/-- `i*(i*z) = -z`. -/
lemma I_mul_I_mul (z : ℂ) : Complex.I * (Complex.I * z) = -z := by
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc Complex.I * (Complex.I * z) = (Complex.I * Complex.I) * z := by ring
    _ = -1 * z := by rw [h]
    _ = -z := by ring

/-- If `a + i b = 0` then `b = i a`. -/
lemma eq_I_mul_of_add_eq_zero {a b : ℂ} (h : a + Complex.I * b = 0) : b = Complex.I * a := by
  have h1 : Complex.I * b = -a := by linear_combination h
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc b = 1 * b := by ring
    _ = (-(Complex.I * Complex.I)) * b := by rw [hI]; ring
    _ = (-Complex.I) * (Complex.I * b) := by ring
    _ = (-Complex.I) * (-a) := by rw [h1]
    _ = Complex.I * a := by ring

/-- The `(0,1)`-part `∂̄u = (1/2)(du + i·du∘J)` of the differential of a complex valued
function, as a complex valued real-linear form.  It vanishes exactly when `u` is
`J`-holomorphic. -/
noncomputable def dbar (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x : E n) : E n →L[ℝ] ℂ :=
  (1/2 : ℝ) • (fderiv ℝ u x + Complex.I • ((fderiv ℝ u x).comp (J x)))

/-- The `(1,0)`-part `∂u = (1/2)(du - i·du∘J)`. -/
noncomputable def dpartial (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x : E n) : E n →L[ℝ] ℂ :=
  (1/2 : ℝ) • (fderiv ℝ u x - Complex.I • ((fderiv ℝ u x).comp (J x)))

lemma dbar_apply (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x v : E n) :
    dbar J u x v = (1/2 : ℂ) * (fderiv ℝ u x v + Complex.I * fderiv ℝ u x (J x v)) := by
  simp [dbar, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

lemma dbar_add_dpartial (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x : E n) :
    dbar J u x + dpartial J u x = fderiv ℝ u x := by
  ext v
  simp [dbar, dpartial, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

/-- `u` is `J`-holomorphic at `x`: its real differential is complex linear. -/
def IsJHolomorphicAt (J : E n → E n →L[ℝ] E n) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] (u : E n → G) (x : E n) : Prop :=
  ∀ v : E n, fderiv ℝ u x (J x v) = Complex.I • fderiv ℝ u x v

/-- `u` is `J`-holomorphic on `U`. -/
def IsJHolomorphicOn (J : E n → E n →L[ℝ] E n) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] (u : E n → G) (U : Set (E n)) : Prop :=
  ∀ x ∈ U, IsJHolomorphicAt J u x

lemma dbar_eq_zero_iff (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x : E n) :
    dbar J u x = 0 ↔ IsJHolomorphicAt J u x := by
  constructor
  · intro h v
    have hv : dbar J u x v = 0 := by rw [h]; rfl
    rw [dbar_apply] at hv
    have h2 : fderiv ℝ u x v + Complex.I * fderiv ℝ u x (J x v) = 0 := by
      have h3 := congrArg (fun z : ℂ => (2 : ℂ) * z) hv
      simpa using h3
    have := eq_I_mul_of_add_eq_zero h2
    simpa [smul_eq_mul] using this
  · intro h
    ext v
    rw [dbar_apply, zero_apply]
    rw [show fderiv ℝ u x (J x v) = Complex.I * fderiv ℝ u x v by
      simpa [smul_eq_mul] using h v]
    rw [I_mul_I_mul]
    ring

/-- The complexified vector field `X + i·JX`, which is of type `(0,1)`. -/
def Z01 (J : E n → E n →L[ℝ] E n) (X : E n → E n) : E n → E n × E n :=
  fun x => (X x, J x (X x))

/-- The `(1,0)`-projection of a complexified vector `(a,b)` (representing `a + i b`). -/
noncomputable def proj10 (J : E n → E n →L[ℝ] E n) (x : E n) (z : E n × E n) : E n × E n :=
  ((1/2 : ℝ) • (z.1 + J x z.2), (1/2 : ℝ) • (z.2 - J x z.1))

/-- The `(0,1)`-projection of a complexified vector `(a,b)` (representing `a + i b`). -/
noncomputable def proj01 (J : E n → E n →L[ℝ] E n) (x : E n) (z : E n × E n) : E n × E n :=
  ((1/2 : ℝ) • (z.1 - J x z.2), (1/2 : ℝ) • (z.2 + J x z.1))

/-- The Lie bracket of complexified vector fields, in the real-imaginary pair picture. -/
noncomputable def cbracket (Z W : E n → E n × E n) (x : E n) : E n × E n :=
  (VectorField.lieBracket ℝ (fun y => (Z y).1) (fun y => (W y).1) x
     - VectorField.lieBracket ℝ (fun y => (Z y).2) (fun y => (W y).2) x,
   VectorField.lieBracket ℝ (fun y => (Z y).1) (fun y => (W y).2) x
     + VectorField.lieBracket ℝ (fun y => (Z y).2) (fun y => (W y).1) x)


/-- Pairing of a complex valued form with a complexified vector `A + i B`. -/
def cpair (om : E n →L[ℝ] ℂ) (z : E n × E n) : ℂ := om z.1 + Complex.I * om z.2

/-- Derivative of a complex valued function along the complexified vector field `A + iB`. -/
noncomputable def czderiv (g : E n → ℂ) (Z : E n → E n × E n) (x : E n) : ℂ :=
  fderiv ℝ g x (Z x).1 + Complex.I * fderiv ℝ g x (Z x).2

/-- The `(0,2)`-part of `d(∂̄u)` evaluated on the real vector fields `X`, `Y`: the expression
`(1/4)·(Z_X(∂̄u(Z_Y)) - Z_Y(∂̄u(Z_X)) - ∂̄u([Z_X,Z_Y]))` with `Z_X = X + iJX`.  It vanishes
exactly when the `∂̄`-operator satisfies `∂̄² = 0`, i.e. when the Nijenhuis tensor vanishes. -/
noncomputable def dbarSq (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (X Y : E n → E n)
    (x : E n) : ℂ :=
  czderiv (fun y => cpair (dbar J u y) (Z01 J Y y)) (Z01 J X) x
    - czderiv (fun y => cpair (dbar J u y) (Z01 J X y)) (Z01 J Y) x
    - cpair (dbar J u x) (cbracket (Z01 J X) (Z01 J Y) x)



/-- The continuous linear equivalence between `Fin n → ℂ` (with the sup norm) and the Euclidean
space `ℂⁿ`. -/
noncomputable def ec (n : ℕ) : (Fin n → ℂ) ≃L[ℂ] F n :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm

/-- The same map, as a real-linear continuous linear map. -/
noncomputable def ecL (n : ℕ) : (Fin n → ℂ) →L[ℝ] F n :=
  (ec n : (Fin n → ℂ) →L[ℂ] F n).restrictScalars ℝ

/-- The same map, as a real-linear continuous linear equivalence. -/
noncomputable def ecR (n : ℕ) : (Fin n → ℂ) ≃L[ℝ] F n :=
  (LinearEquiv.restrictScalars ℝ (ec n).toLinearEquiv).toContinuousLinearEquiv

@[simp] lemma ecL_apply (n : ℕ) (z : Fin n → ℂ) : ecL n z = ec n z := rfl

@[simp] lemma ecR_coe (n : ℕ) : (ecR n : (Fin n → ℂ) →L[ℝ] F n) = ecL n := rfl

lemma ecL_smul (n : ℕ) (c : ℂ) (z : Fin n → ℂ) : ecL n (c • z) = c • ecL n z :=
  (ec n).map_smul c z



/-- The inverse of `ecL`, as a real-linear continuous linear map. -/
noncomputable def ecInvL (n : ℕ) : F n →L[ℝ] (Fin n → ℂ) :=
  ((ec n).symm : F n →L[ℂ] (Fin n → ℂ)).restrictScalars ℝ

/-- The inverse of `ecR`, as a real-linear continuous linear equivalence. -/
noncomputable def ecInv (n : ℕ) : F n ≃L[ℝ] (Fin n → ℂ) :=
  (LinearEquiv.restrictScalars ℝ (ec n).symm.toLinearEquiv).toContinuousLinearEquiv

@[simp] lemma ecInv_coe (n : ℕ) : (ecInv n : F n →L[ℝ] (Fin n → ℂ)) = ecInvL n := rfl

@[simp] lemma ecInvL_apply (n : ℕ) (z : F n) : ecInvL n z = (ec n).symm z := rfl



lemma ecInvL_smul (n : ℕ) (c : ℂ) (z : F n) : ecInvL n (c • z) = c • ecInvL n z :=
  ((ec n).symm).map_smul c z

lemma proj_smul (n : ℕ) (j : Fin n) (c : ℂ) (z : Fin n → ℂ) :
    (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℝ] ℂ) (c • z)
      = c • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℝ] ℂ) z := by
  simp [Pi.smul_apply, smul_eq_mul]



/-- `∂̄` is additive in the function. -/
lemma dbar_sub (J : E n → E n →L[ℝ] E n) (u1 u2 : E n → ℂ) (y : E n)
    (h1 : DifferentiableAt ℝ u1 y) (h2 : DifferentiableAt ℝ u2 y) :
    dbar J (fun z => u1 z - u2 z) y = dbar J u1 y - dbar J u2 y := by
  ext v
  simp only [dbar, sub_apply, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    show (fun z : E n => u1 z - u2 z) = u1 - u2 from rfl, fderiv_sub h1 h2, Complex.real_smul]
  ring

lemma dbar_add (J : E n → E n →L[ℝ] E n) (u1 u2 : E n → ℂ) (y : E n)
    (h1 : DifferentiableAt ℝ u1 y) (h2 : DifferentiableAt ℝ u2 y) :
    dbar J (fun z => u1 z + u2 z) y = dbar J u1 y + dbar J u2 y := by
  ext v
  simp only [dbar, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    show (fun z : E n => u1 z + u2 z) = u1 + u2 from rfl, fderiv_add h1 h2,
    ContinuousLinearMap.add_comp, Complex.real_smul]
  ring

/-- `∂̄` of a constant function vanishes. -/
lemma dbar_const (J : E n → E n →L[ℝ] E n) (c : ℂ) (y : E n) :
    dbar J (fun _ : E n => c) y = 0 := by
  ext v
  simp [dbar]


end Submission
