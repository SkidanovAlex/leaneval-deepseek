import Mathlib
import Submission.Work.Asymptotics.kernelTransform_seminorm_cuspHalf_TS_prelude
import Submission.Work.Asymptotics.Gcusp24_vadd_int

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Topology

noncomputable section

/-!
# The `(T-I)²`-annihilation of the cusp model `Aexp (Gcusp ℓ d)`

`(T-I)² K = 0` (`Work.Residues.Kfun_T2`) makes the cusp-expansion coefficients `Gcusp24 ℓ i j`
affine along `τ ↦ τ + 1`, hence the same holds for the model
`Aexp G τ t = G₀₀(τ) + it·G₀₁(τ) + e^{2πt}(G₁₀(τ) + it·G₁₁(τ))`.

This is the branch-compatible copy of the corresponding development in
`Submission/Work/Asymptotics/Kaxis_expansion_vadd_one.lean` / `Tile/tile_affine.lean`: it is
written on the import branch of `kernelTransform_seminorm_cuspHalf_TS` (the one containing the
`arcT`/`lowBad`/`Kcomp` cusp-`0` machinery), because the two branches cannot be co-imported.

## Main results

* `Work.Asymptotics.T2aux.Gcusp24_T2_all` : `(T-I)² Gcusp24 ℓ i j = 0`;
* `Work.Asymptotics.T2aux.Aexp_Gcusp24_T2` : `(T-I)² Aexp (Gcusp ℓ 24) = 0`.
-/

namespace T2aux

/-- `F` is `T`-periodic if `F (1+τ) = F τ`. -/
def TPeriodic (F : ℍ → ℂ) : Prop := ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ

theorem T2op_of_periodic' {F : ℍ → ℂ} (h : TPeriodic F) : Work.Kernels.T2op F = 0 := by
  ext τ
  have h2 : F ((2 : ℝ) +ᵥ τ) = F τ := by rw [Work.Kernels.vadd_one_add_one, h, h]
  simp only [Work.Kernels.T2op, Pi.zero_apply]
  rw [h2, h]
  ring

theorem T2op_const_mul' (c : ℂ) {F : ℍ → ℂ} (h : Work.Kernels.T2op F = 0) :
    Work.Kernels.T2op (fun τ : ℍ => c * F τ) = 0 := by
  ext τ
  have h1 := congr_fun h τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 ⊢
  linear_combination c * h1

theorem T2op_sub' {F G : ℍ → ℂ} (hF : Work.Kernels.T2op F = 0)
    (hG : Work.Kernels.T2op G = 0) : Work.Kernels.T2op (F - G) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  have h2 := congr_fun hG τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 h2
  simp only [Work.Kernels.T2op, Pi.sub_apply, Pi.zero_apply]
  linear_combination h1 - h2

theorem T2op_of_eq' {F G : ℍ → ℂ} (h : ∀ τ, F τ = G τ) (hG : Work.Kernels.T2op G = 0) :
    Work.Kernels.T2op F = 0 := by
  have hFG : F = G := funext h
  rw [hFG]; exact hG

theorem T2op_div_const' (c : ℂ) {F : ℍ → ℂ} (h : Work.Kernels.T2op F = 0) :
    Work.Kernels.T2op (fun τ : ℍ => F τ / c) = 0 := by
  refine T2op_of_eq' (fun τ => ?_) (T2op_const_mul' c⁻¹ h)
  rw [div_eq_mul_inv, mul_comm]

theorem T2op_id' : Work.Kernels.T2op (fun τ : ℍ => (τ : ℂ)) = 0 := by
  ext τ
  simp only [Work.Kernels.T2op, Pi.zero_apply]
  rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem phi0_vadd_one' (τ : ℍ) :
    Work.Kernels.phi0 ((1 : ℝ) +ᵥ τ) = Work.Kernels.phi0 τ + Work.Kernels.E2Fun τ := by
  unfold Work.Kernels.phi0
  rw [Work.Kernels.E2Fun_vadd_one, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem phi2_vadd_one' (τ : ℍ) :
    Work.Kernels.phi2 ((1 : ℝ) +ᵥ τ) = Work.Kernels.phi2 τ + (Work.Kernels.E2Fun τ) ^ 2 := by
  unfold Work.Kernels.phi2
  rw [Work.Kernels.E2Fun_vadd_one, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem T2op_phi0' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phi0 τ) = 0 := by
  ext τ
  simp only [Work.Kernels.T2op, Pi.zero_apply]
  rw [Work.Kernels.vadd_one_add_one]
  simp only [phi0_vadd_one', Work.Kernels.E2Fun_vadd_one]
  ring

theorem T2op_phi2' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phi2 τ) = 0 := by
  ext τ
  simp only [Work.Kernels.T2op, Pi.zero_apply]
  rw [Work.Kernels.vadd_one_add_one]
  simp only [phi2_vadd_one', Work.Kernels.E2Fun_vadd_one]
  ring

theorem T2op_phiVec0' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 0) = 0 :=
  T2op_of_eq' (fun τ => rfl) T2op_id'

theorem T2op_phiVec1' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 1) = 0 :=
  T2op_of_eq' (fun τ => rfl) T2op_phi0'

theorem T2op_phiVec2' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 2) = 0 :=
  T2op_of_eq' (fun τ => rfl) T2op_phi2'

theorem T2op_E4' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ) = 0 :=
  T2op_of_periodic' (fun τ => Work.Kernels.KernelFacts.E4Fun_vadd_one τ)

theorem T2op_E6' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E6Fun τ) = 0 :=
  T2op_of_periodic' (fun τ => Work.Kernels.KernelFacts.E6Fun_vadd_one τ)

theorem T2op_Delta' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.DeltaFun τ) = 0 :=
  T2op_of_periodic' (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ)

theorem T2op_const' (c : ℂ) : Work.Kernels.T2op (fun _ : ℍ => c) = 0 :=
  T2op_of_periodic' (fun _ => rfl)

/-- `E₄²E₆` is `T`-invariant. -/
theorem per_E4sq_E6' : TPeriodic (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) :=
  fun τ => by
    simp only []
    rw [Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one]

/-- `E₄³` is `T`-invariant. -/
theorem per_E4cube' : TPeriodic (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3) :=
  fun τ => by simp only []; rw [Work.Kernels.KernelFacts.E4Fun_vadd_one]

/-- `E₄E₆` is `T`-invariant. -/
theorem per_E4_E6' : TPeriodic (fun τ : ℍ => Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) :=
  fun τ => by
    simp only []
    rw [Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one]

/-- `E₄²` is `T`-invariant. -/
theorem per_E4sq' : TPeriodic (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2) :=
  fun τ => by simp only []; rw [Work.Kernels.KernelFacts.E4Fun_vadd_one]

theorem T2op_E4cube' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3) = 0 :=
  T2op_of_periodic' per_E4cube'

theorem T2op_E4sq_E6' :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) = 0 :=
  T2op_of_periodic' per_E4sq_E6'

theorem T2op_E4_E6' :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) = 0 :=
  T2op_of_periodic' per_E4_E6'

theorem T2op_E4sq' : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 2) = 0 :=
  T2op_of_periodic' per_E4sq'


theorem T2op_add' {F G : ℍ → ℂ} (hF : Work.Kernels.T2op F = 0) (hG : Work.Kernels.T2op G = 0) :
    Work.Kernels.T2op (F + G) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  have h2 := congr_fun hG τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 h2
  simp only [Work.Kernels.T2op, Pi.add_apply, Pi.zero_apply]
  linear_combination h1 + h2

/-- The explicit interior of `Gcusp24 ℓ 0 0` (without the outer `/2`). -/
noncomputable def gcusp00aux (ℓ : Work.Kernels.LogLambdaData) : ℍ → ℂ := fun τ =>
  -(13 * Complex.I / 12) * (Work.Kernels.phiVec τ 0
      * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))
  + (Complex.I / 6) * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
  - 168 * Complex.I * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
  - (Complex.I / 12) * (Work.Kernels.phiVec τ 2
      * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
  - 720 * Work.Kernels.DeltaFun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
  - 36 * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)
  + Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
  - 7 * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
      / (24 * (Real.pi : ℂ))
  - 5 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2) / (24 * (Real.pi : ℂ))

/-- The explicit interior of `Gcusp24 ℓ 0 1` (without the outer `/2`). -/
noncomputable def gcusp01aux (ℓ : Work.Kernels.LogLambdaData) : ℍ → ℂ := fun τ =>
  (Real.pi : ℂ) / 3
    * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
      + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
      - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
  - Complex.I * (720 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)

theorem Gcusp24_T2_zero_zero (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 0 0 τ) = 0 := by
  have h1 : Work.Kernels.T2op (fun τ : ℍ => -(13 * Complex.I / 12)
      * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))) = 0 :=
    T2op_const_mul' _ (Work.Kernels.T2op_mul_of T2op_phiVec0' per_E4sq_E6')
  have h2 : Work.Kernels.T2op (fun τ : ℍ => (Complex.I / 6)
      * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
    T2op_const_mul' _ (Work.Kernels.T2op_mul_of T2op_phiVec1' per_E4cube')
  have h3 : Work.Kernels.T2op (fun τ : ℍ => 168 * Complex.I * (Work.Kernels.phiVec τ 1
      * Work.Kernels.DeltaFun τ)) = 0 :=
    T2op_const_mul' _ (Work.Kernels.T2op_mul_of T2op_phiVec1'
      (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ))
  have h4 : Work.Kernels.T2op (fun τ : ℍ => (Complex.I / 12)
      * (Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) = 0 :=
    T2op_const_mul' _ (Work.Kernels.T2op_mul_of T2op_phiVec2' per_E4_E6')
  have h5 : Work.Kernels.T2op (fun τ : ℍ => 720 * Work.Kernels.DeltaFun τ
      * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) = 0 :=
    T2op_of_eq' (G := fun τ : ℍ => 720 * (Work.Kernels.DeltaFun τ
        * Work.Asymptotics.cuspL ℓ) / (Real.pi : ℂ)) (fun τ => by ring)
      (T2op_div_const' _ (T2op_const_mul' 720 (Work.Kernels.T2op_mul_of T2op_Delta'
        (fun _ => rfl))))
  have h6 : Work.Kernels.T2op (fun τ : ℍ => 36 * Work.Kernels.DeltaFun τ
      / (Real.pi : ℂ)) = 0 :=
    T2op_div_const' _ (T2op_const_mul' 36 T2op_Delta')
  have h7 : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3
      * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) = 0 :=
    T2op_div_const' _ (Work.Kernels.T2op_mul_of T2op_E4cube' (fun _ => rfl))
  have h8 : Work.Kernels.T2op (fun τ : ℍ => 7 * (Work.Kernels.psi2 ℓ τ
      * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)) / (24 * (Real.pi : ℂ))) = 0 :=
    T2op_div_const' _ (T2op_const_mul' 7 (Work.Kernels.T2op_mul_of
      (Work.Kernels.KernelFacts.psi2_T2 ℓ) per_E4_E6'))
  have h9 : Work.Kernels.T2op (fun τ : ℍ => 5 * (Work.Kernels.psi4 ℓ τ
      * Work.Kernels.E4Fun τ ^ 2) / (24 * (Real.pi : ℂ))) = 0 :=
    T2op_div_const' _ (T2op_const_mul' 5 (Work.Kernels.T2op_mul_of
      (Work.Kernels.KernelFacts.psi4_T2 ℓ) per_E4sq'))
  have hmain : Work.Kernels.T2op (fun τ : ℍ => gcusp00aux ℓ τ) = 0 := by
    simp only [gcusp00aux]
    ext τ
    have g1 := congr_fun h1 τ
    have g2 := congr_fun h2 τ
    have g3 := congr_fun h3 τ
    have g4 := congr_fun h4 τ
    have g5 := congr_fun h5 τ
    have g6 := congr_fun h6 τ
    have g7 := congr_fun h7 τ
    have g8 := congr_fun h8 τ
    have g9 := congr_fun h9 τ
    simp only [Work.Kernels.T2op, Pi.zero_apply] at g1 g2 g3 g4 g5 g6 g7 g8 g9 ⊢
    linear_combination g1 + g2 - g3 - g4 - g5 - g6 + g7 - g8 - g9
  have hhalf : Work.Kernels.T2op (fun τ : ℍ => gcusp00aux ℓ τ / 2) = 0 :=
    T2op_div_const' 2 hmain
  have heq : (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 0 0 τ)
      = fun τ : ℍ => gcusp00aux ℓ τ / 2 := by
    funext τ
    rw [Work.Asymptotics.Gcusp24, if_pos (by decide : ((0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0))]
    simp only [gcusp00aux]
    try ring_nf
  rw [heq]
  exact hhalf

theorem Gcusp24_T2_zero_one (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 0 1 τ) = 0 := by
  have h1 : Work.Kernels.T2op (fun τ : ℍ => (Real.pi : ℂ) / 3
      * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))) = 0 :=
    T2op_const_mul' _ (Work.Kernels.T2op_mul_of T2op_phiVec0' per_E4sq_E6')
  have h2 : Work.Kernels.T2op (fun τ : ℍ => (Real.pi : ℂ) / 3
      * (720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ))) = 0 :=
    T2op_const_mul' _ (T2op_const_mul' 720 (Work.Kernels.T2op_mul_of T2op_phiVec1'
      (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ)))
  have h3 : Work.Kernels.T2op (fun τ : ℍ => (Real.pi : ℂ) / 3
      * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
    T2op_const_mul' _ (Work.Kernels.T2op_mul_of T2op_phiVec1' per_E4cube')
  have h4 : Work.Kernels.T2op (fun τ : ℍ => 720 * Work.Kernels.DeltaFun τ) = 0 :=
    T2op_const_mul' 720 T2op_Delta'
  have h5 : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3) = 0 := T2op_E4cube'
  have hmain : Work.Kernels.T2op (fun τ : ℍ => gcusp01aux ℓ τ) = 0 := by
    simp only [gcusp01aux]
    ext τ
    have g1 := congr_fun h1 τ
    have g2 := congr_fun h2 τ
    have g3 := congr_fun h3 τ
    have g4 := congr_fun h4 τ
    have g5 := congr_fun h5 τ
    simp only [Work.Kernels.T2op, Pi.zero_apply] at g1 g2 g3 g4 g5 ⊢
    linear_combination g1 + g2 - g3 - Complex.I * (g4 - g5)
  have hhalf : Work.Kernels.T2op (fun τ : ℍ => gcusp01aux ℓ τ / 2) = 0 :=
    T2op_div_const' 2 hmain
  have heq : (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 0 1 τ)
      = fun τ : ℍ => gcusp01aux ℓ τ / 2 := by
    funext τ
    rw [Work.Asymptotics.Gcusp24,
      if_neg (by decide : ¬ ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 0)),
      if_pos (by decide : ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 1))]
    simp only [gcusp01aux]
    try ring_nf
  rw [heq]
  exact hhalf

theorem Gcusp24_T2_one (ℓ : Work.Kernels.LogLambdaData) (j : Fin 2) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 1 j τ) = 0 := by
  ext τ
  have h := Work.Asymptotics.Gcusp24_vadd_int ℓ j τ 2
  simp only [Work.Kernels.T2op, Pi.zero_apply]
  push_cast at h
  linear_combination h

theorem Gcusp24_T2_all (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ i j τ) = 0 := by
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with hi | hi
  · subst hi
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with hj | hj
    · subst hj; exact Gcusp24_T2_zero_zero ℓ
    · subst hj; exact Gcusp24_T2_zero_one ℓ
  · subst hi
    exact Gcusp24_T2_one ℓ j

/-- `(T-I)²` of the cusp model: it is a `τ`-independent combination of the `G i j`. -/
theorem T2op_Aexp' {G : Fin 2 → Fin 2 → ℍ → ℂ} (h : ∀ i j, Work.Kernels.T2op (G i j) = 0)
    (t : ℝ) : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Aexp G τ t) = 0 := by
  ext τ
  have g00 := congr_fun (h 0 0) τ
  have g01 := congr_fun (h 0 1) τ
  have g10 := congr_fun (h 1 0) τ
  have g11 := congr_fun (h 1 1) τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at g00 g01 g10 g11 ⊢
  simp only [Work.Asymptotics.Aexp]
  linear_combination g00 + ((t : ℂ) * Complex.I) * g01
    + Complex.exp (2 * Real.pi * t) * (g10 + ((t : ℂ) * Complex.I) * g11)

/-- **The `(T-I)²`-annihilation of the cusp model `Aexp (Gcusp ℓ 24)`.** -/
theorem Aexp_Gcusp24_T2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) (t : ℝ) :
    Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((2 : ℝ) +ᵥ τ) t
      - 2 * Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((1 : ℝ) +ᵥ τ) t
      + Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t = 0 := by
  have h := congr_fun (T2op_Aexp' (G := Work.Asymptotics.Gcusp ℓ 24)
    (fun i j => Gcusp24_T2_all ℓ i j) t) τ
  simpa only [Work.Kernels.T2op, Pi.zero_apply] using h

end T2aux

end

end Work.Asymptotics
