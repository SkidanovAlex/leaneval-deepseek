/-
# The cusp expansion of the kernel at a `T`-translate

`Work.Asymptotics.cuspExpansionKernel` gives the cusp-`i∞` expansion of the kernel along the
contour, uniformly on a compact `K ⊆ 𝒟`:

  `‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖ ≤ C (1+t)^M e^{-π(t-T₀)}`.

The present file transfers it to the `T`-translate `τ = 1 + u` of a point `u` with
`u, u - 1 ∈ 𝒟`: this is the "vadd one" translate that occurs in
`Work.Asymptotics.Kaxis24_pair_gate`, `Work.Asymptotics.pair_gate_wide` and the tile estimates.
(`u - 1 ∈ 𝒟` forces `Re u > 0`, hence `Re τ > 1`, so that the poles `SL(2,ℤ)·τ` of
`z ↦ K(τ,z)` all have non-zero real part and miss the contour; the translate is therefore not
covered by `cuspExpansionKernel` itself, which needs a compact `K ⊆ 𝒟`.)

The transfer is *exact and pointwise*: by CKMRV Theorem 4.9(2),
`(T - I)² K(·,z) = 0` (`Work.Residues.Kfun_T2`, here `Work.Asymptotics.Kaxis_Kfun_T2`), and the
same holds for the cusp model `Aexp (Gcusp ℓ d)` in the `τ`-variable because each coefficient
`Gcusp ℓ d i j` is a sum of products of the `(T-I)²`-annihilated atoms `φ_k`, `ψ_j` with
`T`-invariant modular forms (`T2op_Gcusp_kev` below).  Hence

  `F(1+u) = 2 F(u) - F(u-1)`   for `F = Kaxis (Kfun ℓ d) · t` and `F = Aexp (Gcusp ℓ d) · t`,

and the expansion at `1+u` is the corresponding combination of the expansions at `u` and `u-1`,
both of which lie in the compact set `{u, u-1} ⊆ 𝒟` to which `cuspExpansionKernel` applies.
In particular the two remaining hypotheses `1/2 < u.im` and `u.im < 3` are not used: the two
expansions are combined by an *exact* identity, so no uniformity of the estimate in `u` is
needed and a single compact pair `{u, u-1}` suffices.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.cuspExpansionKernel
import Submission.Work.Asymptotics.T2op_kernelTransform

set_option linter.unusedSimpArgs false

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

/-! The `T2op`-calculus and the `T`-affinity of the cusp-expansion coefficients, used to transfer
the cusp expansion along the translation `τ ↦ τ + 1`.  (`T2op F = 0` means
`F(τ+2) - 2F(τ+1) + F(τ) = 0`, i.e. `F` is affine along the `T`-direction; it is the `τ`-variable
form of CKMRV Theorem 4.9(2).) -/
namespace KevT2

open Work.Kernels

lemma T2op_of_eq' {F G : UpperHalfPlane → ℂ} (h : ∀ τ, F τ = G τ) (hG : T2op G = 0) : T2op F = 0 := by
  rw [show F = G from funext h]; exact hG

lemma T2op_const_mul' (c : ℂ) {F : UpperHalfPlane → ℂ} (h : T2op F = 0) :
    T2op (fun τ : UpperHalfPlane => c * F τ) = 0 := by
  ext τ
  have h1 := congr_fun h τ
  simp only [T2op, Pi.zero_apply] at h1 ⊢
  linear_combination c * h1

lemma T2op_mul_const (c : ℂ) {F : UpperHalfPlane → ℂ} (h : T2op F = 0) :
    T2op (fun τ : UpperHalfPlane => F τ * c) = 0 := by
  refine T2op_of_eq' (fun τ => ?_) (T2op_const_mul' c h)
  rw [mul_comm]

lemma T2op_sub' {F G : UpperHalfPlane → ℂ} (hF : T2op F = 0) (hG : T2op G = 0) :
    T2op (F - G) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  have h2 := congr_fun hG τ
  simp only [T2op, Pi.zero_apply] at h1 h2
  simp only [T2op, Pi.sub_apply, Pi.zero_apply]
  linear_combination h1 - h2

lemma T2op_div_const' (c : ℂ) {F : UpperHalfPlane → ℂ} (h : T2op F = 0) :
    T2op (fun τ : UpperHalfPlane => F τ / c) = 0 := by
  refine T2op_of_eq' (fun τ => ?_) (T2op_const_mul' c⁻¹ h)
  rw [div_eq_mul_inv, mul_comm]

lemma T2op_of_periodic' {F : UpperHalfPlane → ℂ}
    (h : ∀ τ : UpperHalfPlane, F ((1 : ℝ) +ᵥ τ) = F τ) : T2op F = 0 := by
  ext τ
  have h2 : F ((2 : ℝ) +ᵥ τ) = F τ := by rw [vadd_one_add_one, h, h]
  simp only [T2op, Pi.zero_apply]
  rw [h2, h]
  ring

/-- **The `T`-affine law.**  If `(T-I)²F = 0` then `F(τ+1) = 2F(τ) - F(τ-1)`. -/
lemma T2op_vadd_one_eq {F : UpperHalfPlane → ℂ} (hF : T2op F = 0) (u : UpperHalfPlane) :
    F ((1 : ℝ) +ᵥ u) = 2 * F u - F (((-1 : ℝ) +ᵥ u)) := by
  have h := congr_fun hF (((-1 : ℝ) +ᵥ u))
  simp only [T2op, Pi.zero_apply] at h
  rw [show (((2 : ℝ) +ᵥ (((-1 : ℝ) +ᵥ u))) : UpperHalfPlane) = (1 : ℝ) +ᵥ u from by
        rw [← add_vadd]; norm_num,
      show (((1 : ℝ) +ᵥ (((-1 : ℝ) +ᵥ u))) : UpperHalfPlane) = u from by
        rw [← add_vadd]; norm_num] at h
  linear_combination h

/-! ## The atoms -/

lemma phi0_vadd_one_kev (τ : UpperHalfPlane) :
    Work.Kernels.phi0 ((1 : ℝ) +ᵥ τ) = Work.Kernels.phi0 τ + Work.Kernels.E2Fun τ := by
  unfold Work.Kernels.phi0
  rw [Work.Kernels.E2Fun_vadd_one, UpperHalfPlane.coe_vadd]
  push_cast; ring

lemma phi2_vadd_one_kev (τ : UpperHalfPlane) :
    Work.Kernels.phi2 ((1 : ℝ) +ᵥ τ) = Work.Kernels.phi2 τ + (Work.Kernels.E2Fun τ) ^ 2 := by
  unfold Work.Kernels.phi2
  rw [Work.Kernels.E2Fun_vadd_one, UpperHalfPlane.coe_vadd]
  push_cast; ring

lemma T2op_id_kev : T2op (fun τ : UpperHalfPlane => (τ : ℂ)) = 0 := by
  ext τ
  simp only [T2op, Pi.zero_apply]
  rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd]
  push_cast; ring

lemma T2op_phi0_kev : T2op (fun τ : UpperHalfPlane => Work.Kernels.phi0 τ) = 0 := by
  ext τ
  simp only [T2op, Pi.zero_apply]
  rw [vadd_one_add_one]
  simp only [phi0_vadd_one_kev, Work.Kernels.E2Fun_vadd_one]
  ring

lemma T2op_phi2_kev : T2op (fun τ : UpperHalfPlane => Work.Kernels.phi2 τ) = 0 := by
  ext τ
  simp only [T2op, Pi.zero_apply]
  rw [vadd_one_add_one]
  simp only [phi2_vadd_one_kev, Work.Kernels.E2Fun_vadd_one]
  ring

lemma T2op_phiVec_kev (k : Fin 3) :
    T2op (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ k) = 0 := by
  fin_cases k
  · exact T2op_of_eq' (F := fun τ : UpperHalfPlane => (τ : ℂ)) (fun τ => by simp) T2op_id_kev
  · exact T2op_of_eq' (F := fun τ : UpperHalfPlane => Work.Kernels.phi0 τ) (fun τ => rfl)
      T2op_phi0_kev
  · exact T2op_of_eq' (F := fun τ : UpperHalfPlane => Work.Kernels.phi2 τ) (fun τ => rfl)
      T2op_phi2_kev

lemma per_E4sq_E6_kev : ∀ τ : UpperHalfPlane,
    (fun x : UpperHalfPlane => Work.Kernels.E4Fun x ^ 2 * Work.Kernels.E6Fun x) ((1 : ℝ) +ᵥ τ)
      = (fun x : UpperHalfPlane => Work.Kernels.E4Fun x ^ 2 * Work.Kernels.E6Fun x) τ := by
  intro τ
  simp only []
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one]

lemma per_E4cube_kev : ∀ τ : UpperHalfPlane,
    (fun x : UpperHalfPlane => Work.Kernels.E4Fun x ^ 3) ((1 : ℝ) +ᵥ τ)
      = (fun x : UpperHalfPlane => Work.Kernels.E4Fun x ^ 3) τ := by
  intro τ; simp only []; rw [Work.Kernels.KernelFacts.E4Fun_vadd_one]

lemma per_E4_E6_kev : ∀ τ : UpperHalfPlane,
    (fun x : UpperHalfPlane => Work.Kernels.E4Fun x * Work.Kernels.E6Fun x) ((1 : ℝ) +ᵥ τ)
      = (fun x : UpperHalfPlane => Work.Kernels.E4Fun x * Work.Kernels.E6Fun x) τ := by
  intro τ
  simp only []
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one]

lemma per_E4sq_kev : ∀ τ : UpperHalfPlane,
    (fun x : UpperHalfPlane => Work.Kernels.E4Fun x ^ 2) ((1 : ℝ) +ᵥ τ)
      = (fun x : UpperHalfPlane => Work.Kernels.E4Fun x ^ 2) τ := by
  intro τ; simp only []; rw [Work.Kernels.KernelFacts.E4Fun_vadd_one]

lemma per_Delta_kev : ∀ τ : UpperHalfPlane,
    (fun x : UpperHalfPlane => Work.Kernels.DeltaFun x) ((1 : ℝ) +ᵥ τ)
      = (fun x : UpperHalfPlane => Work.Kernels.DeltaFun x) τ :=
  fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ

lemma T2op_E4_kev : T2op (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ) = 0 :=
  T2op_of_periodic' (fun τ => Work.Kernels.KernelFacts.E4Fun_vadd_one τ)

lemma T2op_E6_kev : T2op (fun τ : UpperHalfPlane => Work.Kernels.E6Fun τ) = 0 :=
  T2op_of_periodic' (fun τ => Work.Kernels.KernelFacts.E6Fun_vadd_one τ)

lemma T2op_Delta_kev : T2op (fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ) = 0 :=
  T2op_of_periodic' per_Delta_kev

lemma T2op_E4cube_kev : T2op (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 3) = 0 :=
  T2op_of_periodic' per_E4cube_kev

lemma T2op_E4sq_E6_kev :
    T2op (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) = 0 :=
  T2op_of_periodic' per_E4sq_E6_kev

lemma T2op_E4_E6_kev :
    T2op (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) = 0 :=
  T2op_of_periodic' per_E4_E6_kev

lemma T2op_E4sq_kev : T2op (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 2) = 0 :=
  T2op_of_periodic' per_E4sq_kev

/-! ## The affinity of the cusp-expansion coefficients -/

lemma T2op_Gcusp8_kev (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    T2op (fun τ : UpperHalfPlane => Work.Asymptotics.Gcusp8 ℓ i j τ) = 0 := by
  fin_cases i <;> fin_cases j
  · have h1 : T2op (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
        * (-Complex.I)) = 0 :=
      T2op_mul_const (-Complex.I)
        (T2op_mul_of (T2op_phiVec_kev 0) (fun τ => Work.Kernels.KernelFacts.E6Fun_vadd_one τ))
    have h2 : T2op (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ
        / (Real.pi : ℂ)) = 0 :=
      T2op_div_const' (Real.pi : ℂ) (T2op_mul_const (Work.Asymptotics.cuspL ℓ) T2op_E4_kev)
    have h3 : T2op (fun τ : UpperHalfPlane => Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const' (2 * (Real.pi : ℂ)) (Work.Kernels.KernelFacts.psi4_T2 ℓ)
    refine T2op_of_eq' (F := fun τ : UpperHalfPlane =>
      (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ * (-Complex.I)
        + Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
        - Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) / 2) (fun τ => ?_)
      (T2op_div_const' 2 (T2op_sub' (T2op_add h1 h2) h3))
    show Work.Asymptotics.Gcusp8 ℓ 0 0 τ = _
    rw [Work.Asymptotics.Gcusp8, if_neg (by decide : ¬ ((0 : Fin 2) = 1)),
      if_pos (by decide : ((0 : Fin 2) = 0))]
    simp only [Pi.add_apply, Pi.sub_apply]
  · have h1 : T2op (fun τ : UpperHalfPlane => (Real.pi : ℂ) / 3
        * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
          - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)) = 0 :=
      T2op_const_mul' ((Real.pi : ℂ) / 3) (T2op_sub'
        (T2op_mul_of (T2op_phiVec_kev 0) (fun τ => Work.Kernels.KernelFacts.E6Fun_vadd_one τ))
        (T2op_mul_of (T2op_phiVec_kev 1) (fun τ => Work.Kernels.KernelFacts.E4Fun_vadd_one τ)))
    have h2 : T2op (fun τ : UpperHalfPlane => Complex.I * Work.Kernels.E4Fun τ) = 0 :=
      T2op_const_mul' Complex.I T2op_E4_kev
    refine T2op_of_eq' (F := fun τ : UpperHalfPlane =>
      ((Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
          - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
        + Complex.I * Work.Kernels.E4Fun τ) / 2) (fun τ => ?_)
      (T2op_div_const' 2 (T2op_add h1 h2))
    show Work.Asymptotics.Gcusp8 ℓ 0 1 τ = _
    rw [Work.Asymptotics.Gcusp8, if_neg (by decide : ¬ ((0 : Fin 2) = 1)),
      if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    simp only [Pi.add_apply, Pi.sub_apply]
  · exact T2op_of_eq' (F := fun τ : UpperHalfPlane => Work.Asymptotics.Gcusp8 ℓ 1 0 τ)
      (fun τ => by rw [Work.Asymptotics.Gcusp8, if_pos rfl]) T2op_zero
  · exact T2op_of_eq' (F := fun τ : UpperHalfPlane => Work.Asymptotics.Gcusp8 ℓ 1 1 τ)
      (fun τ => by rw [Work.Asymptotics.Gcusp8, if_pos rfl]) T2op_zero

lemma T2op_Gcusp24_kev (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    T2op (fun τ : UpperHalfPlane => Work.Asymptotics.Gcusp24 ℓ i j τ) = 0 := by
  fin_cases i <;> fin_cases j
  · have h1 : T2op (fun τ : UpperHalfPlane => -(13 * Complex.I / 12)
        * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))) = 0 :=
      T2op_const_mul' (-(13 * Complex.I / 12)) (T2op_mul_of (T2op_phiVec_kev 0) per_E4sq_E6_kev)
    have h2 : T2op (fun τ : UpperHalfPlane => (Complex.I / 6)
        * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul' (Complex.I / 6) (T2op_mul_of (T2op_phiVec_kev 1) per_E4cube_kev)
    have h3 : T2op (fun τ : UpperHalfPlane => (168 * Complex.I)
        * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)) = 0 :=
      T2op_const_mul' (168 * Complex.I) (T2op_mul_of (T2op_phiVec_kev 1) per_Delta_kev)
    have h4 : T2op (fun τ : UpperHalfPlane => (Complex.I / 12)
        * (Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) = 0 :=
      T2op_const_mul' (Complex.I / 12) (T2op_mul_of (T2op_phiVec_kev 2) per_E4_E6_kev)
    have h5 : T2op (fun τ : UpperHalfPlane => (720 * Work.Asymptotics.cuspL ℓ)
        * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)) = 0 :=
      T2op_div_const' (Real.pi : ℂ) (T2op_const_mul' (720 * Work.Asymptotics.cuspL ℓ) T2op_Delta_kev)
    have h6 : T2op (fun τ : UpperHalfPlane => (36 : ℂ) * Work.Kernels.DeltaFun τ
        / (Real.pi : ℂ)) = 0 :=
      T2op_div_const' (Real.pi : ℂ) (T2op_const_mul' 36 T2op_Delta_kev)
    have h7 : T2op (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.cuspL ℓ
        / (Real.pi : ℂ)) = 0 :=
      T2op_div_const' (Real.pi : ℂ) (T2op_mul_const (Work.Asymptotics.cuspL ℓ) T2op_E4cube_kev)
    have h8 : T2op (fun τ : UpperHalfPlane => (7 : ℂ)
        * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
        / (24 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const' (24 * (Real.pi : ℂ)) (T2op_const_mul' 7
        (T2op_mul_of (Work.Kernels.KernelFacts.psi2_T2 ℓ) per_E4_E6_kev))
    have h9 : T2op (fun τ : UpperHalfPlane => (5 : ℂ)
        * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2) / (24 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const' (24 * (Real.pi : ℂ)) (T2op_const_mul' 5
        (T2op_mul_of (Work.Kernels.KernelFacts.psi4_T2 ℓ) per_E4sq_kev))
    refine T2op_of_eq' (F := fun τ : UpperHalfPlane =>
      (-(13 * Complex.I / 12) * (Work.Kernels.phiVec τ 0
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
        - 5 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
            / (24 * (Real.pi : ℂ))) / 2) (fun τ => ?_)
      (T2op_div_const' 2 (T2op_sub' (T2op_sub' (T2op_add (T2op_sub' (T2op_sub' (T2op_sub'
        (T2op_sub' (T2op_add h1 h2) h3) h4) h5) h6) h7) h8) h9))
    show Work.Asymptotics.Gcusp24 ℓ 0 0 τ = _
    dsimp only [Work.Asymptotics.Gcusp24]
    rw [if_pos (by decide : ((0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0))]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · have a1 : T2op (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 0
        * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)) = 0 :=
      T2op_mul_of (T2op_phiVec_kev 0) per_E4sq_E6_kev
    have a2 : T2op (fun τ : UpperHalfPlane => 720 * (Work.Kernels.phiVec τ 1
        * Work.Kernels.DeltaFun τ)) = 0 :=
      T2op_const_mul' (720 : ℂ) (T2op_mul_of (T2op_phiVec_kev 1) per_Delta_kev)
    have a3 : T2op (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 1
        * Work.Kernels.E4Fun τ ^ 3) = 0 :=
      T2op_mul_of (T2op_phiVec_kev 1) per_E4cube_kev
    have b1 : T2op (fun τ : UpperHalfPlane => 720 * Work.Kernels.DeltaFun τ) = 0 :=
      T2op_const_mul' (720 : ℂ) T2op_Delta_kev
    have b2 : T2op (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ ^ 3) = 0 := T2op_E4cube_kev
    refine T2op_of_eq' (F := fun τ : UpperHalfPlane =>
      ((Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
          + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
          - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
        - Complex.I * (720 * Work.Kernels.DeltaFun τ - Work.Kernels.E4Fun τ ^ 3)) / 2)
      (fun τ => ?_)
      (T2op_div_const' 2 (T2op_add
        (T2op_const_mul' ((Real.pi : ℂ) / 3) (T2op_sub' (T2op_add a1 a2) a3))
        (T2op_const_mul' (-Complex.I) (T2op_sub' b1 b2))))
    show Work.Asymptotics.Gcusp24 ℓ 0 1 τ = _
    dsimp only [Work.Asymptotics.Gcusp24]
    rw [if_neg (by decide : ¬ ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 0)),
      if_pos (by decide : ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 1))]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · have u1 : T2op (fun τ : UpperHalfPlane => (-(Complex.I / 288))
        * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
          + Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) = 0 :=
      T2op_const_mul' (-(Complex.I / 288)) (T2op_add (T2op_mul_of (T2op_phiVec_kev 0) per_E4sq_E6_kev)
        (T2op_mul_of (T2op_phiVec_kev 2) per_E4_E6_kev))
    have u2 : T2op (fun τ : UpperHalfPlane => (Complex.I / 144)
        * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul' (Complex.I / 144) (T2op_mul_of (T2op_phiVec_kev 1) per_E4cube_kev)
    have u3 : T2op (fun τ : UpperHalfPlane => (7 * Complex.I)
        * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)) = 0 :=
      T2op_const_mul' (7 * Complex.I) (T2op_mul_of (T2op_phiVec_kev 1) per_Delta_kev)
    have u4 : T2op (fun τ : UpperHalfPlane => Work.Kernels.DeltaFun τ
        * (Work.Asymptotics.cuspL ℓ - 1) / (Real.pi : ℂ)) = 0 :=
      T2op_div_const' (Real.pi : ℂ) (T2op_mul_const (Work.Asymptotics.cuspL ℓ - 1) T2op_Delta_kev)
    have u5 : T2op (fun τ : UpperHalfPlane => (Work.Kernels.psi2 ℓ τ
        * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
        - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2) / (1152 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const' (1152 * (Real.pi : ℂ))
        (T2op_sub' (T2op_mul_of (Work.Kernels.KernelFacts.psi2_T2 ℓ) per_E4_E6_kev)
        (T2op_mul_of (Work.Kernels.KernelFacts.psi4_T2 ℓ) per_E4sq_kev))
    refine T2op_of_eq' (F := fun τ : UpperHalfPlane =>
      (-(Complex.I / 288) * (Work.Kernels.phiVec τ 0
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
          + Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
        + (Complex.I / 144) * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
        - 7 * Complex.I * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
        + Work.Kernels.DeltaFun τ * (Work.Asymptotics.cuspL ℓ - 1) / (Real.pi : ℂ)
        + (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
            - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
            / (1152 * (Real.pi : ℂ))) / 2) (fun τ => ?_)
      (T2op_div_const' 2 (T2op_add (T2op_add (T2op_sub' (T2op_add u1 u2) u3) u4) u5))
    show Work.Asymptotics.Gcusp24 ℓ 1 0 τ = _
    dsimp only [Work.Asymptotics.Gcusp24]
    rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 0)),
      if_neg (by decide : ¬ ((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 1)),
      if_pos (by decide : ((1 : Fin 2) = 1 ∧ (0 : Fin 2) = 0))]
    simp only [Pi.add_apply, Pi.sub_apply]
  · have v1 : T2op (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 0
        * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)) = 0 :=
      T2op_mul_of (T2op_phiVec_kev 0) per_E4sq_E6_kev
    have v2 : T2op (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 2
        * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)) = 0 :=
      T2op_mul_of (T2op_phiVec_kev 2) per_E4_E6_kev
    have v3 : T2op (fun τ : UpperHalfPlane => 1728 * (Work.Kernels.phiVec τ 1
        * Work.Kernels.DeltaFun τ)) = 0 :=
      T2op_const_mul' (1728 : ℂ) (T2op_mul_of (T2op_phiVec_kev 1) per_Delta_kev)
    have v4 : T2op (fun τ : UpperHalfPlane => 2 * (Work.Kernels.phiVec τ 1
        * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul' (2 : ℂ) (T2op_mul_of (T2op_phiVec_kev 1) per_E4cube_kev)
    have v5 : T2op (fun τ : UpperHalfPlane => Complex.I * Work.Kernels.DeltaFun τ) = 0 :=
      T2op_const_mul' Complex.I T2op_Delta_kev
    refine T2op_of_eq' (F := fun τ : UpperHalfPlane =>
      ((Real.pi : ℂ) / 864 * (Work.Kernels.phiVec τ 0
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
          + Work.Kernels.phiVec τ 2 * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
          + 1728 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
          - 2 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3))
        + Complex.I * Work.Kernels.DeltaFun τ) / 2) (fun τ => ?_)
      (T2op_div_const' 2 (T2op_add (T2op_const_mul' ((Real.pi : ℂ) / 864)
        (T2op_sub' (T2op_add (T2op_add v1 v2) v3) v4)) v5))
    show Work.Asymptotics.Gcusp24 ℓ 1 1 τ = _
    dsimp only [Work.Asymptotics.Gcusp24]
    rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 0)),
      if_neg (by decide : ¬ ((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 1)),
      if_neg (by decide : ¬ ((1 : Fin 2) = 1 ∧ (1 : Fin 2) = 0))]
    simp only [Pi.add_apply, Pi.sub_apply]

/-- **`(T-I)²` annihilates the cusp-expansion coefficients.**  Each `Gcusp ℓ d i j` is a sum of
products of the `(T-I)²`-annihilated atoms `φ_k`, `ψ_j` with `T`-invariant modular forms
(`E₄`, `E₆`, `Δ` and their products). -/
lemma T2op_Gcusp_kev (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (i j : Fin 2) : T2op (fun τ : UpperHalfPlane => Work.Asymptotics.Gcusp ℓ d i j τ) = 0 := by
  rcases hd with h8 | h24
  · subst h8
    have h : Work.Asymptotics.Gcusp ℓ 8 = Work.Asymptotics.Gcusp8 ℓ := by
      rw [Work.Asymptotics.Gcusp, if_pos rfl]
    rw [h]
    exact T2op_Gcusp8_kev ℓ i j
  · subst h24
    have h : Work.Asymptotics.Gcusp ℓ 24 = Work.Asymptotics.Gcusp24 ℓ := by
      rw [Work.Asymptotics.Gcusp, if_neg (by norm_num)]
    rw [h]
    exact T2op_Gcusp24_kev ℓ i j

/-- **`(T-I)²` annihilates the cusp model `Aexp (Gcusp ℓ d) · t`.** -/
lemma T2op_Aexp_kev {G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ} (h : ∀ i j, T2op (G i j) = 0)
    (t : ℝ) : T2op (fun τ : UpperHalfPlane => Work.Asymptotics.Aexp G τ t) = 0 := by
  have h1 : T2op (G 0 0) = 0 := h 0 0
  have h2 : T2op (fun τ : UpperHalfPlane => ((t : ℂ) * Complex.I) * G 0 1 τ) = 0 :=
    T2op_const_mul' _ (h 0 1)
  have h3 : T2op (fun τ : UpperHalfPlane =>
      ((t : ℂ) * Complex.I) * G 1 1 τ) = 0 := T2op_const_mul' _ (h 1 1)
  have h4 : T2op (fun τ : UpperHalfPlane => G 1 0 τ + ((t : ℂ) * Complex.I) * G 1 1 τ) = 0 :=
    T2op_add (h 1 0) h3
  have h5 : T2op (fun τ : UpperHalfPlane =>
      Complex.exp (2 * Real.pi * t) * (G 1 0 τ + ((t : ℂ) * Complex.I) * G 1 1 τ)) = 0 :=
    T2op_const_mul' _ h4
  refine T2op_of_eq' (F := fun τ : UpperHalfPlane => Work.Asymptotics.Aexp G τ t) (fun τ => ?_)
    (T2op_add (T2op_add h1 h2) h5)
  show Work.Asymptotics.Aexp G τ t = _
  rw [Work.Asymptotics.Aexp]
  simp only [Pi.add_apply]

end KevT2

open KevT2 in
/-- **The cusp expansion of the kernel at `τ = 1 + u`.**  For `u ∈ 𝒟` with `u - 1 ∈ 𝒟` the
cusp-`i∞` expansion of `z ↦ K^{(d)}(τ,z)` at `τ = 1 + u` follows from the expansion at the two
points `u, u - 1 ∈ 𝒟` (both in the compact set `{u, u - 1} ⊆ 𝒟`), via the exact `T`-affine laws
`F(1+u) = 2F(u) - F(u-1)` satisfied by both sides. -/
theorem Kaxis_expansion_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : UpperHalfPlane) (hu : u ∈ Work.Asymptotics.DomainD)
    (hu1 : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD)
    (him : (1 / 2 : ℝ) < u.im) (him2 : u.im < 3) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  -- the two hypotheses `him`, `him2` are not needed for this route
  obtain ⟨C, M, T₀, hC, hM, hT₀, hb⟩ :=
    Work.Asymptotics.cuspExpansionKernel ℓ d hd
      (K := ({u, (((-1 : ℝ) +ᵥ u))} : Set UpperHalfPlane))
      (Set.Finite.isCompact (by simp))
      (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hu
        · exact hu1)
  refine ⟨3 * C, M, T₀, by positivity, hM, hT₀, fun t ht => ?_⟩
  have hAexp : T2op (fun τ : UpperHalfPlane => Aexp (Gcusp ℓ d) τ t) = 0 :=
    T2op_Aexp_kev (fun i j => T2op_Gcusp_kev ℓ d hd i j) t
  have hKax : T2op (fun τ : UpperHalfPlane => Kaxis (Kfun ℓ d) τ t) = 0 :=
    Work.Asymptotics.Kaxis_Kfun_T2 ℓ d hd t
  have hA := T2op_vadd_one_eq hAexp u
  have hK := T2op_vadd_one_eq hKax u
  have hmem1 : u ∈ ({u, (((-1 : ℝ) +ᵥ u))} : Set UpperHalfPlane) := by simp
  have hmem2 : (((-1 : ℝ) +ᵥ u)) ∈ ({u, (((-1 : ℝ) +ᵥ u))} : Set UpperHalfPlane) := by simp
  have b1 := hb u t hmem1 ht
  have b2 := hb (((-1 : ℝ) +ᵥ u)) t hmem2 ht
  have hkey : (2 * Kaxis (Kfun ℓ d) u t - Kaxis (Kfun ℓ d) (((-1 : ℝ) +ᵥ u)) t)
      - (2 * Aexp (Gcusp ℓ d) u t - Aexp (Gcusp ℓ d) (((-1 : ℝ) +ᵥ u)) t)
      = 2 * (Kaxis (Kfun ℓ d) u t - Aexp (Gcusp ℓ d) u t)
        - (Kaxis (Kfun ℓ d) (((-1 : ℝ) +ᵥ u)) t
            - Aexp (Gcusp ℓ d) (((-1 : ℝ) +ᵥ u)) t) := by ring
  rw [hK, hA, hkey]
  calc ‖2 * (Kaxis (Kfun ℓ d) u t - Aexp (Gcusp ℓ d) u t)
        - (Kaxis (Kfun ℓ d) (((-1 : ℝ) +ᵥ u)) t
            - Aexp (Gcusp ℓ d) (((-1 : ℝ) +ᵥ u)) t)‖
      ≤ ‖2 * (Kaxis (Kfun ℓ d) u t - Aexp (Gcusp ℓ d) u t)‖
        + ‖Kaxis (Kfun ℓ d) (((-1 : ℝ) +ᵥ u)) t
            - Aexp (Gcusp ℓ d) (((-1 : ℝ) +ᵥ u)) t‖ := norm_sub_le _ _
    _ ≤ 2 * (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
        + C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
        refine add_le_add ?_ b2
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
        exact mul_le_mul_of_nonneg_left b1 (by norm_num)
    _ = 3 * C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by ring

end Work.Asymptotics
