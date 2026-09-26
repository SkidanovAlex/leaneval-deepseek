import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24BCoeffs
import Submission.Work.Asymptotics.KhatE1Core.Bracket24B7Bound_proof
import Submission.Work.Asymptotics.KhatE1.Bracket24E2_defs
import Submission.Work.Asymptotics.KhatE1.Bracket24ClearedDefs
import Submission.Work.Asymptotics.KhatE1Core.psi_individual_first_order
import Submission.Work.Asymptotics.funnel_tauAtom_second_order

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Asymptotics.KhatE1 (Bound)

/-!
# The `E(z)^4`-coefficient bound `Bracket24B4Bound`

`Bracket24B4` (module `Submission.Work.Asymptotics.KhatE1Core.Bracket24BCoeffs`) is the
`E(z)^4`-coefficient of the `Sh`-cleared `d = 24` bracket, an explicit `τ`/`z`-polynomial whose
`j(τ)^2`-monomials are all `Δ(τ)j(τ)^2 = E₄(τ)³j(τ)`, i.e. of size `‖q(τ)‖⁻¹` — one power of
`‖q‖` too large for the target bound `O(scale^N(1+t)^M)`.  The point of the coefficient is that
these dangerous terms *cancel* against the `j(τ)¹`-terms once the leading cusp behaviour of the
`τ`-atoms is used.

The proof below exhibits that cancellation as an identity.  Writing

* `Aside` for the `j(τ)`-coefficient of `Bracket24B4` after the exact rewrites
  `Δj² = E₄³j`, `Δj = E₄³`, and `Bside` for the `j`-free remainder
  (`B4_decomp`), and
* `u₁ = E₄-1`, `u₂ = E₆-1`, `u₃ = E₂-1`, `u₄ = ψ₂ - 2(πiτ+c)`, `u₅ = ψ₄ - 2(πiτ+c)`
  for the deviations from the leading cusp values (`‖u_i‖ = O(‖q‖ scale^N)`),

the algebraic core is `B4Aside_decomp`: `Aside = u₁P₁ + u₂P₂ + u₃P₃ + u₄α₂ + u₅α₄ + Corr`,
where `Corr` is the (non-manifestly-zero) remainder `B4Corr`, which vanishes identically
(`B4_corr_zero`, a `field_simp`-consequence of `S0z z = 1 - 6i/(πz)`).  Hence
`Aside = O(‖q‖ scale^N(1+t)^M)` and `Aside·j = O(scale^N(1+t)^M)`.
-/

/-! ## The `τ`-deviations -/

/-- `Λ(τ) = πiτ + cuspC ℓ`, the leading cusp value of `ψ₂/2` and `ψ₄/2`. -/
def B4Lam (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ

/-- `E₄(τ) - 1`. -/
def B4u1 (τ : UpperHalfPlane) : ℂ := Work.Kernels.E4Fun τ - 1
/-- `E₆(τ) - 1`. -/
def B4u2 (τ : UpperHalfPlane) : ℂ := Work.Kernels.E6Fun τ - 1
/-- `E₂(τ) - 1`. -/
def B4u3 (τ : UpperHalfPlane) : ℂ := Work.Kernels.E2Fun τ - 1
/-- `ψ₂ - 2Λ`. -/
def B4u4 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.psi2 ℓ τ - 2 * B4Lam ℓ τ
/-- `ψ₄ - 2Λ`. -/
def B4u5 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.psi4 ℓ τ - 2 * B4Lam ℓ τ

/-! ## Atom bounds for the `Bound` calculus -/

theorem B4b_const (c : ℂ) : Bound (fun (_ _ : UpperHalfPlane) => c) 0 := Bound.const c
theorem B4b_mul {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℕ} (hf : Bound f m)
    (hg : Bound g n) : Bound (fun τ z => f τ z * g τ z) (m + n) := Bound.mul hf hg
theorem B4b_add {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℕ} (hf : Bound f m)
    (hg : Bound g n) : Bound (fun τ z => f τ z + g τ z) (min m n) := Bound.add hf hg
theorem B4b_tau : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => (τ : ℂ)) 0 :=
  Bound.coe_tau
theorem B4b_z : Bound (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => (z : ℂ)) 0 :=
  Bound.coe_z
theorem B4b_S0 : Bound (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Asymptotics.KhatE1.S0z z) 0 := Bound.S0z
theorem B4b_cuspC (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun (_ _ : UpperHalfPlane) => Work.Asymptotics.Compact.cuspC ℓ) 0 := Bound.cuspC ℓ
theorem B4b_E4 : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Kernels.E4Fun τ) 0 := Bound.E4Fun
theorem B4b_E6 : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Kernels.E6Fun τ) 0 := Bound.E6Fun
theorem B4b_E2 : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Kernels.E2Fun τ) 0 := Bound.E2Fun
theorem B4b_DeltaFun : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Kernels.DeltaFun τ) 1 := Bound.DeltaFun
theorem B4b_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => Work.Kernels.psi2 ℓ τ) 0 := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa [Real.rpow_zero, pow_one, mul_one] using (hb τ hF).1
theorem B4b_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => Work.Kernels.psi4 ℓ τ) 0 := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa [Real.rpow_zero, pow_one, mul_one] using (hb τ hF).2

theorem B4b_u1 : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => B4u1 τ) 1 := by
  have hq : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
      (240 : ℂ) * Work.Kernels.qParamFun τ) 1 := Bound.const_mul 240 Bound.qParamFun
  have hdev : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
      Work.Kernels.E4Fun τ - (1 + 240 * Work.Kernels.qParamFun τ)) 2 :=
    Bound.congr Bound.devE4 (fun τ _ => by ring)
  exact Bound.congr (Bound.mono (by norm_num) (hq.add hdev)) (fun τ _ => by
    simp only [B4u1]; ring)
theorem B4b_u2 : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => B4u2 τ) 1 := by
  have hq : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
      (-504 : ℂ) * Work.Kernels.qParamFun τ) 1 := Bound.const_mul (-504) Bound.qParamFun
  have hdev : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
      Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ)) 2 :=
    Bound.congr Bound.devE6 (fun τ _ => by ring)
  exact Bound.congr (Bound.mono (by norm_num) (hq.add hdev)) (fun τ _ => by
    simp only [B4u2]; ring)
theorem B4b_u3 : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => B4u3 τ) 1 := by
  have hq : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
      (-24 : ℂ) * Work.Kernels.qParamFun τ) 1 := Bound.const_mul (-24) Bound.qParamFun
  have hdev : Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
      Work.Kernels.E2Fun τ - (1 - 24 * Work.Kernels.qParamFun τ)) 2 :=
    Bound.congr Bound.devE2 (fun τ _ => by ring)
  exact Bound.congr (Bound.mono (by norm_num) (hq.add hdev)) (fun τ _ => by
    simp only [B4u3]; ring)
theorem B4b_u4 (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => B4u4 ℓ τ) 1 := by
  obtain ⟨C, N, hC, hN, hb⟩ := psi_individual_first_order ℓ
  refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := (hb τ hF).1
  simpa [B4u4, B4Lam, Real.rpow_zero, pow_one, mul_one] using h
theorem B4b_u5 (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) => B4u5 ℓ τ) 1 := by
  obtain ⟨C, N, hC, hN, hb⟩ := psi_individual_first_order ℓ
  refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := (hb τ hF).2
  simpa [B4u5, B4Lam, Real.rpow_zero, pow_one, mul_one] using h
noncomputable def B4P1m0 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((29 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P1m1 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((27 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u1 τ

noncomputable def B4P1m2 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u2 τ

noncomputable def B4P1m3 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((13 : ℂ) / (4 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u3 τ

noncomputable def B4P1m4 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((13 : ℂ) / (12 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u1 τ

noncomputable def B4P1m5 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((13 : ℂ) / (12 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u1 τ * B4u3 τ

noncomputable def B4P1m6 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((3 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u2 τ

noncomputable def B4P1m7 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (4 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u2 τ * B4u3 τ

noncomputable def B4P1m8 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u2 τ * B4u3 τ * B4u3 τ

noncomputable def B4P1m9 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((7 : ℂ) / (2 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P1m10 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u3 τ * B4u3 τ

noncomputable def B4P1m11 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-119 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P1m12 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-49 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u1 τ

noncomputable def B4P1m13 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-67 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u2 τ

noncomputable def B4P1m14 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((3 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u3 τ

noncomputable def B4P1m15 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u1 τ

noncomputable def B4P1m16 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u1 τ * B4u3 τ

noncomputable def B4P1m17 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-137 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u2 τ

noncomputable def B4P1m18 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u2 τ * B4u3 τ

noncomputable def B4P1m19 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u2 τ * B4u3 τ * B4u3 τ

noncomputable def B4P1m20 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P1m21 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u3 τ * B4u3 τ

noncomputable def B4P1m22 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-277 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4P1m23 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-355 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u1 τ

noncomputable def B4P1m24 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((71 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u1 τ * B4u2 τ

noncomputable def B4P1m25 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-71 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u1 τ * B4u3 τ

noncomputable def B4P1m26 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-71 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u1 τ * B4u1 τ

noncomputable def B4P1m27 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-71 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u1 τ * B4u1 τ * B4u3 τ

noncomputable def B4P1m28 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((149 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u2 τ

noncomputable def B4P1m29 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((7 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u2 τ * B4u3 τ

noncomputable def B4P1m30 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u2 τ * B4u3 τ * B4u3 τ

noncomputable def B4P1m31 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-103 : ℂ) / (24 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u3 τ

noncomputable def B4P1m32 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u3 τ * B4u3 τ

noncomputable def B4P1m33 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((21 : ℂ) / (2 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P1m34 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((39 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u1 τ

noncomputable def B4P1m35 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((13 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u1 τ

noncomputable def B4P1m36 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u2 τ

noncomputable def B4P1m37 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u2 τ * B4u3 τ

noncomputable def B4P1m38 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P1m39 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3 : ℂ) / (8 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P1m40 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((9 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u1 τ

noncomputable def B4P1m41 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u1 τ * B4u1 τ

noncomputable def B4P1m42 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u2 τ

noncomputable def B4P1m43 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u2 τ * B4u3 τ

noncomputable def B4P1m44 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P1m45 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-213 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * B4u1 τ

noncomputable def B4P1m46 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-71 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * B4u1 τ * B4u1 τ

noncomputable def B4P1m47 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * B4u2 τ

noncomputable def B4P1m48 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * B4u2 τ * B4u3 τ

noncomputable def B4P1m49 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * B4u3 τ

noncomputable def B4P1m50 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-103 : ℂ) / (8 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4P1m51 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-461 : ℂ) / (48 : ℂ)) * Complex.I) * (τ : ℂ) * B4u1 τ

noncomputable def B4P1m52 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-691 : ℂ) / (48 : ℂ)) * Complex.I) * (τ : ℂ) * B4u2 τ

noncomputable def B4P1m53 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-1613 : ℂ) / (48 : ℂ)) * Complex.I) * (τ : ℂ)

noncomputable def B4P1m54 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((72 : ℂ) * Complex.I) * (z : ℂ) * B4u1 τ

noncomputable def B4P1m55 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((24 : ℂ) * Complex.I) * (z : ℂ) * B4u1 τ * B4u1 τ

noncomputable def B4P1m56 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((72 : ℂ) * Complex.I) * (z : ℂ)

noncomputable def B4P1m57 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((2995 : ℂ) / (48 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Asymptotics.Compact.cuspC ℓ * B4u1 τ

noncomputable def B4P1m58 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (24 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Asymptotics.Compact.cuspC ℓ * B4u1 τ * B4u1 τ

noncomputable def B4P1m59 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-691 : ℂ) / (48 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Asymptotics.Compact.cuspC ℓ * B4u2 τ

noncomputable def B4P1m60 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((1843 : ℂ) / (48 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Asymptotics.Compact.cuspC ℓ

noncomputable def B4P1 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      B4P1m0 ℓ τ z
      + B4P1m1 ℓ τ z
      + B4P1m2 ℓ τ z
      + B4P1m3 ℓ τ z
      + B4P1m4 ℓ τ z
      + B4P1m5 ℓ τ z
      + B4P1m6 ℓ τ z
      + B4P1m7 ℓ τ z
      + B4P1m8 ℓ τ z
      + B4P1m9 ℓ τ z
      + B4P1m10 ℓ τ z
      + B4P1m11 ℓ τ z
      + B4P1m12 ℓ τ z
      + B4P1m13 ℓ τ z
      + B4P1m14 ℓ τ z
      + B4P1m15 ℓ τ z
      + B4P1m16 ℓ τ z
      + B4P1m17 ℓ τ z
      + B4P1m18 ℓ τ z
      + B4P1m19 ℓ τ z
      + B4P1m20 ℓ τ z
      + B4P1m21 ℓ τ z
      + B4P1m22 ℓ τ z
      + B4P1m23 ℓ τ z
      + B4P1m24 ℓ τ z
      + B4P1m25 ℓ τ z
      + B4P1m26 ℓ τ z
      + B4P1m27 ℓ τ z
      + B4P1m28 ℓ τ z
      + B4P1m29 ℓ τ z
      + B4P1m30 ℓ τ z
      + B4P1m31 ℓ τ z
      + B4P1m32 ℓ τ z
      + B4P1m33 ℓ τ z
      + B4P1m34 ℓ τ z
      + B4P1m35 ℓ τ z
      + B4P1m36 ℓ τ z
      + B4P1m37 ℓ τ z
      + B4P1m38 ℓ τ z
      + B4P1m39 ℓ τ z
      + B4P1m40 ℓ τ z
      + B4P1m41 ℓ τ z
      + B4P1m42 ℓ τ z
      + B4P1m43 ℓ τ z
      + B4P1m44 ℓ τ z
      + B4P1m45 ℓ τ z
      + B4P1m46 ℓ τ z
      + B4P1m47 ℓ τ z
      + B4P1m48 ℓ τ z
      + B4P1m49 ℓ τ z
      + B4P1m50 ℓ τ z
      + B4P1m51 ℓ τ z
      + B4P1m52 ℓ τ z
      + B4P1m53 ℓ τ z
      + B4P1m54 ℓ τ z
      + B4P1m55 ℓ τ z
      + B4P1m56 ℓ τ z
      + B4P1m57 ℓ τ z
      + B4P1m58 ℓ τ z
      + B4P1m59 ℓ τ z
      + B4P1m60 ℓ τ z

theorem B4P1b0 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m0 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((29 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4P1m0])

theorem B4P1b1 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m1 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((27 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u1)) (fun τ z => by
    simp only [B4P1m1])

theorem B4P1b2 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m2 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u1) B4b_u2)) (fun τ z => by
    simp only [B4P1m2])

theorem B4P1b3 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m3 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((13 : ℂ) / (4 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u1) B4b_u3)) (fun τ z => by
    simp only [B4P1m3])

theorem B4P1b4 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m4 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((13 : ℂ) / (12 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u1) B4b_u1)) (fun τ z => by
    simp only [B4P1m4])

theorem B4P1b5 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m5 ℓ τ z) 3 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((13 : ℂ) / (12 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u1) B4b_u1) B4b_u3)) (fun τ z => by
    simp only [B4P1m5])

theorem B4P1b6 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m6 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((3 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u2)) (fun τ z => by
    simp only [B4P1m6])

theorem B4P1b7 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m7 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (4 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u2) B4b_u3)) (fun τ z => by
    simp only [B4P1m7])

theorem B4P1b8 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m8 ℓ τ z) 3 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u2) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P1m8])

theorem B4P1b9 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m9 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((7 : ℂ) / (2 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P1m9])

theorem B4P1b10 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m10 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P1m10])

theorem B4P1b11 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m11 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-119 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4P1m11])

theorem B4P1b12 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m12 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-49 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u1)) (fun τ z => by
    simp only [B4P1m12])

theorem B4P1b13 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m13 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-67 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u1) B4b_u2)) (fun τ z => by
    simp only [B4P1m13])

theorem B4P1b14 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m14 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((3 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u1) B4b_u3)) (fun τ z => by
    simp only [B4P1m14])

theorem B4P1b15 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m15 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u1) B4b_u1)) (fun τ z => by
    simp only [B4P1m15])

theorem B4P1b16 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m16 ℓ τ z) 3 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u1) B4b_u1) B4b_u3)) (fun τ z => by
    simp only [B4P1m16])

theorem B4P1b17 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m17 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-137 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u2)) (fun τ z => by
    simp only [B4P1m17])

theorem B4P1b18 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m18 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u2) B4b_u3)) (fun τ z => by
    simp only [B4P1m18])

theorem B4P1b19 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m19 ℓ τ z) 3 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u2) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P1m19])

theorem B4P1b20 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m20 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P1m20])

theorem B4P1b21 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m21 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P1m21])

theorem B4P1b22 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m22 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-277 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4P1m22])

theorem B4P1b23 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m23 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-355 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u1)) (fun τ z => by
    simp only [B4P1m23])

theorem B4P1b24 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m24 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((71 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u1) B4b_u2)) (fun τ z => by
    simp only [B4P1m24])

theorem B4P1b25 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m25 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-71 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u1) B4b_u3)) (fun τ z => by
    simp only [B4P1m25])

theorem B4P1b26 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m26 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-71 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u1) B4b_u1)) (fun τ z => by
    simp only [B4P1m26])

theorem B4P1b27 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m27 ℓ τ z) 3 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-71 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u1) B4b_u1) B4b_u3)) (fun τ z => by
    simp only [B4P1m27])

theorem B4P1b28 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m28 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((149 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u2)) (fun τ z => by
    simp only [B4P1m28])

theorem B4P1b29 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m29 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((7 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u2) B4b_u3)) (fun τ z => by
    simp only [B4P1m29])

theorem B4P1b30 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m30 ℓ τ z) 3 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u2) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P1m30])

theorem B4P1b31 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m31 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-103 : ℂ) / (24 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u3)) (fun τ z => by
    simp only [B4P1m31])

theorem B4P1b32 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m32 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P1m32])

theorem B4P1b33 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m33 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((21 : ℂ) / (2 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4P1m33])

theorem B4P1b34 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m34 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((39 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_u1)) (fun τ z => by
    simp only [B4P1m34])

theorem B4P1b35 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m35 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((13 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_u1) B4b_u1)) (fun τ z => by
    simp only [B4P1m35])

theorem B4P1b36 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m36 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_u2)) (fun τ z => by
    simp only [B4P1m36])

theorem B4P1b37 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m37 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_u2) B4b_u3)) (fun τ z => by
    simp only [B4P1m37])

theorem B4P1b38 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m38 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P1m38])

theorem B4P1b39 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m39 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((3 : ℂ) / (8 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4P1m39])

theorem B4P1b40 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m40 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((9 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u1)) (fun τ z => by
    simp only [B4P1m40])

theorem B4P1b41 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m41 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u1) B4b_u1)) (fun τ z => by
    simp only [B4P1m41])

theorem B4P1b42 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m42 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u2)) (fun τ z => by
    simp only [B4P1m42])

theorem B4P1b43 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m43 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u2) B4b_u3)) (fun τ z => by
    simp only [B4P1m43])

theorem B4P1b44 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m44 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P1m44])

theorem B4P1b45 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m45 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((-213 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_u1)) (fun τ z => by
    simp only [B4P1m45])

theorem B4P1b46 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m46 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-71 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_u1) B4b_u1)) (fun τ z => by
    simp only [B4P1m46])

theorem B4P1b47 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m47 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_u2)) (fun τ z => by
    simp only [B4P1m47])

theorem B4P1b48 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m48 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_u2) B4b_u3)) (fun τ z => by
    simp only [B4P1m48])

theorem B4P1b49 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m49 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_u3)) (fun τ z => by
    simp only [B4P1m49])

theorem B4P1b50 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m50 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((-103 : ℂ) / (8 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4P1m50])

theorem B4P1b51 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m51 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const ((((-461 : ℂ) / (48 : ℂ)) * Complex.I))) B4b_tau) B4b_u1)) (fun τ z => by
    simp only [B4P1m51])

theorem B4P1b52 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m52 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const ((((-691 : ℂ) / (48 : ℂ)) * Complex.I))) B4b_tau) B4b_u2)) (fun τ z => by
    simp only [B4P1m52])

theorem B4P1b53 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m53 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_const ((((-1613 : ℂ) / (48 : ℂ)) * Complex.I))) B4b_tau)) (fun τ z => by
    simp only [B4P1m53])

theorem B4P1b54 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m54 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((72 : ℂ) * Complex.I))) B4b_z) B4b_u1)) (fun τ z => by
    simp only [B4P1m54])

theorem B4P1b55 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m55 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((24 : ℂ) * Complex.I))) B4b_z) B4b_u1) B4b_u1)) (fun τ z => by
    simp only [B4P1m55])

theorem B4P1b56 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m56 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_const (((72 : ℂ) * Complex.I))) B4b_z)) (fun τ z => by
    simp only [B4P1m56])

theorem B4P1b57 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m57 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((2995 : ℂ) / (48 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) (B4b_cuspC ℓ)) B4b_u1)) (fun τ z => by
    simp only [B4P1m57])

theorem B4P1b58 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m58 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const ((24 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) (B4b_cuspC ℓ)) B4b_u1) B4b_u1)) (fun τ z => by
    simp only [B4P1m58])

theorem B4P1b59 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m59 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((-691 : ℂ) / (48 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) (B4b_cuspC ℓ)) B4b_u2)) (fun τ z => by
    simp only [B4P1m59])

theorem B4P1b60 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m60 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_const (((1843 : ℂ) / (48 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) (B4b_cuspC ℓ))) (fun τ z => by
    simp only [B4P1m60])

theorem B4P1_boundX (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1 ℓ τ z) 0 := by
  have h0 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m0 ℓ τ z) _ := B4P1b0 ℓ
  have h1 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m1 ℓ τ z) _ := B4P1b1 ℓ
  have h2 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m2 ℓ τ z) _ := B4P1b2 ℓ
  have h3 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m3 ℓ τ z) _ := B4P1b3 ℓ
  have h4 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m4 ℓ τ z) _ := B4P1b4 ℓ
  have h5 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m5 ℓ τ z) _ := B4P1b5 ℓ
  have h6 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m6 ℓ τ z) _ := B4P1b6 ℓ
  have h7 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m7 ℓ τ z) _ := B4P1b7 ℓ
  have h8 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m8 ℓ τ z) _ := B4P1b8 ℓ
  have h9 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m9 ℓ τ z) _ := B4P1b9 ℓ
  have h10 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m10 ℓ τ z) _ := B4P1b10 ℓ
  have h11 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m11 ℓ τ z) _ := B4P1b11 ℓ
  have h12 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m12 ℓ τ z) _ := B4P1b12 ℓ
  have h13 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m13 ℓ τ z) _ := B4P1b13 ℓ
  have h14 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m14 ℓ τ z) _ := B4P1b14 ℓ
  have h15 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m15 ℓ τ z) _ := B4P1b15 ℓ
  have h16 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m16 ℓ τ z) _ := B4P1b16 ℓ
  have h17 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m17 ℓ τ z) _ := B4P1b17 ℓ
  have h18 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m18 ℓ τ z) _ := B4P1b18 ℓ
  have h19 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m19 ℓ τ z) _ := B4P1b19 ℓ
  have h20 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m20 ℓ τ z) _ := B4P1b20 ℓ
  have h21 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m21 ℓ τ z) _ := B4P1b21 ℓ
  have h22 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m22 ℓ τ z) _ := B4P1b22 ℓ
  have h23 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m23 ℓ τ z) _ := B4P1b23 ℓ
  have h24 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m24 ℓ τ z) _ := B4P1b24 ℓ
  have h25 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m25 ℓ τ z) _ := B4P1b25 ℓ
  have h26 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m26 ℓ τ z) _ := B4P1b26 ℓ
  have h27 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m27 ℓ τ z) _ := B4P1b27 ℓ
  have h28 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m28 ℓ τ z) _ := B4P1b28 ℓ
  have h29 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m29 ℓ τ z) _ := B4P1b29 ℓ
  have h30 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m30 ℓ τ z) _ := B4P1b30 ℓ
  have h31 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m31 ℓ τ z) _ := B4P1b31 ℓ
  have h32 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m32 ℓ τ z) _ := B4P1b32 ℓ
  have h33 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m33 ℓ τ z) _ := B4P1b33 ℓ
  have h34 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m34 ℓ τ z) _ := B4P1b34 ℓ
  have h35 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m35 ℓ τ z) _ := B4P1b35 ℓ
  have h36 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m36 ℓ τ z) _ := B4P1b36 ℓ
  have h37 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m37 ℓ τ z) _ := B4P1b37 ℓ
  have h38 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m38 ℓ τ z) _ := B4P1b38 ℓ
  have h39 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m39 ℓ τ z) _ := B4P1b39 ℓ
  have h40 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m40 ℓ τ z) _ := B4P1b40 ℓ
  have h41 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m41 ℓ τ z) _ := B4P1b41 ℓ
  have h42 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m42 ℓ τ z) _ := B4P1b42 ℓ
  have h43 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m43 ℓ τ z) _ := B4P1b43 ℓ
  have h44 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m44 ℓ τ z) _ := B4P1b44 ℓ
  have h45 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m45 ℓ τ z) _ := B4P1b45 ℓ
  have h46 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m46 ℓ τ z) _ := B4P1b46 ℓ
  have h47 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m47 ℓ τ z) _ := B4P1b47 ℓ
  have h48 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m48 ℓ τ z) _ := B4P1b48 ℓ
  have h49 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m49 ℓ τ z) _ := B4P1b49 ℓ
  have h50 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m50 ℓ τ z) _ := B4P1b50 ℓ
  have h51 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m51 ℓ τ z) _ := B4P1b51 ℓ
  have h52 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m52 ℓ τ z) _ := B4P1b52 ℓ
  have h53 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m53 ℓ τ z) _ := B4P1b53 ℓ
  have h54 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m54 ℓ τ z) _ := B4P1b54 ℓ
  have h55 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m55 ℓ τ z) _ := B4P1b55 ℓ
  have h56 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m56 ℓ τ z) _ := B4P1b56 ℓ
  have h57 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m57 ℓ τ z) _ := B4P1b57 ℓ
  have h58 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m58 ℓ τ z) _ := B4P1b58 ℓ
  have h59 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m59 ℓ τ z) _ := B4P1b59 ℓ
  have h60 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P1m60 ℓ τ z) _ := B4P1b60 ℓ
  have hsum : Work.Asymptotics.KhatE1.Bound (fun τ z => (B4P1m0 ℓ τ z) + (B4P1m1 ℓ τ z) + (B4P1m2 ℓ τ z) + (B4P1m3 ℓ τ z) + (B4P1m4 ℓ τ z) + (B4P1m5 ℓ τ z) + (B4P1m6 ℓ τ z) + (B4P1m7 ℓ τ z) + (B4P1m8 ℓ τ z) + (B4P1m9 ℓ τ z) + (B4P1m10 ℓ τ z) + (B4P1m11 ℓ τ z) + (B4P1m12 ℓ τ z) + (B4P1m13 ℓ τ z) + (B4P1m14 ℓ τ z) + (B4P1m15 ℓ τ z) + (B4P1m16 ℓ τ z) + (B4P1m17 ℓ τ z) + (B4P1m18 ℓ τ z) + (B4P1m19 ℓ τ z) + (B4P1m20 ℓ τ z) + (B4P1m21 ℓ τ z) + (B4P1m22 ℓ τ z) + (B4P1m23 ℓ τ z) + (B4P1m24 ℓ τ z) + (B4P1m25 ℓ τ z) + (B4P1m26 ℓ τ z) + (B4P1m27 ℓ τ z) + (B4P1m28 ℓ τ z) + (B4P1m29 ℓ τ z) + (B4P1m30 ℓ τ z) + (B4P1m31 ℓ τ z) + (B4P1m32 ℓ τ z) + (B4P1m33 ℓ τ z) + (B4P1m34 ℓ τ z) + (B4P1m35 ℓ τ z) + (B4P1m36 ℓ τ z) + (B4P1m37 ℓ τ z) + (B4P1m38 ℓ τ z) + (B4P1m39 ℓ τ z) + (B4P1m40 ℓ τ z) + (B4P1m41 ℓ τ z) + (B4P1m42 ℓ τ z) + (B4P1m43 ℓ τ z) + (B4P1m44 ℓ τ z) + (B4P1m45 ℓ τ z) + (B4P1m46 ℓ τ z) + (B4P1m47 ℓ τ z) + (B4P1m48 ℓ τ z) + (B4P1m49 ℓ τ z) + (B4P1m50 ℓ τ z) + (B4P1m51 ℓ τ z) + (B4P1m52 ℓ τ z) + (B4P1m53 ℓ τ z) + (B4P1m54 ℓ τ z) + (B4P1m55 ℓ τ z) + (B4P1m56 ℓ τ z) + (B4P1m57 ℓ τ z) + (B4P1m58 ℓ τ z) + (B4P1m59 ℓ τ z) + (B4P1m60 ℓ τ z)) _ :=
    (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30) h31) h32) h33) h34) h35) h36) h37) h38) h39) h40) h41) h42) h43) h44) h45) h46) h47) h48) h49) h50) h51) h52) h53) h54) h55) h56) h57) h58) h59) h60)
  exact Work.Asymptotics.KhatE1.Bound.congr (Work.Asymptotics.KhatE1.Bound.mono (Nat.zero_le _) hsum) (fun τ z => by
    simp only [B4P1])

noncomputable def B4P2m0 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (4 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P2m1 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (4 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P2m2 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u3 τ * B4u3 τ

noncomputable def B4P2m3 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-35 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P2m4 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P2m5 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u3 τ * B4u3 τ

noncomputable def B4P2m6 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((13 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4P2m7 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((7 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u3 τ

noncomputable def B4P2m8 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u3 τ * B4u3 τ

noncomputable def B4P2m9 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P2m10 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P2m11 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P2m12 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P2m13 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * B4u3 τ

noncomputable def B4P2m14 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4P2m15 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-691 : ℂ) / (48 : ℂ)) * Complex.I) * (τ : ℂ)

noncomputable def B4P2m16 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-691 : ℂ) / (48 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Asymptotics.Compact.cuspC ℓ

noncomputable def B4P2 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      B4P2m0 ℓ τ z
      + B4P2m1 ℓ τ z
      + B4P2m2 ℓ τ z
      + B4P2m3 ℓ τ z
      + B4P2m4 ℓ τ z
      + B4P2m5 ℓ τ z
      + B4P2m6 ℓ τ z
      + B4P2m7 ℓ τ z
      + B4P2m8 ℓ τ z
      + B4P2m9 ℓ τ z
      + B4P2m10 ℓ τ z
      + B4P2m11 ℓ τ z
      + B4P2m12 ℓ τ z
      + B4P2m13 ℓ τ z
      + B4P2m14 ℓ τ z
      + B4P2m15 ℓ τ z
      + B4P2m16 ℓ τ z

theorem B4P2b0 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m0 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (4 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4P2m0])

theorem B4P2b1 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m1 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (4 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P2m1])

theorem B4P2b2 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m2 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P2m2])

theorem B4P2b3 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m3 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-35 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4P2m3])

theorem B4P2b4 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m4 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P2m4])

theorem B4P2b5 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m5 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P2m5])

theorem B4P2b6 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m6 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const ((((13 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4P2m6])

theorem B4P2b7 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m7 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((7 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u3)) (fun τ z => by
    simp only [B4P2m7])

theorem B4P2b8 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m8 ℓ τ z) 2 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u3) B4b_u3)) (fun τ z => by
    simp only [B4P2m8])

theorem B4P2b9 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m9 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4P2m9])

theorem B4P2b10 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m10 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P2m10])

theorem B4P2b11 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m11 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4P2m11])

theorem B4P2b12 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m12 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P2m12])

theorem B4P2b13 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m13 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_u3)) (fun τ z => by
    simp only [B4P2m13])

theorem B4P2b14 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m14 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4P2m14])

theorem B4P2b15 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m15 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_const ((((-691 : ℂ) / (48 : ℂ)) * Complex.I))) B4b_tau)) (fun τ z => by
    simp only [B4P2m15])

theorem B4P2b16 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m16 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_const (((-691 : ℂ) / (48 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) (B4b_cuspC ℓ))) (fun τ z => by
    simp only [B4P2m16])

theorem B4P2_boundX (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2 ℓ τ z) 0 := by
  have h0 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m0 ℓ τ z) _ := B4P2b0 ℓ
  have h1 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m1 ℓ τ z) _ := B4P2b1 ℓ
  have h2 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m2 ℓ τ z) _ := B4P2b2 ℓ
  have h3 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m3 ℓ τ z) _ := B4P2b3 ℓ
  have h4 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m4 ℓ τ z) _ := B4P2b4 ℓ
  have h5 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m5 ℓ τ z) _ := B4P2b5 ℓ
  have h6 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m6 ℓ τ z) _ := B4P2b6 ℓ
  have h7 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m7 ℓ τ z) _ := B4P2b7 ℓ
  have h8 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m8 ℓ τ z) _ := B4P2b8 ℓ
  have h9 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m9 ℓ τ z) _ := B4P2b9 ℓ
  have h10 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m10 ℓ τ z) _ := B4P2b10 ℓ
  have h11 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m11 ℓ τ z) _ := B4P2b11 ℓ
  have h12 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m12 ℓ τ z) _ := B4P2b12 ℓ
  have h13 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m13 ℓ τ z) _ := B4P2b13 ℓ
  have h14 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m14 ℓ τ z) _ := B4P2b14 ℓ
  have h15 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m15 ℓ τ z) _ := B4P2b15 ℓ
  have h16 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P2m16 ℓ τ z) _ := B4P2b16 ℓ
  have hsum : Work.Asymptotics.KhatE1.Bound (fun τ z => (B4P2m0 ℓ τ z) + (B4P2m1 ℓ τ z) + (B4P2m2 ℓ τ z) + (B4P2m3 ℓ τ z) + (B4P2m4 ℓ τ z) + (B4P2m5 ℓ τ z) + (B4P2m6 ℓ τ z) + (B4P2m7 ℓ τ z) + (B4P2m8 ℓ τ z) + (B4P2m9 ℓ τ z) + (B4P2m10 ℓ τ z) + (B4P2m11 ℓ τ z) + (B4P2m12 ℓ τ z) + (B4P2m13 ℓ τ z) + (B4P2m14 ℓ τ z) + (B4P2m15 ℓ τ z) + (B4P2m16 ℓ τ z)) _ :=
    (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16)
  exact Work.Asymptotics.KhatE1.Bound.congr (Work.Asymptotics.KhatE1.Bound.mono (Nat.zero_le _) hsum) (fun τ z => by
    simp only [B4P2])

noncomputable def B4P3m0 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((4 : ℂ) / (3 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P3m1 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P3m2 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z * B4u3 τ

noncomputable def B4P3m3 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-4 : ℂ) / (3 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4P3m4 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * B4u3 τ

noncomputable def B4P3m5 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P3m6 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4P3m7 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4P3 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      B4P3m0 ℓ τ z
      + B4P3m1 ℓ τ z
      + B4P3m2 ℓ τ z
      + B4P3m3 ℓ τ z
      + B4P3m4 ℓ τ z
      + B4P3m5 ℓ τ z
      + B4P3m6 ℓ τ z
      + B4P3m7 ℓ τ z

theorem B4P3b0 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m0 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((4 : ℂ) / (3 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4P3m0])

theorem B4P3b1 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m1 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P3m1])

theorem B4P3b2 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m2 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0) B4b_u3)) (fun τ z => by
    simp only [B4P3m2])

theorem B4P3b3 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m3 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-4 : ℂ) / (3 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4P3m3])

theorem B4P3b4 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m4 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_tau) B4b_z) B4b_z) B4b_u3)) (fun τ z => by
    simp only [B4P3m4])

theorem B4P3b5 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m5 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4P3m5])

theorem B4P3b6 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m6 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4P3m6])

theorem B4P3b7 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m7 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ))) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4P3m7])

theorem B4P3_boundX (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3 ℓ τ z) 0 := by
  have h0 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m0 ℓ τ z) _ := B4P3b0 ℓ
  have h1 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m1 ℓ τ z) _ := B4P3b1 ℓ
  have h2 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m2 ℓ τ z) _ := B4P3b2 ℓ
  have h3 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m3 ℓ τ z) _ := B4P3b3 ℓ
  have h4 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m4 ℓ τ z) _ := B4P3b4 ℓ
  have h5 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m5 ℓ τ z) _ := B4P3b5 ℓ
  have h6 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m6 ℓ τ z) _ := B4P3b6 ℓ
  have h7 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4P3m7 ℓ τ z) _ := B4P3b7 ℓ
  have hsum : Work.Asymptotics.KhatE1.Bound (fun τ z => (B4P3m0 ℓ τ z) + (B4P3m1 ℓ τ z) + (B4P3m2 ℓ τ z) + (B4P3m3 ℓ τ z) + (B4P3m4 ℓ τ z) + (B4P3m5 ℓ τ z) + (B4P3m6 ℓ τ z) + (B4P3m7 ℓ τ z)) _ :=
    (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add h0 h1) h2) h3) h4) h5) h6) h7)
  exact Work.Asymptotics.KhatE1.Bound.congr (Work.Asymptotics.KhatE1.Bound.mono (Nat.zero_le _) hsum) (fun τ z => by
    simp only [B4P3])

noncomputable def B4Alpha2m0 (τ : UpperHalfPlane) : ℂ :=
      ((-691 : ℂ) / (96 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ

noncomputable def B4Alpha2 (τ : UpperHalfPlane) : ℂ :=
      B4Alpha2m0 τ

theorem B4Alpha2b0  :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Alpha2m0 τ) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((-691 : ℂ) / (96 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) B4b_E4) B4b_E6)) (fun τ z => by
    simp only [B4Alpha2m0])

theorem B4Alpha2_boundX  :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Alpha2 τ) 0 := by
  have h0 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Alpha2m0 τ) _ := B4Alpha2b0 
  have hsum : Work.Asymptotics.KhatE1.Bound (fun τ z => (B4Alpha2m0 τ)) _ :=
    h0
  exact Work.Asymptotics.KhatE1.Bound.congr (Work.Asymptotics.KhatE1.Bound.mono (Nat.zero_le _) hsum) (fun τ z => by
    simp only [B4Alpha2])

noncomputable def B4Alpha4m0 (τ : UpperHalfPlane) : ℂ :=
      ((-461 : ℂ) / (96 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ

noncomputable def B4Alpha4 (τ : UpperHalfPlane) : ℂ :=
      B4Alpha4m0 τ

theorem B4Alpha4b0  :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Alpha4m0 τ) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((-461 : ℂ) / (96 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) B4b_E4) B4b_E4)) (fun τ z => by
    simp only [B4Alpha4m0])

theorem B4Alpha4_boundX  :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Alpha4 τ) 0 := by
  have h0 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Alpha4m0 τ) _ := B4Alpha4b0 
  have hsum : Work.Asymptotics.KhatE1.Bound (fun τ z => (B4Alpha4m0 τ)) _ :=
    h0
  exact Work.Asymptotics.KhatE1.Bound.congr (Work.Asymptotics.KhatE1.Bound.mono (Nat.zero_le _) hsum) (fun τ z => by
    simp only [B4Alpha4])

noncomputable def B4Bsidem0 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-36236320 : ℂ) / (9 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem1 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((413840 : ℂ) / (9 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem2 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-11351920 : ℂ) / (9 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4Bsidem3 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((254386 : ℂ) / (27 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem4 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-8798 : ℂ) / (81 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem5 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((169256 : ℂ) / (81 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4Bsidem6 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-2480 : ℂ) / (27 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem7 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((3695 : ℂ) / (162 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem8 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-885215 : ℂ) / (162 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4Bsidem9 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-2588 : ℂ) / (27 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem10 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-803065 : ℂ) / (162 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem11 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((-85583 : ℂ) / (162 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ)

noncomputable def B4Bsidem12 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-36236320 : ℂ) / (3 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.DeltaFun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem13 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((413840 : ℂ) / (3 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.DeltaFun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem14 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-11351920 : ℂ) / (3 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.DeltaFun τ * (z : ℂ) * (z : ℂ)

noncomputable def B4Bsidem15 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-4960 : ℂ) / (9 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem16 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((3695 : ℂ) / (27 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem17 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-885215 : ℂ) / (27 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * (z : ℂ) * (z : ℂ)

noncomputable def B4Bsidem18 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((254386 : ℂ) / (9 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem19 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-8798 : ℂ) / (27 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z

noncomputable def B4Bsidem20 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((169256 : ℂ) / (27 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * (z : ℂ) * (z : ℂ)

noncomputable def B4Bsidem21 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-69139520 : ℂ) * Complex.I) * Work.Kernels.DeltaFun τ * (z : ℂ)

noncomputable def B4Bsidem22 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((161748 : ℂ) * Complex.I) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * (z : ℂ)

noncomputable def B4Bsidem23 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (-69139520 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.cuspC ℓ

noncomputable def B4Bsidem24 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (161748 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.cuspC ℓ

noncomputable def B4Bsidem25 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (5190880 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.DeltaFun τ

noncomputable def B4Bsidem26 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-1012385 : ℂ) / (18 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ

noncomputable def B4Bsidem27 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      ((-600919 : ℂ) / (18 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ

noncomputable def B4Bsidem28 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (-636 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ

noncomputable def B4Bside (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      B4Bsidem0 ℓ τ z
      + B4Bsidem1 ℓ τ z
      + B4Bsidem2 ℓ τ z
      + B4Bsidem3 ℓ τ z
      + B4Bsidem4 ℓ τ z
      + B4Bsidem5 ℓ τ z
      + B4Bsidem6 ℓ τ z
      + B4Bsidem7 ℓ τ z
      + B4Bsidem8 ℓ τ z
      + B4Bsidem9 ℓ τ z
      + B4Bsidem10 ℓ τ z
      + B4Bsidem11 ℓ τ z
      + B4Bsidem12 ℓ τ z
      + B4Bsidem13 ℓ τ z
      + B4Bsidem14 ℓ τ z
      + B4Bsidem15 ℓ τ z
      + B4Bsidem16 ℓ τ z
      + B4Bsidem17 ℓ τ z
      + B4Bsidem18 ℓ τ z
      + B4Bsidem19 ℓ τ z
      + B4Bsidem20 ℓ τ z
      + B4Bsidem21 ℓ τ z
      + B4Bsidem22 ℓ τ z
      + B4Bsidem23 ℓ τ z
      + B4Bsidem24 ℓ τ z
      + B4Bsidem25 ℓ τ z
      + B4Bsidem26 ℓ τ z
      + B4Bsidem27 ℓ τ z
      + B4Bsidem28 ℓ τ z

theorem B4Bsideb0 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem0 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-36236320 : ℂ) / (9 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E2) B4b_DeltaFun) B4b_tau) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem0])

theorem B4Bsideb1 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem1 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((413840 : ℂ) / (9 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E2) B4b_DeltaFun) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem1])

theorem B4Bsideb2 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem2 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-11351920 : ℂ) / (9 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E2) B4b_DeltaFun) B4b_tau) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4Bsidem2])

theorem B4Bsideb3 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem3 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((254386 : ℂ) / (27 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E4) B4b_E4) B4b_E2) B4b_tau) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem3])

theorem B4Bsideb4 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem4 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-8798 : ℂ) / (81 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E4) B4b_E4) B4b_E2) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem4])

theorem B4Bsideb5 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem5 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((169256 : ℂ) / (81 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E4) B4b_E4) B4b_E2) B4b_tau) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4Bsidem5])

theorem B4Bsideb6 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem6 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-2480 : ℂ) / (27 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E6) B4b_E2) B4b_E2) B4b_tau) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem6])

theorem B4Bsideb7 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem7 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((3695 : ℂ) / (162 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E6) B4b_E2) B4b_E2) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem7])

theorem B4Bsideb8 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem8 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-885215 : ℂ) / (162 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E6) B4b_E2) B4b_E2) B4b_tau) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4Bsidem8])

theorem B4Bsideb9 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem9 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-2588 : ℂ) / (27 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E4) B4b_E6) B4b_tau) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem9])

theorem B4Bsideb10 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem10 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-803065 : ℂ) / (162 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E4) B4b_E6) B4b_tau) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem10])

theorem B4Bsideb11 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem11 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((((-85583 : ℂ) / (162 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2)) B4b_E4) B4b_E4) B4b_E6) B4b_tau) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4Bsidem11])

theorem B4Bsideb12 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem12 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-36236320 : ℂ) / (3 : ℂ)) * (Real.pi : ℂ))) B4b_DeltaFun) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem12])

theorem B4Bsideb13 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem13 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((413840 : ℂ) / (3 : ℂ)) * (Real.pi : ℂ))) B4b_DeltaFun) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem13])

theorem B4Bsideb14 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem14 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((-11351920 : ℂ) / (3 : ℂ)) * (Real.pi : ℂ))) B4b_DeltaFun) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4Bsidem14])

theorem B4Bsideb15 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem15 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-4960 : ℂ) / (9 : ℂ)) * (Real.pi : ℂ))) B4b_E4) B4b_E6) B4b_E2) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem15])

theorem B4Bsideb16 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem16 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((3695 : ℂ) / (27 : ℂ)) * (Real.pi : ℂ))) B4b_E4) B4b_E6) B4b_E2) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem16])

theorem B4Bsideb17 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem17 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-885215 : ℂ) / (27 : ℂ)) * (Real.pi : ℂ))) B4b_E4) B4b_E6) B4b_E2) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4Bsidem17])

theorem B4Bsideb18 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem18 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((254386 : ℂ) / (9 : ℂ)) * (Real.pi : ℂ))) B4b_E4) B4b_E4) B4b_E4) B4b_z) B4b_z) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem18])

theorem B4Bsideb19 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem19 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((-8798 : ℂ) / (27 : ℂ)) * (Real.pi : ℂ))) B4b_E4) B4b_E4) B4b_E4) B4b_z) B4b_z) B4b_S0) B4b_S0)) (fun τ z => by
    simp only [B4Bsidem19])

theorem B4Bsideb20 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem20 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((169256 : ℂ) / (27 : ℂ)) * (Real.pi : ℂ))) B4b_E4) B4b_E4) B4b_E4) B4b_z) B4b_z)) (fun τ z => by
    simp only [B4Bsidem20])

theorem B4Bsideb21 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem21 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const (((-69139520 : ℂ) * Complex.I))) B4b_DeltaFun) B4b_z)) (fun τ z => by
    simp only [B4Bsidem21])

theorem B4Bsideb22 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem22 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const (((161748 : ℂ) * Complex.I))) B4b_E4) B4b_E4) B4b_E4) B4b_z)) (fun τ z => by
    simp only [B4Bsidem22])

theorem B4Bsideb23 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem23 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_const ((-69139520 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) B4b_DeltaFun) (B4b_cuspC ℓ))) (fun τ z => by
    simp only [B4Bsidem23])

theorem B4Bsideb24 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem24 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_mul (B4b_const ((161748 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) B4b_E4) B4b_E4) B4b_E4) (B4b_cuspC ℓ))) (fun τ z => by
    simp only [B4Bsidem24])

theorem B4Bsideb25 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem25 ℓ τ z) 1 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_const ((5190880 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) B4b_DeltaFun)) (fun τ z => by
    simp only [B4Bsidem25])

theorem B4Bsideb26 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem26 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((-1012385 : ℂ) / (18 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) B4b_E4) B4b_E6) (B4b_psi2 ℓ))) (fun τ z => by
    simp only [B4Bsidem26])

theorem B4Bsideb27 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem27 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const (((-600919 : ℂ) / (18 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) B4b_E4) B4b_E4) (B4b_psi4 ℓ))) (fun τ z => by
    simp only [B4Bsidem27])

theorem B4Bsideb28 (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem28 ℓ τ z) 0 :=
  Work.Asymptotics.KhatE1.Bound.congr ((B4b_mul (B4b_mul (B4b_mul (B4b_const ((-636 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)))) B4b_E4) B4b_E4) B4b_E4)) (fun τ z => by
    simp only [B4Bsidem28])

theorem B4Bside_boundX (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bside ℓ τ z) 0 := by
  have h0 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem0 ℓ τ z) _ := B4Bsideb0 ℓ
  have h1 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem1 ℓ τ z) _ := B4Bsideb1 ℓ
  have h2 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem2 ℓ τ z) _ := B4Bsideb2 ℓ
  have h3 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem3 ℓ τ z) _ := B4Bsideb3 ℓ
  have h4 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem4 ℓ τ z) _ := B4Bsideb4 ℓ
  have h5 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem5 ℓ τ z) _ := B4Bsideb5 ℓ
  have h6 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem6 ℓ τ z) _ := B4Bsideb6 ℓ
  have h7 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem7 ℓ τ z) _ := B4Bsideb7 ℓ
  have h8 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem8 ℓ τ z) _ := B4Bsideb8 ℓ
  have h9 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem9 ℓ τ z) _ := B4Bsideb9 ℓ
  have h10 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem10 ℓ τ z) _ := B4Bsideb10 ℓ
  have h11 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem11 ℓ τ z) _ := B4Bsideb11 ℓ
  have h12 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem12 ℓ τ z) _ := B4Bsideb12 ℓ
  have h13 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem13 ℓ τ z) _ := B4Bsideb13 ℓ
  have h14 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem14 ℓ τ z) _ := B4Bsideb14 ℓ
  have h15 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem15 ℓ τ z) _ := B4Bsideb15 ℓ
  have h16 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem16 ℓ τ z) _ := B4Bsideb16 ℓ
  have h17 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem17 ℓ τ z) _ := B4Bsideb17 ℓ
  have h18 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem18 ℓ τ z) _ := B4Bsideb18 ℓ
  have h19 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem19 ℓ τ z) _ := B4Bsideb19 ℓ
  have h20 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem20 ℓ τ z) _ := B4Bsideb20 ℓ
  have h21 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem21 ℓ τ z) _ := B4Bsideb21 ℓ
  have h22 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem22 ℓ τ z) _ := B4Bsideb22 ℓ
  have h23 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem23 ℓ τ z) _ := B4Bsideb23 ℓ
  have h24 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem24 ℓ τ z) _ := B4Bsideb24 ℓ
  have h25 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem25 ℓ τ z) _ := B4Bsideb25 ℓ
  have h26 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem26 ℓ τ z) _ := B4Bsideb26 ℓ
  have h27 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem27 ℓ τ z) _ := B4Bsideb27 ℓ
  have h28 : Work.Asymptotics.KhatE1.Bound (fun τ z => B4Bsidem28 ℓ τ z) _ := B4Bsideb28 ℓ
  have hsum : Work.Asymptotics.KhatE1.Bound (fun τ z => (B4Bsidem0 ℓ τ z) + (B4Bsidem1 ℓ τ z) + (B4Bsidem2 ℓ τ z) + (B4Bsidem3 ℓ τ z) + (B4Bsidem4 ℓ τ z) + (B4Bsidem5 ℓ τ z) + (B4Bsidem6 ℓ τ z) + (B4Bsidem7 ℓ τ z) + (B4Bsidem8 ℓ τ z) + (B4Bsidem9 ℓ τ z) + (B4Bsidem10 ℓ τ z) + (B4Bsidem11 ℓ τ z) + (B4Bsidem12 ℓ τ z) + (B4Bsidem13 ℓ τ z) + (B4Bsidem14 ℓ τ z) + (B4Bsidem15 ℓ τ z) + (B4Bsidem16 ℓ τ z) + (B4Bsidem17 ℓ τ z) + (B4Bsidem18 ℓ τ z) + (B4Bsidem19 ℓ τ z) + (B4Bsidem20 ℓ τ z) + (B4Bsidem21 ℓ τ z) + (B4Bsidem22 ℓ τ z) + (B4Bsidem23 ℓ τ z) + (B4Bsidem24 ℓ τ z) + (B4Bsidem25 ℓ τ z) + (B4Bsidem26 ℓ τ z) + (B4Bsidem27 ℓ τ z) + (B4Bsidem28 ℓ τ z)) _ :=
    (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add (B4b_add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28)
  exact Work.Asymptotics.KhatE1.Bound.congr (Work.Asymptotics.KhatE1.Bound.mono (Nat.zero_le _) hsum) (fun τ z => by
    simp only [B4Bside])
noncomputable def B4Aside (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) : ℂ :=
      (((13 : ℂ) / (12 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z
      + (((1 : ℂ) / (16 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z
      + (((-71 : ℂ) / (48 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ)
      + (((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z
      + (((-1 : ℂ) / (32 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z
      + (((7 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * Work.Kernels.E2Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ)
      + (((1 : ℂ) / (8 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z
      + (((-67 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z
      + (((71 : ℂ) / (96 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * (τ : ℂ) * (z : ℂ) * (z : ℂ)
      + ((3 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z
      + ((-3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z
      + ((7 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ * (z : ℂ) * (z : ℂ)
      + ((13 : ℂ) / (4 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z
      + ((3 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z
      + ((-71 : ℂ) / (16 : ℂ)) * (Real.pi : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * (z : ℂ) * (z : ℂ)
      + ((24 : ℂ) * Complex.I) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * (z : ℂ)
      + (24 : ℂ) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.cuspC ℓ
      + ((-691 : ℂ) / (96 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ
      + ((-461 : ℂ) / (96 : ℂ)) * (((Real.pi : ℂ)) ^ (-1 : ℤ)) * Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ


noncomputable def B4Corr (τ z : UpperHalfPlane) : ℂ :=
      (((4 : ℂ) / (3 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z
      + (((-2 : ℂ) / (3 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z * Work.Asymptotics.KhatE1.S0z z
      + (((-2 : ℂ) / (3 : ℂ)) * Complex.I) * ((Real.pi : ℂ)) ^ 2 * (τ : ℂ) * (z : ℂ) * (z : ℂ)
      + (4 : ℂ) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ) * Work.Asymptotics.KhatE1.S0z z
      + (-4 : ℂ) * (Real.pi : ℂ) * (z : ℂ) * (z : ℂ)
      + ((-24 : ℂ) * Complex.I) * (τ : ℂ)
      + ((24 : ℂ) * Complex.I) * (z : ℂ)

/-! ## The two identities -/

/-- `B4Corr` vanishes identically: it is the remainder of the `u = 0` substitution in
`B4Aside_decomp_corr`, and it vanishes because `S0z z = 1 - 6i/(πz)`. -/
theorem B4_corr_zero (τ z : UpperHalfPlane) : B4Corr τ z = 0 := by
  have hz : (z : ℂ) ≠ 0 := by
    intro h
    have h1 : ((z : ℂ)).im = 0 := by rw [h]; simp
    rw [UpperHalfPlane.coe_im] at h1
    exact (ne_of_gt z.im_pos) h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [B4Corr, Work.Asymptotics.KhatE1.S0z]
  field_simp
  ring_nf
  simp only [Complex.I_pow_three]
  ring

/-- **The algebraic core.**  The `j(τ)`-coefficient of `Bracket24B4` is the sum of the
`τ`-deviations `u₁,…,u₅` times explicit polynomials, plus the (vanishing) `B4Corr`. -/
theorem B4Aside_decomp_corr (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    B4Aside ℓ τ z = B4u1 τ * B4P1 ℓ τ z + B4u2 τ * B4P2 ℓ τ z + B4u3 τ * B4P3 ℓ τ z
      + B4u4 ℓ τ * B4Alpha2 τ + B4u5 ℓ τ * B4Alpha4 τ + B4Corr τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [B4Aside, B4P1, B4P2, B4P3, B4Alpha2, B4Alpha4, B4Corr,
    B4u1, B4u2, B4u3, B4u4, B4u5, B4Lam,
    B4P1m0, B4P1m1, B4P1m2, B4P1m3, B4P1m4, B4P1m5, B4P1m6, B4P1m7, B4P1m8, B4P1m9, B4P1m10, B4P1m11, B4P1m12, B4P1m13, B4P1m14, B4P1m15, B4P1m16, B4P1m17, B4P1m18, B4P1m19, B4P1m20, B4P1m21, B4P1m22, B4P1m23, B4P1m24, B4P1m25, B4P1m26, B4P1m27, B4P1m28, B4P1m29, B4P1m30, B4P1m31, B4P1m32, B4P1m33, B4P1m34, B4P1m35, B4P1m36, B4P1m37, B4P1m38, B4P1m39, B4P1m40, B4P1m41, B4P1m42, B4P1m43, B4P1m44, B4P1m45, B4P1m46, B4P1m47, B4P1m48, B4P1m49, B4P1m50, B4P1m51, B4P1m52, B4P1m53, B4P1m54, B4P1m55, B4P1m56, B4P1m57, B4P1m58, B4P1m59, B4P1m60, B4P2m0, B4P2m1, B4P2m2, B4P2m3, B4P2m4, B4P2m5, B4P2m6, B4P2m7, B4P2m8, B4P2m9, B4P2m10, B4P2m11, B4P2m12, B4P2m13, B4P2m14, B4P2m15, B4P2m16, B4P3m0, B4P3m1, B4P3m2, B4P3m3, B4P3m4, B4P3m5, B4P3m6, B4P3m7, B4Alpha2m0, B4Alpha4m0, B4Bsidem0, B4Bsidem1, B4Bsidem2, B4Bsidem3, B4Bsidem4, B4Bsidem5, B4Bsidem6, B4Bsidem7, B4Bsidem8, B4Bsidem9, B4Bsidem10, B4Bsidem11, B4Bsidem12, B4Bsidem13, B4Bsidem14, B4Bsidem15, B4Bsidem16, B4Bsidem17, B4Bsidem18, B4Bsidem19, B4Bsidem20, B4Bsidem21, B4Bsidem22, B4Bsidem23, B4Bsidem24, B4Bsidem25, B4Bsidem26, B4Bsidem27, B4Bsidem28, zpow_neg_one]
  field_simp
  ring

/-- **The algebraic core**, with the vanishing remainder dropped. -/
theorem B4Aside_decomp (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    B4Aside ℓ τ z = B4u1 τ * B4P1 ℓ τ z + B4u2 τ * B4P2 ℓ τ z + B4u3 τ * B4P3 ℓ τ z
      + B4u4 ℓ τ * B4Alpha2 τ + B4u5 ℓ τ * B4Alpha4 τ := by
  rw [B4Aside_decomp_corr ℓ τ z, B4_corr_zero τ z, add_zero]

/-- **The split of `Bracket24B4`** into `Aside·j + Bside`, using `Δ(τ)j(τ) = E₄(τ)³`. -/
theorem B4_decomp (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    Bracket24B4 ℓ τ z = B4Aside ℓ τ z * Work.Kernels.jInvariantFun τ + B4Bside ℓ τ z := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have h : Work.Kernels.DeltaFun τ * Bracket24B4 ℓ τ z
      = Work.Kernels.DeltaFun τ
          * (B4Aside ℓ τ z * Work.Kernels.jInvariantFun τ + B4Bside ℓ τ z) := by
    simp only [Bracket24B4, B4Aside, B4Bside, Work.Kernels.jInvariantFun,
      B4Bsidem0, B4Bsidem1, B4Bsidem2, B4Bsidem3, B4Bsidem4, B4Bsidem5, B4Bsidem6, B4Bsidem7, B4Bsidem8, B4Bsidem9, B4Bsidem10, B4Bsidem11, B4Bsidem12, B4Bsidem13, B4Bsidem14, B4Bsidem15, B4Bsidem16, B4Bsidem17, B4Bsidem18, B4Bsidem19, B4Bsidem20, B4Bsidem21, B4Bsidem22, B4Bsidem23, B4Bsidem24, B4Bsidem25, B4Bsidem26, B4Bsidem27, B4Bsidem28]
    field_simp
    ring_nf
  exact mul_left_cancel₀ hD h

/-! ## The final bound -/

private lemma b4_three_le {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) : a * b * c ≤ a' * b' * c' := by
  have hb' : 0 ≤ b' := le_trans hb0 hb
  exact mul_le_mul (mul_le_mul ha hb hb0 (le_trans ha0 ha)) hc hc0
    (mul_nonneg (le_trans ha0 ha) hb')

private lemma b4_rpow_scale_mono {N N' : ℝ} (h : N ≤ N') (τ : UpperHalfPlane) :
    Work.Kernels.scale τ ^ N ≤ Work.Kernels.scale τ ^ N' :=
  Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) h

private lemma b4_rpow_t_mono {M M' : ℝ} (h : M ≤ M') {τ : UpperHalfPlane} {t : ℝ}
    (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t) :
    (1 + t) ^ M ≤ (1 + t) ^ M' :=
  Real.rpow_le_rpow_of_exponent_le (by have := hτ.2; linarith) h

theorem Bracket24B4Bound_proof (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1Core.Bracket24B4Bound ℓ := by
  have hP1 := B4P1_boundX ℓ
  have hP2 := B4P2_boundX ℓ
  have hP3 := B4P3_boundX ℓ
  have hA2 := B4Alpha2_boundX
  have hA4 := B4Alpha4_boundX
  have hBside := B4Bside_boundX ℓ
  have h1P : Bound (fun τ z => B4u1 τ * B4P1 ℓ τ z) 1 := B4b_u1.mul hP1
  have h2P : Bound (fun τ z => B4u2 τ * B4P2 ℓ τ z) 1 := B4b_u2.mul hP2
  have h3P : Bound (fun τ z => B4u3 τ * B4P3 ℓ τ z) 1 := B4b_u3.mul hP3
  have h4P : Bound (fun τ z => B4u4 ℓ τ * B4Alpha2 τ) 1 := (B4b_u4 ℓ).mul hA2
  have h5P : Bound (fun τ z => B4u5 ℓ τ * B4Alpha4 τ) 1 := (B4b_u5 ℓ).mul hA4
  have hsum : Bound (fun τ z => B4u1 τ * B4P1 ℓ τ z + B4u2 τ * B4P2 ℓ τ z
      + B4u3 τ * B4P3 ℓ τ z + B4u4 ℓ τ * B4Alpha2 τ + B4u5 ℓ τ * B4Alpha4 τ) 1 :=
    (((h1P.add h2P).add h3P).add h4P).add h5P
  have hAside : Bound (fun τ z => B4Aside ℓ τ z) 1 :=
    Bound.congr hsum (fun τ z => (B4Aside_decomp ℓ τ z).symm)
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hAside
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hBside
  refine ⟨(27 / 4) * C1 + C2 + 1, max N1 N2, max M1 M2, by positivity,
    le_trans hN1 (le_max_left _ _), le_trans hM1 (le_max_left _ _), ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hS0 : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hU0 : (0 : ℝ) ≤ 1 + t := by have := hF.2; linarith
  have hq0 : 0 < ‖Work.Kernels.qParamFun τ‖ := by
    rw [Work.Asymptotics.norm_qParamFun]; exact Real.exp_pos _
  have hqne : ‖Work.Kernels.qParamFun τ‖ ≠ 0 := ne_of_gt hq0
  have hq0' : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := le_of_lt hq0
  have hj : ‖Work.Kernels.jInvariantFun τ‖
      ≤ (27 / 4) * (‖Work.Kernels.qParamFun τ‖)⁻¹ := by
    have h := Work.Asymptotics.Funnel24.norm_j_funnel τ hF
    rw [Work.Asymptotics.norm_qParamFun, ← Real.exp_neg]
    simpa using h
  have hb1' := hb1 τ z t hF ht hz0 hz1 hzim
  have hb2' := hb2 τ z t hF ht hz0 hz1 hzim
  have hAj : ‖B4Aside ℓ τ z * Work.Kernels.jInvariantFun τ‖
      ≤ (27 / 4) * C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by
    have hstep : ‖B4Aside ℓ τ z‖ * ‖Work.Kernels.jInvariantFun τ‖
        ≤ (C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
            * ‖Work.Kernels.qParamFun τ‖ ^ 1)
          * ((27 / 4) * (‖Work.Kernels.qParamFun τ‖)⁻¹) :=
      mul_le_mul hb1' hj (norm_nonneg _) (by
        have h1 := Real.rpow_nonneg hS0 N1
        have h2 := Real.rpow_nonneg hU0 M1
        have h3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 1 := by positivity
        exact mul_nonneg (mul_nonneg (mul_nonneg hC1.le h1) h2) h3)
    have hval : (C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
            * ‖Work.Kernels.qParamFun τ‖ ^ 1)
          * ((27 / 4) * (‖Work.Kernels.qParamFun τ‖)⁻¹)
        = (27 / 4) * C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1 := by
      rw [pow_one]
      field_simp
    have hmono : (27 / 4) * C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        ≤ (27 / 4) * C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      b4_three_le (le_refl _) (b4_rpow_scale_mono (le_max_left _ _) τ)
        (b4_rpow_t_mono (le_max_left _ _) hF ht) (by positivity)
        (Real.rpow_nonneg hS0 N1) (Real.rpow_nonneg hU0 M1)
    rw [norm_mul]
    exact le_trans (le_trans hstep (le_of_eq hval)) hmono
  have hBj : ‖B4Bside ℓ τ z‖
      ≤ C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by
    have h := hb2'
    rw [pow_zero, mul_one] at h
    exact le_trans h (b4_three_le (le_refl _) (b4_rpow_scale_mono (le_max_right _ _) τ)
      (b4_rpow_t_mono (le_max_right _ _) hF ht) hC2.le
      (Real.rpow_nonneg hS0 N2) (Real.rpow_nonneg hU0 M2))
  have hfin : (27 / 4) * C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        + C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
      ≤ ((27 / 4) * C1 + C2 + 1) * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) := by
    have h0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_nonneg (Real.rpow_nonneg hS0 _) (Real.rpow_nonneg hU0 _)
    rw [show (27 / 4) * C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
          + C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        = ((27 / 4) * C1 + C2) * ((Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2)) by ring,
      show ((27 / 4) * C1 + C2 + 1) * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2)
        = ((27 / 4) * C1 + C2 + 1) * ((Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2)) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) h0
  rw [B4_decomp ℓ τ z]
  exact le_trans (norm_add_le _ _) (le_trans (add_le_add hAj hBj) hfin)

end

end Work.Asymptotics.KhatE1Core
