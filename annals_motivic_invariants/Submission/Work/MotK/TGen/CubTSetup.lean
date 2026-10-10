/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.CubTRedDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.CubTSetup` — the change of variables for the cubic `cubTRed`

This file collects the elementary (ring-theoretic) infrastructure for the proof that
`cubTRed a b h` is a prime element of `K[x₀,x₁,x₂]` (`Work.MotK.TGen.CubTPrime`).

The cubic is of degree `3` in `x₀`:

```
cubTRed = α·x₀³ + β·x₀² + γ·x₀ + δ
  α = a²b²h
  β = -2a³bh·x₂
  γ = a⁴h·x₂² - b⁴·x₂ + 2ab³h·x₁² - ab³h·x₁
  δ = -a²b²h·x₁²x₂ - ab³·x₁x₂² + a³b·x₁² - 2a³b·x₁ + a³b + 2ab³·x₂²
```

with leading coefficient `α ∈ K` a *unit* of `K[x₁,x₂]`.  We record the algebra equivalence

`cubTPhi : K[x₀,x₁,x₂] ≃ₐ[K] K[x₁,x₂][X]`,  `X 0 ↦ X`, `X 1 ↦ C (X 0)`, `X 2 ↦ C (X 1)`

(`X 0, X 1` on the right denoting the variables of `K[x₁,x₂]`), together with
`cubTPhi_cubTRed`, which rewrites `cubTRed` as the above cubic in the single variable `X`.

The second half of the file eliminates the variable `x₂` as well: `cubTPsi` is the equivalence
`K[x₁,x₂] ≃ₐ[K] K[x₁][X]` (`X 0 ↦ C (X 0)`, `X 1 ↦ X`), and the intermediate coefficients
`α, β, γ, δ` acquire the explicit forms recorded in `cubTPsi_cubTAl`, … , `cubTPsi_cubTDe`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K]

/-! ## The equivalence `K[x₀,x₁,x₂] ≃ₐ[K] K[x₁,x₂][X]` -/

/-- The `K`-algebra equivalence `K[x₀,x₁,x₂] ≃ₐ[K] K[x₁,x₂][X]` sending `X 0 ↦ X`,
`X 1 ↦ C (X 0)` and `X 2 ↦ C (X 1)`. -/
def cubTPhi (K : Type*) [Field K] :
    MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  MvPolynomial.finSuccEquiv K 2

theorem cubTPhi_X_zero (K : Type*) [Field K] :
    cubTPhi K (MvPolynomial.X 0) = Polynomial.X :=
  MvPolynomial.finSuccEquiv_X_zero

theorem cubTPhi_X_one (K : Type*) [Field K] :
    cubTPhi K (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) := by
  rw [cubTPhi, show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl]
  exact MvPolynomial.finSuccEquiv_X_succ

theorem cubTPhi_X_two (K : Type*) [Field K] :
    cubTPhi K (MvPolynomial.X 2) = Polynomial.C (MvPolynomial.X 1) := by
  rw [cubTPhi, show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl]
  exact MvPolynomial.finSuccEquiv_X_succ

theorem cubTPhi_C (K : Type*) [Field K] (r : K) :
    cubTPhi K (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq K (Fin 3), (cubTPhi K).commutes,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq K (Fin 2)]

/-! ## The explicit coefficients `α, β, γ, δ ∈ K[x₁,x₂]` -/

/-- `α = a²b²h`: the leading coefficient of `cubTRed` in `x₀`. -/
def cubTAl {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (a ^ 2 * b ^ 2 * h)

/-- `β = -2a³bh·x₂`: the `x₀²` coefficient of `cubTRed`. -/
def cubTBe {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (-2 * a ^ 3 * b * h) * MvPolynomial.X 1

/-- `γ = a⁴h·x₂² - b⁴·x₂ + 2ab³h·x₁² - ab³h·x₁`: the `x₀` coefficient of `cubTRed`. -/
def cubTGa {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (a ^ 4 * h) * MvPolynomial.X 1 ^ 2
    - MvPolynomial.C (b ^ 4) * MvPolynomial.X 1
    + MvPolynomial.C (2 * a * b ^ 3 * h) * MvPolynomial.X 0 ^ 2
    - MvPolynomial.C (a * b ^ 3 * h) * MvPolynomial.X 0

/-- `δ`: the constant term of `cubTRed` in `x₀`. -/
def cubTDe {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 2) K :=
  - MvPolynomial.C (a ^ 2 * b ^ 2 * h) * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1
    - MvPolynomial.C (a * b ^ 3) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (a ^ 3 * b) * MvPolynomial.X 0 ^ 2
    - MvPolynomial.C (2 * a ^ 3 * b) * MvPolynomial.X 0
    + MvPolynomial.C (a ^ 3 * b)
    + MvPolynomial.C (2 * a * b ^ 3) * MvPolynomial.X 1 ^ 2

/-- **The cubic in normal form**: `cubTRed = α·X³ + β·X² + γ·X + δ` under `cubTPhi`. -/
theorem cubTPhi_cubTRed (a b h : K) :
    cubTPhi K (cubTRed a b h)
      = Polynomial.C (cubTAl a b h) * Polynomial.X ^ 3
        + Polynomial.C (cubTBe a b h) * Polynomial.X ^ 2
        + Polynomial.C (cubTGa a b h) * Polynomial.X
        + Polynomial.C (cubTDe a b h) := by
  simp only [cubTRed, cubTAl, cubTBe, cubTGa, cubTDe, map_sub, map_add, map_mul, map_pow,
    map_ofNat, map_neg, map_one, cubTPhi_X_zero, cubTPhi_X_one, cubTPhi_X_two, cubTPhi_C]
  first | refl_ring1 | ring

/-! ## The equivalence `K[x₁,x₂] ≃ₐ[K] K[x₁][X]` and the images of `α, β, γ, δ` -/

/-- The `K`-algebra equivalence `K[x₁,x₂] ≃ₐ[K] K[x₁][X]` sending `X 0 ↦ C (X 0)` and
`X 1 ↦ X`. -/
def cubTPsi (K : Type*) [Field K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 1) K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap 0 1)).trans (MvPolynomial.finSuccEquiv K 1)

theorem cubTPsi_X_zero (K : Type*) [Field K] :
    cubTPsi K (MvPolynomial.X 0) = Polynomial.C (MvPolynomial.X 0) := by
  rw [cubTPsi, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    show (Equiv.swap (0 : Fin 2) 1) 0 = 1 from Equiv.swap_apply_left 0 1]
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl]
  exact MvPolynomial.finSuccEquiv_X_succ

theorem cubTPsi_X_one (K : Type*) [Field K] :
    cubTPsi K (MvPolynomial.X 1) = Polynomial.X := by
  rw [cubTPsi, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    show (Equiv.swap (0 : Fin 2) 1) 1 = 0 from Equiv.swap_apply_right 0 1]
  exact MvPolynomial.finSuccEquiv_X_zero

theorem cubTPsi_C (K : Type*) [Field K] (r : K) :
    cubTPsi K (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [cubTPsi, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C,
    ← MvPolynomial.algebraMap_eq K (Fin 2), AlgEquiv.commutes,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq K (Fin 1)]

/-! ### The images of `α, β, γ, δ` under `cubTPsi` -/

/-- The `X²`-coefficient of `cubTPsi β` (an element of `K[x₁]`), i.e. minus twice `a³bh`. -/
def cubTB {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C (-2 * a ^ 3 * b * h)

/-- The `X⁰` part of `cubTPsi γ`. -/
def cubTG0 {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C (2 * a * b ^ 3 * h) * MvPolynomial.X 0 ^ 2
    - MvPolynomial.C (a * b ^ 3 * h) * MvPolynomial.X 0

/-- The `X¹` part of `cubTPsi γ`. -/
def cubTG1 {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C (-(b ^ 4))

/-- The `X²` part of `cubTPsi γ`. -/
def cubTG2 {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C (a ^ 4 * h)

/-- The `X⁰` part of `cubTPsi δ`. -/
def cubTD0 {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C (a ^ 3 * b) * MvPolynomial.X 0 ^ 2
    - MvPolynomial.C (2 * a ^ 3 * b) * MvPolynomial.X 0
    + MvPolynomial.C (a ^ 3 * b)

/-- The `X¹` part of `cubTPsi δ`. -/
def cubTD1 {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C (-(a ^ 2 * b ^ 2 * h)) * MvPolynomial.X 0 ^ 2

/-- The `X²` part of `cubTPsi δ`. -/
def cubTD2 {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C (-(a * b ^ 3)) * MvPolynomial.X 0 + MvPolynomial.C (2 * a * b ^ 3)

theorem cubTPsi_cubTAl (a b h : K) :
    cubTPsi K (cubTAl a b h) = Polynomial.C (MvPolynomial.C (a ^ 2 * b ^ 2 * h)) := by
  simp only [cubTAl, cubTPsi_C]

theorem cubTPsi_cubTBe (a b h : K) :
    cubTPsi K (cubTBe a b h) = Polynomial.C (cubTB a b h) * Polynomial.X := by
  simp only [cubTBe, cubTB, map_mul, map_ofNat, map_neg, cubTPsi_C, cubTPsi_X_one]

theorem cubTPsi_cubTGa (a b h : K) :
    cubTPsi K (cubTGa a b h)
      = Polynomial.C (cubTG0 a b h) + Polynomial.C (cubTG1 a b h) * Polynomial.X
        + Polynomial.C (cubTG2 a b h) * Polynomial.X ^ 2 := by
  simp only [cubTGa, cubTG0, cubTG1, cubTG2, map_sub, map_add, map_mul, map_pow, map_ofNat,
    map_neg, cubTPsi_C, cubTPsi_X_zero, cubTPsi_X_one]
  first | refl_ring1 | ring

theorem cubTPsi_cubTDe (a b h : K) :
    cubTPsi K (cubTDe a b h)
      = Polynomial.C (cubTD0 a b h) + Polynomial.C (cubTD1 a b h) * Polynomial.X
        + Polynomial.C (cubTD2 a b h) * Polynomial.X ^ 2 := by
  simp only [cubTDe, cubTD0, cubTD1, cubTD2, map_sub, map_add, map_mul, map_pow, map_ofNat,
    map_neg, cubTPsi_C, cubTPsi_X_zero, cubTPsi_X_one]
  first | refl_ring1 | ring

/-! ## The inner (single-variable) cubic form -/

/-- `α ∈ K[x₁]`: the coefficient of `Q³` of the inner cubic form, i.e. the image of `cubTAl`
under `cubTPsi` (up to the identification `K[x₁] ↪ K[x₁][X]` by `C`). -/
def cubTA {K : Type*} [Field K] (a b h : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C (a ^ 2 * b ^ 2 * h)

/-- `ψ(γ) = C (cubTG0) + C (cubTG1)·X + C (cubTG2)·X² ∈ K[x₁][X]` (as an element of `K[x₁][X]`). -/
def cubTG {K : Type*} [Field K] (a b h : K) : Polynomial (MvPolynomial (Fin 1) K) :=
  Polynomial.C (cubTG0 a b h) + Polynomial.C (cubTG1 a b h) * Polynomial.X
    + Polynomial.C (cubTG2 a b h) * Polynomial.X ^ 2

/-- `ψ(δ) = C (cubTD0) + C (cubTD1)·X + C (cubTD2)·X² ∈ K[x₁][X]`. -/
def cubTD {K : Type*} [Field K] (a b h : K) : Polynomial (MvPolynomial (Fin 1) K) :=
  Polynomial.C (cubTD0 a b h) + Polynomial.C (cubTD1 a b h) * Polynomial.X
    + Polynomial.C (cubTD2 a b h) * Polynomial.X ^ 2

/-- The inner cubic form `Q ↦ ψ(α)·Q³ + ψ(β)·Q² + ψ(γ)·Q + ψ(δ)`; a point `p` of `K[x₁,x₂]` is a
root of the outer cubic `cubTRed` exactly when `cubTEval` vanishes at `cubTPsi p`
(`cubTPsi_eval_cubTPhi`). -/
def cubTEval {K : Type*} [Field K] (a b h : K) (Q : Polynomial (MvPolynomial (Fin 1) K)) :
    Polynomial (MvPolynomial (Fin 1) K) :=
  Polynomial.C (cubTA a b h) * Q ^ 3 + Polynomial.C (cubTB a b h) * Polynomial.X * Q ^ 2
    + cubTG a b h * Q + cubTD a b h

theorem cubTPsi_cubTAl' (a b h : K) :
    cubTPsi K (cubTAl a b h) = Polynomial.C (cubTA a b h) := by
  rw [cubTPsi_cubTAl, cubTA]

theorem cubTPsi_cubTGa' (a b h : K) : cubTPsi K (cubTGa a b h) = cubTG a b h :=
  cubTPsi_cubTGa a b h

theorem cubTPsi_cubTDe' (a b h : K) : cubTPsi K (cubTDe a b h) = cubTD a b h :=
  cubTPsi_cubTDe a b h

/-- **The transfer of the root equation.**  The `cubTPsi`-image of the evaluation of the cubic
`cubTRed` at a point `p ∈ K[x₁,x₂]` is the inner form `cubTEval` at `cubTPsi p`. -/
theorem cubTPsi_eval_cubTPhi (a b h : K) (p : MvPolynomial (Fin 2) K) :
    cubTPsi K (Polynomial.eval p (cubTPhi K (cubTRed a b h))) = cubTEval a b h (cubTPsi K p) := by
  rw [cubTPhi_cubTRed]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, map_add, map_mul, map_pow, cubTPsi_cubTAl', cubTPsi_cubTBe, cubTPsi_cubTGa',
    cubTPsi_cubTDe', cubTEval, cubTG, cubTD]

/-- `cubTD0 ≠ 0`: its constant coefficient is `a³b ≠ 0`. -/
theorem cubTD0_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) : cubTD0 a b h ≠ 0 := by
  intro h0
  have h1 : MvPolynomial.constantCoeff (cubTD0 a b h) = a ^ 3 * b := by
    simp only [cubTD0, map_add, map_sub, map_mul, map_pow, MvPolynomial.constantCoeff_C,
      MvPolynomial.constantCoeff_X, mul_zero, add_zero]
    first | refl_ring1 | ring
  rw [h0] at h1
  simp only [map_zero] at h1
  exact (mul_ne_zero (pow_ne_zero 3 ha) hb) h1.symm

/-- `cubTD ≠ 0` (its `X⁰`-coefficient is `cubTD0 ≠ 0`). -/
theorem cubTD_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) : cubTD a b h ≠ 0 := by
  intro h0
  have h1 : (cubTD a b h).eval 0 = cubTD0 a b h := by
    simp [cubTD]
  rw [h0, Polynomial.eval_zero] at h1
  exact cubTD0_ne_zero a b h ha hb h1.symm

/-- `cubTEval a b h 0 ≠ 0`: the value at `Q = 0` is `cubTD a b h ≠ 0`. -/
theorem cubTEval_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) : cubTEval a b h 0 ≠ 0 := by
  have hz : cubTEval a b h 0 = cubTD a b h := by
    simp [cubTEval]
  rw [hz]
  exact cubTD_ne_zero a b h ha hb

end

end Work.MotK.TGen
