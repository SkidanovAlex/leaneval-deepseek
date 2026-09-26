import Mathlib

/-!
# Quasimodular forms for `SL(2, ℤ)`: definitions

This file sets up the vocabulary for the quasimodular-forms chapter of the CKMRV
Fourier-interpolation project.  Everything is for the full modular group
`𝒮ℒ = SL(2, ℤ)` (as a subgroup of `GL(2, ℝ)`) acting on the upper half plane `ℍ`.

## Conventions

* `ℍ = UpperHalfPlane`, `q = exp (2 π i τ)`, slash action `f ∣[k] γ`.
* `E2 : ℍ → ℂ` is the normalized weight-two Eisenstein series of Mathlib,
  `E2 τ = 1 - 24 ∑_{n ≥ 1} σ₁(n) q^n`  (`EisensteinSeries.E2_eq_tsum_cexp`).
  It is *not* modular: `E2 (-1/τ) = τ^2 E2 τ - 6 i τ / π`.
* `E4`, `E6` are Mathlib's `ModularForm.E₄`, `ModularForm.E₆` coerced to functions:
  `E4 τ = 1 + 240 ∑ σ₃(n) q^n` and `E6 τ = 1 - 504 ∑ σ₅(n) q^n`.

## Main definitions

* `IsQuasiModularFormDepth d k f`: `f = ∑_{j=0}^d E2^j · m_j` with `m_j` a holomorphic
  modular form of weight `k - 2j` for `SL(2, ℤ)` (depth at most `d`).
* `IsQuasiModularForm k f := IsQuasiModularFormDepth 1 k f` (weight `k`, depth at most 1).
* `IsModularFormOfWeight k f := IsQuasiModularFormDepth 0 k f` (depth zero, i.e. the
  `E2`-part vanishes).
* `quasiModularSpace d k`: the `ℂ`-span of the depth-`d` quasimodular forms of weight `k`.
* `IsQuasiModularSlash k f`: the intrinsic cocycle formulation, that the slash defect
  `f ∣[k] γ - f` is always divisible by the `E2`-defect `E2 ∣[2] γ - E2`.
-/

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace Work.Modular

/-- The weight-two Eisenstein series `E₂` as a function on `ℍ`, with the normalization
`E₂(τ) = 1 - 24 ∑_{n ≥ 1} σ₁(n) q^n`. -/
noncomputable abbrev E2 : ℍ → ℂ := EisensteinSeries.E2

/-- The weight-four Eisenstein series `E₄` as a function on `ℍ`, normalized so that
`E₄(τ) = 1 + 240 ∑_{n ≥ 1} σ₃(n) q^n`. -/
noncomputable abbrev E4 : ℍ → ℂ := ⇑ModularForm.E₄

/-- The weight-six Eisenstein series `E₆` as a function on `ℍ`, normalized so that
`E₆(τ) = 1 - 504 ∑_{n ≥ 1} σ₅(n) q^n`. -/
noncomputable abbrev E6 : ℍ → ℂ := ⇑ModularForm.E₆

/-- `IsQuasiModularFormDepth d k f` means that `f` is a quasimodular form of weight `k`
and depth at most `d` for `SL(2, ℤ)`: there are holomorphic modular forms `m_j` of weight
`k - 2j` (`0 ≤ j ≤ d`) with `f = ∑_{j=0}^d E₂^j · m_j`. -/
def IsQuasiModularFormDepth (d : ℕ) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  ∃ m : (j : Fin (d + 1)) → ModularForm 𝒮ℒ (k - 2 * (j : ℤ)),
    f = ∑ j : Fin (d + 1), E2 ^ (j : ℕ) * ⇑(m j)

/-- A quasimodular form of weight `k` and depth at most `1`. -/
def IsQuasiModularForm (k : ℤ) (f : ℍ → ℂ) : Prop := IsQuasiModularFormDepth 1 k f

/-- A holomorphic modular form of weight `k` for `SL(2, ℤ)`, viewed as a function:
the quasimodular forms of depth `0` (equivalently, those whose `E₂`-part vanishes). -/
def IsModularFormOfWeight (k : ℤ) (f : ℍ → ℂ) : Prop := IsQuasiModularFormDepth 0 k f

/-- The `ℂ`-span of the quasimodular forms of weight `k` and depth at most `d`, as a
submodule of the space of all functions `ℍ → ℂ`.  (A function lies in this span iff it
satisfies `IsQuasiModularFormDepth d k`; see `mem_quasiModularSpace`.) -/
noncomputable def quasiModularSpace (d : ℕ) (k : ℤ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ {f : ℍ → ℂ | IsQuasiModularFormDepth d k f}

/-- The intrinsic (cocycle) formulation of quasimodularity of weight `k` and depth at
most `1`: the slash defect `f ∣[k] γ - f` is a modular form of weight `k - 2` times the
`E₂`-defect `E₂ ∣[2] γ - E₂`. -/
def IsQuasiModularSlash (k : ℤ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), ∃ g : ModularForm 𝒮ℒ (k - 2),
    f ∣[k] γ - f = (E2 ∣[(2 : ℤ)] γ - E2) * ⇑g

/-- The `E₂`-part of a depth-one quasimodular form: `E2Part k f` is the (unique, when it
exists) modular form `g` of weight `k - 2` such that `f - E₂ · g` is modular. -/
noncomputable def E2Part (k : ℤ) (f : ℍ → ℂ) : Set (ModularForm 𝒮ℒ (k - 2)) :=
  {g | IsModularFormOfWeight k (f - E2 * ⇑g)}

end Work.Modular
