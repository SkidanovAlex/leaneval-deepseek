/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Mathlib
import Submission.Work.FFResidual.Kummer.Order

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Kummer automorphism preserves the Eisenstein order `R[s]`

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field over its constants, with
uniformizer `π`, and let `Top P = 𝕜(s)`, `s ^ 5 = π` be the Kummer extension of
`Submission/Work/FFResidual/Kummer/Basic`, with the Eisenstein order
`KummerOrder P = R[X] / (X ^ 5 - π) ⊆ 𝕜(s)` of `Submission/Work/FFResidual/Kummer/Order`.

This file proves that the Kummer automorphism `σ = P.kummerEquiv ζ hζ`, `s ↦ ζ s`, **preserves the
local model** `R[s]`: an element of the top field is integral at the place of the Kummer extension
if and only if its image under `σ` is (`Work.ClassA.ModelPreserves`). This is the
"`σ(R[s]) = R[s]`" input of the reduction-map invariance at the Kummer place.

The argument is completely explicit. Since `ζ` is a constant, the fifth root of unity of `𝔽` maps
into the valuation ring `R` (`zetaR`), and the `R`-algebra endomorphism `kummerOrderHom` of the
Eisenstein order sending the root to `ζ s` satisfies
`kummerOrderMap (kummerOrderHom r) = σ (kummerOrderMap r)` (`kummerOrderMap_kummerOrderHom`).
Hence `σ` maps the image of `kummerOrderMap` into itself; iterating this and using `σ ^ 5 = 1`, the
image is `σ`-invariant, which is exactly `ModelPreserves`.

## Main results

* `FunctionFieldPlace.kummerOrderHom` — the `R`-algebra endomorphism `s ↦ ζ s` of `R[s]`.
* `FunctionFieldPlace.kummerOrderMap_kummerOrderHom` — its compatibility with `σ` and
  `kummerOrderMap`.
* `Work.FFResidual.Kummer.modelPreserves_kummerOrder` — `σ` preserves the local model.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Polynomial

namespace Work.FFResidual

noncomputable section

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- **The fifth root of unity viewed in the valuation ring.**  A primitive fifth root of unity is a
constant of the function field, hence integral at the place. -/
abbrev zetaR (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) : P.R := algebraMap 𝔽 P.R ζ

theorem zetaR_pow_five (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) :
    (zetaR P ζ) ^ 5 = 1 := by
  rw [zetaR, ← map_pow, hζ.pow_eq_one, map_one]

theorem algebraMap_zetaR (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) :
    algebraMap P.R 𝕜 (zetaR P ζ) = zetaK (𝕜 := 𝕜) ζ :=
  (IsScalarTower.algebraMap_apply 𝔽 P.R 𝕜 ζ).symm

theorem algebraMap_R_Top_zetaR (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽) :
    algebraMap P.R P.Top (zetaR P ζ) = algebraMap 𝔽 P.Top ζ := by
  rw [algebraMap_R_Top, algebraMap_zetaR, ← algebraMap_𝔽_Top]

/-! ## 1. The Kummer automorphism fixes the place ring -/

/-- **The Kummer automorphism is `R`-linear**: it fixes the image of the valuation ring, since it
fixes the constants. -/
theorem kummerEquiv_algebraMap_R (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (r : P.R) :
    P.kummerEquiv ζ hζ (algebraMap P.R P.Top r) = algebraMap P.R P.Top r := by
  rw [algebraMap_R_Top, kummerEquiv_algebraMap, ← algebraMap_R_Top]

/-- `kummerEquiv_algebraMap_R`, with the ring-homomorphism coercion of the automorphism. -/
theorem kummerEquiv_algebraMap_R_ringHom (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (r : P.R) :
    (↑(P.kummerEquiv ζ hζ) : P.Top →+* P.Top) (algebraMap P.R P.Top r)
      = algebraMap P.R P.Top r :=
  P.kummerEquiv_algebraMap_R ζ hζ r

/-- `kummerEquiv_root`, with the ring-homomorphism coercion of the automorphism. -/
theorem kummerEquiv_ringHom_root (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    (↑(P.kummerEquiv ζ hζ) : P.Top →+* P.Top) P.kummerRoot
      = zetaK (𝕜 := 𝕜) ζ • P.kummerRoot :=
  P.kummerEquiv_root ζ hζ

/-! ## 2. The endomorphism `s ↦ ζ s` of the Eisenstein order and its compatibility with `σ` -/

/-- The defining relation of the Eisenstein order: `(ζ s) ^ 5 = π`. -/
theorem kummerOrder_root_pow_five (P : FunctionFieldPlace 𝔽 𝕜) :
    (AdjoinRoot.root (X ^ 5 - C P.π : P.R[X])) ^ 5
      = algebraMap P.R P.KummerOrder P.π := by
  have h := AdjoinRoot.eval₂_root (X ^ 5 - C P.π : P.R[X])
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]

/-- The same relation in `eval₂` form, as needed by `AdjoinRoot.lift`. -/
theorem kummerOrder_smul_root_eval₂ (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    eval₂ (algebraMap P.R P.KummerOrder)
      (zetaR P ζ • AdjoinRoot.root (X ^ 5 - C P.π : P.R[X])) (X ^ 5 - C P.π : P.R[X]) = 0 := by
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
  rw [Algebra.smul_def, mul_pow, ← map_pow, zetaR_pow_five P ζ hζ, map_one, one_mul,
    kummerOrder_root_pow_five P]

/-- **The endomorphism `s ↦ ζ s` of the Eisenstein order** `R[s]`, as an `R`-algebra endomorphism
(the root is sent to `ζ s`, i.e. the image of the fifth root of unity in `R`). -/
noncomputable def kummerOrderHom (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) : P.KummerOrder →+* P.KummerOrder :=
  AdjoinRoot.lift (algebraMap P.R P.KummerOrder)
    (zetaR P ζ • AdjoinRoot.root (X ^ 5 - C P.π : P.R[X]))
    (P.kummerOrder_smul_root_eval₂ ζ hζ)

theorem kummerOrderHom_root (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    P.kummerOrderHom ζ hζ (AdjoinRoot.root (X ^ 5 - C P.π : P.R[X]))
      = zetaR P ζ • AdjoinRoot.root (X ^ 5 - C P.π : P.R[X]) :=
  AdjoinRoot.lift_root _

theorem kummerOrderHom_of (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (a : P.R) :
    P.kummerOrderHom ζ hζ (AdjoinRoot.of (X ^ 5 - C P.π : P.R[X]) a)
      = AdjoinRoot.of (X ^ 5 - C P.π : P.R[X]) a :=
  AdjoinRoot.lift_of (P.kummerOrder_smul_root_eval₂ ζ hζ)

/-- **The endomorphism `s ↦ ζ s` of the Eisenstein order computes the Kummer automorphism**: an
element `r ∈ R[s]` and its image under the Kummer automorphism are the images under
`kummerOrderMap` of `r` and of `kummerOrderHom r`.  This is the statement that `σ(R[s]) ⊆ R[s]`,
in the sharp form needed to deduce `ModelPreserves`. -/
theorem kummerOrderMap_kummerOrderHom (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (r : P.KummerOrder) :
    P.kummerOrderMap (P.kummerOrderHom ζ hζ r) = P.kummerEquiv ζ hζ (P.kummerOrderMap r) := by
  have hcomp : (P.kummerOrderMap.comp (P.kummerOrderHom ζ hζ))
      = ((P.kummerEquiv ζ hζ : P.Top →+* P.Top)).comp P.kummerOrderMap := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext a
      simp only [RingHom.comp_apply]
      rw [P.kummerOrderHom_of ζ hζ a, ← AdjoinRoot.algebraMap_eq,
        kummerOrderMap_algebraMap, P.kummerEquiv_algebraMap_R_ringHom ζ hζ]
    · simp only [RingHom.comp_apply]
      rw [P.kummerOrderHom_root ζ hζ, Algebra.smul_def, map_mul, kummerOrderMap_algebraMap,
        kummerOrderMap_root, P.kummerEquiv_ringHom_root ζ hζ, Algebra.smul_def,
        algebraMap_R_Top_zetaR, ← algebraMap_𝔽_Top]
  simpa using RingHom.congr_fun hcomp r

end FunctionFieldPlace

namespace Kummer

open FunctionFieldPlace

/-- **The Kummer automorphism `s ↦ ζ s` preserves the local model** `R[s] ⊆ 𝕜(s)`: an element of
the top field is integral at the place if and only if its image under the Kummer automorphism is. -/
theorem modelPreserves_kummerOrder {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜]
    [Algebra 𝔽 𝕜] (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    Work.ClassA.ModelPreserves (Work.FFResidual.FunctionFieldPlace.KummerOrder P)
      ⇑(P.kummerEquiv ζ hζ) := by
  -- `σ = kummerEquiv ζ hζ` maps the image of `kummerOrderMap` into itself, via `kummerOrderHom`.
  have hstep : ∀ r : P.KummerOrder,
      ∃ r' : P.KummerOrder, P.kummerOrderMap r' = P.kummerEquiv ζ hζ (P.kummerOrderMap r) :=
    fun r => ⟨P.kummerOrderHom ζ hζ r, P.kummerOrderMap_kummerOrderHom ζ hζ r⟩
  -- Iterating, every power of `σ` maps the image of `kummerOrderMap` into itself.
  have hiter : ∀ (n : ℕ) (r : P.KummerOrder),
      ∃ r' : P.KummerOrder, P.kummerOrderMap r' =
        ((P.kummerEquiv ζ hζ) ^ n) (P.kummerOrderMap r) := by
    intro n
    induction n with
    | zero => intro r; exact ⟨r, by rw [pow_zero, AlgEquiv.one_apply]⟩
    | succ n ih =>
        intro r
        obtain ⟨r₁, h₁⟩ := ih r
        obtain ⟨r₂, h₂⟩ := hstep r₁
        refine ⟨r₂, ?_⟩
        rw [h₂, h₁]
        exact congrArg (fun e : P.Top ≃ₐ[𝕜] P.Top => e (P.kummerOrderMap r))
          (pow_succ' (P.kummerEquiv ζ hζ) n).symm
  intro x
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨P.kummerOrderHom ζ hζ r, P.kummerOrderMap_kummerOrderHom ζ hζ r⟩
  · rintro ⟨r, hr⟩
    -- `σ x ∈ R[s]`; then `x = σ ^ 5 x = σ ^ 4 (σ x) ∈ R[s]` as well.
    obtain ⟨s, hs⟩ := hiter 4 r
    refine ⟨s, ?_⟩
    change P.kummerOrderMap s = x
    have hrs : P.kummerOrderMap r = (P.kummerEquiv ζ hζ) x := hr
    rw [hs, hrs]
    have h5 : (P.kummerEquiv ζ hζ) ^ 4 * (P.kummerEquiv ζ hζ) = 1 := by
      rw [← pow_succ, P.kummerEquiv_pow_five ζ hζ]
    rw [← AlgEquiv.mul_apply, h5, AlgEquiv.one_apply]

end Kummer

end

end Work.FFResidual
