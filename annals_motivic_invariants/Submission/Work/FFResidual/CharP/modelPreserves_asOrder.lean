import Mathlib
import Submission.Work.FFResidual.CharP.Order
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier automorphism `s ↦ s + 1` preserves the local model `R[w]`

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field over its constants, with
uniformizer `π`, and let `AsTop P = 𝕜(s)`, `s ^ 5 - s = π⁻¹`, be the Artin–Schreier extension of
`Submission/Work/FFResidual/CharP/Basic`, with the Eisenstein element `w = s⁻¹` satisfying
`w ^ 5 + π w ^ 4 - π = 0` (`asRecip_pow`) and the local model
`AsOrder P = R[X] / (X ^ 5 + π X ^ 4 - π) = R[w]` of
`Submission/Work/FFResidual/CharP/Order`.

This file proves that the Artin–Schreier automorphism `σ = P.asEquiv`, `s ↦ s + 1`, **preserves the
local model** `R[w]`: an element of the top field is integral at the place of the Artin–Schreier
extension if and only if its image under `σ` is (`Work.ClassA.ModelPreserves`).  This is the
"`σ(R[w]) = R[w]`" input of the reduction-map invariance at the Artin–Schreier place.

The argument is explicit.  Since `σ` fixes the constants it fixes `R`, so `σ(R[w]) = R[σ w]`, and

  `σ w = w / (1 + w)`;

it therefore suffices to know that `1 + w` is a unit of the model.  This is elementary: the
telescoping identity `(1 + w) (1 - w + w² - w³ + w⁴) = 1 + w ^ 5` together with the defining
relation `w ^ 5 = π (1 - w ^ 4)` exhibits the inverse

  `(1 + w)⁻¹ = (1 - w + w² - w³ + w⁴) - π (1 - w) (1 + w²)`

(`asOrderUnit`, `oneAdd_mul_asOrderUnit`).  Hence `u := w / (1 + w)` lies in the model, and because
`f(Y) = Y ^ 5 + π Y ^ 4 - π` is invariant under `Y ↦ Y / (1 - Y)` up to the factor `(1 - Y) ^ 5` in
characteristic `5`, `u` satisfies `f(u) = 0` (`asOrderMobius_eval`).  The universal property of
`AdjoinRoot` then produces an endomorphism `asOrderHom` of the model with
`asOrderMap (asOrderHom r) = σ (asOrderMap r)` — the sharp form of `σ(R[w]) ⊆ R[w]` — and iterating
with `σ ^ 5 = 1` gives `ModelPreserves`.

## Main results

* `FunctionFieldPlace.asOrderUnit`, `oneAdd_mul_asOrderUnit` — `1 + w` is a unit of the model.
* `FunctionFieldPlace.asOrderHom`, `asOrderMap_asOrderHom` — the endomorphism `w ↦ w / (1 + w)` of
  the model and its compatibility with `σ`.
* `Work.FFResidual.CharP.modelPreserves_asOrder` — `σ` preserves the local model.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Polynomial

namespace Work.FFResidual

noncomputable section

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-! ## 1. The defining polynomial `X ^ 5 + π X ^ 4 - π` -/

/-- The Eisenstein element `w = s⁻¹` of the local model, i.e. the root of `X ^ 5 + π X ^ 4 - π`. -/
abbrev asOrderRoot (P : FunctionFieldPlace 𝔽 𝕜) : P.AsOrder :=
  AdjoinRoot.root (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X])

/-- The degree of the "lower terms" `π X ^ 4 - π` of the defining polynomial is `< 5`. -/
theorem asOrderPoly_lowdegree (P : FunctionFieldPlace 𝔽 𝕜) :
    (C P.π * X ^ 4 - C P.π : P.R[X]).degree < ((5 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]
  rw [ite_eq_right (by omega : m ≠ 4), ite_eq_right (by omega : m ≠ 0)]
  first | refl_ring1 | ring

/-- **The defining polynomial is monic.** -/
theorem asOrderPoly_monic (P : FunctionFieldPlace 𝔽 𝕜) :
    (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).Monic := by
  have hf : (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X])
      = (X ^ 5 : P.R[X]) + (C P.π * X ^ 4 - C P.π) := by ring
  rw [hf]
  exact Polynomial.Monic.add_of_left (Polynomial.monic_X_pow 5)
    (by rw [Polynomial.degree_X_pow]; exact asOrderPoly_lowdegree P)

/-- **The defining polynomial has positive degree.** -/
theorem asOrderPoly_degree_pos (P : FunctionFieldPlace 𝔽 𝕜) :
    0 < (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]).degree := by
  have hf : (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X])
      = (X ^ 5 : P.R[X]) + (C P.π * X ^ 4 - C P.π) := by ring
  rw [hf, Polynomial.degree_add_eq_left_of_degree_lt
    (by rw [Polynomial.degree_X_pow]; exact asOrderPoly_lowdegree P), Polynomial.degree_X_pow]
  norm_num

/-- **The local model has characteristic five** (it is a finite algebra over the valuation ring,
which embeds into `𝕜` of characteristic `5`). -/
theorem charP_asOrder (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : CharP P.AsOrder 5 := by
  haveI : CharP P.R 5 := (algebraMap P.R 𝕜).charP (IsFractionRing.injective P.R 𝕜) 5
  have hinj : Function.Injective (algebraMap P.R P.AsOrder) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.of.injective_of_monic_of_degree_pos (asOrderPoly_monic P)
      (asOrderPoly_degree_pos P)
  exact charP_of_injective_algebraMap hinj 5

/-- **The Eisenstein relation of `w = s⁻¹`** in the local model: `w ^ 5 + π w ^ 4 - π = 0`. -/
theorem asOrderRoot_relation (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asOrderRoot ^ 5 + algebraMap P.R P.AsOrder P.π * P.asOrderRoot ^ 4
      - algebraMap P.R P.AsOrder P.π = 0 := by
  have h := AdjoinRoot.eval₂_root (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X])
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_mul] at h
  exact h

/-! ## 2. `1 + w` is a unit of the model -/

/-- **The inverse of `1 + w` in the model**, from the telescoping identity
`(1 + w) (1 - w + w² - w³ + w⁴) = 1 + w ^ 5` and the relation `w ^ 5 = π (1 - w ^ 4)`. -/
def asOrderUnit (P : FunctionFieldPlace 𝔽 𝕜) : P.AsOrder :=
  (1 - P.asOrderRoot + P.asOrderRoot ^ 2 - P.asOrderRoot ^ 3 + P.asOrderRoot ^ 4)
    - algebraMap P.R P.AsOrder P.π * ((1 - P.asOrderRoot) * (1 + P.asOrderRoot ^ 2))

/-- **`1 + w` is a unit of the local model**: `asOrderUnit` is its explicit inverse. -/
theorem oneAdd_mul_asOrderUnit (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    (1 + P.asOrderRoot) * P.asOrderUnit = 1 := by
  have h := P.asOrderRoot_relation
  unfold asOrderUnit
  linear_combination (norm := first | refl_ring1 | ring1) h

/-- The element `u := w / (1 + w)` of the local model, the image of `w` under `s ↦ s + 1`. -/
def asOrderMobius (P : FunctionFieldPlace 𝔽 𝕜) : P.AsOrder :=
  P.asOrderRoot * P.asOrderUnit

/-- The defining property of `u = w / (1 + w)`: `(1 + w) u = w`. -/
theorem oneAdd_mul_asOrderMobius (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    (1 + P.asOrderRoot) * P.asOrderMobius = P.asOrderRoot := by
  unfold asOrderMobius
  rw [show (1 + P.asOrderRoot) * (P.asOrderRoot * P.asOrderUnit)
      = P.asOrderRoot * ((1 + P.asOrderRoot) * P.asOrderUnit) by ring,
    oneAdd_mul_asOrderUnit, mul_one]

/-- **`u = w / (1 + w)` satisfies the defining Eisenstein relation.**  In characteristic `5` the
polynomial `f(Y) = Y ^ 5 + π Y ^ 4 - π` is invariant under `Y ↦ Y / (1 - Y)` up to the factor
`(1 - Y) ^ 5`, i.e. `(1 + w) ^ 5 f(w / (1 + w)) = f(w) = 0`. -/
theorem asOrderMobius_eval (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    Polynomial.eval₂ (algebraMap P.R P.AsOrder) P.asOrderMobius
      (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hch : CharP P.AsOrder 5 := charP_asOrder P
  have h5 : (1 + P.asOrderRoot) ^ 5 = 1 + P.asOrderRoot ^ 5 := by
    rw [add_pow_char]; simp
  have hu := oneAdd_mul_asOrderMobius P
  have h1 : (1 + P.asOrderRoot) ^ 5 * P.asOrderMobius ^ 5 = P.asOrderRoot ^ 5 := by
    rw [← mul_pow, hu]
  have h2 : (1 + P.asOrderRoot) ^ 5 * P.asOrderMobius ^ 4
      = (1 + P.asOrderRoot) * P.asOrderRoot ^ 4 := by
    rw [show (1 + P.asOrderRoot) ^ 5 * P.asOrderMobius ^ 4
        = (1 + P.asOrderRoot) * ((1 + P.asOrderRoot) ^ 4 * P.asOrderMobius ^ 4) by ring,
      ← mul_pow, hu]
  have heval : Polynomial.eval₂ (algebraMap P.R P.AsOrder) P.asOrderMobius
      (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X])
      = P.asOrderMobius ^ 5 + algebraMap P.R P.AsOrder P.π * P.asOrderMobius ^ 4
        - algebraMap P.R P.AsOrder P.π := by
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Polynomial.eval₂_mul]
  have hprod : (1 + P.asOrderRoot) ^ 5 * Polynomial.eval₂ (algebraMap P.R P.AsOrder)
      P.asOrderMobius (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]) = 0 := by
    rw [heval, mul_sub, mul_add, h1,
      show (1 + P.asOrderRoot) ^ 5 * (algebraMap P.R P.AsOrder P.π * P.asOrderMobius ^ 4)
        = algebraMap P.R P.AsOrder P.π
          * ((1 + P.asOrderRoot) ^ 5 * P.asOrderMobius ^ 4) by ring,
      h2, h5]
    have hrel := P.asOrderRoot_relation
    linear_combination (norm := first | refl_ring1 | ring1) hrel
  exact (IsUnit.mul_right_eq_zero
    ((IsUnit.of_mul_eq_one P.asOrderUnit (oneAdd_mul_asOrderUnit P)).pow 5)).mp hprod

/-! ## 3. The endomorphism `w ↦ w / (1 + w)` of the local model -/

/-- **The endomorphism `w ↦ w / (1 + w)` of the local model**, obtained from the universal
property of `AdjoinRoot` applied to the root `u = w / (1 + w)` of the defining polynomial. -/
def asOrderHom (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : P.AsOrder →+* P.AsOrder :=
  AdjoinRoot.lift (algebraMap P.R P.AsOrder) P.asOrderMobius P.asOrderMobius_eval

theorem asOrderHom_root (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asOrderHom P.asOrderRoot = P.asOrderMobius :=
  AdjoinRoot.lift_root (P.asOrderMobius_eval)

theorem asOrderHom_of (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] (a : P.R) :
    P.asOrderHom (AdjoinRoot.of (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]) a)
      = AdjoinRoot.of (X ^ 5 + C P.π * X ^ 4 - C P.π : P.R[X]) a :=
  AdjoinRoot.lift_of (P.asOrderMobius_eval)

/-! ## 4. The compatibility `asOrderMap (asOrderHom r) = σ (asOrderMap r)` -/

theorem asOrderMap_oneAdd (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asOrderMap (1 + P.asOrderRoot) = 1 + P.asRecip := by
  rw [map_add, map_one, P.asOrderMap_root]

theorem asOrderMap_asOrderUnit (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asOrderMap P.asOrderUnit = (1 + P.asRecip)⁻¹ := by
  have h := congrArg P.asOrderMap (oneAdd_mul_asOrderUnit P)
  rw [map_mul, map_one, asOrderMap_oneAdd] at h
  exact eq_inv_of_mul_eq_one_right h

/-- `σ` sends the uniformizer `w = s⁻¹` to `(s + 1)⁻¹ = (w⁻¹ + 1)⁻¹`. -/
theorem asEquiv_asRecip (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asEquiv P.asRecip = (P.asRoot + 1)⁻¹ := by
  rw [show P.asRecip = P.asRoot⁻¹ from rfl, map_inv₀, P.asEquiv_root]

/-- `s = 1 / w` is not `-1`, since `s ^ 5 - s = π⁻¹ ≠ 0`. -/
theorem asRoot_add_one_ne_zero (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asRoot + 1 ≠ 0 := by
  intro h
  have h0 : P.asRoot = -1 := by linear_combination h
  have hz : algebraMap 𝕜 P.AsTop P.asElement = 0 := by
    have hr := P.asRoot_equation
    rw [h0] at hr
    rw [← hr]; ring
  exact P.asElement_ne_zero ((algebraMap 𝕜 P.AsTop).injective (by simpa using hz))

/-- **`w / (1 + w) = σ w`**: the image of the uniformizer of the model under the Artin–Schreier
automorphism, computed in the top field. -/
theorem asOrderMap_asOrderMobius (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asOrderMap P.asOrderMobius = P.asEquiv P.asRecip := by
  have hroot : P.asRoot ≠ 0 := P.asRoot_ne_zero
  have h1 : P.asRoot + 1 ≠ 0 := P.asRoot_add_one_ne_zero
  have hpow : P.asRecip * (P.asRoot + 1) = 1 + P.asRecip := by
    rw [show P.asRecip = P.asRoot⁻¹ from rfl]
    field_simp
  have hne : (1 : P.AsTop) + P.asRecip ≠ 0 := by
    rw [← hpow]
    exact mul_ne_zero
      (by rw [show P.asRecip = P.asRoot⁻¹ from rfl]; exact inv_ne_zero hroot) h1
  have hkey : P.asRecip * (1 + P.asRecip)⁻¹ * (P.asRoot + 1) = 1 := by
    rw [show P.asRecip * (1 + P.asRecip)⁻¹ * (P.asRoot + 1)
        = (P.asRecip * (P.asRoot + 1)) * (1 + P.asRecip)⁻¹ by ring, hpow]
    exact mul_inv_cancel₀ hne
  have hcancel : P.asRecip * (1 + P.asRecip)⁻¹ = (P.asRoot + 1)⁻¹ :=
    eq_inv_of_mul_eq_one_left hkey
  rw [show P.asOrderMobius = P.asOrderRoot * P.asOrderUnit from rfl, map_mul, P.asOrderMap_root,
    asOrderMap_asOrderUnit, asEquiv_asRecip]
  exact hcancel

/-- **The sharp form of `σ(R[w]) ⊆ R[w]`**: the element `r` of the model and its image under the
Artin–Schreier automorphism are the images under `asOrderMap` of `r` and of `asOrderHom r`. -/
theorem asOrderMap_asOrderHom (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] (r : P.AsOrder) :
    P.asOrderMap (P.asOrderHom r) = P.asEquiv (P.asOrderMap r) := by
  have hcomp : P.asOrderMap.comp P.asOrderHom
      = ((P.asEquiv : P.AsTop →+* P.AsTop)).comp P.asOrderMap := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext a
      simp only [RingHom.comp_apply]
      rw [P.asOrderHom_of, ← AdjoinRoot.algebraMap_eq, P.asOrderMap_algebraMap]
      rw [P.algebraMap_R_AsTop]
      exact (AlgEquiv.commutes P.asEquiv (algebraMap P.R 𝕜 a)).symm
    · simp only [RingHom.comp_apply]
      rw [P.asOrderHom_root, P.asOrderMap_root, asOrderMap_asOrderMobius]
      rfl
  simpa using RingHom.congr_fun hcomp r

end FunctionFieldPlace

namespace CharP

/-- **The Artin–Schreier automorphism `s ↦ s + 1` preserves the local model** `R[w] ⊆ AsTop`,
`w = s⁻¹`: an element of the top field is integral at the Artin–Schreier place if and only if its
image under the automorphism is (the automorphism sends `w` to `w / (1 + w)`, and `1 + w` is a unit
of the model). -/
theorem modelPreserves_asOrder {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]
    (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    Work.ClassA.ModelPreserves (Work.FFResidual.FunctionFieldPlace.AsOrder P) ⇑(P.asEquiv) := by
  -- `σ` maps the image of `asOrderMap` into itself, via the endomorphism `w ↦ w / (1 + w)`.
  have hstep : ∀ r : P.AsOrder,
      ∃ r' : P.AsOrder, P.asOrderMap r' = P.asEquiv (P.asOrderMap r) :=
    fun r => ⟨P.asOrderHom r, P.asOrderMap_asOrderHom r⟩
  -- Iterating, every power of `σ` maps the image of `asOrderMap` into itself.
  have hiter' : ∀ (n : ℕ) (r : P.AsOrder), ∃ r' : P.AsOrder,
      P.asOrderMap r' = ((P.asEquiv) ^ n) (P.asOrderMap r) := by
    intro n
    induction n with
    | zero => intro r; exact ⟨r, by rw [pow_zero, AlgEquiv.one_apply]⟩
    | succ n ih =>
        intro r
        obtain ⟨r₁, h₁⟩ := ih r
        obtain ⟨r₂, h₂⟩ := hstep r₁
        refine ⟨r₂, ?_⟩
        rw [h₂, h₁]
        exact congrArg (fun e : P.AsTop ≃ₐ[𝕜] P.AsTop => e (P.asOrderMap r))
          (pow_succ' (P.asEquiv) n).symm
  intro x
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨P.asOrderHom r, P.asOrderMap_asOrderHom r⟩
  · rintro ⟨r, hr⟩
    -- `σ x ∈ R[w]`; then `x = σ ^ 5 x = σ ^ 4 (σ x) ∈ R[w]` as well.
    obtain ⟨s, hs⟩ := hiter' 4 r
    refine ⟨s, ?_⟩
    change P.asOrderMap s = x
    have hrs : P.asOrderMap r = P.asEquiv x := hr
    rw [hs, hrs]
    have h5 : (P.asEquiv) ^ 4 * (P.asEquiv) = 1 := by
      rw [← pow_succ, P.asEquiv_pow_five]
    rw [← AlgEquiv.mul_apply, h5, AlgEquiv.one_apply]

end CharP

end

end Work.FFResidual
