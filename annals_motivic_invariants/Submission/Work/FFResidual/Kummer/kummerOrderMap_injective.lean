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
# Injectivity of the map from the Eisenstein order into the Kummer extension

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field `𝕜` over its field of constants
`𝔽`, with uniformizer `π` (`Submission/Work/FFResidual/Defs.lean`), and let

  `KummerOrder P = R[X] / (X ^ 5 - π)`,  `Top P = 𝕜(s) = 𝕜[X] / (X ^ 5 - π)`

be the Eisenstein order of the place and the Kummer extension `s ^ 5 = π` above it
(`Submission/Work/FFResidual/Kummer/Order.lean`, `.../Basic.lean`).

This file proves that the `R`-algebra map `kummerOrderMap : R[X]/(X ^ 5 - π) → 𝕜(s)` -- the map
sending the root of `X ^ 5 - π` to the Kummer root `s` -- is **injective**.

## The argument

The map in question is an instance of a general phenomenon: for a ring homomorphism `A : R →+* S`
that is injective and a monic polynomial `f : R[X]` with `f ≠ 1`, the canonical map

  `AdjoinRoot f = R[X]/(f)  ⟶  S[X]/(f.map A) = AdjoinRoot (f.map A)`

is injective. Indeed, if the class of `g.map A` vanishes, then `f.map A ∣ g.map A`; reducing `g`
modulo `f` (the remainder `g %ₘ f` has smaller natural degree than `f`) and using that the
quotient map kills `f.map A` shows `f.map A ∣ (g %ₘ f).map A`; since `f.map A` is monic of the same
degree as `f` while `(g %ₘ f).map A` has degree `< deg f` (the injectivity of `A` is exactly what
makes the degree of the image equal to the degree of the original), this forces
`(g %ₘ f).map A = 0`, hence `g %ₘ f = 0` by injectivity of `A` applied to polynomials, hence
`f ∣ g` and the class of `g` vanishes.

Here `R` is the valuation ring of the place, `S = 𝕜` its fraction field (so `A = algebraMap R 𝕜` is
injective by `IsFractionRing.injective`), and `f = X ^ 5 - π` is monic.

## Main results

* `Work.FFResidual.Kummer.kummerOrderMap_eq_adjoinRoot_map` -- `kummerOrderMap` is the canonical
  map of `AdjoinRoot`s.
* `Work.FFResidual.Kummer.kummerOrderMap_injective` -- the statement of this file.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Polynomial

namespace Work.FFResidual.Kummer

open Work.FFResidual (FunctionFieldPlace)

/-! ## 1. Adjoining roots: the canonical map between `AdjoinRoot`s -/

section AdjoinRootMap

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **The canonical map between `AdjoinRoot`s computed on representatives**: the map
`AdjoinRoot p → AdjoinRoot q` induced by `A : R →+* S` (where `q ∣ p.map A`) sends the class of
`g` to the class of `g.map A`. -/
lemma adjoinRoot_map_mk (A : R →+* S) (p : R[X]) (q : S[X]) (h : q ∣ p.map A) (g : R[X]) :
    AdjoinRoot.map A p q h (AdjoinRoot.mk p g) = AdjoinRoot.mk q (g.map A) := by
  rw [AdjoinRoot.map, AdjoinRoot.lift_mk]
  rw [← Polynomial.eval₂_map A (AdjoinRoot.of q) (AdjoinRoot.root q)]
  exact AdjoinRoot.aeval_eq _

/-- **Injectivity of `AdjoinRoot.map` for monic polynomials and injective coefficient maps.**
If `A : R →+* S` is injective and `f : R[X]` is monic with `f ≠ 1`, then the canonical map
`R[X]/(f) → S[X]/(f.map A)` is injective. -/
theorem adjoinRoot_map_injective_of_monic (A : R →+* S) (hA : Function.Injective A) (f : R[X])
    (hf : f.Monic) (hf1 : f ≠ 1) :
    Function.Injective (AdjoinRoot.map A f (f.map A) dvd_rfl) := by
  have key : ∀ z : AdjoinRoot f, AdjoinRoot.map A f (f.map A) dvd_rfl z = 0 → z = 0 := by
    intro z hz
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := f) z
    rw [adjoinRoot_map_mk] at hz
    rw [AdjoinRoot.mk_eq_zero] at hz
    -- `f.map A` divides the image of the remainder of `g` modulo `f`
    have hdiv : f.map A ∣ (g %ₘ f).map A := by
      have h1 : (g.map A : S[X]) = ((g %ₘ f) + f * (g /ₘ f)).map A := by
        rw [modByMonic_add_div]
      rw [Polynomial.map_add, Polynomial.map_mul] at h1
      rw [h1] at hz
      exact (dvd_add_left (a := f.map A) (b := (g %ₘ f).map A)
        (c := f.map A * (g /ₘ f).map A) (dvd_mul_right _ _)).mp hz
    rw [AdjoinRoot.mk_eq_zero]
    by_cases hr : g %ₘ f = 0
    · -- the remainder vanishes, so `g = f * (g /ₘ f)`
      refine ⟨g /ₘ f, ?_⟩
      have h2 := modByMonic_add_div g f
      rw [hr, zero_add] at h2
      exact h2.symm
    · -- otherwise the remainder has smaller degree than `f`, hence than `f.map A`
      exfalso
      have hr' : (g %ₘ f).map A ≠ 0 := fun h0 =>
        hr (Polynomial.map_injective A hA (by simpa using h0))
      have hlt : ((g %ₘ f).map A).natDegree < (f.map A).natDegree := by
        rw [Polynomial.natDegree_map_eq_of_injective hA,
          Polynomial.natDegree_map_eq_of_injective hA]
        exact Polynomial.natDegree_modByMonic_lt g hf hf1
      exact (hf.map A).not_dvd_of_natDegree_lt hr' hlt hdiv
  intro x y hxy
  have hsub : x - y = 0 := key (x - y) (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp hsub

/-- The same as `adjoinRoot_map_injective_of_monic`, with the target polynomial `q` given together
with the identification `q = f.map A`: this is the form in which the result is applied to the
Eisenstein order, whose top ring is `AdjoinRoot P.kummerPoly` rather than
`AdjoinRoot ((X ^ 5 - C π).map (algebraMap P.R 𝕜))`. -/
theorem adjoinRoot_map_injective_of_monic' (A : R →+* S) (hA : Function.Injective A) {f : R[X]}
    (hf : f.Monic) (hf1 : f ≠ 1) {q : S[X]} (hq : q = f.map A) :
    Function.Injective (AdjoinRoot.map A f q (by rw [hq])) := by
  subst hq
  exact adjoinRoot_map_injective_of_monic A hA f hf hf1

end AdjoinRootMap

/-! ## 2. The map of the Eisenstein order into the Kummer extension -/

section KummerOrder

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- The defining polynomial `X ^ 5 - π` of the Eisenstein order, as a polynomial over `R`, maps to
the defining polynomial `X ^ 5 - π` of the Kummer extension, viewed over `𝕜`. -/
theorem kummerPoly_eq_map (P : FunctionFieldPlace 𝔽 𝕜) :
    P.kummerPoly = (X ^ 5 - C P.π : P.R[X]).map (algebraMap P.R 𝕜) := by
  simp [FunctionFieldPlace.kummerPoly, FunctionFieldPlace.kummerElement]

/-- **The map from the Eisenstein order into the top field is the canonical map of
`AdjoinRoot`s**: it is the map `R[X]/(X ^ 5 - π) → 𝕜[X]/(X ^ 5 - π)` induced by the structure map
`R → 𝕜`. -/
theorem kummerOrderMap_eq_adjoinRoot_map (P : FunctionFieldPlace 𝔽 𝕜) :
    P.kummerOrderMap = AdjoinRoot.map (algebraMap P.R 𝕜) (X ^ 5 - C P.π : P.R[X]) P.kummerPoly
      (by rw [kummerPoly_eq_map P]) := by
  apply AdjoinRoot.ringHom_ext
  · ext r
    simp only [RingHom.comp_apply, AdjoinRoot.map_of]
    rw [show (AdjoinRoot.of (X ^ 5 - C P.π)) r = algebraMap P.R P.KummerOrder r from rfl]
    rw [FunctionFieldPlace.kummerOrderMap_algebraMap]
    exact FunctionFieldPlace.algebraMap_R_Top P r
  · simp [AdjoinRoot.map_root, FunctionFieldPlace.kummerOrderMap_root]

/-- The `R`-algebra map `R[X]/(X ^ 5 - π) → 𝕜(s)` of the Eisenstein order into the Kummer
extension, sending the root of `X ^ 5 - π` to the Kummer root `s`, is injective. -/
theorem kummerOrderMap_injective {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]
    (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜) :
    Function.Injective P.kummerOrderMap := by
  have hf : (X ^ 5 - C P.π : P.R[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hf1 : (X ^ 5 - C P.π : P.R[X]) ≠ 1 := (hf.natDegree_pos).mp (by
    rw [natDegree_X_pow_sub_C]
    norm_num)
  rw [kummerOrderMap_eq_adjoinRoot_map]
  exact adjoinRoot_map_injective_of_monic' (algebraMap P.R 𝕜) (IsFractionRing.injective P.R 𝕜)
    hf hf1 (kummerPoly_eq_map P)

end KummerOrder

end Work.FFResidual.Kummer
