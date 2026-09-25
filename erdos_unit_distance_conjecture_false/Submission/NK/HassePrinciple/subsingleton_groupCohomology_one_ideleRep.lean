/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `H¹(Gal(L/K), 𝕀_L) = 0`

For a finite Galois extension `L / K` of number fields, the first group cohomology of the idèle
group `𝕀_L` with its natural `Gal(L/K)`-action vanishes.  This is Shapiro's lemma for the idèles
together with Hilbert 90 at the places: `𝕀_L` is, orbit by orbit, an induced module from the
stabiliser `H_w` of a place to `Gal(L/K)`, and `H¹(H_w, L_wˣ) = 0` by Noether's generalisation of
Hilbert 90 for the action of `H_w` on the local field `L_w` by field automorphisms.

The cocycle-level input is `NK.HassePrinciple.exists_idele_coboundary_of_isMulCocycle`: every
multiplicative `1`-cocycle `c : Gal(L/K) → 𝕀_L` is a coboundary, `c g = g • y / y`.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdelesLevel
import Submission.NK.HassePrinciple.exists_idele_coboundary_of_isMulCocycle

open CategoryTheory Representation
open NK.GlobalCFT

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.HassePrinciple

theorem subsingleton_groupCohomology_one_ideleRep {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Subsingleton (groupCohomology (NK.HassePrinciple.ideleRep K L) 1) := by
  -- the `Gal(L/K)`-action on `ideleRep` written multiplicatively on `𝕀_L`
  have hunits : ∀ (g : L ≃ₐ[K] L) (a : Additive (Idele L)),
      (ideleRep K L).ρ g a = Additive.ofMul (α := Idele L) (g • Additive.toMul (α := Idele L) a) :=
    fun _ _ => rfl
  -- it suffices to show that every class in `H¹` vanishes
  have key : ∀ a : groupCohomology (ideleRep K L) 1, a = 0 := by
    intro a
    refine groupCohomology.H1_induction_on a (fun x => ?_)
    -- a cocycle is a coboundary
    refine (groupCohomology.H1π_eq_zero_iff x).2 ?_
    -- rewrite the cocycle `x : Gal(L/K) → Additive 𝕀[L]` into the multiplicative world
    let y : (L ≃ₐ[K] L) → Additive (Idele L) := fun g => x.1 g
    have hcoc : groupCohomology.IsMulCocycle₁ (M := Idele L)
        (fun g => Additive.toMul (α := Idele L) (y g)) := by
      intro g h
      have h1 : y (g * h) =
          Additive.ofMul (α := Idele L) (g • Additive.toMul (α := Idele L) (y h)) + y g := by
        have h0 := (groupCohomology.mem_cocycles₁_iff (A := ideleRep K L) (x.1)).1 x.2 g h
        rw [hunits g (y h)] at h0
        exact h0
      calc Additive.toMul (α := Idele L) (y (g * h))
          = Additive.toMul (α := Idele L)
              (Additive.ofMul (α := Idele L) (g • Additive.toMul (α := Idele L) (y h)) + y g) := by
            rw [h1]
        _ = Additive.toMul (α := Idele L)
              (Additive.ofMul (α := Idele L) (g • Additive.toMul (α := Idele L) (y h)))
              * Additive.toMul (α := Idele L) (y g) := toMul_add (α := Idele L) _ _
        _ = (g • Additive.toMul (α := Idele L) (y h)) * Additive.toMul (α := Idele L) (y g) := by
            rw [toMul_ofMul]
    -- Hilbert 90 for the idèles: the cocycle is a coboundary
    obtain ⟨β, hβ⟩ := exists_idele_coboundary_of_isMulCocycle (K := K) (L := L)
      (c := fun g => Additive.toMul (α := Idele L) (y g)) hcoc
    -- `g ↦ ρ g (β) - β` is exactly `x`
    let hw : (ideleRep K L).V := Additive.ofMul (α := Idele L) β
    refine ⟨hw, ?_⟩
    funext g
    rw [groupCohomology.d₀₁_hom_apply]
    simp only [hw]
    rw [show (ideleRep K L).ρ g (Additive.ofMul (α := Idele L) β)
        = Additive.ofMul (α := Idele L) (g • β) from rfl]
    change Additive.ofMul (α := Idele L) (g • β) - Additive.ofMul (α := Idele L) β = y g
    rw [← ofMul_div (x := g • β) (y := β), hβ g]
    exact ofMul_toMul (α := Idele L) (y g)
  exact ⟨fun a b => by rw [key a, key b]⟩

end NK.HassePrinciple
