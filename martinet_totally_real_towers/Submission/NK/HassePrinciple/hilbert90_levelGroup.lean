/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hilbert 90 for the level group: `H¹(LevelGroup V L, Lˣ) = 0`

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4, §10.4).

The level group `NK.BrauerHasse.LevelGroup V L = V ⧸ (V ⊓ Gal(K'/L))` acts on the units `Lˣ`
of the finite Galois level `L` through the restriction map

`NK.HassePrinciple.levelGroupRestrictHom V L : LevelGroup V L →* Gal(L/K)`,

which is **injective**: its kernel is exactly the subgroup `V ⊓ Gal(K'/L)` that is divided out
(`NK.HassePrinciple.levelGroupRestrictHom_injective`).  Consequently every crossed
homomorphism `f : LevelGroup V L → Lˣ` for this action is a coboundary — Noether's form of
Hilbert's theorem 90 for the (not necessarily surjective) image of the level group in `Gal(L/K)`.

The general statement is proved first in the form in which it is used
(`NK.HassePrinciple.hilbert90_injective`): for *any* group `G` mapping injectively into
`Gal(L/K)` by `ψ` and any `f : G → Lˣ` with `f (g * h) = ψ g (f h) * f g`, there is `x : Lˣ`
with `ψ g x / x = f g`.

The proof is the classical one, done with Dedekind's linear independence of characters: the
linear combination `∑_g f(g)⁻¹ · ψ(g)` is nonzero on `L`, so some `z` has
`Y := ∑_g (f g)⁻¹ * ψ(g) z ≠ 0`; the cocycle identity gives `ψ t Y = f t * Y`, whence `x = Y`
is the required element.  (Injectivity of `ψ` is what makes Dedekind's argument apply; for a
non-injective `ψ` the statement is false.)
-/

import Mathlib
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.finite_levelGroup

set_option autoImplicit false

namespace NK.HassePrinciple

universe u

/-! ## The general form of Hilbert 90 for an injective restriction map -/

set_option maxHeartbeats 1600000 in
set_option linter.style.haveILetI false in
/-- **Hilbert 90 (Noether's form) for a group acting on a field through an injective
homomorphism into `Gal(L/K)`.**

If `ψ : G →* Gal(L/K)` is injective and `f : G → Lˣ` satisfies the crossed-homomorphism identity
`f (g * h) = ψ g (f h) * f g`, then `f` is a coboundary: there is `x : Lˣ` with
`ψ g x / x = f g` for all `g`.

The proof is the classical one: the `L`-linear combination `∑_g (f g)⁻¹ · ψ(g)` of the distinct
field automorphisms `ψ(g)` is nonzero on `L` (Dedekind's independence of characters, using that
each coefficient `(f g)⁻¹` is a nonzero element of `L`), so for a suitable `z` the element
`Y = ∑_g (f g)⁻¹ * ψ(g) z` is nonzero, and the cocycle identity gives `ψ t Y = f t * Y`. -/
theorem hilbert90_injective {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G]
    [Finite G] (ψ : G →* (L ≃ₐ[K] L)) (hψ : Function.Injective ψ) (f : G → Lˣ)
    (hf : ∀ g h : G, f (g * h) = Units.map (ψ g : L →* L) (f h) * f g) :
    ∃ x : Lˣ, ∀ g : G, Units.map (ψ g : L →* L) x / x = f g := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Dedekind: the characters `ψ g` are linearly independent over `L`.
  have hlin : LinearIndependent L (fun g : G => ((ψ g : L ≃ₐ[K] L) : L → L)) :=
    LinearIndependent.comp (ι' := G) (linearIndependent_monoidHom L L) (fun g => ψ g) (by
      intro a b hab
      exact hψ (by ext x; exact DFunLike.ext_iff.1 hab x))
  -- The linear combination `∑ g, (f g)⁻¹ · ψ g` is not the zero function.
  have hex : ∃ z : L, (∑ g : G, (((f g)⁻¹ : Lˣ) : L) * (ψ g) z) ≠ 0 := by
    by_contra h
    push Not at h
    have hcomb : (∑ g : G, (((f g)⁻¹ : Lˣ) : L) • (fun z : L => (ψ g) z)) = 0 := by
      funext z
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact h z
    have h1 := Fintype.linearIndependent_iff.mp hlin (fun g : G => (((f g)⁻¹ : Lˣ) : L))
      hcomb 1
    exact Units.ne_zero ((f 1)⁻¹) h1
  obtain ⟨z, hz⟩ := hex
  set Y : L := ∑ g : G, (((f g)⁻¹ : Lˣ) : L) * (ψ g) z with hYdef
  -- The key identity: `ψ t Y = f t * Y`.
  have hact : ∀ t : G, (↑(ψ t) : L →+* L) Y = ((f t : Lˣ) : L) * Y := by
    intro t
    have hterm : ∀ g : G, (ψ t) ((((f g)⁻¹ : Lˣ) : L) * (ψ g) z) =
        ((f t : Lˣ) : L) * ((((f (t * g))⁻¹ : Lˣ) : L) * (ψ (t * g)) z) := by
      intro g
      -- the cocycle identity, in the field `L`
      have hcoc : (ψ t) ((f g : Lˣ) : L) =
          (((f (t * g) : Lˣ) : L)) * (((f t : Lˣ) : L))⁻¹ := by
        have h := congrArg (fun u : Lˣ => (u : L)) (hf t g)
        simp only [Units.val_mul, Units.coe_map] at h
        rw [← div_eq_mul_inv, eq_div_iff (Units.ne_zero (f t))]
        exact h.symm
      have h2 : (ψ t) (((f g : Lˣ) : L)⁻¹) = ((ψ t) ((f g : Lˣ) : L))⁻¹ := by
        change (↑(ψ t) : L →+* L) (((f g : Lˣ) : L)⁻¹) = _
        rw [map_inv₀]
        rfl
      have h1 : (ψ t) (((f g : Lˣ) : L)⁻¹) =
          ((f t : Lˣ) : L) * (((f (t * g) : Lˣ) : L))⁻¹ := by
        rw [h2, hcoc, mul_inv_rev]
        simp
      rw [show (((f g)⁻¹ : Lˣ) : L) = (((f g : Lˣ) : L))⁻¹ from Units.val_inv_eq_inv_val _]
      rw [map_mul, h1]
      rw [show (ψ t) ((ψ g) z) = (ψ (t * g)) z from by
        rw [← AlgEquiv.mul_apply, ← map_mul]]
      simp only [Units.val_inv_eq_inv_val]
      ring
    calc (↑(ψ t) : L →+* L) Y
        = ∑ g : G, (ψ t) ((((f g)⁻¹ : Lˣ) : L) * (ψ g) z) := by
          rw [hYdef]
          exact map_sum (↑(ψ t) : L →+* L) _ _
      _ = ∑ g : G, ((f t : Lˣ) : L) * ((((f (t * g))⁻¹ : Lˣ) : L) * (ψ (t * g)) z) :=
          Finset.sum_congr rfl (fun g _ => hterm g)
      _ = ((f t : Lˣ) : L) * Y := by
          rw [← Finset.mul_sum, hYdef]
          congr 1
          exact Fintype.sum_bijective (fun g => t * g) (Group.mulLeft_bijective t) _ _
            (fun g => rfl)
  refine ⟨Units.mk0 Y hz, fun t => ?_⟩
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.coe_map, Units.val_mk0]
  change (↑(ψ t) : L →+* L) Y / Y = ↑(f t)
  rw [hact t]
  exact mul_div_cancel_right₀ _ hz

/-! ## The level group acts faithfully on the level -/

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The restriction map of the level group is injective.**  Its kernel is exactly the subgroup
`V ⊓ Gal(K'/L)` by which the level group is divided out, so `LevelGroup V L` embeds into the
finite Galois group `Gal(L/K)` as the image `V.map (levelRestrict L)`. -/
theorem levelGroupRestrictHom_injective (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (levelGroupRestrictHom V L) := by
  rw [levelGroupRestrictHom]
  exact (QuotientGroup.injective_lift_iff (N := L.fixingSubgroup.subgroupOf V)
    (levelRestrictHom V L) _).2 (levelRestrictHom_ker V L).symm

/-! ## Hilbert 90 for the level group -/

/-- **Hilbert 90 for the level group**: every crossed homomorphism `f` on the level group
`LevelGroup V L` with values in `Lˣ`, for the action through the restriction map
`levelGroupRestrictHom V L`, is a coboundary. -/
theorem hilbert90_levelGroup {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup (K' ≃ₐ[K] K')) (L : FiniteGaloisIntermediateField K K')
    (f : NK.BrauerHasse.LevelGroup V L → (↥L)ˣ)
    (hf : ∀ g h : NK.BrauerHasse.LevelGroup V L,
      f (g * h) = Units.map (NK.HassePrinciple.levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) (f h)
        * f g) :
    ∃ x : (↥L)ˣ,
      ∀ g : NK.BrauerHasse.LevelGroup V L,
        Units.map (NK.HassePrinciple.levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) x / x = f g :=
  hilbert90_injective (levelGroupRestrictHom V L) (levelGroupRestrictHom_injective V L) f hf

end NK.HassePrinciple
