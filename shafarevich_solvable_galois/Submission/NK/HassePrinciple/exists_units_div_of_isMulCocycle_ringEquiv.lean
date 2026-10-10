import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hilbert 90 for ring automorphisms of a field

If a finite group `H` acts on a field `F` through an injective homomorphism
`φ : H →* (F ≃+* F)` (so that distinct elements of `H` induce distinct field automorphisms), then
every multiplicative `1`-cocycle `f : H → Fˣ`, i.e. every `f` satisfying
`f (g * h) = (φ g) (f h) * f g`, is a coboundary: there is `β : Fˣ` with
`f g = (φ g) β / β` for all `g`.

This is Noether's form of Hilbert's theorem 90, valid for the (not necessarily surjective) image
of an injective `φ`, with no finite-dimensionality or Galois hypothesis: the only input is
Dedekind's linear independence of characters, applied to the distinct field automorphisms `φ g`.

The proof is the classical one.  The linear combination `∑_g (f g)⁻¹ · φ g` of the distinct field
automorphisms `φ g` is not the zero function, because its coefficients are all nonzero
(Dedekind).  Hence there is `z : F` with `Y := ∑_g (f g)⁻¹ * φ g z ≠ 0`; the cocycle identity
gives `φ t Y = f t * Y`, so `β = Y` is the required element.
-/

namespace NK.HassePrinciple

theorem exists_units_div_of_isMulCocycle_ringEquiv {F : Type*} [Field F] {H : Type*} [Group H]
    [Fintype H] (φ : H →* (F ≃+* F)) (hφ : Function.Injective φ) (f : H → Fˣ)
    (hf : ∀ g h : H, f (g * h) = Units.map (φ g).toMonoidHom (f h) * f g) :
    ∃ β : Fˣ, ∀ g : H, f g = Units.map (φ g).toMonoidHom β / β := by
  classical
  -- Dedekind: the characters `φ g` are linearly independent over `F`.
  have hlin : LinearIndependent F (fun g : H => ((φ g : F ≃+* F) : F → F)) :=
    LinearIndependent.comp (ι' := H) (linearIndependent_monoidHom F F)
      (fun g : H => (φ g).toMonoidHom) (by
        intro a b hab
        exact hφ (by ext x; exact DFunLike.ext_iff.1 hab x))
  -- The linear combination `∑ g, (f g)⁻¹ · φ g` is not the zero function.
  have hex : ∃ z : F, (∑ g : H, (((f g)⁻¹ : Fˣ) : F) * (φ g) z) ≠ 0 := by
    by_contra h
    push Not at h
    have hcomb : (∑ g : H, (((f g)⁻¹ : Fˣ) : F) • (fun z : F => (φ g) z)) = 0 := by
      funext z
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact h z
    have h1 := Fintype.linearIndependent_iff.mp hlin (fun g : H => (((f g)⁻¹ : Fˣ) : F))
      hcomb 1
    exact Units.ne_zero ((f 1)⁻¹) h1
  obtain ⟨z, hz⟩ := hex
  set Y : F := ∑ g : H, (((f g)⁻¹ : Fˣ) : F) * (φ g) z with hYdef
  -- The key identity: `φ t Y = f t * Y`.
  have hact : ∀ t : H, (↑(φ t) : F →+* F) Y = ((f t : Fˣ) : F) * Y := by
    intro t
    have hterm : ∀ g : H, (φ t) ((((f g)⁻¹ : Fˣ) : F) * (φ g) z) =
        ((f t : Fˣ) : F) * ((((f (t * g))⁻¹ : Fˣ) : F) * (φ (t * g)) z) := by
      intro g
      -- the cocycle identity, in the field `F`
      have hcoc : (φ t) ((f g : Fˣ) : F) =
          (((f (t * g) : Fˣ) : F)) * (((f t : Fˣ) : F))⁻¹ := by
        have h := congrArg (fun u : Fˣ => (u : F)) (hf t g)
        simp only [Units.val_mul, Units.coe_map] at h
        rw [← div_eq_mul_inv, eq_div_iff (Units.ne_zero (f t))]
        exact h.symm
      have h2 : (φ t) (((f g : Fˣ) : F)⁻¹) = ((φ t) ((f g : Fˣ) : F))⁻¹ := by
        change (↑(φ t) : F →+* F) (((f g : Fˣ) : F)⁻¹) = _
        rw [map_inv₀]
        rfl
      have h1 : (φ t) (((f g : Fˣ) : F)⁻¹) =
          ((f t : Fˣ) : F) * (((f (t * g) : Fˣ) : F))⁻¹ := by
        rw [h2, hcoc, mul_inv_rev]
        simp
      rw [show (((f g)⁻¹ : Fˣ) : F) = (((f g : Fˣ) : F))⁻¹ from Units.val_inv_eq_inv_val _]
      rw [map_mul, h1]
      rw [show (φ t) ((φ g) z) = (φ (t * g)) z from by
        rw [← RingAut.mul_apply, ← map_mul]]
      simp only [Units.val_inv_eq_inv_val]
      ring
    calc (↑(φ t) : F →+* F) Y
        = ∑ g : H, (φ t) ((((f g)⁻¹ : Fˣ) : F) * (φ g) z) := by
          rw [hYdef]
          exact map_sum (↑(φ t) : F →+* F) _ _
      _ = ∑ g : H, ((f t : Fˣ) : F) * ((((f (t * g))⁻¹ : Fˣ) : F) * (φ (t * g)) z) :=
          Finset.sum_congr rfl (fun g _ => hterm g)
      _ = ((f t : Fˣ) : F) * Y := by
          rw [← Finset.mul_sum, hYdef]
          congr 1
          exact Fintype.sum_bijective (fun g => t * g) (Group.mulLeft_bijective t) _ _
            (fun g => rfl)
  refine ⟨Units.mk0 Y hz, fun t => ?_⟩
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.coe_map, Units.val_mk0]
  change (↑(f t) : F) = (↑(φ t) : F →+* F) Y / Y
  rw [hact t]
  exact (mul_div_cancel_right₀ _ hz).symm

end NK.HassePrinciple
