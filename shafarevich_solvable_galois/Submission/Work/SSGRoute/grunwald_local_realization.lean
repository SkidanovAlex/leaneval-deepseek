import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.grunwald_kummer_idx
import Submission.Work.SSGRoute.kummer_character_realization_inf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local realization of a continuous additive character by a Kummer class

Let `κ` be a field containing a primitive `p`-th root of unity `ζ`, `M` a separable closure of `κ`,
and `g : Gal(M/κ) → ZMod p` an additive map which is continuous for the Krull topology, in the form
that it vanishes on an open subgroup `U`.  Then there is `c ∈ κˣ` and a `p`-th root `γ ∈ Mˣ` of
`c` such that the Kummer index of every `σ` at `(c, γ)` is `g σ`.

The argument uses the realization of Kummer characters of the absolute Galois group
(`Work.SSGRoute.kummer_character_realization_inf`): the character `χ = zr ∘ ofAdd ∘ g` has open
kernel, so there is `γ ∈ M` with `σ γ / γ = χ σ` and `γ ^ p ∈ κ`; `γ` is nonzero (its ratio at
`σ = 1` is `1`), and then `(c, γ) := (γ ^ p, γ)` realizes `g` by `kummerIdx_spec`.

The same statement for a general `κ ⊆ L ⊆ M` was requested as
`Work.SSGRoute.exists_local_kummer_element`; this file proves it directly at the infinite level,
which avoids passing to the finite subextension `L/κ`.
-/

namespace Work.SSGRoute

open scoped Classical

noncomputable section

theorem exists_local_kummer_element {κ M : Type*} [Field κ] [Field M] [Algebra κ M]
    [IsSepClosure κ M] (p : ℕ) [Fact p.Prime] {ζ : κ} (hζ : IsPrimitiveRoot ζ p)
    (g : (M ≃ₐ[κ] M) → ZMod p) (hg : ∀ σ τ : M ≃ₐ[κ] M, g (σ * τ) = g σ + g τ)
    (hgc : ∃ U : Subgroup (M ≃ₐ[κ] M), IsOpen (U : Set (M ≃ₐ[κ] M)) ∧ ∀ x ∈ U, g x = 0) :
    ∃ (c : κˣ) (γ : Mˣ) (h : γ ^ p = Units.map (algebraMap κ M) c),
      ∀ σ : M ≃ₐ[κ] M, kummerIdx p hζ c γ h σ = g σ := by
  classical
  haveI hgal : IsGalois κ M := IsSepClosure.isGalois
  have hg1 : g 1 = 0 := by
    have h := hg 1 1
    rw [mul_one] at h
    exact add_left_cancel (show g 1 + g 1 = g 1 + 0 by rw [add_zero]; exact h.symm)
  let χ : (M ≃ₐ[κ] M) →* ↥(rootsOfUnity p κ) :=
    { toFun := fun σ => zr (isPrimitiveRoot_primRootUnit (F := κ) p hζ)
        (Multiplicative.ofAdd (g σ))
      map_one' := by
        rw [hg1]
        simp
      map_mul' := fun σ τ => by
        rw [hg σ τ, ofAdd_add, map_mul] }
  obtain ⟨U, hUopen, hU⟩ := hgc
  have hUker : U ≤ χ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show zr (isPrimitiveRoot_primRootUnit (F := κ) p hζ) (Multiplicative.ofAdd (g x)) = 1
    rw [hU x hx]
    simp
  have hχopen : IsOpen (χ.ker : Set (M ≃ₐ[κ] M)) := Subgroup.isOpen_mono hUker hUopen
  obtain ⟨γ, hγpow, hγdiv⟩ :=
    kummer_character_realization_inf (U := κ) (L := M) (n := p)
      (Fact.out : p.Prime).ne_zero χ hχopen
  have hγne : γ ≠ 0 := by
    intro h0
    have h := hγdiv 1
    rw [h0, div_zero, map_one, Subgroup.coe_one, Units.val_one, map_one] at h
    exact zero_ne_one h
  obtain ⟨a, ha⟩ := hγpow
  have hane : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha
    exact pow_ne_zero p hγne ha.symm
  have hpow : (Units.mk0 γ hγne) ^ p = Units.map (algebraMap κ M) (Units.mk0 a hane) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, Units.val_mk0]
    exact ha.symm
  refine ⟨Units.mk0 a hane, Units.mk0 γ hγne, hpow, ?_⟩
  intro σ
  have hratio : Work.Kummer.kummerRatio σ (Units.mk0 γ hγne) =
      Units.map (algebraMap κ M)
        (((zr (isPrimitiveRoot_primRootUnit (F := κ) p hζ)
          (Multiplicative.ofAdd (g σ)) : ↥(rootsOfUnity p κ)) : κˣ)) := by
    apply Units.ext
    rw [Work.Kummer.kummerRatio_coe, Units.coe_map]
    rw [show (σ : M ≃ₐ[κ] M) (Units.mk0 γ hγne : M) / (Units.mk0 γ hγne : M) =
      algebraMap κ M (((χ σ : ↥(rootsOfUnity p κ)) : κˣ) : κ) from hγdiv σ]
    rfl
  have hnat := zr_map_eq (F := κ) (E := M) p hζ (Multiplicative.ofAdd (g σ))
  have hspec := kummerIdx_spec p hζ (Units.mk0 a hane) (Units.mk0 γ hγne) hpow σ
  have hkey : (zr (isPrimitiveRoot_mappedRoot (F := κ) (E := M) p hζ)
        (Multiplicative.ofAdd
          (kummerIdx p hζ (Units.mk0 a hane) (Units.mk0 γ hγne) hpow σ)) : Mˣ) =
      (zr (isPrimitiveRoot_mappedRoot (F := κ) (E := M) p hζ)
        (Multiplicative.ofAdd (g σ)) : Mˣ) := by
    rw [← hspec, hratio, hnat]
  exact congrArg Multiplicative.toAdd
    ((zr (isPrimitiveRoot_mappedRoot (F := κ) (E := M) p hζ)).injective (Subtype.ext hkey))

end

end Work.SSGRoute
