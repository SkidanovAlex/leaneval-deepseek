/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `|Ĥ¹(Gal(L/K), ∏_{w | v} L_wˣ)| = 1` for every place `v` of `K`

For a finite Galois extension `L / K` of number fields and a place `v` of `K`, the fibre of the
idèles of `L` over `v` — the idèles supported on the places `w | v`, i.e. Milne's
`∏_{w | v} L_wˣ` (`NK.GlobalCFTdeep.fiberIdelesRep`) — has trivial first Tate cohomology:

  `hOne (fiberIdelesRep v) = |Ĥ¹(Gal(L/K), ∏_{w | v} L_wˣ)| = 1`.

This is the per-place input of Milne's Proposition 2.7 (the fibrewise computation of the Herbrand
quotient of the `T`-idèles), and it is where Hilbert's theorem 90 enters the global picture: by
Shapiro's lemma the fibre is `Coind_{D_w}^{G} L_wˣ` for a place `w | v`
(`NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind`), so its `Ĥ¹` is that of the local units
`L_wˣ` under the decomposition group `D_w`, and every crossed homomorphism
`D_w → L_wˣ` is a coboundary — Noether's form of Hilbert 90.

The statement holds at *every* place `v`, archimedean included, and the proof below is uniform in
`v`: no local class field theory, no cyclicity of the decomposition group and no finiteness or
Galois property of the local field `L_w` is used.  The only input is that the action of `D_w` on
`L_w` is by *faithful* field automorphisms (`localAutHom_injective`): an element of `D_w` acting
trivially on `L_w` acts trivially on the dense image of `L`, hence is the identity.

## Main statements

* `NK.GlobalCFTdeep.Herbrand.subsingleton_groupCohomology_one_of_injective_ringAut` — Hilbert 90
  in the form used here: for a finite group `G` acting on the units of a field `F` through an
  injective homomorphism into the ring automorphisms of `F`, the group cohomology `H¹(G, Fˣ)`
  vanishes.
* `NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_one_localUnitsRep` — the local computation
  `|Ĥ¹(D_w, L_wˣ)| = 1`.
* `NK.GlobalCFTdeep.Herbrand.hOne_fiberIdelesRep_eq_one` — the statement of the file.

For *finite* places the same computation is also available through the identification of `D_q`
with the local Galois group (`NK.GlobalCFTdeep.Herbrand.hOne_localUnitsRep_eq_one`); the argument
here is independent of it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

/-! ## Hilbert 90 for a faithful action on the units of a field -/

/-- **Hilbert's theorem 90, representation-theoretically.**  Let a finite group `G` act on the
units `Fˣ` of a field `F` through a *faithful* homomorphism `φ : G →* (F ≃+* F)` into the ring
automorphisms of `F` (`hact` records that the action is the one induced by `φ`).  Then
`H¹(G, Fˣ) = 0`: every `1`-cocycle is a coboundary.

The proof is Noether's: the crossed homomorphism is a coboundary by
`NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv` (Dedekind's independence of the
distinct characters `φ g`), which is exactly the statement that the class of the cocycle in `H¹`
vanishes. -/
theorem subsingleton_groupCohomology_one_of_injective_ringAut
    {G : Type} [Group G] [Fintype G] {F : Type} [Field F]
    [MulDistribMulAction G Fˣ] (φ : G →* (F ≃+* F)) (hφ : Function.Injective φ)
    (hact : ∀ (g : G) (u : Fˣ), g • u = Units.map (φ g).toMonoidHom u) :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 1) := by
  have key : ∀ a : groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 1, a = 0 := by
    intro a
    refine groupCohomology.H1_induction_on a (fun x => ?_)
    refine (groupCohomology.H1π_eq_zero_iff x).2 ?_
    -- the cocycle in the multiplicative world
    let y : G → Additive Fˣ := fun g => x.1 g
    have hmem : y ∈ groupCohomology.cocycles₁ (Rep.ofMulDistribMulAction G Fˣ) := x.2
    have hcoc : groupCohomology.IsMulCocycle₁ (M := Fˣ) (fun g => Additive.toMul (y g)) :=
      groupCohomology.isMulCocycle₁_of_mem_cocycles₁ (M := Fˣ) (f := y) hmem
    have hφcoc : ∀ g h : G, (fun g => Additive.toMul (y g)) (g * h) =
        Units.map (φ g).toMonoidHom ((fun g => Additive.toMul (y g)) h)
          * (fun g => Additive.toMul (y g)) g := by
      intro g h
      simpa only [hact g (Additive.toMul (y h))] using hcoc g h
    -- Hilbert 90: the crossed homomorphism is a coboundary
    obtain ⟨β, hβ⟩ := NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv
      φ hφ (fun g => Additive.toMul (y g)) hφcoc
    have hb : groupCohomology.IsMulCoboundary₁ (M := Fˣ) (fun g => Additive.toMul (y g)) :=
      ⟨β, fun g => by rw [hact g β]; exact (hβ g).symm⟩
    have hfun : (Additive.ofMul ∘ (fun g => Additive.toMul (y g))) = y := by
      funext g; exact ofMul_toMul (y g)
    have hmem2 : y ∈ groupCohomology.coboundaries₁ (Rep.ofMulDistribMulAction G Fˣ) := by
      have h := (groupCohomology.coboundariesOfIsMulCoboundary₁ hb).2
      have h' : (Additive.ofMul ∘ (fun g => Additive.toMul (y g))) ∈
          groupCohomology.coboundaries₁ (Rep.ofMulDistribMulAction G Fˣ) := h
      rw [hfun] at h'
      exact h'
    show y ∈ groupCohomology.coboundaries₁ (Rep.ofMulDistribMulAction G Fˣ)
    exact hmem2
  exact ⟨fun a b => by rw [key a, key b]⟩

/-! ## The action of the decomposition group on the local field -/

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The action of the decomposition group `D_w` on the local field `L_w`, as a homomorphism into
the ring automorphisms of `L_w`.  It is the transport to `NK.GlobalCFTdeep` of the Hasse–Brauer–
Noether local automorphism `NK.HassePrinciple.localAutHom`; the two are definitionally equal
because `D_w` and the stabiliser of `w` are the same subgroup. -/
noncomputable def decompositionLocalAutHom (w : Place L) :
    NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w →*
      (Place.localField L w ≃+* Place.localField L w) :=
  NK.HassePrinciple.localAutHom (K := K) (L := L) w

/-- The local automorphism attached to a decomposition element is the transported local action
of `NK.GlobalCFT.Inclusion.Place.localAction`. -/
theorem decompositionLocalAutHom_apply (w : Place L)
    (σ : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w) :
    decompositionLocalAutHom (K := K) (L := L) w σ
      = NK.GlobalCFT.Inclusion.Place.localAction σ.1 w
          (NK.GlobalCFTdeep.mem_decompositionSubgroup.mp σ.2) := by
  rw [NK.GlobalCFTdeep.localAction_eq_localAut]
  rfl

/-- **The action of `D_w` on `L_w` is faithful**: distinct elements of the decomposition group
induce distinct automorphisms of `L_w`. -/
theorem decompositionLocalAutHom_injective (w : Place L) :
    Function.Injective (decompositionLocalAutHom (K := K) (L := L) w) :=
  NK.HassePrinciple.localAutHom_injective (K := K) (L := L) w

/-! ## `Ĥ¹` of the local units vanishes -/

/-- **Hilbert 90 for the local units of a place.**  For *every* place `w` of `L` — finite or
archimedean — the first group cohomology of the local units `L_wˣ` under the action of the
decomposition group `D_w` vanishes. -/
theorem subsingleton_groupCohomology_one_localUnitsRep (w : Place L)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)] :
    Subsingleton (groupCohomology (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w) 1) := by
  letI : MulDistribMulAction (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)
      ((Place.localField L w)ˣ) := NK.GlobalCFTdeep.decompositionUnitsAction (K := K) (L := L) w
  exact subsingleton_groupCohomology_one_of_injective_ringAut
    (G := NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w) (F := Place.localField L w)
    (decompositionLocalAutHom (K := K) (L := L) w)
    (decompositionLocalAutHom_injective (K := K) (L := L) w)
    (fun σ u => by rw [decompositionLocalAutHom_apply]; rfl)

/-- **`|Ĥ¹(D_w, L_wˣ)| = 1`**: the first Tate cohomology of the local units of a place, under the
decomposition group, is trivial. -/
theorem natCard_tateCohomology_one_localUnitsRep (w : Place L)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)] :
    Nat.card (tateCohomology (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w) 1) = 1 := by
  have h1 : Nat.card (groupCohomology (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w) 1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨subsingleton_groupCohomology_one_localUnitsRep (K := K) (L := L) w, ⟨0⟩⟩
  exact (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ)
    (G := NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w) 1).app
      (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w)).toLinearEquiv.toEquiv).trans h1

/-- `hOne` of the local units of a place is `1`. -/
theorem hOne_localUnitsRep_of_ringAut_eq_one (w : Place L)
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)] :
    NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w) = 1 := by
  rw [NK.GlobalCFTdeep.hOne_def]
  exact natCard_tateCohomology_one_localUnitsRep (K := K) (L := L) w

/-! ## The fibre of a place has trivial `Ĥ¹` -/

theorem hOne_fiberIdelesRep_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] (v : NK.GlobalCFT.Place K) :
    NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) v) = 1 := by
  classical
  -- a place `w` of `L` above `v`
  obtain ⟨w, hw⟩ := NK.GlobalCFT.Inclusion.exists_place_liesOver (K := K) (L := L) v
  haveI : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w) :=
    Fintype.ofFinite _
  -- Shapiro's lemma: the fibre is the coinduced local units
  obtain ⟨e⟩ := fiberIdelesRep_iso_coind (K := K) (L := L) v w hw
  rw [NK.GlobalCFTdeep.hOne_def]
  calc Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) v) 1)
      = Nat.card (tateCohomology (Rep.coind
            (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w).subtype
            (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w)) 1) :=
          Nat.card_congr (((tateCohomologyFunctor (R := ℤ) (G := L ≃ₐ[K] L) 1).mapIso e)
            |>.toLinearEquiv.toEquiv)
    _ = NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w) := by
          rw [← NK.GlobalCFTdeep.hOne_def]
          exact hOne_coind (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)
            (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := L) w)
    _ = 1 := hOne_localUnitsRep_of_ringAut_eq_one (K := K) (L := L) w

end NK.GlobalCFTdeep.Herbrand
