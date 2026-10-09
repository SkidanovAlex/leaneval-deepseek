import Mathlib
import Submission.Work.SSGRoute.E8Defs
import Submission.Work.SSGRoute.eb_loc_aux
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_helpers
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
import Submission.NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank
import Submission.NK.NUV2.LC.unitsLevelH2_addOrderOf_realization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open NK.GlobalCFT CategoryTheory NumberField
/-- **The second cohomology of a representation only depends on the action as a function.**
Two `G`-representations whose underlying additive groups are identified by an additive equivalence
`e` and whose actions are identified by `hρ` have additively equivalent `H²`, even if their
coefficient rings differ. -/
theorem h2_transport_rho_eq {k k' G : Type} [CommRing k] [CommRing k'] [Group G]
    (A : Rep k G) (B : Rep k' G) (e : A.V ≃+ B.V)
    (hρ : ∀ (g : G) (x : A.V), e (A.ρ g x) = B.ρ g (e x)) :
    Nonempty (groupCohomology A 2 ≃+ groupCohomology B 2) := by
  classical
  have hφadd : ∀ f f' : G × G → A.V,
      (fun p => e (f p + f' p)) = (fun p => e (f p)) + (fun p => e (f' p)) := by
    intro f f'; funext p; exact map_add e _ _
  have hφsub : ∀ f f' : G × G → A.V,
      (fun p => e (f p - f' p)) = (fun p => e (f p)) - (fun p => e (f' p)) := by
    intro f f'; funext p; exact map_sub e _ _
  have hψadd : ∀ f f' : G × G → B.V,
      (fun p => e.symm (f p + f' p)) = (fun p => e.symm (f p)) + (fun p => e.symm (f' p)) := by
    intro f f'; funext p; exact map_add e.symm _ _
  have hψφ : ∀ f : G × G → A.V, (fun p => e.symm (e (f p))) = f := by
    intro f; funext p; exact e.symm_apply_apply (f p)
  have hφψ : ∀ f : G × G → B.V, (fun p => e (e.symm (f p))) = f := by
    intro f; funext p; exact e.apply_symm_apply (f p)
  have hφinj : ∀ {ι : Type} (f f' : ι → A.V),
      (fun p => e (f p)) = (fun p => e (f' p)) → f = f' := by
    intro ι f f' h; funext p
    exact e.injective (congrFun h p)
  have hd₁₂ : ∀ x : G → A.V, (fun p => e ((groupCohomology.d₁₂ A).hom x p)) =
      (groupCohomology.d₁₂ B).hom (fun g => e (x g)) := by
    intro x; funext p
    obtain ⟨g, h⟩ := p
    rw [groupCohomology.d₁₂_hom_apply, groupCohomology.d₁₂_hom_apply]
    simp only [map_sub, map_add]
    rw [hρ g (x h)]
  have hd₂₃ : ∀ f : G × G → A.V, (fun p => e ((groupCohomology.d₂₃ A).hom f p)) =
      (groupCohomology.d₂₃ B).hom (fun p => e (f p)) := by
    intro f; funext p
    obtain ⟨g, h1, h2⟩ := p
    rw [groupCohomology.d₂₃_hom_apply, groupCohomology.d₂₃_hom_apply]
    simp only [map_sub, map_add]
    rw [hρ g (f (h1, h2))]
  have hcoc : ∀ f : G × G → A.V, f ∈ groupCohomology.cocycles₂ A ↔
      (fun p => e (f p)) ∈ groupCohomology.cocycles₂ B := by
    intro f
    rw [groupCohomology.cocycles₂, groupCohomology.cocycles₂, LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro h
      rw [← hd₂₃, h]
      funext p
      exact map_zero e
    · intro h
      refine hφinj _ (0 : G × G × G → A.V) ?_
      rw [hd₂₃, h]
      funext p
      exact (map_zero e).symm
  have hcob : ∀ f : G × G → A.V, f ∈ groupCohomology.coboundaries₂ A ↔
      (fun p => e (f p)) ∈ groupCohomology.coboundaries₂ B := by
    intro f
    rw [groupCohomology.coboundaries₂, groupCohomology.coboundaries₂,
      LinearMap.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun g => e (x g), (hd₁₂ x).symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨fun g => e.symm (y g), ?_⟩
      have h1 : (fun p => e ((groupCohomology.d₁₂ A).hom (fun g => e.symm (y g)) p)) =
          (groupCohomology.d₁₂ B).hom y := by
        rw [hd₁₂]
        congr 1
        funext g
        exact e.apply_symm_apply (y g)
      exact hφinj _ _ (by rw [h1]; exact hy)
  have hsurj : Function.Surjective (⇑(groupCohomology.H2π A)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hsurj' : Function.Surjective (⇑(groupCohomology.H2π B)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  let cast₁ : ↥(groupCohomology.cocycles₂ A) → ↥(groupCohomology.cocycles₂ B) :=
    fun z => ⟨fun p => e (z.1 p), (hcoc z.1).mp z.2⟩
  let cast₂ : ↥(groupCohomology.cocycles₂ B) → ↥(groupCohomology.cocycles₂ A) :=
    fun z => ⟨fun p => e.symm (z.1 p), (hcoc _).mpr (by rw [hφψ]; exact z.2)⟩
  have cast₁_apply : ∀ z : ↥(groupCohomology.cocycles₂ A), ⇑(cast₁ z) = fun p => e (z.1 p) :=
    fun z => rfl
  have cast₂_apply : ∀ z : ↥(groupCohomology.cocycles₂ B), ⇑(cast₂ z) = fun p => e.symm (z.1 p) :=
    fun z => rfl
  have cast₁_add : ∀ x y, cast₁ (x + y) = cast₁ x + cast₁ y := by
    intro x y; exact Subtype.ext (hφadd x.1 y.1)
  have cast₂_add : ∀ x y, cast₂ (x + y) = cast₂ x + cast₂ y := by
    intro x y; exact Subtype.ext (hψadd x.1 y.1)
  have hcomp : ∀ z, cast₂ (cast₁ z) = z := by
    intro z
    refine Subtype.ext ?_
    funext p
    exact e.symm_apply_apply (z.1 p)
  have hcomp' : ∀ z, cast₁ (cast₂ z) = z := by
    intro z
    refine Subtype.ext ?_
    funext p
    exact e.apply_symm_apply (z.1 p)
  have hwd : ∀ x x' : ↥(groupCohomology.cocycles₂ A),
      groupCohomology.H2π A x = groupCohomology.H2π A x' →
      groupCohomology.H2π B (cast₁ x) = groupCohomology.H2π B (cast₁ x') := by
    intro x x' h
    have hsub : ⇑x - ⇑x' ∈ groupCohomology.coboundaries₂ A :=
      (groupCohomology.H2π_eq_iff x x').mp h
    have h1 := (hcob (⇑x - ⇑x')).mp hsub
    have h2 : ⇑(cast₁ x) - ⇑(cast₁ x') = fun p => e ((⇑x - ⇑x') p) := by
      funext p
      exact (map_sub e (⇑x p) (⇑x' p)).symm
    rw [groupCohomology.H2π_eq_iff, h2]
    exact h1
  have hwd' : ∀ x x' : ↥(groupCohomology.cocycles₂ B),
      groupCohomology.H2π B x = groupCohomology.H2π B x' →
      groupCohomology.H2π A (cast₂ x) = groupCohomology.H2π A (cast₂ x') := by
    intro x x' h
    have hsub : ⇑x - ⇑x' ∈ groupCohomology.coboundaries₂ B :=
      (groupCohomology.H2π_eq_iff x x').mp h
    have hsub' : (fun p => e.symm ((⇑x - ⇑x') p)) ∈ groupCohomology.coboundaries₂ A :=
      (hcob _).mpr (by rw [hφψ]; exact hsub)
    have h2 : ⇑(cast₂ x) - ⇑(cast₂ x') = fun p => e.symm ((⇑x - ⇑x') p) := by
      funext p
      exact (map_sub e.symm (⇑x p) (⇑x' p)).symm
    rw [groupCohomology.H2π_eq_iff, h2]
    exact hsub'
  let F : groupCohomology A 2 → groupCohomology B 2 :=
    fun y => groupCohomology.H2π B (cast₁ (Function.surjInv hsurj y))
  let F' : groupCohomology B 2 → groupCohomology A 2 :=
    fun y => groupCohomology.H2π A (cast₂ (Function.surjInv hsurj' y))
  have F_add : ∀ y1 y2, F (y1 + y2) = F y1 + F y2 := by
    intro y1 y2
    show (⇑(groupCohomology.H2π B)) (cast₁ (Function.surjInv hsurj (y1 + y2))) =
      (⇑(groupCohomology.H2π B)) (cast₁ (Function.surjInv hsurj y1)) +
        (⇑(groupCohomology.H2π B)) (cast₁ (Function.surjInv hsurj y2))
    have key := hwd (Function.surjInv hsurj (y1 + y2))
      (Function.surjInv hsurj y1 + Function.surjInv hsurj y2) (by
        rw [map_add, Function.surjInv_eq hsurj y1, Function.surjInv_eq hsurj y2,
          Function.surjInv_eq hsurj (y1 + y2)])
    rw [key, cast₁_add, map_add]
  have F'_add : ∀ y1 y2, F' (y1 + y2) = F' y1 + F' y2 := by
    intro y1 y2
    show (⇑(groupCohomology.H2π A)) (cast₂ (Function.surjInv hsurj' (y1 + y2))) =
      (⇑(groupCohomology.H2π A)) (cast₂ (Function.surjInv hsurj' y1)) +
        (⇑(groupCohomology.H2π A)) (cast₂ (Function.surjInv hsurj' y2))
    have key := hwd' (Function.surjInv hsurj' (y1 + y2))
      (Function.surjInv hsurj' y1 + Function.surjInv hsurj' y2) (by
        rw [map_add, Function.surjInv_eq hsurj' y1, Function.surjInv_eq hsurj' y2,
          Function.surjInv_eq hsurj' (y1 + y2)])
    rw [key, cast₂_add, map_add]
  have F_left : Function.LeftInverse F' F := by
    intro y
    show (⇑(groupCohomology.H2π A)) (cast₂ (Function.surjInv hsurj' (F y))) = y
    have hx := Function.surjInv_eq hsurj' (F y)
    have h := hwd' (Function.surjInv hsurj' (F y)) (cast₁ (Function.surjInv hsurj y)) hx
    rw [h, hcomp, Function.surjInv_eq hsurj y]
  have F_right : Function.RightInverse F' F := by
    intro y
    show (⇑(groupCohomology.H2π B)) (cast₁ (Function.surjInv hsurj (F' y))) = y
    have hx := Function.surjInv_eq hsurj (F' y)
    have h := hwd (Function.surjInv hsurj (F' y)) (cast₂ (Function.surjInv hsurj' y)) hx
    rw [h, hcomp', Function.surjInv_eq hsurj' y]
  exact ⟨{ toFun := F, invFun := F', left_inv := F_left, right_inv := F_right, map_add' := F_add }⟩


/-- **The second cohomology of the Hasse–Brauer–Noether local units representation of the
stabiliser is the second cohomology of the local units representation of `NK.GlobalCFTdeep`.**

Both are representations of the same group (`MulAction.stabilizer` is
`NK.GlobalCFTdeep.decompositionSubgroup` definitionally) on the same module, with the same action,
and differ only in the bookkeeping of the coefficient ring (`ULift ℤ` versus `ℤ`); the general
transport lemma `Work.SSGRoute.h2_transport_rho_eq` (with `hasseUnitsRep_rho_eq`) relates them. -/
theorem eb_loc_h2_hasse (k K E : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [FiniteDimensional k K] [FiniteDimensional K E] [FiniteDimensional k E]
    [IsGalois k K] [IsGalois k E] [IsGalois K E]
    (ŵ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    Nonempty (groupCohomology (NK.HassePrinciple.localUnitsRep K E
        (NK.GlobalCFT.Place.ofFinite ŵ)) 2 ≃+
      groupCohomology (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := E)
        (NK.GlobalCFT.Place.ofFinite ŵ)) 2) :=
  h2_transport_rho_eq
    (A := NK.HassePrinciple.localUnitsRep K E (NK.GlobalCFT.Place.ofFinite ŵ))
    (B := NK.GlobalCFTdeep.localUnitsRep (K := K) (L := E)
      (NK.GlobalCFT.Place.ofFinite ŵ))
    (AddEquiv.refl _)
    (fun g x => NK.GlobalCFTdeep.hasseUnitsRep_rho_eq (K := K) (L := E)
      (NK.GlobalCFT.Place.ofFinite ŵ) g x)

/-- **The local class-formation data at a finite place, transported to the stabiliser.**

`Work.SSGRoute.EB_LocCard k K E ŵ` (see `Submission/Work/SSGRoute/E8Defs.lean`) unfolded: for
`k ⊆ K ⊆ E` finite Galois extensions of number fields and a finite place `ŵ` of `E`, with
`Γ := Stab_{Gal(E/K)}(Place.ofFinite ŵ)` acting on `E_ŵˣ` through
`NK.HassePrinciple.localUnitsRep K E (Place.ofFinite ŵ)` (the action of
`NK.HassePrinciple.localAutHom`):

* `Nat.card (H²(Γ, E_ŵˣ)) = Nat.card Γ`;
* `H²(Γ, E_ŵˣ)` has an element of order `Nat.card Γ`.

Route.  `Place.localField E (Place.ofFinite ŵ) = ŵ.adicCompletion E` holds by `rfl`, so the
coefficient module is `E_ŵˣ` with the `localAutHom` action of `Γ = Stab_{Gal(E/K)}(ŵ)`.

1. `eb_stab_eq_decomp` (`Submission/Work/SSGRoute/brauer_single_place.lean`) identifies `Γ` with
   `Commons…decompositionSubgroup (K := K) ŵ`; then
   `Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois`
   (with `letI := Commons…adicCompletionAlgebra W ŵ hW`, W the place of `K` under `ŵ`) gives
   `Γ ≃* (ŵ.adicCompletion E ≃ₐ[W.adicCompletion K] ŵ.adicCompletion E)`, whose cardinality is
   `Module.finrank (W.adicCompletion K) (ŵ.adicCompletion E)` by `IsGalois.card_aut_eq_finrank`
   (`eb_stab_card` records this).
2. `NK.HassePrinciple.localUnitsRep K E (Place.ofFinite ŵ)` is the restriction of scalars of
   `Rep.ofAlgebraAutOnUnits (W.adicCompletion K) (ŵ.adicCompletion E)` along that isomorphism (the
   actions agree by `NK.HassePrinciple.localAut_apply` /
   `NK.GlobalCFT.Galois.localRingEquiv_eq_cast_decompositionToAdicCompletion`).
3. Transport: `NK.NUV2.LC.nonempty_addEquiv_groupCohomology_res_mulEquiv` (group isomorphism) and
   the coefficient transfer `CoeffInt = ULift ℤ ↔ ℤ`
   (`NK.HassePrinciple.CoeffTransfer` /
   `NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer`, used exactly this way in
   `Submission/NK/NUV2/LC/unitsLevelH2_addOrderOf_realization.lean`).
4. Local inputs: `Commons…groupCohomology_two_units_ge_finrank`,
   `Commons…natCard_groupCohomology_two_units_le_finrank_of_solvable` (with
   `NK.NUV2.LC.isSolvable_algEquiv_local`), `Commons…exists_addOrderOf_eq_finrank_groupCohomology_two_units`,
   and the assembled unconditional forms
   `NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank`,
   `NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local`.
   A good template is `NK.NUV2.RouteC.h2_card_eq_card_of_abelian_local`. -/
theorem eb_loc_card (k K E : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [FiniteDimensional k K] [FiniteDimensional K E] [FiniteDimensional k E]
    [IsGalois k K] [IsGalois k E] [IsGalois K E]
    (ŵ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    Work.SSGRoute.EB_LocCard k K E ŵ := by
  classical
  let W : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    ⟨ŵ.asIdeal.under (NumberField.RingOfIntegers K), inferInstance,
      Ideal.under_ne_bot _ ŵ.ne_bot⟩
  have hW : ŵ.asIdeal.LiesOver W.asIdeal := ⟨rfl⟩
  letI hAlg : Algebra (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra W ŵ hW
  haveI hfd : FiniteDimensional (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion W ŵ hW
  haveI hgal : IsGalois (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion W ŵ hW
  haveI hfin : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := E)
      (NK.GlobalCFT.Place.ofFinite ŵ)) := Fintype.ofFinite _
  obtain ⟨t₁⟩ := eb_loc_h2_hasse k K E ŵ
  have hEq : NK.GlobalCFTdeep.localUnitsRep (K := K) (L := E) (NK.GlobalCFT.Place.ofFinite ŵ) =
      Rep.res (NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois W ŵ hW).toMonoidHom
        (Rep.ofAlgebraAutOnUnits (W.adicCompletion K) (ŵ.adicCompletion E)) :=
    NK.GlobalCFTdeep.localUnitsRep_eq_res (K := K) (L := E) W ŵ hW
  obtain ⟨h⟩ := NK.NUV2.LC.nonempty_addEquiv_groupCohomology_res_mulEquiv
    (A := Rep.ofAlgebraAutOnUnits (W.adicCompletion K) (ŵ.adicCompletion E))
    (e := NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois W ŵ hW) 2
  have t₂ : groupCohomology (NK.GlobalCFTdeep.localUnitsRep (K := K) (L := E)
        (NK.GlobalCFT.Place.ofFinite ŵ)) 2 ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits (W.adicCompletion K)
        (ŵ.adicCompletion E)) 2 := hEq ▸ h
  have hcard : Nat.card (MulAction.stabilizer (E ≃ₐ[K] E)
      (NK.GlobalCFT.Place.ofFinite ŵ)) =
      Module.finrank (W.adicCompletion K) (ŵ.adicCompletion E) :=
    eb_stab_card_aux k K E ŵ W hW
  have hlocal : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (W.adicCompletion K)
        (ŵ.adicCompletion E)) 2) =
      Module.finrank (W.adicCompletion K) (ŵ.adicCompletion E) :=
    NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank (K := K) (Q := W)
      (F := W.adicCompletion K) (E := ŵ.adicCompletion E)
  have hmain : Nat.card (groupCohomology (NK.HassePrinciple.localUnitsRep K E
      (NK.GlobalCFT.Place.ofFinite ŵ)) 2) =
      Nat.card (MulAction.stabilizer (E ≃ₐ[K] E) (NK.GlobalCFT.Place.ofFinite ŵ)) := by
    rw [Nat.card_congr (t₁.trans t₂).toEquiv, hlocal]
    exact hcard.symm
  refine ⟨hmain, ?_⟩
  obtain ⟨α, hα⟩ := NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local
    (K := K) (Q := W) (F := W.adicCompletion K) (E := ŵ.adicCompletion E)
  refine ⟨(t₁.trans t₂).symm α, ?_⟩
  rw [AddEquiv.addOrderOf_eq, hα]
  rw [hmain]
  exact hcard.symm

end Work.SSGRoute
