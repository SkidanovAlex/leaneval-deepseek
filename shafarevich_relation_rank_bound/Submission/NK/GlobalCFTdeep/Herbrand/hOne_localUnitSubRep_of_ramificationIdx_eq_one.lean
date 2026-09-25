import Mathlib
import Submission.NK.GlobalCFTdeep.Shared

/-!
# `Ĥ¹(𝒪_qˣ) = 0` for an unramified local extension

For a finite Galois extension `L / K` of number fields with cyclic Galois group, a finite place
`q` of `L` lying over the finite place `Q` of `K` with **ramification index one** (i.e. the local
extension `L_q / K_Q` is unramified), the first Tate cohomology of the local units `𝒪_qˣ`, viewed
as a `ℤ[D_q]`-module for the decomposition group `D_q`, vanishes:

  `hOne (localUnitSubRep (Place.ofFinite q)) = 1`,   i.e.  `|Ĥ¹(D_q, 𝒪_qˣ)| = 1`.

## Proof

Herbrand's theorem for the local units
(`NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitSubRep_ofFinite`) gives `|Ĥ⁰| = |Ĥ¹|`, so it
suffices to prove `|Ĥ⁰(D_q, 𝒪_qˣ)| = 1`.

This is proved for the local Galois representation `𝒪_qˣ` of `Γ = Gal(L_q/K_Q)`
(`Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep`): for an unramified extension,
every `Γ`-invariant unit of `𝒪_q` is a norm
(`Commons.NumberTheory.NumberField.Completion.geMem_range_norm_of_mem_invariants`), whence the
quotient `invariants ⧸ range norm` is trivial and `Ĥ⁰ = 0`
(`tateCohomology_zero_iso`).  The statement is transported to `D_q` along
`NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois` and the identification
`localUnitSubRep ≅ res (geIntegersUnitsRep)` (`localUnitSubRepIsoGeIntegersUnitsRep`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open scoped NumberField
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Step 1: `Ĥ⁰` of the local Galois representation on the units of the ring of integers -/

/-- **`Ĥ⁰` of the local units of the ring of integers vanishes for an unramified extension.**
For an arbitrary `Fintype` instance `A` on the local Galois group `Γ = Gal(L_q/K_Q)`, the zeroth
Tate cohomology of `𝒪_qˣ` (with the natural `Γ`-action) is trivial. -/
theorem natCard_tateCohomology_zero_geIntegersUnitsRep_of_ramificationIdx_eq_one
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (A : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) :
    Nat.card (@tateCohomology ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) _ _
      A (Rep.of (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)) 0) = 1 := by
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  -- every invariant unit is a norm, for the `Fintype` instance used by the library lemma
  obtain ⟨B, htop⟩ : ∃ B : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      (LinearMap.range (@Representation.norm ℤ _ _ _ _ B _ _
        (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq))).comap
        (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq).invariants.subtype
        = ⊤ :=
    ⟨_, by
      rw [Submodule.eq_top_iff']
      intro v
      rw [Submodule.mem_comap]
      simpa using
        Commons.NumberTheory.NumberField.Completion.geMem_range_norm_of_mem_invariants Q q hq hunr
          (Additive.toMul v.1) (by simpa using v.2)⟩
  have hcardB : Nat.card (@tateCohomology ℤ _
      _ _ B (Rep.of (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)) 0) = 1 := by
    obtain ⟨e⟩ := @Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso _ _ _ B _ _
      (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)
    haveI : Subsingleton
        ((Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq).invariants ⧸
          (LinearMap.range (@Representation.norm ℤ _ _ _ _ B _ _
            (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq))).comap
            (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq).invariants.subtype) := by
      rw [htop]; infer_instance
    haveI : Subsingleton (@tateCohomology ℤ _ _ _
        B (Rep.of (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)) 0) :=
      ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
    exact Nat.card_unique
  rw [NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_zero_eq_of_fintype_eq A B
    (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)]
  exact hcardB

/-! ## Step 2: the intertwining between the local action and the Galois action -/

/-- **The action of the decomposition group on the local units is the Galois action.**  Under the
equivalence `↥S.units ≃ Sˣ` between the units of `L_q` lying in `𝒪_q` and the units of `𝒪_q`,
the action of `σ ∈ D_q` on `𝒪_qˣ` corresponds to the action of the local Galois automorphism
`decompositionSubgroupIsoLocalGalois Q q hq σ`.

Both actions act on the underlying element of `L_q` by the *same* ring automorphism: the local
action of `σ` is `decompositionToAdicCompletion`
(`localAction_eq_decompositionToAdicCompletion`), which is also
`decompositionSubgroupIsoLocalGalois σ`.  Stating the goal directly in terms of
`localField L (Place.ofFinite q)` before rewriting spares the elaborator from having to unfold the
semireducible definition `localUnitSubRep` during rewriting. -/
theorem unitsEquivUnitsType_geIntegersUnitsRep
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (σ : decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))
    (u : ↥(Place.localUnits L (Place.ofFinite q))) :
    (Submonoid.unitsEquivUnitsType ((q.adicCompletionIntegers L).toSubmonoid))
        (Additive.toMul ((localUnitSubRep (K := K) (L := L) (Place.ofFinite q)).ρ σ
          (Additive.ofMul u)))
      = Additive.toMul
          ((Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)
            (decompositionSubgroupIsoLocalGalois Q q hq σ)
            (Additive.ofMul
              (Submonoid.unitsEquivUnitsType ((q.adicCompletionIntegers L).toSubmonoid) u))) := by
  apply Units.ext
  apply Subtype.ext
  show (NK.GlobalCFT.Inclusion.Place.localAction σ.1 (Place.ofFinite q) σ.2)
        ((u : (Place.localField L (Place.ofFinite q))ˣ) : Place.localField L (Place.ofFinite q))
      = ((decompositionSubgroupIsoLocalGalois Q q hq σ).toRingEquiv)
        ((u : (Place.localField L (Place.ofFinite q))ˣ) : Place.localField L (Place.ofFinite q))
  rw [NK.GlobalCFTdeep.localAction_eq_decompositionToAdicCompletion (K := K) (L := L) q σ.1 σ.2,
    NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois_apply (K := K) (L := L) Q q hq σ]

/-! ## Step 3: the identification of `localUnitSubRep` with the restriction of `geIntegersUnitsRep` -/

/-- **The local units representation of the decomposition group is the restriction of the local
Galois representation on `𝒪_qˣ` along `D_q ≃* Gal(L_q/K_Q)`.** -/
noncomputable def localUnitSubRepIsoGeIntegersUnitsRep
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    localUnitSubRep (K := K) (L := L) (Place.ofFinite q) ≅
      Rep.res (decompositionSubgroupIsoLocalGalois Q q hq).toMonoidHom
        (Rep.of (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)) := by
  let f : Additive ↥(Place.localUnits L (Place.ofFinite q)) ≃ₗ[ℤ]
      Additive ((↥(q.adicCompletionIntegers L))ˣ) :=
    AddEquiv.toIntLinearEquiv (MulEquiv.toAdditive
      (Submonoid.unitsEquivUnitsType ((q.adicCompletionIntegers L).toSubmonoid)))
  refine Rep.mkIso (ρ := (localUnitSubRep (K := K) (L := L) (Place.ofFinite q)).ρ)
    (σ := (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq).comp
      (decompositionSubgroupIsoLocalGalois Q q hq).toMonoidHom)
    (Representation.Equiv.mk f ?_)
  intro σ
  apply LinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
  show Additive.ofMul
        ((Submonoid.unitsEquivUnitsType ((q.adicCompletionIntegers L).toSubmonoid))
          (Additive.toMul ((localUnitSubRep (K := K) (L := L) (Place.ofFinite q)).ρ σ
            (Additive.ofMul u))))
      = Additive.ofMul (Additive.toMul
          ((Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)
            (decompositionSubgroupIsoLocalGalois Q q hq σ)
            (Additive.ofMul
              (Submonoid.unitsEquivUnitsType ((q.adicCompletionIntegers L).toSubmonoid) u))))
  exact congrArg Additive.ofMul (unitsEquivUnitsType_geIntegersUnitsRep Q q hq σ u)

/-! ## Step 4: `Ĥ⁰` of the local units of the decomposition group -/

/-- **`Ĥ⁰(D_q, 𝒪_qˣ) = 0` for an unramified place.** -/
theorem hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    [Fintype (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    hZero (localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) = 1 := by
  haveI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    Fintype.ofEquiv (decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))
      (decompositionSubgroupIsoLocalGalois Q q hq).toEquiv
  rw [NK.GlobalCFTdeep.hZero_def]
  calc Nat.card (tateCohomology (localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) 0)
      = Nat.card (tateCohomology
          (Rep.res (decompositionSubgroupIsoLocalGalois Q q hq).toMonoidHom
            (Rep.of (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq))) 0) :=
        NK.GlobalCFTdeep.Herbrand.hZero_congr
          (localUnitSubRepIsoGeIntegersUnitsRep Q q hq)
    _ = Nat.card (tateCohomology
          (Rep.of (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)) 0) :=
        NK.GlobalCFTdeep.natCard_tateCohomology_zero_of_mulEquiv_res
          (decompositionSubgroupIsoLocalGalois Q q hq)
          (Commons.NumberTheory.NumberField.Completion.geIntegersUnitsRep Q q hq)
    _ = 1 :=
        natCard_tateCohomology_zero_geIntegersUnitsRep_of_ramificationIdx_eq_one Q q hq hunr _

/-! ## Step 5: the main theorem -/

/-- **`Ĥ¹` of the local units vanishes for an unramified place.**  For an unramified finite place
`q` of `L` above `Q`, the first Tate cohomology of `𝒪_qˣ` for the decomposition group `D_q`
is trivial. -/
theorem hOne_localUnitSubRep_of_ramificationIdx_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [q.asIdeal.LiesOver Q.asIdeal]
    [Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))]
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) = 1 := by
  have herb : hZero (localUnitSubRep (K := K) (L := L) (Place.ofFinite q))
      = 1 * hOne (localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) :=
    herbrandEq_localUnitSubRep_ofFinite Q q
  have h0 : hZero (localUnitSubRep (K := K) (L := L) (Place.ofFinite q)) = 1 :=
    hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one Q q
      (inferInstance : q.asIdeal.LiesOver Q.asIdeal) hunr
  rw [h0, one_mul] at herb
  exact herb.symm

end NK.GlobalCFTdeep.Herbrand

end
