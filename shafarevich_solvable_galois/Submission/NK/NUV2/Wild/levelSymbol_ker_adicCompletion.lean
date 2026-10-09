import Mathlib
import Submission.NK.NUV2.RouteE.levelCompat
import Submission.NK.NUV2.RouteE.levelH2
import Submission.NK.NUV2.RouteF.transition
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup
import Submission.NK.LocalReciprocityLubinTate.GroupTheory.subgroup_eq_of_forall_map_eq_of_isCyclic_quotient
import Submission.Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_finrank_of_abelian_local
import Submission.Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_of_solvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# L7 at an arbitrary local level: the level symbol kills exactly the norms

For a finite Galois extension `E / F` of a nonarchimedean local field `F = Q.adicCompletion K`
(with commutative Galois group) and a *fundamental class* `u ∈ H²(Gal(E/F), Eˣ)` (an element of
additive order the order of the cyclic group `H²`), the level symbol
`NK.NUV2.RouteE.levelSymbol hcomm u hu : Fˣ →* Gal(E/F)` satisfies

`ker θ = N_{E/F} Eˣ` and `θ` is surjective.

The proof reduces the surjectivity to the **cyclic** case (already established for an arbitrary
finite Galois extension with cyclic Galois group) by the group-theoretic lemma that a proper
subgroup of a finite abelian group is separated from an element outside it by a cyclic quotient:
if `H = range θ ≠ ⊤`, choose `K ≥ H` with `K ≠ ⊤` and `Gal(E/F) ⧸ K` cyclic.  The fixed field
`C = E^K` has cyclic Galois group over `F`, the level inflation
`NK.NUV2.RouteF.transition_generator` provides a compatible fundamental class `v` at `C`, and the
compatibility `NK.NUV2.RouteE.levelSymbol_restrict` shows that the level symbol at `C` is trivial.
The cyclic case then gives `N_{C/F} Cˣ = Fˣ`, contradicting the norm index theorem
`Nat.card (Fˣ ⧸ N_{C/F} Cˣ) = [C : F] = |Gal(E/F) ⧸ K| > 1`.

The kernel is then pinned down by the norm index theorem together with the surjectivity.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory

namespace NK.NUV2.Wild

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E] [Fintype (E ≃ₐ[F] E)]
  [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)]

/-- **Step 0**: the norm group lies in the kernel of the level symbol. -/
theorem normGroup_le_ker_levelSymbol
    (hcomm : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) :
    NK.LocalReciprocity.normGroup F E
      ≤ MonoidHom.ker (NK.NUV2.RouteE.levelSymbol (F := F) (E := E) hcomm u hu) := by
  intro a ha
  rw [MonoidHom.mem_ker]
  apply NK.NUV2.RouteE.doubleDual_injective hcomm
  intro χ
  rw [NK.NUV2.RouteE.levelSymbol_apply]
  have key : NK.NUV2.RouteC.invariantOf u hu
      ((groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ)) = 0 := by
    refine (congrArg (NK.NUV2.RouteC.invariantOf u hu) ?_).trans (map_zero _)
    exact NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup (F := F) (E := E) χ a ha
  exact key.trans (by simp)

end General

section CyclicCase

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E] [Fintype (E ≃ₐ[F] E)]
  [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)]

/-- A faithful character of a finite cyclic group: the invariant of a generator, viewed as a
`ℚ/ℤ`-valued character, has additive order the cardinality of the group. -/
theorem addOrderOf_invariantOf_of_generator {G : Type} [CommGroup G] [Finite G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hgord : addOrderOf (Additive.ofMul g) = Nat.card (Additive G)) :
    addOrderOf (NK.NUV2.RouteC.invariantOf (Additive.ofMul g) hgord) = Nat.card G := by
  have hn0 : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  rw [NK.NUV2.RouteC.addOrderOf_addMonoidHom_eq_of_generator g hg,
    NK.NUV2.RouteC.invariantOf_generator (Additive.ofMul g) hgord]
  have hcard : Nat.card (Additive G) = Nat.card G := Nat.card_congr (Additive.ofMul)
  rw [hcard, ← NK.NUV2.RouteC.zmodToQmodZ_one (Nat.card G),
    NK.NUV2.RouteC.addOrderOf_zmodToQmodZ hn0, ZMod.addOrderOf_one]

/-- **The level symbol of a cyclic level kills exactly the norms.** -/
theorem levelSymbol_ker_of_isCyclic
    (hcomm : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ) (hcyc : IsCyclic (E ≃ₐ[F] E))
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) :
    MonoidHom.ker (NK.NUV2.RouteE.levelSymbol (F := F) (E := E) hcomm u hu)
      = NK.LocalReciprocity.normGroup F E := by
  classical
  letI : CommGroup (E ≃ₐ[F] E) := { (inferInstance : Group (E ≃ₐ[F] E)) with mul_comm := hcomm }
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  have hgord : addOrderOf (Additive.ofMul g) = Nat.card (Additive (E ≃ₐ[F] E)) := by
    rw [addOrderOf_ofMul_eq_orderOf]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  let χ : Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ :=
    NK.NUV2.RouteC.invariantOf (Additive.ofMul g) hgord
  have hχ : addOrderOf χ = Nat.card (E ≃ₐ[F] E) :=
    addOrderOf_invariantOf_of_generator g hg hgord
  refine le_antisymm ?_ (normGroup_le_ker_levelSymbol hcomm u hu)
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have h1 : χ (Additive.ofMul
      (NK.NUV2.RouteE.levelSymbol (F := F) (E := E) hcomm u hu a)) = 0 := by
    rw [ha]
    exact map_zero χ
  rw [NK.NUV2.RouteE.levelSymbol_apply] at h1
  have h2 : (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
      (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2)
      (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ) = 0 := by
    have h1' : NK.NUV2.RouteC.invariantOf u hu
        ((groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
          (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2)
          (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ)) = 0 := h1
    refine NK.NUV2.RouteC.invariantOf_injective u hu ?_
    rw [h1', map_zero]
  have h3 := (NK.NUV2.RouteC.map_powHom_eq_zero_iff_of_isCyclic hcyc χ hχ a).mp h2
  rwa [NK.LocalReciprocity.normGroup_eq_range]

end CyclicCase

section Adic

/-- **Surjectivity of the level symbol at a local level.**  The level symbol of a fundamental class
at a finite Galois level of `Q.adicCompletion K` (with commutative Galois group) is surjective. -/
theorem levelSymbol_surjective_adicCompletion
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    [Fintype (E ≃ₐ[Q.adicCompletion K] E)]
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)]
    (hcomm : ∀ σ τ : E ≃ₐ[Q.adicCompletion K] E, σ * τ = τ * σ)
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology
      (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)) :
    Function.Surjective
      (NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := E) hcomm u hu) := by
  classical
  set θ := NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := E) hcomm u hu with hθ
  have hcardE : Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)
      = Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
    rw [(NK.NUV2.RouteE.h2_cyclic_level (Q := Q) (F := Q.adicCompletion K)
        (E := E) hcomm).1, IsGalois.card_aut_eq_finrank]
  by_contra hsurj
  have hHne : MonoidHom.range θ ≠ ⊤ := fun h => hsurj (MonoidHom.range_eq_top.mp h)
  haveI : Finite (E ≃ₐ[Q.adicCompletion K] E) := Fintype.finite inferInstance
  letI : CommGroup (E ≃ₐ[Q.adicCompletion K] E) :=
    { (inferInstance : Group (E ≃ₐ[Q.adicCompletion K] E)) with mul_comm := hcomm }
  obtain ⟨g, -, hgH⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hHne)
  obtain ⟨Ksub, hHK, hKcyc, hgK⟩ :=
    NK.LocalReciprocityLubinTate.GroupTheory.exists_isCyclic_quotient_not_mem
      (MonoidHom.range θ) hgH
  have hKne : Ksub ≠ ⊤ := fun h => hgK (h ▸ Subgroup.mem_top g)
  haveI hKnormal : Ksub.Normal := Subgroup.normal_of_comm Ksub
  -- the level fixed by `Ksub`
  let C : IntermediateField (Q.adicCompletion K) E := IntermediateField.fixedField Ksub
  have hCfix : C.fixingSubgroup = Ksub := IntermediateField.fixingSubgroup_fixedField Ksub
  haveI hgalC : IsGalois (Q.adicCompletion K) ↥C := IsGalois.of_fixedField_normal_subgroup Ksub
  haveI hfintC : Fintype (↥C ≃ₐ[Q.adicCompletion K] ↥C) := AlgEquiv.fintype _ _
  have hcommC : ∀ σ τ : ↥C ≃ₐ[Q.adicCompletion K] ↥C, σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := Q.adicCompletion K)
      (K₁ := ↥C) E σ
    obtain ⟨t, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := Q.adicCompletion K)
      (K₁ := ↥C) E τ
    rw [← map_mul, ← map_mul, hcomm s t]
  haveI hfinC : Finite (groupCohomology
      (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2) :=
    Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_of_solvable
      (Q := Q) (F := Q.adicCompletion K) (E := ↥C) (Group.isSolvable_of_comm hcommC)
  have hcardC : Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2) = Ksub.index := by
    rw [(NK.NUV2.RouteE.h2_cyclic_level (Q := Q) (F := Q.adicCompletion K)
        (E := ↥C) hcommC).1,
      IntermediateField.finrank_eq_fixingSubgroup_index E C, hCfix]
  obtain ⟨v, hvord, hvmap⟩ := NK.NUV2.RouteF.transition_generator (F := Q.adicCompletion K)
    (L := E) Ksub (inferInstance : Finite (groupCohomology
      (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)) hcardE u hu hcardC
  have hdvd : Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2)
      ∣ Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2) := by
    rw [hcardC, hcardE]
    exact Subgroup.index_dvd_card Ksub
  have hden : Nat.card (E ≃ₐ[Q.adicCompletion K] E) / Ksub.index
      = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)
        / Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2) := by
    rw [← hcardE, ← hcardC]
  have hcoh : (NK.NUV2.RouteC.levelInfMap (F := Q.adicCompletion K) (M := ↥C) (L := E)) v
      = ((Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)
          / Nat.card (groupCohomology
            (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2) : ℕ) : ℤ) • u :=
    calc (NK.NUV2.RouteC.levelInfMap (F := Q.adicCompletion K) (M := ↥C) (L := E)) v
        = (NK.NUV2.RouteD.levelInfMap (F := Q.adicCompletion K) (M := ↥C) (L := E)) v := rfl
      _ = ((Nat.card (E ≃ₐ[Q.adicCompletion K] E) / Ksub.index : ℕ) : ℤ) • u := hvmap
      _ = ((Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)
          / Nat.card (groupCohomology
            (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥C) 2) : ℕ) : ℤ) • u := by
          rw [hden]
  -- compatibility of the level symbols at `E` and at `C`
  have hres : ∀ a : (Q.adicCompletion K)ˣ,
      (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K) (K₁ := E) (E := ↥C)) (θ a)
        = NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := ↥C) hcommC v hvord a := by
    intro a
    rw [hθ]
    exact NK.NUV2.RouteE.levelSymbol_restrict (F := Q.adicCompletion K) (M := ↥C) (L := E)
      hcommC hcomm v hvord u hu hdvd hcoh a
  -- the level symbol at `C` is trivial, because its values are restrictions of values of `θ`
  -- which lie in `Ksub = ker (restrictNormalHom)`
  have hθC : NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := ↥C) hcommC v hvord
      = 1 := by
    have hkerRE : (AlgEquiv.restrictNormalHom (F := Q.adicCompletion K) (K₁ := E)
        (E := ↥C)).ker = Ksub := by
      rw [IntermediateField.restrictNormalHom_ker, hCfix]
    refine MonoidHom.ext (fun a => ?_)
    rw [← hres a]
    exact MonoidHom.mem_ker.mp (hkerRE.symm ▸ hHK ⟨a, rfl⟩)
  have hkerC : MonoidHom.ker
      (NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := ↥C) hcommC v hvord)
      = ⊤ := by
    rw [MonoidHom.ker_eq_top_iff]
    exact hθC
  have hcycC : IsCyclic (↥C ≃ₐ[Q.adicCompletion K] ↥C) :=
    (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient (K := Q.adicCompletion K)
      (L := E) Ksub)).mp hKcyc
  have hnormTop : NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥C = ⊤ := by
    rw [← levelSymbol_ker_of_isCyclic (F := Q.adicCompletion K) (E := ↥C) hcommC hcycC v hvord]
    exact hkerC
  -- the norm index theorem at the level `C` contradicts `Ksub ≠ ⊤`
  have hnormC : Nat.card ((Q.adicCompletion K)ˣ ⧸
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥C)
      = Module.finrank (Q.adicCompletion K) ↥C := by
    rw [NK.LocalReciprocity.normGroup_eq_range]
    exact Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_finrank_of_abelian_local
      (Q := Q) (E := ↥C) hcommC
  have hone : Nat.card ((Q.adicCompletion K)ˣ ⧸
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥C) = 1 := by
    rw [← Subgroup.index_eq_card, hnormTop, Subgroup.index_top]
  have hfinC : Module.finrank (Q.adicCompletion K) ↥C = Ksub.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index E C, hCfix]
  have hKidx : Ksub.index = 1 := by
    rw [← hfinC, ← hnormC]
    exact hone
  exact hKne (Subgroup.index_eq_one.mp hKidx)

end Adic

theorem levelSymbol_ker_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    [Fintype (E ≃ₐ[Q.adicCompletion K] E)]
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)]
    (hcomm : ∀ σ τ : E ≃ₐ[Q.adicCompletion K] E, σ * τ = τ * σ)
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) E) 2)) :
    MonoidHom.ker (NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := E) hcomm u hu)
        = NK.LocalReciprocity.normGroup (Q.adicCompletion K) E ∧
      Function.Surjective
        (NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := E) hcomm u hu) := by
  classical
  set θ := NK.NUV2.RouteE.levelSymbol (F := Q.adicCompletion K) (E := E) hcomm u hu with hθ
  have hnorm_le : NK.LocalReciprocity.normGroup (Q.adicCompletion K) E ≤ MonoidHom.ker θ := by
    rw [hθ]
    exact normGroup_le_ker_levelSymbol (F := Q.adicCompletion K) (E := E) hcomm u hu
  have hsurj : Function.Surjective θ := by
    rw [hθ]
    exact levelSymbol_surjective_adicCompletion (Q := Q) hcomm u hu
  refine ⟨le_antisymm ?_ hnorm_le, hsurj⟩
  have hKidx : (MonoidHom.ker θ).index = Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
    rw [Subgroup.index_eq_card]
    calc Nat.card ((Q.adicCompletion K)ˣ ⧸ MonoidHom.ker θ)
        = Nat.card (↥(MonoidHom.range θ)) :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
      _ = Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
          rw [MonoidHom.range_eq_top.mpr hsurj]
          exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hNidx : (NK.LocalReciprocity.normGroup (Q.adicCompletion K) E).index
      = Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
    rw [Subgroup.index_eq_card, NK.LocalReciprocity.normGroup_eq_range,
      Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_finrank_of_abelian_local
        (Q := Q) (E := E) hcomm]
    exact (IsGalois.card_aut_eq_finrank (Q.adicCompletion K) E).symm
  have hrel : (NK.LocalReciprocity.normGroup (Q.adicCompletion K) E).relIndex
      (MonoidHom.ker θ) = 1 := by
    have h := Subgroup.relIndex_mul_index
      (H := NK.LocalReciprocity.normGroup (Q.adicCompletion K) E) (K := MonoidHom.ker θ) hnorm_le
    rw [hKidx, hNidx] at h
    have hm : 0 < Nat.card (E ≃ₐ[Q.adicCompletion K] E) := by
      haveI : Nonempty (E ≃ₐ[Q.adicCompletion K] E) := ⟨AlgEquiv.refl⟩
      exact Nat.card_pos
    exact Nat.mul_right_cancel hm (by rw [h, one_mul])
  intro x hx
  exact (Subgroup.relIndex_eq_one.mp hrel) hx

end NK.NUV2.Wild
