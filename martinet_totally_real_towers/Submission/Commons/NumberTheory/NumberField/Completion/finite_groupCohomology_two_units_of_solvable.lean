import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.NumberField.Completion

open CategoryTheory Representation

/-- A finite solvable group which is not cyclic has a nontrivial proper normal subgroup.  This is
the "peeling" step of the dévissage of the finiteness of `H²(Gal(E/B), Eˣ)` for solvable
`Gal(E/B)`: we cut `G` by a proper normal subgroup `H ≠ 1`, express the extension as `C/B` with
`C = E^H` (Galois group `G ⧸ H`) and `E/C` (Galois group `H`), and apply the induction hypothesis
to both — both groups being strictly smaller than `G`. -/
private lemma exists_nontrivial_proper_normal_of_solvable_not_isCyclic
    {G : Type} [Group G] [Finite G] [Group.IsSolvable G] (hG : ¬ IsCyclic G) :
    ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ ∧ H ≠ ⊤ := by
  by_cases hab : ∀ a b : G, a * b = b * a
  · haveI : IsMulCommutative G := IsMulCommutative.of_comm hab
    have hnt : Nontrivial G := by
      refine not_subsingleton_iff_nontrivial.mp ?_
      intro hsub
      haveI : Subsingleton G := hsub
      refine hG (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨1, ?_⟩)
      exact le_antisymm le_top (fun x _ => by
        rw [Subsingleton.elim x (1 : G)]; exact Subgroup.mem_zpowers 1)
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    refine ⟨Subgroup.zpowers g, Subgroup.normal_of_isMulCommutative _, ?_, ?_⟩
    · intro hbot
      exact hg (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers g))
    · intro htop
      exact hG (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, htop⟩)
  · haveI : Nontrivial G := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      exact hab fun a b => Subsingleton.elim _ _
    refine ⟨commutator G, inferInstance, ?_, ?_⟩
    · intro hbot
      exact hab (fun a b => ((commutator_eq_bot_iff G).mp hbot).is_comm.comm a b)
    · intro htop
      exact absurd htop (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial G))

/-- **Finiteness induction for the solvable case.**  For a finite solvable Galois group
`G = Gal(E/B)`, the group `H²(G, Eˣ)` is finite.  The proof is a strong induction on `|G|`:
* if `G` is cyclic, `H²(G, Eˣ) ≅ Bˣ ⧸ N_{E/B}(Eˣ)`, a quotient of `Bˣ` by a finite-index
  subgroup, hence finite;
* otherwise, `G` has a nontrivial proper normal subgroup `H`; put `C = E^H` and use the
  inflation–restriction exact sequence
  `H²(G ⧸ H, Cˣ) → H²(G, Eˣ) → H²(H, Eˣ)`,
  together with the induction hypothesis for the two smaller groups `G ⧸ H = Gal(C/B)` and
  `H = Gal(E/C)`. -/
private theorem p_fin {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ n : ℕ, ∀ {B E : Type} [Field B] [Field E]
      [instAlgB : Algebra (Q.adicCompletion K) B] [Algebra B E]
      [instAlgE : Algebra (Q.adicCompletion K) E]
      [IsScalarTower (Q.adicCompletion K) B E]
      [instFdB : FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
      [IsGalois B E],
      Group.IsSolvable (E ≃ₐ[B] E) → Nat.card (E ≃ₐ[B] E) = n →
      Finite (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B E hB hE hAlgB hAlgBE hAlgE hST hFdB hFdBE hGal hsolv hdeg
    haveI hGsolv : Group.IsSolvable (E ≃ₐ[B] E) := hsolv
    by_cases hcyc : IsCyclic (E ≃ₐ[B] E)
    · -- ### cyclic case
      haveI hCyc : IsCyclic (E ≃ₐ[B] E) := hcyc
      have hunits : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) =
          Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) :=
        Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_units_of_cyclic B E
      haveI hidx : (MonoidHom.range (Units.map (Algebra.norm B : E →* B))).FiniteIndex :=
        Commons.NumberTheory.NumberField.Completion.finiteIndex_range_norm_units_of_finiteDimensional
          (Q := Q)
      have hne : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2) ≠ 0 := by
        rw [hunits]
        exact Nat.card_ne_zero.mpr ⟨inferInstance, Subgroup.finite_quotient_of_finiteIndex⟩
      exact (Nat.card_ne_zero.mp hne).2
    · -- ### non-cyclic case: peel a nontrivial proper normal subgroup
      obtain ⟨H, hHnorm, hHne_bot, hHne_top⟩ :=
        exists_nontrivial_proper_normal_of_solvable_not_isCyclic hcyc
      haveI hHnorm' : H.Normal := hHnorm
      let C : IntermediateField B E := IntermediateField.fixedField H
      haveI hCgalB : IsGalois B ↥C := IsGalois.of_fixedField_normal_subgroup H
      haveI hCfdB : FiniteDimensional B ↥C := inferInstance
      haveI hIsGaloisCE : IsGalois ↥C E := inferInstance
      letI instAlgC : Algebra (Q.adicCompletion K) ↥C :=
        ((algebraMap B ↥C).comp (algebraMap (Q.adicCompletion K) B)).toAlgebra
      haveI instSTBC : IsScalarTower (Q.adicCompletion K) B ↥C :=
        IsScalarTower.of_algebraMap_eq (fun x => rfl)
      letI instModC : Module (Q.adicCompletion K) ↥C := instAlgC.toModule
      haveI instFdC : Module.Finite (Q.adicCompletion K) ↥C :=
        Module.Finite.trans (R := Q.adicCompletion K) B ↥C
      haveI instFdC' : FiniteDimensional (Q.adicCompletion K) ↥C := instFdC
      haveI instSTCE : IsScalarTower (Q.adicCompletion K) ↥C E :=
        IsScalarTower.of_algebraMap_eq (fun x => by
          rw [IsScalarTower.algebraMap_apply (Q.adicCompletion K) B E,
              IsScalarTower.algebraMap_apply B ↥C E]
          congr 1)
      -- ### the quotient `G ⧸ H` is nontrivial, hence `|G ⧸ H| < |G|`
      haveI : Nontrivial ((E ≃ₐ[B] E) ⧸ H) := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        haveI : Subsingleton ((E ≃ₐ[B] E) ⧸ H) := hsub
        have hGal : H = ⊤ := by
          rw [eq_top_iff]
          intro x
          have hh1 : (QuotientGroup.mk x : (E ≃ₐ[B] E) ⧸ H) = 1 := Subsingleton.elim _ _
          rw [QuotientGroup.eq_one_iff] at hh1
          simpa using hh1
        exact absurd hGal hHne_top
      have h1ltQ : 1 < Nat.card ((E ≃ₐ[B] E) ⧸ H) := by
        haveI : Fintype ((E ≃ₐ[B] E) ⧸ H) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      -- ### `|H| < |G|`
      have hltH : Nat.card ↥H < Nat.card (E ≃ₐ[B] E) := by
        rw [← Subgroup.card_mul_index H, Subgroup.index_eq_card]
        calc Nat.card ↥H = Nat.card ↥H * 1 := (Nat.mul_one _).symm
          _ < Nat.card ↥H * Nat.card ((E ≃ₐ[B] E) ⧸ H) :=
                Nat.mul_lt_mul_of_pos_left h1ltQ Nat.card_pos
      -- ### `|G ⧸ H| < |G|`
      have hltQ : Nat.card ((E ≃ₐ[B] E) ⧸ H) < Nat.card (E ≃ₐ[B] E) := by
        rw [← Subgroup.card_mul_index H, Subgroup.index_eq_card]
        haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHne_bot
        haveI : Fintype ↥H := Fintype.ofFinite _
        have hH2 : 1 < Nat.card ↥H := by
          rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
        calc Nat.card ((E ≃ₐ[B] E) ⧸ H) = 1 * Nat.card ((E ≃ₐ[B] E) ⧸ H) :=
              (Nat.one_mul _).symm
          _ < Nat.card ↥H * Nat.card ((E ≃ₐ[B] E) ⧸ H) :=
                Nat.mul_lt_mul_of_pos_right hH2 Nat.card_pos
      -- ### the two cardinality transfers
      have hcardE : Nat.card (E ≃ₐ[↥C] E) = Nat.card ↥H := by
        rw [IsGalois.card_aut_eq_finrank ↥C E, IntermediateField.finrank_fixedField_eq_card H]
      have hltCE : Nat.card (E ≃ₐ[↥C] E) < n := by
        rw [hcardE, ← hdeg]; exact hltH
      have hltCB : Nat.card (↥C ≃ₐ[B] ↥C) < n := by
        rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv, ← hdeg]
        exact hltQ
      -- ### solvability of the two subproblems
      haveI hCBsolv : Group.IsSolvable (↥C ≃ₐ[B] ↥C) :=
        Group.isSolvable_of_surjective (f := (IsGalois.normalAutEquivQuotient H).toMonoidHom)
          (IsGalois.normalAutEquivQuotient H).surjective
      haveI hCEsolv : Group.IsSolvable (E ≃ₐ[↥C] E) :=
        Group.isSolvable_of_surjective (f := (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom)
          (IntermediateField.subgroupEquivAlgEquiv H).surjective
      -- ### induction hypothesis on the two smaller extensions
      have hYfinCB : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥C) 2) :=
        ih (Nat.card (↥C ≃ₐ[B] ↥C)) hltCB hCBsolv rfl
      have hZfinCE : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits ↥C E) 2) :=
        ih (Nat.card (E ≃ₐ[↥C] E)) hltCE (instAlgB := instAlgC) (instFdB := instFdC') hCEsolv rfl
      -- ### the two identifications
      have hYeq : Nat.card (groupCohomology
            ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) =
          Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits B ↥C) 2) :=
        NatCardP9.natCard_groupCohomology_two_quotientToInvariants_units H
      have hZeq : Nat.card (groupCohomology
            (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) =
          Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits ↥C E) 2) :=
        NatCardP9.natCard_groupCohomology_two_res_units H
      haveI hYfin' : Finite (groupCohomology
          ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) := by
        have hne : Nat.card (groupCohomology
            ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2) ≠ 0 := by
          rw [hYeq]; exact Nat.card_ne_zero.mpr ⟨inferInstance, hYfinCB⟩
        exact (Nat.card_ne_zero.mp hne).2
      haveI hZfin' : Finite (groupCohomology
          (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) := by
        have hne : Nat.card (groupCohomology
            (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2) ≠ 0 := by
          rw [hZeq]; exact Nat.card_ne_zero.mpr ⟨inferInstance, hZfinCE⟩
        exact (Nat.card_ne_zero.mp hne).2
      haveI h1sub : Subsingleton
          (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 1) := by
        rw [NatCardP9.res_subtype_eq_res_subgroupEquivAlgEquiv H]
        exact (NatCardP9.subsingleton_groupCohomology_res_mulEquiv
          (IntermediateField.subgroupEquivAlgEquiv H)
          (Rep.ofAlgebraAutOnUnits ↥C E) 1).mpr inferInstance
      -- ### exactness and finiteness via range/ker
      let i : groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2 →ₗ[ℤ]
          groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2 :=
        ModuleCat.Hom.hom ((groupCohomology.infNatTrans ℤ H 2).app (Rep.ofAlgebraAutOnUnits B E))
      let r : groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2 →ₗ[ℤ]
          groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2 :=
        ModuleCat.Hom.hom ((groupCohomology.resNatTrans ℤ (G := H) (H := E ≃ₐ[B] E) H.subtype 2).app
          (Rep.ofAlgebraAutOnUnits B E))
      have hexact : LinearMap.range i = LinearMap.ker r :=
        Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
          H (Rep.ofAlgebraAutOnUnits B E) h1sub
      have hsurjrange : Function.Surjective
          (fun w : groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2 =>
            (⟨i w, ⟨w, rfl⟩⟩ : LinearMap.range i)) := by
        intro y
        obtain ⟨w, hw⟩ := y.2
        exact ⟨w, Subtype.ext hw⟩
      exact NatCardP9.finite_of_finite_range_ker r
        (Finite.of_injective
          (fun x : LinearMap.range r =>
            (x : groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits B E)) 2))
          Subtype.val_injective)
        (by rw [← hexact]; exact Finite.of_surjective _ hsurjrange)

theorem finite_groupCohomology_two_units_of_solvable
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F E : Type} [Field F] [Field E]
    [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) F E]
    [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
    [FiniteDimensional (Q.adicCompletion K) E]
    [IsGalois F E]
    (hsolv : Group.IsSolvable (E ≃ₐ[F] E)) :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) :=
  p_fin Q (Nat.card (E ≃ₐ[F] E)) hsolv rfl

end Commons.NumberTheory.NumberField.Completion
