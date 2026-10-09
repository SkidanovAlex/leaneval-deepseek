import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_finrank_of_abelian_local
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_cyclic_tower
import Submission.Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_mul_of_tower
import Submission.Commons.NumberTheory.NumberField.Completion.kernel_condition_of_cyclic_middle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

noncomputable section

universe u

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000



/-! ## Auxiliary instance lemmas for a middle field over an intermediate base

Let `F ⊆ B ⊆ E` be a tower of fields.  For a subgroup `H ≤ Gal(E/B)` and
`C = E^H : IntermediateField B E` the fixed field, we record two facts about the
`F`-algebra structure on `C` that are needed to feed `C` as the *base* of an induction:

* `IsScalarTower F ↥C E`;
* `IsGalois F ↥C`, provided `Gal(E/F)` is abelian (so that `H`, being a subgroup, is normal
  in `Gal(E/F)`, whence `E^H` is Galois over `F`).
-/

section InstanceLemmas

variable {F B E : Type*} [Field F] [Field B] [Field E]
  [Algebra F B] [Algebra B E] [Algebra F E] [IsScalarTower F B E]
  [FiniteDimensional F B] [FiniteDimensional B E] [FiniteDimensional F E]
  [IsGalois F B] [IsGalois B E] [IsGalois F E]

/-- The `F`-algebra structure on the fixed field `E^H` (`H ≤ Gal(E/B)`) is compatible with
the inclusion into `E`: `IsScalarTower F ↥(E^H) E`. -/
private lemma isScalarTower_fixedField (H : Subgroup (E ≃ₐ[B] E)) :
    let C : IntermediateField B E := IntermediateField.fixedField H
    IsScalarTower F ↥C E := by
  intro C
  refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
  rfl

/-- If `Gal(E/F)` is abelian then the fixed field `E^H` of any subgroup `H ≤ Gal(E/B)` is
Galois over `F`. -/
private lemma isGalois_fixedField_of_commutative
    (hcommF : ∀ a b : E ≃ₐ[F] E, a * b = b * a) (H : Subgroup (E ≃ₐ[B] E)) :
    let C : IntermediateField B E := IntermediateField.fixedField H
    IsGalois F ↥C := by
  intro C
  haveI : IsMulCommutative (E ≃ₐ[F] E) := IsMulCommutative.of_comm hcommF
  let H' : Subgroup (E ≃ₐ[F] E) := H.map (AlgEquiv.restrictScalarsHom F)
  have key1 : ∀ x : E, x ∈ (IntermediateField.fixedField H' : Set E) ↔ ∀ f ∈ H', f x = x :=
    fun x => IntermediateField.mem_fixedField_iff H' x
  have key2 : ∀ x : E, x ∈ (C : Set E) ↔ ∀ f ∈ H, f x = x :=
    fun x => IntermediateField.mem_fixedField_iff H x
  have hset : ((IntermediateField.fixedField H' : IntermediateField F E) : Set E) = (C : Set E) := by
    ext x
    rw [key1 x, key2 x]
    constructor
    · intro hx g hg
      exact hx ((AlgEquiv.restrictScalarsHom F) g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
    · intro hx g hg
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
      exact hx h hh
  let e : ↥(IntermediateField.fixedField H') ≃+* ↥C :=
    { toFun := fun x => ⟨x.1, by show (x : E) ∈ (C : Set E); rw [← hset]; exact x.2⟩
      invFun := fun x =>
        ⟨x.1, by
          show (x : E) ∈ ((IntermediateField.fixedField H' : IntermediateField F E) : Set E)
          rw [hset]; exact x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_mul' := fun x y => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  haveI hnorm : H'.Normal := Subgroup.normal_of_isMulCommutative H'
  refine IsGalois.of_equiv_equiv (F := F) (E := ↥(IntermediateField.fixedField H'))
    (M := F) (N := ↥C) (f := RingEquiv.refl F) (g := e) ?_
  ext x
  rfl

end InstanceLemmas

/-! ## The abelian local norm index theorem from the cyclic-middle kernel condition -/

/-- **Numerical (degree) form of the abelian local norm index theorem, conditional on the
`hcrux` condition restricted to *cyclic* middle extensions.**

`hcrux` asserts the tower kernel condition `ker N_{B₁/B} ≤ range N_{E/B₁}` only when the middle
extension `B₁/B` is cyclic.  The statement below computes, by strong induction on the local degree
`[E : B]`, the norm index `|Bˣ ⧸ N_{E/B}(Eˣ)| = [E : B]` for every finite abelian Galois extension
`E` of a finite Galois extension `B` of `F = Q.adicCompletion K`.

The induction peels a **maximal** subgroup `H < Gal(E/B)`: the intermediate field `C = E^H` then has
`C/B` cyclic of prime order (handled by the cyclic norm index theorem) while `E/C` is again abelian
of strictly smaller degree, so the induction hypothesis applies at the base `C`.  The tower kernel
condition for `B ⊆ C ⊆ E` is exactly what `hcrux` provides, since `C/B` is cyclic. -/
theorem normIndex_same_universe
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    :
    ∀ n : ℕ, ∀ (B : Type u) [Field B] [Algebra (Q.adicCompletion K) B]
      [FiniteDimensional (Q.adicCompletion K) B] [IsGalois (Q.adicCompletion K) B]
      (E : Type u) [Field E] [Algebra B E] [Algebra (Q.adicCompletion K) E]
      [IsScalarTower (Q.adicCompletion K) B E]
      [FiniteDimensional B E] [FiniteDimensional (Q.adicCompletion K) E]
      [IsGalois B E] [IsGalois (Q.adicCompletion K) E],
      (∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) →
      Module.finrank B E = n →
      Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
        Module.finrank B E := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B _ _ _ _ E _ _ _ _ _ _ _ _ hcommF hdeg
    let F := Q.adicCompletion K
    by_cases hnt : Nontrivial (E ≃ₐ[B] E)
    · -- ## The nontrivial case: peel a maximal subgroup
      haveI : IsMulCommutative (E ≃ₐ[B] E) :=
        IsMulCommutative.of_comm (fun a b => by
          apply AlgEquiv.restrictScalars_injective F
          change (AlgEquiv.restrictScalarsHom F) (a * b) =
            (AlgEquiv.restrictScalarsHom F) (b * a)
          rw [map_mul, map_mul]
          exact hcommF _ _)
      have hcommB : ∀ a b : E ≃ₐ[B] E, a * b = b * a := fun a b => by
        apply AlgEquiv.restrictScalars_injective F
        change (AlgEquiv.restrictScalarsHom F) (a * b) =
          (AlgEquiv.restrictScalarsHom F) (b * a)
        rw [map_mul, map_mul]
        exact hcommF _ _
      obtain ⟨H, hHlt, hHcyc⟩ := exists_maximal_subgroup_quotient_cyclic (E ≃ₐ[B] E)
      haveI hHnorm : H.Normal := Subgroup.normal_of_isMulCommutative H
      let C : IntermediateField B E := IntermediateField.fixedField H
      haveI hCgalB : IsGalois B C := IsGalois.of_fixedField_normal_subgroup H
      haveI hCfdB : FiniteDimensional B C := inferInstance
      haveI hCcyc : IsCyclic (C ≃ₐ[B] C) :=
        (IsGalois.normalAutEquivQuotient H).isCyclic.mp hHcyc
      -- the `F`-algebra structure on `C`
      haveI hScal : IsScalarTower F C E := isScalarTower_fixedField (F := F) (B := B) (E := E) H
      haveI hCfdF : FiniteDimensional F C := Module.Finite.trans (R := F) (A := B) (M := C)
      haveI hCgalF : IsGalois F C :=
        isGalois_fixedField_of_commutative (F := F) (B := B) (E := E) hcommF H
      -- the cyclic norm index theorem for `C / B`
      have hcycCase : Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : C →* B))) =
          Nat.card (C ≃ₐ[B] C) :=
        natCard_quotient_units_range_norm_eq_card_of_cyclic_tower (K := K) (Q := Q) (M := B) (E := C)
      -- the tower kernel condition, supplied by `hcrux`
      have hker_raw := kernel_condition_of_cyclic_middle (Q := Q) (B := B) (B₁ := C) (E := E) hcommB hCcyc
      have hker : ∀ m : Cˣ, Algebra.norm B (m : C) = 1 →
          ∃ w : Eˣ, Algebra.norm C (w : E) = (m : C) := by
        intro m hm
        have hmker : m ∈ MonoidHom.ker (Units.map (Algebra.norm B : C →* B)) := by
          rw [MonoidHom.mem_ker, Units.ext_iff]
          show (↑(Units.map (Algebra.norm B : C →* B) m) : B) = ↑(1 : Bˣ)
          simpa using hm
        obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (hker_raw hmker)
        exact ⟨w, by
          have hh : ((Units.map (Algebra.norm C : E →* C)) w : C) = (m : C) :=
            congrArg (fun u : Cˣ => (u : C)) hw
          simpa using hh⟩
      -- multiplicativity along `B ⊆ C ⊆ E`
      have hmul := Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_mul_of_tower
        (F := B) (M := C) (E := E) hker
      -- degree bookkeeping
      have hfinCE : Module.finrank C E = Nat.card H :=
        IntermediateField.finrank_fixedField_eq_card H
      have hcardGB : Nat.card (E ≃ₐ[B] E) = n := by
        rw [IsGalois.card_aut_eq_finrank B E, hdeg]
      haveI : Nontrivial ((E ≃ₐ[B] E) ⧸ H) := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        haveI : Subsingleton ((E ≃ₐ[B] E) ⧸ H) := hsub
        have hGal : H = ⊤ := by
          rw [eq_top_iff]
          intro x
          have h1 : (QuotientGroup.mk x : (E ≃ₐ[B] E) ⧸ H) = 1 := Subsingleton.elim _ _
          rw [QuotientGroup.eq_one_iff] at h1
          simpa using h1
        exact absurd hGal (ne_of_lt hHlt)
      have h1lt : 1 < Nat.card ((E ≃ₐ[B] E) ⧸ H) := by
        haveI : Finite ((E ≃ₐ[B] E) ⧸ H) := Quotient.finite _
        haveI : Fintype ((E ≃ₐ[B] E) ⧸ H) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      have hHlt_n : Nat.card H < n := by
        rw [← hcardGB, ← Subgroup.card_mul_index H, Subgroup.index_eq_card]
        calc Nat.card H = Nat.card H * 1 := (Nat.mul_one _).symm
          _ < Nat.card H * Nat.card ((E ≃ₐ[B] E) ⧸ H) :=
                Nat.mul_lt_mul_of_pos_left h1lt Nat.card_pos
      -- the induction hypothesis at the base `C`
      have hIH := ih (Nat.card H) hHlt_n C E hcommF hfinCE
      have hcardC : Nat.card (C ≃ₐ[B] C) = Nat.card ((E ≃ₐ[B] E) ⧸ H) :=
        (Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv).symm
      calc
        Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B)))
            = Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : C →* B))) *
                Nat.card (Cˣ ⧸ MonoidHom.range (Units.map (Algebra.norm C : E →* C))) := hmul
        _ = Nat.card (C ≃ₐ[B] C) *
                Nat.card (Cˣ ⧸ MonoidHom.range (Units.map (Algebra.norm C : E →* C))) := by
              rw [hcycCase]
        _ = Nat.card ((E ≃ₐ[B] E) ⧸ H) * Nat.card H := by rw [hcardC, hIH, hfinCE]
        _ = Nat.card (E ≃ₐ[B] E) := by
              rw [Nat.mul_comm, ← Subgroup.index_eq_card H, Subgroup.card_mul_index]
        _ = Module.finrank B E := IsGalois.card_aut_eq_finrank B E
    · -- ## The trivial case: `B = E`
      haveI : Subsingleton (E ≃ₐ[B] E) := not_nontrivial_iff_subsingleton.mp hnt
      have hcardG : Nat.card (E ≃ₐ[B] E) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      have hfin1 : Module.finrank B E = 1 := by
        rw [← IsGalois.card_aut_eq_finrank B E, hcardG]
      have hrange : MonoidHom.range (Units.map (Algebra.norm B : E →* B)) = ⊤ := by
        rw [eq_top_iff]
        rintro y -
        refine ⟨Units.map (algebraMap B E).toMonoidHom y, Units.ext ?_⟩
        show Algebra.norm B ((algebraMap B E) (y : B)) = (y : B)
        rw [Algebra.norm_algebraMap, hfin1, pow_one]
      have hq : Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) = 1 := by
        rw [hrange, ← Subgroup.index_eq_card (⊤ : Subgroup Bˣ), Subgroup.index_top]
      rw [hq, hfin1]


theorem le_natCard_quotient_units_range_norm_of_abelian_local
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (Q.adicCompletion K) E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois (Q.adicCompletion K) E]
    (hcomm : ∀ a b : E ≃ₐ[Q.adicCompletion K] E, a * b = b * a) :
    Module.finrank (Q.adicCompletion K) E ≤
      Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          E →* Q.adicCompletion K))) := by
  let F := Q.adicCompletion K
  suffices h : Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) =
      Nat.card (E ≃ₐ[F] E) by
    rw [h, IsGalois.card_aut_eq_finrank]
  by_cases hnt : Nontrivial (E ≃ₐ[F] E)
  · haveI : IsMulCommutative (E ≃ₐ[F] E) := IsMulCommutative.of_comm hcomm
    obtain ⟨H, hHlt, hHcyc⟩ := exists_maximal_subgroup_quotient_cyclic (E ≃ₐ[F] E)
    haveI hHnorm : H.Normal := Subgroup.normal_of_isMulCommutative H
    let C : IntermediateField F E := IntermediateField.fixedField H
    haveI hCgalF : IsGalois F C := IsGalois.of_fixedField_normal_subgroup H
    haveI hCcyc : IsCyclic (C ≃ₐ[F] C) :=
      (IsGalois.normalAutEquivQuotient H).isCyclic.mp hHcyc
    have hcycCase : Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : C →* F))) =
        Nat.card (C ≃ₐ[F] C) :=
      natCard_quotient_units_range_norm_eq_card_of_cyclic_tower (K := K) (Q := Q) (M := F) (E := C)
    have hker_raw := kernel_condition_of_cyclic_middle (Q := Q) (B := F) (B₁ := C) (E := E)
      hcomm hCcyc
    have hker : ∀ m : Cˣ, Algebra.norm F (m : C) = 1 →
        ∃ w : Eˣ, Algebra.norm C (w : E) = (m : C) := by
      intro m hm
      have hmker : m ∈ MonoidHom.ker (Units.map (Algebra.norm F : C →* F)) := by
        rw [MonoidHom.mem_ker, Units.ext_iff]
        show (↑(Units.map (Algebra.norm F : C →* F) m) : F) = ↑(1 : Fˣ)
        simpa using hm
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (hker_raw hmker)
      exact ⟨w, by
        have hh : ((Units.map (Algebra.norm C : E →* C)) w : C) = (m : C) :=
          congrArg (fun u : Cˣ => (u : C)) hw
        simpa using hh⟩
    have hmul := Commons.FieldTheory.Galois.natCard_quotient_units_range_norm_eq_mul_of_tower
      (F := F) (M := C) (E := E) hker
    have hIH : Nat.card (Cˣ ⧸ MonoidHom.range (Units.map (Algebra.norm C : E →* C))) =
        Module.finrank C E :=
      normIndex_same_universe (K := K) Q (Module.finrank C E) C E hcomm rfl
    have hcardC : Nat.card (C ≃ₐ[F] C) = Nat.card ((E ≃ₐ[F] E) ⧸ H) :=
      (Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv).symm
    have hfinCE : Module.finrank C E = Nat.card H :=
      IntermediateField.finrank_fixedField_eq_card H
    calc Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F)))
        = Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : C →* F))) *
            Nat.card (Cˣ ⧸ MonoidHom.range (Units.map (Algebra.norm C : E →* C))) := hmul
      _ = Nat.card (C ≃ₐ[F] C) *
            Nat.card (Cˣ ⧸ MonoidHom.range (Units.map (Algebra.norm C : E →* C))) := by
            rw [hcycCase]
      _ = Nat.card (C ≃ₐ[F] C) * Module.finrank C E := by rw [hIH]
      _ = Nat.card (C ≃ₐ[F] C) * Nat.card (E ≃ₐ[C] E) := by
            rw [IsGalois.card_aut_eq_finrank C E]
      _ = Nat.card ((E ≃ₐ[F] E) ⧸ H) * Nat.card H := by rw [hcardC, IsGalois.card_aut_eq_finrank C E, hfinCE]
      _ = Nat.card (E ≃ₐ[F] E) := by
            rw [Nat.mul_comm, ← Subgroup.index_eq_card H, Subgroup.card_mul_index]
  · haveI : Subsingleton (E ≃ₐ[F] E) := not_nontrivial_iff_subsingleton.mp hnt
    have hcardG : Nat.card (E ≃ₐ[F] E) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have hfin1 : Module.finrank F E = 1 := by
      rw [← IsGalois.card_aut_eq_finrank F E, hcardG]
    have hrange : MonoidHom.range (Units.map (Algebra.norm F : E →* F)) = ⊤ := by
      rw [eq_top_iff]
      rintro y -
      refine ⟨Units.map (algebraMap F E).toMonoidHom y, Units.ext ?_⟩
      show Algebra.norm F ((algebraMap F E) (y : F)) = (y : F)
      rw [Algebra.norm_algebraMap, hfin1, pow_one]
    have hq : Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) = 1 := by
      rw [hrange, ← Subgroup.index_eq_card (⊤ : Subgroup Fˣ), Subgroup.index_top]
    rw [hq, hcardG]

end Commons.NumberTheory.NumberField.Completion
