import Mathlib
import Submission.Work.SSGRoute.PTembedding.KummerMuDefs
import Submission.Work.SSGRoute.PT.KrullCorrespondence
import Submission.Work.SSGRoute.PT.Hilbert90IsAlgClosure
import Submission.Work.SSGRoute.PTembedding.mup_kummer_defs
import Submission.Work.SSGRoute.LTDDefs.DecompAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hilbert 90 for the decomposition group of a finite place
-/

open SSGRoute
open Work.SSGRoute
open Filter
open scoped Topology

namespace Work.SSGRoute.PTembedding.MupCard

set_option linter.style.haveILetI false

/-! ## Continuity of `fixingSubgroupEquiv` for an arbitrary intermediate field -/

section Continuity

variable {k Ω : Type} [Field k] [CharZero k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]

/-- **The isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)` is continuous** for an arbitrary
intermediate field `K` of an *algebraic* extension. -/
theorem continuous_fixingSubgroupEquiv_of_charZero (K : IntermediateField k Ω) :
    Continuous ((IntermediateField.fixingSubgroupEquiv K).toMonoidHom :
      ↥(K.fixingSubgroup) → (Ω ≃ₐ[↥K] Ω)) := by
  classical
  let f : ↥(K.fixingSubgroup) →* (Ω ≃ₐ[↥K] Ω) :=
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, f.map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff ↥K Ω] at hU
  obtain ⟨E, hEfin, hEU⟩ := hU
  haveI : FiniteDimensional ↥K ↥E := hEfin
  let b := Module.finBasis ↥K ↥E
  let s : Finset ↥E := Finset.univ.image b
  have hspan : Submodule.span ↥K (↑s : Set ↥E) = ⊤ := by
    rw [show (↑s : Set ↥E) = Set.range b by ext x; simp [s]]
    exact b.span_eq
  let S : Set Ω := (fun x : ↥E => (x : Ω)) '' (↑s : Set ↥E)
  let M : IntermediateField k Ω := IntermediateField.adjoin k S
  haveI hSfin : S.Finite := (s.finite_toSet).image (fun x : ↥E => (x : Ω))
  haveI : Finite S := hSfin
  haveI hMfin : FiniteDimensional k ↥M :=
    IntermediateField.finiteDimensional_adjoin (K := k) (S := S)
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  have hopen : IsOpen (M.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen M
  have hmem : (Subtype.val ⁻¹' (M.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)))
      ∈ 𝓝 (1 : ↥(K.fixingSubgroup)) :=
    (hopen.preimage continuous_subtype_val).mem_nhds (by simp)
  refine Filter.mem_of_superset hmem ?_
  intro σ hσ
  show f σ ∈ U
  apply hEU
  have hfix : ∀ y : ↥E, (f σ : Ω ≃ₐ[↥K] Ω) (y : Ω) = (y : Ω) := by
    intro y
    have hy : y ∈ Submodule.span ↥K (↑s : Set ↥E) := by rw [hspan]; trivial
    exact Submodule.span_induction
      (p := fun (y : ↥E) (_ : y ∈ Submodule.span ↥K (↑s : Set ↥E)) =>
        (f σ : Ω ≃ₐ[↥K] Ω) (y : Ω) = (y : Ω))
      (fun a ha => by
        have haS : (a : Ω) ∈ S := ⟨a, ha, rfl⟩
        have haM : (a : Ω) ∈ M := IntermediateField.subset_adjoin k S haS
        have hσa : (σ : Ω ≃ₐ[k] Ω) (a : Ω) = (a : Ω) :=
          (IntermediateField.mem_fixingSubgroup_iff M (σ : Ω ≃ₐ[k] Ω)).mp hσ (a : Ω) haM
        show (f σ : Ω ≃ₐ[↥K] Ω) (a : Ω) = (a : Ω)
        rw [show (f σ : Ω ≃ₐ[↥K] Ω) (a : Ω) = (σ : Ω ≃ₐ[k] Ω) (a : Ω) from rfl]
        exact hσa)
      (by simp)
      (fun a c _ _ ha hc => by
        show (f σ) ((a + c : ↥E) : Ω) = ((a + c : ↥E) : Ω)
        rw [show ((a + c : ↥E) : Ω) = (a : Ω) + (c : Ω) from rfl, map_add, ha, hc])
      (fun a c _ hc => by
        show (f σ) ((a • c : ↥E) : Ω) = ((a • c : ↥E) : Ω)
        rw [show ((a • c : ↥E) : Ω) = a • (c : Ω) from rfl, map_smul, hc])
      hy
  refine (IntermediateField.mem_fixingSubgroup_iff (K := E) (f σ)).mpr ?_
  intro x hx
  exact hfix ⟨x, hx⟩

end Continuity

/-! ## Hilbert 90 for the decomposition group -/

section Decomp

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **Hilbert 90 for the decomposition group** of a finite place: `H¹(D_A, Ωˣ) = 0`. -/
theorem hilbert90_decompH1
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (x : Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) : x = 0 := by
  let F₀ : IntermediateField k Ω := Work.SSGRoute.mup.decompField k Ω A
  have hL : F₀.fixingSubgroup = SSGRoute.decomp k A :=
    Work.SSGRoute.PTembedding.fixingSubgroup_decompField k Ω A
  haveI hAlgF : Algebra.IsAlgebraic ↥F₀ Ω :=
    Algebra.IsAlgebraic.tower_top (K := k) (L := ↥F₀) (A := Ω)
  haveI : IsAlgClosure ↥F₀ Ω :=
    ⟨IsAlgClosure.isAlgClosed k, hAlgF⟩
  haveI : IsGalois ↥F₀ Ω := IsAlgClosure.isGalois ↥F₀ Ω
  haveI : CharZero ↥F₀ := inferInstance
  haveI : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥F₀] Ω) (Additive (Units Ω))) :=
    ⟨fun a b => by
      rw [Work.SSGRoute.PT.hilbert90_H1_eq_zero_of_isAlgClosure ↥F₀ Ω a,
        Work.SSGRoute.PT.hilbert90_H1_eq_zero_of_isAlgClosure ↥F₀ Ω b]⟩
  haveI : CompactSpace ↥(F₀.fixingSubgroup) := by
    have hclosed : IsClosed ((F₀.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
      rw [hL]
      exact Work.SSGRoute.PTembedding.isClosed_decomp' k Ω A
    haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  haveI : T2Space (Ω ≃ₐ[↥F₀] Ω) := krullTopology_t2 (K := ↥F₀) (L := Ω)
  have hΦ : IsHomeomorph ((IntermediateField.fixingSubgroupEquiv F₀ :
      ↥(F₀.fixingSubgroup) → (Ω ≃ₐ[↥F₀] Ω))) :=
    (isHomeomorph_iff_continuous_bijective).mpr
      ⟨continuous_fixingSubgroupEquiv_of_charZero (k := k) (Ω := Ω) F₀,
        (IntermediateField.fixingSubgroupEquiv F₀).bijective⟩
  have h := Work.SSGRoute.PT.h1Transfer (G := Ω ≃ₐ[↥F₀] Ω) (G' := ↥(F₀.fixingSubgroup))
    (M := Additive (Units Ω)) (M' := Additive (Units Ω))
    (IntermediateField.fixingSubgroupEquiv F₀) hΦ (AddEquiv.refl (Additive (Units Ω)))
    (fun g' m' => rfl)
  have hsub : Subsingleton (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) :=
    hL ▸ (⟨fun a b => h.injective (Subsingleton.elim _ _)⟩ :
      Subsingleton (Work.AbsoluteKummer.H1 ↥(F₀.fixingSubgroup) (Additive (Units Ω))))
  exact hsub.elim x 0

end Decomp

end Work.SSGRoute.PTembedding.MupCard
