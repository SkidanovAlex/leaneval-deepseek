import Submission.Work.SSGRoute.ZSplit.InductionStep
import Submission.Work.SSGRoute.PT.vanishingInertia_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary constructions for the codimension-one induction step

* `Work.SSGRoute.IsYRealisation.congr_datum`: the realisation predicate only sees the prescribed
  datum at the places of `T`, so the datum may be replaced by any function agreeing with it there.
* `Work.SSGRoute.exists_normal_fixingSubgroup_vanishing`: every class which is additive and locally
  constant on `G_K` vanishes on the fixing subgroup of a finite normal extension of `k` (the field
  "cut out" by the class, in the form in which the induction of Schmidt--Wingberg §4 uses it).
* `Work.SSGRoute.exists_auxiliary_placeSet`: a finite set of representatives of the conjugacy
  classes of the places of a given finite set `S` together with the places ramified in a finite
  normal extension `L|k` (the set `T₀ = T ∪ Ram(L|k)` of the paper).
* `Work.SSGRoute.exists_linearFunctional_finrank_ker`: for a finite `𝔽_p`-vector space of dimension
  `≥ 2`, a linear functional with a prescribed value at a nonzero vector and whose kernel has
  dimension `= dim E - 1`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The realisation predicate only sees the datum at the places of `T`.** -/
theorem IsYRealisation.congr_datum {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K Λ : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f f' : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p} {ytilde : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f ytilde)
    (hf : ∀ A : ValuationSubring Ω, (∃ A' ∈ T, IsConjPlace k A' A) → f A = f' A) :
    IsYRealisation p K Λ T S₀ f' ytilde := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, ?_, h4, h5, h6⟩
  intro A hA
  rw [← hf A hA]
  exact h3 A hA

/-- **The field cut out by an additive, locally constant class.** -/
theorem exists_normal_fixingSubgroup_vanishing (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [Normal k K]
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (z : (Ω ≃ₐ[k] Ω) → E)
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ Normal k L ∧
      ∀ σ ∈ L.fixingSubgroup, z σ = 0 := by
  classical
  obtain ⟨U, hUopen, hUc⟩ := hzloc
  have hUopen' : IsOpen ((U ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := hUopen.inter (IntermediateField.fixingSubgroup_isOpen K)
  obtain ⟨L, hLfin, hLnorm, hLle⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le
      (U := k) (L := Ω) (U ⊓ K.fixingSubgroup) hUopen'
  have hz1 : z 1 = 0 := by
    have h := hzadd 1 K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
    rw [mul_one] at h
    have h' : z 1 + z 1 = z 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h'
  refine ⟨L, hLfin, hLnorm, fun σ hσ => ?_⟩
  have hσU : σ ∈ U := (Subgroup.mem_inf.mp (hLle hσ)).1
  have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp (hLle hσ)).2
  have h := hUc 1 K.fixingSubgroup.one_mem σ hσU hσK
  rw [one_mul, hz1] at h
  exact h

/-- **Ramification in a compositum.**  If a place is ramified in `L ⊔ Λ`, it is ramified in one of
the two.  (The elements of `(L ⊔ Λ).fixingSubgroup` are exactly those fixing both fields.) -/
lemma isRamifiedIn_sup {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (L Λ : IntermediateField k Ω) {B : ValuationSubring Ω}
    (h : SSGRoute.IsRamifiedIn k (L ⊔ Λ) B) :
    SSGRoute.IsRamifiedIn k L B ∨ SSGRoute.IsRamifiedIn k Λ B := by
  obtain ⟨σ, hσI, hσ⟩ := h
  by_cases hL : σ ∈ L.fixingSubgroup
  · right
    refine ⟨σ, hσI, fun hΛ => hσ ?_⟩
    rw [IntermediateField.fixingSubgroup_sup]
    exact Subgroup.mem_inf.mpr ⟨hL, hΛ⟩
  · exact Or.inl ⟨σ, hσI, hL⟩

/-- **The auxiliary place set `T₀ = T ∪ Ram(L|k)`.** -/
theorem exists_auxiliary_placeSet (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) :
    ∃ S₀ : Finset (ValuationSubring Ω),
      (∀ A ∈ S₀, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ S₀, ∀ B ∈ S₀, SSGRoute.IsConjPlace k A B → A = B) ∧
      (∀ A ∈ S, ∃ A' ∈ S₀, SSGRoute.IsConjPlace k A A') ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k L B →
        ∃ A ∈ S₀, SSGRoute.IsConjPlace k A B) := by
  classical
  haveI hgal : IsGalois k L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  obtain ⟨R, hRfin, hRdisj, hRram⟩ := Work.SSGRoute.PT.ramifiedPlaces_finite_k_aux k Ω L
  refine ⟨S ∪ R.filter (fun A => ∀ B ∈ S, ¬ SSGRoute.IsConjPlace k B A), ?_, ?_, ?_, ?_⟩
  · -- all elements are finite places
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact hSfin A hA
    · exact hRfin A (Finset.mem_of_mem_filter A hA)
  · -- pairwise non-conjugate
    intro A hA B hB hconj
    rcases Finset.mem_union.mp hA with hA | hA
    · rcases Finset.mem_union.mp hB with hB | hB
      · exact hSdisj A hA B hB hconj
      · exact absurd hconj ((Finset.mem_filter.mp hB).2 A hA)
    · rcases Finset.mem_union.mp hB with hB | hB
      · exact absurd (SSGRoute.isConjPlace_symm hconj) ((Finset.mem_filter.mp hA).2 B hB)
      · exact hRdisj A (Finset.mem_of_mem_filter A hA) B (Finset.mem_of_mem_filter B hB) hconj
  · -- `S` is contained up to conjugacy
    intro A hA
    exact ⟨A, Finset.mem_union_left _ hA, SSGRoute.isConjPlace_refl A⟩
  · -- the places ramified in `L`
    intro B hB hram
    obtain ⟨A, hA, hAB⟩ := hRram B hB hram
    by_cases hAc : ∀ B' ∈ S, ¬ SSGRoute.IsConjPlace k B' A
    · exact ⟨A, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, hAc⟩), hAB⟩
    · push Not at hAc
      obtain ⟨B', hB', hB'A⟩ := hAc
      exact ⟨B', Finset.mem_union_left _ hB',
        SSGRoute.isConjPlace_trans hB'A hAB⟩

/-- **A hyperplane and a linear functional** in a finite `𝔽_p`-vector space of dimension `≥ 2`. -/
theorem exists_linearFunctional_finrank_ker (p : ℕ) [Fact p.Prime] {E : Type} [AddCommGroup E]
    [Module (ZMod p) E] [Finite E] (h : 2 ≤ Module.finrank (ZMod p) E) :
    ∃ (ρ : E →ₗ[ZMod p] ZMod p) (z₀ : E), ρ z₀ = 1 ∧
      Module.finrank (ZMod p) ↥(LinearMap.ker ρ) + 1 = Module.finrank (ZMod p) E := by
  classical
  haveI : Module.Finite (ZMod p) E := Module.Finite.of_finite
  haveI : Module.Free (ZMod p) E := Module.Free.of_divisionRing (ZMod p) E
  have hn : 0 < Module.finrank (ZMod p) E := lt_of_lt_of_le (by norm_num) h
  let i : Fin (Module.finrank (ZMod p) E) := ⟨0, hn⟩
  let b := Module.finBasis (ZMod p) E
  let ρ : E →ₗ[ZMod p] ZMod p :=
    (Finsupp.lapply (R := ZMod p) i).comp b.repr.toLinearMap
  let z₀ : E := b i
  have hρz₀ : ρ z₀ = 1 := by
    simp [ρ, z₀, b, i]
  have hsurj : Function.Surjective ρ := by
    intro c
    exact ⟨c • z₀, by rw [map_smul, hρz₀, smul_eq_mul, mul_one]⟩
  have hrange : Module.finrank (ZMod p) ↥(LinearMap.range ρ) = 1 := by
    have htop : LinearMap.range ρ = ⊤ := LinearMap.range_eq_top.mpr hsurj
    rw [htop]
    simp [Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker ρ
  rw [hrange] at hrn
  exact ⟨ρ, z₀, hρz₀, by omega⟩

end Work.SSGRoute
