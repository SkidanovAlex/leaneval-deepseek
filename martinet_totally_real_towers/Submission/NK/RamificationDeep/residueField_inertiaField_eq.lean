import Mathlib
import Submission.NK.RamificationDeep.InertiaField
import Submission.NK.RamificationDeep.subring_eq_top_of_coeff_mem

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace NK.RamificationDeep

universe u

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-! ### Auxiliary lemmas -/

/-- The action of the decomposition subgroup on `A` is induced by its action on `L`. -/
theorem coe_smul_decompositionSubgroup (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (σ : ↥(A.decompositionSubgroup K)) (a : A) :
    ((σ • a : A) : L) = (σ : L ≃ₐ[K] L) (a : L) := rfl

/-- An element of the inertia subgroup acts trivially on the residue field of `A`. -/
theorem smul_residue_eq_of_mem_inertiaSubgroup (A : ValuationSubring L)
    [IsDiscreteValuationRing A] {τ : ↥(A.decompositionSubgroup K)}
    (hτ : τ ∈ A.inertiaSubgroup K) (w : IsLocalRing.ResidueField A) :
    τ • w = w := by
  have hker := MonoidHom.mem_ker.mp hτ
  simpa using congrArg (fun (g : RingAut (IsLocalRing.ResidueField A)) => g w) hker

/-- The element of `A ∩ E` attached to an element `a : A` whose image in `L` lies in `E`. -/
noncomputable def restrictRingOf (A : ValuationSubring L) (E : IntermediateField K L) (a : A)
    (h : (a : L) ∈ E) : ↥(restrictRing A E) :=
  ⟨⟨(a : L), h⟩, by rw [mem_restrictRing_iff]; exact a.2⟩

theorem restrictRingToA_restrictRingOf (A : ValuationSubring L) (E : IntermediateField K L)
    (a : A) (h : (a : L) ∈ E) :
    restrictRingToA A E (restrictRingOf A E a h) = a := Subtype.ext rfl

/-! ### The main theorem -/

theorem residueField_inertiaField_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsGalois K L] [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤)
    [PerfectField (IsLocalRing.ResidueField A)] :
    ∀ x : A, ∃ b : ↥(NK.RamificationDeep.restrictRing A (NK.RamificationDeep.inertiaField (K := K) A)),
      NK.RamificationDeep.restrictRingToA A (NK.RamificationDeep.inertiaField (K := K) A) b - x
        ∈ IsLocalRing.maximalIdeal A := by
  classical
  intro x
  haveI : Fintype ↥(A.inertiaSubgroup K) := Fintype.ofFinite _
  set E : IntermediateField K L := inertiaField (K := K) A with hEdef
  set n : ℕ := Nat.card ↥(A.inertiaSubgroup K) with hndef
  have hn : 0 < n := by rw [hndef]; exact Nat.card_pos
  -- For every `z` in the residue field, all coefficients of `(X - C z)^n` lie in the image of
  -- the reduction map `A ∩ E → 𝔪_A`.
  have key : ∀ z : IsLocalRing.ResidueField A, ∀ k : ℕ,
      ((Polynomial.X - Polynomial.C z) ^ n).coeff k ∈
        RingHom.range ((IsLocalRing.residue A).comp (restrictRingToA A E)) := by
    intro z k
    obtain ⟨x₀, hx₀⟩ := IsLocalRing.residue_surjective z
    set Q : Polynomial A :=
      ∏ σ : ↥(A.inertiaSubgroup K), (Polynomial.X - Polynomial.C (σ.1 • x₀)) with hQdef
    -- the polynomial `Q` is invariant under the inertia subgroup
    have hsmul_Q : ∀ τ : ↥(A.inertiaSubgroup K),
        (τ.1 : ↥(A.decompositionSubgroup K)) • Q = Q := by
      intro τ
      rw [hQdef, Finset.smul_prod']
      refine Fintype.prod_bijective (fun σ : ↥(A.inertiaSubgroup K) => τ * σ)
        (MulAction.bijective τ) _ _ ?_
      intro σ
      simp only [smul_sub, Polynomial.smul_X, Polynomial.smul_C, mul_smul, Subgroup.coe_mul]
    -- hence its coefficients are fixed
    have hcoeff_fixed : ∀ (τ : ↥(A.inertiaSubgroup K)) (m : ℕ),
        (τ.1 : ↥(A.decompositionSubgroup K)) • Q.coeff m = Q.coeff m := by
      intro τ m
      have h := congrArg (fun p : Polynomial A => p.coeff m) (hsmul_Q τ)
      simpa only [Polynomial.coeff_smul] using h
    -- and therefore lie in the inertia field `E`
    have hcoeff_mem : ((Q.coeff k : A) : L) ∈ E := by
      rw [hEdef, inertiaField_eq_fixedField_inertiaImage, IntermediateField.mem_fixedField_iff]
      rintro σ ⟨τ, hτ, rfl⟩
      have h := congrArg (fun a : A => (a : L)) (hcoeff_fixed ⟨τ, hτ⟩ k)
      rw [coe_smul_decompositionSubgroup] at h
      exact h
    -- the reduction of `Q` is `(X - C z)^n`
    have hmap : Polynomial.map (IsLocalRing.residue A) Q = (Polynomial.X - Polynomial.C z) ^ n := by
      rw [hQdef, Polynomial.map_prod]
      have hterm : ∀ σ : ↥(A.inertiaSubgroup K),
          Polynomial.map (IsLocalRing.residue A)
            (Polynomial.X - Polynomial.C (σ.1 • x₀)) = Polynomial.X - Polynomial.C z := by
        intro σ
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
          IsLocalRing.ResidueField.residue_smul, hx₀,
          smul_residue_eq_of_mem_inertiaSubgroup A σ.2 z]
      rw [Finset.prod_congr rfl (fun σ _ => hterm σ), Finset.prod_const]
      congr 1
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← hndef]
    -- conclude
    refine RingHom.mem_range.mpr ⟨restrictRingOf A E (Q.coeff k) hcoeff_mem, ?_⟩
    rw [RingHom.comp_apply, restrictRingToA_restrictRingOf]
    show IsLocalRing.residue A (Q.coeff k) = ((Polynomial.X - Polynomial.C z) ^ n).coeff k
    rw [← hmap, Polynomial.coeff_map]
  -- The arithmetic input turns the coefficient information into surjectivity.
  have htop : RingHom.range ((IsLocalRing.residue A).comp (restrictRingToA A E)) = ⊤ :=
    subring_eq_top_of_coeff_mem _ hn key
  have hx : IsLocalRing.residue A x ∈
      RingHom.range ((IsLocalRing.residue A).comp (restrictRingToA A E)) := by
    rw [htop]; exact Subring.mem_top _
  obtain ⟨b, hb⟩ := RingHom.mem_range.mp hx
  have hb' : IsLocalRing.residue A (restrictRingToA A E b) = IsLocalRing.residue A x := hb
  refine ⟨b, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hb', sub_self]

end NK.RamificationDeep
