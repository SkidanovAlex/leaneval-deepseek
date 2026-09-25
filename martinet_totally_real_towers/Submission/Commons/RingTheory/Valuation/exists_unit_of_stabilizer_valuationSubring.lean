import Mathlib
import Submission.Commons.RingTheory.Valuation.ValuationSubring.exists_unit_at_index_nonunit_else

namespace Commons.RingTheory.Valuation

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

private lemma mem_smul_iff' {F E : Type*} [Field F] [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (X : ValuationSubring E) (x : E) : x ∈ σ • X ↔ σ.symm x ∈ X := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]; rfl

/-- Members of `σ • A` vs. nonunits of `A`. -/
private lemma mem_nonunits_smul_iff {F E : Type*} [Field F] [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (A : ValuationSubring E) (x : E) :
    x ∈ (σ • A).nonunits ↔ σ.symm x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  constructor
  · rintro (h | h)
    · left; rw [h, map_zero]
    · right
      intro hx
      exact h ((mem_smul_iff' σ A x⁻¹).mpr (by rw [map_inv₀]; exact hx))
  · rintro (h | h)
    · left; exact σ.symm.injective (by rw [h, map_zero])
    · right
      intro hx
      exact h (by simpa using (mem_smul_iff' σ A x⁻¹).mp hx)

/-- `A.valuation (σ u) < 1` is the same as `u` being a nonunit at the conjugate `σ.symm • A`. -/
private lemma val_smul_lt_one_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (u : L) :
    A.valuation (σ u) < 1 ↔ u ∈ (σ.symm • A).nonunits := by
  have h : u ∈ (σ.symm • A).nonunits ↔ A.valuation (σ u) < 1 := by
    rw [mem_nonunits_smul_iff σ.symm A u, AlgEquiv.symm_symm,
      ValuationSubring.mem_nonunits_iff]
  exact h.symm

/-- Conjugates of a valuation subring are pairwise incomparable: if `σ • A ≤ τ • A` then the two
conjugates coincide. -/
private lemma conjugate_not_le (A : ValuationSubring L) (σ τ : L ≃ₐ[K] L) (h : σ • A ≠ τ • A) :
    ¬ (σ • A ≤ τ • A) := by
  have hsm : ∀ (g : L ≃ₐ[K] L) (m : ℕ), 0 < m → g ^ m = 1 → A ≤ g • A → g • A = A := by
    intro g m hmpos hm hle
    have hstep : ∀ k, g ^ k • A ≤ g ^ (k + 1) • A := by
      intro k
      have hh : g ^ k • A ≤ g ^ k • g • A :=
        (ValuationSubring.pointwise_smul_le_pointwise_smul_iff (g := g ^ k)).mpr hle
      rwa [smul_smul, ← pow_succ] at hh
    have hchain : ∀ k, 1 ≤ k → g ^ 1 • A ≤ g ^ k • A := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact le_refl _
      | succ n hn ih => exact le_trans ih (hstep n)
    have hm' := hchain m hmpos
    rw [hm, one_smul] at hm'
    exact le_antisymm (by simpa [pow_one] using hm') hle
  intro hle
  have h1 : A ≤ (σ⁻¹ * τ) • A := by
    have h2 : A ≤ σ⁻¹ • (τ • A) := (ValuationSubring.pointwise_smul_subset_iff).mp hle
    rwa [smul_smul] at h2
  have hδ : (σ⁻¹ * τ) • A = A :=
    hsm (σ⁻¹ * τ) (orderOf (σ⁻¹ * τ)) (orderOf_pos _) (pow_orderOf_eq_one _) h1
  refine h ?_
  calc σ • A = σ • ((σ⁻¹ * τ) • A) := by rw [hδ]
    _ = (σ * (σ⁻¹ * τ)) • A := by rw [smul_smul]
    _ = τ • A := by rw [show σ * (σ⁻¹ * τ) = τ by group]

set_option maxHeartbeats 400000 in
/-- **Chinese-remainder/approximation element for a decomposition group.**
Let `L/K` be a finite Galois extension, `A` a valuation subring of `L`, and `d` the stabiliser of
`A` in `Gal(L/K)` (the decomposition group).  Then there is `u : L` with `A.valuation u = 1`
(`u` is a unit of `A`) and `A.valuation (σ u) < 1` for every `σ ∉ d` (`σ u` lies in the maximal
ideal of `A`).

Equivalently, `u ≡ 1` at the place `A` and `u ≡ 0` at all the other conjugate places. -/
theorem exists_unit_of_stabilizer_valuationSubring {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (A : ValuationSubring L) :
    ∃ u : L, A.valuation u = 1 ∧
      ∀ σ : L ≃ₐ[K] L, σ ∉ MulAction.stabilizer (L ≃ₐ[K] L) A → A.valuation (σ u) < 1 := by
  classical
  by_cases hA : A = ⊤
  · refine ⟨1, ?_, ?_⟩
    · rw [hA]; exact Valuation.map_one _
    · intro σ hσ
      refine absurd ?_ hσ
      rw [hA, MulAction.mem_stabilizer_iff]
      ext x
      simp [mem_smul_iff']
  · let S : Finset (ValuationSubring L) := Finset.univ.image (fun σ : L ≃ₐ[K] L => σ • A)
    have hAmem : A ∈ S := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩
    have hnt : ∀ B : ↥S, (B : ValuationSubring L) ≠ ⊤ := by
      intro B hB
      obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp B.2
      apply hA
      have h1 : σ⁻¹ • ((σ : L ≃ₐ[K] L) • A) = A := by
        rw [smul_smul, show σ⁻¹ * σ = 1 from by ext x; simp, one_smul]
      rw [← h1, hσ, hB]
      ext x
      simp [mem_smul_iff']
    have hincomp : ∀ B B' : ↥S, B ≠ B' → ¬ ((B : ValuationSubring L) ≤ B') := by
      intro B B' hne hle
      obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp B.2
      obtain ⟨τ, -, hτ⟩ := Finset.mem_image.mp B'.2
      have hσB : (B : ValuationSubring L) = σ • A := hσ.symm
      have hτB : (B' : ValuationSubring L) = τ • A := hτ.symm
      rw [hσB, hτB] at hle
      have hne' : σ • A ≠ τ • A := by
        intro hc
        exact hne (Subtype.ext (by rw [hσB, hτB, hc]))
      exact conjugate_not_le A σ τ hne' hle
    obtain ⟨u, huD, hu_notmem, hu_mem⟩ :=
      ValuationSubring.exists_unit_at_index_nonunit_else
        (fun B : ↥S => (B : ValuationSubring L)) hnt hincomp ⟨A, hAmem⟩
    refine ⟨u, ?_, ?_⟩
    · have huA : u ∈ A := by
        have h := Subring.mem_iInf.mp huD ⟨A, hAmem⟩
        simpa using h
      have hle : A.valuation u ≤ 1 :=
        (ValuationSubring.valuation_le_one_iff (A := A) u).mpr huA
      have hlt : ¬ (A.valuation u < 1) :=
        fun h => hu_notmem ((ValuationSubring.mem_nonunits_iff A).mpr h)
      exact le_antisymm hle (not_lt.mp hlt)
    · intro σ hσ
      rw [val_smul_lt_one_iff A σ u]
      have hsmem : σ.symm • A ∈ S :=
        Finset.mem_image.mpr ⟨σ.symm, Finset.mem_univ _, rfl⟩
      have hne : (⟨σ.symm • A, hsmem⟩ : ↥S) ≠ ⟨A, hAmem⟩ := by
        intro hc
        refine hσ ?_
        rw [MulAction.mem_stabilizer_iff]
        have h2 : σ.symm • A = A := congrArg (fun k : ↥S => (k : ValuationSubring L)) hc
        calc σ • A = σ • (σ.symm • A) := by rw [h2]
          _ = (σ * σ.symm) • A := by rw [smul_smul]
          _ = A := by rw [show σ * σ.symm = 1 from by ext x; simp, one_smul]
      exact hu_mem ⟨σ.symm • A, hsmem⟩ hne

end Commons.RingTheory.Valuation
