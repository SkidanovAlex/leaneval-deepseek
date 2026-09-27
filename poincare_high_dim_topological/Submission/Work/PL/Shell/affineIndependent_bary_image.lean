import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Subdiv.Coord

/-!
# The barycenters of a chain of subsets of an affinely independent set are affinely independent

Let `Δ` be an affinely independent finite set of points of `PL.E N` and let `C` be a finite
family of nonempty subsets of `Δ`, totally ordered by inclusion (a "chain").  Then the
centroids (`Work.PL.Shell.bary`) of the members of `C` are affinely independent.

The proof is the same combinatorial argument as in `Work.PL.Subdiv.SdIndep`, transported to the
present vocabulary: the coefficients of an affine dependence, regrouped along the vertices of the
top of the chain, give zero barycentric coordinates, hence vanish, and peeling off the top element
of the chain finishes by induction.
-/

namespace Work.PL.Shell

open Set Metric Finset
open scoped BigOperators

variable {N : ℕ}

/-- Regrouping a sum of barycenters over a chain of faces, phrased with `Work.PL.Shell.bary`.
Stated for the local `bary` (definitionally the same as `Work.PL.Subdiv.bary`). -/
private lemma shell_sum_smul_bary_eq_sum_smul (C : Finset (Finset (PL.E N)))
    (τ : Finset (PL.E N)) (h : ∀ ρ ∈ C, ρ ⊆ τ) (c : Finset (PL.E N) → ℝ) :
    (∑ ρ ∈ C, c ρ • Work.PL.Shell.bary ρ)
      = ∑ v ∈ τ, (∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), c ρ / (ρ.card : ℝ)) • v :=
  Work.PL.Subdiv.sum_smul_bary_eq_sum_smul C τ h c

/-- Primitive form: the coefficients of an affine dependence among the barycenters of a chain of
subsets of an affinely independent set all vanish. -/
private theorem chain_bary_eq_zero {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N)) :
    ∀ (C : Finset (Finset (PL.E N))),
      (∀ A ∈ C, A.Nonempty ∧ A ⊆ Δ) →
      (∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) →
      ∀ c : Finset (PL.E N) → ℝ,
      (∑ A ∈ C, c A) = 0 → (∑ A ∈ C, c A • Work.PL.Shell.bary A) = 0 →
      ∀ A ∈ C, c A = 0 := by
  intro C
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    intro hC hchain c hsum hpt
    by_cases hne : C.Nonempty
    · have hτC : Work.PL.Subdiv.chainTop C ∈ C :=
        Work.PL.Subdiv.chainTop_mem_chain hchain hne
      have hex : ∃ v ∈ Work.PL.Subdiv.chainTop C,
          v ∉ Work.PL.Subdiv.chainTop (C.erase (Work.PL.Subdiv.chainTop C)) := by
        rcases Finset.eq_empty_or_nonempty (C.erase (Work.PL.Subdiv.chainTop C)) with hempty | hne'
        · obtain ⟨v, hv⟩ := (hC _ hτC).1
          exact ⟨v, Work.PL.Subdiv.le_chainTop hτC hv,
            by rw [hempty]; exact Finset.notMem_empty v⟩
        · have hmem' : Work.PL.Subdiv.chainTop (C.erase (Work.PL.Subdiv.chainTop C))
              ∈ C.erase (Work.PL.Subdiv.chainTop C) :=
            Work.PL.Subdiv.chainTop_mem_chain
              (fun ρ hρ ρ' hρ' => hchain ρ (Finset.mem_of_mem_erase hρ) ρ'
                (Finset.mem_of_mem_erase hρ')) hne'
          refine Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
          · exact Work.PL.Subdiv.chainTop_le_iff.mpr fun ρ hρ =>
              Work.PL.Subdiv.le_chainTop (Finset.mem_of_mem_erase hρ)
          · intro hcon
            exact Finset.notMem_erase _ _ (hcon ▸ hmem')
      obtain ⟨v, hvτ, hvnot⟩ := hex
      have hτΔ : Work.PL.Subdiv.chainTop C ⊆ Δ := fun x hx => (hC _ hτC).2 hx
      have hind : AffineIndependent ℝ ((↑) : Work.PL.Subdiv.chainTop C → PL.E N) :=
        AffineIndependent.mono hΔ hτΔ
      have hcoord := shell_sum_smul_bary_eq_sum_smul C (Work.PL.Subdiv.chainTop C)
        (fun ρ hρ => Work.PL.Subdiv.le_chainTop hρ) c
      have hsumα : (∑ x ∈ Work.PL.Subdiv.chainTop C,
          (∑ ρ ∈ C.filter (fun ρ => x ∈ ρ), c ρ / (ρ.card : ℝ))) = 0 := by
        rw [Work.PL.Subdiv.sum_coeff_filter C (Work.PL.Subdiv.chainTop C)
          (fun ρ hρ => Work.PL.Subdiv.le_chainTop hρ) (fun ρ hρ => (hC ρ hρ).1) c, hsum]
      have hptα : (∑ x ∈ Work.PL.Subdiv.chainTop C,
          (∑ ρ ∈ C.filter (fun ρ => x ∈ ρ), c ρ / (ρ.card : ℝ)) • x) = 0 := by
        rw [← hcoord, hpt]
      have hαzero := hind.eq_zero_of_sum_eq_zero_subtype hsumα hptα
      have hfilter : C.filter (fun ρ => v ∈ ρ) = {Work.PL.Subdiv.chainTop C} := by
        ext ρ
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hρC, hvρ⟩
          by_contra hne'
          exact hvnot (Work.PL.Subdiv.le_chainTop (Finset.mem_erase.mpr ⟨hne', hρC⟩) hvρ)
        · rintro rfl
          exact ⟨hτC, hvτ⟩
      have hcτ : c (Work.PL.Subdiv.chainTop C) = 0 := by
        have h0 := hαzero v hvτ
        rw [hfilter, Finset.sum_singleton] at h0
        have hcard : ((Work.PL.Subdiv.chainTop C).card : ℝ) ≠ 0 := by
          simp only [Nat.cast_ne_zero]
          exact Finset.card_ne_zero.mpr (hC _ hτC).1
        rcases div_eq_zero_iff.mp h0 with h | h
        · exact h
        · exact absurd h hcard
      have hC' : ∀ A ∈ C.erase (Work.PL.Subdiv.chainTop C), A.Nonempty ∧ A ⊆ Δ :=
        fun A hA => hC A (Finset.mem_of_mem_erase hA)
      have hchain' : ∀ A ∈ C.erase (Work.PL.Subdiv.chainTop C),
          ∀ B ∈ C.erase (Work.PL.Subdiv.chainTop C), A ⊆ B ∨ B ⊆ A :=
        fun A hA B hB => hchain A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB)
      have hlt : C.erase (Work.PL.Subdiv.chainTop C) ⊂ C := Finset.erase_ssubset hτC
      intro ρ hρ
      by_cases hρτ : ρ = Work.PL.Subdiv.chainTop C
      · rw [hρτ]; exact hcτ
      · refine ih _ hlt hC' hchain' c ?_ ?_ ρ (Finset.mem_erase.mpr ⟨hρτ, hρ⟩)
        · have h := Finset.sum_erase_add C c hτC
          rw [hsum, hcτ, add_zero] at h
          exact h
        · have h := Finset.sum_erase_add C (fun ρ => c ρ • Work.PL.Shell.bary ρ) hτC
          rw [hpt, hcτ, zero_smul, add_zero] at h
          exact h
    · intro ρ hρ
      exact absurd ⟨ρ, hρ⟩ hne

/-- The barycenters of the members of a chain of subsets of an affinely independent set, indexed
by the chain, are affinely independent. -/
private theorem affineIndependent_bary_chain {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {C : Finset (Finset (PL.E N))} (hC : ∀ A ∈ C, A.Nonempty ∧ A ⊆ Δ)
    (hchain : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) :
    AffineIndependent ℝ (fun A : ↥C => Work.PL.Shell.bary (A : Finset (PL.E N))) := by
  rw [affineIndependent_iff]
  intro s w hw hpt
  classical
  set c : Finset (PL.E N) → ℝ := fun A =>
    if h : A ∈ C then (if (⟨A, h⟩ : ↥C) ∈ s then w ⟨A, h⟩ else 0) else 0 with hc
  have hmem : ∀ x ∈ s, x ∈ C.attach := fun x _ => Finset.mem_attach C x
  have hsum : (∑ A ∈ C, c A) = 0 := by
    rw [← Finset.sum_attach C c, ← Finset.sum_subset hmem ?_, ← hw]
    · exact Finset.sum_congr rfl fun x hx => by simp [hc, x.2, hx]
    · intro x _ hx; simp [hc, x.2, hx]
  have hpt' : (∑ A ∈ C, c A • Work.PL.Shell.bary A) = 0 := by
    rw [← Finset.sum_attach C (fun A => c A • Work.PL.Shell.bary A),
      ← Finset.sum_subset hmem ?_, ← hpt]
    · exact Finset.sum_congr rfl fun x hx => by simp [hc, x.2, hx]
    · intro x _ hx; simp [hc, x.2, hx]
  intro A hAs
  have h := chain_bary_eq_zero hΔ C hC hchain c hsum hpt' A A.2
  simpa [hc, A.2, hAs] using h

theorem affineIndependent_bary_image {N : ℕ} {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {C : Finset (Finset (PL.E N))} (hC : ∀ A ∈ C, A.Nonempty ∧ A ⊆ Δ)
    (hchain : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) :
    AffineIndependent ℝ ((↑) : ↥(C.image Work.PL.Shell.bary) → PL.E N) := by
  have hchain_ind := affineIndependent_bary_chain hΔ hC hchain
  have h1 := hchain_ind.range
  set f : ↥C → PL.E N := fun A => Work.PL.Shell.bary (A : Finset (PL.E N)) with hf
  have hset : Set.range f = (↑(C.image Work.PL.Shell.bary) : Set (PL.E N)) := by
    ext b
    simp [hf]
  exact AffineIndependent.mono (s := (↑(C.image Work.PL.Shell.bary) : Set (PL.E N)))
    h1 hset.ge

end Work.PL.Shell
