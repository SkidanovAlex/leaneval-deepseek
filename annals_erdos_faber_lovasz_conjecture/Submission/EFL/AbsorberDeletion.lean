import Submission.EFL.CrossingAbsorption

/-!
# Robustness of absorbers (paper Observation `obs:del_absorber`)

A `(ρ,γ,ξ,ε)`-absorber `R` for `𝓥` stays an absorber when

* the typicality parameter `γ` is increased (part (i) of the observation), or
* a subfamily `R' ⊆ R` is removed whose *deleted* part `R ∖ R'` has maximum
  degree at most `αn`: then `R'` is a `(ρ, γ + α, ξ, ε)`-absorber for `𝓥`
  (part (ii)), because the `R'`-degree of a vertex inside `X` differs from the
  `R`-degree by at most `deg_{R∖R'}(v) ≤ αn`, and the `ξ`-upper-regularity is
  inherited from `R` since `R' ⊆ R`.

This is the observation repeatedly used in Steps 4--6 of §12 of the paper.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The neighbourhood of `v` in a subfamily: `nbrs R v = nbrs R' v ∪ nbrs (R∖R') v`
when `R' ⊆ R`. -/
theorem nbrs_eq_union_sdiff {R R' : Hypergraph (Fin n)} (h : R' ⊆ R) (v : Fin n) :
    nbrs R v = nbrs R' v ∪ nbrs (R \ R') v := by
  ext x
  simp only [nbrs, Set.mem_setOf_eq, Set.mem_union, Set.mem_diff]
  constructor
  · intro hx
    by_cases hx' : ({v, x} : Set (Fin n)) ∈ R'
    · exact Or.inl hx'
    · exact Or.inr ⟨hx, hx'⟩
  · rintro (hx | ⟨hx, -⟩)
    · exact h hx
    · exact hx

/-- **Observation `obs:del_absorber` (i).**  Increasing `γ` preserves
absorbers. -/
theorem IsAbsorber.mono_gamma {G' R : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {ρ γ γ' ξ : ℝ} (h : IsAbsorber G' R 𝓥 ρ γ ξ) (hγ : γ ≤ γ') :
    IsAbsorber G' R 𝓥 ρ γ' ξ := by
  obtain ⟨hsub, htyp, hup⟩ := h
  refine ⟨hsub, ?_, hup⟩
  intro X hX v
  obtain ⟨h1, h2⟩ := htyp X hX v
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact ⟨le_trans h1 (by nlinarith), le_trans h2 (by nlinarith)⟩

/-- **Observation `obs:del_absorber` (ii).**  Deleting a subfamily of max
degree at most `αn` from an absorber increases `γ` by at most `α`. -/
theorem IsAbsorber.delete {G' R R' : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {ρ γ ξ α : ℝ} (h : IsAbsorber G' R 𝓥 ρ γ ξ) (hR' : R' ⊆ R)
    (hΔ : ∀ v : Fin n, (degAt (R \ R') v : ℝ) ≤ α * (n : ℝ)) :
    IsAbsorber G' R' 𝓥 ρ (γ + α) ξ := by
  obtain ⟨hsub, htyp, hup⟩ := h
  refine ⟨fun e he => hsub (hR' he), ?_, ?_⟩
  · intro X hX v
    have hsplit := nbrs_eq_union_sdiff hR' v
    have hdisj : Disjoint (X ∩ nbrs R' v) (X ∩ nbrs (R \ R') v) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx'⟩ ⟨-, hx''⟩
      have h1 : x ∈ nbrs R' v := hx'
      have h2 : x ∈ nbrs (R \ R') v := hx''
      rw [nbrs, Set.mem_setOf_eq] at h1
      rw [nbrs, Set.mem_setOf_eq, Set.mem_diff] at h2
      exact h2.2 h1
    have hsum : (X ∩ nbrs R v).ncard =
        (X ∩ nbrs R' v).ncard + (X ∩ nbrs (R \ R') v).ncard := by
      have h1 : X ∩ nbrs R v = (X ∩ nbrs R' v) ∪ (X ∩ nbrs (R \ R') v) := by
        rw [hsplit]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_union]
        tauto
      rw [h1]
      exact Set.ncard_union_eq (s := X ∩ nbrs R' v) (t := X ∩ nbrs (R \ R') v)
        hdisj (Set.toFinite _) (Set.toFinite _)
    have hle : ((X ∩ nbrs (R \ R') v).ncard : ℝ) ≤ α * (n : ℝ) := by
      have h1 : (X ∩ nbrs (R \ R') v).ncard ≤ (nbrs (R \ R') v).ncard :=
        Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
      have h2 : (nbrs (R \ R') v).ncard = degAt (R \ R') v := rfl
      rw [h2] at h1
      exact le_trans (by exact_mod_cast h1) (hΔ v)
    obtain ⟨hh1, hh2⟩ := htyp X hX v
    rw [abs_le] at hh1 hh2
    constructor
    · have hcast : ((X ∩ nbrs R' v).ncard : ℝ) =
          ((X ∩ nbrs R v).ncard : ℝ) - ((X ∩ nbrs (R \ R') v).ncard : ℝ) := by
        rw [hsum]
        push_cast
        ring
      have hle0 : (0 : ℝ) ≤ ((X ∩ nbrs (R \ R') v).ncard : ℝ) := Nat.cast_nonneg _
      rw [abs_le, hcast]
      constructor <;> linarith [hh1.1, hh1.2, hle, hle0]
    · have hsplit' := nbrs_eq_union_sdiff hR' v
      have hdisj' : Disjoint (Xᶜ ∩ nbrs R' v) (Xᶜ ∩ nbrs (R \ R') v) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, hx'⟩ ⟨-, hx''⟩
        have h1 : x ∈ nbrs R' v := hx'
        have h2 : x ∈ nbrs (R \ R') v := hx''
        rw [nbrs, Set.mem_setOf_eq] at h1
        rw [nbrs, Set.mem_setOf_eq, Set.mem_diff] at h2
        exact h2.2 h1
      have hsum' : (Xᶜ ∩ nbrs R v).ncard =
          (Xᶜ ∩ nbrs R' v).ncard + (Xᶜ ∩ nbrs (R \ R') v).ncard := by
        have h1 : Xᶜ ∩ nbrs R v = (Xᶜ ∩ nbrs R' v) ∪ (Xᶜ ∩ nbrs (R \ R') v) := by
          rw [hsplit']
          ext x
          simp only [Set.mem_inter_iff, Set.mem_union]
          tauto
        rw [h1]
        exact Set.ncard_union_eq (s := Xᶜ ∩ nbrs R' v) (t := Xᶜ ∩ nbrs (R \ R') v)
          hdisj' (Set.toFinite _) (Set.toFinite _)
      have hle' : ((Xᶜ ∩ nbrs (R \ R') v).ncard : ℝ) ≤ α * (n : ℝ) := by
        have h1 : (Xᶜ ∩ nbrs (R \ R') v).ncard ≤ (nbrs (R \ R') v).ncard :=
          Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
        have h2 : (nbrs (R \ R') v).ncard = degAt (R \ R') v := rfl
        rw [h2] at h1
        exact le_trans (by exact_mod_cast h1) (hΔ v)
      have hcast : ((Xᶜ ∩ nbrs R' v).ncard : ℝ) =
          ((Xᶜ ∩ nbrs R v).ncard : ℝ) - ((Xᶜ ∩ nbrs (R \ R') v).ncard : ℝ) := by
        rw [hsum']
        push_cast
        ring
      have hle0 : (0 : ℝ) ≤ ((Xᶜ ∩ nbrs (R \ R') v).ncard : ℝ) := Nat.cast_nonneg _
      rw [abs_le, hcast]
      constructor <;> linarith [hh2.1, hh2.2, hle', hle0]
  · -- upper regularity is inherited
    intro S T hST hS hT
    exact le_trans (by exact_mod_cast edgeCount_mono hR' S T) (hup S T hST hS hT)

end

end ErdosFaberLovaszConjecture
