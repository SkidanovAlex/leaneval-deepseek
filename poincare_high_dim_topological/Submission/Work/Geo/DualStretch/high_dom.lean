/-
`Geo/DualStretch` — `high_dom`: the dual `(n-p-1)`-skeleton `High P p` is `(n-p-1)`-dominated.

`High P p` is the union, over chains `T` of faces of `P` with at least `p+2` vertices, of the
simplices spanned by the barycentres of the members of `T`.  Such a chain has at most `n - p`
members: the cardinality map is injective on a chain and takes values in the interval
`[p+2, n+1]` (the upper bound being that faces of a simplicial complex in `ℝⁿ` have at most
`n+1` vertices, since they are affinely independent).  Hence `High P p` is covered by the finitely
many simplices `simp (T.image bary)` and each of these spans at most `n - p = (n-p-1)+1` vertices,
which is Newman's `DomDim`.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Basic

open Set Metric
open scoped Classical
open PL (E Cx simp closedCube openCube)

namespace Work.Geo.DualStretch

/-- **A face of a simplicial complex in `ℝⁿ` spans at most `n+1` vertices.**

Faces are affinely independent, and an affinely independent family of `k` points spans a vector
space of dimension at least `k-1`, which is at most `n = finrank ℝ (E n)`. -/
theorem face_card_le {n : ℕ} (P : Cx n) {s : Finset (E n)} (hs : s ∈ P.faces) :
    s.card ≤ n + 1 := by
  have h := P.indep hs
  have h1 : Fintype.card s ≤
      Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E n))) + 1 :=
    AffineIndependent.card_le_finrank_succ (k := ℝ) (P := E n) h
  have h3 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E n))) ≤ n :=
    (Submodule.finrank_le _).trans_eq finrank_euclideanSpace_fin
  rw [Fintype.card_coe] at h1
  omega

/-- **A chain of faces with at least `p+2` vertices has at most `n - p` members.**

The cardinality is injective on a chain (two comparable finite sets of equal cardinality are equal)
and its values lie in the interval `[p+2, n+1]`, which has `n - p` elements. -/
theorem chain_card_le {n p : ℕ} (P : Cx n) {T : Finset (Finset (E n))}
    (hT : ∀ σ ∈ T, σ ∈ P.faces) (hchain : IsChain T) (hcard : ∀ σ ∈ T, p + 2 ≤ σ.card) :
    T.card ≤ n - p := by
  have hinj : Set.InjOn (fun σ : Finset (E n) => σ.card) (T : Set (Finset (E n))) := by
    intro σ hσ τ hτ h
    rcases hchain σ hσ τ hτ with hsub | hsub
    · exact Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
    · exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq h)).symm
  rw [← Finset.card_image_of_injOn hinj]
  have hsub : T.image (fun σ => σ.card) ⊆ Finset.Icc (p + 2) (n + 1) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨σ, hσ, rfl⟩ := hm
    exact Finset.mem_Icc.2 ⟨hcard σ hσ, face_card_le P (hT σ hσ)⟩
  calc (T.image (fun σ => σ.card)).card ≤ (Finset.Icc (p + 2) (n + 1)).card :=
        Finset.card_le_card hsub
    _ = n - p := by rw [Nat.card_Icc]; omega

/-- The integer form of `chain_card_le` used in the domination statement: the simplex spanned by
the barycentres of the chain has at most `n - p = (n-p-1)+1` vertices. -/
theorem chain_card_le_int {n p : ℕ} (P : Cx n) {T : Finset (Finset (E n))}
    (hT : ∀ σ ∈ T, σ ∈ P.faces) (hne : T.Nonempty) (hchain : IsChain T)
    (hcard : ∀ σ ∈ T, p + 2 ≤ σ.card) :
    ((T.image bary).card : ℤ) ≤ (n : ℤ) - (p : ℤ) := by
  have h1 : T.card ≤ n - p := chain_card_le P hT hchain hcard
  obtain ⟨σ, hσ⟩ := hne
  have hpn : p ≤ n := by
    have h2 := hcard σ hσ
    have h3 := face_card_le P (hT σ hσ)
    omega
  have h4 : ((T.image bary).card : ℤ) ≤ (T.card : ℤ) := by
    exact_mod_cast Finset.card_image_le
  have h5 : (T.card : ℤ) ≤ ((n - p : ℕ) : ℤ) := by exact_mod_cast h1
  have h6 : ((n - p : ℕ) : ℤ) = (n : ℤ) - (p : ℤ) := Int.ofNat_sub hpn
  linarith

theorem high_dom {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    PL.DomDim (Work.Geo.DualStretch.High P p) (n - p - 1 : ℤ) := by
  refine ⟨(hP.toFinset.powerset.filter
      (fun T => T.Nonempty ∧ IsChain T ∧ ∀ σ ∈ T, p + 2 ≤ σ.card)).image
      (fun T => T.image bary), ?_, ?_⟩
  · -- every chain in the cover spans at most `(n-p-1)+1` vertices
    intro s hs
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at hs
    obtain ⟨T, ⟨hTsub, hne, hchain, hcard⟩, rfl⟩ := hs
    have := chain_card_le_int P (fun σ hσ => (hP.mem_toFinset).mp (hTsub hσ)) hne hchain hcard
    linarith
  · -- every point of `High P p` lies in one of them
    intro x hx
    obtain ⟨T, hTsub, hne, hchain, hcard, hxT⟩ := hx
    simp only [mem_iUnion₂, Finset.mem_image]
    refine ⟨T.image bary, ⟨T, ?_, rfl⟩, hxT⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun σ hσ => (hP.mem_toFinset).mpr (hTsub hσ), hne, hchain, hcard⟩

end Work.Geo.DualStretch
