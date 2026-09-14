import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace Commons.Geometry.Convex

open Set

/-- Given a convex combination `∑ i, w i • z i` of at most `n` terms (i.e. `Fintype.card ι ≤ n`),
one can re-index it by `Fin n`, padding with the dummy point `p` and weight `0`. -/
lemma exists_fin_sum_of_card_le {ι : Type*} [Fintype ι] {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {n : ℕ} (h : Fintype.card ι ≤ n) (z : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (p : E) :
    ∃ (y : Fin n → E) (t : Fin n → ℝ),
      (∀ i, y i ∈ Set.range z ∪ {p}) ∧ (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1 ∧
        (∑ i, t i • y i) = ∑ i, w i • z i := by
  classical
  let m := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let G : ℕ → ℝ := fun k => if hk : k < m then w (e.symm ⟨k, hk⟩) else 0
  let Y : ℕ → E := fun k => if hk : k < m then z (e.symm ⟨k, hk⟩) else p
  have hGm : ∀ k : Fin m, G (k : ℕ) = w (e.symm k) := by
    intro k
    simp only [G, dif_pos k.isLt, Fin.eta]
  have hYm : ∀ k : Fin m, Y (k : ℕ) = z (e.symm k) := by
    intro k
    simp only [Y, dif_pos k.isLt, Fin.eta]
  have hsub : Finset.range m ⊆ Finset.range n := Finset.range_subset_range.mpr h
  refine ⟨fun i => Y i, fun i => G i, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases lt_or_ge (i : ℕ) m with hk | hk
    · left
      exact ⟨e.symm ⟨(i : ℕ), hk⟩, by simp only [Y, dif_pos hk]⟩
    · right
      simp only [Set.mem_singleton_iff]
      simp only [Y, dif_neg (not_lt.mpr hk)]
  · intro i
    rcases lt_or_ge (i : ℕ) m with hk | hk
    · simp only [G, dif_pos hk]
      exact hw _
    · simp only [G, dif_neg (not_lt.mpr hk)]
      exact le_refl 0
  · calc ∑ i : Fin n, G (i : ℕ)
        = ∑ k ∈ Finset.range n, G k := Fin.sum_univ_eq_sum_range G n
      _ = ∑ k ∈ Finset.range m, G k := by
            refine (Finset.sum_subset hsub ?_).symm
            intro k _ hk
            have hk' : ¬ (k < m) := by simpa using hk
            simp only [G, dif_neg hk']
      _ = ∑ k : Fin m, G (k : ℕ) := (Fin.sum_univ_eq_sum_range G m).symm
      _ = ∑ k : Fin m, w (e.symm k) := Finset.sum_congr rfl (fun k _ => hGm k)
      _ = ∑ i : ι, w i := Equiv.sum_comp e.symm w
      _ = 1 := hsum
  · calc ∑ i : Fin n, G (i : ℕ) • Y (i : ℕ)
        = ∑ k ∈ Finset.range n, G k • Y k := Fin.sum_univ_eq_sum_range (fun k => G k • Y k) n
      _ = ∑ k ∈ Finset.range m, G k • Y k := by
            refine (Finset.sum_subset hsub ?_).symm
            intro k _ hk
            have hk' : ¬ (k < m) := by simpa using hk
            simp only [G, dif_neg hk', zero_smul]
      _ = ∑ k : Fin m, G (k : ℕ) • Y (k : ℕ) :=
            (Fin.sum_univ_eq_sum_range (fun k => G k • Y k) m).symm
      _ = ∑ k : Fin m, w (e.symm k) • z (e.symm k) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [hGm k, hYm k]
      _ = ∑ i : ι, w i • z i := Equiv.sum_comp e.symm (fun i => w i • z i)

theorem convexHull_eq_image_simplex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Set E) :
    convexHull ℝ s = {x : E | ∃ (y : Fin (Module.finrank ℝ E + 1) → E) (t : Fin (Module.finrank ℝ E + 1) → ℝ),
      (∀ i, y i ∈ s) ∧ (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1 ∧ (∑ i, t i • y i) = x} := by
  refine Set.Subset.antisymm ?_ ?_
  · -- Carathéodory: every point of the convex hull is a combination of at most `finrank ℝ E + 1`
    -- points of `s`.
    intro x hx
    obtain ⟨ι, hι, z, w, hzs, hind, hwpos, hwsum, hwz⟩ :=
      eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hx
    obtain ⟨p, hp⟩ := (convexHull_nonempty_iff (𝕜 := ℝ) (s := s)).mp ⟨x, hx⟩
    have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
      have h1 := hind.card_le_finrank_succ
      have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ E :=
        Submodule.finrank_le _
      exact le_trans h1 (Nat.add_le_add_right h2 1)
    obtain ⟨y, t, hy, ht0, htsum, hyt⟩ :=
      exists_fin_sum_of_card_le hcard z w (fun i => le_of_lt (hwpos i)) hwsum p
    refine ⟨y, t, ?_, ht0, htsum, ?_⟩
    · intro i
      rcases hy i with h | h
      · exact hzs h
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact hp
    · rw [hyt]
      exact hwz
  · -- Conversely, a convex combination of points of `s` lies in the convex hull of `s`.
    rintro x ⟨y, t, hys, ht0, htsum, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (t := Finset.univ) (fun i _ => ht0 i)
      (by simpa using htsum) (fun i _ => subset_convexHull ℝ s (hys i))

end Commons.Geometry.Convex