import Mathlib
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilC4.encardLePigeonhole

set_option autoImplicit false
noncomputable section

namespace Work.WilE2

open Classical

theorem coverBound_of_pdist_bound {k : ℕ} {X : Set (Fin k → ℝ)} {N : ℕ}
    (h : ∀ s : Finset (Fin k → ℝ), (↑s : Set (Fin k → ℝ)) ⊆ X →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → connectedComponentIn X x ≠ connectedComponentIn X y) →
      s.card ≤ N) :
    Work.WilE2.CoverBound X N := by
  classical
  -- `S` is the set of connected components of `X`.
  set S : Set (Set (Fin k → ℝ)) := (fun x => connectedComponentIn X x) '' X with hSdef
  -- Any finite family of pairwise distinct components has at most `N` members.
  have hSenc : S.encard ≤ (N : ℕ∞) := by
    rw [Work.WilC4.encardLePigeonhole S N]
    intro f hf
    -- pick a point of `X` in each of the given components
    have hchoice : ∀ i, ∃ x ∈ X, connectedComponentIn X x = f i := by
      intro i
      have hi : f i ∈ (fun x => connectedComponentIn X x) '' X := by
        rw [← hSdef]; exact hf i
      rw [Set.mem_image] at hi
      obtain ⟨x, hxX, hx⟩ := hi
      exact ⟨x, hxX, hx⟩
    by_contra hcon
    push_neg at hcon
    have hf_inj : ∀ i j, f i = f j → i = j := by
      intro i j hij
      by_contra hne
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact hcon i j hlt hij
      · exact hne heq
      · exact hcon j i hgt hij.symm
    let pt : Fin (N + 1) → Fin k → ℝ := fun i => Classical.choose (hchoice i)
    have hptX : ∀ i, pt i ∈ X := fun i => (Classical.choose_spec (hchoice i)).1
    have hptC : ∀ i, connectedComponentIn X (pt i) = f i :=
      fun i => (Classical.choose_spec (hchoice i)).2
    have hpt_inj : Function.Injective pt := by
      intro i j hij
      refine hf_inj i j ?_
      rw [← hptC i, ← hptC j, hij]
    let s : Finset (Fin k → ℝ) := Finset.univ.image pt
    have hs_card : s.card = N + 1 := by
      simp only [s]
      rw [Finset.card_image_of_injective Finset.univ hpt_inj, Finset.card_univ,
        Fintype.card_fin]
    have hs_sub : (↑s : Set (Fin k → ℝ)) ⊆ X := by
      intro x hx
      simp only [s, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hptX i
    have hs_comp : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        connectedComponentIn X x ≠ connectedComponentIn X y := by
      intro x hx y hy hxy hc
      simp only [s, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      have hcij : f i = f j := by
        rw [← hptC i, ← hptC j]; exact hc
      exact hxy (by rw [hf_inj i j hcij])
    have hle := h s hs_sub hs_comp
    rw [hs_card] at hle
    omega
  -- hence `S` is finite with at most `N` elements
  obtain ⟨hSfin, hSncard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hSenc
  refine ⟨hSfin.toFinset, ?_, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card S hSfin]
    exact hSncard
  · intro B hB
    rw [Set.Finite.mem_toFinset hSfin] at hB
    rw [hSdef, Set.mem_image] at hB
    obtain ⟨x, hxX, rfl⟩ := hB
    exact ⟨connectedComponentIn_subset X x, ⟨x, mem_connectedComponentIn hxX⟩,
      isPreconnected_connectedComponentIn⟩
  · intro x hx
    refine ⟨connectedComponentIn X x, ?_, mem_connectedComponentIn hx⟩
    rw [Finset.mem_coe, Set.Finite.mem_toFinset hSfin, hSdef]
    exact ⟨x, hx, rfl⟩

end Work.WilE2
