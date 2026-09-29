import Mathlib

namespace Work.Holonomy3

open scoped BigOperators

/-- If `S : Finset (Fin d)` has cardinality `k`, then its `i`-th smallest element (given by the
increasing parametrisation `S.orderEmbOfFin`) is at most `d - k + i`, because the `k - i`
elements of `S` from position `i` on are `k - i` distinct elements of `Fin d` lying to the right
of it. -/
lemma orderEmbOfFin_apply_le {d : ℕ} (S : Finset (Fin d)) (i : Fin S.card) :
    (S.orderEmbOfFin rfl i : ℕ) ≤ d - S.card + i := by
  have hkd : S.card ≤ d := by
    have := Finset.card_le_card (Finset.subset_univ S); simpa using this
  -- the `k - i` elements `S ∩ [e i, ∞)` embed into the `d - e i` elements of `Fin d` that
  -- are `≥ e i`.
  have h1 : (Finset.image (S.orderEmbOfFin rfl) (Finset.Ici i)).card ≤
      (Finset.Ici ((S.orderEmbOfFin rfl) i) : Finset (Fin d)).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Ici] at hx ⊢
    obtain ⟨j, hj, rfl⟩ := hx
    exact (S.orderEmbOfFin rfl).monotone hj
  rw [Finset.card_image_of_injective _ (S.orderEmbOfFin rfl).injective] at h1
  simp only [Fin.card_Ici] at h1
  omega

/-- The sum of a monotone `ℕ`-valued function over a finset `S ⊆ Fin d` is at most its sum over
the top `t` positions, whenever `S.card ≤ t`. (Layer-cake / majorisation argument.) -/
theorem sum_le_top_of_monotone {d t : ℕ} (ht : t ≤ d) {g : Fin d → ℕ} (hg : Monotone g)
    (S : Finset (Fin d)) (hcard : S.card ≤ t) :
    ∑ s ∈ S, g s ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin d => d - t ≤ (j : ℕ)), g j := by
  set T : Finset (Fin d) := Finset.univ.filter (fun j : Fin d => d - t ≤ (j:ℕ)) with hTdef
  -- rewrite the sum over `S` as a sum over its positions `Fin S.card`
  have hS : ∑ s ∈ S, g s = ∑ i : Fin S.card, g (S.orderEmbOfFin rfl i) := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
    rw [Finset.sum_map]
    simp
  rw [hS]
  -- parametrise the top `t` positions by `Fin t`
  set ψ : Fin t → Fin d := fun i => ⟨d - t + i, by have := i.2; omega⟩ with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h : (ψ a : ℕ) = (ψ b : ℕ) := congrArg Fin.val hab
    simp only [hψdef] at h
    omega
  have himage : Finset.image ψ Finset.univ = T := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hTdef, Finset.mem_filter]
    constructor
    · rintro ⟨i, rfl⟩
      simp only [hψdef]
      omega
    · intro hj
      refine ⟨⟨(j:ℕ) - (d - t), by have := j.isLt; omega⟩, ?_⟩
      ext
      simp only [hψdef]
      omega
  have hTsum : ∑ j ∈ T, g j = ∑ i : Fin t, g (ψ i) := by
    rw [← himage, Finset.sum_image]
    intro a _ b _ hab
    exact hψinj hab
  rw [hTsum]
  -- map the `i`-th smallest element of `S` to the `(t - S.card + i)`-th smallest of the top `t`
  set φ : Fin S.card → Fin t := fun i => ⟨t - S.card + i, by have := i.2; omega⟩ with hφdef
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h : (φ a : ℕ) = (φ b : ℕ) := congrArg Fin.val hab
    simp only [hφdef] at h
    omega
  have hpt : ∑ i : Fin S.card, g (S.orderEmbOfFin rfl i) ≤ ∑ i : Fin S.card, g (ψ (φ i)) := by
    apply Finset.sum_le_sum
    intro i _
    apply hg
    rw [Fin.le_def]
    have hk := orderEmbOfFin_apply_le S i
    have hψφ : (ψ (φ i) : ℕ) = d - S.card + i := by
      simp only [hψdef, hφdef]
      omega
    omega
  refine le_trans hpt ?_
  -- the `S.card` positions `t - S.card + i` used by `φ` are all among the `t` positions of `T`
  have h1 : ∑ x ∈ Finset.image φ Finset.univ, g (ψ x) ≤
      ∑ x ∈ (Finset.univ : Finset (Fin t)), g (ψ x) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx; simp
    · intro x _ _; exact Nat.zero_le _
  have h2 : ∑ x ∈ Finset.image φ Finset.univ, g (ψ x) = ∑ i : Fin S.card, g (ψ (φ i)) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hφinj hab
  rw [← h2]
  exact h1

end Work.Holonomy3
