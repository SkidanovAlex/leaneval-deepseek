import Mathlib

namespace Work.WilE3K

/-- Combinatorial core: a finite set `s`, mapped into a type `α` by two injective maps `F`, `G`
whose images are disjoint, produces at least `2 * s.card` distinct points among the pairs
`{F z, G z}`, `z ∈ s`. -/
lemma two_mul_card_le_card_biUnion_pair {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (F G : ι → α) (hF : Function.Injective F) (hG : Function.Injective G)
    (hd : Disjoint (s.image F) (s.image G)) :
    2 * s.card ≤ (s.biUnion (fun z => ({F z, G z} : Finset α))).card := by
  have himgF : (s.image F).card = s.card := Finset.card_image_of_injective s hF
  have himgG : (s.image G).card = s.card := Finset.card_image_of_injective s hG
  have hsub : s.image F ∪ s.image G ⊆ s.biUnion (fun z => ({F z, G z} : Finset α)) := by
    intro w hw
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · rw [Finset.mem_image] at hw
      obtain ⟨z, hzs, rfl⟩ := hw
      exact Finset.mem_biUnion.mpr ⟨z, hzs, by simp⟩
    · rw [Finset.mem_image] at hw
      obtain ⟨z, hzs, rfl⟩ := hw
      exact Finset.mem_biUnion.mpr ⟨z, hzs, by simp⟩
  have hcard : (s.image F ∪ s.image G).card = 2 * s.card := by
    rw [Finset.card_union_of_disjoint hd, himgF, himgG]
    omega
  calc 2 * s.card = (s.image F ∪ s.image G).card := hcard.symm
    _ ≤ (s.biUnion (fun z => ({F z, G z} : Finset α))).card := Finset.card_le_card hsub

/-- The `±` sphere lift of a finite set of interior points of the ball of radius `√c` in
`ℝ^{N+1}` has at least `2 * s.card` elements in `ℝ^{N+2}`: each point `z` of `s` gives the two
distinct points `Fin.snoc z (±√(c - ∑ z k²))`, and the two sheets are disjoint. -/
theorem two_mul_card_le_card_sphereLift {N : ℕ} (s : Finset (Fin (N + 1) → ℝ)) (c : ℝ)
    (hc : ∀ z ∈ s, (∑ k : Fin (N + 1), (z k) ^ 2) < c) :
    2 * s.card ≤ (s.biUnion (fun z =>
      ({Fin.snoc z (Real.sqrt (c - ∑ k : Fin (N + 1), (z k) ^ 2)),
        Fin.snoc z (-(Real.sqrt (c - ∑ k : Fin (N + 1), (z k) ^ 2)))} :
        Finset (Fin ((N + 1) + 1) → ℝ)))).card := by
  let F : (Fin (N + 1) → ℝ) → (Fin ((N + 1) + 1) → ℝ) :=
    fun z => Fin.snoc z (Real.sqrt (c - ∑ k : Fin (N + 1), (z k) ^ 2))
  let G : (Fin (N + 1) → ℝ) → (Fin ((N + 1) + 1) → ℝ) :=
    fun z => Fin.snoc z (-(Real.sqrt (c - ∑ k : Fin (N + 1), (z k) ^ 2)))
  change 2 * s.card ≤
    (s.biUnion (fun z => ({F z, G z} : Finset (Fin ((N + 1) + 1) → ℝ)))).card
  refine two_mul_card_le_card_biUnion_pair s F G ?_ ?_ ?_
  · -- injectivity of the `+` sheet, from `Fin.init (Fin.snoc z _) = z`
    intro z z' h
    have h2 : Fin.init (F z) = Fin.init (F z') := by rw [h]
    simpa [F] using h2
  · -- injectivity of the `-` sheet
    intro z z' h
    have h2 : Fin.init (G z) = Fin.init (G z') := by rw [h]
    simpa [G] using h2
  · -- the two sheets are disjoint: a common point would force `√(c - ∑z²) = -√(c - ∑z²)`
    rw [Finset.disjoint_left]
    intro w hwF hwG
    rw [Finset.mem_image] at hwF hwG
    obtain ⟨z, hzs, rfl⟩ := hwF
    obtain ⟨z', hz's, hz'eq⟩ := hwG
    have hzz' : z' = z := by
      have h2 : Fin.init (G z') = Fin.init (F z) := by rw [hz'eq]
      simpa [F, G] using h2
    rw [hzz'] at hz'eq
    have hlast : -(Real.sqrt (c - ∑ k : Fin (N + 1), (z k) ^ 2))
        = Real.sqrt (c - ∑ k : Fin (N + 1), (z k) ^ 2) := by
      have hh := congrFun hz'eq (Fin.last (N + 1))
      simpa [F, G] using hh
    have hpos : 0 < Real.sqrt (c - ∑ k : Fin (N + 1), (z k) ^ 2) :=
      Real.sqrt_pos_of_pos (by have := hc z hzs; linarith)
    linarith

end Work.WilE3K
