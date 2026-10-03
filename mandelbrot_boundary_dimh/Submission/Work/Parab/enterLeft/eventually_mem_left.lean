import Mathlib
import Submission.Work.Parab.petal_cone

namespace Work.Parab.enterLeft

/-!
# An inverse orbit of `f₀` converging to `0` eventually lies in the repelling petal

Shishikura, *The Hausdorff dimension of the boundary of the Mandelbrot set* (arXiv math/9201282),
Lemma 5.1 (`ParabData.invOrbit`).  The flower `Ωp ∪ φ '' QLeft ξ ∪ {0}` is a neighbourhood of `0`,
so an inverse orbit `z` tending to `0` is eventually in the flower.  It cannot be in the attracting
petal `Ωp`: on `Ωp` the iterates of `f₀` converge to `0` *uniformly*, and since `f₀(z (j+1)) = z j`
iterating `j - j₁` times sends `z j` to `z j₁`; a uniform bound `< ‖z j₁‖/2` for `j - j₁ ≥ N`
would then force `‖z j₁‖ < ‖z j₁‖/2`.  Nor can `z j` vanish: the vanishing indices form an initial
segment, and past the first non-zero index `j₁` of `z` (which exists by `hne`) `z` never vanishes.
Hence `z j ∈ φ '' QLeft ξ` for all large `j`.
-/

open Complex Set Metric Filter
open scoped Topology

/-- **Iterating the inverse orbit relation.**  `f₀^[k] (z (j + k)) = z j`. -/
theorem iterate_invOrbit {f₀ : ℂ → ℂ} {z : ℕ → ℂ} (hz : ∀ j : ℕ, f₀ (z (j + 1)) = z j) :
    ∀ k j : ℕ, (f₀^[k]) (z (j + k)) = z j := by
  intro k
  induction k with
  | zero => intro j; simp
  | succ k ih =>
    intro j
    rw [Function.iterate_succ_apply', show j + (k + 1) = (j + 1) + k from by omega, ih (j + 1),
      hz j]

/-- **The vanishing indices of an inverse orbit form an initial segment.** -/
theorem zero_prefix {f₀ : ℂ → ℂ} {z : ℕ → ℂ} (hf0 : f₀ 0 = 0)
    (hz : ∀ j : ℕ, f₀ (z (j + 1)) = z j) :
    ∀ i : ℕ, z i = 0 → ∀ m : ℕ, m ≤ i → z m = 0 := by
  intro i
  induction i with
  | zero =>
    intro h m hm
    have : m = 0 := Nat.le_zero.mp hm
    subst this
    exact h
  | succ i ih =>
    intro h m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · have hzi : z i = 0 := by rw [← hz i, h, hf0]
      exact ih hzi m (Nat.lt_succ_iff.mp hlt)
    · exact heq ▸ h

set_option linter.unusedVariables false in
theorem eventually_mem_left {f₀ : ℂ → ℂ} {Ωp : Set ℂ} {φ : ℂ → ℂ} {ξ : ℝ}
    (hzero : (0 : ℂ) ∉ Ωp) (hf0 : f₀ 0 = 0)
    (hconvΩ : ∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ u ∈ Ωp, ‖(f₀^[k]) u‖ < ε)
    (hflower : Ωp ∪ φ '' MandelDim.QLeft ξ ∪ {0} ∈ nhds (0 : ℂ))
    {z : ℕ → ℂ} (hz : ∀ j : ℕ, f₀ (z (j + 1)) = z j)
    (hlim : Filter.Tendsto z Filter.atTop (nhds (0 : ℂ))) (hne : ∃ j : ℕ, z j ≠ 0) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∃ u ∈ MandelDim.QLeft ξ, φ u = z j := by
  -- (1) the first index where `z` is non-zero
  set j₁ := Nat.find hne with hj₁
  have hzj₁ : z j₁ ≠ 0 := Nat.find_spec hne
  -- past `j₁` the sequence never vanishes again
  have hne_zero : ∀ j : ℕ, j₁ ≤ j → z j ≠ 0 := by
    intro j hj h
    exact hzj₁ (zero_prefix hf0 hz j h j₁ hj)
  -- (2) uniformity of the attraction on `Ωp`: nothing in `Ωp` survives `N` steps
  obtain ⟨N, hN⟩ := hconvΩ (‖z j₁‖ / 2) (by positivity)
  have hnotΩp : ∀ j : ℕ, j₁ + N ≤ j → z j ∉ Ωp := by
    intro j hj hmem
    have hj₁j : j₁ ≤ j := le_trans (Nat.le_add_right j₁ N) hj
    have hk : N ≤ j - j₁ := Nat.le_sub_of_add_le (by omega : N + j₁ ≤ j)
    have hiter := iterate_invOrbit hz (j - j₁) j₁
    rw [Nat.add_sub_cancel' hj₁j] at hiter
    have hbound := hN (j - j₁) hk (z j) hmem
    rw [hiter] at hbound
    have hpos : 0 < ‖z j₁‖ := norm_pos_iff.mpr hzj₁
    linarith
  -- (3) eventually in the flower
  have hev : ∀ᶠ j in Filter.atTop, z j ∈ Ωp ∪ φ '' MandelDim.QLeft ξ ∪ {0} :=
    hlim.eventually hflower
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hev
  -- (4) assemble
  refine ⟨max 1 (max (j₁ + N) N₂), le_max_left _ _, fun j hj => ?_⟩
  have hJ₁ : j₁ ≤ j :=
    le_trans (Nat.le_add_right j₁ N) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hj))
  have hJN : j₁ + N ≤ j := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hj)
  have hJN₂ : N₂ ≤ j := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hj)
  have hmem := hN₂ j hJN₂
  rw [Set.mem_union, Set.mem_union] at hmem
  rcases hmem with (hΩ | himg) | h0
  · exact absurd hΩ (hnotΩp j hJN)
  · exact Set.mem_image _ _ _ |>.mp himg
  · exact absurd (Set.mem_singleton_iff.mp h0) (hne_zero j hJ₁)

end Work.Parab.enterLeft
