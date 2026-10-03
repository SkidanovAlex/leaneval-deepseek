import Mathlib
import Submission.Work.A3.Weil.Defs

/-!
# The autocorrelation (van der Corput) inequality behind Weyl differencing

For a sequence `v : ℤ → ℂ` vanishing off the window `wRange N = [0,N)` we prove

`‖∑_{n ∈ wRange N} v n‖ ^ 2 ≤ ∑_{h ∈ shiftIdx N} ‖∑_{n ∈ wRange N} v (n + h) * conj (v n)‖`.

This is the elementary step that turns the `2^k`-th power of an exponential sum into the
`k`-fold autocorrelation sums `iterCorr` (see `Work.A3.Weil.iter_differencing`): it is the
`k = 0` case of the van der Corput recursion.

The mathematics is the identity
`(∑_n v n) * conj (∑_n v n) = ∑_h (∑_n v (n + h) * conj (v n))`,
i.e. `|S|² = ∑_h C_h` with `C_h` the `h`-th autocorrelation, followed by the triangle
inequality `|∑_h C_h| ≤ ∑_h |C_h|`.  (The sum over `h` may be taken over all of `ℤ`: the
term `C_h` vanishes unless `|h| ≤ N - 1`, and it is for this reason that the statement is
written with the finite shift set `shiftIdx N`.)
-/

namespace Work.A3.Weil

/-- **Reindexing.**  If `v` vanishes off `wRange N` and `n ∈ wRange N`, then the `star`-sum of
`v` over the window may be reindexed over the shifts: `∑_{h ∈ shiftIdx N} star (v (n + h))` has
the same value, because every term with `n + h ∉ wRange N` vanishes. -/
private lemma sum_star_v_eq_sum_shift {N : ℕ} {v : ℤ → ℂ}
    (hv : ∀ n : ℤ, n ∉ wRange N → v n = 0) {n : ℤ} (hn : n ∈ wRange N) :
    ∑ h ∈ shiftIdx N, star (v (n + h)) = ∑ m ∈ wRange N, star (v m) := by
  have hn' : (0 : ℤ) ≤ n ∧ n ≤ (N : ℤ) - 1 := by
    simpa [wRange, Finset.mem_Icc] using hn
  have hmap : Finset.Icc (0 : ℤ) ((N : ℤ) - 1)
      = Finset.map (addRightEmbedding n) (Finset.Icc (-n) ((N : ℤ) - 1 - n)) := by
    rw [Finset.map_add_right_Icc]
    congr 1 <;> omega
  have h1 : ∑ m ∈ wRange N, star (v m)
      = ∑ h ∈ Finset.Icc (-n) ((N : ℤ) - 1 - n), star (v (n + h)) := by
    rw [wRange, hmap, Finset.sum_map]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp only [addRightEmbedding_apply]
    rw [add_comm h n]
  have hsub : Finset.Icc (-n) ((N : ℤ) - 1 - n) ⊆ shiftIdx N := by
    intro h hh
    simp only [shiftIdx, Finset.mem_Icc] at hh ⊢
    omega
  have hzero : ∀ h ∈ shiftIdx N, h ∉ Finset.Icc (-n) ((N : ℤ) - 1 - n) →
      star (v (n + h)) = 0 := by
    intro h hZ hnot
    have hZ' : -((N : ℤ) - 1) ≤ h ∧ h ≤ (N : ℤ) - 1 := by
      simpa [shiftIdx, Finset.mem_Icc] using hZ
    have hnot' : ¬ ((-n ≤ h) ∧ (h ≤ (N : ℤ) - 1 - n)) := fun hh =>
      hnot (Finset.mem_Icc.mpr hh)
    rw [not_and_or, not_le, not_le] at hnot'
    have hmem : n + h ∉ wRange N := by
      simp only [wRange, Finset.mem_Icc]
      omega
    simp [hv _ hmem]
  calc ∑ h ∈ shiftIdx N, star (v (n + h))
      = ∑ h ∈ Finset.Icc (-n) ((N : ℤ) - 1 - n), star (v (n + h)) :=
        (Finset.sum_subset (s₁ := Finset.Icc (-n) ((N : ℤ) - 1 - n))
          (s₂ := shiftIdx N) hsub hzero).symm
    _ = ∑ m ∈ wRange N, star (v m) := h1.symm

/-- **The autocorrelation identity.**  For `v` vanishing off `wRange N`,
`(∑_n v n) * star (∑_n v n) = star (∑_{h ∈ shiftIdx N} ∑_{n ∈ wRange N} v (n + h) * star (v n))`,
i.e. `|S|² = ∑_h C_h`. -/
private lemma mul_star_sum_eq_sum_corr {N : ℕ} {v : ℤ → ℂ}
    (hv : ∀ n : ℤ, n ∉ wRange N → v n = 0) :
    (∑ n ∈ wRange N, v n) * star (∑ n ∈ wRange N, v n)
      = star (∑ h ∈ shiftIdx N, ∑ n ∈ wRange N, v (n + h) * star (v n)) := by
  have key1 : (∑ n ∈ wRange N, v n) * star (∑ n ∈ wRange N, v n)
      = ∑ h ∈ shiftIdx N, ∑ n ∈ wRange N, v n * star (v (n + h)) := by
    rw [star_sum, Finset.sum_mul_sum]
    have inner : ∀ n ∈ wRange N, (∑ m ∈ wRange N, v n * star (v m))
        = ∑ h ∈ shiftIdx N, v n * star (v (n + h)) := by
      intro n hn
      rw [← Finset.mul_sum, ← sum_star_v_eq_sum_shift hv hn, Finset.mul_sum]
    rw [Finset.sum_congr rfl inner, Finset.sum_comm]
  have key2 : star (∑ h ∈ shiftIdx N, ∑ n ∈ wRange N, v (n + h) * star (v n))
      = ∑ h ∈ shiftIdx N, ∑ n ∈ wRange N, v n * star (v (n + h)) := by
    rw [star_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [star_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [star_mul, star_star])
  exact key1.trans key2.symm

theorem normSq_le_sum_corr {N : ℕ} {v : ℤ → ℂ}
    (hv : ∀ n : ℤ, n ∉ Work.A3.Weil.wRange N → v n = 0) :
    ‖∑ n ∈ Work.A3.Weil.wRange N, v n‖ ^ 2 ≤
      ∑ h ∈ Work.A3.Weil.shiftIdx N,
        ‖∑ n ∈ Work.A3.Weil.wRange N, v (n + h) * star (v n)‖ := by
  classical
  have hA := mul_star_sum_eq_sum_corr hv
  have hnorm : ‖∑ n ∈ wRange N, v n‖ ^ 2
      = ‖∑ h ∈ shiftIdx N, ∑ n ∈ wRange N, v (n + h) * star (v n)‖ := by
    have h1 : ‖∑ n ∈ wRange N, v n‖ ^ 2
        = ‖(∑ n ∈ wRange N, v n) * star (∑ n ∈ wRange N, v n)‖ := by
      rw [norm_mul, norm_star, pow_two]
    rw [h1, hA, norm_star]
  calc ‖∑ n ∈ wRange N, v n‖ ^ 2
      = ‖∑ h ∈ shiftIdx N, ∑ n ∈ wRange N, v (n + h) * star (v n)‖ := hnorm
    _ ≤ ∑ h ∈ shiftIdx N, ‖∑ n ∈ wRange N, v (n + h) * star (v n)‖ :=
        norm_sum_le _ _

end Work.A3.Weil
