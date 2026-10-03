import Mathlib

namespace Work.FIArea7

/-- Fibre-mass bound: if `g` maps `T` into `s` and every `g`-fibre of `T` has at most `M`
elements, then `Σ_{p ∈ T} f (g p)² ≤ M * Σ_{z ∈ s} f z²`. -/
lemma mass_le_of_fibre_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (T : Finset (ι × ι)) (M : ℝ) (g : ι × ι → ι) (hg : ∀ p ∈ T, g p ∈ s)
    (h : ∀ z ∈ s, ((T.filter (fun p => g p = z)).card : ℝ) ≤ M) :
    (∑ p ∈ T, f (g p) ^ 2) ≤ M * (∑ z ∈ s, f z ^ 2) := by
  rw [← Finset.sum_fiberwise_of_maps_to hg (fun p => f (g p) ^ 2)]
  calc ∑ z ∈ s, ∑ p ∈ T with g p = z, f (g p) ^ 2
      = ∑ z ∈ s, ((T.filter (fun p => g p = z)).card : ℝ) * f z ^ 2 := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ s, M * f z ^ 2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_right (h z hz) (sq_nonneg _)
    _ = M * ∑ z ∈ s, f z ^ 2 := by rw [Finset.mul_sum]

/-- **Pair-count Cauchy–Schwarz with fibre bounds.**  If `T ⊆ s × s` and every row and every
column of `T` has at most `M` elements, then the `f`-mass of `T` is at most `M` times the `L²`-mass
of `s`:
`Σ_{(x,y) ∈ T} f x * f y ≤ M * Σ_{x ∈ s} f x ^ 2`.
(Proof: Cauchy–Schwarz on `T` and `Σ_{(x,y) ∈ T} f x ² = Σ_{x ∈ s} (row count x) * f x².) -/
theorem pairMass_fibre_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (T : Finset (ι × ι)) (M : ℝ) (hM : 0 ≤ M)
    (hT1 : ∀ p ∈ T, p.1 ∈ s) (hT2 : ∀ p ∈ T, p.2 ∈ s)
    (h1 : ∀ z ∈ s, ((T.filter (fun p => p.1 = z)).card : ℝ) ≤ M)
    (h2 : ∀ z ∈ s, ((T.filter (fun p => p.2 = z)).card : ℝ) ≤ M) :
    (∑ p ∈ T, f p.1 * f p.2) ≤ M * (∑ z ∈ s, f z ^ 2) := by
  have hrow := mass_le_of_fibre_le s f T M Prod.fst hT1 h1
  have hcol := mass_le_of_fibre_le s f T M Prod.snd hT2 h2
  -- termwise AM–GM: `2 * f x * f y ≤ f x ^ 2 + f y ^ 2`
  have hamgm : ∀ p ∈ T, 2 * (f p.1 * f p.2) ≤ f p.1 ^ 2 + f p.2 ^ 2 := by
    intro p _
    have h := two_mul_le_add_sq (f p.1) (f p.2)
    rw [mul_assoc] at h
    exact h
  have key : 2 * (∑ p ∈ T, f p.1 * f p.2) ≤ 2 * (M * (∑ z ∈ s, f z ^ 2)) := by
    calc 2 * (∑ p ∈ T, f p.1 * f p.2)
        = ∑ p ∈ T, 2 * (f p.1 * f p.2) := by rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ T, (f p.1 ^ 2 + f p.2 ^ 2) := Finset.sum_le_sum hamgm
      _ = (∑ p ∈ T, f p.1 ^ 2) + (∑ p ∈ T, f p.2 ^ 2) := by rw [Finset.sum_add_distrib]
      _ ≤ M * (∑ z ∈ s, f z ^ 2) + M * (∑ z ∈ s, f z ^ 2) := add_le_add hrow hcol
      _ = 2 * (M * (∑ z ∈ s, f z ^ 2)) := by ring
  exact le_of_mul_le_mul_left key (by norm_num)

end Work.FIArea7
