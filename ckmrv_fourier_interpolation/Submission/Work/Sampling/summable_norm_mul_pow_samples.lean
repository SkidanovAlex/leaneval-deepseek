import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Sampling.summable_norm_mul_pow

set_option linter.style.haveILetI false

namespace Work.Sampling

open LeanEval.Analysis.CKMRVInterpolation
open Filter Topology

/-!
# Summability of a rapidly decreasing sequence times a polynomial weight

If a complex sequence indexed by `Set.Ici k₀` is rapidly decreasing (every
natural power of the index times its norm tends to `0`), then multiplying its
norm by the weight `(k + 1) ^ N` still leaves a summable sequence.  Consequently
the corresponding family over `Set.Ici k₀ × Fin 4` is summable as well, which is
the elementary summability input to the CKMRV interpolation theorem.
-/

/-- **A rapidly decreasing sequence times any polynomial weight is summable.**

Rapid decrease with exponent `N + 2` gives `k ^ (N + 2) * ‖b k‖ ≤ 1` for all
large `k`; for `k ≥ 1` the inequality `(k + 1) ^ N ≤ (2 k) ^ N` then bounds the
weighted term by `2 ^ N / k ^ 2`, which is summable.  Only finitely many small
`k` remain. -/
private lemma summable_of_rapidlyDecreasing {k₀ : ℕ} (N : ℕ) (b : Set.Ici k₀ → ℂ)
    (hb : RapidlyDecreasing b) :
    Summable fun k : Set.Ici k₀ => ‖b k‖ * (((k.1 : ℕ) : ℝ) + 1) ^ N := by
  haveI : Nonempty (Set.Ici k₀) := ⟨⟨k₀, by simp⟩⟩
  -- The dominating summable sequence `k ↦ 2 ^ N / (k : ℝ) ^ 2`.
  have hg : Summable fun k : Set.Ici k₀ => (2:ℝ)^N / (k.1 : ℝ)^2 := by
    have hnat1 : Summable fun n : ℕ => 1 / (n : ℝ)^2 :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have hnat2 : Summable fun n : ℕ => (2:ℝ)^N * (1 / (n : ℝ)^2) :=
      hnat1.mul_left ((2:ℝ)^N)
    have hnat3 : Summable fun n : ℕ => (2:ℝ)^N / (n : ℝ)^2 :=
      hnat2.congr (fun n => by rw [mul_one_div])
    exact hnat3.subtype (fun n => k₀ ≤ n)
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  -- Eventually, `(k : ℝ) ^ (N + 2) * ‖b k‖ ≤ 1` and `k ≥ 1`.
  have hev : ∀ᶠ k : Set.Ici k₀ in Filter.atTop,
      ((k.1 : ℝ)^(N + 2) * ‖b k‖ ≤ 1) ∧ (1 ≤ (k.1 : ℕ)) := by
    have h1 : ∀ᶠ k : Set.Ici k₀ in Filter.atTop, (k.1 : ℝ)^(N + 2) * ‖b k‖ ≤ 1 :=
      (hb (N + 2)).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
    have h2 : ∀ᶠ k : Set.Ici k₀ in Filter.atTop, (1 : ℕ) ≤ k.1 := by
      filter_upwards
        [Filter.eventually_ge_atTop (⟨(max k₀ 1 : ℕ), le_max_left k₀ 1⟩ : Set.Ici k₀)]
        with k hk
      exact le_trans (le_max_right k₀ 1) (show (max k₀ 1 : ℕ) ≤ k.1 from hk)
    exact h1.and h2
  obtain ⟨b₀, hb₀⟩ := Filter.eventually_atTop.mp hev
  -- It remains to show that the set where the bound fails is finite.
  refine Set.Finite.subset
    ((Set.finite_Iio b₀.1).preimage (fun x _ y _ h => Subtype.coe_injective h)) ?_
  intro k hk
  simp only [Set.mem_preimage, Set.mem_Iio]
  by_contra hlt
  have hlt' : b₀.1 ≤ k.1 := not_lt.mp hlt
  have hbk : b₀ ≤ k := hlt'
  obtain ⟨hdec, h1⟩ := hb₀ k hbk
  apply hk
  have hnonneg : 0 ≤ ‖b k‖ * (((k.1 : ℕ) : ℝ) + 1) ^ N :=
    mul_nonneg (norm_nonneg _) (by positivity)
  rw [Real.norm_of_nonneg hnonneg]
  have hn1 : (1:ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast h1
  have hn2pos : 0 < (k.1 : ℝ)^2 := by positivity
  rw [le_div_iff₀ hn2pos]
  calc ‖b k‖ * (((k.1 : ℕ) : ℝ) + 1)^N * (k.1 : ℝ)^2
      ≤ ‖b k‖ * (2 * (k.1 : ℝ))^N * (k.1 : ℝ)^2 := by
        gcongr
        linarith
    _ = (2:ℝ)^N * ((k.1 : ℝ)^(N + 2) * ‖b k‖) := by
        rw [mul_pow, pow_add]; ring
    _ ≤ (2:ℝ)^N * 1 := by
        exact mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = (2:ℝ)^N := by ring

theorem summable_norm_mul_pow_samples (k₀ N : ℕ) (a : Set.Ici k₀ × Fin 4 → ℂ)
    (ha : RapidlyDecreasingSamples a) :
    Summable fun i : Set.Ici k₀ × Fin 4 => ‖a i‖ * (((i.1.1 : ℕ) : ℝ) + 1) ^ N := by
  have hf : (0 : Set.Ici k₀ × Fin 4 → ℝ) ≤
      fun i => ‖a i‖ * (((i.1.1 : ℕ) : ℝ) + 1)^N :=
    fun i => mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) N)
  refine (summable_prod_of_nonneg
    (f := fun i : Set.Ici k₀ × Fin 4 => ‖a i‖ * (((i.1.1 : ℕ) : ℝ) + 1)^N) hf).mpr ⟨?_, ?_⟩
  · intro x
    exact Summable.of_finite
  · have hslice : ∀ y : Fin 4,
        Summable fun x : Set.Ici k₀ => ‖a (x, y)‖ * (((x.1 : ℕ) : ℝ) + 1)^N :=
      fun y => summable_of_rapidlyDecreasing N (fun x => a (x, y)) (ha y)
    have hsum : Summable fun x : Set.Ici k₀ =>
        ∑ y : Fin 4, ‖a (x, y)‖ * (((x.1 : ℕ) : ℝ) + 1)^N :=
      summable_sum (f := fun y x => ‖a (x, y)‖ * (((x.1 : ℕ) : ℝ) + 1)^N)
        (s := Finset.univ) (fun y _ => hslice y)
    refine hsum.congr (fun x => ?_)
    rw [tsum_fintype]

end Work.Sampling
