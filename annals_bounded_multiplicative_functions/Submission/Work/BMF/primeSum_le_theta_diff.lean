import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- Fiber containment: if `p ≤ ⌊x⌋` is a prime with `⌊x/p⌋₊ = n`, then `p` lies in
`(⌊x/n⌋₊).primesLE` and strictly above `⌊x/(n+1)⌋₊`. This is the combinatorial content of the
reindexing step. -/
theorem primesLE_fiber_subset (x : ℝ) (hx : 2 ≤ x) (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) :
    (⌊x⌋₊).primesLE.filter (fun (p : ℕ) => ⌊x / (p : ℝ)⌋₊ = n) ⊆
      (⌊x / (n : ℝ)⌋₊).primesLE \ (⌊x / ((n : ℝ) + 1)⌋₊).primesLE := by
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpM, hpeq⟩ := hp
  have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpM
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
  have hfloor1 : (n : ℝ) ≤ x / (p : ℝ) := by
    have := Nat.floor_le (show 0 ≤ x / (p : ℝ) by positivity)
    rwa [hpeq] at this
  have h2 : (p : ℝ) ≤ x / (n : ℝ) := by
    rw [le_div_iff₀ hp_pos] at hfloor1
    rw [le_div_iff₀ hnpos]
    calc (p : ℝ) * (n : ℝ) = (n : ℝ) * (p : ℝ) := by ring
      _ ≤ x := hfloor1
  have hp_le : p ≤ ⌊x / (n : ℝ)⌋₊ := Nat.le_floor h2
  have h4 : x / ((n : ℝ) + 1) < (p : ℝ) := by
    have h := Nat.lt_floor_add_one (x / (p : ℝ))
    rw [hpeq] at h
    rw [div_lt_iff₀ hp_pos] at h
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    calc x < ((n : ℝ) + 1) * (p : ℝ) := h
      _ = (p : ℝ) * ((n : ℝ) + 1) := by ring
  have h3 : ⌊x / ((n : ℝ) + 1)⌋₊ < p := (Nat.floor_lt (by positivity)).mpr h4
  refine Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hp_le, hpprime⟩, ?_⟩
  intro hmem
  exact absurd (Nat.le_of_mem_primesLE hmem) (not_le.mpr h3)

/-- Reindexing + Chebyshev-step bound. For `x ≥ 2`, `M = ⌊x⌋₊`, and any nonnegative `d`,
`∑_{p ≤ M, p prime} log p · d ⌊x/p⌋₊ ≤ ∑_{n ∈ [1,M]} d n · (θ(x/n) - θ(x/(n+1)))`.

Route. (i) `Finset.sum_fiberwise_of_maps_to` with `g p = ⌊x/p⌋₊`: for `p ∈ M.primesLE` one has
`⌊x/p⌋₊ ∈ Icc 1 M` (since `p ≤ M ≤ x` and `p ≥ 2`), so the left side equals
`∑_{n∈Icc 1 M} ∑_{p ∈ M.primesLE, ⌊x/p⌋₊ = n} (log p · d n)`, i.e.
`∑_{n∈Icc 1 M} d n · c n` with `c n = ∑_{p ∈ M.primesLE, ⌊x/p⌋₊=n} log p`.
(ii) For `n ∈ Icc 1 M` and such a prime `p`: `n ≤ x/p < n+1` gives `x/(n+1) < p ≤ x/n`, hence
`p ≤ x/n` so `p ∈ (⌊x/n⌋₊).primesLE`, while `p > ⌊x/(n+1)⌋₊` so `p ∉ (⌊x/(n+1)⌋₊).primesLE`.
Thus the fiber is contained in
`(⌊x/n⌋₊).primesLE \ (⌊x/(n+1)⌋₊).primesLE`, and since
`(⌊x/(n+1)⌋₊).primesLE ⊆ (⌊x/n⌋₊).primesLE` and every fiber element is prime,
`c n ≤ ∑_{p ∈ (⌊x/n⌋₊).primesLE} log p - ∑_{p ∈ (⌊x/(n+1)⌋₊).primesLE} log p`
(`Finset.sum_sdiff`). Use `Chebyshev.theta_eq_sum_primesLE_log` and
`Chebyshev.theta_eq_theta_coe_floor` to identify these with `θ(x/n)` and `θ(x/(n+1))`.
(iii) Combine termwise using `d n ≥ 0`. -/
theorem primeSum_le_theta_diff (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊) ≤
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, d n * (Chebyshev.theta (x / n) - Chebyshev.theta (x / ((n : ℝ) + 1))) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hMle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  -- the index map `p ↦ ⌊x/p⌋₊` takes `M.primesLE` into `Icc 1 M`
  have h1 : ∀ p ∈ (⌊x⌋₊).primesLE, ⌊x / (p : ℝ)⌋₊ ∈ Finset.Icc 1 ⌊x⌋₊ := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hpx : (p : ℝ) ≤ x :=
      le_trans (by exact_mod_cast Nat.le_of_mem_primesLE hp) hMle
    rw [Finset.mem_Icc]
    constructor
    · apply Nat.le_floor
      rw [Nat.cast_one, le_div_iff₀ hp_pos, one_mul]
      exact hpx
    · apply Nat.floor_le_floor
      rw [div_le_iff₀ hp_pos]
      nlinarith [hx0, hp_pos, (by exact_mod_cast hpprime.one_le : (1 : ℝ) ≤ (p : ℝ))]
  -- reindex the left side by the fibers of `p ↦ ⌊x/p⌋₊`
  have h2 : (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * d ⌊x / p⌋₊) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, d n *
        ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun (p : ℕ) => ⌊x / (p : ℝ)⌋₊ = n), Real.log p := by
    rw [← Finset.sum_fiberwise_of_maps_to h1 (fun p => Real.log p * d ⌊x / (p : ℝ)⌋₊)]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [hp.2]
    ring
  rw [h2]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hmono : ⌊x / ((n : ℝ) + 1)⌋₊ ≤ ⌊x / (n : ℝ)⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_left hx0 hnpos (by linarith))
  have hSsub : (⌊x / ((n : ℝ) + 1)⌋₊).primesLE ⊆ (⌊x / (n : ℝ)⌋₊).primesLE :=
    Nat.primesLE_mono hmono
  have hsub := primesLE_fiber_subset x hx n hn
  apply mul_le_mul_of_nonneg_left _ (hd n)
  calc ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun (p : ℕ) => ⌊x / (p : ℝ)⌋₊ = n), Real.log p
      ≤ ∑ p ∈ ((⌊x / (n : ℝ)⌋₊).primesLE \ (⌊x / ((n : ℝ) + 1)⌋₊).primesLE), Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun (p : ℕ) hp _ =>
          Real.log_nonneg (by
            have hp1 : (1 : ℕ) ≤ p := (Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1).one_le
            exact_mod_cast hp1)
    _ = Chebyshev.theta (x / n) - Chebyshev.theta (x / ((n : ℝ) + 1)) := by
        have hsd := Finset.sum_sdiff hSsub (f := fun (p : ℕ) => Real.log (p : ℝ))
        rw [Chebyshev.theta_eq_theta_coe_floor (x / (n : ℝ)),
          Chebyshev.theta_eq_sum_primesLE_log ⌊x / (n : ℝ)⌋₊,
          Chebyshev.theta_eq_theta_coe_floor (x / ((n : ℝ) + 1)),
          Chebyshev.theta_eq_sum_primesLE_log ⌊x / ((n : ℝ) + 1)⌋₊]
        linarith [hsd]

end Work.BMF
