import Mathlib

namespace Work.L62

open Complex Set Metric Filter Topology
open scoped Topology

/-- **Shishikura, Lemma 6.2 (local form).**  If `h` agrees near `a` with the parabolic germ
`z ↦ z + (z - a)^m g z` (`m ≥ 2`, `g` analytic at `a`), then for every `n`
`(h^[n] z - z) / (z - a)^m → n * g a` as `z → a` through the punctured neighbourhood. -/
theorem tendsto_iterate_sub_div_pow {h : ℂ → ℂ} {a : ℂ} {m : ℕ} (hm : 2 ≤ m) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g a) (hU : ∀ᶠ z in 𝓝 a, h z = z + (z - a) ^ m * g z) (n : ℕ) :
    Tendsto (fun z => (h^[n] z - z) / (z - a) ^ m) (𝓝[≠] a) (𝓝 ((n : ℂ) * g a)) := by
  have hm1 : 1 ≤ m := by omega
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul]
      refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
      filter_upwards with z
      simp [Function.iterate_zero_apply]
  | succ n ih =>
      -- `z - a → 0` (in the punctured neighbourhood)
      have hza : Tendsto (fun z : ℂ => z - a) (𝓝[≠] a) (𝓝 (0 : ℂ)) := by
        have h0 : Tendsto (fun z : ℂ => z) (𝓝[≠] a) (𝓝 a) :=
          (tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 a) (𝓝 a)).mono_left
            (nhdsWithin_le_nhds (s := {a}ᶜ))
        simpa using h0.sub (tendsto_const_nhds (x := a))
      -- `(z - a)^{m-1} → 0`
      have hpow : Tendsto (fun z : ℂ => (z - a) ^ (m - 1)) (𝓝[≠] a) (𝓝 (0 : ℂ)) := by
        have hne : m - 1 ≠ 0 := by omega
        simpa [zero_pow hne] using hza.pow (m - 1)
      -- `(h^[n] z - z)/(z - a) → 0`
      have hprod : Tendsto (fun z => (h^[n] z - z) / (z - a)) (𝓝[≠] a) (𝓝 (0 : ℂ)) := by
        have hmul := ih.mul hpow
        have heq : (fun z => (h^[n] z - z) / (z - a)) =ᶠ[𝓝[≠] a]
            (fun z => (h^[n] z - z) / (z - a) ^ m * (z - a) ^ (m - 1)) := by
          filter_upwards [self_mem_nhdsWithin] with z hzne
          have hz : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hzne)
          have h1 : (z - a) ^ m = (z - a) ^ (m - 1) * (z - a) := by
            nth_rewrite 1 [← Nat.sub_add_cancel hm1]
            rw [pow_succ]
          rw [div_mul_eq_mul_div, div_eq_div_iff hz (pow_ne_zero m hz)]
          rw [mul_assoc, ← h1]
        simpa using hmul.congr' heq.symm
      -- `(h^[n] z - a)/(z - a) → 1`
      have hB : Tendsto (fun z => (h^[n] z - a) / (z - a)) (𝓝[≠] a) (𝓝 (1 : ℂ)) := by
        have hsum := hprod.add (tendsto_const_nhds (x := (1 : ℂ)))
        have heq : (fun z => (h^[n] z - a) / (z - a)) =ᶠ[𝓝[≠] a]
            (fun z => (h^[n] z - z) / (z - a) + 1) := by
          filter_upwards [self_mem_nhdsWithin] with z hzne
          have hz : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hzne)
          field_simp
          ring
        simpa using hsum.congr' heq.symm
      -- `h^[n] z → a`
      have hha : Tendsto (fun z => h^[n] z) (𝓝[≠] a) (𝓝 a) := by
        have hsub : Tendsto (fun z => h^[n] z - a) (𝓝[≠] a) (𝓝 (0 : ℂ)) := by
          have hmul := hB.mul hza
          have heq : (fun z => h^[n] z - a) =ᶠ[𝓝[≠] a]
              (fun z => (h^[n] z - a) / (z - a) * (z - a)) := by
            filter_upwards [self_mem_nhdsWithin] with z hzne
            have hz : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hzne)
            field_simp
          simpa using hmul.congr' heq.symm
        have hadd := hsub.add (tendsto_const_nhds (x := a))
        have heq : (fun z => h^[n] z) =ᶠ[𝓝[≠] a] (fun z => (h^[n] z - a) + a) := by
          filter_upwards with z
          ring
        simpa using hadd.congr' heq.symm
      -- `g (h^[n] z) → g a`
      have hgt : Tendsto (fun z => g (h^[n] z)) (𝓝[≠] a) (𝓝 (g a)) :=
        hg.continuousAt.tendsto.comp hha
      -- the recursion for the numerator of `F_{n+1}`
      have heq1 : (fun z => (h^[n + 1] z - z) / (z - a) ^ m) =ᶠ[𝓝[≠] a]
          (fun z => ((h^[n] z - a) / (z - a)) ^ m * g (h^[n] z)
            + (h^[n] z - z) / (z - a) ^ m) := by
        filter_upwards [hha.eventually hU] with z hzU
        rw [Function.iterate_succ_apply', hzU]
        have hA : ((h^[n] z - a) ^ m * g (h^[n] z)) / (z - a) ^ m
            = ((h^[n] z - a) / (z - a)) ^ m * g (h^[n] z) := by
          rw [div_pow, div_mul_eq_mul_div]
        rw [show h^[n] z + (h^[n] z - a) ^ m * g (h^[n] z) - z
              = (h^[n] z - z) + (h^[n] z - a) ^ m * g (h^[n] z) from by ring,
            add_div, hA]
        ring
      -- limit of the right-hand side
      have hterm : Tendsto (fun z => ((h^[n] z - a) / (z - a)) ^ m * g (h^[n] z))
          (𝓝[≠] a) (𝓝 (g a)) := by
        have h1 : Tendsto (fun z => ((h^[n] z - a) / (z - a)) ^ m) (𝓝[≠] a) (𝓝 (1 : ℂ)) := by
          simpa using hB.pow m
        simpa using h1.mul hgt
      have hsum : Tendsto (fun z =>
            ((h^[n] z - a) / (z - a)) ^ m * g (h^[n] z) + (h^[n] z - z) / (z - a) ^ m)
          (𝓝[≠] a) (𝓝 (g a + (n : ℂ) * g a)) := by
        simpa using hterm.add ih
      have hres := hsum.congr' heq1.symm
      have ht : g a + (n : ℂ) * g a = ((n + 1 : ℕ) : ℂ) * g a := by
        push_cast
        ring
      rw [ht] at hres
      exact hres

end Work.L62
