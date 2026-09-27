import Mathlib

namespace Work.EQ

open Filter Metric Set
open scoped Topology

set_option linter.style.haveILetI false

/-- If a function `P : ℂ → ℕ` is locally constant on `ℂ \ {0}` in the sense that each point
`u ≠ 0` has a punctured neighbourhood on which `P` is constant, then the constant is the same
everywhere.  This is the statement that `ℂ \ {0}` is (pre)connected: the "eventual value"
function is locally constant and therefore constant. -/
theorem exists_common_eventual_value {P : ℂ → ℕ}
    (h : ∀ u : ℂ, u ≠ 0 → ∃ N : ℕ, ∀ᶠ v in nhdsWithin u {u}ᶜ, P v = N) :
    ∃ n : ℕ, ∀ u : ℂ, u ≠ 0 → ∀ᶠ v in nhdsWithin u {u}ᶜ, P v = n := by
  classical
  -- Rewrite the local constancy hypothesis in balls: every `u ≠ 0` has a value `N u` and a
  -- radius `r u > 0` such that `P = N u` on `ball u (r u) \ {u}`.
  have hball : ∀ u : ℂ, u ≠ 0 → ∃ N : ℕ, ∃ r : ℝ,
      0 < r ∧ ∀ v : ℂ, v ≠ u → dist v u < r → P v = N := by
    intro u hu
    obtain ⟨N, hN⟩ := h u hu
    rw [eventually_nhdsWithin_iff] at hN
    rw [Metric.eventually_nhds_iff] at hN
    obtain ⟨r, hr, hN⟩ := hN
    exact ⟨N, r, hr, fun v hv hd => hN hd hv⟩
  choose! N r hr hP using hball
  -- `ℂ \ {0}` is preconnected.
  haveI : PreconnectedSpace {u : ℂ // u ≠ 0} := by
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [← Module.finrank_eq_rank', Complex.finrank_real_complex]
      norm_num
    have hconn : IsConnected ({0}ᶜ : Set ℂ) := isConnected_compl_singleton_of_one_lt_rank hrank 0
    have hset : ({u : ℂ | u ≠ 0} : Set ℂ) = {0}ᶜ := by ext u; simp
    have hpre : IsPreconnected ({u : ℂ | u ≠ 0} : Set ℂ) := by
      rw [hset]; exact hconn.isPreconnected
    exact Subtype.preconnectedSpace hpre
  -- The "eventual value" function on `ℂ \ {0}` is locally constant.
  have hg : IsLocallyConstant (fun x : {u : ℂ // u ≠ 0} => N x.1) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{y : {u : ℂ // u ≠ 0} | dist y.1 x.1 < r x.1},
      isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const, ?_, ?_⟩
    · show dist x.1 x.1 < r x.1
      simpa using hr x.1 x.2
    · intro y hy
      show N y.1 = N x.1
      by_cases hyx : y.1 = x.1
      · rw [hyx]
      · -- `y` shares the value of `x`: a point of the punctured neighbourhood of `y` also lies in
        -- the punctured neighbourhood of `x`.
        have hAy : ∀ᶠ v in 𝓝[{y.1}ᶜ] y.1, P v = N x.1 := by
          have hopen : IsOpen ((ball x.1 (r x.1)) \ ({x.1} : Set ℂ)) :=
            Metric.isOpen_ball.sdiff isClosed_singleton
          have hyopen : y.1 ∈ (ball x.1 (r x.1)) \ ({x.1} : Set ℂ) :=
            ⟨by simpa using hy, by simpa using hyx⟩
          have hmem : (ball x.1 (r x.1)) \ ({x.1} : Set ℂ) ∈ 𝓝[{y.1}ᶜ] y.1 :=
            nhdsWithin_le_nhds (hopen.mem_nhds hyopen)
          filter_upwards [hmem] with v hv
          exact hP x.1 x.2 v (by simpa using hv.2) (by simpa using hv.1)
        have hB : ∀ᶠ v in 𝓝[{y.1}ᶜ] y.1, P v = N y.1 := by
          rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
          exact ⟨r y.1, hr y.1 y.2, fun v hv hvmem => hP y.1 y.2 v (by simpa using hvmem) hv⟩
        obtain ⟨v, hvA, hvB⟩ := (hAy.and hB).exists
        exact hvB.symm.trans hvA
  refine ⟨N 1, fun u hu => ?_⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨r u, hr u hu, fun v hv hvmem => ?_⟩
  have hNu : N u = N 1 := by
    have := hg.apply_eq_of_preconnectedSpace (x := ⟨u, hu⟩) (y := ⟨1, one_ne_zero⟩)
    simpa using this
  rw [← hNu]
  exact hP u hu v (by simpa using hvmem) hv

end Work.EQ
