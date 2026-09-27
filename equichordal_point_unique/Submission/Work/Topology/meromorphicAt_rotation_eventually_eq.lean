import Mathlib

open Filter
open scoped Topology

namespace Work.Topology

/-- **Collisions with a rotation, accumulating at `0`, force a germ equality.**

If `f` is meromorphic at `0` and `f (ω * t) = f t` holds at nonzero points `t` of arbitrarily small
modulus, then the same identity holds throughout some punctured disc around `0`.

Route: `MeromorphicAt f 0` gives `n` with `t ↦ t ^ n * f t` analytic at `0`; that function `A`
satisfies `A (ω * t) = ω ^ n * A t` at the accumulating collision points, so by the identity
theorem `A (ω * t) = ω ^ n * A t` on a ball, whence `f (ω * t) = f t` wherever `t` and `ω * t` are
nonzero and inside it. -/
theorem meromorphicAt_rotation_eventually_eq {f : ℂ → ℂ} {ω : ℂ} (hω : ω ≠ 0)
    (hmer : MeromorphicAt f 0)
    (h : ∀ δ : ℝ, 0 < δ → ∃ t : ℂ, 0 < ‖t‖ ∧ ‖t‖ < δ ∧ f (ω * t) = f t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → f (ω * t) = f t := by
  obtain ⟨n, hA⟩ := hmer
  -- `A z = z ^ n • f z` is analytic at `0` by definition of meromorphy.
  set A : ℂ → ℂ := fun z => z ^ n • f z with hAdef
  have hAan : AnalyticAt ℂ A 0 := by simpa [hAdef] using hA
  -- The obstruction `B z = A (ω * z) - ω ^ n • A z` is analytic at `0`.
  have hBan : AnalyticAt ℂ (fun z => A (ω * z) - ω ^ n • A z) 0 := by
    have h1 : AnalyticAt ℂ (fun z => A (ω * z)) 0 :=
      hAan.comp_of_eq
        ((ContinuousLinearMap.analyticAt ((ContinuousLinearMap.mul ℂ ℂ) ω) 0)) (by simp)
    have h2 : AnalyticAt ℂ (fun z => ω ^ n • A z) 0 := hAan.const_smul (c := ω ^ n)
    exact h1.sub h2
  -- At every collision point, `B` vanishes.
  have hBzero : ∀ t : ℂ, f (ω * t) = f t → A (ω * t) - ω ^ n • A t = 0 := by
    intro t hft
    rw [sub_eq_zero, hAdef]
    simp only [smul_eq_mul, hft, mul_pow]
    ring
  -- Hence, by the principle of isolated zeros, `B` vanishes on a neighbourhood of `0`.
  have hBeq : ∀ᶠ z in 𝓝 (0 : ℂ), A (ω * z) - ω ^ n • A z = 0 := by
    rcases hBan.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exact h0
    · exfalso
      rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hne
      obtain ⟨ε, hε, hball⟩ := hne
      obtain ⟨t, ht0, htε, hft⟩ := h ε hε
      have htmem : t ∈ Metric.ball (0 : ℂ) ε ∩ {0}ᶜ := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right]; exact htε
        · rw [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact norm_ne_zero_iff.mp (ne_of_gt ht0)
      exact (hball htmem) (hBzero t hft)
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hBeq
  obtain ⟨δ, hδ, hball⟩ := hBeq
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ
  have hBt : A (ω * t) - ω ^ n • A t = 0 :=
    hball (by rw [Metric.mem_ball, dist_zero_right]; exact htδ)
  rw [sub_eq_zero] at hBt
  -- Unfold `A` and cancel the nonzero factor `(ω * t) ^ n`.
  have hkey : (ω * t) ^ n • f (ω * t) = (ω * t) ^ n • f t := by
    rw [hAdef] at hBt
    simp only [smul_eq_mul] at hBt ⊢
    rw [hBt]; ring
  exact (smul_right_inj (pow_ne_zero n (mul_ne_zero hω (norm_pos_iff.mp ht0)))).mp hkey

end Work.Topology
