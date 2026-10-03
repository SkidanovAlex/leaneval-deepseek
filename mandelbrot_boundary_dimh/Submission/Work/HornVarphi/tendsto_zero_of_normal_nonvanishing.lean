import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.hurwitz_nonvanishing

namespace Work.HornVarphi

open Filter Set Topology
open scoped Topology

/-- **A zero-free normal family whose members vanish at one point vanishes everywhere.**

Let `U ⊆ ℂ` be open and preconnected, let `G n` be holomorphic and zero-free on `U`, and suppose
the family `{G n}` is normal on `U` (in the single-disjunct sense of `Work.Normal.IsNormalFamily`).
If `G n z₀ → 0` at a single point `z₀ ∈ U`, then `G n → 0` locally uniformly on `U`.

Proof.  Suppose not; then there is a compact `K ⊆ U` and `ε > 0` together with a strictly monotone
sequence of indices `φ` and points `x k ∈ K` with `ε ≤ ‖G (φ k) (x k)‖`.  Normality of `{G n}`
provides a further subsequence converging locally uniformly on `U` to a limit `g`, or to `∞`.
In the second case `‖G (φ (σ k)) z₀‖ → ∞` contradicts `G n z₀ → 0`.  In the first case
`g z₀ = 0`, so Hurwitz's non-vanishing theorem (`Work.Normal.hurwitz_nonvanishing`) applied to the
zero-free holomorphic functions `G (φ (σ k))` forces `g ≡ 0` on `U` (the alternative "`g` nowhere
zero" is excluded by `g z₀ = 0`); then `G (φ (σ k)) → 0` uniformly on `K`, contradicting the
choice of the `x k`. -/
theorem tendsto_zero_of_normal_nonvanishing {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) (G : ℕ → ℂ → ℂ) (hhol : ∀ n, DifferentiableOn ℂ (G n) U) (hne : ∀ n z, z ∈ U → G n z ≠ 0) (hnorm : Work.Normal.IsNormalFamily (Set.range G) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hlim : Filter.Tendsto (fun n => G n z₀) Filter.atTop (nhds 0)) : TendstoLocallyUniformlyOn G (fun _ => 0) Filter.atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hbad
  rw [Filter.not_eventually] at hbad
  push Not at hbad
  -- `hbad` now says that the bad indices are frequent.
  have hfreq : ∃ᶠ n in atTop, ∃ x ∈ K, ε ≤ ‖G n x‖ := by
    simpa only [dist_zero_left, Pi.zero_apply] using hbad
  -- Extract a strictly monotone subsequence of bad indices.
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hfreq
  -- Apply normality to that subsequence.
  obtain ⟨σ, hσ, hres⟩ := hnorm (fun k => G (φ k)) (fun k => ⟨φ k, rfl⟩)
  have hτ : Tendsto (fun k => φ (σ k)) atTop atTop := (hφ.comp hσ).tendsto_atTop
  have h0 : Tendsto (fun k => G (φ (σ k)) z₀) atTop (nhds 0) := by
    simpa [Function.comp_def] using hlim.comp hτ
  rcases hres with ⟨g, hg⟩ | hinf
  · -- Case 1: a further subsequence converges locally uniformly to `g`.
    have hg0 : g z₀ = 0 := by
      have h1 : Tendsto (fun k => G (φ (σ k)) z₀) atTop (nhds (g z₀)) := hg.tendsto_at hz₀
      exact tendsto_nhds_unique h1 h0
    -- Hurwitz: `g` is zero-free on `U` or identically zero; the former is excluded by `g z₀ = 0`.
    have hnv := Work.Normal.hurwitz_nonvanishing hU hUc (fun k => G (φ (σ k))) g
      (fun k => hhol (φ (σ k))) (fun k z hz => hne (φ (σ k)) z hz) hg
    have hgz : ∀ z ∈ U, g z = 0 := by
      rcases hnv with h | h
      · exact absurd hg0 (h z₀ hz₀)
      · exact h
    -- Hence the subsequence converges uniformly to `0` on `K`.
    have hunif : ∀ᶠ k in atTop, ∀ x ∈ K, ‖G (φ (σ k)) x‖ < ε := by
      have hKconv : TendstoUniformlyOn (fun k => G (φ (σ k))) g atTop K :=
        (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hg K hKU hK
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hKconv ε hε] with k hk
      intro x hx
      have hxk := hk x hx
      rw [hgz x (hKU hx)] at hxk
      simpa only [dist_zero_left] using hxk
    obtain ⟨k, hk1, hk2⟩ := (hunif.and (Eventually.of_forall fun k => hφbad (σ k))).exists
    obtain ⟨x, hxK, hxε⟩ := hk2
    linarith [hk1 x hxK, hxε]
  · -- Case 2: the subsequence tends locally uniformly to `∞`, contradicting `G n z₀ → 0`.
    obtain ⟨N, hN⟩ := hinf {z₀} (by rintro z rfl; exact hz₀) isCompact_singleton (1 : ℝ)
    have h1 : ∀ᶠ k in atTop, (1 : ℝ) ≤ ‖G (φ (σ k)) z₀‖ := by
      filter_upwards [eventually_ge_atTop N] with k hk
      exact hN k hk z₀ rfl
    have h2 : ∀ᶠ k in atTop, ‖G (φ (σ k)) z₀‖ < (1 : ℝ) := by
      have hn : Tendsto (fun k => ‖G (φ (σ k)) z₀‖) atTop (nhds 0) := by
        simpa using h0.norm
      exact hn.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    linarith

end Work.HornVarphi
