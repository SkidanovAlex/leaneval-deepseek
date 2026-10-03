import Mathlib
import Submission.Work.Normal.montel_omits_three
import Submission.Work.Normal.hurwitz_nonvanishing
import Submission.Work.Normal.Basic

/-!
# A normal family of zero-free holomorphic functions converging to `0` at one point

This file proves the lemma used in the proof of Shishikura's Lemma 6.1 (area `L61`): if `v n` is a
sequence of holomorphic functions on a preconnected open set `U ⊆ ℂ`, none of which vanishes on
`U`, the family `{v n}` is normal on `U`, and `v n z₀ → 0` for some `z₀ ∈ U`, then `v n → 0`
locally uniformly on `U`.

The argument is the classical one.  Any subsequence of `v` has (by normality) a further
subsequence converging locally uniformly on `U` to a holomorphic `g`, or tending locally uniformly
to `∞`; the second alternative is impossible because `v n z₀ → 0` while a compact neighbourhood of
`z₀` lies in `U`.  In the first alternative `g z₀ = 0`, so Hurwitz's non-vanishing theorem
(`Work.Normal.hurwitz_nonvanishing`) together with the preconnectedness of `U` forces `g ≡ 0`.
Hence every subsequence has a further subsequence converging locally uniformly to `0`; the
elementary principle `tendsto_of_forall_subseq` upgrades this to convergence of the whole sequence.
-/

namespace Work.L61.Normal

open Filter Set Topology Metric

/-- If every strictly monotone subsequence of a sequence of functions `u n : ℂ → ℂ` admits a
further strictly monotone subsequence converging locally uniformly on an open set `U ⊆ ℂ` to `g`,
then `u` itself converges locally uniformly to `g` on `U`. -/
theorem tendsto_of_forall_subseq {U : Set ℂ} (hUo : IsOpen U)
    {u : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun n => u (φ (ψ n))) g Filter.atTop U) :
    TendstoLocallyUniformlyOn u g Filter.atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨ns, hns, hbad⟩ := Filter.exists_seq_forall_of_frequently hcon
  obtain ⟨χ, -, hχ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ψ, hψ, htu⟩ := h (ns ∘ χ) hχ
  have htuK : TendstoUniformlyOn (fun n => u ((ns ∘ χ) (ψ n))) g atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (htu.mono hKU)
  rw [Metric.tendstoUniformlyOn_iff] at htuK
  obtain ⟨n, hn⟩ := (htuK ε hε).exists
  exact hbad (χ (ψ n)) hn

/-- **Extraction step.** Under the hypotheses of `tendsto_zero_of_normal`, every strictly monotone
subsequence of `v` has a further strictly monotone subsequence converging locally uniformly to `0`
on `U`. -/
theorem exists_subseq_tendsto_zero {U : Set ℂ} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {v : ℕ → ℂ → ℂ} (hhol : ∀ n, DifferentiableOn ℂ (v n) U)
    (hne : ∀ n z, z ∈ U → v n z ≠ 0) (hnorm : Work.Normal.IsNormalFamily (Set.range v) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h0 : Filter.Tendsto (fun n => v n z₀) Filter.atTop (nhds 0)) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun n => v (φ (ψ n))) (fun _ => 0) Filter.atTop U := by
  intro φ hφ
  obtain ⟨ψ, hψ, ⟨g, hlim⟩ | hlim⟩ := hnorm (fun n => v (φ n)) (fun n => ⟨φ n, rfl⟩)
  · -- The extracted subsequence converges locally uniformly to some `g : ℂ → ℂ`.
    have hcomp : Tendsto (fun n => v (φ (ψ n)) z₀) atTop (𝓝 0) :=
      h0.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
    have hgz₀ : g z₀ = 0 := tendsto_nhds_unique (hlim.tendsto_at hz₀) hcomp
    rcases Work.Normal.hurwitz_nonvanishing hUo hUpc (fun n => v (φ (ψ n))) g
      (fun n => hhol (φ (ψ n))) (fun n z hz => hne (φ (ψ n)) z hz) hlim with hne' | hzero
    · exact absurd hgz₀ (hne' z₀ hz₀)
    · exact ⟨ψ, hψ, hlim.congr_right (fun z hz => hzero z hz)⟩
  · -- The extracted subsequence cannot tend locally uniformly to `∞`.
    exfalso
    obtain ⟨δ, hδpos, hδU⟩ : ∃ δ > 0, closedBall z₀ δ ⊆ U := by
      obtain ⟨ρ, hρpos, hρU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hz₀)
      refine ⟨ρ / 2, half_pos hρpos, fun z hz => hρU ?_⟩
      simp only [mem_ball, mem_closedBall] at hz ⊢
      linarith
    have hbig : ∃ N : ℕ, ∀ n ≥ N, (1 : ℝ) ≤ ‖v (φ (ψ n)) z₀‖ := by
      obtain ⟨N, hN⟩ := hlim (closedBall z₀ δ) hδU (isCompact_closedBall z₀ δ) 1
      exact ⟨N, fun n hn => hN n hn z₀ (mem_closedBall_self hδpos.le)⟩
    obtain ⟨N, hN⟩ := hbig
    have hcomp : Tendsto (fun n => v (φ (ψ n)) z₀) atTop (𝓝 0) :=
      h0.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
    have hsmall : ∀ᶠ n in atTop, ‖v (φ (ψ n)) z₀‖ < 1 := by
      have h1 : Tendsto (fun n => ‖v (φ (ψ n)) z₀‖) atTop (𝓝 0) := by
        simpa only [Function.comp_def, norm_zero] using
          (continuous_norm.tendsto (0 : ℂ)).comp hcomp
      exact h1.eventually_lt_const zero_lt_one
    obtain ⟨n, hn, hnN⟩ := (hsmall.and (eventually_ge_atTop N)).exists
    have hbad := hN n hnN
    linarith

/-- **Normal families of zero-free functions converging to `0` at one point.** Let `U ⊆ ℂ` be open
and preconnected, `v n` holomorphic and zero-free on `U`, and suppose the family `{v n}` is normal
on `U`.  If `v n z₀ → 0` for some `z₀ ∈ U`, then `v n → 0` locally uniformly on `U`. -/
theorem tendsto_zero_of_normal {U : Set ℂ} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {v : ℕ → ℂ → ℂ} (hhol : ∀ n, DifferentiableOn ℂ (v n) U)
    (hne : ∀ n z, z ∈ U → v n z ≠ 0) (hnorm : Work.Normal.IsNormalFamily (Set.range v) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h0 : Filter.Tendsto (fun n => v n z₀) Filter.atTop (nhds 0)) :
    TendstoLocallyUniformlyOn v (fun _ => 0) Filter.atTop U := by
  exact tendsto_of_forall_subseq hUo (exists_subseq_tendsto_zero hUo hUpc hhol hne hnorm hz₀ h0)

end Work.L61.Normal
