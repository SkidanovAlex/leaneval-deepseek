import Mathlib
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.FatouCH.Cont.InjOfTendsto
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Work.L62C.tendstoUniformlyOn_of_unique_limit
import Submission.Work.L62C.deriv_eq_zero_of_tendsto_iterate

namespace Work.L62C

open Filter Set Metric
open scoped Topology

/-- **Escape to an attracting fixed point.** `Ω ⊆ ℂ` open, bounded, preconnected, `0 ∈ Ω`; `F`
holomorphic on `Ω`, mapping `Ω` into itself, with `F 0 = 0`, injective on `Ω`, and
`‖deriv F 0‖ < 1`.  Then the iterates of `F` converge to `0` uniformly on every compact subset.

Route: `{F^[n]}` is normal on `Ω` (Montel: `F^[n] (Ω) ⊆ Ω` is bounded).  Let `g` be a locally
uniform limit of a subsequence.  Then `g 0 = 0` and `deriv g 0 = lim (deriv F 0)^n = 0`
(`TendstoLocallyUniformlyOn.deriv`).  On a ball `B ⊆ Ω` around `0` all `F^[n]` are injective, so
Hurwitz (`Work.L62.hurwitz_injOn_or_const` in `Work.FatouCH.Cont.InjOfTendsto`) gives that `g` is
injective on `B` or constant on `B`; injectivity is impossible because it would give
`deriv g 0 ≠ 0` (use `Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`, available as the
module `Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`; it is the
only genuinely complex-analytic input).  So `g ≡ 0` on `B`, and by the identity principle on the
preconnected `Ω`, `g ≡ 0` on `Ω`.  Hence every cluster point of `{F^[n]}` is `0`, so the full
sequence converges to `0` locally uniformly on `Ω`. -/
theorem escape_of_selfmap {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩpc : IsPreconnected Ω) (h0 : (0 : ℂ) ∈ Ω) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F Ω) (hmap : Set.MapsTo F Ω Ω) (hfix : F 0 = 0)
    (hinj : Set.InjOn F Ω) (hder : ‖deriv F 0‖ < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ S : Set ℂ, S ⊆ Ω → IsCompact S →
      ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ S, (F^[n]) z ∈ Metric.ball 0 δ := by
  -- The iterates of `F` stay in `Ω` and are holomorphic there.
  have hmap_n : ∀ n : ℕ, Set.MapsTo (F^[n]) Ω Ω := fun n => hmap.iterate n
  have hdiff_n : ∀ n : ℕ, DifferentiableOn ℂ (F^[n]) Ω := by
    intro n
    induction n with
    | zero => simpa using (differentiableOn_id : DifferentiableOn ℂ (id : ℂ → ℂ) Ω)
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hF.comp ih (hmap_n k)
  -- `F^[n] (Ω) ⊆ Ω` is bounded, so the iterate family is normal on `Ω` (Montel).
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hΩb
  have hbdd : ∀ n z, z ∈ Ω → ‖(F^[n]) z‖ ≤ M := fun n z hz => hM _ (hmap_n n hz)
  have hnormal : Work.Normal.IsNormalFamily (Set.range (fun n : ℕ => (F^[n]))) Ω :=
    Work.Normal.montel_locallyBounded hΩo
      (fun f hf => by obtain ⟨n, rfl⟩ := hf; exact hdiff_n n)
      (fun K hKΩ _ => ⟨M, fun f hf z hz => by
        obtain ⟨n, rfl⟩ := hf; exact hbdd n z (hKΩ hz)⟩)
  -- Every locally uniform limit of a subsequence of the iterates vanishes on `Ω`.
  have huniq : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun n => (F^[φ n])) g atTop Ω →
        Set.EqOn g (fun _ => (0 : ℂ)) Ω := by
    intro φ hφ g hlim
    have hdiffφ : ∀ n : ℕ, DifferentiableOn ℂ (F^[φ n]) Ω := fun n => hdiff_n (φ n)
    have hg_diff : DifferentiableOn ℂ g Ω :=
      hlim.differentiableOn (Eventually.of_forall hdiffφ) hΩo
    have hiter0 : ∀ n : ℕ, (F^[n]) (0 : ℂ) = 0 := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]
    have hg0 : g 0 = 0 := by
      have ht : Tendsto (fun n : ℕ => (F^[φ n]) 0) atTop (𝓝 (g 0)) := hlim.tendsto_at h0
      have ht' : Tendsto (fun n : ℕ => (0 : ℂ)) atTop (𝓝 (g 0)) := by
        refine ht.congr' ?_
        filter_upwards with n
        exact hiter0 (φ n)
      exact (tendsto_nhds_unique tendsto_const_nhds ht').symm
    have hder0 : deriv g 0 = 0 := deriv_eq_zero_of_tendsto_iterate hΩo h0 hF hmap hfix hder hφ hlim
    -- Hurwitz: `g` is injective on `Ω`, or constant on it.
    rcases Work.FatouCH.Cont.hurwitz_injOn_or_const hΩo hΩpc (Eventually.of_forall hdiffφ)
        hg_diff hlim (Eventually.of_forall (fun n => hinj.iterate hmap (φ n))) with
      hginj | ⟨c, hc⟩
    · -- Injectivity is impossible: it would force `deriv g 0 ≠ 0`.
      exfalso
      obtain ⟨r, hr0, hrΩ⟩ := Metric.mem_nhds_iff.mp (hΩo.mem_nhds h0)
      exact (Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr0
        (hg_diff.analyticAt (hΩo.mem_nhds h0)) (hginj.mono hrΩ)) hder0
    · intro z hz
      have hcc := hc 0 h0
      rw [hg0] at hcc
      rw [hc z hz, hcc.symm]
  -- Since every subsequential limit is `0`, the full sequence converges to `0`.
  have hfinal := tendstoUniformlyOn_of_unique_limit hΩo hnormal (fun n z hz => hbdd n z hz) huniq
  intro δ hδ S hSΩ hSc
  obtain ⟨N, hN⟩ := hfinal δ hδ S hSΩ hSc
  exact ⟨N, fun n hn z hz => by
    have h := hN n hn z hz
    simpa [Metric.mem_ball] using h⟩

end Work.L62C
