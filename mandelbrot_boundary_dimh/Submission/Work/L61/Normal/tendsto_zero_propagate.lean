import Mathlib
import Submission.Work.Normal.montel_omits_three
import Submission.Work.Normal.hurwitz_nonvanishing
import Submission.Work.Normal.Basic
import Submission.Work.Normal.isNormalFamily_of_tendsto_iterate

namespace Work.L61.Normal

open Filter Topology Set
open scoped Topology

/-- Reindexing a sequence that tends locally uniformly to `∞` by a map tending to `atTop`. -/
theorem tendstoLocallyUniformlyAtTop_comp {F : ℕ → ℂ → ℂ} {U : Set ℂ} {φ : ℕ → ℕ}
    (h : Work.Normal.TendstoLocallyUniformlyAtTop F U) (hφ : Tendsto φ atTop atTop) :
    Work.Normal.TendstoLocallyUniformlyAtTop (fun n => F (φ n)) U := by
  intro K hKU hK R
  obtain ⟨N, hN⟩ := h K hKU hK R
  obtain ⟨M, hM⟩ :=
    eventually_atTop.mp (hφ.eventually (eventually_atTop.mpr ⟨N, fun n hn => hn⟩))
  exact ⟨M, fun n hn z hz => hN (φ n) (hM n hn) z hz⟩

theorem tendsto_zero_propagate {U V : Set ℂ} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    (hVo : IsOpen V) (hUV : (U ∩ V).Nonempty) {v w : ℕ → ℂ → ℂ}
    (hholv : ∀ n, DifferentiableOn ℂ (v n) U) (hholw : ∀ n, DifferentiableOn ℂ (w n) V)
    (hnev : ∀ n z, z ∈ U → v n z ≠ 0) (hnew : ∀ n z, z ∈ V → w n z ≠ 0)
    (hnormv : Work.Normal.IsNormalFamily (Set.range v) U)
    (hnormw : Work.Normal.IsNormalFamily (Set.range w) V)
    (hagree : ∀ n, Set.EqOn (v n) (w n) (U ∩ V))
    (hw : TendstoLocallyUniformlyOn w (fun _ => 0) Filter.atTop V) :
    TendstoLocallyUniformlyOn v (fun _ => 0) Filter.atTop U := by
  -- The agreement on `U ∩ V` transfers the convergence from `V` to `U ∩ V`.
  have hVUV : TendstoLocallyUniformlyOn v (fun _ => 0) atTop (U ∩ V) :=
    (hw.mono inter_subset_right).congr (fun n => (hagree n).symm)
  obtain ⟨z₀, hz₀U, hz₀V⟩ := hUV
  have hz₀UV : z₀ ∈ U ∩ V := ⟨hz₀U, hz₀V⟩
  -- It suffices to prove uniform convergence on every compact subset of `U`.
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUo]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  -- Failure gives a strictly monotone subsequence carrying large values on `K`.
  have hfreq : ∃ᶠ n in atTop, ∃ x ∈ K, ε ≤ dist (0 : ℂ) (v n x) :=
    (not_eventually.mp hcon).mono (fun n hn => by
      push Not at hn
      exact hn)
  obtain ⟨ns, hnsmono, hns⟩ := extraction_of_frequently_atTop hfreq
  -- Normality of `v` on `U` extracts a further subsequence.
  obtain ⟨ψ, hψmono, hcase⟩ := hnormv (fun k => v (ns k)) (fun k => ⟨ns k, rfl⟩)
  have hν : Tendsto (fun k => ns (ψ k)) atTop atTop :=
    hnsmono.tendsto_atTop.comp hψmono.tendsto_atTop
  have hFUV : TendstoLocallyUniformlyOn (fun k => v (ns (ψ k))) (fun _ => 0)
      atTop (U ∩ V) :=
    Work.Normal.TendstoLocallyUniformlyOn.comp_strictMono_atTop hVUV hν
  rcases hcase with ⟨g, hgU⟩ | hinf
  · -- The convergent alternative: the limit vanishes on `U ∩ V`, hence on `U`.
    have hgUV : TendstoLocallyUniformlyOn (fun k => v (ns (ψ k))) g atTop (U ∩ V) :=
      hgU.mono inter_subset_left
    have hg0 : Set.EqOn g (fun _ => 0) (U ∩ V) := hgUV.unique hFUV
    have hgdiff : DifferentiableOn ℂ g U :=
      hgU.differentiableOn (Eventually.of_forall (fun k => hholv (ns (ψ k)))) hUo
    have hfz : g =ᶠ[𝓝 z₀] 0 :=
      eventually_of_mem ((hUo.inter hVo).mem_nhds hz₀UV) (fun z hz => hg0 hz)
    have hgz : Set.EqOn g (fun _ => 0) U :=
      (hgdiff.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUpc hz₀U hfz
    have hF0U : TendstoLocallyUniformlyOn (fun k => v (ns (ψ k))) (fun _ => 0) atTop U :=
      hgU.congr_right hgz
    have hunif : TendstoUniformlyOn (fun k => v (ns (ψ k))) (fun _ => 0) atTop K :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).mp hF0U K hKU hK
    obtain ⟨M, hM⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hunif ε hε)
    obtain ⟨x, hxK, hx⟩ := hns (ψ M)
    exact absurd (hM M le_rfl x hxK) (not_lt.mpr hx)
  · -- The `→∞` alternative contradicts convergence to `0` at the point `z₀ ∈ U ∩ V`.
    have hz0 : Tendsto (fun k => v (ns (ψ k)) z₀) atTop (𝓝 (0 : ℂ)) :=
      hFUV.tendsto_at hz₀UV
    obtain ⟨N, hN⟩ := hinf {z₀} (by rw [Set.singleton_subset_iff]; exact hz₀U)
      isCompact_singleton (1 : ℝ)
    have hev : ∀ᶠ k in atTop, dist (v (ns (ψ k)) z₀) (0 : ℂ) < 1 :=
      hz0.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    have h1 := hN (max N M) (le_max_left _ _) z₀ rfl
    have h2 := hM (max N M) (le_max_right _ _)
    rw [dist_eq_norm, sub_zero] at h2
    linarith

end Work.L61.Normal
