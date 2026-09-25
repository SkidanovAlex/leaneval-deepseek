import Mathlib.Analysis.Meromorphic.Divisor
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal

open Filter Metric
open scoped Topology

namespace Commons.NumberTheory.Zeta

noncomputable section

/-- The entire Riemann xi function `Ξ(s) = 1/2 + (1/2)·s·(s−1)·Λ₀(s)`. -/
private def xiC (s : ℂ) : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

private lemma xiC_differentiable : Differentiable ℂ xiC := by
  unfold xiC
  have h1 : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by fun_prop
  have h2 : Differentiable ℂ (fun s : ℂ => completedRiemannZeta₀ s) :=
    differentiable_completedZeta₀
  exact (differentiable_const (1 / 2 : ℂ)).add (h1.mul h2)

private lemma xiC_analyticAt (z : ℂ) : AnalyticAt ℂ xiC z := xiC_differentiable.analyticAt z

/-- The prefactor `s ↦ (1/2)·s·Γℝ(s)` relating `Ξ` to `riemannZeta₁`. -/
private def xiHead (s : ℂ) : ℂ := (1 / 2 : ℂ) * s * Complex.Gammaℝ s

private lemma xiHead_analyticAt {ρ : ℂ} (hre : 0 < ρ.re) : AnalyticAt ℂ xiHead ρ := by
  have hGinv : AnalyticAt ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) ρ :=
    Complex.differentiable_Gammaℝ_inv.analyticAt ρ
  have hne : ((fun z : ℂ => (Complex.Gammaℝ z)⁻¹) ρ) ≠ 0 := by
    simpa using inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hre)
  have hG : AnalyticAt ℂ (fun z : ℂ => Complex.Gammaℝ z) ρ :=
    (hGinv.inv hne).congr (by filter_upwards with z; simp)
  exact (analyticAt_const.mul analyticAt_id).mul hG

private lemma xiHead_ne_zero {ρ : ℂ} (hre : 0 < ρ.re) : xiHead ρ ≠ 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  unfold xiHead
  exact mul_ne_zero (mul_ne_zero (by norm_num) hρ0) (Complex.Gammaℝ_ne_zero_of_re_pos hre)

/-- Near any point of the strip `Re s > 1/4` the Riemann xi function agrees with
`(1/2)·s·Γℝ(s)·riemannZeta₁(s)`. -/
private lemma xiC_eventuallyEq {ρ : ℂ} (hre : (1 / 4 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1) :
    xiC =ᶠ[𝓝[≠] ρ] xiHead * riemannZeta₁ := by
  have hopen : IsOpen {z : ℂ | (1 / 4 : ℝ) < z.re} :=
    isOpen_Ioi.preimage Complex.continuous_re
  have hre_nhds : ∀ᶠ z in 𝓝 ρ, (1 / 4 : ℝ) < z.re := hopen.mem_nhds hre
  have h1_nhds : ∀ᶠ z in 𝓝 ρ, z ≠ 1 :=
    isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hρ1)
  filter_upwards [hre_nhds.filter_mono nhdsWithin_le_nhds,
    h1_nhds.filter_mono nhdsWithin_le_nhds] with z hzre hz1
  have hz0 : z ≠ 0 := by
    intro h
    have h0 : z.re = 0 := by rw [h]; simp
    linarith
  have hzG : 0 < z.re := by linarith
  have hG : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hzG
  have hΛ0 : completedRiemannZeta₀ z = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    rw [completedRiemannZeta_eq]; ring
  have hΛ : completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z := by
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp
  have hζ : riemannZeta₁ z = (z - 1) * riemannZeta z := by
    rw [riemannZeta_eq_inv_sub_mul hz1]
    field_simp
  simp only [xiC, xiHead, Pi.mul_apply]
  rw [hΛ0, hΛ, hζ]
  field_simp
  ring

/-- If `logDeriv f` has a simple pole with residue `m` at `ρ`, then the order of vanishing of `f`
at `ρ` equals `m`. -/
private lemma meromorphicOrderAt_eq_of_logDeriv_sub_pole {f : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f ρ) (hρ : f ρ = 0) (hnot : ¬(∀ᶠ z in 𝓝 ρ, f z = 0)) (_hm : 1 ≤ m)
    (hF : ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, F s = logDeriv f s - m / (s - ρ)) :
    meromorphicOrderAt f ρ = (m : ℤ) := by
  rcases (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hf).mpr hnot with
    ⟨n, g, hg, hgρ, hfac⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · exfalso
      subst hn0
      have hfac0 : ∀ᶠ z in 𝓝 ρ, f z = g z := by
        filter_upwards [hfac] with z hz
        simpa using hz
      exact hgρ (hfac0.self_of_nhds.symm.trans hρ)
    · exact hpos
  obtain ⟨F, hFan, hFev⟩ := hF
  obtain ⟨F', hF'an, hF'ev⟩ := logDeriv_sub_pole_analyticAt hf hρ hg hgρ hfac hn1
  have hkey : (fun s => (s - ρ) * (F s - F' s)) =ᶠ[𝓝[≠] ρ]
      (fun _ => (n : ℂ) - (m : ℂ)) := by
    filter_upwards [hFev, hF'ev, eventually_mem_nhdsWithin] with s hs hs' hmem
    have hsne : s - ρ ≠ 0 := sub_ne_zero.mpr hmem
    rw [hs, hs']
    field_simp
    ring
  have hcont : Tendsto (fun s => (s - ρ) * (F s - F' s)) (𝓝 ρ) (𝓝 0) := by
    have hca : ContinuousAt (fun s : ℂ => (s - ρ) * (F s - F' s)) ρ :=
      (continuousAt_id.sub continuousAt_const).mul (hFan.continuousAt.sub hF'an.continuousAt)
    simpa using hca.tendsto
  have h2 : Tendsto (fun s => (s - ρ) * (F s - F' s)) (𝓝[≠] ρ) (𝓝 ((n : ℂ) - (m : ℂ))) :=
    tendsto_const_nhds.congr' hkey.symm
  have h3 : Tendsto (fun s => (s - ρ) * (F s - F' s)) (𝓝[≠] ρ) (𝓝 0) :=
    hcont.mono_left nhdsWithin_le_nhds
  have hnmC : (n : ℂ) - (m : ℂ) = 0 := tendsto_nhds_unique h2 h3
  have hnm : n = m := by
    have hcast : (n : ℂ) = (m : ℂ) := sub_eq_zero.mp hnmC
    exact Nat.cast_inj.mp hcast
  rw [← hnm]
  refine (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).2 ⟨g, hg, hgρ, ?_⟩
  filter_upwards [hfac.filter_mono nhdsWithin_le_nhds] with z hz
  simpa [zpow_natCast] using hz

theorem divisor_xi_eq_logDeriv_pole_order {R : ℝ} (hR : 0 ≤ R) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (hρR : ‖ρ‖ ≤ R) (hre : (1 / 4 : ℝ) < ρ.re)
    (hre2 : ρ.re < 2) {m : ℕ} (hm : 1 ≤ m)
    (hF : ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
      Filter.Eventually (fun s => F s = logDeriv riemannZeta₁ s - m / (s - ρ))
        (nhdsWithin ρ {s : ℂ | s ≠ ρ})) :
    (m : ℤ) = (MeromorphicOn.divisor (fun z : ℂ =>
        (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
      (Metric.closedBall 0 R)) ρ := by
  change (m : ℤ) = (MeromorphicOn.divisor xiC (Metric.closedBall 0 R)) ρ
  have hρre : 0 < ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, riemannZeta₁_one] at hρ
    exact one_ne_zero hρ
  have hρK : ρ ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hρR
  have hξmero : MeromorphicOn xiC (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => (xiC_analyticAt z).meromorphicAt
  have hordξ : meromorphicOrderAt xiC ρ = meromorphicOrderAt riemannZeta₁ ρ := by
    rw [meromorphicOrderAt_congr (xiC_eventuallyEq hre hρ1)]
    exact meromorphicOrderAt_mul_of_ne_zero (xiHead_analyticAt hρre) (xiHead_ne_zero hρre)
  have hordf : meromorphicOrderAt riemannZeta₁ ρ = (m : ℤ) :=
    meromorphicOrderAt_eq_of_logDeriv_sub_pole (differentiable_riemannZeta₁.analyticAt ρ) hρ
      (riemannZeta₁_not_eventually_zero ρ) hm hF
  rw [MeromorphicOn.divisor_apply hξmero hρK, hordξ, hordf]
  simp

end

end Commons.NumberTheory.Zeta