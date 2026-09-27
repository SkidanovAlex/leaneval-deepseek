import Mathlib
import Submission.Work.EQ.TailGlueDefs

namespace Work.EQ.Tl

open Complex Filter _root_.Topology

/-- **A local right inverse of `t ↦ z₀ + t^N` around a nonzero point.**

Given `t ≠ 0` and `‖t‖ < ρ`, there is a function `g` with `g (z₀ + t^N) = t`, with
`z₀ + (g u)^N = u` for *every* `u`, which is continuous on a neighbourhood of `z₀ + t^N` and
sends that neighbourhood into the punctured disc `0 < ‖·‖ < ρ`.  The inverse is the explicit
principal-branch formula `g u = t · (((u - z₀)/t^N)^(1/N))`, whose derivative at `t` is nonzero. -/
lemma local_inv_pow (z₀ t : ℂ) (N : ℕ) (hN : N ≠ 0) (ht : t ≠ 0) {ρ : ℝ}
    (htρ : ‖t‖ < ρ) :
    ∃ g : ℂ → ℂ,
      g (z₀ + t^N) = t ∧
      (∀ u, z₀ + (g u)^N = u) ∧
      ∃ ε : ℝ, 0 < ε ∧ ContinuousOn g (Metric.ball (z₀ + t^N) ε) ∧
        ∀ u ∈ Metric.ball (z₀ + t^N) ε, 0 < ‖g u‖ ∧ ‖g u‖ < ρ := by
  let s : ℂ := (N : ℂ)⁻¹
  let hfun : ℂ → ℂ := fun u => (u - z₀) / t^N
  let g : ℂ → ℂ := fun u => t * (hfun u) ^ s
  have htN : t^N ≠ 0 := pow_ne_zero N ht
  have hgpow : ∀ u, (g u)^N = u - z₀ := by
    intro u
    simp only [g, hfun, s]
    rw [mul_pow, Complex.cpow_nat_inv_pow _ hN]
    rw [mul_comm (t^N), div_mul_cancel₀ _ htN]
  have hhfun_at : hfun (z₀ + t^N) = 1 := by
    simp only [hfun]
    rw [add_sub_cancel_left, div_self htN]
  have hgt : g (z₀ + t^N) = t := by
    simp only [g, hhfun_at]
    rw [Complex.one_cpow, mul_one]
  have hcont_hfun : Continuous hfun := by
    simp only [hfun]
    exact (continuous_id.sub continuous_const).div_const _
  have hpre : hfun ⁻¹' slitPlane ∈ 𝓝 (z₀ + t^N) :=
    hcont_hfun.continuousAt
      (isOpen_slitPlane.mem_nhds (by rw [hhfun_at]; exact one_mem_slitPlane))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hgc : ContinuousOn g (Metric.ball (z₀ + t^N) r) := by
    unfold g
    refine continuousOn_const.mul ?_
    exact ((hcont_hfun.continuousOn).mono (Set.subset_univ _)).cpow_const
      (fun u hu => hrsub hu)
  have hgat : ContinuousAt g (z₀ + t^N) :=
    hgc.continuousAt (Metric.ball_mem_nhds _ hr)
  have hδ : 0 < min ‖t‖ (ρ - ‖t‖) := lt_min (norm_pos_iff.mpr ht) (sub_pos.mpr htρ)
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.continuousAt_iff.mp hgat (min ‖t‖ (ρ - ‖t‖)) hδ
  refine ⟨g, hgt, fun u => ?_, min r ε₁, lt_min hr hε₁, ?_, ?_⟩
  · rw [hgpow]; ring
  · exact hgc.mono (Metric.ball_subset_ball (min_le_left _ _))
  · intro u hu
    have hu₁ : dist u (z₀ + t^N) < ε₁ :=
      lt_of_lt_of_le (Metric.mem_ball.mp hu) (min_le_right _ _)
    have hd : ‖g u - t‖ < min ‖t‖ (ρ - ‖t‖) := by
      have := hε₁sub hu₁
      rwa [hgt, dist_eq_norm] at this
    have hm1 : ‖g u - t‖ < ‖t‖ := lt_of_lt_of_le hd (min_le_left _ _)
    have hm2 : ‖g u - t‖ < ρ - ‖t‖ := lt_of_lt_of_le hd (min_le_right _ _)
    constructor
    · have h1 : ‖t‖ ≤ ‖t - g u‖ + ‖g u‖ := by
        have := norm_add_le (t - g u) (g u)
        rwa [sub_add_cancel] at this
      rw [norm_sub_rev] at h1
      linarith
    · have h1 : ‖g u‖ ≤ ‖g u - t‖ + ‖t‖ := by
        have := norm_add_le (g u - t) t
        rwa [sub_add_cancel] at this
      linarith

/-- **A glued family that is a continuous family of chains on a punctured disc lies in `⁰H`.**

If `t' ↦ tailGlue a h c z₀ dep σ t'` is continuous on the punctured disc `0 < ‖t'‖ < ρ` and every
one of its values there is a chain of the equichordal relation, then each of those values lies in
Rychlik's connection surface `⁰H`: the local family witnessing the definition of `H0` is obtained
by reparametrising with a local inverse of `t ↦ z₀ + t^(2^(2*dep))`, whose derivative is nonzero at
`t ≠ 0`. -/
theorem mem_H0_tailGlue {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {c z₀ : ℂ} (hz₀ : z₀ ≠ 0) {dep : ℕ} (hdep : 1 ≤ dep) {σ : Fin (2 * dep) → Bool}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn (fun t' : ℂ => tailGlue a h c z₀ dep σ t')
      {t' : ℂ | 0 < ‖t'‖ ∧ ‖t'‖ < ρ})
    {t : ℂ} (ht : 0 < ‖t‖) (htρ : ‖t‖ < ρ)
    (hchain : ∀ t' : ℂ, 0 < ‖t'‖ → ‖t'‖ < ρ → IsChain a h (tailGlue a h c z₀ dep σ t')) :
    tailGlue a h c z₀ dep σ t ∈ H0 a h := by
  have hNne : 2 ^ (2 * dep) ≠ 0 := pow_ne_zero _ (by norm_num)
  have htne : t ≠ 0 := norm_pos_iff.mp ht
  obtain ⟨g, hgt, hgpow, ε, hεpos, hgcont, hgsmall⟩ :=
    local_inv_pow z₀ t (2 ^ (2 * dep)) hNne htne htρ
  refine ⟨ε, hεpos, fun u => tailGlue a h c z₀ dep σ (g u), ?_, ?_, ?_⟩
  · have hmaps : Set.MapsTo g (Metric.ball (z₀ + t ^ (2 ^ (2 * dep))) ε)
        {t' : ℂ | 0 < ‖t'‖ ∧ ‖t'‖ < ρ} := fun u hu => hgsmall u hu
    exact hcont.comp hgcont hmaps
  · change tailGlue a h c z₀ dep σ (g (z₀ + t ^ (2 ^ (2 * dep)))) = tailGlue a h c z₀ dep σ t
    rw [hgt]
  · intro u hu
    refine ⟨hchain (g u) (hgsmall u hu).1 (hgsmall u hu).2, ?_⟩
    rw [tailGlue_psi1]
    exact hgpow u

end Work.EQ.Tl
