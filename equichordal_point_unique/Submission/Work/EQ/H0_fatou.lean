import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_regular_aux
import Submission.Work.EQ.H0_hyperbolic
import Submission.Work.EQ.good_directions

/-!
# Fatou's theorem for a component of `H0`: the good rays

Given a covering `q : 𝔻 → S` of a component `S` of `H0` by the unit disc, the function
`z ↦ 1/ψ (q z)` is bounded (because `|ψ| ≥ ρ > 0` on `H0`).  Fatou–Riesz therefore gives, for
almost every direction `θ`, a nonzero radial limit avoiding any prescribed countable set `L`; in
particular the radius `r ↦ q (r e^{iθ})` of `S` has a `ψ`-limit `c₀` with `1/c₀ ∉ L`.  These are
the "good rays" of Rychlik's proof of Theorem 11.
-/

noncomputable section

open Filter _root_.Topology Complex Metric

namespace Work.EQ

/-- Extension of a map on the unit disc to the whole plane (constant outside the disc). -/
noncomputable def discExt {S : Type*} (q : Disc → S) : ℂ → S := by
  classical
  exact fun z =>
    if hz : z ∈ Metric.ball (0 : ℂ) 1 then q ⟨z, hz⟩ else q ⟨0, by simp [Metric.mem_ball]⟩

theorem discExt_of_mem {S : Type*} (q : Disc → S) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discExt q z = q ⟨z, hz⟩ := by
  rw [discExt, dif_pos hz]

/-- **Good rays.**  Almost every radius of the disc cover of `S` has a nonzero `ψ`-limit `c₀`
whose inverse avoids a prescribed countable set `L`. -/
theorem good_ray_data (hfatou : FatouRiesz) {a : ℝ} {h : ℂ → ℂ} {P : H0 a h} {ρ : ℝ}
    (hρ : 0 < ρ) (hbd : ∀ q : ↥(connectedComponent P), ρ ≤ ‖psi q‖)
    {q : Disc → ↥(connectedComponent P)}
    (hG : DifferentiableOn ℂ (fun z : ℂ => (psiC (discExt q z))⁻¹) (Metric.ball 0 1))
    (L : Set ℂ) (hL : L.Countable) (hLc : ∀ c ∈ L, ∃ u : Disc, (psiC (q u))⁻¹ ≠ c) :
    ∀ᵐ θ : ℝ, ∃ c₀ : ℂ, c₀ ≠ 0 ∧ c₀⁻¹ ∉ L ∧
      Tendsto (fun r : ℝ => psiC (q (discRay θ r))) (nhdsWithin 1 (Set.Iio (1 : ℝ)))
        (nhds c₀) := by
  -- `ψ` never vanishes on `S`
  have hpsi0 : ∀ u : ↥(connectedComponent P), psi ((u : H0 a h) : ChainData) ≠ 0 := by
    intro u h0
    have := hbd u
    rw [h0, norm_zero] at this
    linarith
  have hbd' : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖(psiC (discExt q z))⁻¹‖ ≤ ρ⁻¹ := by
    intro z hz
    rw [discExt_of_mem q hz, norm_inv]
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hpsi0 _)) hρ).mpr (hbd _)
  have hne : ∃ z ∈ Metric.ball (0 : ℂ) 1, (psiC (discExt q z))⁻¹ ≠ 0 := by
    refine ⟨0, by simp [Metric.mem_ball], ?_⟩
    rw [discExt_of_mem q (by simp [Metric.mem_ball])]
    exact inv_ne_zero (hpsi0 _)
  have hLc' : ∀ c ∈ L, ∃ z ∈ Metric.ball (0 : ℂ) 1, (psiC (discExt q z))⁻¹ ≠ c := by
    intro c hc
    obtain ⟨u, hu⟩ := hLc c hc
    exact ⟨(u : ℂ), u.2, by rwa [discExt_of_mem q u.2]⟩
  have hae := ae_radial_limit_ne_zero_notMem_countable hfatou hG hbd' hne L hL hLc'
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 1 (Set.Iio (1 : ℝ)) :=
    (nhdsLT_basis (1 : ℝ)).mem_iff.mpr ⟨0, zero_lt_one, fun t ht => ht⟩
  filter_upwards [hae] with θ hθ
  obtain ⟨ĉ, hĉ0, hĉL, hlim⟩ := hθ
  refine ⟨ĉ⁻¹, inv_ne_zero hĉ0, by rwa [inv_inv], ?_⟩
  have h2 : Tendsto (fun t : ℝ => psiC (discExt q (t * Complex.exp ((θ : ℂ) * Complex.I))))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (ĉ⁻¹)) := by
    have := hlim.inv₀ hĉ0
    simpa [inv_inv] using this
  refine h2.congr' ?_
  filter_upwards [hIoo] with r hr
  have hmem : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hnorm : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r
    rw [hnorm, abs_of_pos hr.1]
    exact hr.2
  rw [discExt_of_mem q hmem, discRay, dif_pos (show r ∈ Set.Ioo (0 : ℝ) 1 from hr)]

end Work.EQ
