import Mathlib
import Submission.Work.OddVolterra.RowIdentity.Basic

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

noncomputable section

/-! ## Pointwise factorizations of the radicand at the section endpoints

At the right endpoint `t = y σ` of the section of slope `σ`, whenever `f` agrees with the
frozen line `line h σ`, the radicand factors as `ψ(u, yσ) = (σ - u) · Qy h y u σ`.  This is
`Work.OddVolterra.RowIdentity.psi_y_germ_factor` re-proved pointwise (no germ), and its
`-x`-analogue. -/

/-- `ψ(u, yσ) = (σ - u) · Qy h y u σ` whenever `f (y σ) = line h σ (y σ)`. -/
lemma psi_y_endpoint_eq {h f y : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {u σ : ℝ}
    (hyσ : f (y σ) = σ * y σ + h σ) :
    psi h f u (y σ) = (σ - u) * Qy h y u σ := by
  have hq : h σ - h u = (σ - u) * hquot h u σ := sub_mul_hquot hh u σ
  have key : f (y σ) ^ 2 - (u * y σ + h u) ^ 2
      = ((σ - u) * y σ + (h σ - h u)) * ((σ + u) * y σ + (h σ + h u)) := by
    rw [hyσ]; ring
  unfold psi Qy line
  rw [key, hq]
  ring

/-- `ψ(u, -xσ) = (σ - u) · Qx h x u σ` whenever `f (-(x σ)) = -(line h σ (-(x σ)))`. -/
lemma psi_negx_endpoint_eq {h f x : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {u σ : ℝ}
    (hxσ : f (-(x σ)) = -(σ * (-(x σ)) + h σ)) :
    psi h f u (-(x σ)) = (σ - u) * Qx h x u σ := by
  have hq : h σ - h u = (σ - u) * hquot h u σ := sub_mul_hquot hh u σ
  have key : f (-(x σ)) ^ 2 - (u * (-(x σ)) + h u) ^ 2
      = ((σ - u) * (-(x σ)) + (h σ - h u)) * ((σ + u) * (-(x σ)) + (h σ + h u)) := by
    rw [hxσ]; ring
  unfold psi Qx line
  rw [key, hq]
  ring

/-! ## The two half-integer power identities at the endpoints -/

/-- At the right endpoint, for `u < σ` and positive frozen factor `Qy`, the moment integrand
`ψ^n √ψ(u, yσ)` equals the product of half-integer powers `(σ-u)^{n+1/2} · Qy^{n+1/2}`. -/
lemma momentIntegrand_y_endpoint_eq (H : Setup) {u σ : ℝ} (huσ : u < σ)
    (hyσ : H.f (H.y σ) = σ * H.y σ + H.h σ) (hQ : 0 < Qy H.h H.y u σ) :
    momentIntegrand H.n H.h H.f u (H.y σ)
      = (σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Qy H.h H.y u σ) ^ ((H.n : ℝ) + 1 / 2) := by
  have hpsi := psi_y_endpoint_eq (u := u) (H.hh.of_le (by norm_num)) hyσ
  have hspos : 0 < σ - u := sub_pos.mpr huσ
  have hpsipos : 0 < psi H.h H.f u (H.y σ) := by rw [hpsi]; exact mul_pos hspos hQ
  rw [momentIntegrand, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast (psi H.h H.f u (H.y σ)) H.n, ← Real.rpow_add hpsipos, hpsi,
    Real.mul_rpow (le_of_lt hspos) (le_of_lt hQ)]

/-- At the left endpoint, for `u < σ` and positive frozen factor `Qx`, the moment integrand
`ψ^n √ψ(u, -xσ)` equals `(σ-u)^{n+1/2} · Qx^{n+1/2}`. -/
lemma momentIntegrand_negx_endpoint_eq (H : Setup) {u σ : ℝ} (huσ : u < σ)
    (hxσ : H.f (-(H.x σ)) = -(σ * (-(H.x σ)) + H.h σ)) (hQ : 0 < Qx H.h H.x u σ) :
    momentIntegrand H.n H.h H.f u (-(H.x σ))
      = (σ - u) ^ ((H.n : ℝ) + 1 / 2) * (Qx H.h H.x u σ) ^ ((H.n : ℝ) + 1 / 2) := by
  have hpsi := psi_negx_endpoint_eq (u := u) (H.hh.of_le (by norm_num)) hxσ
  have hspos : 0 < σ - u := sub_pos.mpr huσ
  have hpsipos : 0 < psi H.h H.f u (-(H.x σ)) := by rw [hpsi]; exact mul_pos hspos hQ
  rw [momentIntegrand, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast (psi H.h H.f u (-(H.x σ))) H.n, ← Real.rpow_add hpsipos, hpsi,
    Real.mul_rpow (le_of_lt hspos) (le_of_lt hQ)]

/-- **The split of the section integral into a fixed part and a swept part.**

`momentF` is the integral of `momentIntegrand n h f u` over the moving section `(-x u, y u)`.
The local Leibniz rule `Work.Analysis.Abel.integral_moving_split_local` (module
`Submission.Work.Analysis.Abel.integral_moving_split_local`) splits it at the fixed interval
`(-x 1, y 1) = (-X₁, X₁)`:

`momentF ... u = ∫_{-X₁}^{X₁} momentIntegrand n h f u + ∫_σ in u..1 (...)`,

the first term being `AA n h u` because `f = semicircle` on `[-X₁,X₁]` (so that
`psi h f u t = psi h semicircle u t = Psi h u t = 1 - t² - (ut + h u)²`), and the second term
being `WW n h x y u`: at each endpoint `t = y σ` resp. `t = -x σ` the radicand factors as
`ψ(u,t) = (σ-u)·Qy(u,σ)` resp. `(σ-u)·Qx(u,σ)` (the germ factorization; see
`Work.OddVolterra.RowIdentity.psi_y_germ_factor` in the module
`Submission.Work.OddVolterra.RowIdentity.yend_iteratedDeriv_eq_rpow` for the `y`-case, and the
analogous computation for `-x`), and since `σ > u` and the frozen factors are positive, the
`(n+1/2)`-power of the radicand is exactly `(σ-u)^{n+1/2} · Q^{n+1/2}` (`Real.mul_rpow`,
`Real.rpow_add`, `Real.sqrt_eq_rpow`, `Real.rpow_natCast`), which is the integrand `Wint`. -/
theorem momentF_eq_AA_add_WW (H : Setup) {u c d : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (hc : ContinuousOn (momentIntegrand H.n H.h H.f u) (Set.Icc c d))
    (hbox : ∀ σ ∈ Set.Icc u 1, c < -(H.x σ) ∧ -(H.x σ) ≤ d ∧ c ≤ H.y σ ∧ H.y σ < d)
    (henv : ∀ σ ∈ Set.Ioc u 1,
      H.f (H.y σ) = σ * H.y σ + H.h σ ∧ H.f (-(H.x σ)) = -(σ * (-(H.x σ)) + H.h σ))
    (hQy : ∀ σ ∈ Set.Icc u 1, 0 < Qy H.h H.y u σ)
    (hQx : ∀ σ ∈ Set.Icc u 1, 0 < Qx H.h H.x u σ) :
    momentF H.n H.h H.x H.y H.f u = AA H.n H.h u + WW H.n H.h H.x H.y u := by
  have hsplit := Work.Analysis.Abel.integral_moving_split_local
    (x := H.x) (y := H.y) (P := momentIntegrand H.n H.h H.f u) H.hx H.hy hu hu1 hc hbox
  -- The integral over the fixed window `(-X₁, X₁)`.
  have hfix : (∫ t in (-(H.x 1))..(H.y 1), momentIntegrand H.n H.h H.f u t) = AA H.n H.h u := by
    rw [H.hxb, H.hyb, AA]
    apply intervalIntegral.integral_congr
    intro t ht
    have hle : -(profileX 1) ≤ profileX 1 := by linarith [profileX_one_pos]
    rw [Set.uIcc_of_le hle] at ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith [ht.1, profileX_one_le_one], by linarith [ht.2, profileX_one_le_one]⟩
    have hft : H.f t = semicircle t := H.hfb t ⟨ht.1, ht.2⟩
    have hsq : semicircle t ^ 2 = 1 - t ^ 2 :=
      Commons.Geometry.Ulam.semicircle_sq_of_mem_Icc htIcc
    simp only [momentIntegrand, psi, Psi, line]
    rw [hft, hsq]
  -- The swept integral.
  have hswept : (∫ σ in u..1, (momentIntegrand H.n H.h H.f u (H.y σ) * (-(deriv H.y σ))
      + momentIntegrand H.n H.h H.f u (-(H.x σ)) * (-(deriv H.x σ))))
      = WW H.n H.h H.x H.y u := by
    rw [WW]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hu1]
    refine Eventually.of_forall (fun σ hσ => ?_)
    simp only [Wint]
    obtain ⟨hyσ, hxσ⟩ := henv σ hσ
    have hIcc : σ ∈ Set.Icc u 1 := ⟨le_of_lt hσ.1, hσ.2⟩
    rw [momentIntegrand_y_endpoint_eq H hσ.1 hyσ (hQy σ hIcc),
      momentIntegrand_negx_endpoint_eq H hσ.1 hxσ (hQx σ hIcc)]
    ring
  rw [momentF, hsplit, hfix, hswept]

end

end Work.OddVolterra.RowIdentity
