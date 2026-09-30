import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.mrlas.Psi2_defs
import Submission.Work.BMF.LSeries_norm_le_exp_Wsup
import Submission.Work.BMF.Kser_gp_bounds
import Submission.Work.BMF.mrlas.tendsto_tailNat_rpow
import Submission.Work.BMF.mrlas.sum_le_tsum_tail
import Submission.Work.BMF.mrlas.norm_prod_one_add_le_exp
import Submission.Work.BMF.mrlas.sum_primesBelow_rpow_le
import Submission.Work.BMF.mrlas.gp_eq_eulerFac
import Submission.Work.BMF.mrlas.tendstoUniformlyOn_of_dist_le
import Submission.Work.BMF.mrlas.norm_prod_gp_diff_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset Real Complex Filter
open scoped Topology BigOperators

/-- The tail sum `∑_{k} (N + k)^{-σ}` of the `p`-series, used to control the
Euler-product tail. -/
noncomputable def tailNat (σ : ℝ) (N : ℕ) : ℝ := ∑' k : ℕ, ((N + k : ℕ) : ℝ) ^ (-σ)

/-- Pointwise convergence of the truncated Euler products to `LSeries f` on `re s > 1`:
the two local factors `gp` and `eulerFac` agree at every prime, so this is a rewriting of
`Work.BMF.eulerProduct_tendsto`. -/
theorem tendsto_prod_gp (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hb : ∀ n, ‖f n‖ ≤ 1)
    (z : ℂ) (hz : 1 < z.re) :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p z)
      Filter.atTop (nhds (LSeries f z)) := by
  have h := Work.BMF.eulerProduct_tendsto f hf1 hmul hb z hz
  have hprod : (fun N : ℕ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p z)
      = fun N : ℕ => ∏ p ∈ N.primesBelow, Work.BMF.eulerFac f p z := by
    funext N
    exact Finset.prod_congr rfl
      (fun p hp => gp_eq_eulerFac f (Nat.prime_of_mem_primesBelow hp) z)
  rw [hprod]
  exact h

/-- Uniform convergence of the truncated Euler products on the half-plane `re z > σ`, `σ > 1`. -/
theorem tendstoUniformlyOn_gp_halfplane (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hb : ∀ n, ‖f n‖ ≤ 1)
    (σ : ℝ) (hσ : 1 < σ) :
    TendstoUniformlyOn (fun N : ℕ => fun z : ℂ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p z)
      (LSeries f) Filter.atTop {z : ℂ | σ < z.re} := by
  obtain ⟨B, hBpos, hB⟩ := norm_prod_gp_diff_le f hf1 hb hσ
  refine tendstoUniformlyOn_of_dist_le
    (b := fun N : ℕ => B * (Real.exp (2 * tailNat σ N) - 1)) ?_ ?_
  · have h1 : Tendsto (fun N : ℕ => tailNat σ N) Filter.atTop (nhds 0) := by
      simpa [tailNat] using tendsto_tailNat_rpow σ hσ
    have h2 : Tendsto (fun N : ℕ => 2 * tailNat σ N) Filter.atTop (nhds 0) := by
      simpa using h1.const_mul (2 : ℝ)
    have h3 : Tendsto (fun N : ℕ => Real.exp (2 * tailNat σ N)) Filter.atTop (nhds 1) := by
      have hc := (Real.continuous_exp.tendsto (0 : ℝ)).comp h2
      rw [Real.exp_zero] at hc
      exact hc
    have h4 : Tendsto (fun N : ℕ => Real.exp (2 * tailNat σ N) - 1) Filter.atTop (nhds 0) := by
      have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
      have hsub := h3.sub hc
      simpa using hsub
    simpa using h4.const_mul B
  · intro N z hz
    rw [Complex.dist_eq]
    have hz1 : 1 < z.re := lt_trans hσ hz
    have hpt := tendsto_prod_gp f hf1 hmul hb z hz1
    have hsub : Tendsto (fun N' : ℕ =>
        (∏ p ∈ N'.primesBelow, Work.BMF.gp f p z)
          - (∏ p ∈ N.primesBelow, Work.BMF.gp f p z))
        Filter.atTop (nhds (LSeries f z - ∏ p ∈ N.primesBelow, Work.BMF.gp f p z)) :=
      hpt.sub tendsto_const_nhds
    refine le_of_tendsto hsub.norm ?_
    filter_upwards [Filter.eventually_ge_atTop N] with N' hN'
    exact hB N N' hN' z hz

theorem tendstoLocallyUniformlyOn_eulerProduct (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hb : ∀ n, ‖f n‖ ≤ 1) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p z)
      (LSeries f) Filter.atTop {z : ℂ | 1 < z.re} := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds ?_
  intro x hx
  have hxr : 1 < x.re := hx
  obtain ⟨σ, hσ1, hσx⟩ : ∃ σ : ℝ, 1 < σ ∧ σ < x.re :=
    ⟨(1 + x.re) / 2, by linarith, by linarith⟩
  refine ⟨{z : ℂ | σ < z.re}, ?_, tendstoUniformlyOn_gp_halfplane f hf1 hmul hb σ hσ1⟩
  have hmem : {z : ℂ | σ < z.re} ∈ nhds x := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : 0 < x.re - σ)) ?_
    intro z hz
    rw [Metric.mem_ball] at hz
    have h1 : |z.re - x.re| ≤ ‖z - x‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - x)
    have h2 : ‖z - x‖ = dist z x := (Complex.dist_eq z x).symm
    have hz' : ‖z - x‖ < x.re - σ := by rw [h2]; exact hz
    have h3 : |z.re - x.re| < x.re - σ := lt_of_le_of_lt h1 hz'
    have h4 := (abs_lt.mp h3).1
    show σ < z.re
    linarith
  exact nhdsWithin_le_nhds hmem

end Work.BMF.mrlas
