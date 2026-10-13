/-
`Work.FTS.Apriori.Profile.SliceDiff` — the angular difference bound used by `linf_H2_quad`:

for `g` of class `SmoothQuad` in `HkMem α 2` with decay in `z`, and `0 < a ≤ b < π/2`,

  `(g z a - g z b)² ≤ (∫_a^b sin(2σ)^{γ-2} dσ) · HkSq α 2 g`.

The proof combines the radial Hardy inequality applied to the `θ`-derivative `∂_θ g(·,σ)` with
the angular fundamental theorem of calculus: the derivative of `σ ↦ g z σ` is bounded, up to the
weight `sin(2σ)^{2-γ}`, by one of the slots of `HkIntegrand α 2 g`, namely
`(D_z D_θ g · W)²` (via the identity `D_z D_θ g = z ∂_z ∂_θ g`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Linf_H2
import Submission.Work.Spaces.HardyZ
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.Apriori.Profile.Support
import Submission.Work.FTS.Apriori.Profile.SliceMass

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Profile

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.Spaces

/-- The `(i,j) = (1,1)` slot of `HkIntegrand`, in terms of the mixed partial derivative of `g`:
`(D_z D_θ g · W)² = (z ∂_z ∂_θ g)² w² sin(2θ)^{2-γ}` on the angular range. -/
theorem mixedSlot_eq {α : ℝ} (hγ0 : gam α ≠ 0) (hγ2 : gam α ≠ 2) (g : ℝ → ℝ → ℝ) {s σ : ℝ}
    (hσ : 0 ≤ Real.sin (2 * σ)) :
    (Dz (Dth g) s σ * Wt α s σ) ^ 2
      = (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) := by
  have h1 : pz (Dth g) s σ = Real.sin (2 * σ) * pz (pth g) s σ := by
    show deriv (fun s' => Real.sin (2 * σ) * pth g s' σ) s
      = Real.sin (2 * σ) * deriv (fun s' => pth g s' σ) s
    rw [deriv_const_mul_field]
  have hD : Dz (Dth g) s σ = s * Real.sin (2 * σ) * pz (pth g) s σ := by
    rw [Dz, h1]; ring
  have hA : (Real.sin (2 * σ) ^ (-(gam α / 2))) ^ 2 = (Real.sin (2 * σ)) ^ (-(gam α)) := by
    rw [pow_two, ← Real.rpow_add' hσ (by intro hc; exact hγ0 (by linarith))]
    congr 1
    ring
  have hB : Real.sin (2 * σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))
      = (Real.sin (2 * σ)) ^ (2 - gam α) := by
    nth_rewrite 1 [← Real.rpow_natCast]
    rw [← Real.rpow_add' hσ (by push_cast; intro hc; exact hγ2 (by linarith))]
    congr 1
  rw [hD, Wt, wTheta]
  repeat rw [mul_pow]
  rw [hA]
  linear_combination (s ^ 2 * (pz (pth g) s σ) ^ 2 * (w s) ^ 2) * hB

/-- The `(i,j) = (1,1)` slot of the `ℋ²`-integrand is product-integrable with integral at most
`HkSq α 2 g`. -/
theorem mixedSlot_prod_le {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 2 g) :
    Integrable (fun p : ℝ × ℝ => (Dz (Dth g) p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) ∧
    (MeasureTheory.integral ((volume.restrict Iz).prod (volume.restrict Iθ))
      (fun p : ℝ × ℝ => (Dz (Dth g) p.1 p.2 * Wt α p.1 p.2) ^ 2)) ≤ HkSq α 2 g := by
  obtain ⟨hsumI, hsumE⟩ := HkIntegrand_integrable_prod (k := 2) hsm hmem
  have hle : ∀ p : ℝ × ℝ,
      (Dz (Dth g) p.1 p.2 * Wt α p.1 p.2) ^ 2 ≤ HkIntegrand α 2 g p.1 p.2 := by
    intro p
    have hterm : (Dz (Dth g) p.1 p.2 * Wt α p.1 p.2) ^ 2
        = (mixed 1 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2 := rfl
    rw [hterm, HkIntegrand]
    have hinner : (mixed 1 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2
        ≤ ∑ j ∈ Finset.range 3,
            (if 1 ≤ (1:ℕ) ∧ 1 + j ≤ 2 then (mixed j 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0) := by
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j =>
        if 1 ≤ (1:ℕ) ∧ 1 + j ≤ 2 then (mixed j 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0)
        (fun j _ => by split_ifs <;> simp [sq_nonneg])
        (Finset.mem_range.mpr (by norm_num : 1 < 3)))
      exact (ite_eq_left (by norm_num : 1 ≤ 1 ∧ 1 + 1 ≤ 2)).symm
    have houter : (∑ j ∈ Finset.range 3,
          (if 1 ≤ (1:ℕ) ∧ 1 + j ≤ 2 then (mixed j 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0))
        ≤ ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i g p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0) :=
      Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i g p.1 p.2 * Wt α p.1 p.2) ^ 2 else 0))
        (fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> simp [sq_nonneg])
        (Finset.mem_range.mpr (by norm_num : 1 < 3))
    exact le_trans (le_trans hinner houter)
      (le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hAESM : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Dz (Dth g) p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := by
    have hDz : ContinuousOn (fun p : ℝ × ℝ => Dz (Dth g) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((Work.FTS.LocData.contDiffOn_Dz isOpen_quadU
        (Work.FTS.LocData.contDiffOn_Dth isOpen_quadU hsm)).continuousOn).mono
        (fun p hp => ⟨lt_trans (by norm_num : (-1 : ℝ) < 0) hp.1, hp.2.1, hp.2.2⟩)
    have hWt : ContinuousOn (fun p : ℝ × ℝ => Wt α p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := Work.FTS.H2.continuousOn_Wt_Qd α
    exact aesm_of_continuousOn_Qd _ ((hDz.mul hWt).pow 2)
  refine ⟨Integrable.mono' hsumI hAESM (Filter.Eventually.of_forall fun p => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle p
  · calc (∫ p, (Dz (Dth g) p.1 p.2 * Wt α p.1 p.2) ^ 2
          ∂((volume.restrict Iz).prod (volume.restrict Iθ)))
        ≤ ∫ p, HkIntegrand α 2 g p.1 p.2 ∂((volume.restrict Iz).prod (volume.restrict Iθ)) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun p => sq_nonneg _) hsumI
            (Filter.Eventually.of_forall fun p => hle p)
      _ = HkSq α 2 g := hsumE

/-- For almost every `σ`, the `z`-slice of `(z ∂_z ∂_θ g)² w²` is integrable. -/
theorem mixedSlot_slice_ae {α : ℝ} {g : ℝ → ℝ → ℝ} (hγ0 : gam α ≠ 0) (hγ2 : gam α ≠ 2)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 2 g) :
    ∀ᵐ σ ∂(volume.restrict Iθ),
      Integrable (fun s => (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2) (volume.restrict Iz) := by
  obtain ⟨hslotI, -⟩ := mixedSlot_prod_le (α := α) hsm hmem
  filter_upwards [hslotI.prod_left_ae, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hsl hσIoo
  have hsinpos : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσIoo.1]) (by linarith [hσIoo.2, Real.pi_pos])
  have heq : (fun s => (Dz (Dth g) s σ * Wt α s σ) ^ 2)
      = fun s => (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) :=
    by
      funext s
      exact mixedSlot_eq hγ0 hγ2 g hsinpos.le
  rw [heq] at hsl
  have hc : (Real.sin (2 * σ)) ^ (2 - gam α) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hsinpos _)
  have hcomm : (fun s => (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - gam α))
      = fun s => ((Real.sin (2 * σ)) ^ (2 - gam α))
          * ((s * pz (pth g) s σ) ^ 2 * (w s) ^ 2) := by
    funext s; ring
  rw [hcomm] at hsl
  exact (hsl.const_mul (((Real.sin (2 * σ)) ^ (2 - gam α))⁻¹)).congr
    (Filter.Eventually.of_forall fun s => by
      simp only [Pi.mul_apply]
      rw [inv_mul_cancel_left₀ hc])

/-- The Hardy bound for the angular derivative: almost everywhere in `σ`, the `θ`-derivative is
dominated by the `z`-integral of `(z ∂_z ∂_θ g)² w²`. -/
theorem pth_g_le_G1_ae {α : ℝ} {g : ℝ → ℝ → ℝ} (hγ0 : gam α ≠ 0) (hγ2 : gam α ≠ 2)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hdec : Work.Spaces.DecayInZ 2 g)
    (hmem : Work.Spaces.HkMem α 2 g) :
    ∀ᵐ σ ∂(volume.restrict Iθ), ∀ z ∈ Set.Ioi (0 : ℝ),
      (pth g z σ) ^ 2
        ≤ ∫ s, (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz) := by
  filter_upwards [mixedSlot_slice_ae hγ0 hγ2 hsm hmem, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hsl hσIoo
  have hσIθ : σ ∈ Iθ := ⟨hσIoo.1.le, hσIoo.2.le⟩
  intro z hz
  have hcd : ContDiffOn ℝ 1 (fun s => pth g s σ) (Set.Ioi 0) :=
    (Work.FTS.LocData.contDiffOn_slice_z
      (s := Set.Ioi (-1)) (t := Set.Ioo 0 (π / 2))
      (Work.FTS.LocData.contDiffOn_pth isOpen_quadU hsm) hσIoo).of_le
      (by simp [Work.Stability.smoothOrder]) |>.mono
      (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
  have hten : Tendsto (fun s => pth g s σ) atTop (nhds 0) := hdec 0 1 (by norm_num) σ hσIθ
  have hint : IntegrableOn (fun s => (s * deriv (fun s' => pth g s' σ) s) ^ 2 * (w s) ^ 2)
      Iz := by
    have heq : (fun s => (s * deriv (fun s' => pth g s' σ) s) ^ 2 * (w s) ^ 2)
        = fun s => (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 := by
      funext s; rfl
    rw [heq]
    exact hsl
  have hH := Work.FTS.H2.hardyZ_open hcd hten hint z hz
  simpa only [pz] using hH

/-- The weighted `z`-integral of `(z ∂_z ∂_θ g)² w²` is bounded by `HkSq α 2 g`. -/
theorem G1_weighted_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hγ0 : gam α ≠ 0) (hγ2 : gam α ≠ 2)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 2 g) :
    Integrable (fun σ => (∫ s, (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz))
        * (Real.sin (2 * σ)) ^ (2 - gam α)) (volume.restrict Iθ) ∧
    (∫ σ, (∫ s, (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz))
        * (Real.sin (2 * σ)) ^ (2 - gam α) ∂(volume.restrict Iθ)) ≤ HkSq α 2 g := by
  obtain ⟨hslotI, hslotle⟩ := mixedSlot_prod_le (α := α) hsm hmem
  have hM : Integrable (fun σ => ∫ s, (Dz (Dth g) s σ * Wt α s σ) ^ 2 ∂(volume.restrict Iz))
      (volume.restrict Iθ) := hslotI.integral_prod_right
  have hpt : ∀ σ ∈ Iθ, (∫ s, (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz))
      * (Real.sin (2 * σ)) ^ (2 - gam α)
      = ∫ s, (Dz (Dth g) s σ * Wt α s σ) ^ 2 ∂(volume.restrict Iz) := by
    intro σ hσ
    have hsin : 0 ≤ Real.sin (2 * σ) := sin_two_nonneg_Iθ hσ
    rw [← MeasureTheory.integral_mul_const]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s =>
      (mixedSlot_eq hγ0 hγ2 g hsin).symm)
  have hcongr : (∫ σ in Iθ, (∫ s in Iz, (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2)
        * (Real.sin (2 * σ)) ^ (2 - gam α))
      = ∫ σ in Iθ, (∫ s in Iz, (Dz (Dth g) s σ * Wt α s σ) ^ 2) :=
    MeasureTheory.setIntegral_congr_ae measurableSet_Icc
      (Filter.Eventually.of_forall fun σ hσ => hpt σ hσ)
  have hAESM : AEStronglyMeasurable
      (fun σ => (∫ s, (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz))
        * (Real.sin (2 * σ)) ^ (2 - gam α)) (volume.restrict Iθ) :=
    hM.aestronglyMeasurable.congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ => (hpt σ hσ).symm)
  refine ⟨Integrable.mono' hM hAESM ?_, ?_⟩
  · filter_upwards [MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt] with σ hσ
    rw [Real.norm_eq_abs, hσ, abs_of_nonneg (MeasureTheory.integral_nonneg fun s => sq_nonneg _)]
  · rw [hcongr]
    show (∫ σ, (∫ s, (Dz (Dth g) s σ * Wt α s σ) ^ 2 ∂(volume.restrict Iz))
        ∂(volume.restrict Iθ)) ≤ HkSq α 2 g
    rw [← MeasureTheory.integral_integral_swap
        (f := fun s σ => (Dz (Dth g) s σ * Wt α s σ) ^ 2) hslotI,
      MeasureTheory.integral_integral
        (f := fun s σ => (Dz (Dth g) s σ * Wt α s σ) ^ 2) hslotI]
    exact hslotle


/-- The `(i,j) = (0,1)` slot of `HkIntegrand` dominates `(∂_θ g)² sin(2θ)^{2-γ}` (for `z > 0`). -/
theorem massSlot_theta_le_HkIntegrand {α : ℝ} (hγ0 : gam α ≠ 0) (hγ2 : gam α ≠ 2)
    (g : ℝ → ℝ → ℝ) {z σ : ℝ} (hz : 0 < z) (hσ : σ ∈ Iθ) :
    (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) ≤ HkIntegrand α 2 g z σ := by
  have hsin : 0 ≤ Real.sin (2 * σ) := sin_two_nonneg_Iθ hσ
  have hw1 : 1 ≤ (w z) ^ 2 := by
    have h1 : 1 ≤ w z := one_le_w hz
    nlinarith
  have hA : (Real.sin (2 * σ) ^ (-(gam α / 2))) ^ 2
      = (Real.sin (2 * σ)) ^ (-(gam α)) := by
    rw [pow_two, ← Real.rpow_add' hsin (by intro hc; exact hγ0 (by linarith))]
    congr 1
    ring
  have hB : Real.sin (2 * σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))
      = (Real.sin (2 * σ)) ^ (2 - gam α) := by
    nth_rewrite 1 [← Real.rpow_natCast]
    rw [← Real.rpow_add' hsin (by push_cast; intro hc; exact hγ2 (by linarith))]
    congr 1
  have hterm : (Dth g z σ * Wt α z σ) ^ 2
      = (pth g z σ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) := by
    have hDth : Dth g z σ = Real.sin (2 * σ) * pth g z σ := rfl
    rw [hDth, Wt, wTheta]
    repeat rw [mul_pow]
    rw [hA]
    linear_combination ((pth g z σ) ^ 2 * (w z) ^ 2) * hB
  have hle : (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)
      ≤ (Dth g z σ * Wt α z σ) ^ 2 := by
    rw [hterm]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg _) hw1)
      (Real.rpow_nonneg hsin _)
  have hterm0 : (Dth g z σ * Wt α z σ) ^ 2 = (mixed 0 1 g z σ * Wt α z σ) ^ 2 := rfl
  rw [HkIntegrand]
  refine le_trans hle ?_
  rw [hterm0]
  have hmem0 : (0:ℕ) ∈ Finset.range 3 := Finset.mem_range.mpr (by norm_num)
  have hmem1 : (1:ℕ) ∈ Finset.range 3 := Finset.mem_range.mpr (by norm_num)
  have hinner0 : (mixed 0 1 g z σ * Wt α z σ) ^ 2
      ≤ ∑ j ∈ Finset.range 3, (if 1 ≤ (1:ℕ) ∧ 1 + j ≤ 2 then
          (mixed j 1 g z σ * Wt α z σ) ^ 2 else 0) := by
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j : ℕ =>
      if 1 ≤ (1:ℕ) ∧ 1 + j ≤ 2 then (mixed j 1 g z σ * Wt α z σ) ^ 2 else 0)
      (fun j _ => by split_ifs <;> simp [sq_nonneg]) hmem0)
    exact (ite_eq_left (by norm_num : 1 ≤ (1:ℕ) ∧ 1 + 0 ≤ 2)).symm
  have houter0 : (∑ j ∈ Finset.range 3, (if 1 ≤ (1:ℕ) ∧ 1 + j ≤ 2 then
        (mixed j 1 g z σ * Wt α z σ) ^ 2 else 0))
      ≤ ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
          (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i g z σ * Wt α z σ) ^ 2 else 0) :=
    Finset.single_le_sum (f := fun i : ℕ => ∑ j ∈ Finset.range 3,
      (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i g z σ * Wt α z σ) ^ 2 else 0))
      (fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> simp [sq_nonneg]) hmem1
  exact le_trans (le_trans hinner0 houter0)
    (le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg _))


/-- **The angular difference bound.**  For `z > 0` and `0 < a ≤ b < π/2`,
`(g z a - g z b)² ≤ (∫_a^b sin(2σ)^{γ-2}) · HkSq α 2 g`. -/
theorem slice_diff_le_HkSq {α : ℝ} (hγ0 : gam α ≠ 0) (hγ2 : gam α ≠ 2)
    {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) (hdec : Work.Spaces.DecayInZ 2 g)
    (hmem : Work.Spaces.HkMem α 2 g)
    {a b : ℝ} (ha : a ∈ Set.Ioo 0 (Real.pi / 2)) (hb : b ∈ Set.Ioo 0 (Real.pi / 2))
    (hab : a ≤ b) {z : ℝ} (hz : 0 < z) :
    (g z a - g z b) ^ 2
      ≤ (∫ σ in Set.Ioc a b, (Real.sin (2 * σ)) ^ (gam α - 2)) * HkSq α 2 g := by
  have hsub : Set.Ioc a b ⊆ Iθ := fun σ hσ =>
    ⟨le_of_lt (lt_trans ha.1 hσ.1), le_of_lt (lt_of_le_of_lt hσ.2 hb.2)⟩
  have hIcc : Set.Icc a b ⊆ Iθ := fun σ hσ =>
    ⟨le_trans ha.1.le hσ.1, le_trans hσ.2 hb.2.le⟩
  have hIcc' : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := fun σ hσ =>
    ⟨lt_of_lt_of_le ha.1 hσ.1, lt_of_le_of_lt hσ.2 hb.2⟩
  -- the two weighted integrands
  set ρ : ℝ → ℝ := fun σ => (Real.sin (2 * σ)) ^ (2 - gam α) with hρ
  set G₁ : ℝ → ℝ := fun σ =>
    ∫ s, (s * pz (pth g) s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz) with hG1
  have hpthI : IntegrableOn (fun σ => (pth g z σ) ^ 2 * ρ σ) Iθ := by
    refine Integrable.mono' (hmem.1 z hz.le) ?_ ?_
    · have hcont : ContinuousOn (fun p : ℝ × ℝ => (pth g p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - gam α)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
        have hpth : ContinuousOn (fun p : ℝ × ℝ => pth g p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          ((Work.FTS.LocData.contDiffOn_pth isOpen_quadU hsm).continuousOn).mono
            (fun p hp => ⟨lt_trans (by norm_num : (-1 : ℝ) < 0) hp.1, hp.2.1, hp.2.2⟩)
        refine (hpth.pow 2).mul ?_
        refine ((Real.continuous_sin.comp
          (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
        intro p hp
        have h1 : 0 < p.2 := hp.2.1
        have h2 : p.2 < Real.pi / 2 := hp.2.2
        refine Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_))
        · show 0 < 2 * p.2; linarith
        · show 2 * p.2 < Real.pi; linarith [Real.pi_pos]
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _))]
      exact massSlot_theta_le_HkIntegrand hγ0 hγ2 g hz hσ
  have hmasse : (∫ σ in Set.Ioc a b, (pth g z σ) ^ 2 * ρ σ) ≤ HkSq α 2 g := by
    have hG1I : IntegrableOn (fun σ => G₁ σ * ρ σ) Iθ := (G1_weighted_le hγ0 hγ2 hsm hmem).1
    have hae := pth_g_le_G1_ae hγ0 hγ2 hsm hdec hmem
    calc (∫ σ in Set.Ioc a b, (pth g z σ) ^ 2 * ρ σ)
        ≤ ∫ σ in Set.Ioc a b, G₁ σ * ρ σ := by
          refine MeasureTheory.integral_mono_ae (hpthI.mono_set hsub) (hG1I.mono_set hsub) ?_
          filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hae,
            MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
              (fun σ hσ => hsub hσ)] with σ hσ hσI
          exact mul_le_mul_of_nonneg_right (hσ z hz)
            (Real.rpow_nonneg (sin_two_nonneg_Iθ hσI) _)
      _ ≤ ∫ σ in Iθ, G₁ σ * ρ σ := by
          refine MeasureTheory.setIntegral_mono_set hG1I ?_ ?_
          · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun σ hσ =>
              mul_nonneg (MeasureTheory.integral_nonneg fun s =>
                mul_nonneg (sq_nonneg _) (sq_nonneg _))
                (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _))
          · exact Filter.Eventually.of_forall (fun σ hσ => hsub hσ)
      _ ≤ HkSq α 2 g := (G1_weighted_le hγ0 hγ2 hsm hmem).2
  -- Cauchy–Schwarz on the angular interval
  set A : ℝ := (2 - gam α) / 2 with hA
  have hsinpos : ∀ σ ∈ Set.uIcc a b, 0 < Real.sin (2 * σ) := by
    intro σ hσ
    rw [Set.uIcc_of_le hab] at hσ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1, ha.1])
      (by linarith [hσ.2, hb.2, Real.pi_pos])
  have hcont0 : ContinuousOn (fun σ => pth g z σ) (Set.uIcc a b) := by
    have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun σ => pth g z σ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.LocData.contDiffOn_slice_θ (Work.FTS.LocData.contDiffOn_pth isOpen_quadU hsm)
        (lt_trans (by norm_num : (-1 : ℝ) < 0) hz)
    refine hcd.continuousOn.mono ?_
    intro σ hσ
    rw [Set.uIcc_of_le hab] at hσ
    exact ⟨lt_of_lt_of_le ha.1 hσ.1, lt_of_le_of_lt hσ.2 hb.2⟩
  have hcont1 : ContinuousOn (fun σ => |pth g z σ| * (Real.sin (2 * σ)) ^ A) (Set.uIcc a b) :=
    (hcont0.abs.mul (((Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun σ hσ => Or.inl (ne_of_gt (hsinpos σ hσ)))))
  have hcont2 : ContinuousOn (fun σ => (Real.sin (2 * σ)) ^ (-A)) (Set.uIcc a b) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun σ hσ => Or.inl (ne_of_gt (hsinpos σ hσ)))
  have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab hcont1 hcont2
  have hI2 : (∫ σ in a..b, ((Real.sin (2 * σ)) ^ (-A)) ^ 2)
      = ∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    have hs := hsinpos σ hσ
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    rw [hA]; ring
  have hI1 : (∫ σ in a..b, (|pth g z σ| * (Real.sin (2 * σ)) ^ A) ^ 2)
      = ∫ σ in a..b, (pth g z σ) ^ 2 * ρ σ := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    have hs := hsinpos σ hσ
    have hs2 : ((Real.sin (2 * σ)) ^ A) ^ 2 = ρ σ := by
      show ((Real.sin (2 * σ)) ^ A) ^ 2 = (Real.sin (2 * σ)) ^ (2 - gam α)
      rw [pow_two, ← Real.rpow_add hs]
      congr 1
      rw [hA]; ring
    rw [mul_pow, sq_abs, hs2]
  have hprod : ∀ σ ∈ Set.uIcc a b,
      (|pth g z σ| * (Real.sin (2 * σ)) ^ A) * (Real.sin (2 * σ)) ^ (-A) = |pth g z σ| := by
    intro σ hσ
    have hs := hsinpos σ hσ
    rw [mul_assoc, ← Real.rpow_add hs, show A + -A = 0 by ring, Real.rpow_zero, mul_one]
  have hFTC : (∫ σ in a..b, pth g z σ) = g z b - g z a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
    · exact (hsm.curry_θ (lt_trans (by norm_num : (-1 : ℝ) < 0) hz)).continuousOn.mono hIcc'
    · intro x hx
      exact (((hsm.curry_θ (lt_trans (by norm_num : (-1 : ℝ) < 0) hz)).differentiableOn
        Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds (⟨lt_of_le_of_lt ha.1.le hx.1, lt_of_lt_of_le hx.2 hb.2.le⟩ :
          x ∈ Set.Ioo 0 (Real.pi / 2)))).hasDerivAt
    · exact hcont0.intervalIntegrable
  have hmain : |g z b - g z a|
      ≤ Real.sqrt (∫ σ in a..b, (pth g z σ) ^ 2 * ρ σ)
        * Real.sqrt (∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2)) := by
    calc |g z b - g z a| = |∫ σ in a..b, pth g z σ| := by rw [hFTC]
      _ ≤ ∫ σ in a..b, |pth g z σ| := by
          simpa [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
              (f := fun σ => pth g z σ)
      _ = ∫ σ in a..b, (|pth g z σ| * (Real.sin (2 * σ)) ^ A)
            * (Real.sin (2 * σ)) ^ (-A) := by
          refine intervalIntegral.integral_congr fun σ hσ => ?_
          exact (hprod σ hσ).symm
      _ = |∫ σ in a..b, (|pth g z σ| * (Real.sin (2 * σ)) ^ A)
            * (Real.sin (2 * σ)) ^ (-A)| := by
          rw [show (∫ σ in a..b, (|pth g z σ| * (Real.sin (2 * σ)) ^ A)
                * (Real.sin (2 * σ)) ^ (-A)) = ∫ σ in a..b, |pth g z σ| from
              intervalIntegral.integral_congr fun σ hσ => hprod σ hσ]
          exact (abs_of_nonneg
            (intervalIntegral.integral_nonneg_of_forall hab fun σ => abs_nonneg _)).symm
      _ ≤ Real.sqrt (∫ σ in a..b, (|pth g z σ| * (Real.sin (2 * σ)) ^ A) ^ 2)
            * Real.sqrt (∫ σ in a..b, ((Real.sin (2 * σ)) ^ (-A)) ^ 2) := hcs
      _ = Real.sqrt (∫ σ in a..b, (pth g z σ) ^ 2 * ρ σ)
            * Real.sqrt (∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2)) := by
          rw [hI1, hI2]
  have hIoc : (∫ σ in a..b, (pth g z σ) ^ 2 * ρ σ) ≤ HkSq α 2 g := by
    rw [intervalIntegral.integral_of_le hab]
    exact hmasse
  have hIoc2 : (∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2))
      = ∫ σ in Set.Ioc a b, (Real.sin (2 * σ)) ^ (gam α - 2) :=
    intervalIntegral.integral_of_le hab
  have hnn1 : 0 ≤ (∫ σ in a..b, (pth g z σ) ^ 2 * ρ σ) := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ (hsub hσ)) _)
  have hnn2 : 0 ≤ (∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2)) := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun σ hσ =>
      Real.rpow_nonneg (sin_two_nonneg_Iθ (hsub hσ)) _
  have hsquare : (g z a - g z b) ^ 2
      ≤ (Real.sqrt (∫ σ in a..b, (pth g z σ) ^ 2 * ρ σ)
          * Real.sqrt (∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2))) ^ 2 := by
    have hneg : (-(g z b - g z a)) ^ 2 = (g z b - g z a) ^ 2 := by ring
    rw [show g z a - g z b = -(g z b - g z a) by ring, hneg]
    refine sq_le_sq' ?_ ?_
    · linarith [neg_abs_le (g z b - g z a), hmain]
    · exact le_trans (le_abs_self _) hmain
  calc (g z a - g z b) ^ 2
      ≤ (Real.sqrt (∫ σ in a..b, (pth g z σ) ^ 2 * ρ σ)
          * Real.sqrt (∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2))) ^ 2 := hsquare
    _ = (∫ σ in a..b, (pth g z σ) ^ 2 * ρ σ)
          * (∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2)) := by
        rw [mul_pow, Real.sq_sqrt hnn1, Real.sq_sqrt hnn2]
    _ ≤ HkSq α 2 g * (∫ σ in a..b, (Real.sin (2 * σ)) ^ (gam α - 2)) :=
        mul_le_mul_of_nonneg_right hIoc hnn2
    _ = HkSq α 2 g * (∫ σ in Set.Ioc a b, (Real.sin (2 * σ)) ^ (gam α - 2)) := by rw [hIoc2]
    _ = (∫ σ in Set.Ioc a b, (Real.sin (2 * σ)) ^ (gam α - 2)) * HkSq α 2 g := by ring

end Work.FTS.Apriori.Profile
