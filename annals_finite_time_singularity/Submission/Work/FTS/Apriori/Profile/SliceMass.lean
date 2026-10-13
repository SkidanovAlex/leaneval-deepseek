/-
`Work.FTS.Apriori.Profile.SliceMass` — the radial-Hardy slice bound used by `linf_H2_quad`:
for `g` of class `SmoothQuad` in `HkMem α 2` with decay in `z`,

  `∫_θ (g z θ)² sin(2θ)^{-η} ≤ HkSq α 2 g`   for every `z > 0`.

The proof is the standard `L² × L²` Hardy argument in the radial variable, applied to each
`θ`-slice `s ↦ g s θ` and then averaged over `θ` against the weight `sin(2θ)^{-η}` (which is one
of the slots of `HkIntegrand α 2`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
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

/-- The `i`-th term of the first sum of `HkIntegrand` is the square of a weighted derivative. -/
theorem sq_mul_div_rpow_eq (c d : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (c * (d / a ^ (eta / 2))) ^ 2 = c ^ 2 * d ^ 2 * a ^ (-(eta)) := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · subst h0
    rw [Real.zero_rpow (ne_of_gt (by linarith [eta_pos] : (0 : ℝ) < eta / 2)), div_zero, mul_zero,
      sq, mul_zero, Real.zero_rpow (by linarith [eta_pos] : -(eta) ≠ 0)]
    ring
  · have hpow : (a ^ (eta / 2)) ^ 2 = a ^ eta := by
      rw [pow_two, ← Real.rpow_add hpos]
      congr 1
      ring
    rw [mul_pow, div_pow, hpow, Real.rpow_neg ha eta, div_eq_mul_inv]
    ring

/-- The `ℋ^k`-integrand of a `SmoothQuad` function is product-integrable over the quadrant,
and its product integral is the squared `ℋ^k`-norm. -/
theorem HkIntegrand_integrable_prod {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : HkMem α k g) :
    Integrable (fun p : ℝ × ℝ => HkIntegrand α k g p.1 p.2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) ∧
    (∫ p, HkIntegrand α k g p.1 p.2
        ∂((volume.restrict Iz).prod (volume.restrict Iθ))) = HkSq α k g := by
  have hnn : ∀ a b, 0 ≤ HkIntegrand α k g a b := HkIntegrand_nonneg α k g
  have hAE : AEStronglyMeasurable (Function.uncurry (fun z θ : ℝ => HkIntegrand α k g z θ))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    aesm_of_continuousOn_Qd _ (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k g hsm)
  have hslice : ∀ᵐ z ∂(volume.restrict Iz), Integrable (fun θ => HkIntegrand α k g z θ)
      (volume.restrict Iθ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    exact hmem.1 z hz
  have houter : Integrable (fun z => ∫ θ, HkIntegrand α k g z θ ∂(volume.restrict Iθ))
      (volume.restrict Iz) := hmem.2
  exact integrable_prod_of_iterated hnn hAE hslice houter

/-- `w` is measurable. -/
theorem measurable_w : Measurable w := by
  have hnum : Measurable (fun z : ℝ => (1 + z) ^ 2) := by
    have h : Measurable (fun z : ℝ => (1 + z) * (1 + z)) :=
      (measurable_const.add measurable_id).mul (measurable_const.add measurable_id)
    simpa [pow_two] using h
  have hden : Measurable (fun z : ℝ => z ^ 2) := by
    have h : Measurable (fun z : ℝ => z * z) := measurable_id.mul measurable_id
    simpa [pow_two] using h
  exact hnum.div hden

/-- `w z ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ w z := by
  rw [w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- For `z > 0` and `θ ∈ Iθ`, the `(i=0)` slot of `HkIntegrand` dominates the plain weighted
square of `g`. -/
theorem mass_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Iθ) :
    (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) ≤ HkIntegrand α 2 g z θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hw1 : 1 ≤ (w z) ^ 2 := by
    have h1 : 1 ≤ w z := one_le_w hz
    nlinarith
  have hterm : (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta))
      ≤ (g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
    rw [sq_mul_div_rpow_eq (g z θ) (w z) hsin]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg _) hw1)
      (Real.rpow_nonneg hsin _)
  refine le_trans hterm ?_
  rw [HkIntegrand]
  refine le_trans (Finset.single_le_sum (f := fun i : ℕ =>
      (DzIter i g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) ?_
      (Finset.mem_range.mpr (by norm_num : 0 < 3))) ?_
  · intro i _
    exact sq_nonneg _
  · refine le_add_of_nonneg_right ?_
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> simp [sq_nonneg]

/-- The `(i=1)` slot of `HkIntegrand` dominates the weighted square of `D_z g`. -/
theorem massSlot_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Iθ) :
    (Dz g z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) ≤ HkIntegrand α 2 g z θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hterm : (Dz g z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta))
      = (DzIter 1 g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
    rw [show DzIter 1 g = Dz g from rfl, sq_mul_div_rpow_eq (Dz g z θ) (w z) hsin]
  rw [hterm, HkIntegrand]
  refine le_trans (Finset.single_le_sum (f := fun i : ℕ =>
      (DzIter i g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) ?_
      (Finset.mem_range.mpr (by norm_num : 1 < 3))) ?_
  · intro i _
    exact sq_nonneg _
  · refine le_add_of_nonneg_right ?_
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> simp [sq_nonneg]

/-- The `(i=1)` slot of `HkIntegrand` dominates the weighted square of `D_z g` (version with
`z ∈ Iz`, where the case `z = 0` is trivial). -/
theorem massSlot_le_HkIntegrand_Iz (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : z ∈ Iz)
    (hθ : θ ∈ Iθ) :
    (Dz g z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) ≤ HkIntegrand α 2 g z θ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · subst h0
    simp [Dz, HkIntegrand_nonneg]
  · exact massSlot_le_HkIntegrand α g hpos hθ

/-- **The radial-Hardy slice mass bound.** -/
theorem slice_mass_le_HkSq {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hdec : Work.Spaces.DecayInZ 2 g)
    (hmem : Work.Spaces.HkMem α 2 g) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta))) ≤ HkSq α 2 g := by
  obtain ⟨hsumI, hsumE⟩ := HkIntegrand_integrable_prod (k := 2) hsm hmem
  -- the σ-slice of the `HkIntegrand` sum is integrable
  have hSint : ∀ᵐ σ ∂(volume.restrict Iθ),
      Integrable (fun s => HkIntegrand α 2 g s σ) (volume.restrict Iz) :=
    hsumI.prod_left_ae
  -- integrability of the right-hand side as a function of σ
  have hMint : Integrable (fun σ => ∫ s, HkIntegrand α 2 g s σ ∂(volume.restrict Iz))
      (volume.restrict Iθ) := hsumI.integral_prod_right
  -- the swap producing `HkSq`
  have hswap : (∫ σ, ∫ s, HkIntegrand α 2 g s σ ∂(volume.restrict Iz)
        ∂(volume.restrict Iθ)) = HkSq α 2 g :=
    ((MeasureTheory.integral_integral_swap hsumI).symm.trans
      ((MeasureTheory.integral_integral hsumI).trans hsumE))
  -- integrability of the left-hand side
  have hLint : Integrable (fun σ => (g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta)))
      (volume.restrict Iθ) := by
    refine Integrable.mono' (hmem.1 z hz.le) ?_ ?_
    · have hcont : ContinuousOn
          (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(eta)))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
        have hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          hsm.continuousOn.mono (fun p hp =>
            ⟨lt_trans (by norm_num : (-1 : ℝ) < 0) (show (0 : ℝ) < p.1 from hp.1), hp.2⟩)
        refine (hg.pow 2).mul ?_
        refine ((Real.continuous_sin.comp
          (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
        intro p hp
        have h1 : 0 < p.2 := hp.2.1
        have h2 : p.2 < Real.pi / 2 := hp.2.2
        refine Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_))
        · show 0 < 2 * p.2
          linarith
        · show 2 * p.2 < Real.pi
          linarith [Real.pi_pos]
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _))]
      exact mass_le_HkIntegrand α g hz hσ
  -- the pointwise Hardy bound, averaged over `θ`
  have hpt : ∀ᵐ σ ∂(volume.restrict Iθ),
      (g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta))
        ≤ ∫ s, HkIntegrand α 2 g s σ ∂(volume.restrict Iz) := by
    filter_upwards [hSint, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hS hσIoo
    have hσIθ : σ ∈ Iθ := ⟨hσIoo.1.le, hσIoo.2.le⟩
    have hsinpos : 0 < Real.sin (2 * σ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hσIoo.1]) (by linarith [hσIoo.2, Real.pi_pos])
    have hc1 : 1 ≤ (Real.sin (2 * σ)) ^ (-(eta)) := one_le_sin_rpow_neg_eta hσIoo.1 hσIoo.2
    have hcnn : 0 ≤ (Real.sin (2 * σ)) ^ (-(eta)) :=
      Real.rpow_nonneg hsinpos.le _
    -- the radial Hardy inequality for the `σ`-slice
    have hcd : ContDiffOn ℝ 1 (fun s => g s σ) (Set.Ioi 0) :=
      (hsm.curry_z hσIoo).of_le (by simp [Work.Stability.smoothOrder]) |>.mono
        (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
    have hten : Tendsto (fun s => g s σ) atTop (nhds 0) :=
      hdec 0 0 (by norm_num) σ hσIθ
    -- the `(i=1)` slot of the sum, as a function of `s`
    have hmass_aesm : AEStronglyMeasurable
        (fun s => (Dz g s σ) ^ 2 * (w s) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta)))
        (volume.restrict Iz) :=
      ((((measurable_id.mul (measurable_deriv (fun s' => g s' σ))).pow_const 2).mul
        (measurable_w.pow_const 2)).mul_const _).aestronglyMeasurable
    have hmassInt : Integrable
        (fun s => (Dz g s σ) ^ 2 * (w s) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta)))
        (volume.restrict Iz) := by
      refine Integrable.mono' hS hmass_aesm ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
      have hle := massSlot_le_HkIntegrand_Iz α g (by simpa [Iz] using hs) hσIθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg hsinpos.le _))]
      exact hle
    have hGint : Integrable (fun s => (Dz g s σ) ^ 2 * (w s) ^ 2) (volume.restrict Iz) := by
      refine Integrable.mono' hmassInt
        ((((measurable_id.mul (measurable_deriv (fun s' => g s' σ))).pow_const 2).mul
          (measurable_w.pow_const 2))).aestronglyMeasurable ?_
      filter_upwards with s
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hc1
    have hHardy : (g z σ) ^ 2 ≤ ∫ s, (Dz g s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz) :=
      Work.FTS.H2.hardyZ_open hcd hten hGint z hz
    have hle1 : (∫ s, (Dz g s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz))
        * (Real.sin (2 * σ)) ^ (-(eta))
        ≤ ∫ s, HkIntegrand α 2 g s σ ∂(volume.restrict Iz) := by
      have h1 : (∫ s, (Dz g s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz))
          * (Real.sin (2 * σ)) ^ (-(eta))
          = ∫ s, (Dz g s σ) ^ 2 * (w s) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta))
              ∂(volume.restrict Iz) := by
        rw [MeasureTheory.integral_mul_const]
      rw [h1]
      exact MeasureTheory.integral_mono_ae hmassInt hS
        (ae_restrict_of_forall_mem measurableSet_Ici fun s hs =>
          massSlot_le_HkIntegrand_Iz α g (by simpa [Iz] using hs) hσIθ)
    calc (g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta))
        ≤ (∫ s, (Dz g s σ) ^ 2 * (w s) ^ 2 ∂(volume.restrict Iz))
            * (Real.sin (2 * σ)) ^ (-(eta)) := mul_le_mul_of_nonneg_right hHardy hcnn
      _ ≤ ∫ s, HkIntegrand α 2 g s σ ∂(volume.restrict Iz) := hle1
  calc (∫ θ in Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)))
      = ∫ σ, (g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(eta)) ∂(volume.restrict Iθ) := rfl
    _ ≤ ∫ σ, (∫ s, HkIntegrand α 2 g s σ ∂(volume.restrict Iz))
          ∂(volume.restrict Iθ) := MeasureTheory.integral_mono_ae hLint hMint hpt
    _ = HkSq α 2 g := hswap

end Work.FTS.Apriori.Profile
