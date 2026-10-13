/-
`Work.FTS.Apriori.Profile.linf_H2_quad` — the `L^∞`–`ℋ²` bound in the interior class
`SmoothQuad` (Elgindi, §H2, Corollary `Linfty`).

For `g` smooth on the *open* quadrant (`SmoothQuad`, genuine `C^∞` — **not** the analytic
class `SmoothNbhd`), vanishing on the angular boundary, with decay in `z` and in `ℋ²`, the
uniform norm of `g` on the closed quadrant is bounded by `100/√(γ-1)` times its `ℋ²`-norm.

Structure of the proof.  The values at the two angular endpoints are `0` by `VanishTheta`, and
the case `z = 0` follows from the case `z > 0` by continuity on the open quadrant.  For `z > 0`
and `θ ∈ (0,π/2)` one compares `g z θ` with `g z θ'` for `θ'` in an interval on one side of `θ`:
the *radial Hardy inequality* applied to `∂_θ g(·,σ)` bounds the angular difference by the slot
`(D_z D_θ g · W)²` of `HkIntegrand` (`slice_diff_le_HkSq`), while the average of `|g z θ'|²`
against the weight `sin(2θ')^{-η}` is bounded by `HkSq` (`slice_mass_le_HkSq`).  Splitting at
`θ = 3π/8` and using that both angular weights have mass at least `1/4` on the relevant side
(`theta_mass_up`, `theta_mass_down`) closes the estimate.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Submission.Work.FTS.Apriori.Profile.SliceDiff

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

/-- The elementary closing estimate of the bootstrap: from `x · NJ ≤ 2S + (200/γ') S NJ`,
`NJ ≥ 1/4`, `γ' ≤ 1/10` and `S ≥ 0` one gets `x ≤ (500/γ') S`. -/
theorem arith_bound {γ' S NJ x : ℝ} (hγ : 0 < γ') (hγ' : γ' ≤ 1 / 10) (hS : 0 ≤ S)
    (hNJ : 1 / 4 ≤ NJ) (h : x * NJ ≤ 200 / γ' * S * NJ + 2 * S) :
    x ≤ 500 / γ' * S := by
  have hNJpos : 0 < NJ := lt_of_lt_of_le (by norm_num) hNJ
  have hx : x ≤ (200 / γ' * S * NJ + 2 * S) / NJ := (le_div_iff₀ hNJpos).mpr h
  have h2 : 2 * S / NJ ≤ 8 * S := by
    rw [div_le_iff₀ hNJpos]
    nlinarith [hNJ, hS]
  have h3 : 8 * S ≤ 0.8 / γ' * S := by
    have h0 : 8 ≤ 0.8 / γ' := by
      rw [le_div_iff₀ hγ]
      linarith
    exact mul_le_mul_of_nonneg_right h0 hS
  calc x ≤ (200 / γ' * S * NJ + 2 * S) / NJ := hx
    _ = 200 / γ' * S + 2 * S / NJ := by
        field_simp
        try ring
    _ ≤ 200 / γ' * S + 8 * S := by linarith
    _ ≤ 200 / γ' * S + 0.8 / γ' * S := by linarith
    _ = 200.8 / γ' * S := by ring
    _ ≤ 500 / γ' * S := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        exact div_le_div_of_nonneg_right (by norm_num) hγ.le

/-- The pointwise bound for `z > 0`. -/
theorem linf_pointwise {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hvt : Work.Spaces.VanishTheta g)
    (hdec : Work.Spaces.DecayInZ 2 g) (hmem : Work.Spaces.HkMem α 2 g) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Iθ, |g z θ| ^ 2 ≤ 500 / (gam α - 1) * HkSq α 2 g := by
  have hg1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hg0 : gam α ≠ 0 := ne_of_gt (by linarith [one_lt_gam hα])
  have hg2 : gam α ≠ 2 := by
    intro h
    have h' : gam α ≤ 1.1 := by rw [gam]; linarith
    linarith
  have hdec0 : ∀ θ ∈ Iθ, Tendsto (fun z => g z θ) atTop (nhds 0) :=
    fun θ hθ => hdec 0 0 (by norm_num) θ hθ
  set S : ℝ := HkSq α 2 g with hSdef
  have hSnn : 0 ≤ S := HkSq_nonneg α 2 g
  have hCnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hg1.le
  have hK500 : 0 ≤ 500 / (gam α - 1) := div_nonneg (by norm_num) hg1.le
  -- the angular weights
  have hηint : IntegrableOn (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (-(eta)))
      (Set.Ioc 0 (Real.pi / 2)) :=
    ((sin_two_rpow (-(eta)) (by linarith [eta_lt_one]) (by linarith [eta_pos])).1).mono_set
      (fun θ' hθ' => ⟨le_of_lt hθ'.1, hθ'.2⟩)
  -- the weighted mass of `g` at fixed `z`
  have hmassI : ∀ z : ℝ, 0 < z →
      IntegrableOn (fun θ' => g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) Iθ := by
    intro z hz
    refine Integrable.mono' (hmem.1 z hz.le) ?_ ?_
    · have hcont : ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(eta))) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
        have hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          hsm.continuousOn.mono (fun p hp =>
            ⟨lt_trans (by norm_num : (-1 : ℝ) < 0) hp.1, hp.2⟩)
        refine (hg.pow 2).mul ?_
        refine ((Real.continuous_sin.comp
          (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
        intro p hp
        have h1 : 0 < p.2 := hp.2.1
        have h2 : p.2 < Real.pi / 2 := hp.2.2
        refine Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_))
        · show 0 < 2 * p.2; linarith
        · show 2 * p.2 < Real.pi; linarith [Real.pi_pos]
      exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ' hθ'
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ') _))]
      exact mass_le_HkIntegrand α g hz hθ'
  have hmass_int : ∀ z : ℝ, 0 < z →
      IntegrableOn (fun θ' => g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta)))
        (Set.Ioc 0 (Real.pi / 2)) := fun z hz =>
    (hmassI z hz).mono_set (fun θ' hθ' => ⟨le_of_lt hθ'.1, hθ'.2⟩)
  have hmass_le : ∀ z : ℝ, 0 < z →
      (∫ θ' in Set.Ioc 0 (Real.pi / 2), g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) ≤ S := by
    intro z hz
    refine le_trans (MeasureTheory.setIntegral_mono_set (hmassI z hz) ?_ ?_)
      (slice_mass_le_HkSq hsm hdec hmem hz)
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ' hθ' =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ') _))
    · exact Filter.Eventually.of_forall (fun θ' hθ' => ⟨le_of_lt hθ'.1, hθ'.2⟩)
  have hgle : gam α - 1 ≤ 1 / 10 := by rw [gam_sub_one]; linarith
  intro z hzpos θ hθ
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
  · rw [← hθ0, hvt.1 z]
    have : (0 : ℝ) ≤ 500 / (gam α - 1) * HkSq α 2 g := mul_nonneg hK500 (HkSq_nonneg α 2 g)
    simpa using this
  rcases lt_or_eq_of_le hθ.2 with hθπ | hθπ
  · -- #### the interior of the quadrant
    have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθπ⟩
    by_cases hcase : θ ≤ 3 * Real.pi / 8
    · -- **Case A**: `θ ≤ 3π/8`, average over `θ' ∈ (θ, π/2)`
      set NJ : ℝ := ∫ θ' in Set.Ioc θ (Real.pi / 2), (Real.sin (2 * θ')) ^ (-(eta)) with hNJdef
      have hNJ : 1 / 4 ≤ NJ := theta_mass_up hθ.1 hcase
      have hNJpos : 0 < NJ := lt_of_lt_of_le (by norm_num) hNJ
      have hsub : Set.Ioc θ (Real.pi / 2) ⊆ Set.Ioc 0 (Real.pi / 2) := fun θ' hθ' =>
        ⟨lt_trans hθpos hθ'.1, hθ'.2⟩
      have hkey : ∀ θ' ∈ Set.Ioc θ (Real.pi / 2),
          (|g z θ| ^ 2) * (Real.sin (2 * θ')) ^ (-(eta))
            ≤ (2 * (100 / (gam α - 1)) * S) * (Real.sin (2 * θ')) ^ (-(eta))
              + 2 * (g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) := by
        intro θ' hθ'
        rcases eq_or_lt_of_le hθ'.2 with h | h
        · -- the endpoint `π/2`: the weight vanishes
          have hs0 : (Real.sin (2 * θ')) ^ (-(eta)) = 0 := by
            rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
              Real.zero_rpow (by linarith [eta_pos] : -(eta) ≠ 0)]
          rw [hs0]
          simp only [mul_zero, zero_add]
          exact le_refl 0
        · -- the interior: the Hardy difference bound
          have hθ'Ioo : θ' ∈ Set.Ioo 0 (Real.pi / 2) :=
            ⟨lt_of_lt_of_le hθpos hθ'.1.le, h⟩
          have hdiff := slice_diff_le_HkSq hg0 hg2 hsm hdec hmem hθIoo hθ'Ioo hθ'.1.le hzpos
          have hcost : (∫ σ in Set.Ioc θ θ', (Real.sin (2 * σ)) ^ (gam α - 2))
              ≤ 100 / (gam α - 1) := by
            have h1 : (∫ σ in Set.Ioc θ θ', (Real.sin (2 * σ)) ^ (gam α - 2))
                ≤ (∫ σ in Set.Ioc θ (Real.pi / 2), (Real.sin (2 * σ)) ^ (gam α - 2)) := by
              refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
              · exact (integrableOn_sin_gam_sub_two hα hα1).mono_set
                  (fun σ hσ => ⟨le_of_lt (lt_trans hθpos hσ.1), hσ.2⟩)
              · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun σ hσ =>
                  Real.rpow_nonneg (sin_two_nonneg_Iθ
                    ⟨le_of_lt (lt_trans hθpos hσ.1), hσ.2⟩) _)
              · exact Filter.Eventually.of_forall (fun σ hσ => ⟨hσ.1, le_trans hσ.2 hθ'.2⟩)
            exact le_trans h1 (theta_cost_le_up hα hα1 hθ)
          have hdf : (g z θ - g z θ') ^ 2 ≤ (100 / (gam α - 1)) * S :=
            le_trans hdiff (mul_le_mul_of_nonneg_right hcost hSnn)
          have hpt : |g z θ| ^ 2 ≤ 2 * (100 / (gam α - 1)) * S + 2 * |g z θ'| ^ 2 := by
            have h1 : |g z θ| ≤ |g z θ - g z θ'| + |g z θ'| := by
              have h2 := abs_add_le (g z θ - g z θ') (g z θ')
              simpa only [sub_add_cancel] using h2
            have h2 : (g z θ - g z θ') ^ 2 = |g z θ - g z θ'| ^ 2 := (sq_abs _).symm
            nlinarith [h1, hdf, h2, abs_nonneg (g z θ), abs_nonneg (g z θ - g z θ'),
              abs_nonneg (g z θ'), sq_nonneg (|g z θ - g z θ'| - |g z θ'|)]
          have hsin0 : 0 ≤ Real.sin (2 * θ') := Real.sin_nonneg_of_nonneg_of_le_pi
            (by linarith [hθ'.1, hθpos]) (by linarith [h, Real.pi_pos])
          calc (|g z θ| ^ 2) * (Real.sin (2 * θ')) ^ (-(eta))
              ≤ (2 * (100 / (gam α - 1)) * S + 2 * |g z θ'| ^ 2)
                  * (Real.sin (2 * θ')) ^ (-(eta)) :=
                mul_le_mul_of_nonneg_right hpt (Real.rpow_nonneg hsin0 _)
            _ = (2 * (100 / (gam α - 1)) * S) * (Real.sin (2 * θ')) ^ (-(eta))
                  + 2 * (g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) := by
                rw [sq_abs]; ring
      -- integrate the pointwise bound against `sin(2θ')^{-η}`
      have hfI : IntegrableOn (fun θ' => g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta)))
          (Set.Ioc θ (Real.pi / 2)) := (hmass_int z hzpos).mono_set hsub
      have hhI : IntegrableOn (fun θ' => (Real.sin (2 * θ')) ^ (-(eta)))
          (Set.Ioc θ (Real.pi / 2)) := hηint.mono_set hsub
      have hbigI : IntegrableOn
          (fun θ' => (2 * (100 / (gam α - 1)) * S) * (Real.sin (2 * θ')) ^ (-(eta))
            + 2 * (g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta)))) (Set.Ioc θ (Real.pi / 2)) :=
        IntegrableOn.add (hhI.const_mul (2 * (100 / (gam α - 1)) * S)) (hfI.const_mul 2)
      have hIneq := MeasureTheory.integral_mono_ae (hhI.const_mul (|g z θ| ^ 2)) hbigI
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun θ' hθ' => hkey θ' hθ')
      have hLHS : (∫ θ' in Set.Ioc θ (Real.pi / 2),
            (|g z θ| ^ 2) * (Real.sin (2 * θ')) ^ (-(eta))) = |g z θ| ^ 2 * NJ := by
        rw [hNJdef, MeasureTheory.integral_const_mul]
      have hRHS : (∫ θ' in Set.Ioc θ (Real.pi / 2),
            (2 * (100 / (gam α - 1)) * S) * (Real.sin (2 * θ')) ^ (-(eta))
              + 2 * (g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))))
          = (2 * (100 / (gam α - 1)) * S) * NJ
            + 2 * (∫ θ' in Set.Ioc θ (Real.pi / 2),
                g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) := by
        rw [hNJdef, MeasureTheory.integral_add (hhI.const_mul _) (hfI.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [hLHS, hRHS] at hIneq
      have hmid : (∫ θ' in Set.Ioc θ (Real.pi / 2),
          g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) ≤ S := by
        refine le_trans (MeasureTheory.setIntegral_mono_set (hmassI z hzpos) ?_ ?_)
          (slice_mass_le_HkSq hsm hdec hmem hzpos)
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ' hθ' =>
            mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ') _))
        · exact Filter.Eventually.of_forall (fun θ' hθ' =>
            ⟨le_of_lt (lt_trans hθpos hθ'.1), hθ'.2⟩)
      refine arith_bound hg1 hgle hSnn hNJ ?_
      calc |g z θ| ^ 2 * NJ
          ≤ (2 * (100 / (gam α - 1)) * S) * NJ
            + 2 * (∫ θ' in Set.Ioc θ (Real.pi / 2),
                g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) := hIneq
        _ ≤ (2 * (100 / (gam α - 1)) * S) * NJ + 2 * S := by linarith
        _ = 200 / (gam α - 1) * S * NJ + 2 * S := by ring
    · -- **Case B**: `3π/8 < θ`, average over `θ' ∈ (0, θ)`
      set NJ : ℝ := ∫ θ' in Set.Ioc 0 θ, (Real.sin (2 * θ')) ^ (-(eta)) with hNJdef
      have hNJ : 1 / 4 ≤ NJ := theta_mass_down hθ.2 (le_of_lt (not_le.mp hcase))
      have hNJpos : 0 < NJ := lt_of_lt_of_le (by norm_num) hNJ
      have hsub : Set.Ioc 0 θ ⊆ Set.Ioc 0 (Real.pi / 2) := fun θ' hθ' =>
        ⟨hθ'.1, le_of_lt (lt_of_le_of_lt hθ'.2 hθπ)⟩
      have hkey : ∀ θ' ∈ Set.Ioc 0 θ,
          (|g z θ| ^ 2) * (Real.sin (2 * θ')) ^ (-(eta))
            ≤ (2 * (100 / (gam α - 1)) * S) * (Real.sin (2 * θ')) ^ (-(eta))
              + 2 * (g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) := by
        intro θ' hθ'
        rcases eq_or_lt_of_le hθ'.1.le with h | h
        · -- the endpoint `0`: the weight vanishes
          have hs0 : (Real.sin (2 * θ')) ^ (-(eta)) = 0 := by
            rw [← h, show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero,
              Real.zero_rpow (by linarith [eta_pos] : -(eta) ≠ 0)]
          rw [hs0]
          simp only [mul_zero, zero_add]
          exact le_refl 0
        · -- the interior
          have hθ'Ioo : θ' ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h, lt_of_le_of_lt hθ'.2 hθπ⟩
          have hdiff := slice_diff_le_HkSq hg0 hg2 hsm hdec hmem hθ'Ioo hθIoo hθ'.2 hzpos
          have hcost : (∫ σ in Set.Ioc θ' θ, (Real.sin (2 * σ)) ^ (gam α - 2))
              ≤ 100 / (gam α - 1) := by
            have h1 : (∫ σ in Set.Ioc θ' θ, (Real.sin (2 * σ)) ^ (gam α - 2))
                ≤ (∫ σ in Set.Ioc 0 θ, (Real.sin (2 * σ)) ^ (gam α - 2)) := by
              refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
              · exact (integrableOn_sin_gam_sub_two hα hα1).mono_set
                  (fun σ hσ => ⟨le_of_lt hσ.1, le_trans hσ.2 hθ.2⟩)
              · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun σ hσ =>
                  Real.rpow_nonneg (sin_two_nonneg_Iθ
                    ⟨le_of_lt hσ.1, le_trans hσ.2 hθ.2⟩) _)
              · exact Filter.Eventually.of_forall (fun σ hσ => ⟨lt_trans h hσ.1, hσ.2⟩)
            exact le_trans h1 (theta_cost_le_down hα hα1 hθ)
          have hdf : (g z θ' - g z θ) ^ 2 ≤ (100 / (gam α - 1)) * S :=
            le_trans hdiff (mul_le_mul_of_nonneg_right hcost hSnn)
          have hdf' : (g z θ - g z θ') ^ 2 ≤ (100 / (gam α - 1)) * S := by
            rw [show g z θ - g z θ' = -(g z θ' - g z θ) by ring,
              show (-(g z θ' - g z θ)) ^ 2 = (g z θ' - g z θ) ^ 2 by ring]
            exact hdf
          have hpt : |g z θ| ^ 2 ≤ 2 * (100 / (gam α - 1)) * S + 2 * |g z θ'| ^ 2 := by
            have h1 : |g z θ| ≤ |g z θ - g z θ'| + |g z θ'| := by
              have h2 := abs_add_le (g z θ - g z θ') (g z θ')
              simpa only [sub_add_cancel] using h2
            have h2 : (g z θ - g z θ') ^ 2 = |g z θ - g z θ'| ^ 2 := (sq_abs _).symm
            nlinarith [h1, hdf', h2, abs_nonneg (g z θ), abs_nonneg (g z θ - g z θ'),
              abs_nonneg (g z θ'), sq_nonneg (|g z θ - g z θ'| - |g z θ'|)]
          have hsin0 : 0 ≤ Real.sin (2 * θ') := Real.sin_nonneg_of_nonneg_of_le_pi
            (by linarith [h]) (by linarith [hθ'.2, hθπ, Real.pi_pos])
          calc (|g z θ| ^ 2) * (Real.sin (2 * θ')) ^ (-(eta))
              ≤ (2 * (100 / (gam α - 1)) * S + 2 * |g z θ'| ^ 2)
                  * (Real.sin (2 * θ')) ^ (-(eta)) :=
                mul_le_mul_of_nonneg_right hpt (Real.rpow_nonneg hsin0 _)
            _ = (2 * (100 / (gam α - 1)) * S) * (Real.sin (2 * θ')) ^ (-(eta))
                  + 2 * (g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) := by
                rw [sq_abs]; ring
      have hfI : IntegrableOn (fun θ' => g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta)))
          (Set.Ioc 0 θ) := (hmass_int z hzpos).mono_set hsub
      have hhI : IntegrableOn (fun θ' => (Real.sin (2 * θ')) ^ (-(eta))) (Set.Ioc 0 θ) :=
        hηint.mono_set hsub
      have hbigI : IntegrableOn
          (fun θ' => (2 * (100 / (gam α - 1)) * S) * (Real.sin (2 * θ')) ^ (-(eta))
            + 2 * (g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta)))) (Set.Ioc 0 θ) :=
        IntegrableOn.add (hhI.const_mul (2 * (100 / (gam α - 1)) * S)) (hfI.const_mul 2)
      have hIneq := MeasureTheory.integral_mono_ae (hhI.const_mul (|g z θ| ^ 2)) hbigI
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun θ' hθ' => hkey θ' hθ')
      have hLHS : (∫ θ' in Set.Ioc 0 θ,
            (|g z θ| ^ 2) * (Real.sin (2 * θ')) ^ (-(eta))) = |g z θ| ^ 2 * NJ := by
        rw [hNJdef, MeasureTheory.integral_const_mul]
      have hRHS : (∫ θ' in Set.Ioc 0 θ,
            (2 * (100 / (gam α - 1)) * S) * (Real.sin (2 * θ')) ^ (-(eta))
              + 2 * (g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))))
          = (2 * (100 / (gam α - 1)) * S) * NJ
            + 2 * (∫ θ' in Set.Ioc 0 θ, g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) := by
        rw [hNJdef, MeasureTheory.integral_add (hhI.const_mul _) (hfI.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [hLHS, hRHS] at hIneq
      have hmid : (∫ θ' in Set.Ioc 0 θ, g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) ≤ S := by
        refine le_trans (MeasureTheory.setIntegral_mono_set (hmassI z hzpos) ?_ ?_)
          (slice_mass_le_HkSq hsm hdec hmem hzpos)
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ' hθ' =>
            mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ') _))
        · exact Filter.Eventually.of_forall (fun θ' hθ' =>
            ⟨le_of_lt hθ'.1, le_of_lt (lt_of_le_of_lt hθ'.2 hθπ)⟩)
      refine arith_bound hg1 hgle hSnn hNJ ?_
      calc |g z θ| ^ 2 * NJ
          ≤ (2 * (100 / (gam α - 1)) * S) * NJ
            + 2 * (∫ θ' in Set.Ioc 0 θ,
                g z θ' ^ 2 * (Real.sin (2 * θ')) ^ (-(eta))) := hIneq
        _ ≤ (2 * (100 / (gam α - 1)) * S) * NJ + 2 * S := by linarith
        _ = 200 / (gam α - 1) * S * NJ + 2 * S := by ring
  · -- the endpoint `θ = π/2`
    rw [hθπ, hvt.2 z]
    have : (0 : ℝ) ≤ 500 / (gam α - 1) * HkSq α 2 g := mul_nonneg hK500 (HkSq_nonneg α 2 g)
    simpa using this

theorem linf_H2_quad {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hvt : Work.Spaces.VanishTheta g)
    (hdec : Work.Spaces.DecayInZ 2 g) (hmem : Work.Spaces.HkMem α 2 g) :
    Work.Spaces.supAbs g
      ≤ 100 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 2 g := by
  have hg1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hKnn : 0 ≤ 500 / (gam α - 1) := div_nonneg (by norm_num) hg1.le
  have hpt := linf_pointwise hα hα1 hsm hvt hdec hmem
  have hsqr : ∀ z : ℝ, 0 < z → ∀ θ ∈ Iθ,
      |g z θ| ≤ Real.sqrt (500 / (gam α - 1)) * Real.sqrt (HkSq α 2 g) := by
    intro z hz θ hθ
    calc |g z θ| = Real.sqrt ((g z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (500 / (gam α - 1) * HkSq α 2 g) :=
          Real.sqrt_le_sqrt (by rw [← sq_abs (g z θ)]; exact hpt z hz θ hθ)
      _ = Real.sqrt (500 / (gam α - 1)) * Real.sqrt (HkSq α 2 g) := Real.sqrt_mul hKnn _
  have hzero : ∀ θ ∈ Iθ, |g 0 θ| ≤ Real.sqrt (500 / (gam α - 1)) * Real.sqrt (HkSq α 2 g) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · rw [← hθ0, hvt.1 0]
      simp only [abs_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rcases lt_or_eq_of_le hθ.2 with hθπ | hθπ
    · have hcd : ContDiffAt ℝ 1 (Function.uncurry g) (0, θ) :=
        (hsm.contDiffAt (isOpen_quadU.mem_nhds (by
          refine ⟨?_, ?_⟩
          · show (-1 : ℝ) < 0; norm_num
          · exact ⟨hθpos, hθπ⟩))).of_le (by norm_num)
      have hcont : ContinuousAt (fun z : ℝ => g z θ) 0 := by
        have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => g z θ)
            (Set.Ioi (-1)) :=
          Work.FTS.LocData.contDiffOn_slice_z
            (s := Set.Ioi (-1)) (t := Set.Ioo 0 (Real.pi / 2)) hsm ⟨hθpos, hθπ⟩
        exact hslice.continuousOn.continuousAt
          (isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0))
      have htend : Tendsto (fun z => |g z θ| ^ 2) (𝓝[>] (0 : ℝ)) (nhds (|g 0 θ| ^ 2)) := by
        have h1 : Tendsto (fun z => g z θ) (𝓝[>] (0 : ℝ)) (nhds (g 0 θ)) :=
          hcont.tendsto.mono_left nhdsWithin_le_nhds
        simpa using h1.abs.pow 2
      have hsq : |g 0 θ| ^ 2 ≤ 500 / (gam α - 1) * HkSq α 2 g := by
        refine le_of_tendsto htend ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact hpt z hz θ hθ
      calc |g 0 θ| = Real.sqrt ((g 0 θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (500 / (gam α - 1) * HkSq α 2 g) :=
            Real.sqrt_le_sqrt (by rw [← sq_abs (g 0 θ)]; exact hsq)
        _ = Real.sqrt (500 / (gam α - 1)) * Real.sqrt (HkSq α 2 g) := Real.sqrt_mul hKnn _
    · rw [hθπ, hvt.2 0]
      simp only [abs_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hpt' : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |g z θ| ≤ Real.sqrt (500 / (gam α - 1)) * Real.sqrt (HkSq α 2 g) := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0; exact hzero θ hθ
    · exact hsqr z hzpos θ hθ
  have hsup : supAbs g ≤ Real.sqrt (500 / (gam α - 1)) * Real.sqrt (HkSq α 2 g) :=
    supAbs_le hpt'
  have hconst : Real.sqrt (500 / (gam α - 1)) ≤ 100 / Real.sqrt (gam α - 1) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 500) (gam α - 1),
      div_le_div_iff_of_pos_right (Real.sqrt_pos_of_pos hg1)]
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc supAbs g ≤ Real.sqrt (500 / (gam α - 1)) * Real.sqrt (HkSq α 2 g) := hsup
    _ = Real.sqrt (500 / (gam α - 1)) * HkNorm α 2 g := rfl
    _ ≤ 100 / Real.sqrt (gam α - 1) * HkNorm α 2 g :=
        mul_le_mul_of_nonneg_right hconst (HkNorm_nonneg α 2 g)

end Work.FTS.Apriori.Profile
