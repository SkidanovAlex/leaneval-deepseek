import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.mixed_slice_pointwise_le_noTrace
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS_RegExport.RXT.HkMinSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.HkMinSq`

The squared form of the pointwise bound: for a datum `f` which is `C⁴` on the open quadrant and
honestly in `ℋ⁴`, every mixed slot of order `≤ 2` satisfies

  `(D_z^bD_θ^af z θ)² ≤ C₀ · (min z 1)² · HkSq α 4 f`,  `C₀ = ((4/π) + 2·(100/(γ-1)))·40`.

The three steps are the angular mean-value/variation bound, the weighted radial Agmon bound for
the slot itself and for its `θ`-derivative, and the identification of the occurring slice
energies with the slots of `HkIntegrand α 4`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two delegated helpers, repointed to their proved siblings -/

theorem tmp_angular_meanVar_le {γ : ℝ} (hγ : 1 < γ) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint1 : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ)
    (hint2 : MeasureTheory.IntegrableOn (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      g θ ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))
          * (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) :=
  angular_meanVar_le hγ hg hint1 hint2

theorem tmp_radial_noDecay_le {v v' : ℝ → ℝ}
    (hv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' z) z)
    (hint1 : MeasureTheory.IntegrableOn (fun z => v z ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn (fun z => (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), v z ^ 2 ≤ 20 * (min z 1) ^ 2 *
      ((∫ z in Set.Ioi 0, v z ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ioi 0, (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2)) :=
  radial_noDecay_le hv hint1 hint2

/-- The `Wt`-identity: the weighted square of a mixed slot is `sin^{-γ}` times its `w`-weighted
square. -/
theorem Wt_sq (α : ℝ) {x σ u : ℝ} (hσ : 0 < Real.sin (2 * σ)) :
    (u * Work.Spaces.Wt α x σ) ^ 2
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (u ^ 2 * (Work.Spaces.w x) ^ 2) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow]
  rw [show ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) from by
    rw [sq, ← Real.rpow_add hσ]; congr 1; ring]
  ring

theorem hkMem_pointwise_min_sq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) {b a : ℕ} (hab : a + b ≤ 2) {z θ : ℝ} (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (((4 / Real.pi) + 2 * (100 / (Work.Spaces.gam α - 1))) * 40) * (min z 1) ^ 2
        * Work.Spaces.HkSq α 4 f := by
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := Work.FTS.H2.one_le_w_sq hz
  obtain ⟨hNfin, hNint, hNae⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  -- admissibility of the four slots
  have hadm_ba : FTSAdm b a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact Or.inr ⟨h, by omega⟩
    · exact Or.inl ⟨h, by omega⟩
  have hadm_ba1 : FTSAdm (b + 1) a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact Or.inr ⟨h, by omega⟩
    · exact Or.inl ⟨h, by omega⟩
  have hadm_ba2 : FTSAdm b (a + 1) := Or.inl ⟨by omega, by omega⟩
  have hadm_ba3 : FTSAdm (b + 1) (a + 1) := Or.inl ⟨by omega, by omega⟩
  -- the four slice energies
  obtain ⟨hAint, hAae, hAcmp, hAbd⟩ := slot_slice_all hα h4 hmem b a hadm_ba
  obtain ⟨hA1int, hA1ae, hA1cmp, hA1bd⟩ := slot_slice_all hα h4 hmem (b + 1) a hadm_ba1
  obtain ⟨hBint, hBae, hBcmp, hBbd⟩ := slot_slice_all hα h4 hmem b (a + 1) hadm_ba2
  obtain ⟨hB1int, hB1ae, hB1cmp, hB1bd⟩ := slot_slice_all hα h4 hmem (b + 1) (a + 1) hadm_ba3
  obtain ⟨hCint, hCcmp, hCbd⟩ := slot_slice_Wt_all hα h4 hmem b (a + 1) (by omega) (by omega)
  obtain ⟨hC1int, hC1cmp, hC1bd⟩ := slot_slice_Wt_all hα h4 hmem (b + 1) (a + 1) (by omega)
    (by omega)
  -- the two θ-integrands of the angular inequality are integrable
  have hslice1 : ContinuousOn (fun σ => Work.Spaces.mixed b a f z σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 b a 1 (by omega) hz).continuousOn
  have hint1 : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.mixed b a f z σ) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z hzI)
      (aestrongly_Iθ_of_continuousOn (hslice1.pow 2)) ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc (Work.Spaces.mixed b a f z σ) ^ 2
        ≤ (Work.Spaces.mixed b a f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          le_mul_of_one_le_right (sq_nonneg _) hw1
      _ ≤ Work.Spaces.HkIntegrand α 4 f z σ := slot_pointwise_le hα b a hadm_ba z hσ
  -- the angular identity `(∂_θ u)² sin^{2-γ} = sin^{-γ} (D_θ u)²`
  have hId2 : (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) := by
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hD := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hz hσ
    have hpth : Work.Spaces.pth (Work.Spaces.mixed b a f) z σ
        = Work.Spaces.mixed b (a + 1) f z σ / Real.sin (2 * σ) := by
      have h' : Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.mixed b a f) z σ
          = Work.Spaces.mixed b (a + 1) f z σ := hD
      rw [eq_div_iff (ne_of_gt hsin), mul_comm]
      exact h'
    rw [hpth]
    have h1 : (Work.Spaces.mixed b (a + 1) f z σ / Real.sin (2 * σ)) ^ 2
        * (Real.sin (2 * σ)) ^ (2 : ℝ) = (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
      rw [Real.rpow_ofNat, div_pow]
      field_simp
    calc (Work.Spaces.mixed b (a + 1) f z σ / Real.sin (2 * σ)) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Work.Spaces.mixed b (a + 1) f z σ / Real.sin (2 * σ)) ^ 2
            * ((Real.sin (2 * σ)) ^ (2 : ℝ)
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by
          rw [show (2 - Work.Spaces.gam α) = (2 : ℝ) + (-(Work.Spaces.gam α)) by ring,
            Real.rpow_add hsin]
      _ = ((Work.Spaces.mixed b (a + 1) f z σ / Real.sin (2 * σ)) ^ 2
            * (Real.sin (2 * σ)) ^ (2 : ℝ))
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by ring
      _ = (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by rw [h1]
      _ = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by ring
  have hslice2 : ContinuousOn (fun σ => (Real.sin (2 * σ)) ^ (Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)))
  have hmeas_inv : MeasureTheory.AEStronglyMeasurable
      (fun σ : ℝ => ((Real.sin (2 * σ)) ^ (Work.Spaces.gam α))⁻¹
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aestrongly_Iθ_of_continuousOn
      ((hslice2.inv₀ (fun σ hσ =>
        ne_of_gt (Real.rpow_pos_of_pos (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ) _))).mul
        (((Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 b (a + 1) 1
          (by omega) hz).continuousOn).pow 2))
  have hg2bound : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 ≤ Real.sin (2 * σ) := (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ).le
    have hsinr : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsin _
    have hle : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        ≤ (Work.Spaces.mixed b (a + 1) f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
      calc (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          ≤ (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2 :=
            le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) hsinr) hw1
        _ = (Work.Spaces.mixed b (a + 1) f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
            rw [Wt_sq α (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)]; ring
    have hfin : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
      rw [mul_comm]
      exact hle.trans (Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ (a + 1) b (by omega)
        (by omega))
    exact hfin
  have hint2' : MeasureTheory.IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z hzI) ?_ ?_
    · refine hmeas_inv.congr ?_
      filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
      rw [Real.rpow_neg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ))]
    · filter_upwards [hg2bound, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ hσ'
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg
        (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ')) _) (sq_nonneg _))]
      exact hσ
  have hint2 : MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    hint2'.congr hId2.symm
  -- the derivative hypothesis of the angular step
  have hgd : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' => Work.Spaces.mixed b a f z σ')
        (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) σ := by
    intro σ hσ
    exact ((Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 b a 1 (by omega) hz).differentiableOn
      (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hσ) |>.hasDerivAt
  -- the angular inequality (Step I)
  have hang := tmp_angular_meanVar_le (γ := Work.Spaces.gam α) hγ1 hgd hint1 hint2 θ hθmem
  rw [MeasureTheory.integral_congr_ae hId2] at hang
  -- Step II: the radial bound for the first θ-integral
  have hL2u : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.mixed b a f z σ) ^ 2 ≤ 20 * (min z 1) ^ 2 *
        ((∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
          + (∫ x in Work.Spaces.Iz,
              (Work.Spaces.mixed (b + 1) a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)) := by
    filter_upwards [hAae, hA1ae, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hA hA1 hσ
    have hd : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun x' => Work.Spaces.mixed b a f x' σ)
          (Work.Spaces.pz (Work.Spaces.mixed b a f) x σ) x := by
      intro x hx
      exact ((Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hσ
        (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b a 1 (by omega))).differentiableOn
          (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hx) |>.hasDerivAt
    have h2 : MeasureTheory.IntegrableOn
        (fun x => (x * Work.Spaces.pz (Work.Spaces.mixed b a f) x σ) ^ 2
          * (Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
      hA1.mono_set (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))
    have h1 : MeasureTheory.IntegrableOn
        (fun x => (Work.Spaces.mixed b a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
      hA.mono_set (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))
    have hmain := tmp_radial_noDecay_le hd h1 h2 z hz
    have hconv1 : (∫ x in Set.Ioi (0 : ℝ), (Work.Spaces.mixed b a f x σ) ^ 2
          * (Work.Spaces.w x) ^ 2)
        = (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2) :=
      integral_Ioi_eq_integral_Iz _
    have hconv2 : (∫ x in Set.Ioi (0 : ℝ),
          (x * Work.Spaces.pz (Work.Spaces.mixed b a f) x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
        = (∫ x in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2) := by
      rw [integral_Ioi_eq_integral_Iz]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only []
      rw [show x * Work.Spaces.pz (Work.Spaces.mixed b a f) x σ
          = Work.Spaces.mixed (b + 1) a f x σ from rfl]
    rw [hconv1, hconv2] at hmain
    exact hmain
  have hstep2 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2)
      ≤ 20 * (min z 1) ^ 2 *
        ((∫ σ in Work.Spaces.Iθ, ∫ x in Work.Spaces.Iz,
            (Work.Spaces.mixed b a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
          + (∫ σ in Work.Spaces.Iθ, ∫ x in Work.Spaces.Iz,
              (Work.Spaces.mixed (b + 1) a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)) := by
    have hGA : MeasureTheory.Integrable (fun σ => 20 * (min z 1) ^ 2 *
        ((∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
          + (∫ x in Work.Spaces.Iz,
              (Work.Spaces.mixed (b + 1) a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hAint.add hA1int).const_mul _
    have hmono := MeasureTheory.integral_mono_ae hint1 hGA hL2u
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hAint hA1int] at hmono
    exact hmono
  have hA_final : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2)
      ≤ 40 * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f := by
    calc (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2)
        ≤ 20 * (min z 1) ^ 2 *
            ((∫ σ in Work.Spaces.Iθ, ∫ x in Work.Spaces.Iz,
                (Work.Spaces.mixed b a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
              + (∫ σ in Work.Spaces.Iθ, ∫ x in Work.Spaces.Iz,
                  (Work.Spaces.mixed (b + 1) a f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)) := hstep2
      _ ≤ 20 * (min z 1) ^ 2 * (2 * Work.Spaces.HkSq α 4 f) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hAbd, hA1bd]
      _ = 40 * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f := by ring
  -- Step III: the radial bound for the second θ-integral, integrated against `sin^{-γ}`
  have hL2u2 : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 ≤ 20 * (min z 1) ^ 2 *
        ((∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
          + (∫ x in Work.Spaces.Iz,
              (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2)) := by
    filter_upwards [hBae, hB1ae, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hB hB1 hσ
    have hd : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun x' => Work.Spaces.mixed b (a + 1) f x' σ)
          (Work.Spaces.pz (Work.Spaces.mixed b (a + 1) f) x σ) x := by
      intro x hx
      exact ((Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hσ
        (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b (a + 1) 1 (by omega))).differentiableOn
          (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hx) |>.hasDerivAt
    have h2 : MeasureTheory.IntegrableOn
        (fun x => (x * Work.Spaces.pz (Work.Spaces.mixed b (a + 1) f) x σ) ^ 2
          * (Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
      hB1.mono_set (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))
    have h1 : MeasureTheory.IntegrableOn
        (fun x => (Work.Spaces.mixed b (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
      hB.mono_set (fun x hx => Set.mem_Ici.mpr (le_of_lt hx))
    have hmain := tmp_radial_noDecay_le hd h1 h2 z hz
    have hconv1 : (∫ x in Set.Ioi (0 : ℝ), (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
          * (Work.Spaces.w x) ^ 2)
        = (∫ x in Work.Spaces.Iz,
            (Work.Spaces.mixed b (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2) :=
      integral_Ioi_eq_integral_Iz _
    have hconv2 : (∫ x in Set.Ioi (0 : ℝ),
          (x * Work.Spaces.pz (Work.Spaces.mixed b (a + 1) f) x σ) ^ 2 * (Work.Spaces.w x) ^ 2)
        = (∫ x in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2) := by
      rw [integral_Ioi_eq_integral_Iz]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only []
      rw [show x * Work.Spaces.pz (Work.Spaces.mixed b (a + 1) f) x σ
          = Work.Spaces.mixed (b + 1) (a + 1) f x σ from rfl]
    rw [hconv1, hconv2] at hmain
    exact hmain
  -- the `σ`-integrability of the weighted right hand side
  have hIdB : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
            * (Work.Spaces.w x) ^ 2))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ => ∫ x in Work.Spaces.Iz,
        (Work.Spaces.mixed b (a + 1) f x σ * Work.Spaces.Wt α x σ) ^ 2) := by
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (Wt_sq α (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)).symm
  have hIdB1 : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2
            * (Work.Spaces.w x) ^ 2))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ => ∫ x in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f x σ * Work.Spaces.Wt α x σ) ^ 2) := by
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (Wt_sq α (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)).symm
  have hBwt_int : MeasureTheory.Integrable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
            * (Work.Spaces.w x) ^ 2)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hCint.congr hIdB.symm
  have hB1wt_int : MeasureTheory.Integrable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2
            * (Work.Spaces.w x) ^ 2)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hC1int.congr hIdB1.symm
  have hstep3 : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
      ≤ 20 * (min z 1) ^ 2 *
        ((∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
                * (Work.Spaces.w x) ^ 2))
          + (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2
                  * (Work.Spaces.w x) ^ 2))) := by
    have hGR : MeasureTheory.Integrable (fun σ => (20 * (min z 1) ^ 2)
        * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
                * (Work.Spaces.w x) ^ 2)
          + (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2
                * (Work.Spaces.w x) ^ 2)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hBwt_int.add hB1wt_int).const_mul _
    have hae : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ => (20 * (min z 1) ^ 2)
          * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
                  * (Work.Spaces.w x) ^ 2)
            + (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2
                  * (Work.Spaces.w x) ^ 2))) := by
      filter_upwards [hL2u2, Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ hσ'
      calc (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
          ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (20 * (min z 1) ^ 2 *
                ((∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
                    * (Work.Spaces.w x) ^ 2)
                  + (∫ x in Work.Spaces.Iz,
                      (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2 * (Work.Spaces.w x) ^ 2))) :=
            mul_le_mul_of_nonneg_left hσ (Real.rpow_nonneg
              (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ')) _)
        _ = (20 * (min z 1) ^ 2)
              * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                  * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
                      * (Work.Spaces.w x) ^ 2)
                + (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                  * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2
                      * (Work.Spaces.w x) ^ 2)) := by
            ring
    have hmono := MeasureTheory.integral_mono_ae hint2' hGR hae
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hBwt_int hB1wt_int] at hmono
    exact hmono
  have hB_final : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
      ≤ 40 * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f := by
    have h1 : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
              * (Work.Spaces.w x) ^ 2)) ≤ Work.Spaces.HkSq α 4 f := by
      rw [MeasureTheory.integral_congr_ae hIdB]
      exact hCbd
    have h2 : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2
              * (Work.Spaces.w x) ^ 2)) ≤ Work.Spaces.HkSq α 4 f := by
      rw [MeasureTheory.integral_congr_ae hIdB1]
      exact hC1bd
    calc (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
        ≤ 20 * (min z 1) ^ 2 *
            ((∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed b (a + 1) f x σ) ^ 2
                    * (Work.Spaces.w x) ^ 2))
              + (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                  * (∫ x in Work.Spaces.Iz, (Work.Spaces.mixed (b + 1) (a + 1) f x σ) ^ 2
                      * (Work.Spaces.w x) ^ 2))) := hstep3
      _ ≤ 20 * (min z 1) ^ 2 * (2 * Work.Spaces.HkSq α 4 f) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [h1, h2]
      _ = 40 * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f := by ring
  -- combination
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hK : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
      ≤ 100 / (Work.Spaces.gam α - 1) := by
    have h := (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) (by linarith) (by linarith)).2
    rwa [show (Work.Spaces.gam α - 2) + 1 = Work.Spaces.gam α - 1 by ring] at h
  have hBnn : 0 ≤ (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
      (sq_nonneg _)
  have h1 : (4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z σ) ^ 2)
      ≤ (4 / Real.pi) * (40 * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f) :=
    mul_le_mul_of_nonneg_left hA_final (by positivity)
  have h2 : 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
        * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
      ≤ 2 * (100 / (Work.Spaces.gam α - 1))
        * (40 * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f) := by
    have hh : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2))
          * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2)
        ≤ (100 / (Work.Spaces.gam α - 1)) * (40 * (min z 1) ^ 2 * Work.Spaces.HkSq α 4 f) :=
      mul_le_mul hK hB_final hBnn (by positivity)
    linarith [hh]
  linarith [hang, h1, h2]

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The trace-free weighted `ℋ⁴ → L^∞` trade-off

For `0 < α ≤ 1` there is `C = C(α)` such that every `C⁴` function `f` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` which is honestly in `ℋ⁴` satisfies, for every `a + b ≤ 2`,

  `|D_z^b D_θ^a f (z,θ)| ≤ C · min z 1 · |f|_{ℋ⁴}`     (`z > 0`, `0 < θ < π/2`).

Unlike `Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved` this needs **no**
`BdryTraces` hypothesis: the boundary terms of the angular Hardy and of the radial Agmon
inequality are replaced by

* the weighted angular sup bound `v2_theta_sup_uniform` (a companion angle minimising the
  `θ`-slice on `[π/8,3π/8]` plus Cauchy–Schwarz), and
* the trace-free radial Agmon inequality `v2_agmonZ_noDecay` (whose decay at `∞` is automatic
  from the integrability, via `liminf`).

The constant depends on `α` only; the consumer allows that.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `z^{3/2}/(1+z)² ≤ min z 1` for `z > 0`. -/
theorem v2_zpow_div_le_min {z : ℝ} (hz : 0 < z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ min z 1 := by
  have hpos : (0 : ℝ) < 1 + z := by linarith
  rcases le_or_gt z 1 with h | h
  · rw [min_eq_left h]
    have hrw : z ^ ((3 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * z := by
      rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hz, Real.rpow_one]
    have hroot : z ^ ((1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hz.le h (by norm_num)
    have hsq : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg (1 + z), hz]
    have h4 : z ^ ((1 : ℝ) / 2) * z ≤ 1 * z := mul_le_mul_of_nonneg_right hroot hz.le
    have h5 : (1 : ℝ) * z ≤ z * (1 + z) ^ 2 := by nlinarith [hsq, hz]
    rw [div_le_iff₀ (by positivity)]
    linarith [hrw, h4, h5]
  · rw [min_eq_right h.le]
    have hroot : (1 : ℝ) ≤ z ^ ((1 : ℝ) / 2) := Real.one_le_rpow h.le (by norm_num)
    have hzr : z ^ ((1 : ℝ) / 2) ≤ z := by
      calc z ^ ((1 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * 1 := (mul_one _).symm
        _ ≤ z ^ ((1 : ℝ) / 2) * z ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hz.le ((1 : ℝ) / 2))
        _ = z := by
            rw [← Real.rpow_add hz, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
    have hrw : z ^ ((3 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * z := by
      rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hz, Real.rpow_one]
    have hz2 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [hz]
    rw [div_le_one (by positivity)]
    rw [hrw]
    nlinarith [hzr, hz.le, Real.rpow_nonneg hz.le ((1 : ℝ) / 2), hz2,
      mul_le_mul_of_nonneg_right hzr hz.le]

/-- `w(z)² · z = (1+z)⁴/z³` for `z ≠ 0`. -/
theorem v2_wsq_mul_eq {z : ℝ} (hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 * z = (1 + z) ^ 4 / z ^ 3 := by
  rw [Work.Spaces.w, div_pow]
  field_simp

/-- `w` is continuous on `(0,∞)`. -/
theorem v2_continuousOn_w : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
  have h : (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) = Work.Spaces.w := by
    funext y; rw [Work.Spaces.w]
  rw [← h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 (ne_of_gt hy))

/-- The trace-free weighted `ℋ⁴ → L^∞` trade-off. -/
theorem v2_hkMem_pointwise_min {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨K, hK0, hsup⟩ := Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform hα hα1
  refine ⟨Real.sqrt (5 * K), Real.sqrt_nonneg _, ?_⟩
  intro f h4 hmem b a hab z θ hz hθ0 hθ1
  have h5K : (0 : ℝ) ≤ 5 * K := by linarith
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the radial function whose `Iz`-integral is `HkSq`
  have hHint : MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) Work.Spaces.Iz :=
    hmem.2
  have hHnonneg : ∀ x : ℝ, 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ :=
    fun x => MeasureTheory.integral_nonneg (fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f x σ)
  have hHsq : (∫ x in Work.Spaces.Iz,
        ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ)
      = Work.Spaces.HkSq α 4 f := rfl
  -- the two pointwise bounds from the angular sup lemma
  have hb1 : ∀ x : ℝ, 0 < x →
      (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2
        ≤ (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K := by
    intro x hx
    have h := hsup f h4 hmem b a (by omega) x hx θ hθ0 hθ1
    rwa [mul_comm K] at h
  have hb2 : ∀ x : ℝ, 0 < x →
      (Work.Spaces.mixed (b + 1) a f x θ * Work.Spaces.w x) ^ 2
        ≤ (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K := by
    intro x hx
    have h := hsup f h4 hmem (b + 1) a (by omega) x hx θ hθ0 hθ1
    rwa [mul_comm K] at h
  have hmul : ∀ x : ℝ, x ≠ 0 →
      x * (Work.Spaces.mixed (b + 1) a f x θ / x) = Work.Spaces.mixed (b + 1) a f x θ := by
    intro x hx
    field_simp
  -- continuity of the two slices
  have hcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.mixed b a f x θ) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
      (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b a 0 (by omega))).continuousOn
  have hcont2 : ContinuousOn (fun x : ℝ => Work.Spaces.mixed (b + 1) a f x θ)
      (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
      (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 (b + 1) a 0 (by omega))).continuousOn
  -- integrability of the two `θ`-slices
  have hint1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.mul_const hHint K) ?_ ?_
    · rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
      exact ((hcont1.mul v2_continuousOn_w).pow 2).aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_
      intro x hx
      have hx' : (0 : ℝ) ≤ x := hx
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      rcases eq_or_lt_of_le hx' with h0 | hpos
      · subst h0
        have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
        rw [hw0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact mul_nonneg (hHnonneg 0) hK0
      · exact hb1 x hpos
  have hint2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.mul_const hHint K) ?_ ?_
    · rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
      refine (((continuousOn_id.mul ?_).mul v2_continuousOn_w).pow 2).aestronglyMeasurable
        measurableSet_Ioi
      exact ContinuousOn.div hcont2 continuousOn_id (fun x hx => ne_of_gt hx)
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_
      intro x hx
      have hx' : (0 : ℝ) ≤ x := hx
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      rcases eq_or_lt_of_le hx' with h0 | hpos
      · subst h0
        have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
        rw [hw0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact mul_nonneg (hHnonneg 0) hK0
      · have hxne : x ≠ 0 := ne_of_gt hpos
        rw [hmul x hxne]
        exact hb2 x hpos
  -- the derivative identity for the Agmon inequality
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s : ℝ => Work.Spaces.mixed b a f s θ)
        (Work.Spaces.mixed (b + 1) a f x θ / x) x := by
    intro x hx
    have hz1 : 0 < x := hx
    have hcd : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.mixed b a f s θ) (Set.Ioi 0) :=
      Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
        (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b a 1 (by omega))
    have hdiff : DifferentiableAt ℝ (fun s : ℝ => Work.Spaces.mixed b a f s θ) x :=
      (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz1)
    have hder : deriv (fun s : ℝ => Work.Spaces.mixed b a f s θ) x
        = Work.Spaces.mixed (b + 1) a f x θ / x := by
      have h1 : Work.Spaces.mixed (b + 1) a f x θ
          = x * deriv (fun s : ℝ => Work.Spaces.mixed b a f s θ) x := rfl
      rw [h1, mul_div_cancel_left₀ _ (ne_of_gt hz1)]
    have h := hdiff.hasDerivAt
    rw [hder] at h
    exact h
  -- the trace-free Agmon inequality
  have hag := Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay (v := fun s : ℝ => Work.Spaces.mixed b a f s θ)
    (v' := fun s : ℝ => Work.Spaces.mixed (b + 1) a f s θ / s) hz hderiv hint1 hint2
  -- the two tails, bounded by `K ∫ H = K HkSq`
  have ht1 : (∫ x in Set.Ioi z, (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2)
      ≤ K * Work.Spaces.HkSq α 4 f := by
    have hzsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
    have hInt1 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2) (Set.Ioi z) :=
      hint1.mono_set hzsub
    have hHsub : MeasureTheory.IntegrableOn
        (fun x : ℝ => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) (Set.Ioi z) :=
      MeasureTheory.Integrable.mono_measure hHint
        (MeasureTheory.Measure.restrict_mono hzsub le_rfl)
    have hInt2 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K)
        (Set.Ioi z) := MeasureTheory.Integrable.mul_const hHsub K
    have hmono := MeasureTheory.integral_mono_ae hInt1 hInt2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun x hx => hb1 x (lt_trans hz hx)))
    have hKint : (∫ x in Set.Ioi z,
          (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K)
        = K * (∫ x in Set.Ioi z,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) := by
      rw [MeasureTheory.integral_mul_const]
      ring
    have hle : (∫ x in Set.Ioi z,
          ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ)
        ≤ ∫ x in Work.Spaces.Iz,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ :=
      MeasureTheory.setIntegral_mono_set hHint
        (Filter.Eventually.of_forall hHnonneg)
        (Filter.Eventually.of_forall (fun x hx => hzsub hx))
    calc (∫ x in Set.Ioi z, (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2)
        ≤ ∫ x in Set.Ioi z,
            (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K := hmono
      _ = K * (∫ x in Set.Ioi z,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) := hKint
      _ ≤ K * (∫ x in Work.Spaces.Iz,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) :=
          mul_le_mul_of_nonneg_left hle hK0
      _ = K * Work.Spaces.HkSq α 4 f := by rw [hHsq]
  have ht2 : (∫ x in Set.Ioi z,
        (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2)
      ≤ K * Work.Spaces.HkSq α 4 f := by
    have hzsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
    have hInt1 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2)
        (Set.Ioi z) := hint2.mono_set hzsub
    have hHsub : MeasureTheory.IntegrableOn
        (fun x : ℝ => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) (Set.Ioi z) :=
      MeasureTheory.Integrable.mono_measure hHint
        (MeasureTheory.Measure.restrict_mono hzsub le_rfl)
    have hInt2 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K)
        (Set.Ioi z) := MeasureTheory.Integrable.mul_const hHsub K
    have hmono := MeasureTheory.integral_mono_ae hInt1 hInt2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => by
        show (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2
          ≤ (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K
        rw [hmul x (ne_of_gt (lt_trans hz hx))]
        exact hb2 x (lt_trans hz hx)))
    have hKint : (∫ x in Set.Ioi z,
          (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K)
        = K * (∫ x in Set.Ioi z,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) := by
      rw [MeasureTheory.integral_mul_const]
      ring
    have hle : (∫ x in Set.Ioi z,
          ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ)
        ≤ ∫ x in Work.Spaces.Iz,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ :=
      MeasureTheory.setIntegral_mono_set hHint
        (Filter.Eventually.of_forall hHnonneg)
        (Filter.Eventually.of_forall (fun x hx => hzsub hx))
    calc (∫ x in Set.Ioi z,
          (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2)
        ≤ ∫ x in Set.Ioi z,
            (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K := hmono
      _ = K * (∫ x in Set.Ioi z,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) := hKint
      _ ≤ K * (∫ x in Work.Spaces.Iz,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) :=
          mul_le_mul_of_nonneg_left hle hK0
      _ = K * Work.Spaces.HkSq α 4 f := by rw [hHsq]
  -- the Agmon conclusion
  have hbound : (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
    have h4t : 4 * (∫ x in Set.Ioi z, (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2)
        ≤ 4 * (K * Work.Spaces.HkSq α 4 f) :=
      mul_le_mul_of_nonneg_left ht1 (by norm_num)
    linarith [hag, h4t, ht2]
  -- convert to the pointwise bound
  have hstep : (Work.Spaces.mixed b a f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * z)
      ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
    rw [← mul_assoc]
    exact hbound
  rw [v2_wsq_mul_eq (ne_of_gt hz)] at hstep
  have hstep2 : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ 5 * K * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4) := by
    have h2 := mul_le_mul_of_nonneg_right hstep
      (le_of_lt (div_pos (pow_pos hz 3) (pow_pos (by linarith : (0 : ℝ) < 1 + z) 4)))
    have hone : ((1 + z) ^ 4 / z ^ 3) * (z ^ 3 / (1 + z) ^ 4) = 1 := by
      rw [div_mul_div_comm, mul_comm (z ^ 3) ((1 + z) ^ 4)]
      exact div_self (by positivity)
    have heq : (Work.Spaces.mixed b a f z θ) ^ 2 * ((1 + z) ^ 4 / z ^ 3)
          * (z ^ 3 / (1 + z) ^ 4) = (Work.Spaces.mixed b a f z θ) ^ 2 := by
      rw [mul_assoc, hone, mul_one]
    rwa [heq] at h2
  have hA2 : (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) ^ 2 = z ^ 3 / (1 + z) ^ 4 := by
    rw [div_pow]
    congr 1
    · rw [← Real.rpow_natCast (z ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hz.le]
      norm_num
    · ring
  have hAnonneg : (0 : ℝ) ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  have hHknn : (0 : ℝ) ≤ Work.Spaces.HkSq α 4 f :=
    MeasureTheory.integral_nonneg hHnonneg
  have hNormsq : (Work.Spaces.HkNorm α 4 f) ^ 2 = Work.Spaces.HkSq α 4 f :=
    Real.sq_sqrt hHknn
  have hR : (Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
        * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) ^ 2
      = 5 * K * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt h5K, hNormsq, hA2]
  have hsq : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
          * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) ^ 2 := by
    rw [hR]
    exact hstep2
  have hprodnonneg : (0 : ℝ) ≤ Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
      * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Work.Spaces.HkNorm_nonneg α 4 f)) hAnonneg
  have hfinal : |Work.Spaces.mixed b a f z θ|
      ≤ Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
        * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq hprodnonneg] at h
    exact h
  have hmono : Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
        * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
      ≤ Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f * min z 1 :=
    mul_le_mul_of_nonneg_left (v2_zpow_div_le_min hz)
      (mul_nonneg (Real.sqrt_nonneg _) (Work.Spaces.HkNorm_nonneg α 4 f))
  have hcomm : Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f * min z 1
      = Real.sqrt (5 * K) * min z 1 * Work.Spaces.HkNorm α 4 f := by ring
  rw [hcomm] at hmono
  linarith [hfinal, hmono]

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.angular_L2_noTrace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `THL.angular_L2_noTrace` — the trace-free angular `L²` bound at fixed `z`

`angular_L2_noTrace`: for `0 < β ≤ 1` and a `C⁴` datum `f` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` which is honestly in `ℋ⁴` (**no** boundary-trace hypothesis),

  `∫_{Iθ} sin(2σ)^{-γ} (D_θ f(z,σ))² dσ ≤ 5 · z³/(1+z)⁴ · |f|²_{ℋ⁴}`,  `γ = gam β`,

together with integrability of the angular integrand.

This is leaf A2 of `THL.Leaves` ("copy `RXA1w.mixed_slice_pointwise_le` with
`RXA1w.agmonZ_weight` replaced by `RXT.Slots.v2_agmonZ_noDecay`").  The two steps are:

* **the a.e. slice bound** (`THL.mixed_slice_pointwise_le_noTrace`, the trace-free sibling of
  `RXA1w.mixed_slice_pointwise_le`): for almost every angle, the weighted `θ`-derivative at
  the slot `(b,a) = (0,0)` is dominated by `5 z³/(1+z)⁴ · ∫_s HkIntegrand β 4 f (s,σ)`.  The
  radial Agmon inequality is applied there without any decay hypothesis, and both of its
  energy slots are mixed slots of the nonnegative `ℋ⁴`-integrand;

* **integration in `σ`** (`C4.HkSqSwap_C4`, Tonelli for that nonnegative integrand): the
  `σ`-integral of `∫_s HkIntegrand β 4 f (s,σ)` is exactly `HkSq β 4 f` and is integrable as a
  function of `σ`, so `integral_mono_of_nonneg` applies.

The first conjunct (integrability of `sin(2σ)^{-γ} (D_θf(z,σ))²` on `Iθ`) is
`RXA1.integrableOn_pth_mixed_sq_sin_C4` at `(b,a) = (0,0)` — where the plain `θ`-derivative
carries the weight `sin(2σ)^{2-γ} = sin(2σ)² · sin(2σ)^{-γ}` — transported along the a.e.
identity `D_θ f = sin(2σ) ∂_θ f`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.THL

theorem angular_L2_noTrace {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun σ => Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed 0 1 f z σ) ^ 2) Work.Spaces.Iθ ∧
      ∫ σ in Work.Spaces.Iθ, Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed 0 1 f z σ) ^ 2
        ≤ 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by
  -- ## The first conjunct: integrability of the weighted angular slice at the slot `(0,1)`.
  have hint : MeasureTheory.IntegrableOn (fun σ => Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
      * (Work.Spaces.mixed 0 1 f z σ) ^ 2) Work.Spaces.Iθ := by
    refine (Work.FTS_RegExport.RXA1.integrableOn_pth_mixed_sq_sin_C4 hβ hβ1 h4 hmem 0 0
      (by omega) hz).congr ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    have hs : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hD : Work.Spaces.mixed 0 1 f z σ = Real.sin (2 * σ) * Work.Spaces.pth f z σ := rfl
    have hsplit : Real.sin (2 * σ) ^ (2 - Work.Spaces.gam β)
        = Real.sin (2 * σ) ^ (2 : ℝ) * Real.sin (2 * σ) ^ (-(Work.Spaces.gam β)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam β = 2 + (-(Work.Spaces.gam β)) by ring,
        Real.rpow_add hs]
    rw [hD, mul_pow, hsplit]
    simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero, Real.rpow_two]
    ring
  -- ## The second conjunct: integrate the a.e. slice bound over the angle.
  obtain ⟨hswap, hTint, -⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 h4 hmem
  have hslice := mixed_slice_pointwise_le_noTrace hβ h4 hmem 0 0 (by omega) hz
  have hrhs : MeasureTheory.Integrable (fun σ => 5 * (z ^ 3 / (1 + z) ^ 4)
      * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hTint.const_mul _
  have hmono := integral_mono_of_nonneg
    (ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
      mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσ) _) (sq_nonneg _))
    hrhs hslice
  have hIntegral : (∫ σ in Work.Spaces.Iθ, Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed 0 1 f z σ) ^ 2)
      ≤ 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by
    calc (∫ σ in Work.Spaces.Iθ, Real.sin (2 * σ) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed 0 1 f z σ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand β 4 f s σ) := hmono
      _ = 5 * (z ^ 3 / (1 + z) ^ 4)
            * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
                Work.Spaces.HkIntegrand β 4 f s σ) := by
          rw [MeasureTheory.integral_const_mul]
      _ = 5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f := by rw [hswap]
  exact ⟨hint, hIntegral⟩

end Work.FTS_RegExport.THL
end
end
