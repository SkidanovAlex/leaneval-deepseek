import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.HkMinPrep
import Submission.Work.FTS_RegExport.RXT.HkMinSlices
import Submission.Work.FTS_RegExport.RXT.angular_meanVar_le
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.FTS.H2.LinfQ

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
