import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllSol.VopAux.SliceDDefs
import Submission.Work.FTS.EllSol.VopAux.SliceDPointwise
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.H2W.sliceEtaPoincare
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.EllipticEst.Lop_iter_sin_sq_bound
import Submission.Work.FTS.EllipticEst.Lop_iter_cos_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The integration step

The pointwise bound of `Submission/Work/FTS/EllSol/VopAux/SliceDPointwise.lean`
(`(L^i u θ)²·thGam α θ ≤ Cd·sliceD K α u θ` at interior angles, for `1 ≤ i ≤ K`) is integrated
against the measure `volume.restrict Iθ` below.  The ingredients are
`Work.FTS.EllipticEst.H2W.sliceEtaPoincare` (integrability of `u²thEta` and `(u')²thEta`, and
their bounds by `∫(u'')²thEta`), the linearity of the integral over `Iθ` (to split `sliceF` and
`∫ sliceD`), and `integral_mono_ae` / `Integrable.mono'` for the transfer of the pointwise
bounds. -/

/-- The open interval `(0, π/2)` and `Iθ = [0, π/2]` carry the same restricted measure. -/
theorem sfIθ_ae :
    volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

theorem sfIθ_continuousOn_thEta :
    ContinuousOn thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sfIθ_continuousOn_thGam (α : ℝ) :
    ContinuousOn (thGam α) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- **The integration step.**  Given the pointwise bound of `SliceDPointwise` as a hypothesis,
the integrated single-slice estimate of `sliceF_le_sliceV` follows. -/
theorem sliceF_le_sliceV_of_pointwise (K : ℕ)
    (hPt : ∃ Cd : ℝ, 0 < Cd ∧ ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      ∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (LopIter i u θ) ^ 2 * thGam α θ ≤ Cd * sliceD K α u θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ),
    0 < α → α ≤ 1 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        Work.Spaces.Iθ) ∧
      Work.FTS.EllSol.VopAux.sliceF K α u
        ≤ C * Work.FTS.EllSol.VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := hPt
  obtain ⟨C0, hC0pos, hC0⟩ := Work.FTS.EllipticEst.H2W.sliceEtaPoincare
  refine ⟨max 1 (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))), lt_max_of_lt_left one_pos, ?_⟩
  intro α u hα0 hα1 hu hlim0 hlim1 hintV hintVm
  -- Poincaré input for the slice `u` and its first derivative
  have hpo := hC0 u hu hlim0 hlim1 hintV
  have hpoU : IntegrableOn (fun θ => (u θ) ^ 2 * thEta θ) Work.Spaces.Iθ := hpo.1
  have hpoD : IntegrableOn (fun θ => (deriv u θ) ^ 2 * thEta θ) Work.Spaces.Iθ := hpo.2.1
  have hpoUle : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      ≤ C0 * ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ := hpo.2.2.1
  have hpoDle : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * thEta θ)
      ≤ C0 * ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ := hpo.2.2.2
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIVnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ :=
    MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))
  -- the integrability of the `m`-sum of the datum
  have hsumV_int : IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 K,
      (LopIter m (sliceV u) θ) ^ 2 * thGam α θ) Work.Spaces.Iθ :=
    MeasureTheory.integrable_finsetSum (Finset.Icc 1 K) (fun m hm => hintVm m hm)
  -- integrality of the dominating function
  have hDint : IntegrableOn (fun θ => sliceD K α u θ) Work.Spaces.Iθ := by
    have hmain : IntegrableOn (fun θ => (u θ) ^ 2 * thEta θ
        + ((deriv u θ) ^ 2 * thEta θ
          + ((sliceV u θ) ^ 2 * thEta θ
            + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)))
        Work.Spaces.Iθ := hpoU.add (hpoD.add (hintV.add hsumV_int))
    refine hmain.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [sliceD]
    ring
  -- the pointwise bound, upgraded to integrability of the left-hand integrands
  have hcontu : ∀ i : ℕ, ContinuousOn (LopIter i u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun i => (sd_LopIter_contDiffOn (sd_contDiffOn_smoothOrder hu) i).continuousOn
  have hLi_int : ∀ i ∈ Finset.Icc 1 K,
      IntegrableOn (fun θ => (LopIter i u θ) ^ 2 * thGam α θ) Work.Spaces.Iθ := by
    intro i hi
    refine Integrable.mono' (g := fun θ => Cd * sliceD K α u θ) (hDint.const_mul Cd) ?_ ?_
    · rw [← sfIθ_ae]
      exact (((hcontu i).pow 2).mul (sfIθ_continuousOn_thGam α)).aestronglyMeasurable
        measurableSet_Ioo
    · rw [← sfIθ_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (thGam_nonneg hθI))]
      exact hCd α u hα0 hα1 hu i hi θ hθ
  -- the integral bounds for the individual `L^i u`
  have hLi_le : ∀ i ∈ Finset.Icc 1 K,
      (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ Cd * ∫ θ in Work.Spaces.Iθ, sliceD K α u θ := by
    intro i hi
    have hae : (fun θ => (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Cd * sliceD K α u θ) := by
      rw [← sfIθ_ae]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hCd α u hα0 hα1 hu i hi θ hθ
    have h := MeasureTheory.integral_mono_ae (hLi_int i hi) (hDint.const_mul Cd) hae
    rwa [MeasureTheory.integral_const_mul] at h
  -- the two decompositions of `sliceF`
  have hsumU_int : IntegrableOn (fun θ => ∑ i ∈ Finset.Icc 1 K,
      (LopIter i u θ) ^ 2 * thGam α θ) Work.Spaces.Iθ :=
    MeasureTheory.integrable_finsetSum (Finset.Icc 1 K) (fun i hi => hLi_int i hi)
  have hsliceF_u : sliceF K α u = (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      + ∑ i ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ := by
    have hw : sliceW K α u = fun θ => (u θ) ^ 2 * thEta θ
        + ∑ i ∈ Finset.Icc 1 K, (LopIter i u θ) ^ 2 * thGam α θ := by
      funext θ
      simp only [sliceW]
    have h1 : sliceF K α u = ∫ θ in Work.Spaces.Iθ, ((u θ) ^ 2 * thEta θ
        + ∑ i ∈ Finset.Icc 1 K, (LopIter i u θ) ^ 2 * thGam α θ) := by
      rw [sliceF, hw]
    rw [h1, MeasureTheory.integral_add hpoU hsumU_int,
      MeasureTheory.integral_finsetSum (Finset.Icc 1 K) (fun i hi => hLi_int i hi)]
  have hsliceF_v : sliceF K α (sliceV u)
      = (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
      + ∑ m ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
    have hw : sliceW K α (sliceV u) = fun θ => (sliceV u θ) ^ 2 * thEta θ
        + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
      funext θ
      simp only [sliceW]
    have h1 : sliceF K α (sliceV u) = ∫ θ in Work.Spaces.Iθ, ((sliceV u θ) ^ 2 * thEta θ
        + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ) := by
      rw [sliceF, hw]
    rw [h1, MeasureTheory.integral_add hintV hsumV_int,
      MeasureTheory.integral_finsetSum (Finset.Icc 1 K) (fun m hm => hintVm m hm)]
  -- the value of `∫ sliceD`
  have hDval : (∫ θ in Work.Spaces.Iθ, sliceD K α u θ)
      = (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
        + ∑ m ∈ Finset.Icc 1 K,
            ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
    have hAB : IntegrableOn (fun θ => (u θ) ^ 2 * thEta θ + (deriv u θ) ^ 2 * thEta θ)
        Work.Spaces.Iθ := hpoU.add hpoD
    have hABC : IntegrableOn (fun θ => (u θ) ^ 2 * thEta θ + (deriv u θ) ^ 2 * thEta θ
        + (sliceV u θ) ^ 2 * thEta θ) Work.Spaces.Iθ := hAB.add hintV
    have hcongr : sliceD K α u = fun θ => ((u θ) ^ 2 * thEta θ
        + (deriv u θ) ^ 2 * thEta θ + (sliceV u θ) ^ 2 * thEta θ)
        + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
      funext θ
      simp only [sliceD]
    rw [hcongr, MeasureTheory.integral_add hABC hsumV_int,
      MeasureTheory.integral_add hAB hintV, MeasureTheory.integral_add hpoU hpoD,
      MeasureTheory.integral_finsetSum (Finset.Icc 1 K) (fun m hm => hintVm m hm)]
  -- the nonnegativity of the summed data of `sliceF K α (sliceV u)`
  have hsumV_nn : 0 ≤ ∑ m ∈ Finset.Icc 1 K,
      ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg fun m _ => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ))
  have hIV_le : (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
      ≤ sliceF K α (sliceV u) := by
    rw [hsliceF_v]
    linarith
  -- `∫ sliceD ≤ (2 C0 + 1)·sliceF K α (sliceV u)`
  have hIntD_le : (∫ θ in Work.Spaces.Iθ, sliceD K α u θ)
      ≤ (2 * C0 + 1) * sliceF K α (sliceV u) := by
    rw [hDval, hsliceF_v]
    have hc : (1 : ℝ) ≤ 2 * C0 + 1 := by linarith
    have hA : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * thEta θ)
        + (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
        ≤ (2 * C0 + 1) * ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ := by
      nlinarith [hpoUle, hpoDle, hIVnn]
    have hB : (∑ m ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
        ≤ (2 * C0 + 1) * ∑ m ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
      nlinarith [hsumV_nn, hc]
    have hdist : (2 * C0 + 1) * ((∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
        + ∑ m ∈ Finset.Icc 1 K,
            ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
        = (2 * C0 + 1) * (∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ)
          + (2 * C0 + 1) * ∑ m ∈ Finset.Icc 1 K,
              ∫ θ in Work.Spaces.Iθ, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ := by
      ring
    linarith [hA, hB, hdist]
  -- the bound for each `∫ (L^i u)² thGam`
  have hLi_bound : ∀ i ∈ Finset.Icc 1 K,
      (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ Cd * (2 * C0 + 1) * sliceF K α (sliceV u) := by
    intro i hi
    calc (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ Cd * ∫ θ in Work.Spaces.Iθ, sliceD K α u θ := hLi_le i hi
      _ ≤ Cd * ((2 * C0 + 1) * sliceF K α (sliceV u)) :=
          mul_le_mul_of_nonneg_left hIntD_le (le_of_lt hCdpos)
      _ = Cd * (2 * C0 + 1) * sliceF K α (sliceV u) := by ring
  -- the sum of the bounds
  have hsum_bound : (∑ i ∈ Finset.Icc 1 K,
        ∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
      ≤ ((K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := by
    calc (∑ i ∈ Finset.Icc 1 K,
          ∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
        ≤ ∑ _i ∈ Finset.Icc 1 K, (Cd * (2 * C0 + 1) * sliceF K α (sliceV u)) :=
          Finset.sum_le_sum (fun i hi => hLi_bound i hi)
      _ = (K : ℝ) * (Cd * (2 * C0 + 1) * sliceF K α (sliceV u)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          norm_num
      _ = ((K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := by ring
  -- the first-order term of `u`
  have hIU_le : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      ≤ C0 * sliceF K α (sliceV u) := by
    calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
        ≤ C0 * ∫ θ in Work.Spaces.Iθ, (sliceV u θ) ^ 2 * thEta θ := hpoUle
      _ ≤ C0 * sliceF K α (sliceV u) :=
          mul_le_mul_of_nonneg_left hIV_le (le_of_lt hC0pos)
  refine ⟨hpoU, hLi_int, ?_⟩
  rw [hsliceF_u]
  have hSV : 0 ≤ sliceF K α (sliceV u) := sliceF_nonneg _ _ _
  have hmain : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      + ∑ i ∈ Finset.Icc 1 K, (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
      ≤ (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := by
    have hdist : (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u)
        = C0 * sliceF K α (sliceV u)
          + ((K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := by ring
    linarith [hIU_le, hsum_bound, hdist]
  calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ)
      + ∑ i ∈ Finset.Icc 1 K, (∫ θ in Work.Spaces.Iθ, (LopIter i u θ) ^ 2 * thGam α θ)
      ≤ (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) := hmain
    _ ≤ max 1 (C0 + (K : ℝ) * (Cd * (2 * C0 + 1))) * sliceF K α (sliceV u) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hSV

/-
# The one-dimensional `∂_θ²`-Poincaré estimate with boundary *traces*

`sliceF K α u = ∫_{Iθ} [(u)²sin(2θ)^{-η} + ∑_{1≤i≤K}(L^i u)²sin(2θ)^{-γ}]`, `L = D_θ = sin(2θ)∂_θ`
(defined in `Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean`; `Work.FTS.EllipticEst.sliceV u = u'' = deriv(deriv u)`).
For a slice `u` which is `C^∞` on the OPEN interval `(0,π/2)` (NOT on a neighbourhood of
`[0,π/2]`), tends to `0` as `θ→0⁺` and as `θ→π/2⁻`, and has `(u'')²sin(2θ)^{-η}` and all
`(L^m u'')²sin(2θ)^{-γ}` (`1 ≤ m ≤ K`) integrable on `Iθ`:

  `sliceF K α u ≤ C_K · sliceF K α u''`,   with `C_K` uniform in `α ∈ (0,1]` and in `u`,

and all the terms of the left-hand `sliceF` are themselves integrable on `Iθ`.

The pointwise input is `Submission/Work/FTS/EllSol/VopAux/SliceDPointwise.lean`, and the
integration step is `sliceF_le_sliceV_of_pointwise` above.
-/
theorem sliceF_le_sliceV (K : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ),
    0 < α → α ≤ 1 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        Work.Spaces.Iθ) ∧
      Work.FTS.EllSol.VopAux.sliceF K α u
        ≤ C * Work.FTS.EllSol.VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
  exact sliceF_le_sliceV_of_pointwise K (SliceDPointwise K)

end Work.FTS.EllSol.VopAux
