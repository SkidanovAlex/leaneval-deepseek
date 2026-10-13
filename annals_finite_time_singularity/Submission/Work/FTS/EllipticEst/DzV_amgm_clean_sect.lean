/-
Copyright: work module for the Elgindi finite-time singularity project.

# `DzV_amgm_clean` -- Agmon--Nirenberg interpolation for `D_z = z∂_z` in the weighted `H^k`-norm

The target lemma is `Work.Blocks.DzV_amgm_clean`: there is a universal `C > 0` such that for
every `0 < α ≤ 1/4`, every `f` smooth (`C^∞`) on the open quadrant whose `z`-slices lie in `ℋ^k`
and whose second radial derivative `z²∂_z²f` also lies in `ℋ^k`,

  `α · |D_z f| ≤ C (|f| + α² |z²∂_z²f|)`,   and `D_z f ∈ ℋ^k`,

the norms being the weighted `H^k`-norms of the paper.

## Structure of this file

Everything is proved here, in the fresh namespace `Work.Blocks.DzVamgm` (nothing is declared in
the shared `Work.FTS.EllipticEst.*` namespaces, so this file cannot clash with the work of
colleagues).

* **The one-dimensional analytic core** (`DzAgmon1D_clean`): the weighted Agmon--Nirenberg
  inequality `α² ∫⁻ ρ (zh')² ≤ C² (α⁴ ∫⁻ ρ (z²h'')² + ∫⁻ ρ h²)` for `ρ = (w z)²`, in
  unconditional `lintegral` form, for `C^∞` data `h` on `(0,∞)`.  It is assembled from three
  independent, separately proved inputs (see `Submission/Work/EllipticEst/NOTES_AgmonCutoff.md`):
  `Work.Blocks.DzV1_chi_second_deriv` (`|z²(logChi n)''| ≤ K/log(n+2)`),
  `Work.EllipticEst.agmon_cutoff_estimate_mine` (the `χ`-weighted cut-off estimate) and
  `Work.Blocks.DzV3_logChi_iSup` (monotone convergence along the cut-off family).
  The assembly (`logChiPos`, the trivial `⊤`-cases, the `ofReal`/Bochner bridges, the
  monotonicity in `n` and the final `⨆`) is the one written in
  `Submission/Work/EllipticEst/DzAgmonSmooth_mine.lean`.
* **The `θ`-integration** (`hgen_of_agmon`): `Work.FTS.EllipticEst.Blocks.TermAgmon` applies the
  one-dimensional inequality to every angular slice.
* **The term-by-term assembly** (`TZ_termwise`, `TM_termwise`, `LkSq_Dz_le`, `HkNorm_Dz_le_of`):
  applied to the summands `D_z^m f` and `D_z^mD_θ^i f` of the `ℋ^k`-integrand, using
  `z²∂_z²(D_z^jD_θ^if) = D_z^jD_θ^i(z²∂_z²f)`.
* **The honesty certificate** (`HkMem_Dz_slices`, `integrableOn_sliceIntegral_of_LkSq_lt_top`):
  the `θ`-slice of every summand of `HkIntegrand α k (D_z f)` is finite, via the Taylor
  identity `Work.FTS.EllipticEst.Blocks.SliceZDeriv_finite` (Taylor's formula with integral
  remainder plus Cauchy--Schwarz).
* **The final theorem** `DzV_amgm_clean` (the `α ≤ 1/4` instance of the `α ≤ 1` statement).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AgmonSlice.Blocks
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.EllipticEst.DzAmgm.Defs
import Submission.Work.FTS.EllipticEst.DzAmgmScratchSect
import Submission.Work.FTS.EllipticEst.Blocks.TermAgmon
import Submission.Work.FTS.EllipticEst.Blocks.SliceZDeriv_finite
import Submission.Work.FTS.EllipticEst.Blocks.DzAgmonDefs
import Submission.Work.FTS.EllipticEst.Blocks.AgmonIBP
import Submission.Work.FTS.EllipticEst.Blocks.AgmonDerivVanishing
import Submission.Work.FTS.EllipticEst.Blocks.AgmonArith
import Submission.Work.FTS.EllipticEst.Blocks.AgmonSmallness
import Submission.Work.FTS.EllipticEst.Blocks.logChiFamily
import Submission.Work.FTS.EllipticEst.TT.logCutDefs
import Submission.Work.Stability.Cutoff
import Submission.Work.EllipticEst.logChi_second_deriv_le
import Submission.Work.EllipticEst.agmon_cutoff_estimate
import Submission.Work.EllipticEst.logChi_iSup_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst
open Work.FTS.EllipticEst.Blocks
open Work.FTS.EllipticEst.DzAmgm
open Work.FTS.EllipticEst.DzAmgmSect

namespace Work.BlocksSect

namespace DzVamgm

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## The cut-off `logChi n`, extended by `0` on `(-∞,0]` -/

/-- `Work.FTS.EllipticEst.TT.logChi n`, extended by `0` on `(-∞,0]`.  This extension has
compact support in `(0,∞)`, which is the support hypothesis required by
`Work.FTS.EllipticEst.Blocks.AgmonIBP`; on `(0,∞)` it agrees with `logChi n`. -/
def logChiPos (n : ℕ) : ℝ → ℝ :=
  fun z => if 0 < z then Work.FTS.EllipticEst.TT.logChi n z else 0

theorem logChiPos_of_pos {n : ℕ} {z : ℝ} (hz : 0 < z) :
    logChiPos n z = Work.FTS.EllipticEst.TT.logChi n z := by
  simp only [logChiPos, if_pos hz]

theorem logChiPos_nonneg (n : ℕ) (z : ℝ) : 0 ≤ logChiPos n z := by
  by_cases hz : 0 < z
  · rw [logChiPos_of_pos hz]
    exact (Work.FTS.EllipticEst.TT.logChi_mem_Icc n z).1
  · simp only [logChiPos, if_neg hz, le_refl]

theorem logChiPos_le_one (n : ℕ) (z : ℝ) : logChiPos n z ≤ 1 := by
  by_cases hz : 0 < z
  · rw [logChiPos_of_pos hz]
    exact (Work.FTS.EllipticEst.TT.logChi_mem_Icc n z).2
  · simp only [logChiPos, if_neg hz]
    norm_num

theorem logChiPos_contDiffOn (n : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (logChiPos n) (Set.Ioi (0 : ℝ)) := by
  refine (contDiffOn_congr ?_).mpr (Work.FTS.EllipticEst.TT.logChi_contDiffOn n)
  intro z hz
  exact logChiPos_of_pos hz

/-- `logChiPos n` is supported in `[1/((n:ℝ)+2)², ((n:ℝ)+2)²] ⊆ (0,∞)`. -/
theorem logChiPos_eq_zero_off (n : ℕ) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ z : ℝ, z ∉ Set.Icc a b → logChiPos n z = 0 := by
  refine ⟨1 / ((n : ℝ) + 2) ^ 2, ((n : ℝ) + 2) ^ 2, ?_, ?_, ?_⟩
  · positivity
  · have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := Work.FTS.EllipticEst.TT.two_le_two_add_natCast n
    have h4 : (4 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith
  · intro z hz
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with h | h
    · by_cases hz0 : 0 < z
      · rw [logChiPos_of_pos hz0]
        exact Work.FTS.EllipticEst.TT.logChi_eq_zero_of_le hz0 (le_of_lt h)
      · simp only [logChiPos, if_neg hz0]
    · have hz0 : 0 < z := by
        have hb : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
        linarith
      rw [logChiPos_of_pos hz0]
      exact Work.FTS.EllipticEst.TT.logChi_eq_zero_of_ge (le_of_lt h)

theorem deriv_logChiPos_eq {n : ℕ} {z : ℝ} (hz : 0 < z) :
    deriv (logChiPos n) z = deriv (Work.FTS.EllipticEst.TT.logChi n) z := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  exact logChiPos_of_pos hy

theorem deriv_deriv_logChiPos_eq {n : ℕ} {z : ℝ} (hz : 0 < z) :
    deriv (deriv (logChiPos n)) z
      = deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
  exact deriv_logChiPos_eq hy

/-! ## The main assembly -/

/-- **The one-dimensional weighted Agmon--Nirenberg inequality for `C^∞` data, unconditional
`lintegral` form.**  This is `Work.EllipticEst.DzAgmonSmooth` (proved from the three pieces
above), used by `Work.EllipticEst.DzV_amgm_Hk`. -/
theorem DzAgmon1D_clean : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)) →
      ENNReal.ofReal (α ^ 2) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal (α ^ 4) *
                MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
              + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α h hα hα1 hcd
  -- abbreviations, matching the goal syntactically
  set F : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2 with hF
  set H : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2 with hH
  set G : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 with hG
  -- the two trivial cases
  by_cases hHtop : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (H z)) = ⊤
  · rw [hHtop, add_top, ENNReal.mul_top]
    · exact le_top
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 100 ^ 2))
  by_cases hGtop : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (G z)) = ⊤
  · rw [hGtop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hα 4))), top_add,
      ENNReal.mul_top]
    · exact le_top
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 100 ^ 2))
  -- ### continuity of the data integrands
  have hw2cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z; simp only [Work.Spaces.w]
    rw [h]
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · exact continuousOn_id.pow 2
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  have hdh_smooth : ContDiffOn ℝ Work.Stability.smoothOrder (deriv h) (Set.Ioi (0 : ℝ)) :=
    hcd.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
  have hdhcont : ContinuousOn (deriv h) (Set.Ioi (0 : ℝ)) := hdh_smooth.continuousOn
  have hd2h_smooth : ContDiffOn ℝ Work.Stability.smoothOrder (deriv (deriv h))
      (Set.Ioi (0 : ℝ)) :=
    hdh_smooth.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
  have hd2hcont : ContinuousOn (deriv (deriv h)) (Set.Ioi (0 : ℝ)) := hd2h_smooth.continuousOn
  have hHcont : ContinuousOn H (Set.Ioi (0 : ℝ)) := by
    rw [hH]
    exact hw2cont.mul (hcd.continuousOn.pow 2)
  have hGcont : ContinuousOn G (Set.Ioi (0 : ℝ)) := by
    rw [hG]
    exact hw2cont.mul (((continuousOn_id.pow 2).mul hd2hcont).pow 2)
  have hFcont : ContinuousOn F (Set.Ioi (0 : ℝ)) := by
    rw [hF]
    exact hw2cont.mul ((continuousOn_id.mul hdhcont).pow 2)
  -- ### integrability of the data
  have hHmeas : AEStronglyMeasurable H (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hHcont.aestronglyMeasurable measurableSet_Ioi
  have hGmeas : AEStronglyMeasurable G (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hGcont.aestronglyMeasurable measurableSet_Ioi
  have hFmeas : AEMeasurable F (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hFcont.aemeasurable measurableSet_Ioi
  have hHnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] H :=
    Filter.Eventually.of_forall fun z => by
      rw [hH]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hGnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] G :=
    Filter.Eventually.of_forall fun z => by
      rw [hG]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hFnn : ∀ z : ℝ, 0 ≤ F z := fun z => by
    rw [hF]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHint : IntegrableOn H (Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hHmeas hHnn).mp hHtop
  have hGint : IntegrableOn G (Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hGmeas hGnn).mp hGtop
  -- the `ofReal` bridges
  have hbridgeH : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (H z))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), H z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hHint hHnn).symm
  have hbridgeG : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (G z))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), G z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint hGnn).symm
  have hpnn : (0 : ℝ) ≤ ∫ z in Set.Ioi (0 : ℝ), H z :=
    integral_nonneg fun z => by rw [hH]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hqnn : (0 : ℝ) ≤ ∫ z in Set.Ioi (0 : ℝ), G z :=
    integral_nonneg fun z => by rw [hG]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- ### integrability of `F · logChi n²`
  obtain ⟨Kw, hKw0, -, hKw, -, -⟩ := Work.FTS.EllipticEst.Blocks.logChiFamily
  have hFint : ∀ n : ℕ, IntegrableOn
      (fun z : ℝ => F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    intro n
    obtain ⟨a, b, ha, hab, hsupp⟩ := logChiPos_eq_zero_off n
    set g : ℝ → ℝ := fun z => h z * logChiPos n z with hg
    have hgcd : ContDiffOn ℝ Work.Stability.smoothOrder g (Set.Ioi (0 : ℝ)) := by
      rw [hg]
      exact hcd.mul (logChiPos_contDiffOn n)
    have hgsupp : ∀ z : ℝ, z ∉ Set.Icc a b → g z = 0 := by
      intro z hz
      rw [hg]
      simp only [hsupp z hz, mul_zero]
    obtain ⟨hgd_left, hgd_right, -, -⟩ :=
      Work.FTS.EllipticEst.Blocks.AgmonDerivVanishing hgsupp
    have hsub : ∀ z ∈ Set.Icc a b, (0 : ℝ) < z := fun z hz => lt_of_lt_of_le ha hz.1
    have hdom_int : IntegrableOn
        (fun z : ℝ => 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2)
          + 2 * Kw ^ 2 * H z) (Set.Ioi (0 : ℝ)) := by
      refine IntegrableOn.add ?_ (hHint.const_mul _)
      refine Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
        (a := a) (b := b) ?_ ?_
      · refine ContinuousOn.mul continuousOn_const ?_
        have hgd_smooth : ContDiffOn ℝ Work.Stability.smoothOrder (deriv g) (Set.Ioi (0 : ℝ)) :=
          hgcd.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
        have hgd_cont : ContinuousOn (deriv g) (Set.Icc a b) :=
          hgd_smooth.continuousOn.mono (fun z hz => hsub z hz)
        have hw2_cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Icc a b) :=
          hw2cont.mono (fun z hz => hsub z hz)
        exact ContinuousOn.mul hw2_cont
          (ContinuousOn.pow (ContinuousOn.mul continuousOn_id hgd_cont) 2)
      · intro z hz
        rcases (by
          simpa only [Set.mem_Icc, not_and_or, not_le] using hz : z < a ∨ b < z) with h' | h'
        · rw [hgd_left z h']; ring
        · rw [hgd_right z h']; ring
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
        ‖F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2‖
          ≤ 2 * ((Work.Spaces.w z) ^ 2 * (z * deriv g z) ^ 2) + 2 * Kw ^ 2 * H z := by
      intro z hz
      have hχ : Work.FTS.EllipticEst.TT.logChi n z = logChiPos n z :=
        (logChiPos_of_pos hz).symm
      have hdh : DifferentiableAt ℝ h z :=
        (hcd.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hdχ : DifferentiableAt ℝ (logChiPos n) z :=
        ((logChiPos_contDiffOn n).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioi.mem_nhds hz)
      have hgderiv : deriv g z
          = deriv h z * logChiPos n z + h z * deriv (logChiPos n) z := by
        rw [hg]
        exact deriv_mul hdh hdχ
      have hkey : z * deriv h z * logChiPos n z
          = z * deriv g z - z * h z * deriv (logChiPos n) z := by
        rw [hgderiv]; ring
      have hb2 : (z * deriv (logChiPos n) z) ^ 2 ≤ Kw ^ 2 := by
        have h := hKw n z hz
        rw [← deriv_logChiPos_eq hz] at h
        calc (z * deriv (logChiPos n) z) ^ 2 = |z * deriv (logChiPos n) z| ^ 2 :=
              (sq_abs _).symm
          _ ≤ Kw ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      have hsq : (z * deriv h z * logChiPos n z) ^ 2
          ≤ 2 * (z * deriv g z) ^ 2 + 2 * Kw ^ 2 * (h z) ^ 2 := by
        have h2 : (z * h z * deriv (logChiPos n) z) ^ 2 ≤ Kw ^ 2 * (h z) ^ 2 := by
          have h3 : (z * h z * deriv (logChiPos n) z) ^ 2
              = (h z) ^ 2 * (z * deriv (logChiPos n) z) ^ 2 := by ring
          rw [h3]
          nlinarith [hb2, sq_nonneg (h z)]
        have h1 : ∀ u v : ℝ, (u - v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
          intro u v; nlinarith [sq_nonneg (u + v)]
        calc (z * deriv h z * logChiPos n z) ^ 2
            = (z * deriv g z - z * h z * deriv (logChiPos n) z) ^ 2 := by rw [hkey]
          _ ≤ 2 * (z * deriv g z) ^ 2 + 2 * (z * h z * deriv (logChiPos n) z) ^ 2 := h1 _ _
          _ ≤ 2 * (z * deriv g z) ^ 2 + 2 * (Kw ^ 2 * (h z) ^ 2) := by linarith
          _ = 2 * (z * deriv g z) ^ 2 + 2 * Kw ^ 2 * (h z) ^ 2 := by ring
      rw [Real.norm_eq_abs, hχ, hF, hH]
      rw [abs_of_nonneg (by
        refine mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
      have hw2 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have h4 : (z * deriv h z * logChiPos n z) ^ 2
          = (z * deriv h z) ^ 2 * (logChiPos n z) ^ 2 := by ring
      nlinarith [hsq, hw2, sq_nonneg (Work.Spaces.w z), sq_nonneg (z * deriv h z),
        sq_nonneg (logChiPos n z)]
    refine Integrable.mono' hdom_int
      ((hFcont.mul ((Work.FTS.EllipticEst.TT.logChi_contDiffOn n).continuousOn.pow 2))
        |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact hpt z hz
  -- ### the estimate, for `n` large
  obtain ⟨N₁, hN₁⟩ := Work.FTS.EllipticEst.Blocks.AgmonSmallness
  obtain ⟨K₂, hK₂pos, hK₂⟩ := Work.EllipticEst.logChi_second_deriv_le
  have hlogtop : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_mono (fun n : ℕ => by
      have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith) tendsto_natCast_atTop_atTop)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlogtop.eventually_ge_atTop K₂)
  set N₀ : ℕ := max N₁ N₂ with hN₀
  have hest : ∀ n : ℕ, N₀ ≤ n → α ^ 2 *
      (∫ z in Set.Ioi (0 : ℝ), F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)
      ≤ 100 * ((∫ z in Set.Ioi (0 : ℝ), H z)
          + α ^ 4 * (∫ z in Set.Ioi (0 : ℝ), G z)) := by
    intro n hn
    have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
    have hder1 : ∀ z : ℝ, 0 < z → |z * deriv (logChiPos n) z| ≤ 1 / 8 := by
      intro z hz
      rw [deriv_logChiPos_eq hz]
      exact hN₁ n hn₁ z hz
    have hder2 : ∀ z : ℝ, 0 < z → |z ^ 2 * deriv (deriv (logChiPos n)) z| ≤ 1 := by
      intro z hz
      have hle : |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z|
          ≤ K₂ / Real.log ((n : ℝ) + 2) := hK₂ n z hz
      rw [deriv_deriv_logChiPos_eq hz]
      have hlog : K₂ ≤ Real.log ((n : ℝ) + 2) := hN₂ n hn₂
      have hpos : 0 < Real.log ((n : ℝ) + 2) :=
        Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
      have hle1 : K₂ / Real.log ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one hpos]
        exact hlog
      exact le_trans hle hle1
    have hag := Work.EllipticEst.agmon_cutoff_estimate (logChiPos n) 1 (by norm_num) (by norm_num)
      (logChiPos_contDiffOn n) (logChiPos_nonneg n) (logChiPos_le_one n) hder1 hder2
      (logChiPos_eq_zero_off n) α hα hα1 h hcd hHint hGint
    -- replace `logChiPos` by `logChi` inside the integral (they agree on `(0,∞)`)
    have hcongr : (∫ z in Set.Ioi (0 : ℝ),
          Work.FTS.EllipticEst.Blocks.W2 z * (z * deriv h z) ^ 2 * (logChiPos n z) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ),
            F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      rw [logChiPos_of_pos hz]
      simp only [hF, Work.FTS.EllipticEst.Blocks.W2]
    rw [hcongr] at hag
    have hpH : (∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.Blocks.W2 z * h z ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), H z := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hH, Work.FTS.EllipticEst.Blocks.W2]
    have hqG : (∫ z in Set.Ioi (0 : ℝ),
          Work.FTS.EllipticEst.Blocks.W2 z * (z ^ 2 * deriv (deriv h) z) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), G z := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hG, Work.FTS.EllipticEst.Blocks.W2]
    rwa [hpH, hqG] at hag
  -- ### monotonicity in `n`
  have hmono : Monotone fun n : ℕ =>
      ∫ z in Set.Ioi (0 : ℝ), F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2 := by
    intro m n hmn
    refine MeasureTheory.integral_mono_ae (hFint m) (hFint n) ?_
    filter_upwards with z
    have hle : Work.FTS.EllipticEst.TT.logChi m z ≤ Work.FTS.EllipticEst.TT.logChi n z :=
      monotone_nat_of_le_succ (fun k => Work.FTS.EllipticEst.Blocks.logChi_mono_succ k z) hmn
    have h0 : 0 ≤ Work.FTS.EllipticEst.TT.logChi m z :=
      (Work.FTS.EllipticEst.TT.logChi_mem_Icc m z).1
    have h1 : 0 ≤ Work.FTS.EllipticEst.TT.logChi n z :=
      (Work.FTS.EllipticEst.TT.logChi_mem_Icc n z).1
    have hsq : (Work.FTS.EllipticEst.TT.logChi m z) ^ 2
        ≤ (Work.FTS.EllipticEst.TT.logChi n z) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hsq (hFnn z)
  -- ### monotone convergence and conclusion
  have hmct := Work.EllipticEst.logChi_iSup_lintegral F hFnn hFmeas hFint
  rw [hmct, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 2)]
  have hbound : α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
      F z * (Work.FTS.EllipticEst.TT.logChi n z) ^ 2)
      ≤ 100 * ((∫ z in Set.Ioi (0 : ℝ), H z) + α ^ 4 * (∫ z in Set.Ioi (0 : ℝ), G z)) := by
    by_cases hn : n < N₀
    · exact le_trans (mul_le_mul_of_nonneg_left (hmono (le_of_lt hn)) (by positivity))
        (hest N₀ le_rfl)
    · exact hest n (not_lt.mp hn)
  refine le_trans (ENNReal.ofReal_le_ofReal hbound) ?_
  rw [hbridgeG, hbridgeH]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 4),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100 ^ 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [hpnn, hqnn, (by positivity : (0 : ℝ) ≤ α ^ 4)]

end

end DzVamgm

namespace DzVamgm

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.DzAmgm
open Work.FTS.EllipticEst.DzAmgmSect

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The angular weights as squares -/

theorem angZ_sq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : (angZ θ) ^ 2 = sEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [angZ, sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hs]
  norm_num

theorem angM_sq (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : (angM α θ) ^ 2 = sGam α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [angM, sGam, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hs]
  norm_num

/-! ## The termwise Agmon estimate (adapted from `DzAmgm.Scratch`) -/

/-- **Termwise AM–GM, pure summands.**  Applying `TermAMGMLintegral` with `V = D_z^m f`,
`wth = angZ` and rewriting `D_z (D_z^m f) = D_z^{m+1} f`,
`z²∂_z²(D_z^m f) = D_z^m (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate for `TZ`. -/
theorem TZ_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (m : ℕ),
      ENNReal.ofReal (α ^ 2) * TZ f (m + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) m + TZ f m) := by
  intro α hα hα1 f hf m
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angZ θ := fun θ hθ =>
    angZ_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.DzIter m f) angZ (hf.DzIter m) hang
  -- the first factor of the left-hand integrand
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ * Work.Spaces.w z
          * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter (m + 1) f z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [Work.Spaces.DzIter_succ]
  -- the second-derivative factor of the right-hand side
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
          * Work.Spaces.w z * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter m (zsqPz2 f) z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := AgmonSlice.zsq_pzIter2_mixed_open f ((smoothOpen_iff_forall f).mp hf) m 0 hz hθ
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
        = Work.Spaces.DzIter m (zsqPz2 f) z θ := hcomm
    rw [h1]
  rw [hL, hR2] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-- **Termwise AM–GM, mixed summands.**  Applying `TermAMGMLintegral` with
`V = D_z^j D_θ^i f`, `wth = angM α` and rewriting `D_z (D_z^j D_θ^i f) = D_z^{j+1} D_θ^i f`,
`z²∂_z²(D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate. -/
theorem TM_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (i j : ℕ),
      ENNReal.ofReal (α ^ 2) * TM α f i (j + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) i j + TM α f i j) := by
  intro α hα hα1 f hf i j
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angM α θ := fun θ hθ =>
    angM_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.mixed j i f) (angM α) (hf.mixed j i) hang
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed j i f) z θ * Work.Spaces.w z
          * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed (j + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hdz : Work.Spaces.Dz (Work.Spaces.mixed j i f)
        = Work.Spaces.mixed (j + 1) i f := by
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
    rw [hdz]
    exact mixed_ofReal_eq α f i (j + 1) z θ
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
          * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i (zsqPz2 f) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := AgmonSlice.zsq_pzIter2_mixed_open f ((smoothOpen_iff_forall f).mp hf) j i hz hθ
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
        = Work.Spaces.mixed j i (zsqPz2 f) z θ := hcomm
    rw [h1, mixed_ofReal_eq α (zsqPz2 f) i j z θ]
  have hR3 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact mixed_ofReal_eq α f i j z θ
  rw [hL, hR2, hR3] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h



/-! ## The `LkSq` inequality -/

/-- **The `θ`-integrated radial interpolation for `D_z f`, at the level of the honest
`lintegral`s.** -/
theorem LkSq_Dz_le (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (k : ℕ) (f : ℝ → ℝ → ℝ),
      (∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
        Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
          = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) →
      SmoothOpen f →
      ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) := by
  intro α hα hα1 k f hcomm hf
  have hDz : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQ : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hdec : LkSq α k (Work.Spaces.Dz f)
      = (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0) := by
    rw [LkSq_eq_sum α k (Work.Spaces.Dz f) hDz]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => TZ_Dz f i
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc, TM_Dz_of_comm α f hcomm p.1 p.2]
      · rw [if_neg hc, if_neg hc]
  have hdecQ : LkSq α k (zsqPz2 f)
      = (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0) :=
    LkSq_eq_sum α k (zsqPz2 f) hQ
  have hdecf : LkSq α k f
      = (∑ i ∈ Finset.range (k + 1), TZ f i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0) :=
    LkSq_eq_sum α k f hf
  -- the termwise bounds
  have hT : ∀ i ∈ Finset.range (k + 1), ENNReal.ofReal (α ^ 2) * TZ f (i + 1)
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) i + TZ f i) :=
    fun i _ => TZ_termwise C1 hC1 hgen α hα hα1 f hf i
  have hM : ∀ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
      (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
              ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0) := by
    intro p _
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc, if_pos hc]
      exact TM_termwise C1 hC1 hgen α hα hα1 f hf p.1 p.2
    · rw [if_neg hc, if_neg hc, mul_zero]
  -- the two sums
  have hS1le : ENNReal.ofReal (α ^ 2) * (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
            + (∑ i ∈ Finset.range (k + 1), TZ f i)) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum hT) (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
  have hS2le : ENNReal.ofReal (α ^ 2)
        * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4)
              * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0))
            + (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0))) := by
    rw [Finset.mul_sum]
    have hstep : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
          ENNReal.ofReal (α ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
        = ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
              then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [hstep]
    refine le_trans (Finset.sum_le_sum hM) (le_of_eq ?_)
    have hflat : ∀ p : ℕ × ℕ,
        ENNReal.ofReal (C1 ^ 2) * (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
            ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0)
          = (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (C1 ^ 2) *
                (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2)
              else 0) := by
      intro p; by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k <;> simp [hc]
    rw [Finset.sum_congr rfl (fun p _ => hflat p)]
    rw [sum_ite_mul_split (k := k) (ENNReal.ofReal (C1 ^ 2)) (ENNReal.ofReal (α ^ 4))
      (fun p => TM α (zsqPz2 f) p.1 p.2) (fun p => TM α f p.1 p.2)]
    rw [mul_add]
    ring
  -- combine
  rw [hdec, mul_add]
  refine le_trans (add_le_add hS1le hS2le) (le_of_eq ?_)
  rw [hdecQ, hdecf]
  ring

/-- Finiteness of `LkSq (D_z f)` from the `LkSq` inequality. -/
theorem LkSq_Dz_lt_top (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f)) :
    LkSq α k (Work.Spaces.Dz f) < ⊤ := by
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ (SmoothOpen_zsqPz2 f hf) hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  have hfin : ENNReal.ofReal (C1 ^ 2) *
      (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin, hffin⟩
  have hlt : ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f) < ⊤ := lt_of_le_of_lt h hfin
  have hpos : ENNReal.ofReal (α ^ 2) ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < α ^ 2)).ne'
  rcases ENNReal.mul_lt_top_iff.mp hlt with ⟨-, h2⟩ | h0 | h0
  · exact h2
  · exact absurd h0 hpos
  · exact lt_top_iff_ne_top.mpr (by simp [h0])

/-- **The norm inequality**, given the honesty of `D_z f`. -/
theorem HkNorm_Dz_le_of (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f))
    (hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f)) :
    α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
      ≤ C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by
  have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQSm : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hDzfin := LkSq_Dz_lt_top C1 hC1 hgen α hα hα1 k f hf hmf hmQ
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ hQSm hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  -- (★) in terms of `HkSq`
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  rw [LkSq_eq_ofReal_HkSq α k (Work.Spaces.Dz f) hDzSm hmDz,
    LkSq_eq_ofReal_HkSq α k (zsqPz2 f) hQSm hmQ,
    LkSq_eq_ofReal_HkSq α k f hf hmf] at h
  have hnn : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz f) :=
    Work.Spaces.HkSq_nonneg α k _
  have hnnQ : 0 ≤ Work.Spaces.HkSq α k (zsqPz2 f) := Work.Spaces.HkSq_nonneg α k _
  have hnnf : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hL : ENNReal.ofReal (α ^ 2) * ENNReal.ofReal (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      = ENNReal.ofReal (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 2)]
  have hR : ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) *
        ENNReal.ofReal (Work.Spaces.HkSq α k (zsqPz2 f)) + ENNReal.ofReal (Work.Spaces.HkSq α k f))
      = ENNReal.ofReal (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
          + Work.Spaces.HkSq α k f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C1 ^ 2),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)) hnnf,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 4)]
  rw [hL, hR] at h
  have hsq : α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  -- take square roots
  have hsqrt : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := by
    have h1 : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
        = Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
      rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
    have h2 : C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        = Real.sqrt (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
            + Work.Spaces.HkSq α k f)) := by
      rw [Real.sqrt_mul (sq_nonneg C1), Real.sqrt_sq hC1.le]
    rw [h1, h2]
    exact Real.sqrt_le_sqrt hsq
  have hf1 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
      = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ α ^ 4), Work.Spaces.HkNorm,
      show Real.sqrt (α ^ 4) = α ^ 2 by
        rw [show α ^ 4 = (α ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ α ^ 2)]]
  have hadd : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
      ≤ α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
    calc Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
          + Real.sqrt (Work.Spaces.HkSq α k f) :=
          sqrt_add_le_sqrt _ _ (by positivity) (Work.Spaces.HkSq_nonneg α k f)
      _ = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
          rw [hf1]
          rfl
  calc α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := hsqrt
    _ ≤ C1 * (α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f) :=
        mul_le_mul_of_nonneg_left hadd (le_of_lt hC1)
    _ = C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by ring


/-! ## The honesty certificate `HkMem α k (D_z f)` -/

section Cert

/-- `D_z` commutes with the iterates `D_z^m` on the left: `D_z^m (D_z f) = D_z (D_z^m f)`. -/
theorem DzIter_Dz_eq (m : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter m (Work.Spaces.Dz f) = Work.Spaces.Dz (Work.Spaces.DzIter m f) := by
  have h1 : Work.Spaces.Dz f = Work.Spaces.DzIter 1 f := rfl
  rw [h1, ← Work.Spaces.DzIter_add_right m 1 f,
    show m + 1 = 1 + m from by omega, Work.Spaces.DzIter_add_right 1 m f]
  rfl

theorem angw_zero (α : ℝ) (θ : ℝ) : angw α 0 θ = sEta θ := by simp [angw]

theorem angw_pos (α : ℝ) {i : ℕ} (hi : 1 ≤ i) (θ : ℝ) : angw α i θ = sGam α θ := by
  simp only [angw]
  rw [if_neg (by omega)]

theorem measurable_angZ : Measurable angZ := by
  have h : angZ = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := rfl
  rw [h]; fun_prop

theorem measurable_angM (α : ℝ) : Measurable (angM α) := by
  have h : angM α = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [h]; fun_prop

/-- A single block of the `ℋ^k`-integrand is dominated by the whole integrand. -/
theorem hblk_le_HkIntegrand (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (i m : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : hblk α k φ (i, m) z θ ≤ Work.Spaces.HkIntegrand α k φ z θ := by
  by_cases h : i + m ≤ k
  · rw [HkIntegrand_eq_hblk α k φ hθ]
    refine le_trans (Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun m' => hblk α k φ (i, m') z θ)
      (fun m' _ => hblk_nonneg α k φ (i, m') z θ hθ) (a := m)
      (Finset.mem_range.mpr (by omega))) ?_
    exact Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun i' => ∑ m' ∈ Finset.range (k + 1), hblk α k φ (i', m') z θ)
      (fun i' _ => Finset.sum_nonneg (fun m' _ => hblk_nonneg α k φ (i', m') z θ hθ)) (a := i)
      (Finset.mem_range.mpr (by omega))
  · rw [hblk_eq_zero α k φ (i, m) z θ h]
    exact Work.Spaces.HkIntegrand_nonneg α k φ z θ

/-- The `θ`-slice integral of a single block of the `ℋ^k`-integrand is finite, as soon as the
integrand is honest. -/
theorem hblk_Iθ_lt_top (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (hφ : SmoothOpen φ)
    (hm : Work.Spaces.HkMem α k φ) (i m : ℕ) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k φ (i, m) z θ) < ⊤ := by
  have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k φ z θ) Work.Spaces.Iθ :=
    hm.1 z (le_of_lt hz)
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k φ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hφ.continuousOn_HkIntegrand α k) hz
  have hbnd : ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ z θ) < ⊤ :=
    lt_top_iff_ne_top.mpr ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k φ z θ)).mpr hInt)
  exact lt_of_le_of_lt (lintegral_mono_ae (by
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with θ hθ
    exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k φ i m hθ))) hbnd

/-- **The `z`-slice of `D_z V`, against a general angular weight, is finite.**  This is the
`D_z`-form of the slice lemma `SliceZDeriv_finite`. -/
theorem sliceDz_lintegral_lt_top (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ)
    (hwth : ∀ θ, 0 ≤ wth θ) (hwthmeas : Measurable wth)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hG : ∀ z ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal ((V z θ * wth θ) ^ 2) < ⊤)
    (hB : ∀ z ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z' in Set.Ioo z (z + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 V z' θ * wth θ) ^ 2) < ⊤)
    {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2) < ⊤ := by
  have h1 := SliceZDeriv_finite V wth hwth hwthmeas hsm hG hB hz
  rw [lintegral_Iθ_eq_Ioo]
  have hEq : ∀ θ : ℝ, ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2)
      = ENNReal.ofReal ((z * Work.Spaces.w z) ^ 2)
        * ENNReal.ofReal ((Work.Spaces.pz V z θ * wth θ) ^ 2) := by
    intro θ
    have hpt : (Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2
        = (z * Work.Spaces.w z) ^ 2 * (Work.Spaces.pz V z θ * wth θ) ^ 2 := by
      simp only [Work.Spaces.Dz]
      ring
    rw [hpt, ENNReal.ofReal_mul (by positivity)]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hEq)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

/-- The raw shape of the open-quadrant smoothness hypothesis. -/
theorem smooth_raw {φ : ℝ → ℝ → ℝ} (h : SmoothOpen φ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => (smoothOpen_iff_forall φ).mp h n

/-- The second radial derivative of `f`, as a `SmoothOpen` function. -/
theorem smooth_zsqPz2 (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) := by
  have h1 : (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) = zsqPz2 f := rfl
  rw [h1]; exact SmoothOpen_zsqPz2 f hf

/-- The global `z`-`θ` `lintegral` of the `ℋ^k`-integrand of `z²∂_z²f` is finite. -/
theorem global_zsqPz2_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) :
    (∫⁻ z' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z' θ)) < ⊤ := by
  have hQSm : SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) := smooth_zsqPz2 f hf
  have h := LkSq_lt_top α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) hQSm hmQ
  rw [LkSq] at h
  rw [MeasureTheory.lintegral_lintegral_swap
    ((aesm_HkIntegrand_prod α k _ hQSm).prod_swap)] at h
  exact h

/-- **The block of the `ℋ^k`-integrand of `D_z f` at `(0,m)` has finite `θ`-slice integral.** -/
theorem hblk_pure_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))
    {m : ℕ} (hm : m ≤ k) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (0, m) z θ) < ⊤ := by
  have hcongr : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (0, m) z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ
        * Work.Spaces.w z * |angZ θ|) ^ 2)) := by
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    rw [hblk_eq α k (Work.Spaces.Dz f) (0, m) z θ (by omega), angw_zero]
    simp only [hblkR, Work.Spaces.DthIter_zero]
    rw [DzIter_Dz_eq]
    simp only [mul_pow, sq_abs, angZ_sq ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩] <;> ring_nf
  rw [lintegral_congr_ae hcongr]
  have hG : ∀ z' ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2) < ⊤ := by
    intro z' hz'
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, hblk α k f (0, m) z' θ
        = (Work.Spaces.w z') ^ 2 * ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2) := by
      intro θ hθ
      rw [hblk_eq α k f (0, m) z' θ (by omega), angw_zero]
      simp only [hblkR, Work.Spaces.DthIter_zero]
      simp only [mul_pow, sq_abs, angZ_sq hθ] <;> ring_nf
    have hrel : (fun θ => ENNReal.ofReal (hblk α k f (0, m) z' θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
          * ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      rw [hpt θ hθ, ENNReal.ofReal_mul (by positivity)]
    have h4 : ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2)) < ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, lintegral_congr_ae hrel.symm]
      exact hblk_Iθ_lt_top α k f hf hmf 0 m hz'
    have hpos : ENNReal.ofReal ((Work.Spaces.w z') ^ 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have hthis : (0 : ℝ) < ((1 + z') ^ 2 / z' ^ 2) ^ 2 := by
        have hz'pos : (0 : ℝ) < z' := hz'
        positivity
      simpa only [Work.Spaces.w] using hthis
    rcases ENNReal.mul_lt_top_iff.mp h4 with ⟨-, h⟩ | h0 | h0
    · rwa [lintegral_Iθ_eq_Ioo] at h
    · exact absurd h0 hpos
    · rw [← lintegral_Iθ_eq_Ioo, h0]; exact ENNReal.zero_lt_top
  have hB : ∀ z' ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z'' in Set.Ioo z' (z' + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
          * |angZ θ|) ^ 2) < ⊤ := by
    intro z' hz'
    refine ⟨1, one_pos, ?_⟩
    have hglob := global_zsqPz2_lt_top α k f hf hmQ
    have hstep : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
            * |angZ θ|) ^ 2))
        ≤ (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet (Set.Ioo z' (z' + 1)) from
        measurableSet_Ioo)] with z'' hz''
      have hz''0 : 0 < z'' := lt_trans hz' hz''.1
      refine le_trans ?_ (lintegral_mono_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) 0 m hθ)))
      rw [← lintegral_Iθ_eq_Ioo]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_mem_Ioo_theta] with θ hθ
      have hcom := AgmonSlice.zsq_pzIter2_mixed_open f (smooth_raw hf) m 0 hz''0 hθ
      have hcom' : Work.Spaces.DzIter m (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ
          = z'' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ := by
        simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero] using hcom.symm
      have hval2 : hblk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (0, m) z'' θ
          = (1 + z'') ^ 4
            * (Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ * angZ θ) ^ 2 := by
        rw [hblk_eq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (0, m) z'' θ (by omega),
          angw_zero]
        simp only [hblkR, Work.Spaces.DthIter_zero]
        rw [hcom']
        simp only [mul_pow, angZ_sq ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
        have hzne : z'' ≠ 0 := ne_of_gt hz''0
        rw [Work.Spaces.w]
        field_simp
      rw [hval2]
      have hsq : ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
            * |angZ θ|) ^ 2)
          = ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
              * angZ θ) ^ 2) := by
        congr 1
        simp only [mul_pow, sq_abs]
      rw [hsq]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (1 : ℝ) ≤ (1 + z'') ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z'')
      have h2 : (0 : ℝ) ≤ (Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ * angZ θ) ^ 2 :=
        sq_nonneg _
      simpa using mul_le_mul_of_nonneg_right h1 h2
    have hdom : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ))
        ≤ (∫⁻ z'' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) :=
      MeasureTheory.lintegral_mono_set
        (fun z'' hz'' => show z'' ∈ Work.Spaces.Iz from
          le_of_lt (lt_trans (show (0 : ℝ) < z' from hz') hz''.1))
    exact lt_of_le_of_lt (le_trans hstep hdom) hglob
  exact sliceDz_lintegral_lt_top (Work.Spaces.DzIter m f) (fun θ => |angZ θ|)
    (fun θ => abs_nonneg _) measurable_angZ.abs
    (show ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter m f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from (hf.DzIter m).forall 2) hG hB hz

theorem hblk_mixed_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))
    {i m : ℕ} (hi : 1 ≤ i) (him : i + m ≤ k) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ) < ⊤ := by
  have hcongr : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed m i f) z θ
        * Work.Spaces.w z * |angM α θ|) ^ 2)) := by
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    have hcom : Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
        = Work.Spaces.Dz (Work.Spaces.mixed m i f) z θ := by
      rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f))
          = Work.Spaces.mixed m i (Work.Spaces.Dz f) from rfl,
        show Work.Spaces.mixed m i (Work.Spaces.Dz f)
          = Work.Spaces.mixed m i (Work.Spaces.DzIter 1 f) from rfl,
        AgmonSlice.mixed_DzIter_open f hf m i 1 z θ hz hθ.1 hθ.2]
      rfl
    rw [hblk_eq α k (Work.Spaces.Dz f) (i, m) z θ (by omega), angw_pos α hi]
    simp only [hblkR]
    rw [hcom]
    simp only [mul_pow, sq_abs, angM_sq α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩] <;> ring_nf
  rw [lintegral_congr_ae hcongr]
  have hG : ∀ z' ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2) < ⊤ := by
    intro z' hz'
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, hblk α k f (i, m) z' θ
        = (Work.Spaces.w z') ^ 2 * ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2) := by
      intro θ hθ
      rw [hblk_eq α k f (i, m) z' θ (by omega), angw_pos α hi]
      simp only [hblkR]
      simp only [Work.Spaces.mixed, mul_pow, sq_abs, angM_sq α hθ] <;> ring_nf
    have hrel : (fun θ => ENNReal.ofReal (hblk α k f (i, m) z' θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
          * ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      rw [hpt θ hθ, ENNReal.ofReal_mul (by positivity)]
    have h4 : ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2)) < ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, lintegral_congr_ae hrel.symm]
      exact hblk_Iθ_lt_top α k f hf hmf i m hz'
    have hpos : ENNReal.ofReal ((Work.Spaces.w z') ^ 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have hthis : (0 : ℝ) < ((1 + z') ^ 2 / z' ^ 2) ^ 2 := by
        have hz'pos : (0 : ℝ) < z' := hz'
        positivity
      simpa only [Work.Spaces.w] using hthis
    rcases ENNReal.mul_lt_top_iff.mp h4 with ⟨-, h⟩ | h0 | h0
    · rwa [lintegral_Iθ_eq_Ioo] at h
    · exact absurd h0 hpos
    · rw [← lintegral_Iθ_eq_Ioo, h0]; exact ENNReal.zero_lt_top
  have hB : ∀ z' ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z'' in Set.Ioo z' (z' + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
          * |angM α θ|) ^ 2) < ⊤ := by
    intro z' hz'
    refine ⟨1, one_pos, ?_⟩
    have hglob := global_zsqPz2_lt_top α k f hf hmQ
    have hstep : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
            * |angM α θ|) ^ 2))
        ≤ (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet (Set.Ioo z' (z' + 1)) from
        measurableSet_Ioo)] with z'' hz''
      have hz''0 : 0 < z'' := lt_trans hz' hz''.1
      refine le_trans ?_ (lintegral_mono_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) i m hθ)))
      rw [← lintegral_Iθ_eq_Ioo]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_mem_Ioo_theta] with θ hθ
      have hcomA := AgmonSlice.zsq_pzIter2_mixed_open f (smooth_raw hf) m i hz''0 hθ
      have hcom' : Work.Spaces.DzIter m (Work.Spaces.DthIter i
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) z'' θ
          = z'' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ := by
        simpa only [Work.Spaces.mixed] using hcomA.symm
      have hval2 : hblk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m) z'' θ
          = (1 + z'') ^ 4
            * (Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ * angM α θ) ^ 2 := by
        rw [hblk_eq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m) z'' θ (by omega),
          angw_pos α hi]
        simp only [hblkR]
        rw [hcom']
        simp only [mul_pow, angM_sq α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
        have hzne : z'' ≠ 0 := ne_of_gt hz''0
        rw [Work.Spaces.w]
        field_simp
      rw [hval2]
      have hsq : ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
            * |angM α θ|) ^ 2)
          = ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
              * angM α θ) ^ 2) := by
        congr 1
        simp only [mul_pow, sq_abs]
      rw [hsq]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (1 : ℝ) ≤ (1 + z'') ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z'')
      have h2 : (0 : ℝ) ≤ (Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ * angM α θ) ^ 2 :=
        sq_nonneg _
      simpa using mul_le_mul_of_nonneg_right h1 h2
    have hdom : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ))
        ≤ (∫⁻ z'' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) :=
      MeasureTheory.lintegral_mono_set
        (fun z'' hz'' => show z'' ∈ Work.Spaces.Iz from
          le_of_lt (lt_trans (show (0 : ℝ) < z' from hz') hz''.1))
    exact lt_of_le_of_lt (le_trans hstep hdom) hglob
  exact sliceDz_lintegral_lt_top (Work.Spaces.mixed m i f) (fun θ => |angM α θ|)
    (fun θ => abs_nonneg _) (measurable_angM α).abs
    (show ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.mixed m i f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from (hf.mixed m i).forall 2) hG hB hz

/-- **The pointwise-in-`z` honesty of `HkIntegrand α k (D_z f)`.** -/
theorem HkMem_Dz_slices (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) :
    ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
        Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    have h : (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) 0 θ)
        = fun _ => (0 : ℝ) := by
      funext θ; exact Work.Coercivity.HkIntegrand_zero_left α k (Work.Spaces.Dz f) θ
    rw [h]; exact integrableOn_zero
  · have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
    have haesm : AEStronglyMeasurable
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hDzSm.continuousOn_HkIntegrand α k) hz0
    have hfin : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)) < ⊤ := by
      have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
            = ∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1),
                ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        rw [HkIntegrand_eq_hblk α k (Work.Spaces.Dz f) hθ]
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun i _ => Finset.sum_nonneg (fun m _ =>
            hblk_nonneg α k (Work.Spaces.Dz f) (i, m) z θ hθ))]
        exact Finset.sum_congr rfl fun i _ =>
          ENNReal.ofReal_sum_of_nonneg
            (fun m _ => hblk_nonneg α k (Work.Spaces.Dz f) (i, m) z θ hθ)
      have haesm_blk : ∀ i m : ℕ, AEMeasurable
          (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun i m =>
        ((Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (continuousOn_hblk_Q0 α k (Work.Spaces.Dz f) (smooth_raw hDzSm) i m) hz0).aemeasurable).ennreal_ofReal
      rw [lintegral_congr_ae hpt]
      have houter := MeasureTheory.lintegral_finsetSum' (s := Finset.range (k + 1))
        (f := fun i a => ∑ m ∈ Finset.range (k + 1),
          ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z a))
        (fun i _ => (Finset.aemeasurable_sum (Finset.range (k + 1))
          (fun m _ => haesm_blk i m)).congr
          (Filter.Eventually.of_forall fun a => by simp only [Finset.sum_apply]))
      rw [houter]
      refine ENNReal.sum_lt_top.mpr (fun i hi => ?_)
      have hinner := MeasureTheory.lintegral_finsetSum' (s := Finset.range (k + 1))
        (f := fun m a => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z a))
        (fun m _ => haesm_blk i m)
      rw [hinner]
      refine ENNReal.sum_lt_top.mpr (fun m hm => ?_)
      by_cases him : i + m ≤ k
      · rcases eq_or_ne i 0 with h | h
        · subst h
          exact hblk_pure_lt_top α k f hf hmf hmQ (by omega) hz0
        · exact hblk_mixed_lt_top α k f hf hmf hmQ (by omega) him hz0
      · have hzero : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
            = fun _ => (0 : ℝ≥0∞) := by
          funext θ
          rw [hblk_eq_zero α k (Work.Spaces.Dz f) (i, m) z θ him]
          simp
        rw [hzero, lintegral_zero]
        exact ENNReal.zero_lt_top


    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.Dz f) z θ)).mp ?_
    exact lt_top_iff_ne_top.mp hfin

end Cert


/-! ## The last bridges -/

/-- The second `HkMem` conjunct of `g`, from the finiteness of `LkSq α k g`. -/
theorem integrableOn_sliceIntegral_of_LkSq_lt_top (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) (h : LkSq α k g < ⊤) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      Work.Spaces.Iz := by
  have hprod : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aesm_HkIntegrand_prod α k g hg
  have hswap : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)) < ⊤ := by
    rw [LkSq] at h
    rwa [MeasureTheory.lintegral_lintegral_swap (hprod.prod_swap)] at h
  have hA : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprod.lintegral_prod_right'
  have hintA : Integrable (fun z => (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)).toReal)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hA (ne_of_lt hswap)
  have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  refine hintA.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from
    measurableSet_Ici), hpos] with z hz hzpos
  exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hg.continuousOn_HkIntegrand α k) hzpos)).symm

/-- The `θ`-integrated Agmon interface, assembled from the one-dimensional estimate. -/
theorem hgen_of_agmon : ∃ C : ℝ, 0 < C ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (MeasureTheory.lintegral
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
          (fun θ => MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))))
        ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal (α ^ 4) * (MeasureTheory.lintegral
                (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                (fun θ => MeasureTheory.lintegral
                  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))))
              + (MeasureTheory.lintegral
                  (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                  (fun θ => MeasureTheory.lintegral
                    (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                    (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))))) := by
  obtain ⟨C, hC, h1D⟩ := DzAgmon1D_clean
  refine ⟨C, hC, ?_⟩
  intro α hα hα1 V wth hV hwth
  exact TermAgmon C hC h1D α V wth hα hα1 hV hwth

/-- **Agmon--Nirenberg (interpolation) for `D_z = z∂_z` in the weighted `H^k`-norm.** -/
theorem HkNorm_Dz_amgm (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k f →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz f) ∧
        α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
          ≤ C * (Work.Spaces.HkNorm α k f
              + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) := by
  obtain ⟨C, hC, hgen⟩ := hgen_of_agmon
  refine ⟨C, hC, ?_⟩
  intro α f hα hα1 hf hmf hmQ
  have hF : SmoothOpen f := smoothOpen_of_forall hf
  have hmQ' : Work.Spaces.HkMem α k (zsqPz2 f) := hmQ
  have hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f) :=
    ⟨HkMem_Dz_slices α k f hF hmf hmQ',
      integrableOn_sliceIntegral_of_LkSq_lt_top α k (Work.Spaces.Dz f) hF.Dz
        (LkSq_Dz_lt_top C hC hgen α hα hα1 k f hF hmf hmQ')⟩
  exact ⟨hmDz, HkNorm_Dz_le_of C hC hgen α hα hα1 k f hF hmf hmQ' hmDz⟩

end DzVamgm

/-- **Agmon--Nirenberg (interpolation) for `D_z = z∂_z` in the weighted `H^k`-norm**, for
`0 < α ≤ 1/4` (a special case of the `α ≤ 1` statement `DzVamgm.HkNorm_Dz_amgm` proved above). -/
theorem DzV_amgm_clean (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k f →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz f) ∧
      α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
        ≤ C * (Work.Spaces.HkNorm α k f
            + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) := by
  obtain ⟨C, hC, hgen⟩ := DzVamgm.HkNorm_Dz_amgm k
  refine ⟨C, hC, ?_⟩
  intro α f hα hα1 hf hmf hmQ
  exact hgen α f hα (le_trans hα1 (by norm_num)) hf hmf hmQ

end Work.BlocksSect
