import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_MuLamOK.RowReduction
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.one_le_mul_w
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.caseExcMine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The exceptional `D_θ`-row slot of the level-six coefficient pairing

This module proves `Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.caseExcMine`, the per-summand
estimate for the **exceptional** slot of the level-six `A · D_θ f` pairing: the configuration
`(a,b,i,j) = (1,5,0,5)` with the `γ`-weight `ρ = leafGam α`, i.e. the pairing
`D_z⁵A · D_θ²f · D_z⁵D_θf`.

The Leibniz expansion of the coefficient slot pairs the *pure radial* slot `D_z⁵A` of the
coefficient with the mixed datum slot `D_θ²f = mixed 0 2 f`, and the second datum slot is
`D_z⁵D_θf = mixed 5 1 f`.  The two factors are estimated by the shipped
`H6Rows.Npair6Aux.excDz5Dth2Le4` (which prices `D_z⁵A · D_θ²f · Wt` by
`HkSq α 6 A · HkSq α 4 f`, with the factor `10/α = 1/(γ-1)`) and by the level-six energy of
the mixed slot `mixed 5 1 f`; Cauchy–Schwarz together with the weight split
`canonW (gam α) = Wt²` then gives

`|∫∫ leafGam α · D_z⁵A · D_θ²f · D_z⁵D_θf| ≤ C · α^{-1/2} · HkNorm α 6 A · M · HkNorm α 6 f`,

and `HkNorm α 6 A ≤ K6` converts this into the announced bracket (constant
`C = √(10 Ce) + 1`).  The weight identity `leafGam α = canonW (gam α)` is `rfl` (both are
`w(z)² sin(2θ)^{-γ}`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_gam_eq)
open Work.FTS.OpenPkg.ProdOpen (continuousOn_Wt)

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The constant of the exceptional-case estimate, given the constant `Ce` of the shipped
exceptional pairing `H6Rows.Npair6Aux.excDz5Dth2Le4`. -/
def caseCofM (Ce : ℝ) : ℝ := Real.sqrt (Ce * 10) + 1

theorem caseCofMM_pos {Ce : ℝ} (h : 0 < Ce) : 0 < caseCofM Ce := by
  unfold caseCofM
  have := Real.sqrt_nonneg (Ce * 10)
  linarith

theorem caseExcMine : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ
          => Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 5 0 A z θ
            * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.mixed 5 1 f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 5 0 A z θ
            * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.mixed 5 1 f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed 5 0 A z θ
            * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.mixed 5 1 f z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨Ce, hCepos, hCe⟩ := Work.FTS.StrongPersist.H6Rows.Npair6Aux.excDz5Dth2Le4
  refine ⟨caseCofM Ce, caseCofMM_pos hCepos, ?_⟩
  intro α hαmem A f K0 K4 K6 M hcoef hdat
  obtain ⟨hα, hα1⟩ := hαmem
  obtain ⟨hsmA, hA4, hA6, hvalA, hn4, hn6⟩ := hcoef
  obtain ⟨hsmf, hf6, hf7, hvanish, haxis, hbdd⟩ := hdat
  have hf4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmf 4 (by norm_num) hf6
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hn6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hK0nn : 0 ≤ K0 := le_trans (abs_nonneg (A 1 (Real.pi / 4)))
    (hvalA 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos]))
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hn4
  have hSq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hX6Ann : 0 ≤ Work.Spaces.HkNorm α 6 A := Work.Spaces.HkNorm_nonneg α 6 A
  have hαnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCnn : 0 ≤ caseCofM Ce := (caseCofMM_pos hCepos).le
  rw [show Work.FTS.TransportS.leafGam α = canonW (Work.Spaces.gam α) from rfl]
  simp only [Work.Spaces.mixed_zero_right]
  -- ## the two weight facts
  have hWtEq : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      canonW (Work.Spaces.gam α) z θ = (Work.Spaces.Wt α z θ) ^ 2 :=
    fun z θ hθ => canonW_gam_eq α z θ hθ
  have hptW : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      canonW (Work.Spaces.gam α) z θ * (Work.Spaces.mixed 5 1 f z θ) ^ 2
        = (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    intro z θ hθ; rw [hWtEq z θ hθ]; ring
  have hkey : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 5 A z θ|
          * |Work.Spaces.mixed 0 2 f z θ| * |Work.Spaces.mixed 5 1 f z θ|
        = |Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ|
          * |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ| := by
    intro z θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hWtnn : 0 ≤ Work.Spaces.Wt α z θ := by
      rw [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
      exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hsin _)
    rw [hWtEq z θ hθ]
    simp only [abs_mul]
    rw [abs_of_nonneg hWtnn]
    ring
  -- ## the `Z`-slot energy (`D_z⁵D_θf`) at level six
  obtain ⟨hZsl', hZmg', hZint'⟩ := canonW_energy_mixed6
    hα (q := Work.Spaces.gam α) (Work.Spaces.gam_pos hα).le le_rfl hsmf hf6 (j' := 5) (i' := 1)
    (by norm_num) (by norm_num)
  have hZ2sl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ :=
    fun z hz => (hZsl' z hz).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hptW z θ hθ))
  have hZ2mg : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz :=
    hZmg'.congr (Filter.Eventually.of_forall (fun z =>
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hptW z θ hθ))))
  have hZ2int : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f := by
    have hEq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            canonW (Work.Spaces.gam α) z θ * (Work.Spaces.mixed 5 1 f z θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_))
      exact MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => (hptW z θ hθ).symm))
    rw [hEq]
    exact hZint'
  -- ## the exceptional pairing `D_z⁵A · D_θ²f` at the `γ`-weight
  have hexc := hCe α A f hα hα1 hsmA hA6 hsmf hf4 hf6
  have hfac1 : Ce / (Work.Spaces.gam α - 1) = Ce * 10 * α⁻¹ := by
    rw [Work.Spaces.gam_sub_one]; field_simp
  have hsq : Ce * 10 ≤ (Real.sqrt (Ce * 10) + 1) ^ 2 := by
    have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ Ce * 10 by positivity)
    nlinarith [Real.sqrt_nonneg (Ce * 10)]
  have hhalf : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
    rw [sq, ← Real.rpow_add hα, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num,
      Real.rpow_neg_one]
  have hfacD : Ce / (Work.Spaces.gam α - 1)
      ≤ ((Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ))) ^ 2 := by
    rw [hfac1, mul_pow, hhalf]
    exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hα.le)
  have hsqX : Real.sqrt (Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 5 A z θ
      * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ))
      ≤ caseCofM Ce * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A * M := by
    have hmono : Ce / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 4 f
        ≤ ((Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ))) ^ 2
          * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 4 f) := by
      calc Ce / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 4 f
            = (Ce / (Work.Spaces.gam α - 1))
              * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 4 f) := by ring
        _ ≤ ((Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ))) ^ 2
              * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 4 f) :=
              mul_le_mul_of_nonneg_right hfacD
                (mul_nonneg (Work.Spaces.HkSq_nonneg α 6 A) (Work.Spaces.HkSq_nonneg α 4 f))
    have hstep1 : Real.sqrt (Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 5 A z θ
        * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ))
        ≤ Real.sqrt (((Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ))) ^ 2
          * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 4 f)) :=
      Real.sqrt_le_sqrt (le_trans hexc.2 hmono)
    have hstep2 : Real.sqrt (((Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ))) ^ 2
          * (Work.Spaces.HkSq α 6 A * Work.Spaces.HkSq α 4 f))
        = (Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A
          * Work.Spaces.HkNorm α 4 f := by
      rw [Real.sqrt_mul (sq_nonneg ((Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ)))),
          Real.sqrt_sq (mul_nonneg (by positivity) hαnn),
          Real.sqrt_mul (Work.Spaces.HkSq_nonneg α 6 A)]
      simp only [Work.Spaces.HkNorm]
      ring
    have hstep3 : (Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A
          * Work.Spaces.HkNorm α 4 f
        ≤ (Real.sqrt (Ce * 10) + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A * M :=
      mul_le_mul_of_nonneg_left hbdd (mul_nonneg (mul_nonneg (by positivity) hαnn) hX6Ann)
    exact le_trans (le_trans hstep1 (le_of_eq hstep2)) hstep3
  have hsqZ : Real.sqrt (Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 5 1 f z θ
      * Work.Spaces.Wt α z θ)) ≤ Work.Spaces.HkNorm α 6 f := by
    simpa only [Work.Spaces.L2Sq, Work.Spaces.HkNorm, Work.Spaces.HkSq] using
      Real.sqrt_le_sqrt hZ2int
  -- ## the AM–GM majorant of the integrand
  have hAM : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ|
        * |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ|
      ≤ ((Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
        + (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) / 2 := by
    intro z θ _
    have h := two_mul_le_add_sq
      |Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ|
      |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ|
    rw [sq_abs, sq_abs] at h
    linarith
  have hHsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      ((Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
        + (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) / 2) Work.Spaces.Iθ :=
    fun z hz => ((hexc.1.1 z hz).add (hZ2sl z hz)).div_const 2
  have hHmg : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      ((Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
        + (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) / 2) Work.Spaces.Iz := by
    refine ((hexc.1.2.add hZ2mg).div_const 2).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    show ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
        * Work.Spaces.Wt α z θ) ^ 2) + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 5 1 f z θ
        * Work.Spaces.Wt α z θ) ^ 2)) / 2
      = ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
        * Work.Spaces.Wt α z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) / 2
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add (hexc.1.1 z hz) (hZ2sl z hz)]
  have hcontX2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 5 A p.1 p.2
      * Work.Spaces.mixed 0 2 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((hsmA.DzIter 5).continuousOn.mul (hsmf.mixed 0 2).continuousOn).mul (continuousOn_Wt α)
  have hcontZ2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed 5 1 f p.1 p.2
      * Work.Spaces.Wt α p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsmf.mixed 5 1).continuousOn.mul (continuousOn_Wt α)
  have hABsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ|
      * |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ|) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ => |Work.Spaces.DzIter 5 A 0 θ * Work.Spaces.mixed 0 2 f 0 θ
            * Work.Spaces.Wt α 0 θ|
          * |Work.Spaces.mixed 5 1 f 0 θ * Work.Spaces.Wt α 0 θ|) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp only [Work.Spaces.Wt, Work.Spaces.w]
        norm_num
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono' (hHsl z hz) ?_ ?_
      · refine Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ =>
          |Work.Spaces.DzIter 5 A p.1 p.2 * Work.Spaces.mixed 0 2 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2|
          * |Work.Spaces.mixed 5 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2|) ?_ hzpos
        exact hcontX2.abs.mul hcontZ2.abs
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        exact hAM z θ hθ
  have hABmg : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ|
      * |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ|) Work.Spaces.Iz := by
    refine Integrable.mono' hHmg ?_ ?_
    · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
          |Work.Spaces.DzIter 5 A p.1 p.2 * Work.Spaces.mixed 0 2 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2|
          * |Work.Spaces.mixed 5 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2|)
          (hcontX2.abs.mul hcontZ2.abs))
    · rw [restrict_Iz_eq_Ioi]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      refine le_trans (MeasureTheory.norm_integral_le_integral_norm
        (fun θ : ℝ => |Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
          * Work.Spaces.Wt α z θ| * |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ|)) ?_
      refine MeasureTheory.integral_mono_ae (hABsl z (Set.mem_Ici.mpr hz.le)).norm
        (hHsl z (Set.mem_Ici.mpr hz.le)) ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      show ‖|Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ|
          * |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ|‖
        ≤ ((Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
          + (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) / 2
      rw [Real.norm_of_nonneg (by positivity)]
      exact hAM z θ hθ
  have hGsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 5 A z θ|
        * |Work.Spaces.mixed 0 2 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) Work.Spaces.Iθ :=
    fun z hz => (hABsl z hz).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => (hkey z θ hθ).symm))
  have hGmg : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      canonW (Work.Spaces.gam α) z θ * |Work.Spaces.DzIter 5 A z θ|
        * |Work.Spaces.mixed 0 2 f z θ| * |Work.Spaces.mixed 5 1 f z θ|) Work.Spaces.Iz := by
    refine hABmg.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
    exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => (hkey z θ hθ).symm))
  have hFcont : ContinuousOn (Function.uncurry (fun z θ : ℝ => canonW (Work.Spaces.gam α) z θ
      * Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.mixed 5 1 f z θ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)).mul
      (hsmA.DzIter 5).continuousOn).mul (hsmf.mixed 0 2).continuousOn).mul
      (hsmf.mixed 5 1).continuousOn
  have hHaesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun z θ : ℝ =>
      ((Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
        + (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) / 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ =>
      ((Work.Spaces.DzIter 5 A p.1 p.2 * Work.Spaces.mixed 0 2 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
        + (Work.Spaces.mixed 5 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) / 2)
      ((hcontX2.pow 2).add (hcontZ2.pow 2) |>.div_const 2)
  have hptD : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |canonW (Work.Spaces.gam α) z θ * Work.Spaces.DzIter 5 A z θ
          * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.mixed 5 1 f z θ|
        ≤ ((Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ) ^ 2
          + (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) / 2 := by
    intro z θ hz0 hθ0 hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (canonW_nonneg hθI)]
    rw [hkey z θ hθI]
    exact hAM z θ hθI
  have hint := integrableConjuncts
    (F := fun z θ : ℝ => canonW (Work.Spaces.gam α) z θ * Work.Spaces.DzIter 5 A z θ
      * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.mixed 5 1 f z θ)
    (H := fun z θ : ℝ => ((Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
        * Work.Spaces.Wt α z θ) ^ 2 + (Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) / 2)
    hFcont hHaesm (fun θ => by rw [canonW_zero_z]; ring) hHsl hHmg hptD
  -- ## Cauchy–Schwarz for the two factors
  have hCS := cs_iterated (ρ := fun _ _ => (1 : ℝ))
    (A := fun z θ : ℝ => Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ)
    (B := fun z θ : ℝ => Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ)
    (fun _ _ _ _ => zero_le_one)
    (fun z hz => (hexc.1.1 z hz).congr (Filter.Eventually.of_forall (fun θ => by ring)))
    (fun z hz => (hZ2sl z hz).congr (Filter.Eventually.of_forall (fun θ => by ring)))
    (hexc.1.2.congr (Filter.Eventually.of_forall (fun z => by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring)))))
    (hZ2mg.congr (Filter.Eventually.of_forall (fun z => by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring)))))
  have hCSD' : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ|
      * |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ|)
      ≤ caseCofM Ce * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A * M
        * Work.Spaces.HkNorm α 6 f := by
    refine le_trans ?_ (mul_le_mul hsqX hsqZ (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg hCnn hαnn) hX6Ann) hMnn))
    simpa only [Work.Spaces.L2Sq, one_mul] using hCS
  -- ## the final bound
  refine ⟨hint.1, hint.2, ?_⟩
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ
        * Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
        * Work.Spaces.mixed 5 1 f z θ|
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW (Work.Spaces.gam α) z θ
          * |Work.Spaces.DzIter 5 A z θ| * |Work.Spaces.mixed 0 2 f z θ|
          * |Work.Spaces.mixed 5 1 f z θ| := by
        refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
        refine integral_Iz_mono_ae (fun z hz => ?_)
          (fun z hz => abs_nonneg _) hGmg
        refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
        refine integral_Iθ_mono_ae (fun θ hθ => ?_)
          (fun θ hθ => abs_nonneg _) (hGsl z (Set.mem_Ici.mpr hz.le))
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (canonW_nonneg (Set.Ioo_subset_Icc_self hθ))]
      _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ * Work.Spaces.Wt α z θ|
          * |Work.Spaces.mixed 5 1 f z θ * Work.Spaces.Wt α z θ| := by
        refine MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_))
        exact MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hkey z θ hθ))
      _ ≤ caseCofM Ce * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A * M
          * Work.Spaces.HkNorm α 6 f := hCSD'
      _ ≤ caseCofM Ce * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
        have h1 : caseCofM Ce * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A * M
              * Work.Spaces.HkNorm α 6 f
            = (caseCofM Ce * α ^ (-(1 / 2 : ℝ)))
              * (Work.Spaces.HkNorm α 6 A * M * Work.Spaces.HkNorm α 6 f) := by ring
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCnn hαnn)
        have hA' : Work.Spaces.HkNorm α 6 A * M * Work.Spaces.HkNorm α 6 f
            ≤ K6 * M * Work.Spaces.HkNorm α 6 f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn6 hMnn) hX6nn
        have hB' : K6 * M * Work.Spaces.HkNorm α 6 f
            ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
          have h1' : K6 ≤ K4 + K6 := by linarith
          have h2' : M ≤ 1 + M := by linarith
          have h3' : Work.Spaces.HkNorm α 6 f ≤ 1 + Work.Spaces.HkNorm α 6 f := by linarith
          calc K6 * M * Work.Spaces.HkNorm α 6 f
              ≤ (K4 + K6) * M * Work.Spaces.HkNorm α 6 f :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1' hMnn) hX6nn
            _ ≤ (K4 + K6) * (1 + M) * Work.Spaces.HkNorm α 6 f :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2' (by linarith)) hX6nn
            _ ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
                mul_le_mul_of_nonneg_left h3' (by positivity)
        have hC' : (0 : ℝ) ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_nonneg (by linarith) (by linarith)
        linarith

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.caseGe5Mine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem caseGe5Mine : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b i j : ℕ)
      (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ → i ≤ a → j ≤ b → ¬(i = 0 ∧ j = 0) →
      5 ≤ i + j → ¬(i = 0 ∧ ρ = Work.FTS.TransportS.leafGam α) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨Cm, hCmpos, hCmsup⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨Cm, hCmpos, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hia hjb hne h5 hexc
  obtain ⟨hsmA, hA4, hA6, hvalA, hn4, hn6⟩ := hcoef
  obtain ⟨hsmf, hf6, hf7, hvanish, haxis, hbdd⟩ := hdat
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hf4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmf 4 (by norm_num) hf6
  have hK0nn : 0 ≤ K0 := le_trans (abs_nonneg (A 1 (Real.pi / 4)))
    (hvalA 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos]))
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hn4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hn6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hSq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hCmnn : 0 ≤ Cm := hCmpos.le
  have hαnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  -- ## the canonical exponent carried by the leaf weight `ρ`
  have heta_gam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  have hgam_nn : 0 ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hcases : ∃ q : ℝ, ρ = canonW q ∧ 0 ≤ q ∧ q ≤ Work.Spaces.gam α
      ∧ (i = 0 → q ≤ Work.Spaces.eta) := by
    rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
    · refine ⟨Work.Spaces.eta, ?_, Work.Spaces.eta_pos.le, heta_gam, fun _ => le_rfl⟩
      rw [hρ]; exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.1
    · refine ⟨0, ?_, le_rfl, hgam_nn, fun _ => Work.Spaces.eta_pos.le⟩
      rw [hρ]; exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.1
    · refine ⟨Work.Spaces.gam α, ?_, hgam_nn, le_rfl, ?_⟩
      · rw [hρ]; exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.2 α
      · intro hi0
        exact absurd ⟨hi0, hρ⟩ hexc
  obtain ⟨q, rfl, hq0, hqγ, hqiη⟩ := hcases
  -- ## index bookkeeping
  have hge : 1 ≤ a - i + 1 := by omega
  have hle : a - i + 1 + (b - j) ≤ 6 := by omega
  have hqy2 : a - i + 1 + (b - j) ≤ 2 := by omega
  -- ## the pointwise (sup) bound on the second `f`-slot
  have hYsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| ≤ Cm * M := by
    intro z θ hz hθ0 hθ2
    refine le_trans
      (hCmsup α f hα0 hα1 hsmf hf4 (b - j) (a - i + 1) hge hqy2 z θ hz hθ0 hθ2) ?_
    exact mul_le_mul_of_nonneg_left hbdd hCmnn
  -- ## the level-`6` energy of the coefficient slot `X = D_z^j D_θ^i A`
  have hEX : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * (Work.Spaces.mixed j i A z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed j i A z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed j i A z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 A := by
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · have hqη : q ≤ Work.Spaces.eta := hqiη hi0
      rw [hi0, Work.Spaces.mixed_zero_right]
      exact canonW_energy_z6 hq0 hqη hsmA hA6 (by omega)
    · exact canonW_energy_mixed6 hα0 hq0 hqγ hsmA hA6 hipos (by omega)
  -- ## the level-`6` energy of the third `f`-slot `Z = D_z^b D_θ^a f`
  have hEZ : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha1
    · have hi0 : i = 0 := by omega
      have hqη : q ≤ Work.Spaces.eta := hqiη hi0
      rw [ha0, Work.Spaces.mixed_zero_right]
      exact canonW_energy_z6 hq0 hqη hsmf hf6 (by omega)
    · exact canonW_energy_mixed6 hα0 hq0 hqγ hsmf hf6 ha1 (by omega)
  -- ## iterated Cauchy–Schwarz on the coefficient slot and the third `f`-slot
  have hCS := cs_iterated (ρ := fun z θ => canonW q z θ)
    (A := fun z θ => Work.Spaces.mixed j i A z θ)
    (B := fun z θ => Work.Spaces.mixed b a f z θ)
    (fun z hz θ hθ => canonW_nonneg hθ) hEX.1 hEZ.1 hEX.2.1 hEZ.2.1
  have hCS' : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
      * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|)
      ≤ K6 * Work.Spaces.HkNorm α 6 f := by
    refine le_trans hCS ?_
    have h1 : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed j i A z θ) ^ 2) ≤ K6 :=
      le_trans (Real.sqrt_le_sqrt hEX.2.2) hn6
    have h2 : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkNorm α 6 f :=
      le_trans (Real.sqrt_le_sqrt hEZ.2.2) le_rfl
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) hK6nn
  -- ## the pointwise domination of the coefficient slot
  have hX6le : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Work.Spaces.mixed j i A z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
    intro z θ _ hθ0 hθ2
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · have hqη : q ≤ Work.Spaces.eta := hqiη hi0
      rw [hi0, Work.Spaces.mixed_zero_right]
      exact canonW_mul_z_le6 hq0 hqη (by omega) ⟨hθ0, hθ2⟩
    · exact canonW_mul_mixed_le6 hα0 hq0 hqγ hipos (by omega) ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  -- ## the pointwise domination of the third `f`-slot
  have hZle : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ _ hθ0 hθ2
    by_cases ha0 : a = 0
    · have hi0 : i = 0 := by omega
      have hqη : q ≤ Work.Spaces.eta := hqiη hi0
      rw [ha0, Work.Spaces.mixed_zero_right]
      exact canonW_mul_z_le6 hq0 hqη (by omega) ⟨hθ0, hθ2⟩
    · have ha1 : 1 ≤ a := by omega
      exact canonW_mul_mixed_le6 hα0 hq0 hqγ ha1 (by omega) ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  -- ## AM–GM for the weighted product of the two `L²`-slots
  have hXZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|
        ≤ Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hX2 := hX6le z θ hz hθ0 hθ2
    have hZ2 := hZle z θ hz hθ0 hθ2
    have hAM : 2 * (canonW q z θ * (|Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|))
        ≤ canonW q z θ * (Work.Spaces.mixed j i A z θ) ^ 2
          + canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      have h := two_mul_le_add_sq |Work.Spaces.mixed j i A z θ|
        |Work.Spaces.mixed b a f z θ|
      calc 2 * (canonW q z θ * (|Work.Spaces.mixed j i A z θ|
            * |Work.Spaces.mixed b a f z θ|))
          = canonW q z θ * (2 * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed b a f z θ|) := by ring
        _ ≤ canonW q z θ * (|Work.Spaces.mixed j i A z θ| ^ 2
              + |Work.Spaces.mixed b a f z θ| ^ 2) := mul_le_mul_of_nonneg_left h hcw
        _ = canonW q z θ * (Work.Spaces.mixed j i A z θ) ^ 2
              + canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
            rw [sq_abs, sq_abs]; ring
    have h2 : canonW q z θ * (|Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|)
        ≤ Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
      have hleft : 0 ≤ canonW q z θ * (|Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|) :=
        mul_nonneg hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      linarith [hAM, hX2, hZ2, hleft]
    calc canonW q z θ * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|
        = canonW q z θ * (|Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|) := by ring
      _ ≤ _ := h2
  -- ## the pointwise bound of the full integrand
  have hptC : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        ≤ (Cm * M) * (Work.Spaces.HkIntegrand α 6 A z θ
            + Work.Spaces.HkIntegrand α 6 f z θ) := by
    intro z θ hz hθ0 hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hXs := hYsup z θ hz hθ0 hθ2
    have hXZ' := hXZ z θ hz hθ0 hθ2
    have hcst : 0 ≤ Cm * M := mul_nonneg hCmnn hMnn
    have hleft : 0 ≤ canonW q z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed b a f z θ| :=
      mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)
    calc |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        = |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * (canonW q z θ
          * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
      _ ≤ (Cm * M) * (Work.Spaces.HkIntegrand α 6 A z θ
            + Work.Spaces.HkIntegrand α 6 f z θ) := mul_le_mul hXs hXZ' hleft hcst
  -- ## the marginal of the pointwise majorant
  have hmargH : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
      Work.Spaces.Iz :=
    (hA6.2.add hf6.2).congr_fun
      (fun z hz => (MeasureTheory.integral_add (hA6.1 z hz) (hf6.1 z hz)).symm)
      measurableSet_Ici
  have hmargH' : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Cm * M) * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
      Work.Spaces.Iz := by
    have h0 : MeasureTheory.IntegrableOn (fun z : ℝ => (Cm * M) *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)))
        Work.Spaces.Iz :=
      hmargH.const_mul (Cm * M)
    refine MeasureTheory.IntegrableOn.congr_fun h0 ?_ measurableSet_Ici
    intro z hz
    exact (MeasureTheory.integral_const_mul (Cm * M)
      (fun θ => Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)).symm
  -- ## the integrability conjuncts of the full integrand
  have hint : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz :=
    integrableConjuncts
      (F := fun z θ => canonW q z θ * Work.Spaces.mixed j i A z θ
        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ)
      (H := fun z θ => (Cm * M) * (Work.Spaces.HkIntegrand α 6 A z θ
        + Work.Spaces.HkIntegrand α 6 f z θ))
      ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (hsmA.mixed j i).continuousOn).mul
        (hsmf.mixed (b - j) (a - i + 1)).continuousOn).mul (hsmf.mixed b a).continuousOn)
      (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_const.mul
        ((hsmA.continuousOn_HkIntegrand α 6).add (hsmf.continuousOn_HkIntegrand α 6))))
      (fun θ => by rw [canonW_zero_z]; ring)
      (fun z hz => ((hA6.1 z hz).add (hf6.1 z hz)).const_mul _)
      hmargH' hptC
  -- ## the integrability of the absolute-value integrand
  have hGcont : ContinuousOn (Function.uncurry (fun z θ => canonW q z θ
      * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (hsmA.mixed j i).continuousOn.abs).mul (hsmf.mixed b a).continuousOn.abs)
  have hGboth : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|)
        Work.Spaces.Iz :=
    integrableConjuncts
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed b a f z θ|)
      (H := fun z θ => Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
      hGcont
      (Work.Spaces.aesm_of_continuousOn_Qd _
        ((hsmA.continuousOn_HkIntegrand α 6).add (hsmf.continuousOn_HkIntegrand α 6)))
      (fun θ => by rw [canonW_zero_z]; ring)
      (fun z hz => (hA6.1 z hz).add (hf6.1 z hz))
      hmargH
      (fun z θ hz hθ0 hθ2 => by
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _))
          (abs_nonneg _))]
        exact hXZ z θ hz hθ0 hθ2)
  -- ## the slicewise bound
  have hptC' : ∀ z ∈ Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, |canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|)
      ≤ (Cm * M) * (∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    rw [← MeasureTheory.integral_const_mul]
    refine integral_Iθ_mono_ae (fun θ hθ => ?_) (fun θ hθ => abs_nonneg _)
      ((hGboth.1 z hzIz).const_mul _)
    have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hXs := hYsup z θ hz hθ.1 hθ.2
    have hleft : 0 ≤ canonW q z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed b a f z θ| :=
      mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)
    calc |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        = |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * (canonW q z θ
          * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
      _ ≤ (Cm * M) * (canonW q z θ * |Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|) := mul_le_mul_of_nonneg_right hXs hleft
  -- ## the arithmetic at the target bracket
  have hbr : K6 * M * Work.Spaces.HkNorm α 6 f
      ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
    have h1 : (0 : ℝ) ≤ K4 + K6 := by linarith
    have hK6M : K6 * M ≤ (K4 + K6) * (1 + M) :=
      mul_le_mul (by linarith) (by linarith) hMnn h1
    have hstep : K6 * M * Work.Spaces.HkNorm α 6 f
        ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
      mul_le_mul hK6M (by linarith) hX6nn (by positivity)
    have hnn : (0 : ℝ) ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have htail : (Cm * M) * (K6 * Work.Spaces.HkNorm α 6 f)
      ≤ Cm * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
    have hnn2 : 0 ≤ K6 * M * Work.Spaces.HkNorm α 6 f :=
      mul_nonneg (mul_nonneg hK6nn hMnn) hX6nn
    have hα12 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_alpha_rpow_neg_half hα0 hα1
    calc (Cm * M) * (K6 * Work.Spaces.HkNorm α 6 f)
        = Cm * (K6 * M * Work.Spaces.HkNorm α 6 f) := by ring
      _ ≤ Cm * (α ^ (-(1 / 2 : ℝ)) * (K6 * M * Work.Spaces.HkNorm α 6 f)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnn2 hα12) hCmnn
      _ = Cm * α ^ (-(1 / 2 : ℝ)) * (K6 * M * Work.Spaces.HkNorm α 6 f) := by ring
      _ ≤ Cm * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
          mul_le_mul_of_nonneg_left hbr (mul_nonneg hCmnn hαnn)
  -- ## assembly
  refine ⟨hint.1, hint.2, ?_⟩
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, (Cm * M) * (∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) := by
        refine integral_Iz_mono_ae (fun z hz => ?_) (fun z hz => abs_nonneg _)
          (hGboth.2.const_mul _)
        exact le_trans MeasureTheory.abs_integral_le_integral_abs (hptC' z hz)
    _ = (Cm * M) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (Cm * M) * (K6 * Work.Spaces.HkNorm α 6 f) :=
        mul_le_mul_of_nonneg_left hCS' (mul_nonneg hCmnn hMnn)
    _ ≤ Cm * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := htail

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
end
end
