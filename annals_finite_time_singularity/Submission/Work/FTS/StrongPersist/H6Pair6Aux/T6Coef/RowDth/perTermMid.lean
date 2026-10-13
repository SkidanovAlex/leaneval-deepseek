/-
# The middle slots `3 ≤ i + j ≤ 4` of the `D_θ`-row per-term estimate

The coefficient slot `X = D_z^jD_θ^iA` is bounded *pointwise* by the level-`6` norm of `A`
(`N6.PwAny6`), and the two `f`-slots are paired by the iterated Cauchy–Schwarz
`RowDth.cs_iterated`: the middle slot `D_z^{b-j}D_θ^{a-i+1}f` carries `a - i + 1 ≥ 1` angular
derivatives, hence is a *mixed* slot of order `≤ 4` and can be priced at level `4`
(`RowDth.canonW_energy_mixed4`), while the last slot `D_z^bD_θ^af` is priced at level `6`
(`T1SixAux.slotEnergyZOuter`).  The integrability conjuncts come from
`RowDth.integrableConjuncts`, with the level-`6` integrand of `f` as the majorant.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.CS
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Integ
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SlicePrep
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.Galerkin (Fn)
open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- From `u² ≤ c²v²`, `0 ≤ c`, `0 ≤ v` conclude `|u| ≤ c v`. -/
theorem abs_le_of_sq_le_nn' {u c v : ℝ} (h : u ^ 2 ≤ c ^ 2 * v ^ 2) (hc : 0 ≤ c)
    (hv : 0 ≤ v) : |u| ≤ c * v := by
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg hc hv)
  rw [mul_pow]
  exact h

theorem caseTo4Mine : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b i j : ℕ)
      (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ → i ≤ a → j ≤ b → ¬(i = 0 ∧ j = 0) →
      3 ≤ i + j → i + j ≤ 4 →
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
  obtain ⟨Cp, hCppos, hCp⟩ := Work.FTS.StrongPersist.N6.PwAny6
  set CB : ℝ := Real.sqrt (Cp * 10) + 1 with hCBdef
  have hCBpos : 0 < CB := by rw [hCBdef]; positivity
  refine ⟨CB, hCBpos, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hia hjb hne h3 h4
  obtain ⟨hsmA, hA4, hA6, hvalA, hn4, hn6⟩ := hcoef
  obtain ⟨hsmf, hf6, hf7, hvanish, haxis, hbdd⟩ := hdat
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hf4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmf 4 (by norm_num) hf6
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hn4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hn6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hSq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hK0nn : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 (Real.pi / 4)))
      (hvalA 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos]))
  have hCBnn : 0 ≤ CB := hCBpos.le
  have hαnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  obtain ⟨q, rfl, hq0, hqγ, hqη⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.leafW_canon_cases hα0 hleaf
  -- ## index bookkeeping
  have hge : 1 ≤ a - i + 1 := by omega
  have hY6le : (a - i + 1) + (b - j) ≤ 6 := by omega
  have hY4le : (a - i + 1) + (b - j) ≤ 4 := by omega
  -- ## the level-`6` dominations of the two `f`-slots
  have hY6 : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z θ hθ0 hθ1 => canonW_mul_mixed_le6 hα0 hq0 hqγ hge hY6le ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hZ6 : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z θ hθ0 hθ1 =>
      Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f a b hqγ hqη hab ⟨hθ0, hθ1⟩
  have hYZ : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → canonW q z θ
      * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hθ0 hθ1
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have h := two_mul_le_add_sq |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
      |Work.Spaces.mixed b a f z θ|
    rw [sq_abs, sq_abs] at h
    nlinarith [h, hcw, hY6 z θ hθ0 hθ1, hZ6 z θ hθ0 hθ1]
  -- ## the sup bound on the coefficient slot
  have hXsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A := by
    intro z θ hz hθ0 hθ1
    have h := hCp α A j i hα0 hα1 hsmA hA6 (by omega) z hz θ ⟨hθ0, hθ1⟩
    have hfac : Cp / (Work.Spaces.gam α - 1) ≤ (CB * α ^ (-(1 / 2 : ℝ))) ^ 2 := by
      have hfac1 : Cp / (Work.Spaces.gam α - 1) = Cp * 10 * α⁻¹ := by
        rw [Work.Spaces.gam_sub_one]
        field_simp
      have hsq : Cp * 10 ≤ CB ^ 2 := by
        rw [hCBdef]
        have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ Cp * 10 by positivity)
        nlinarith [Real.sqrt_nonneg (Cp * 10)]
      have hhalf : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
        rw [sq, ← Real.rpow_add hα0, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num,
          Real.rpow_neg_one]
      rw [hfac1, mul_pow, hhalf]
      exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hα0.le)
    have h2 : (Work.Spaces.mixed j i A z θ) ^ 2
        ≤ (CB * α ^ (-(1 / 2 : ℝ))) ^ 2 * (Work.Spaces.HkNorm α 6 A) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 A)]
      exact le_trans h (mul_le_mul_of_nonneg_right hfac (Work.Spaces.HkSq_nonneg α 6 A))
    exact abs_le_of_sq_le_nn' h2 (mul_nonneg hCBnn hαnn)
      (Work.Spaces.HkNorm_nonneg α 6 A)
  -- ## the pointwise bound on the full integrand
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        ≤ (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
            * Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ1
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hXs := hXsup z θ hz hθ0 hθ1
    have hYZ' := hYZ z θ hθ0 hθ1
    have hleft : 0 ≤ canonW q z θ
        * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
      mul_nonneg hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcst : 0 ≤ CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A :=
      mul_nonneg (mul_nonneg hCBnn hαnn) (Work.Spaces.HkNorm_nonneg α 6 A)
    calc |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        = |Work.Spaces.mixed j i A z θ| * (canonW q z θ
          * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
      _ ≤ (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
            * Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul hXs hYZ' hleft hcst
  -- ## integrability of the full integrand
  have hFcont : ContinuousOn (Function.uncurry (fun z θ => canonW q z θ
      * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
      * Work.Spaces.mixed b a f z θ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (hsmA.mixed j i).continuousOn).mul
      (hsmf.mixed (b - j) (a - i + 1)).continuousOn).mul (hsmf.mixed b a).continuousOn
  have hmargH : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
        * Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iz := by
    rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
            * Work.Spaces.HkIntegrand α 6 f z θ)
        = fun z => (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ from
          funext (fun z => MeasureTheory.integral_const_mul _ _)]
    exact hf6.2.const_mul _
  have hinter := integrableConjuncts
    (F := fun z θ => canonW q z θ * Work.Spaces.mixed j i A z θ
      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ)
    (H := fun z θ => (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
      * Work.Spaces.HkIntegrand α 6 f z θ)
    hFcont
    (Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_const.mul (hsmf.continuousOn_HkIntegrand α 6)))
    (fun θ => by rw [canonW_zero_z]; ring)
    (fun z hz => (hf6.1 z hz).const_mul _)
    hmargH
    hpt
  -- ## the level-`4` energy of the middle slot and the level-`6` energy of the last slot
  have hEY4 := canonW_energy_mixed4 hα0 hq0 hqγ hsmf hf4 hge hY4le
  have hZsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
      * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.StrongPersist.N6Trans.T1SixAux.slotSliceIntegrable α q hsmf hf6
      hqγ hqη hab hz
  have hZen := Work.FTS.StrongPersist.N6Trans.T1SixAux.slotEnergyZOuter α q hsmf hf6
    hq0 hqγ hqη hab
  -- ## the iterated Cauchy–Schwarz on the two `f`-slots
  have hCS := cs_iterated (ρ := fun z θ => canonW q z θ)
    (A := fun z θ => Work.Spaces.mixed (b - j) (a - i + 1) f z θ)
    (B := fun z θ => Work.Spaces.mixed b a f z θ)
    (fun z hz θ hθ => canonW_nonneg hθ) hEY4.1 hZsl hEY4.2.1 hZen.1
  have hCS' : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
      * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
    refine le_trans hCS ?_
    have h1 : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2) ≤ Work.Spaces.HkNorm α 4 f :=
      le_trans (Real.sqrt_le_sqrt hEY4.2.2) le_rfl
    have h2 : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkNorm α 6 f :=
      le_trans (Real.sqrt_le_sqrt hZen.2) le_rfl
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Work.Spaces.HkNorm_nonneg α 4 f)
  -- ## slice and marginal integrability of `ρ|Y||Z|`
  have hYZcont : ContinuousOn (Function.uncurry (fun z θ => canonW q z θ
      * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (hsmf.mixed (b - j) (a - i + 1)).continuousOn.abs).mul
      (hsmf.mixed b a).continuousOn.abs)
  have hYZi : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
        Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|)
        Work.Spaces.Iz :=
    integrableConjuncts
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
        * |Work.Spaces.mixed b a f z θ|)
      (H := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
      hYZcont
      (Work.Spaces.aesm_of_continuousOn_Qd _ (hsmf.continuousOn_HkIntegrand α 6))
      (fun θ => by rw [canonW_zero_z]; ring)
      (fun z hz => hf6.1 z hz)
      hf6.2
      (fun z θ hz hθ0 hθ1 => by
        have hcw : 0 ≤ canonW q z θ := canonW_nonneg ⟨le_of_lt hθ0, le_of_lt hθ1⟩
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)), mul_assoc]
        exact hYZ z θ hθ0 hθ1)
  -- ## the value bound
  have hKxnn : 0 ≤ CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A :=
    mul_nonneg (mul_nonneg hCBnn hαnn) (Work.Spaces.HkNorm_nonneg α 6 A)
  refine ⟨hinter.1, hinter.2, ?_⟩
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
        * (∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) := by
        refine integral_Iz_mono_ae (fun z hz => ?_) (fun z hz => abs_nonneg _)
          (hYZi.2.const_mul _)
        refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
        rw [← MeasureTheory.integral_const_mul]
        refine integral_Iθ_mono_ae (fun θ hθ => ?_) (fun θ hθ => abs_nonneg _)
          ((hYZi.1 z (Set.mem_Ici.mpr hz.le)).const_mul _)
        have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
        have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
        have hXs := hXsup z θ (Set.mem_Ioi.mp hz) hθ.1 hθ.2
        have hleft : 0 ≤ canonW q z θ
            * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
          mul_nonneg hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        calc |canonW q z θ * Work.Spaces.mixed j i A z θ
              * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
              * Work.Spaces.mixed b a f z θ|
            = |Work.Spaces.mixed j i A z θ| * (canonW q z θ
              * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
          _ ≤ (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
              * (canonW q z θ * (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|)) :=
              mul_le_mul_of_nonneg_right hXs hleft
          _ = (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
              * (canonW q z θ * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|) := by ring
    _ = (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
        * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
          * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
        * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) :=
        mul_le_mul_of_nonneg_left hCS' hKxnn
    _ ≤ CB * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
        have hx6le : Work.Spaces.HkNorm α 6 A ≤ K6 := hn6
        have hh4 : Work.Spaces.HkNorm α 4 f ≤ M := hbdd
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
        have hnn2 : 0 ≤ K6 * M * Work.Spaces.HkNorm α 6 f :=
          mul_nonneg (mul_nonneg hK6nn hMnn) hX6nn
        have hmid : Work.Spaces.HkNorm α 6 A * (Work.Spaces.HkNorm α 4 f
              * Work.Spaces.HkNorm α 6 f) ≤ K6 * M * Work.Spaces.HkNorm α 6 f := by
          calc Work.Spaces.HkNorm α 6 A * (Work.Spaces.HkNorm α 4 f
                * Work.Spaces.HkNorm α 6 f)
              ≤ K6 * (M * Work.Spaces.HkNorm α 6 f) :=
                mul_le_mul hx6le (mul_le_mul_of_nonneg_right hh4 hX6nn)
                  (mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) hX6nn) hK6nn
            _ = K6 * M * Work.Spaces.HkNorm α 6 f := by ring
        calc (CB * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 A)
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
            = CB * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.HkNorm α 6 A
                * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)) := by ring
          _ ≤ CB * α ^ (-(1 / 2 : ℝ)) * (K6 * M * Work.Spaces.HkNorm α 6 f) :=
              mul_le_mul_of_nonneg_left (hmid.trans le_rfl)
                (mul_nonneg hCBnn hαnn)
          _ ≤ CB * α ^ (-(1 / 2 : ℝ))
                * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                   + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
              mul_le_mul_of_nonneg_left hbr (mul_nonneg hCBnn hαnn)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
