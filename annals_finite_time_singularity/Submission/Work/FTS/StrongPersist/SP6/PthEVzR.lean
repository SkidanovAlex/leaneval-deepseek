import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyA
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option quotPrecheck false in
local notation "PMq" => (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ)


/-- **The case `b₁ ≤ 4` of `leafGamPureZ`.** -/
theorem leafGamPureZ_le4 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a₁ = 0 → 1 ≤ a → a₁ ≤ a → b₁ ≤ b → 3 ≤ a₁ + b₁ → a + b ≤ 6 → b₁ ≤ 4 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨10 * C₁ + 2, by positivity, ?_⟩
  intro α hα A f K0 K4 K6 M a b a₁ b₁ hCoef hDat ha₁ ha hle hb₁b h3 hab hb₁4
  subst ha₁
  simp only [Nat.sub_zero]
  obtain ⟨hα0, hα1⟩ := hα
  have hsmA : Work.FTS.EllipticEst.SmoothOpen A := hCoef.sm
  have hmemA6 : Work.Spaces.HkMem α 6 A := hCoef.h6
  have hnA6 : Work.Spaces.HkNorm α 6 A ≤ K6 := hCoef.n6
  have hsmF : Work.FTS.EllipticEst.SmoothOpen f := hDat.sm
  have hmemF6 : Work.Spaces.HkMem α 6 f := hDat.h6
  have hbddF : Work.FTS.Nonlin.Xn α f ≤ M := hDat.bdd
  have h4f : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmF 4 (by norm_num) hmemF6
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hnA6
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hCoef.n4
  have hN6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbddF
  have hK0nn : 0 ≤ K0 := by
    have h := hCoef.val 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    exact le_trans (abs_nonneg _) h
  have hsub4 : a + (b - b₁) ≤ 4 := by omega
  have hleaf : Work.FTS.TransportS.IsLeafW α a (Work.FTS.TransportS.leafGam α) :=
    Or.inr (Or.inr ⟨ha, rfl⟩)
  -- the pointwise bound for the coefficient slot
  have hXpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ 0 A z θ| ≤ Real.sqrt (10 * C₁ / α) * K6 := by
    intro z θ hz hθ hθ2
    have hp := hC₁ α A b₁ 0 hα0 hα1 hsmA hmemA6 (by omega : 0 + b₁ ≤ 4) z hz θ ⟨hθ, hθ2⟩
    have hgam : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
    have hden : 0 < Work.Spaces.gam α - 1 := by rw [hgam]; linarith
    have hK6sq : Work.Spaces.HkSq α 6 A = (Work.Spaces.HkNorm α 6 A) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 A)]
    have hstep : (Work.Spaces.mixed b₁ 0 A z θ) ^ 2 ≤ (10 * C₁ / α) * K6 ^ 2 := by
      rw [hK6sq] at hp
      have hcoef : 0 ≤ C₁ / (Work.Spaces.gam α - 1) := div_nonneg hC₁pos.le hden.le
      have h1 : C₁ / (Work.Spaces.gam α - 1) * (Work.Spaces.HkNorm α 6 A) ^ 2
          ≤ C₁ / (Work.Spaces.gam α - 1) * K6 ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 A) hnA6 2) hcoef
      have hcoefeq : C₁ / (Work.Spaces.gam α - 1) = 10 * C₁ / α := by
        rw [hgam, div_eq_mul_inv, inv_div]
        ring
      calc (Work.Spaces.mixed b₁ 0 A z θ) ^ 2
          ≤ C₁ / (Work.Spaces.gam α - 1) * (Work.Spaces.HkNorm α 6 A) ^ 2 := hp
        _ ≤ C₁ / (Work.Spaces.gam α - 1) * K6 ^ 2 := h1
        _ = (10 * C₁ / α) * K6 ^ 2 := by rw [hcoefeq]
    calc |Work.Spaces.mixed b₁ 0 A z θ|
        = Real.sqrt ((Work.Spaces.mixed b₁ 0 A z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((10 * C₁ / α) * K6 ^ 2) := Real.sqrt_le_sqrt hstep
      _ = Real.sqrt (10 * C₁ / α) * K6 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg hK6nn]
  -- the numerical bound for `√(10 C₁/α)`
  have hsqrt_le : Real.sqrt (10 * C₁ / α) ≤ (10 * C₁ + 1) * α ^ (-(3 : ℝ)) := by
    have h1 : Real.sqrt (10 * C₁ / α) ≤ 10 * C₁ / α + 1 := by
      have h2 : (10 * C₁ / α) = (Real.sqrt (10 * C₁ / α)) ^ 2 :=
        (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 10 * C₁ / α)).symm
      nlinarith [Real.sqrt_nonneg (10 * C₁ / α), h2]
    have h4 : 10 * C₁ / α = 10 * C₁ * α⁻¹ := by ring
    have h5 : α⁻¹ ≤ α ^ (-(3 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1
        (show -(3 : ℝ) ≤ -(1 : ℝ) by norm_num)
      have hh : α ^ (-(1 : ℝ)) = α⁻¹ := by rw [Real.rpow_neg hα0.le, Real.rpow_one]
      rwa [hh] at h
    have h6 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(3 : ℝ) ≤ 0 by norm_num)
      rwa [Real.rpow_zero] at h
    have h7 : 10 * C₁ * α⁻¹ ≤ 10 * C₁ * α ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have h8 : 10 * C₁ / α + 1 ≤ 10 * C₁ * α ^ (-(3 : ℝ)) + α ^ (-(3 : ℝ)) := by
      rw [h4]; linarith
    have h9 : 10 * C₁ * α ^ (-(3 : ℝ)) + α ^ (-(3 : ℝ))
        = (10 * C₁ + 1) * α ^ (-(3 : ℝ)) := by ring
    linarith
  -- the two slot bounds
  have hslotY := leafGamPureZ_mixedSlotLe (α := α) hα0 (k := 4) hsmF h4f (j := b - b₁) (i := a) ha
    (by omega)
  have hslotZ := leafGamPureZ_mixedSlotLe (α := α) hα0 (k := 6) hsmF hmemF6 (j := b) (i := a) ha hab
  -- the leaf weight is nonnegative a.e.
  have hρ : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 ≤ Work.FTS.TransportS.leafGam α p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    exact Work.FTS.TransportS.leafGam_nonneg α
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])))
  -- the matched-weight Cauchy–Schwarz
  have hpair : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
        * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
        * |Work.Spaces.mixed b a f p.1 p.2|
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
    have hcs := leafGamPureZ_cs (ρ := fun z θ => Work.FTS.TransportS.leafGam α z θ)
      (A := Work.Spaces.mixed (b - b₁) a f) (B := Work.Spaces.mixed b a f)
      hρ hslotY.1 hslotZ.1
      (Work.Spaces.aesm_of_continuousOn_Qd _ ((hsmF.mixed (b - b₁) a).continuousOn))
      (Work.Spaces.aesm_of_continuousOn_Qd _ ((hsmF.mixed b a).continuousOn))
      (Work.Spaces.aesm_of_continuousOn_Qd _
        (Real.continuous_sqrt.comp_continuousOn (leafGamPureZ_cont α)))
    calc (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
          * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ Real.sqrt (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
              * (Work.Spaces.mixed (b - b₁) a f p.1 p.2) ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          * Real.sqrt (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
              * (Work.Spaces.mixed b a f p.1 p.2) ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := hcs
      _ ≤ Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 6 f) :=
          mul_le_mul (Real.sqrt_le_sqrt hslotY.2) (Real.sqrt_le_sqrt hslotZ.2)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := rfl
  -- integrability of `√I₄·√I₆`
  have haesm4 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsmF h4f).1.aestronglyMeasurable
  have haesm6 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsmF hmemF6).1.aestronglyMeasurable
  have hLP4 : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f p.1 p.2)) 2
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm4).mpr
      ((Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsmF h4f).1.congr
        (Filter.Eventually.of_forall (fun p =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 f p.1 p.2)).symm)))
  have hLP6 : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2)) 2
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm6).mpr
      ((Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsmF hmemF6).1.congr
        (Filter.Eventually.of_forall (fun p =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 6 f p.1 p.2)).symm)))
  have hmaj2_int : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Real.sqrt (Work.Spaces.HkIntegrand α 4 f p.1 p.2)
        * Real.sqrt (Work.Spaces.HkIntegrand α 6 f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.memLp_one_iff_integrable.mp (hLP4.mul hLP6)
  -- integrability of the majorant `leafGam |Y| |Z|`
  have hmaj_int : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
        * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
        * |Work.Spaces.mixed b a f p.1 p.2|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine hmaj2_int.mono' ?_ ?_
    · exact Work.Spaces.aesm_of_continuousOn_Qd _
        (((leafGamPureZ_cont α).mul
          ((hsmF.mixed (b - b₁) a).continuousOn.abs)).mul
          ((hsmF.mixed b a).continuousOn.abs))
    · refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
      have hPt : Work.FTS.TransportS.leafGam α z θ
          * |Work.Spaces.mixed (b - b₁) a f z θ| * |Work.Spaces.mixed b a f z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) :=
        Work.FTS.StrongPersist.H6Pair6Aux.leaf_prod_sqrt_le
          (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg_Iθ hleaf z θ hθI)
          (Work.FTS.StrongPersist.H6Pair6Aux.leaf_sq_le4 hα0 hleaf hsub4 hz ⟨hθ0, hθ1⟩)
          (Work.FTS.StrongPersist.H6Pair6Aux.leaf_sq_le6 hα0 hleaf hab hz ⟨hθ0, hθ1⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
        (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg_Iθ hleaf z θ hθI)
        (abs_nonneg _)) (abs_nonneg _))]
      exact hPt
  -- the integrand and its pointwise majorant
  set F : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ 0 A p.1 p.2
      * Work.Spaces.mixed (b - b₁) a f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 with hFdef
  have hFaesm : MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hFdef]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    exact (((leafGamPureZ_cont α).mul ((hsmA.mixed b₁ 0).continuousOn)).mul
      ((hsmF.mixed (b - b₁) a).continuousOn)).mul ((hsmF.mixed b a).continuousOn)
  have hpt : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      |F p| ≤ (Real.sqrt (10 * C₁ / α) * K6) * (Work.FTS.TransportS.leafGam α p.1 p.2
        * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
        * |Work.Spaces.mixed b a f p.1 p.2|) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hρ0 : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
    have hFp : |F (z, θ)| = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (|Work.Spaces.mixed b₁ 0 A z θ|
          * (|Work.Spaces.mixed (b - b₁) a f z θ|
            * |Work.Spaces.mixed b a f z θ|)) := by
      rw [hFdef]
      simp only [Work.FTS.TransportS.leafGam]
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (Real.rpow_nonneg hs.le _)]
      ring
    rw [hFp]
    have hb := hXpt z θ hz hθ0 hθ1
    have hkey : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed b₁ 0 A z θ|
            * (|Work.Spaces.mixed (b - b₁) a f z θ|
              * |Work.Spaces.mixed b a f z θ|))
        ≤ (Real.sqrt (10 * C₁ / α) * K6)
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed (b - b₁) a f z θ|
              * |Work.Spaces.mixed b a f z θ|)) := by
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed (b - b₁) a f z θ|
            * |Work.Spaces.mixed b a f z θ|) :=
        mul_nonneg hρ0 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (|Work.Spaces.mixed b₁ 0 A z θ|
              * (|Work.Spaces.mixed (b - b₁) a f z θ|
                * |Work.Spaces.mixed b a f z θ|))
          = ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) a f z θ|
                * |Work.Spaces.mixed b a f z θ|)) * |Work.Spaces.mixed b₁ 0 A z θ| := by ring
        _ ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) a f z θ|
                * |Work.Spaces.mixed b a f z θ|))
            * (Real.sqrt (10 * C₁ / α) * K6) := mul_le_mul_of_nonneg_left hb hnn
        _ = (Real.sqrt (10 * C₁ / α) * K6)
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) a f z θ|
                * |Work.Spaces.mixed b a f z θ|)) := by ring
    have hshape : (Real.sqrt (10 * C₁ / α) * K6)
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed (b - b₁) a f z θ|
            * |Work.Spaces.mixed b a f z θ|))
        = (Real.sqrt (10 * C₁ / α) * K6)
          * (Work.FTS.TransportS.leafGam α z θ
            * |Work.Spaces.mixed (b - b₁) a f z θ|
            * |Work.Spaces.mixed b a f z θ|) := by
      simp only [Work.FTS.TransportS.leafGam]
      ring
    exact hkey.trans_eq hshape
  have hF_int : MeasureTheory.Integrable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.Integrable.mono' (hmaj_int.const_mul (Real.sqrt (10 * C₁ / α) * K6))
      hFaesm ?_
    filter_upwards [hpt] with p hp
    rwa [Real.norm_eq_abs]
  have hbound : |∫ p, F p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ (Real.sqrt (10 * C₁ / α) * K6)
        * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := by
    calc |∫ p, F p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ ∫ p, ‖F p‖ ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
            MeasureTheory.norm_integral_le_integral_norm F
      _ ≤ ∫ p, (Real.sqrt (10 * C₁ / α) * K6) * (Work.FTS.TransportS.leafGam α p.1 p.2
            * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
            * |Work.Spaces.mixed b a f p.1 p.2|)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun p => norm_nonneg _))
            (hmaj_int.const_mul (Real.sqrt (10 * C₁ / α) * K6)) hpt
      _ = (Real.sqrt (10 * C₁ / α) * K6)
          * ∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * |Work.Spaces.mixed (b - b₁) a f p.1 p.2|
            * |Work.Spaces.mixed b a f p.1 p.2|
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (Real.sqrt (10 * C₁ / α) * K6)
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hpair (by positivity)
  have hfinal : (Real.sqrt (10 * C₁ / α) * K6)
      * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
      ≤ (10 * C₁ + 2) * α ^ (-(3 : ℝ))
        * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
           + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
    have hB : Work.Spaces.HkNorm α 4 f ≤ M := hbddF
    have hC : K6 * (M * Work.Spaces.HkNorm α 6 f)
        ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
          + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
      have h1 : K6 * (M * Work.Spaces.HkNorm α 6 f)
          ≤ (K4 + K6) * ((1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
        have hM1 : M ≤ 1 + M := by linarith
        have hN1 : Work.Spaces.HkNorm α 6 f ≤ 1 + Work.Spaces.HkNorm α 6 f := by linarith
        have hK : K6 ≤ K4 + K6 := by linarith
        have hMN : M * Work.Spaces.HkNorm α 6 f
            ≤ (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
          mul_le_mul hM1 hN1 hN6nn (by linarith)
        calc K6 * (M * Work.Spaces.HkNorm α 6 f)
            ≤ K6 * ((1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
              mul_le_mul_of_nonneg_left hMN hK6nn
          _ ≤ (K4 + K6) * ((1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
              mul_le_mul_of_nonneg_right hK (by positivity)
      have h3 : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
        mul_nonneg (by linarith) (by linarith [Work.Spaces.HkSq_nonneg α 6 f])
      nlinarith [h1, h3]
    have hstep1 : Real.sqrt (10 * C₁ / α) * K6
        * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
        ≤ ((10 * C₁ + 1) * α ^ (-(3 : ℝ))) * K6 * (M * Work.Spaces.HkNorm α 6 f) := by
      have h1 : Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
          ≤ M * Work.Spaces.HkNorm α 6 f :=
        mul_le_mul_of_nonneg_right hB hN6nn
      have h4 : Real.sqrt (10 * C₁ / α) * K6
          ≤ ((10 * C₁ + 1) * α ^ (-(3 : ℝ))) * K6 :=
        mul_le_mul_of_nonneg_right hsqrt_le hK6nn
      have h5 : 0 ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f :=
        mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkNorm_nonneg α 6 f)
      have h6 : 0 ≤ ((10 * C₁ + 1) * α ^ (-(3 : ℝ))) * K6 := by positivity
      exact mul_le_mul h4 h1 h5 h6
    have hstep2 : ((10 * C₁ + 1) * α ^ (-(3 : ℝ))) * K6 * (M * Work.Spaces.HkNorm α 6 f)
        = ((10 * C₁ + 1) * α ^ (-(3 : ℝ))) * (K6 * (M * Work.Spaces.HkNorm α 6 f)) := by
      ring
    have hstep3 : 0 ≤ (10 * C₁ + 1) * α ^ (-(3 : ℝ)) := by positivity
    have hstep4 : (0 : ℝ) ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
      have h3 : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
        mul_nonneg (by linarith) (by linarith [Work.Spaces.HkSq_nonneg α 6 f])
      have h4 : 0 ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    calc Real.sqrt (10 * C₁ / α) * K6
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
        ≤ ((10 * C₁ + 1) * α ^ (-(3 : ℝ))) * K6 * (M * Work.Spaces.HkNorm α 6 f) := hstep1
      _ = ((10 * C₁ + 1) * α ^ (-(3 : ℝ))) * (K6 * (M * Work.Spaces.HkNorm α 6 f)) := hstep2
      _ ≤ ((10 * C₁ + 1) * α ^ (-(3 : ℝ)))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
          mul_le_mul_of_nonneg_left hC hstep3
      _ ≤ (10 * C₁ + 2) * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
          have h5 : (10 * C₁ + 1) * α ^ (-(3 : ℝ))
              ≤ (10 * C₁ + 2) * α ^ (-(3 : ℝ)) := by
            have : (0 : ℝ) ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα0.le _
            nlinarith
          exact mul_le_mul_of_nonneg_right h5 hstep4
  exact ⟨hF_int, hbound.trans hfinal⟩
end
end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# Auxiliary lemmas for the `b = 5` crux of `T6CoefAux/mismatchCaseHard`

The elementary `sin(2θ)`-power identities, the `η`-slot weight domination, the `z`-marginal of
the pure-`z` slot `D_z⁵f` at the `η`-weight, and the slice Agmon bound for `D_z⁵f`
(the `H2.T1Q.SliceSupOpen` instance).
-/
namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000


/-- `sin(2θ)^{-γ} · sin(2θ) = sin(2θ)^{1-γ}` at an interior angle. -/
theorem mh_neg_gam_mul {γ s : ℝ} (hs : 0 < s) : s ^ (-γ) * s = s ^ (1 - γ) := by
  have h := Real.rpow_add hs (-γ) (1 : ℝ)
  rw [Real.rpow_one] at h
  rw [← h]
  congr 1
  ring

/-- `sin(2θ)^{1-γ} · sin(2θ) = sin(2θ)^{2-γ}` at an interior angle. -/
theorem mh_one_sub_gam_mul {γ s : ℝ} (hs : 0 < s) : s ^ (1 - γ) * s = s ^ (2 - γ) := by
  have h := Real.rpow_add hs (1 - γ) (1 : ℝ)
  rw [Real.rpow_one] at h
  rw [← h]
  congr 1
  ring

/-- `sin(2θ)^{-γ} · sin(2θ)² = sin(2θ)^{2-γ}` at an interior angle. -/
theorem mh_neg_gam_mul_sq {γ s : ℝ} (hs : 0 < s) : s ^ (-γ) * s ^ (2 : ℕ) = s ^ (2 - γ) := by
  have h : s ^ (-γ) * s ^ (2 : ℕ) = s ^ (-γ) * (s * s) := by ring
  rw [h, ← mul_assoc, mh_neg_gam_mul hs, mh_one_sub_gam_mul hs]

/-- `sin(2θ)² · sin(2θ)^{-γ} = sin(2θ)^{2-γ}` at an interior angle. -/
theorem mh_sq_mul_neg_gam {γ s : ℝ} (hs : 0 < s) : s ^ (2 : ℕ) * s ^ (-γ) = s ^ (2 - γ) := by
  rw [mul_comm, mh_neg_gam_mul_sq hs]

/-- `w(z)² X² ≤ (X·(w z / sin(2θ)^{η/2}))²` for `z > 0`, `0 < θ < π/2` (the `ℋ⁶`-slot weight
`w/σ^{η/2}` dominates `w` because `w ≥ 1` and `σ ≤ 1`). -/
theorem mh_w_le_slotWeight {z θ X : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.w z) ^ 2 * X ^ 2
      ≤ (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : 1 ≤ Work.Spaces.w z := Work.FTS.TransportS.one_le_w hz
  have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw
  have hση : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hσ.le (Real.sin_le_one _) Work.Spaces.eta_nonneg
  have hpos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := Real.rpow_pos_of_pos hσ _
  have hinv : 1 ≤ ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹ := (one_le_inv₀ hpos).mpr hση
  have hp : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [show ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ ((2 : ℕ) : ℝ) from
      (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hσ.le]
    norm_num
  calc (Work.Spaces.w z) ^ 2 * X ^ 2 = X ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ X ^ 2 * ((Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (sq_nonneg _) hinv) (sq_nonneg X)
    _ = (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow, div_pow, div_eq_mul_inv, hp]

/-- `X² ≤ (X·(w z / sin(2θ)^{η/2}))²` for `z > 0`, `0 < θ < π/2` (the weight factor is `≥ 1`). -/
theorem mh_le_slotWeight {z θ X : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    X ^ 2 ≤ (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : 1 ≤ Work.Spaces.w z := Work.FTS.TransportS.one_le_w hz
  have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw
  have hση : (Real.sin (2 * θ)) ^ (Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hσ.le (Real.sin_le_one _) Work.Spaces.eta_nonneg
  have hpos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := Real.rpow_pos_of_pos hσ _
  have hinv : 1 ≤ ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹ := (one_le_inv₀ hpos).mpr hση
  have hp : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [show ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ ((2 : ℕ) : ℝ) from
      (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hσ.le]
    norm_num
  have hkey : (1 : ℝ) ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, div_eq_mul_inv, hp]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta))⁻¹ :=
          mul_le_mul hw2 hinv (by norm_num) (sq_nonneg _)
  calc X ^ 2 = X ^ 2 * 1 := by ring
    _ ≤ X ^ 2 * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg X)
    _ = (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow]

/-- **The pure-`z` slot `D_z⁵f` at the `η`-weight, sliced in `z`.**  For `f` of class
`SmoothOpen` with honest `HkMem α 6 f`, `∫_z w(z)² ∫_θ (D_z⁵f)² ≤ |f|²_{ℋ⁶}`, with membership
of the `z`-marginal. -/
theorem mh_pureZ_eta_slot_l2 : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ (f : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2))
      ≤ Work.Spaces.HkSq α 6 f := by
  intro α hα f hfsm hf6
  obtain ⟨hbase, hbaseval⟩ :=
    Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := 6) hfsm hf6
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.DzIter 5 f p.1 p.2) ^ 2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    exact contOn_w.mul
      ((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn (hfsm.DzIter 5)).pow 2)
  have hnn : ∀ z θ : ℝ,
      0 ≤ (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z θ) ^ 2 :=
    fun z θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpt : ∀ᵐ p ∂pm, (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.DzIter 5 f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    exact le_trans (mh_w_le_slotWeight (X := Work.Spaces.DzIter 5 f z θ) hz hθ0 hθ1)
      (Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ 5 (by norm_num))
  have hWint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.DzIter 5 f p.1 p.2) ^ 2) pm := by
    refine MeasureTheory.Integrable.mono' hbase haesm ?_
    filter_upwards [hpt] with p hp
    rwa [Real.norm_eq_abs, abs_of_nonneg (hnn p.1 p.2)]
  -- the `z`-marginal of the *joint* integrand
  have hOuter : MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (((MeasureTheory.integrable_prod_iff haesm).mp hWint).2).congr
      (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ y in Work.Spaces.Iθ, ‖(Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z y) ^ 2‖)
      = ∫ y in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z y) ^ 2
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => Real.norm_of_nonneg (hnn z y)))
  have hMarg : MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hOuter.congr (Filter.Eventually.of_forall (fun z =>
      MeasureTheory.integral_const_mul ((Work.Spaces.w z) ^ 2)
        (fun θ : ℝ => (Work.Spaces.DzIter 5 f z θ) ^ 2)))
  refine ⟨hMarg, ?_⟩
  obtain ⟨hjoint, hjointval⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z θ) ^ 2)
    hnn haesm ((MeasureTheory.integrable_prod_iff haesm).mp hWint).1 hOuter
  rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter 5 f z θ) ^ 2 from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z =>
      (MeasureTheory.integral_const_mul _ _).symm))]
  rw [← hjointval, ← hbaseval]
  exact MeasureTheory.integral_mono_ae hjoint hbase hpt

/-- **The slice Agmon bound for `D_z⁵f`** (the `H2.T1Q.SliceSupOpen` instance, whose two `θ`-slice
integrals are the `η`-slot mean and the γ-weighted `(5,1)`-slot). -/
theorem mh_agmon {α : ℝ} {f : ℝ → ℝ → ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f) (hf6 : Work.Spaces.HkMem α 6 f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter 5 f z θ) ^ 2
        ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 f z θ') ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ' in Work.Spaces.Iθ, (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'')) θ' ^ 2
                * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) := by
    intro z θ hz hθ0 hθ1
    have hmean : MeasureTheory.IntegrableOn
        (fun θ' : ℝ => (Work.Spaces.DzIter 5 f z θ') ^ 2) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hf6.1 z (Set.mem_Ici.mpr hz.le))
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _
          ((Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.smoothOpen_continuousOn
            (hfsm.DzIter 5)).pow 2) hz) ?_
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ' hθ'0 hθ'1 => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact le_trans (mh_le_slotWeight (X := Work.Spaces.DzIter 5 f z θ') hz hθ'0 hθ'1)
        (Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ' 5 (by norm_num))
    have hder : MeasureTheory.IntegrableOn
        (fun θ' : ℝ => (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'') θ') ^ 2
          * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.congr
        (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.integrableOn_gamMixed_slice
          (α := α) (f := f) (b := 5) (a := 1) hα0 hfsm hf6 (by norm_num) (by norm_num) hz) ?_
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ' hθ'0 hθ'1 => ?_)
      show Real.sin (2 * θ') ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ') ^ 2
        = (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'') θ') ^ 2
          * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)
      have hdw : (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'') θ') ^ 2
          * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)
          = (Work.Spaces.mixed 5 1 f z θ') ^ 2
            * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)) :=
        Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hfsm 5 0 hz ⟨hθ'0, hθ'1⟩
      calc Real.sin (2 * θ') ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 5 1 f z θ') ^ 2
          = (Work.Spaces.mixed 5 1 f z θ') ^ 2 * Real.sin (2 * θ') ^ (-(Work.Spaces.gam α)) := by ring
        _ = (deriv (fun θ'' : ℝ => Work.Spaces.DzIter 5 f z θ'') θ') ^ 2
              * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α) := hdw.symm
    have h := Work.H2.T1Q.SliceSupOpen α (fun θ' : ℝ => Work.Spaces.DzIter 5 f z θ') hα0 hα1
      (((hfsm.DzIter 5).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder]))
      hmean hder θ ⟨hθ0, hθ1⟩
    exact h

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardBLe4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `b ≤ 4` case of the mismatch coefficient estimate
-/
namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

theorem mh_hard_b_le_four : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (b : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → b ≤ 4 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.mixed b 0 f p.1 p.2
          * Work.Spaces.mixed b 1 f p.1 p.2) pm ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed 0 1 A p.1 p.2 * Work.Spaces.mixed b 0 f p.1 p.2
            * Work.Spaces.mixed b 1 f p.1 p.2 ∂pm|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨Cpw, hCpwpos, hCpw⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨Real.sqrt (10 * Cpw + 1) + 1, by positivity, ?_⟩
  intro α hα A f K0 K4 b hAsm hA4 hAbdd hA4bnd hfsm hf6 hb4
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd
  have hH : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hC0 : 0 ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f :=
    mul_nonneg (mul_nonneg (mul_nonneg hCpwpos.le (by norm_num))
      (le_of_lt (Real.rpow_pos_of_pos hα0 _))) hH
  -- #### the `A`-slot
  have hXsl := mixed_slot_le (α := α) 4 hAsm hA4 (i := 1) (j := 0) le_rfl (by norm_num)
  have hX4 : Work.Spaces.HkSq α 4 A = (Work.FTS.Nonlin.Xn α A) ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 A)]
  have hXint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2 ^ 2) pm := by
    simpa only [Work.FTS.TransportS.leafGam] using hXsl.1
  have hXv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2 ^ 2 ∂pm) ≤ K4 ^ 2 + 1 := by
    have h2 : (Work.FTS.Nonlin.Xn α A) ^ 2 ≤ K4 ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd 2
    have h3 : (∫ p, Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ (-(Work.Spaces.gam α))
        * Work.Spaces.mixed 0 1 A p.1 p.2 ^ 2 ∂pm) ≤ K4 ^ 2 + 1 := by
      rw [hX4] at hXsl
      linarith [hXsl.2]
    simpa only [Work.FTS.TransportS.leafGam] using h3
  -- #### the top `f`-slot
  have hZsl := mixed_slot_le (α := α) 6 hfsm hf6 (i := 1) (j := b) le_rfl (by omega)
  have hZint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) pm := by
    simpa only [Work.FTS.TransportS.leafGam] using hZsl.1
  have hZv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 6 f := by
    simpa only [Work.FTS.TransportS.leafGam] using hZsl.2
  -- #### the remaining `D_z`-factor, pointwise
  have hGnn : ∀ᵐ p ∂pm, 0 ≤ Work.FTS.TransportS.leafGam α p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ _ hθ0 hθ1 => ?_)
    exact Work.FTS.TransportS.leafGam_nonneg α
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
  have hY2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed b 0 f z θ) ^ 2
        ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f := by
    intro z θ hz hθ0 hθ1
    rw [Work.Spaces.mixed_zero_right]
    have h := hCpw α f b 0 hα0 hα1 hfsm hf6 (by omega) z hz θ ⟨hθ0, hθ1⟩
    have hval : Cpw / (Work.Spaces.gam α - 1) = Cpw * 10 * α ^ (-(1 : ℝ)) := by
      rw [Work.Spaces.gam_sub_one, Real.rpow_neg_one]
      field_simp
    rwa [hval] at h
  -- #### integrability and bound of the middle slot
  have hYZmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    exact (h1.mul ((hfsm.mixed b 0).continuousOn.pow 2)).mul
      ((hfsm.mixed b 1).continuousOn.pow 2)
  have hYZpt : ∀ᵐ p ∂pm, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2
      ≤ (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
        * (Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hG : 0 ≤ Work.FTS.TransportS.leafGam α z θ :=
      Work.FTS.TransportS.leafGam_nonneg α hs.le
    have hY := hY2 z θ hz hθ0 hθ1
    have hZ2 : 0 ≤ (Work.Spaces.mixed b 1 f z θ) ^ 2 := sq_nonneg _
    calc Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b 0 f z θ ^ 2
          * Work.Spaces.mixed b 1 f z θ ^ 2
        = (Work.Spaces.mixed b 1 f z θ) ^ 2 * (Work.FTS.TransportS.leafGam α z θ
            * Work.Spaces.mixed b 0 f z θ ^ 2) := by ring
      _ ≤ (Work.Spaces.mixed b 1 f z θ) ^ 2 * (Work.FTS.TransportS.leafGam α z θ
            * (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hG) hZ2
      _ = (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b 1 f z θ ^ 2) := by ring
  have hYZint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) pm := by
    refine MeasureTheory.Integrable.mono' (hZint.const_mul
      (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)) hYZmeas ?_
    filter_upwards [hYZpt, hGnn] with p hp hgn
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg hgn (sq_nonneg _)) (sq_nonneg _))]
    exact hp
  have hYZv : (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
      * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2 ∂pm)
      ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f * Work.Spaces.HkSq α 6 f + 1 := by
    calc (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b 0 f p.1 p.2 ^ 2
          * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2 ∂pm)
        ≤ ∫ p, (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2) ∂pm :=
          MeasureTheory.integral_mono_ae hYZint (hZint.const_mul _) hYZpt
      _ = (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f)
            * (∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b 1 f p.1 p.2 ^ 2 ∂pm) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left hZv hC0
      _ ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f * Work.Spaces.HkSq α 6 f + 1 := by
          linarith
  -- #### measurability of the full integrand
  have hFmeas : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed 0 1 A p.1 p.2
      * Work.Spaces.mixed b 0 f p.1 p.2
      * Work.Spaces.mixed b 1 f p.1 p.2) pm := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    exact ((h1.mul (hAsm.mixed 0 1).continuousOn).mul
      (hfsm.mixed b 0).continuousOn).mul (hfsm.mixed b 1).continuousOn
  -- #### weighted Cauchy–Schwarz
  have hApos : 0 < K4 ^ 2 + 1 := by nlinarith [sq_nonneg K4]
  have hBpos : 0 < Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
      * Work.Spaces.HkSq α 6 f + 1 := by
    have h1 : 0 ≤ Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
        * Work.Spaces.HkSq α 6 f := mul_nonneg hC0 hH
    linarith
  obtain ⟨hFint, hFbnd⟩ := slotAmgm (G := Work.FTS.TransportS.leafGam α)
    (X := fun z θ => Work.Spaces.mixed 0 1 A z θ)
    (Y := fun z θ => Work.Spaces.mixed b 0 f z θ)
    (Z := fun z θ => Work.Spaces.mixed b 1 f z θ)
    (A := K4 ^ 2 + 1)
    (B := Cpw * 10 * α ^ (-(1 : ℝ)) * Work.Spaces.HkSq α 6 f
      * Work.Spaces.HkSq α 6 f + 1)
    hXint hYZint hXv hYZv hApos hBpos hGnn hFmeas
  exact ⟨hFint, hFbnd.trans (slotArith hα0 hα1 hCpwpos hK0 hK4 hH)⟩

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.F0FiveEVzD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

set_option maxHeartbeats 1600000

/-- **The order-five flat bound of the `∂_θ`-derivative expression `EVzD` of the `EVz`-field.**

`EVzD Y = 2·(cos²θ − 2 sin²θ)'·Y + 2·(cos²θ − 2 sin²θ)·∂_θY + (sin 2θ)'·∂_θY + D_θ(∂_θY)`
is the sum of three products of a *universal* smooth angular coefficient with one of the two
blocks `Y`, `∂_θY`, plus the angular block `D_θ(∂_θY)`.  With `A ≥ 1` the constant of
`CoefBundle6s`:

* `F0 5 (2⁵·(2A)·K) (2·(cos²θ − 2 sin²θ)'·Y)` — Leibniz (`F0_mul`);
* `F0 5 (2⁵·(2A)·KY) (2·(cos²θ − 2 sin²θ)·∂_θY)` — Leibniz;
* `F0 5 (2⁵·A·KY) ((sin 2θ)'·∂_θY)` — Leibniz;
* `F0 5 KY (D_θ(∂_θY))` — `F0_Dth` (one more angular derivative of the `F0 6 KY (∂_θY)` datum);

the four constants sum to `64AK + 96AKY + KY ≤ (160A+1)·(K+KY)`, and `F0_congr` transfers the
bound to `EVzD Y` itself.  Everything is `sorry`-free. -/
theorem F0FiveEVzD : ∃ C : ℝ, 0 < C ∧ ∀ (K KY : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ K → 0 ≤ KY → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 K Y → Work.FTS.PhiStar.F0 6 KY (Work.Spaces.pth Y) →
    Work.FTS.PhiStar.F0 5 (C * (K + KY)) (Work.FTS.StrongPersist.SP6.EVzD Y) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  refine ⟨160 * A + 1, by linarith, ?_⟩
  intro K KY Y hK hKY hYs hY hdY
  -- the three angular coefficients
  have hphi := hcoef (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by simp [coefFun])
  have hdPhi := hcoef (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
    (by simp [coefFun])
  have hdSin := hcoef (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) (by simp [coefFun])
  -- lower everything to order `5`
  have hY5 : Work.FTS.PhiStar.F0 5 K Y :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := K) (K' := K) (f := Y)
      (by norm_num) le_rfl hY
  have hdY5 : Work.FTS.PhiStar.F0 5 KY (Work.Spaces.pth Y) :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := KY) (K' := KY)
      (f := Work.Spaces.pth Y) (by norm_num) le_rfl hdY
  have hphi5 : Work.FTS.PhiStar.F0 5 A (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := A) (K' := A)
      (f := fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by norm_num) le_rfl hphi.1
  have hdPhi5 : Work.FTS.PhiStar.F0 5 A
      (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := A) (K' := A)
      (f := fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
      (by norm_num) le_rfl hdPhi.1
  have hdSin5 : Work.FTS.PhiStar.F0 5 A
      (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) :=
    Work.FTS.PhiStar.F0.mono (n := 5) (n' := 6) (K := A) (K' := A)
      (f := fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) (by norm_num) le_rfl hdSin.1
  -- the coefficients `2·(cos²−2sin²)` and `2·(cos²−2sin²)'`
  have h2phi : Work.FTS.PhiStar.F0 5 (2 * A)
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hphi5
    simpa using h
  have h2dPhi : Work.FTS.PhiStar.F0 5 (2 * A)
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hdPhi5
    simpa using h
  -- smoothness of the coefficients
  have s2phi : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hphi.2 2
  have s2dPhi : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hdPhi.2 2
  have sdsin : Work.FTS.EllipticEst.SmoothOpen
      (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) := hdSin.2
  -- the four summands
  have hX1 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * K)
      (fun z θ : ℝ =>
        (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_mul (n := 5)
      (K := 2 * A) (K' := K)
      (f := fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
      (g := Y) (by linarith) hK s2dPhi hYs h2dPhi hY5
    simpa using h
  have hX2 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * KY)
      (fun z θ : ℝ =>
        (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_mul (n := 5)
      (K := 2 * A) (K' := KY)
      (f := fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2))
      (g := Work.Spaces.pth Y) (by linarith) hKY s2phi hYs.pth h2phi hdY5
    simpa using h
  have hX3 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * A * KY)
      (fun z θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_mul (n := 5)
      (K := A) (K' := KY)
      (f := fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ)
      (g := Work.Spaces.pth Y) hA0 hKY sdsin hYs.pth hdSin5 hdY5
    simpa using h
  have hX4 : Work.FTS.PhiStar.F0 5 KY (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_Dth (n := 5) hdY
  -- smoothness of the summands
  have sm1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ =>
        (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2dPhi hYs
  have sm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ =>
        (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2phi hYs.pth
  have sm3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul sdsin hYs.pth
  have sm4 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    hYs.pth.Dth
  -- assemble
  have hX23 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY)
      (fun z θ : ℝ =>
        (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
          + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_add sm2 sm3 hX2 hX3
    simpa using h
  have sm23 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ =>
        (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
          + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add sm2 sm3
  have hX123 : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + ((2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY))
      (fun z θ : ℝ =>
        (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ
          + ((2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
            + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_add sm1 sm23 hX1 hX23
    simpa using h
  have sm123 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ =>
        (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ
          + ((2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
            + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add sm1 sm23
  have htot : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + ((2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY) + KY)
      (fun z θ : ℝ =>
        ((2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) * Y z θ
          + ((2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ
            + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ))
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_add sm123 sm4 hX123 hX4
    simpa using h
  -- normalise the constant
  have hconst : (2 : ℝ) ^ 5 * (2 * A) * K
      + ((2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY) + KY
      ≤ (160 * A + 1) * (K + KY) := by
    nlinarith [hA0, hK, hKY, mul_nonneg hA0 hK, mul_nonneg hA0 hKY]
  have htot' := htot.mono le_rfl hconst
  refine Work.FTS.PhiStar.CoreAux.F0_congr (f := Work.FTS.StrongPersist.SP6.EVzD Y) ?_ htot'
  intro z θ _ _ _
  simp only [Work.FTS.StrongPersist.SP6.EVzD, Work.Spaces.Dth, Work.Spaces.pth]
  ring

end Work.FTS.StrongPersist.SP6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.F0SixEVzR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

/-- **The order-six flat bound of the reassociated `EVz`-field, *linear* in the two block
bounds.**

`EVzR Y = 2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY` is a sum of two products of a smooth angular
coefficient with one of the two blocks `Y`, `∂_θY`:

`EVzR Y = (2·(cos²θ − 2 sin²θ))·Y + sin(2θ)·∂_θY`.

Let `A ≥ 1` be the universal constant of `CoefBundle6s`, so that each of the two coefficients is
`F0 6 A` and `SmoothOpen`.  The Leibniz estimate `F0_mul` (which is *bilinear*, hence never
squares `K`) gives

* `F0 6 (2⁶·(2A)·K) (2(cos²θ − 2 sin²θ)·Y)` — coefficient constant `2A`;
* `F0 6 (2⁶·A·KY) (sin(2θ)·∂_θY)` — coefficient constant `A`, upgraded to `2⁶·(2A)·KY` by
  monotonicity since `A·KY ≥ 0`.

`F0_add` adds the two constants `2⁶(2A)K + 2⁶(2A)KY = 128·A·(K + KY)`, and `F0_congr` transfers
the bound to `EVzR Y` itself.  Hence `C = 128·A` works and is linear in `K + KY`, as required.

Everything here is `sorry`-free. -/
theorem F0SixEVzR : ∃ C : ℝ, 0 < C ∧ ∀ (K KY : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ K → 0 ≤ KY → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 K Y → Work.FTS.PhiStar.F0 6 KY (Work.Spaces.pth Y) →
    Work.FTS.PhiStar.F0 6 (C * (K + KY)) (Work.FTS.StrongPersist.SP6.EVzR Y) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  refine ⟨128 * A, by nlinarith, ?_⟩
  intro K KY Y hK hKY hYs hY hdY
  have hphi := hcoef (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by simp [coefFun])
  have hs2 := hcoef (fun _ θ : ℝ => Real.sin (2 * θ)) (by simp [coefFun])
  have s2phi : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hphi.2 2
  have h2phi : Work.FTS.PhiStar.F0 6 (2 * A)
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hphi.1
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2] at h
    exact h
  -- the `Y`-slot
  have ht1 : Work.FTS.PhiStar.F0 6 ((2 : ℝ) ^ 6 * (2 * A) * K)
      ((fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Y) :=
    Work.FTS.PhiStar.CoreAux.F0_mul (mul_nonneg (by norm_num) hA0) hK s2phi hYs h2phi hY
  -- the `∂_θY`-slot
  have ht2 : Work.FTS.PhiStar.F0 6 ((2 : ℝ) ^ 6 * A * KY)
      ((fun _ θ : ℝ => Real.sin (2 * θ)) * Work.Spaces.pth Y) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hKY hs2.2 hYs.pth hs2.1 hdY
  have hAKY : (0 : ℝ) ≤ A * KY := mul_nonneg hA0 hKY
  have ht2' : Work.FTS.PhiStar.F0 6 ((2 : ℝ) ^ 6 * (2 * A) * KY)
      ((fun _ θ : ℝ => Real.sin (2 * θ)) * Work.Spaces.pth Y) :=
    ht2.mono le_rfl (by nlinarith [hAKY])
  have hsum := Work.FTS.PhiStar.CoreAux.F0_add
    (Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2phi hYs)
    (Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hs2.2 hYs.pth) ht1 ht2'
  have hcc : (2 : ℝ) ^ 6 * (2 * A) * K + (2 : ℝ) ^ 6 * (2 * A) * KY
      = 128 * A * (K + KY) := by ring
  rw [hcc] at hsum
  exact Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => rfl) hsum

end Work.FTS.StrongPersist.SP6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.PthEVzR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false

/-!
# `pth (EVzR Y) = EVzD Y` on the open quadrant

`EVzR Y = 2(cos²θ - 2 sin²θ)·Y + sin(2θ)·∂_θY` and `EVzD Y` is its product-rule derivative
(`Flat6Defs`).  The identity is the analytic step of the order-six flat bound `EVz6`: it lets the
consumers transfer a bound on `EVzD Y` to a bound on `∂_θ(EVzR Y)`.

The proof is the product rule.  On the open quadrant the two `θ`-slices `θ' ↦ Y z θ'` and
`θ' ↦ ∂_θY z θ'` are `C^∞` (hence differentiable), and the two coefficient functions
`θ' ↦ cos²θ' - 2 sin²θ'` and `θ' ↦ sin(2θ')` are differentiable; `HasDerivAt.mul` /
`HasDerivAt.const_mul` / `HasDerivAt.add` assemble the derivative of the sum, and
`HasDerivAt.deriv` converts back to the `deriv`-form.  Everything is definitional after
unfolding `EVzD`, `Dth` and `pth`.
-/

theorem PthEVzR (Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.FTS.StrongPersist.SP6.EVzR Y) z θ
        = Work.FTS.StrongPersist.SP6.EVzD Y z θ := by
  intro z θ hz hθ hθ2
  have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  -- the two `θ`-slices of `Y` and of `∂_θY` are differentiable on the open quadrant
  have hYd : DifferentiableAt ℝ (fun θ' : ℝ => Y z θ') θ :=
    ((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hmem)
  have hPYd : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pth Y z θ') θ :=
    (((hsm.pth).curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hmem)
  -- the two angular coefficients
  have hcd : DifferentiableAt ℝ (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ := by
    fun_prop
  have hsd : DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ := by fun_prop
  have hc : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2)
      (deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) θ := hcd.hasDerivAt
  have hs : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ'))
      (deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ) θ := hsd.hasDerivAt
  have hY : HasDerivAt (fun θ' : ℝ => Y z θ') (deriv (fun θ' : ℝ => Y z θ') θ) θ :=
    hYd.hasDerivAt
  have hP : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth Y z θ')
      (deriv (fun θ' : ℝ => Work.Spaces.pth Y z θ') θ) θ := hPYd.hasDerivAt
  -- the two summands of `EVzR Y`
  have hA : HasDerivAt (fun θ' : ℝ => 2 * (Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) * Y z θ')
      (2 * deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * deriv (fun θ' : ℝ => Y z θ') θ) θ :=
    (hc.const_mul 2).mul hY
  have hB : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ') * Work.Spaces.pth Y z θ')
      (deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ
        + Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.pth Y z θ') θ) θ :=
    hs.mul hP
  have hmain : HasDerivAt (fun θ' : ℝ => Work.FTS.StrongPersist.SP6.EVzR Y z θ')
      (Work.FTS.StrongPersist.SP6.EVzD Y z θ) θ := by
    refine (hA.add hB).congr_deriv ?_
    simp only [Work.FTS.StrongPersist.SP6.EVzD, Work.Spaces.Dth, Work.Spaces.pth]
    ring
  show deriv (fun θ' : ℝ => Work.FTS.StrongPersist.SP6.EVzR Y z θ') θ
    = Work.FTS.StrongPersist.SP6.EVzD Y z θ
  exact hmain.deriv

end Work.FTS.StrongPersist.SP6
end
end
