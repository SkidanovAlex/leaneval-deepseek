import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyA
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.OpenPkg.Basic

import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZCS

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

