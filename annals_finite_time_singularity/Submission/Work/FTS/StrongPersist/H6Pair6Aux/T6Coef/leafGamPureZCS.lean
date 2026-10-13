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

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1600000

set_option quotPrecheck false in
local notation "PMq" => (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
  (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- **The weighted Cauchy–Schwarz inequality in `L²`** for the product measure. -/
lemma leafGamPureZ_cs {ρ A B : ℝ → ℝ → ℝ}
    (hρ : ∀ᵐ p ∂PMq, 0 ≤ ρ p.1 p.2)
    (hA2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * (A p.1 p.2) ^ 2) PMq)
    (hB2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2 * (B p.1 p.2) ^ 2) PMq)
    (hA : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => A p.1 p.2) PMq)
    (hB : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => B p.1 p.2) PMq)
    (hρs : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Real.sqrt (ρ p.1 p.2)) PMq) :
    (∫ p, ρ p.1 p.2 * |A p.1 p.2| * |B p.1 p.2| ∂PMq)
      ≤ Real.sqrt (∫ p, ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂PMq)
        * Real.sqrt (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂PMq) := by
  set f : ℝ × ℝ → ℝ := fun p => Real.sqrt (ρ p.1 p.2) * A p.1 p.2 with hf
  set g : ℝ × ℝ → ℝ := fun p => Real.sqrt (ρ p.1 p.2) * B p.1 p.2 with hg
  have hfm : MeasureTheory.AEStronglyMeasurable f PMq := hρs.mul hA
  have hgm : MeasureTheory.AEStronglyMeasurable g PMq := hρs.mul hB
  have hfsq : (fun p : ℝ × ℝ => f p ^ 2) =ᵐ[PMq] fun p => ρ p.1 p.2 * (A p.1 p.2) ^ 2 := by
    filter_upwards [hρ] with p hp
    show (Real.sqrt (ρ p.1 p.2) * A p.1 p.2) ^ 2 = ρ p.1 p.2 * (A p.1 p.2) ^ 2
    rw [mul_pow, Real.sq_sqrt hp]
  have hgsq : (fun p : ℝ × ℝ => g p ^ 2) =ᵐ[PMq] fun p => ρ p.1 p.2 * (B p.1 p.2) ^ 2 := by
    filter_upwards [hρ] with p hp
    show (Real.sqrt (ρ p.1 p.2) * B p.1 p.2) ^ 2 = ρ p.1 p.2 * (B p.1 p.2) ^ 2
    rw [mul_pow, Real.sq_sqrt hp]
  have hfint : MeasureTheory.Integrable (fun p : ℝ × ℝ => f p ^ 2) PMq := hA2.congr hfsq.symm
  have hgint : MeasureTheory.Integrable (fun p : ℝ × ℝ => g p ^ 2) PMq := hB2.congr hgsq.symm
  have hfmem : MeasureTheory.MemLp f 2 PMq :=
    (MeasureTheory.memLp_two_iff_integrable_sq hfm).mpr hfint
  have hgmem : MeasureTheory.MemLp g 2 PMq :=
    (MeasureTheory.memLp_two_iff_integrable_sq hgm).mpr hgint
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := PMq) (p := 2) (q := 2)
    (f := f) (g := g) Real.HolderConjugate.two_two
    (by rw [ENNReal.ofReal_ofNat]; exact hfmem)
    (by rw [ENNReal.ofReal_ofNat]; exact hgmem)
  have hnorm : (fun p : ℝ × ℝ => ‖f p‖ * ‖g p‖)
      =ᵐ[PMq] (fun p => ρ p.1 p.2 * |A p.1 p.2| * |B p.1 p.2|) := by
    filter_upwards [hρ] with p hp
    have hs : 0 ≤ Real.sqrt (ρ p.1 p.2) := Real.sqrt_nonneg _
    have h2 : Real.sqrt (ρ p.1 p.2) * Real.sqrt (ρ p.1 p.2) = ρ p.1 p.2 := by
      rw [← sq, Real.sq_sqrt hp]
    show |Real.sqrt (ρ p.1 p.2) * A p.1 p.2| * |Real.sqrt (ρ p.1 p.2) * B p.1 p.2|
      = ρ p.1 p.2 * |A p.1 p.2| * |B p.1 p.2|
    simp only [abs_mul, abs_of_nonneg hs]
    rw [show (Real.sqrt (ρ p.1 p.2) * |A p.1 p.2|) * (Real.sqrt (ρ p.1 p.2) * |B p.1 p.2|)
        = (Real.sqrt (ρ p.1 p.2) * Real.sqrt (ρ p.1 p.2)) * (|A p.1 p.2| * |B p.1 p.2|)
        from by ring, h2]
    ring
  have hsqA : (∫ p, ‖f p‖ ^ (2 : ℝ) ∂PMq) = ∫ p, ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂PMq := by
    calc (∫ p, ‖f p‖ ^ (2 : ℝ) ∂PMq) = ∫ p, f p ^ 2 ∂PMq := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
      _ = ∫ p, ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂PMq := MeasureTheory.integral_congr_ae hfsq
  have hsqB : (∫ p, ‖g p‖ ^ (2 : ℝ) ∂PMq) = ∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂PMq := by
    calc (∫ p, ‖g p‖ ^ (2 : ℝ) ∂PMq) = ∫ p, g p ^ 2 ∂PMq := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
      _ = ∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂PMq := MeasureTheory.integral_congr_ae hgsq
  calc (∫ p, ρ p.1 p.2 * |A p.1 p.2| * |B p.1 p.2| ∂PMq)
      = ∫ p, ‖f p‖ * ‖g p‖ ∂PMq := (MeasureTheory.integral_congr_ae hnorm).symm
    _ ≤ (∫ p, ‖f p‖ ^ (2 : ℝ) ∂PMq) ^ (1 / (2 : ℝ))
          * (∫ p, ‖g p‖ ^ (2 : ℝ) ∂PMq) ^ (1 / (2 : ℝ)) := hholder
    _ = Real.sqrt (∫ p, ρ p.1 p.2 * (A p.1 p.2) ^ 2 ∂PMq)
          * Real.sqrt (∫ p, ρ p.1 p.2 * (B p.1 p.2) ^ 2 ∂PMq) := by
        rw [hsqA, hsqB, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-! ## Tools for the `b₁ ≤ 4` case of `leafGamPureZ`

For `b₁ ≤ 4` the coefficient slot `D_z^{b₁}A` has order at most `4`, hence a *pointwise* bound
(`N6.PwAny6`, priced by `HkNorm α 6 A ≤ K6`).  The two `f`-slots `mixed (b - b₁) a f` and
`mixed b a f` are both *mixed* (`1 ≤ a`) of order at most `4` resp. `6`, so the matched-weight
Cauchy–Schwarz (`Npair6Aux.weightedCS_ae`) prices their pair by
`|f|_{ℋ⁴}·|f|_{ℋ⁶} ≤ M·|f|_{ℋ⁶}`. -/

/-- `√(x²+1) ≤ x+1` for `x ≥ 0`. -/
lemma leafGamPureZ_sqrtSqAddOneLe {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ 2 + 1) ≤ x + 1 := by
  have h : x ^ 2 + 1 ≤ (x + 1) ^ 2 := by nlinarith
  calc Real.sqrt (x ^ 2 + 1) ≤ Real.sqrt ((x + 1) ^ 2) := Real.sqrt_le_sqrt h
    _ = x + 1 := Real.sqrt_sq (by linarith)

/-- The `γ`-leaf weight is continuous on the open quadrant. -/
lemma leafGamPureZ_cont (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h : (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
      = fun p : ℝ × ℝ =>
          (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := rfl
  rw [h]
  exact (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0).mul
    (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 (Work.Spaces.gam α))

/-- The `γ`-weighted density of a mixed slot is continuous on the open quadrant. -/
lemma leafGamPureZ_densCont {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
    (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 (Work.Spaces.gam α))).mul
    ((hsm.mixed j i).continuousOn.pow 2)

/-- **Product-measure integrability and value bound for a `γ`-weighted mixed slot.** -/
lemma leafGamPureZ_mixedSlotLe {α : ℝ} (hα0 : 0 < α) {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ Work.Spaces.HkSq α k f := by
  have hbase := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := k) hsm hmem
  have hpt : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 ≤ Work.Spaces.HkIntegrand α k f p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hid : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα0 hθI]
      ring
    rw [hid]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij
  have hnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      0 ≤ (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)) (sq_nonneg _)
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j i f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.Integrable.mono' hbase.1
      (Work.Spaces.aesm_of_continuousOn_Qd _ (leafGamPureZ_densCont hsm j i)) ?_
    filter_upwards [hpt, hnn] with p hp hpn
    rw [Real.norm_eq_abs, abs_of_nonneg hpn]
    exact hp
  refine ⟨hint, ?_⟩
  rw [← hbase.2]
  exact MeasureTheory.integral_mono_ae hint hbase.1 hpt

