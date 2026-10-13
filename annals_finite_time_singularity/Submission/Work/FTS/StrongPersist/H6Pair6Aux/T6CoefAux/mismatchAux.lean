import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.TransportS.T3BadAux.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Shared tools for the mismatch coefficient estimate

Pointwise AM–GM tools, continuity of the weighted slot densities and the single-slot
integrability/bound lemmas used by the three index cases of
`Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCoefCase`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

/-- The product measure on the quadrant `[0,∞) × [0,π/2]`. -/
def pm : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- `2 |a| |b| ≤ lam·a² + b²/lam` for `lam > 0`. -/
lemma two_abs_mul_le (lam a b : ℝ) (hlam : 0 < lam) :
    2 * |a| * |b| ≤ lam * a ^ 2 + b ^ 2 / lam := by
  have h : (0 : ℝ) ≤ (lam * |a| - |b|) ^ 2 := sq_nonneg _
  have h1 : 2 * (lam * |a|) * |b| ≤ (lam * |a|) ^ 2 + |b| ^ 2 := by nlinarith [h]
  have h1' : 2 * lam * |a| * |b| ≤ lam ^ 2 * a ^ 2 + b ^ 2 := by
    have h2 := h1
    rw [mul_pow, sq_abs a, sq_abs b, mul_assoc] at h2
    nlinarith [h2]
  have h3 : (2 * lam * |a| * |b|) / lam ≤ (lam ^ 2 * a ^ 2 + b ^ 2) / lam :=
    div_le_div_of_nonneg_right h1' hlam.le
  have h4 : (2 * lam * |a| * |b|) / lam = 2 * |a| * |b| := by
    field_simp
  have h5 : (lam ^ 2 * a ^ 2 + b ^ 2) / lam = lam * a ^ 2 + b ^ 2 / lam := by
    field_simp
  rwa [h4, h5] at h3

/-- **The pointwise AM–GM majorant**: `W |a| |b| |c| ≤ ½ (lam (W a²) + lam⁻¹ (W b² c²))`. -/
lemma pt_le (W a b c lam : ℝ) (hW : 0 ≤ W) (hlam : 0 < lam) :
    W * |a| * (|b| * |c|) ≤ (1 / 2) * (lam * (W * a ^ 2) + lam⁻¹ * (W * (b ^ 2 * c ^ 2))) := by
  have h2 := two_abs_mul_le lam a (|b| * |c|) hlam
  have h3 : (|b| * |c|) ^ 2 / lam = lam⁻¹ * (b ^ 2 * c ^ 2) := by
    rw [mul_pow, sq_abs, sq_abs, div_eq_mul_inv]
    ring
  have h2' : 2 * |a| * (|b| * |c|) ≤ lam * a ^ 2 + (|b| * |c|) ^ 2 / lam := by
    simpa only [abs_mul, abs_of_nonneg (abs_nonneg b), abs_of_nonneg (abs_nonneg c)] using h2
  have h4 : 2 * |a| * (|b| * |c|) ≤ lam * a ^ 2 + lam⁻¹ * (b ^ 2 * c ^ 2) := by
    rw [← h3]; exact h2'
  have hab : |a| * (|b| * |c|) ≤ (1 / 2) * (lam * a ^ 2 + lam⁻¹ * (b ^ 2 * c ^ 2)) := by linarith
  have h5 := mul_le_mul_of_nonneg_left hab hW
  calc W * |a| * (|b| * |c|) = W * (|a| * (|b| * |c|)) := by ring
    _ ≤ W * ((1 / 2) * (lam * a ^ 2 + lam⁻¹ * (b ^ 2 * c ^ 2))) := h5
    _ = (1 / 2) * (lam * (W * a ^ 2) + lam⁻¹ * (W * (b ^ 2 * c ^ 2))) := by ring

/-- `√(x²+1) ≤ x+1` for `x ≥ 0`. -/
lemma sqrt_sq_add_one_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ 2 + 1) ≤ x + 1 := by
  have h : x ^ 2 + 1 ≤ (x + 1) ^ 2 := by nlinarith
  calc Real.sqrt (x ^ 2 + 1) ≤ Real.sqrt ((x + 1) ^ 2) := Real.sqrt_le_sqrt h
    _ = x + 1 := Real.sqrt_sq (by linarith)

/-- `K·H ≤ (1+K)(1+H)` for nonnegative `K, H`. -/
lemma mul_le_one_add {K H : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) :
    K * H ≤ (1 + K) * (1 + H) := by nlinarith

/-- Continuity of `w(z)²` on the open quadrant. -/
lemma contOn_w : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
    Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div (((continuousOn_const.add continuousOn_id).pow 2).pow 2)
      ((continuousOn_id.pow 2).pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz))
  have h2 : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2 := by
    funext z
    rw [Work.Spaces.w, div_pow]
  have h3 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    rw [h2]; exact h1
  exact h3.comp continuous_fst.continuousOn (fun p hp => hp.1)

/-- Continuity of `sin(2θ)^{-γ}` on the open quadrant. -/
lemma contOn_sig (α : ℝ) : ContinuousOn
    (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))
    Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  refine hsin.rpow_const ?_
  intro p hp
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
    (by linarith [hp.2.2, Real.pi_pos])))

/-- Continuity of the weighted slot density of a mixed slot. -/
lemma contOn_dens {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
  (contOn_w.mul (contOn_sig α)).mul ((hsm.mixed j i).continuousOn.pow 2)

/-- **One mixed slot with its `σ^{-γ}` weight**: integrability on the product measure and the
`ℋ^k`-bound. -/
lemma mixed_slot_le {α : ℝ} (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) pm ∧
      (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 ∂pm) ≤ Work.Spaces.HkSq α k f := by
  have hbase := Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen (α := α) (k := k) hsm hmem
  have hbase' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α k f p.1 p.2) pm := hbase.1
  have hval' : (∫ p, Work.Spaces.HkIntegrand α k f p.1 p.2 ∂pm) = Work.Spaces.HkSq α k f :=
    hbase.2
  have hpt : ∀ᵐ p ∂pm, (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α k f p.1 p.2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hid : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [mul_pow, Work.FTS.TransportS.T3BadAux.Wt_sq_eq (α := α) (z := z) (θ := θ) hθI]
      ring
    rw [hid]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij
  have hnn : ∀ᵐ p ∂pm, 0 ≤ (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed j i f p.1 p.2) ^ 2 := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    refine mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ?_ _)) (sq_nonneg _)
    exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f p.1 p.2) ^ 2) pm := by
    refine MeasureTheory.Integrable.mono' hbase'
      (Work.Spaces.aesm_of_continuousOn_Qd _ (contOn_dens hsm j i)) ?_
    filter_upwards [hpt, hnn] with p hp hpn
    rw [Real.norm_eq_abs, abs_of_nonneg hpn]
    exact hp
  refine ⟨hint, ?_⟩
  rw [← hval']
  exact MeasureTheory.integral_mono_ae hint hbase' hpt

/-- **A pointwise majorant gives the integral bound**. -/
lemma abs_integral_le_of_pointwise {μ : MeasureTheory.Measure (ℝ × ℝ)}
    {F M : ℝ × ℝ → ℝ} (hM : MeasureTheory.Integrable M μ)
    (haesm : MeasureTheory.AEStronglyMeasurable F μ)
    (h : ∀ᵐ p ∂μ, |F p| ≤ M p) :
    |∫ p, F p ∂μ| ≤ ∫ p, M p ∂μ := by
  have hFint : MeasureTheory.Integrable F μ := by
    refine MeasureTheory.Integrable.mono' hM haesm ?_
    filter_upwards [h] with p hp
    rwa [Real.norm_eq_abs]
  calc |∫ p, F p ∂μ| ≤ ∫ p, |F p| ∂μ := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ p, M p ∂μ := MeasureTheory.integral_mono_ae hFint.abs hM h

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
