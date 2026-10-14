import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.R.SlotHigh
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ CoerAdm UnifIP Xn)

set_option autoImplicit false




end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.limFam_EpsMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false

/-- **The metric clause of `hlimP`**: the limit slice of a Picard sequence which stays in the
weighted `X`-ball of radius `R` is itself in that ball. -/
theorem limFam_EpsMem {α R δ : ℝ} {F : Fn → Fn} {h₀ : Fn} (hR : 0 ≤ R)
    (hconv : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => slice (iter F h₀ N) τ z θ) Filter.atTop
        (nhds (slice (limFam F h₀) τ z θ)))
    (hP : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc 0 δ →
      EpsMem α (slice (iter F h₀ n) τ) ∧ EpsSq α (slice (iter F h₀ n) τ) ≤ R) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      EpsMem α (slice (limFam F h₀) τ) ∧ EpsSq α (slice (limFam F h₀) τ) ≤ R := by
  intro τ hτ
  refine EpsMem_and_EpsSq_le_of_ae_tendsto_mem (α := α) (B := R) hR
    (A := fun n : ℕ => slice (iter F h₀ n) τ)
    (Alim := slice (limFam F h₀) τ)
    (fun n => (hP n τ hτ).1) (fun n => (hP n τ hτ).2) ?_
  exact ae_of_forall_open (fun z hz θ hθ0 hθ1 => hconv τ hτ z θ hz hθ0 hθ1)

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.mul_WlInf6_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.aux

open scoped Real Topology

/-- **The elementary `HkSq` arithmetic of the product rule.**  If `S² = C` and
`b ≤ S·α^{-1/2}·W·N` with `b ≥ 0`, `W ≥ 0` and `W ≤ CY·α`, then `b² ≤ C·CY²·α·N²`.

This isolates the passage from the (square-root) norm bound to the squared norm bound: the
two `α`-powers `α^{-1/2}` and `α^{-1}` and the factor `(CY·α)²` are combined here. -/
private lemma sq_bound_of {C S α CY W N b : ℝ} (hC : 0 ≤ C) (hS : S ^ 2 = C) (hα : 0 < α)
    (hWnn : 0 ≤ W) (hW : W ≤ CY * α)
    (hb : b ≤ S * α ^ (-(1 / 2 : ℝ)) * W * N) (hb0 : 0 ≤ b) :
    b ^ 2 ≤ C * CY ^ 2 * α * N ^ 2 := by
  have hrpow : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
    rw [pow_two, ← Real.rpow_add hα, show (-(1 / 2 : ℝ)) + (-(1 / 2)) = -1 by norm_num,
      Real.rpow_neg_one]
  have heq : (S * α ^ (-(1 / 2 : ℝ)) * W * N) ^ 2 = C * α⁻¹ * W ^ 2 * N ^ 2 := by
    rw [show (S * α ^ (-(1 / 2 : ℝ)) * W * N) ^ 2
        = S ^ 2 * (α ^ (-(1 / 2 : ℝ))) ^ 2 * W ^ 2 * N ^ 2 from by ring, hS, hrpow]
  have h1 : b ^ 2 ≤ (S * α ^ (-(1 / 2 : ℝ)) * W * N) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  have hW2 : W ^ 2 ≤ (CY * α) ^ 2 := pow_le_pow_left₀ hWnn hW 2
  have h2 : C * α⁻¹ * W ^ 2 * N ^ 2 ≤ C * α⁻¹ * (CY * α) ^ 2 * N ^ 2 := by
    have h : 0 ≤ C * α⁻¹ := mul_nonneg hC (inv_nonneg.mpr hα.le)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW2 h) (sq_nonneg N)
  have h4 : C * α⁻¹ * (CY * α) ^ 2 * N ^ 2 = C * CY ^ 2 * α * N ^ 2 := by field_simp
  calc b ^ 2 ≤ (S * α ^ (-(1 / 2 : ℝ)) * W * N) ^ 2 := h1
    _ = C * α⁻¹ * W ^ 2 * N ^ 2 := heq
    _ ≤ C * α⁻¹ * (CY * α) ^ 2 * N ^ 2 := h2
    _ = C * CY ^ 2 * α * N ^ 2 := h4

theorem mul_WlInf6_HkSq : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Y w : ℝ → ℝ → ℝ) (CY : ℝ),
    Work.FTS.EllipticEst.SmoothOpen Y → Work.Spaces.WlInfMem α 6 Y →
    Work.Spaces.WlInf α 6 Y ≤ CY * α → 0 ≤ CY →
    Work.FTS.EllipticEst.SmoothOpen w → Work.Spaces.HkMem α 6 w →
    Work.Spaces.HkSq α 6 (fun z θ => Y z θ * w z θ) ≤ C * CY ^ 2 * α * Work.Spaces.HkSq α 6 w := by
  -- the slot constants of the `C⁶` product rule
  obtain ⟨Cz, hCz, hZ⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
  obtain ⟨CB, _hCB, hCBmean⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cm, hCm, hMx⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6 CB
  refine ⟨(7 * Cz + 49 * Cm) * 42701, by positivity, ?_⟩
  intro α hαIoc Y w CY hYsm hYW hYle hCY hwsm hwH
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- `SmoothOpen` is `C^∞` on the open quadrant, in particular `C⁶`
  have hYcd : ContDiffOn ℝ 6 (Function.uncurry Y) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall hYsm 6
  have hwcd : ContDiffOn ℝ 6 (Function.uncurry w) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall hwsm 6
  -- the norm form of the product rule
  obtain ⟨-, hnorm⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_aux6 (f := Y) (g := w)
      hα hα1 hYcd hYW hwcd hwH hCz hCm
      (fun i hi z θ hz hθ0 hθ1 => hZ α Y w hα hα1 hYcd hYW hwcd i hi z θ hz hθ0 hθ1)
      (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α Y w hα hα1 hYcd hYW hwcd hwH
        (fun d hd z' θ' hz' hθ0' hθ1' =>
          hCBmean α w d hα hα1 hwcd hwH hd z' θ' hz' hθ0' hθ1')
        I J hI hIJ z θ hz hθ0 hθ1)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 Y := Work.Spaces.WlInf_nonneg α 6 Y hYW
  have hmain := sq_bound_of (C := (7 * Cz + 49 * Cm) * 42701)
    (S := Real.sqrt ((7 * Cz + 49 * Cm) * 42701)) (α := α) (CY := CY)
    (W := Work.Spaces.WlInf α 6 Y) (N := Work.Spaces.HkNorm α 6 w)
    (b := Work.Spaces.HkNorm α 6 (fun z θ => Y z θ * w z θ))
    (by positivity) (Real.sq_sqrt (by positivity)) hα hWnn hYle hnorm
    (Work.Spaces.HkNorm_nonneg α 6 _)
  calc Work.Spaces.HkSq α 6 (fun z θ => Y z θ * w z θ)
      = (Work.Spaces.HkNorm α 6 (fun z θ => Y z θ * w z θ)) ^ 2 := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)]
    _ ≤ ((7 * Cz + 49 * Cm) * 42701) * CY ^ 2 * α * (Work.Spaces.HkNorm α 6 w) ^ 2 := hmain
    _ = ((7 * Cz + 49 * Cm) * 42701) * CY ^ 2 * α * Work.Spaces.HkSq α 6 w := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 w)]

end Work.FTS.StrongEps.E4R3.Nblock6.aux
end
