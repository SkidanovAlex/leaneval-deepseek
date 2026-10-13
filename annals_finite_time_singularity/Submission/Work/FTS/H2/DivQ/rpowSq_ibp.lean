import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Set Filter
open scoped Topology

/-- `t ↦ t ^ p` is continuous on `[a, b]` when `0 < a`. -/
private lemma continuousOn_rpow_Icc {p a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => t ^ p) (Set.Icc a b) :=
  (continuousOn_id (s := Set.Icc a b)).rpow_const
    (fun _t ht => Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1)))

/-- Integration by parts for a power-weighted square:

  `(1+γ) ∫_ε^x t^{-γ-2} G(t)^2 = ε^{-γ-1} G(ε)^2 - x^{-γ-1} G(x)^2 + 2 ∫_ε^x t^{-γ-1} G(t) ψ(t)`,

obtained by integrating the identity
`(t^{-γ-1} G(t)^2)' = (-γ-1) t^{-γ-2} G(t)^2 + 2 t^{-γ-1} G(t) ψ(t)` over `[ε, x]`
(with `0 < ε ≤ x`, `G` continuous on `[ε,x]`, differentiable on `(ε,x)` with derivative `ψ`,
and `ψ` continuous on `[ε,x]`). -/
theorem rpowSq_ibp {G ψ : ℝ → ℝ} {γ ε x : ℝ} (hε : 0 < ε) (hεx : ε ≤ x)
    (hGc : ContinuousOn G (Set.Icc ε x))
    (hderiv : ∀ t ∈ Set.Ioo ε x, HasDerivAt G (ψ t) t)
    (hψc : ContinuousOn ψ (Set.Icc ε x)) :
    (1 + γ) * (∫ t in ε..x, t ^ (-γ - 2) * G t ^ 2)
      = ε ^ (-γ - 1) * G ε ^ 2 - x ^ (-γ - 1) * G x ^ 2
        + 2 * (∫ t in ε..x, t ^ (-γ - 1) * G t * ψ t) := by
  have hp1 : ContinuousOn (fun t : ℝ => t ^ (-γ - 1)) (Set.Icc ε x) :=
    continuousOn_rpow_Icc (p := -γ - 1) hε
  have hp2 : ContinuousOn (fun t : ℝ => t ^ (-γ - 2)) (Set.Icc ε x) :=
    continuousOn_rpow_Icc (p := -γ - 2) hε
  -- continuity of the pieces on the closed interval
  have hFcont : ContinuousOn (fun t : ℝ => t ^ (-γ - 1) * G t ^ 2) (Set.Icc ε x) :=
    hp1.mul (hGc.pow 2)
  have hg1cont : ContinuousOn (fun t : ℝ => (-γ - 1) * (t ^ (-γ - 2) * G t ^ 2))
      (Set.Icc ε x) :=
    (hp2.mul (hGc.pow 2)).const_mul (-γ - 1)
  have hg2cont : ContinuousOn (fun t : ℝ => 2 * (t ^ (-γ - 1) * G t * ψ t))
      (Set.Icc ε x) :=
    ((hp1.mul hGc).mul hψc).const_mul 2
  have hf'cont : ContinuousOn
      (fun t : ℝ => (-γ - 1) * (t ^ (-γ - 2) * G t ^ 2) + 2 * (t ^ (-γ - 1) * G t * ψ t))
      (Set.Icc ε x) := hg1cont.add hg2cont
  -- the pointwise derivative on the open interval
  have hderivF : ∀ t ∈ Set.Ioo ε x,
      HasDerivAt (fun s : ℝ => s ^ (-γ - 1) * G s ^ 2)
        ((-γ - 1) * (t ^ (-γ - 2) * G t ^ 2) + 2 * (t ^ (-γ - 1) * G t * ψ t)) t := by
    intro t ht
    have htpos : 0 < t := lt_trans hε ht.1
    have hA : HasDerivAt (fun s : ℝ => s ^ (-γ - 1)) ((-γ - 1) * t ^ (-γ - 2)) t := by
      have h := Real.hasDerivAt_rpow_const (x := t) (p := -γ - 1) (Or.inl (ne_of_gt htpos))
      rwa [show (-γ - 1 - 1 : ℝ) = -γ - 2 by ring] at h
    have hB : HasDerivAt (fun s : ℝ => G s ^ 2) (2 * G t * ψ t) t := by
      have h := (hderiv t ht).pow 2
      convert h using 1
      ring
    convert hA.mul hB using 1
    ring
  -- integrability
  have hint : IntervalIntegrable
      (fun t : ℝ => (-γ - 1) * (t ^ (-γ - 2) * G t ^ 2) + 2 * (t ^ (-γ - 1) * G t * ψ t))
      volume ε x := ContinuousOn.intervalIntegrable_of_Icc hεx hf'cont
  have hi1 : IntervalIntegrable (fun t : ℝ => (-γ - 1) * (t ^ (-γ - 2) * G t ^ 2))
      volume ε x := ContinuousOn.intervalIntegrable_of_Icc hεx hg1cont
  have hi2 : IntervalIntegrable (fun t : ℝ => 2 * (t ^ (-γ - 1) * G t * ψ t))
      volume ε x := ContinuousOn.intervalIntegrable_of_Icc hεx hg2cont
  -- fundamental theorem of calculus
  have hFTC : (∫ t in ε..x,
        ((-γ - 1) * (t ^ (-γ - 2) * G t ^ 2) + 2 * (t ^ (-γ - 1) * G t * ψ t)))
      = x ^ (-γ - 1) * G x ^ 2 - ε ^ (-γ - 1) * G ε ^ 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεx hFcont hderivF hint
  -- split the integral
  have hsplit : (∫ t in ε..x,
        ((-γ - 1) * (t ^ (-γ - 2) * G t ^ 2) + 2 * (t ^ (-γ - 1) * G t * ψ t)))
      = (-γ - 1) * (∫ t in ε..x, t ^ (-γ - 2) * G t ^ 2)
        + 2 * (∫ t in ε..x, t ^ (-γ - 1) * G t * ψ t) := by
    rw [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have key : (-γ - 1) * (∫ t in ε..x, t ^ (-γ - 2) * G t ^ 2)
      + 2 * (∫ t in ε..x, t ^ (-γ - 1) * G t * ψ t)
      = x ^ (-γ - 1) * G x ^ 2 - ε ^ (-γ - 1) * G ε ^ 2 := by
    rw [← hsplit]
    exact hFTC
  linarith [key]

end Work.FTS.H2.DivQ
