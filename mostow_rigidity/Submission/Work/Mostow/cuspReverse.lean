import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.cuspMap
import Submission.Work.Mostow.cuspCoshFactor
import Submission.Work.Mostow.cuspReverse_arith

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

set_option linter.unusedVariables false

/-- **Reverse cusp estimate.**  If `ψ` carries the hyperplane `ξ^⊥` into `η^⊥` and is a
quasi-isometry of constants `L, Cq` in both directions, then two points `u`, `v` whose levels at
`ξ` are at most `exp T ≤ 1` and whose `η`-horospherical images

`hptOf η (ψ (yc ξ u)) (lam * lev ξ u)` and `hptOf η (ψ (yc ξ v)) (lam * lev ξ v)`

are within hyperbolic distance `M` satisfy

`hdist u v ≤ arcosh (cosh M + 2 L² cosh M / lam² + Cq²)`. -/
theorem cuspReverse {n : ℕ} (hI : Work.Mostow.HypIsoData n)
    {ξ η : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hη : η ∈ Submission.Mostow.Sph n)
    {lam T M L Cq : ℝ} (hlam : 0 < lam) (hT : Real.exp T ≤ 1) (hL : 1 ≤ L) (hCq : 0 ≤ Cq)
    {ψ : Submission.Mostow.E n → Submission.Mostow.E n}
    (hψperp : ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ (ψ x) η = 0)
    (hψfwd : ∀ x y : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 →
      ‖ψ x - ψ y‖ ≤ L * ‖x - y‖ + Cq)
    (hψrev : ∀ x y : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 →
      ‖x - y‖ ≤ L * ‖ψ x - ψ y‖ + Cq)
    {u v : Submission.Mostow.E n} (hu : Work.Mostow.lev ξ u ≤ Real.exp T)
    (hv : Work.Mostow.lev ξ v ≤ Real.exp T)
    (hM : Submission.Mostow.hdist (Work.Mostow.hptOf η (ψ (Work.Mostow.yc ξ u))
        (lam * Work.Mostow.lev ξ u))
      (Work.Mostow.hptOf η (ψ (Work.Mostow.yc ξ v)) (lam * Work.Mostow.lev ξ v)) ≤ M) :
    Submission.Mostow.hdist u v ≤
      Real.arcosh (Real.cosh M + 2 * L ^ 2 * Real.cosh M / lam ^ 2 + Cq ^ 2) := by
  have hsu : 0 < Work.Mostow.lev ξ u := Work.Mostow.lev_pos ξ hξ u
  have htv : 0 < Work.Mostow.lev ξ v := Work.Mostow.lev_pos ξ hξ v
  have ha : inner ℝ (Work.Mostow.yc ξ u) ξ = 0 := Work.Mostow.yc_orth hξ
  have hb : inner ℝ (Work.Mostow.yc ξ v) ξ = 0 := Work.Mostow.yc_orth hξ
  -- The `cosh` of the image distance in terms of the levels and the images.
  have hcoshImg := cuspCoshFactor hξ hη hlam hψperp u v
  -- The image distance is at most `M`, hence its `cosh` at most `cosh M`.
  have hM0 : 0 ≤ M := le_trans (hI.nonneg _ _) hM
  have hImg_le : Real.cosh (Submission.Mostow.hdist
        (Work.Mostow.hptOf η (ψ (Work.Mostow.yc ξ u)) (lam * Work.Mostow.lev ξ u))
        (Work.Mostow.hptOf η (ψ (Work.Mostow.yc ξ v)) (lam * Work.Mostow.lev ξ v))) ≤
      Real.cosh M := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_of_nonneg (hI.nonneg _ _), abs_of_nonneg hM0]
    exact hM
  have hY : Real.cosh (Real.log (Work.Mostow.lev ξ u / Work.Mostow.lev ξ v))
        + (lam * Work.Mostow.lev ξ u) * (lam * Work.Mostow.lev ξ v) / 2
            * ‖ψ (Work.Mostow.yc ξ u) - ψ (Work.Mostow.yc ξ v)‖ ^ 2 ≤ Real.cosh M := by
    rw [← hcoshImg]; exact hImg_le
  -- The levels are at most one, so their product is at most one.
  have hst : Work.Mostow.lev ξ u * Work.Mostow.lev ξ v ≤ 1 := by
    have h1 : Work.Mostow.lev ξ u ≤ 1 := le_trans hu hT
    have h2 : Work.Mostow.lev ξ v ≤ 1 := le_trans hv hT
    calc Work.Mostow.lev ξ u * Work.Mostow.lev ξ v ≤ Work.Mostow.lev ξ u * 1 :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hsu)
      _ = Work.Mostow.lev ξ u := mul_one _
      _ ≤ 1 := h1
  have hAB : ‖Work.Mostow.yc ξ u - Work.Mostow.yc ξ v‖
      ≤ L * ‖ψ (Work.Mostow.yc ξ u) - ψ (Work.Mostow.yc ξ v)‖ + Cq := hψrev _ _ ha hb
  have harith := cuspReverse_arith (s := Work.Mostow.lev ξ u) (t := Work.Mostow.lev ξ v)
      (L := L) (lam := lam)
      (Cq := Cq) (A := ‖Work.Mostow.yc ξ u - Work.Mostow.yc ξ v‖)
      (B := ‖ψ (Work.Mostow.yc ξ u) - ψ (Work.Mostow.yc ξ v)‖)
      (X := Real.cosh (Real.log (Work.Mostow.lev ξ u / Work.Mostow.lev ξ v))) (M := M)
      (le_of_lt hsu) (le_of_lt htv) hst (le_trans zero_le_one hL) hlam hCq
      (norm_nonneg _) (norm_nonneg _) hAB (Real.one_le_cosh _) hM0 hY
  have hcoshuv : Real.cosh (Submission.Mostow.hdist u v)
      = Real.cosh (Real.log (Work.Mostow.lev ξ u / Work.Mostow.lev ξ v))
        + Work.Mostow.lev ξ u * Work.Mostow.lev ξ v / 2
            * ‖Work.Mostow.yc ξ u - Work.Mostow.yc ξ v‖ ^ 2 := Work.Mostow.levYcFormula hξ u v
  have hcosh_le : Real.cosh (Submission.Mostow.hdist u v)
      ≤ Real.cosh M + 2 * L ^ 2 * Real.cosh M / lam ^ 2 + Cq ^ 2 := by
    rw [hcoshuv]; exact harith
  have hR : 0 < Real.cosh M + 2 * L ^ 2 * Real.cosh M / lam ^ 2 + Cq ^ 2 := by
    have h1 : (1 : ℝ) ≤ Real.cosh M := Real.one_le_cosh M
    have h2 : 0 ≤ 2 * L ^ 2 * Real.cosh M / lam ^ 2 := by positivity
    have h3 : 0 ≤ Cq ^ 2 := sq_nonneg Cq
    linarith
  calc Submission.Mostow.hdist u v
      = Real.arcosh (Real.cosh (Submission.Mostow.hdist u v)) :=
        (Real.arcosh_cosh (hI.nonneg u v)).symm
    _ ≤ Real.arcosh (Real.cosh M + 2 * L ^ 2 * Real.cosh M / lam ^ 2 + Cq ^ 2) :=
        (Real.arcosh_le_arcosh (Real.cosh_pos _) hR).mpr hcosh_le

end Work.Mostow
