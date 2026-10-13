/-
# `PkgK5.gK_ibp_fts` — the radial integration by parts for the cut-off mass `m_k`

This is the radial counterpart of the box `θ`-integration-by-parts of the `m`-level argument of
`PkgK5.InterpTraceCore` (`m_k(θ) = ∫_{cA k}^{cB k} χ_k w² ψ(z,θ)² dz`, `ψ = D_zG`).

For the logarithmic cut-off family `χ` (`CutFam χ K`, supported in `[cA k, cB k] = [1/(k+1)²,
(k+1)²]`) and `G` smooth on the open quadrant, the identity

  `∫ χ_k w² (D_zG) ∂_θ²(D_zG) = - ∫ χ_k w² (D_z²G + b·D_zG) ∂_θ²G
                                - ∫ (z χ_k') w² (D_zG) ∂_θ²G`,  `b z = (z-3)/(1+z)`,

is the fundamental theorem of calculus for the flux `F(z) = z w(z)² χ_k(z) (D_zG(z,θ))
(∂_θ²G)(z,θ)`:

  `F' = z w² χ_k (D_zG)(∂_θ²(D_zG)) + w² χ_k (D_z²G + b·D_zG)(∂_θ²G) + z χ_k' w² (D_zG)(∂_θ²G)`,

where `D_z∂_θ²G = ∂_θ²(D_zG)` (Clairaut, `pthIter_two_Dz_eq`) and `(z w²)' = w²·((z-3)/(1+z))`
(the logarithmic derivative of the weight).  Both boundary terms vanish: `χ_k` vanishes at
`z = cA k` and at `z = cB k` by the support hypothesis of `CutFam`.

The engine is `Work.FTS.EllipticEst.RPFresh.radial_ibp_bt` (integration by parts against `w²`
for an arbitrary `C¹` coefficient `φ`, with the boundary terms kept).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore
import Submission.Work.FTS.EllSol.SliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped Real Topology

/-- **Clairaut for the two mixed second derivatives.**  For `G` smooth on the open quadrant,
`z > 0` and `θ ∈ (0,π/2)`, `∂_θ²(D_zG) = D_z(∂_θ²G)`; in the form needed here,
`∂_θ²(D_zG)(z,θ) = z·∂_z(θ' ↦ ∂_θ²G(z',θ))(z)`. -/
private lemma pthIter_two_Dz_eq {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ
      = z * deriv (fun z' => Work.Spaces.pthIter 2 G z' θ) z := by
  rw [show Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ
      = deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ from rfl]
  rw [Work.FTS.EllSol.deriv_deriv_slice_Dz hG hz hθ]
  rfl

/-- The squared radial weight `w²` is `C¹` on `(0,∞)`. -/
private lemma w_sq_contDiffOn :
    ContDiffOn ℝ 1 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h : ContDiffOn ℝ 1 (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := by
    refine ContDiffOn.pow ?_ 2
    refine ContDiffOn.div ?_ ?_ ?_
    · exact (contDiffOn_const.add contDiffOn_id).pow 2
    · exact contDiffOn_id.pow 2
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < z from hz))
  simpa only [Work.Spaces.w] using h

/-- The squared radial weight `w²` is continuous on `(0,∞)`. -/
private lemma w_sq_cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
  w_sq_contDiffOn.continuousOn

theorem gK_ibp_fts {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
        * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ)
      = - (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
            * Work.Spaces.pthIter 2 G z θ)
        - (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
            * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) := by
  have ha : 0 < cA k := cA_pos k
  have hab : cA k ≤ cB k := cA_le_cB k
  have hchi1 : ContDiffOn ℝ 1 (χ k) (Set.Ioi 0) :=
    (hχ.sm k).of_le (by simp [Work.Stability.smoothOrder])
  have hDz1 : ContDiffOn ℝ 1 (fun z => Work.Spaces.Dz G z θ) (Set.Ioi 0) :=
    (hG.Dz.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 G) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hG.pth.pth
  have hp2_1 : ContDiffOn ℝ 1 (fun z => Work.Spaces.pthIter 2 G z θ) (Set.Ioi 0) :=
    (hpth2.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hφ : ContDiffOn ℝ 1 (fun z => χ k z * Work.Spaces.Dz G z θ) (Set.Ioi 0) := hchi1.mul hDz1
  -- the radial integration by parts, with the boundary terms kept
  have hIBP :=
    Work.FTS.EllipticEst.RPFresh.radial_ibp_bt (a := cA k) (b := cB k) ha hab hφ hp2_1
  -- the boundary terms vanish by the support hypothesis of `CutFam`
  have hχa : χ k (cA k) = 0 := hχ.supp k (cA k) ha (Or.inl le_rfl)
  have hχb : χ k (cB k) = 0 := hχ.supp k (cB k) (cB_pos k) (Or.inr le_rfl)
  have hBd : cB k * (Work.Spaces.w (cB k)) ^ 2 * (χ k (cB k) * Work.Spaces.Dz G (cB k) θ)
        * Work.Spaces.pthIter 2 G (cB k) θ
      - cA k * (Work.Spaces.w (cA k)) ^ 2 * (χ k (cA k) * Work.Spaces.Dz G (cA k) θ)
        * Work.Spaces.pthIter 2 G (cA k) θ = 0 := by
    rw [hχa, hχb]; ring
  -- the left-hand side is exactly the left-hand side of the radial IBP (Clairaut)
  have hLHS : (∫ z in (cA k)..(cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
        * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ)
      = ∫ z in (cA k)..(cB k),
          (Work.Spaces.w z) ^ 2 * (χ k z * Work.Spaces.Dz G z θ)
            * (z * deriv (fun z' => Work.Spaces.pthIter 2 G z' θ) z) := by
    refine intervalIntegral.integral_congr (fun z hz => ?_)
    rw [Set.uIcc_of_le hab] at hz
    have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
    rw [pthIter_two_Dz_eq hG hzpos hθ]
    ring
  -- the derivative of the coefficient `φ = χ_k · D_zG`
  have hderivmul : ∀ z ∈ Set.Ioi (0 : ℝ),
      deriv (fun y => χ k y * Work.Spaces.Dz G y θ) z
        = deriv (χ k) z * Work.Spaces.Dz G z θ
          + χ k z * deriv (fun y => Work.Spaces.Dz G y θ) z := by
    intro z hzpos
    have h1 : HasDerivAt (fun y : ℝ => χ k y) (deriv (χ k) z) z :=
      ((hchi1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hzpos)).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => Work.Spaces.Dz G y θ)
        (deriv (fun y : ℝ => Work.Spaces.Dz G y θ) z) z :=
      ((hDz1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hzpos)).hasDerivAt
    exact (h1.mul h2).deriv
  -- the two right-hand integrands agree pointwise
  have hpoint : Set.EqOn
      (fun z => ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * (χ k z * Work.Spaces.Dz G z θ)
        + (z * (Work.Spaces.w z) ^ 2) * deriv (fun y => χ k y * Work.Spaces.Dz G y θ) z)
          * Work.Spaces.pthIter 2 G z θ)
      (fun z => χ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
            * Work.Spaces.pthIter 2 G z θ
        + (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
            * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ)
      (Set.uIcc (cA k) (cB k)) := by
    intro z hz
    simp only []
    rw [Set.uIcc_of_le hab] at hz
    have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
    rw [hderivmul z hzpos]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  have hsubIcc : Set.Icc (cA k) (cB k) ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hD2 : ContDiffOn ℝ 1 (fun z => Work.Spaces.DzIter 2 G z θ) (Set.Ioi 0) :=
    ((hG.DzIter 2).curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hb : ContDiffOn ℝ 1 (fun z : ℝ => (z - 3) / (1 + z)) (Set.Ioi 0) := by
    refine ContDiffOn.div ?_ ?_ ?_
    · exact contDiffOn_id.sub contDiffOn_const
    · exact contDiffOn_const.add contDiffOn_id
    · intro z hz; exact ne_of_gt (by linarith [show (0 : ℝ) < z from hz])
  -- interval integrability of the two pieces of the right-hand side
  have hint1 : IntervalIntegrable
      (fun z => χ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
          * Work.Spaces.pthIter 2 G z θ) volume (cA k) (cB k) := by
    have hcd : ContDiffOn ℝ 1 (fun z => χ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
          * Work.Spaces.pthIter 2 G z θ) (Set.Ioi 0) :=
      ((hchi1.mul w_sq_contDiffOn).mul (hD2.add (hb.mul hDz1))).mul hp2_1
    exact (hcd.continuousOn.mono hsubIcc).intervalIntegrable_of_Icc hab
  have hdchi : ContinuousOn (fun z : ℝ => deriv (χ k) z) (Set.Ioi 0) :=
    hchi1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hint2 : IntervalIntegrable
      (fun z => (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) volume (cA k) (cB k) := by
    have hcdc : ContinuousOn (fun z => (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) (Set.Ioi 0) :=
      (((continuousOn_id.mul hdchi).mul w_sq_cont).mul hDz1.continuousOn).mul hp2_1.continuousOn
    exact (hcdc.mono hsubIcc).intervalIntegrable_of_Icc hab
  -- split the radial IBP right-hand side into the two integrals of the statement
  have hJrhs :
      (∫ z in (cA k)..(cB k),
          ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) * (χ k z * Work.Spaces.Dz G z θ)
            + (z * (Work.Spaces.w z) ^ 2)
              * deriv (fun y => χ k y * Work.Spaces.Dz G y θ) z)
            * Work.Spaces.pthIter 2 G z θ)
      = (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
            * Work.Spaces.pthIter 2 G z θ)
        + (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
            * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) := by
    rw [intervalIntegral.integral_congr hpoint]
    rw [intervalIntegral.integral_add hint1 hint2]
  have hmain : (∫ z in (cA k)..(cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
        * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ)
      = 0 - ((∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
            * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
            * Work.Spaces.pthIter 2 G z θ)
        + (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
            * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ)) := by
    rw [hLHS, hIBP, hBd, hJrhs]
  rw [hmain]
  ring

end Work.FTS.EllSol.PkgK5
