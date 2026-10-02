/-
# `Work.FQCInputs.continuous_muQC_apply`

The invariant Beltrami coefficient `Work.FQC.muQC d fl P t` of the quasiconformal deformation of
the attracting Écalle cylinder depends continuously on the deformation parameter `t`, pointwise:

`Continuous fun t : ℝ => Work.FQC.muQC d fl P t z`.

This is step **S2 (`muQC-CONT`)** of the lead's design
(`Submission/Work/NOTES_LEAD_mandelbar_simple.md` §3.3): it is what makes the conjugated root
`c₂ (t)` — and hence `iteratedDeriv 2 (F (c₂ t)) (θ_t z₁)`, with `θ_t = principal (muQC d fl P t)` —
continuous in the deformation parameter of the simplicity-transfer continuation argument.

The proof unpacks the definition.  The branch `∃ n, (T_c)^[n] z ∈ P` of `muQC` and the least
return time `Nat.find` do not depend on `t`; on the parabolic basin

`muQC d fl P t z = pullAntiIter (T_c) n (pullHoloOn (beltramiOf (ℓ_t)) fl.φa P) z`,

and off it `muQC d fl P t z = 0`.  Two ingredients:

* `Work.FQCInputs.pullAntiIter_eq_comp` — the `n`-fold antiholomorphic pull-back reads off `μ` at
  the *single* point `(T_c)^[n] z`, through a continuous map `Φ` independent of `μ`.  Hence the
  whole `t`-dependence is that of the one number
  `t ↦ pullHoloOn (beltramiOf (ℓ_t)) fl.φa P ((T_c)^[n] z)`;
* `continuous_pullHoloOn` below — the guarded pull-back is continuous in `t` pointwise, because
  the guard `y ∈ P` does not depend on `t` and, having fixed `y`, the coefficient is
  `Work.MRMT.beltramiOf (ℓ_t) (φa y)`, continuous in `t` at *every* point by
  `continuous_beltramiOf_ell`: off the corner lines of the triangle wave this is the rational
  function `± i t / (1 ± i t)` (`continuous_beltramiOf_ell_of_good`), while on the corner lines
  `ℓ_t` fails to be real-differentiable for `t ≠ 0`, so that the dilatation is the junk value `0`
  there (`Work.FQC.not_differentiableAt_ell_of_fract_zero`, `…_half`).
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.ell_beltrami_of_differentiableAt
import Submission.Work.FQCInputs.continuous_beltramiOf_ell_of_good
import Submission.Work.FQCInputs.pullAntiIter_eq_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set MeasureTheory
open scoped Topology
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 1. The dilatation of the MNS twist is continuous in the parameter -/

/-- **The complex dilatation of the MNS twist `ℓ_t` is continuous in `t`**, at every point, with
no restriction on `Re w`: at a corner of the triangle wave `saw` the twist is not
real-differentiable for `t ≠ 0`, so the (junk) dilatation is `0` for every `t`. -/
theorem continuous_beltramiOf_ell (w : ℂ) :
    Continuous fun t : ℝ => Work.MRMT.beltramiOf (Work.FQC.ell t) w := by
  by_cases h0 : Int.fract (w.re + 1/4) = 0
  · have hzero : ∀ t : ℝ, Work.MRMT.beltramiOf (Work.FQC.ell t) w = 0 := by
      intro t
      rcases eq_or_ne t 0 with rfl | ht
      · have hell0 : Work.FQC.ell 0 = id := funext fun v => by simp [Work.FQC.ell_apply]
        rw [hell0]
        exact Work.MRMT.beltramiOf_id w
      · have hd : ¬ DifferentiableAt ℝ (Work.FQC.ell t) w :=
          Work.FQC.not_differentiableAt_ell_of_fract_zero ht h0
        simp [Work.MRMT.beltramiOf, Work.MRMT.dzbar, Work.MRMT.dz,
          fderiv_zero_of_not_differentiableAt hd]
    rw [show (fun t : ℝ => Work.MRMT.beltramiOf (Work.FQC.ell t) w) = fun _ => 0 from
      funext hzero]
    exact continuous_const
  · by_cases h2 : Int.fract (w.re + 1/4) = 1/2
    · have hzero : ∀ t : ℝ, Work.MRMT.beltramiOf (Work.FQC.ell t) w = 0 := by
        intro t
        rcases eq_or_ne t 0 with rfl | ht
        · have hell0 : Work.FQC.ell 0 = id := funext fun v => by simp [Work.FQC.ell_apply]
          rw [hell0]
          exact Work.MRMT.beltramiOf_id w
        · have hd : ¬ DifferentiableAt ℝ (Work.FQC.ell t) w :=
            Work.FQC.not_differentiableAt_ell_of_fract_half ht h2
          simp [Work.MRMT.beltramiOf, Work.MRMT.dzbar, Work.MRMT.dz,
            fderiv_zero_of_not_differentiableAt hd]
      rw [show (fun t : ℝ => Work.MRMT.beltramiOf (Work.FQC.ell t) w) = fun _ => 0 from
        funext hzero]
      exact continuous_const
    · exact continuous_beltramiOf_ell_of_good w h0 h2

/-! ## 2. The guarded pull-back of the Fatou coordinate is continuous in the parameter -/

/-- **The pull-back `pullHoloOn (beltramiOf (ℓ_t)) φ P`, evaluated at a fixed point `y`, is
continuous in `t`.**  The guard `y ∈ P` is independent of `t`, and off the corner lines the
coefficient at the fixed point `φ y` is continuous in `t`. -/
theorem continuous_pullHoloOn (P : Set ℂ) (φ : ℂ → ℂ) (y : ℂ) :
    Continuous fun t : ℝ =>
      Work.FQC.pullHoloOn (Work.MRMT.beltramiOf (Work.FQC.ell t)) φ P y := by
  by_cases hy : y ∈ P
  · rw [show (fun t : ℝ =>
          Work.FQC.pullHoloOn (Work.MRMT.beltramiOf (Work.FQC.ell t)) φ P y)
        = fun t => Work.MRMT.beltramiOf (Work.FQC.ell t) (φ y) * star (deriv φ y) / deriv φ y
        from funext fun t => by simp [Work.FQC.pullHoloOn, hy]]
    exact ((continuous_beltramiOf_ell (φ y)).mul_const _).div_const _
  · rw [show (fun t : ℝ =>
          Work.FQC.pullHoloOn (Work.MRMT.beltramiOf (Work.FQC.ell t)) φ P y)
        = fun _ => (0 : ℂ) from funext fun t => by simp [Work.FQC.pullHoloOn, hy]]
    exact continuous_const

/-! ## 3. Continuity of `muQC` in the parameter -/

theorem continuous_muQC_apply {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Set ℂ) (z : ℂ) :
    Continuous fun t : ℝ => Work.FQC.muQC d fl P t z := by
  by_cases h : ∃ n : ℕ, (Tantibar c)^[n] z ∈ P
  · -- the point lies in the basin: the return time and the branch are independent of `t`
    have hmem : z ∈ Work.FQC.basin d P := h
    have hfun : (fun t : ℝ => Work.FQC.muQC d fl P t z)
        = fun t => Work.FQC.pullAntiIter (Tantibar c) (Nat.find hmem)
            (Work.FQC.pullHoloOn (Work.MRMT.beltramiOf (Work.FQC.ell t)) fl.φa P) z := by
      funext t
      exact Work.FQC.muQC_of_mem d hmem
    rw [hfun]
    obtain ⟨Φ, hΦc, hΦ⟩ := pullAntiIter_eq_comp (Tantibar c) (Nat.find hmem) z
    have hinner : Continuous fun t : ℝ =>
        Work.FQC.pullHoloOn (Work.MRMT.beltramiOf (Work.FQC.ell t)) fl.φa P
          ((Tantibar c)^[Nat.find hmem] z) :=
      continuous_pullHoloOn P fl.φa ((Tantibar c)^[Nat.find hmem] z)
    exact (hΦc.comp hinner).congr fun t => (hΦ (Work.FQC.pullHoloOn
      (Work.MRMT.beltramiOf (Work.FQC.ell t)) fl.φa P)).symm
  · -- off the basin the coefficient vanishes identically in `t`
    have hnot : z ∉ Work.FQC.basin d P := h
    have hfun : (fun t : ℝ => Work.FQC.muQC d fl P t z) = fun _ => (0 : ℂ) := by
      funext t
      exact Work.FQC.muQC_of_notMem d hnot
    rw [hfun]
    exact continuous_const

end Work.FQCInputs

end
