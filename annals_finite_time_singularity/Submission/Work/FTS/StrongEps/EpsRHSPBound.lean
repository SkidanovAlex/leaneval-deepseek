/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsRHSPBound.lean` — the sup bound of the scheme's right-hand side
# on a compact, from the sup bound of `epsWP`

`EpsLimVolterraP` (the Volterra half of `E5-4`, proved) takes as a hypothesis the uniform bound

  `hbdd : ∀ p ∈ Q0, ∃ C, ∀ n, ∀ s ∈ Icc 0 T, |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C`

at each point of the open quadrant.  The scheme's right-hand side is the *projection of the
mollification*, `epsRHSP … s = Pz (J_ε (epsWP … s))` (`epsRHSP_eq_Pz_Jeps_epsWP`), so its value at a
point of the quadrant is controlled by

* the **average** of `epsWP … s` over the fixed window `{(zShift z q₁, thShift θ q₂) : |q| ≤ ε}`
  (`abs_Jeps_le_sup` — this is why only the *value* bound of `epsWP` is needed here, not the
  slot-wise bound that `EpsRHSP_slotSup` consumes), and
* the rank-one correction `(L₁₂(J_ε(epsWP))(0)/pzNorm)·bump`, whose profile part is bounded on the
  compact by `exists_bound_mixed_bump`.

Both are hypotheses here, and both are produced on the proof path: the first by
`Work.FTS.StrongEps.epsWP_sup_le_of_mem` (from the interface data alone, on the window compact
`K'`), the second by the ℋ⁴-size of `epsWP` (`epsWP_hkMem4_bnd`) through
`OpenPkg.l12zero_field` + `HkSq_Jeps_le` once the smoothness of `epsWP` is available
(`smoothOpen_epsWP`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.JepsBasic
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.OpenPkg.l12zero_field

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The uniform sup bound of `epsRHSP` on a compact, from the value bound of `epsWP` on a window
and the correction bound.**  The `K'` is a compact containing the mollification window of every
`p ∈ K` (`hshift`), and `B`/`Cc` bound `epsWP` resp. the `L₁₂`-zero mode of the mollified right-hand
side, uniformly in the fake time. -/
theorem epsRHSP_sup_le_of_epsWP_sup {α C₀ Ce Cs T B Cc ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g : Fam}
    (hρ : IsSmoothKernel ρ) (hε : ε ∈ Set.Ioc 0 1)
    {K K' : Set (ℝ × ℝ)} (hKc : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hKK' : K ⊆ K')
    (hshift : ∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
      (zShift p.1 q.1, thShift p.2 q.2) ∈ K')
    (hB0 : 0 ≤ B)
    (hwp : ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K',
      |epsWP α ρ ε Φs E g s p.1 p.2| ≤ B)
    (hCc0 : 0 ≤ Cc)
    (hcorr : ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0| ≤ Cc) :
    ∃ B' : ℝ, 0 < B' ∧ ∀ s ∈ Set.Icc 0 T, ∀ p : ℝ × ℝ, p ∈ K →
      |epsRHSP α ρ ε Φs E g s p.1 p.2| ≤ B' := by
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hKc
  have hpz : 0 < pzNorm := PZeroAux.pzNorm_pos
  refine ⟨B + (Cc / pzNorm) * Cb + 1, by positivity, ?_⟩
  intro s hs p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
  -- the split of the projection
  have hsplit : epsRHSP α ρ ε Φs E g s p.1 p.2
      = Jeps ρ ε (epsWP α ρ ε Φs E g s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
          * bump p.1 p.2 := by
    rw [epsRHSP_eq_Pz_Jeps_epsWP, Pz_apply]
  -- the mollifier average
  have hJ : |Jeps ρ ε (epsWP α ρ ε Φs E g s) p.1 p.2| ≤ B :=
    abs_Jeps_le_sup ρ hρ.moll hε.1 hz ⟨hθ0, hθ1⟩
      (fun q hq1 hq2 => hwp s hs (zShift p.1 q.1, thShift p.2 q.2) (hshift p hp q hq1 hq2)) hB0
  -- the correction
  have hbu : |bump p.1 p.2| ≤ Cb := by
    have h := hbump 0 0 (by norm_num) p hp
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h
  have hcor : |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
      * bump p.1 p.2| ≤ (Cc / pzNorm) * Cb := by
    rw [abs_mul]
    have hL := hcorr s hs
    have hc : |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm|
        ≤ Cc / pzNorm := by
      rw [abs_div, abs_of_pos hpz]
      exact div_le_div_of_nonneg_right hL hpz.le
    exact mul_le_mul hc hbu (abs_nonneg _) (div_nonneg hCc0 hpz.le)
  rw [hsplit]
  have htri : |Jeps ρ ε (epsWP α ρ ε Φs E g s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
          * bump p.1 p.2|
      ≤ |Jeps ρ ε (epsWP α ρ ε Φs E g s) p.1 p.2|
        + |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
          * bump p.1 p.2| := by
    have h := abs_add_le (Jeps ρ ε (epsWP α ρ ε Φs E g s) p.1 p.2)
      (-((Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm) * bump p.1 p.2))
    simpa only [sub_eq_add_neg, abs_neg] using h
  calc |Jeps ρ ε (epsWP α ρ ε Φs E g s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
          * bump p.1 p.2|
      ≤ |Jeps ρ ε (epsWP α ρ ε Φs E g s) p.1 p.2|
        + |(Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0 / pzNorm)
          * bump p.1 p.2| := htri
    _ ≤ B + (Cc / pzNorm) * Cb := add_le_add hJ hcor
    _ ≤ B + (Cc / pzNorm) * Cb + 1 := by linarith

/-! ## The correction bound -/

/-- **The `L₁₂`-zero mode of the *mollified* right-hand side is uniformly bounded.**  From the
ℋ⁴-honesty and ℋ⁴-size of `epsWP … s` (`hKW`) and the smoothness of `epsWP … s` (`hsm`, used to
feed `J_ε` and the ℋ⁴-honesty of its image), the mollifier gain `HkSq_Jeps_le` and the zero-mode
bound `OpenPkg.l12zero_field` give a constant `Cc` bounding `|L₁₂ (J_ε (epsWP … s))(0)|` uniformly
in the fake time. -/
theorem epsWP_corr_le {α T KW ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : ε ∈ Set.Ioc 0 1)
    (hsm : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ ε Φs E g s))
    (hKW : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (epsWP α ρ ε Φs E g s) ∧
      Work.FTS.Nonlin.Xn α (epsWP α ρ ε Φs E g s) ≤ KW) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0| ≤ Cc := by
  obtain ⟨C, hC0, hZ⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨CJ, hCJ0, hSqJ⟩ := HkSq_Jeps_le ρ hρ.moll
  have hexp1 : Real.exp (CJ * ε / 2) ≤ Real.exp (CJ / 2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hCJ0, hε.2]
  refine ⟨C * Real.exp (CJ / 2) * max KW 0 + 1, by positivity, ?_⟩
  intro s hs
  obtain ⟨hmem, hbnd⟩ := hKW s hs
  have hsm' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (epsWP α ρ ε Φs E g s)) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsm s hs)
  have hWmem : Work.Spaces.HkMem α 4 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) :=
    HkMem_Jeps hρ.moll hα hε.1 hsm' hmem
  have hWsm : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε (epsWP α ρ ε Φs E g s)) :=
    smoothOpen_Jeps ρ hρ hε.1 hsm'
  have h1 := hZ α hα.1 hα.2 _ ⟨hWsm, hWmem⟩
  have hKW0 : 0 ≤ KW := le_trans (Work.Spaces.HkNorm_nonneg α 4 _) hbnd
  have hXnW : Work.FTS.Nonlin.Xn α (epsWP α ρ ε Φs E g s) ≤ max KW 0 :=
    le_trans hbnd (le_max_left _ _)
  have hsqW : Work.Spaces.HkSq α 4 (epsWP α ρ ε Φs E g s) ≤ KW ^ 2 := by
    have h : Work.Spaces.HkSq α 4 (epsWP α ρ ε Φs E g s)
        = (Work.FTS.Nonlin.Xn α (epsWP α ρ ε Φs E g s)) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
    rw [h]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) hbnd 2
  have hXnJ : Work.FTS.Nonlin.Xn α (Jeps ρ ε (epsWP α ρ ε Φs E g s))
      ≤ Real.exp (CJ / 2) * max KW 0 := by
    have hsq := hSqJ α hα 4 ε hε.1 hε.2 _ hsm' hmem hWmem
    have hkey : Work.Spaces.HkSq α 4 (Jeps ρ ε (epsWP α ρ ε Φs E g s))
        ≤ Real.exp (CJ * ε) * KW ^ 2 :=
      le_trans hsq (mul_le_mul_of_nonneg_left hsqW (Real.exp_pos _).le)
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ ε (epsWP α ρ ε Φs E g s)))
        ≤ Real.sqrt (Real.exp (CJ * ε) * KW ^ 2) := Real.sqrt_le_sqrt hkey
      _ = Real.exp (CJ * ε / 2) * KW := by
          rw [Real.sqrt_mul (Real.exp_pos _).le, Real.sqrt_sq hKW0, ← Real.exp_half]
      _ ≤ Real.exp (CJ / 2) * max KW 0 :=
          mul_le_mul hexp1 (le_max_left _ _) hKW0 (Real.exp_pos _).le
  have h2 : |Work.Construction.L12 (Jeps ρ ε (epsWP α ρ ε Φs E g s)) 0|
      ≤ C * (Real.exp (CJ / 2) * max KW 0) :=
    le_trans h1 (mul_le_mul_of_nonneg_left hXnJ hC0.le)
  have h3 : 0 ≤ C * (Real.exp (CJ / 2) * max KW 0) :=
    mul_nonneg hC0.le (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))
  linarith [h2]

end Work.FTS.StrongEps
