/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsRHSPSup.lean` — the family form of the sup bound of the scheme's
# right-hand side, and `hbdd`

`EpsLimVolterraP` (the Volterra half of `E5-4`, proved) takes as a hypothesis the uniform bound

  `hbdd : ∀ p ∈ Q0, ∃ C, ∀ n, ∀ s ∈ Icc 0 T, |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C`

at each point of the open quadrant.  Because the constant is **uniform in `n`**, the bricks that
produce it must be stated in *family* form: a per-family existential (`∃ B, ∀ s p, |…| ≤ B` for a
fixed `ε`, `g`) does **not** give a common `B`, since the existential witness of a per-family lemma
is not definitionally independent of the family's own hypotheses (the session-14 probe
`_probe_unif.lean` records the failed `rfl`-congruence for `epsWP_sup_le_of_mem` and
`epsWP_hkMem4_bnd`).

This module performs the part of the assembly that *is* family-uniform by construction:

* `epsWP_corr_le_fam` — a common `Cc` bounding `|L₁₂(J_{ε n}(epsWP … s))(0)|`, from a common
  ℋ⁴-size `KW` and the per-`n` smoothness of `epsWP` (whose production needs no constant:
  `smoothOpen_epsWP`);
* `epsRHSP_sup_le_fam` — a common bound for `epsRHSP`, from a common value bound of `epsWP` on a
  window and the common correction bound: the pointwise split
  `epsRHSP = J_ε(epsWP) − (L₁₂(J_ε(epsWP))(0)/pzNorm)·bump`, the mollifier average
  `abs_Jeps_le_sup` and the compact bound `exists_bound_mixed_bump` of the correction profile;
* `hbdd_of_mem` — the `hbdd` shape itself: for every point `p` of the quadrant, a bound uniform in
  `n` and `s`, taking the window compact and the two common constants as hypotheses.

The two remaining *inputs* (a common ℋ⁴-size of `epsWP`, and a common value bound of `epsWP` on a
window) are the family forms of `epsWP_hkMem4_bnd` and `epsWP_sup_le_of_mem`; see
`NOTES_session14.md` §3.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRHSPBound
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
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

/-- **A common `L₁₂`-zero-mode bound of the mollified right-hand side, in family form.** -/
theorem epsWP_corr_le_fam {α T KW : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G : ℕ → Fam} {ε : ℕ → ℝ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hsm : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s))
    (hKW : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (epsWP α ρ (ε n) Φs E (G n) s) ∧
        Work.FTS.Nonlin.Xn α (epsWP α ρ (ε n) Φs E (G n) s) ≤ KW) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ Cc := by
  obtain ⟨C, hC0, hZ⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨CJ, hCJ0, hSqJ⟩ := HkSq_Jeps_le ρ hρ.moll
  refine ⟨C * Real.exp (CJ / 2) * max KW 0 + 1, by positivity, ?_⟩
  intro n s hs
  have hεn : 0 < ε n := (hε n).1
  have hεn1 : ε n ≤ 1 := (hε n).2
  have hexp1 : Real.exp (CJ * ε n / 2) ≤ Real.exp (CJ / 2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hCJ0, hεn1]
  obtain ⟨hmem, hbnd⟩ := hKW n s hs
  have hsm' : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry (epsWP α ρ (ε n) Φs E (G n) s)) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsm n s hs)
  have hWmem : Work.Spaces.HkMem α 4 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) :=
    HkMem_Jeps hρ.moll hα hεn hsm' hmem
  have hWsm : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) :=
    smoothOpen_Jeps ρ hρ hεn hsm'
  have h1 := hZ α hα.1 hα.2 _ ⟨hWsm, hWmem⟩
  have hKW0 : 0 ≤ KW := le_trans (Work.Spaces.HkNorm_nonneg α 4 _) hbnd
  have hsqW : Work.Spaces.HkSq α 4 (epsWP α ρ (ε n) Φs E (G n) s) ≤ KW ^ 2 := by
    have h : Work.Spaces.HkSq α 4 (epsWP α ρ (ε n) Φs E (G n) s)
        = (Work.FTS.Nonlin.Xn α (epsWP α ρ (ε n) Φs E (G n) s)) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
    rw [h]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) hbnd 2
  have hXnJ : Work.FTS.Nonlin.Xn α (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s))
      ≤ Real.exp (CJ / 2) * max KW 0 := by
    have hsq := hSqJ α hα 4 (ε n) hεn hεn1 _ hsm' hmem hWmem
    have hkey : Work.Spaces.HkSq α 4 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s))
        ≤ Real.exp (CJ * ε n) * KW ^ 2 :=
      le_trans hsq (mul_le_mul_of_nonneg_left hsqW (Real.exp_pos _).le)
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)))
        ≤ Real.sqrt (Real.exp (CJ * ε n) * KW ^ 2) := Real.sqrt_le_sqrt hkey
      _ = Real.exp (CJ * ε n / 2) * KW := by
          rw [Real.sqrt_mul (Real.exp_pos _).le, Real.sqrt_sq hKW0, ← Real.exp_half]
      _ ≤ Real.exp (CJ / 2) * max KW 0 :=
          mul_le_mul hexp1 (le_max_left _ _) hKW0 (Real.exp_pos _).le
  have h2 : |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0|
      ≤ C * (Real.exp (CJ / 2) * max KW 0) :=
    le_trans h1 (mul_le_mul_of_nonneg_left hXnJ hC0.le)
  have h3 : 0 ≤ C * (Real.exp (CJ / 2) * max KW 0) :=
    mul_nonneg hC0.le (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))
  linarith [h2]

/-- **A common sup bound for `epsRHSP` on a compact, in family form.** -/
theorem epsRHSP_sup_le_fam {α C₀ Ce Cs T B Cc : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G : ℕ → Fam} {ε : ℕ → ℝ}
    (hρ : IsSmoothKernel ρ) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    {K K' : Set (ℝ × ℝ)} (hKc : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hKK' : K ⊆ K')
    (hshift : ∀ n : ℕ, ∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε n → |q.2| ≤ ε n →
      (zShift p.1 q.1, thShift p.2 q.2) ∈ K')
    (hB0 : 0 ≤ B)
    (hwp : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K',
      |epsWP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ B)
    (hCc0 : 0 ≤ Cc)
    (hcorr : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ Cc) :
    ∃ B' : ℝ, 0 < B' ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ p : ℝ × ℝ, p ∈ K →
      |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ B' := by
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hKc
  have hpz : 0 < pzNorm := PZeroAux.pzNorm_pos
  refine ⟨B + (Cc / pzNorm) * Cb + 1, by positivity, ?_⟩
  intro n s hs p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
  have hsplit : epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2
      = Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2 := by
    rw [epsRHSP_eq_Pz_Jeps_epsWP, Pz_apply]
  have hJ : |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2| ≤ B :=
    abs_Jeps_le_sup ρ hρ.moll (hε n).1 hz ⟨hθ0, hθ1⟩
      (fun q hq1 hq2 => hwp n s hs (zShift p.1 q.1, thShift p.2 q.2) (hshift n p hp q hq1 hq2)) hB0
  have hbu : |bump p.1 p.2| ≤ Cb := by
    have h := hbump 0 0 (by norm_num) p hp
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h
  have hcor : |(Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
      * bump p.1 p.2| ≤ (Cc / pzNorm) * Cb := by
    rw [abs_mul]
    have hL := hcorr n s hs
    have hc : |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm|
        ≤ Cc / pzNorm := by
      rw [abs_div, abs_of_pos hpz]
      exact div_le_div_of_nonneg_right hL hpz.le
    exact mul_le_mul hc hbu (abs_nonneg _) (div_nonneg hCc0 hpz.le)
  rw [hsplit]
  have htri : |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2|
      ≤ |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2|
        + |(Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2| := by
    have h := abs_add_le (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2)
      (-((Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
        * bump p.1 p.2))
    simpa only [sub_eq_add_neg, abs_neg] using h
  calc |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2|
      ≤ |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2|
        + |(Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2| := htri
    _ ≤ B + (Cc / pzNorm) * Cb := add_le_add hJ hcor
    _ ≤ B + (Cc / pzNorm) * Cb + 1 := by linarith

/-- **`hbdd`**, the shape consumed by `EpsLimVolterraP`: at every point of the open quadrant, a
bound on the scheme's right-hand side *uniform in the family index and in the fake time*.

The two inputs are the family forms of the scalar bounds: a common value bound `B` of `epsWP` on a
window compact `K'` of `p`, and the common correction bound `Cc` (produced by
`epsWP_corr_le_fam`). -/
theorem hbdd_of_mem {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G : ℕ → Fam} {ε : ℕ → ℝ}
    (hρ : IsSmoothKernel ρ) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0)
    {B Cc : ℝ} (hB0 : 0 ≤ B) (hCc0 : 0 ≤ Cc)
    (hwin : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ p ∈ K' ∧
      (∀ n : ℕ, ∀ q : ℝ × ℝ, |q.1| ≤ ε n → |q.2| ≤ ε n →
        (zShift p.1 q.1, thShift p.2 q.2) ∈ K') ∧
      ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ q ∈ K',
        |epsWP α ρ (ε n) Φs E (G n) s q.1 q.2| ≤ B)
    (hcorr : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ Cc) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hpK', hshift, hwp⟩ := hwin
  have hKc : IsCompact ({p} : Set (ℝ × ℝ)) := isCompact_singleton
  have hKQ : ({p} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; subst hq; exact hp
  have hKK' : ({p} : Set (ℝ × ℝ)) ⊆ K' := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; subst hq; exact hpK'
  obtain ⟨B', hB'0, hbd⟩ := epsRHSP_sup_le_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (T := T) (B := B) (Cc := Cc) hρ hε hKc hKQ hKK'
    (fun n q hq r hr1 hr2 => by
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hshift n r hr1 hr2)
    hB0 hwp hCc0 hcorr
  refine ⟨B', fun n s hs => hbd n s hs p (Set.mem_singleton _)⟩

end Work.FTS.StrongEps
