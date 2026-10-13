/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Pz ∘ J_ε` is bounded on `ℋ^k` for `4 ≤ k ≤ 6`, uniformly in `α` and `ε`

The projection `Work.FTS.StrongEps.Pz f = f − (L₁₂ f 0 / pzNorm) • bump` and the
log-coordinate mollifier `J_ε = Work.FTS.StrongEps.Jeps ρ ε` are both bounded on the weighted
space `ℋ^k` for every order `k ∈ [4,6]`, with constants independent of `α ∈ (0,1]`:

* `hkNorm_Pz_le_of_ge_four` below: `‖Pz f‖_{ℋᵏ} ≤ A ‖f‖_{ℋᵏ}` for `4 ≤ k ≤ 6` (`SmoothOpen f`,
  `HkMem α k f`).  This is the `k`-version of `Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le`
  (which states the bound at order `k` against `‖f‖_{ℋ⁶}`) and of the proved
  `E5G.hkNorm_Pz_le_four` (`k = 4`, bound against `‖f‖_{ℋ⁴}`).  The same proof works at every
  order `k ≥ 4` because the zero-mode bound `l12zero_field` is an `ℋ⁴`-statement and
  `ℋ⁴ ⊆ ℋᵏ` for `k ≥ 4` (`HkNorm_mono_of_mem`), while the correction profile `bump` is
  uniformly bounded in `ℋᵏ` for `k ≤ 6`.
* `HkSq_Jeps_le` (the `E1` chapter): `HkSq α k (J_ε f) ≤ e^{Cε} HkSq α k f`, with the
  membership `HkMem α k (J_ε f)` supplied by `HkMem_Jeps`.

Composing them gives the requested bound

  `‖Pz (J_ε f)‖_{ℋᵏ} ≤ A ‖f‖_{ℋᵏ}`,

with `A = A₁ e^{C/2}`, for every `α ∈ (0,1]`, `k ∈ [4,6]`, `ε ∈ (0,1]` and every
`C^∞`-profile `f` of class `ℋᵏ`.

Every declaration in this file is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5G.hkNorm_Pz_le_four
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.EllipticEst.HkNorm_add_fts
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.OpenPkg.l12zero_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The projection `Pz` is bounded in `ℋᵏ` for every order `k ≥ 4` -/

/-- **`Pz` is bounded on `ℋᵏ` for every order `k ∈ [4,6]`, uniformly in `α`.**

`Pz f = f + (−c) • bump` with `c = L₁₂ f 0 / pzNorm`.  The zero-mode coefficient is controlled
by `|L₁₂ f 0| ≤ C₁ ‖f‖_{ℋ⁴} ≤ C₁ ‖f‖_{ℋᵏ}` (`OpenPkg.l12zero_field` and the monotonicity
`HkNorm_mono_of_mem`, valid because `4 ≤ k`), the correction profile is uniformly bounded by
`‖bump‖_{ℋᵏ} ≤ B` (`PZeroAux.exists_HkNorm_bump_le`, `k ≤ 6`), and the two pieces are glued with
the subadditivity `HkNorm_add_fts` and the absolute homogeneity `HkNorm_const_mul` of the open
quadrant norm.  The constant is `A₁ = √2 (1 + C₁ B / pzNorm)`, exactly as in
`E5G.hkNorm_Pz_le_four`. -/
theorem hkNorm_Pz_le_of_ge_four :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ (k : ℕ), 4 ≤ k → k ≤ 6 →
      ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
        Work.Spaces.HkMem α k f →
          Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz f)
            ≤ A * Work.Spaces.HkNorm α k f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα k hk4 hk6 f hfsm hmk
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    -- descent `ℋᵏ → ℋ⁴` (`4 ≤ k`)
    have hm4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm 4 hk4 hmk
    -- the zero-mode bound, in `ℋ⁴`
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hm4⟩
    -- and ascent `ℋ⁴ → ℋᵏ`
    have hnorm4k : Work.Spaces.HkNorm α 4 f ≤ Work.Spaces.HkNorm α k f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem hk4 hmk
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    -- the correction coefficient is controlled by the `ℋᵏ`-norm
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α k f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 4 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by ring
        _ ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α k f :=
            mul_le_mul_of_nonneg_left hnorm4k hcoefnn
    -- the correction profile
    have hbmem : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump :=
      Work.FTS.StrongEps.PZeroAux.hkMem_bump α k
    have hbnorm : Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B :=
      hB α hα k hk6
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen _
        Work.FTS.StrongEps.smoothOpen_bump
    have hgmem : Work.Spaces.HkMem α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _ hbmem
    -- `Pz f` in the additive shape needed by the subadditivity lemma
    have hPz : Work.FTS.StrongEps.Pz f
        = fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply]
      ring
    rw [hPz]
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α k
      (fun n => hfsm.forall n) (fun n => hgsm.forall n) hmk hgmem
    have hcm : Work.Spaces.HkNorm α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α k _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α k (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α k f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α k f := by ring

/-! ## The main theorem -/

/-- **`Pz ∘ J_ε` is bounded on `ℋᵏ`, uniformly in `α ∈ (0,1]`, `k ∈ [4,6]` and `ε ∈ (0,1]`.**

The mollifier `J_ε` preserves `ℋᵏ` (`HkMem_Jeps`), its `ℋᵏ`-norm grows at most by `e^{Cε/2}`
(the square root of the `E1` bound `HkSq_Jeps_le`), and `Pz` is bounded on `ℋᵏ`
(`hkNorm_Pz_le_of_ge_four`); note that `J_ε f` is `SmoothOpen` for a smooth kernel
(`SmoothOpen_Jeps`).  The resulting constant is `A₁ e^{C/2}`, independent of `ε ≤ 1`. -/
theorem hkNorm_PzJeps_le_gen (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ (k : ℕ), 4 ≤ k → k ≤ 6 →
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) 1 → ∀ f : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α k f →
          Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
            ≤ A * Work.Spaces.HkNorm α k f := by
  obtain ⟨A₁, hA₁pos, hA₁⟩ := hkNorm_Pz_le_of_ge_four
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  refine ⟨A₁ * Real.exp (C / 2), by positivity, ?_⟩
  intro α hα k hk4 hk6 ε hε f hf hmk
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- `J_ε f` is `C^∞` on the open quadrant and of class `ℋᵏ`
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (Work.FTS.StrongEps.SmoothOpen_Jeps ρ hρ.moll hε0 hf)
  have hmemJ : Work.Spaces.HkMem α k (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε0 hf hmk
  -- the `ℋᵏ`-bound for the mollifier, from the `E1` bound on `HkSq`
  have hsq := hC α hα k ε hε0 hε1 f hf hmk hmemJ
  have hnormJ : Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Jeps ρ ε f)
      ≤ Real.exp (C / 2) * Work.Spaces.HkNorm α k f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α k (Work.FTS.StrongEps.Jeps ρ ε f))
        ≤ Real.sqrt (Real.exp (C * ε) * Work.Spaces.HkSq α k f) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (C * ε)) * Real.sqrt (Work.Spaces.HkSq α k f) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ ≤ Real.exp (C / 2) * Real.sqrt (Work.Spaces.HkSq α k f) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          rw [← Real.exp_half (C * ε)]
          exact Real.exp_le_exp.mpr (by nlinarith [hε1, hCpos.le])
  calc Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ A₁ * Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Jeps ρ ε f) :=
        hA₁ α hα k hk4 hk6 _ hsmJ hmemJ
    _ ≤ A₁ * (Real.exp (C / 2) * Work.Spaces.HkNorm α k f) :=
        mul_le_mul_of_nonneg_left hnormJ hA₁pos.le
    _ = A₁ * Real.exp (C / 2) * Work.Spaces.HkNorm α k f := by ring

end Work.FTS.StrongEps.E5G
