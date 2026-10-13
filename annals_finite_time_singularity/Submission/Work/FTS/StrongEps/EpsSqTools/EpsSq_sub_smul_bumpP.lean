/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/EpsSq_sub_smul_bumpP.lean`

`EpsSq_sub_smul_bumpP`.  The profile `c · bump` may be subtracted from a *difference* `f - g` of
two profiles of the chapter's regularity class `SmoothOpen` (C^∞ on the open quadrant) without
leaving the space `X` of the `ε`-scheme, and its weighted `L²`-size grows at most quadratically in
the shift `c`:

  `EpsMem α (f - g - c·bump)`  and
  `EpsSq α (f - g - c·bump) ≤ 2 · EpsSq α (f - g) + B · c²`

with a constant `B` uniform in `α ∈ (0,1]`, in `f`, `g` and `c`.

This is the corrected form of the requested lemma `EpsSq_sub_smul_bump` (which is *false* for an
arbitrary profile `h`: `EpsMem α h` constrains only the weighted *square* `(h·epsW α)²`, so it says
nothing about the a.e. measurability of `h · epsW α`; see the module docstring of
`EpsSq_sub_smul_bump` and the formal refutation in `EpsSq_sub_smul_bump_refute`).  In the
regularity class `SmoothOpen` of the chapter the missing a.e. measurability is *automatic*: the
open quadrant carries the whole mass of the restricted product measure, and there both `h` and the
weight `epsW α` are continuous.  The sibling packaging of the same statement is
`EpsSq_sub_smul_bump_of_smoothOpen_pair` (in `EpsSq_sub_smul_bump_res`).

## The proof

Write `F = (h·epsW α)²`, `G = (bump·epsW α)²`, `D = ((h − c·bump)·epsW α)²`, all on `ℝ × ℝ`.

1. `(x − c y)² ≤ 2x² + 2c²y²` pointwise (`nlinarith` from `(x + c y)² ≥ 0`) gives `D ≤ 2F + 2c²G`
   everywhere; `EpsMem α h` and `EpsMem α bump` make the dominator `2F + 2c²G` integrable.
2. The a.e. strong measurability of the weighted profile `h · epsW α` (from `SmoothOpen h` and the
   continuity of `epsW α` on the open quadrant, via `Work.Spaces.aesm_of_continuousOn_Qd`) and of
   `bump · epsW α` turn `D` into an a.e. strongly measurable function, so `Integrable.mono'` gives
   `EpsMem α (h − c·bump)`.
3. `setIntegral_prod` identifies `EpsSq α k` with the integral of its integrand over the product
   `Iz ×ˢ Iθ` (`Iz = [0,∞)`, `Iθ = [0,π/2]`), so `integral_mono` and the linearity of the integral
   give `EpsSq α (h − c·bump) ≤ 2 EpsSq α h + 2c² EpsSq α bump`; the last term is bounded
   uniformly in `α ∈ (0,1]` by `BumpEpsSqBound` (`EpsSq α bump ≤ 1024`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.StrongEps.EpsSqTools.BumpEpsSqBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The weight `epsW` is continuous on the open quadrant -/

/-- `epsW α z θ = w z / sin(2θ)^{γ/2}` is continuous on the open quadrant, where `z ≠ 0` and
`sin(2θ) ≠ 0`. -/
theorem continuousOn_epsW_Q0P (α : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.epsW α q.1 q.2)
      Work.FTS.StrongEps.Quad := by
  have hsinpos : ∀ p ∈ Work.FTS.StrongEps.Quad, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.StrongEps.Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.gam α / 2))
      Work.FTS.StrongEps.Quad :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  change ContinuousOn
    (fun q : ℝ × ℝ => Work.Spaces.w q.1 / Real.sin (2 * q.2) ^ (Work.Spaces.gam α / 2))
    Work.FTS.StrongEps.Quad
  exact hw.div hsinpow (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))

/-! ## The a.e. strong measurability of the weighted profiles -/

/-- The weighted bump `bump · epsW α` is a.e. strongly measurable for the measure of `EpsMem`
(`bump` is smooth on all of `ℝ²`, `epsW α` is continuous on the open quadrant, and the quadrant
carries the whole mass of `volume ∣ Iz ×ˢ Iθ`). -/
theorem aesm_bump_mul_epsW_P (α : ℝ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      Work.FTS.StrongEps.Quad :=
    (Work.FTS.StrongEps.contDiff_bump 0).continuous.continuousOn.mul (continuousOn_epsW_Q0P α)
  have h1 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  rwa [Measure.prod_restrict] at h1

/-- The a.e. strong measurability of the weighted profile `h · epsW α` for a profile `h` of the
chapter's regularity class `SmoothOpen` — this is exactly the hypothesis that `EpsMem α h` alone
does *not* provide. -/
theorem aesm_mul_epsW_of_smoothOpenP {α : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) Work.FTS.StrongEps.Quad :=
    ((hh.forall 0).continuousOn).mul (continuousOn_epsW_Q0P α)
  have h1 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  rwa [Measure.prod_restrict] at h1

/-- `SmoothOpen` is closed under differences. -/
theorem smoothOpen_subP {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => (hf.forall n).sub (hg.forall n))

/-! ## The target -/

theorem EpsSq_sub_smul_bumpP : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ c : ℝ,
      Work.FTS.StrongEps.EpsMem α (fun z θ => f z θ - g z θ) →
      Work.FTS.StrongEps.EpsMem α
          (fun z θ => f z θ - g z θ - c * Work.FTS.StrongEps.bump z θ) ∧
      Work.FTS.StrongEps.EpsSq α
          (fun z θ => f z θ - g z θ - c * Work.FTS.StrongEps.bump z θ)
        ≤ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) + B * c ^ 2 := by
  -- the uniform bound `EpsSq α bump ≤ K` for `α ∈ (0,1]`
  obtain ⟨K, hKpos, hB⟩ := BumpEpsSqBound
  refine ⟨2 * K, by linarith, ?_⟩
  intro α hα f g hf hg c hmem
  -- the general step, for an arbitrary `SmoothOpen` profile `h` and shift `c`
  have key : ∀ (h : Work.FTS.Galerkin.Fn) (c : ℝ),
      Work.FTS.EllipticEst.SmoothOpen h → Work.FTS.StrongEps.EpsMem α h →
      Work.FTS.StrongEps.EpsMem α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
        ≤ 2 * Work.FTS.StrongEps.EpsSq α h + (2 * K) * c ^ 2 := by
    intro h c hsm hh
    obtain ⟨hbumpmem, hbumpSq⟩ := hB α hα
    -- (1) the pointwise domination `D ≤ 2F + 2c²G`
    have hDle : ∀ p : ℝ × ℝ,
        ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
              * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
          ≤ 2 * (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
            + 2 * c ^ 2 * (Work.FTS.StrongEps.bump p.1 p.2
                * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
      intro p
      nlinarith [sq_nonneg ((h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        + c * (Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2))]
    -- (2) integrability of the dominator and a.e. strong measurability of `D`
    have hFint : Integrable
        (fun p : ℝ × ℝ => (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hh
    have hGint : Integrable
        (fun p : ℝ × ℝ => (Work.FTS.StrongEps.bump p.1 p.2
            * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hbumpmem
    have hBigint : Integrable (fun p : ℝ × ℝ =>
        2 * (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
          + 2 * c ^ 2 * (Work.FTS.StrongEps.bump p.1 p.2
              * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      (hFint.const_mul 2).add (hGint.const_mul (2 * c ^ 2))
    have hGE : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      aesm_bump_mul_epsW_P α
    have hDaesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
            * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
      have h1 : (fun p : ℝ × ℝ =>
            ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
              * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
          = fun p : ℝ × ℝ => (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2
              - c * (Work.FTS.StrongEps.bump p.1 p.2
                  * Work.FTS.StrongEps.epsW α p.1 p.2)) ^ 2 := by
        funext p; ring
      rw [h1]
      exact (aesm_mul_epsW_of_smoothOpenP hsm).sub (hGE.const_mul c) |>.pow 2
    have hDint : Integrable (fun p : ℝ × ℝ =>
        ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
            * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      Integrable.mono' hBigint hDaesm (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hDle p))
    -- (3) `EpsSq` as the integral of the integrand over the product `Iz ×ˢ Iθ`
    have hEsq : ∀ {k : ℝ → ℝ → ℝ}, Work.FTS.StrongEps.EpsMem α k →
        Work.FTS.StrongEps.EpsSq α k
          = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
              (k p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
      intro k hk
      rw [Work.FTS.StrongEps.EpsSq]
      exact (MeasureTheory.setIntegral_prod _ hk).symm
    refine ⟨hDint, ?_⟩
    have hmono := MeasureTheory.integral_mono hDint hBigint hDle
    have h2 : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          2 * (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
            + 2 * c ^ 2 * (Work.FTS.StrongEps.bump p.1 p.2
                * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        = 2 * Work.FTS.StrongEps.EpsSq α h
          + 2 * c ^ 2 * Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump := by
      rw [MeasureTheory.integral_add (hFint.const_mul 2) (hGint.const_mul (2 * c ^ 2)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        ← hEsq hh, ← hEsq hbumpmem]
    calc Work.FTS.StrongEps.EpsSq α
          (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
        = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
              * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := hEsq hDint
      _ ≤ _ := hmono
      _ = 2 * Work.FTS.StrongEps.EpsSq α h
          + 2 * c ^ 2 * Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump := h2
      _ ≤ 2 * Work.FTS.StrongEps.EpsSq α h + (2 * K) * c ^ 2 := by
          have h3 := mul_le_mul_of_nonneg_left hbumpSq (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)
          linarith
  exact key (fun z θ => f z θ - g z θ) c (smoothOpen_subP hf hg) hmem

end Work.FTS.StrongEps.EpsSqTools
