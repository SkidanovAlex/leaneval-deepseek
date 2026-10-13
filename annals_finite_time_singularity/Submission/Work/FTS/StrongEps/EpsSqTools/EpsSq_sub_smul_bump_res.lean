/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/EpsSq_sub_smul_bump_res.lean`

## The requested lemma `EpsSq_sub_smul_bump` is **FALSE as stated**

The requested statement

```
theorem EpsSq_sub_smul_bump : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ (h : Fn) (c : ℝ), EpsMem α h →
      EpsMem α (fun z θ => h z θ - c · bump z θ) ∧
      EpsSq α (fun z θ => h z θ - c · bump z θ) ≤ 2 · EpsSq α h + B · c ^ 2
```

is missing a *measurability* hypothesis on `h`.  Indeed
`EpsMem α h` is `IntegrableOn (fun p => (h p.1 p.2 · epsW α p.1 p.2)²) (Iz ×ˢ Iθ)` and
`Integrable` is `AEStronglyMeasurable ∧ HasFiniteIntegral`; the hypothesis therefore controls only
the **square** of the weighted profile, and a.e. strong measurability of a square does not imply
a.e. strong measurability of the function itself.  Concretely: for `E ⊆ (5/8,7/8) × (π/4,3π/8)`
not Lebesgue measurable, the datum `h = ±bump` (sign `+1` on `E`, `−1` off `E`) satisfies
`EpsMem 1 h`, because its weighted square is the *measurable* `(bump · epsW 1)²`; but for `c ≠ 0`
the profile `h − c·bump` has weighted square `(bump · epsW 1)² · (9 − 8·1_E)` on that box, which
is not a.e. strongly measurable, so `¬ EpsMem 1 (h − c·bump)`.  The formal refutation is
`EpsSq_sub_smul_bump_is_false` below (via `EpsSq_sub_smul_bump_refute`; as usual in this project
the existence of the non-measurable set is the classical Vitali construction, not yet available in
Mathlib, so it is carried as an explicit hypothesis).

## What is proved here instead

* `continuousOn_epsW_quad` — `epsW α` is continuous on the open quadrant `Q0`;
* `aesm_mul_epsW` — the a.e. strong measurability of `p ↦ h p.1 p.2 · epsW α p.1 p.2` follows
  from `SmoothOpen h` (the regularity class of the chapter), so the corrected statements below are
  usable in exactly the applications that motivated the request (`h = f − g` with `f`, `g`
  `SmoothOpen` is `SmoothOpen` too);
* **`EpsSq_sub_smul_bump_of_aesm`** — the requested statement with the honest extra hypothesis
  `AEStronglyMeasurable (fun p => h p.1 p.2 · epsW α p.1 p.2) (volume ∣ Iz ×ˢ Iθ)`;
* **`EpsSq_sub_smul_bump_of_smoothOpen`** — the same with `SmoothOpen h` instead of the raw a.e.
  measurability.

Both have the same conclusion as the requested lemma, and the same constant shape.

## The mathematics of the corrected statement

`bump` is smooth on `ℝ²`, supported in the compact box `[1/2,1] × [π/4,3π/8] ⊂ Q0`, and bounded
by `1`; on that box `w z ≤ 9` and `sin(2θ) ∈ [√2/2, 1]`, so `epsW α` is uniformly bounded there
for `α ∈ (0,1]` (`γ = 1 + α/10 ≤ 1.1`).  Hence `EpsMem α bump` and `EpsSq α bump ≤ K` uniformly
in `α ∈ (0,1]` (`BumpEpsSqBound`).  Writing
`F = (h · epsW α)²`, `G = (bump · epsW α)²`, `D = ((h − c·bump) · epsW α)²`, the pointwise bound
`(x − c y)² ≤ 2x² + 2c²y²` gives `D ≤ 2F + 2c²G`, and with the a.e. measurability of the weighted
profile `h · epsW α` this shows `Integrable D = EpsMem α (h − c·bump)` (via `Integrable.mono'`)
and, after rewriting `EpsSq` as the integral over `Iz ×ˢ Iθ` (`setIntegral_prod`), the integral
comparison `∫ D ≤ ∫ (2F + 2c²G) = 2 EpsSq α h + 2c² EpsSq α bump ≤ 2 EpsSq α h + B c²`
with `B = 2K`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic
import Submission.Work.FTS.StrongEps.EpsSqTools.BumpEpsSqBound
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_smul_bump_refute
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

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

/-! ## The weight `epsW` on the open quadrant -/

/-- `epsW α z θ = w z / sin(2θ)^{γ/2}` is continuous on the open quadrant (where `z ≠ 0` and
`sin(2θ) ≠ 0`). -/
theorem continuousOn_epsW_quad (α : ℝ) :
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

/-- The weighted profile `bump · epsW α` is a.e. strongly measurable for the measure of
`EpsMem`. -/
theorem aesm_bump_mul_epsW (α : ℝ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      Work.FTS.StrongEps.Quad :=
    (Work.FTS.StrongEps.contDiff_bump 0).continuous.continuousOn.mul (continuousOn_epsW_quad α)
  have h1 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  rwa [Measure.prod_restrict] at h1

/-- The a.e. strong measurability of the weighted profile `h · epsW α` follows from the
`C^∞`-on-the-open-quadrant regularity class `SmoothOpen h` of the chapter. -/
theorem aesm_mul_epsW_of_smoothOpen {α : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) Work.FTS.StrongEps.Quad :=
    ((hh.forall 0).continuousOn).mul (continuousOn_epsW_quad α)
  have h1 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  rwa [Measure.prod_restrict] at h1

/-! ## The corrected statement -/

/-- **The corrected `EpsSq_sub_smul_bump`** (the requested statement is false: see the module
docstring).  The extra hypothesis is exactly the a.e. strong measurability of the weighted profile
`h · epsW α`, which `EpsMem α h` does *not* imply (it controls only its square). -/
theorem EpsSq_sub_smul_bump_of_aesm : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ (h : Work.FTS.Galerkin.Fn) (c : ℝ), Work.FTS.StrongEps.EpsMem α h →
      AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) →
      Work.FTS.StrongEps.EpsMem α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
        ≤ 2 * Work.FTS.StrongEps.EpsSq α h + B * c ^ 2 := by
  obtain ⟨K, hKpos, hB⟩ := BumpEpsSqBound
  refine ⟨2 * K, by linarith, ?_⟩
  intro α hα h c hh hAESM
  obtain ⟨hbumpmem, hbumpSq⟩ := hB α hα
  have hFint : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hh
  have hGint : Integrable (fun p : ℝ × ℝ =>
      (Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hbumpmem
  have hDle : ∀ p : ℝ × ℝ,
      ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
        ≤ 2 * (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
          + 2 * c ^ 2 * (Work.FTS.StrongEps.bump p.1 p.2
              * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
    intro p
    nlinarith [sq_nonneg ((h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
        + c * (Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2))]
  have hBigint : Integrable (fun p : ℝ × ℝ =>
      2 * (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
        + 2 * c ^ 2 * (Work.FTS.StrongEps.bump p.1 p.2
            * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    (hFint.const_mul 2).add (hGint.const_mul (2 * c ^ 2))
  have hGE : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    aesm_bump_mul_epsW α
  have hDaesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    have h1 : (fun p : ℝ × ℝ => ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        = fun p : ℝ × ℝ => (h p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2
            - c * (Work.FTS.StrongEps.bump p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2)) ^ 2 := by
      funext p; ring
    rw [h1]
    exact (hAESM.sub (hGE.const_mul c)).pow 2
  have hDint : Integrable (fun p : ℝ × ℝ =>
      ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2) * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    Integrable.mono' hBigint hDaesm (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hDle p))
  have hEsq : ∀ {f : ℝ → ℝ → ℝ}, Work.FTS.StrongEps.EpsMem α f →
      Work.FTS.StrongEps.EpsSq α f
        = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
    intro f hf
    rw [Work.FTS.StrongEps.EpsSq]
    exact (MeasureTheory.setIntegral_prod _ hf).symm
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
  calc Work.FTS.StrongEps.EpsSq α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          ((h p.1 p.2 - c * Work.FTS.StrongEps.bump p.1 p.2)
            * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := hEsq hDint
    _ ≤ _ := hmono
    _ = 2 * Work.FTS.StrongEps.EpsSq α h
        + 2 * c ^ 2 * Work.FTS.StrongEps.EpsSq α Work.FTS.StrongEps.bump := h2
    _ ≤ 2 * Work.FTS.StrongEps.EpsSq α h + (2 * K) * c ^ 2 := by
        have h3 := mul_le_mul_of_nonneg_left hbumpSq (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)
        linarith

/-- **The corrected `EpsSq_sub_smul_bump`, in the regularity class of the chapter**: for
`SmoothOpen h` (which is the case in every intended application, e.g. `h = f - g` with `f`, `g`
`SmoothOpen`) the a.e. measurability hypothesis is automatic. -/
theorem EpsSq_sub_smul_bump_of_smoothOpen : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ (h : Work.FTS.Galerkin.Fn) (c : ℝ), Work.FTS.EllipticEst.SmoothOpen h →
      Work.FTS.StrongEps.EpsMem α h →
      Work.FTS.StrongEps.EpsMem α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
        ≤ 2 * Work.FTS.StrongEps.EpsSq α h + B * c ^ 2 := by
  obtain ⟨B, hBpos, hB⟩ := EpsSq_sub_smul_bump_of_aesm
  exact ⟨B, hBpos, fun α hα h c hsm hmem =>
    hB α hα h c hmem (aesm_mul_epsW_of_smoothOpen hsm)⟩

/-- `SmoothOpen` is closed under differences. -/
theorem SmoothOpen_sub {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => (hf.forall n).sub (hg.forall n))

/-- **The corrected `EpsSq_sub_smul_bump` in the exact shape needed by `EpsSq_Pz_sub_le`**: the
difference of two `SmoothOpen` profiles is `SmoothOpen`, so the extra measurability hypothesis of
`EpsSq_sub_smul_bump_of_aesm` is discharged by the standing hypotheses there. -/
theorem EpsSq_sub_smul_bump_of_smoothOpen_pair : ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ c : ℝ,
      Work.FTS.StrongEps.EpsMem α (fun z θ => f z θ - g z θ) →
      Work.FTS.StrongEps.EpsMem α
          (fun z θ => f z θ - g z θ - c * Work.FTS.StrongEps.bump z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ - c * Work.FTS.StrongEps.bump z θ)
        ≤ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) + B * c ^ 2 := by
  obtain ⟨B, hBpos, hB⟩ := EpsSq_sub_smul_bump_of_smoothOpen
  exact ⟨B, hBpos, fun α hα f g hf hg c hmem =>
    hB α hα (fun z θ => f z θ - g z θ) c (SmoothOpen_sub hf hg) hmem⟩

/-! ## The formal refutation of the requested statement -/

/-- **The requested statement is false.**  Any non-Lebesgue-measurable `E` inside the bump's
positive box provides a counterexample: the `±bump` datum `h` built from `E` satisfies
`EpsMem 1 h`, but `h - c·bump` (`c ≠ 0`) does not, so the `EpsMem` conjunct of
`EpsSq_sub_smul_bump` fails for `α = 1 ∈ Set.Ioc 0 1`. -/
theorem EpsSq_sub_smul_bump_is_false
    (hE : ∃ E : Set (ℝ × ℝ),
      E ⊆ Set.Ioo (5 / 8) (7 / 8) ×ˢ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) ∧
        ¬ MeasureTheory.NullMeasurableSet E MeasureTheory.volume) :
    ¬ (∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
        ∀ (h : Work.FTS.Galerkin.Fn) (c : ℝ), Work.FTS.StrongEps.EpsMem α h →
          Work.FTS.StrongEps.EpsMem α
              (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ) ∧
          Work.FTS.StrongEps.EpsSq α (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ)
            ≤ 2 * Work.FTS.StrongEps.EpsSq α h + B * c ^ 2) := by
  obtain ⟨E, hEsub, hE'⟩ := hE
  obtain ⟨K, hKpos, hB⟩ := BumpEpsSqBound
  intro hlemma
  obtain ⟨B₀, hB₀pos, hstep⟩ := hlemma
  obtain ⟨h, c, hc, hmem, hnotmem⟩ :=
    EpsSq_sub_smul_bump_refute (hB 1 ⟨by norm_num, le_refl 1⟩).1 hEsub hE'
  exact hnotmem (hstep 1 ⟨by norm_num, le_refl 1⟩ h c hmem).1

end Work.FTS.StrongEps.EpsSqTools
