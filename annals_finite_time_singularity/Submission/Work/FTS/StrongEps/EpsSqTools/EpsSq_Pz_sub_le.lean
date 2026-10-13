/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/EpsSq_Pz_sub_le.lean`

**The projection `P₀` is bounded on the weighted space `X` of the `ε`-scheme, in difference form:**

  `EpsSq α (Pz f - Pz g) ≤ C · EpsSq α (f - g)`,

with a constant `C` that is *universal* (independent of `α ∈ (0,1]`, of `f`, `g`), together with the
membership `EpsMem α (Pz f - Pz g)`; the hypotheses are the two class requirements of the elliptic
layer (`SmoothOpen`, `HkMem α 4`) and the honest level-`0` integrability of the difference.

## Route

`Pz f = f - (L₁₂ f 0 / pzNorm) • bump` (`StrongEps.PZero`), so with `c := (L₁₂ f 0 - L₁₂ g 0)/pzNorm`
one has `Pz f - Pz g = (f - g) - c·bump` pointwise (`Pz_sub_apply`), and `L₁₂_sub_HkMem`
(`StrongEps.EComparison`) at `z = 0 ∈ Iz = Ici 0` turns the coefficient into
`c = L₁₂ (f - g) 0 / pzNorm`.  The two ingredients are

* `EpsSqTools.L12_zero_le_EpsSq` — the Cauchy–Schwarz bound
  `|L₁₂ h 0| ≤ C₁ √(EpsSq α h)`, which uses only `EpsMem α h` (the level-`0` weight `w` is exactly
  the Hardy weight of `L₁₂(·)(0)`);
* `EpsSqTools.EpsSq_sub_smul_bumpP` — `EpsMem α ((f - g) - c·bump)` and
  `EpsSq α ((f - g) - c·bump) ≤ 2 EpsSq α (f - g) + B c²`, from `bump` being smooth and compactly
  supported inside the open quadrant (`StrongEps.BumpDefs`); the `SmoothOpen` hypotheses are used
  here, and are genuinely needed — without them the statement fails for a non-measurable `±bump`
  datum (see `EpsSqTools.NOTES_EpsSq_Pz_sub_le.md`),

and then `c² ≤ C₁² EpsSq α (f - g) / pzNorm²`, so that

  `EpsSq α (Pz f - Pz g) ≤ (2 + B C₁²/pzNorm²) · EpsSq α (f - g)`.

This module is complete (no unfinished proofs).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSq_Jeps_le
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos
import Submission.Work.FTS.StrongEps.EpsSqTools.L12_zero_le_EpsSq
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_smul_bumpP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Two transport lemmas for the `X`-structure -/

/-- **The membership `EpsMem` only depends on the pointwise values.**  `EpsMem α f` is the
integrability of `(f · epsW α)²` on `Iz ×ˢ Iθ`, so it transfers along a pointwise equality. -/
theorem EpsMem_congr {α : ℝ} {f g : Work.FTS.Galerkin.Fn} (h : ∀ z θ, f z θ = g z θ) :
    Work.FTS.StrongEps.EpsMem α f → Work.FTS.StrongEps.EpsMem α g := by
  intro hf
  have heq : (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      = fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 := by
    funext p
    rw [h p.1 p.2]
  rw [Work.FTS.StrongEps.EpsMem] at hf ⊢
  rwa [heq] at hf

/-- **The pointwise form of the projected difference.**  `Pz f - Pz g = (f - g) - c · bump` with
`c = (L₁₂ f 0 - L₁₂ g 0)/pzNorm` (the projection is affine with linear part the identity). -/
theorem Pz_sub_apply (f g : Work.FTS.Galerkin.Fn) (z θ : ℝ) :
    (Work.FTS.StrongEps.Pz f - Work.FTS.StrongEps.Pz g) z θ
      = (f z θ - g z θ)
        - ((Work.Construction.L12 f 0 - Work.Construction.L12 g 0) / Work.FTS.StrongEps.pzNorm)
            * Work.FTS.StrongEps.bump z θ := by
  simp only [Pi.sub_apply, Work.FTS.StrongEps.Pz_apply]
  ring

/-! ## The target -/

/-- **`P₀` is bounded on the weighted space `X`** (difference form), with a constant independent of
`α ∈ (0,1]`: for `f`, `g` in the open-quadrant class with honest `ℋ⁴`-size and with the difference
in `X`, the projected difference is in `X` and

  `EpsSq α (Pz f - Pz g) ≤ C · EpsSq α (f - g)`.

See the module docstring for the route; the two inputs are
`EpsSqTools.L12_zero_le_EpsSq` (`|L₁₂ h 0| ≤ C₁ √(EpsSq α h)`) and
`EpsSqTools.EpsSq_sub_smul_bumpP` (`EpsSq α ((f - g) - c • bump) ≤ 2 EpsSq α (f - g) + B c²`). -/
theorem EpsSq_Pz_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g →
      Work.FTS.StrongEps.EpsMem α (fun z θ => f z θ - g z θ) →
        Work.FTS.StrongEps.EpsMem α
            (fun z θ => Work.FTS.StrongEps.Pz f z θ - Work.FTS.StrongEps.Pz g z θ) ∧
        Work.FTS.StrongEps.EpsSq α
            (fun z θ => Work.FTS.StrongEps.Pz f z θ - Work.FTS.StrongEps.Pz g z θ)
          ≤ C * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := L12_zero_le_EpsSq
  obtain ⟨B, hBpos, hB⟩ := EpsSq_sub_smul_bumpP
  refine ⟨2 + B * C₁ ^ 2 / pzNorm ^ 2, ?_, ?_⟩
  · have h1 : 0 ≤ B * C₁ ^ 2 / pzNorm ^ 2 :=
      div_nonneg (mul_nonneg hBpos.le (sq_nonneg _)) (sq_nonneg _)
    linarith
  intro α hα f g hf hg hmf hmg hmem
  -- `L₁₂` is additive on the honest `ℋ⁴`-class at `z = 0 ∈ Iz = Ici 0`
  have hL12 : Work.Construction.L12 (fun z θ => f z θ - g z θ) 0
      = Work.Construction.L12 f 0 - Work.Construction.L12 g 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hf hg hmf hmg 0 (Set.mem_Ici.mpr le_rfl)
  set c : ℝ := (Work.Construction.L12 f 0 - Work.Construction.L12 g 0) / pzNorm with hcdef
  have hpt : ∀ z θ : ℝ, (Work.FTS.StrongEps.Pz f - Work.FTS.StrongEps.Pz g) z θ
      = (f z θ - g z θ) - c * Work.FTS.StrongEps.bump z θ := by
    intro z θ
    rw [Pz_sub_apply f g z θ, hcdef]
  obtain ⟨hmem', hbd⟩ := hB α hα f g hf hg c hmem
  have hc : c = Work.Construction.L12 (fun z θ => f z θ - g z θ) 0 / pzNorm := by
    rw [hcdef, ← hL12]
  have hcsq : c ^ 2 ≤ C₁ ^ 2 / pzNorm ^ 2
      * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by
    have hL := hC₁ α hα (fun z θ => f z θ - g z θ) hmem
    have hS : 0 ≤ Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) :=
      Work.FTS.StrongEps.EpsSq_nonneg α _
    have hsq : (Work.Construction.L12 (fun z θ => f z θ - g z θ) 0) ^ 2
        ≤ (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ))) ^ 2 := by
      rcases abs_le.mp hL with ⟨hlo, hhi⟩
      exact sq_le_sq' hlo hhi
    have hrhs : (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ))) ^ 2
        = C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by
      rw [mul_pow, Real.sq_sqrt hS]
    rw [hc, div_pow]
    calc (Work.Construction.L12 (fun z θ => f z θ - g z θ) 0) ^ 2 / pzNorm ^ 2
        ≤ (C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ)) / pzNorm ^ 2 :=
          div_le_div_of_nonneg_right (by rw [← hrhs]; exact hsq) (sq_nonneg pzNorm)
      _ = C₁ ^ 2 / pzNorm ^ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by
          ring
  constructor
  · exact EpsMem_congr (fun z θ => (hpt z θ).symm) hmem'
  · calc Work.FTS.StrongEps.EpsSq α
          (fun z θ => Work.FTS.StrongEps.Pz f z θ - Work.FTS.StrongEps.Pz g z θ)
        = Work.FTS.StrongEps.EpsSq α
            (fun z θ => (f z θ - g z θ) - c * Work.FTS.StrongEps.bump z θ) :=
          Work.FTS.StrongEps.EpsSq_congr (fun z θ => hpt z θ)
      _ ≤ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) + B * c ^ 2 := hbd
      _ ≤ 2 * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ)
            + B * (C₁ ^ 2 / pzNorm ^ 2
                * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ)) :=
          (by linarith [mul_le_mul_of_nonneg_left hcsq hBpos.le])
      _ = (2 + B * C₁ ^ 2 / pzNorm ^ 2)
            * Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - g z θ) := by ring

end Work.FTS.StrongEps.EpsSqTools
