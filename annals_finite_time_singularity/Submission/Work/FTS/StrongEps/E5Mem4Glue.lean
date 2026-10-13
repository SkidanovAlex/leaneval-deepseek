/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Mem4Glue.lean` — the per-`z` bound of the projected family

`EpsLimMem4` (`EpsE5Facts.lean`, proved) turns the extraction data of the `ε`-sequence into the
honest `ℋ⁴`-membership `HkMem α 4 (slice g τ)` of the **limit**, but it consumes the *per-`z`*
bound

  `∀ z ∈ Iz, ∃ Bz, ∀ n, ∫_θ HkIntegrand α 4 (G n) z θ ≤ Bz`

of the approximating sequence.  That bound is **not** implied by a uniform `ℋ⁶`-bound plus
pointwise convergence (Fatou gives it only a.e. in `z`; the sharp counterexample is recorded in
`NOTES_session9.md` §3.2), so it has to be produced for the family the E5 route actually uses.

This module produces it for the **projected** family `Pn n := slice (JfamP ρ (ε n) (G n)) τ`,
which is the family on which `E5_mem4_JfamP`/`E5_bd4_JfamP` run.  The two inputs are

* `classC_mixed_sup_le_four` — a *global* pointwise bound on the mixed slots of order `≤ 4` of a
  class-`C` profile, priced by its `ℋ⁶`-norm.  This is what makes the θ-integral of the
  `ℋ⁴`-integrand finite **uniformly in `n`** (the price is uniform, the weights are θ-integrable);
  the lemma `E5Aux.HkIntegrand_four_perz_le` packages that bound;
* `HkNorm_JfamP_le` — the `ℋ⁶`-size of the projected slice, bounded by `A ·` the `ℋ⁶`-size of the
  plain slice.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5Aux.HkIntegrand_four_perz_le
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.ConvLocUnifH6_JfamP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-`z` bound of the `ℋ⁴`-integrand of the projected family.**  For the sequence
`ε n ∈ (0,1]`, the families `G n`, a fixed fake time `τ` and datum

* the smoothness of the plain slices (`hsm`, all orders on the open quadrant),
* their honest `ℋ⁶`-membership (`hmem6`) and the uniform bound `Xn6 ≤ B` (`hb6`, `0 ≤ B`),
* the class-`C` clause of the *projected* slices (`hC`, an interface conjunct),

there is at every `z ∈ Iz` a bound of the per-`z` θ-integral of `HkIntegrand α 4` of the projected
slice, **uniform in `n`** — exactly the `hz` input of `EpsLimMem4`/`E5_mem4_JfamP`. -/
theorem hz_of_classC_JfamP {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {G : ℕ → Fam} {ε : ℕ → ℝ} {τ : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hB : 0 ≤ B) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (slice (G n) τ)) Quad)
    (hmem6 : ∀ n : ℕ, Work.Spaces.HkMem α 6 (slice (G n) τ))
    (hb6 : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α (slice (G n) τ) ≤ B)
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε n) (G n)) τ)) :
    ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (slice (JfamP ρ (ε n) (G n)) τ) z θ) ≤ Bz := by
  obtain ⟨A, hA0, hA⟩ := HkNorm_JfamP_le (ρ := ρ) hρ
  obtain ⟨C, hC0, hCb⟩ := E5Aux.HkIntegrand_four_perz_le
  have hAB : 0 ≤ A * B := mul_nonneg hA0 hB
  refine fun z hz => ⟨C * (1 + (Work.Spaces.w z) ^ 2) * (1 + A * B) ^ 2, fun n => ?_⟩
  have hXn : Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) τ) ≤ A * B :=
    le_trans (hA hα (hε n) (hsm n) (hmem6 n)).2
      (mul_le_mul_of_nonneg_left (hb6 n) hA0)
  have h1 := hCb α hα (hC n) z hz
  have h2 : (1 + Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) τ)) ^ 2
      ≤ (1 + A * B) ^ 2 :=
    pow_le_pow_left₀ (by
        simpa using add_nonneg zero_le_one
          (Work.Spaces.HkNorm_nonneg α 6 (slice (JfamP ρ (ε n) (G n)) τ))) (by linarith) 2
  have h3 : 0 ≤ C * (1 + (Work.Spaces.w z) ^ 2) := by positivity
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (slice (JfamP ρ (ε n) (G n)) τ) z θ)
      ≤ C * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ (ε n) (G n)) τ)) ^ 2 := h1
    _ ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + A * B) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 h3

end Work.FTS.StrongEps
