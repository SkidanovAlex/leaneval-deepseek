import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.fstarDzUniform
import Submission.Work.FTS.RegPkgGal.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.Regularity.dzProfFullUniform` — the uniform `z`-derivative of the full profile

For a regularity package `h : RegPkg' α S A B g` and a radius `R ≥ 0`, the `z`-derivative of the
full self-similar profile `F = F_* + g` (`profFull α g`) enjoys, uniformly on `z ∈ [0,R]`,
`θ ∈ Iθ`, `τ ∈ [0,S]`:

1. the **splitting** `∂_z F = ∂_z F_* + ∂_z g` (plain additivity of `deriv`, available because
   `RegPkg'.hcont` makes `(z,τ) ↦ g z θ τ` jointly `C¹` at each fixed `θ` while `F_*` is smooth);
2. a **uniform bound** `|∂_z F| ≤ M`;
3. a **joint `α`-Hölder estimate in `(z,τ)`**:
   `|∂_zF(z,θ,τ) - ∂_zF(z',θ,τ')| ≤ N * (|z-z'| + |τ-τ'|)^α`.

The sum is estimated on its two parts:

* the **static part** `∂_z F_*` is bounded and `α`-Hölder on `[0,R]`; this is the content of the
  sibling module `Submission.Work.FTS.Regularity.fstarDzUniform`
  (`Work.FTS.Regularity.fstarDzUniform`);
* the **perturbation part** `∂_z g` is bounded and jointly `α`-Hölder in `(z,θ,τ)` by the jet
  field `RegPkg'.hpz` (restricted to `θ = θ'`).
-/

noncomputable section

open FiniteTimeSingularity Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-- **The `z`-slices of the perturbation are differentiable.**  `RegPkg'.hcont` states that
`(z,τ) ↦ g z θ τ` is `C¹` on `Ioi (-1) ×ˢ Ioo (-1) (S+1)` at each fixed `θ ∈ Iθ`; since
`z ≥ 0 > -1` and `τ ∈ [0,S] ⊂ (-1, S+1)`, composing with `z' ↦ (z',τ)` gives differentiability of
the `z`-slice `z' ↦ g z' θ τ` at `z`. -/
theorem gSlice_differentiableAt {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∀ θ ∈ Work.Spaces.Iθ, ∀ z τ : ℝ, 0 ≤ z → τ ∈ Set.Icc 0 S →
      DifferentiableAt ℝ (fun z' => g z' θ τ) z := by
  intro θ hθ z τ hz hτ
  have hz1 : -1 < z := by linarith
  have hτ1 : -1 < τ := by linarith [hτ.1]
  have hτ2 : τ < S + 1 := by linarith [hτ.2, h.hS]
  have hmem : (z, τ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) : Set (ℝ × ℝ)) :=
    ⟨hz1, hτ1, hτ2⟩
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hcd : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2) (z, τ) :=
    (h.hcont θ hθ).contDiffAt (hopen.mem_nhds hmem)
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (z, τ) :=
    hcd.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun z' : ℝ => (z', τ)) z := by fun_prop
  exact hdiff.comp z hg

/-- **The `z`-slices of the fundamental profile are differentiable** on `z > -1`: `F_*` is a
constant (in `z`; the `θ`-dependence enters only through the factor `Γ(θ)/c`) multiple of
`Work.FM.Fstar z = 2z/(1+z)²`, whose derivative is explicit
(`Work.FM.hasDerivAt_Fstar`). -/
theorem fstarSlice_differentiableAt {α : ℝ} (z θ : ℝ) (hz : -1 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (pExp α) z' θ) z := by
  have hfun : (fun z' => Work.Construction.Fstar (pExp α) z' θ)
      = fun z' => (pExp α * (Work.Spaces.Gam (pExp α) θ / Work.Spaces.c (pExp α)))
          * Work.FM.Fstar z' := by
    funext z'
    rw [Work.Construction.Fstar]
  rw [hfun]
  exact (Work.FM.hasDerivAt_Fstar z hz).const_mul _ |>.differentiableAt

theorem dzProfFullUniform {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) (R : ℝ) (hR : 0 ≤ R) :
    (∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        deriv (fun z' => profFull α g z' θ τ) z
          = deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ z θ τ : ℝ, 0 ≤ z → z ≤ R → θ ∈ Work.Spaces.Iθ →
        τ ∈ Set.Icc 0 S → |deriv (fun z' => profFull α g z' θ τ) z| ≤ M) ∧
      (∃ N : ℝ, 0 ≤ N ∧ ∀ z z' θ τ τ' : ℝ, 0 ≤ z → z ≤ R → 0 ≤ z' → z' ≤ R →
        θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → τ' ∈ Set.Icc 0 S →
        |deriv (fun z'' => profFull α g z'' θ τ) z
          - deriv (fun z'' => profFull α g z'' θ τ') z'| ≤ N * (|z - z'| + |τ - τ'|) ^ α) := by
  -- the static part: bounds for `∂_z F_*` on `[0,R]`
  obtain ⟨M0, N0, hM0, hN0, hM0b, hN0b⟩ := fstarDzUniform h.hα h.hα13 hR
  -- the perturbation part: the jet of `∂_z g`
  obtain ⟨Npz, hNpz⟩ := h.hpz
  have hNpz0 : 0 ≤ Npz := hNpz.1
  -- conjunct 1: `deriv` is additive on the sum `F_* + g`
  have hpart1 : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun z' => profFull α g z' θ τ) z
        = deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
          + Work.Spaces.pz (gSlice g τ) z θ := by
    intro z θ τ hz hθ hτ
    have hFd : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (pExp α) z' θ) z :=
      fstarSlice_differentiableAt z θ (by linarith)
    have hGd : DifferentiableAt ℝ (fun z' => g z' θ τ) z :=
      gSlice_differentiableAt h θ hθ z τ hz hτ
    exact deriv_add hFd hGd
  refine ⟨hpart1, ?_, ?_⟩
  · -- conjunct 2: triangle inequality, `M = M0 + Npz`
    refine ⟨M0 + Npz, by linarith, ?_⟩
    intro z θ τ hz hzR hθ hτ
    rw [hpart1 z θ τ hz hθ hτ]
    have h1 := hM0b z θ hz hzR hθ
    have h2 := hNpz.abs_le hz hθ hτ
    calc |deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ|
        ≤ |deriv (fun z' => Work.Construction.Fstar (pExp α) z' θ) z|
          + |Work.Spaces.pz (gSlice g τ) z θ| := abs_add_le _ _
      _ ≤ M0 + Npz := add_le_add h1 h2
  · -- conjunct 3: triangle inequality; the static part is `α`-Hölder, the perturbation part is
    -- jointly `α`-Hölder by its jet (at `θ = θ'`), then `|z-z'|^α ≤ (|z-z'|+|τ-τ'|)^α`
    refine ⟨N0 + Npz, by linarith, ?_⟩
    intro z z' θ τ τ' hz hzR hz' hz'R hθ hτ hτ'
    rw [hpart1 z θ τ hz hθ hτ, hpart1 z' θ τ' hz' hθ hτ']
    have h1 := hN0b z z' θ hz hzR hz' hz'R hθ
    have h2 := hNpz.2.2 z z' θ θ τ τ' hz hz' hθ hθ hτ hτ'
    have h3 : |z - z'| ^ α ≤ (|z - z'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (le_add_of_nonneg_right (abs_nonneg _)) h.hα.le
    have h5 : (0 : ℝ) ≤ (|z - z'| + |τ - τ'|) ^ α := Real.rpow_nonneg (by positivity) _
    have h6 : (0 : ℝ) ≤ N0 := hN0
    calc |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
            + Work.Spaces.pz (gSlice g τ) z θ
            - (deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'
              + Work.Spaces.pz (gSlice g τ') z' θ)|
        = |(deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
              - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z')
            + (Work.Spaces.pz (gSlice g τ) z θ - Work.Spaces.pz (gSlice g τ') z' θ)| := by
          ring_nf
      _ ≤ |deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z
              - deriv (fun z'' => Work.Construction.Fstar (pExp α) z'' θ) z'|
            + |Work.Spaces.pz (gSlice g τ) z θ - Work.Spaces.pz (gSlice g τ') z' θ| :=
          abs_add_le _ _
      _ ≤ N0 * |z - z'| ^ α + Npz * (|z - z'| + |θ - θ| + |τ - τ'|) ^ α :=
          add_le_add h1 h2
      _ ≤ (N0 + Npz) * (|z - z'| + |τ - τ'|) ^ α := by
          simp only [sub_self, abs_zero, add_zero] at *
          nlinarith [mul_le_mul_of_nonneg_left h3 h6, h5]

end Work.FTS.FireFix.Prime
