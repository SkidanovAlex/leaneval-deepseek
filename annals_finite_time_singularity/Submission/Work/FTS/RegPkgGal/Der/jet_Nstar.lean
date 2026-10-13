import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.regPkg_inhabited
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.jet_Nstar`

The modulation term `N_*` of the fake-time equation,

  `N_*(μ,λ,g) = -μ·g - (μ + λ + μλ)·D_z g`   (`Work.Construction.Nstar`),

evaluated on the clock functions `μ(τ)`, `λ(τ)` and on the perturbation family
`(z,θ,τ) ↦ g z θ τ`.  The statement is the `Jet`-regularity of that family:

if `g` and `D_z g(·,·,τ)` are bounded and jointly `α`-Hölder on the strip
`z ≥ 0, θ ∈ Iθ, τ ∈ [0,S]` with constant `N` (`Jet`), and if `μ`, `λ` are bounded by `Nmu` and
`α`-Hölder with constant `Nmu` on `[0,S]`, then `N_*` is again a `Jet` on the strip.

The proof is purely algebraic: `μ`, `λ`, `μλ` and `μ + λ + μλ` are `Jet`s depending on `τ` only
(`Jet.of_time` below), and the `Jet`-calculus of `Submission.Work.FTS.Regularity.regPkg_inhabited`
(`Jet.add`, `Jet.neg`, `Jet.mul`, `Jet.congr`) closes the term under products and sums, with the
constants adding: a product of a `Jet` of constant `N₁` with one of constant `N₂` has constant
`2·N₁·N₂`.

This is exactly the `hNs` hypothesis of `Work.FTS.RegPkgGal.Der.rhs_jet_of_parts`.
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-- A function of `τ` alone which is bounded by `M` on `[0,S]` and `α`-Hölder there with
constant `M` is a `Jet` (constant in `z` and `θ`). -/
theorem Jet.of_time {α S M : ℝ} {m : ℝ → ℝ} (hα0 : 0 ≤ α) (hM : 0 ≤ M)
    (hb : ∀ τ ∈ Set.Icc 0 S, |m τ| ≤ M)
    (hh : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |m τ - m τ'| ≤ M * |τ - τ'| ^ α) :
    Work.FTS.Regularity.Jet α S M (fun _ _ τ => m τ) := by
  refine ⟨hM, fun _ _ τ _ _ hτ => hb τ hτ, ?_⟩
  intro z z' θ θ' τ τ' _ _ _ _ hτ hτ'
  refine le_trans (hh τ hτ τ' hτ') (mul_le_mul_of_nonneg_left ?_ hM)
  refine Real.rpow_le_rpow (abs_nonneg _) ?_ hα0
  have h1 : 0 ≤ |z - z'| := abs_nonneg _
  have h2 : 0 ≤ |θ - θ'| := abs_nonneg _
  have h3 : 0 ≤ |τ - τ'| := abs_nonneg _
  linarith

theorem jet_Nstar {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {mu lam : ℝ → ℝ} {N Nmu : ℝ}
    (hα : 0 < α) (hS : 0 < S)
    (hg : Work.FTS.Regularity.Jet α S N g)
    (hDg : Work.FTS.Regularity.Jet α S N (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hmu : 0 ≤ Nmu ∧ ∀ τ ∈ Set.Icc 0 S, |mu τ| ≤ Nmu ∧ ∀ τ' ∈ Set.Icc 0 S,
      |mu τ - mu τ'| ≤ Nmu * |τ - τ'| ^ α)
    (hlam : ∀ τ ∈ Set.Icc 0 S, |lam τ| ≤ Nmu ∧ ∀ τ' ∈ Set.Icc 0 S,
      |lam τ - lam τ'| ≤ Nmu * |τ - τ'| ^ α) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α S Nc
      (fun z θ τ => Work.Construction.Nstar (mu τ) (lam τ) (fun z θ => g z θ τ) z θ) := by
  obtain ⟨hNmu0, hmu⟩ := hmu
  have hMuh : ∀ τ ∈ Set.Icc 0 S, |mu τ| ≤ Nmu := fun τ hτ => (hmu τ hτ).1
  have hMud : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |mu τ - mu τ'| ≤ Nmu * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => (hmu τ hτ).2 τ' hτ'
  have hLamh : ∀ τ ∈ Set.Icc 0 S, |lam τ| ≤ Nmu := fun τ hτ => (hlam τ hτ).1
  have hLamd : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |lam τ - lam τ'| ≤ Nmu * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => (hlam τ hτ).2 τ' hτ'
  have hMuJ : Work.FTS.Regularity.Jet α S Nmu (fun _ _ τ => mu τ) :=
    Jet.of_time hα.le hNmu0 hMuh hMud
  have hLamJ : Work.FTS.Regularity.Jet α S Nmu (fun _ _ τ => lam τ) :=
    Jet.of_time hα.le hNmu0 hLamh hLamd
  have hMuLamJ : Work.FTS.Regularity.Jet α S (2 * Nmu * Nmu) (fun _ _ τ => mu τ * lam τ) :=
    Work.FTS.Regularity.Jet.mul hMuJ hLamJ
  have hCJ : Work.FTS.Regularity.Jet α S ((Nmu + Nmu) + 2 * Nmu * Nmu)
      (fun _ _ τ => mu τ + lam τ + mu τ * lam τ) :=
    Work.FTS.Regularity.Jet.add (Work.FTS.Regularity.Jet.add hMuJ hLamJ) hMuLamJ
  have hMuGJ : Work.FTS.Regularity.Jet α S (2 * Nmu * N) (fun z θ τ => mu τ * g z θ τ) :=
    Work.FTS.Regularity.Jet.mul hMuJ hg
  have hCDgJ : Work.FTS.Regularity.Jet α S (2 * ((Nmu + Nmu) + 2 * Nmu * Nmu) * N)
      (fun z θ τ => (mu τ + lam τ + mu τ * lam τ)
        * Work.Spaces.Dz (fun z θ => g z θ τ) z θ) :=
    Work.FTS.Regularity.Jet.mul hCJ hDg
  refine ⟨2 * Nmu * N + 2 * ((Nmu + Nmu) + 2 * Nmu * Nmu) * N, ?_⟩
  refine Work.FTS.Regularity.Jet.congr
    (Work.FTS.Regularity.Jet.add (Work.FTS.Regularity.Jet.neg hMuGJ)
      (Work.FTS.Regularity.Jet.neg hCDgJ)) ?_
  intro z θ τ hz hθ hτ
  simp only [Work.Construction.Nstar, Work.Spaces.Dz]
  ring

end Work.FTS.RegPkgGal.Der
