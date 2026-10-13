/-
# `Assembly/AnsatzDefs.lean` — the product ansatz of the `RegQ`-counterexample

This module fixes the vocabulary of the counterexample to the norm comparison
`HkSq α n (D_θ f) ≤ HkSq α (n+1) f` for `α < -1/10` (the target
`Work.FTS.CoercivityFix.Assembly.exists_not_normSub_lt`).

## The one-variable operators

For a product `f z θ = ψ z * h θ` the operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ`
act on the two factors separately:

* `vz ψ = z ψ'`, `vzIter j ψ` its `j`-fold iterate, so that `D_z^j f = (vzIter j ψ) · h`;
* `vth h = sin(2θ) h'`, `vthIter i h` its `i`-fold iterate, so that `D_θ^i f = ψ · (vthIter i h)`.

The two integrals of the counterexample are then the z-slot and the θ-slot

* `Zc ψ j = ∫_z (vzIter j ψ · w)^2`,
* `Sc h i q = ∫_θ (vthIter i h)^2 · sin(2θ)^{-q}`.

## The concrete bumps

`psiA z = χ(z - 5/2)` (supported in `(1/2, 9/2)`) and `hA δ θ = χ((θ - 1/2)/δ)`
(supported in `(1/2 - 2δ, 1/2 + 2δ)`), both built from the workspace cut-off
`Work.Stability.chi` (`= smoothTransition (2 - |x|)`, `C^∞`, `= 1` on `[-1,1]`, `= 0` off
`(-2,2)`).  The counterexample is `ansatz δ z θ = psiA z * hA δ θ`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## The one-variable operators -/

/-- The one-variable operator `z ↦ z · ψ'(z)`. -/
noncomputable def vz (ψ : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv ψ z

/-- The `j`-fold iterate of `vz`. -/
noncomputable def vzIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, ψ => ψ
  | k + 1, ψ => vz (vzIter k ψ)

/-- The one-variable operator `θ ↦ sin(2θ) · h'(θ)`. -/
noncomputable def vth (g : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv g θ

/-- The `i`-fold iterate of `vth`. -/
noncomputable def vthIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, g => g
  | i + 1, g => vth (vthIter i g)

@[simp] theorem vzIter_zero (ψ : ℝ → ℝ) : vzIter 0 ψ = ψ := rfl
@[simp] theorem vzIter_succ (k : ℕ) (ψ : ℝ → ℝ) : vzIter (k + 1) ψ = vz (vzIter k ψ) := rfl
@[simp] theorem vthIter_zero (g : ℝ → ℝ) : vthIter 0 g = g := rfl
@[simp] theorem vthIter_succ (i : ℕ) (g : ℝ → ℝ) : vthIter (i + 1) g = vth (vthIter i g) := rfl

/-- Iterating: `vzIter a (vzIter b ψ) = vzIter (a + b) ψ`. -/
theorem vzIter_add (a b : ℕ) (ψ : ℝ → ℝ) :
    vzIter a (vzIter b ψ) = vzIter (a + b) ψ := by
  induction a with
  | zero => simp
  | succ a ih => rw [vzIter_succ, ih, Nat.succ_add, vzIter_succ]

/-- Iterating: `vthIter a (vthIter b g) = vthIter (a + b) g`. -/
theorem vthIter_add (a b : ℕ) (g : ℝ → ℝ) :
    vthIter a (vthIter b g) = vthIter (a + b) g := by
  induction a with
  | zero => simp
  | succ a ih => rw [vthIter_succ, ih, Nat.succ_add, vthIter_succ]

/-! ## The two slot integrals -/

/-- The radial slot `Z_j = ∫_z (D_z^j ψ · w)^2`. -/
noncomputable def Zc (ψ : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (vzIter j ψ z * Work.Spaces.w z) ^ 2

/-- The angular slot `S^i_q = ∫_θ (D_θ^i h)^2 · sin(2θ)^{-q}`. -/
noncomputable def Sc (g : ℝ → ℝ) (i : ℕ) (q : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (vthIter i g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)

/-! ## The concrete bumps and the ansatz -/

/-- The angular centre `θ₀ = 1/2` of the counterexample. -/
def th0 : ℝ := 1 / 2

/-- The radial bump `ψ(z) = χ(z - 5/2)`, supported in `(1/2, 9/2)`. -/
noncomputable def psiA : ℝ → ℝ := fun z => Work.Stability.chi (z - 5 / 2)

/-- The angular bump `h_δ(θ) = χ((θ - θ₀)/δ)`, supported in `(θ₀ - 2δ, θ₀ + 2δ)`. -/
noncomputable def hA (δ : ℝ) : ℝ → ℝ := fun θ => Work.Stability.chi ((θ - th0) / δ)

/-- **THE COUNTEREXAMPLE**: `f_δ(z,θ) = ψ(z)·h_δ(θ)`. -/
noncomputable def ansatz (δ : ℝ) : ℝ → ℝ → ℝ := fun z θ => psiA z * hA δ θ

@[simp] theorem psiA_apply (z : ℝ) : psiA z = Work.Stability.chi (z - 5 / 2) := rfl
@[simp] theorem hA_apply (δ θ : ℝ) : hA δ θ = Work.Stability.chi ((θ - th0) / δ) := rfl
@[simp] theorem ansatz_apply (δ z θ : ℝ) : ansatz δ z θ = psiA z * hA δ θ := rfl

/-! ## The pure and mixed parts of the `ℋ^k`-integrand

Splitting `Work.Spaces.HkIntegrand` into its radial part (`Pure`) and its genuinely mixed
part (`Mixed`) is what makes the level shift `n ↦ n+1` transparent: `Mixed` is shifted by
one under `D_θ` (this is `Mixed_succ`), while `Pure` simply grows by the top slot. -/

/-- The radial part of the `ℋ^k`-integrand: the sum of the weighted `D_z`-slots. -/
noncomputable def Pure (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (Work.Spaces.DzIter i f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed part of the `ℋ^k`-integrand: the sum of the weighted `mixed j i`-slots with
`1 ≤ i` and `i + j ≤ k`. -/
noncomputable def Mixed (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
    else 0

/-- The splitting of the `ℋ^k`-integrand into its radial and mixed parts (definitional). -/
theorem HkIntegrand_eq_Pure_add_Mixed (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ = Pure k f z θ + Mixed α k f z θ := rfl

end Work.FTS.CoercivityFix.Assembly
