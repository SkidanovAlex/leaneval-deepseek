/-
# `Work.FTS.RegPkgGal.Basic` — the API of the corrected package `RegPkg'`

The counterpart, field by field, of the API block `Work.FTS.Regularity.RegPkg.*` in
`Submission/Work/FTS/Regularity/Defs.lean`, for the corrected structure `RegPkg'` of
`Submission/Work/FTS/RegPkgGal/Defs.lean` (design correction 5: the third clause of `htay` is the
Hölder form `≤ K z² |Δθ|^α`, not the false Lipschitz form `≤ K z |Δθ|`).

The proofs are the delivered ones verbatim — the correction touches only the third clause of
`htay`, and no *other* clause is affected by it.  The only genuinely different statement is
`tay'`/`thmod'`: the delivered `thmod` (the `θ`-modulus from the `Jet`) is unchanged, and the
Taylor angular clause now carries `z²|Δθ|^α` instead of `z|Δθ|`.

**Why there is no `RegPkg.toRegPkg'`.**  The Lipschitz clause does *not* imply the Hölder clause
with a universal constant: for `z = |Δθ| = ε` one has `z|Δθ| = ε²` while `z²|Δθ|^α = ε^{2+α}`, and
`ε^{-α}` is unbounded.  The two clauses are genuinely different bounds, and only the Hölder one is
true for the genuine solution (`g ≈ c(τ)z²Γ(θ)`, `Γ = (sinθcos²θ)^α`); this is exactly why the
correction has to be re-derived rather than recovered from the delivered interface.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

variable {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}

theorem RegPkg'.alpha_pos (h : RegPkg' α S A B g) : 0 < α := h.hα
theorem RegPkg'.alpha_le (h : RegPkg' α S A B g) : α ≤ 1 / 3 := h.hα13
theorem RegPkg'.strip_pos (h : RegPkg' α S A B g) : 0 < S := h.hS

theorem RegPkg'.pExp_pos (h : RegPkg' α S A B g) : 0 < pExp α :=
  Work.FTS.Regularity.pExp_pos h.hα
theorem RegPkg'.pExp_le_one (h : RegPkg' α S A B g) : pExp α ≤ 1 :=
  Work.FTS.Regularity.pExp_le_one h.hα13

/-- The `VanishTheta` data, as a `Prop` about the slice. -/
theorem RegPkg'.vanish (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Work.Spaces.VanishTheta (gSlice g τ) := h.hvt τ hτ

/-- The perturbation vanishes at `z = 0`. -/
theorem RegPkg'.zero_z (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : g 0 θ τ = 0 := h.hquad0 τ hτ θ hθ

/-- The `z`-derivative of the perturbation vanishes at `z = 0`. -/
theorem RegPkg'.zero_z_pz (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.pz (gSlice g τ) 0 θ = 0 :=
  h.hquad τ hτ θ hθ

/-- **Pointwise boundedness of the perturbation**: `|g| ≤ Cv` on the domain, since `Γ ≤ 1`. -/
theorem RegPkg'.abs_le_Cv (h : RegPkg' α S A B g) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv := by
  obtain ⟨Cv, hCv0, hCv⟩ := h.hvan
  refine ⟨Cv, hCv0, fun τ hτ z θ hz hθ => ?_⟩
  refine le_trans (hCv τ hτ z θ hz hθ) ?_
  have hΓ1 : Gamma α θ ≤ 1 := Work.ConstructionInstance.Gamma_le_one h.hα.le hθ
  have hΓ0 : 0 ≤ Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  nlinarith

/-- **The linear vanishing at `z = 0`**: `|g z θ τ| ≤ K z` for `z ∈ [0,1]`. -/
theorem RegPkg'.abs_le_Kz (h : RegPkg' α S A B g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → z ≤ 1 →
      θ ∈ Work.Spaces.Iθ → |g z θ τ| ≤ K * z := by
  obtain ⟨K, hK0, hK⟩ := h.htay
  refine ⟨K, hK0, fun τ hτ z θ hz hz1 hθ => ?_⟩
  have h1 := (hK τ hτ θ hθ).1 z hz (by linarith)
  have hz2 : z ^ 2 ≤ z := by nlinarith
  calc |g z θ τ| ≤ K * z ^ 2 := h1
    _ ≤ K * z := mul_le_mul_of_nonneg_left hz2 hK0

/-- **The boundedness box of the perturbation** from the regularity jet. -/
theorem RegPkg'.abs_le_Ng (h : RegPkg' α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ N := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun τ hτ z θ hz hθ => hN.abs_le hz hθ hτ⟩

/-- The uniform bound on `∂_z g` from the regularity jet. -/
theorem RegPkg'.abs_le_Npz (h : RegPkg' α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ N := by
  obtain ⟨N, hN⟩ := h.hpz
  exact ⟨N, hN.1, fun τ hτ z θ hz hθ => hN.abs_le hz hθ hτ⟩

/-- The uniform bound on `∂_τ g` from the regularity jet. -/
theorem RegPkg'.abs_le_Nd (h : RegPkg' α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |deriv (fun s => g z θ s) τ| ≤ N := by
  obtain ⟨N, hN⟩ := h.hgdoth
  exact ⟨N, hN.1, fun τ hτ z θ hz hθ => hN.abs_le hz hθ hτ⟩

/-- **The radial modulus of the perturbation at a strip time** (`Lg` of the `St1`-class). -/
theorem RegPkg'.zmod (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |g z θ τ - g z' θ τ| ≤ Lg * |z - z'| ^ α := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun z z' θ hz hz' hθ => hN.zmod hz hz' hθ hτ⟩

/-- **The angular modulus of the perturbation at a strip time** (`Lθ` of the `St1`-class). -/
theorem RegPkg'.thmod (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ z θ θ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ τ - g z θ' τ| ≤ Lθ * |θ - θ'| ^ α := by
  obtain ⟨N, hN⟩ := h.hg
  exact ⟨N, hN.1, fun z θ θ' hz hθ hθ' => hN.thmod hz hθ hθ' hτ⟩

/-- **The Taylor data of the `St1`-class at a strip time**, in the shape consumed by the
quantitative per-slice transfer — `Basic` counterpart of `Regularity.RegPkg.tay`, with the
*corrected* angular clause `|g z θ τ - g z θ' τ| ≤ K z² |θ - θ'|^α`. -/
theorem RegPkg'.tay (h : RegPkg' α S A B g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K * z ^ 2 * |θ - θ'| ^ α) := h.htay

/-- The three Taylor clauses at a fixed strip time. -/
theorem RegPkg'.tay_at (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K * z ^ 2 * |θ - θ'| ^ α) := by
  obtain ⟨K, hK0, hK⟩ := h.htay
  exact ⟨K, hK0, hK τ hτ⟩

/-- The support data: the full profile vanishes for `z ≥ L`. -/
theorem RegPkg'.supp (h : RegPkg' α S A B g) :
    ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z → profFull α g z θ τ = 0 :=
  h.hsupp

/-- The honest `ℋ⁴`-membership of every slice. -/
theorem RegPkg'.hH4_at (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Work.Spaces.HkMem (pExp α) 4 (gSlice g τ) := h.hH4 τ hτ

/-- The `τ`-jet of the perturbation. -/
theorem RegPkg'.gdoth (h : RegPkg' α S A B g) :
    ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => g z θ s) τ) := h.hgdoth

/-- The joint `C¹` smoothness of `(z,τ) ↦ g z θ τ` at every fixed angle `θ ∈ Iθ`. -/
theorem RegPkg'.cont (h : RegPkg' α S A B g) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) := h.hcont θ hθ

/-! ## Elementary consequences of the corrected Taylor clause -/

/-- The corrected angular clause, in the form in which the composite-Hölder transfer uses it: at a
*small* radius `z ≤ 2` and with the *fixed* parameter `z`, the difference in `θ` is dominated by
`K z²|Δθ|^α`. -/
theorem RegPkg'.tay_th' {K τ z θ θ' : ℝ}
    (hK : ∀ θ ∈ Work.Spaces.Iθ, (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K * z ^ 2 * |θ - θ'| ^ α))
    (hz : 0 ≤ z) (hz2 : z ≤ 2) (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |g z θ τ - g z θ' τ| ≤ K * z ^ 2 * |θ - θ'| ^ α :=
  ((hK θ hθ).2.2) z hz hz2 θ' hθ'

end Work.FTS.RegPkgGal
