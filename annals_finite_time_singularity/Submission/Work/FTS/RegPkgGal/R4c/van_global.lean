/-
# `Work.FTS.RegPkgGal.R4c.van_global`

**The global class lemma R4c.**  On a strip `τ ∈ [0,S]`, a family `g` whose angular derivative
satisfies the `Γ`-bound `|D_θ g| = |sin(2θ)·∂_θ g| ≤ Cθ·z²·Γ(θ)`, which vanishes on the two angular
boundary lines (`VanishTheta`) and which satisfies the *far-field* bound `|g z θ τ| ≤ Lz·Γ(θ)` for
`z ≥ Lz`, is dominated by `Γ` on the whole half-line `z ≥ 0`:

  `∃ Cv ≥ 0, ∀ τ ∈ [0,S], ∀ z ≥ 0, ∀ θ ∈ Iθ, |g z θ τ| ≤ Cv · Γ(θ)`.

This is R4b (`R4b/van_of_dthvan`) with the `z ≤ 2` window removed: the *same* hypotheses with no
upper bound on `z`, at the price of one extra hypothesis, the far-field bound `hfar`, which in the
paper is carried by the compact support of the vorticity (the perturbation vanishes identically
for large `z`).  Nothing below `z = Lz` and above `z = max 2 Lz` is new; the interesting range is
the intermediate one, and it is covered by the angular fundamental-theorem-of-calculus bound with
its `z²` factor (`van_zsq`), whose constant is uniform in `z`.

## Proof

`van_zsq` (the analytic core, `R4c/van_zsq.lean`) gives `K ≥ 0` with

  `|g z θ τ| ≤ K·z²·Γ(θ)`   for every `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]`.

Then

* for `z ≤ Lz`: `|g z θ τ| ≤ K·z²·Γ(θ) ≤ K·Lz²·Γ(θ)`, using `z² ≤ Lz²` and `Γ ≥ 0`;
* for `z > Lz`: `|g z θ τ| ≤ Lz·Γ(θ)` by `hfar`.

So `Cv := max (K·Lz²) Lz` works (it is `≥ 0` since `K ≥ 0 ≥ ...`, `Lz ≥ 0`).

The gluing itself, with the `z²` bound as a hypothesis, is the helper `van_global_of_zsq` below.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.R4c.van_zsq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R4c

set_option autoImplicit false

/-- **The gluing step of R4c.**  If `|g|` is dominated by `K·z²·Γ` on the whole half-line (the
output of the analytic core `van_zsq`) and by `Lz·Γ` in the far field `z ≥ Lz`, then `|g|` is
dominated by a single multiple of `Γ` everywhere: the case `z ≤ Lz` uses the `z²`-bound and
`z² ≤ Lz²`, the case `z > Lz` is the far-field bound.  The constant is
`max (K·Lz²) Lz`. -/
theorem van_global_of_zsq {α S Lz : ℝ} (hLz : 0 ≤ Lz)
    {g : ℝ → ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hzsq : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hfar : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Lz * Work.FTS.Regularity.Gamma α θ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma α θ := by
  refine ⟨max (K * Lz ^ 2) Lz, ?_, ?_⟩
  · exact le_trans (mul_nonneg hK (sq_nonneg Lz)) (le_max_left _ _)
  · intro τ hτ z θ hz hθ
    have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
    rcases le_or_gt z Lz with hzL | hzL
    · have h1 : |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := hzsq τ hτ z θ hz hθ
      have h2 : K * z ^ 2 ≤ K * Lz ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzL 2) hK
      calc |g z θ τ| ≤ K * z ^ 2 * Work.FTS.Regularity.Gamma α θ := h1
        _ ≤ K * Lz ^ 2 * Work.FTS.Regularity.Gamma α θ := mul_le_mul_of_nonneg_right h2 hΓ0
        _ ≤ max (K * Lz ^ 2) Lz * Work.FTS.Regularity.Gamma α θ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hΓ0
    · have h1 : |g z θ τ| ≤ Lz * Work.FTS.Regularity.Gamma α θ :=
        hfar τ hτ z θ (le_of_lt hzL) hθ
      exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_right _ _) hΓ0)

theorem van_global {α S Cθ Lz : ℝ} (hα : 0 < α) (hS : 0 < S) (hCθ : 0 ≤ Cθ) (hLz : 0 ≤ Lz)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (-1 : ℝ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hfar : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Lz * Work.FTS.Regularity.Gamma α θ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨K, hK0, hzsq⟩ :=
    van_zsq (α := α) (S := S) (Cθ := Cθ) hα hS hCθ hsm hd hvt
  exact van_global_of_zsq hLz hK0 hzsq hfar

end Work.FTS.RegPkgGal.R4c
