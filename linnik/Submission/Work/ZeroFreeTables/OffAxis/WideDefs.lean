/-
# ZeroFreeTables/OffAxis — `WideDefs`

The height-`W` numbering of the off-axis route (`OFFAXIS_ROUTE_LEAD.md` §3.1): the predicate
`IsMinWideAt H W χ₁ ρ₁` says that `ρ₁` is a non-principal zero at height `≤ H` of `χ₁`, and that
`λ₁ = lamOf q ρ₁` is minimal among the zeros of *all* non-principal characters at height `≤ W`.

This is the height-parametric version of `Work.ZeroFreeTables.IsMin1WideAt` (which is the case
`H ≤ 1`, `W = 10`): the engines of HB §§6–10 (`hbLemma6_2_engine_*`, `hbLemma9_2_engine`,
`hbLemma9_3_engine`) use `IsMin1WideAt 10` only through the two facts

* `hmax`: a zero at height `≤ W` has `Re ≤ Re ρ₁` (i.e. `λ ≥ λ₁`), and
* `hzw`: a zero in the window `‖1 + i·Im s - u‖ ≤ δ` around a point `s` has `Re ≤ Re ρ₁`,
  which follows from `hmax` when `|s.im| + δ ≤ W`.

Their proofs are unchanged in the general setting; only the constant `10` becomes `W`.

`IsRectStrip L χ₁ ρ₁` (minimality over `|Im| ≤ L` together with the zero-free strip `(L, 10L]`)
gives `IsMinWideAt L (10L) χ₁ ρ₁` as soon as `λ₁ ≤ 2`: below height `L` this is the strip
minimality, and in the strip `(L, 10L]` every zero has `λ > 2 ≥ λ₁`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- **HB §6 numbering at height `H` with room `W`**: `ρ₁` is a non-principal zero of `χ₁` with
`|Im ρ₁| ≤ H`, and `λ₁` is minimal over *all* non-principal zeros of height `≤ W`. -/
def IsMinWideAt {q : ℕ} [NeZero q] (H W : ℝ) (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  χ₁ ≠ 1 ∧ zeroMult χ₁ ρ₁ ≠ 0 ∧ |ρ₁.im| ≤ H ∧
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 → zeroMult χ u ≠ 0 → |u.im| ≤ W →
      lamOf q ρ₁ ≤ lamOf q u

/-- **`IsRectStrip` gives the height-`W` numbering** (`W = 10L`) below the strip threshold `2`:
below height `L` the strip minimality applies, and in `(L, 10L]` every zero has `λ > 2 ≥ λ₁`. -/
theorem isMinWideAt_of_isRectStrip {q : ℕ} [NeZero q] {L : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (hR : IsRectStrip L χ₁ ρ₁)
    (hlam : lamOf q ρ₁ ≤ 2) : IsMinWideAt L (10 * L) χ₁ ρ₁ := by
  refine ⟨hR.1.1, hR.1.2.1, hR.1.2.2, ?_⟩
  intro χ u hχ hzm him
  by_cases h : |u.im| ≤ L
  · exact hR.2.1 χ u ⟨hχ, hzm, h⟩
  · have h2 := hR.2.2 χ u ⟨hχ, hzm, him⟩ (not_le.mp h)
    linarith

/-- A zero at height `≤ W` of a non-principal character lies to the left of `ρ₁`. -/
theorem IsMinWideAt.hmax {q : ℕ} [NeZero q] {H W : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : IsMinWideAt H W χ₁ ρ₁) (hL : 0 < Real.log q) (ψ : DirichletCharacter ℂ q)
    [NeZero ψ.conductor] (hψ : ψ ≠ 1) {R : ℝ} {u : ℂ}
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 R)) u ≠ 0) (him : |u.im| ≤ W) : u.re ≤ ρ₁.re := by
  have hle := hmin.2.2.2 ψ u hψ (zeroMult_ne_zero_of_divisor_v2 ψ hψ hdiv) him
  simp only [lamOf] at hle
  nlinarith [hL, hle]

/-- Every zero of the window `‖1 + i·Im s - u‖ ≤ δ` around a point `s` with `|Im s| + δ ≤ W`
lies to the left of `ρ₁`. -/
theorem IsMinWideAt.hzw {q : ℕ} [NeZero q] {H W : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : IsMinWideAt H W χ₁ ρ₁) (hL : 0 < Real.log q) (ψ : DirichletCharacter ℂ q)
    [NeZero ψ.conductor] (hψ : ψ ≠ 1) {s : ℂ} {δ : ℝ} (hIm : |s.im| + δ ≤ W) :
    ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ ρ₁.re := by
  intro u hdiv hwin
  refine hmin.hmax hL ψ hψ hdiv ?_
  have h1 : |s.im - u.im| ≤ δ := by
    have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
    rw [h'] at h; exact le_trans h hwin
  have h2 : |u.im| ≤ |s.im| + δ := by
    calc |u.im| = |s.im - (s.im - u.im)| := by ring_nf
      _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
      _ ≤ |s.im| + δ := by linarith
  linarith [h2, hIm]

end Work.ZeroFreeTables
