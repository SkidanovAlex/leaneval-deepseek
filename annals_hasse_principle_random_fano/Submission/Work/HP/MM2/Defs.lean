import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MMDefs

/-!
# N09 `moment_mix_loc`: pair-summation route (design review hasse2, 2026-09-27)

Statement file for the new sub-lemmas in `DESIGN_REVIEW.md` §1. Every statement elaborates
against the workspace; all proofs are `sorry`. Everything lives in the fresh namespace
`Work.HP.MM2` so that nothing collides with the existing workspace declarations.

Notation: `N = NN d n`, `α = log B`, `W = bigW (wOf B)`, `λ(x) = lamX d n x`.
-/

set_option autoImplicit false

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## Definitions -/

/-- `λ(x) := λ_{N-1}(Λ_{ν(x)})`, the intrinsic "key lemma one vector" quantity. -/
def lamX (d n : ℕ) (x : Fin (n + 1) → ℤ) : ℝ := lam (latOrth (veronese d n x)) (NN d n - 1)

/-- `ζ(s)`, written the way `iotaDN` writes it. -/
def zetaR (s : ℕ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s

/-- `𝓢₁(Λ_{ν(x)} ∖ 0; B(T))`, the weighted small-ball sum. -/
def S1ball (d n : ℕ) (x : Fin (n + 1) → ℤ) (T : ℝ) : ℝ :=
  ∑ᶠ a ∈ {a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T}, 1 / eNorm a

/-- Per-pair target for `D^mix`: `8ι A^{N-2} ‖ν(y)‖ / (α W det Γ_{x,y})`. -/
def mixMain (d n : ℕ) (A B : ℝ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℝ :=
  8 * iotaDN d n * A ^ (NN d n - 2) * eNorm (veronese d n p.2) /
    (Real.log B * (bigW (wOf B) : ℝ) * detL (Gam d n p.1 p.2))

/-- Per-pair target for `D^loc`: `8ι A^{N-2} ‖ν(x)‖ ‖ν(y)‖ / ((αW)² det Γ_{x,y})`. -/
def locMain (d n : ℕ) (A B : ℝ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℝ :=
  8 * iotaDN d n * A ^ (NN d n - 2) * (eNorm (veronese d n p.1) * eNorm (veronese d n p.2)) /
    ((Real.log B * (bigW (wOf B) : ℝ)) ^ 2 * detL (Gam d n p.1 p.2))

/-- Pairs where `x` is non-degenerate: `W λ(x) ≤ A^{3/4}`. -/
def OmegaGood (d n : ℕ) (A B : ℝ) : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
  {p | p ∈ Omega d n B ∧ (bigW (wOf B) : ℝ) * lamX d n p.1 ≤ A ^ ((3 : ℝ) / 4)}

/-- Pairs where `x` is degenerate: `W λ(x) > A^{3/4}`. -/
def OmegaBad (d n : ℕ) (A B : ℝ) : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
  {p | p ∈ Omega d n B ∧ ¬ ((bigW (wOf B) : ℝ) * lamX d n p.1 ≤ A ^ ((3 : ℝ) / 4))}

section sums
variable (d n : ℕ) [DecidableEq (Mon d n)]

/-- `Σ₁^{mix}`: the non-degenerate part of the reindexed `D^mix` (`DmixReindex`). -/
def Sigma1mix (A B : ℝ) : ℝ :=
  (Real.log B * (bigW (wOf B) : ℝ) / 4) *
    ∑ᶠ p ∈ OmegaGood d n A B,
      Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) /
        eNorm (veronese d n p.2)

/-- `Σ₂^{mix}`: the degenerate part. -/
def Sigma2mix (A B : ℝ) : ℝ :=
  (Real.log B * (bigW (wOf B) : ℝ) / 4) *
    ∑ᶠ p ∈ OmegaBad d n A B,
      Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) /
        eNorm (veronese d n p.2)

end sums

/-! ## Level 0: independent lemmas -/

end Work.HP.MM2
