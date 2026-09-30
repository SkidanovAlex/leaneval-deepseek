import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the `k`-th derivative reduction (Heath-Brown, Lemma 1)

Shared vocabulary for the proof of `Work.BMF.kth_derivative_reduction`.
-/

namespace Work.BMF

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

/-- The polynomial phase `Σ_{j : Fin m} α j * h ^ (j+1)`. -/
noncomputable def phase (m : ℕ) (α : Fin m → ℝ) (h : ℕ) : ℝ :=
  ∑ j : Fin m, α j * (h : ℝ) ^ ((j : ℕ) + 1)

/-- The polynomial exponential sum `Σ_{1 ≤ h ≤ ⌊x⌋₊} e(Σ_{j} α j * h ^ (j+1))`. -/
noncomputable def polySum (m : ℕ) (α : Fin m → ℝ) (x : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌊x⌋₊, eC (phase m α h)

/-- The standard box `[0,1]^m` inside `Fin m → ℝ`. -/
def unitBox (m : ℕ) : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m => Set.Icc (0:ℝ) 1)

/-- Indicator of the wrapped arc of radius `δ` around `a`, evaluated at `t`. -/
noncomputable def arcInd (a δ : ℝ) (t : ℝ) : ℝ :=
  if (∃ z : ℤ, |t - a - z| ≤ δ) then 1 else 0

/-- The set of pairs `(m,n) ∈ [1,N]²` counted by `𝒩` in Heath-Brown's Lemma 1. -/
def Nset (k N : ℕ) (f : ℝ → ℝ) (H : ℝ) : Set (ℕ × ℕ) :=
  {mn | mn.1 ∈ Finset.Icc 1 N ∧ mn.2 ∈ Finset.Icc 1 N ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 →
      ∃ z : ℤ, |iteratedDeriv j f (mn.1 : ℝ) / (Nat.factorial j : ℝ)
        - iteratedDeriv j f (mn.2 : ℝ) / (Nat.factorial j : ℝ) - (z : ℝ)|
        ≤ 2 * H ^ (-(j : ℝ))}

end Work.BMF
