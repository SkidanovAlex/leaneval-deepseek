import Mathlib
import Submission.ArcFamily
import Submission.TrigObservation

/-! Section 5 objects (paper arXiv:1907.09464v1 §5), quadrant-normalised.

We fix the construction size `n`, the target level `K : ℝ`, and a quadrant
family `F : Family.Quad n N`.  All sums over odd sine positions run over
`r = 0..n-1` (frequency `2r+1`, i.e. `S_o = {1,3,...,2n-1}`).

The colouring `α : Fin N → ℝ` takes values ±1 (one value per quadrant
interval).  Its Fourier-type coefficients are

    ê_r(α) := 4·K·√n · Σ_i α_i · ∫_{I_i} sin((2r+1)θ) dθ ,       r < n

and the associated sine polynomial is

    ŝ_α(θ0) := Σ_{r<n} ê_r(α)·sin((2r+1)θ0).

By the trig observation (`Submission.Trig`), for θ0 ∈ [0, π/2]:

    ŝ_α(θ0) = K√n · Σ_i α_i · ∫_{I_i} [ D(θ−θ0) − D(θ+θ0) ] dθ
    D(u) := sin(2n·u)/sin(u)

which is the basis of the lower/upper bounds on `ŝ_α` (Lemma 5.10 in the paper).
Finally the actual odd sine polynomial is `s_o(θ) = Σ_{r<n} ε_r sin((2r+1)θ)`
for an unknown colouring `ε : Fin n → ℝ`, `ε_r ∈ {±1}`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

namespace Submission
namespace S5

/-- Odd sine frequency `2r+1` (as a real). -/
def freq (r : ℕ) : ℝ := (2 * (r : ℝ) + 1)

/-- `sin((2r+1)·θ)`. -/
def oddSin (r : ℕ) (θ : ℝ) : ℝ := Real.sin (freq r * θ)

/-- The coefficient vector for the `r`-th constraint (times `α`), before `α`:
`(v_r)_i = 4·K·√n · ∫_{I_i} sin((2r+1)θ) dθ`. -/
def vec (n N : ℕ) (K : ℝ) (F : Family.Quad n N) (r : ℕ) : Fin N → ℝ :=
  fun i => 4 * K * Real.sqrt (n : ℝ) *
    ∫ θ in (F.arc i).lo..(F.arc i).hi, oddSin r θ

/-- The hat coefficients `ê_r(α) = Σ_i α_i (v_r)_i`. -/
def ehat (n N : ℕ) (K : ℝ) (F : Family.Quad n N) (α : Fin N → ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin N, α i * vec n N K F r i

/-- The sine polynomial with Fourier-type coefficients `ê`:
`ŝ_α(θ0) = Σ_{r<n} ê_r(α)·sin((2r+1)θ0)`. -/
def sHat (n N : ℕ) (K : ℝ) (F : Family.Quad n N) (α : Fin N → ℝ) (θ0 : ℝ) : ℝ :=
  ∑ r ∈ Finset.range n, ehat n N K F α r * oddSin r θ0

/-- The odd sine polynomial from a colouring `ε : Fin n → ℝ`:
`s_o(θ) = Σ_{r<n} ε_r·sin((2r+1)θ)`. -/
def sOdd (n : ℕ) (ε : Fin n → ℝ) (θ : ℝ) : ℝ :=
  ∑ i : Fin n, ε i * oddSin i.1 θ

/-- Colouring α in `{±1}`. -/
def IsColoring {ι : Type*} (α : ι → ℝ) : Prop := ∀ i, α i = 1 ∨ α i = -1

/-- A full data package for Theorem 2.4: quadrant colouring `α`, sign colouring
`ε` (both ±1), smallness of `ê(α)` (needed so `ε = ê + (ε − ê)` makes sense as
a perturbation of a vector in `[-1,1]^n`), and the closeness of `s_o` to `ŝ`. -/
structure SinCert (n N : ℕ) (K : ℝ) (F : Family.Quad n N) where
  α : Fin N → ℝ
  eps : Fin n → ℝ
  α_sign : IsColoring α
  eps_sign : IsColoring eps
  ehat_le_one : ∀ r : Fin n, |ehat n N K F α r.1| ≤ 1
  eps_close : ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) → |sOdd n eps θ - sHat n N K F α θ| ≤ 75 * Real.sqrt (n : ℝ)

end S5
end Submission
