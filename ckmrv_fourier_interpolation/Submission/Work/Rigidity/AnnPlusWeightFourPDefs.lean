/-
# Definitions for the weight-four rigidity lemma at eigenvalue `-1`

These are the auxiliary functions `g_0, g_1, g_2`, `h_0, h_1, h_2` and `m` of the proof of
CKMRV Proposition `prop: HFE plus` (`univopt.tex`, Section 3.3) specialised to weight `4`,
together with the combination

  `m = h_0 - (π i / 6) E₂ h_1`

which is the weight-six modular form underlying `f`.

For `f : ℍ → ℂ` with `(T - I)² f = 0` and `f ∣[4] S = -f` (i.e. `f ∈ Ann₄(𝓘₊, 𝒫)`) one has

* `g_0 = f ∣[4] T - f` is `T`-periodic;
* `h_2 = τ² g_0 - 2τ g_1 + g_2` spans a weight-two `SL(2,ℤ)`-invariant function, which
  therefore vanishes (`M_2 = 0`);
* hence `h_1 = -2τ g_0 + 2 g_1` is a weight-four modular form and `m` a weight-six one;
* `f = τ h_0 + h_1 / 2`.
-/
import Mathlib
import Submission.Work.Rigidity.Diff
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

/-- The `T`-defect `g_0 = f ∣[4] T - f` of CKMRV's proof, at slash weight `4`. -/
def G0 (f : ℍ → ℂ) : ℍ → ℂ := f ∣[(4 : ℤ)] ModularGroup.T - f

/-- `g_1 = f`. -/
def G1 (f : ℍ → ℂ) : ℍ → ℂ := f

/-- `g_2 = f ∣[4] (TS) + f`. -/
def G2 (f : ℍ → ℂ) : ℍ → ℂ := f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.S) + f

/-- The weight-two combination `h_2 = τ² g_0 - 2τ g_1 + g_2`. -/
def H2 (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => (τ : ℂ) ^ 2 * G0 f τ - 2 * (τ : ℂ) * G1 f τ + G2 f τ

/-- The weight-four combination `h_1 = -2τ g_0 + 2 g_1 = 2 (f - τ (fstDiff f))`. -/
def H1 (f : ℍ → ℂ) : ℍ → ℂ := fun τ => -2 * (τ : ℂ) * G0 f τ + 2 * G1 f τ

/-- The weight-six combination `h_0 = g_0`. -/
def H0 (f : ℍ → ℂ) : ℍ → ℂ := G0 f

/-- `m = h_0 - (π i / 6) E₂ h_1`, the weight-six modular form underlying `f`. -/
def Mmod (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => H0 f τ - (Real.pi * Complex.I / 6) * Work.Kernels.E2Fun τ * H1 f τ

lemma G0_apply (f : ℍ → ℂ) (τ : ℍ) : G0 f τ = (f ∣[(4 : ℤ)] ModularGroup.T) τ - f τ := rfl

lemma G2_apply (f : ℍ → ℂ) (τ : ℍ) :
    G2 f τ = (f ∣[(4 : ℤ)] (ModularGroup.T * ModularGroup.S)) τ + f τ := rfl

end Work.Rigidity
