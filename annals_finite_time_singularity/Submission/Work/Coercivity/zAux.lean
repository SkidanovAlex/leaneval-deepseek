/-
# Auxiliary definitions for the `D_z`-coercivity estimate (`zDerivative`)

The paper's Proposition "`L²` coercivity for `𝓛_Γ^T` with one `z`-derivative"
(Elgindi, Annals 194 (3) 2021, §"`L²` coercivity for `𝓛_Γ^T` with one `z`-derivative")
states, using `D_z = z ∂_z`,

  `(D_z 𝓛_Γ^T f, D_z f · w²/sin(2θ)^η)_{L²} ≥ (1/4)|D_z f · w/√sin(2θ)^η|² - 10⁸ E_θ¹`.

Its proof expands `D_z(𝓛_Γ^T f)` pointwise into seven terms `Z1,…,Z7` and estimates each
one.  This file fixes the names of those seven terms (and of the weight `Weta` and the two
auxiliary quantities `Kavg`, `C0`) so that the main file and the delegated lemmas can share
them.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The angular weight of the `D_z`-estimate: `w(z)² · sin(2θ)^{-η}`, `η = 99/100`.
This is the weight against which `D_z f` is squared in `EDz`. -/
def Weta (z θ : ℝ) : ℝ := Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)

/-- The angular average `(K, f)_{L²_θ}(z) = ∫_θ K(θ) f(z,θ) dθ`; it equals
`z · L12dens K f z`. -/
def Kavg (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Spaces.Iθ, Spaces.K θ * f z θ

/-- The constant `L₁₂(Transport f)(0)` appearing in the projector term of `𝓛_Γ^T`. -/
def C0 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport f) 0

/-- The `𝓛(D_z f)` term (the coercive one). -/
def Z1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := L (Spaces.Dz f)

/-- The `2z(1+z)^{-2} f` term. -/
def Z2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => 2 * z / (1 + z) ^ 2 * f z θ

/-- The `(2zΓ)/(c(1+z)²) · (K,f)_{L²_θ}` term. -/
def Z3 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (2 * z * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 2)) * Kavg f z

/-- The `-(2z(1-z)Γ)/(c(1+z)³) · L₁₂(f)` term. -/
def Z4 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(2 * z * (1 - z) * Spaces.Gam α θ / (Spaces.c α * (1 + z) ^ 3)) * L12f f z

/-- The `3z(1+z)^{-2} D_θ f` term. -/
def Z5 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => 3 * z / (1 + z) ^ 2 * Spaces.Dth f z θ

/-- The `-3(1+z)^{-1} D_θ(D_z f)` transport term. -/
def Z6 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(3 / (1 + z)) * Spaces.Dth (Spaces.Dz f) z θ

/-- The projector-derivative term `(Γ/c)·L₁₂(Transport f)(0)·2z²(2-z)/(1+z)^4`. -/
def Z7 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (Spaces.Gam α θ / Spaces.c α) * C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)

/-- The pointwise sum of the seven terms of `D_z(𝓛_Γ^T f)`. -/
def SumI (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Z1 f z θ + Z2 f z θ + Z3 α f z θ + Z4 α f z θ + Z5 f z θ + Z6 f z θ
    + Z7 α f z θ

/-- The combined coercive term `Z1 + Z6 = 𝓛(D_z f) - 3(1+z)^{-1} D_θ(D_z f)`. -/
def Z16 (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Z1 f z θ + Z6 f z θ

/-- The sum of the five lower-order terms `Z2 + Z3 + Z4 + Z5 + Z7`. -/
def Zrest (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Z2 f z θ + Z3 α f z θ + Z4 α f z θ + Z5 f z θ + Z7 α f z θ

end Work.Coercivity
