/-
# The commutator `[D_θ, 𝓛_Γ^T]`: shared vocabulary

This module fixes the objects used by the proof of `Work.Coercivity.CommutTheta_holds`,
which is the paper's estimate `|E₁|_{ℋ^{k-1}} ≤ C̄_k |f|_{ℋ^{k-1}}` for the commutator
defect

  `E₁ = D_θ 𝓛_Γ^T f - 𝓛_Γ^T (D_θ f)`

of Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (3) 2021, §"Higher order
derivatives and the inner product on `ℋ^k`" (tex 680--693).

Since `D_θ` commutes with everything in `𝓛_Γ^T` except the `Γ(θ)`-dependence and the
angular transport term (which cancels), the defect splits as

  `E₁(z,θ) = Γ(θ) · F₁(z) + D_θΓ(θ) · F₂(z)`

with the two *radial* factors

  `F₁ = (2z/(c(1+z)²))·L₁₂(D_θ f) - (2z²/(c(1+z)³))·L₁₂(Transport(D_θ f))(0)`,
  `F₂ = (2z²/(c(1+z)³))·L₁₂(Transport f)(0) - (2z/(c(1+z)²))·L₁₂(f)`.

Writing `E₁` this way separates the `θ`-dependence (entirely through `Γ` and `D_θΓ`) from
the `z`-dependence, which is what makes the `ℋ^n`-estimate a sum of products of an angular
integral and a radial integral.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
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

namespace CT

set_option autoImplicit false

/-! ## Lifting angular and radial functions to the quadrant -/

/-- A function of the angle alone, viewed as a function of `(z,θ)`. -/
def ang (g : ℝ → ℝ) : ℝ → ℝ → ℝ := fun _ θ => g θ

/-- A function of `z` alone, viewed as a function of `(z,θ)`. -/
def rad (R : ℝ → ℝ) : ℝ → ℝ → ℝ := fun z _ => R z

theorem ang_apply (g : ℝ → ℝ) (z θ : ℝ) : ang g z θ = g θ := rfl
theorem rad_apply (R : ℝ → ℝ) (z θ : ℝ) : rad R z θ = R z := rfl

/-! ## `D_z` on radial functions -/

/-- `D_z = z ∂_z` acting on functions of `z` alone. -/
def DzR (R : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv R z

/-- Iterated `D_z` on functions of `z` alone. -/
def DzRIter : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, R => R
  | n + 1, R => DzR (DzRIter n R)

@[simp] theorem DzRIter_zero (R : ℝ → ℝ) : DzRIter 0 R = R := rfl
@[simp] theorem DzRIter_succ (n : ℕ) (R : ℝ → ℝ) :
    DzRIter (n + 1) R = DzR (DzRIter n R) := rfl

/-- Iterated `D_θ = sin(2θ) ∂_θ` on functions of the angle alone. -/
def DthIterAng : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, g => g
  | n + 1, g => fun θ => Real.sin (2 * θ) * deriv (DthIterAng n g) θ

@[simp] theorem DthIterAng_zero (g : ℝ → ℝ) : DthIterAng 0 g = g := rfl
theorem DthIterAng_succ (n : ℕ) (g : ℝ → ℝ) :
    DthIterAng (n + 1) g = fun θ => Real.sin (2 * θ) * deriv (DthIterAng n g) θ := rfl

/-! ## The angular data as functions of `(z,θ)` -/

/-- `Γ(θ)` as a function of `(z,θ)`. -/
def GamF (α : ℝ) : ℝ → ℝ → ℝ := ang (Spaces.Gam α)

/-- `D_θΓ` as a function of `(z,θ)` (radially constant). -/
def DthGamF (α : ℝ) : ℝ → ℝ → ℝ := Spaces.Dth (GamF α)

theorem GamF_apply (α z θ : ℝ) : GamF α z θ = Spaces.Gam α θ := rfl

theorem DthGamF_apply (α z θ : ℝ) :
    DthGamF α z θ = Real.sin (2 * θ) * deriv (Spaces.Gam α) θ := rfl

/-! ## The radial factors of the commutator defect -/

/-- `L₁₂(D_θ f)`. -/
def A1 (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => L12f (Spaces.Dth f) z

/-- `L₁₂(f)`. -/
def A2 (f : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => L12f f z

/-- The constant `L₁₂(Transport f)(0)` of the projector term. -/
def KC0 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport f) 0

/-- The constant `L₁₂(Transport(D_θ f))(0)`. -/
def KC1 (f : ℝ → ℝ → ℝ) : ℝ := L12f (Transport (Spaces.Dth f)) 0

/-- The radial factor multiplying `Γ(θ)` in the commutator defect. -/
def F1 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (2 * z / (Spaces.c α * (1 + z) ^ 2)) * A1 f z
    - (2 * z ^ 2 / (Spaces.c α * (1 + z) ^ 3)) * KC1 f

/-- The radial factor multiplying `D_θΓ(θ)` in the commutator defect. -/
def F2 (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (2 * z ^ 2 / (Spaces.c α * (1 + z) ^ 3)) * KC0 f
    - (2 * z / (Spaces.c α * (1 + z) ^ 2)) * A2 f z

/-- The coefficient `2z/(c(1+z)²)` of `L₁₂`. -/
def pcoef (α : ℝ) : ℝ → ℝ := fun z => 2 * z / (Spaces.c α * (1 + z) ^ 2)

/-- The coefficient `2z²/(c(1+z)³)` of the projector term. -/
def Wcoef (α : ℝ) : ℝ → ℝ := fun z => 2 * z ^ 2 / (Spaces.c α * (1 + z) ^ 3)

/-- **The commutator defect of `D_θ` and `𝓛_Γ^T`.** -/
def EcommT (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.Dth (LGammaT α f) z θ - LGammaT α (Spaces.Dth f) z θ

/-! ## The weighted energies and angular integrals occurring in the estimate -/

/-- `∫∫ g² w² sin(2θ)^{-γ}` with `γ = gam α`: the `L²` energy of `g` with the weight of
the mixed derivatives of the `ℋ`-norm. -/
def Ewgam (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
    (g z θ) ^ 2 * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-- `∫∫ g² w² sin(2θ)^{-η}`: the `L²` energy of `g` with the weight of the pure `D_z`
derivatives of the `ℋ`-norm. -/
def Eweta (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
    (g z θ) ^ 2 * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)

/-- The angular integral `∫_θ (D_θ^iΓ)² sin(2θ)^{-γ}`. -/
def AngGam (α : ℝ) (i : ℕ) : ℝ :=
  ∫ θ in Spaces.Iθ,
    (DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-- The angular integral `∫_θ (D_θ^iΓ)² sin(2θ)^{-η}`. -/
def AngEta (α : ℝ) (i : ℕ) : ℝ :=
  ∫ θ in Spaces.Iθ,
    (DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)

end CT

end Work.Coercivity

namespace Work.Coercivity

namespace CT

set_option autoImplicit false

/-- The pointwise majorant of `HkIntegrand α n (EcommT α f)` obtained by splitting each
`D_z^j D_θ^i` of `EcommT α f = Γ·F₁ + D_θΓ·F₂` by the product rule and using
`(a+b)² ≤ 2a² + 2b²`.  In the pure-`D_z` sum the angular factors are `Γ` and `D_θΓ`
(independent of the radial order), while in the mixed sum they are `D_θ^iΓ` and
`D_θ^{i+1}Γ`. -/
def Bound (α : ℝ) (n : ℕ) (F₁ F₂ : ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1),
      2 * ((DthIterAng 0 (Spaces.Gam α) θ) ^ 2 * (DzRIter i F₁ z) ^ 2
          + (DthIterAng 1 (Spaces.Gam α) θ) ^ 2 * (DzRIter i F₂ z) ^ 2)
        * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
  + ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      if 1 ≤ i ∧ i + j ≤ n then
        2 * ((DthIterAng i (Spaces.Gam α) θ) ^ 2 * (DzRIter j F₁ z) ^ 2
          + (DthIterAng (i + 1) (Spaces.Gam α) θ) ^ 2 * (DzRIter j F₂ z) ^ 2)
        * (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      else 0

/-- The `θ`-integral of `Bound`, with the angular integrals `AngEta`/`AngGam` evaluated. -/
def BoundInt (α : ℝ) (n : ℕ) (F₁ F₂ : ℝ → ℝ) (z : ℝ) : ℝ :=
  2 * (∑ i ∈ Finset.range (n + 1),
        (AngEta α 0 * (DzRIter i F₁ z) ^ 2 + AngEta α 1 * (DzRIter i F₂ z) ^ 2)
          * (Spaces.w z) ^ 2)
  + 2 * (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      if 1 ≤ i ∧ i + j ≤ n then
        (AngGam α i * (DzRIter j F₁ z) ^ 2 + AngGam α (i + 1) * (DzRIter j F₂ z) ^ 2)
          * (Spaces.w z) ^ 2
      else 0)

end CT

end Work.Coercivity
