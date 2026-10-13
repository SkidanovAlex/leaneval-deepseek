/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.Data` — the bundle of endpoint data for the box-`C²` chapter

The L3 producer `PkgBoxH` needs, for every box `[a₀,b₀] × [0,π/2]` with `0 < a₀ ≤ b₀`, the
following data on the stream function `Ψ = E g` (`g` of the source class `ClassC α`):

* `ModWith K β`  — the uniform second angular-derivative bound
  `|∂_θ²Ψ| ≤ K·Xn6 α g · min(θ,π/2−θ)^β`;
* `RatesWith K β` — the eight pointwise derivative bounds on the *open* strip and the six
  endpoint/rate bounds (rates `θ`, `π/2−θ`, `θ^β`, `(π/2−θ)^β` for `∂_zΨ`, `∂_z²Ψ`, `∂_θ²Ψ`);
* `Limits`  — the two one-sided angular limits of `∂_θΨ` and of `∂_z∂_θΨ`, with linear rates,
  continuity in `z` and the identification of the `z`-derivative of the limit function;
* `HolMod`  — the two-point θ-Hölder modulus of `∂_θ²Ψ` on the open strip.

`BoxData α Ce E a₀ b₀` bundles all four.  The point of the bundling is that the three box
clauses (closed-box `C²`, the jet bounds, the Hölder modulus) are proved from `BoxData` alone;
the four components are produced by the sibling modules `th2_rate`, `bounds_rates`, `eg_limits`
and `th2_holder`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The uniform second angular-derivative bound** on the box, with the rate variable
`min θ (π/2 - θ)` and a fixed exponent `β`. -/
def ModWith (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ K β : ℝ) : Prop :=
  ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv (deriv (fun θ' => (E g) z θ')) θ|
        ≤ K * Work.FTS.StrongGlobal.Xn6 α g * (min θ (π / 2 - θ)) ^ β

/-- **The pointwise derivative bounds of `E g`** on the open strip `(a₀,b₀) × (0,π/2)`. -/
def PartBounds (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g

/-- **The endpoint bounds and rates** of the radial derivatives of `E g`.  The first eight
conjuncts are the pointwise bounds (`PartBounds`); the last six are the endpoint rates, with the
exponent `β` of the second angular derivative. -/
def RatesWith (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ β : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz (E g))) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g ∧
      |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ∧
      |Work.Spaces.pz (E g) z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ) ∧
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ) ∧
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ ^ β ∧
      |Work.Spaces.pth (Work.Spaces.pth (E g)) z θ|
        ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ) ^ β

/-- **The angular endpoint limits** of `∂_θ(E g)` and of `∂_z∂_θ(E g)`: existence, linear rates,
continuity in `z`, and the identification of the `z`-derivative. -/
def Limits (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∃ L0 N0 L1 N1 : ℝ → ℝ,
      (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth (E g) z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (L0 z))) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pth (E g) z θ - L0 z| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ) ∧
      (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (N0 z))) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ - N0 z|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * θ) ∧
      (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth (E g) z θ)
        (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (L1 z))) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pth (E g) z θ - L1 z|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ)) ∧
      (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth (E g)) z θ)
        (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (N1 z))) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.pz (Work.Spaces.pth (E g)) z θ - N1 z|
          ≤ C * Work.FTS.StrongGlobal.Xn6 α g * (π / 2 - θ)) ∧
      ContinuousOn L0 (Set.Icc a b) ∧ ContinuousOn N0 (Set.Icc a b) ∧
      ContinuousOn L1 (Set.Icc a b) ∧ ContinuousOn N1 (Set.Icc a b) ∧
      (∀ z ∈ Set.Icc a b, HasDerivWithinAt L0 (N0 z) (Set.Icc a b) z) ∧
      (∀ z ∈ Set.Icc a b, HasDerivWithinAt L1 (N1 z) (Set.Icc a b) z)

/-- **The two-point θ-Hölder modulus** of the second angular derivative on the open strip. -/
def HolMod (α : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
    ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        |deriv (deriv (fun θ'' => (E g) z θ'')) θ
            - deriv (deriv (fun θ'' => (E g) z θ'')) θ'|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ β

/-- **The complete endpoint data** for the box `[a₀,b₀] × [0,π/2]`: the angular rate bound,
the pointwise/endpoint bounds of the radial derivatives, the angular limits and the two-point
Hölder modulus. -/
def BoxData (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) (a₀ b₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ModWith α E a₀ b₀ K β ∧ RatesWith α E a₀ b₀ β ∧
    Limits α E a₀ b₀ ∧ HolMod α E a₀ b₀

/-! ## Projections -/

theorem BoxData.mod {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {a₀ b₀ : ℝ}
    (h : BoxData α Ce E a₀ b₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ModWith α E a₀ b₀ K β := by
  obtain ⟨K, hK, β, hβ, h1, -⟩ := h
  exact ⟨K, hK, β, hβ, h1⟩

theorem BoxData.bounds {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {a₀ b₀ : ℝ}
    (h : BoxData α Ce E a₀ b₀) : PartBounds α E a₀ b₀ := by
  obtain ⟨K, hK, β, hβ, -, h2, -⟩ := h
  obtain ⟨C, hC, hCb⟩ := h2
  exact ⟨C, hC, fun g hg => by
    intro z hz θ hθ
    obtain ⟨h1, h2', h3, h4, h5, h6, h7, h8, -⟩ := hCb g hg z hz θ hθ
    exact ⟨h1, h2', h3, h4, h5, h6, h7, h8⟩⟩

theorem BoxData.rates {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {a₀ b₀ : ℝ}
    (h : BoxData α Ce E a₀ b₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ RatesWith α E a₀ b₀ β := by
  obtain ⟨K, hK, β, hβ, -, h2, -⟩ := h
  exact ⟨K, hK, β, hβ, h2⟩

theorem BoxData.limits {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {a₀ b₀ : ℝ}
    (h : BoxData α Ce E a₀ b₀) : Limits α E a₀ b₀ := by
  obtain ⟨K, hK, β, hβ, -, -, h3, -⟩ := h
  exact h3

theorem BoxData.hol {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {a₀ b₀ : ℝ}
    (h : BoxData α Ce E a₀ b₀) : HolMod α E a₀ b₀ := by
  obtain ⟨K, hK, β, hβ, -, -, -, h4⟩ := h
  exact h4

end Work.FTS_EllLimOK.ProducerH.H2
