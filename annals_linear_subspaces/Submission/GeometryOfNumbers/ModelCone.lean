import Mathlib
import Submission.GeometryOfNumbers.WedgeGeneralE1
import Submission.GeometryOfNumbers.WedgeBlockZero
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.Bridge.Challenge
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

/-!
# Model Proposition 1, part 2 (distance bound under the cone condition) — coordinate model

Model: `0 < k ≤ ℓ ≤ d`, `x₀ = modelX ℓ`, `u : Fin k → ℝᵈ` independent (so
`V = span(range u)` is a `k`-plane), and `w = ιMulti u ∈ ⋀^k ℝᵈ`.  For the two-scale flow
`f = scaleMap (twoScale a b ℓ)` (`a` on the first `ℓ` coordinates, `b` on the rest;
`a = exp(-t/ℓ)`, `b = exp(t/(d-ℓ))` in the application), the cone condition
`c · ‖fₖ w‖ ≤ ‖block₀(fₖ w)‖` (block-0 stays dominant along the flow) forces the distance
estimate
    `distSubspaces V x₀ ≤ a / (c · b)`
(i.e. `≤ C · exp(-t(1/ℓ + 1/(d-ℓ)))` when `a = exp(-t/ℓ)`, `b = exp(t/(d-ℓ))`).

Assembly:
* the flow `f` is invertible (twoScale coefficients `a,b ≠ 0`), so `fₖ w = 0 ⇒ w = 0`;
  together with `w = ιMulti u ≠ 0` (from `u` independent, commons
  `iMulti_ne_zero_of_linearIndependent`) and the block eigenspace identity
  `block₀(fₖ w) = a^k • block₀ w` (`blockElem_map_scaleMap_twoScale`), the cone condition
  gives `block₀ w ≠ 0` (`hb0`);
* then `block₀ w ≠ 0` gives `V ∩ x₀ᗮ = ⊥` (`inj_modelX_of_block0_ne_zero`), so the general
  E1(b) (`planeResidual_pureTensor_le_blockRatio`) applies: `δ(V,x₀) ≤ ‖block₁ w‖/‖block₀ w‖`;
* `blockRatio_le_of_cone` turns the cone condition into `‖block₁ w‖/‖block₀ w‖ ≤ a/(c·b)`;
* the distance bridge (`Submission.Bridge.distSubspaces_le_planeResidual_of_le`, using
  `finrank V = k ≤ ℓ = finrank x₀`, `V ≠ ⊥`, `x₀ ≠ ⊥`) converts `δ ≤ a/(c·b)` into the
  challenge-distance statement.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real LinearSubspaces
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.WedgeGeneralE1
open Submission.WedgeBlockZero

namespace Submission.ModelCone

variable {d k : ℕ}

/-- The two-scale diagonal map is invertible when both scales are nonzero (a left inverse is
given by the diagonal map with reciprocal coefficients). -/
lemma scaleMap_twoScale_comp_inv (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (scaleMap (fun i : Fin d => (twoScale a b ℓ i)⁻¹)) ∘ₗ (scaleMap (twoScale a b ℓ)) =
      LinearMap.id := by
  classical
  let s₂ : Fin d → ℝ := twoScale a b ℓ
  let s₁ : Fin d → ℝ := fun i => (s₂ i)⁻¹
  have h1 : ∀ i : Fin d, s₁ i * s₂ i = 1 := by
    intro i
    dsimp [s₁, s₂]
    by_cases hi : i.val < ℓ
    · rw [twoScale_apply, if_pos hi]
      exact inv_mul_cancel₀ ha
    · rw [twoScale_apply, if_neg hi]
      exact inv_mul_cancel₀ hb
  apply LinearMap.ext
  intro x
  apply rd_ext
  intro i
  calc
    ((scaleMap s₁ ∘ₗ scaleMap s₂) x) i = (scaleMap s₁ (scaleMap s₂ x)) i := rfl
    _ = s₁ i * (scaleMap s₂ x) i := by rw [scaleMap_apply]
    _ = s₁ i * (s₂ i * x i) := by rw [scaleMap_apply]
    _ = (s₁ i * s₂ i) * x i := by rw [← mul_assoc]
    _ = x i := by rw [h1 i, one_mul]

/-- The induced map on the exterior power is injective when both scales are nonzero. -/
lemma map_twoScale_injective (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (fun w : WK d k =>
      exteriorPower.map k (scaleMap (twoScale a b ℓ)) w) := by
  classical
  let g : RD d →ₗ[ℝ] RD d := scaleMap (fun i : Fin d => (twoScale a b ℓ i)⁻¹)
  let f : RD d →ₗ[ℝ] RD d := scaleMap (twoScale a b ℓ)
  have hg : g ∘ₗ f = LinearMap.id := by
    dsimp [g, f]
    exact scaleMap_twoScale_comp_inv (d := d) a b ℓ ha hb
  have hcomp : exteriorPower.map k g ∘ₗ exteriorPower.map k f = LinearMap.id := by
    rw [← exteriorPower.map_comp (f := f) (g := g)]
    rw [hg]
    rw [exteriorPower.map_id]
  have hleft : Function.LeftInverse (exteriorPower.map k g) (exteriorPower.map k f) := by
    intro x
    have := congrArg (fun φ : WK d k →ₗ[ℝ] WK d k => φ x) hcomp
    simpa using this
  exact hleft.injective

/-- **Model Prop 1, part 2**: cone condition ⇒ distance bound `dist(V,x₀) ≤ a/(c·b)`. -/
theorem model_prop1_part2 (ℓ : ℕ) (hk : 0 < k) (hkℓ : k ≤ ℓ) (hℓpos : 0 < ℓ) (hℓd : ℓ ≤ d)
    (u : Fin k → RD d) (hu : LinearIndependent ℝ u) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcone : c * ‖exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k u)‖ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ k u)) 0‖) :
    LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range u)) (modelX (d := d) ℓ) ≤
      a / (c * b) := by
  classical
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let f : RD d →ₗ[ℝ] RD d := scaleMap (twoScale a b ℓ)
  let aw : WK d k := exteriorPower.map k f w
  have hcone_w : c * ‖exteriorPower.map k f w‖ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.map k f w) 0‖ := by
    simpa [w, f] using hcone
  -- w ≠ 0 (pure wedge of an independent family)
  have hwne : w ≠ 0 := by
    dsimp [w]
    exact Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent u hu
  -- flow is injective
  have hinj : Function.Injective (exteriorPower.map k f) := by
    dsimp [f]
    exact map_twoScale_injective a b ℓ ha.ne' hb.ne'
  -- cone condition forces block₀ w ≠ 0
  have hb0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ≠ 0 := by
    intro hz0
    have hb0flow : ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ = 0 := by
      dsimp [aw, f]
      rw [norm_blockElem_map_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b) w
        (by omega : 0 ≤ k) (le_of_lt ha) (le_of_lt hb)]
      simp [hz0]
    have hle0 : c * ‖aw‖ ≤ 0 := by
      calc
        c * ‖aw‖ ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ := by simpa [aw] using hcone_w
        _ = 0 := hb0flow
    have hn0 : ‖aw‖ = 0 :=
      (mul_eq_zero.mp (le_antisymm hle0 (mul_nonneg (le_of_lt hc) (norm_nonneg _)))).resolve_left hc.ne'
    have haw0 : aw = 0 := norm_eq_zero.mp hn0
    have hw0 : w = 0 := by
      dsimp [aw] at haw0
      exact hinj (by simpa [f] using haw0)
    exact hwne hw0
  have hw0v : blockElem (d := d) (k := k) (ℓ := ℓ) w 0 ≠ 0 := by
    intro hz
    exact hb0 (by simp [hz])
  -- block₀ ≠ 0 ⇒ V ∩ x₀ᗮ = ⊥
  have hbot : (Submodule.span ℝ (Set.range u)) ⊓ (modelX (d := d) ℓ)ᗮ = ⊥ := by
    exact inj_modelX_of_block0_ne_zero (d := d) ℓ u hu (by simpa [w] using hw0v)
  -- E1(b) general: δ ≤ ratio
  have hdelta :
      Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
        (modelX (d := d) ℓ) ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
    dsimp [w]
    exact planeResidual_pureTensor_le_blockRatio (d := d) (k := k) ℓ hk u hu hbot
  -- cone ⇒ ratio ≤ a/(c·b)
  have hratio :
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ≤ a / (c * b) := by
    dsimp [w, aw] at hb0 hcone_w
    exact blockRatio_le_of_cone (d := d) (k := k) ℓ hk a b c ha hb hc w hb0 hcone_w
  -- finrank data
  have hkl' : Module.finrank ℝ (Submodule.span ℝ (Set.range u)) ≤
      Module.finrank ℝ (modelX (d := d) ℓ) := by
    rw [PlaneFinrank.finrank_span_range (d := d) u hu]
    rw [PlaneFinrank.finrank_modelX (d := d) ℓ hℓd]
    exact hkℓ
  have hvn : Submodule.span ℝ (Set.range u) ≠ ⊥ :=
    PlaneFinrank.span_range_ne_bot (d := d) hk u hu
  have hxn : modelX (d := d) ℓ ≠ ⊥ :=
    PlaneFinrank.modelX_ne_bot (d := d) ℓ hℓpos hℓd
  -- distance bridge: distSubspaces ≤ planeResidual
  have hbrid : LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range u))
      (modelX (d := d) ℓ) ≤
      Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
        (modelX (d := d) ℓ) := by
    exact Submission.Bridge.distSubspaces_le_planeResidual_of_le
      (Submodule.span ℝ (Set.range u)) (modelX (d := d) ℓ) hkl' hvn hxn
  calc
    LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range u)) (modelX (d := d) ℓ)
        ≤ Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
            (modelX (d := d) ℓ) := hbrid
    _ ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ /
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := hdelta
    _ ≤ a / (c * b) := hratio

end Submission.ModelCone
