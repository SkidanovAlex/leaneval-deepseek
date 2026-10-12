import ChallengeDeps
import Submission.BoxEnergy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 seed: passing to the thermodynamic limit.

If the box-energy densities converge along the joint filter, then `e ρ v` is their
limit; nonnegativity and order pass to the limit.  These are the filter facts used
by every thermodynamic-limit argument.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A nonnegative function that converges has a nonnegative limit. -/
lemma tendsto_nonneg_of_eventually {α : Type*} {f : α → ℝ} {F : Filter α} {x : ℝ}
    [hF : F.NeBot] (hf : ∀ᶠ a in F, 0 ≤ f a) (hx : Tendsto f F (𝓝 x)) : 0 ≤ x := by
  exact ge_of_tendsto hx hf

/-- If the box energy densities tend to a limit, then the energy density is nonnegative
for `0 ≤ v`. -/
lemma e_nonneg_of_tendsto {ρ : ℝ} {v : ℝ³ → ℝ} (hρ : 0 < ρ) (hv : 0 ≤ v) {x : ℝ}
    (hx : Tendsto (fun (p : ℝ × ℕ) => p.1 ^ (-3 : ℤ) * boxEnergy p.2 p.1 v)
      (jointFilter ρ) (𝓝 x)) : 0 ≤ e ρ v := by
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  haveI : (jointFilter ρ).NeBot := jointFilter_neBot hρ0
  have hpos : ∀ᶠ (p : ℝ × ℕ) in jointFilter ρ,
      0 ≤ p.1 ^ (-3 : ℤ) * boxEnergy p.2 p.1 v := by
    filter_upwards [eventually_pos_L ρ hρ0] with p hp
    have hLne : p.1 ≠ 0 := ne_of_gt hp
    have hzpow : 0 ≤ p.1 ^ (-3 : ℤ) := by
      rw [zpow_neg]
      exact inv_nonneg.mpr (pow_nonneg hp.le 3)
    exact mul_nonneg hzpow (boxEnergy_nonneg hp hv)
  have hx0 : 0 ≤ x := tendsto_nonneg_of_eventually (F := jointFilter ρ) hpos hx
  have heq : e ρ v = x := e_eq_tendsto_boxEnergy hρ0 hx
  rw [heq]
  exact hx0

/-- `e ρ v` is bounded below by the limit of any eventual lower bound of the box densities. -/
lemma e_ge_of_tendsto_of_eventually_ge {ρ : ℝ} {v : ℝ³ → ℝ} {x B : ℝ} (hρ : 0 ≤ ρ)
    (hx : Tendsto (fun (p : ℝ × ℕ) => p.1 ^ (-3 : ℤ) * boxEnergy p.2 p.1 v)
      (jointFilter ρ) (𝓝 x))
    (hg : ∀ᶠ (p : ℝ × ℕ) in jointFilter ρ, B ≤ p.1 ^ (-3 : ℤ) * boxEnergy p.2 p.1 v) :
    B ≤ e ρ v := by
  haveI : (jointFilter ρ).NeBot := jointFilter_neBot hρ
  have hBx : B ≤ x := ge_of_tendsto hx hg
  have heq : e ρ v = x := e_eq_tendsto_boxEnergy hρ hx
  simpa [heq] using hBx

end BoseGases

end Submission

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Density-dependent lower bounds and the eventual assembly

For the proof of `theorem_1_2` one proves a *box lower bound* of the shape
`φ(N/L³) ≤ L⁻³ boxEnergy N L v` for every admissible box, where `φ` is the
right-hand side of the Lee--Huang--Yang formula read as a function of the
density.  Combined with the existence of the thermodynamic limit (convergence
of the box densities along the joint filter) this lifts to the pointwise bound
`φ ρ ≤ e ρ v` for every small `ρ`.  The two lemmas below are exactly that
lifting.
-/

/-- The canonical box energy density (per unit volume) at `(L,N)`. -/
noncomputable def boxDensity (v : ℝ³ → ℝ) (p : ℝ × ℕ) : ℝ :=
  p.1 ^ (-3 : ℤ) * boxEnergy p.2 p.1 v

/-- Along the joint filter the density coordinate `N / L³` tends to `ρ`. -/
lemma density_tendsto (ρ : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.2 : ℝ) / p.1 ^ 3) (jointFilter ρ) (𝓝 ρ) := by
  simpa using tendsto_density ρ

/-- Lifting an eventual lower bound `φ(N/L³) ≤ box density` to the limit: if the box
densities converge to `x` along the joint filter and `φ` is continuous at `ρ`, then
`φ ρ ≤ x`, hence `φ ρ ≤ e ρ v`. -/
lemma e_ge_of_tendsto_of_eventually_density_ge {ρ : ℝ} {v : ℝ³ → ℝ} {x : ℝ} {φ : ℝ → ℝ}
    (hρ : 0 ≤ ρ) (hφ : ContinuousAt φ ρ)
    (hx : Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x))
    (hg : ∀ᶠ p in jointFilter ρ, φ ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p) :
    φ ρ ≤ e ρ v := by
  haveI : (jointFilter ρ).NeBot := jointFilter_neBot hρ
  have hφρ : Tendsto (fun p : ℝ × ℕ => φ ((p.2 : ℝ) / p.1 ^ 3)) (jointFilter ρ) (𝓝 (φ ρ)) :=
    hφ.tendsto.comp (density_tendsto ρ)
  have hsub : Tendsto (fun p : ℝ × ℕ => boxDensity v p - φ ((p.2 : ℝ) / p.1 ^ 3))
      (jointFilter ρ) (𝓝 (x - φ ρ)) := hx.sub hφρ
  have h0 : ∀ᶠ p in jointFilter ρ, 0 ≤ boxDensity v p - φ ((p.2 : ℝ) / p.1 ^ 3) := by
    filter_upwards [hg] with p hp
    linarith
  have hxφ : 0 ≤ x - φ ρ := ge_of_tendsto hsub h0
  have hφx : φ ρ ≤ x := by linarith
  exact hφx.trans_eq (e_eq_tendsto_boxEnergy hρ hx).symm

/-- The eventual assembly: if (a) `φ` is continuous at every small density,
(b) the box densities converge along the joint filter at every small density, and
(c) the box-energy lower bound `φ(N/L³) ≤ box density` holds eventually at every
small density, then `φ ρ ≤ e ρ v` eventually for small `ρ`. -/
lemma e_ge_of_eventually_box_ge {v : ℝ³ → ℝ} {φ : ℝ → ℝ}
    (hφ : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ContinuousAt φ ρ)
    (hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x, Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x))
    (hbox : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      ∀ᶠ p in jointFilter ρ, φ ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), φ ρ ≤ e ρ v := by
  filter_upwards [self_mem_nhdsWithin, hφ, hconv, hbox] with ρ hρpos hφρ hconvρ hboxρ
  rcases hconvρ with ⟨x, hx⟩
  exact e_ge_of_tendsto_of_eventually_density_ge (le_of_lt hρpos) hφρ hx hboxρ

end BoseGases

end Submission
