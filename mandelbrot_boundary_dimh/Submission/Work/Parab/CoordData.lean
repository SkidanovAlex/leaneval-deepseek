import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.LeftData

/-!
# The `φ`-side data of §4.1 (the maximal domain of the Ecalle coordinate)

`CoordData f D₀` bundles the interface's `(ξ₀, φ, Dφ)` together with the maximality structure of
Shishikura's A.3:

`Dφ = {w | ∃ n ≥ 0, w - n ∈ Q₀ and f₀^j(φ₀(w - n)) ∈ D₀ for j < n}`,  `φ w = f₀^n(φ₀(w-n))`,

where `φ₀ = τ₀ ∘ Φ_{-,0}^{-1}` is the seed on `QLeft ξ₀ ⊆ Φ_{-,0}(L)` (`Work.Parab.LeftCoordData`).

For `D₀` **bounded** the maximal domain is a proper subset of `ℂ`; for `D₀ = ℂ` (or `univ`) the
maximality `succ_iff` forces `Dφ = ℂ` and `φ` entire (Shishikura: `Dom φ₀ = ℂ` for entire `f₀`) —
that case is NOT covered by this structure (see NOTES_PARAB0_findings.md §A.3/§D).
-/

namespace Work.Parab

open Complex Set Metric Filter
open scoped Topology

noncomputable section

/-- The `φ`-side data of §4.1 on its maximal domain. -/
structure CoordData (f : ℂ → ℂ) (D₀ : Set ℂ) where
  ξ₀ : ℝ
  φ : ℂ → ℂ
  Dφ : Set ℂ
  η₀ : ℝ
  ξ₀_pos : 0 < ξ₀
  Dφ_open : IsOpen Dφ
  Q_sub : MandelDim.QLeft ξ₀ ⊆ Dφ
  exhaust : ∀ w ∈ Dφ, ∃ n : ℕ, w - (n : ℂ) ∈ MandelDim.QLeft ξ₀
  left_inv : ∀ w ∈ Dφ, w - 1 ∈ Dφ
  succ_iff : ∀ w ∈ Dφ, (w + 1 ∈ Dφ ↔ φ w ∈ D₀)
  φ_holo : DifferentiableOn ℂ φ Dφ
  Q_maps : Set.MapsTo φ (MandelDim.QLeft ξ₀) D₀
  φ_abel : ∀ w ∈ Dφ, w + 1 ∈ Dφ → φ (w + 1) = f (φ w)
  φ_inj : Set.InjOn φ (MandelDim.QLeft ξ₀)
  φ_asymp : ∃ a b : ℂ, ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ MandelDim.QLeft ξ₀, R < ‖w‖ →
    ‖MandelDim.tau0 (φ w) - (w + a * Complex.log (-w) + b)‖ < ε
  /-- the quadratic coefficient `h'(0)` of the germ (`f z = z + z² h z`); it is the logarithmic
  coefficient of the Fatou coordinate of the cusp, hence the one appearing in `φ_asymp` -/
  ag : ℂ
  /-- the additive constant of the end asymptotic -/
  bEnd : ℂ
  /-- the asymptotic of `τ₀ ∘ φ` on the two ends `w → ±i∞`, uniformly in `Re w`; the coefficient
  is `1 - ag`, the logarithmic coefficient of `fatouCoord f (1 - ag)` -/
  φ_asymp_ends : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < |w.im| →
    ‖MandelDim.tau0 (φ w) - (w + (1 - ag) * Complex.log (-w) + bEnd)‖ < ε
  /-- a quantitative germ bound whose quadratic coefficient is `ag` (this ties `ag` to `f`) -/
  hbond : ∃ (h : ℂ → ℂ) (r A A' : ℝ), Work.FatouCoord.ParabolicBounds f h ag r A A'
  /-- (first half of Lemma 5.1) elements of the sector whose image under `φ` is very small are
  far out: this is the properness of `φ` near `0` on the sector, and is what makes the preimages
  of an inverse orbit converging to `0` visible to the asymptotic of `φ_asymp`. -/
  preimage_far : ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ∀ u ∈ MandelDim.QLeft ξ₀, ‖φ u‖ < δ → B ≤ ‖u‖
  /-- the repelling piece of the flower covers the cone complementary to the petal's -/
  cover : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ →
    |z.arg| ≤ Real.pi / 2 + Real.pi / 12 →
      ∃ w ∈ MandelDim.QLeft ξ₀, φ w = z
  /-- (4.1.4): the two ends -/
  ends_sub : ∀ w : ℂ, η₀ < |w.im| → w ∈ Dφ ∧ φ w ∈ MandelDim.ParabolicBasin f D₀

/-!
## How the five "extra" fields are meant to be produced

The builder of `CoordData` (see `Work.Parab.coordData.exists_CoordData`) has, in its own scope,
the seed `τ : ℂ → ℂ`, the sector bound `ξ₀`, and the facts `Φ (τ u) = u` (`hspec`),
`τ u ∈ L` and `τ u ≠ 0` (because `0 ∉ L`, as `L = -Esc N (wMap F)` and `0` is not in `Esc`), plus
the asymptotic `‖τ u - (u + a log (-u) + b)‖ < ε` (`hasymp`) and `coord w = τ₀ (wMap^· (τ u))`
along the maximal-domain recursion.  Then

* `ag` is the quadratic coefficient `h'(0)` of the germ (the same number as in any
  `ParabolicBounds f h ag r A A'`); `hbond` records one such bound, so that
  `coordData.parabolicBounds_aeq` can compare it with any other one;
* `bEnd` is the constant in the end asymptotic;
* `φ_asymp_ends`: `τ₀ (φ w) = Φ⁻¹ (w)` on the ends (this is exactly what the maximal-domain
  recursion gives: the witness `u = w - n` of `ends_of_orbit` satisfies `Φ (τ u) = u`, hence
  `wMap^· (τ u) = Φ⁻¹ w`), so the end asymptotic of `τ₀ ∘ φ` is that of `invOn Φ L`, which is
  `Work.Parab.inversion.inverse_asymptotic` applied to `LeftCoordData.Φ_asym`; the coefficient is
  `-a_lc = 1 - ag` because `a_lc = 1 - (2 - a_F) = ag - 1` (`reflected_inverse_germ`);
* `preimage_far`: with `Φ (τ u) = u` and `‖τ₀ x‖ = 1/‖x‖` one has `‖φ u‖ = 1/‖τ u‖` for
  `u ∈ QLeft ξ₀`, and the asymptotic of `τ` gives `‖τ u‖ ≤ ‖u‖ + |a| log‖u‖ + |b| + 1`; hence
  `‖φ u‖ < δ` forces `‖u‖` to be at least `≈ 1/δ - |a| log(1/δ) - |b|`.  Concretely: pick `δ`
  small enough that `‖τ u‖` cannot be `< 1/δ` for `‖u‖ ≤ B` (where `‖τ u‖` is bounded by
  `B + |a| log + |b| + 1`), which gives `B ≤ ‖u‖`.
-/

end
end Work.Parab
