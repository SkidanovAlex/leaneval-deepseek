import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.Lzero_self_form
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- **The truncated radial weight** `W_R z = chi (z/R) · (w z)²`, where `w z = (1+z)²/z²` and
`chi` is the smooth cut-off of `Work.Stability` (`chi = 1` on `[-1,1]`, `chi = 0` off `(-2,2)`).
For `R ≥ 1` this weight equals `w²` on `[0,R]` and vanishes on `[2R,∞)`, and it tends pointwise to
`w²` as `R → ∞`; multiplying the elliptic equation by `Φ · W_R` is the truncation used to justify
the radial integration by parts of the energy inequality. -/
def cutW (R : ℝ) (z : ℝ) : ℝ := Work.Stability.chi (z / R) * (Work.Spaces.w z) ^ 2

/-- The angular `L²`-mass `z ↦ ∫_θ Φ(z,θ)² dθ` of `Φ`. -/
def thSq (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Φ z θ) ^ 2

/-- The angular cross term `z ↦ 2 ∫_θ Φ(z,θ) ∂_zΦ(z,θ) dθ`, i.e. the derivative of `thSq`. -/
def thCross (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => 2 * ∫ θ in Work.Spaces.Iθ, Φ z θ * Work.Spaces.pz Φ z θ

/-- The angular `L²`-mass of `∂_zΦ`: `z ↦ ∫_θ (∂_zΦ(z,θ))² dθ`. -/
def thRad (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Φ z θ) ^ 2

/-- The angular "second derivative" term `z ↦ ∫_θ ∂_z²Φ(z,θ) · Φ(z,θ) dθ`. -/
def thZZ (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Φ z θ * Φ z θ

/-- The angular quadratic form `∫_θ (∂_θΦ)² + (1/2) ∫_θ (Φ/cos θ)²` of `Lzero_self_form`. -/
def thAng (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth Φ z θ) ^ 2)
    + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (Φ z θ / Real.cos θ) ^ 2)

/-- **The angular integration by parts on the slices of `Φ`**, i.e. `Work.FTS.EllipticEst.Lzero_self_form`
applied to the `θ`-slices of a function smooth on a neighbourhood of the closed quadrant and
vanishing on the two boundary lines `θ = 0`, `θ = π/2`. -/
theorem Lzero_slice_of_smooth (Φ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Φ)
    (hDir0 : ∀ z : ℝ, Φ z 0 = 0) (hDirπ : ∀ z : ℝ, Φ z (π / 2) = 0) :
    ∀ z ∈ Set.Ioi (-1 : ℝ),
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero Φ z θ * Φ z θ) = thAng Φ z - 6 * thSq Φ z := by
  intro z hz
  have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Icc 0 (π / 2))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
    intro θ hθ
    exact ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hslice : ContDiffOn ℝ 2 (fun θ => Φ z θ) (Set.Icc 0 (π / 2)) := by
    have h1 : ContDiffOn ℝ ⊤ (fun θ => Φ z θ) (Set.Icc 0 (π / 2)) := by
      have hc := hsm.comp (contDiffOn_const.prodMk contDiffOn_id) hmaps
      simpa [Function.uncurry, Function.comp_def] using hc
    exact h1.of_le (by norm_num)
  have h := Lzero_self_form Φ z hslice (hDir0 z) (hDirπ z)
  simp only [thAng, thSq, Work.Spaces.pth]
  exact h

/-- **The truncated energy identity** at scale `R`: the elliptic equation `bslOp α Φ = G` of the
open quadrant, paired with the truncated test weight `cutW R = chi (·/R) · w²` and integrated by
parts in `z` and in `θ`.  The right-hand side carries the three pieces produced by the two
integrations by parts: the non-negative radial term, the angular pairing of `Lzero Φ` with `Φ`, and
the two weight-derivative terms. -/
def TruncIdentity (α : ℝ) (G Φ : ℝ → ℝ → ℝ) (R : ℝ) : Prop :=
  (∫ z in Work.Spaces.Iz, cutW R z * (∫ θ in Work.Spaces.Iθ, G z θ * Φ z θ))
    = α ^ 2 * (∫ z in Work.Spaces.Iz, z ^ 2 * cutW R z
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Φ z θ) ^ 2))
      + (∫ z in Work.Spaces.Iz, cutW R z
          * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero Φ z θ * Φ z θ))
      - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => z ^ 2 * cutW R z)) z
            * (∫ θ in Work.Spaces.Iθ, (Φ z θ) ^ 2))
      + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
          deriv (fun z => z * cutW R z) z * (∫ θ in Work.Spaces.Iθ, (Φ z θ) ^ 2))

end Work.FTS.EllipticEst
