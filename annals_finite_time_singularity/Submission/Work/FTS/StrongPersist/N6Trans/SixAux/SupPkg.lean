import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise sup-bound package for the level-6 `T2` slot

The `f`- and `g`-side pointwise bounds consumed by the per-term case analysis of
`Work.FTS.StrongPersist.N6Trans.SixAux.term_bound`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The pointwise data on `(f, g)` with a common bound `K` used by the per-term bound. -/
structure SupPkg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg : ℝ) : Prop where
  /-- pure `D_z`-derivatives of `f` of order `≤ 4`. -/
  fpure : ∀ b : ℕ, b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.DzIter b f z θ| ≤ Kf
  /-- pure `D_z`-derivatives of `g` of order `≤ 4`. -/
  gpure : ∀ b : ℕ, b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.DzIter b g z θ| ≤ Kg
  /-- mixed derivatives of `f` of order `≤ 4` with at least one angular derivative. -/
  fmix : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.mixed j i f z θ| ≤ Kf
  /-- mixed derivatives of `g` of order `≤ 4` with at least one angular derivative. -/
  gmix : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.mixed j i g z θ| ≤ Kg
  /-- the plain angular derivative of `f` (the `σ`-gain of `D_θ f = sin(2·)·∂_θ f`). -/
  pthf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth f z θ| ≤ Kf

theorem SupPkg.fval {α Kf Kg : ℝ} {f g : ℝ → ℝ → ℝ} (h : SupPkg α f g Kf Kg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |f z θ| ≤ Kf :=
  fun z θ hz hθ hθ2 => h.fpure 0 (by norm_num) z θ hz hθ hθ2

theorem SupPkg.gval {α Kf Kg : ℝ} {f g : ℝ → ℝ → ℝ} (h : SupPkg α f g Kf Kg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |g z θ| ≤ Kg :=
  fun z θ hz hθ hθ2 => h.gpure 0 (by norm_num) z θ hz hθ hθ2

theorem SupPkg.fdz {α Kf Kg : ℝ} {f g : ℝ → ℝ → ℝ} (h : SupPkg α f g Kf Kg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dz f z θ| ≤ Kf := by
  intro z θ hz hθ hθ2
  have := h.fpure 1 (by norm_num) z θ hz hθ hθ2
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using this

end Work.FTS.StrongPersist.N6Trans.SixAux
