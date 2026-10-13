import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.PhiStar.CoreAux.Fb_EU_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/StrongPersist/SP6/EU6.lean` — the order-six flat bound of the `EU`-star-field

`Work.FTS.PhiStar.EU α Y = -(z/(z+1))·Wone α Y` with
`Wone α Y = 3Y + α(Y/(z+1) + z ∂_zY)`, and `EUz α Y = -Wone α Y`.  This file proves the
order-six flat bound

`FlatW 6 (EU α Y) (C·(α+1)·(K + KY + KD))`

from `SmoothOpen Y`, `FlatW 7 Y K`, `Fb 6 KY Y` and `F0 6 KD (Yblk Y)`, with a constant which
is **linear** in `K + KY + KD`.

## The route

`EU α Y = -(z/(z+1))·EUz α Y` and `FlatW 6` is the pair (`F0 6`, `F0 5 ∘ ∂_θ`) — this is
`flatW6_of_F0`.  So it suffices to prove the strong pair

* `F0 6 (EUR α Y)` — the reassociated field `(z/(z+1))·EUzR α Y`,
* `F0 5 (pth (EUR α Y))`, identified with `F0 5 (EUD α Y)` through the pointwise identity
  `∂_θ(EUR α Y) = EUD α Y` on the open quadrant (the radial factor `z/(1+z)` is `θ`-free and
  `∂_θ(EUzR α Y) = EUzD α Y`, which is the product rule plus
  `∂_θ(D_zY) = D_z(∂_θY)`, i.e. `Fb_zpz.pth_zpz_smoothOpen`).

Both halves are then pure flat calculus (`F0_mul`, `F0_add`, `F0_const_mul`, `F0_congr`) against
the block bounds of `Flat6Defs.atomData` and the coefficient bounds of `Flat6Defs.CoefBundle6s`
(the two radial factors `z/(1+z)`, `(1+z)⁻¹`).  The auxiliary definition `EUzB` is the
*un-negated* body `3Y + α((1+z)⁻¹Y + D_zY)`; both `EUzR α Y = -EUzB α Y` and
`EUzD α Y = -EUzB α (∂_θY)` hold by `rfl`, which makes the negation bookkeeping trivial.

The order-four analogue of this statement is `PhiStar/CoreAux/Fb_EU_bound.lean`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The un-negated `EUz`-body -/

/-- The un-negated body of `EUz`: `EUzB α Y = 3Y + α(Y/(z+1) + D_zY)`.  The two identities
`EUzR α Y = -EUzB α Y` and `EUzD α Y = -EUzB α (∂_θY)` hold definitionally. -/
def EUzB (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ) + α * Work.FTS.PhiStar.Yblk Y z θ

theorem euzR_eq_neg (α : ℝ) (Y : ℝ → ℝ → ℝ) : EUzR α Y = -EUzB α Y := rfl

theorem euzD_eq_neg (α : ℝ) (Y : ℝ → ℝ → ℝ) :
    EUzD α Y = -EUzB α (Work.Spaces.pth Y) := rfl

/-! ## Elementary flat-calculus helpers -/

/-- `∂_θ` of a multiple by a factor depending on `z` alone. -/
theorem pth_zM (g : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => g z * f z θ) = fun z θ => g z * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field (g z)

/-- `Yblk Y = z ∂_zY` is smooth on the open quadrant when `Y` is. -/
theorem sYblk {Y : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.Yblk Y) := h.Dz

/-- Negation preserves smoothness on the open quadrant. -/
theorem smoothOpen_neg_S {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => -f z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ : ℝ => -f z θ)
      = fun p : ℝ × ℝ => -(Function.uncurry f p) := rfl
  rw [h]
  exact hf.neg

/-- Negation preserves the flat class `F0`. -/
theorem F0_neg_S (n : ℕ) {K : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.PhiStar.F0 n K f) :
    Work.FTS.PhiStar.F0 n K (fun z θ => -f z θ) := by
  refine Work.FTS.PhiStar.CoreAux.F0_congr (g := fun z θ => (-1 : ℝ) * f z θ)
    (fun z θ _ _ _ => by ring) ?_
  have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (-1 : ℝ) hf
  simpa using h

/-! ## Smoothness of the two `EUz`-bodies -/

theorem smoothOpen_EUzB (α : ℝ) (Y : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EUzB α Y) := by
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts 3 hsm
  have s2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α
      (Work.FTS.PhiStar.CoreAux.smoothOpen_mul_fts
        Work.FTS.PhiStar.CoreAux.smoothOpen_inv_one_plus_z_fts hsm)
  have s3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α (sYblk hsm)
  exact Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts
    (Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts s1 s2) s3

theorem smoothOpen_EUzR (α : ℝ) (Y : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EUzR α Y) := by
  change Work.FTS.EllipticEst.SmoothOpen (fun z θ => -EUzB α Y z θ)
  exact smoothOpen_neg_S (smoothOpen_EUzB α Y hsm)

theorem smoothOpen_EUzD (α : ℝ) (Y : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EUzD α Y) := by
  change Work.FTS.EllipticEst.SmoothOpen (fun z θ => -EUzB α (Work.Spaces.pth Y) z θ)
  exact smoothOpen_neg_S (smoothOpen_EUzB α (Work.Spaces.pth Y) hsm.pth)

/-! ## The pointwise `θ`-derivative identities -/

/-- `∂_θ(EUzB α Y) = EUzB α (∂_θY)` on the open quadrant. -/
theorem pth_EUzB (α : ℝ) (Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EUzB α Y) z θ = EUzB α (Work.Spaces.pth Y) z θ := by
  intro z θ hz hθ hθ'
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts 3 hsm
  have s2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α
      (Work.FTS.PhiStar.CoreAux.smoothOpen_mul_fts
        Work.FTS.PhiStar.CoreAux.smoothOpen_inv_one_plus_z_fts hsm)
  have s3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α (sYblk hsm)
  have hW1 : Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ) z θ = 3 * Work.Spaces.pth Y z θ :=
    congrFun (congrFun (Work.FTS.PhiStar.CoreAux.pth_const_mul 3 Y) z) θ
  have hW2 : Work.Spaces.pth (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) z θ
      = α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ) := by
    rw [congrFun (congrFun (Work.FTS.PhiStar.CoreAux.pth_const_mul α
      (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ)) z) θ]
    rw [congrFun (congrFun (pth_zM (fun z => (1 + z)⁻¹) Y) z) θ]
  have hW3 : Work.Spaces.pth (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) z θ
      = α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ := by
    rw [congrFun (congrFun (Work.FTS.PhiStar.CoreAux.pth_const_mul α
      (Work.FTS.PhiStar.Yblk Y)) z) θ]
    show α * Work.Spaces.pth (fun z θ => z * Work.Spaces.pz Y z θ) z θ
      = α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ
    rw [Work.FTS.PhiStar.CoreAux.pth_zpz_smoothOpen (f := Y) hsm z θ hz hθ hθ']
    rfl
  have h12 : Work.Spaces.pth (fun z θ : ℝ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)) z θ
      = 3 * Work.Spaces.pth Y z θ + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ) := by
    rw [Work.FTS.PhiStar.CoreAux.pth_add_Q0 s1 s2 z θ hz hθ hθ', hW1, hW2]
  have h123 : Work.Spaces.pth (fun z θ : ℝ =>
      (3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ)) + α * Work.FTS.PhiStar.Yblk Y z θ) z θ
      = (3 * Work.Spaces.pth Y z θ + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ))
        + α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ := by
    rw [Work.FTS.PhiStar.CoreAux.pth_add_Q0
      (Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts s1 s2) s3 z θ hz hθ hθ', h12, hW3]
  exact h123

/-- `∂_θ(EUzR α Y) = EUzD α Y` on the open quadrant. -/
theorem pth_EUzR (α : ℝ) (Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EUzR α Y) z θ = EUzD α Y z θ := by
  intro z θ hz hθ hθ'
  have h1 : Work.Spaces.pth (EUzR α Y) z θ = -(Work.Spaces.pth (EUzB α Y) z θ) := by
    change Work.Spaces.pth (-EUzB α Y) z θ = -(Work.Spaces.pth (EUzB α Y) z θ)
    exact congrFun (congrFun (Work.FTS.EllipticEst.pth_neg (EUzB α Y)) z) θ
  rw [h1, pth_EUzB α Y hsm z θ hz hθ hθ']
  rfl

/-- `∂_θ(EUR α Y) = EUD α Y` on the open quadrant (`z/(1+z)` is `θ`-free). -/
theorem pth_EUR (α : ℝ) (Y : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EUR α Y) z θ = EUD α Y z θ := by
  intro z θ hz hθ hθ'
  have h1 : Work.Spaces.pth (EUR α Y) z θ
      = (z / (1 + z)) * Work.Spaces.pth (EUzR α Y) z θ := by
    change Work.Spaces.pth (fun z θ => (z / (1 + z)) * EUzR α Y z θ) z θ
      = (z / (1 + z)) * Work.Spaces.pth (EUzR α Y) z θ
    exact congrFun (congrFun (pth_zM (fun z => z / (1 + z)) (EUzR α Y)) z) θ
  rw [h1, pth_EUzR α Y hsm z θ hz hθ hθ']
  rfl

/-! ## The `F0`-bounds of the two `EUz`-bodies -/

/-- **`F0 6` of `EUzR`.**  The bound is `3KY + α(2⁶AKY) + αKD`, linear in `KY`, `KD`. -/
theorem F0_EUzR (α K KY KD A : ℝ) (Y : ℝ → ℝ → ℝ)
    (hα : 0 ≤ α) (hA0 : 0 ≤ A) (hKY : 0 ≤ KY) (hKD : 0 ≤ KD)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hY : Work.FTS.PhiStar.F0 6 KY Y) (hD : Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y))
    (hrhoinv : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹))
    (srhoinv : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹)) :
    Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)) (EUzR α Y) := by
  have hW1 : Work.FTS.PhiStar.F0 6 (3 * KY) (fun z θ : ℝ => 3 * Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (3 : ℝ) hY
    simpa using h
  have hInv : Work.FTS.PhiStar.F0 6 (2 ^ 6 * A * KY) (fun z θ : ℝ => (1 + z)⁻¹ * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hKY srhoinv hsm hrhoinv hY
  have hW2 : Work.FTS.PhiStar.F0 6 (α * (2 ^ 6 * A * KY))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul α hInv
    rwa [abs_of_nonneg hα] at h
  have hW3 : Work.FTS.PhiStar.F0 6 (α * KD)
      (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul α hD
    rwa [abs_of_nonneg hα] at h
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts 3 hsm
  have s2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * ((1 + z)⁻¹ * Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α
      (Work.FTS.PhiStar.CoreAux.smoothOpen_mul_fts srhoinv hsm)
  have s3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α (sYblk hsm)
  have h12 := Work.FTS.PhiStar.CoreAux.F0_add s1 s2 hW1 hW2
  have h123 := Work.FTS.PhiStar.CoreAux.F0_add
    (Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts s1 s2) s3 h12 hW3
  have hneg : Work.FTS.PhiStar.F0 6 (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      (fun z θ : ℝ => -EUzB α Y z θ) := by
    have h := h123
    have hc : (3 * KY + α * (2 ^ 6 * A * KY)) + α * KD
        = 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD) := by ring
    rw [hc] at h
    have h2 := Work.FTS.PhiStar.CoreAux.F0_const_mul (-1 : ℝ) h
    have h3 : (|(-1 : ℝ)| * (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)))
        = (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)) := by
      rw [abs_neg, abs_one, one_mul]
    rw [h3] at h2
    refine Work.FTS.PhiStar.CoreAux.F0_congr
      (g := fun z θ : ℝ => (-1 : ℝ) * ((3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ))
        + α * Work.FTS.PhiStar.Yblk Y z θ)) (fun z θ _ _ _ => ?_) h2
    simp only [EUzB]
    ring
  refine Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => ?_) hneg
  simp only [EUzR]
  rfl

/-- **`F0 5` of `EUzD`.**  The bound is `3(K+KY) + α(2⁵A(K+KY)) + α·6(K+KY)`, linear in the
blocks. -/
theorem F0_EUzD (α K KY KD A : ℝ) (Y : ℝ → ℝ → ℝ)
    (hα : 0 ≤ α) (hA0 : 0 ≤ A) (hKY : 0 ≤ KY) (hKPY : 0 ≤ K + KY)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hP : Work.FTS.PhiStar.F0 6 (K + KY) (Work.Spaces.pth Y))
    (hZp : Work.FTS.PhiStar.F0 5 (6 * (K + KY)) (Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y)))
    (hrhoinv : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹))
    (srhoinv : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹)) :
    Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))) (EUzD α Y) := by
  have hP5 : Work.FTS.PhiStar.F0 5 (K + KY) (Work.Spaces.pth Y) := hP.mono (by norm_num) le_rfl
  have hW1 : Work.FTS.PhiStar.F0 5 (3 * (K + KY))
      (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (3 : ℝ) hP5
    simpa using h
  have hInv : Work.FTS.PhiStar.F0 5 (2 ^ 5 * A * (K + KY))
      (fun z θ : ℝ => (1 + z)⁻¹ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hKPY srhoinv hsm.pth
      (hrhoinv.mono (by norm_num) le_rfl) hP5
  have hW2 : Work.FTS.PhiStar.F0 5 (α * (2 ^ 5 * A * (K + KY)))
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul α hInv
    rwa [abs_of_nonneg hα] at h
  have hW3 : Work.FTS.PhiStar.F0 5 (α * (6 * (K + KY)))
      (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul α hZp
    rwa [abs_of_nonneg hα] at h
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 3 * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts 3 hsm.pth
  have s2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α
      (Work.FTS.PhiStar.CoreAux.smoothOpen_mul_fts srhoinv hsm.pth)
  have s3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ) :=
    Work.FTS.PhiStar.CoreAux.smoothOpen_const_mul_fts α (sYblk hsm.pth)
  have h12 := Work.FTS.PhiStar.CoreAux.F0_add s1 s2 hW1 hW2
  have h123 := Work.FTS.PhiStar.CoreAux.F0_add
    (Work.FTS.PhiStar.CoreAux.smoothOpen_add_fts s1 s2) s3 h12 hW3
  have hneg : Work.FTS.PhiStar.F0 5
      (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      (fun z θ : ℝ => -EUzB α (Work.Spaces.pth Y) z θ) := by
    have h := h123
    have hc : (3 * (K + KY) + α * (2 ^ 5 * A * (K + KY))) + α * (6 * (K + KY))
        = 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))) := by ring
    rw [hc] at h
    have h2 := Work.FTS.PhiStar.CoreAux.F0_const_mul (-1 : ℝ) h
    have h3 : (|(-1 : ℝ)| * (3 * (K + KY)
          + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))))
        = (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))) := by
      rw [abs_neg, abs_one, one_mul]
    rw [h3] at h2
    refine Work.FTS.PhiStar.CoreAux.F0_congr
      (g := fun z θ : ℝ => (-1 : ℝ) * ((3 * Work.Spaces.pth Y z θ
        + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ))
        + α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ)) (fun z θ _ _ _ => ?_) h2
    simp only [EUzB]
    ring
  refine Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => ?_) hneg
  simp only [EUzD]
  rfl

/-! ## The radial multiplications -/

theorem F0_EUR (α A BU : ℝ) (Y : ℝ → ℝ → ℝ) (hA0 : 0 ≤ A) (hBU : 0 ≤ BU)
    (srho : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)))
    (sEUzR : Work.FTS.EllipticEst.SmoothOpen (EUzR α Y))
    (hrho : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (1 + z)))
    (hEUzR : Work.FTS.PhiStar.F0 6 BU (EUzR α Y)) :
    Work.FTS.PhiStar.F0 6 (2 ^ 6 * A * BU) (EUR α Y) := by
  have h := Work.FTS.PhiStar.CoreAux.F0_mul hA0 hBU srho sEUzR hrho hEUzR
  exact h

theorem F0_EUD (α A BE : ℝ) (Y : ℝ → ℝ → ℝ) (hA0 : 0 ≤ A) (hBE : 0 ≤ BE)
    (srho : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)))
    (sEUzD : Work.FTS.EllipticEst.SmoothOpen (EUzD α Y))
    (hrho : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (1 + z)))
    (hEUzD : Work.FTS.PhiStar.F0 5 BE (EUzD α Y)) :
    Work.FTS.PhiStar.F0 5 (2 ^ 5 * A * BE) (EUD α Y) := by
  have h := Work.FTS.PhiStar.CoreAux.F0_mul hA0 hBE srho sEUzD
    (hrho.mono (by norm_num) le_rfl) hEUzD
  exact h

/-! ## The elementary absorption `αᵐ Aʲ x ≤ (A+1)²(α+1)S` -/

/-- `A·x ≤ (A+1)²(α+1)S` for `0 ≤ x ≤ S`, `1 ≤ A`, `0 ≤ α`. -/
theorem leM1 {A α S x : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α) (hx : 0 ≤ x) (hxS : x ≤ S) :
    A * x ≤ (A + 1) ^ 2 * (α + 1) * S := by
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  have hS : 0 ≤ S := le_trans hx hxS
  have h1 : A * x ≤ (A + 1) * S := by
    calc A * x ≤ (A + 1) * x := mul_le_mul_of_nonneg_right (by linarith) hx
      _ ≤ (A + 1) * S := mul_le_mul_of_nonneg_left hxS hA1.le
  have h2 : (A + 1) * S ≤ (A + 1) ^ 2 * (α + 1) * S :=
    mul_le_mul_of_nonneg_right (by nlinarith : A + 1 ≤ (A + 1) ^ 2 * (α + 1)) hS
  linarith

/-- `α·A·x ≤ (A+1)²(α+1)S` for `0 ≤ x ≤ S`, `1 ≤ A`, `0 ≤ α`. -/
theorem leM2 {A α S x : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α) (hx : 0 ≤ x) (hxS : x ≤ S) :
    α * A * x ≤ (A + 1) ^ 2 * (α + 1) * S := by
  have hA0 : 0 ≤ A := by linarith
  have hS : 0 ≤ S := le_trans hx hxS
  have h1 : α * A * x ≤ (α + 1) * (A + 1) * S := by
    have hbc : A * x ≤ (A + 1) * S := by
      calc A * x ≤ (A + 1) * x := mul_le_mul_of_nonneg_right (by linarith) hx
        _ ≤ (A + 1) * S := mul_le_mul_of_nonneg_left hxS (by linarith)
    calc α * A * x = α * (A * x) := by ring
      _ ≤ (α + 1) * ((A + 1) * S) :=
          mul_le_mul (by linarith) hbc (mul_nonneg hA0 hx) (by linarith)
      _ = (α + 1) * (A + 1) * S := by ring
  have h2 : (α + 1) * (A + 1) * S ≤ (A + 1) ^ 2 * (α + 1) * S := by
    have hc : A + 1 ≤ (A + 1) ^ 2 := by nlinarith
    calc (α + 1) * (A + 1) * S = (α + 1) * ((A + 1) * S) := by ring
      _ ≤ (α + 1) * ((A + 1) ^ 2 * S) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hS) (by linarith)
      _ = (A + 1) ^ 2 * (α + 1) * S := by ring
  linarith

/-- `α·A²·x ≤ (A+1)²(α+1)S` for `0 ≤ x ≤ S`, `1 ≤ A`, `0 ≤ α`. -/
theorem leM3 {A α S x : ℝ} (hA : 1 ≤ A) (hα : 0 ≤ α) (hx : 0 ≤ x) (hxS : x ≤ S) :
    α * A ^ 2 * x ≤ (A + 1) ^ 2 * (α + 1) * S := by
  have hA0 : 0 ≤ A := by linarith
  have hA10 : 0 ≤ A + 1 := by linarith
  have hA2 : A ^ 2 ≤ (A + 1) ^ 2 := pow_le_pow_left₀ hA0 (by linarith) 2
  calc α * A ^ 2 * x = α * (A ^ 2 * x) := by ring
    _ ≤ (α + 1) * ((A + 1) ^ 2 * S) :=
        mul_le_mul (by linarith) (mul_le_mul hA2 hxS hx (pow_nonneg hA10 2))
          (mul_nonneg (pow_nonneg hA0 2) hx) (by linarith)
    _ = (A + 1) ^ 2 * (α + 1) * S := by ring

/-! ## The target -/

/-- **The order-six flat bound of the `EU`-star-field**, `EU α Y = -(z/(z+1))·Wone α Y`.

Prove `FlatW 6 (EU α Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`, `FlatW 7 Y K`,
`Fb 6 KY Y`, `F0 6 KD (Yblk Y)`; the constant must stay **linear** in `K + KY + KD`.

Import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`: `CoefBundle6s`, `atomData`,
`EUzR`/`EUzD`, `EUR`/`EUD` and `euEUR_eq`, `flatW6_of_F0`, `FlatW_mono6`, `mono_const`,
`pth_thetaOnly`. Recommended route: prove the strong pair `F0 6 (EUR α Y)` and
`F0 5 (pth (EUR α Y)) = F0 5 (EUD α Y)` (`z/(z+1)` is `θ`-free), where the `EUz`-parts are the
same estimates as in the `EUz`-task; then `F0_congr` + `flatW6_of_F0`. The sibling
`Submission/Work/FTS/PhiStar/CoreAux/Fb_EU_bound.lean` proves the order-**four** version of the
joint statement for `EUz` and `EU`. -/
theorem EU6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EU α Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hrF : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (1 + z)) :=
    (hcoef (fun z _ : ℝ => z / (1 + z)) (by simp [coefFun])).1
  have srF : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) :=
    (hcoef (fun z _ : ℝ => z / (1 + z)) (by simp [coefFun])).2
  have hiF : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (1 + z)⁻¹) :=
    (hcoef (fun z _ : ℝ => (1 + z)⁻¹) (by simp [coefFun])).1
  have siF : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹) :=
    (hcoef (fun z _ : ℝ => (1 + z)⁻¹) (by simp [coefFun])).2
  refine ⟨5000 * (A + 1) ^ 2, by positivity, ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb hD
  obtain ⟨hY6, hP6, hD6, hZp5, _hDthP5⟩ := atomData hK hKY hKD hsm hW hFb hD
  have hKPY : 0 ≤ K + KY := by linarith
  have hEUzR6 := F0_EUzR α K KY KD A Y hα hA0 hKY hKD hsm hY6 hD6 hiF siF
  have hEUzD5 := F0_EUzD α K KY KD A Y hα hA0 hKY hKPY hsm hP6 hZp5 hiF siF
  have sEUzR := smoothOpen_EUzR α Y hsm
  have sEUzD := smoothOpen_EUzD α Y hsm
  have BU6nn : 0 ≤ 3 * KY + (α * (2 ^ 6 * A * KY) + α * KD) := by
    have h1 : 0 ≤ α * (2 ^ 6 * A * KY) :=
      mul_nonneg hα (mul_nonneg (mul_nonneg (by positivity) hA0) hKY)
    have h2 : 0 ≤ α * KD := mul_nonneg hα hKD
    have h3 : 0 ≤ 3 * KY := by linarith
    linarith
  have BE5nn : 0 ≤ 3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))) := by
    have h1 : 0 ≤ α * (2 ^ 5 * A * (K + KY)) :=
      mul_nonneg hα (mul_nonneg (mul_nonneg (by positivity) hA0) hKPY)
    have h2 : 0 ≤ α * (6 * (K + KY)) := mul_nonneg hα (by linarith)
    have h3 : 0 ≤ 3 * (K + KY) := by linarith
    linarith
  have hEUR6 := F0_EUR α A (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD)) Y
    hA0 BU6nn srF sEUzR hrF hEUzR6
  have hEUD5 := F0_EUD α A
    (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))) Y
    hA0 BE5nn srF sEUzD hrF hEUzD5
  have hEURp5 : Work.FTS.PhiStar.F0 5
      (2 ^ 5 * A * (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY)))))
      (Work.Spaces.pth (EUR α Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (pth_EUR α Y hsm) hEUD5
  -- the arithmetic: both constants are dominated by `5000(A+1)²(α+1)(K+KY+KD)`
  set S : ℝ := K + KY + KD with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; linarith
  have hKYle : KY ≤ S := by rw [hSdef]; linarith
  have hKPYle : K + KY ≤ S := by rw [hSdef]; linarith
  have hKDle : KD ≤ S := by rw [hSdef]; linarith
  have hM0 : 0 ≤ (A + 1) ^ 2 * (α + 1) * S :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) hS0
  have hle6 : 2 ^ 6 * A * (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
      ≤ 5000 * (A + 1) ^ 2 * (α + 1) * S := by
    have h1 := leM1 (A := A) (α := α) (S := S) (x := KY) hA1 hα hKY hKYle
    have h2 := leM2 (A := A) (α := α) (S := S) (x := KD) hA1 hα hKD hKDle
    have h3 := leM3 (A := A) (α := α) (S := S) (x := KY) hA1 hα hKY hKYle
    have hexp : 2 ^ 6 * A * (3 * KY + (α * (2 ^ 6 * A * KY) + α * KD))
        = 192 * (A * KY) + 4096 * (α * A ^ 2 * KY) + 64 * (α * A * KD) := by ring
    rw [hexp]
    calc 192 * (A * KY) + 4096 * (α * A ^ 2 * KY) + 64 * (α * A * KD)
        ≤ 5000 * ((A + 1) ^ 2 * (α + 1) * S) := by linarith
      _ = 5000 * (A + 1) ^ 2 * (α + 1) * S := by ring
  have hle5 : 2 ^ 5 * A * (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
      ≤ 5000 * (A + 1) ^ 2 * (α + 1) * S := by
    have h1 := leM1 (A := A) (α := α) (S := S) (x := K + KY) hA1 hα hKPY hKPYle
    have h2 := leM2 (A := A) (α := α) (S := S) (x := K + KY) hA1 hα hKPY hKPYle
    have h3 := leM3 (A := A) (α := α) (S := S) (x := K + KY) hA1 hα hKPY hKPYle
    have hexp : 2 ^ 5 * A * (3 * (K + KY) + (α * (2 ^ 5 * A * (K + KY)) + α * (6 * (K + KY))))
        = 96 * (A * (K + KY)) + 1024 * (α * A ^ 2 * (K + KY)) + 192 * (α * A * (K + KY)) := by
      ring
    rw [hexp]
    calc 96 * (A * (K + KY)) + 1024 * (α * A ^ 2 * (K + KY)) + 192 * (α * A * (K + KY))
        ≤ 5000 * ((A + 1) ^ 2 * (α + 1) * S) := by linarith
      _ = 5000 * (A + 1) ^ 2 * (α + 1) * S := by ring
  have hF1 : Work.FTS.PhiStar.F0 6 (5000 * (A + 1) ^ 2 * (α + 1) * S) (EUR α Y) :=
    hEUR6.mono le_rfl hle6
  have hF2 : Work.FTS.PhiStar.F0 5 (5000 * (A + 1) ^ 2 * (α + 1) * S)
      (Work.Spaces.pth (EUR α Y)) := hEURp5.mono le_rfl hle5
  -- transfer the two halves to `EU α Y = EUR α Y` (`euEUR_eq`) and assemble
  have heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.PhiStar.EU α Y z θ = EUR α Y z θ := fun z θ _ _ _ => euEUR_eq α Y z θ
  have hF1' : Work.FTS.PhiStar.F0 6 (5000 * (A + 1) ^ 2 * (α + 1) * S)
      (Work.FTS.PhiStar.EU α Y) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ hz hθ hθ' => heq z θ hz hθ hθ') hF1
  have hF2' : Work.FTS.PhiStar.F0 5 (5000 * (A + 1) ^ 2 * (α + 1) * S)
      (Work.Spaces.pth (Work.FTS.PhiStar.EU α Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (fun z θ hz hθ hθ' => pth_congr6 heq z θ hz hθ hθ') hF2
  exact flatW6_of_F0 hF1' hF2'

end Work.FTS.StrongPersist.SP6
