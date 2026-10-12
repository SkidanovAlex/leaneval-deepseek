import ChallengeDeps
import Submission.PotSupport
import Submission.RadialRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 3/5 — radial functions are even; the scattering numerator `g := v(1−ω)`
is even and vanishes outside `ball 0 R`

For instantiating the convolution lemmas (`Submission.ConvolutionTaylor`) and
the kernel calculus on the scattering numerator `g := v·(1−w)`, we record the
closure facts for `IsRadial` (pointwise sum, difference, product, `1 − w`)
and the consequences: every radial function is even (`w (−x) = w x`), and if
`tsupport v ⊆ ball 0 R` then `g x = 0` for `R ≤ ‖x‖`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real

namespace Submission.BoseGases

open _root_.BoseGases
set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A radial function is even. -/
lemma radial_neg {w : ℝ³ → ℝ} (hw : IsRadial w) (x : ℝ³) : w (-x) = w x := by
  exact hw (-x) x (by simp)

/-- A radial function is even (bundled form). -/
lemma radial_even {w : ℝ³ → ℝ} (hw : IsRadial w) : ∀ x : ℝ³, w (-x) = w x :=
  radial_neg hw

/-- Radial functions are closed under pointwise addition. -/
lemma radial_add {f g : ℝ³ → ℝ} (hf : IsRadial f) (hg : IsRadial g) :
    IsRadial (fun x : ℝ³ => f x + g x) := by
  intro x y hxy
  simp [hf x y hxy, hg x y hxy]

/-- Radial functions are closed under pointwise subtraction. -/
lemma radial_sub {f g : ℝ³ → ℝ} (hf : IsRadial f) (hg : IsRadial g) :
    IsRadial (fun x : ℝ³ => f x - g x) := by
  intro x y hxy
  simp [hf x y hxy, hg x y hxy]

/-- Radial functions are closed under pointwise multiplication. -/
lemma radial_mul {f g : ℝ³ → ℝ} (hf : IsRadial f) (hg : IsRadial g) :
    IsRadial (fun x : ℝ³ => f x * g x) := by
  intro x y hxy
  simp [hf x y hxy, hg x y hxy]

/-- The constant `1` is radial, hence so is `1 − w` for radial `w`. -/
lemma radial_one_sub {w : ℝ³ → ℝ} (hw : IsRadial w) :
    IsRadial (fun x : ℝ³ => 1 - w x) := by
  intro x y hxy
  simp [hw x y hxy]

/-- `g := v(1−w)` is radial when `v` and `w` are. -/
lemma radial_scat_g {v w : ℝ³ → ℝ} (hv : IsRadial v) (hw : IsRadial w) :
    IsRadial (fun x : ℝ³ => v x * (1 - w x)) :=
  radial_mul hv (radial_one_sub hw)

/-- `g := v(1−w)` is even when `v` and `w` are radial. -/
lemma scat_g_even {v w : ℝ³ → ℝ} (hv : IsRadial v) (hw : IsRadial w) :
    ∀ x : ℝ³, (v (-x) * (1 - w (-x))) = (v x * (1 - w x)) := by
  intro x
  simp [radial_neg hv x, radial_neg hw x]

/-- `g := v(1−w)` vanishes outside `ball 0 R` when `v` does. -/
lemma scat_g_zero_of_norm_ge {v w : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {x : ℝ³} (hx : R ≤ ‖x‖) :
    v x * (1 - w x) = 0 := by
  have hvx : v x = 0 := v_eq_zero_of_norm_ge hv_supp hx
  simp [hvx]

/-- `g(1+ω) := v(1−w)(1+w)` vanishes outside `ball 0 R` when `v` does. -/
lemma scat_g1pw_zero_of_norm_ge {v w : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {x : ℝ³} (hx : R ≤ ‖x‖) :
    (v x * (1 - w x)) * (1 + w x) = 0 := by
  have hvx : v x = 0 := v_eq_zero_of_norm_ge hv_supp hx
  simp [hvx]

end BoseGases

end Submission
