/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the gluing construction (FBif, part 3c)

This module fixes the *geometry* and the *definitions* of the C¹ gluing of the perturbation
`f_ε = perturb c q ε` with the model `T_c` outside a large ball, and of the invariant Beltrami
coefficient of the glued map.  The lemmas about these definitions live in

* `FBif/escR_props.lean`      — the escape radius of `T_c` and the cycle bound;
* `FBif/radius_numerics.lean` — the numeric inequalities between the three radii;
* `FBif/cutoff_props.lean`    — the radial cutoff and its Wirtinger derivatives;
* `FBif/glue_derivs.lean`     — the Wirtinger derivatives of the glued map;
* `FBif/glueMu_*.lean`        — measurability, invariance, bound and support of `glueMu`,
* `FBif/GlueAssembly.lean`    — the assembly of the gluing datum.

## The geometry

`Work.FBif.escR c` is the escape radius of `T_c`: `T_c` does not decrease the modulus outside
its ball.  Three radii are fixed:

* `innerRad c = farRad c / 2` — inside this ball the glued map is *equal* to the perturbation,
  hence antiholomorphic;
* `cutRad c = 3 * farRad c / 4` — the perturbation is cut off (vanishes) outside this ball;
* `farRad c = max 16 (8 * (‖c‖ + 1))` — beyond this ball the glued map is *equal* to `T_c`.

The glued map is `glueMap c q ε χ z = T_c z + ε * χ z * q z` for a smooth radial cutoff `χ`
equal to `1` on the closed ball of radius `innerRad c` and to `0` outside the open ball of
radius `cutRad c` (`cutoff c`).  Then

* `‖z‖ ≥ innerRad c` ⟹ `‖F z‖ ≥ farRad c`: the outer region escapes in one step, so every
  orbit passes through the cut annulus at most once before entering the far region;
* `F = T_c` on a neighbourhood of every point of `{‖z‖ ≥ farRad c}`, so `∂F = 0` there;
* hence the non-escaping set `nonEsc F (farRad c)` is contained in the inner ball, where `F` is
  antiholomorphic.

The invariant coefficient is defined by pulling back `0` along the orbit until it hits the far
region: `glueMu F R z = (pullRev · F)^[n z] 0 z` where `n z` is the first hitting time of
`{‖z‖ ≥ R}`, and `0` on the non-escaping set.
-/
import Mathlib
import Submission.Work.MRMT.Found.M
import Submission.Work.FBif.Defs
import Submission.Work.FBif.Antipoly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The escape radius of `T_c` -/

/-- The escape radius of the mandelbar: for `‖z‖ ≥ escR c` the modulus of the orbit of `z`
under `T_c` is nondecreasing. -/
def escR (c : ℂ) : ℝ := (1 + Real.sqrt (1 + 4 * ‖c‖)) / 2

/-! ## The three radii -/

/-- The far radius: beyond it the glued map is the model `T_c`. -/
def farRad (c : ℂ) : ℝ := max 16 (8 * (‖c‖ + 1))

/-- The inner radius: inside it the glued map is the perturbation. -/
def innerRad (c : ℂ) : ℝ := farRad c / 2

/-- The cut radius: the perturbation is cut off outside it. -/
def cutRad (c : ℂ) : ℝ := 3 * farRad c / 4

/-! ## The radial cutoff, the glued map and the invariant coefficient -/

/-- A real valued function, viewed as a complex valued one. -/
def realCoe (f : ℂ → ℝ) : ℂ → ℂ := fun z => (f z : ℂ)

/-- The far radius of the gluing datum: it exceeds `2 * (farRad c + 1)`, so that the
quantitative normalisation `Work.FBif.principal_decay_bound` of the principal solution of
`glueMu` (whose support is contained in the ball of radius `farRad c`) is available at this
radius. -/
def datumRad (c : ℂ) : ℝ := 2 * (farRad c + 1)

/-- The radial cutoff `z ↦ f (‖z‖ ^ 2)`. -/
def radialCut (f : ℝ → ℝ) : ℂ → ℝ := fun z => f (‖z‖ ^ 2)

/-- The radial cutoff adapted to the radii `innerRad c` and `cutRad c`: it is `1` inside the
ball of radius `innerRad c` and `0` outside the ball of radius `cutRad c`. -/
def cutoff (c : ℂ) : ℂ → ℝ :=
  radialCut (fun t => Real.smoothTransition ((cutRad c ^ 2 - t) / (cutRad c ^ 2 - innerRad c ^ 2)))

theorem cutoff_apply (c : ℂ) (z : ℂ) :
    cutoff c z = Real.smoothTransition ((cutRad c ^ 2 - ‖z‖ ^ 2) /
      (cutRad c ^ 2 - innerRad c ^ 2)) := rfl

/-- The glued map: the perturbation inside, the model `T_c` outside. -/
def glueMap (c : ℂ) (q : ℂ → ℂ) (ε : ℝ) (χ : ℂ → ℝ) : ℂ → ℂ :=
  fun z => Tantibar c z + (ε : ℂ) * ((χ z : ℝ) : ℂ) * q z

@[simp] theorem glueMap_apply (c : ℂ) (q : ℂ → ℂ) (ε : ℝ) (χ : ℂ → ℝ) (z : ℂ) :
    glueMap c q ε χ z = Tantibar c z + (ε : ℂ) * ((χ z : ℝ) : ℂ) * q z := rfl

/-- On the inner ball, the glued map is the perturbation. -/
theorem glueMap_eq_perturb {c : ℂ} {q : ℂ → ℂ} {ε : ℝ} {χ : ℂ → ℝ}
    (hχ : ∀ z : ℂ, ‖z‖ ≤ innerRad c → χ z = 1) {z : ℂ} (hz : ‖z‖ ≤ innerRad c) :
    glueMap c q ε χ z = perturb c q ε z := by
  rw [glueMap_apply, perturb_apply, hχ z hz]
  norm_num

/-- Outside the cut ball, the glued map is the model. -/
theorem glueMap_eq_tantibar {c : ℂ} {q : ℂ → ℂ} {ε : ℝ} {χ : ℂ → ℝ}
    (hχ : ∀ z : ℂ, cutRad c ≤ ‖z‖ → χ z = 0) {z : ℂ} (hz : cutRad c ≤ ‖z‖) :
    glueMap c q ε χ z = Tantibar c z := by
  rw [glueMap_apply, hχ z hz]
  norm_num

/-- The non-escaping set of `F` at radius `R`. -/
def nonEsc (F : ℂ → ℂ) (R : ℝ) : Set ℂ := {z : ℂ | ∀ n : ℕ, ‖(F^[n]) z‖ < R}

theorem nonEsc_forward {F : ℂ → ℂ} {R : ℝ} {z : ℂ} (h : z ∈ nonEsc F R) :
    F z ∈ nonEsc F R := fun n => by
  have h' : (F^[n]) (F z) = (F^[n + 1]) z := (Function.iterate_succ_apply F n z).symm
  rw [h']
  exact h (n + 1)

/-- If everything outside the ball of radius `alpha` escapes in one step, the non-escaping set
is contained in that ball. -/
theorem nonEsc_subset_ball {F : ℂ → ℂ} {R α : ℝ} (hesc : ∀ z : ℂ, α ≤ ‖z‖ → R ≤ ‖F z‖) :
    nonEsc F R ⊆ Metric.ball 0 α := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hlt
  push_neg at hlt
  have h1 : R ≤ ‖F z‖ := hesc z hlt
  have h2 := hz 1
  rw [Function.iterate_one] at h2
  linarith

/-- The `n`-fold pull-back operator applied to `0`. -/
def pullIter (F : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  (fun ν : ℂ → ℂ => Work.MRMT.Found.pullRev ν F)^[n] 0

/-- The first hitting time of the far ball `{‖z‖ ≥ R}` (and `0` if there is none). -/
noncomputable def hitTime (F : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℕ :=
  if h : ∃ n : ℕ, R ≤ ‖(F^[n]) z‖ then Nat.find h else 0

/-- **The invariant Beltrami coefficient of the glued map**: the pull-back of `0` along the
orbit until it hits the far ball. -/
noncomputable def glueMu (F : ℂ → ℂ) (R : ℝ) : ℂ → ℂ :=
  fun z => if h : ∃ n : ℕ, R ≤ ‖(F^[n]) z‖ then pullIter F (Nat.find h) z else 0

/-- The exceptional set of the glued map: where it fails to be orientation reversing. -/
def badSet (F : ℂ → ℂ) : Set ℂ := {z : ℂ | ‖Work.MRMT.dz F z‖ ≥ ‖Work.MRMT.dzbar F z‖}

theorem badSet_hrev {F : ℂ → ℂ} :
    ∀ z ∉ badSet F, ‖Work.MRMT.dz F z‖ < ‖Work.MRMT.dzbar F z‖ :=
  fun z hz => not_le.mp hz

end Work.FBif

end
