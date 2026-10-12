import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.integrableOn_wSmallPair_cube
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.PlateauDefs` — the vocabulary of the plateau ledger

The sliding kernel `wSmallPair M ℓ d u f` of the corpus is the product

    `χ_{B(u)}(x) · (f(x−y)/(χ_M⋆χ_M)((x−y)/(ℓd))) / (χ⋆χ)((x−y)/ℓ) · χ_{B(u)}(y)`

(FS `eq:HBU`).  On the **plateau** — i.e. when the sliding box `B(u) = dlBox ℓ d u`
is nonempty and satisfies the clearance `‖z‖ ≤ ℓ/4 − ℓd` for `z ∈ B(u)` — the
`ℓ`-scale factor `χ(x/ℓ) = chiScale ℓ x` is the *constant* `chiSupAbs` on `B(u)`, so
the whole cutoff collapses onto the *explicit* cosine bump `chiSmall M`:

    `chiSmallB M ℓ d u x = chiSupAbs · psi M ℓ d u x`,
    `psi M ℓ d u x := chiSmall M ((ℓd)⁻¹ • x − u)`.

This file lays down `psi`, the renormalisation denominator `D₁ = convScaleSmall M (ℓd)`
and the ratio kernel `K`, together with the definitional identifications with the
corpus kernels (`wSmallPair`, `wSmallScaled`, `chiMass`).

Nothing here is proved beyond definitional rewriting; the analytic content lives in the
`Submission/Work/BoseFixB1S/Plateau/` modules.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **plateau profile** of the sliding box: the explicit cosine bump
`χ_M((ℓd)⁻¹•x − u)`.  The corpus cutoff `chiSmallB M ℓ d u x` equals
`chiScale ℓ x · psi M ℓ d u x` (definitionally). -/
noncomputable def psi (M : ℕ) (ℓ d : ℝ) (u : ℝ³) : ℝ³ → ℝ :=
  fun x => chiSmall M ((ℓ * d)⁻¹ • x - u)

@[simp] lemma psi_apply (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (x : ℝ³) :
    psi M ℓ d u x = chiSmall M ((ℓ * d)⁻¹ • x - u) := rfl

lemma psi_nonneg (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (x : ℝ³) : 0 ≤ psi M ℓ d u x :=
  chiSmall_nonneg M _

lemma psi_continuous {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : ℝ³) :
    Continuous (psi M ℓ d u) := by
  have h2 : Continuous fun x : ℝ³ => (ℓ * d)⁻¹ • x - u := by fun_prop
  exact (chiSmall_continuous hM).comp h2

/-- The `(ℓd)`-scale renormalisation denominator `(χ_M⋆χ_M)((ℓd)⁻¹•z)`. -/
noncomputable def D1 (M : ℕ) (ℓ d : ℝ) : ℝ³ → ℝ :=
  fun z => convScaleSmall M (ℓ * d) z

@[simp] lemma D1_apply (M : ℕ) (ℓ d : ℝ) (z : ℝ³) :
    D1 M ℓ d z = conv3Small M ((ℓ * d)⁻¹ • z) := rfl

lemma conv3Small_nonneg' (M : ℕ) (z : ℝ³) : 0 ≤ conv3Small M z := by
  rw [conv3Small]
  exact integral_nonneg (fun y => mul_nonneg (chiSmall_nonneg M y) (chiSmall_nonneg M (z - y)))

lemma D1_nonneg (M : ℕ) (ℓ d : ℝ) (z : ℝ³) : 0 ≤ D1 M ℓ d z :=
  conv3Small_nonneg' M _

/-- The `(ℓd)`-scale renormalisation denominator, in `conv3Small` form. -/
lemma D1_eq (M : ℕ) (ℓ d : ℝ) (z : ℝ³) :
    D1 M ℓ d z = conv3Small M ((ℓ * d)⁻¹ • z) := rfl

/-- The renormalised ratio kernel of the sliding box:
`K f z = (f z / (χ_M⋆χ_M)(z/(ℓd))) / (χ⋆χ)(z/ℓ)`. -/
noncomputable def K (M : ℕ) (ℓ d : ℝ) (f : ℝ³ → ℝ) : ℝ³ → ℝ :=
  fun z => (f z / D1 M ℓ d z) / convScale ℓ z

@[simp] lemma K_apply (M : ℕ) (ℓ d : ℝ) (f : ℝ³ → ℝ) (z : ℝ³) :
    K M ℓ d f z = (f z / D1 M ℓ d z) / convScale ℓ z := rfl

/-- The corpus `wSmallScaled`-over-`convScale` ratio is exactly the `K` kernel. -/
lemma wSmallScaled_div_convScale_eq_K (M : ℕ) (ℓ d : ℝ) (f : ℝ³ → ℝ) (z : ℝ³) :
    wSmallScaled M (ℓ * d) f z / convScale ℓ z = K M ℓ d f z := rfl

/-- **The kernel identification**: `wSmallPair` is the product of the two cutoffs with
the ratio kernel `K` of the difference variable. -/
lemma wSmallPair_eq_chiSmallB_mul_K (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (f : ℝ³ → ℝ)
    (x y : ℝ³) :
    wSmallPair M ℓ d u f x y
      = chiSmallB M ℓ d u x * K M ℓ d f (x - y) * chiSmallB M ℓ d u y := rfl

/-- The same for the one-body kernel (`f = g₀`). -/
lemma wSmall1Pair_eq_chiSmallB_mul_K {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (x y : ℝ³) :
    wSmall1Pair h M ℓ d u x y
      = chiSmallB M ℓ d u x * K M ℓ d (g0 v h) (x - y) * chiSmallB M ℓ d u y := rfl

/-- `chiSmallB` is the `ℓ`-scale factor times the plateau profile (definitional). -/
lemma chiSmallB_eq_chiScale_mul_psi (M : ℕ) (ℓ d : ℝ) (u x : ℝ³) :
    chiSmallB M ℓ d u x = chiScale ℓ x * psi M ℓ d u x := rfl

end Work.BoseFixB1S
