/-
# `FTS/StrongPersist/StarPkg6Fields.lean` — the order-six flat bounds of the five star fields

This module proves `Work.FTS.StrongPersist.FlatW6Fields_self`, the flat-calculus input of
`StarPkg6OfCore`: from the flat data of `Ŷ`,

* `SmoothOpen Y`, `FlatW 7 Y K`,
* `Fb 6 KY Y` (i.e. `F0 6` of `Y` and of `∂_θY`),
* `F0 6 KD (Yblk Y)`,  `Yblk Y = z ∂_z Y`,

the five fields `EH α Y`, `EVz Y`, `EV Y`, `EUz α Y`, `EU α Y` (the `Ŷ`-expressions of the
transport coefficients `ℛ, 𝒱, 𝒰` of `Work.Construction`) satisfy `FlatW 6` at the constant
`C·(α+1)·(K + KY + KD)`.

The pricing is the corrected one: `EU α Y = -(z/(z+1))·Wone α Y` with
`Wone α Y = 3Y + α(Y/(z+1) + Yblk Y)` grows *linearly* in `α`, so the constant carries the
factor `(α+1)` for **all five** fields (the `(α+1)` is a weakening on the two `α`-free fields
`EVz`, `EV`).

The proof is the order-six lift of `CoreAux/Assembly`'s flat calculus:

* every field is a combination of the *blocks* `Y`, `Yblk Y = z∂_z Y`, `Tblk Y = sin 2θ·∂_θ Y`
  and `Y/(z+1)` with the smooth coefficients `sin²θ`, `cos²θ-2sin²θ`, `sin 2θ`, `cos 2θ`,
  `z/(z+1)`, `(1+z)⁻¹`;
* `F0` is closed under products (`F0_mul`), sums (`F0_add`), multiplication by `z∂_z` with an
  order shift (`F0_zpz`) and by constants; the `D_θ`-shift `F0 n (D_θ g) ← F0 (n+1) g` handles
  the `Tblk`-block;
* the `FlatW 6` conclusion is `F0 6` (radial clause) together with `F0 5 ∘ ∂_θ` (angular
  clause), and the second is obtained by the `Fb`-route (`Fb_add`, `Fb_mul_theta_free` on
  blocks and coefficients, `Fb.const_mul`).

All constants are explicit and are finally dominated by `2^48·(Ac+Az+1)^40 + 8`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongPersist.StarPkg6Aux
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.F0_theta_coefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_z_coefs
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add
import Submission.Work.FTS.PhiStar.CoreAux.Fb_mul_theta_free
import Submission.Work.FTS.PhiStar.CoreAux.Fb_EU_bound
import Submission.Work.FTS.PhiStar.CoreAux.LopIter_continuousOn_of_contDiff
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.PhiStar (F0 Fb)

/-! ## The master constants -/

/-- A monomial of degree `≤ 39` in `M` and a factor `z ≤ M` is dominated by `2^45·M^40`. -/
theorem monomial_le_big {M : ℝ} (hM : 1 ≤ M) {j : ℕ} (hj : j ≤ 45) {y z : ℝ}
    (hy0 : 0 ≤ y) (hyM : y ≤ M) (hz0 : 0 ≤ z) (hzM : z ≤ M) {c : ℕ} (hc : c ≤ 38) :
    (2 : ℝ) ^ j * y * z * M ^ c ≤ 2 ^ 45 * M ^ 40 := by
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ 45 := pow_le_pow_right₀ (by norm_num) hj
  have hy : y ≤ M := hyM
  have hz : z ≤ M := hzM
  have hc' : M ^ c ≤ M ^ 38 := pow_le_pow_right₀ hM (by omega)
  have hM0 : 0 ≤ M := by linarith
  have h1 : (2 : ℝ) ^ j * y * z ≤ 2 ^ 45 * M * M := by
    have h21 : (2 : ℝ) ^ j * y ≤ 2 ^ 45 * M :=
      mul_le_mul h2 hy hy0 (by positivity)
    calc (2 : ℝ) ^ j * y * z ≤ (2 ^ 45 * M) * M :=
          mul_le_mul h21 hz hz0 (mul_nonneg (by positivity) hM0)
      _ = 2 ^ 45 * M * M := rfl
  calc (2 : ℝ) ^ j * y * z * M ^ c ≤ (2 ^ 45 * M * M) * M ^ 38 :=
        mul_le_mul h1 hc' (by positivity) (by positivity)
    _ = 2 ^ 45 * M ^ 40 := by ring

/-- A sum of at most eight such monomials is dominated by the final constant. -/
theorem bound_le_final {M B C S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α)
    (hB : B ≤ 8 * (2 ^ 45 * M ^ 40)) (hC : C ≤ 8 * (2 ^ 45 * M ^ 40)) :
    (B + α * C) * S ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have hM0 : 0 ≤ M := by linarith
  have hbig : 0 ≤ 2 ^ 45 * M ^ 40 := by positivity
  have h1 : B + α * C ≤ 8 * (2 ^ 45 * M ^ 40) * (α + 1) := by
    have h2 : α * C ≤ α * (8 * (2 ^ 45 * M ^ 40)) :=
      mul_le_mul_of_nonneg_left hC hα
    nlinarith [h2, hbig, hα]
  have h3 : 8 * (2 ^ 45 * M ^ 40) * (α + 1) ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) := by
    have h4 : (8 : ℝ) * (2 ^ 45 * M ^ 40) ≤ 2 ^ 48 * M ^ 40 + 8 := by
      have : (2 : ℝ) ^ 48 = 8 * 2 ^ 45 := by norm_num
      nlinarith [hbig, this]
    exact mul_le_mul_of_nonneg_right h4 (by linarith)
  have hfinal : (2 ^ 48 * M ^ 40 + 8) * (α + 1) ≥ 0 :=
    mul_nonneg (by positivity) (by linarith)
  calc (B + α * C) * S ≤ (8 * (2 ^ 45 * M ^ 40) * (α + 1)) * S :=
        mul_le_mul_of_nonneg_right h1 hS
    _ ≤ ((2 ^ 48 * M ^ 40 + 8) * (α + 1)) * S :=
        mul_le_mul_of_nonneg_right h3 hS
    _ = (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by ring

/-! ## Monomial absorption -/

/-- Three `M`-bounded factors and an `M`-power are dominated by `2^45·M^40`. -/
theorem mono3_le_big {M : ℝ} (hM : 1 ≤ M) {j : ℕ} (hj : j ≤ 45) {c : ℕ} (hc : c ≤ 37)
    {u v w : ℝ} (hu0 : 0 ≤ u) (huM : u ≤ M) (hv0 : 0 ≤ v) (hvM : v ≤ M) (hw0 : 0 ≤ w)
    (hwM : w ≤ M) : (2 : ℝ) ^ j * u * v * w * M ^ c ≤ 2 ^ 45 * M ^ 40 := by
  have hM0 : 0 ≤ M := by linarith
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ 45 := pow_le_pow_right₀ (by norm_num) hj
  have hleft : (2 : ℝ) ^ j * u * v * w ≤ 2 ^ 45 * (M * M * M) := by
    have ha : u * v ≤ M * M := mul_le_mul huM hvM hv0 hM0
    have hb : w ≤ M := hwM
    calc (2 : ℝ) ^ j * u * v * w = (2 ^ j * (u * v)) * w := by ring
      _ ≤ (2 ^ 45 * (M * M)) * M :=
          mul_le_mul (mul_le_mul h2 ha (by positivity) (by positivity)) hb hw0
            (mul_nonneg (by positivity) (by positivity))
      _ = 2 ^ 45 * (M * M * M) := by ring
  have hc' : M ^ c ≤ M ^ 37 := pow_le_pow_right₀ hM (by omega)
  calc (2 : ℝ) ^ j * u * v * w * M ^ c = ((2 : ℝ) ^ j * u * v * w) * M ^ c := rfl
    _ ≤ (2 ^ 45 * (M * M * M)) * M ^ 37 :=
        mul_le_mul hleft hc' (by positivity) (by positivity)
    _ = 2 ^ 45 * M ^ 40 := by ring

/-- A monomial (α-free) is dominated by the final constant. -/
theorem mono_final {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α)
    {j : ℕ} (hj : j ≤ 45) {c : ℕ} (hc : c ≤ 37) {u v w : ℝ}
    (hu0 : 0 ≤ u) (huM : u ≤ M) (hv0 : 0 ≤ v) (hvM : v ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M) :
    (2 : ℝ) ^ j * u * v * w * M ^ c * S ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have h1 : (2 : ℝ) ^ j * u * v * w * M ^ c ≤ 2 ^ 45 * M ^ 40 :=
    mono3_le_big hM hj hc hu0 huM hv0 hvM hw0 hwM
  have hbig : 0 ≤ 2 ^ 45 * M ^ 40 := by positivity
  have hS1 : S ≤ (α + 1) * S := by nlinarith
  have h3 : (2 : ℝ) ^ 45 * M ^ 40 ≤ 2 ^ 48 * M ^ 40 + 8 := by
    have he : (2 : ℝ) ^ 48 = 8 * 2 ^ 45 := by norm_num
    nlinarith [hbig, he]
  calc (2 : ℝ) ^ j * u * v * w * M ^ c * S ≤ (2 ^ 45 * M ^ 40) * S :=
        mul_le_mul_of_nonneg_right h1 hS
    _ ≤ (2 ^ 45 * M ^ 40) * ((α + 1) * S) := mul_le_mul_of_nonneg_left hS1 hbig
    _ ≤ (2 ^ 48 * M ^ 40 + 8) * ((α + 1) * S) :=
        mul_le_mul_of_nonneg_right h3 (by nlinarith)
    _ = (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by ring

/-- A monomial carrying one factor of `α` is dominated by the final constant. -/
theorem mono_final_alpha {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α)
    {j : ℕ} (hj : j ≤ 45) {c : ℕ} (hc : c ≤ 37) {u v w : ℝ}
    (hu0 : 0 ≤ u) (huM : u ≤ M) (hv0 : 0 ≤ v) (hvM : v ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M) :
    (2 : ℝ) ^ j * u * v * w * M ^ c * α * S ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have h1 : (2 : ℝ) ^ j * u * v * w * M ^ c ≤ 2 ^ 45 * M ^ 40 :=
    mono3_le_big hM hj hc hu0 huM hv0 hvM hw0 hwM
  have hbig : 0 ≤ 2 ^ 45 * M ^ 40 := by positivity
  have hαS : α * S ≤ (α + 1) * S := by nlinarith
  have h3 : (2 : ℝ) ^ 45 * M ^ 40 ≤ 2 ^ 48 * M ^ 40 + 8 := by
    have he : (2 : ℝ) ^ 48 = 8 * 2 ^ 45 := by norm_num
    nlinarith [hbig, he]
  calc (2 : ℝ) ^ j * u * v * w * M ^ c * α * S
      = ((2 : ℝ) ^ j * u * v * w * M ^ c) * (α * S) := by ring
    _ ≤ (2 ^ 45 * M ^ 40) * ((α + 1) * S) :=
        mul_le_mul h1 hαS (by positivity) hbig
    _ ≤ (2 ^ 48 * M ^ 40 + 8) * ((α + 1) * S) :=
        mul_le_mul_of_nonneg_right h3 (by nlinarith)
    _ = (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by ring

/-- The final shape of the per-field comparison. -/
theorem sum_le_final {M S α Z : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α)
    (hZ : Z ≤ 6 * ((2 ^ 48 * M ^ 40 + 8) * (α + 1) * S)) :
    Z ≤ 8 * ((2 ^ 48 * M ^ 40 + 8) * (α + 1) * S) := by
  nlinarith [hZ, mul_nonneg (by positivity : (0:ℝ) ≤ 2 ^ 48 * M ^ 40 + 8)
    (by nlinarith : (0:ℝ) ≤ (α + 1) * S)]

/-- A monomial is dominated by the unit budget. -/
theorem mono_le_unit {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α)
    {j : ℕ} (hj : j ≤ 45) {c : ℕ} (hc : c ≤ 37) {u v w : ℝ}
    (hu0 : 0 ≤ u) (huM : u ≤ M) (hv0 : 0 ≤ v) (hvM : v ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M) :
    (2 : ℝ) ^ j * u * v * w * M ^ c * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S := by
  have h1 : (2 : ℝ) ^ j * u * v * w * M ^ c ≤ 2 ^ 45 * M ^ 40 :=
    mono3_le_big hM hj hc hu0 huM hv0 hvM hw0 hwM
  have hS1 : S ≤ (α + 1) * S := by nlinarith
  calc (2 : ℝ) ^ j * u * v * w * M ^ c * S ≤ (2 ^ 45 * M ^ 40) * S :=
        mul_le_mul_of_nonneg_right h1 hS
    _ ≤ (2 ^ 45 * M ^ 40) * ((α + 1) * S) :=
        mul_le_mul_of_nonneg_left hS1 (by positivity)
    _ = (2 ^ 45 * M ^ 40) * (α + 1) * S := by ring

/-- A monomial with one factor of `α` is dominated by the unit budget. -/
theorem mono_le_unit_alpha {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α)
    {j : ℕ} (hj : j ≤ 45) {c : ℕ} (hc : c ≤ 37) {u v w : ℝ}
    (hu0 : 0 ≤ u) (huM : u ≤ M) (hv0 : 0 ≤ v) (hvM : v ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M) :
    (2 : ℝ) ^ j * u * v * w * M ^ c * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S := by
  have h1 : (2 : ℝ) ^ j * u * v * w * M ^ c ≤ 2 ^ 45 * M ^ 40 :=
    mono3_le_big hM hj hc hu0 huM hv0 hvM hw0 hwM
  have hαS : α * S ≤ (α + 1) * S := by nlinarith
  calc (2 : ℝ) ^ j * u * v * w * M ^ c * α * S
      = ((2 : ℝ) ^ j * u * v * w * M ^ c) * (α * S) := by ring
    _ ≤ (2 ^ 45 * M ^ 40) * ((α + 1) * S) :=
        mul_le_mul h1 hαS (by positivity) (by positivity)
    _ = (2 ^ 45 * M ^ 40) * (α + 1) * S := by ring

/-- Eight units fit into the final constant. -/
theorem eight_unit_le {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α) :
    8 * ((2 ^ 45 * M ^ 40) * (α + 1) * S) ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have hM0 : 0 ≤ M := by linarith
  have hM40 : (0 : ℝ) ≤ M ^ 40 := pow_nonneg hM0 40
  have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
  have h7 : (8 : ℝ) * 2 ^ 45 ≤ 2 ^ 48 := by norm_num
  have h8 : 8 * 2 ^ 45 * M ^ 40 ≤ 2 ^ 48 * M ^ 40 :=
    mul_le_mul_of_nonneg_right h7 hM40
  have h9 : 8 * 2 ^ 45 * M ^ 40 * (α + 1) ≤ 2 ^ 48 * M ^ 40 * (α + 1) :=
    mul_le_mul_of_nonneg_right h8 hα1
  have h10 : 2 ^ 48 * M ^ 40 * (α + 1) ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) :=
    mul_le_mul_of_nonneg_right (by linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 ^ 48) hM40])
      hα1
  calc 8 * ((2 ^ 45 * M ^ 40) * (α + 1) * S) = (8 * 2 ^ 45 * M ^ 40) * (α + 1) * S := by ring
    _ ≤ (2 ^ 48 * M ^ 40) * (α + 1) * S := mul_le_mul_of_nonneg_right h9 hS
    _ ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := mul_le_mul_of_nonneg_right h10 hS


end Work.FTS.StrongPersist
