/-
# `FTS_RegExport/RXT/starVop.lean` — the `min z 1`-bound on `𝒱(Φ̃_*)` and its derivatives

The field `VzW` of `Work.FTS.VocabO2.StarPkgo2` bounds the *weighted* coefficient

  `W = ((z+1)/z)·𝒱(Φ̃_*)`,   `𝒱 = Vop (PhiTs α Φs)`,

in `𝒲^{4,∞}` (`WlInfMem α 4 W`, `WlInf α 4 W ≤ Cs·α`), while the row-19 consumer asks for a
pointwise bound on **`D_z^j D_θ^i 𝒱`** for `j + i ≤ 2` **carrying a `min z 1` factor**, i.e. the
vanishing of `𝒱` and of its low-order derivatives at `z = 0⁺`.

The two are related by the elementary z-only factor `A(z) = z/(1+z)`: `𝒱 = A(z)·W` on `z ≠ 0`
(see `RXT/StarVopAux.lean`), so that every `z`-derivative of `𝒱` acquires the factor `A`, or the
Stirling factors `z·A' = z/(1+z)²` resp. `z·(z·A')' = z(1-z)/(1+z)³`, all of which are `≤ min z 1`
on `z > 0`:

* `D_θ^i 𝒱 = A·D_θ^i W`                                   (`DthIter_eq_mul`),
* `D_z D_θ^i 𝒱 = (z/(1+z)²)·D_θ^i W + A·D_z D_θ^i W`       (`DzIter_one_eq_mul`),
* `D_z²D_θ^i 𝒱 = (z(1-z)/(1+z)³)·D_θ^i W + 2(z/(1+z)²)·D_z D_θ^i W + A·D_z²D_θ^i W`
                                                          (`DzIter_two_eq_mul`),

while the `W`-side is bounded uniformly by `mixed_two_le_WlInf` (`RXT/StarVopWlInf.lean`):

  `|D_z^k D_θ^i W| ≤ 4·WlInf α 4 W`   for `k ≤ 2`, `i ≤ 2`.

Each `W`-derivative therefore contributes `4·WlInf α 4 W ≤ 4·Cs·α ≤ 4·max Cs 1·α`, and each
`A`/`B`/`C` factor contributes `min z 1`; summing the (at most three) terms gives the constant
`16` of `starVop`.  The smoothness of `𝒱` and `W` on the open quadrant (used by the product
rules) comes from `Work.FTS.PhiStar.CoreAux.fields_smooth` (for `Φ̃_* = PhiTs α Φs`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs_lipschitz
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.VsFields
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.PhiStar.CoreAux.fields_smooth
import Submission.Work.FTS_RegExport.RXT.StarVopAux
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-- the coefficient `𝒱(Φ̃_*)` of the self-similar vorticity equation (row 19) -/
def Vof (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)

/-- the weighted coefficient `((z+1)/z)·𝒱(Φ̃_*)` whose `𝒲^{4,∞}`-norm is the field `VzW` of
`VocabO2.StarPkgo2` -/
def Wof (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => (z + 1) / z * Vof α Φs z θ

theorem starVop {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ C * (max Cs 1 * α) * min z 1 := by
  have hsm := Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hS.smooth
  have hWsm : Work.FTS.EllipticEst.SmoothOpen (Wof α Φs) := hsm.2.2.2.1
  have hWmem : Work.Spaces.WlInfMem α 4 (Wof α Φs) := hS.VzW.1
  have hWle : Work.Spaces.WlInf α 4 (Wof α Φs) ≤ Cs * α := hS.VzW.2
  have hW₀nn : 0 ≤ Work.Spaces.WlInf α 4 (Wof α Φs) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 (Wof α Φs) hWmem)
      (Work.Spaces.wlThSum_nonneg α 4 (Wof α Φs) hWmem)
  have hCs : Cs ≤ max Cs 1 := le_max_left _ _
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Vof α Φs z θ = z / (1 + z) * Wof α Φs z θ := by
    intro z θ hz hθ0 hθ1
    show Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        = z / (1 + z) * ((z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    field_simp
    try ring
  refine ⟨16, by norm_num, ?_⟩
  intro j i hji z θ hz hθ0 hθ1
  have hj2 : j ≤ 2 := by omega
  have hi2 : i ≤ 2 := by omega
  have hminnn : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hA := affine_bound hz
  have hB := quad_bound hz
  have hC := cubic_bound hz
  have hWle16 : 4 * Work.Spaces.WlInf α 4 (Wof α Φs) ≤ 16 * (max Cs 1 * α) := by
    nlinarith [hWle, hCs, hα.le]
  have hmix := mixed_two_le_WlInf hα hα1 hWsm hWmem
  show |Work.Spaces.mixed j i (Vof α Φs) z θ| ≤ 16 * (max Cs 1 * α) * min z 1
  interval_cases j
  · -- j = 0: `D_θ^i 𝒱 = A·D_θ^i W`
    interval_cases i
    · have h1 := DthIter_eq_mul hid hWsm 0 (by norm_num) z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 0 (Wof α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 0 0 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 0 (Vof α Φs) z θ
          = Work.Spaces.DthIter 0 (Vof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 0 (Wof α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 0 (Wof α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
    · have h1 := DthIter_eq_mul hid hWsm 1 (by norm_num) z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 1 (Wof α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 0 1 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 1 (Vof α Φs) z θ
          = Work.Spaces.DthIter 1 (Vof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 1 (Wof α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 1 (Wof α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
    · have h1 := DthIter_eq_mul hid hWsm 2 (by norm_num) z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 2 (Wof α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 0 2 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 2 (Vof α Φs) z θ
          = Work.Spaces.DthIter 2 (Vof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 2 (Wof α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 2 (Wof α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
  · -- j = 1: `D_z D_θ^i 𝒱 = B·D_θ^i W + A·D_z D_θ^i W`
    have hi1 : i ≤ 1 := by omega
    have hid' : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        Work.Spaces.DthIter i (Vof α Φs) z' θ'
          = z' / (1 + z') * Work.Spaces.DthIter i (Wof α Φs) z' θ' :=
      fun z' θ' hz' hθ' hθ'' => DthIter_eq_mul hid hWsm i hi2 z' θ' hz' hθ' hθ''
    have h1 := DzIter_one_eq_mul hid' (hWsm.DthIter i) z θ hz hθ0 hθ1
    have h2 : |Work.Spaces.DthIter i (Wof α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 0 i (by norm_num) hi2 z θ hz hθ0 hθ1
    have h3 : |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Wof α Φs)) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 1 i (by norm_num) hi2 z θ hz hθ0 hθ1
    rw [show Work.Spaces.mixed 1 i (Vof α Φs) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Vof α Φs)) z θ from rfl]
    rw [h1]
    calc |z / (1 + z) ^ 2 * Work.Spaces.DthIter i (Wof α Φs) z θ
            + z / (1 + z) * Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Wof α Φs)) z θ|
        ≤ |z / (1 + z) ^ 2 * Work.Spaces.DthIter i (Wof α Φs) z θ|
            + |z / (1 + z)
                * Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Wof α Φs)) z θ| := abs_add_le _ _
      _ = |z / (1 + z) ^ 2| * |Work.Spaces.DthIter i (Wof α Φs) z θ|
            + |z / (1 + z)|
              * |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Wof α Φs)) z θ| := by
          rw [abs_mul, abs_mul]
      _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs))
            + min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) :=
          add_le_add (mul_le_mul hB h2 (abs_nonneg _) hminnn)
            (mul_le_mul hA h3 (abs_nonneg _) hminnn)
      _ = (8 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
      _ ≤ (16 * (max Cs 1 * α)) * min z 1 := by
          refine mul_le_mul_of_nonneg_right ?_ hminnn
          nlinarith [hWle, hCs, hα.le]
      _ = 16 * (max Cs 1 * α) * min z 1 := by ring
  · -- j = 2, hence i = 0
    have hi0 : i = 0 := by omega
    subst hi0
    have h1 := DzIter_two_eq_mul hid hWsm z θ hz hθ0 hθ1
    have h2 : |Wof α Φs z θ| ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) :=
      hmix 0 0 (by norm_num) (by norm_num) z θ hz hθ0 hθ1
    have h3 : |Work.Spaces.DzIter 1 (Wof α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 1 0 (by norm_num) (by norm_num)
          z θ hz hθ0 hθ1
    have h4 : |Work.Spaces.DzIter 2 (Wof α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (Wof α Φs) := hmix 2 0 (by norm_num) (by norm_num)
          z θ hz hθ0 hθ1
    rw [show Work.Spaces.mixed 2 0 (Vof α Φs) z θ = Work.Spaces.DzIter 2 (Vof α Φs) z θ
        from rfl]
    rw [h1]
    calc |z * (1 - z) / (1 + z) ^ 3 * Wof α Φs z θ
            + 2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (Wof α Φs) z θ
            + z / (1 + z) * Work.Spaces.DzIter 2 (Wof α Φs) z θ|
        ≤ |z * (1 - z) / (1 + z) ^ 3 * Wof α Φs z θ|
            + |2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (Wof α Φs) z θ|
            + |z / (1 + z) * Work.Spaces.DzIter 2 (Wof α Φs) z θ| := by
          refine le_trans (abs_add_le _ _) ?_
          exact add_le_add (abs_add_le _ _) (le_refl _)
      _ = |z * (1 - z) / (1 + z) ^ 3| * |Wof α Φs z θ|
            + |2 * (z / (1 + z) ^ 2)| * |Work.Spaces.DzIter 1 (Wof α Φs) z θ|
            + |z / (1 + z)| * |Work.Spaces.DzIter 2 (Wof α Φs) z θ| := by
          have habs1 : |z * (1 - z) / (1 + z) ^ 3 * Wof α Φs z θ|
              = |z * (1 - z) / (1 + z) ^ 3| * |Wof α Φs z θ| := abs_mul _ _
          have habs2 : |2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (Wof α Φs) z θ|
              = |2 * (z / (1 + z) ^ 2)| * |Work.Spaces.DzIter 1 (Wof α Φs) z θ| :=
            abs_mul _ _
          have habs3 : |z / (1 + z) * Work.Spaces.DzIter 2 (Wof α Φs) z θ|
              = |z / (1 + z)| * |Work.Spaces.DzIter 2 (Wof α Φs) z θ| := abs_mul _ _
          rw [habs1, habs2, habs3]
      _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs))
            + (2 * min z 1) * (4 * Work.Spaces.WlInf α 4 (Wof α Φs))
            + min z 1 * (4 * Work.Spaces.WlInf α 4 (Wof α Φs)) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul hC h2 (abs_nonneg _) hminnn
          · refine mul_le_mul ?_ h3 (abs_nonneg _) (by positivity)
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            exact mul_le_mul_of_nonneg_left hB (by norm_num)
          · exact mul_le_mul hA h4 (abs_nonneg _) hminnn
      _ = (16 * Work.Spaces.WlInf α 4 (Wof α Φs)) * min z 1 := by ring
      _ ≤ (16 * (max Cs 1 * α)) * min z 1 := by
          refine mul_le_mul_of_nonneg_right ?_ hminnn
          nlinarith [hWle, hCs, hα.le]
      _ = 16 * (max Cs 1 * α) * min z 1 := by ring

end Work.FTS_RegExport.RXT
