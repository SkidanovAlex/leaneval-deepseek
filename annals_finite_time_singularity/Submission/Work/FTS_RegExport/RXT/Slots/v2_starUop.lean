import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_RegExport.RXT.StarVopAux
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS.PhiStar.CoreAux.fields_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Slots.v2_starUop`

The pointwise regularity of the coefficient `𝒰(Φ̃_*)/sin 2θ` of the self-similar vorticity
equation, in the form consumed by the regularity-export (`RXT`) cone.

The field `UszW` of the star package `Work.FTS.VocabO2.StarPkgo2 α Cs Φs` bounds the
*weighted* coefficient

  `W = ((z+1)/z)·𝒰(Φ̃_*)/sin 2θ`,   `𝒰 = Uop α (PhiTs α Φs)`,

in `𝒲^{4,∞}` (`WlInfMem α 4 W`, `WlInf α 4 W ≤ Cs·α`), whereas the consumer asks for a
pointwise bound on the mixed derivatives `D_z^j D_θ^i (𝒰/sin 2θ)`, `j + i ≤ 2`, **carrying a
`min z 1` factor** — i.e. the vanishing of `𝒰/sin 2θ` and its low-order derivatives at
`z = 0⁺`.

The two are related by the elementary `z`-only factor `A(z) = z/(1+z)`:

  `𝒰/sin 2θ = A(z)·W`      on `z ≠ 0`

(trivially, since `A(z)·((z+1)/z) = 1`), so that every `z`-derivative acquires either the
factor `A`, or one of the Stirling factors `z·A' = z/(1+z)²`, `z·(z·A')' = z(1-z)/(1+z)³`, all
of which are `≤ min z 1` in modulus for `z > 0` (`RXT/StarVopAux.lean`,
`affine_bound`/`quad_bound`/`cubic_bound`):

* `D_θ^i (𝒰/sin 2θ) = A·D_θ^i W`                                       (`DthIter_eq_mul`),
* `D_z D_θ^i (𝒰/sin 2θ) = (z/(1+z)²)·D_θ^i W + A·D_z D_θ^i W`           (`DzIter_one_eq_mul`),
* `D_z² D_θ^i (𝒰/sin 2θ) = (z(1-z)/(1+z)³)·D_θ^i W + 2(z/(1+z)²)·D_z D_θ^i W + A·D_z²D_θ^i W`
                                                                        (`DzIter_two_eq_mul`),

while the `W`-side is bounded uniformly by `mixed_two_le_WlInf` (`RXT/StarVopWlInf.lean`):

  `|D_z^k D_θ^i W| ≤ 4·WlInf α 4 W`   for `k ≤ 2`, `i ≤ 2`.

Each `W`-derivative contributes `4·WlInf α 4 W ≤ 4·Cs·α ≤ 4·max Cs 1·α` and each `A`/`B`/`C`
factor contributes `min z 1`, giving the constant `16`.

This is the `𝒰`-analogue of `Work.FTS_RegExport.RXT.starVop` (which treats `𝒱(Φ̃_*)`), and the
proof follows that file line by line.  The smoothness on the open quadrant used by the product
rules comes from `Work.FTS.PhiStar.CoreAux.fields_smooth`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false

/-- the coefficient `𝒰(Φ̃_*)/sin 2θ` of the self-similar vorticity equation (rows 14, 15) -/
def Uof (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ)

/-- the weighted coefficient `((z+1)/z)·𝒰(Φ̃_*)/sin 2θ` whose `𝒲^{4,∞}`-norm is the field
`UszW` of `VocabO2.StarPkgo2` -/
def WU (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  fun z θ => (z + 1) / z * Uof α Φs z θ

theorem v2_starUop {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop α
        (Work.FTS.Nonlin.PhiTs α Φs) z θ / Real.sin (2 * θ)) z θ|
        ≤ C * (max Cs 1 * α) * min z 1 := by
  have hsm := Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hS.smooth
  have hWsm : Work.FTS.EllipticEst.SmoothOpen (WU α Φs) := hsm.2.2.2.2.2.1
  have hWmem : Work.Spaces.WlInfMem α 4 (WU α Φs) := hS.UszW.1
  have hWle : Work.Spaces.WlInf α 4 (WU α Φs) ≤ Cs * α := hS.UszW.2
  have hCs : Cs ≤ max Cs 1 := le_max_left _ _
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Uof α Φs z θ = z / (1 + z) * WU α Φs z θ := by
    intro z θ hz hθ0 hθ1
    have h1 : (z : ℝ) ≠ 0 := ne_of_gt hz
    have h2 : (1 + z : ℝ) ≠ 0 := by linarith
    have hcoef : z / (1 + z) * ((z + 1) / z) = 1 := by
      rw [div_mul_div_comm, show (z : ℝ) * (z + 1) = (1 + z) * z from by ring]
      exact div_self (mul_ne_zero h2 h1)
    have hgoal : ∀ a : ℝ, a = z / (1 + z) * ((z + 1) / z * a) := by
      intro a
      rw [← mul_assoc, hcoef, one_mul]
    exact hgoal _
  refine ⟨16, by norm_num, ?_⟩
  intro j i hji z θ hz hθ0 hθ1
  have hj2 : j ≤ 2 := by omega
  have hi2 : i ≤ 2 := by omega
  have hminnn : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hA := Work.FTS_RegExport.RXT.affine_bound hz
  have hB := Work.FTS_RegExport.RXT.quad_bound hz
  have hC := Work.FTS_RegExport.RXT.cubic_bound hz
  have hmax1 : (1 : ℝ) ≤ max Cs 1 := le_max_right _ _
  have hmaxnn : 0 ≤ max Cs 1 * α := mul_nonneg (by linarith) hα.le
  have hWleM : 4 * Work.Spaces.WlInf α 4 (WU α Φs) ≤ 4 * (max Cs 1 * α) := by
    have h2 : 4 * (Cs * α) ≤ 4 * (max Cs 1 * α) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCs hα.le) (by norm_num)
    linarith [hWle, h2]
  have hWle16 : 4 * Work.Spaces.WlInf α 4 (WU α Φs) ≤ 16 * (max Cs 1 * α) := by
    nlinarith [hWleM, hmaxnn]
  have hWle8 : 8 * Work.Spaces.WlInf α 4 (WU α Φs) ≤ 16 * (max Cs 1 * α) := by
    nlinarith [hWleM, hmaxnn]
  have hmix := Work.FTS_RegExport.RXT.mixed_two_le_WlInf hα hα1 hWsm hWmem
  show |Work.Spaces.mixed j i (Uof α Φs) z θ| ≤ 16 * (max Cs 1 * α) * min z 1
  interval_cases j
  · -- j = 0: `D_θ^i (𝒰/sin 2θ) = A·D_θ^i W`
    interval_cases i
    · have h1 := Work.FTS_RegExport.RXT.DthIter_eq_mul hid hWsm 0 (by norm_num)
        z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 0 (WU α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 0 0 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 0 (Uof α Φs) z θ
          = Work.Spaces.DthIter 0 (Uof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 0 (WU α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 0 (WU α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
    · have h1 := Work.FTS_RegExport.RXT.DthIter_eq_mul hid hWsm 1 (by norm_num)
        z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 1 (WU α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 0 1 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 1 (Uof α Φs) z θ
          = Work.Spaces.DthIter 1 (Uof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 1 (WU α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 1 (WU α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
    · have h1 := Work.FTS_RegExport.RXT.DthIter_eq_mul hid hWsm 2 (by norm_num)
        z θ hz hθ0 hθ1
      have h2 : |Work.Spaces.DthIter 2 (WU α Φs) z θ|
          ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 0 2 (by norm_num) (by norm_num)
            z θ hz hθ0 hθ1
      rw [show Work.Spaces.mixed 0 2 (Uof α Φs) z θ
          = Work.Spaces.DthIter 2 (Uof α Φs) z θ from rfl]
      rw [h1]
      calc |z / (1 + z) * Work.Spaces.DthIter 2 (WU α Φs) z θ|
          = |z / (1 + z)| * |Work.Spaces.DthIter 2 (WU α Φs) z θ| := abs_mul _ _
        _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) :=
            mul_le_mul hA h2 (abs_nonneg _) hminnn
        _ = (4 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
        _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
            mul_le_mul_of_nonneg_right hWle16 hminnn
        _ = 16 * (max Cs 1 * α) * min z 1 := by ring
  · -- j = 1: `D_z D_θ^i (𝒰/sin 2θ) = B·D_θ^i W + A·D_z D_θ^i W`
    have hi1 : i ≤ 1 := by omega
    have hid' : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        Work.Spaces.DthIter i (Uof α Φs) z' θ'
          = z' / (1 + z') * Work.Spaces.DthIter i (WU α Φs) z' θ' :=
      fun z' θ' hz' hθ' hθ'' =>
        Work.FTS_RegExport.RXT.DthIter_eq_mul hid hWsm i hi2 z' θ' hz' hθ' hθ''
    have h1 := Work.FTS_RegExport.RXT.DzIter_one_eq_mul hid' (hWsm.DthIter i)
      z θ hz hθ0 hθ1
    have h2 : |Work.Spaces.DthIter i (WU α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 0 i (by norm_num) hi2
          z θ hz hθ0 hθ1
    have h3 : |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (WU α Φs)) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 1 i (by norm_num) hi2
          z θ hz hθ0 hθ1
    rw [show Work.Spaces.mixed 1 i (Uof α Φs) z θ
        = Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (Uof α Φs)) z θ from rfl]
    rw [h1]
    calc |z / (1 + z) ^ 2 * Work.Spaces.DthIter i (WU α Φs) z θ
            + z / (1 + z) * Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (WU α Φs)) z θ|
        ≤ |z / (1 + z) ^ 2 * Work.Spaces.DthIter i (WU α Φs) z θ|
            + |z / (1 + z)
                * Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (WU α Φs)) z θ| := abs_add_le _ _
      _ = |z / (1 + z) ^ 2| * |Work.Spaces.DthIter i (WU α Φs) z θ|
            + |z / (1 + z)|
              * |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i (WU α Φs)) z θ| := by
          rw [abs_mul, abs_mul]
      _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs))
            + min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) :=
          add_le_add (mul_le_mul hB h2 (abs_nonneg _) hminnn)
            (mul_le_mul hA h3 (abs_nonneg _) hminnn)
      _ = (8 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
      _ ≤ (16 * (max Cs 1 * α)) * min z 1 :=
          mul_le_mul_of_nonneg_right hWle8 hminnn
      _ = 16 * (max Cs 1 * α) * min z 1 := by ring
  · -- j = 2, hence i = 0
    have hi0 : i = 0 := by omega
    subst hi0
    have h1 := Work.FTS_RegExport.RXT.DzIter_two_eq_mul hid hWsm z θ hz hθ0 hθ1
    have h2 : |WU α Φs z θ| ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) :=
      hmix 0 0 (by norm_num) (by norm_num) z θ hz hθ0 hθ1
    have h3 : |Work.Spaces.DzIter 1 (WU α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 1 0 (by norm_num) (by norm_num)
          z θ hz hθ0 hθ1
    have h4 : |Work.Spaces.DzIter 2 (WU α Φs) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 (WU α Φs) := hmix 2 0 (by norm_num) (by norm_num)
          z θ hz hθ0 hθ1
    rw [show Work.Spaces.mixed 2 0 (Uof α Φs) z θ = Work.Spaces.DzIter 2 (Uof α Φs) z θ
        from rfl]
    rw [h1]
    calc |z * (1 - z) / (1 + z) ^ 3 * WU α Φs z θ
            + 2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (WU α Φs) z θ
            + z / (1 + z) * Work.Spaces.DzIter 2 (WU α Φs) z θ|
        ≤ |z * (1 - z) / (1 + z) ^ 3 * WU α Φs z θ|
            + |2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (WU α Φs) z θ|
            + |z / (1 + z) * Work.Spaces.DzIter 2 (WU α Φs) z θ| := by
          refine le_trans (abs_add_le _ _) ?_
          exact add_le_add (abs_add_le _ _) (le_refl _)
      _ = |z * (1 - z) / (1 + z) ^ 3| * |WU α Φs z θ|
            + |2 * (z / (1 + z) ^ 2)| * |Work.Spaces.DzIter 1 (WU α Φs) z θ|
            + |z / (1 + z)| * |Work.Spaces.DzIter 2 (WU α Φs) z θ| := by
          have habs1 : |z * (1 - z) / (1 + z) ^ 3 * WU α Φs z θ|
              = |z * (1 - z) / (1 + z) ^ 3| * |WU α Φs z θ| := abs_mul _ _
          have habs2 : |2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 (WU α Φs) z θ|
              = |2 * (z / (1 + z) ^ 2)| * |Work.Spaces.DzIter 1 (WU α Φs) z θ| :=
            abs_mul _ _
          have habs3 : |z / (1 + z) * Work.Spaces.DzIter 2 (WU α Φs) z θ|
              = |z / (1 + z)| * |Work.Spaces.DzIter 2 (WU α Φs) z θ| := abs_mul _ _
          rw [habs1, habs2, habs3]
      _ ≤ min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs))
            + (2 * min z 1) * (4 * Work.Spaces.WlInf α 4 (WU α Φs))
            + min z 1 * (4 * Work.Spaces.WlInf α 4 (WU α Φs)) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul hC h2 (abs_nonneg _) hminnn
          · refine mul_le_mul ?_ h3 (abs_nonneg _) (by positivity)
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            exact mul_le_mul_of_nonneg_left hB (by norm_num)
          · exact mul_le_mul hA h4 (abs_nonneg _) hminnn
      _ = (16 * Work.Spaces.WlInf α 4 (WU α Φs)) * min z 1 := by ring
      _ ≤ (16 * (max Cs 1 * α)) * min z 1 := by
          refine mul_le_mul_of_nonneg_right ?_ hminnn
          linarith [hWleM]
      _ = 16 * (max Cs 1 * α) * min z 1 := by ring

end Work.FTS_RegExport.RXT.Slots
