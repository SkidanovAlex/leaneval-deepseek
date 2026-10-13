/-
# `FTS_RegExport/RXT/StarVopAux.lean` — the factor `A(z) = z/(1+z)` and the Leibniz rules

The field `VzW` of `Work.FTS.VocabO2.StarPkgo2` bounds the *weighted* coefficient

  `W = ((z+1)/z)·𝒱(Φ̃_*)`,   `𝒱 = Vop (PhiTs α Φs)`,

in `𝒲^{4,∞}`, while the row-19 consumer asks for a pointwise bound on `D_z^j D_θ^i 𝒱`
(`j + i ≤ 2`) **carrying a `min z 1` factor**, i.e. the vanishing of `𝒱` and of its low-order
derivatives at `z = 0⁺`.  This module supplies the elementary machinery relating the two:
the z-only factor `A(z) = z/(1+z)` with `𝒱 = A·W`, its derivatives `B = z·A' = z/(1+z)²` and
`z·B' = z(1-z)/(1+z)³` (all `≤ min z 1` on `z > 0`), and the Leibniz rules

* `D_θ^i (A·X) = A·D_θ^i X`                                             (`DthIter_mul_zonly`),
* `D_z (A·X) = B·X + A·D_z X`                                            (`DzIter_one_mul_zonly`),
* `D_z² (A·X) = (z·B')·X + 2B·D_z X + A·D_z² X`                           (`DzIter_two_mul_zonly`),

together with their transfer to a pair `(V, W)` with `V = A·W` on the open quadrant
(`DthIter_eq_mul`, `DzIter_one_eq_mul`, `DzIter_two_eq_mul`).

The target theorem `starVop` and the bound `mixed_two_le_WlInf` on the `W`-side live in
`RXT.starVop` resp. `RXT.StarVopWlInf`.  Everything here is `sorry`-free and rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs

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

/-! ## Part 1 — the elementary factor `A(z) = z/(1+z)` and its derivatives -/

/-- `A'(z) = 1/(1+z)²` for `A(z) = z/(1+z)`. -/
theorem hasDerivAt_affine {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y / (1 + y)) (1 / (1 + z) ^ 2) z := by
  have hne : (1 + z) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) + y) (1 : ℝ) z :=
    (hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_id z)
  have h := h1.div h2 hne
  rw [show ((fun y : ℝ => y) / (fun y : ℝ => (1 : ℝ) + y))
      = (fun y : ℝ => y / (1 + y)) from rfl] at h
  rw [show (1 : ℝ) * (1 + z) - z * 1 = 1 by ring] at h
  exact h

/-- `B'(z) = (1-z)/(1+z)³` for `B(z) = z/(1+z)²`. -/
theorem hasDerivAt_quad {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y / (1 + y) ^ 2) ((1 - z) / (1 + z) ^ 3) z := by
  have hne : ((1 : ℝ) + z) ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => ((1 : ℝ) + y) ^ 2) (2 * (1 + z) ^ (2 - 1) * 1) z :=
    ((hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_id z)).pow 2
  have h := h1.div h2 hne
  rw [show ((fun y : ℝ => y) / (fun y : ℝ => ((1 : ℝ) + y) ^ 2))
      = (fun y : ℝ => y / (1 + y) ^ 2) from rfl] at h
  rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one, mul_one] at h
  rw [show (1 * (1 + z) ^ 2 - z * (2 * (1 + z))) / ((1 + z) ^ 2) ^ 2
      = (1 - z) / (1 + z) ^ 3 by
    field_simp
    ring] at h
  exact h

/-- `|A(z)| = |z/(1+z)| ≤ min z 1` for `z > 0`. -/
theorem affine_bound {z : ℝ} (hz : 0 < z) : |z / (1 + z)| ≤ min z 1 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ z / (1 + z))]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [div_le_one h1]; linarith

/-- `|z/(1+z)²| ≤ min z 1` for `z > 0`. -/
theorem quad_bound {z : ℝ} (hz : 0 < z) : |z / (1 + z) ^ 2| ≤ min z 1 := by
  have h2 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ z / (1 + z) ^ 2)]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h2]; nlinarith [sq_nonneg z, hz]
  · rw [div_le_one h2]; nlinarith [sq_nonneg z, hz]

/-- `|z(1-z)/(1+z)³| ≤ min z 1` for `z > 0`. -/
theorem cubic_bound {z : ℝ} (hz : 0 < z) : |z * (1 - z) / (1 + z) ^ 3| ≤ min z 1 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hzabs : |1 - z| ≤ 1 + z := by
    rw [abs_le]; constructor <;> linarith
  have hcube : (1 + z) ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg (1 + z)]
  have hsq : z ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg (1 + z), hz]
  have hval : |z * (1 - z) / (1 + z) ^ 3| = z * |1 - z| / (1 + z) ^ 3 := by
    rw [abs_div, abs_mul, abs_of_nonneg hz.le, abs_of_pos h2]
  rw [hval]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h2]
    nlinarith [hzabs, hcube, hz]
  · rw [div_le_one h2]
    nlinarith [hzabs, hsq, hz, mul_le_mul_of_nonneg_left hzabs hz.le]

/-! ## Part 2 — the Leibniz rules for `D_θ^i` and `D_z^j` against the z-only factor -/

/-- `D_θ` commutes with multiplication by a function of `z` alone:
`D_θ^i (A·X) = A·D_θ^i X` for `A = A(z)`, `i ≤ 2`. -/
theorem DthIter_mul_zonly {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    ∀ i : ℕ, i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i (fun z θ => z / (1 + z) * X z θ) z θ
        = z / (1 + z) * Work.Spaces.DthIter i X z θ := by
  intro i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  interval_cases i
  · rfl
  · have hdiff : DifferentiableAt ℝ (fun θ' : ℝ => X z θ') θ :=
      ((hX.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
    have hder : deriv (fun θ' : ℝ => z / (1 + z) * X z θ') θ
        = z / (1 + z) * deriv (fun θ' : ℝ => X z θ') θ :=
      deriv_const_mul (z / (1 + z)) hdiff
    show Real.sin (2 * θ) * deriv (fun θ' : ℝ => z / (1 + z) * X z θ') θ
        = z / (1 + z) * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => X z θ') θ)
    rw [hder]; ring
  · have hev : (fun θ' : ℝ => Work.Spaces.DthIter 1
          (fun z θ => z / (1 + z) * X z θ) z θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => z / (1 + z) * Work.Spaces.DthIter 1 X z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact DthIter_mul_zonly hX 1 (by norm_num) z θ' hz hθ'.1 hθ'.2
    have hdiff : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.DthIter 1 X z θ') θ :=
      (((hX.DthIter 1).curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)
    have hL : Work.Spaces.DthIter 2 (fun z θ => z / (1 + z) * X z θ) z θ
        = Real.sin (2 * θ) * (z / (1 + z)
            * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1 X z θ') θ) := by
      rw [show Work.Spaces.DthIter 2 (fun z θ => z / (1 + z) * X z θ) z θ
          = Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1
              (fun z θ => z / (1 + z) * X z θ) z θ') θ from rfl]
      rw [hev.deriv_eq, deriv_const_mul (z / (1 + z)) hdiff]
    have hR : Work.Spaces.DthIter 2 X z θ
        = Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1 X z θ') θ := rfl
    rw [hL, hR]; ring

/-- `D_z (A·X) = (z/(1+z)²)·X + A·D_z X` for `A = A(z)`. -/
theorem DzIter_one_mul_zonly {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * X z θ) z θ
        = z / (1 + z) ^ 2 * X z θ + z / (1 + z) * Work.Spaces.DzIter 1 X z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hX' : HasDerivAt (fun z' : ℝ => X z' θ) (Work.Spaces.pzIter 1 X z θ) z :=
    hX.hasDerivAt_slice hθ hz
  have hmul := (hasDerivAt_affine hz).mul hX'
  have hder : deriv (fun z' : ℝ => z' / (1 + z') * X z' θ) z
      = (1 / (1 + z) ^ 2) * X z θ + z / (1 + z) * Work.Spaces.pzIter 1 X z θ := hmul.deriv
  show z * deriv (fun z' : ℝ => z' / (1 + z') * X z' θ) z
      = z / (1 + z) ^ 2 * X z θ + z / (1 + z) * (z * Work.Spaces.pzIter 1 X z θ)
  rw [hder]
  ring_nf

/-- `D_z²(A·X) = (z(1-z)/(1+z)³)·X + 2(z/(1+z)²)·D_z X + A·D_z²X` for `A = A(z)`. -/
theorem DzIter_two_mul_zonly {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 2 (fun z θ => z / (1 + z) * X z θ) z θ
        = z * (1 - z) / (1 + z) ^ 3 * X z θ
          + 2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 X z θ
          + z / (1 + z) * Work.Spaces.DzIter 2 X z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * X z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ
        + z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact DzIter_one_mul_zonly hX z' θ hz' hθ0 hθ1
  have h1 : deriv (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ) z
      = ((1 - z) / (1 + z) ^ 3) * X z θ + z / (1 + z) ^ 2 * Work.Spaces.pzIter 1 X z θ :=
    ((hasDerivAt_quad hz).mul (hX.hasDerivAt_slice hθ hz)).deriv
  have h2 : deriv (fun z' : ℝ => z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) z
      = (1 / (1 + z) ^ 2) * (z * Work.Spaces.pzIter 1 X z θ)
          + z / (1 + z) * Work.Spaces.pzIter 1 (Work.Spaces.DzIter 1 X) z θ :=
    ((hasDerivAt_affine hz).mul ((hX.DzIter 1).hasDerivAt_slice hθ hz)).deriv
  have hd1 : DifferentiableAt ℝ (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ) z :=
    ((hasDerivAt_quad hz).mul (hX.hasDerivAt_slice hθ hz)).differentiableAt
  have hd2 : DifferentiableAt ℝ
      (fun z' : ℝ => z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) z :=
    ((hasDerivAt_affine hz).mul ((hX.DzIter 1).hasDerivAt_slice hθ hz)).differentiableAt
  have hder : deriv (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ
        + z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) z
      = ((1 - z) / (1 + z) ^ 3) * X z θ + z / (1 + z) ^ 2 * Work.Spaces.pzIter 1 X z θ
        + ((1 / (1 + z) ^ 2) * (z * Work.Spaces.pzIter 1 X z θ)
            + z / (1 + z) * Work.Spaces.pzIter 1 (Work.Spaces.DzIter 1 X) z θ) := by
    rw [show deriv (fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ
          + z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ) z
        = deriv ((fun z' : ℝ => z' / (1 + z') ^ 2 * X z' θ)
            + (fun z' : ℝ => z' / (1 + z') * Work.Spaces.DzIter 1 X z' θ)) z from rfl,
      deriv_add hd1 hd2, h1, h2]
  show z * deriv (fun z' : ℝ => Work.Spaces.DzIter 1
        (fun z θ => z / (1 + z) * X z θ) z' θ) z
      = z * (1 - z) / (1 + z) ^ 3 * X z θ
        + 2 * (z / (1 + z) ^ 2) * (z * Work.Spaces.pzIter 1 X z θ)
        + z / (1 + z) * (z * Work.Spaces.pzIter 1 (Work.Spaces.DzIter 1 X) z θ)
  rw [hev.deriv_eq, hder]
  ring_nf

/-! ## Part 3 — transfer of the Leibniz rules to `𝒱 = A·W`

The three lemmas below state the identities for a pair `(V, W)` related by the algebraic
identity `V = A(z)·W` (on the open quadrant).  They are used with `(V, W) = (𝒱(Φ̃_*), W)`
and with `(V, W) = (D_θ^i 𝒱(Φ̃_*), D_θ^i W)`. -/

/-- `D_θ^i V = A·D_θ^i W` for `i ≤ 2`, when `V = A·W` on the open quadrant. -/
theorem DthIter_eq_mul {V W : ℝ → ℝ → ℝ}
    (hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → V z θ = z / (1 + z) * W z θ)
    (hW : Work.FTS.EllipticEst.SmoothOpen W) :
    ∀ i : ℕ, i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i V z θ = z / (1 + z) * Work.Spaces.DthIter i W z θ := by
  intro i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  interval_cases i
  · exact hid z θ hz hθ0 hθ1
  · have hev : (fun θ' : ℝ => V z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => z / (1 + z) * W z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact hid z θ' hz hθ'.1 hθ'.2
    have hdiff : DifferentiableAt ℝ (fun θ' : ℝ => W z θ') θ :=
      ((hW.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
    show Real.sin (2 * θ) * deriv (fun θ' : ℝ => V z θ') θ
        = z / (1 + z) * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => W z θ') θ)
    rw [hev.deriv_eq, deriv_const_mul (z / (1 + z)) hdiff]
    ring
  · have hev : (fun θ' : ℝ => Work.Spaces.DthIter 1 V z θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => z / (1 + z) * Work.Spaces.DthIter 1 W z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact DthIter_eq_mul hid hW 1 (by norm_num) z θ' hz hθ'.1 hθ'.2
    have hdiff : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.DthIter 1 W z θ') θ :=
      (((hW.DthIter 1).curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)
    have hL : Work.Spaces.DthIter 2 V z θ
        = Real.sin (2 * θ) * (z / (1 + z)
            * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1 W z θ') θ) := by
      rw [show Work.Spaces.DthIter 2 V z θ
          = Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1 V z θ') θ from rfl]
      rw [hev.deriv_eq, deriv_const_mul (z / (1 + z)) hdiff]
    have hR : Work.Spaces.DthIter 2 W z θ
        = Real.sin (2 * θ) * deriv (fun θ' : ℝ => Work.Spaces.DthIter 1 W z θ') θ := rfl
    rw [hL, hR]; ring

/-- `D_z V = (z/(1+z)²)·W + A·D_z W` when `V = A·W` on the open quadrant. -/
theorem DzIter_one_eq_mul {V W : ℝ → ℝ → ℝ}
    (hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → V z θ = z / (1 + z) * W z θ)
    (hW : Work.FTS.EllipticEst.SmoothOpen W) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 V z θ
        = z / (1 + z) ^ 2 * W z θ + z / (1 + z) * Work.Spaces.DzIter 1 W z θ := by
  intro z θ hz hθ0 hθ1
  have hA := DzIter_one_mul_zonly hW z θ hz hθ0 hθ1
  have hev : (fun z' : ℝ => V z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => z' / (1 + z') * W z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hid z' θ hz' hθ0 hθ1
  rw [show Work.Spaces.DzIter 1 V z θ = z * Work.Spaces.pz V z θ from rfl]
  rw [show Work.Spaces.pz V z θ
      = Work.Spaces.pz (fun z θ => z / (1 + z) * W z θ) z θ from hev.deriv_eq]
  rw [← show Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * W z θ) z θ
      = z * Work.Spaces.pz (fun z θ => z / (1 + z) * W z θ) z θ from rfl]
  exact hA

/-- `D_z² V = (z(1-z)/(1+z)³)·W + 2(z/(1+z)²)·D_z W + A·D_z² W` when `V = A·W`. -/
theorem DzIter_two_eq_mul {V W : ℝ → ℝ → ℝ}
    (hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → V z θ = z / (1 + z) * W z θ)
    (hW : Work.FTS.EllipticEst.SmoothOpen W) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 2 V z θ
        = z * (1 - z) / (1 + z) ^ 3 * W z θ
          + 2 * (z / (1 + z) ^ 2) * Work.Spaces.DzIter 1 W z θ
          + z / (1 + z) * Work.Spaces.DzIter 2 W z θ := by
  intro z θ hz hθ0 hθ1
  have hgen := DzIter_two_mul_zonly hW z θ hz hθ0 hθ1
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 1 V z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.DzIter 1
        (fun z θ => z / (1 + z) * W z θ) z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [DzIter_one_eq_mul hid hW z' θ hz' hθ0 hθ1,
      DzIter_one_mul_zonly hW z' θ hz' hθ0 hθ1]
  rw [show Work.Spaces.DzIter 2 V z θ
      = z * Work.Spaces.pz (Work.Spaces.DzIter 1 V) z θ from rfl]
  rw [show Work.Spaces.pz (Work.Spaces.DzIter 1 V) z θ
      = Work.Spaces.pz (Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * W z θ)) z θ
      from hev.deriv_eq]
  rw [← show Work.Spaces.DzIter 2 (fun z θ => z / (1 + z) * W z θ) z θ
      = z * Work.Spaces.pz (Work.Spaces.DzIter 1 (fun z θ => z / (1 + z) * W z θ)) z θ
      from rfl]
  exact hgen

end Work.FTS_RegExport.RXT
