import Mathlib
import Submission.Work.Core.Defs
import Submission.Work.Nijenhuis.antisymm

/-!
# `∂̄² = 0` for an integrable almost complex structure

This file proves `Work.Dbar.sq_zero`: the `(0,2)`-part `dbarSq J u X Y x` of `d(∂̄u)` vanishes
whenever the Nijenhuis tensor of `J` vanishes on an open set `U ∋ x`.

The proof has three ingredients, all collected in the auxiliary namespace `Work.Dbar.Aux`:

* `dbarSq_eq_cpair_dpartial`: for *any* field of endomorphisms `J` with `J² = -1` near `x` and any
  `C²` function `u`, `dbarSq J u X Y x` is `∂u` evaluated on the complexified Lie bracket
  `[Z_X, Z_Y]`, where `Z_X = X + iJX`, `Z_Y = Y + iJY`.  This is the product rule for `∂̄`: it uses
  the symmetry of the second derivative of `u` (`S2_cancel`), the evaluation of `∂̄u` on a `(0,1)`
  vector (`cpair_dbar_Z01`) and the product rule `czderiv_fderiv_apply`.
* `cbracket_Z01_eq_of_nijenhuis_zero`: if the Nijenhuis tensor vanishes at `x`, the complexified
  bracket of two `(0,1)` fields is again `(0,1)`, i.e. of the form `(A, J x A)`: the `(0,1)`
  distribution is involutive.
* `cpair_dpartial_self`: `∂u` annihilates `(0,1)` vectors.

The hypothesis `NijenhuisVanishesOn J U`, which quantifies over globally smooth vector fields, is
transferred to the fields that are only `C¹` at `x` in `nijenhuis_zero_of_vanishes`: the Nijenhuis
tensor is tensorial, so its value at `x` depends only on the pointwise values of its arguments, and
those can be realised by constant (globally smooth) fields.
-/


namespace Work.Dbar

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open scoped ContDiff Topology

variable {n : ℕ}

namespace Aux

/-! ### Elementary linearity of `cpair` -/

lemma cpair_add (om₁ om₂ : E n →L[ℝ] ℂ) (z : E n × E n) :
    cpair (om₁ + om₂) z = cpair om₁ z + cpair om₂ z := by
  simp only [cpair, add_apply]
  ring

lemma cpair_sub (om₁ om₂ : E n →L[ℝ] ℂ) (z : E n × E n) :
    cpair (om₁ - om₂) z = cpair om₁ z - cpair om₂ z := by
  simp only [cpair, sub_apply]
  ring

lemma cpair_smul (c : ℂ) (om : E n →L[ℝ] ℂ) (z : E n × E n) :
    cpair (c • om) z = c * cpair om z := by
  simp only [cpair, smul_apply, smul_eq_mul]
  ring

lemma cpair_add_pair (om : E n →L[ℝ] ℂ) (z w : E n × E n) :
    cpair om (z + w) = cpair om z + cpair om w := by
  simp only [cpair, Prod.fst_add, Prod.snd_add, map_add]
  ring

lemma cpair_sub_pair (om : E n →L[ℝ] ℂ) (z w : E n × E n) :
    cpair om (z - w) = cpair om z - cpair om w := by
  simp only [cpair, Prod.fst_sub, Prod.snd_sub, map_sub]
  ring

/-- Multiplication by `i` on the complexified tangent space, in real coordinates. -/
def Ismul (z : E n × E n) : E n × E n := (-z.2, z.1)

lemma cpair_Ismul (om : E n →L[ℝ] ℂ) (z : E n × E n) :
    cpair om (Ismul z) = Complex.I * cpair om z := by
  simp only [cpair, Ismul, map_neg]
  ring_nf
  simp only [sq, Complex.I_mul_I]
  ring

/-- The complexified derivative of the field `v` at `x`, applied to a complexified vector. -/
noncomputable def Dvel (v : E n → E n) (x : E n) (Z : E n × E n) : E n × E n :=
  (fderiv ℝ v x Z.1, fderiv ℝ v x Z.2)

/-- The flat connection applied to a complexified vector field. -/
noncomputable def Dd (W : E n → E n × E n) (x : E n) (Z : E n × E n) : E n × E n :=
  (fderiv ℝ (fun y => (W y).1) x Z.1 - fderiv ℝ (fun y => (W y).2) x Z.2,
   fderiv ℝ (fun y => (W y).1) x Z.2 + fderiv ℝ (fun y => (W y).2) x Z.1)

lemma Dvel_combine (L : E n →L[ℝ] ℂ) (W : E n → E n × E n) (x : E n) (Z : E n × E n) :
    cpair L (Dvel (fun y => (W y).1) x Z) + Complex.I * cpair L (Dvel (fun y => (W y).2) x Z)
      = cpair L (Dd W x Z) := by
  simp only [cpair, Dvel, Dd, map_sub, map_add]
  rw [mul_add, ← mul_assoc, Complex.I_mul_I]
  ring

lemma Dd_sub_eq_cbracket (Z W : E n → E n × E n) (x : E n) :
    Dd W x (Z x) - Dd Z x (W x) = cbracket Z W x := by
  unfold Dd cbracket VectorField.lieBracket
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> abel

/-! ### Linearity of the complexified directional derivative `czderiv` -/

lemma czderiv_congr {g₁ g₂ : E n → ℂ} {x : E n} (h : g₁ =ᶠ[𝓝 x] g₂)
    (Z : E n → E n × E n) : czderiv g₁ Z x = czderiv g₂ Z x := by
  rw [czderiv, czderiv, h.fderiv_eq]

lemma czderiv_add {g₁ g₂ : E n → ℂ} {x : E n} (h₁ : DifferentiableAt ℝ g₁ x)
    (h₂ : DifferentiableAt ℝ g₂ x) (Z : E n → E n × E n) :
    czderiv (g₁ + g₂) Z x = czderiv g₁ Z x + czderiv g₂ Z x := by
  rw [czderiv, czderiv, czderiv, fderiv_add h₁ h₂]
  simp only [add_apply]
  ring

lemma czderiv_const_smul (c : ℂ) {g : E n → ℂ} {x : E n} (hg : DifferentiableAt ℝ g x)
    (Z : E n → E n × E n) : czderiv (c • g) Z x = c * czderiv g Z x := by
  rw [czderiv, czderiv, fderiv_const_smul hg]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma czderiv_add_const_smul {g₁ g₂ : E n → ℂ} {x : E n} (h₁ : DifferentiableAt ℝ g₁ x)
    (h₂ : DifferentiableAt ℝ g₂ x) (c : ℂ) (Z : E n → E n × E n) :
    czderiv (fun y => g₁ y + c * g₂ y) Z x = czderiv g₁ Z x + c * czderiv g₂ Z x := by
  have hfun : (fun y => g₁ y + c * g₂ y) = g₁ + c • g₂ := by
    funext y; simp [smul_eq_mul]
  rw [hfun, czderiv_add h₁ (h₂.const_smul c), czderiv_const_smul c h₂]

/-! ### The `(0,1)` pairing of `∂̄u` -/

/-- `∂̄u` evaluated on the `(0,1)` vector `Z_X = X + iJX` is `du(X) + i·du(JX)`. -/
lemma cpair_dbar_Z01 {U : Set (E n)} {J : E n → E n →L[ℝ] E n} (hJ : IsAlmostComplexOn J U)
    {y : E n} (hy : y ∈ U) (u : E n → ℂ) (V : E n → E n) :
    cpair (dbar J u y) (Z01 J V y)
      = fderiv ℝ u y (V y) + Complex.I * fderiv ℝ u y (J y (V y)) := by
  have hsq := hJ.2 y hy (V y)
  simp only [cpair, Z01]
  rw [dbar_apply J u y (V y), dbar_apply J u y (J y (V y)), hsq, map_neg]
  ring_nf
  simp only [sq, Complex.I_mul_I]
  ring

/-- The `∂`-form applied to a `(0,1)` vector is zero. -/
lemma cpair_dpartial_self {J : E n → E n →L[ℝ] E n} {x : E n} (u : E n → ℂ)
    (hJJ : ∀ v, J x (J x v) = -v) (A : E n) :
    cpair (dpartial J u x) (A, J x A) = 0 := by
  have hd : dpartial J u x (A) = (1/2 : ℂ) * (fderiv ℝ u x A - Complex.I * fderiv ℝ u x (J x A)) := by
    simp only [dpartial, sub_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    norm_num
  have hd' : dpartial J u x (J x A)
      = (1/2 : ℂ) * (fderiv ℝ u x (J x A) - Complex.I * fderiv ℝ u x (J x (J x A))) := by
    simp only [dpartial, sub_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    norm_num
  simp only [cpair]
  rw [hd, hd', hJJ A, map_neg]
  ring_nf
  simp only [sq, Complex.I_mul_I]
  ring

/-! ### The second derivative pairing and the cancellation lemma -/

/-- The second derivative of `u` at `x`, paired with a complexified vector and a real vector. -/
noncomputable def S2 (u : E n → ℂ) (x : E n) (Z : E n × E n) (v : E n) : ℂ :=
  (fderiv ℝ (fun y => fderiv ℝ u y) x Z.1) v
    + Complex.I * ((fderiv ℝ (fun y => fderiv ℝ u y) x Z.2) v)

/-- The two terms involving the second derivative of `u` which appear in `dbarSq` cancel by
symmetry of the second derivative. -/
lemma S2_cancel {u : E n → ℂ} {x : E n} (hu : ContDiffAt ℝ 2 u x) (Js : E n → E n) (p q : E n) :
    S2 u x (p, Js p) q + Complex.I * S2 u x (p, Js p) (Js q)
      = S2 u x (q, Js q) p + Complex.I * S2 u x (q, Js q) (Js p) := by
  have hsymm : ∀ a b : E n,
      (fderiv ℝ (fun y => fderiv ℝ u y) x a) b = (fderiv ℝ (fun y => fderiv ℝ u y) x b) a :=
    fun a b => (hu.isSymmSndFDerivAt (by simp)).eq a b
  simp only [S2]
  rw [hsymm p q, hsymm (Js p) q, hsymm p (Js q), hsymm (Js p) (Js q)]
  ring

/-! ### The product rule for `czderiv` of `y ↦ du_y(v y)` -/

lemma differentiableAt_fderiv_apply {u : E n → ℂ} {x : E n} (hu : ContDiffAt ℝ 2 u x)
    {v : E n → E n} (hv : ContDiffAt ℝ 1 v x) :
    DifferentiableAt ℝ (fun y => fderiv ℝ u y (v y)) x :=
  ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (hv.differentiableAt (by simp))

lemma czderiv_fderiv_apply {u : E n → ℂ} {x : E n} (hu : ContDiffAt ℝ 2 u x)
    (v : E n → E n) (hv : ContDiffAt ℝ 1 v x) (Z : E n → E n × E n) :
    czderiv (fun y => fderiv ℝ u y (v y)) Z x
      = S2 u x (Z x) (v x) + cpair (fderiv ℝ u x) (Dvel v x (Z x)) := by
  have hc : DifferentiableAt ℝ (fun y => fderiv ℝ u y) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvD : DifferentiableAt ℝ v x := hv.differentiableAt (by simp)
  rw [czderiv, fderiv_clm_apply hc hvD]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, S2,
    Dvel, cpair]
  ring

lemma fderiv_sub_dbar (J : E n → E n →L[ℝ] E n) (u : E n → ℂ) (x : E n) :
    fderiv ℝ u x - dbar J u x = dpartial J u x := by
  have h := dbar_add_dpartial J u x
  rw [← h]
  abel

lemma cpair_sub_same (om₁ om₂ : E n →L[ℝ] ℂ) (z : E n × E n) :
    cpair om₁ z - cpair om₂ z = cpair (om₁ - om₂) z :=
  (cpair_sub om₁ om₂ z).symm

/-- Two terms of the shape `(A + B) - (A + C)` cancel. -/
lemma cancel_pair (A B C R : ℂ) (h : B - C = R) : (A + B) - (A + C) = R := by
  rw [← h]; abel

/-! ### The main identity: `dbarSq` is `∂` of the complexified Lie bracket -/

theorem dbarSq_eq_cpair_dpartial {U : Set (E n)} {J : E n → E n →L[ℝ] E n} (hU : IsOpen U)
    (hJ : IsAlmostComplexOn J U) {x : E n} (hx : x ∈ U) {u : E n → ℂ}
    (hu : ContDiffAt ℝ 2 u x) {X Y : E n → E n} (hX : ContDiffAt ℝ 1 X x)
    (hY : ContDiffAt ℝ 1 Y x) :
    dbarSq J u X Y x = cpair (dpartial J u x) (cbracket (Z01 J X) (Z01 J Y) x) := by
  have hJat : ContDiffAt ℝ ∞ J x := hJ.1.contDiffAt (hU.mem_nhds hx)
  have hJat1 : ContDiffAt ℝ 1 J x := hJat.of_le (by simp)
  have hJX : ContDiffAt ℝ 1 (fun y => J y (X y)) x := hJat1.clm_apply hX
  have hJY : ContDiffAt ℝ 1 (fun y => J y (Y y)) x := hJat1.clm_apply hY
  have hPhiY : (fun y => cpair (dbar J u y) (Z01 J Y y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y (Y y) + Complex.I * fderiv ℝ u y (J y (Y y))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact cpair_dbar_Z01 hJ hy u Y
  have hPhiX : (fun y => cpair (dbar J u y) (Z01 J X y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y (X y) + Complex.I * fderiv ℝ u y (J y (X y))) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact cpair_dbar_Z01 hJ hy u X
  have hYterm : czderiv (fun y => cpair (dbar J u y) (Z01 J Y y)) (Z01 J X) x
      = (S2 u x (Z01 J X x) (Y x) + Complex.I * S2 u x (Z01 J X x) (J x (Y x)))
        + (cpair (fderiv ℝ u x) (Dvel Y x (Z01 J X x))
           + Complex.I * cpair (fderiv ℝ u x) (Dvel (fun y => J y (Y y)) x (Z01 J X x))) := by
    rw [czderiv_congr hPhiY,
      czderiv_add_const_smul (differentiableAt_fderiv_apply hu hY)
        (differentiableAt_fderiv_apply hu hJY) Complex.I (Z01 J X),
      czderiv_fderiv_apply hu Y hY (Z01 J X),
      czderiv_fderiv_apply hu (fun y => J y (Y y)) hJY (Z01 J X)]
    ring
  have hXterm : czderiv (fun y => cpair (dbar J u y) (Z01 J X y)) (Z01 J Y) x
      = (S2 u x (Z01 J Y x) (X x) + Complex.I * S2 u x (Z01 J Y x) (J x (X x)))
        + (cpair (fderiv ℝ u x) (Dvel X x (Z01 J Y x))
           + Complex.I * cpair (fderiv ℝ u x) (Dvel (fun y => J y (X y)) x (Z01 J Y x))) := by
    rw [czderiv_congr hPhiX,
      czderiv_add_const_smul (differentiableAt_fderiv_apply hu hX)
        (differentiableAt_fderiv_apply hu hJX) Complex.I (Z01 J Y),
      czderiv_fderiv_apply hu X hX (Z01 J Y),
      czderiv_fderiv_apply hu (fun y => J y (X y)) hJX (Z01 J Y)]
    ring
  have hS2 : S2 u x (Z01 J X x) (Y x) + Complex.I * S2 u x (Z01 J X x) (J x (Y x))
      = S2 u x (Z01 J Y x) (X x) + Complex.I * S2 u x (Z01 J Y x) (J x (X x)) :=
    S2_cancel hu (fun v => J x v) (X x) (Y x)
  have hPY : cpair (fderiv ℝ u x) (Dvel Y x (Z01 J X x))
      + Complex.I * cpair (fderiv ℝ u x) (Dvel (fun y => J y (Y y)) x (Z01 J X x))
      = cpair (fderiv ℝ u x) (Dd (Z01 J Y) x (Z01 J X x)) :=
    Dvel_combine (fderiv ℝ u x) (Z01 J Y) x (Z01 J X x)
  have hPX : cpair (fderiv ℝ u x) (Dvel X x (Z01 J Y x))
      + Complex.I * cpair (fderiv ℝ u x) (Dvel (fun y => J y (X y)) x (Z01 J Y x))
      = cpair (fderiv ℝ u x) (Dd (Z01 J X) x (Z01 J Y x)) :=
    Dvel_combine (fderiv ℝ u x) (Z01 J X) x (Z01 J Y x)
  have hDd : cpair (fderiv ℝ u x) (Dd (Z01 J Y) x (Z01 J X x))
      - cpair (fderiv ℝ u x) (Dd (Z01 J X) x (Z01 J Y x))
      = cpair (fderiv ℝ u x) (cbracket (Z01 J X) (Z01 J Y) x) := by
    rw [← cpair_sub_pair, Dd_sub_eq_cbracket]
  have hmain : czderiv (fun y => cpair (dbar J u y) (Z01 J Y y)) (Z01 J X) x
      - czderiv (fun y => cpair (dbar J u y) (Z01 J X y)) (Z01 J Y) x
      = cpair (fderiv ℝ u x) (cbracket (Z01 J X) (Z01 J Y) x) := by
    rw [hYterm, hXterm, hPY, hPX, hS2]
    exact cancel_pair _ _ _ _ hDd
  rw [dbarSq, hmain, cpair_sub_same, fderiv_sub_dbar]

/-! ### The Nijenhuis tensor makes the complexified bracket `(0,1)` -/

lemma cbracket_Z01_eq_of_nijenhuis_zero {J : E n → E n →L[ℝ] E n} {x : E n}
    (hJJ : ∀ v, J x (J x v) = -v) {X Y : E n → E n} (hN : nijenhuis J X Y x = 0) :
    cbracket (Z01 J X) (Z01 J Y) x
      = Z01 J (fun y => VectorField.lieBracket ℝ X Y y
          - VectorField.lieBracket ℝ (fun z => J z (X z)) (fun z => J z (Y z)) y) x := by
  have hN'' : VectorField.lieBracket ℝ (fun z => J z (X z)) (fun z => J z (Y z)) x
      - J x (VectorField.lieBracket ℝ (fun z => J z (X z)) Y x)
      - J x (VectorField.lieBracket ℝ X (fun z => J z (Y z)) x)
      - VectorField.lieBracket ℝ X Y x = 0 := by
    simpa only [nijenhuis] using hN
  have key : J x (VectorField.lieBracket ℝ X Y x)
      - J x (VectorField.lieBracket ℝ (fun z => J z (X z)) (fun z => J z (Y z)) x)
      = VectorField.lieBracket ℝ (fun z => J z (X z)) Y x
        + VectorField.lieBracket ℝ X (fun z => J z (Y z)) x := by
    have h1 := congrArg (J x) hN''
    simp only [map_sub, map_zero] at h1
    simp only [hJJ] at h1
    simp only [sub_neg_eq_add] at h1
    rw [sub_eq_zero] at h1
    rw [← h1]
    abel
  simp only [cbracket, Z01]
  refine Prod.ext ?_ ?_
  · rfl
  · rw [map_sub, key]
    abel_nf


/-! ### Locality of the Nijenhuis tensor and conclusion -/

lemma nijenhuis_add_left {J : E n → E n →L[ℝ] E n} {V₁ V₂ W : E n → E n} {x : E n}
    (hJd : DifferentiableAt ℝ J x) (hV₁ : ContDiffAt ℝ 1 V₁ x) (hV₂ : ContDiffAt ℝ 1 V₂ x)
    (hW : ContDiffAt ℝ 1 W x) :
    nijenhuis J (V₁ + V₂) W x = nijenhuis J V₁ W x + nijenhuis J V₂ W x := by
  have hV₁d : DifferentiableAt ℝ V₁ x := hV₁.differentiableAt (by norm_num)
  have hV₂d : DifferentiableAt ℝ V₂ x := hV₂.differentiableAt (by norm_num)
  have hJ₁ : DifferentiableAt ℝ (fun y => J y (V₁ y)) x := hJd.clm_apply hV₁d
  have hJ₂ : DifferentiableAt ℝ (fun y => J y (V₂ y)) x := hJd.clm_apply hV₂d
  have hsplit : (fun y => J y ((V₁ + V₂) y))
      = (fun y => J y (V₁ y)) + (fun y => J y (V₂ y)) := by
    funext y; exact map_add (J y) _ _
  unfold nijenhuis
  rw [hsplit]
  rw [VectorField.lieBracket_add_left hJ₁ hJ₂ (W := fun y => J y (W y))]
  rw [VectorField.lieBracket_add_left hJ₁ hJ₂ (W := W)]
  rw [VectorField.lieBracket_add_left hV₁d hV₂d (W := fun y => J y (W y))]
  rw [VectorField.lieBracket_add_left hV₁d hV₂d (W := W)]
  simp only [map_add]
  abel

/-- If a vector field vanishes at `x`, then the Nijenhuis tensor evaluated on it at `x` vanishes:
`N` depends only on the pointwise values of its arguments. -/
lemma nijenhuis_zero_of_left_eq_zero {J : E n → E n →L[ℝ] E n} {x : E n}
    (hJd : DifferentiableAt ℝ J x) (hJJ : ∀ v, J x (J x v) = -v)
    {D Y : E n → E n} (hD : ContDiffAt ℝ 1 D x) (hY : ContDiffAt ℝ 1 Y x) (hDx : D x = 0) :
    nijenhuis J D Y x = 0 := by
  have hDd : DifferentiableAt ℝ D x := hD.differentiableAt (by norm_num)
  have hJD : fderiv ℝ (fun y => J y (D y)) x = (J x).comp (fderiv ℝ D x) := by
    rw [fderiv_clm_apply hJd hDd, hDx, map_zero, add_zero]
  unfold nijenhuis
  simp only [VectorField.lieBracket, hJD, hDx, map_zero, ContinuousLinearMap.comp_apply]
  simp only [hJJ, map_neg, zero_sub]
  abel

/-- The vanishing of the Nijenhuis tensor of `J` on the open set `U`, tested on globally smooth
vector fields, extends to vector fields that are only `C¹` at the point: `N` is tensorial, so it
depends only on the values of the two fields at the point, and those can be realised by constant
(hence globally smooth) fields. -/
theorem nijenhuis_zero_of_vanishes {U : Set (E n)} {J : E n → E n →L[ℝ] E n} (hU : IsOpen U)
    (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U) {x : E n} (hx : x ∈ U)
    {V W : E n → E n} (hV : ContDiffAt ℝ 1 V x) (hW : ContDiffAt ℝ 1 W x) :
    nijenhuis J V W x = 0 := by
  have hJat : ContDiffAt ℝ ∞ J x := hJ.1.contDiffAt (hU.mem_nhds hx)
  have hJd : DifferentiableAt ℝ J x := hJat.differentiableAt (by simp)
  have hJJ : ∀ v, J x (J x v) = -v := hJ.2 x hx
  have hVsub : ContDiffAt ℝ 1 (fun y => V y - V x) x := hV.sub contDiffAt_const
  have hWsub : ContDiffAt ℝ 1 (fun y => W y - W x) x := hW.sub contDiffAt_const
  have hVdecomp : V = (fun y => V y - V x) + (fun _ : E n => V x) := by
    funext y; simp only [Pi.add_apply]; abel
  have hWdecomp : W = (fun y => W y - W x) + (fun _ : E n => W x) := by
    funext y; simp only [Pi.add_apply]; abel
  have hVsub0 : (fun y => V y - V x) x = 0 := by simp
  have hWsub0 : (fun y => W y - W x) x = 0 := by simp
  have h0 : nijenhuis J (fun _ : E n => V x) (fun _ : E n => W x) x = 0 :=
    hN (fun _ => V x) (fun _ => W x) contDiff_const contDiff_const x hx
  calc nijenhuis J V W x
      = nijenhuis J ((fun y => V y - V x) + (fun _ : E n => V x)) W x := by
          conv_lhs => rw [hVdecomp]
    _ = nijenhuis J (fun y => V y - V x) W x + nijenhuis J (fun _ : E n => V x) W x :=
        nijenhuis_add_left hJd hVsub contDiffAt_const hW
    _ = nijenhuis J (fun _ : E n => V x) W x := by
        rw [nijenhuis_zero_of_left_eq_zero hJd hJJ hVsub hW hVsub0]
        simp
    _ = - nijenhuis J W (fun _ : E n => V x) x := by
        rw [Work.Nijenhuis.antisymm hU hJ hx contDiffAt_const hW]
    _ = - nijenhuis J ((fun y => W y - W x) + (fun _ : E n => W x)) (fun _ : E n => V x) x := by
        conv_lhs => rw [hWdecomp]
    _ = - (nijenhuis J (fun y => W y - W x) (fun _ : E n => V x) x
            + nijenhuis J (fun _ : E n => W x) (fun _ : E n => V x) x) := by
        rw [nijenhuis_add_left hJd hWsub contDiffAt_const contDiffAt_const]
    _ = - (0 + nijenhuis J (fun _ : E n => W x) (fun _ : E n => V x) x) := by
        rw [nijenhuis_zero_of_left_eq_zero hJd hJJ hWsub contDiffAt_const hWsub0]
    _ = nijenhuis J (fun _ : E n => V x) (fun _ : E n => W x) x := by
        rw [Work.Nijenhuis.antisymm hU hJ hx contDiffAt_const contDiffAt_const]
        abel
    _ = 0 := h0

end Aux

/-- **The vanishing of the Nijenhuis tensor implies `∂̄² = 0`.**
`dbarSq J u X Y x` is the `(0,2)`-part of `d(∂̄u)` at `x` evaluated on the real vector fields
`X`, `Y` (up to a nonzero constant): it is
`Z_X(∂̄u(Z_Y)) - Z_Y(∂̄u(Z_X)) - ∂̄u([Z_X,Z_Y])` with `Z_X = X + iJX`, `Z_Y = Y + iJY`.
If the Nijenhuis tensor of `J` vanishes on the open set `U ∋ x`, then this vanishes: the
`∂̄`-operator of an integrable almost complex structure satisfies `∂̄² = 0`. -/
theorem sq_zero {n : ℕ} {U : Set (E n)} {J : E n → E n →L[ℝ] E n} (hU : IsOpen U)
    (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U)
    {x : E n} (hx : x ∈ U) {u : E n → ℂ} (hu : ContDiffAt ℝ 2 u x)
    {X Y : E n → E n} (hX : ContDiffAt ℝ 1 X x) (hY : ContDiffAt ℝ 1 Y x) :
    dbarSq J u X Y x = 0 := by
  have hJJ : ∀ v, J x (J x v) = -v := hJ.2 x hx
  have hN0 : nijenhuis J X Y x = 0 := Aux.nijenhuis_zero_of_vanishes hU hJ hN hx hX hY
  rw [Aux.dbarSq_eq_cpair_dpartial hU hJ hx hu hX hY,
    Aux.cbracket_Z01_eq_of_nijenhuis_zero hJJ hN0]
  exact Aux.cpair_dpartial_self u hJJ _

end Work.Dbar
