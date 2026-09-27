import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.gapA.rotSetup
import Submission.Work.Mostow.gapA.rotationFormula
import Submission.Work.Mostow.perpNullUnit
import Submission.Work.Mostow.finite_nearStab

/-!
# The rotation subgroup of the pointwise stabiliser of a geodesic, and its complex parameter

For two distinct boundary points `a ≠ b` of the sphere `Sph 3`:

* `NormP a b` is the *normal plane* `{Z | ⟨Z,θ_a⟩ = ⟨Z,θ_b⟩ = 0}` of the geodesic `geodSet a b`,
  a positive definite plane of dimension `2` (`⟨·,·⟩ = mink`);
* `PB a b` bundles a Minkowski-orthonormal basis `(e1,e2)` of that plane together with the
  spanning statements for `NormP a b` and for the whole Minkowski space;
* `AxisSub hA a b` is the subgroup of `PO 3 1` consisting of the orientation-preserving isometries
  fixing `geodSet a b` pointwise (equivalently: `emat g` fixes both null vectors and has
  determinant `1`);
* `rotMat B g` is the `2 × 2` matrix of the action of `emat g` on the normal plane in the
  orthonormal basis `(e1,e2)`, and `zOf B g` is the corresponding complex number
  `(rotMat B g) 0 0 + (rotMat B g) 1 0 * I`.

The main content is that for `g ∈ AxisSub hA a b` the matrix `rotMat B g` is a *rotation matrix*
`!![c, -s; s, c]`, so that `g ↦ zOf B g` is a group homomorphism into `ℂˣ`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

variable {a b : E 3}

/-! ## The normal plane -/

/-- The normal plane of the geodesic `geodSet a b`: the orthogonal complement of the two null
vectors `nvec a`, `nvec b`. -/
def NormP (a b : E 3) : Submodule ℝ (Fin 3 ⊕ Fin 1 → ℝ) where
  carrier := {Z | mink Z (nvec a) = 0 ∧ mink Z (nvec b) = 0}
  zero_mem' := ⟨by simp [mink], by simp [mink]⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [minkSeg_add_left, hx1, hy1, add_zero],
           by rw [minkSeg_add_left, hx2, hy2, add_zero]⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · rw [mink_smul_left'', hx1, mul_zero]
    · rw [mink_smul_left'', hx2, mul_zero]

lemma mem_NormP {Z : Fin 3 ⊕ Fin 1 → ℝ} :
    Z ∈ NormP a b ↔ mink Z (nvec a) = 0 ∧ mink Z (nvec b) = 0 := Iff.rfl

/-! ## An orthonormal basis of the normal plane -/

/-- A positive definite orthonormal basis `(e1,e2)` of the normal plane of `geodSet a b`,
together with the spanning statements for `NormP a b` and for the whole Minkowski space. -/
structure PB (a b : E 3) where
  /-- first basis vector of the normal plane -/
  e1 : Fin 3 ⊕ Fin 1 → ℝ
  /-- second basis vector of the normal plane -/
  e2 : Fin 3 ⊕ Fin 1 → ℝ
  mem1 : e1 ∈ NormP a b
  mem2 : e2 ∈ NormP a b
  n11 : mink e1 e1 = 1
  n22 : mink e2 e2 = 1
  n12 : mink e1 e2 = 0
  /-- `e1`, `e2` span the normal plane -/
  span : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormP a b → ∃ α β : ℝ, Z = α • e1 + β • e2
  /-- `nvec a`, `nvec b`, `e1`, `e2` span the whole Minkowski space -/
  spanV : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, ∃ α β γ δ : ℝ,
    Z = α • nvec a + β • nvec b + γ • e1 + δ • e2

/-- Coordinate decomposition of an element of the normal plane in the orthonormal basis. -/
lemma eq_coord (B : PB a b) {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormP a b) :
    mink Z B.e1 • B.e1 + mink Z B.e2 • B.e2 = Z := by
  obtain ⟨α, β, hαβ⟩ := B.span Z hZ
  have h1 : mink Z B.e1 = α := by
    rw [hαβ, minkSeg_add_left, mink_smul_left'', mink_smul_left'', B.n11,
      minkSeg_comm B.e2 B.e1, B.n12]
    ring
  have h2 : mink Z B.e2 = β := by
    rw [hαβ, minkSeg_add_left, mink_smul_left'', mink_smul_left'', B.n22, B.n12]
    ring
  rw [h1, h2, hαβ]

/-- The Minkowski pairing of two elements of the normal plane, in coordinates. -/
lemma mink_coord (B : PB a b) {Z Z' : Fin 3 ⊕ Fin 1 → ℝ} (hZ' : Z' ∈ NormP a b) :
    mink Z Z' = mink Z B.e1 * mink Z' B.e1 + mink Z B.e2 * mink Z' B.e2 := by
  conv_lhs => rw [← eq_coord B hZ']
  rw [minkSeg_add_right, mink_smul_right'', mink_smul_right'']
  ring

/-- `e1`, `e2` are linearly independent. -/
lemma indep_pair (B : PB a b) {α β : ℝ} (h : α • B.e1 + β • B.e2 = 0) :
    α = 0 ∧ β = 0 := by
  have h1 : mink (α • B.e1 + β • B.e2) B.e1 = 0 := by rw [h]; simp [mink]
  have h2 : mink (α • B.e1 + β • B.e2) B.e2 = 0 := by rw [h]; simp [mink]
  simp only [minkSeg_add_left, mink_smul_left'', B.n11, B.n12, minkSeg_comm B.e2 B.e1,
    mul_one, mul_zero, mul_comm B.e1, add_zero, zero_mul] at h1
  simp only [minkSeg_add_left, mink_smul_left'', B.n22, B.n12, mul_one, mul_zero,
    add_zero] at h2
  constructor <;> linarith

/-- `nvec a`, `nvec b`, `e1`, `e2` are linearly independent. -/
lemma indepV (B : PB a b) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) {α β γ δ : ℝ}
    (h : α • nvec a + β • nvec b + γ • B.e1 + δ • B.e2 = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 := by
  have hYmem : γ • B.e1 + δ • B.e2 ∈ NormP a b :=
    (NormP a b).add_mem ((NormP a b).smul_mem γ B.mem1) ((NormP a b).smul_mem δ B.mem2)
  obtain ⟨hY1, hY2⟩ := mem_NormP.mp hYmem
  have hXY : mink (α • nvec a + β • nvec b) (γ • B.e1 + δ • B.e2) = 0 := by
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'',
      minkSeg_comm (nvec a) (γ • B.e1 + δ • B.e2), minkSeg_comm (nvec b) (γ • B.e1 + δ • B.e2),
      hY1, hY2]
    ring
  have hYY : mink (γ • B.e1 + δ • B.e2) (γ • B.e1 + δ • B.e2) = 0 := by
    have h0 : mink ((α • nvec a + β • nvec b) + (γ • B.e1 + δ • B.e2))
        (γ • B.e1 + δ • B.e2) = 0 := by
      have h' : (α • nvec a + β • nvec b) + (γ • B.e1 + δ • B.e2) = 0 := by
        rw [← h]; abel
      rw [h']
      simp [mink]
    rw [minkSeg_add_left, hXY, zero_add] at h0
    exact h0
  have hsq : γ * γ + δ * δ = 0 := by
    have hh := hYY
    simp only [minkSeg_add_left, minkSeg_add_right, mink_smul_left'', mink_smul_right'',
      B.n11, B.n22, B.n12, minkSeg_comm B.e2 B.e1] at hh
    linarith [hh]
  have hγ : γ = 0 := by nlinarith [sq_nonneg γ, sq_nonneg δ]
  have hδ : δ = 0 := by nlinarith [sq_nonneg γ, sq_nonneg δ]
  have hαβ : α • nvec a + β • nvec b = 0 := by
    rw [hγ, hδ] at h
    simpa using h
  have hne : mink (nvec a) (nvec b) ≠ 0 := by
    rw [mink_nvec_nvec']
    have hlt : inner ℝ a b < 1 :=
      inner_lt_one_of_ne_unit ((mem_Sph_iff a).mp ha) ((mem_Sph_iff b).mp hb) hab
    linarith
  have hnb : mink (nvec b) (nvec a) ≠ 0 := by
    rw [minkSeg_comm]; exact hne
  have hβ : β = 0 := by
    have h0 : mink (α • nvec a + β • nvec b) (nvec a) = 0 := by rw [hαβ]; simp [mink]
    simp only [minkSeg_add_left, mink_smul_left'', mink_nvec_self' ha, mul_zero, zero_add,
      add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right hnb
  have hα : α = 0 := by
    have h0 : mink (α • nvec a + β • nvec b) (nvec b) = 0 := by rw [hαβ]; simp [mink]
    simp only [minkSeg_add_left, mink_smul_left'', mink_nvec_self' hb, mul_zero, add_zero,
      zero_add, hβ] at h0
    exact (mul_eq_zero.mp h0).resolve_right hne
  exact ⟨hα, hβ, hγ, hδ⟩

/-! ## The pointwise stabiliser of the geodesic -/

/-- The subgroup of `PO 3 1` consisting of the orientation preserving isometries fixing
`geodSet a b` pointwise: equivalently, `emat g` fixes both null vectors and has determinant `1`. -/
def AxisSub (hA : POActionProp 3) (a b : E 3) : Subgroup (PO 3 1) where
  carrier := {g | emat g *ᵥ nvec a = nvec a ∧ emat g *ᵥ nvec b = nvec b ∧ (emat g).det = 1}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hgd⟩ ⟨hh1, hh2, hhd⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [emat_mul hA, ← Matrix.mulVec_mulVec, hh1, hg1]
    · rw [emat_mul hA, ← Matrix.mulVec_mulVec, hh2, hg2]
    · rw [emat_mul hA, Matrix.det_mul, hgd, hhd, one_mul]
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [emat_one hA, Matrix.one_mulVec]
    · rw [emat_one hA, Matrix.one_mulVec]
    · rw [emat_one hA, Matrix.det_one]
  inv_mem' := by
    rintro g ⟨hg1, hg2, hgd⟩
    have hg'g : emat g⁻¹ * emat g = 1 := by rw [← emat_mul hA, inv_mul_cancel, emat_one hA]
    have hgg' : emat g * emat g⁻¹ = 1 := by rw [← emat_mul hA, mul_inv_cancel, emat_one hA]
    refine ⟨?_, ?_, ?_⟩
    · have h := congrArg (fun z => emat g⁻¹ *ᵥ z) hg1
      rw [Matrix.mulVec_mulVec, hg'g, Matrix.one_mulVec] at h
      exact h.symm
    · have h := congrArg (fun z => emat g⁻¹ *ᵥ z) hg2
      rw [Matrix.mulVec_mulVec, hg'g, Matrix.one_mulVec] at h
      exact h.symm
    · have h : (emat g).det * (emat g⁻¹).det = 1 := by
        rw [← Matrix.det_mul, hgg', Matrix.det_one]
      rw [hgd, one_mul] at h
      exact h

lemma mem_AxisSub_iff {hA : POActionProp 3} {g : PO 3 1} :
    g ∈ AxisSub hA a b ↔
      emat g *ᵥ nvec a = nvec a ∧ emat g *ᵥ nvec b = nvec b ∧ (emat g).det = 1 := Iff.rfl

/-- The determinant of `emat g` is `1` for an orientation preserving isometry. -/
lemma det_emat_eq_one_of_isOriented (g : PO 3 1) (h : IsOriented g) : (emat g).det = 1 := by
  have h1 : (emat g).det = (mat (rep g)).det := det_emat3 g
  have key : (mat (rep g))ᵀ * pmOneMat * mat (rep g) * pmOneMat
      = (1 : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ) := by
    rw [show (mat (rep g))ᵀ * pmOneMat * mat (rep g) * pmOneMat
          = ((mat (rep g))ᵀ * pmOneMat * mat (rep g)) * pmOneMat from rfl,
      O1_form_col (rep g), pmOneMat_mul_pmOneMat]
  have hdet1 : ((mat (rep g))ᵀ * pmOneMat * mat (rep g) * pmOneMat).det = 1 := by
    rw [key, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet1
  have hsq : (mat (rep g)).det * (mat (rep g)).det = 1 := by
    have hJ : (pmOneMat : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ).det
        * (pmOneMat : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ).det = 1 := by
      rw [← Matrix.det_mul, pmOneMat_mul_pmOneMat, Matrix.det_one]
    nlinarith [hdet1, hJ]
  have hsq2 : (mat (rep g)).det ^ 2 = 1 := by rw [pow_two]; exact hsq
  have hpos : 0 < (mat (rep g)).det := h
  rw [h1]
  rcases sq_eq_one_iff.mp hsq2 with h' | h'
  · exact h'
  · rw [h'] at hpos; norm_num at hpos

lemma isOriented_of_mem_AxisSub {hA : POActionProp 3} {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) : IsOriented g := by
  rw [isOriented_iff_det, (mem_AxisSub_iff.mp hg).2.2]
  norm_num

/-- An orientation preserving isometry fixing `geodSet a b` pointwise lies in `AxisSub`. -/
lemma mem_AxisSub_of_isOriented_of_fixes (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) {g : PO 3 1} (hor : IsOriented g)
    (hax : ∀ u : E 3, u ∈ geodSet a b → g • u = u) : g ∈ AxisSub hA a b := by
  obtain ⟨h1, h2⟩ := emat_fixes_nvec hA hI g a b ha hb hab hax
  exact ⟨h1, h2, det_emat_eq_one_of_isOriented g hor⟩

/-- An element of `AxisSub` fixes `geodSet a b` pointwise. -/
lemma geodSet_fixed_of_mem_AxisSub (hA : POActionProp 3) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    (hab : a ≠ b) {g : PO 3 1} (hg : g ∈ AxisSub hA a b) :
    ∀ u : E 3, u ∈ geodSet a b → g • u = u := by
  intro u hu
  obtain ⟨α, β, hαβ⟩ := (mem_geodSet_iff_span a b ha hb hab u).mp hu
  obtain ⟨hg1, hg2, -⟩ := mem_AxisSub_iff.mp hg
  have hml : emat g *ᵥ hlift u = hlift u := by
    rw [hαβ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hg1, hg2]
  have h2 : hlift (g • u) = hlift u := by rw [← emat_hlift g u, hml]
  exact Submission.Mostow.Hyper.hlift_injective h2

/-- `emat g` preserves the normal plane for `g ∈ AxisSub`. -/
lemma emat_mem_NormP_of_mem (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormP a b) :
    emat g *ᵥ Z ∈ NormP a b := by
  obtain ⟨hg1, hg2, -⟩ := mem_AxisSub_iff.mp hg
  obtain ⟨hZ1, hZ2⟩ := mem_NormP.mp hZ
  refine mem_NormP.mpr ⟨?_, ?_⟩
  · rw [← hg1, mink_emat_emat g Z (nvec a), hZ1]
  · rw [← hg2, mink_emat_emat g Z (nvec b), hZ2]

lemma emat_mem_NormP (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) :
    emat g *ᵥ B.e1 ∈ NormP a b ∧ emat g *ᵥ B.e2 ∈ NormP a b :=
  ⟨emat_mem_NormP_of_mem hA B hg B.mem1, emat_mem_NormP_of_mem hA B hg B.mem2⟩

/-! ## The matrix and the complex number of the normal action -/

/-- `(0,0)`-entry of the normal action. -/
def rot00 (B : PB a b) (g : PO 3 1) : ℝ := mink (emat g *ᵥ B.e1) B.e1
/-- `(1,0)`-entry of the normal action. -/
def rot10 (B : PB a b) (g : PO 3 1) : ℝ := mink (emat g *ᵥ B.e1) B.e2
/-- `(0,1)`-entry of the normal action. -/
def rot01 (B : PB a b) (g : PO 3 1) : ℝ := mink (emat g *ᵥ B.e2) B.e1
/-- `(1,1)`-entry of the normal action. -/
def rot11 (B : PB a b) (g : PO 3 1) : ℝ := mink (emat g *ᵥ B.e2) B.e2

/-- The `2 × 2` matrix of the action of `emat g` on the normal plane in the basis `(e1,e2)`. -/
def rotMat (B : PB a b) (g : PO 3 1) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![rot00 B g, rot01 B g; rot10 B g, rot11 B g]

/-- The complex parameter of the action of `g` on the normal plane. -/
def zOf (B : PB a b) (g : PO 3 1) : ℂ := ⟨rot00 B g, rot10 B g⟩

@[simp] lemma rotMat_apply_zero_zero (B : PB a b) (g : PO 3 1) :
    (rotMat B g) 0 0 = rot00 B g := by simp [rotMat]
@[simp] lemma rotMat_apply_zero_one (B : PB a b) (g : PO 3 1) :
    (rotMat B g) 0 1 = rot01 B g := by simp [rotMat]
@[simp] lemma rotMat_apply_one_zero (B : PB a b) (g : PO 3 1) :
    (rotMat B g) 1 0 = rot10 B g := by simp [rotMat]
@[simp] lemma rotMat_apply_one_one (B : PB a b) (g : PO 3 1) :
    (rotMat B g) 1 1 = rot11 B g := by simp [rotMat]

lemma zOf_eq_mat (B : PB a b) (g : PO 3 1) :
    zOf B g = ⟨(rotMat B g) 0 0, (rotMat B g) 1 0⟩ := by simp [zOf]

@[simp] lemma zOf_re (B : PB a b) (g : PO 3 1) : (zOf B g).re = rot00 B g := rfl
@[simp] lemma zOf_im (B : PB a b) (g : PO 3 1) : (zOf B g).im = rot10 B g := rfl

/-- The two columns of the normal action. -/
lemma emat_mulVec_e1 (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) :
    emat g *ᵥ B.e1 = rot00 B g • B.e1 + rot10 B g • B.e2 := by
  have h := eq_coord B (emat_mem_NormP_of_mem hA B hg B.mem1)
  rw [← h]
  simp only [rot00, rot10]

lemma emat_mulVec_e2 (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) :
    emat g *ᵥ B.e2 = rot01 B g • B.e1 + rot11 B g • B.e2 := by
  have h := eq_coord B (emat_mem_NormP_of_mem hA B hg B.mem2)
  rw [← h]
  simp only [rot01, rot11]

/-- The action of `emat g` on the normal plane, in coordinates. -/
lemma rotMat_action (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormP a b) :
    emat g *ᵥ Z
      = (mink Z B.e1 * rot00 B g + mink Z B.e2 * rot01 B g) • B.e1
        + (mink Z B.e1 * rot10 B g + mink Z B.e2 * rot11 B g) • B.e2 := by
  have hmem := emat_mem_NormP_of_mem hA B hg hZ
  have h1 : mink (emat g *ᵥ Z) B.e1
      = mink Z B.e1 * rot00 B g + mink Z B.e2 * rot01 B g := by
    conv_lhs => rw [← eq_coord B hZ]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, minkSeg_add_left,
      mink_smul_left'', mink_smul_left'']
    rfl
  have h2 : mink (emat g *ᵥ Z) B.e2
      = mink Z B.e1 * rot10 B g + mink Z B.e2 * rot11 B g := by
    conv_lhs => rw [← eq_coord B hZ]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, minkSeg_add_left,
      mink_smul_left'', mink_smul_left'']
    rfl
  rw [← eq_coord B hmem, h1, h2]

/-- The normal action is Minkowski-orthogonal. -/
lemma rotMat_orth (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) :
    rot00 B g ^ 2 + rot10 B g ^ 2 = 1 ∧ rot01 B g ^ 2 + rot11 B g ^ 2 = 1 ∧
      rot00 B g * rot01 B g + rot10 B g * rot11 B g = 0 := by
  have hmem1 := emat_mem_NormP_of_mem hA B hg B.mem1
  have hmem2 := emat_mem_NormP_of_mem hA B hg B.mem2
  have h11 : mink (emat g *ᵥ B.e1) (emat g *ᵥ B.e1) = 1 := by
    rw [mink_emat_emat g B.e1 B.e1, B.n11]
  have h22 : mink (emat g *ᵥ B.e2) (emat g *ᵥ B.e2) = 1 := by
    rw [mink_emat_emat g B.e2 B.e2, B.n22]
  have h12 : mink (emat g *ᵥ B.e1) (emat g *ᵥ B.e2) = 0 := by
    rw [mink_emat_emat g B.e1 B.e2, B.n12]
  refine ⟨?_, ?_, ?_⟩
  · have h := h11
    rw [mink_coord B hmem1] at h
    simp only [rot00, rot10]
    nlinarith [h]
  · have h := h22
    rw [mink_coord B hmem2] at h
    simp only [rot01, rot11]
    nlinarith [h]
  · have h := h12
    rw [mink_coord B hmem2] at h
    simp only [rot00, rot01, rot10, rot11]
    nlinarith [h]

/-- The rotation form of the normal action, given that its determinant is `1`. -/
lemma rotMat_form (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (hdet : (rotMat B g).det = 1) :
    rot01 B g = - rot10 B g ∧ rot11 B g = rot00 B g ∧
      rot00 B g ^ 2 + rot10 B g ^ 2 = 1 := by
  obtain ⟨h1, h2, h3⟩ := rotMat_orth hA B hg
  have hdet' : rot00 B g * rot11 B g - rot01 B g * rot10 B g = 1 := by
    rw [rotMat, Matrix.det_fin_two] at hdet
    simpa using hdet
  have hkey : (rot01 B g + rot10 B g) ^ 2 + (rot11 B g - rot00 B g) ^ 2 = 0 := by
    nlinarith [h1, h2, h3, hdet']
  refine ⟨?_, ?_, h1⟩
  · nlinarith [hkey, sq_nonneg (rot01 B g + rot10 B g), sq_nonneg (rot11 B g - rot00 B g)]
  · nlinarith [hkey, sq_nonneg (rot01 B g + rot10 B g), sq_nonneg (rot11 B g - rot00 B g)]

/-- `zOf` is a unit of `ℂ`. -/
lemma zOf_ne_zero (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) : zOf B g ≠ 0 := by
  intro h
  have h00 : rot00 B g = 0 := by
    have := congrArg Complex.re h
    simpa using this
  have h10 : rot10 B g = 0 := by
    have := congrArg Complex.im h
    simpa using this
  have h1 := (rotMat_orth hA B hg).1
  rw [h00, h10] at h1
  norm_num at h1

/-! ## Multiplicativity and injectivity of `zOf` -/

@[simp] lemma rot00_mul (hA : POActionProp 3) (B : PB a b) {g h : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (hh : h ∈ AxisSub hA a b) :
    rot00 B (g * h) = rot00 B g * rot00 B h + rot01 B g * rot10 B h := by
  have key : emat (g * h) *ᵥ B.e1
      = rot00 B h • (emat g *ᵥ B.e1) + rot10 B h • (emat g *ᵥ B.e2) := by
    rw [emat_mul hA, ← Matrix.mulVec_mulVec, emat_mulVec_e1 hA B hh, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
  rw [show rot00 B (g * h) = mink (emat (g * h) *ᵥ B.e1) B.e1 from rfl, key,
    minkSeg_add_left, mink_smul_left'', mink_smul_left'']
  simp only [rot00, rot01, rot10]
  ring

@[simp] lemma rot10_mul (hA : POActionProp 3) (B : PB a b) {g h : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (hh : h ∈ AxisSub hA a b) :
    rot10 B (g * h) = rot10 B g * rot00 B h + rot11 B g * rot10 B h := by
  have key : emat (g * h) *ᵥ B.e1
      = rot00 B h • (emat g *ᵥ B.e1) + rot10 B h • (emat g *ᵥ B.e2) := by
    rw [emat_mul hA, ← Matrix.mulVec_mulVec, emat_mulVec_e1 hA B hh, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
  rw [show rot10 B (g * h) = mink (emat (g * h) *ᵥ B.e1) B.e2 from rfl, key,
    minkSeg_add_left, mink_smul_left'', mink_smul_left'']
  simp only [rot10, rot11]
  ring

@[simp] lemma rot01_mul (hA : POActionProp 3) (B : PB a b) {g h : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (hh : h ∈ AxisSub hA a b) :
    rot01 B (g * h) = rot00 B g * rot01 B h + rot01 B g * rot11 B h := by
  have key : emat (g * h) *ᵥ B.e2
      = rot01 B h • (emat g *ᵥ B.e1) + rot11 B h • (emat g *ᵥ B.e2) := by
    rw [emat_mul hA, ← Matrix.mulVec_mulVec, emat_mulVec_e2 hA B hh, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
  rw [show rot01 B (g * h) = mink (emat (g * h) *ᵥ B.e2) B.e1 from rfl, key,
    minkSeg_add_left, mink_smul_left'', mink_smul_left'']
  simp only [rot00, rot01, rot11]
  ring

@[simp] lemma rot11_mul (hA : POActionProp 3) (B : PB a b) {g h : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (hh : h ∈ AxisSub hA a b) :
    rot11 B (g * h) = rot10 B g * rot01 B h + rot11 B g * rot11 B h := by
  have key : emat (g * h) *ᵥ B.e2
      = rot01 B h • (emat g *ᵥ B.e1) + rot11 B h • (emat g *ᵥ B.e2) := by
    rw [emat_mul hA, ← Matrix.mulVec_mulVec, emat_mulVec_e2 hA B hh, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
  rw [show rot11 B (g * h) = mink (emat (g * h) *ᵥ B.e2) B.e2 from rfl, key,
    minkSeg_add_left, mink_smul_left'', mink_smul_left'']
  simp only [rot01, rot10, rot11]
  ring

lemma rotMat_mul (hA : POActionProp 3) (B : PB a b) {g h : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (hh : h ∈ AxisSub hA a b) :
    rotMat B (g * h) = rotMat B g * rotMat B h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [rotMat, Matrix.mul_fin_two]
  · exact rot00_mul hA B hg hh
  · exact rot01_mul hA B hg hh
  · exact rot10_mul hA B hg hh
  · exact rot11_mul hA B hg hh

lemma rotMat_one (hA : POActionProp 3) (B : PB a b) :
    rotMat B (1 : PO 3 1) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMat, Matrix.one_fin_two, rot00, rot10, rot01, rot11, emat_one hA, B.n11, B.n12,
      B.n22, minkSeg_comm B.e2 B.e1]

/-- Powers of a rotation matrix are rotation matrices, with the complex numbers multiplying. -/
lemma rotForm_pow (c s : ℝ) (k : ℕ) :
    ∃ c' s' : ℝ, (!![c, -s; s, c] : Matrix (Fin 2) (Fin 2) ℝ) ^ k = !![c', -s'; s', c'] ∧
      (⟨c', s'⟩ : ℂ) = (⟨c, s⟩ : ℂ) ^ k := by
  induction k with
  | zero =>
      refine ⟨1, 0, ?_, ?_⟩
      · rw [pow_zero, Matrix.one_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      · rw [pow_zero]
        rfl
  | succ k ih =>
      obtain ⟨c', s', hmat, hz⟩ := ih
      refine ⟨c' * c - s' * s, c' * s + s' * c, ?_, ?_⟩
      · rw [pow_succ, hmat, Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> ring
      · rw [pow_succ, ← hz]
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma rotMat_pow (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (k : ℕ) : rotMat B (g ^ k) = (rotMat B g) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, rotMat_one hA B]
  | succ k ih =>
      rw [pow_succ, pow_succ, rotMat_mul hA B ((AxisSub hA a b).pow_mem hg k) hg, ih]

/-- The iterates of `zOf` are the powers of `zOf`. -/
lemma zOf_pow (hA : POActionProp 3) (B : PB a b) {g : PO 3 1} (hg : g ∈ AxisSub hA a b)
    {c s : ℝ} (hf : rotMat B g = !![c, -s; s, c]) (k : ℕ) :
    zOf B (g ^ k) = (zOf B g) ^ k := by
  obtain ⟨c', s', hmat, hz⟩ := rotForm_pow c s k
  have h1 : zOf B (g ^ k) = ⟨c', s'⟩ := by
    rw [zOf_eq_mat, rotMat_pow hA B hg k, hf, hmat]
    simp
  have h2 : zOf B g = ⟨c, s⟩ := by rw [zOf_eq_mat, hf]; simp
  rw [h1, h2, hz]

/-- `zOf` of a rotation matrix pair acts on the normal plane by the rotation by that angle. -/
lemma mink_mulVec_zOf (hA : POActionProp 3) (B : PB a b) {g : PO 3 1}
    (hg : g ∈ AxisSub hA a b) {c s : ℝ} (hf : rotMat B g = !![c, -s; s, c])
    {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormP a b) :
    mink (emat g *ᵥ Z) Z = c * mink Z Z := by
  have h00 : rot00 B g = c := by rw [← rotMat_apply_zero_zero, hf]; simp
  have h10 : rot10 B g = s := by rw [← rotMat_apply_one_zero, hf]; simp
  have h01 : rot01 B g = -s := by rw [← rotMat_apply_zero_one, hf]; simp
  have h11 : rot11 B g = c := by rw [← rotMat_apply_one_one, hf]; simp
  rw [rotMat_action hA B hg hZ, minkSeg_add_left, mink_smul_left'', mink_smul_left'',
    minkSeg_comm B.e1 Z, minkSeg_comm B.e2 Z, mink_coord B hZ, h00, h10, h01, h11]
  ring

/-- The rotation formula for the iterates of an element of `AxisSub`. -/
lemma mink_pow (hA : POActionProp 3) (B : PB a b) {g : PO 3 1} (hg : g ∈ AxisSub hA a b)
    {c s : ℝ} (hf : rotMat B g = !![c, -s; s, c]) (k : ℕ)
    {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormP a b) :
    mink (emat (g ^ k) *ᵥ Z) Z = ((zOf B g) ^ k).re * mink Z Z := by
  have hgk : g ^ k ∈ AxisSub hA a b := (AxisSub hA a b).pow_mem hg k
  obtain ⟨c', s', hmat, hz⟩ := rotForm_pow c s k
  have hpow : rotMat B (g ^ k) = !![c', -s'; s', c'] := by
    rw [rotMat_pow hA B hg k, hf, hmat]
  rw [mink_mulVec_zOf hA B hgk hpow hZ]
  have h2 : zOf B g = ⟨c, s⟩ := by rw [zOf_eq_mat, hf]; simp
  rw [h2, ← hz]

end

end Work.Mostow.gapA
