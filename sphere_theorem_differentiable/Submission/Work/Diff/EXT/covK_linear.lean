import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.curvNormK_frame_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! ## Auxiliary material for the field-level linearity of `∇^k Rm`

The recursion `Work.Diff.EXT.covKRmExt` is the split version of the uniform recursion
`Work.Diff.EXT.ckt` of `Submission/Work/Diff/EXT/curvNormK_frame_indep.lean`, which already
proves the `C^∞(M)`-linearity, smoothness and locality of `ckt` (statement `TensProp`) in a
single induction on `k`.  Here we transport that linearity back to `covKRmExt`.
-/

section Aux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- Unfold `SmoothTField` into the recursion's `SmoothF`. -/
lemma smoothF_of_smoothTField {X : TField (I := I) (M := M)}
    (h : SmoothTField (I := I) (M := M) X) : SmoothF X := by
  simpa only [SmoothF] using h

/-- The four curvature slots of `covKRmExt`, packed as a `Fin 4`-tuple. -/
noncomputable def quadF (A B C D : TField (I := I) (M := M)) :
    Fin 4 → TField (I := I) (M := M) := ![A, B, C, D]

@[simp] lemma quadF_zero (A B C D : TField (I := I) (M := M)) : quadF A B C D 0 = A := rfl
@[simp] lemma quadF_one (A B C D : TField (I := I) (M := M)) : quadF A B C D 1 = B := rfl
@[simp] lemma quadF_two (A B C D : TField (I := I) (M := M)) : quadF A B C D 2 = C := rfl
@[simp] lemma quadF_three (A B C D : TField (I := I) (M := M)) : quadF A B C D 3 = D := rfl

lemma update_quadF_zero (A B C D X : TField (I := I) (M := M)) :
    Function.update (quadF A B C D) 0 X = quadF X B C D := by
  rw [Function.update_eq_iff]
  refine ⟨rfl, ?_⟩
  intro p hp
  fin_cases p
  · exact absurd rfl hp
  · rfl
  · rfl
  · rfl

lemma update_quadF_one (A B C D X : TField (I := I) (M := M)) :
    Function.update (quadF A B C D) 1 X = quadF A X C D := by
  rw [Function.update_eq_iff]
  refine ⟨rfl, ?_⟩
  intro p hp
  fin_cases p
  · rfl
  · exact absurd rfl hp
  · rfl
  · rfl

lemma update_quadF_two (A B C D X : TField (I := I) (M := M)) :
    Function.update (quadF A B C D) 2 X = quadF A B X D := by
  rw [Function.update_eq_iff]
  refine ⟨rfl, ?_⟩
  intro p hp
  fin_cases p
  · rfl
  · rfl
  · exact absurd rfl hp
  · rfl

lemma update_quadF_three (A B C D X : TField (I := I) (M := M)) :
    Function.update (quadF A B C D) 3 X = quadF A B C X := by
  rw [Function.update_eq_iff]
  refine ⟨rfl, ?_⟩
  intro p hp
  fin_cases p
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hp

/-- `ckt` on the packed tuple computes `covKRmExt` with separated curvature slots. -/
lemma ckt_quadF (g : SMet I M) (k : ℕ) (w : Fin k → TField (I := I) (M := M))
    (A B C D : TField (I := I) (M := M)) :
    ckt g k (mkT w (quadF A B C D)) = covKRmExt g k w A B C D := by
  funext y
  rw [ckt_mkT_eq g k w (quadF A B C D) y]
  simp only [quadF_zero, quadF_one, quadF_two, quadF_three]

/-- Smoothness of a packed tuple of smooth fields. -/
lemma smoothF_mkT {k : ℕ} {w : Fin k → TField (I := I) (M := M)} (hw : ∀ i, SmoothF (w i))
    {B : Fin 4 → TField (I := I) (M := M)} (hB : ∀ p, SmoothF (B p)) :
    ∀ s, SmoothF (mkT w B s) := by
  intro s
  refine Fin.addCases (motive := fun s => SmoothF (mkT w B s)) ?_ ?_ s
  · intro i
    rw [mkT_castAdd]
    exact hw i
  · intro p
    rw [mkT_natAdd]
    exact hB p

lemma smoothF_mkT' {k : ℕ} {w : Fin k → TField (I := I) (M := M)}
    (hw : ∀ i, SmoothTField (I := I) (M := M) (w i))
    {B : Fin 4 → TField (I := I) (M := M)}
    (hB : ∀ p, SmoothTField (I := I) (M := M) (B p)) :
    ∀ s, SmoothF (mkT w B s) :=
  smoothF_mkT (fun i => smoothF_of_smoothTField (hw i))
    (fun p => smoothF_of_smoothTField (hB p))

lemma smoothTField_quadF {A B C D : TField (I := I) (M := M)}
    (hA : SmoothTField (I := I) (M := M) A) (hB : SmoothTField (I := I) (M := M) B)
    (hC : SmoothTField (I := I) (M := M) C) (hD : SmoothTField (I := I) (M := M) D) :
    ∀ p, SmoothTField (I := I) (M := M) (quadF A B C D p) := by
  intro p
  fin_cases p
  · simpa using hA
  · simpa using hB
  · simpa using hC
  · simpa using hD

/-- Additivity of `ckt` in one slot, in the form supplied by `TensProp`. -/
lemma covK_slot_add (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {w : Fin k → TField (I := I) (M := M)} (hw : ∀ i, SmoothTField (I := I) (M := M) (w i))
    {B : Fin 4 → TField (I := I) (M := M)} (hB : ∀ p, SmoothTField (I := I) (M := M) (B p))
    (s : Fin (k + 4)) {X Y : TField (I := I) (M := M)}
    (hX : SmoothTField (I := I) (M := M) X) (hY : SmoothTField (I := I) (M := M) Y) :
    ckt g k (Function.update (mkT w B) s (X + Y))
      = ckt g k (Function.update (mkT w B) s X) + ckt g k (Function.update (mkT w B) s Y) :=
  TensProp_add hLC g (tensProp_all hLC g k) (smoothF_mkT' hw hB) s
    (smoothF_of_smoothTField hX) (smoothF_of_smoothTField hY)

/-- Homogeneity of `ckt` in one slot under a smooth scalar. -/
lemma covK_slot_smul (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {w : Fin k → TField (I := I) (M := M)} (hw : ∀ i, SmoothTField (I := I) (M := M) (w i))
    {B : Fin 4 → TField (I := I) (M := M)} (hB : ∀ p, SmoothTField (I := I) (M := M) (B p))
    (s : Fin (k + 4)) (f : M → ℝ) (hf : CMDiff ∞ f) {X : TField (I := I) (M := M)}
    (hX : SmoothTField (I := I) (M := M) X) :
    ckt g k (Function.update (mkT w B) s (f • X)) = f • ckt g k (Function.update (mkT w B) s X) := by
  have h1 := (tensProp_all hLC g k (mkT w B) (smoothF_mkT' hw hB)).2.1 s X X f
    (fun _ : M => (0 : ℝ)) (smoothF_of_smoothTField hX) (smoothF_of_smoothTField hX) hf
    (contMDiff_const (c := (0 : ℝ)))
  have e1 : f • X + (fun _ : M => (0 : ℝ)) • X = f • X := by funext z; simp
  have e2 : f • ckt g k (Function.update (mkT w B) s X)
      + (fun _ : M => (0 : ℝ)) • ckt g k (Function.update (mkT w B) s X)
      = f • ckt g k (Function.update (mkT w B) s X) := by funext z; simp
  rw [e1, e2] at h1
  exact h1

end Aux

/-- **`C^∞(M)`-linearity of `∇^k Rm` in its `k + 4` field slots** (`KrLinear`, see
`Submission/Work/Diff/EXT/curvDefs.lean`): the field-level expression `covKRmExt g k V A B C D` is
additive and `C^∞(M)`-homogeneous in each of its `k` derivative slots and in each of its four
curvature slots (as an identity of functions `M → ℝ`).

PROOF: induction on `k` using the recursion defining `covKRmExt`.
* `k = 0`: `covKRmExt g 0 _ A B C D = fun y ↦ rmP g y (A y) (B y) (C y) (D y)`; use the proved
  `Work.Diff.GE.rmP_add_fst/…/rmP_smul_fst/…` (module `Submission.Work.Diff.GE.NablaRm`) for constant
  scalars and the pointwise form for a function `f`.
* `k + 1`: unfold; the `mvfderiv` term is additive/homogeneous in the direction `V 0` by linearity of
  `mvfderiv` in its direction argument, and the derivative of a sum is handled by `mvfderiv_add`
  which needs `MDiffAt` of the two summands — these are the *intermediate* expressions
  `covKRmExt g j (…)` for `j ≤ k`, which are smooth for smooth fields by the corollary of
  `Work.Diff.EXT.covK_familySmooth` (fixed-metric case); each correction term is handled by the
  induction hypothesis together with additivity/homogeneity of `lcOf g` in each of its field slots
  (`IsCovariantDerivativeOn.add`, `.leibniz`, and smoothness of `lcOf g X` for smooth `X`). -/
theorem covK_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (k : ℕ) :
    KrLinear (I := I) (M := M) g k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- additivity in a differentiation slot
    intro i V V' A B C D hV hV' hA hB hC hD
    have h := covK_slot_add hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.castAdd 4 i) (X := V i) (Y := V') (hV i) hV'
    simpa only [update_castAdd_mkT, Function.update_eq_self, ckt_quadF] using h
  · -- homogeneity in a differentiation slot
    intro i V f A B C D hf hV hA hB hC hD
    have h := covK_slot_smul hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.castAdd 4 i) f hf (X := V i) (hV i)
    simpa only [update_castAdd_mkT, Function.update_eq_self, ckt_quadF] using h
  · -- additivity in the first curvature slot
    intro V A A' B C D hV hA hA' hB hC hD
    have h := covK_slot_add hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.natAdd k 0) (X := A) (Y := A') hA hA'
    simpa only [update_natAdd_mkT, update_quadF_zero, ckt_quadF] using h
  · -- homogeneity in the first curvature slot
    intro V f A B C D hf hV hA hB hC hD
    have h := covK_slot_smul hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.natAdd k 0) f hf (X := A) hA
    simpa only [update_natAdd_mkT, update_quadF_zero, ckt_quadF] using h
  · -- additivity in the second curvature slot
    intro V A B B' C D hV hA hB hB' hC hD
    have h := covK_slot_add hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.natAdd k 1) (X := B) (Y := B') hB hB'
    simpa only [update_natAdd_mkT, update_quadF_one, ckt_quadF] using h
  · -- homogeneity in the second curvature slot
    intro V f A B C D hf hV hA hB hC hD
    have h := covK_slot_smul hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.natAdd k 1) f hf (X := B) hB
    simpa only [update_natAdd_mkT, update_quadF_one, ckt_quadF] using h
  · -- additivity in the third curvature slot
    intro V A B C C' D hV hA hB hC hC' hD
    have h := covK_slot_add hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.natAdd k 2) (X := C) (Y := C') hC hC'
    simpa only [update_natAdd_mkT, update_quadF_two, ckt_quadF] using h
  · -- homogeneity in the third curvature slot
    intro V f A B C D hf hV hA hB hC hD
    have h := covK_slot_smul hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.natAdd k 2) f hf (X := C) hC
    simpa only [update_natAdd_mkT, update_quadF_two, ckt_quadF] using h
  · -- additivity in the fourth curvature slot
    intro V A B C D D' hV hA hB hC hD hD'
    have h := covK_slot_add hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.natAdd k 3) (X := D) (Y := D') hD hD'
    simpa only [update_natAdd_mkT, update_quadF_three, ckt_quadF] using h
  · -- homogeneity in the fourth curvature slot
    intro V f A B C D hf hV hA hB hC hD
    have h := covK_slot_smul hLC g k (w := V) hV (B := quadF A B C D)
      (smoothTField_quadF hA hB hC hD) (Fin.natAdd k 3) f hf (X := D) hD
    simpa only [update_natAdd_mkT, update_quadF_three, ckt_quadF] using h

end Work.Diff.EXT
