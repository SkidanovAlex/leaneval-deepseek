import Mathlib
import Submission.Work.Diff.GE.CurvDerivDefs
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.GE.kato_covRm_field
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.contMDiff_rmP_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `∇³Rm`-bookkeeping for `Work.Diff.GE.cov3Rm_swap`

This module supplies the objects and the elementary tensor facts used by the proof of the
third-derivative symmetry

`cov3Rm g x X Y P a b c d - cov3Rm g x X P Y a b c d = -(…curvDeriv… ) - (…covRm…)`.

The mathematical content is the following.  Write `T = Rm` for the curvature `(0,4)`-tensor and
`∇³T` for its third covariant derivative; `cov3Rm g x X Y P a b c d = ∇³T(X,Y,P;a,b,c,d)` has
`X,Y,P` as derivative slots.  Then, by the Ricci identity for the second covariant derivative
(`cov2Rm g x u p a b c d - cov2Rm g x p u a b c d = -∑_i Rm(… R(u,p)· …)`),

  `∇³T(X,Y,P) - ∇³T(X,P,Y) = - ∇_X (R(Y,P) · T)`,

and the right hand side is the covariant derivative of the `(0,6)`-tensor
`Φ(r,s,a,b,c,d) = Rm(R(r,s)a,b,c,d) + Rm(a,R(r,s)b,c,d) + Rm(a,b,R(r,s)c,d) + Rm(a,b,c,R(r,s)d)`
evaluated at `(Y,P,a,b,c,d)`, which by the Leibniz rule is the sum of the two brackets in the
statement of `cov3Rm_swap`.

* `phiTV`/`phiT` is `Φ` at a point / as a field-level tensor of arity `Fin 6`;
* `hexad` packages six fields (or six vectors) into a `Fin 6`-indexed tuple;
* `curvDeriv_pairing` identifies the vector `curvDeriv g x X Y P Z` by
  `g.inner x (curvDeriv g x X Y P Z) Z' = covRm g x X Y P Z' Z`;
* `covAlong_curv_section` is the Leibniz rule for the covariant derivative of the curvature
  section `y ↦ R(Y,P)A(y)`.

Everything here is stated for `IsManifold I ∞ M` (smooth) and `T2Space M`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## The curvature contraction `Φ` -/

/-- The curvature contraction at a point:
`Φ(u,v,a,b,c,d) = Rm(R(u,v)a,b,c,d) + Rm(a,R(u,v)b,c,d) + Rm(a,b,R(u,v)c,d) + Rm(a,b,c,R(u,v)d)`,
i.e. the action of the curvature endomorphism `R(u,v)` on (each slot of) `Rm`.
This is the right hand side of the Ricci identity `cov2Rm_ricci`, with the sign removed. -/
noncomputable def phiTV (g : SMet I M) (x : M) (T : Fin 6 → TangentSpace I x) : ℝ :=
  rmP g x (rmVec (lcOf g) x (T 0) (T 1) (T 2)) (T 3) (T 4) (T 5)
  + rmP g x (T 2) (rmVec (lcOf g) x (T 0) (T 1) (T 3)) (T 4) (T 5)
  + rmP g x (T 2) (T 3) (rmVec (lcOf g) x (T 0) (T 1) (T 4)) (T 5)
  + rmP g x (T 2) (T 3) (T 4) (rmVec (lcOf g) x (T 0) (T 1) (T 5))

/-- `Φ` as a field-level tensor of arity `Fin 6`; the curvature sections are written with `curv`
so that all four `Φ`-summands are contractions of *smooth* sections. -/
noncomputable def phiT (g : SMet I M) : ExtTensor (I := I) (M := M) (Fin 6) :=
  fun F => fun y =>
    rmP g y (curv (lcOf g) (F 0) (F 1) (F 2) y) (F 3 y) (F 4 y) (F 5 y)
    + rmP g y (F 2 y) (curv (lcOf g) (F 0) (F 1) (F 3) y) (F 4 y) (F 5 y)
    + rmP g y (F 2 y) (F 3 y) (curv (lcOf g) (F 0) (F 1) (F 4) y) (F 5 y)
    + rmP g y (F 2 y) (F 3 y) (F 4 y) (curv (lcOf g) (F 0) (F 1) (F 5) y)

/-- **The curvature section is `rmVec` pointwise.** For smooth fields `X,Y,Z`, the section
`y ↦ curv (lcOf g) X Y Z y` has at `y` the value of the frozen `rmVec (lcOf g) y (X y) (Y y) (Z y)`. -/
theorem curv_section_apply_eq_rmVec (hLC : LCSmooth I M) (g : SMet I M)
    {X Y Z : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (y : M) :
    curv (lcOf g) X Y Z y = rmVec (lcOf g) y (X y) (Y y) (Z y) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov⟩ := (hLC g).1
  show curv (lcOf g) X Y Z y
    = curv (lcOf g) (smoothExt y (X y)) (smoothExt y (Y y)) (smoothExt y (Z y)) y
  exact (Submission.Curvature.curv_eq_of_apply_eq (lcOf g) hcov (smoothExt_cmdiff y (X y)) hX
    (smoothExt_cmdiff y (Y y)) hY (smoothExt_cmdiff y (Z y)) hZ
    (smoothExt_apply y (X y)) (smoothExt_apply y (Y y)) (smoothExt_apply y (Z y))).symm

/-- **`phiT` at a point is `phiTV`.**  For smooth fields, the curvature section
`y ↦ R(F 0, F 1)(F j)(y)` has value `rmVec (lcOf g) y (F 0 y) (F 1 y) (F j y)` at `y`. -/
theorem phiT_apply (hLC : LCSmooth I M) (g : SMet I M)
    {F : Fin 6 → (Π y : M, TangentSpace I y)} (hF : ∀ i, CMDiff ∞ (T% (F i))) (y : M) :
    phiT g F y = phiTV g y (fun i => F i y) := by
  have hcurv : ∀ i : Fin 6, curv (lcOf g) (F 0) (F 1) (F i) y
      = rmVec (lcOf g) y (F 0 y) (F 1 y) (F i y) :=
    fun i => curv_section_apply_eq_rmVec (I := I) (M := M) hLC g (hF 0) (hF 1) (hF i) y
  simp only [phiT, phiTV, hcurv 2, hcurv 3, hcurv 4, hcurv 5]

/-! ## Six-tuples -/

/-- Six fields packaged as a `Fin 6`-indexed tuple. -/
abbrev hexad (Y P A B C D : Π y : M, TangentSpace I y) : Fin 6 → (Π y : M, TangentSpace I y) :=
  ![Y, P, A, B, C, D]

/-- Six tangent vectors packaged as a `Fin 6`-indexed tuple. -/
abbrev hexadV {x : M} (Y P A B C D : TangentSpace I x) : Fin 6 → TangentSpace I x :=
  ![Y, P, A, B, C, D]

@[simp] theorem hexad_zero (Y P A B C D : Π y : M, TangentSpace I y) :
    hexad Y P A B C D 0 = Y := rfl
@[simp] theorem hexad_one (Y P A B C D : Π y : M, TangentSpace I y) :
    hexad Y P A B C D 1 = P := rfl
@[simp] theorem hexad_two (Y P A B C D : Π y : M, TangentSpace I y) :
    hexad Y P A B C D 2 = A := rfl
@[simp] theorem hexad_three (Y P A B C D : Π y : M, TangentSpace I y) :
    hexad Y P A B C D 3 = B := rfl
@[simp] theorem hexad_four (Y P A B C D : Π y : M, TangentSpace I y) :
    hexad Y P A B C D 4 = C := rfl
@[simp] theorem hexad_five (Y P A B C D : Π y : M, TangentSpace I y) :
    hexad Y P A B C D 5 = D := rfl

@[simp] theorem hexadV_zero {x : M} (Y P A B C D : TangentSpace I x) :
    hexadV Y P A B C D 0 = Y := rfl
@[simp] theorem hexadV_one {x : M} (Y P A B C D : TangentSpace I x) :
    hexadV Y P A B C D 1 = P := rfl
@[simp] theorem hexadV_two {x : M} (Y P A B C D : TangentSpace I x) :
    hexadV Y P A B C D 2 = A := rfl
@[simp] theorem hexadV_three {x : M} (Y P A B C D : TangentSpace I x) :
    hexadV Y P A B C D 3 = B := rfl
@[simp] theorem hexadV_four {x : M} (Y P A B C D : TangentSpace I x) :
    hexadV Y P A B C D 4 = C := rfl
@[simp] theorem hexadV_five {x : M} (Y P A B C D : TangentSpace I x) :
    hexadV Y P A B C D 5 = D := rfl

/-! ## Expansion in an orthonormal frame, in every dimension -/

/-- Expansion in the chosen orthonormal frame, without a dimension hypothesis
(the degenerate case `finrank = 0` is handled by `Subsingleton`). -/
theorem frame_expand (g : SMet I M) (x : M) (v : TangentSpace I x) :
    ∑ i, g.inner x (onFrame g x i) v • onFrame g x i = v := by
  by_cases hpos : 0 < Module.finrank ℝ E
  · exact sum_inner_smul_eq_self (I := I) (M := M) g x hpos (onFrame g x)
      (isONFrame_onFrame (I := I) (M := M) g x) v
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hpos
    haveI hsubE : Subsingleton E := Module.finrank_zero_iff.mp h0
    haveI hsubT : Subsingleton (TangentSpace I x) := hsubE
    rw [Subsingleton.elim v 0]
    apply Finset.sum_eq_zero
    intro i _
    exact absurd (h0 ▸ i.isLt) (Nat.not_lt_zero i.val)

/-! ## Linearity of `covRm` in its fourth argument, in sum form -/

/-- `covRm` vanishes when its fourth argument is zero. -/
theorem covRm_zero_fourth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b d : TangentSpace I x) :
    covRm g x v a b 0 d = 0 := by
  have h := covRm_linear_fth (I := I) (M := M) hLC g x v a b (0 : ℝ) (0 : ℝ)
    (0 : TangentSpace I x) (0 : TangentSpace I x) d
  simpa using h

/-- `covRm` is additive over finite linear combinations in its fourth argument. -/
theorem covRm_sum_fourth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b d : TangentSpace I x) {ι' : Type*} (s : Finset ι') (c : ι' → ℝ)
    (w : ι' → TangentSpace I x) :
    covRm g x v a b (∑ i ∈ s, c i • w i) d = ∑ i ∈ s, c i * covRm g x v a b (w i) d := by
  classical
  induction s using Finset.induction with
  | empty => simp [covRm_zero_fourth (I := I) (M := M) hLC g x v a b d]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have h := covRm_linear_fth (I := I) (M := M) hLC g x v a b (c j) (1 : ℝ) (w j)
      (∑ i ∈ s, c i • w i) d
    rw [one_smul] at h
    rw [h, ih]
    ring

/-! ## `curvDeriv` as a pairing -/

/-- **Characterisation of `curvDeriv`.**  The vector `curvDeriv g x X Y P Z = (∇_X R)(Y,P)Z` is
determined by `g.inner x (curvDeriv g x X Y P Z) Z' = covRm g x X Y P Z' Z = (∇_X Rm)(Y,P,Z',Z)`. -/
theorem curvDeriv_pairing (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (X Y P Z Z' : TangentSpace I x) :
    g.inner x (curvDeriv g x X Y P Z) Z' = covRm g x X Y P Z' Z := by
  rw [curvDeriv]
  rw [map_sum]
  simp only [ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  conv_rhs => rw [← frame_expand (I := I) (M := M) g x Z']
  rw [covRm_sum_fourth (I := I) (M := M) hLC g x X Y P Z Finset.univ
    (fun i => g.inner x (onFrame g x i) Z') (onFrame g x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-!
## Proof plan for the downstream step `Work.Diff.GE.cov3Rm_swap_extD_phiT`

The companion lemma (module `Work.Diff.GE.cov3Rm_swap_extD_phiT`) states that for
`Xs := smoothExt x X` and `F := hexad (smoothExt x Y) (smoothExt x P) (smoothExt x a)
(smoothExt x b) (smoothExt x c) (smoothExt x d)` one has

`extD (lcOf g) (phiT g) x Xs F = B₁ + B₂`

with `B₁ = rmP g x (curvDeriv g x X Y P a) b c d + rmP g x a (curvDeriv g x X Y P b) c d
+ rmP g x a b (curvDeriv g x X Y P c) d + rmP g x a b c (curvDeriv g x X Y P d)` and
`B₂ = covRm g x X (rmVec (lcOf g) x Y P a) b c d + … + covRm g x X a b c (rmVec (lcOf g) x Y P d)`.

Sketch.  By `extD_eq`,
`extD (lcOf g) (phiT g) x Xs F = mvfderiv (phiT g F) x (Xs x) - ∑ i, phiT g (upd (lcOf g) Xs F i) x`.

* Write `A j := fun y => curv (lcOf g) (F 0) (F 1) (F (2+j)) y` (smooth, by
  `Work.Diff.GE.contMDiff_curv_fields`) and split `phiT g F = T₀ + T₁ + T₂ + T₃` where
  `T₀ = fun y => rmP g y (A 0 y) (F 3 y) (F 4 y) (F 5 y)`, `T₁ = fun y => rmP g y (F 2 y) (A 1 y) (F 4 y) (F 5 y)`,
  `T₂ = fun y => rmP g y (F 2 y) (F 3 y) (A 2 y) (F 5 y)`, `T₃ = fun y => rmP g y (F 2 y) (F 3 y) (F 4 y) (A 3 y)`.
  `mvfderiv_add` (differentiability from `rmP_fields_smooth`) splits the derivative, and
  `kato_covRm_field` applied to the fields `(Xs, A j, B j, C j, D j)` (the four slots of `T j`)
  gives `covRm g x (Xs x) (A j x) (B j x) (C j x) (D j x)` plus the four terms with `∇` in one slot.
  The `covRm`-terms are `B₂` since `A j x = curv (lcOf g) (F 0) (F 1) (F (2+j)) x
  = rmVec (lcOf g) x (F 0 x) (F 1 x) (F (2+j) x) = rmVec (lcOf g) x Y P (slot j)` by
  `Work.Diff.GE.curv_section_apply_eq_rmVec` and `smoothExt_apply`.
* The term `rmP g x ((lcOf g) (A j) x (Xs x)) (B j x) (C j x) (D j x)` is rewritten with
  `Work.Diff.GE.covAlong_curv_section` and `Work.Diff.GE.rmP_add_fst`; its `curvDeriv`-summand
  contributes the `j`-th term of `B₁`, while the three extra summands
  `curv (lcOf g) (covD (F 0)) (F 1) (slot j) x`, `curv (lcOf g) (F 0) (covD (F 1)) (slot j) x`,
  `curv (lcOf g) (F 0) (F 1) (covD slot) x` cancel against `∑ i, phiT g (upd (lcOf g) Xs F i) x`
  (the `i = 0, 1` corrections and the `i = 2+j` corrections respectively, after
  `Work.Diff.GE.curv_section_apply_eq_rmVec`; `covD` is `fun y => (lcOf g) (F i) y (Xs y)`,
  i.e. `Work.Diff.GE.covAlong (lcOf g) Xs (F i)`).
* `Fin.sum_univ_six` expands both `Fin 6`-sums; `Function.update_apply` (with `Fin.isValue`,
  `Fin.reduceFinMk`) evaluates `upd`; finish with `ring`/`Finset.sum_congr`.

`curvDeriv_pairing` identifies `curvDeriv g x X Y P Z` by its pairings with all vectors and is the
route to any statement about `curvDeriv` alone (it uses `frame_expand`, which has no dimension
hypothesis).
-/

/-! ## The second covariant derivative of the curvature as a field-level tensor -/

/-- Reindexing a tuple of fields: `(tupSw σ F) i = F (σ i)`. -/
abbrev tupSw {ι : Type*} (σ : ι → ι) (F : ι → (Π y : M, TangentSpace I y)) :
    ι → (Π y : M, TangentSpace I y) := fun i => F (σ i)

/-- The permutation of `Fin 6` exchanging the first two indices. -/
def swap01 : Equiv.Perm (Fin 6) where
  toFun := fun i => ![1, 0, 2, 3, 4, 5] i
  invFun := fun i => ![1, 0, 2, 3, 4, 5] i
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp] theorem swap01_zero : swap01 0 = 1 := rfl
@[simp] theorem swap01_one : swap01 1 = 0 := rfl
@[simp] theorem swap01_two : swap01 2 = 2 := rfl
@[simp] theorem swap01_three : swap01 3 = 3 := rfl
@[simp] theorem swap01_four : swap01 4 = 4 := rfl
@[simp] theorem swap01_five : swap01 5 = 5 := rfl

/-- `swap01` is an involution. -/
theorem swap01_invol (i : Fin 6) : swap01 (swap01 i) = i := by fin_cases i <;> rfl

/-- The second covariant derivative `∇²Rm` as a field-level tensor of arity `Fin 6`
(the two derivative directions and the four curvature slots). -/
noncomputable def cov2T (g : SMet I M) : ExtTensor (I := I) (M := M) (Fin 6) :=
  fun F => fun y => cov2Rm g y (F 0 y) (F 1 y) (F 2 y) (F 3 y) (F 4 y) (F 5 y)

/-- `cov2T g` is smooth on smooth tuples. -/
theorem cov2T_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {F : Fin 6 → (Π y : M, TangentSpace I y)} (hF : SmoothTuple F) :
    SmoothFunT (I := I) (M := M) (cov2T g F) :=
  Kato3.cov2Rm_field_smooth (g := g) hLC (hF 0) (hF 1) (hF 2) (hF 3) (hF 4) (hF 5)

/-- The pointwise Ricci identity for `∇²Rm` (`Work.Diff.GE.cov2Rm_ricci`), as a hypothesis. -/
abbrev RicciPt (g : SMet I M) : Prop :=
  ∀ (y : M) (u p a b c d : TangentSpace I y),
    cov2Rm g y u p a b c d - cov2Rm g y p u a b c d
      = -(rmP g y (rmVec (lcOf g) y u p a) b c d
          + rmP g y a (rmVec (lcOf g) y u p b) c d
          + rmP g y a b (rmVec (lcOf g) y u p c) d
          + rmP g y a b c (rmVec (lcOf g) y u p d))

/-- **The Ricci identity for `∇²Rm` in tuple form.**  The difference of `cov2T g` at a smooth tuple
`F` and at the tuple with the first two slots exchanged is the curvature contraction `-phiT g F`. -/
theorem cov2T_sub_swap (hLC : LCSmooth I M) (g : SMet I M) (hRicci : RicciPt g)
    {F : Fin 6 → (Π y : M, TangentSpace I y)} (hF : SmoothTuple F) :
    cov2T g F - cov2T g (tupSw swap01 F) = -phiT g F := by
  funext y
  have h := hRicci y (F 0 y) (F 1 y) (F 2 y) (F 3 y) (F 4 y) (F 5 y)
  have hphi := phiT_apply (I := I) (M := M) hLC g hF y
  simp only [cov2T, tupSw, swap01_zero, swap01_one, swap01_two, swap01_three, swap01_four,
    swap01_five, Pi.sub_apply, Pi.neg_apply, hphi, phiTV]
  rw [h]

/-! ## Covariant differentiation at a swapped tuple -/

/-- **`extD` at a tuple and at its first-two-slots-swapped version.**  If a field-level tensor `τ`
satisfies `τ G - τ (G ∘ σ) = -τ' G` for every smooth tuple `G` (with `σ` an involution on the index
type), then the same identity holds for the covariant derivatives:
`extD τ F - extD τ (F ∘ σ) = -extD τ' F`. -/
theorem extD_sub_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (hσσ : ∀ i, σ (σ i) = i)
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (hcov : CovSmooth cov)
    (τ τ' : ExtTensor (I := I) (M := M) ι)
    (hτ : ∀ G : ι → (Π y : M, TangentSpace I y),
      SmoothTuple (I := I) (M := M) G → SmoothFunT (I := I) (M := M) (τ G))
    (hpt : ∀ G : ι → (Π y : M, TangentSpace I y), SmoothTuple (I := I) (M := M) G →
      τ G - τ (tupSw σ G) = -τ' G)
    (x : M) (X : Π y : M, TangentSpace I y) (hX : SmoothFieldT (I := I) (M := M) X)
    (F : ι → (Π y : M, TangentSpace I y)) (hF : SmoothTuple F) :
    extD cov τ x X F - extD cov τ x X (tupSw σ F) = -extD cov τ' x X F := by
  classical
  have hFσ : SmoothTuple (tupSw σ F) := fun i => hF (σ i)
  have hd1 : MDiffAt (τ F) x := (hτ F hF).contMDiffAt.mdifferentiableAt (by simp)
  have hd2 : MDiffAt (τ (tupSw σ F)) x :=
    (hτ (tupSw σ F) hFσ).contMDiffAt.mdifferentiableAt (by simp)
  have hsub : mvfderiv I (τ F - τ (tupSw σ F)) x (X x)
      = mvfderiv I (τ F) x (X x) - mvfderiv I (τ (tupSw σ F)) x (X x) := by
    rw [mvfderiv_sub hd1 hd2, ContinuousLinearMap.sub_apply]
  have hmv : mvfderiv I (τ F) x (X x) - mvfderiv I (τ (tupSw σ F)) x (X x)
      = -mvfderiv I (τ' F) x (X x) := by
    rw [← hsub, hpt F hF, mvfderiv_neg]
    rfl
  have hcomp : ∀ i : ι, upd cov X (tupSw σ F) i = tupSw σ (upd cov X F (σ i)) := by
    intro i
    funext k
    simp only [upd, tupSw, covAlong, Function.update_apply]
    by_cases hk : k = i
    · subst hk; simp
    · have hk' : σ k ≠ σ i := fun hh => hk (σ.injective hh)
      simp [hk, hk']
  have hterm : ∀ i : ι, τ (upd cov X (tupSw σ F) i) x
      = τ (upd cov X F (σ i)) x + τ' (upd cov X F (σ i)) x := by
    intro i
    have hG : SmoothTuple (upd cov X F (σ i)) := smoothTuple_upd cov hcov hX hF (σ i)
    have h := congrFun (hpt (upd cov X F (σ i)) hG) x
    rw [hcomp i]
    simp only [Pi.sub_apply, Pi.neg_apply] at h
    linarith
  have hsum : (∑ i, τ (upd cov X (tupSw σ F) i) x)
      = (∑ i, τ (upd cov X F i) x) + (∑ i, τ' (upd cov X F i) x) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Equiv.sum_comp σ (fun j => τ (upd cov X F j) x),
      Equiv.sum_comp σ (fun j => τ' (upd cov X F j) x)]
  rw [extD_eq, extD_eq, extD_eq]
  linarith [hmv, hsum]

/-! ## `cov3RmExt` as the `extD` of `∇²Rm` -/

/-- **`cov3RmExt` is the covariant derivative of `∇²Rm`.**  The six Leibniz corrections of
`cov3RmExt` are the six slots of the `(0,6)`-tensor `cov2T g`. -/
theorem cov3RmExt_eq_extD (hLC : LCSmooth I M) (g : SMet I M) (x : M) (w : TangentSpace I x)
    (Xs U V A B C D : Π y : M, TangentSpace I y) (hXs : Xs x = w) :
    cov3RmExt g x w U V A B C D
      = extD (lcOf g) (cov2T g) x Xs (hexad U V A B C D) := by
  have hsum : (∑ i : Fin 6, cov2T g (upd (lcOf g) Xs (hexad U V A B C D) i) x)
      = cov2Rm g x (lcOf g U x (Xs x)) (V x) (A x) (B x) (C x) (D x)
        + cov2Rm g x (U x) (lcOf g V x (Xs x)) (A x) (B x) (C x) (D x)
        + cov2Rm g x (U x) (V x) (lcOf g A x (Xs x)) (B x) (C x) (D x)
        + cov2Rm g x (U x) (V x) (A x) (lcOf g B x (Xs x)) (C x) (D x)
        + cov2Rm g x (U x) (V x) (A x) (B x) (lcOf g C x (Xs x)) (D x)
        + cov2Rm g x (U x) (V x) (A x) (B x) (C x) (lcOf g D x (Xs x)) := by
    rw [Fin.sum_univ_six]
    simp only [cov2T, hexad_zero, hexad_one, hexad_two, hexad_three, hexad_four, hexad_five,
      upd, covAlong, Function.update_apply, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, reduceIte]
    try ring
  have hmv : mvfderiv I (cov2T g (hexad U V A B C D)) x (Xs x)
      = mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x (Xs x) := rfl
  rw [← hXs, cov3RmExt, extD_eq, hmv, hsum]
  try ring

/-! ## Step 1 of `cov3Rm_swap`: the two third derivatives differ by `-extD phiT` -/

/-- **Step 1.**  Antisymmetrising the second and third derivative slots of `∇³Rm` is
`-extD (lcOf g) (phiT g)`: the Ricci identity for `∇²Rm` (in tuple form, `cov2T_sub_swap`) applied
to the tuple and to its six slot-corrections. -/
theorem cov3Rm_swap_step1 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (X Y P a b c d : TangentSpace I x) (hRicci : RicciPt g) :
    cov3Rm g x X Y P a b c d - cov3Rm g x X P Y a b c d
      = -extD (lcOf g) (phiT g) x (smoothExt x X)
          (hexad (smoothExt x Y) (smoothExt x P) (smoothExt x a) (smoothExt x b)
            (smoothExt x c) (smoothExt x d)) := by
  have hcov : CovSmooth (lcOf g) := (hLC g).1.some
  have hF : SmoothTuple (hexad (smoothExt x Y) (smoothExt x P) (smoothExt x a)
      (smoothExt x b) (smoothExt x c) (smoothExt x d)) := by
    intro i
    fin_cases i <;>
      simp only [hexad_zero, hexad_one, hexad_two, hexad_three, hexad_four, hexad_five] <;>
      first
        | exact smoothExt_cmdiff x Y
        | exact smoothExt_cmdiff x P
        | exact smoothExt_cmdiff x a
        | exact smoothExt_cmdiff x b
        | exact smoothExt_cmdiff x c
        | exact smoothExt_cmdiff x d
  have hswap : hexad (smoothExt x P) (smoothExt x Y) (smoothExt x a) (smoothExt x b)
        (smoothExt x c) (smoothExt x d)
      = tupSw swap01 (hexad (smoothExt x Y) (smoothExt x P) (smoothExt x a) (smoothExt x b)
        (smoothExt x c) (smoothExt x d)) := by
    funext i
    fin_cases i <;> rfl
  have h1 : cov3Rm g x X Y P a b c d
      = extD (lcOf g) (cov2T g) x (smoothExt x X) (hexad (smoothExt x Y) (smoothExt x P)
          (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) := by
    rw [cov3Rm]
    exact cov3RmExt_eq_extD (I := I) (M := M) hLC g x X (smoothExt x X) (smoothExt x Y)
      (smoothExt x P) (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)
      (smoothExt_apply x X)
  have h2 : cov3Rm g x X P Y a b c d
      = extD (lcOf g) (cov2T g) x (smoothExt x X) (tupSw swap01 (hexad (smoothExt x Y)
          (smoothExt x P) (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d))) := by
    rw [cov3Rm, cov3RmExt_eq_extD (I := I) (M := M) hLC g x X (smoothExt x X) (smoothExt x P)
      (smoothExt x Y) (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)
      (smoothExt_apply x X), hswap]
  have hstep := extD_sub_swap (I := I) (M := M) swap01 swap01_invol (lcOf g) hcov (cov2T g)
    (phiT g) (fun G hG => cov2T_smooth hLC g hG) (fun G hG => cov2T_sub_swap hLC g hRicci hG)
    x (smoothExt x X) (smoothExt_cmdiff x X)
    (hexad (smoothExt x Y) (smoothExt x P) (smoothExt x a) (smoothExt x b) (smoothExt x c)
      (smoothExt x d)) hF
  rw [h1, h2, hstep]

end Work.Diff.GE
