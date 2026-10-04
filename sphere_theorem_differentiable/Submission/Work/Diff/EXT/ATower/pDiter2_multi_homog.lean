import Mathlib
import Submission.Work.Diff.EXT.ATower.scaleTup
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestTower
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.RicFlip.RicT_props
import Submission.Work.Diff.EXT.ric_bound_of_curvBound

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multi-homogeneity of the packed Ricci tower `pDiter2`

`Work.Diff.EXT.ATower.pDiter2_multi_homog` states that the packed iterated covariant derivative
`pDiter2 (lcOf g) (ric2 g') m` is homogeneous of degree `m + 2` in its `m + 2` field slots, with an
*independent* scalar `c j` in each slot:

  `pDiter2 … (scaleTup c F) x = (∏ j, c j) * pDiter2 … F x`.

It is the sharp form of the homogeneity consumed by `Work.Diff.EXT.ConnCov.sharp_of_bnd1_homog`
(the passage from the monotone slot bound `AMB.Bnd1` to the sharp product bound).

## Status: the requested statement is **mis-stated** (it needs `[T2Space M]`)

The proof has to parts.  The *recursion step* is `T2Space`-free and is fully proved below:

* `hom_pD`: `AMB.pD (lcOf g)` preserves slotwise homogeneity.  The `mvfderiv` term is handled by the
  (junk-compatible) constant-factor homogeneity of `mvfderiv` together with the induction
  hypothesis; each correction term needs the homogeneity of `lcOf g` in its *section* slot for
  arbitrary (possibly non-mdifferentiable) fields — `lcOf_smul_field'` — and the linearity of
  `lcOf g X y` in its direction argument.

The *base case* (`m = 0`) is `ric2 g' F x = ricAt (lcOf g') x (F 0 x) (F 1 x)`, so it requires the
frozen `ricAt (lcOf g')` to be bilinear in its two *value* arguments.  `ricAt` is defined through the
`Classical.epsilon`-chosen "smooth extensions" `Submission.Diff.smoothExt x u`, so this needs the
ε-spec

  `CMDiff ∞ (T% (smoothExt x u)) ∧ smoothExt x u x = u`,

which by `Classical.epsilon_spec` needs the predicate `{X | CMDiff ∞ (T% X) ∧ X x = u}` to be
**nonempty**, i.e. a *globally* smooth section of the tangent bundle with value `u` at `x`.  In this
Mathlib the only construction of such a section is

  `Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq`,

whose proof uses `SmoothBumpFunction.nhds_basis_tsupport`, hence `[T2Space M]`; there is no
`T2Space`-free bump/cutoff function.  **The natural candidate witness is false**: the constant model
section `fun y : M ↦ (u : TangentSpace I y)` (which is what the sibling lemma
`Work.Diff.EXT.smE_constModel_noT2` asserts to be smooth) is *nowhere vanishing* for `u ≠ 0`
(its value at `y` is the non-zero model vector `u`, as `TangentSpace I y` is definitionally `E`), so
its smoothness on `M = S²` would produce a nowhere vanishing smooth vector field on the 2-sphere,
contradicting the hairy ball theorem.  Hence the base case cannot be obtained from the definitions in
the generality of the target statement (no `[T2Space M]`); with the unconstrained junk values of
`Classical.epsilon` on a non-`T2` manifold the identity may even fail.

The file therefore records (i) the complete `T2Space`-free *step*, and (ii) the correct statement,
with `[T2Space M]`, as `pDiter2_multi_homog_t2`, proved from the `T2Space`-locked library lemmas
`Work.Diff.EXT.ricAt_smul_middle_L` / `ricAt_smul_last_L` (which are axiom-clean: they depend only on
`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The junk value of the Levi-Civita connection and its `C^∞`-homogeneity in the section slot

Mathlib's `CovariantDerivative.leviCivitaConnection` has
`toFun = leviCivitaAux I = fun Y x ↦ if MDiffAt (T% Y) x then … else 0`.  The two facts recorded
here are therefore pure `dite`-bookkeeping, plus the Leibniz axiom: on an mdifferentiable field the
constant factor can be pulled out with the help of `mdifferentiableAt_const`. -/

/-- `lcOf g X x = 0` when `X` is not mdifferentiable at `x` (the junk branch of
`CovariantDerivative.leviCivitaAux`).  `T2Space`-free version of
`Work.Diff.EXT.lcOf_eq_zero_of_not_mdiffAt`. -/
theorem lcOf_eq_zero_of_not_mdiffAt'
    (g : SMet I M) {X : TField (I := I) (M := M)} {x : M}
    (hX : ¬ MDiffAt (T% X) x) : lcOf g X x = 0 := by
  rw [Submission.Diff.lcOf]
  simp only [CovariantDerivative.leviCivitaConnection]
  exact dite_eq_right hX

/-- The zero section has `lcOf`-value `0`. -/
theorem lcOf_zero_section' (g : SMet I M) (x : M) :
    lcOf g (0 : TField (I := I) (M := M)) x = 0 := by
  have hsm : MDiffAt (T% (0 : TField (I := I) (M := M))) x :=
    Bundle.mdifferentiableAt_zeroSection ℝ (fun y : M => TangentSpace I y)
  have hadd := (CovariantDerivative.isCovariantDerivativeOn (lcOf g) (s := Set.univ)).add hsm hsm
  have hz : (0 : TField (I := I) (M := M)) + 0 = 0 := by
    funext z; simp
  rw [hz] at hadd
  have h : lcOf g 0 x + (0 : TangentSpace I x →L[ℝ] TangentSpace I x)
      = lcOf g 0 x + lcOf g 0 x := by
    rw [add_zero]; exact hadd
  exact (add_left_cancel h).symm

/-- `MDiffAt` of a section is invariant under scaling the section by a nonzero constant. -/
theorem mdiffAt_const_smul_section_iff'
    (c : ℝ) (hc : c ≠ 0) {X : TField (I := I) (M := M)} {x : M} :
    MDiffAt (T% (c • X)) x ↔ MDiffAt (T% X) x := by
  rw [mdifferentiableAt_section (E := fun y : M => TangentSpace I y) I (c • X),
      mdifferentiableAt_section (E := fun y : M => TangentSpace I y) I X]
  have hx : x ∈ (trivializationAt E (fun y : M => TangentSpace I y) x).baseSet :=
    mem_baseSet_trivializationAt E (fun y : M => TangentSpace I y) x
  have heq : (fun z => ((trivializationAt E (fun y : M => TangentSpace I y) x)
          ⟨z, (c • X) z⟩).2)
      =ᶠ[𝓝 x] (c • (fun z => ((trivializationAt E (fun y : M => TangentSpace I y) x)
          ⟨z, X z⟩).2)) := by
    filter_upwards [(trivializationAt E (fun y : M => TangentSpace I y) x).open_baseSet.mem_nhds hx]
      with z hz
    simp only [Pi.smul_apply]
    rw [Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ _ z hz (c • X z),
      Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ _ z hz (X z)]
    simp only [map_smul]
  constructor
  · intro h
    rw [heq.mdifferentiableAt_iff] at h
    have h2 : MDiffAt (c⁻¹ • (c • (fun z => ((trivializationAt E
        (fun y : M => TangentSpace I y) x) ⟨z, X z⟩).2))) x := h.const_smul c⁻¹
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with z
    simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · intro h
    exact heq.mdifferentiableAt_iff.mpr (h.const_smul c)

/-- **`C^∞`-homogeneity of `lcOf g` in its section slot, junk-compatible**: for an *arbitrary*
(possibly non-mdifferentiable) field `X` and a constant `c`, `∇_{cX} = c∇_X`.  This is the
`T2Space`-free version of `Work.Diff.EXT.evolX.lcOf_smul_field`. -/
theorem lcOf_smul_field'
    (g : SMet I M) (c : ℝ) (X : TField (I := I) (M := M)) (x : M) (v : TangentSpace I x) :
    lcOf g (c • X) x v = c • lcOf g X x v := by
  by_cases hX : MDiffAt (T% X) x
  · have hleib := (CovariantDerivative.isCovariantDerivativeOn (lcOf g) (s := Set.univ)).leibniz
      (σ := X) (g := fun _ : M => c) hX (mdifferentiableAt_const (c := c) (x := x))
    have h0 : mvfderiv I (fun _ : M => c) x = 0 := mvfderiv_const c
    rw [h0, ContinuousLinearMap.zero_smulRight, add_zero] at hleib
    have hfun : (fun _ : M => c) • X = c • X := by
      funext z; rfl
    rw [hfun] at hleib
    exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hleib
  · by_cases hc : c = 0
    · subst hc
      have h1 : (0 : ℝ) • X = (0 : TField (I := I) (M := M)) := by
        funext z; simp
      rw [h1, lcOf_zero_section' g x]
      simp
    · have hne : ¬ MDiffAt (T% (c • X)) x :=
        fun hh => hX ((mdiffAt_const_smul_section_iff' c hc).mp hh)
      rw [lcOf_eq_zero_of_not_mdiffAt' g hne, lcOf_eq_zero_of_not_mdiffAt' g hX]
      simp

/-! ## Homogeneity of the curvature in its second and third slots (`T2Space`-free)

`curv` is defined in `ChallengeDeps` as `∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]}Z`; the compatibility with
scalar multiplication in a slot is the Leibniz rule for `∇` (section slot) combined with the
Leibniz rule for the Lie bracket.  The proofs below are the `T2Space`-free (and
`RiemannianBundle`-free) re-runs of `Submission.Curvature.curv_smul_middle` /
`curv_smul_right`. -/

/-- **Tensoriality in the second slot**: `R(X, fY)Z = f R(X,Y)Z`. -/
theorem curv_smul_middle'
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (f : M → ℝ) (X Y Z : TField (I := I) (M := M)) (x : M)
    (hf : CMDiff ∞ f) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov X (f • Y) Z x = f x • curv cov X Y Z x := by
  unfold curv
  have hζYZ : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (I := I) (M := M) cov hcov hZ hY
  have hsect : (fun y : M => cov Z y ((f • Y) y)) = f • (fun y : M => cov Z y (Y y)) := by
    funext y
    rw [show (f • Y) y = f y • Y y from rfl, map_smul]
    rfl
  have h1 : cov (fun y : M => cov Z y ((f • Y) y)) x (X x)
      = f x • cov (fun y : M => cov Z y (Y y)) x (X x)
        + (mvfderiv I f x (X x)) • (cov Z x (Y x)) := by
    rw [hsect]
    have hL := cov.isCovariantDerivativeOn.leibniz (σ := fun y : M => cov Z y (Y y))
      ((hζYZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    have hL' := congrArg (fun (L : TangentSpace I x →L[ℝ] TangentSpace I x) => L (X x)) hL
    rw [hL']
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have h2 : cov (fun y : M => cov Z y (X y)) x ((f • Y) x)
      = f x • cov (fun y : M => cov Z y (X y)) x (Y x) := by
    rw [show (f • Y) x = f x • Y x from rfl, map_smul]
  have h3 : cov Z x (mlieBracket I X (f • Y) x)
      = f x • cov Z x (mlieBracket I X Y x)
        + (mvfderiv I f x (X x)) • (cov Z x (Y x)) := by
    rw [mlieBracket_smul_right ((hf x).mdifferentiableAt (by simp))
      ((hY x).mdifferentiableAt (by simp))]
    rw [map_add, map_smul, map_smul]
    module
  rw [h1, h2, h3]
  simp only [smul_sub]
  module

/-- **Tensoriality in the third slot**: `R(X,Y)(fZ) = f R(X,Y)Z`. -/
theorem curv_smul_right'
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (f : M → ℝ) (X Y Z : TField (I := I) (M := M)) (x : M)
    (hf : CMDiff ∞ f) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov X Y (f • Z) x = f x • curv cov X Y Z x := by
  unfold curv
  have hζYZ : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (I := I) (M := M) cov hcov hZ hY
  have hζXZ : CMDiff ∞ (T% (fun y : M => cov Z y (X y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (I := I) (M := M) cov hcov hZ hX
  have hYf : CMDiff ∞ (fun y : M => mvfderiv I f y (Y y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff (I := I) hf hY
  have hXf : CMDiff ∞ (fun y : M => mvfderiv I f y (X y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff (I := I) hf hX
  have hsectY : (fun y : M => cov (f • Z) y (Y y))
      = f • (fun y : M => cov Z y (Y y)) + (fun y : M => mvfderiv I f y (Y y)) • Z := by
    funext y
    rw [cov.isCovariantDerivativeOn.leibniz (σ := Z) ((hZ y).mdifferentiableAt (by simp))
      ((hf y).mdifferentiableAt (by simp))]
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  have hsectX : (fun y : M => cov (f • Z) y (X y))
      = f • (fun y : M => cov Z y (X y)) + (fun y : M => mvfderiv I f y (X y)) • Z := by
    funext y
    rw [cov.isCovariantDerivativeOn.leibniz (σ := Z) ((hZ y).mdifferentiableAt (by simp))
      ((hf y).mdifferentiableAt (by simp))]
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  have hT1 : cov (fun y : M => cov (f • Z) y (Y y)) x (X x)
      = (f x • cov (fun y : M => cov Z y (Y y)) x (X x)
          + (mvfderiv I f x (X x)) • (cov Z x (Y x)))
        + ((mvfderiv I f x (Y x)) • (cov Z x (X x))
          + (mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x)) • (Z x)) := by
    rw [hsectY]
    rw [cov.isCovariantDerivativeOn.add
      ((hf.smul_section hζYZ x).mdifferentiableAt (by simp))
      ((hYf.smul_section hZ x).mdifferentiableAt (by simp))]
    have hL1 := cov.isCovariantDerivativeOn.leibniz (σ := fun y : M => cov Z y (Y y))
      ((hζYZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    have hL2 := cov.isCovariantDerivativeOn.leibniz (σ := Z)
      ((hZ x).mdifferentiableAt (by simp)) ((hYf x).mdifferentiableAt (by simp))
    rw [show (cov (f • fun y => cov Z y (Y y)) x + cov ((fun y => mvfderiv I f y (Y y)) • Z) x)
        (X x)
        = (cov (f • fun y => cov Z y (Y y)) x) (X x)
          + (cov ((fun y => mvfderiv I f y (Y y)) • Z) x) (X x) from by rw [add_apply]]
    rw [show (cov (f • fun y => cov Z y (Y y)) x) (X x) = _ from
        congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (X x)) hL1,
      show (cov ((fun y => mvfderiv I f y (Y y)) • Z) x) (X x) = _ from
        congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (X x)) hL2]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have hT2 : cov (fun y : M => cov (f • Z) y (X y)) x (Y x)
      = (f x • cov (fun y : M => cov Z y (X y)) x (Y x)
          + (mvfderiv I f x (Y x)) • (cov Z x (X x)))
        + ((mvfderiv I f x (X x)) • (cov Z x (Y x))
          + (mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)) • (Z x)) := by
    rw [hsectX]
    rw [cov.isCovariantDerivativeOn.add
      ((hf.smul_section hζXZ x).mdifferentiableAt (by simp))
      ((hXf.smul_section hZ x).mdifferentiableAt (by simp))]
    have hL1 := cov.isCovariantDerivativeOn.leibniz (σ := fun y : M => cov Z y (X y))
      ((hζXZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    have hL2 := cov.isCovariantDerivativeOn.leibniz (σ := Z)
      ((hZ x).mdifferentiableAt (by simp)) ((hXf x).mdifferentiableAt (by simp))
    rw [show (cov (f • fun y => cov Z y (X y)) x + cov ((fun y => mvfderiv I f y (X y)) • Z) x)
        (Y x)
        = (cov (f • fun y => cov Z y (X y)) x) (Y x)
          + (cov ((fun y => mvfderiv I f y (X y)) • Z) x) (Y x) from by rw [add_apply]]
    rw [show (cov (f • fun y => cov Z y (X y)) x) (Y x) = _ from
        congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (Y x)) hL1,
      show (cov ((fun y => mvfderiv I f y (X y)) • Z) x) (Y x) = _ from
        congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (Y x)) hL2]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have hT3 : cov (f • Z) x (mlieBracket I X Y x)
      = f x • cov Z x (mlieBracket I X Y x)
        + (mvfderiv I f x (mlieBracket I X Y x)) • (Z x) := by
    have hL := cov.isCovariantDerivativeOn.leibniz (σ := Z)
      ((hZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    rw [show (cov (f • Z) x) (mlieBracket I X Y x) = _ from
      congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (mlieBracket I X Y x)) hL]
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have hbrF : mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x)
      = mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)
        + mvfderiv I f x (mlieBracket I X Y x) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields (I := I) hf hX hY
  rw [hT1, hT2, hT3, hbrF, add_smul]
  module

/-- Constant-scalar version of `curv_smul_middle'`. -/
theorem curv_const_smul_middle'
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (c : ℝ) {X Y Z : TField (I := I) (M := M)}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    curv cov X (c • Y) Z x = c • curv cov X Y Z x := by
  exact curv_smul_middle' cov hcov (fun _ : M => c) X Y Z x
    (contMDiff_const (c := c)) hX hY hZ

/-- Constant-scalar version of `curv_smul_right'`. -/
theorem curv_const_smul_right'
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (c : ℝ) {X Y Z : TField (I := I) (M := M)}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    curv cov X Y (c • Z) x = c • curv cov X Y Z x := by
  exact curv_smul_right' cov hcov (fun _ : M => c) X Y Z x
    (contMDiff_const (c := c)) hX hY hZ

/-! ## Slotwise homogeneity of packed families

Following the convention of `Work.Diff.EXT.ConnCov.AMB`, tuples of fields are `AMB.TF`-valued; the
scaling of the `j`-th slot field by `c j` is written as the explicit lambda
`fun j => fun y => c j • F j y` (which is definitionally the frozen `scaleTup c F`). -/

/-- **Joint scaling homogeneity** of a packed family `τ : Fam N`: scaling the `j`-th slot field by
the scalar `c j` (for every `j`) multiplies the value by `∏ j, c j`. -/
def Hom {N : ℕ} (τ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) N) : Prop :=
  ∀ (c : Fin N → ℝ) (F : Fin N → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (x : M),
    τ (fun j : Fin N => fun y : M => c j • F j y) x
      = (Finset.univ.prod (fun j : Fin N => c j)) * τ F x

/-- **Single-slot scaling homogeneity** of a packed family. -/
def SlotHom {N : ℕ} (τ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) N) : Prop :=
  ∀ (j : Fin N) (r : ℝ) (F : Fin N → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (x : M),
    τ (Function.update F j (r • F j)) x = r * τ F x

/-! ## The recursion step: `AMB.pD` preserves slotwise homogeneity

The two homogeneity facts used are joint scaling (`Hom`) for the `mvfderiv` term and for the correction
terms (where the *field* argument `F j.succ` is scaled), and single-slot scaling (`SlotHom`) for the
inserted field `c 0 • ∇_{F j} F 0`, which is obtained from `Hom` by the constant product
`∏ i, (if i = j then r else 1) = r`. -/

/-- **Single-slot scaling homogeneity**, derived from joint scaling homogeneity. -/
theorem slotHom_of_hom {N : ℕ} {τ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) N}
    (h : Hom τ) : SlotHom (I := I) (M := M) τ := by
  intro j r F x
  have h' := h (fun i : Fin N => if i = j then r else 1) F x
  have hfun : (fun i : Fin N => fun y : M => (if i = j then r else 1) • F i y)
      = Function.update F j (r • F j) := by
    funext i y
    by_cases hi : i = j
    · subst hi
      simp
    · simp only [Function.update_of_ne hi, if_neg hi, one_smul]
  have hprod : (∏ i : Fin N, (if i = j then r else 1)) = r := by
    simp
  rw [hfun, hprod] at h'
  exact h'

/-- **The recursion step**: `AMB.pD (lcOf g)` sends slotwise homogeneous families to slotwise
homogeneous families. -/
theorem hom_pD (g : SMet I M) {N : ℕ} {τ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) N}
    (hhom : Hom τ) : Hom (Work.Diff.EXT.ConnCov.AMB.pD (lcOf g) τ) := by
  classical
  intro c F x
  have hslot := slotHom_of_hom hhom
  have hPQ : (∏ j : Fin N, c j.succ) * c 0 = ∏ i : Fin (N + 1), c i := by
    rw [Fin.prod_univ_succ]
    ring
  show mvfderiv I (τ (fun j : Fin N => fun y : M => c j.succ • F j.succ y)) x (c 0 • F 0 x)
      - (∑ j : Fin N, τ (Function.update
          (fun i : Fin N => fun y : M => c i.succ • F i.succ y) j
          (fun y : M => lcOf g (fun y' : M => c j.succ • F j.succ y') y (c 0 • F 0 y))) x)
    = (∏ i : Fin (N + 1), c i) *
      (mvfderiv I (τ (fun j : Fin N => F j.succ)) x (F 0 x)
        - ∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
            (fun y : M => lcOf g (F j.succ) y (F 0 y))) x)
  -- ## the derivative term
  have hfun1 : τ (fun j : Fin N => fun y : M => c j.succ • F j.succ y)
      = fun y : M => (∏ j : Fin N, c j.succ) • τ (fun j : Fin N => F j.succ) y := by
    funext y
    have h := hhom (fun j : Fin N => c j.succ) (fun j : Fin N => F j.succ) y
    simpa [smul_eq_mul] using h
  have ht1 : mvfderiv I (τ (fun j : Fin N => fun y : M => c j.succ • F j.succ y)) x
        (c 0 • F 0 x)
      = (∏ i : Fin (N + 1), c i) *
        mvfderiv I (τ (fun j : Fin N => F j.succ)) x (F 0 x) := by
    rw [hfun1, Commons.Geometry.Manifold.Riemannian.mvfderiv_const_smul,
      smul_apply, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hPQ]
  -- ## the correction terms
  have hcorr : ∀ j : Fin N,
      τ (Function.update (fun i : Fin N => fun y : M => c i.succ • F i.succ y) j
          (fun y : M => lcOf g (fun y' : M => c j.succ • F j.succ y') y (c 0 • F 0 y))) x
        = (∏ i : Fin (N + 1), c i) *
          τ (Function.update (fun i : Fin N => F i.succ) j
            (fun y : M => lcOf g (F j.succ) y (F 0 y))) x := by
    intro j
    have hfield : (fun y : M => lcOf g (fun y' : M => c j.succ • F j.succ y') y (c 0 • F 0 y))
        = fun y : M => c j.succ • (c 0 • lcOf g (F j.succ) y (F 0 y)) := by
      funext y
      rw [show lcOf g (fun y' : M => c j.succ • F j.succ y') y (c 0 • F 0 y)
          = lcOf g (c j.succ • F j.succ) y (c 0 • F 0 y) from rfl,
        lcOf_smul_field', ContinuousLinearMap.map_smul, smul_smul]
    have htuple : Function.update (fun i : Fin N => fun y : M => c i.succ • F i.succ y) j
          (fun y : M => lcOf g (fun y' : M => c j.succ • F j.succ y') y (c 0 • F 0 y))
        = fun i : Fin N => c i.succ •
            (Function.update (fun i : Fin N => F i.succ) j
              (fun y : M => c 0 • lcOf g (F j.succ) y (F 0 y))) i := by
      funext i y
      by_cases hi : i = j
      · subst hi
        rw [Function.update_self, Function.update_self]
        simpa using congrFun hfield y
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
        rfl
    rw [htuple]
    have h1 := hhom (fun i : Fin N => c i.succ)
      (Function.update (fun i : Fin N => F i.succ) j
        (fun y : M => c 0 • lcOf g (F j.succ) y (F 0 y))) x
    rw [show τ (fun i : Fin N => c i.succ • (Function.update (fun i : Fin N => F i.succ) j
              (fun y : M => c 0 • lcOf g (F j.succ) y (F 0 y))) i) x
        = (∏ i : Fin N, c i.succ) * τ (Function.update (fun i : Fin N => F i.succ) j
              (fun y : M => c 0 • lcOf g (F j.succ) y (F 0 y))) x from h1]
    have h2 := hslot j (c 0) (Function.update (fun i : Fin N => F i.succ) j
        (fun y : M => lcOf g (F j.succ) y (F 0 y))) x
    have hupd : Function.update (Function.update (fun i : Fin N => F i.succ) j
          (fun y : M => lcOf g (F j.succ) y (F 0 y))) j
        (c 0 • Function.update (fun i : Fin N => F i.succ) j
          (fun y : M => lcOf g (F j.succ) y (F 0 y)) j)
        = Function.update (fun i : Fin N => F i.succ) j
            (fun y : M => c 0 • lcOf g (F j.succ) y (F 0 y)) := by
      funext i
      by_cases hi : i = j
      · subst hi
        rw [Function.update_self, Function.update_self, Function.update_self]
        rfl
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, Function.update_of_ne hi]
    rw [hupd] at h2
    rw [show τ (Function.update (fun i : Fin N => F i.succ) j
              (fun y : M => c 0 • lcOf g (F j.succ) y (F 0 y))) x
        = c 0 * τ (Function.update (fun i : Fin N => F i.succ) j
              (fun y : M => lcOf g (F j.succ) y (F 0 y))) x from h2]
    rw [← mul_assoc, hPQ]
  rw [ht1, Finset.sum_congr rfl (fun j _ => hcorr j), mul_sub, Finset.mul_sum]

/-! ## The base case for `[T2Space M]`, and the corresponding form of the target

On a `T2Space` manifold the frozen `Submission.Diff.smoothExt` really is a smooth field with the
prescribed value, and the bilinearity of `ricAt` is available in the library
(`Work.Diff.EXT.ricAt_smul_middle_L`, `ricAt_smul_last_L`).  With those, the base case — and hence
the whole target — follows from the `T2Space`-free recursion step `hom_pD` proved above. -/

/-- **The base case**, for `[T2Space M]`. -/
theorem hom_ric2_t2 [T2Space M] (g' : SMet I M)
    (hcov : ContMDiffCovariantDerivative (lcOf g') ∞) :
    Hom (Work.Diff.EXT.ConnCov.RicFlip.ric2 g') := by
  intro c F x
  show ricAt (lcOf g') x (c 0 • F 0 x) (c 1 • F 1 x)
    = (∏ j : Fin 2, c j) * ricAt (lcOf g') x (F 0 x) (F 1 x)
  rw [Fin.prod_univ_two,
    Work.Diff.EXT.ricAt_smul_middle_L g' hcov x (c 0) (F 0 x) (c 1 • F 1 x),
    Work.Diff.EXT.ricAt_smul_last_L g' hcov x (c 1) (F 0 x) (F 1 x)]
  ring

/-- **The target statement in its correct form** (`[T2Space M]` added), which is what the consumer
`Work.Diff.EXT.ATower.fixedRicTowerBound` — whose context does carry `[T2Space M]` — actually needs.
Together with `T2Space`-free `hom_pD` this is a three-line assembly. -/
theorem pDiter2_multi_homog_t2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (g g' : Submission.Diff.SMet I M)
    (m : ℕ) (c : Fin (m + 2) → ℝ)
    (F : Fin (m + 2) → TF (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 g') m
        (scaleTup (I := I) (M := M) c F) x
      = (Finset.univ.prod (fun j : Fin (m + 2) => c j))
        * Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf g)
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 g') m F x := by
  have hcov' : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g')
      (⊤ : ℕ∞) := by
    obtain ⟨hcov, -, -⟩ := hLC g'
    exact Classical.choice hcov
  have hiter : ∀ k : ℕ, Hom (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf g)
      (Work.Diff.EXT.ConnCov.RicFlip.ric2 g') k) := by
    intro k
    induction k with
    | zero => exact hom_ric2_t2 g' hcov'
    | succ k ih => exact hom_pD g ih
  exact hiter m c F x

theorem pDiter2_multi_homog
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M)
    (g g' : Submission.Diff.SMet I M)
    (m : ℕ) (c : Fin (m + 2) → ℝ)
    (F : Fin (m + 2) → Work.Diff.EXT.ATower.TF (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 g') m
        (Work.Diff.EXT.ATower.scaleTup (I := I) (M := M) c F) x
      = (Finset.univ.prod (fun j : Fin (m + 2) => c j))
        * Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf g)
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 g') m F x := by
  -- NOT PROVABLE as stated: see the module docstring.  The `m = 0` instance of the identity is the
  -- bilinearity of `ricAt (lcOf g')` in its two value arguments, which needs the `T2Space`-locked
  -- specification of `Submission.Diff.smoothExt` (bump functions are not available without
  -- `[T2Space M]`), and the natural `T2Space`-free candidate for that specification — the constant
  -- model section — is refuted by the hairy ball theorem.
  sorry

end Work.Diff.EXT.ATower
