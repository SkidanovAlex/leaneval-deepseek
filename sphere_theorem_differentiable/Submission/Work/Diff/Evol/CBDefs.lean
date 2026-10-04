import Mathlib
import Submission.Work.Diff.Evol.RicDeriv
import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Work.Diff.GE.dRSec_bianchi
import Submission.Work.Diff.GE.smooth_onframe
import Submission.Work.Diff.GE.curvVec_pair_exchange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared vocabulary for the contracted Bianchi identity (`Work.Diff.Evol.contracted_bianchi`)

The target of this area is the pointwise contracted second Bianchi identity

`∑ m, covRm g x (e m) (e m) a b c = covRic g x b a c - covRic g x c a b`

for an orthonormal frame `e` of `T_xM`, where (`Submission/Diff/Grad.lean`, `Evol/RicDeriv.lean`)

* `rmP g x a b c d = g(R(a,b)d, c)`, `covRm g x v a b c d = (∇_v Rm)(a,b,c,d)`,
* `covRic g x v p q = (∇_v Ric)(p,q)`.

Both frozen definitions are "`Ext` patterns" in the `Classical.epsilon`-chosen extensions
`smoothExt x ·`: a `mvfderiv` of an expression in those fields, minus the connection corrections in
each of the field slots (`Evol/RicDeriv.lean` for `Ric`, `Submission/Diff/Grad.lean` for `Rm`).

This module is the *shared vocabulary* of the development.  It is deliberately built on the chain
`Submission/Work/Diff/GE/bianchi_kato_defs` – `dRSec_bianchi` – `smooth_onframe` –
`curvVec_pair_exchange` (which contains the second Bianchi identity for `∇Rm` as an identity of
*fields* and a smooth field of orthonormal frames).  It must NOT be mixed with the sibling chain
`curvbasic`/`Frame`/`NablaRm`/`dRmPhi`/`Kato3.CovRmKit`: the two chains duplicate the definitions
`Work.Diff.GE.exists_isONFrame`, `Work.Diff.GE.isONFrame_onFrame`, `Work.Diff.GE.rmVec_eq_curvVec_lcOf`,
so importing one after the other is a hard error in the Lean environment.

Contents (all in the coordinates/notations of the frozen interfaces):

* `dRmPhi` – the `Ext` pattern of `∇Rm` on arbitrary smooth fields, with
  `covRm_eq_dRmPhi : covRm g x v a b c d = dRmPhi g x v (smoothExt x a) … (smoothExt x d)`;
* the algebraic identities of `rmP` (`rmP_skew`, `rmP_antisymm`, `rmP_pair_exchange`);
* `mvfderiv_sum`, `mvfderiv_congr_eventuallyEq`;
* smoothness of the curvature section (`contMDiff_curv_fields`) and of the scalar
  `y ↦ rmP g y (A y) (B y) (C y) (D y)` (`rmP_fields_smooth`);
* expansion in an orthonormal frame (`onFrame_expand`, `onFrame_expand'`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Finset
open Submission.CurvatureVec

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-! ## The `Ext` pattern of `∇Rm` on arbitrary fields -/

/-- The `Ext` pattern of `∇Rm`: the derivative of `rmP g · (A ·) (B ·) (C ·) (D ·)` along the
tangent vector `v`, minus the four connection corrections that make the expression depend only on
the values of `A`, `B`, `C`, `D` at the base point. -/
noncomputable def dRmPhi (g : SMet I M) (x : M) (v : TangentSpace I x)
    (A B C D : Π y : M, TangentSpace I y) : ℝ :=
  mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v
    - rmP g x (lcOf g A x v) (B x) (C x) (D x)
    - rmP g x (A x) (lcOf g B x v) (C x) (D x)
    - rmP g x (A x) (B x) (lcOf g C x v) (D x)
    - rmP g x (A x) (B x) (C x) (lcOf g D x v)

/-- `covRm` is `dRmPhi` evaluated on the chosen extensions `smoothExt x ·`. -/
theorem covRm_eq_dRmPhi (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    covRm g x v a b c d
      = dRmPhi g x v (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) := by
  simp only [dRmPhi, covRm, (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x a).2,
    (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x b).2,
    (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x c).2,
    (Work.Diff.GE.smoothExt_spec (I := I) (M := M) x d).2]

/-! ## The algebraic identities of `rmP` -/

/-- Skew-adjointness in the last two slots: `rmP g x a b c d = - rmP g x a b d c`. -/
theorem rmP_skew (hLC : LCSmooth I M) (g : SMet I M) (x : M) (a b c d : TangentSpace I x) :
    rmP g x a b c d = -rmP g x a b d c := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, -, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  have h := inner_curvVec_skew (lcOf g) hcov hmet x a b c d
  simp only [Submission.Diff.rmP]
  rw [Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov x a b c, Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov x a b d]
  have key : g.inner x c (curvVec (lcOf g) x a b d)
      = -g.inner x d (curvVec (lcOf g) x a b c) := by
    rw [g.symm x d (curvVec (lcOf g) x a b c)]
    have h2 : Inner.inner ℝ c (curvVec (lcOf g) x a b d)
        = -Inner.inner ℝ (curvVec (lcOf g) x a b c) d := by
      rw [h]; ring
    exact h2
  rw [g.symm x (curvVec (lcOf g) x a b d) c, g.symm x (curvVec (lcOf g) x a b c) d]
  exact key

/-- Antisymmetry in the first two slots: `rmP g x a b c d = - rmP g x b a c d`. -/
theorem rmP_antisymm (hLC : LCSmooth I M) (g : SMet I M) (x : M) (a b c d : TangentSpace I x) :
    rmP g x a b c d = -rmP g x b a c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, -, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  have h := curvVec_antisymm (lcOf g) hcov x a b d
  simp only [Submission.Diff.rmP]
  rw [Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov x a b d, Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov x b a d]
  show Inner.inner ℝ (curvVec (lcOf g) x a b d) c = -Inner.inner ℝ (curvVec (lcOf g) x b a d) c
  rw [h]
  simp

/-- Exchange of the two pairs: `rmP g x a b c d = rmP g x d c b a`. -/
theorem rmP_pair_exchange (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    rmP g x a b c d = rmP g x d c b a := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, htor, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  have h := Work.Diff.GE.curvVec_pair_exchange (lcOf g) hcov htor hmet x a b d c
  simp only [Submission.Diff.rmP]
  rw [Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov x a b d, Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov x d c a]
  show Inner.inner ℝ (curvVec (lcOf g) x a b d) c = Inner.inner ℝ (curvVec (lcOf g) x d c a) b
  exact h

/-! ## Toolbox: `mvfderiv` on sums and on eventually equal functions -/

/-- `mvfderiv` of a finite sum of smooth functions. -/
theorem mvfderiv_sum {ι : Type*} (t : Finset ι) (F : ι → M → ℝ)
    (hF : ∀ i, CMDiff ∞ (F i)) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => ∑ i ∈ t, F i y) x v = ∑ i ∈ t, mvfderiv I (F i) x v := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, mvfderiv_const, zero_apply]
  | insert i t hi ih =>
      have ht : CMDiff ∞ (fun y : M => ∑ j ∈ t, F j y) :=
        ContMDiff.sum (fun j _ => hF j)
      have h1 : mvfderiv I (fun y : M => F i y + ∑ j ∈ t, F j y) x v
          = mvfderiv I (F i) x v + mvfderiv I (fun y : M => ∑ j ∈ t, F j y) x v := by
        rw [show (fun y : M => F i y + ∑ j ∈ t, F j y)
            = F i + (fun y : M => ∑ j ∈ t, F j y) from rfl]
        have h := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
          (mvfderiv_add (x := x) (g := F i) (g' := fun y : M => ∑ j ∈ t, F j y)
            ((hF i).mdifferentiableAt (by simp)) (ht.mdifferentiableAt (by simp)))
        simpa only [add_apply] using h
      rw [Finset.sum_insert hi]
      simp only [Finset.sum_insert hi, h1, ih]

/-- `mvfderiv` only depends on the germ of the function. -/
theorem mvfderiv_congr_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f₁ f₂ : M → F} {x : M} (h : f₁ =ᶠ[𝓝 x] f₂) :
    mvfderiv I f₁ x = mvfderiv I f₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-! ## Smoothness of the curvature section and of the scalar `rmP` -/

/-- **The curvature of a smooth connection as a smooth section.**
If `cov` is a `C^∞` covariant derivative and `X, Y, Z` are smooth vector fields, then
`y ↦ curv cov X Y Z y = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` is a smooth vector field. -/
theorem contMDiff_curv_fields
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    CMDiff ∞ (T% (fun y : M => curv cov X Y Z y)) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
    rw [h]; infer_instance
  have hbr : CMDiff ∞ (T% (mlieBracket I X Y)) := by
    intro y
    exact (hX y).mlieBracket_vectorField (hY y) (by simp)
  have h1 : CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (Y y')) y (X y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
        hZ hY) hX
  have h2 : CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (X y')) y (Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
      (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov
        hZ hX) hY
  have h3 : CMDiff ∞ (T% (fun y : M => cov Z y (mlieBracket I X Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov hZ hbr
  change CMDiff ∞ (T% (fun y : M => cov (fun y' : M => cov Z y' (Y y')) y (X y)
      - cov (fun y' : M => cov Z y' (X y')) y (Y y) - cov Z y (mlieBracket I X Y y)))
  exact (h1.sub_section h2).sub_section h3

/-- `y ↦ rmP g y (A y) (B y) (C y) (D y)` is `C^∞` for smooth fields `A, B, C, D`. -/
theorem rmP_fields_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C y) (D y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, -, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  have hpt : ∀ y : M, rmP g y (A y) (B y) (C y) (D y)
      = Inner.inner ℝ (curv (lcOf g) A B D y) (C y) := by
    intro y
    show g.inner y (rmVec (lcOf g) y (A y) (B y) (D y)) (C y)
      = Inner.inner ℝ (curv (lcOf g) A B D y) (C y)
    rw [show Inner.inner ℝ (curv (lcOf g) A B D y) (C y)
        = g.inner y (curv (lcOf g) A B D y) (C y) from rfl]
    rw [Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov y (A y) (B y) (D y)]
    exact congrArg (fun z => g.inner y z (C y))
      (Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hD rfl rfl rfl)
  have hbody : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      = fun y : M => Inner.inner ℝ (curv (lcOf g) A B D y) (C y) := funext hpt
  rw [hbody]
  exact ContMDiff.inner_bundle (v := fun y : M => curv (lcOf g) A B D y) (w := C)
    (contMDiff_curv_fields (lcOf g) hcov hA hB hD) hC

/-- `y ↦ curvVec (lcOf g) y (A y) (B y) (D y)` is a smooth section for smooth `A, B, D`. -/
theorem curvVec_fields_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {A B D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (T% (fun y : M => curvVec (lcOf g) y (A y) (B y) (D y))) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, -, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  have hpt : (fun y : M => curvVec (lcOf g) y (A y) (B y) (D y))
      = fun y : M => curv (lcOf g) A B D y := by
    funext y
    exact Submission.CurvatureVec.curvVec_eq (lcOf g) hcov hA hB hD rfl rfl rfl
  refine (contMDiff_curv_fields (lcOf g) hcov hA hB hD).congr (fun y => ?_)
  have hy := congrFun hpt y
  simp only [hy]

/-! ## Expansion in an orthonormal frame -/

/-- **Expansion of a tangent vector in an orthonormal frame**: `v = ∑ i, ⟪e i, v⟫ • e i`. -/
theorem onFrame_expand (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v : TangentSpace I x) : ∑ i, g.inner x (e i) v • e i = v := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hn
  classical
  have hconv : ∀ a b : TangentSpace I x, Inner.inner ℝ a b = g.inner x a b := fun a b => rfl
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hconv (e i) (e j)]
    exact he i j
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfOrthonormalOfCardEqFinrank hon (by rw [Fintype.card_fin]; rfl)
  have hb : (b : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
    coe_basisOfOrthonormalOfCardEqFinrank hon _
  have honb : Orthonormal ℝ (b : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
    rw [hb]; exact hon
  have h := (b.toOrthonormalBasis honb).sum_repr' v
  have hco : (b.toOrthonormalBasis honb : Fin (Module.finrank ℝ E) → TangentSpace I x) = e := by
    rw [Module.Basis.coe_toOrthonormalBasis]; exact hb
  rw [hco] at h
  refine Eq.trans ?_ h
  exact Finset.sum_congr rfl fun i _ => by
    rw [show Inner.inner ℝ (e i) v = g.inner x (e i) v from rfl]

/-- Expansion in an orthonormal frame, other pairing: `v = ∑ i, ⟪v, e i⟫ • e i`. -/
theorem onFrame_expand' (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v : TangentSpace I x) : ∑ i, g.inner x v (e i) • e i = v := by
  refine Eq.trans ?_ (onFrame_expand (I := I) (M := M) g x hn e he v)
  exact Finset.sum_congr rfl fun i _ => by rw [g.symm x v (e i)]

end Work.Diff.Evol
