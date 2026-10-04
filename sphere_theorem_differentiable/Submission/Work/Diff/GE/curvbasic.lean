import Mathlib
import Submission.Diff.Grad
import Submission.CurvatureVec
import Submission.ChartCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Basic bridges from the `Submission.Diff` definitions to the tensor calculus

The contracts in `Submission/Diff/Interfaces.lean` define the curvature, its frame components and
the scalar/Ricci traces using `Classical.epsilon`-chosen smooth extensions (`smoothExt`) and frames
(`onFrame`).  This file records the elementary consequences:

* `smoothExt` really is a smooth extension (`smoothExt_cmdiff`, `smoothExt_apply`);
* `rmVec` is multilinear in its three vector slots (`rmVec_add_*`, `rmVec_smul_*`, `rmVec_sum_*`),
  and satisfies the algebraic symmetries (`rmVec_antisymm`, `rmVec_bianchi`);
* orthonormal frames exist (`exists_isONFrame`) and `onFrame g x` is one (`isONFrame_onFrame`);
* the traces `scalAt`, `ricNormSq` are independent of the chosen orthonormal frame
  (`scalAt_eq_scalAlg_rmFrame`, `ricNormSq_eq_ricSq_rmFrame`).

All later files (curvature evolution, gradient estimate) build on these.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Curvature
open Submission.CurvatureVec

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## The `Classical.epsilon` smooth extension -/

theorem smoothExt_cmdiff (x : M) (u : TangentSpace I x) : CMDiff ∞ (T% (smoothExt x u)) :=
  (Classical.epsilon_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
    (I := I) (M := M) u)).1

theorem smoothExt_apply (x : M) (u : TangentSpace I x) : smoothExt x u x = u :=
  (Classical.epsilon_spec (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
    (I := I) (M := M) u)).2

/-! ## Multilinearity of `rmVec`

The library lemmas about `curv` are stated in a Riemannian context, so we carry the (unused)
instances along.
-/

section CurvAlg

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

theorem rmVec_add_left (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u₁ u₂ v w : TangentSpace I x) :
    rmVec cov x (u₁ + u₂) v w = rmVec cov x u₁ v w + rmVec cov x u₂ v w := by
  have h1 : CMDiff ∞ (T% (smoothExt x u₁ + smoothExt x u₂)) :=
    (smoothExt_cmdiff x u₁).add_section (smoothExt_cmdiff x u₂)
  have h2 : CMDiff ∞ (T% (smoothExt x (u₁ + u₂))) := smoothExt_cmdiff x (u₁ + u₂)
  have hv : smoothExt x (u₁ + u₂) x = (smoothExt x u₁ + smoothExt x u₂) x := by
    simp only [Pi.add_apply, smoothExt_apply]
  rw [show rmVec cov x (u₁ + u₂) v w
      = curv cov (smoothExt x (u₁ + u₂)) (smoothExt x v) (smoothExt x w) x from rfl,
    curv_eq_of_apply_eq cov hcov h2 h1 (smoothExt_cmdiff x v) (smoothExt_cmdiff x v)
      (smoothExt_cmdiff x w) (smoothExt_cmdiff x w) hv rfl rfl,
    show rmVec cov x u₁ v w
      = curv cov (smoothExt x u₁) (smoothExt x v) (smoothExt x w) x from rfl,
    show rmVec cov x u₂ v w
      = curv cov (smoothExt x u₂) (smoothExt x v) (smoothExt x w) x from rfl]
  exact congrFun (curv_add_left cov hcov (smoothExt x u₁) (smoothExt x u₂)
    (smoothExt x v) (smoothExt x w) (smoothExt_cmdiff x u₁) (smoothExt_cmdiff x u₂)
    (smoothExt_cmdiff x v) (smoothExt_cmdiff x w)) x

theorem rmVec_add_middle (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v₁ v₂ w : TangentSpace I x) :
    rmVec cov x u (v₁ + v₂) w = rmVec cov x u v₁ w + rmVec cov x u v₂ w := by
  have h1 : CMDiff ∞ (T% (smoothExt x v₁ + smoothExt x v₂)) :=
    (smoothExt_cmdiff x v₁).add_section (smoothExt_cmdiff x v₂)
  have h2 : CMDiff ∞ (T% (smoothExt x (v₁ + v₂))) := smoothExt_cmdiff x (v₁ + v₂)
  have hv : smoothExt x (v₁ + v₂) x = (smoothExt x v₁ + smoothExt x v₂) x := by
    simp only [Pi.add_apply, smoothExt_apply]
  rw [show rmVec cov x u (v₁ + v₂) w
      = curv cov (smoothExt x u) (smoothExt x (v₁ + v₂)) (smoothExt x w) x from rfl,
    curv_eq_of_apply_eq cov hcov (smoothExt_cmdiff x u) (smoothExt_cmdiff x u)
      h2 h1 (smoothExt_cmdiff x w) (smoothExt_cmdiff x w) rfl hv rfl,
    show rmVec cov x u v₁ w
      = curv cov (smoothExt x u) (smoothExt x v₁) (smoothExt x w) x from rfl,
    show rmVec cov x u v₂ w
      = curv cov (smoothExt x u) (smoothExt x v₂) (smoothExt x w) x from rfl]
  exact congrFun (curv_add_middle cov hcov (smoothExt x u) (smoothExt x v₁) (smoothExt x v₂)
    (smoothExt x w) (smoothExt_cmdiff x u) (smoothExt_cmdiff x v₁) (smoothExt_cmdiff x v₂)
    (smoothExt_cmdiff x w)) x

theorem rmVec_add_right (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v w₁ w₂ : TangentSpace I x) :
    rmVec cov x u v (w₁ + w₂) = rmVec cov x u v w₁ + rmVec cov x u v w₂ := by
  have h1 : CMDiff ∞ (T% (smoothExt x w₁ + smoothExt x w₂)) :=
    (smoothExt_cmdiff x w₁).add_section (smoothExt_cmdiff x w₂)
  have h2 : CMDiff ∞ (T% (smoothExt x (w₁ + w₂))) := smoothExt_cmdiff x (w₁ + w₂)
  have hv : smoothExt x (w₁ + w₂) x = (smoothExt x w₁ + smoothExt x w₂) x := by
    simp only [Pi.add_apply, smoothExt_apply]
  rw [show rmVec cov x u v (w₁ + w₂)
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x (w₁ + w₂)) x from rfl,
    curv_eq_of_apply_eq cov hcov (smoothExt_cmdiff x u) (smoothExt_cmdiff x u)
      (smoothExt_cmdiff x v) (smoothExt_cmdiff x v) h2 h1 rfl rfl hv,
    show rmVec cov x u v w₁
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x w₁) x from rfl,
    show rmVec cov x u v w₂
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x w₂) x from rfl]
  exact congrFun (curv_add_right cov hcov (smoothExt x u) (smoothExt x v) (smoothExt x w₁)
    (smoothExt x w₂) (smoothExt_cmdiff x u) (smoothExt_cmdiff x v) (smoothExt_cmdiff x w₁)
    (smoothExt_cmdiff x w₂)) x

private lemma smul_section_const {X : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (c : ℝ) :
    CMDiff ∞ (T% (c • X)) := by
  simpa using (contMDiff_const (c := c)).smul_section hX

theorem rmVec_smul_left (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v w : TangentSpace I x) :
    rmVec cov x (c • u) v w = c • rmVec cov x u v w := by
  have h1 : CMDiff ∞ (T% ((fun _ : M => c) • smoothExt x u)) :=
    (contMDiff_const (c := c)).smul_section (smoothExt_cmdiff x u)
  have h2 : CMDiff ∞ (T% (smoothExt x (c • u))) := smoothExt_cmdiff x (c • u)
  have hv : smoothExt x (c • u) x = ((fun _ : M => c) • smoothExt x u) x := by
    simp [smoothExt_apply]
  rw [show rmVec cov x (c • u) v w
      = curv cov (smoothExt x (c • u)) (smoothExt x v) (smoothExt x w) x from rfl,
    curv_eq_of_apply_eq cov hcov h2 h1 (smoothExt_cmdiff x v) (smoothExt_cmdiff x v)
      (smoothExt_cmdiff x w) (smoothExt_cmdiff x w) hv rfl rfl,
    show rmVec cov x u v w
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x w) x from rfl]
  exact curv_smul_left cov hcov (fun _ : M => c) (smoothExt x u) (smoothExt x v)
    (smoothExt x w) x contMDiff_const (smoothExt_cmdiff x u) (smoothExt_cmdiff x v)
    (smoothExt_cmdiff x w)

theorem rmVec_smul_middle (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v w : TangentSpace I x) :
    rmVec cov x u (c • v) w = c • rmVec cov x u v w := by
  have h1 : CMDiff ∞ (T% ((fun _ : M => c) • smoothExt x v)) :=
    (contMDiff_const (c := c)).smul_section (smoothExt_cmdiff x v)
  have h2 : CMDiff ∞ (T% (smoothExt x (c • v))) := smoothExt_cmdiff x (c • v)
  have hv : smoothExt x (c • v) x = ((fun _ : M => c) • smoothExt x v) x := by
    simp [smoothExt_apply]
  rw [show rmVec cov x u (c • v) w
      = curv cov (smoothExt x u) (smoothExt x (c • v)) (smoothExt x w) x from rfl,
    curv_eq_of_apply_eq cov hcov (smoothExt_cmdiff x u) (smoothExt_cmdiff x u)
      h2 h1 (smoothExt_cmdiff x w) (smoothExt_cmdiff x w) rfl hv rfl,
    show rmVec cov x u v w
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x w) x from rfl]
  exact curv_smul_middle cov hcov (fun _ : M => c) (smoothExt x u) (smoothExt x v)
    (smoothExt x w) x contMDiff_const (smoothExt_cmdiff x u) (smoothExt_cmdiff x v)
    (smoothExt_cmdiff x w)

theorem rmVec_smul_right (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v w : TangentSpace I x) :
    rmVec cov x u v (c • w) = c • rmVec cov x u v w := by
  have h1 : CMDiff ∞ (T% ((fun _ : M => c) • smoothExt x w)) :=
    (contMDiff_const (c := c)).smul_section (smoothExt_cmdiff x w)
  have h2 : CMDiff ∞ (T% (smoothExt x (c • w))) := smoothExt_cmdiff x (c • w)
  have hv : smoothExt x (c • w) x = ((fun _ : M => c) • smoothExt x w) x := by
    simp [smoothExt_apply]
  rw [show rmVec cov x u v (c • w)
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x (c • w)) x from rfl,
    curv_eq_of_apply_eq cov hcov (smoothExt_cmdiff x u) (smoothExt_cmdiff x u)
      (smoothExt_cmdiff x v) (smoothExt_cmdiff x v) h2 h1 rfl rfl hv,
    show rmVec cov x u v w
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x w) x from rfl]
  exact curv_smul_right cov hcov (fun _ : M => c) (smoothExt x u) (smoothExt x v)
    (smoothExt x w) x contMDiff_const (smoothExt_cmdiff x u) (smoothExt_cmdiff x v)
    (smoothExt_cmdiff x w)

theorem rmVec_sum_left {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (s : Finset ι) (c : ι → ℝ)
    (u : ι → TangentSpace I x) (v w : TangentSpace I x) :
    rmVec cov x (∑ i ∈ s, c i • u i) v w = ∑ i ∈ s, c i • rmVec cov x (u i) v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rmVec_smul_left cov hcov x 0 (0 : TangentSpace I x) v w
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, rmVec_add_left cov hcov,
        rmVec_smul_left cov hcov, ih]

theorem rmVec_sum_middle {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (s : Finset ι) (c : ι → ℝ)
    (v : ι → TangentSpace I x) (u w : TangentSpace I x) :
    rmVec cov x u (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i • rmVec cov x u (v i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rmVec_smul_middle cov hcov x 0 u (0 : TangentSpace I x) w
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, rmVec_add_middle cov hcov,
        rmVec_smul_middle cov hcov, ih]

theorem rmVec_sum_right {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (s : Finset ι) (c : ι → ℝ)
    (w : ι → TangentSpace I x) (u v : TangentSpace I x) :
    rmVec cov x u v (∑ i ∈ s, c i • w i) = ∑ i ∈ s, c i • rmVec cov x u v (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rmVec_smul_right cov hcov x 0 u v (0 : TangentSpace I x)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, rmVec_add_right cov hcov,
        rmVec_smul_right cov hcov, ih]

theorem rmVec_antisymm (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v w : TangentSpace I x) :
    rmVec cov x u v w = -rmVec cov x v u w := by
  rw [show rmVec cov x u v w
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x w) x from rfl,
    show rmVec cov x v u w
      = curv cov (smoothExt x v) (smoothExt x u) (smoothExt x w) x from rfl]
  exact curv_antisymm_apply cov (smoothExt x u) (smoothExt x v) (smoothExt x w) x

theorem rmVec_bianchi (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (htor : cov.torsion = 0)
    (x : M) (u v w : TangentSpace I x) :
    rmVec cov x u v w + rmVec cov x v w u + rmVec cov x w u v = 0 := by
  rw [show rmVec cov x u v w
      = curv cov (smoothExt x u) (smoothExt x v) (smoothExt x w) x from rfl,
    show rmVec cov x v w u
      = curv cov (smoothExt x v) (smoothExt x w) (smoothExt x u) x from rfl,
    show rmVec cov x w u v
      = curv cov (smoothExt x w) (smoothExt x u) (smoothExt x v) x from rfl]
  exact curv_bianchi cov hcov htor (smoothExt_cmdiff x u) (smoothExt_cmdiff x v)
    (smoothExt_cmdiff x w)

end CurvAlg

/-! ## Orthonormal frames

`TangentSpace I x` is a type synonym for `E`; endowing it with the scalar product `g.inner x`
turns `IsONFrame g x e` into `Orthonormal ℝ e`, and lets us use Mathlib's orthonormal-basis API. -/

theorem exists_isONFrame (g : SMet I M) (x : M) :
    ∃ e : Fin (Module.finrank ℝ E) → TangentSpace I x, IsONFrame g x e := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  let e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => (stdOrthonormalBasis ℝ (TangentSpace I x) : Fin (Module.finrank ℝ E) → _) i
  refine ⟨e, ?_⟩
  intro i j
  have h := orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal i j
  have hconv : Inner.inner ℝ (e i) (e j) = g.inner x (e i) (e j) := rfl
  rw [← hconv]; exact h

/-- `onFrame g x` is an orthonormal frame (for the metric `g`). -/
theorem isONFrame_onFrame (g : SMet I M) (x : M) : IsONFrame g x (onFrame g x) :=
  Classical.epsilon_spec (exists_isONFrame (I := I) (M := M) g x)

/-- **Expansion in an orthonormal frame**: `v = ∑ i ⟪e i, v⟫ e i`. -/
theorem sum_inner_smul_eq_self (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
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

/-- **Expansion in an orthonormal frame**, other pairing: `v = ∑ i ⟪v, e i⟫ e i`. -/
theorem sum_smul_inner_eq_self (g : SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (v : TangentSpace I x) : ∑ i, g.inner x v (e i) • e i = v := by
  refine Eq.trans ?_ (sum_inner_smul_eq_self (I := I) (M := M) g x hn e he v)
  exact Finset.sum_congr rfl fun i _ => by rw [g.symm x v (e i)]


end Work.Diff.GE
