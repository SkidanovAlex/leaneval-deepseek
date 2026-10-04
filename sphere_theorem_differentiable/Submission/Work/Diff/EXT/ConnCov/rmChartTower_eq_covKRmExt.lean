import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.covK_valueDepN
import Submission.Work.Diff.EXT.covK_germ
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.EXT.covKRmExt_tensorial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart tower of the curvature is the geometric tower in the coordinate frame

`Work.Diff.EXT.ConnCov.rmChartTower` is the chart recursion for the iterated *moving* covariant
derivatives `∇^{G t, m}Rm` of the curvature in the coordinate frame of the chart at `x₀`
(`Submission/Work/Diff/EXT/ConnCov/ChartTowerDefs.lean`): level `0` is the chart curvature array
`rmChartExpr`, and each level is the chart derivative of the previous one corrected by the
Christoffel contractions of the coordinate frame.

This file proves that this recursion computes exactly the *geometric* tower
`Work.Diff.EXT.covKRmExt (G t) m` evaluated on the coordinate frame fields
`σ_i = cFrame x₀ i` at the chart point `pt x₀ y` of the chart coordinate `y`.

## Route

* `chrCoord_expand` — the Christoffel expansion `∇_{σ_a} σ_b = ∑_p Γ^p_{ab} σ_p` for a family of
  globally smooth fields agreeing with the coordinate frame near a point
  (from the proved `Work.Diff.GE.CovRmChartAux.lcOf_field_eq_sum_chrCoord`);
* `ckt_slot_sum` — `C^∞(M)`-linearity of the packed tower `Work.Diff.EXT.ckt` in one slot, extended
  from two terms (`Work.Diff.EXT.TensProp`) to a `Finset` sum;
* `ckt_dirF_update` — the *covariant-derivative slot substitution*: replacing a slot field by
  `∇_{σ_b}(σ_a)` multiplies the tower by the Christoffel coefficients (tensoriality via
  `Work.Diff.EXT.ckt_val_dep_all` + `ckt_slot_sum`);
* `main_ind` — the induction on the order `m`, comparing the five groups of the chart recursion
  with the `m + 4` slots of the geometric recursion (the derivative term via
  `mvfderiv_pt_eq_fderiv`, the slots via `ckt_dirF_update` and the induction hypothesis);
* the final step replaces the globally smooth fields `X a` by the coordinate frame fields
  `cFrame x₀ a` using the germ-locality `Work.Diff.EXT.covK_germ`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Diff.EXT.ConnCov

namespace RMChartAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]


/-- The chart point of `y` lies in the chart source. -/
lemma pt_mem_chart_source (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
  have h : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).symm '' (extChartAt I x₀).target :=
    ⟨y, hy, rfl⟩
  have hs : (extChartAt I x₀).symm '' (extChartAt I x₀).target = (extChartAt I x₀).source :=
    PartialEquiv.symm_image_target_eq_source (extChartAt I x₀)
  rw [hs] at h
  rw [extChartAt_source] at h
  exact h

/-- **The manifold derivative at a chart point, read in the chart.** -/
theorem mvfderiv_pt_eq_fderiv (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    {F : M → ℝ} (hF : MDifferentiableAt I 𝓘(ℝ,ℝ) F (Work.Diff.EXT.pt (I := I) x₀ y))
    (a : Fin (Module.finrank ℝ E)) :
    mvfderiv I F (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y))
      = fderiv ℝ (fun y' : E => F (Work.Diff.EXT.pt (I := I) x₀ y')) y
          (Work.Diff.GE.cBasis (E := E) a) := by
  have hsrc := pt_mem_chart_source (I := I) x₀ hy
  have h := Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hsrc hF
    (Work.Diff.GE.cBasis (E := E) a)
  have hcf : Work.Diff.GE.cFrame (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y)
      = Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cBasis (E := E) a) :=
    Work.Diff.GE.cFrame_apply (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y)
  have hpt : (extChartAt I x₀) (Work.Diff.EXT.pt (I := I) x₀ y) = y :=
    (extChartAt I x₀).right_inv hy
  rw [hcf, h, hpt]
  rfl

/-- **Smoothness of the curvature tower for globally smooth fields.** -/
theorem covKRmExt_smooth (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (k : ℕ) (V : Fin k → Work.Diff.EXT.TField (I := I) (M := M))
    (hV : ∀ i, Work.Diff.EXT.SmoothTField (I := I) (M := M) (V i))
    (A B C D : Work.Diff.EXT.TField (I := I) (M := M))
    (hA : Work.Diff.EXT.SmoothTField (I := I) (M := M) A)
    (hB : Work.Diff.EXT.SmoothTField (I := I) (M := M) B)
    (hC : Work.Diff.EXT.SmoothTField (I := I) (M := M) C)
    (hD : Work.Diff.EXT.SmoothTField (I := I) (M := M) D) :
    CMDiff ∞ (fun y : M => Work.Diff.EXT.covKRmExt g k V A B C D y) := by
  have h := (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g k
      (Work.Diff.EXT.mkT V (Work.Diff.EXT.quadF A B C D))
      (Work.Diff.EXT.smoothF_mkT' hV (Work.Diff.EXT.smoothTField_quadF hA hB hC hD))).1
  rwa [Work.Diff.EXT.ckt_quadF] at h

/-- Smoothness of a finite sum of smooth fields. -/
lemma smoothF_sum {ι : Type*} (Y : ι → Work.Diff.EXT.TField (I := I) (M := M))
    (hY : ∀ p, Work.Diff.EXT.SmoothF (Y p))
    (w : Work.Diff.EXT.TField (I := I) (M := M)) (hw : Work.Diff.EXT.SmoothF w)
    (c : ι → ℝ) (S : Finset ι) :
    Work.Diff.EXT.SmoothF (fun z : M => ∑ p ∈ S, c p • Y p z) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have h0 : (fun z : M => ∑ p ∈ (∅ : Finset ι), c p • Y p z)
          = (fun _ : M => (0 : ℝ)) • w := by
        funext z; simp
      rw [h0]
      exact Work.Diff.EXT.smoothF_smul (contMDiff_const (c := (0 : ℝ))) hw
  | insert p S hp ih =>
      have h0 : (fun z : M => ∑ q ∈ insert p S, c q • Y q z)
          = (fun _ : M => c p) • Y p + (fun z : M => ∑ q ∈ S, c q • Y q z) := by
        funext z; rw [Finset.sum_insert hp]; rfl
      rw [h0]
      exact Work.Diff.EXT.smoothF_add
        (Work.Diff.EXT.smoothF_smul (contMDiff_const (c := c p)) (hY p)) ih

/-- **The Christoffel expansion of a field along the coordinate frame.** -/
theorem chrCoord_expand (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ)
    (X : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hX : ∀ a, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (X a))
    {z : M} (hz : z ∈ (chartAt H x₀).source)
    (hXc : ∀ a, X a =ᶠ[𝓝 z] Work.Diff.GE.cFrame (I := I) x₀ a)
    (a b : Fin (Module.finrank ℝ E)) :
    (Submission.Diff.lcOf (G t) (X a) z) (X b z)
      = ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p b a t z •
          Work.Diff.GE.cFrame (I := I) x₀ p z := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have h := Work.Diff.GE.CovRmChartAux.lcOf_field_eq_sum_chrCoord (I := I) hLC G x₀ hz t b a
    (hX a) (hXc a)
  rw [show X b z = Work.Diff.GE.cFrame (I := I) x₀ b z from (hXc b).eq_of_nhds]
  exact h

/-- **Linear slot substitution at the level of the packed recursion `ckt`.** -/
theorem ckt_slot_sum (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (k : ℕ)
    (F : Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (F i))
    (s : Fin (k + 4)) {ι : Type*}
    (Y : ι → Work.Diff.EXT.TField (I := I) (M := M))
    (hY : ∀ p, Work.Diff.EXT.SmoothF (Y p))
    (c : ι → ℝ) (S : Finset ι) :
    Work.Diff.EXT.ckt g k (Function.update F s (fun z => ∑ p ∈ S, c p • Y p z))
      = fun z => ∑ p ∈ S, c p * Work.Diff.EXT.ckt g k (Function.update F s (Y p)) z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have h0 : (fun z : M => ∑ p ∈ (∅ : Finset ι), c p • Y p z)
          = (fun _ : M => (0 : ℝ)) • F s + (fun _ : M => (0 : ℝ)) • F s := by
        funext z; simp
      rw [h0]
      have h := (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g k F hF).2.1 s (F s) (F s)
        (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (hF s) (hF s)
        (contMDiff_const (c := (0 : ℝ))) (contMDiff_const (c := (0 : ℝ)))
      rw [h]
      funext z
      simp
  | insert p S hp ih =>
      have h0 : (fun z : M => ∑ q ∈ insert p S, c q • Y q z)
          = (fun _ : M => c p) • Y p
            + (fun _ : M => (1 : ℝ)) • (fun z : M => ∑ q ∈ S, c q • Y q z) := by
        funext z; rw [Finset.sum_insert hp]; simp
      rw [h0]
      have hYsum : Work.Diff.EXT.SmoothF (fun z : M => ∑ q ∈ S, c q • Y q z) :=
        smoothF_sum Y hY (F s) (hF s) c S
      have h := (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g k F hF).2.1 s (Y p)
        (fun z : M => ∑ q ∈ S, c q • Y q z) (fun _ => c p) (fun _ => (1 : ℝ))
        (hY p) hYsum (contMDiff_const (c := c p)) (contMDiff_const (c := (1 : ℝ)))
      rw [h, ih]
      funext z
      rw [Finset.sum_insert hp]
      simp

/-- **The covariant-derivative slot substitution** at the level of the packed recursion `ckt`. -/
theorem ckt_dirF_update (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ) (m : ℕ)
    (X : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hX : ∀ a, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (X a))
    {z : M} (hz : z ∈ (chartAt H x₀).source)
    (hXc : ∀ a, X a =ᶠ[𝓝 z] Work.Diff.GE.cFrame (I := I) x₀ a)
    (W : Fin (m + 4) → Fin (Module.finrank ℝ E)) (s : Fin (m + 4))
    (b : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.ckt (G t) m
        (Function.update (fun r : Fin (m + 4) => X (W r)) s
          (Work.Diff.EXT.dirF (G t) (X (W s)) (X b))) z
      = ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p b (W s) t z *
          Work.Diff.EXT.ckt (G t) m
            (Function.update (fun r : Fin (m + 4) => X (W r)) s (X p)) z := by
  classical
  set Z : Work.Diff.EXT.TField (I := I) (M := M) :=
    fun z' => ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p b (W s) t z • X p z' with hZ
  have hZval : Work.Diff.EXT.dirF (G t) (X (W s)) (X b) z = Z z := by
    have h := chrCoord_expand (I := I) hLC G x₀ t X hX hz hXc (W s) b
    have hdir : Work.Diff.EXT.dirF (G t) (X (W s)) (X b) z
        = (Submission.Diff.lcOf (G t) (X (W s)) z) (X b z) := rfl
    rw [hdir, h, hZ]
    exact Finset.sum_congr rfl (fun p _ => by rw [← (hXc p).eq_of_nhds])
  have hZsm : Work.Diff.EXT.SmoothF Z := by
    rw [hZ]
    exact smoothF_sum X hX (X (W ⟨0, by omega⟩)) (hX (W ⟨0, by omega⟩))
      (fun p => Work.Diff.GE.chrCoord (I := I) G x₀ p b (W s) t z) Finset.univ
  have h1 : Work.Diff.EXT.ckt (G t) m
        (Function.update (fun r : Fin (m + 4) => X (W r)) s
          (Work.Diff.EXT.dirF (G t) (X (W s)) (X b))) z
      = Work.Diff.EXT.ckt (G t) m (Function.update (fun r : Fin (m + 4) => X (W r)) s Z) z := by
    refine Work.Diff.EXT.ckt_val_dep_all (I := I) hLC (G t) m z ?_ ?_ ?_
    · intro r
      rcases eq_or_ne r s with h | h
      · rw [h, Function.update_self]
        exact Work.Diff.EXT.dirF_smooth hLC (G t) (hX (W s)) (hX b)
      · rw [Function.update_of_ne h]; exact hX (W r)
    · intro r
      rcases eq_or_ne r s with h | h
      · rw [h, Function.update_self]; exact hZsm
      · rw [Function.update_of_ne h]; exact hX (W r)
    · intro r
      rcases eq_or_ne r s with h | h
      · rw [h, Function.update_self, Function.update_self]; exact hZval
      · rw [Function.update_of_ne h, Function.update_of_ne h]
  have h2 : Work.Diff.EXT.ckt (G t) m (Function.update (fun r : Fin (m + 4) => X (W r)) s Z) z
      = ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p b (W s) t z *
          Work.Diff.EXT.ckt (G t) m
            (Function.update (fun r : Fin (m + 4) => X (W r)) s (X p)) z := by
    rw [hZ]
    rw [ckt_slot_sum (I := I) hLC (G t) m (fun r : Fin (m + 4) => X (W r))
      (fun r => hX (W r)) s X hX
      (fun p => Work.Diff.GE.chrCoord (I := I) G x₀ p b (W s) t z) Finset.univ]
  rw [h1, h2]

/-- The index `4`-tuple `(i, j, k, l)`. -/
def quadI (i j k l : Fin (Module.finrank ℝ E)) : Fin 4 → Fin (Module.finrank ℝ E) := ![i, j, k, l]

@[simp] lemma quadI_zero (i j k l : Fin (Module.finrank ℝ E)) : quadI i j k l 0 = i := rfl
@[simp] lemma quadI_one (i j k l : Fin (Module.finrank ℝ E)) : quadI i j k l 1 = j := rfl
@[simp] lemma quadI_two (i j k l : Fin (Module.finrank ℝ E)) : quadI i j k l 2 = k := rfl
@[simp] lemma quadI_three (i j k l : Fin (Module.finrank ℝ E)) : quadI i j k l 3 = l := rfl

/-- Packing of a `k`-tuple of index vectors and a `4`-tuple of index vectors (the analogue of
`mkT` for index vectors). -/
def mkI {k : ℕ} (w : Fin k → Fin (Module.finrank ℝ E))
    (B : Fin 4 → Fin (Module.finrank ℝ E)) : Fin (k + 4) → Fin (Module.finrank ℝ E) :=
  Fin.addCases w B

lemma mkI_castAdd {k : ℕ} (w : Fin k → Fin (Module.finrank ℝ E))
    (B : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin k) :
    mkI w B (Fin.castAdd 4 i) = w i :=
  Fin.addCases_left i

lemma mkI_natAdd {k : ℕ} (w : Fin k → Fin (Module.finrank ℝ E))
    (B : Fin 4 → Fin (Module.finrank ℝ E)) (p : Fin 4) :
    mkI w B (Fin.natAdd k p) = B p :=
  Fin.addCases_right p

/-- `mkT` with the empty family is the curvature tuple. -/
lemma mkT_zero {w : Fin 0 → Work.Diff.EXT.TField (I := I) (M := M)}
    (B : Fin 4 → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.mkT w B = B := by
  funext p
  have h1 : Fin.natAdd 0 p = p := Fin.ext (by simp)
  have h2 := Work.Diff.EXT.mkT_natAdd w B p
  rwa [h1] at h2

/-- `X` of a packed tuple of index vectors is the packed tuple of the fields `X ·`. -/
lemma mkT_comp_X (X : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E))
    (i j k l : Fin (Module.finrank ℝ E)) :
    (fun r : Fin (m + 4) => X (mkI v (quadI i j k l) r))
      = Work.Diff.EXT.mkT (fun s : Fin m => X (v s))
          (Work.Diff.EXT.quadF (X i) (X j) (X k) (X l)) := by
  funext r
  refine Fin.addCases ?_ ?_ r
  · intro s
    rw [mkI_castAdd, Work.Diff.EXT.mkT_castAdd]
  · intro p
    rw [mkI_natAdd, Work.Diff.EXT.mkT_natAdd]
    fin_cases p <;> rfl

lemma castAdd_ne_natAdd {m : ℕ} (r : Fin m) (q : Fin 4) :
    Fin.castAdd 4 r ≠ Fin.natAdd m q := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- Updating a direction slot of the `X`-indexed tuple. -/
lemma update_comp_X_castAdd (X : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (m : ℕ) (vv : Fin m → Fin (Module.finrank ℝ E))
    (i j k l : Fin (Module.finrank ℝ E)) (r : Fin m) (p : Fin (Module.finrank ℝ E)) :
    Function.update
        (fun r' : Fin (m + 4) => X (mkI vv (quadI i j k l) r'))
        (Fin.castAdd 4 r) (X p)
      = fun r' => X (mkI (Function.update vv r p) (quadI i j k l) r') := by
  funext r'
  refine Fin.addCases ?_ ?_ r'
  · intro s
    rcases eq_or_ne s r with hs | hs
    · rw [hs, Function.update_self, mkI_castAdd, Function.update_self]
    · rw [Function.update_of_ne (fun hh => hs (Fin.castAdd_inj.mp hh)), mkI_castAdd, mkI_castAdd,
        Function.update_of_ne hs]
  · intro q
    rw [Function.update_of_ne (Ne.symm (castAdd_ne_natAdd r q)), mkI_natAdd, mkI_natAdd]

/-- Updating a curvature slot of the `X`-indexed tuple. -/
lemma update_comp_X_natAdd (X : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (m : ℕ) (vv : Fin m → Fin (Module.finrank ℝ E))
    (i j k l : Fin (Module.finrank ℝ E)) (q : Fin 4) (p : Fin (Module.finrank ℝ E)) :
    Function.update
        (fun r' : Fin (m + 4) => X (mkI vv (quadI i j k l) r'))
        (Fin.natAdd m q) (X p)
      = fun r' => X (mkI vv (Function.update (quadI i j k l) q p) r') := by
  funext r'
  refine Fin.addCases ?_ ?_ r'
  · intro s
    rw [Function.update_of_ne (castAdd_ne_natAdd s q), mkI_castAdd, mkI_castAdd]
  · intro q'
    rcases eq_or_ne q' q with hq | hq
    · rw [hq, Function.update_self, mkI_natAdd, Function.update_self]
    · rw [Function.update_of_ne (fun hh => hq ((Fin.natAdd_inj m).mp hh)), mkI_natAdd, mkI_natAdd,
        Function.update_of_ne hq]

lemma update_quadI_zero (i j k l p : Fin (Module.finrank ℝ E)) :
    Function.update (quadI i j k l) 0 p = quadI p j k l := by
  funext q
  fin_cases q <;> simp [Function.update_apply, quadI]

lemma update_quadI_one (i j k l p : Fin (Module.finrank ℝ E)) :
    Function.update (quadI i j k l) 1 p = quadI i p k l := by
  funext q
  fin_cases q <;> simp [Function.update_apply, quadI]

lemma update_quadI_two (i j k l p : Fin (Module.finrank ℝ E)) :
    Function.update (quadI i j k l) 2 p = quadI i j p l := by
  funext q
  fin_cases q <;> simp [Function.update_apply, quadI]

lemma update_quadI_three (i j k l p : Fin (Module.finrank ℝ E)) :
    Function.update (quadI i j k l) 3 p = quadI i j k p := by
  funext q
  fin_cases q <;> simp [Function.update_apply, quadI]

lemma mkI_comp_succ {k : ℕ} (w : Fin (k + 1) → Fin (Module.finrank ℝ E))
    (B : Fin 4 → Fin (Module.finrank ℝ E)) :
    (fun i : Fin (k + 4) => mkI w B i.succ)
      = mkI (fun i : Fin k => w i.succ) B := by
  funext s
  refine Fin.addCases ?_ ?_ s
  · intro i
    rw [Work.Diff.EXT.succ_castAdd_four, mkI_castAdd, mkI_castAdd]
  · intro p
    rw [mkI_natAdd, Work.Diff.EXT.succ_natAdd_four, mkI_natAdd]

lemma mkI_zero {w : Fin 0 → Fin (Module.finrank ℝ E)}
    (B : Fin 4 → Fin (Module.finrank ℝ E)) : mkI w B = B := by
  funext p
  have h1 : Fin.natAdd 0 p = p := Fin.ext (by simp)
  have h2 := mkI_natAdd w B p
  rwa [h1] at h2

/-- The chart expression of the curvature in the coordinate frame. -/
lemma rmChartExpr_eq' (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ) {y : M} (hy : y ∈ (chartAt H x₀).source)
    (i j k l : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.rmChartExpr (I := I) G x₀ i j k l t y
      = rmP (G t) y (Work.Diff.GE.cFrame (I := I) x₀ i y) (Work.Diff.GE.cFrame (I := I) x₀ j y)
          (Work.Diff.GE.cFrame (I := I) x₀ k y) (Work.Diff.GE.cFrame (I := I) x₀ l y) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  rw [← Work.Diff.GE.rmChartExpr_eq (I := I) hLC G x₀ t hy i j k l]
  rfl

/-- **The main induction.** -/
theorem main_ind (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ)
    (X : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hX : ∀ a, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (X a))
    (U : Set E) (hUo : IsOpen U)
    (hUtgt : ∀ y' ∈ U, y' ∈ (extChartAt I x₀).target)
    (hgerm : ∀ y' ∈ U, ∀ a, X a =ᶠ[𝓝 (Work.Diff.EXT.pt (I := I) x₀ y')]
      Work.Diff.GE.cFrame (I := I) x₀ a) :
    ∀ m (v : Fin m → Fin (Module.finrank ℝ E)) (i j k l : Fin (Module.finrank ℝ E))
      {y : E}, y ∈ U →
      Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v i j k l y
        = Work.Diff.EXT.ckt (G t) m
            (fun r : Fin (m + 4) => X (mkI v (quadI i j k l) r))
            (Work.Diff.EXT.pt (I := I) x₀ y) := by
  intro m
  induction m with
  | zero =>
      intro v i j k l y hy
      have hz : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source :=
        pt_mem_chart_source (I := I) x₀ (hUtgt y hy)
      have hB : (fun r : Fin (0 + 4) => X (mkI v (quadI i j k l) r))
          = Work.Diff.EXT.quadF (X i) (X j) (X k) (X l) := by
        rw [mkI_zero]
        funext r
        fin_cases r <;> rfl
      rw [Work.Diff.EXT.ConnCov.rmChartTower_zero, hB]
      simp only [Work.Diff.EXT.ckt, Work.Diff.EXT.quadF_zero, Work.Diff.EXT.quadF_one,
        Work.Diff.EXT.quadF_two, Work.Diff.EXT.quadF_three]
      rw [rmChartExpr_eq' (I := I) hLC G x₀ t hz i j k l,
        ← (hgerm y hy i).eq_of_nhds, ← (hgerm y hy j).eq_of_nhds,
        ← (hgerm y hy k).eq_of_nhds, ← (hgerm y hy l).eq_of_nhds]
  | succ m ih =>
      intro v i j k l y hy
      have hz : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source :=
        pt_mem_chart_source (I := I) x₀ (hUtgt y hy)
      rw [Work.Diff.EXT.ConnCov.rmChartTower_succ, Work.Diff.EXT.ckt_succ]
      simp only [Pi.sub_apply, Finset.sum_apply]
      have hshift : ∀ i' : Fin (m + 4),
          X (mkI v (quadI i j k l) i'.succ)
            = X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) i') := by
        intro i'
        rw [← congrFun (mkI_comp_succ v (quadI i j k l)) i']
      have hdir : X (mkI v (quadI i j k l) (0 : Fin ((m + 1) + 4))) = X (v 0) := by
        have h0 : (0 : Fin ((m + 1) + 4)) = Fin.castAdd 4 (0 : Fin (m + 1)) := Fin.ext (by simp)
        rw [h0, mkI_castAdd]
      rw [Fin.sum_univ_add, Fin.sum_univ_four]
      simp only [hshift, hdir, mkI_castAdd, mkI_natAdd, quadI_zero, quadI_one, quadI_two,
        quadI_three]
      have hIHf : (Work.Diff.EXT.ConnCov.rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j k l)
          =ᶠ[𝓝 y] (fun y' : E => Work.Diff.EXT.ckt (G t) m
              (fun r : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r))
              (Work.Diff.EXT.pt (I := I) x₀ y')) := by
        filter_upwards [hUo.mem_nhds hy] with y' hy'
        exact ih (fun s : Fin m => v s.succ) i j k l hy'
      have hCktsm : ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun u : M => Work.Diff.EXT.ckt (G t) m
          (fun r : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r)) u) :=
        (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC (G t) m
          (fun r : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r))
          (fun r => hX _)).1
      have hfd : fderiv ℝ (Work.Diff.EXT.ConnCov.rmChartTower G x₀ t m
            (fun s : Fin m => v s.succ) i j k l) y (Work.Diff.GE.cBasis (E := E) (v 0))
          = (mvfderiv I (Work.Diff.EXT.ckt (G t) m
                (fun r : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r)))
              (Work.Diff.EXT.pt (I := I) x₀ y)) (X (v 0) (Work.Diff.EXT.pt (I := I) x₀ y)) := by
        rw [hIHf.fderiv_eq]
        rw [← mvfderiv_pt_eq_fderiv (I := I) x₀ (hUtgt y hy)
          (hCktsm.contMDiffAt.mdifferentiableAt (by simp)) (v 0)]
        congr 1
        exact (hgerm y hy (v 0)).eq_of_nhds.symm
      rw [hfd]
      have hIH1 : ∀ (r : Fin m) (p : Fin (Module.finrank ℝ E)),
          Work.Diff.EXT.ConnCov.rmChartTower G x₀ t m
              (Function.update (fun s : Fin m => v s.succ) r p) i j k l y
            = Work.Diff.EXT.ckt (G t) m (fun r' : Fin (m + 4) =>
                X (mkI (Function.update (fun s : Fin m => v s.succ) r p) (quadI i j k l) r'))
              (Work.Diff.EXT.pt (I := I) x₀ y) :=
        fun r p => ih (Function.update (fun s : Fin m => v s.succ) r p) i j k l hy
      have hIH2 : ∀ (p : Fin (Module.finrank ℝ E)),
          Work.Diff.EXT.ConnCov.rmChartTower G x₀ t m (fun s : Fin m => v s.succ) p j k l y
            = Work.Diff.EXT.ckt (G t) m (fun r' : Fin (m + 4) =>
                X (mkI (fun s : Fin m => v s.succ) (quadI p j k l) r'))
              (Work.Diff.EXT.pt (I := I) x₀ y) :=
        fun p => ih (fun s : Fin m => v s.succ) p j k l hy
      have hIH3 : ∀ (p : Fin (Module.finrank ℝ E)),
          Work.Diff.EXT.ConnCov.rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i p k l y
            = Work.Diff.EXT.ckt (G t) m (fun r' : Fin (m + 4) =>
                X (mkI (fun s : Fin m => v s.succ) (quadI i p k l) r'))
              (Work.Diff.EXT.pt (I := I) x₀ y) :=
        fun p => ih (fun s : Fin m => v s.succ) i p k l hy
      have hIH4 : ∀ (p : Fin (Module.finrank ℝ E)),
          Work.Diff.EXT.ConnCov.rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j p l y
            = Work.Diff.EXT.ckt (G t) m (fun r' : Fin (m + 4) =>
                X (mkI (fun s : Fin m => v s.succ) (quadI i j p l) r'))
              (Work.Diff.EXT.pt (I := I) x₀ y) :=
        fun p => ih (fun s : Fin m => v s.succ) i j p l hy
      have hIH5 : ∀ (p : Fin (Module.finrank ℝ E)),
          Work.Diff.EXT.ConnCov.rmChartTower G x₀ t m (fun s : Fin m => v s.succ) i j k p y
            = Work.Diff.EXT.ckt (G t) m (fun r' : Fin (m + 4) =>
                X (mkI (fun s : Fin m => v s.succ) (quadI i j k p) r'))
              (Work.Diff.EXT.pt (I := I) x₀ y) :=
        fun p => ih (fun s : Fin m => v s.succ) i j k p hy
      simp only [hIH1, hIH2, hIH3, hIH4, hIH5]
      have hgrp1 : ∀ r : Fin m,
          Work.Diff.EXT.ckt (G t) m
            (Function.update
              (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r'))
              (Fin.castAdd 4 r)
              (Work.Diff.EXT.dirF (G t) (X (v r.succ)) (X (v 0))))
            (Work.Diff.EXT.pt (I := I) x₀ y)
          = ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) (v r.succ) t
                (Work.Diff.EXT.pt (I := I) x₀ y) *
              Work.Diff.EXT.ckt (G t) m
                (fun r' : Fin (m + 4) => X (mkI (Function.update (fun s : Fin m => v s.succ) r p)
                  (quadI i j k l) r')) (Work.Diff.EXT.pt (I := I) x₀ y) := by
        intro r
        have h := ckt_dirF_update (I := I) hLC G x₀ t m X hX hz (hgerm y hy)
          (mkI (fun s : Fin m => v s.succ) (quadI i j k l)) (Fin.castAdd 4 r) (v 0)
        rw [mkI_castAdd] at h
        refine h.trans ?_
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [update_comp_X_castAdd X m (fun s : Fin m => v s.succ) i j k l r p]
      have hgrpA : Work.Diff.EXT.ckt (G t) m
            (Function.update
              (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r'))
              (Fin.natAdd m 0)
              (Work.Diff.EXT.dirF (G t) (X i) (X (v 0))))
            (Work.Diff.EXT.pt (I := I) x₀ y)
          = ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) i t (Work.Diff.EXT.pt (I := I) x₀ y) *
              Work.Diff.EXT.ckt (G t) m
                (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI p j k l) r'))
                (Work.Diff.EXT.pt (I := I) x₀ y) := by
        have h := ckt_dirF_update (I := I) hLC G x₀ t m X hX hz (hgerm y hy)
          (mkI (fun s : Fin m => v s.succ) (quadI i j k l)) (Fin.natAdd m 0) (v 0)
        rw [mkI_natAdd, quadI_zero] at h
        refine h.trans ?_
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [update_comp_X_natAdd X m (fun s : Fin m => v s.succ) i j k l 0 p]
        rw [update_quadI_zero]
      have hgrpB : Work.Diff.EXT.ckt (G t) m
            (Function.update
              (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r'))
              (Fin.natAdd m 1)
              (Work.Diff.EXT.dirF (G t) (X j) (X (v 0))))
            (Work.Diff.EXT.pt (I := I) x₀ y)
          = ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) j t (Work.Diff.EXT.pt (I := I) x₀ y) *
              Work.Diff.EXT.ckt (G t) m
                (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i p k l) r'))
                (Work.Diff.EXT.pt (I := I) x₀ y) := by
        have h := ckt_dirF_update (I := I) hLC G x₀ t m X hX hz (hgerm y hy)
          (mkI (fun s : Fin m => v s.succ) (quadI i j k l)) (Fin.natAdd m 1) (v 0)
        rw [mkI_natAdd, quadI_one] at h
        refine h.trans ?_
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [update_comp_X_natAdd X m (fun s : Fin m => v s.succ) i j k l 1 p]
        rw [update_quadI_one]
      have hgrpC : Work.Diff.EXT.ckt (G t) m
            (Function.update
              (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r'))
              (Fin.natAdd m 2)
              (Work.Diff.EXT.dirF (G t) (X k) (X (v 0))))
            (Work.Diff.EXT.pt (I := I) x₀ y)
          = ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) k t (Work.Diff.EXT.pt (I := I) x₀ y) *
              Work.Diff.EXT.ckt (G t) m
                (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j p l) r'))
                (Work.Diff.EXT.pt (I := I) x₀ y) := by
        have h := ckt_dirF_update (I := I) hLC G x₀ t m X hX hz (hgerm y hy)
          (mkI (fun s : Fin m => v s.succ) (quadI i j k l)) (Fin.natAdd m 2) (v 0)
        rw [mkI_natAdd, quadI_two] at h
        refine h.trans ?_
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [update_comp_X_natAdd X m (fun s : Fin m => v s.succ) i j k l 2 p]
        rw [update_quadI_two]
      have hgrpD : Work.Diff.EXT.ckt (G t) m
            (Function.update
              (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k l) r'))
              (Fin.natAdd m 3)
              (Work.Diff.EXT.dirF (G t) (X l) (X (v 0))))
            (Work.Diff.EXT.pt (I := I) x₀ y)
          = ∑ p, Work.Diff.GE.chrCoord (I := I) G x₀ p (v 0) l t (Work.Diff.EXT.pt (I := I) x₀ y) *
              Work.Diff.EXT.ckt (G t) m
                (fun r' : Fin (m + 4) => X (mkI (fun s : Fin m => v s.succ) (quadI i j k p) r'))
                (Work.Diff.EXT.pt (I := I) x₀ y) := by
        have h := ckt_dirF_update (I := I) hLC G x₀ t m X hX hz (hgerm y hy)
          (mkI (fun s : Fin m => v s.succ) (quadI i j k l)) (Fin.natAdd m 3) (v 0)
        rw [mkI_natAdd, quadI_three] at h
        refine h.trans ?_
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [update_comp_X_natAdd X m (fun s : Fin m => v s.succ) i j k l 3 p]
        rw [update_quadI_three]
      rw [hgrpA, hgrpB, hgrpC, hgrpD]
      simp only [hgrp1]
      abel

/-- **The chart tower is the geometric tower in the coordinate frame.** -/
theorem main_thm (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (x₀ : M) (t : ℝ) (m : ℕ)
    (v : Fin m → Fin (Module.finrank ℝ E))
    (i j k l : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v i j k l y
      = Work.Diff.EXT.covKRmExt (G t) m
          (fun s : Fin m => Work.Diff.GE.cFrame (I := I) x₀ (v s))
          (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
          (Work.Diff.GE.cFrame (I := I) x₀ k) (Work.Diff.GE.cFrame (I := I) x₀ l)
          (Work.Diff.EXT.pt (I := I) x₀ y) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hz : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source :=
    pt_mem_chart_source (I := I) x₀ hy
  choose X hXs hXc using fun a : Fin (Module.finrank ℝ E) =>
    Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀
      (Work.Diff.GE.cBasis (E := E) a) hz
  have hV : ∀ᶠ w in 𝓝 (Work.Diff.EXT.pt (I := I) x₀ y),
      ∀ a, X a =ᶠ[𝓝 w] Work.Diff.GE.cFrame (I := I) x₀ a := by
    rw [Filter.eventually_all]
    intro a
    exact Work.Diff.EXT.eventuallyEq_nhds_eventually (hXc a)
  obtain ⟨V, hVmem, hVg⟩ := Filter.eventually_iff_exists_mem.mp hV
  have hsrcV : (chartAt H x₀).source ∈ 𝓝 (Work.Diff.EXT.pt (I := I) x₀ y) :=
    (chartAt H x₀).open_source.mem_nhds hz
  have hV'mem : V ∩ (chartAt H x₀).source ∈ 𝓝 (Work.Diff.EXT.pt (I := I) x₀ y) :=
    Filter.inter_mem hVmem hsrcV
  have hptcont : ContinuousAt (Work.Diff.EXT.pt (I := I) x₀) y := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x₀) hy
    rw [show Set.range I = Set.univ from ModelWithCorners.Boundaryless.range_eq_univ] at h
    exact (mdifferentiableWithinAt_univ.mp h).continuousAt
  set U : Set E :=
    interior ((Work.Diff.EXT.pt (I := I) x₀) ⁻¹' (V ∩ (chartAt H x₀).source))
      ∩ (extChartAt I x₀).target with hUdef
  have hUo : IsOpen U := isOpen_interior.inter (isOpen_extChartAt_target (I := I) x₀)
  have hyU : y ∈ U := by
    rw [hUdef]
    exact ⟨mem_interior_iff_mem_nhds.mpr (hptcont.preimage_mem_nhds hV'mem), hy⟩
  have hUtgt : ∀ y' ∈ U, y' ∈ (extChartAt I x₀).target := by
    intro y' hy'
    rw [hUdef] at hy'
    exact hy'.2
  have hgerm : ∀ y' ∈ U, ∀ a, X a =ᶠ[𝓝 (Work.Diff.EXT.pt (I := I) x₀ y')]
      Work.Diff.GE.cFrame (I := I) x₀ a := by
    intro y' hy'
    rw [hUdef] at hy'
    exact hVg _ (interior_subset hy'.1).1
  have hmain := main_ind (I := I) (M := M) hLC G x₀ t X hXs U hUo hUtgt hgerm m v i j k l hyU
  rw [hmain]
  have hconv : Work.Diff.EXT.ckt (G t) m
        (fun r : Fin (m + 4) => X (mkI v (quadI i j k l) r))
      = Work.Diff.EXT.covKRmExt (G t) m (fun s : Fin m => X (v s)) (X i) (X j) (X k) (X l) := by
    rw [mkT_comp_X (I := I) X m v i j k l, Work.Diff.EXT.ckt_quadF]
  rw [hconv]
  have hCf : ∀ a : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.SmoothTFieldAt (I := I) (M := M) (Work.Diff.GE.cFrame (I := I) x₀ a)
        (Work.Diff.EXT.pt (I := I) x₀ y) := by
    intro a
    exact Submission.Geodesic.contMDiffAt_frameSection (I := I) x₀ (Work.Diff.GE.cBasis (E := E) a) hz
  exact Work.Diff.EXT.covK_germ (I := I) (M := M) hLC (G t) m
    (fun s : Fin m => X (v s)) (fun s : Fin m => Work.Diff.GE.cFrame (I := I) x₀ (v s))
    (X i) (Work.Diff.GE.cFrame (I := I) x₀ i) (X j) (Work.Diff.GE.cFrame (I := I) x₀ j)
    (X k) (Work.Diff.GE.cFrame (I := I) x₀ k) (X l) (Work.Diff.GE.cFrame (I := I) x₀ l)
    (Work.Diff.EXT.pt (I := I) x₀ y)
    (fun s => (hXs (v s)).contMDiffAt) (fun s => hCf (v s))
    (hXs i).contMDiffAt (hCf i) (hXs j).contMDiffAt (hCf j)
    (hXs k).contMDiffAt (hCf k) (hXs l).contMDiffAt (hCf l)
    (fun s => hXc (v s)) (hXc i) (hXc j) (hXc k) (hXc l)

end RMChartAux

/-- **The chart recursion for the iterated moving covariant derivatives of the curvature computes
the geometric tower in the coordinate frame.** -/
theorem rmChartTower_eq_covKRmExt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (m : ℕ)
    (v : Fin m → Fin (Module.finrank ℝ E))
    (i j k l : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.EXT.ConnCov.rmChartTower (I := I) (M := M) G x₀ t m v i j k l y
      = Work.Diff.EXT.covKRmExt (G t) m
          (fun s : Fin m => Work.Diff.GE.cFrame (I := I) x₀ (v s))
          (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
          (Work.Diff.GE.cFrame (I := I) x₀ k) (Work.Diff.GE.cFrame (I := I) x₀ l)
          (Work.Diff.EXT.pt (I := I) x₀ y) :=
  RMChartAux.main_thm (I := I) (M := M) hLC G x₀ t m v i j k l hy

end Work.Diff.EXT.ConnCov
