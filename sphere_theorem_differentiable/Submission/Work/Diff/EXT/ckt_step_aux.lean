import Mathlib
import Submission.Work.Diff.EXT.curvNormK_frame_indepL
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.covK_valueDepN
import Submission.Work.Diff.GE.hasDerivAt_mvfderiv
import Submission.Work.Diff.GE.ExtTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary lemmas for `Work.Diff.EXT.ckt_step_tderiv`

Supporting material for the time-derivative of one step of the curvature tower `∇^k Rm`:

* `ckt_familySmoothAt` — the tower `(s,y) ↦ ckt (G s) k U y` is `C^∞` at `(t,y)` along a Ricci
  flow (from the proved `Work.Diff.EXT.covK_familySmooth` and the bridge
  `Work.Diff.EXT.ckt_eq_covKRmExt`);
* `hasDerivAt_ckt_family` — the scalar corollary: `s ↦ ckt (G s) k U y` is differentiable at `t`;
* `hasDerivAt_linMap_apply_family` — the basis product rule for a curve of linear functionals;
* `kptSlotLin` — the (linear) map `w ↦ Kpt g x k (update v j w)` of `∇^k Rm` in one slot;
* the value-dependence identities `kpt_eq_ckt_update`, `ckt_update_eq_constant`.

NOTE ON IMPORTS.  The clash-free copy `curvNormK_frame_indepL` of `curvNormK_frame_indep` is used,
because the joint smoothness lemma `covK_familySmooth` (whose closure contains
`Work.Diff.GE.norms_defs`) may not be imported together with the non-`L` copy (both would declare
`Work.Diff.GE.rot5`, cf. the note in `cktestep_tderiv.lean`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **Joint smoothness of the curvature tower along a Ricci flow.**  For a smooth Ricci flow `G` on
`[0,T)`, an interior time `t ∈ Ioo 0 T` and a tuple `U` of globally smooth fields, the function
`(s,y) ↦ ckt (G s) k U y` is `C^∞` at `(t,y)`. -/
theorem ckt_familySmoothAt
    (hLC : LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) {y : M}
    {k : ℕ} {U : Fin (k + 4) → (y : M) → TangentSpace I y}
    (hU : ∀ i, SmoothTField (I := I) (M := M) (U i)) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ckt (G p.1) k U p.2) (t, y) := by
  have hV : IsOpen (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) := isOpen_Ioo.prod isOpen_univ
  have hJM : Work.Diff.EXT.JointMet G (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) :=
    (jointMet_prod G (Set.Ico 0 T)).mp hflow.1 |>.mono
      (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl _))
  have hsub : (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) ⊆ (Set.univ : Set (ℝ × M)) :=
    fun p _ => Set.mem_univ p
  have hVf : ∀ i : Fin k,
      JointField (fun _ : ℝ => U (Fin.castAdd 4 i)) (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) :=
    fun i => (jointField_const (I := I) (M := M) (hU _)).mono hsub
  have hA : JointField (fun _ : ℝ => U (Fin.natAdd k 0)) (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) :=
    (jointField_const (I := I) (M := M) (hU _)).mono hsub
  have hB : JointField (fun _ : ℝ => U (Fin.natAdd k 1)) (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) :=
    (jointField_const (I := I) (M := M) (hU _)).mono hsub
  have hC : JointField (fun _ : ℝ => U (Fin.natAdd k 2)) (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) :=
    (jointField_const (I := I) (M := M) (hU _)).mono hsub
  have hD : JointField (fun _ : ℝ => U (Fin.natAdd k 3)) (Set.Ioo 0 T ×ˢ (Set.univ : Set M)) :=
    (jointField_const (I := I) (M := M) (hU _)).mono hsub
  have h4 := covK_familySmooth (I := I) (M := M) hLC hV hJM k hVf hA hB hC hD
  have hfun : (fun p : ℝ × M => ckt (G p.1) k U p.2)
      = fun p : ℝ × M => covKRmExt (G p.1) k (fun i : Fin k => U (Fin.castAdd 4 i))
          (U (Fin.natAdd k 0)) (U (Fin.natAdd k 1)) (U (Fin.natAdd k 2)) (U (Fin.natAdd k 3)) p.2 := by
    funext p
    exact ckt_eq_covKRmExt (G p.1) k U p.2
  rw [← hfun] at h4
  exact h4.contMDiffAt (hV.mem_nhds ⟨ht, Set.mem_univ y⟩)

/-- **The tower is differentiable along the flow.**  Scalar form of `ckt_familySmoothAt`. -/
theorem hasDerivAt_ckt_family
    (hLC : LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    {k : ℕ} {U : Fin (k + 4) → (y : M) → TangentSpace I y}
    (hU : ∀ i, SmoothTField (I := I) (M := M) (U i)) (y : M) :
    HasDerivAt (fun s : ℝ => ckt (G s) k U y) (deriv (fun s : ℝ => ckt (G s) k U y) t) t := by
  have h1 := ckt_familySmoothAt (I := I) (M := M) hLC hflow ht (y := y) hU
  have h2 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => ckt (G s) k U y) t := by
    have hcomp := h1.comp t (contMDiffAt_id.prodMk (contMDiffAt_const (c := y)))
    simpa only [Function.comp_def, id_eq] using hcomp
  exact (h2.contDiffAt.differentiableAt (by simp)).hasDerivAt

/-! ## The product rule for a curve of linear functionals -/

/-- **Product rule with the linear-map derivative available only through a basis.**  If `V` has
derivative `v` at `t`, and for every basis vector `b i = Module.finBasis ℝ E i` the scalar function
`s ↦ L s (b i)` is differentiable at `t`, then `s ↦ L s (V s)` has derivative
`L t v + deriv (fun s ↦ L s (V t)) t` at `t`.  (Only the finitely many basis coordinates are used,
so no continuity of `L` in the operator norm is needed.) -/
theorem hasDerivAt_linMap_apply_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : ℝ → (E →ₗ[ℝ] ℝ)} {V : ℝ → E} {v : E} {t : ℝ}
    (hV : HasDerivAt V v t)
    (hL : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => L s (Module.finBasis ℝ E i))
        (deriv (fun s => L s (Module.finBasis ℝ E i)) t) t) :
    HasDerivAt (fun s => L s (V s)) (L t v + deriv (fun s => L s (V t)) t) t := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb
  have hsumcoord : ∀ x : E, (∑ i, b.coord i x • b i) = x := by
    intro x
    have h1 : (∑ i, b.coord i x • b i) = ∑ i, b.repr x i • b i :=
      Finset.sum_congr rfl (fun i _ => by rw [Module.Basis.coord_apply])
    rw [h1, b.sum_repr]
  have hpoint : ∀ (s : ℝ) (w : E), L s w = ∑ i, b.coord i w * L s (b i) := by
    intro s w
    conv_lhs => rw [← hsumcoord w]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])
  have hcoord : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => b.coord i (V s)) (b.coord i v) t := by
    intro i
    have hc : HasFDerivAt (fun w : E => b.coord i w) ((b.coord i).toContinuousLinearMap) (V t) :=
      ContinuousLinearMap.hasFDerivAt ((b.coord i).toContinuousLinearMap)
    have h2 := (hc.comp t hV.hasFDerivAt).hasDerivAt
    have hfun : (fun s : ℝ => b.coord i (V s)) = (fun w : E => b.coord i w) ∘ V := rfl
    have hval : (((b.coord i).toContinuousLinearMap ∘SL ContinuousLinearMap.toSpanSingleton ℝ v) 1)
        = b.coord i v := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rw [← hfun, hval] at h2
    exact h2
  have hder : HasDerivAt (fun s => ∑ i, b.coord i (V s) * L s (b i))
      (∑ i, (b.coord i v * L t (b i) + b.coord i (V t) * deriv (fun s => L s (b i)) t)) t := by
    have hsum := HasDerivAt.sum (u := Finset.univ) (A := fun i s => b.coord i (V s) * L s (b i))
      (A' := fun i => b.coord i v * L t (b i) + b.coord i (V t) * deriv (fun s => L s (b i)) t)
      (fun i _ => (hcoord i).mul (hL i))
    convert hsum using 1
    ext s
    rw [Finset.sum_apply]
  have h1val : (∑ i, b.coord i v * L t (b i)) = L t v := (hpoint t v).symm
  have h2val : (∑ i, b.coord i (V t) * deriv (fun s => L s (b i)) t) = deriv (fun s => L s (V t)) t := by
    have hS : HasDerivAt (fun s : ℝ => ∑ i, b.coord i (V t) * L s (b i))
        (∑ i, b.coord i (V t) * deriv (fun s => L s (b i)) t) t := by
      have hsum := HasDerivAt.sum (u := Finset.univ) (A := fun i s => b.coord i (V t) * L s (b i))
        (A' := fun i => b.coord i (V t) * deriv (fun s => L s (b i)) t)
        (fun i _ => (hL i).const_mul _)
      convert hsum using 1
      ext s
      rw [Finset.sum_apply]
    have hcongr : (fun s : ℝ => L s (V t)) = fun s => ∑ i, b.coord i (V t) * L s (b i) :=
      funext (fun s => hpoint s (V t))
    rw [← hS.deriv, ← hcongr]
  have hfun : (fun s : ℝ => L s (V s)) = fun s => ∑ i, b.coord i (V s) * L s (b i) :=
    funext (fun s => hpoint s (V s))
  rw [hfun]
  have hD : (∑ i, (b.coord i v * L t (b i) + b.coord i (V t) * deriv (fun s => L s (b i)) t))
      = L t v + deriv (fun s => L s (V t)) t := by
    rw [Finset.sum_add_distrib, h1val, h2val]
  rw [← hD]
  exact hder

/-! ## `∇^k Rm` in one slot, and its value dependence -/

/-- **`∇^k Rm` as a linear functional of one slot.**  The map `w ↦ Kpt g x k (update v j w)` is
linear (`Kpt` is multilinear in the values). -/
noncomputable def kptSlotLin
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    (v : Fin (k + 4) → TangentSpace I x) (j : Fin (k + 4)) :
    TangentSpace I x →ₗ[ℝ] ℝ where
  toFun w := Kpt g x k (Function.update v j w)
  map_add' a b := Kpt_add hLC g x k v j a b
  map_smul' c a := Kpt_smul hLC g x k v j c a

/-- Unfolding of `kptSlotLin`. -/
theorem kptSlotLin_apply (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    (v : Fin (k + 4) → TangentSpace I x) (j : Fin (k + 4)) (w : TangentSpace I x) :
    kptSlotLin (I := I) (M := M) hLC g x k v j w = Kpt g x k (Function.update v j w) := rfl

/-- **`Kpt` in one slot is `ckt` on the tuple with that slot replaced by a constant field.** -/
theorem kpt_eq_ckt_update
    (hLC : LCSmooth I M) (g : SMet I M) {k : ℕ} (x : M)
    {F' : Fin (k + 4) → (y : M) → TangentSpace I y} (hF' : ∀ i, SmoothTField (I := I) (M := M) (F' i))
    (j : Fin (k + 4)) (w : TangentSpace I x) :
    Kpt g x k (Function.update (fun i => F' i x) j w)
      = ckt g k (Function.update F' j (smoothExt x w)) x := by
  have h1 : Kpt g x k (Function.update (fun i => F' i x) j w)
      = ckt g k (fun i => smoothExt x ((Function.update (fun i => F' i x) j w) i)) x := rfl
  rw [h1]
  refine (ckt_valueDep_all (I := I) (M := M) hLC g k x ?_ ?_ ?_).symm
  · refine smoothF_update (G := F') ?_ (Work.Diff.GE.smoothExt_cmdiff x w)
    intro i
    exact hF' i
  · intro i
    have h := Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x
      ((Function.update (fun i => F' i x) j w) i)
    exact h
  · intro i
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self, Work.Diff.GE.smoothExt_apply]
    · simp only [Function.update_of_ne hi, Work.Diff.GE.smoothExt_apply]

/-- **Value dependence in the slot that is being differentiated**: replacing the field in one slot
of the tuple by the constant field with the same value at `x` does not change `ckt` at `x`. -/
theorem ckt_update_eq_constant
    (hLC : LCSmooth I M) (g : SMet I M) {k : ℕ} (x : M)
    {F' : Fin (k + 4) → (y : M) → TangentSpace I y} (hF' : ∀ i, SmoothTField (I := I) (M := M) (F' i))
    (j : Fin (k + 4)) {U : (y : M) → TangentSpace I y}
    (hU : SmoothTField (I := I) (M := M) U) :
    ckt g k (Function.update F' j U) x
      = ckt g k (Function.update F' j (smoothExt x (U x))) x := by
  refine ckt_valueDep_all (I := I) (M := M) hLC g k x ?_ ?_ ?_
  · refine smoothF_update (G := F') ?_ hU
    intro i; exact hF' i
  · refine smoothF_update (G := F') ?_ (Work.Diff.GE.smoothExt_cmdiff x (U x))
    intro i; exact hF' i
  · intro i
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self, Work.Diff.GE.smoothExt_apply]
    · simp only [Function.update_of_ne hi]

end Work.Diff.EXT
