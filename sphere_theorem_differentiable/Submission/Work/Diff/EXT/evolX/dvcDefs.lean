import Mathlib
import Submission.Work.Diff.EXT.evolX.compLadderDefs
import Submission.Work.Diff.EXT.jetSmoothDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `dvc` sections: vocabulary

This module fixes the vocabulary used to prove that the covariant-derivative sections of a
vector-valued operator are mdifferentiable (`Work.Diff.EXT.evolX.dvcFieldSmooth`).

## The two objects

* `chartFrame x i` — the *chart frame* of the tangent bundle at `x`: the section whose coordinates
  in the trivialisation `trivializationAt E (TangentSpace I) x` are the `i`-th basis vector of `E`.
  It is smooth on the chart at `x` (but not globally); its values at points near `x` form a basis
  of `T_yM`.

* `dvcTup K j F W` — the tuple layout of the ladder: given a `(K+j)`-tuple `F` (the arguments of
  the vector-valued operator `dvc g K U j`) and one further field `W`, it is the `((K+1)+j)`-tuple
  `(F 0, …, F (K+j-1), W)` — the `dvc`-tuple followed by the extra slot `W`.  This is the argument
  tuple of `jetAll g j (K+1) (pairVec g U)`, whose value is the pairing of the `j`-th covariant
  derivative of `U` with `W`.

## ROUTE for the pairing-to-section step (`sectionOfChartPairing`)

To show that a section `V : Π y, T_yM` is mdifferentiable at `x` from the mdifferentiability of
its pairings `⟪V, chartFrame x i⟫` against the chart frame:

* Globalise each chart-frame vector with `Work.Diff.T.exists_global_eventuallyEq_symmL`
  (`Submission/Work/Diff/T/FrameExt.lean`, PROVED): a globally smooth field agreeing near `x` with
  `chartFrame x i`.  Smoothness of the Gram entries comes from `ContMDiff.inner_bundle`.
* The *exact analogue* of the proof, in the `C^∞` (instead of pointwise-`MDifferentiableAt`)
  setting, is `Work.EXT.lc_section_of_inner` in `Submission/Work/EXT/lcSmooth_noBoundary.lean`:
  copy it and replace `ContMDiffAt I 𝓘(ℝ,ℝ) ∞` by `MDifferentiableAt I 𝓘(ℝ,ℝ)`, `CMDiff ∞` by the
  pointwise hypothesis, and read off the conclusion through
  `Trivialization.mdifferentiableAt_section_iff`.  In that proof

  - `Γ y := Matrix.gram ℝ (fun i => Z i y)` (`Z i` the globally smooth globalisations) has smooth
    entries;
  - `(Γ x).det ≠ 0` by `Matrix.posDef_gram_of_linearIndependent` (`Γ x` is the Gram matrix of the
    basis `chartFrame x · x`);
  - the entries of `((Γ y)ᵀ)⁻¹` are *smooth* near `x` (`det` smooth, `det ≠ 0` near `x` by
    continuity, `adjugate` polynomial in the entries) — copy `det_smooth`/`hadj`/`hinv`;
  - the coefficients `c i y := ∑ j, ((Γ y)ᵀ)⁻¹ i j * ⟪V y, Z j y⟫` are mdifferentiable at `x`
    (`MDifferentiableAt.mul` with a smooth factor, `.sum`);
  - `V =ᶠ[𝓝 x] (fun y => ∑ i, c i y • Z i y)` (the algebra `hexp`/`hsys`/`hxq` of
    `lc_section_of_inner`);
  - the right-hand side is `MDifferentiableAt I I.tangent` at `x` by `MDifferentiableAt.smul_section`
    and `MDifferentiableAt.sum_section`;
  - conclude with `MDifferentiableAt.congr_of_eventuallyEq`.

Note: `lc_section_of_inner` is stated with the metric as an *instance*; here `g : SMet I M` is an
explicit argument, and one starts the proof with
`letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩`
(and `haveI : IsContMDiffRiemannianBundle I ∞ E _ := inferInstance`), after which `inner ℝ` and
`g.inner` are definitionally the same, as in `Work.Diff.EXT.evolX.pairingSplitNB`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The chart frame of the tangent bundle at `x`**: the section of `TM` whose coordinates in the
trivialisation at `x` are the `i`-th basis vector of `E`. -/
noncomputable def chartFrame (x : M) (i : Fin (Module.finrank ℝ E)) :
    (y : M) → TangentSpace I y :=
  fun y => (Bundle.Trivialization.symmL ℝ (FiberBundle.trivializationAt E (TangentSpace I) x) y)
    (Module.finBasis ℝ E i)

/-- **The tuple layout of the ladder.**  On the `(K+j)`-tuple `F` (the arguments of the vector-valued
operator `dvc g K U j`) and the extra field `W`, this is the `((K+1)+j)`-tuple
`(F 0, …, F (K+j-1), W)`. -/
noncomputable def dvcTup (K j : ℕ) (F : Fin (K + j) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) : Fin ((K + 1) + j) → TField (I := I) (M := M) :=
  fun i => if h : (i : ℕ) < K + j then F ⟨i, h⟩ else W

/-- **The definitional unfolding of `dvcTup`.** -/
theorem dvcTup_apply (K j : ℕ) (F : Fin (K + j) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) (i : Fin ((K + 1) + j)) :
    dvcTup (I := I) (M := M) K j F W i
      = if h : (i : ℕ) < K + j then F ⟨i, h⟩ else W := rfl

/-- **The value of `dvcTup` at an index in the range of `F`.** -/
theorem dvcTup_eq_of_lt {K j : ℕ} (F : Fin (K + j) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) (i : Fin ((K + 1) + j)) (h : (i : ℕ) < K + j) :
    dvcTup (I := I) (M := M) K j F W i = F ⟨(i : ℕ), h⟩ := dif_pos h

/-- **The value of `dvcTup` at the last index is the extra field.** -/
theorem dvcTup_eq_of_ge {K j : ℕ} (F : Fin (K + j) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) (i : Fin ((K + 1) + j)) (h : ¬ (i : ℕ) < K + j) :
    dvcTup (I := I) (M := M) K j F W i = W := dif_neg h

/-- The value of `Fin.castLE` is the value of the original index. -/
theorem dvcField_castLE_val {K j : ℕ} (i : Fin (K + j)) :
    ((Fin.castLE (by omega) i : Fin ((K + 1) + j)) : ℕ) = (i : ℕ) := rfl

/-- **The entries of `dvcTup` before the last one.** -/
theorem dvcTup_castLE (K j : ℕ) (F : Fin (K + j) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) (i : Fin (K + j)) :
    dvcTup (I := I) (M := M) K j F W (Fin.castLE (by omega) i) = F i := by
  rw [dvcTup_eq_of_lt (K := K) (j := j) F W (Fin.castLE (by omega) i) (by exact i.isLt)]
  exact congrArg F (Fin.ext rfl)

/-- **The last entry of `dvcTup` is the extra field.** -/
theorem dvcTup_last (K j : ℕ) (F : Fin (K + j) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) :
    dvcTup (I := I) (M := M) K j F W ⟨K + j, by omega⟩ = W :=
  dvcTup_eq_of_ge (K := K) (j := j) F W ⟨K + j, by omega⟩ (by simp)

/-- **The entry of `dvcTup` at the first index.** -/
theorem dvcTup_apply_zero (K j : ℕ) (F : Fin (K + (j + 1)) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) :
    dvcTup (I := I) (M := M) K (j + 1) F W 0 = F 0 := by
  rw [dvcTup_eq_of_lt (K := K) (j := j + 1) F W 0 (by simp)]
  exact congrArg F (Fin.ext rfl)

/-- **The base case**: the entries of `dvcTup K 0` before the last one. -/
theorem dvcTup_zero_castSucc (K : ℕ) (F : Fin K → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) (i : Fin K) :
    dvcTup (I := I) (M := M) K 0 F W (Fin.castSucc i) = F i := by
  rw [dvcTup_eq_of_lt (K := K) (j := 0) F W (Fin.castSucc i) (by exact i.isLt)]
  exact congrArg F (Fin.ext rfl)

/-- **The base case**: the last entry of `dvcTup K 0`. -/
theorem dvcTup_zero_last (K : ℕ) (F : Fin K → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) :
    dvcTup (I := I) (M := M) K 0 F W (Fin.last K) = W :=
  dvcTup_eq_of_ge (K := K) (j := 0) F W (Fin.last K) (by simp [Fin.val_last])

/-- **Shifting a step of `dvcTup`** (evaluated form): the `(i+1)`-st entry of the `(j+1)`-tuple is
the `i`-th entry of the shifted `j`-tuple. -/
theorem dvcTup_succ_apply (K j : ℕ) (F : Fin (K + (j + 1)) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) (i : Fin ((K + 1) + j)) :
    dvcTup (I := I) (M := M) K (j + 1) F W i.succ
      = dvcTup (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W i := by
  have hkey : ((i.succ : ℕ) < K + (j + 1)) ↔ ((i : ℕ) < K + j) := by
    simp only [Fin.val_succ]; omega
  by_cases h : (i : ℕ) < K + j
  · rw [dvcTup_eq_of_lt (K := K) (j := j + 1) F W i.succ (hkey.mpr h),
      dvcTup_eq_of_lt (K := K) (j := j) (fun i : Fin (K + j) => F i.succ) W i h]
    exact congrArg F (Fin.ext (by simp only [Fin.val_succ]))
  · rw [dvcTup_eq_of_ge (K := K) (j := j + 1) F W i.succ (fun hh => h (hkey.mp hh)),
      dvcTup_eq_of_ge (K := K) (j := j) (fun i : Fin (K + j) => F i.succ) W i h]

/-- **Shifting a step of `dvcTup`**: dropping the first entry of the `(j+1)`-tuple is dropping the
first entry of the `((K+1)+(j+1))`-tuple. -/
theorem dvcTup_succ (K j : ℕ) (F : Fin (K + (j + 1)) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) :
    (fun i : Fin ((K + 1) + j) =>
        dvcTup (I := I) (M := M) K (j + 1) F W i.succ)
      = dvcTup (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W :=
  funext (fun i => dvcTup_succ_apply (I := I) (M := M) K j F W i)

/-- **Updating an entry of `dvcTup` before the last one.** -/
theorem dvcTup_update (K j : ℕ) (F : Fin (K + j) → TField (I := I) (M := M))
    (W : TField (I := I) (M := M)) (r : Fin (K + j)) (X : TField (I := I) (M := M)) :
    Function.update (dvcTup (I := I) (M := M) K j F W)
        (Fin.castLE (by omega) r) X
      = dvcTup (I := I) (M := M) K j (Function.update F r X) W := by
  have hval : ((Fin.castLE (by omega) r : Fin ((K + 1) + j)) : ℕ) = (r : ℕ) := rfl
  have hcast : (Fin.castLE (by omega) r : Fin ((K + 1) + j))
      = (⟨(r : ℕ), by omega⟩ : Fin ((K + 1) + j)) := Fin.ext rfl
  funext i
  rw [Function.update_apply]
  by_cases hir : i = Fin.castLE (by omega) r
  · rw [if_pos hir]
    have hlt : (i : ℕ) < K + j := by
      have h1 : (i : ℕ) = ((Fin.castLE (by omega) r : Fin ((K + 1) + j)) : ℕ) :=
        congrArg Fin.val hir
      rw [hval] at h1
      rw [h1]
      exact r.isLt
    rw [dvcTup_eq_of_lt (K := K) (j := j) (Function.update F r X) W i hlt]
    have hri : (⟨(i : ℕ), hlt⟩ : Fin (K + j)) = r := by
      refine Fin.ext ?_
      show (i : ℕ) = (r : ℕ)
      have h1 : (i : ℕ) = ((Fin.castLE (by omega) r : Fin ((K + 1) + j)) : ℕ) :=
        congrArg Fin.val hir
      rwa [hval] at h1
    rw [Function.update_apply, if_pos hri]
  · rw [if_neg hir]
    by_cases hi : (i : ℕ) < K + j
    · rw [dvcTup_eq_of_lt (K := K) (j := j) F W i hi,
        dvcTup_eq_of_lt (K := K) (j := j) (Function.update F r X) W i hi,
        Function.update_apply,
        if_neg (fun hc => hir (by
          refine Fin.ext ?_
          show (i : ℕ) = ((Fin.castLE (by omega) r : Fin ((K + 1) + j)) : ℕ)
          have h1 : (⟨(i : ℕ), hi⟩ : Fin (K + j)) = r := hc
          have h2 : (i : ℕ) = (r : ℕ) := congrArg Fin.val h1
          rw [hval]
          exact h2))]
    · rw [dvcTup_eq_of_ge (K := K) (j := j) F W i hi,
        dvcTup_eq_of_ge (K := K) (j := j) (Function.update F r X) W i hi]

/-- **Updating the last entry of `dvcTup` replaces the extra field.** -/
theorem dvcTup_update_last (K j : ℕ) (F : Fin (K + j) → TField (I := I) (M := M))
    (W X : TField (I := I) (M := M)) :
    Function.update (dvcTup (I := I) (M := M) K j F W) ⟨K + j, by omega⟩ X
      = dvcTup (I := I) (M := M) K j F X := by
  funext i
  rw [Function.update_apply]
  by_cases hi : (i : ℕ) < K + j
  · rw [if_neg (fun hc => by
        have h2 : (i : ℕ) = K + j := congrArg Fin.val hc
        omega),
      dvcTup_eq_of_lt (K := K) (j := j) F W i hi,
      dvcTup_eq_of_lt (K := K) (j := j) F X i hi]
  · have hlast : i = (⟨K + j, by omega⟩ : Fin ((K + 1) + j)) := by
      refine Fin.ext ?_
      show (i : ℕ) = K + j
      have := i.isLt
      omega
    rw [if_pos hlast, dvcTup_eq_of_ge (K := K) (j := j) F X i hi]

/-- **Membership of the smoothness hypotheses for a `dvcTup`.** -/
theorem smoothF_dvcTup {K j : ℕ} {F : Fin (K + j) → TField (I := I) (M := M)}
    {W : TField (I := I) (M := M)} (hF : ∀ i, SmoothF (F i)) (hW : SmoothF W) :
    ∀ i, SmoothF (dvcTup (I := I) (M := M) K j F W i) := by
  intro i
  by_cases h : (i : ℕ) < K + j
  · rw [dvcTup_eq_of_lt (K := K) (j := j) F W i h]
    exact hF _
  · rw [dvcTup_eq_of_ge (K := K) (j := j) F W i h]
    exact hW

end Work.Diff.EXT.evolX
