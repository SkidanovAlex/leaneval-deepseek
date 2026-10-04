import Mathlib
import Submission.Work.Diff.EXT.evolX.compLadderDefs
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs
import Submission.Work.Diff.EXT.evolX.mulOpJetsPos
import Submission.Work.Diff.EXT.evolX.wTupConsTrue
import Submission.Work.Diff.EXT.evolX.wTupConsFalse
import Submission.Work.Diff.EXT.evolX.wTupBConsTrue
import Submission.Work.Diff.EXT.evolX.wTupBConsFalse
import Submission.Work.Diff.EXT.evolX.wTupUpdateA
import Submission.Work.Diff.EXT.evolX.wTupUntouchedA
import Submission.Work.Diff.EXT.evolX.wTupUpdateB
import Submission.Work.Diff.EXT.evolX.wTupUntouchedB
import Submission.Work.Diff.EXT.evolX.wTupZeroLemmas
import Submission.Work.Diff.EXT.evolX.sumSplitWPos
import Submission.Work.Diff.EXT.evolX.prodSplitWPos
import Submission.Work.Diff.EXT.evolX.sumWordsChoose
import Submission.Work.Diff.EXT.evolX.dvcDefs
import Submission.Work.Diff.EXT.evolX.dvcFieldSmooth
import Submission.Work.Diff.EXT.evolX.pairVecJetAll
import Submission.Work.Diff.EXT.evolX.ZskPair
import Submission.Work.Diff.EXT.evolX.pairVecZskStrongAtB
import Submission.Work.Diff.EXT.evolX.pairVecZskJetSmooth
import Submission.Work.Diff.EXT.evolX.jetAllPrecomp
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.evolX.jetCalcDefs
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The composition ladder for the contracted tower: vocabulary

This module fixes the vocabulary of the *composition ladder* used to prove the jet bound
`Work.Diff.EXT.evolX.substOp_jets_le_v2B` (the last open input of
`Work.Diff.EXT.evolX.connVarOp_jets`).

## The object

`Work.Diff.EXT.evolX.substOp g k s V` is the level-`k` curvature tower with its slot `s` filled by
the value of a vector-valued operator `V`.  Contracting with the frame-expanded curvature vector
`Zsk g W k s` (`substOp = ⟪V (F 0) (F (s+1)), Zsk g W k s Ψ⟫`, `ZskPair`) turns it into the
**pairing of two vector-valued operators**, and the jets of a pairing are computed by the
**composition** (or "shuffle") ladder: expanding the `a`-fold covariant derivative of a pairing by
the Leibniz rule gives the sum over the `2^a` words `w : Word a` (which of the `a` derivative
directions is applied to which factor) of the pairing of the `wCntT w`-fold covariant derivative of
one factor with the `wCntF w`-fold covariant derivative of the other.

## The layout

We use `Work.Diff.EXT.evolX.Word` and the *shuffle calculus* of
`Submission/Work/Diff/EXT/evolX/mulOpJetsDefs.lean` with `(K₁, K₂) = (K, 2)`:

* the tuple of the operator has arity `K + 2 + a` (`a` derivative directions, newest first, at the
  positions `0, …, a-1`; the *slot block* of `K + 2` entries at the positions `a, …, a+K+1`);
* the `A`-sub-tuple `wTupA K 2 a w F` (arity `K + wCntT w`) is the `U`-side: the `wCntT w`
  directions routed to `U` followed by the `K` arguments of `U`;
* the `B`-sub-tuple `wTupB K 2 a w F` (arity `2 + wCntF w`) is the `V`-side: the `wCntF w`
  directions routed to `V`, followed by the two arguments of `V`.

Everything about these two extraction maps is already proved:
`wTupConsTrue`/`wTupConsFalse`/`wTupBConsTrue`/`wTupBConsFalse` (the `Fin.cons` recursions),
`wTupUpdateA`/`wTupUntouchedA`/`wTupUpdateB`/`wTupUntouchedB` (the effect of updating one entry),
`sumSplitWPos`/`prodSplitWPos` (the splitting of a sum/product along the word), `wTupA_smooth`,
`wTupB_smooth` and `sumWordsChoose` (the count of the words by their number of `true`s).

## The statements of this chapter

* `SOp g V U` / `Stw g V U a w` — the pairing operator and the states of the ladder;
* `stb_Stw_zero`, `stb_dvcStep_eq`, `stb_Stw_update_A`, `stb_Stw_update_B` — the elementary
  structural facts;
* `stb_Stw_mdiff` — the state functions are mdifferentiable (from the `JetSmoothOp` hypotheses, via
  `dvcFieldSmooth` and `MDifferentiableAt.inner_bundle'`);
* `stb_mvfderiv_sum`, `stb_extStep_sum` — additivity of `mvfderiv` and of `extStep` over the sum
  over the words; `stb_sum_cons` — the reindexing
  `∑_w [f (cons true w) + f (cons false w)] = ∑_{w'} f w'`;
* `brho` (+ `stb_brho_val`, `stb_brho_apply_upos`, `stb_brho_bijective`) — the slot permutation
  which turns the layout of `SOp` (the `U`-slots first, then the two `V`-slots) into the layout of
  `substOp` (the two `V`-slots at the positions `0` and `s+1`, the tower slots at the positions
  `upos k s ·`).

The targets of the chapter, proved in the sibling modules, are `Stw_extStep` (the per-word recursion
of the ladder, `substB/Step.lean`), `jetAll_SOp_eq_sum` (the ladder identity,
`substB/Ladder.lean`), `Stw_bound` (the per-state bound, `substB/Bound.lean`) and the pointwise
instantiation `substOp_eq_SOp_comp` (`substB/Comp.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The two operators of the ladder -/

/-- **The pairing form of the composition**: the metric pairing of the value of the vector-valued
operator `U` (arity `K`, on the first `K` entries of the tuple) with the value of the vector-valued
operator `V` (arity `2`, on the last two entries). -/
noncomputable def SOp (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    (Fin (K + 2) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => g.inner y
    (U (fun i : Fin K => F (Fin.castAdd 2 i)) y)
    (V (fun t : Fin 2 => F (Fin.natAdd K t)) y)

/-- **A state of the composition ladder**: for a word `w : Word a` (which of the `a` covariant
derivative directions is applied to `U`, resp. to `V`), the pairing of the `wCntT w`-fold covariant
derivative of `U` on the `A`-sub-tuple with the `wCntF w`-fold covariant derivative of `V` on the
`B`-sub-tuple.  The operator has arity `K + 2 + a`. -/
noncomputable def Stw (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (a : ℕ) (w : Word a) :
    (Fin (K + 2 + a) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => g.inner y
    (dvc g K U (wCntT w) (wTupA K 2 a w F) y)
    (dvc g 2 V (wCntF w) (wTupB K 2 a w F) y)

theorem stb_Stw_zero (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (F : Fin (K + 2 + 0) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Stw (I := I) (M := M) g V U 0 Word.nil F = SOp (I := I) (M := M) g V U F := by
  have hA : wTupA (I := I) (M := M) K 2 0 Word.nil F
      = fun i : Fin K => F (Fin.castAdd 2 i) := by
    funext i
    exact congrArg F (Fin.ext rfl)
  have hB : wTupB (I := I) (M := M) K 2 0 Word.nil F
      = fun t : Fin 2 => F (Fin.natAdd K t) := by
    funext i
    exact congrArg F (Fin.ext rfl)
  show (fun y : M => g.inner y
      (dvc g K U (wCntT (Word.nil : Word 0)) (wTupA (I := I) (M := M) K 2 0 Word.nil F) y)
      (dvc g 2 V (wCntF (Word.nil : Word 0)) (wTupB (I := I) (M := M) K 2 0 Word.nil F) y))
    = fun y : M => g.inner y
      (U (fun i : Fin K => F (Fin.castAdd 2 i)) y)
      (V (fun t : Fin 2 => F (Fin.natAdd K t)) y)
  rw [hA, hB]
  funext y
  simp only [wCntT, wCntF, dvc_zero]

theorem stb_dvcStep_eq (g : Submission.Diff.SMet I M) {K : ℕ}
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (c : ℕ) (B : Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (X : Work.Diff.EXT.TField (I := I) (M := M)) :
    (fun y : M => (Submission.Diff.lcOf g) (dvc g K U c B) y (X y))
      = dvc g K U (c + 1) (Fin.cons X B)
        + ∑ ρ : Fin (K + c), dvc g K U c
            (Function.update B ρ (dirF g (B ρ) X)) := by
  funext y
  show (Submission.Diff.lcOf g) (dvc g K U c B) y (X y)
      = (dvc g K U (c + 1) (Fin.cons X B)) y
        + (∑ ρ : Fin (K + c), dvc g K U c
            (Function.update B ρ (dirF g (B ρ) X))) y
  have key : (dvStep g (dvc g K U c)) (Fin.cons X B) y
      = (Submission.Diff.lcOf g) (dvc g K U c B) y (X y)
        - ∑ x : Fin (K + c),
            dvc g K U c (Function.update B x (dirF g (B x) X)) y := by
    simp only [dvStep, Fin.cons_succ, Fin.cons_zero]
  rw [show dvc g K U (c + 1) = dvStep g (dvc g K U c) from rfl]
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [key, sub_add_cancel]

theorem stb_Stw_update_A (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (a : ℕ) (w : Word (a + 1))
    (F : Fin (K + 2 + (a + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (v : Work.Diff.EXT.TField (I := I) (M := M)) (ρ : Fin (K + wCntT w)) :
    Stw (I := I) (M := M) g V U (a + 1) w
        (Function.update F (wPosA K 2 a w ρ.val) v)
      = fun y => g.inner y
          (dvc g K U (wCntT w)
            (Function.update (wTupA (I := I) (M := M) K 2 (a + 1) w F) ρ v) y)
          (dvc g 2 V (wCntF w)
            (wTupB (I := I) (M := M) K 2 (a + 1) w F) y) := by
  funext y
  show g.inner y (dvc g K U (wCntT w)
        (wTupA (I := I) (M := M) K 2 (a + 1) w
          (Function.update F (wPosA K 2 a w ρ.val) v)) y)
      (dvc g 2 V (wCntF w)
        (wTupB (I := I) (M := M) K 2 (a + 1) w
          (Function.update F (wPosA K 2 a w ρ.val) v)) y)
    = g.inner y (dvc g K U (wCntT w)
        (Function.update (wTupA (I := I) (M := M) K 2 (a + 1) w F) ρ v) y)
      (dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 (a + 1) w F) y)
  rw [wTupUpdateA (I := I) (M := M) K 2 a w F v ρ,
    wTupUntouchedA (I := I) (M := M) K 2 a w F v ρ]

theorem stb_Stw_update_B (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (a : ℕ) (w : Word (a + 1))
    (F : Fin (K + 2 + (a + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (v : Work.Diff.EXT.TField (I := I) (M := M)) (ρ : Fin (2 + wCntF w)) :
    Stw (I := I) (M := M) g V U (a + 1) w
        (Function.update F (wPosB K 2 a w ρ.val) v)
      = fun y => g.inner y
          (dvc g K U (wCntT w)
            (wTupA (I := I) (M := M) K 2 (a + 1) w F) y)
          (dvc g 2 V (wCntF w)
            (Function.update (wTupB (I := I) (M := M) K 2 (a + 1) w F) ρ v) y) := by
  funext y
  show g.inner y (dvc g K U (wCntT w)
        (wTupA (I := I) (M := M) K 2 (a + 1) w
          (Function.update F (wPosB K 2 a w ρ.val) v)) y)
      (dvc g 2 V (wCntF w)
        (wTupB (I := I) (M := M) K 2 (a + 1) w
          (Function.update F (wPosB K 2 a w ρ.val) v)) y)
    = g.inner y (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 (a + 1) w F) y)
      (dvc g 2 V (wCntF w)
        (Function.update (wTupB (I := I) (M := M) K 2 (a + 1) w F) ρ v) y)
  rw [wTupUntouchedB (I := I) (M := M) K 2 a w F v ρ,
    wTupUpdateB (I := I) (M := M) K 2 a w F v ρ]

theorem stb_Stw_mdiff (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hVs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g 3
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g V) x)
    (hUs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) x)
    (a : ℕ) (w : Word a)
    (F : Fin (K + 2 + a) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun z : M => Stw (I := I) (M := M) g V U a w F z) y := by
  have hA : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
      (wTupA (I := I) (M := M) K 2 a w F i) := wTupA_smooth w F hF
  have hB : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
      (wTupB (I := I) (M := M) K 2 a w F i) := wTupB_smooth w F hF
  filter_upwards [dvcFieldSmooth (I := I) (M := M) hLC g x U hUs (wCntT w)
      (wTupA (I := I) (M := M) K 2 a w F) hA,
    dvcFieldSmooth (I := I) (M := M) hLC g x V hVs (wCntF w)
      (wTupB (I := I) (M := M) K 2 a w F) hB] with y hy1 hy2
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  show MDifferentiableAt I 𝓘(ℝ, ℝ)
    (fun z : M => inner ℝ (dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 a w F) z)
      (dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 a w F) z)) y
  exact MDifferentiableAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := (id : M → M))
    (v := fun z : M => dvc g K U (wCntT w) (wTupA (I := I) (M := M) K 2 a w F) z)
    (w := fun z : M => dvc g 2 V (wCntF w) (wTupB (I := I) (M := M) K 2 a w F) z)
    hy1 hy2


/-! ## Additivity of `mvfderiv` over a finite sum -/

/-- **Additivity of `mvfderiv` over a finite sum** of functions mdifferentiable at the point. -/
theorem stb_mvfderiv_sum {ι : Type*} (t : Finset ι) (f : ι → M → ℝ) (x : M)
    (v : TangentSpace I x) (h : ∀ i ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) :
    mvfderiv I (fun y => ∑ i ∈ t, f i y) x v = ∑ i ∈ t, mvfderiv I (f i) x v := by
  classical
  have hdiff : ∀ s : Finset ι, (∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x) →
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => ∑ i ∈ s, f i y) x := by
    intro s hs
    refine (MDifferentiableAt.sum (t := s) (f := f) (fun i hi => hs i hi)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [Finset.sum_apply]
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      change ((mvfderiv I (fun _ : M => (0 : ℝ)) x) v) = (0 : ℝ)
      rw [mvfderiv_const, zero_apply]
  | insert a s ha ih =>
      have ha' : MDifferentiableAt I 𝓘(ℝ, ℝ) (f a) x := h a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) x :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      simp only [Finset.sum_insert ha]
      rw [show (fun y : M => f a y + ∑ i ∈ s, f i y)
          = ((f a) + (fun y : M => ∑ i ∈ s, f i y)) from rfl]
      rw [mvfderiv_add (g := f a) (g' := fun y : M => ∑ i ∈ s, f i y) ha' (hdiff s hs'),
        add_apply]
      rw [ih hs']

/-! ## The reindexing of the word sum -/

/-- **Splitting the words of length `a+1` according to their first letter.** -/
theorem stb_sum_cons (g : Submission.Diff.SMet I M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (a : ℕ) (F : Fin (K + 2 + (a + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) :
    (∑ w : Word a, (Stw (I := I) (M := M) g V U (a + 1) (Word.cons true w) F y
        + Stw (I := I) (M := M) g V U (a + 1) (Word.cons false w) F y))
      = ∑ w' : Word (a + 1), Stw (I := I) (M := M) g V U (a + 1) w' F y := by
  classical
  rw [← Equiv.sum_comp (Word.consEquiv a)
      (fun w' : Word (a + 1) => Stw (I := I) (M := M) g V U (a + 1) w' F y)]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  rfl

/-! ## Additivity of `extStep` over the word sum -/

/-- **The linearity of `extStep` over the sum over the words.** -/
theorem stb_extStep_sum (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hVs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g 3
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g V) x)
    (hUs : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) x)
    (a : ℕ) (F : Fin (K + 2 + (a + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    Filter.EventuallyEq (nhds x)
      (Work.Diff.EXT.extStep (I := I) (M := M) g
        (fun (G : Fin (K + 2 + a) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
          ∑ w : Word a, Stw (I := I) (M := M) g V U a w G y) F)
      (fun y : M => ∑ w : Word a, Work.Diff.EXT.extStep (I := I) (M := M) g
        (Stw (I := I) (M := M) g V U a w) F y) := by
  have hFs : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
      ((fun t : Fin (K + 2 + a) => F t.succ) i) := fun i => hF i.succ
  have hmd : ∀ w : Word a, ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun z : M => Stw (I := I) (M := M) g V U a w
        (fun t : Fin (K + 2 + a) => F t.succ) z) y :=
    fun w => stb_Stw_mdiff (I := I) (M := M) hLC g x V U hVs hUs a w _ hFs
  filter_upwards [Filter.eventually_all.mpr hmd] with y hy
  have hpt : mvfderiv I (fun z : M => ∑ w : Word a, Stw (I := I) (M := M) g V U a w
        (fun t : Fin (K + 2 + a) => F t.succ) z) y ((F 0) y)
      = ∑ w : Word a, mvfderiv I (fun z : M => Stw (I := I) (M := M) g V U a w
          (fun t : Fin (K + 2 + a) => F t.succ) z) y ((F 0) y) :=
    stb_mvfderiv_sum Finset.univ (fun w => fun z => Stw (I := I) (M := M) g V U a w
      (fun t : Fin (K + 2 + a) => F t.succ) z) y ((F 0) y) (fun w _ => hy w)
  simp only [Work.Diff.EXT.extStep]
  beta_reduce
  rw [hpt, Finset.sum_sub_distrib, Finset.sum_comm]

/-! ## The slot permutation turning `SOp` into `substOp` -/

/-- **The slot permutation of the block of `substOp`.**  It maps the block position `j` of `SOp`
(the `k+3` arguments of the tower operator, then the two arguments of `V`) to the block position of
`substOp`: the `j`-th tower argument (for `j ≤ k+2`) sits at `upos k s j` (the slot
`Fin.succAbove s j` shifted by one), the first argument of `V` at the position `0` and its second
argument at the position `s+1`. -/
noncomputable def brho (k : ℕ) (s : Fin (k + 4)) : Fin (k + 5) → Fin (k + 5) :=
  fun j => if h : (j : ℕ) < k + 3 then upos k s ⟨(j : ℕ), h⟩
    else if (j : ℕ) = k + 3 then ⟨0, by omega⟩
    else ⟨(s : ℕ) + 1, by omega⟩

/-- **The value of `brho` on the `U`-part of the block** (the first `k+3` positions). -/
theorem stb_brho_apply_upos (k : ℕ) (s : Fin (k + 4)) (j : Fin (k + 3)) :
    brho k s ⟨(j : ℕ), by have := j.isLt; omega⟩ = upos k s j := by
  rw [brho]
  simp only [dif_pos j.isLt]

/-- **`brho` on the `k+3`-rd position is `0`.** -/
theorem stb_brho_apply_last1 (k : ℕ) (s : Fin (k + 4)) :
    brho k s ⟨k + 3, by omega⟩ = (⟨0, by omega⟩ : Fin (k + 5)) := by
  rw [brho]
  simp

/-- **`brho` on the last position is `s+1`.** -/
theorem stb_brho_apply_last2 (k : ℕ) (s : Fin (k + 4)) :
    brho k s ⟨k + 4, by omega⟩ = (⟨(s : ℕ) + 1, by have := s.isLt; omega⟩ : Fin (k + 5)) := by
  rw [brho]
  simp [show ¬ (k + 4 < k + 3) by omega]

/-- The value form of `stb_brho_apply_upos`. -/
theorem stb_brho_val_upos (k : ℕ) (s : Fin (k + 4)) (j : Fin (k + 5))
    (hj : (j : ℕ) < k + 3) :
    ((brho k s j : Fin (k + 5)) : ℕ)
      = ((Fin.succAbove s ⟨(j : ℕ), hj⟩ : Fin (k + 4)) : ℕ) + 1 := by
  rw [brho]
  simp only [dif_pos hj]
  rfl

/-- **The slot permutation is injective.** -/
theorem stb_brho_injective (k : ℕ) (s : Fin (k + 4)) : Function.Injective (brho k s) := by
  intro j j' h
  have hval := congrArg Fin.val h
  have hlast1 : ((brho k s (⟨k + 3, by omega⟩ : Fin (k + 5)) : Fin (k + 5)) : ℕ) = 0 := by
    rw [stb_brho_apply_last1]
  have hlast2 : ((brho k s (⟨k + 4, by omega⟩ : Fin (k + 5)) : Fin (k + 5)) : ℕ) = (s : ℕ) + 1 := by
    rw [stb_brho_apply_last2]
  by_cases hj : (j : ℕ) < k + 3
  · by_cases hj' : (j' : ℕ) < k + 3
    · rw [stb_brho_val_upos k s j hj, stb_brho_val_upos k s j' hj'] at hval
      have hsu : (Fin.succAbove s ⟨(j : ℕ), hj⟩ : Fin (k + 4))
          = Fin.succAbove s ⟨(j' : ℕ), hj'⟩ := by
        apply Fin.ext
        omega
      have hjj := Fin.succAbove_right_injective hsu
      exact Fin.ext (by have := congrArg Fin.val hjj; omega)
    · have h0 : (j' : ℕ) = k + 3 ∨ (j' : ℕ) = k + 4 := by have := j'.isLt; omega
      rw [stb_brho_val_upos k s j hj] at hval
      rcases h0 with h0 | h0
      · rw [show j' = (⟨k + 3, by omega⟩ : Fin (k + 5)) from Fin.ext h0] at hval
        rw [hlast1] at hval
        omega
      · rw [show j' = (⟨k + 4, by omega⟩ : Fin (k + 5)) from Fin.ext h0] at hval
        rw [hlast2] at hval
        have hsu : (Fin.succAbove s ⟨(j : ℕ), hj⟩ : Fin (k + 4)) = s := by
          apply Fin.ext
          omega
        exact absurd hsu (Fin.succAbove_ne s ⟨(j : ℕ), hj⟩)
  · have h0 : (j : ℕ) = k + 3 ∨ (j : ℕ) = k + 4 := by have := j.isLt; omega
    by_cases hj' : (j' : ℕ) < k + 3
    · rw [stb_brho_val_upos k s j' hj'] at hval
      rcases h0 with h0 | h0
      · rw [show j = (⟨k + 3, by omega⟩ : Fin (k + 5)) from Fin.ext h0] at hval
        rw [hlast1] at hval
        omega
      · rw [show j = (⟨k + 4, by omega⟩ : Fin (k + 5)) from Fin.ext h0] at hval
        rw [hlast2] at hval
        have hsu : (Fin.succAbove s ⟨(j' : ℕ), hj'⟩ : Fin (k + 4)) = s := by
          apply Fin.ext
          omega
        exact absurd hsu (Fin.succAbove_ne s ⟨(j' : ℕ), hj'⟩)
    · have h0' : (j' : ℕ) = k + 3 ∨ (j' : ℕ) = k + 4 := by have := j'.isLt; omega
      rcases h0 with h0 | h0 <;> rcases h0' with h1 | h1
      · exact Fin.ext (by omega)
      · rw [show j = (⟨k + 3, by omega⟩ : Fin (k + 5)) from Fin.ext h0,
            show j' = (⟨k + 4, by omega⟩ : Fin (k + 5)) from Fin.ext h1] at hval
        rw [hlast1, hlast2] at hval
        omega
      · rw [show j = (⟨k + 4, by omega⟩ : Fin (k + 5)) from Fin.ext h0,
            show j' = (⟨k + 3, by omega⟩ : Fin (k + 5)) from Fin.ext h1] at hval
        rw [hlast2, hlast1] at hval
        omega
      · exact Fin.ext (by omega)

/-- **The slot permutation is a bijection.** -/
theorem stb_brho_bijective (k : ℕ) (s : Fin (k + 4)) : Function.Bijective (brho k s) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨stb_brho_injective k s, rfl⟩

/-- **The slot permutation as an equivalence of `Fin (k+5)`.** -/
noncomputable def brhoEquiv (k : ℕ) (s : Fin (k + 4)) : Fin (k + 5) ≃ Fin (k + 5) :=
  Equiv.ofBijective (brho k s) (stb_brho_bijective k s)

/-! ## Two helpers for the per-state bound -/

/-- **Smoothness of the `dvcTup` entries.** -/
theorem stb_dvcTup_smooth {K j : ℕ} (F : Fin (K + j) → Work.Diff.EXT.TField (I := I) (M := M))
    (W : Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i))
    (hW : Work.Diff.EXT.SmoothF (I := I) (M := M) W) :
    ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (dvcTup K j F W i) := by
  intro i
  rw [dvcTup_apply]
  split_ifs with h
  · exact hF _
  · exact hW

/-- **The pairing of the `c`-fold covariant derivative with a test field is a jet of the pairing
operator.**  The pointwise form of `pairVecJetAll` used by the per-state bound. -/
theorem stb_pairVec_jet (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {K : ℕ}
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hU : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) x)
    (c : ℕ) (A : Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (hA : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (A i))
    (W : Work.Diff.EXT.TField (I := I) (M := M))
    (hW : Work.Diff.EXT.SmoothF (I := I) (M := M) W) :
    g.inner x (dvc g K U c A x) (W x)
      = Work.Diff.EXT.jetAll g c (K + 1)
          (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) (dvcTup K c A W) x := by
  have h := pairVecJetAll (I := I) (M := M) hLC g x U hU c (dvcTup K c A W)
    (stb_dvcTup_smooth (I := I) (M := M) A W hA hW)
  have h1 : firstPart (I := I) (M := M) (dvcTup (I := I) (M := M) K c A W) = A := by
    funext i
    rw [firstPart_eq]
    exact dvcTup_castLE K c A W i
  have h2 : lastPart (I := I) (M := M) (dvcTup (I := I) (M := M) K c A W) = W := by
    rw [lastPart_eq]
    exact dvcTup_last K c A W
  rw [h1, h2] at h
  exact h.eq_of_nhds.symm

end Work.Diff.EXT.evolX
