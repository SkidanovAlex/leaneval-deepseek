import Mathlib
import Submission.Work.Diff.EXT.evolK_bridges
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.EXT.lcSmooth_noBoundary
import Submission.Work.Diff.GE.cov3Rm_ricci

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-!
# The `k = 1` case of the rough Laplacian of `∇^k Rm`, in the two vocabularies

`Work.Diff.EXT.lapCovKRm g x k u a b c d` is the component of the *rough* Laplacian
`Δ∇^k Rm = Σ_m ∇_m∇_m∇^k Rm` of the `k`-th covariant derivative of the curvature, traced in the
frame `onFrame g x`; it is built from the recursive `covKRmExt` tower.  At `k = 1` the GE area
writes the same object as `Work.Diff.GE.lapCovRmAt g x v a b c d`, built from the explicit tensors
`covRm`, `cov2Rm`, `cov3Rm`.  This file identifies the two, so that the GE-area `k = 1` component
estimates (`Work.Diff.GE.covRm_frame_evol_abs`, `hasDerivWithinAt_covRm_le`) can be fed into the
`k`-th order interface `EvolCompK` (`Submission/Work/Diff/EXT/evolKDefs.lean`, needed for
`EvolK`), cf. the companion bridges in `Submission/Work/Diff/EXT/evolK_bridges.lean`.

Both sides unfold to `Σ_m (∇_m ∇_m ∇_v Rm)(a,b,c,d)`: one step of the tower recursion is exactly
one `ExtTensor`-derivative `Work.Diff.GE.extD` of the packed `Fin (k+4)`-tuple
(`Work.Diff.EXT.ckt`), and the level-one tower agrees with `∇Rm` on values, by the
value-dependence of the tower `Work.Diff.EXT.covKRmExt_tensorial`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The tower as an iteration of `extD` -/

/-- `Rm` as an `ExtTensor` of arity `4`. -/
noncomputable def rmPT (g : SMet I M) : Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin 4) :=
  fun F => fun y => rmP g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)

/-- The first slot of the tuple is consumed as the differentiation direction. -/
noncomputable def shift (g : SMet I M) {m : ℕ}
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin m)) :
    Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin (m + 1)) :=
  fun G => fun y => Work.Diff.GE.extD (lcOf g) τ y (G 0) (fun j : Fin m => G j.succ)

/-- `shift` written out. -/
theorem shift_apply (g : SMet I M) {m : ℕ}
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin m))
    (G : Fin (m + 1) → TField (I := I) (M := M)) :
    shift g τ G
      = (fun y : M => Work.Diff.GE.extD (lcOf g) τ y (G 0) (fun j : Fin m => G j.succ)) := rfl

/-- The `k = 0` level of the tower is `rmPT`. -/
theorem ckt_zero_eq_rmPT (g : SMet I M) : ckt g 0 = rmPT g := rfl

/-- One recursion step of the tower is one `extD`. -/
theorem ckt_succ_eq_shift (g : SMet I M) (k : ℕ) : ckt g (k + 1) = shift g (ckt g k) := by
  funext F y
  show ckt g (k + 1) F y
      = Work.Diff.GE.extD (lcOf g) (ckt g k) y (F 0) (fun j : Fin (k + 4) => F j.succ)
  rw [ckt_succ, Work.Diff.GE.extD_eq]
  simp only [Pi.sub_apply, Finset.sum_apply, Work.Diff.GE.upd]
  rfl

/-! ## Level one -/

/-- One unfolding step: `extD` of the `(0,4)`-curvature tensor is the level-one tower. -/
theorem extD_rmPT_eq_covKRmExt (g : SMet I M) (x : M) (X : TField (I := I) (M := M))
    (G : Fin 4 → TField (I := I) (M := M)) :
    Work.Diff.GE.extD (lcOf g) (rmPT g) x X G
      = covKRmExt g 1 (fun _ => X) (G 0) (G 1) (G 2) (G 3) x := by
  rw [Work.Diff.GE.extD_eq]
  rw [show rmPT g G = (fun y : M => rmP g y (G 0 y) (G 1 y) (G 2 y) (G 3 y)) from rfl]
  simp only [covKRmExt, Work.Diff.GE.upd, Function.update_apply, Finset.univ_eq_empty,
    Finset.sum_empty, rmPT]
  rw [Fin.sum_univ_four]
  simp
  ring_nf

/-- `covKRmExt` at level `1` agrees with `covRm` on the values of its fields
(value-dependence of the tower at level one, via `covKRmExt_tensorial`). -/
theorem covKRmExt_one_eq_covRm (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {X A B C D : TField (I := I) (M := M)}
    (hX : CMDiff ∞ (T% X)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    covKRmExt g 1 (fun _ => X) A B C D x = covRm g x (X x) (A x) (B x) (C x) (D x) := by
  have h := covKRmExt_tensorial hLC 1 g x (fun _ => X) (fun _ => smoothExt x (X x))
    A (smoothExt x (A x)) B (smoothExt x (B x))
    C (smoothExt x (C x)) D (smoothExt x (D x))
    (fun _ => hX) (fun _ => Work.Diff.GE.smoothExt_cmdiff x (X x))
    hA (Work.Diff.GE.smoothExt_cmdiff x (A x)) hB (Work.Diff.GE.smoothExt_cmdiff x (B x))
    hC (Work.Diff.GE.smoothExt_cmdiff x (C x)) hD (Work.Diff.GE.smoothExt_cmdiff x (D x))
    (fun _ => (Work.Diff.GE.smoothExt_apply x (X x)).symm)
    (Work.Diff.GE.smoothExt_apply x (A x)).symm (Work.Diff.GE.smoothExt_apply x (B x)).symm
    (Work.Diff.GE.smoothExt_apply x (C x)).symm (Work.Diff.GE.smoothExt_apply x (D x)).symm
  rw [h]
  exact covKRm_one g x (X x) (A x) (B x) (C x) (D x)

/-- Level one in the `extD` form: `extD` of `rmPT` is `covRm` on the values. -/
theorem extD_rmPT_eq_covRm (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {X : TField (I := I) (M := M)} {G : Fin 4 → TField (I := I) (M := M)}
    (hX : CMDiff ∞ (T% X)) (hG : ∀ i, CMDiff ∞ (T% (G i))) :
    Work.Diff.GE.extD (lcOf g) (rmPT g) x X G
      = covRm g x (X x) (G 0 x) (G 1 x) (G 2 x) (G 3 x) := by
  rw [extD_rmPT_eq_covKRmExt]
  exact covKRmExt_one_eq_covRm hLC g x hX (hG 0) (hG 1) (hG 2) (hG 3)

/-- `shift g (rmPT g)` is `covRmT g` on smooth tuples. -/
theorem shift_rmPT_eq_covRmT (hLC : LCSmooth I M) (g : SMet I M)
    {F : Fin 5 → TField (I := I) (M := M)} (hF : ∀ i, CMDiff ∞ (T% (F i))) :
    shift g (rmPT g) F = Work.Diff.GE.covRmT g F := by
  funext y
  show Work.Diff.GE.extD (lcOf g) (rmPT g) y (F 0) (fun j : Fin 4 => F j.succ)
      = Work.Diff.GE.covRmT g F y
  rw [extD_rmPT_eq_covRm hLC g y (hF 0) (fun i => hF i.succ)]
  have e0 : F (Fin.succ 0) = F 1 := rfl
  have e1 : F (Fin.succ 1) = F 2 := rfl
  have e2 : F (Fin.succ 2) = F 3 := rfl
  have e3 : F (Fin.succ 3) = F 4 := rfl
  rw [e0, e1, e2, e3]
  rfl

/-! ## Two `shift`s are one `extDD` -/

/-- Iterating the `extD` pattern twice is the two-step `extDD`. -/
theorem extD_cons_eq_extDD_aux
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {m : ℕ} (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin m))
    (x : M) (X Y : TField (I := I) (M := M)) (F : Fin m → TField (I := I) (M := M)) :
    Work.Diff.GE.extD cov
        (fun (G : Fin (m + 1) → TField (I := I) (M := M)) => fun y =>
          Work.Diff.GE.extD cov τ y (G 0) (fun j : Fin m => G j.succ))
        x X (Fin.cons Y F)
      = Work.Diff.GE.extDD cov τ x X Y F := by
  rw [Work.Diff.GE.extD_eq, Work.Diff.GE.extDD_eq, Fin.sum_univ_succ]
  simp only [Work.Diff.GE.upd, Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero,
    ← Fin.cons_update]
  ring

/-- Two `shift`s are one `extDD` (in the `Fin.tail` form convenient here). -/
theorem shift_shift_apply (g : SMet I M) {m : ℕ}
    (τ : Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin m))
    (x : M) (F : Fin (m + 2) → TField (I := I) (M := M)) :
    shift g (shift g τ) F x
      = Work.Diff.GE.extDD (lcOf g) τ x (F 0) (F 1) (Fin.tail (Fin.tail F)) := by
  show Work.Diff.GE.extD (lcOf g) (shift g τ) x (F 0) (fun j : Fin (m + 1) => F j.succ)
      = Work.Diff.GE.extDD (lcOf g) τ x (F 0) (F 1) (Fin.tail (Fin.tail F))
  rw [show (fun j : Fin (m + 1) => F j.succ) = Fin.cons (F 1) (Fin.tail (Fin.tail F)) from by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.cons_zero]
      rfl
    · intro i
      simp only [Fin.cons_succ, Fin.tail]]
  exact extD_cons_eq_extDD_aux (lcOf g) τ x (F 0) (F 1) (Fin.tail (Fin.tail F))

/-- `extD` respects agreement of tensors on smooth tuples. -/
theorem extD_congr_smooth (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : Work.Diff.GE.CovSmooth cov) {m : ℕ}
    {τ τ' : Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin m)}
    {x : M} {X : TField (I := I) (M := M)} {F : Fin m → TField (I := I) (M := M)}
    (hX : CMDiff ∞ (T% X)) (hF : ∀ i, CMDiff ∞ (T% (F i)))
    (hτ : ∀ (G : Fin m → TField (I := I) (M := M)),
      (∀ i, CMDiff ∞ (T% (G i))) → τ G = τ' G) :
    Work.Diff.GE.extD cov τ x X F = Work.Diff.GE.extD cov τ' x X F := by
  rw [Work.Diff.GE.extD_eq, Work.Diff.GE.extD_eq]
  congr 1
  · rw [hτ F hF]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hτ _ (fun j => Work.Diff.GE.smoothTuple_upd cov hcov hX hF i j)]

/-- `extDD` respects agreement of tensors on smooth tuples. -/
theorem extDD_congr_smooth (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : Work.Diff.GE.CovSmooth cov) {m : ℕ}
    {τ τ' : Work.Diff.GE.ExtTensor (I := I) (M := M) (Fin m)}
    {x : M} {X Y : TField (I := I) (M := M)} {F : Fin m → TField (I := I) (M := M)}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hF : ∀ i, CMDiff ∞ (T% (F i)))
    (hτ : ∀ (G : Fin m → TField (I := I) (M := M)),
      (∀ i, CMDiff ∞ (T% (G i))) → τ G = τ' G) :
    Work.Diff.GE.extDD cov τ x X Y F = Work.Diff.GE.extDD cov τ' x X Y F := by
  rw [Work.Diff.GE.extDD_eq, Work.Diff.GE.extDD_eq]
  rw [show (fun y : M => Work.Diff.GE.extD cov τ y Y F)
        = (fun y : M => Work.Diff.GE.extD cov τ' y Y F) from
      funext (fun y => extD_congr_smooth cov hcov hY hF hτ)]
  rw [extD_congr_smooth cov hcov (Work.Diff.GE.cmdiff_covAlong cov hcov hX hY) hF hτ]
  rw [show (∑ i, Work.Diff.GE.extD cov τ x Y (Work.Diff.GE.upd cov X F i))
        = (∑ i, Work.Diff.GE.extD cov τ' x Y (Work.Diff.GE.upd cov X F i)) from
      Finset.sum_congr rfl (fun i _ => extD_congr_smooth cov hcov hY
        (fun j => Work.Diff.GE.smoothTuple_upd cov hcov hX hF i j) hτ)]

/-- `extDD` of `shift g (rmPT g)` is `extDD` of `covRmT g`. -/
theorem extDD_shift_rmPT_eq (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {X Y : TField (I := I) (M := M)} {F : Fin 5 → TField (I := I) (M := M)}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hF : ∀ i, CMDiff ∞ (T% (F i))) :
    Work.Diff.GE.extDD (lcOf g) (shift g (rmPT g)) x X Y F
      = Work.Diff.GE.extDD (lcOf g) (Work.Diff.GE.covRmT g) x X Y F := by
  obtain ⟨hcov⟩ := (hLC g).1
  exact extDD_congr_smooth (lcOf g) hcov hX hY hF (fun _ hG => shift_rmPT_eq_covRmT hLC g hG)

/-! ## The main computation -/

/-- `covKRm` at level `3` is `cov3Rm` on the values. -/
theorem covKRm_three_eq_cov3Rm (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin 3 → TangentSpace I x) (a b c d : TangentSpace I x) :
    covKRm g x 3 W a b c d = Work.Diff.GE.cov3Rm g x (W 0) (W 1) (W 2) a b c d := by
  obtain ⟨hcov⟩ := (hLC g).1
  set F : Fin 7 → TField (I := I) (M := M) :=
    mkT (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) with hF
  have hFsm : ∀ i, CMDiff ∞ (T% (F i)) := by
    rw [hF]
    refine smoothF_mkT' (w := fun s => smoothExt x (W s)) (B :=
      quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) ?_ ?_
    · intro i
      exact Work.Diff.GE.smoothExt_cmdiff x (W i)
    · intro p
      fin_cases p <;> simp only [quad_zero, quad_one, quad_two, quad_three] <;>
        exact Work.Diff.GE.smoothExt_cmdiff x _
  have hF0 : F 0 = smoothExt x (W 0) := by
    rw [hF, show (0 : Fin 7) = Fin.castAdd 4 (0 : Fin 3) from by decide]
    exact mkT_castAdd (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) 0
  have hF1 : F 1 = smoothExt x (W 1) := by
    rw [hF, show (1 : Fin 7) = Fin.castAdd 4 (1 : Fin 3) from by decide]
    exact mkT_castAdd (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) 1
  have hF2 : F 2 = smoothExt x (W 2) := by
    rw [hF, show (2 : Fin 7) = Fin.castAdd 4 (2 : Fin 3) from by decide]
    exact mkT_castAdd (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) 2
  have hF3 : F 3 = smoothExt x a := by
    rw [hF, show (3 : Fin 7) = Fin.natAdd 3 (0 : Fin 4) from by decide]
    exact mkT_natAdd (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) 0
  have hF4 : F 4 = smoothExt x b := by
    rw [hF, show (4 : Fin 7) = Fin.natAdd 3 (1 : Fin 4) from by decide]
    exact mkT_natAdd (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) 1
  have hF5 : F 5 = smoothExt x c := by
    rw [hF, show (5 : Fin 7) = Fin.natAdd 3 (2 : Fin 4) from by decide]
    exact mkT_natAdd (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) 2
  have hF6 : F 6 = smoothExt x d := by
    rw [hF, show (6 : Fin 7) = Fin.natAdd 3 (3 : Fin 4) from by decide]
    exact mkT_natAdd (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) 3
  have ht0 : (Fin.tail (Fin.tail F)) 0 = F 2 := rfl
  have ht1 : (Fin.tail (Fin.tail F)) 1 = F 3 := rfl
  have ht2 : (Fin.tail (Fin.tail F)) 2 = F 4 := rfl
  have ht3 : (Fin.tail (Fin.tail F)) 3 = F 5 := rfl
  have ht4 : (Fin.tail (Fin.tail F)) 4 = F 6 := rfl
  have hFx : (F 0) x = W 0 := by
    rw [hF0]
    exact Work.Diff.GE.smoothExt_apply x (W 0)
  have h1 : covKRm g x 3 W a b c d = ckt g 3 F x := by
    rw [show covKRm g x 3 W a b c d
        = covKRmExt g 3 (fun s => smoothExt x (W s))
            (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) x from rfl]
    rw [hF]
    exact (ckt_mkT_eq g 3 (fun s => smoothExt x (W s))
      (quad (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)) x).symm
  have h2 : ckt g 3 F x = Work.Diff.GE.extDD (lcOf g) (Work.Diff.GE.covRmT g) x (F 0) (F 1)
      (Fin.tail (Fin.tail F)) := by
    rw [ckt_succ_eq_shift, ckt_succ_eq_shift, ckt_succ_eq_shift, ckt_zero_eq_rmPT,
      shift_shift_apply (g := g) (τ := shift g (rmPT g)) (x := x) (F := F)]
    exact extDD_shift_rmPT_eq hLC g x (hFsm 0) (hFsm 1)
      (fun i => hFsm i.succ.succ)
  have h3 : Work.Diff.GE.extDD (lcOf g) (Work.Diff.GE.covRmT g) x (F 0) (F 1)
        (Fin.tail (Fin.tail F))
      = Work.Diff.GE.cov3Rm g x (W 0) (W 1) (W 2) a b c d := by
    rw [show Work.Diff.GE.cov3Rm g x (W 0) (W 1) (W 2) a b c d
        = Work.Diff.GE.cov3RmExt g x (W 0) (smoothExt x (W 1))
            (smoothExt x (W 2)) (smoothExt x a) (smoothExt x b) (smoothExt x c)
            (smoothExt x d) from rfl]
    rw [Work.Diff.GE.extDD_covRmT hLC g x (F 0) (F 1) (hFsm 0) (hFsm 1)
      (Fin.tail (Fin.tail F)) (fun j => hFsm j.succ.succ)]
    rw [ht0, ht1, ht2, ht3, ht4, hF1, hF2, hF3, hF4, hF5, hF6, hFx]
  rw [h1, h2, h3]

/-- **The `k = 1` case of the rough Laplacian in the two vocabularies.** -/
theorem lapCovKRm_one_eq_lapCovRmAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    Work.Diff.EXT.lapCovKRm g x 1 (fun _ => v) a b c d
      = Work.Diff.GE.lapCovRmAt g x v a b c d := by
  have hLC : LCSmooth I M := Work.EXT.lcSmooth_noBoundary
  have hpt : ∀ m : Fin (Module.finrank ℝ E),
      covKRm g x 3 (Fin.cons (onFrame g x m) (Fin.cons (onFrame g x m) (fun _ => v))) a b c d
        = Work.Diff.GE.cov3Rm g x (onFrame g x m) (onFrame g x m) v a b c d := by
    intro m
    rw [covKRm_three_eq_cov3Rm hLC g x
      (Fin.cons (onFrame g x m) (Fin.cons (onFrame g x m) (fun _ => v))) a b c d]
    have h1 : (1 : Fin 3) = (0 : Fin 2).succ := by decide
    have h2 : (2 : Fin 3) = ((0 : Fin 1).succ).succ := by decide
    simp only [h1, h2, Fin.cons_zero, Fin.cons_succ]
  show (∑ m : Fin (Module.finrank ℝ E),
      covKRm g x (1 + 2) (Fin.cons (onFrame g x m) (Fin.cons (onFrame g x m) (fun _ => v)))
        a b c d)
    = ∑ m : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cov3Rm g x (onFrame g x m) (onFrame g x m) v a b c d
  exact Finset.sum_congr rfl (fun m _ => hpt m)

end Work.Diff.EXT
