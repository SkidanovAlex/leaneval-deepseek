import Mathlib
import Submission.Work.Diff.EXT.aCovArr_eq_covKAExt
import Submission.Work.Diff.EXT.ATens.Defs
import Submission.Work.Diff.EXT.covKAExt_frame_eq_smoothExt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.Diff.EXT.ConnCov

/-!
# Expansion of `cktA` in a finite family of fields

`Work.Diff.EXT.cktA G t k` is the `k`-th covariant derivative (with respect to the fixed background
connection `∇^{G 0}`) of the lowered connection difference `aOf G t`, evaluated on a `Fin (k+3)`-tuple
of fields.  Its value at a point depends only on the values of the fields at that point and is
`ℝ`-multilinear there (`Work.Diff.EXT.ka_all`, `Work.Diff.EXT.ka_val_dep_all`).

This file proves the resulting expansion of the value of `cktA` when every field of the tuple is
written as a finite linear combination `F q = ∑ i, d q i • V q i` of a family `V`.

## Contents

* `expansionOfSlotwise` — the general algebraic expansion of a slotwise additive and homogeneous
  functional on `Fin n`-tuples;
* `smExtTuple`, `smExtTuple_sma`, `smExtTuple_update` — the tuple of pointwise smooth extensions
  `smoothExt x ·`;
* `cktAVal` and its slotwise additivity/homogeneity, first for the canonical `DecidableEq` instance
  on `Fin (k+3)` (`cktAVal_add_c`, `cktAVal_smul_c`, via `TensPropA_add`/`TensPropA_smul`), then for
  an *arbitrary* instance (`cktAVal_add`, `cktAVal_smul`), which is the form needed inside
  `MultilinearMap.mk`'s fields;
* `cktA_expand` — the expansion on `cktA` itself.
-/

/-- **General slotwise-multilinear expansion.**  If `T` is additive and `ℝ`-homogeneous in every
slot of a `Fin n`-tuple, then expanding a finite linear combination `∑ i, c q i • A q i` in each slot
gives the corresponding sum over all index functions `p : Fin n → ι` of the products of the
coefficients with `T` evaluated on the `A`-tuple selected by `p`.

The hypotheses quantify over *all* `DecidableEq (Fin n)` instances, which is the form in which they
can be discharged when `T` is produced as the `toFun` of a `MultilinearMap`. -/
theorem expansionOfSlotwise
    {X : Type*} [AddCommMonoid X] [Module ℝ X]
    {ι : Type*} [Fintype ι] (n : ℕ) (T : (Fin n → X) → ℝ)
    (hadd : ∀ (iD : DecidableEq (Fin n)) (u : Fin n → X) (s : Fin n) (v w : X),
      T (@Function.update (Fin n) (fun _ => X) iD u s (v + w))
        = T (@Function.update (Fin n) (fun _ => X) iD u s v)
          + T (@Function.update (Fin n) (fun _ => X) iD u s w))
    (hsmul : ∀ (iD : DecidableEq (Fin n)) (u : Fin n → X) (s : Fin n) (c : ℝ) (v : X),
      T (@Function.update (Fin n) (fun _ => X) iD u s (c • v))
        = c * T (@Function.update (Fin n) (fun _ => X) iD u s v))
    (c : Fin n → ι → ℝ) (A : Fin n → ι → X) :
    T (fun q => ∑ i, c q i • A q i)
      = ∑ p : Fin n → ι, (∏ q, c q (p q)) * T (fun q => A q (p q)) := by
  let m : MultilinearMap ℝ (fun _ : Fin n => X) ℝ :=
    MultilinearMap.mk T (by intro iL u s v w; exact hadd iL u s v w)
      (by intro iL u s cc v; exact hsmul iL u s cc v)
  have hm : ⇑m = T := rfl
  rw [← hm, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, hm]

/-- Two `Decidable` instances of the same proposition give the same `dite`. -/
lemma dite_inst_congr {c : Prop} (i₁ i₂ : Decidable c) {α : Sort*} (t : c → α) (e : ¬c → α) :
    @dite α c i₁ t e = @dite α c i₂ t e := by
  cases i₁ with
  | isTrue h₁ =>
      cases i₂ with
      | isTrue h₂ => exact congrArg t (Subsingleton.elim h₁ h₂)
      | isFalse h₂ => exact absurd h₁ h₂
  | isFalse h₁ =>
      cases i₂ with
      | isTrue h₂ => exact absurd h₂ h₁
      | isFalse h₂ => exact congrArg e (Subsingleton.elim h₁ h₂)

/-- `Function.update` does not depend on the choice of the `DecidableEq` instance. -/
lemma update_inst_congr {α : Sort*} {β : α → Sort*} (i₁ i₂ : DecidableEq α)
    (f : (a : α) → β a) (a' : α) (v : β a') :
    @Function.update α β i₁ f a' v = @Function.update α β i₂ f a' v := by
  funext a
  simp only [Function.update]

/-- The canonical `DecidableEq` instance on `Fin n`, named so that it can be referred to inside
contexts that carry a different local instance of the same class. -/
def finDecEq (n : ℕ) : DecidableEq (Fin n) := inferInstance

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Pointwise smooth extensions of tuples of tangent vectors -/

/-- The tuple of the pointwise smooth extensions `smoothExt x` of a tuple of tangent vectors at
`x`. -/
noncomputable def smExtTuple (x : M) {n : ℕ} (u : Fin n → TangentSpace I x) :
    Fin n → Work.Diff.EXT.TfA (I := I) (M := M) :=
  fun q => Submission.Diff.smoothExt x (u q)

/-- Every member of `smExtTuple x u` is a smooth field. -/
lemma smExtTuple_smA (x : M) {n : ℕ} (u : Fin n → TangentSpace I x) :
    ∀ q, Work.Diff.EXT.SmA (I := I) (M := M) (smExtTuple (I := I) (M := M) x u q) :=
  fun q => Work.Diff.GE.smoothExt_cmdiff x (u q)

/-- `smExtTuple` turns `Function.update` on the tuple of vectors into `Function.update` on the tuple
of fields. -/
lemma smExtTuple_update (x : M) {n : ℕ} (u : Fin n → TangentSpace I x) (s : Fin n)
    (v : TangentSpace I x) :
    smExtTuple (I := I) (M := M) x (Function.update u s v)
      = Function.update (smExtTuple (I := I) (M := M) x u) s (Submission.Diff.smoothExt x v) := by
  funext q
  by_cases h : q = s
  · subst h; simp only [smExtTuple, Function.update_self]
  · show Submission.Diff.smoothExt x ((Function.update u s v) q)
        = (Function.update (fun q => Submission.Diff.smoothExt x (u q)) s
            (Submission.Diff.smoothExt x v)) q
    rw [Function.update_of_ne h, Function.update_of_ne h]

/-- The value of the `aOf`-tower on the pointwise smooth extensions of a tuple of tangent vectors. -/
noncomputable def cktAVal (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ) (x : M)
    (u : Fin (k + 3) → TangentSpace I x) : ℝ :=
  Work.Diff.EXT.cktA G t k (smExtTuple (I := I) (M := M) x u) x

/-! ## Slotwise linearity of the value functional -/

/-- Additivity of `cktAVal` in a single slot (canonical `DecidableEq` instance). -/
lemma cktAVal_add_c (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (x : M) (u : Fin (k + 3) → TangentSpace I x) (s : Fin (k + 3))
    (v w : TangentSpace I x) :
    cktAVal (I := I) (M := M) G t k x (Function.update u s (v + w))
      = cktAVal (I := I) (M := M) G t k x (Function.update u s v)
        + cktAVal (I := I) (M := M) G t k x (Function.update u s w) := by
  have hΦ : ∀ q, Work.Diff.EXT.SmA (I := I) (M := M) (smExtTuple (I := I) (M := M) x u q) :=
    smExtTuple_smA x u
  have e1 : smExtTuple (I := I) (M := M) x (Function.update u s (v + w))
      = Function.update (smExtTuple (I := I) (M := M) x u) s
          (Submission.Diff.smoothExt x (v + w)) := smExtTuple_update x u s (v + w)
  have e2 : smExtTuple (I := I) (M := M) x (Function.update u s v)
      = Function.update (smExtTuple (I := I) (M := M) x u) s
          (Submission.Diff.smoothExt x v) := smExtTuple_update x u s v
  have e3 : smExtTuple (I := I) (M := M) x (Function.update u s w)
      = Function.update (smExtTuple (I := I) (M := M) x u) s
          (Submission.Diff.smoothExt x w) := smExtTuple_update x u s w
  show Work.Diff.EXT.cktA G t k (smExtTuple (I := I) (M := M) x (Function.update u s (v + w))) x
      = Work.Diff.EXT.cktA G t k (smExtTuple (I := I) (M := M) x (Function.update u s v)) x
        + Work.Diff.EXT.cktA G t k (smExtTuple (I := I) (M := M) x (Function.update u s w)) x
  rw [e1, e2, e3]
  have h1 : Work.Diff.EXT.cktA G t k
        (Function.update (smExtTuple (I := I) (M := M) x u) s
          (Submission.Diff.smoothExt x (v + w))) x
      = Work.Diff.EXT.cktA G t k
        (Function.update (smExtTuple (I := I) (M := M) x u) s
          (Submission.Diff.smoothExt x v + Submission.Diff.smoothExt x w)) x := by
    refine Work.Diff.EXT.ka_val_dep_all hLC G t k x
      (F := Function.update (smExtTuple (I := I) (M := M) x u) s
        (Submission.Diff.smoothExt x (v + w)))
      (F' := Function.update (smExtTuple (I := I) (M := M) x u) s
        (Submission.Diff.smoothExt x v + Submission.Diff.smoothExt x w))
      (Work.Diff.EXT.smA_update hΦ (Work.Diff.GE.smoothExt_cmdiff x (v + w)))
      (Work.Diff.EXT.smA_update hΦ (Work.Diff.EXT.SmA_add (Work.Diff.GE.smoothExt_cmdiff x v)
        (Work.Diff.GE.smoothExt_cmdiff x w))) ?_
    intro q
    by_cases h : q = s
    · subst h
      simp only [Function.update_self, Work.Diff.GE.smoothExt_apply, Pi.add_apply]
    · rw [Function.update_of_ne h, Function.update_of_ne h]
  rw [h1]
  exact congrFun (Work.Diff.EXT.TensPropA_add (Work.Diff.EXT.ka_all hLC G t k) hΦ s
    (Work.Diff.GE.smoothExt_cmdiff x v) (Work.Diff.GE.smoothExt_cmdiff x w)) x

/-- Homogeneity of `cktAVal` in a single slot (canonical `DecidableEq` instance). -/
lemma cktAVal_smul_c (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (x : M) (u : Fin (k + 3) → TangentSpace I x) (s : Fin (k + 3))
    (c : ℝ) (v : TangentSpace I x) :
    cktAVal (I := I) (M := M) G t k x (Function.update u s (c • v))
      = c * cktAVal (I := I) (M := M) G t k x (Function.update u s v) := by
  have hΦ : ∀ q, Work.Diff.EXT.SmA (I := I) (M := M) (smExtTuple (I := I) (M := M) x u q) :=
    smExtTuple_smA x u
  have e1 : smExtTuple (I := I) (M := M) x (Function.update u s (c • v))
      = Function.update (smExtTuple (I := I) (M := M) x u) s
          (Submission.Diff.smoothExt x (c • v)) := smExtTuple_update x u s (c • v)
  have e2 : smExtTuple (I := I) (M := M) x (Function.update u s v)
      = Function.update (smExtTuple (I := I) (M := M) x u) s
          (Submission.Diff.smoothExt x v) := smExtTuple_update x u s v
  show Work.Diff.EXT.cktA G t k (smExtTuple (I := I) (M := M) x (Function.update u s (c • v))) x
      = c * Work.Diff.EXT.cktA G t k (smExtTuple (I := I) (M := M) x (Function.update u s v)) x
  rw [e1, e2]
  have h1 : Work.Diff.EXT.cktA G t k
        (Function.update (smExtTuple (I := I) (M := M) x u) s
          (Submission.Diff.smoothExt x (c • v))) x
      = Work.Diff.EXT.cktA G t k
        (Function.update (smExtTuple (I := I) (M := M) x u) s
          ((fun _ : M => c) • Submission.Diff.smoothExt x v)) x := by
    refine Work.Diff.EXT.ka_val_dep_all hLC G t k x
      (F := Function.update (smExtTuple (I := I) (M := M) x u) s
        (Submission.Diff.smoothExt x (c • v)))
      (F' := Function.update (smExtTuple (I := I) (M := M) x u) s
        ((fun _ : M => c) • Submission.Diff.smoothExt x v))
      (Work.Diff.EXT.smA_update hΦ (Work.Diff.GE.smoothExt_cmdiff x (c • v)))
      (Work.Diff.EXT.smA_update hΦ (Work.Diff.EXT.SmA_smul (contMDiff_const (c := c))
        (Work.Diff.GE.smoothExt_cmdiff x v))) ?_
    intro q
    by_cases h : q = s
    · subst h
      simp only [Function.update_self, Work.Diff.GE.smoothExt_apply, Pi.smul_apply']
    · rw [Function.update_of_ne h, Function.update_of_ne h]
  rw [h1]
  exact congrFun (Work.Diff.EXT.TensPropA_smul (Work.Diff.EXT.ka_all hLC G t k) hΦ s c
    (Work.Diff.GE.smoothExt_cmdiff x v)) x

/-- Additivity of `cktAVal` in a single slot, with the `DecidableEq` instance as an explicit
argument. -/
lemma cktAVal_add (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (x : M) (iD : DecidableEq (Fin (k + 3)))
    (u : Fin (k + 3) → TangentSpace I x) (s : Fin (k + 3)) (v w : TangentSpace I x) :
    cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s (v + w))
      = cktAVal (I := I) (M := M) G t k x
          (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s v)
        + cktAVal (I := I) (M := M) G t k x
          (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s w) := by
  have e1 : cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s (v + w))
      = cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) (finDecEq (k + 3)) u s
          (v + w)) :=
    congrArg (cktAVal (I := I) (M := M) G t k x)
      (update_inst_congr iD (finDecEq (k + 3)) u s (v + w))
  have e2 : cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s v)
      = cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) (finDecEq (k + 3)) u s v) :=
    congrArg (cktAVal (I := I) (M := M) G t k x)
      (update_inst_congr iD (finDecEq (k + 3)) u s v)
  have e3 : cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s w)
      = cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) (finDecEq (k + 3)) u s w) :=
    congrArg (cktAVal (I := I) (M := M) G t k x)
      (update_inst_congr iD (finDecEq (k + 3)) u s w)
  rw [e1, e2, e3]
  exact cktAVal_add_c hLC G t k x u s v w

/-- Homogeneity of `cktAVal` in a single slot, with the `DecidableEq` instance as an explicit
argument. -/
lemma cktAVal_smul (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (x : M) (iD : DecidableEq (Fin (k + 3)))
    (u : Fin (k + 3) → TangentSpace I x) (s : Fin (k + 3)) (c : ℝ) (v : TangentSpace I x) :
    cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s (c • v))
      = c * cktAVal (I := I) (M := M) G t k x
          (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s v) := by
  have e1 : cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s (c • v))
      = cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) (finDecEq (k + 3)) u s
          (c • v)) :=
    congrArg (cktAVal (I := I) (M := M) G t k x)
      (update_inst_congr iD (finDecEq (k + 3)) u s (c • v))
  have e2 : cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s v)
      = cktAVal (I := I) (M := M) G t k x
        (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) (finDecEq (k + 3)) u s v) :=
    congrArg (cktAVal (I := I) (M := M) G t k x)
      (update_inst_congr iD (finDecEq (k + 3)) u s v)
  rw [e1, e2]
  exact cktAVal_smul_c hLC G t k x u s c v

/-- The value of the `aOf`-tower expands over a finite family of fields: if
`F q = ∑ i, d q i • V q i` for every slot `q`, then the value of `Work.Diff.EXT.cktA` on `F` at `x`
is the sum over all index functions `p` of the products of the coefficients with the value on the
tuple `fun q => V q (p q)`. -/
theorem cktA_expand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (x : M) {ι : Type*} [Fintype ι]
    (F : Fin (k + 3) → Π y : M, TangentSpace I y)
    (d : Fin (k + 3) → ι → M → ℝ)
    (V : Fin (k + 3) → ι → Π y : M, TangentSpace I y)
    (hF : ∀ q, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F q))
    (hd : ∀ q i, ContMDiff I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞) (d q i))
    (hV : ∀ q i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (V q i))
    (hrep : ∀ q y, F q y = ∑ i, d q i y • V q i y) :
    Work.Diff.EXT.cktA G t k F x
      = ∑ p : Fin (k + 3) → ι,
          (Finset.univ.prod (fun q => d q (p q) x))
            * Work.Diff.EXT.cktA G t k (fun q => V q (p q)) x := by
  have hTadd : ∀ (iD : DecidableEq (Fin (k + 3))) (u : Fin (k + 3) → TangentSpace I x)
      (s : Fin (k + 3)) (v w : TangentSpace I x),
      cktAVal (I := I) (M := M) G t k x
          (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s (v + w))
        = cktAVal (I := I) (M := M) G t k x
            (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s v)
          + cktAVal (I := I) (M := M) G t k x
            (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s w) :=
    fun iD u s v w => cktAVal_add hLC G t k x iD u s v w
  have hTsmul : ∀ (iD : DecidableEq (Fin (k + 3))) (u : Fin (k + 3) → TangentSpace I x)
      (s : Fin (k + 3)) (c : ℝ) (v : TangentSpace I x),
      cktAVal (I := I) (M := M) G t k x
          (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s (c • v))
        = c * cktAVal (I := I) (M := M) G t k x
            (@Function.update (Fin (k + 3)) (fun _ => TangentSpace I x) iD u s v) :=
    fun iD u s c v => cktAVal_smul hLC G t k x iD u s c v
  have hexp := expansionOfSlotwise (k + 3) (cktAVal (I := I) (M := M) G t k x) hTadd hTsmul
    (fun q (i : ι) => d q i x) (fun q (i : ι) => V q i x)
  have hL : cktAVal (I := I) (M := M) G t k x (fun q => ∑ i, d q i x • V q i x)
      = Work.Diff.EXT.cktA G t k F x := by
    have htu : (fun q => ∑ i, d q i x • V q i x) = (fun q => F q x) :=
      funext (fun q => (hrep q x).symm)
    rw [htu]
    show Work.Diff.EXT.cktA G t k (smExtTuple (I := I) (M := M) x (fun q => F q x)) x
        = Work.Diff.EXT.cktA G t k F x
    exact Work.Diff.EXT.ka_val_dep_all hLC G t k x
      (F := smExtTuple (I := I) (M := M) x (fun q => F q x)) (F' := F)
      (smExtTuple_smA x _) hF (fun q => Work.Diff.GE.smoothExt_apply x (F q x))
  have hR : ∀ p : Fin (k + 3) → ι,
      cktAVal (I := I) (M := M) G t k x (fun q => V q (p q) x)
        = Work.Diff.EXT.cktA G t k (fun q => V q (p q)) x := by
    intro p
    show Work.Diff.EXT.cktA G t k (smExtTuple (I := I) (M := M) x (fun q => V q (p q) x)) x
        = Work.Diff.EXT.cktA G t k (fun q => V q (p q)) x
    exact Work.Diff.EXT.ka_val_dep_all hLC G t k x
      (F := smExtTuple (I := I) (M := M) x (fun q => V q (p q) x))
      (F' := fun q => V q (p q)) (smExtTuple_smA x _) (fun q => hV q (p q))
      (fun q => Work.Diff.GE.smoothExt_apply x (V q (p q) x))
  rw [← hL, hexp]
  exact Finset.sum_congr rfl (fun p _ => by rw [hR p])

end Work.Diff.EXT.ConnCov
