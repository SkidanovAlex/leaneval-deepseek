import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ConnCov.aOf_hasDerivAt
import Submission.Work.Diff.EXT.ConnCov.tower_aOf_hasDerivAt
import Submission.Work.Diff.EXT.covKAExt_tensorial
import Submission.Work.Diff.T.FrameExt
import Submission.Work.Diff.EXT.ConnCov.tower_dAOfBase_congr_germ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reaction bound for the frozen tower of the connection difference (Shi input) -- auxiliaries

This module collects the *definitions* and *elementary lemmas* about the reaction tower
`tower (lcOf (G 0)) (dAOfBase G t)` of the connection difference, used both by the target
`Work.Diff.EXT.ConnCov.dAOfTowerBoundShi` (`Submission/Work/Diff/EXT/ConnCov/dAOfTowerBoundShi.lean`)
and by the sibling modules that prove its inputs
(`aComp_jets_of_aOfTower`, `chartMat_jets_of_aComp_jets`, `dAOfTower_chart_bound`, ...).

It is separated from the target so that those siblings can import the lemmas *without* importing the
(necessarily open) target module.

## What is here

* `dAOfBase_apply` — the *explicit* value of `dAOfBase G t` on smooth fields (the Koszul combination
  of `dtMet`), obtained from the proved `aOf_hasDerivAt` and `HasDerivAt.deriv`.

* `tower_dAOfBase_eq_deriv` — **Clairaut in the shape used below**: the `∇^{G 0}`-tower of
  `dAOfBase G t` at level `k` *is* the time derivative of the `∇^{G 0}`-tower of `aOf G ·` at level
  `k` (the proved `tower_aOf_hasDerivAt`, rewritten with `HasDerivAt.deriv`).

* `dAOf_tower_val_dep` — **tensoriality (value dependence) of the reaction tower**: the value of
  `tower (lcOf (G 0)) (dAOfBase G t) k` at `x` depends only on the *values* of its `k + 3` field
  arguments at `x`.

* `aOf_tower_value_bound` — the `ValBound` hypothesis `hA` rewritten in *value* form (arbitrary
  smooth fields, not just the `Classical.epsilon`-chosen extensions).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The explicit value of `dAOfBase` on smooth fields.**  At an interior time this is the
expression produced by the first variation of the Levi-Civita connection (`aOf_hasDerivAt`):
`−2 Ric(∇^{g_t} − ∇^{g_0}, ·) + ½(∇^{g_t}_{X}h(Y,Z) + ∇^{g_t}_Y h(X,Z) − ∇^{g_t}_Z h(X,Y))` with
`h = dtMet G t`. -/
theorem dAOfBase_apply
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : SmE I M X) (hY : SmE I M Y) (hZ : SmE I M Z) (x : M) :
    dAOfBase G t (Fin.elim0 : Fin 0 → (Π y : M, TangentSpace I y)) X Y Z x
      = -2 * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x
          (Submission.Diff.lcOf (G t) Y x (X x) - Submission.Diff.lcOf (G 0) Y x (X x)) (Z x)
        + (1 / 2 : ℝ) * (Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
              (Submission.Diff.dtMet G t) X Y Z x
            + Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
              (Submission.Diff.dtMet G t) Y X Z x
            - Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
              (Submission.Diff.dtMet G t) Z X Y x) := by
  have h := (Work.Diff.EXT.ConnCov.aOf_hasDerivAt (I := I) (M := M) hLC hflow ht
    hX hY hZ x).deriv
  simpa only [dAOfBase] using h

/-- **Clairaut for the reaction tower.**  The `∇^{G 0}`-tower of `dAOfBase G t` at level `k` is the
`t`-derivative of the `∇^{G 0}`-tower of `aOf G ·` at level `k` (the connection `∇^{G 0}` is
independent of `t`).  This is the proved `tower_aOf_hasDerivAt`, rewritten with
`HasDerivAt.deriv`. -/
theorem tower_dAOfBase_eq_deriv
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ)
    (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y)
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k v A B C x
      = deriv (fun s : ℝ => tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G s) k v A B C x) t :=
  (Work.Diff.EXT.ConnCov.tower_aOf_hasDerivAt (I := I) (M := M) hLC hflow ht k v A B C
    hv hA hB hC x).deriv.symm

/-- **Tensoriality (value dependence) of the reaction tower.**  For smooth field tuples with the
same values at `x`, the values of `tower (lcOf (G 0)) (dAOfBase G t) k` at `x` agree.  The proof
rewrites both sides as `t`-derivatives of the `aOf`-tower (`tower_dAOfBase_eq_deriv`) and uses the
*proved* tensoriality `covKAExt_tensorial` of the `aOf`-tower at every time `s`. -/
theorem dAOf_tower_val_dep
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (x : M)
    (v v' : Fin k → (Π y : M, TangentSpace I y))
    (A A' B B' C C' : Π y : M, TangentSpace I y)
    (hv : ∀ i, SmE I M (v i)) (hv' : ∀ i, SmE I M (v' i))
    (hA : SmE I M A) (hA' : SmE I M A') (hB : SmE I M B) (hB' : SmE I M B')
    (hC : SmE I M C) (hC' : SmE I M C')
    (hvv : ∀ i, v i x = v' i x) (hAA : A x = A' x) (hBB : B x = B' x) (hCC : C x = C' x) :
    tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k v A B C x
      = tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k v' A' B' C' x := by
  rw [tower_dAOfBase_eq_deriv (I := I) (M := M) hLC hflow ht k v A B C hv hA hB hC x,
    tower_dAOfBase_eq_deriv (I := I) (M := M) hLC hflow ht k v' A' B' C' hv' hA' hB' hC' x]
  congr 1
  funext s
  rw [tower_eq_covKAExt G s k]
  exact Work.Diff.EXT.covKAExt_tensorial (I := I) (M := M) hLC G s k x v v' A A' B B' C C'
    hv hv' hA hA' hB hB' hC hC' hvv hAA hBB hCC

/-- **The `ValBound` hypothesis in *value* form.**  `ValBound` evaluates the tower on the
`Classical.epsilon`-chosen extensions `smoothExt x ·`; by the proved tensoriality
`covKAExt_tensorial` of the `aOf`-tower, the same bound holds for *arbitrary* smooth fields
(with the same values).  This is the form in which `hA` is applied to coordinate/frame fields. -/
theorem aOf_tower_value_bound
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (Bk : ℝ)
    (h : ValBound G t k (tower (Submission.Diff.lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G t) k)
      Bk) :
    ∀ (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y) (x : M),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C →
      |tower (Submission.Diff.lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G t) k v A B C x|
        ≤ Bk * (Finset.univ.prod (fun i : Fin k =>
              Real.sqrt ((G t).inner x (v i x) (v i x))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x)) := by
  intro v A B C x hv hA hB hC
  have key : tower (Submission.Diff.lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G t) k v A B C x
      = valOp (tower (Submission.Diff.lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G t) k) x
          (fun i => v i x) (A x) (B x) (C x) := by
    rw [valOp, tower_eq_covKAExt G t k]
    exact Work.Diff.EXT.covKAExt_tensorial (I := I) (M := M) hLC G t k x v
      (fun i => Submission.Diff.smoothExt x (v i x)) A (Submission.Diff.smoothExt x (A x))
      B (Submission.Diff.smoothExt x (B x)) C (Submission.Diff.smoothExt x (C x))
      hv (fun i => Work.Diff.GE.smoothExt_cmdiff x (v i x)) hA
      (Work.Diff.GE.smoothExt_cmdiff x (A x)) hB
      (Work.Diff.GE.smoothExt_cmdiff x (B x)) hC
      (Work.Diff.GE.smoothExt_cmdiff x (C x))
      (fun i => (Work.Diff.GE.smoothExt_apply x (v i x)).symm)
      (Work.Diff.GE.smoothExt_apply x (A x)).symm
      (Work.Diff.GE.smoothExt_apply x (B x)).symm
      (Work.Diff.GE.smoothExt_apply x (C x)).symm
  rw [key]
  exact h x (fun i => v i x) (A x) (B x) (C x)

/-! ## The packed reaction tower

For the *reduction* to the metric-norm shape of the target one wants to see the reaction tower as a
`(k+3)`-fold linear functional on the tangent space at `x`.  The packing used throughout the
workspace puts the `k` differentiation slots first (`Fin.castAdd 3 ·`) and the three value slots last
(`Fin.natAdd k ·`), cf. `Work.Diff.EXT.mkT3`.  `tvdP` is the corresponding packed tower on *fields*,
`tvdVal` its value functional on the smooth extensions `smoothExt x ·`.
-/

/-- **The packed reaction tower.**  `tvdP G t k F` is the level-`k` tower of `dAOfBase G t` evaluated
on the field tuple packed by `F : Fin (k+3) → TF` (direction slots first, then the three value
slots). -/
noncomputable def tvdP (G : ℝ → SMet I M) (t : ℝ) (k : ℕ)
    (F : Fin (k + 3) → TF (I := I) (M := M)) : M → ℝ :=
  fun x => tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
    (fun i : Fin k => F (Fin.castAdd 3 i)) (F (Fin.natAdd k 0)) (F (Fin.natAdd k 1))
    (F (Fin.natAdd k 2)) x

/-- The packing of a `Fin (k+3)`-tuple from its direction part and its three value slots is the
identity. -/
theorem mkT3_self [T2Space M] {k : ℕ} (F : Fin (k + 3) → TF (I := I) (M := M)) :
    mkT3 (fun i : Fin k => F (Fin.castAdd 3 i))
      (trip3 (F (Fin.natAdd k 0)) (F (Fin.natAdd k 1)) (F (Fin.natAdd k 2))) = F := by
  funext s
  exact Fin.addCases (fun i => mkT3_castAdd _ _ i)
    (fun p => by fin_cases p <;> exact mkT3_natAdd _ _ _) s

/-- `tvdP` on a packed tuple is the tower with the three value slots written out. -/
theorem tvdP_mkT3 [T2Space M] {k : ℕ} (G : ℝ → SMet I M) (t : ℝ)
    (v : Fin k → TF (I := I) (M := M))
    (B : Fin 3 → TF (I := I) (M := M)) :
    tvdP G t k (mkT3 v B) = tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k v (B 0) (B 1) (B 2) := by
  funext x
  simp only [tvdP]
  rw [show (fun i : Fin k => mkT3 v B (Fin.castAdd 3 i)) = v from
        funext (fun i => mkT3_castAdd v B i),
    mkT3_natAdd, mkT3_natAdd, mkT3_natAdd]

/-- The packed `aOf`-tower in coordinates: `cktA` on a `Fin (k+3)`-tuple is `covKAExt` with the
three value slots singled out. -/
theorem cktA_pack [T2Space M] {k : ℕ} (G : ℝ → SMet I M) (t : ℝ)
    (F : Fin (k + 3) → TF (I := I) (M := M))
    (x : M) :
    cktA G t k F x = covKAExt G t k (fun i : Fin k => F (Fin.castAdd 3 i))
      (F (Fin.natAdd k 0)) (F (Fin.natAdd k 1)) (F (Fin.natAdd k 2)) x := by
  conv_lhs => rw [← mkT3_self (k := k) F]
  rw [Work.Diff.EXT.cktA_mkT3_eq]
  simp only [trip3_zero, trip3_one, trip3_two]

/-- **The `t`-derivative identity for the packed tower.**  The packed reaction tower is the
`t`-derivative of the packed `aOf`-tower (Clairaut). -/
theorem tvdP_hasDerivAt
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (F : Fin (k + 3) → TF (I := I) (M := M))
    (hF : ∀ s, SmE I M (F s)) (x : M) :
    HasDerivAt (fun s : ℝ => cktA G s k F x) (tvdP G t k F x) t := by
  have h := Work.Diff.EXT.ConnCov.tower_aOf_hasDerivAt (I := I) (M := M) hLC hflow ht k
    (fun i : Fin k => F (Fin.castAdd 3 i)) (F (Fin.natAdd k 0)) (F (Fin.natAdd k 1))
    (F (Fin.natAdd k 2)) (fun i => hF (Fin.castAdd 3 i)) (hF (Fin.natAdd k 0))
    (hF (Fin.natAdd k 1)) (hF (Fin.natAdd k 2)) x
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => ?_))
  show cktA G s k F x = tower (Submission.Diff.lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G s) k
    (fun i : Fin k => F (Fin.castAdd 3 i)) (F (Fin.natAdd k 0)) (F (Fin.natAdd k 1))
    (F (Fin.natAdd k 2)) x
  rw [tower_eq_covKAExt]
  exact cktA_pack G s F x

/-- **Clairaut for the packed reaction tower**, in `deriv` form. -/
theorem tvdP_eq_deriv
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (F : Fin (k + 3) → TF (I := I) (M := M))
    (hF : ∀ s, SmE I M (F s)) (x : M) :
    tvdP G t k F x = deriv (fun s : ℝ => cktA G s k F x) t :=
  (tvdP_hasDerivAt (I := I) (M := M) hLC hflow ht k F hF x).deriv.symm

/-- **Value dependence of the packed reaction tower.** -/
theorem tvdP_val_dep
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (x : M)
    (F F' : Fin (k + 3) → TF (I := I) (M := M))
    (hF : ∀ s, SmE I M (F s)) (hF' : ∀ s, SmE I M (F' s))
    (h : ∀ s, F s x = F' s x) :
    tvdP G t k F x = tvdP G t k F' x := by
  rw [tvdP_eq_deriv (I := I) (M := M) hLC hflow ht k F hF x,
    tvdP_eq_deriv (I := I) (M := M) hLC hflow ht k F' hF' x]
  congr 1
  funext s
  exact Work.Diff.EXT.ka_val_dep_all (I := I) (M := M) hLC G s k x hF hF' h

/-- **Slot linearity of the packed reaction tower** on smooth fields (Clairaut in `t` applied to the
slot linearity of the packed `aOf`-tower, which holds at every time). -/
theorem tvdP_slotLin
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (F : Fin (k + 3) → TF (I := I) (M := M))
    (hF : ∀ s, SmE I M (F s)) (s : Fin (k + 3))
    {X₁ X₂ : TF (I := I) (M := M)} (hX₁ : SmE I M X₁) (hX₂ : SmE I M X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) (x : M) :
    tvdP G t k (Function.update F s (f₁ • X₁ + f₂ • X₂)) x
      = f₁ x * tvdP G t k (Function.update F s X₁) x
        + f₂ x * tvdP G t k (Function.update F s X₂) x := by
  have hXc : SmE I M (f₁ • X₁ + f₂ • X₂) :=
    (ContMDiff.smul_section hf₁ hX₁).add_section (ContMDiff.smul_section hf₂ hX₂)
  have h1 := tvdP_hasDerivAt (I := I) (M := M) hLC hflow ht k
    (Function.update F s (f₁ • X₁ + f₂ • X₂)) (smE_update hF hXc) x
  have h2 := tvdP_hasDerivAt (I := I) (M := M) hLC hflow ht k
    (Function.update F s X₁) (smE_update hF hX₁) x
  have h3 := tvdP_hasDerivAt (I := I) (M := M) hLC hflow ht k
    (Function.update F s X₂) (smE_update hF hX₂) x
  have hsum : HasDerivAt (fun u : ℝ => f₁ x * cktA G u k (Function.update F s X₁) x
      + f₂ x * cktA G u k (Function.update F s X₂) x)
      (f₁ x * tvdP G t k (Function.update F s X₁) x
        + f₂ x * tvdP G t k (Function.update F s X₂) x) t :=
    (h2.const_mul (f₁ x)).add (h3.const_mul (f₂ x))
  have heq : (fun u : ℝ => cktA G u k (Function.update F s (f₁ • X₁ + f₂ • X₂)) x)
      = fun u : ℝ => f₁ x * cktA G u k (Function.update F s X₁) x
        + f₂ x * cktA G u k (Function.update F s X₂) x := by
    funext u
    have h := congrFun ((Work.Diff.EXT.ka_all (I := I) (M := M) hLC G u k F hF).2.1
      s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂) x
    simpa only [Pi.add_apply, smul_eq_mul, Pi.mul_apply] using h
  exact h1.unique (hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun u => congrFun heq u)))

/-! ## The value functional of the packed reaction tower

`cktA G t k F : M → ℝ` is the *scalar-valued* packed recursion, so the reaction tower is a
`(k+3)`-fold linear functional on the tangent space at a point: this is the form in which the
metric-norm bound of the target is obtained from a bound of the values on a *basis*.
-/

/-- **The value functional of the reaction tower** at `x`: the packed tower evaluated on the
`Classical.epsilon`-chosen smooth extensions `smoothExt x ·`. -/
noncomputable def tvdVal (G : ℝ → SMet I M) (t : ℝ) (k : ℕ) (x : M) :
    (Fin (k + 3) → TangentSpace I x) → ℝ :=
  fun u => tvdP G t k (fun s => Submission.Diff.smoothExt x (u s)) x

/-- `tvdVal` at `u` equals `tvdP` at any smooth tuple with the same values at `x`. -/
theorem tvdVal_eq_tvdP
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (x : M)
    (u : Fin (k + 3) → TangentSpace I x) (F : Fin (k + 3) → TF (I := I) (M := M))
    (hF : ∀ s, SmE I M (F s)) (h : ∀ s, F s x = u s) :
    tvdVal G t k x u = tvdP G t k F x :=
  tvdP_val_dep (I := I) (M := M) hLC hflow ht k x _ F
    (fun s => Work.Diff.GE.smoothExt_cmdiff x (u s)) hF
    (fun s => by rw [Work.Diff.GE.smoothExt_apply]; exact (h s).symm)

/-- **The packing of the arguments of the reaction tower**: `k` direction vectors followed by the
three value vectors. -/
def uOf {k : ℕ} {x : M} (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    Fin (k + 3) → TangentSpace I x :=
  Fin.addCases (motive := fun _ => TangentSpace I x) v ![a, b, c]

theorem uOf_castAdd {k : ℕ} {x : M} (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x)
    (i : Fin k) : uOf v a b c (Fin.castAdd 3 i) = v i := Fin.addCases_left i

theorem uOf_natAdd {k : ℕ} {x : M} (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x)
    (p : Fin 3) : uOf v a b c (Fin.natAdd k p) = ![a, b, c] p := Fin.addCases_right p

theorem uOf_natAdd_zero {k : ℕ} {x : M} (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    uOf v a b c (Fin.natAdd k 0) = a := by
  rw [uOf_natAdd]; rfl

theorem uOf_natAdd_one {k : ℕ} {x : M} (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    uOf v a b c (Fin.natAdd k 1) = b := by
  rw [uOf_natAdd]; rfl

theorem uOf_natAdd_two {k : ℕ} {x : M} (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    uOf v a b c (Fin.natAdd k 2) = c := by
  rw [uOf_natAdd]; rfl

/-- **The value functional on the packed arguments is the tower of the target.** -/
theorem tvdVal_uOf [T2Space M] {k : ℕ} (G : ℝ → SMet I M) (t : ℝ) (x : M)
    (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x) :
    tvdVal G t k x (uOf v a b c)
      = tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
          (fun i => Submission.Diff.smoothExt x (v i)) (Submission.Diff.smoothExt x a)
          (Submission.Diff.smoothExt x b) (Submission.Diff.smoothExt x c) x := by
  simp only [tvdVal, tvdP, uOf_castAdd, uOf_natAdd_zero, uOf_natAdd_one, uOf_natAdd_two]

/-- **Slot linearity of the value functional of the reaction tower.** -/
theorem tvdVal_slotLin
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (x : M)
    (u : Fin (k + 3) → TangentSpace I x) (s : Fin (k + 3)) (p q : TangentSpace I x)
    (α β : ℝ) :
    tvdVal G t k x (Function.update u s (α • p + β • q))
      = α * tvdVal G t k x (Function.update u s p)
        + β * tvdVal G t k x (Function.update u s q) := by
  have hXp : SmE I M (Submission.Diff.smoothExt x p) := Work.Diff.GE.smoothExt_cmdiff x p
  have hXq : SmE I M (Submission.Diff.smoothExt x q) := Work.Diff.GE.smoothExt_cmdiff x q
  have hα : CMDiff ∞ (fun _ : M => α) := contMDiff_const
  have hβ : CMDiff ∞ (fun _ : M => β) := contMDiff_const
  have hcomb : SmE I M ((fun _ : M => α) • Submission.Diff.smoothExt x p
      + (fun _ : M => β) • Submission.Diff.smoothExt x q) :=
    (hα.smul_section hXp).add_section (hβ.smul_section hXq)
  -- (i) value dependence in the updated slot
  have e1 : tvdVal G t k x (Function.update u s (α • p + β • q))
      = tvdP G t k (Function.update (fun s' => Submission.Diff.smoothExt x (u s')) s
          ((fun _ : M => α) • Submission.Diff.smoothExt x p
            + (fun _ : M => β) • Submission.Diff.smoothExt x q)) x := by
    refine tvdVal_eq_tvdP (I := I) (M := M) hLC hflow ht k x _ _ ?_ ?_
    · intro s'
      rcases eq_or_ne s' s with h | h
      · subst h; rw [Function.update_self]; exact hcomb
      · rw [Function.update_of_ne h]; exact Work.Diff.GE.smoothExt_cmdiff x (u s')
    · intro s'
      rcases eq_or_ne s' s with h | h
      · subst h
        rw [Function.update_self, Function.update_self]
        simp only [Pi.add_apply, Pi.smul_apply', Work.Diff.GE.smoothExt_apply]
      · rw [Function.update_of_ne h, Function.update_of_ne h, Work.Diff.GE.smoothExt_apply]
  -- (ii) slot linearity of the packed tower
  have hlin := tvdP_slotLin (I := I) (M := M) hLC hflow ht k
    (fun s' => Submission.Diff.smoothExt x (u s'))
    (fun s' => Work.Diff.GE.smoothExt_cmdiff x (u s')) s hXp hXq hα hβ x
  -- (iii) the two value-dependences back
  have e2 : tvdP G t k (Function.update (fun s' => Submission.Diff.smoothExt x (u s')) s
        (Submission.Diff.smoothExt x p)) x = tvdVal G t k x (Function.update u s p) := by
    refine (tvdVal_eq_tvdP (I := I) (M := M) hLC hflow ht k x (Function.update u s p) _ ?_ ?_).symm
    · intro s'
      rcases eq_or_ne s' s with h | h
      · subst h; rw [Function.update_self]; exact hXp
      · rw [Function.update_of_ne h]; exact Work.Diff.GE.smoothExt_cmdiff x (u s')
    · intro s'
      rcases eq_or_ne s' s with h | h
      · subst h
        rw [Function.update_self, Function.update_self]
        simp only [Work.Diff.GE.smoothExt_apply]
      · rw [Function.update_of_ne h, Function.update_of_ne h, Work.Diff.GE.smoothExt_apply]
  have e3 : tvdP G t k (Function.update (fun s' => Submission.Diff.smoothExt x (u s')) s
        (Submission.Diff.smoothExt x q)) x = tvdVal G t k x (Function.update u s q) := by
    refine (tvdVal_eq_tvdP (I := I) (M := M) hLC hflow ht k x (Function.update u s q) _ ?_ ?_).symm
    · intro s'
      rcases eq_or_ne s' s with h | h
      · subst h; rw [Function.update_self]; exact hXq
      · rw [Function.update_of_ne h]; exact Work.Diff.GE.smoothExt_cmdiff x (u s')
    · intro s'
      rcases eq_or_ne s' s with h | h
      · subst h
        rw [Function.update_self, Function.update_self]
        simp only [Work.Diff.GE.smoothExt_apply]
      · rw [Function.update_of_ne h, Function.update_of_ne h, Work.Diff.GE.smoothExt_apply]
  rw [e1, hlin, e2, e3]

/-- **The coordinate-frame tower equals the value-functional tower** (at the chart coordinate of
the base point).  Both are the reaction tower evaluated on fields with the same values at the base
point; the transfer is germ-locality plus value dependence. -/
theorem cFrame_tower_eq_smoothExt
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v : Fin k → Fin (Module.finrank ℝ E))
    (i j l : Fin (Module.finrank ℝ E)) :
    tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
        (fun s => Work.Diff.GE.cFrame (I := I) x₀ (v s)) (Work.Diff.GE.cFrame (I := I) x₀ i)
        (Work.Diff.GE.cFrame (I := I) x₀ j) (Work.Diff.GE.cFrame (I := I) x₀ l)
        (Work.Diff.EXT.pt (I := I) x₀ y)
      = tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
        (fun s => Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))
        (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
        (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)))
        (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y)))
        (Work.Diff.EXT.pt (I := I) x₀ y) := by
  have hpsrc : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source := by
      have hmem : (extChartAt I x₀).symm y ∈
          (extChartAt I x₀).symm '' (extChartAt I x₀).target := Set.mem_image_of_mem _ hy
      rwa [PartialEquiv.symm_image_target_eq_source] at hmem
    have h2 : (extChartAt I x₀).source = (chartAt H x₀).source := extChartAt_source I x₀
    show (extChartAt I x₀).symm y ∈ (chartAt H x₀).source
    rw [← h2]
    exact h1
  have hYex : ∀ a : Fin (Module.finrank ℝ E), ∃ Z : Π y : M, TangentSpace I y,
      SmE I M Z ∧ Z =ᶠ[𝓝 (Work.Diff.EXT.pt (I := I) x₀ y)]
        Work.Diff.GE.cFrame (I := I) x₀ a := by
    intro a
    obtain ⟨Z, hZsm, hZeq⟩ := Work.Diff.T.exists_global_eventuallyEq_symmL (I := I) x₀
      (Work.Diff.GE.cBasis (E := E) a) hpsrc
    exact ⟨Z, hZsm, hZeq⟩
  choose Z hZsm hZeq using hYex
  have hZval : ∀ a, Z a (Work.Diff.EXT.pt (I := I) x₀ y) =
      Work.Diff.GE.cFrame (I := I) x₀ a (Work.Diff.EXT.pt (I := I) x₀ y) :=
    fun a => (hZeq a).eq_of_nhds
  -- germ-locality
  have e1 : tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
        (fun s => Work.Diff.GE.cFrame (I := I) x₀ (v s)) (Work.Diff.GE.cFrame (I := I) x₀ i)
        (Work.Diff.GE.cFrame (I := I) x₀ j) (Work.Diff.GE.cFrame (I := I) x₀ l)
        (Work.Diff.EXT.pt (I := I) x₀ y)
      = tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
        (fun s => Z (v s)) (Z i) (Z j) (Z l) (Work.Diff.EXT.pt (I := I) x₀ y) :=
    tower_dAOfBase_congr_germ (I := I) (M := M) G t k
      (fun s => Work.Diff.GE.cFrame (I := I) x₀ (v s)) (fun s => Z (v s))
      (Work.Diff.GE.cFrame (I := I) x₀ i) (Z i)
      (Work.Diff.GE.cFrame (I := I) x₀ j) (Z j)
      (Work.Diff.GE.cFrame (I := I) x₀ l) (Z l) (Work.Diff.EXT.pt (I := I) x₀ y)
      (fun s => (hZeq (v s)).symm) ((hZeq i).symm) ((hZeq j).symm) ((hZeq l).symm)
  -- value dependence
  have e2 : tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
        (fun s => Z (v s)) (Z i) (Z j) (Z l) (Work.Diff.EXT.pt (I := I) x₀ y)
      = tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
        (fun s => Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
          (Z (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))
        (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
          (Z i (Work.Diff.EXT.pt (I := I) x₀ y)))
        (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
          (Z j (Work.Diff.EXT.pt (I := I) x₀ y)))
        (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
          (Z l (Work.Diff.EXT.pt (I := I) x₀ y)))
        (Work.Diff.EXT.pt (I := I) x₀ y) :=
    dAOf_tower_val_dep (I := I) (M := M) hLC hflow ht k (Work.Diff.EXT.pt (I := I) x₀ y)
      (fun s => Z (v s))
      (fun s => Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Z (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))
      (Z i) (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Z i (Work.Diff.EXT.pt (I := I) x₀ y)))
      (Z j) (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Z j (Work.Diff.EXT.pt (I := I) x₀ y)))
      (Z l) (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
        (Z l (Work.Diff.EXT.pt (I := I) x₀ y)))
      (fun s => hZsm (v s)) (fun s => Work.Diff.GE.smoothExt_cmdiff _ _)
      (hZsm i) (Work.Diff.GE.smoothExt_cmdiff _ _) (hZsm j) (Work.Diff.GE.smoothExt_cmdiff _ _)
      (hZsm l) (Work.Diff.GE.smoothExt_cmdiff _ _)
      (fun s => (Work.Diff.GE.smoothExt_apply _ _).symm) (Work.Diff.GE.smoothExt_apply _ _).symm
      (Work.Diff.GE.smoothExt_apply _ _).symm (Work.Diff.GE.smoothExt_apply _ _).symm
  rw [e1, e2]
  simp only [hZval]

/-- **A finite cover by chart balls, keeping the chart-source condition.**  On a compact charted
space there are finitely many centres `x₀ i` and radii `r i > 0` with the closed coordinate balls
inside the chart targets, such that the sets
`(chartAt H (x₀ i)).source ∩ (extChartAt I (x₀ i)) ⁻¹' ball ((extChartAt I (x₀ i)) (x₀ i)) (r i)`
cover `M`.  (The chart-source condition is what makes the chart coordinate of a cover point
invertible, `pt (x₀ i) (extChartAt I (x₀ i) x) = x`.) -/
theorem exists_chart_ball_cover_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [CompactSpace M] [T2Space M] [I.Boundaryless] :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (x₀ : ι₀ → M) (r : ι₀ → ℝ),
      (∀ i, 0 < r i) ∧
      (∀ i, Metric.closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r i)
        ⊆ (extChartAt I (x₀ i)).target) ∧
      (⋃ i, (chartAt H (x₀ i)).source ∩
        (extChartAt I (x₀ i)) ⁻¹' Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i)) = Set.univ := by
  classical
  have hrad : ∀ x : M, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall ((extChartAt I x) x) ρ ⊆ (extChartAt I x).target := by
    intro x
    have hmem : (extChartAt I x) x ∈ (extChartAt I x).target := mem_extChartAt_target x
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target x).mem_nhds hmem)
    exact ⟨ε / 2, by linarith,
      fun y hy => hsub (Metric.closedBall_subset_ball (by linarith) hy)⟩
  choose r hrpos hrsub using hrad
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt H x).source ∩
      (extChartAt I x) ⁻¹' Metric.ball ((extChartAt I x) x) (r x))
    (fun x => isOpen_extChartAt_preimage x Metric.isOpen_ball)
    (fun y _ => Set.mem_iUnion.mpr
      ⟨y, mem_chart_source H y, Metric.mem_ball_self (hrpos y)⟩)
  let x₀ : Fin t.card → M := fun i => ((t.equivFin.symm i : {x // x ∈ t}) : M)
  let r₀ : Fin t.card → ℝ := fun i => r (x₀ i)
  refine ⟨Fin t.card, inferInstance, x₀, r₀, ?_, ?_, ?_⟩
  · intro i; exact hrpos _
  · intro i
    show Metric.closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r (x₀ i)) ⊆ _
    exact hrsub _
  · refine Set.eq_univ_iff_forall.mpr (fun y => ?_)
    rw [Set.mem_iUnion]
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    have hxx : x₀ (t.equivFin ⟨x, hx⟩) = x := by
      simp only [x₀]
      rw [Equiv.symm_apply_apply]
    have hr₀ : r₀ (t.equivFin ⟨x, hx⟩) = r x := by simp only [r₀, hxx]
    rw [hxx, hr₀]
    exact hyx

/-- The coordinates of a tangent vector in the chart frame of the chart at `x₀` (given by the
tangent-bundle trivialisation at `x₀`). -/
noncomputable def frameCoef (x₀ x : M) (w : TangentSpace I x) : Fin (Module.finrank ℝ E) → ℝ :=
  (Module.finBasis ℝ E).repr
    ((FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x w)

/-- The chart frame expands a tangent vector with its `frameCoef` coefficients. -/
theorem sum_frameCoef_smul_cFrame (x₀ x : M) (hx : x ∈ (chartAt H x₀).source)
    (w : TangentSpace I x) :
    Finset.sum Finset.univ
      (fun p => frameCoef x₀ x w p • Work.Diff.GE.cFrame (I := I) x₀ p x) = w := by
  have hbase : x ∈ (FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hx
  have h1 : Finset.sum Finset.univ
        (fun p => frameCoef x₀ x w p • Work.Diff.GE.cFrame (I := I) x₀ p x)
      = Finset.sum Finset.univ (fun p => frameCoef x₀ x w p •
          (FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x
            (Work.Diff.GE.cBasis (E := E) p)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rfl
  rw [h1]
  have h2 : Finset.sum Finset.univ (fun p => frameCoef x₀ x w p •
        (FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x
          (Work.Diff.GE.cBasis (E := E) p))
      = Finset.sum Finset.univ (fun p =>
          (FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x
            (frameCoef x₀ x w p • Work.Diff.GE.cBasis (E := E) p)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [map_smul]
  rw [h2, ← map_sum]
  have h3 : Finset.sum Finset.univ
        (fun p => frameCoef x₀ x w p • Work.Diff.GE.cBasis (E := E) p)
      = (FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x w := by
    rw [frameCoef]
    exact Module.Basis.sum_repr _ _
  rw [h3]
  exact Trivialization.symmL_continuousLinearMapAt _ (R := ℝ) hbase w

end Work.Diff.EXT.ConnCov
