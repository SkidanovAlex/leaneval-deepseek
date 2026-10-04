import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestTower
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.RicTr.baseRic_sm

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The structural properties of the honest Ricci tower `RicT g i`

`Work.Diff.EXT.ConnCov.RicFlip.RicT g i = pDiter2 (lcOf g) (ric2 g) i : AMB.Fam (i+2)` is the
`i`-th covariant derivative of the `(0,2)`-tensor `Ric`, written in the *packed* convention of
`Work.Diff.EXT.ConnCov.AMB`.  This file establishes the three structural facts about it that the
two-connection flip needs:

1. **Slot additivity** (`AMB.SlotAddP`): `RicT g i` is additive in every one of its `i+2` slots, on
   smooth fields.  This is what makes the flip identity `pD_flip_full` applicable.
2. **Smoothness** (`AMB.SmP`): `RicT g i` sends tuples of smooth fields to smooth functions.
3. **The bridge to the curried honest tower**:
   `AMB.pack (htower (lcOf g) (baseRic g) i) F = RicT g i (F ∘ Fin.castSucc)` for every tuple
   `F : Fin (i+3) → TF`.  The statement ignores the last slot of `F` (the honest tower of `baseRic`
   is independent of its third value slot), so it says that `RicT g i` is exactly the packed honest
   tower with the dummy slot dropped.

## The proof of (1) and (2)

`RicT g ·` is the `pD`-iteration of `ric2 g`, so it suffices to know that `pD cov` preserves the
conjunction `AMB.SlotAddP ∧ AMB.SmP`:

* the base case `ric2 g` is bilinearity and smoothness of the pointwise Ricci tensor
  (`Work.Diff.EXT.ricAt_add_middle_L`, `Work.Diff.EXT.ricAt_add_last_L` and
  `Work.Diff.EXT.ConnCov.RicTr.baseRic_sm`);
* for the step, `pD cov τ F = mvfderiv I (τ (F ∘ Fin.succ)) x (F 0 x) − ∑_j τ (update … j …) x`, so
  additivity in the leading (direction) slot is the additivity of `mvfderiv` in its direction
  together with the linearity of the connection in the section (`pD_add_zero`), while additivity in
  a slot `i.succ` needs `AMB.SlotAddP τ` at slot `i` and `mvfderiv_add` on the differentiable
  functions `τ (update … i …)` (`pD_add_succ`).  Smoothness (`pD_smP`) is
  `Work.Diff.C.mvfderiv_contMDiffAt` plus the smoothness of the connection
  (`Work.Diff.EXT.ATower.lcOf_apply_smE`).

## The proof of (3)

The packed recursion `AMB.pD` and the curried recursion `Work.Diff.EXT.ATower.step` are intertwined
by `AMB.pack` (`AMB.pack_step_apply`), and the honest recursion is `hstep = step + drop`.  Writing
`drop τ` for the operator which discards the head direction slot, one has the *slot-shift* identity

  `AMB.pack (drop τ) F = AMB.pack τ (F ∘ Fin.succ)`

(the correction that `pD` pays for the dummy `C`-slot is exactly the `drop` term).  Hence
`AMB.pack (hstep cov τ) F = AMB.pD cov (AMB.pack τ) F + AMB.pack τ (F ∘ Fin.succ)`, and (3) follows
by induction from the identity

  `AMB.pD cov (lift T) F = lift (AMB.pD cov T) F − lift T (F ∘ Fin.succ)`

for the lift `lift T F = T (F ∘ Fin.castSucc)` of a packed object to one more slot: the induction
step reads `pack (htower (i+1)) = pack (hstep (htower i)) = pD (lift (RicT g i)) + lift (RicT g i) ∘
shift = lift (RicT g (i+1))`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ConnCov.AMB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## The slot-wise lift of a packed object -/

/-- The lift of a packed object with `N` slots to one with `N + 1` slots: the tuple is read through
`Fin.castSucc`, i.e. the new (last) slot is ignored. -/
noncomputable def lift {N : ℕ} (T : AMB.Fam (I := I) (M := M) N) :
    AMB.Fam (I := I) (M := M) (N + 1) :=
  fun F => T (fun l : Fin N => F (Fin.castSucc l))

@[simp] lemma lift_apply {N : ℕ} (T : AMB.Fam (I := I) (M := M) N)
    (F : Fin (N + 1) → AMB.TF (I := I) (M := M)) (x : M) :
    lift T F x = T (fun l : Fin N => F (Fin.castSucc l)) x := rfl

/-! ## `drop` under `AMB.pack` -/

/-- **The slot-shift identity for `drop`**: packing `drop τ` and applying it to `F` is the same as
packing `τ` and applying it to `F ∘ Fin.succ`. -/
theorem pack_drop {k : ℕ} (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k)
    (F : Fin (k + 4) → AMB.TF (I := I) (M := M)) :
    AMB.pack (Work.Diff.EXT.ConnCov.drop τ) F
      = AMB.pack τ (fun j : Fin (k + 3) => F j.succ) := by
  funext x
  simp only [AMB.pack_apply, Work.Diff.EXT.ConnCov.drop, AMB.succ_castAdd_three,
    AMB.succ_natAdd_three]

/-- **The packed form of the honest recursion step.**  One `hstep` of a curried operator is one
`pD` of the packed operator plus the `drop` correction, which is the evaluation of the packed
operator on the shifted tuple. -/
theorem pack_hstep (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k)
    (F : Fin (k + 4) → AMB.TF (I := I) (M := M)) :
    AMB.pack (Work.Diff.EXT.ConnCov.hstep cov τ) F
      = AMB.pD cov (AMB.pack τ) F + AMB.pack τ (fun j : Fin (k + 3) => F j.succ) := by
  funext x
  have h1 : AMB.pack (Work.Diff.EXT.ConnCov.hstep cov τ) F x
      = AMB.pack (Work.Diff.EXT.ATower.step cov τ) F x
        + AMB.pack (Work.Diff.EXT.ConnCov.drop τ) F x := by
    simp only [Work.Diff.EXT.ConnCov.hstep, AMB.pack_apply, Pi.add_apply]
  rw [h1, AMB.pack_step_apply cov τ F x, pack_drop τ F, Pi.add_apply]

/-! ## The base of the `pD`-iteration: `ric2 g` -/

/-- **Slot additivity of `ric2 g`**: the pointwise Ricci tensor is bilinear. -/
theorem ric2_slotAddP (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    AMB.SlotAddP (ric2 g) := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞) :=
    (hLC g).1.some
  intro j H W W' hH hW hW' x
  fin_cases j
  · have h0 : (Function.update H 0 (W + W')) 0 = W + W' := Function.update_self 0 (W + W') H
    have h1 : (Function.update H 0 (W + W')) 1 = H 1 :=
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0) _ _
    have k0 : (Function.update H 0 W) 0 = W := Function.update_self 0 W H
    have k1 : (Function.update H 0 W) 1 = H 1 :=
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0) _ _
    have l0 : (Function.update H 0 W') 0 = W' := Function.update_self 0 W' H
    have l1 : (Function.update H 0 W') 1 = H 1 :=
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0) _ _
    simp only [ric2, h0, h1, k0, k1, l0, l1, Pi.add_apply]
    exact Work.Diff.EXT.ricAt_add_middle_L g hcov x (W x) (W' x) (H 1 x)
  · have h0 : (Function.update H 1 (W + W')) 0 = H 0 :=
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1) _ _
    have h1 : (Function.update H 1 (W + W')) 1 = W + W' := Function.update_self 1 (W + W') H
    have k0 : (Function.update H 1 W) 0 = H 0 :=
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1) _ _
    have k1 : (Function.update H 1 W) 1 = W := Function.update_self 1 W H
    have l0 : (Function.update H 1 W') 0 = H 0 :=
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1) _ _
    have l1 : (Function.update H 1 W') 1 = W' := Function.update_self 1 W' H
    simp only [ric2, h0, h1, k0, k1, l0, l1, Pi.add_apply]
    exact Work.Diff.EXT.ricAt_add_last_L g hcov x (H 0 x) (W x) (W' x)

/-- **Smoothness of `ric2 g`** on smooth tuples: the pointwise Ricci tensor of a smooth metric is
smooth on smooth fields. -/
theorem ric2_smP (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    AMB.SmP (ric2 g) := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞) :=
    (hLC g).1.some
  intro H hH
  have h := Work.Diff.EXT.ConnCov.RicTr.baseRic_sm (I := I) (M := M) g hcov (H 0) (H 1) (H 0)
    (hH 0) (hH 1) (hH 0)
  have h' : Work.Diff.EXT.ATower.SmF I M
      (fun y => ricAt (Submission.Diff.lcOf g) y (H 0 y) (H 1 y)) := h
  exact h'

/-! ## Unfolding `AMB.pD` at an updated slot -/

/-- `AMB.pD` at a tuple whose leading slot has been replaced. -/
theorem pD_update_zero (cov : CovariantDerivative I E (TangentSpace I (M := M))) {N : ℕ}
    (τ : AMB.Fam (I := I) (M := M) N)
    (F : Fin (N + 1) → AMB.TF (I := I) (M := M)) (S : AMB.TF (I := I) (M := M)) :
    AMB.pD cov τ (Function.update F 0 S)
      = fun x => (d% (τ (fun i : Fin N => F i.succ)) x) (S x)
        - ∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
            (fun y => cov ((fun i : Fin N => F i.succ) j) y (S y))) x := by
  funext x
  have hu : ∀ j : Fin N, (Function.update F 0 S) j.succ = F j.succ :=
    fun j => Function.update_of_ne (Fin.succ_ne_zero j) S F
  have h0 : (Function.update F 0 S) 0 = S := Function.update_self 0 S F
  simp only [AMB.pD]
  simp_rw [hu, h0]

/-- `AMB.pD` at a tuple whose slot `i.succ` has been replaced. -/
theorem pD_update_succ (cov : CovariantDerivative I E (TangentSpace I (M := M))) {N : ℕ}
    (τ : AMB.Fam (I := I) (M := M) N)
    (F : Fin (N + 1) → AMB.TF (I := I) (M := M)) (i : Fin N) (S : AMB.TF (I := I) (M := M)) :
    AMB.pD cov τ (Function.update F i.succ S)
      = fun x => (d% (τ (Function.update (fun j : Fin N => F j.succ) i S)) x) (F 0 x)
        - ∑ j : Fin N, τ (Function.update (Function.update (fun k : Fin N => F k.succ) i S) j
            (fun y => cov ((Function.update (fun k : Fin N => F k.succ) i S) j) y (F 0 y))) x := by
  funext x
  have hu : ∀ j : Fin N, (Function.update F i.succ S) j.succ
      = Function.update (fun k : Fin N => F k.succ) i S j := by
    intro j
    simp only [Function.update_apply, Fin.succ_inj]
  have h0 : (Function.update F i.succ S) 0 = F 0 :=
    Function.update_of_ne (Fin.succ_ne_zero i).symm S F
  simp only [AMB.pD]
  simp_rw [hu, h0]

/-! ## `AMB.pD` preserves smoothness -/

/-- **`AMB.pD` preserves smoothness.**  Both summands of

  `pD cov τ F x = mvfderiv I (τ (F ∘ Fin.succ)) x (F 0 x) − ∑_j τ (update … j …) x`

are smooth when `τ` is smooth on smooth tuples and `cov = lcOf g` is the Levi-Civita connection of
a smooth metric. -/
theorem pD_smP (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) {N : ℕ}
    {τ : AMB.Fam (I := I) (M := M) N} (hsm : AMB.SmP τ) :
    AMB.SmP (AMB.pD (Submission.Diff.lcOf g) τ) := by
  intro F hF x
  have hlc : ∀ (Y Z : AMB.TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => Submission.Diff.lcOf g Y y (Z y)) :=
    fun Y Z hY hZ => Work.Diff.EXT.ATower.lcOf_apply_smE hLC g Y Z hY hZ
  have h1 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun y => (d% (τ (fun j : Fin N => F j.succ)) y) (F 0 y)) x :=
    Work.Diff.C.mvfderiv_contMDiffAt (hsm _ (fun j => hF _) x) (hF 0 x)
  have h2 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun y => ∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
        (fun z => Submission.Diff.lcOf g (F j.succ) z (F 0 z))) y) x := by
    refine ContMDiffAt.sum (fun j _ => ?_)
    refine hsm _ (fun k => ?_) x
    by_cases hkj : k = j
    · rw [hkj, Function.update_self]
      exact hlc (F j.succ) (F 0) (hF _) (hF 0)
    · rw [Function.update_of_ne hkj]; exact hF _
  have hgoal : AMB.pD (Submission.Diff.lcOf g) τ F = fun y =>
      (d% (τ (fun j : Fin N => F j.succ)) y) (F 0 y)
        - ∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
            (fun z => Submission.Diff.lcOf g (F j.succ) z (F 0 z))) y := rfl
  rw [hgoal]
  exact h1.sub h2

/-! ## `AMB.pD` preserves slot additivity -/

/-- **Additivity of `AMB.pD` in the leading (direction) slot.**  The direction enters only through
the continuous linear map `mvfderiv I (τ (F ∘ Fin.succ)) x` and, linearly, in the section argument
of the connection corrections. -/
theorem pD_add_zero (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) {N : ℕ}
    {τ : AMB.Fam (I := I) (M := M) N}
    (hadd : AMB.SlotAddP τ) (hsm : AMB.SmP τ)
    (F : Fin (N + 1) → AMB.TF (I := I) (M := M))
    (hF : ∀ j, Work.Diff.EXT.ATower.SmE I M (F j))
    (W W' : AMB.TF (I := I) (M := M))
    (hW : Work.Diff.EXT.ATower.SmE I M W) (hW' : Work.Diff.EXT.ATower.SmE I M W') (x : M) :
    AMB.pD (Submission.Diff.lcOf g) τ (Function.update F 0 (W + W')) x
      = AMB.pD (Submission.Diff.lcOf g) τ (Function.update F 0 W) x
        + AMB.pD (Submission.Diff.lcOf g) τ (Function.update F 0 W') x := by
  have e1 := pD_update_zero (cov := Submission.Diff.lcOf g) τ F (W + W')
  have e2 := pD_update_zero (cov := Submission.Diff.lcOf g) τ F W
  have e3 := pD_update_zero (cov := Submission.Diff.lcOf g) τ F W'
  have hmv : (d% (τ (fun i : Fin N => F i.succ)) x) (W x + W' x)
      = (d% (τ (fun i : Fin N => F i.succ)) x) (W x)
        + (d% (τ (fun i : Fin N => F i.succ)) x) (W' x) :=
    map_add _ _ _
  have hsum : (∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
        (fun y => Submission.Diff.lcOf g ((fun i : Fin N => F i.succ) j) y (W y + W' y))) x)
      = (∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
            (fun y => Submission.Diff.lcOf g ((fun i : Fin N => F i.succ) j) y (W y))) x)
        + (∑ j : Fin N, τ (Function.update (fun i : Fin N => F i.succ) j
            (fun y => Submission.Diff.lcOf g ((fun i : Fin N => F i.succ) j) y (W' y))) x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfield : (fun y : M => Submission.Diff.lcOf g ((fun i : Fin N => F i.succ) j) y
          (W y + W' y))
        = (fun y : M => Submission.Diff.lcOf g ((fun i : Fin N => F i.succ) j) y (W y))
          + (fun y : M => Submission.Diff.lcOf g ((fun i : Fin N => F i.succ) j) y (W' y)) := by
      funext y
      exact map_add _ _ _
    rw [hfield]
    exact hadd j (fun i : Fin N => F i.succ)
      (fun y => Submission.Diff.lcOf g ((fun i : Fin N => F i.succ) j) y (W y))
      (fun y => Submission.Diff.lcOf g ((fun i : Fin N => F i.succ) j) y (W' y))
      (fun i => hF i.succ)
      (Work.Diff.EXT.ATower.lcOf_apply_smE hLC g _ _ (hF j.succ) hW)
      (Work.Diff.EXT.ATower.lcOf_apply_smE hLC g _ _ (hF j.succ) hW') x
  simp only [e1, e2, e3, Pi.add_apply]
  rw [hmv, hsum]
  ring

/-- **Additivity of `AMB.pD` in a slot `i.succ`.**  The slot is a value slot of `τ`, so this needs
`AMB.SlotAddP τ` at slot `i` (together with the differentiability of `τ` on the updated tuples, to
split the `mvfderiv` term). -/
theorem pD_add_succ (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) {N : ℕ}
    {τ : AMB.Fam (I := I) (M := M) N}
    (hadd : AMB.SlotAddP τ) (hsm : AMB.SmP τ)
    (F : Fin (N + 1) → AMB.TF (I := I) (M := M))
    (hF : ∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) (i : Fin N)
    (W W' : AMB.TF (I := I) (M := M))
    (hW : Work.Diff.EXT.ATower.SmE I M W) (hW' : Work.Diff.EXT.ATower.SmE I M W') (x : M) :
    AMB.pD (Submission.Diff.lcOf g) τ (Function.update F i.succ (W + W')) x
      = AMB.pD (Submission.Diff.lcOf g) τ (Function.update F i.succ W) x
        + AMB.pD (Submission.Diff.lcOf g) τ (Function.update F i.succ W') x := by
  let H : Fin N → AMB.TF (I := I) (M := M) := fun j => F j.succ
  have hHs : ∀ j : Fin N, Work.Diff.EXT.ATower.SmE I M (H j) := fun j => hF j.succ
  have hcov : ∀ (Y Z : AMB.TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => Submission.Diff.lcOf g Y y (Z y)) :=
    fun Y Z hY hZ => Work.Diff.EXT.ATower.lcOf_apply_smE hLC g Y Z hY hZ
  have hupd : ∀ (S : AMB.TF (I := I) (M := M)), Work.Diff.EXT.ATower.SmE I M S →
      ∀ j, Work.Diff.EXT.ATower.SmE I M (Function.update H i S j) := by
    intro S hS j
    by_cases hji : j = i
    · rw [hji, Function.update_self]; exact hS
    · rw [Function.update_of_ne hji]; exact hHs j
  have e1 : AMB.pD (Submission.Diff.lcOf g) τ (Function.update F i.succ (W + W'))
      = fun x => (d% (τ (Function.update H i (W + W'))) x) (F 0 x)
        - ∑ j : Fin N, τ (Function.update (Function.update H i (W + W')) j
            (fun y => Submission.Diff.lcOf g ((Function.update H i (W + W')) j) y (F 0 y))) x :=
    pD_update_succ (Submission.Diff.lcOf g) τ F i (W + W')
  have e2 : AMB.pD (Submission.Diff.lcOf g) τ (Function.update F i.succ W)
      = fun x => (d% (τ (Function.update H i W)) x) (F 0 x)
        - ∑ j : Fin N, τ (Function.update (Function.update H i W) j
            (fun y => Submission.Diff.lcOf g ((Function.update H i W) j) y (F 0 y))) x :=
    pD_update_succ (Submission.Diff.lcOf g) τ F i W
  have e3 : AMB.pD (Submission.Diff.lcOf g) τ (Function.update F i.succ W')
      = fun x => (d% (τ (Function.update H i W')) x) (F 0 x)
        - ∑ j : Fin N, τ (Function.update (Function.update H i W') j
            (fun y => Submission.Diff.lcOf g ((Function.update H i W') j) y (F 0 y))) x :=
    pD_update_succ (Submission.Diff.lcOf g) τ F i W'
  have hmv : (d% (τ (Function.update H i (W + W'))) x) (F 0 x)
      = (d% (τ (Function.update H i W)) x) (F 0 x)
        + (d% (τ (Function.update H i W')) x) (F 0 x) := by
    have h1f : τ (Function.update H i (W + W'))
        = τ (Function.update H i W) + τ (Function.update H i W') :=
      funext (hadd i H W W' hHs hW hW')
    have hmdW : MDiffAt (τ (Function.update H i W)) x :=
      (hsm _ (hupd W hW) x).mdifferentiableAt (by simp)
    have hmdW' : MDiffAt (τ (Function.update H i W')) x :=
      (hsm _ (hupd W' hW') x).mdifferentiableAt (by simp)
    rw [h1f, mvfderiv_add hmdW hmdW']
    rfl
  have hsum : (∑ j : Fin N, τ (Function.update (Function.update H i (W + W')) j
        (fun y => Submission.Diff.lcOf g ((Function.update H i (W + W')) j) y (F 0 y))) x)
      = (∑ j : Fin N, τ (Function.update (Function.update H i W) j
            (fun y => Submission.Diff.lcOf g ((Function.update H i W) j) y (F 0 y))) x)
        + (∑ j : Fin N, τ (Function.update (Function.update H i W') j
            (fun y => Submission.Diff.lcOf g ((Function.update H i W') j) y (F 0 y))) x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · rw [hji]
      have hZ : ∀ S : AMB.TF (I := I) (M := M),
          (fun y : M => Submission.Diff.lcOf g ((Function.update H i S) i) y (F 0 y))
            = fun y : M => Submission.Diff.lcOf g S y (F 0 y) := by
        intro S; rw [Function.update_self]
      rw [Function.update_idem, Function.update_idem, Function.update_idem]
      rw [hZ (W + W'), hZ W, hZ W']
      have hfield : (fun y : M => Submission.Diff.lcOf g (W + W') y (F 0 y))
          = (fun y : M => Submission.Diff.lcOf g W y (F 0 y))
            + (fun y : M => Submission.Diff.lcOf g W' y (F 0 y)) := by
        funext y
        have hc : Submission.Diff.lcOf g (W + W') y
            = Submission.Diff.lcOf g W y + Submission.Diff.lcOf g W' y :=
          ((Submission.Diff.lcOf g).isCovariantDerivativeOn (s := Set.univ)).add (σ := W) (σ' := W')
            (hW.mdifferentiableAt (by simp)) (hW'.mdifferentiableAt (by simp)) (by simp)
        simp only [Pi.add_apply]
        rw [hc]; rfl
      rw [hfield]
      exact hadd i H (fun y => Submission.Diff.lcOf g W y (F 0 y))
        (fun y => Submission.Diff.lcOf g W' y (F 0 y)) hHs
        (hcov W (F 0) hW (hF 0)) (hcov W' (F 0) hW' (hF 0)) x
    · have hij : i ≠ j := fun h => hji h.symm
      have hSj : ∀ S : AMB.TF (I := I) (M := M), (Function.update H i S) j = H j :=
        fun S => Function.update_of_ne hji S H
      have hupd2 : ∀ l, Work.Diff.EXT.ATower.SmE I M
          ((Function.update H j (fun y : M => Submission.Diff.lcOf g (H j) y (F 0 y))) l) := by
        intro l
        by_cases hlj : l = j
        · rw [hlj, Function.update_self]; exact hcov (H j) (F 0) (hHs j) (hF 0)
        · rw [Function.update_of_ne hlj]; exact hHs l
      have hL : Function.update (Function.update H i (W + W')) j
            (fun y : M => Submission.Diff.lcOf g ((Function.update H i (W + W')) j) y (F 0 y))
          = Function.update
              (Function.update H j (fun y : M => Submission.Diff.lcOf g (H j) y (F 0 y)))
              i (W + W') := by
        rw [hSj (W + W')]
        exact Function.update_comm hij (W + W') _ H
      have hM : Function.update (Function.update H i W) j
            (fun y : M => Submission.Diff.lcOf g ((Function.update H i W) j) y (F 0 y))
          = Function.update
              (Function.update H j (fun y : M => Submission.Diff.lcOf g (H j) y (F 0 y))) i W := by
        rw [hSj W]
        exact Function.update_comm hij W _ H
      have hR : Function.update (Function.update H i W') j
            (fun y : M => Submission.Diff.lcOf g ((Function.update H i W') j) y (F 0 y))
          = Function.update
              (Function.update H j (fun y : M => Submission.Diff.lcOf g (H j) y (F 0 y)))
              i W' := by
        rw [hSj W']
        exact Function.update_comm hij W' _ H
      rw [hL, hM, hR]
      exact hadd i (Function.update H j (fun y : M => Submission.Diff.lcOf g (H j) y (F 0 y)))
        W W' hupd2 hW hW' x
  simp only [e1, e2, e3]
  rw [hmv, hsum]
  ring

/-- **`AMB.pD` preserves slot additivity**: a slot-additive and smooth packed object has slot-additive
`pD`-derivative.  The two cases are the leading (direction) slot (`pD_add_zero`) and the remaining
value slots (`pD_add_succ`). -/
theorem pD_SlotAddP (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) {N : ℕ}
    {τ : AMB.Fam (I := I) (M := M) N} (hadd : AMB.SlotAddP τ) (hsm : AMB.SmP τ) :
    AMB.SlotAddP (AMB.pD (Submission.Diff.lcOf g) τ) := by
  intro j H W W' hH hW hW' x
  rcases Fin.eq_zero_or_eq_succ j with hj | ⟨i, hi⟩
  · rw [hj]
    exact pD_add_zero hLC g hadd hsm H hH W W' hW hW' x
  · rw [hi]
    exact pD_add_succ hLC g hadd hsm H hH i W W' hW hW' x

/-! ## The recursion identity for the lift -/

/-- **The `pD`-identity for the lift.**  Deriving a packed object with respect to one more slot and
then dropping the dummy slot reproduces the tuple of derivatives of the original object: the extra
summand that `pD` pays for the top slot of the lifted tuple is exactly the `drop` correction
evaluated on the shifted tuple. -/
theorem pD_lift (cov : CovariantDerivative I E (TangentSpace I (M := M))) {N : ℕ}
    (T : AMB.Fam (I := I) (M := M) N) (F : Fin (N + 2) → AMB.TF (I := I) (M := M)) :
    AMB.pD cov (lift T) F = lift (AMB.pD cov T) F - lift T (fun l : Fin (N + 1) => F l.succ) := by
  funext x
  let G : Fin N → AMB.TF (I := I) (M := M) := fun l => F (Fin.castSucc l).succ
  have hLsum : (∑ j : Fin (N + 1), (lift T) (Function.update (fun i : Fin (N + 1) => F i.succ) j
        (fun y => cov ((fun i : Fin (N + 1) => F i.succ) j) y (F 0 y))) x)
      = (∑ l : Fin N, T (Function.update G l (fun y => cov (G l) y (F 0 y))) x) + T G x := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [lift_apply]
      rw [Function.update_comp_eq_of_injective' (fun i : Fin (N + 1) => F i.succ)
        (Fin.castSucc_injective N) l
        (fun y : M => cov (F (Fin.castSucc l).succ) y (F 0 y))]
    · rw [lift_apply]
      rw [Function.update_comp_eq_of_forall_ne' (fun i : Fin (N + 1) => F i.succ)
        (fun y : M => cov (F (Fin.last N).succ) y (F 0 y))
        (fun l => by
          intro h
          have h2 : (Fin.castSucc l : ℕ) = (Fin.last N : ℕ) := congrArg Fin.val h
          simp only [Fin.val_castSucc, Fin.val_last] at h2
          omega)]
  have hL : AMB.pD cov (lift T) F x
      = (d% (T G) x) (F 0 x)
        - ((∑ l : Fin N, T (Function.update G l (fun y => cov (G l) y (F 0 y))) x) + T G x) := by
    rw [AMB.pD, hLsum]
    rfl
  have hR : lift (AMB.pD cov T) F x
      = (d% (T G) x) (F 0 x)
        - ∑ l : Fin N, T (Function.update G l (fun y => cov (G l) y (F 0 y))) x := by
    rw [lift_apply, AMB.pD]
    simp only [Fin.castSucc_succ, Fin.castSucc_zero]
    rfl
  have hlt : lift T (fun l : Fin (N + 1) => F l.succ) x = T G x := rfl
  simp only [Pi.sub_apply]
  rw [hL, hR, hlt, sub_sub]

/-! ## The structural properties of `RicT` -/

/-- **Slot additivity and smoothness of the honest Ricci tower**, by induction on the level: the base
case is `ric2 g` and the induction step is the `pD`-invariance of the two properties. -/
theorem RicT_good (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    ∀ i : ℕ, AMB.SlotAddP (RicT g i) ∧ AMB.SmP (RicT g i) := by
  intro i
  induction i with
  | zero => exact ⟨ric2_slotAddP hLC g, ric2_smP hLC g⟩
  | succ i ih => exact ⟨pD_SlotAddP hLC g ih.1 ih.2, pD_smP hLC g ih.2⟩

/-- **The bridge to the curried honest tower**: the packed honest tower of `baseRic g` is `RicT g i`
read on the first `i + 2` slots of the tuple (the honest tower is independent of its third value
slot). -/
theorem RicT_pack_htower (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    ∀ (i : ℕ) (F : Fin (i + 3) → AMB.TF (I := I) (M := M)),
      AMB.pack (htower (Submission.Diff.lcOf g) (baseRic g) i) F
        = RicT g i (fun l : Fin (i + 2) => F (Fin.castSucc l)) := by
  intro i
  induction i with
  | zero =>
      intro F
      funext x
      simp only [htower_zero, AMB.pack_apply, RicT_zero, ric2, baseRic]
      rfl
  | succ i ih =>
      intro F
      have hpack : AMB.pack (htower (Submission.Diff.lcOf g) (baseRic g) i) = lift (RicT g i) :=
        funext ih
      rw [show htower (Submission.Diff.lcOf g) (baseRic g) (i + 1)
          = hstep (Submission.Diff.lcOf g) (htower (Submission.Diff.lcOf g) (baseRic g) i)
          from rfl]
      rw [pack_hstep (Submission.Diff.lcOf g)]
      rw [hpack]
      rw [pD_lift]
      rw [sub_add_cancel]
      rw [show RicT g (i + 1) = AMB.pD (Submission.Diff.lcOf g) (RicT g i) from rfl]
      rfl

/-! ## The main statement -/

theorem RicT_props
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    (∀ i : ℕ, Work.Diff.EXT.ConnCov.AMB.SlotAddP (Work.Diff.EXT.ConnCov.RicFlip.RicT g i))
    ∧ (∀ (i : ℕ) (F : Fin (i + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
        (∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) →
        Work.Diff.EXT.ATower.SmF I M (Work.Diff.EXT.ConnCov.RicFlip.RicT g i F))
    ∧ (∀ (i : ℕ) (F : Fin (i + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
        Work.Diff.EXT.ConnCov.AMB.pack (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf g)
            (Work.Diff.EXT.ConnCov.baseRic g) i) F
          = Work.Diff.EXT.ConnCov.RicFlip.RicT g i (fun l : Fin (i + 2) => F (Fin.castSucc l))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (RicT_good hLC g i).1
  · intro i F hF
    exact (RicT_good hLC g i).2 F hF
  · exact RicT_pack_htower hLC g

end Work.Diff.EXT.ConnCov.RicFlip
