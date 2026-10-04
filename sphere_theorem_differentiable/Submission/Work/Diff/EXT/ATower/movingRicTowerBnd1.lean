import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.HonestTower
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packedTowerShift
import Submission.Work.Diff.EXT.ConnCov.RicTr.movingRicHonestTower
import Submission.Work.Diff.EXT.ConnCov.RicTr.htowerTensorialH
import Submission.Work.Diff.EXT.ConnCov.RicTr.frameCorrZero
import Submission.Work.Diff.EXT.ConnCov.RicFlip.RicT_props
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.conn_diff_bound_of_shibounds
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ATower.step_flip

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The moving-connection bounds for the honest Ricci tower

`Work.Diff.EXT.ConnCov.RicFlip.RicT (G t) j = pDiter2 (lcOf (G t)) (ric2 (G t)) j` is the `j`-th
covariant derivative of the Ricci tensor of the metric `G t`, computed with the **moving**
connection `∇^{G t}` (`j + 2` slots: `j` differentiation slots and the two value slots of the
`(0,2)`-tensor `Ric`).  `Work.Diff.EXT.ConnCov.AMB.Bnd1 G t τ C` is the *monotone slot bound*

  `|τ F x| ≤ C · ∏_s (1 + ‖F s (x)‖_{G t})`  for every tuple `F` of smooth fields,

which is the shape consumed by the two-connection flip (`RicFlip/Defs.lean`, `ricFlipOfMoving`).

This module proves `Work.Diff.EXT.ATower.movingRicTowerBnd1`: on the collapsed interval
`[T/2, T)` of a Ricci flow satisfying `|Rm| ≤ C` and Shi's a priori estimates, all levels
`j ≤ k` of the moving honest Ricci tower are uniformly bounded in the `Bnd1` shape.

## Route

The honest tower `htower (lcOf (G t)) (baseRic (G t)) j` — the `j`-th covariant derivative of
`Ric` read as a `(0,3)`-tensor with a dummy third value slot — is bounded **uniformly on the slab**
by `Work.Diff.EXT.ConnCov.RicTr.movingRicHonestTower` (proved through the trace identity
`∇^j Ric = ∑_p ∇^j Rm(·, e_p, ·, e_p, ·)`, the frame-correction cancellation of
`RicTr/frameCorrZero.lean` and the evaluation bound `covKRmExt_eval_bound`).  Its value on
`smoothExt`-fields is the value-level operator `valOp`, which is exactly what that theorem bounds.

The bridge to the target is the *packed* bridge `RicFlip.pack_htower_pDiter2`:
`AMB.pack (htower cov (baseRic g) i) F = pDiter2 cov (ric2 g) i (F ∘ Fin.castSucc)`.  Given a tuple
`F : Fin (j+2) → TF` of smooth fields, extend it by a dummy (the smooth field `smoothExt x 0`, which
vanishes at `x`) in the slot that `pDiter2` drops: then the packed honest tower on the extension is
the honest Ricci tower on `F`.  Two auxiliary facts finish the job:

* `pack_htower_eq_valOp` — the packed honest tower on a tuple of smooth fields equals `valOp` on the
  *values* of that tuple (value-dependence of the honest tower, `RicTr.htowerTensorialH`, whose
  frame-correction hypothesis is discharged by `RicTr.frameCorrZero`);
* `prod_sqrt_le_oneAdd_two` — the elementary product comparison
  `∏_i √f_i · √f_{j} · √f_{j+1} ≤ ∏_s (1 + √f_s)` over the `j + 2` slots.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ATower

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- Evaluation of `Fin.snoc` at a slot of the `Fin.castAdd` block. -/
private lemma snoc_castAdd {j : ℕ}
    (F : Fin (j + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (d : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (i : Fin j) :
    (Fin.snoc F d : Fin (j + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
        (Fin.castAdd 3 i) = F (Fin.castAdd 2 i) := by
  have h : (Fin.castAdd 3 i : Fin (j + 3)) = (Fin.castAdd 2 i).castSucc := Fin.ext rfl
  rw [h]
  exact @Fin.snoc_castSucc (j + 2)
    (fun _ => Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) d F (Fin.castAdd 2 i)

/-- Evaluation of `Fin.snoc` at the first value slot. -/
private lemma snoc_natAdd0 {j : ℕ}
    (F : Fin (j + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (d : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    (Fin.snoc F d : Fin (j + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
        (Fin.natAdd j (0 : Fin 3)) = F (Fin.natAdd j (0 : Fin 2)) := by
  have h : (Fin.natAdd j (0 : Fin 3) : Fin (j + 3))
      = (Fin.natAdd j (0 : Fin 2)).castSucc := Fin.ext rfl
  rw [h]
  exact @Fin.snoc_castSucc (j + 2)
    (fun _ => Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) d F (Fin.natAdd j (0 : Fin 2))

/-- Evaluation of `Fin.snoc` at the second value slot. -/
private lemma snoc_natAdd1 {j : ℕ}
    (F : Fin (j + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (d : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    (Fin.snoc F d : Fin (j + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
        (Fin.natAdd j (1 : Fin 3)) = F (Fin.natAdd j (1 : Fin 2)) := by
  have h : (Fin.natAdd j (1 : Fin 3) : Fin (j + 3))
      = (Fin.natAdd j (1 : Fin 2)).castSucc := Fin.ext rfl
  rw [h]
  exact @Fin.snoc_castSucc (j + 2)
    (fun _ => Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) d F (Fin.natAdd j (1 : Fin 2))

/-- Evaluation of `Fin.snoc` at the dropped third value slot. -/
private lemma snoc_natAdd2 {j : ℕ}
    (F : Fin (j + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (d : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    (Fin.snoc F d : Fin (j + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
        (Fin.natAdd j (2 : Fin 3)) = d := by
  have h : (Fin.natAdd j (2 : Fin 3) : Fin (j + 3)) = Fin.last (j + 2) := Fin.ext rfl
  rw [h]
  exact @Fin.snoc_last (j + 2)
    (fun _ => Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) d F

/-- **The packed honest Ricci tower on a smooth tuple is the value-level operator.**

`AMB.pack` evaluates `htower (lcOf g) (baseRic g) j` on the `j` direction fields `F ∘ Fin.castAdd 3`
and the three value fields `F (Fin.natAdd j 0/1/2)`; `valOp` evaluates it on the canonical smooth
extensions `smoothExt x ·` of the values of those fields.  Since the honest tower of `Ric` is
tensorial in all its slots (`RicTr.htowerTensorialH`), the two agree. -/
theorem pack_htower_eq_valOp
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (j : ℕ)
    (x : M) (F : Fin (j + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (hF : ∀ s, Work.Diff.EXT.ATower.SmE I M (F s)) :
    Work.Diff.EXT.ConnCov.AMB.pack
        (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G t))
          (Work.Diff.EXT.ConnCov.baseRic (G t)) j) F x
      = Work.Diff.EXT.ATower.valOp
          (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G t))
            (Work.Diff.EXT.ConnCov.baseRic (G t)) j) x
          (fun i : Fin j => F (Fin.castAdd 3 i) x) (F (Fin.natAdd j 0) x)
          (F (Fin.natAdd j 1) x) (F (Fin.natAdd j 2) x) := by
  -- the frame-correction cancellation of `∇^j Rm` (`RicTr.frameCorrZero`)
  have hcan : ∀ (g : Submission.Diff.SMet I M) (y : M) (n : ℕ)
      (v : Fin n → (Π z : M, TangentSpace I z)) (v0 A B : Π z : M, TangentSpace I z)
      (W : Fin (Module.finrank ℝ E) → (Π z : M, TangentSpace I z)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M v0 →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      (∀ m, Work.Diff.EXT.ATower.SmE I M (W m)) →
      (∀ᶠ z in nhds y, Submission.Diff.IsONFrame g z (fun m => W m z)) →
      (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g n v
          (Work.Diff.EXT.dirF g (W m) v0) A (W m) B y))
        + (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g n v (W m) A
            (Work.Diff.EXT.dirF g (W m) v0) B y)) = 0 :=
    fun g y n v v0 A B W hv hv0 hA hB hW hON =>
      Work.Diff.EXT.ConnCov.RicTr.frameCorrZero (I := I) (M := M) hLC g y n v v0 A B W
        hv hv0 hA hB hW hON
  -- value-dependence of the honest tower of `Ric`
  have hten := Work.Diff.EXT.ConnCov.RicTr.htowerTensorialH (I := I) (M := M) hcan hLC (G t) j
    (fun i : Fin j => F (Fin.castAdd 3 i))
    (fun i : Fin j => Submission.Diff.smoothExt x (F (Fin.castAdd 3 i) x))
    (F (Fin.natAdd j 0)) (Submission.Diff.smoothExt x (F (Fin.natAdd j 0) x))
    (F (Fin.natAdd j 1)) (Submission.Diff.smoothExt x (F (Fin.natAdd j 1) x))
    (F (Fin.natAdd j 2)) (Submission.Diff.smoothExt x (F (Fin.natAdd j 2) x)) x
    (fun i => hF _) (fun i => Work.Diff.GE.smoothExt_cmdiff x _)
    (hF _) (Work.Diff.GE.smoothExt_cmdiff x _)
    (hF _) (Work.Diff.GE.smoothExt_cmdiff x _)
    (hF _) (Work.Diff.GE.smoothExt_cmdiff x _)
    (fun i => (Work.Diff.GE.smoothExt_apply x _).symm) (Work.Diff.GE.smoothExt_apply x _).symm
    (Work.Diff.GE.smoothExt_apply x _).symm (Work.Diff.GE.smoothExt_apply x _).symm
  simp only [Work.Diff.EXT.ConnCov.AMB.pack_apply, Work.Diff.EXT.ATower.valOp]
  exact hten

/-- **The product estimate for the `j + 2`-slot `Bnd1` shape**: the product of the square roots of
the `j` direction slots and of the two value slots is dominated by the product of `(1 + √·)` over
all `j + 2` slots. -/
lemma prod_sqrt_le_oneAdd_two (j : ℕ) (f : Fin (j + 2) → ℝ) (C : ℝ) (hC : 0 ≤ C) :
    C * ((∏ i : Fin j, Real.sqrt (f (Fin.castAdd 2 i)))
        * Real.sqrt (f (Fin.natAdd j 0)) * Real.sqrt (f (Fin.natAdd j 1)))
      ≤ C * ∏ k : Fin (j + 2), (1 + Real.sqrt (f k)) := by
  have hprod : (∏ k : Fin (j + 2), (1 + Real.sqrt (f k)))
      = (∏ i : Fin j, (1 + Real.sqrt (f (Fin.castAdd 2 i))))
        * (1 + Real.sqrt (f (Fin.natAdd j 0)))
        * (1 + Real.sqrt (f (Fin.natAdd j 1))) := by
    rw [Fin.prod_univ_add (a := j) (b := 2)
      (fun k : Fin (j + 2) => 1 + Real.sqrt (f k))]
    rw [Fin.prod_univ_two (fun m : Fin 2 => 1 + Real.sqrt (f (Fin.natAdd j m)))]
    ring
  rw [hprod]
  have hA : (∏ i : Fin j, Real.sqrt (f (Fin.castAdd 2 i)))
      ≤ ∏ i : Fin j, (1 + Real.sqrt (f (Fin.castAdd 2 i))) :=
    Finset.prod_le_prod₀ (fun i _ => Real.sqrt_nonneg _)
      (fun i _ => by linarith [Real.sqrt_nonneg (f (Fin.castAdd 2 i))])
  have hA1 : (0 : ℝ) ≤ ∏ i : Fin j, (1 + Real.sqrt (f (Fin.castAdd 2 i))) :=
    Finset.prod_nonneg (fun i _ => by linarith [Real.sqrt_nonneg (f (Fin.castAdd 2 i))])
  have h0 : (0 : ℝ) ≤ Real.sqrt (f (Fin.natAdd j 0)) := Real.sqrt_nonneg _
  have h1 : (0 : ℝ) ≤ Real.sqrt (f (Fin.natAdd j 1)) := Real.sqrt_nonneg _
  have e0 : Real.sqrt (f (Fin.natAdd j 0)) ≤ 1 + Real.sqrt (f (Fin.natAdd j 0)) := by linarith
  have e1 : Real.sqrt (f (Fin.natAdd j 1)) ≤ 1 + Real.sqrt (f (Fin.natAdd j 1)) := by linarith
  have hmul : (∏ i : Fin j, Real.sqrt (f (Fin.castAdd 2 i)))
        * Real.sqrt (f (Fin.natAdd j 0)) * Real.sqrt (f (Fin.natAdd j 1))
      ≤ (∏ i : Fin j, (1 + Real.sqrt (f (Fin.castAdd 2 i))))
        * (1 + Real.sqrt (f (Fin.natAdd j 0)))
        * (1 + Real.sqrt (f (Fin.natAdd j 1))) :=
    mul_le_mul (mul_le_mul hA e0 h0 hA1) e1 h1
      (mul_nonneg hA1 (by linarith))
  exact mul_le_mul_of_nonneg_left hmul hC

end Helpers

theorem movingRicTowerBnd1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (k : ℕ) :
    ∃ R : ℕ → ℝ, (∀ j, 0 ≤ R j) ∧ ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ConnCov.AMB.Bnd1 (I := I) (M := M) G t
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) j) (R j) := by
  classical
  -- the uniform bound on the honest towers of `Ric` along the flow (`∇^{G t,m}Ric`, `m ≤ k`)
  obtain ⟨R₀, hR₀, hR⟩ := Work.Diff.EXT.ConnCov.RicTr.movingRicHonestTower (I := I) (M := M)
    hLC G T C hT hC hflow hbound hmet hShi k
  refine ⟨fun _ => R₀, fun _ => hR₀, ?_⟩
  intro j hj t ht F x hF
  -- the tuple `F` extended by a dummy (smooth, zero at `x`) in the dropped third value slot
  set dummy : Π y : M, TangentSpace I y := Submission.Diff.smoothExt x (0 : TangentSpace I x)
    with hdummy
  set Fext : Fin (j + 3) → (Π y : M, TangentSpace I y) := Fin.snoc F dummy with hFext
  have hFextsm : ∀ s, Work.Diff.EXT.ATower.SmE I M (Fext s) := by
    intro s
    rcases Fin.eq_castSucc_or_eq_last s with ⟨l, hl⟩ | hl
    · rw [hl, hFext, Fin.snoc_castSucc]
      exact hF l
    · rw [hl, hFext, Fin.snoc_last, hdummy]
      exact Work.Diff.GE.smoothExt_cmdiff x 0
  -- the packed honest tower is the honest Ricci tower on the first `j + 2` slots
  have hbr := congrFun (Work.Diff.EXT.ConnCov.RicFlip.pack_htower_pDiter2 (I := I) (M := M)
    (Submission.Diff.lcOf (G t)) (G t) j Fext) x
  have htail : (fun l : Fin (j + 2) => Fext l.castSucc) = F := by
    funext l
    rw [hFext]
    exact @Fin.snoc_castSucc (j + 2)
      (fun _ => (Π y : M, TangentSpace I y)) dummy F l
  rw [htail] at hbr
  -- and the packed honest tower is the value-level operator
  have hval := pack_htower_eq_valOp (I := I) (M := M) hLC G t j x Fext hFextsm
  rw [← hbr, hval]
  -- the argument slots of `valOp` are those of `F`
  have e1 : (fun i : Fin j => Fext (Fin.castAdd 3 i) x)
      = fun i : Fin j => F (Fin.castAdd 2 i) x := by
    funext i
    rw [hFext]
    exact congrFun (snoc_castAdd F dummy i) x
  have e2 : Fext (Fin.natAdd j 0) x = F (Fin.natAdd j 0) x := by
    rw [hFext]
    exact congrFun (snoc_natAdd0 F dummy) x
  have e3 : Fext (Fin.natAdd j 1) x = F (Fin.natAdd j 1) x := by
    rw [hFext]
    exact congrFun (snoc_natAdd1 F dummy) x
  rw [e1, e2, e3]
  -- the honest-tower bound supplied by the Shi estimates
  have hb := hR t ht j hj x (fun i : Fin j => F (Fin.castAdd 2 i) x) (F (Fin.natAdd j 0) x)
    (F (Fin.natAdd j 1) x) (Fext (Fin.natAdd j 2) x)
  refine hb.trans ?_
  -- the elementary product comparison
  exact prod_sqrt_le_oneAdd_two j (fun s : Fin (j + 2) => (G t).inner x (F s x) (F s x))
    R₀ hR₀

end Work.Diff.EXT.ATower
