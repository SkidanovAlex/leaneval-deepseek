import Mathlib
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.evolX.jetCalcDefs
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jets of the curvature tower are the tower at the higher level

`Work.Diff.EXT.evolX.jetAll_ckt`: the `j`-th packed jet of the level-`k` tower
`Work.Diff.EXT.ckt g k = ∇^k Rm` (a packed operator of arity `k + 4`, `Work.Diff.EXT.jetAll` being
the tower-style iteration of `Work.Diff.EXT.extStep`) is the tower at level `k + j`, up to the
reindexing of the tuple that identifies `Fin ((k+4)+j)` with `Fin ((k+j)+4)`:

`jetAll g j (k+4) (ckt g k) (fun r => H (Fin.cast _ r)) = ckt g (k+j) H`.

This is the iterated form of the definitional identity `extStep g (ckt g k) = ckt g (k+1)`
(`Work.Diff.EXT.extStep_ckt`, itself a restatement of the recursion `Work.Diff.EXT.ckt_succ`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

theorem jetAll_ckt (g : Submission.Diff.SMet I M) (K : ℕ) :
    ∀ (j : ℕ) (H : Fin ((K + j) + 4) → Work.Diff.EXT.TField (I := I) (M := M)),
      Work.Diff.EXT.jetAll g j (K + 4) (Work.Diff.EXT.ckt g K)
        (fun r : Fin ((K + 4) + j) =>
          H (Fin.cast (by omega : (K + 4) + j = (K + j) + 4) r))
      = Work.Diff.EXT.ckt g (K + j) H := by
  intro j
  induction j with
  | zero =>
    intro H
    have hfun : (fun r : Fin ((K + 4) + 0) =>
        H (Fin.cast (by omega : (K + 4) + 0 = (K + 0) + 4) r)) = H := by
      funext r
      exact congrArg H (Fin.ext (by simp))
    simp only [Work.Diff.EXT.jetAll]
    rw [hfun]
    rfl
  | succ l ih =>
    intro H
    have hA : (K + 4) + l = (K + l) + 4 := by omega
    have hB : (K + 4) + (l + 1) = (K + (l + 1)) + 4 := by omega
    -- the shifted tuple of the level-`l` jet, and the cast lemmas
    set Hs : Fin ((K + l) + 4) → Work.Diff.EXT.TField (I := I) (M := M) :=
      fun i => H i.succ with hHs
    have hsucc : ∀ (i : Fin ((K + 4) + l)),
        Fin.cast hB i.succ = (Fin.cast hA i).succ := fun i => Fin.ext (by simp)
    have hzero : Fin.cast hB (0 : Fin ((K + 4) + (l + 1))) = 0 := Fin.ext rfl
    have htu : (fun i : Fin ((K + 4) + l) =>
          (fun r : Fin ((K + 4) + (l + 1)) => H (Fin.cast hB r)) i.succ)
        = (fun i : Fin ((K + 4) + l) => Hs (Fin.cast hA i)) := by
      funext i
      rw [hHs]
      exact congrArg H (hsucc i)
    have hhd : H (Fin.cast hB (0 : Fin ((K + 4) + (l + 1)))) = H 0 := congrArg H hzero
    have hdir : ∀ (x : Fin ((K + 4) + l)),
        H (Fin.cast hB x.succ) = Hs (Fin.cast hA x) := by
      intro x
      rw [hHs]
      exact congrArg H (hsucc x)
    -- each Leibniz correction, transported along the cast
    have hcorr : ∀ (i : Fin ((K + 4) + l)),
        (Function.update (fun i : Fin ((K + 4) + l) => Hs (Fin.cast hA i)) i
          (Work.Diff.EXT.dirF g (Hs (Fin.cast hA i)) (H 0)))
        = (fun j : Fin ((K + 4) + l) =>
            (Function.update Hs (Fin.cast hA i)
              (Work.Diff.EXT.dirF g (Hs (Fin.cast hA i)) (H 0))) (Fin.cast hA j)) := by
      intro i
      funext j
      rw [Function.update_apply, Function.update_apply]
      by_cases hj : j = i
      · subst hj
        rw [if_pos rfl, if_pos rfl]
      · have hne : Fin.cast hA j ≠ Fin.cast hA i := by
          intro h
          refine hj (Fin.ext ?_)
          simpa only [Fin.val_cast] using congrArg Fin.val h
        rw [if_neg hj, if_neg hne]
    -- the induction hypothesis, in the forms needed below
    have hstep : Work.Diff.EXT.jetAll g l (K + 4) (Work.Diff.EXT.ckt g K)
        (fun i : Fin ((K + 4) + l) => Hs (Fin.cast hA i)) = Work.Diff.EXT.ckt g (K + l) Hs :=
      ih Hs
    have hstepcorr : ∀ (i : Fin ((K + 4) + l)),
        Work.Diff.EXT.jetAll g l (K + 4) (Work.Diff.EXT.ckt g K)
          (Function.update (fun i : Fin ((K + 4) + l) => Hs (Fin.cast hA i)) i
            (Work.Diff.EXT.dirF g (Hs (Fin.cast hA i)) (H 0)))
        = Work.Diff.EXT.ckt g (K + l)
            (Function.update Hs (Fin.cast hA i)
              (Work.Diff.EXT.dirF g (Hs (Fin.cast hA i)) (H 0))) := by
      intro i
      rw [hcorr i]
      exact ih _
    -- compare the two recursions pointwise
    funext y
    show (Work.Diff.EXT.extStep g (Work.Diff.EXT.jetAll g l (K + 4) (Work.Diff.EXT.ckt g K))
        (fun r : Fin ((K + 4) + (l + 1)) => H (Fin.cast hB r)) y)
      = Work.Diff.EXT.ckt g ((K + l) + 1) H y
    simp only [Work.Diff.EXT.ckt_succ, Work.Diff.EXT.extStep, htu, hhd, hdir, hstep, ← hHs]
    rw [Finset.sum_congr rfl (fun i _ => congrFun (hstepcorr i) y)]
    congr 1
    exact Fintype.sum_bijective (finCongr hA) (finCongr hA).bijective _ _
      (fun i => by simp only [finCongr_apply, hHs])

/-- **The jets of the tower are the tower at the higher level**, with the reindexing eliminated:
`jetAll g j (k+4) (ckt g k) F = ckt g (k+j) (F ∘ Fin.cast _)`. -/
theorem jetAll_ckt' (g : Submission.Diff.SMet I M) (K : ℕ) (j : ℕ)
    (F : Fin ((K + 4) + j) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.jetAll g j (K + 4) (Work.Diff.EXT.ckt g K) F
      = Work.Diff.EXT.ckt g (K + j) (fun r : Fin ((K + j) + 4) =>
          F (Fin.cast (by omega : (K + j) + 4 = (K + 4) + j) r)) := by
  have h := jetAll_ckt (I := I) (M := M) g K j
    (fun r : Fin ((K + j) + 4) =>
      F (Fin.cast (by omega : (K + j) + 4 = (K + 4) + j) r))
  have htuple : F = (fun r : Fin ((K + 4) + j) =>
      (fun r : Fin ((K + j) + 4) =>
        F (Fin.cast (by omega : (K + j) + 4 = (K + 4) + j) r))
      (Fin.cast (by omega : (K + 4) + j = (K + j) + 4) r)) := by
    funext r
    congr 1
  rw [htuple, h]
  congr 1

/-- **The single-level strength of the curvature tower.**  The `j`-th jet of `ckt g k = ∇^k Rm` is
bounded by `√(|∇^{k+j} Rm|²)` times the product of the metric norms of the entries of the tuple:
this is `Work.Diff.EXT.evolX.jetAll_ckt'` (the jets of the tower are the tower at the higher level)
combined with the sharp evaluation bound `Work.Diff.EXT.Kpt_norm_bound` and the value dependence
`Work.Diff.EXT.ckt_val_dep_all` of the tower. -/
theorem strongAt_ckt [T2Space M] (g : Submission.Diff.SMet I M) (x : M) (K : ℕ) :
    StrongAt g x K (fun _ => (1 : ℝ)) (Work.Diff.EXT.ckt (I := I) (M := M) g K) := by
  intro j G hG
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  -- replace the tuple by the `smoothExt`-tuple of its values
  set G' : Fin ((K + j) + 4) → Work.Diff.EXT.TField (I := I) (M := M) :=
    fun r => Submission.Diff.smoothExt x (G (Fin.cast (by omega : (K + j) + 4 = (K + 4) + j) r) x)
    with hG'
  have hGsm : ∀ r, Work.Diff.EXT.SmoothF (I := I) (M := M)
      ((fun r : Fin ((K + j) + 4) =>
        G (Fin.cast (by omega : (K + j) + 4 = (K + 4) + j) r)) r) := fun r => hG _
  have hG'sm : ∀ r, Work.Diff.EXT.SmoothF (I := I) (M := M) (G' r) :=
    fun r => Work.Diff.GE.smoothExt_cmdiff x _
  have hval : ∀ r, (fun r : Fin ((K + j) + 4) =>
        G (Fin.cast (by omega : (K + j) + 4 = (K + 4) + j) r)) r x = G' r x :=
    fun r => (Work.Diff.GE.smoothExt_apply x _).symm
  rw [jetAll_ckt' (I := I) (M := M) g K j G]
  rw [Work.Diff.EXT.ckt_val_dep_all (I := I) (M := M) hLC g (K + j) x hGsm hG'sm hval]
  -- the resulting value is `Kpt` on the tuple of values
  have hKpt : Work.Diff.EXT.ckt g (K + j) G' x
      = Work.Diff.EXT.Kpt g x (K + j) (fun r => G' r x) := by
    simp only [Work.Diff.EXT.Kpt]
    congr 1
    funext r
    simp only [hG', Work.Diff.GE.smoothExt_apply]
  rw [hKpt]
  refine le_trans (Work.Diff.EXT.Kpt_norm_bound (I := I) (M := M) hLC g x (K + j)
    (fun r => G' r x)) ?_
  simp only [one_mul]
  -- the product of the norms is the same, reindexed by the cast
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [← Fintype.prod_equiv (finCongr (by omega : (K + j) + 4 = (K + 4) + j))
    (fun r : Fin ((K + j) + 4) => Real.sqrt (g.inner x (G' r x) (G' r x)))
    (fun r : Fin ((K + 4) + j) => Real.sqrt (g.inner x (G r x) (G r x)))]
  intro r
  simp only [finCongr_apply, hG', Work.Diff.GE.smoothExt_apply]

end Work.Diff.EXT.evolX
