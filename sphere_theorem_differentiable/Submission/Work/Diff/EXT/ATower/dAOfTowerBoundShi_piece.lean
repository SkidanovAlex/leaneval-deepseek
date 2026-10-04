import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ATower.DA3Defs
import Submission.Work.Diff.EXT.ATower.fixedRicTowerBound
import Submission.Work.Diff.EXT.ATower.dR3_tower_eq_tower2
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.moving_honest_ric_tower
import Submission.Work.Diff.EXT.ConnCov.RicTr.honestRicTowerH
import Submission.Work.Diff.EXT.ConnCov.RicTr.honestRicTowerA
import Submission.Work.Diff.EXT.ConnCov.RicTr.movingRicHonestTower
import Submission.Work.Diff.EXT.ConnCov.RicTr.ricTowerBound_fixed_of_stage
import Submission.Work.Diff.EXT.ConnCov.RicTr.deltaTower_bound_of_hA
import Submission.Work.Diff.EXT.ConnCov.RicTr.htowerLift23
import Submission.Work.Diff.EXT.ConnCov.RicTr.baseRic_sm
import Submission.Work.Diff.EXT.ConnCov.RicTr.frameCorrZero
import Submission.Work.Diff.EXT.ConnCov.covKAExt_bound_local
import Submission.Work.Diff.EXT.ConnCov.covKAExt_bound_locBdd
import Submission.Work.Diff.EXT.covKAExt_tensorial
import Submission.Work.Diff.EXT.ATower.step_flip
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF
import Submission.Work.Diff.EXT.ATower.tower_value_dep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ATower

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- `stepAux cov τ` depends only on the values of `τ` on smooth field tuples. -/
theorem stepAux_eq_of_eq_smE
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    {τ₁ τ₂ : Op3 (I := I) (M := M) k}
    (hτ : ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (u i)) → SmE I M A → SmE I M B → SmE I M C →
      ∀ y : M, τ₁ u A B C y = τ₂ u A B C y)
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    (w : TF (I := I) (M := M)) (u : Fin k → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M))
    (hw : SmE I M w) (hu : ∀ i, SmE I M (u i)) (hA : SmE I M A) (hB : SmE I M B)
    (hC : SmE I M C) (x : M) :
    stepAux cov τ₁ w u A B C x = stepAux cov τ₂ w u A B C x := by
  have hfun : τ₁ u A B C = τ₂ u A B C := funext (fun y => hτ u A B C hu hA hB hC y)
  have hu' : ∀ i : Fin k, SmE I M (fun y => cov (u i) y (w y)) :=
    fun i => hcov (u i) w (hu i) hw
  have hupd : ∀ i : Fin k,
      (∀ j, SmE I M ((Function.update u i (fun y => cov (u i) y (w y))) j)) := by
    intro i j
    by_cases hj : j = i
    · rw [hj, Function.update_self]
      exact hu' i
    · rw [Function.update_of_ne hj]
      exact hu j
  have hsum : (∑ i : Fin k, τ₁ (Function.update u i (fun y => cov (u i) y (w y))) A B C x)
      = ∑ i : Fin k, τ₂ (Function.update u i (fun y => cov (u i) y (w y))) A B C x :=
    Finset.sum_congr rfl (fun i _ => hτ _ A B C (hupd i) hA hB hC x)
  have hA' : τ₁ u (fun y => cov A y (w y)) B C x = τ₂ u (fun y => cov A y (w y)) B C x :=
    hτ u _ B C hu (hcov A w hA hw) hB hC x
  have hB' : τ₁ u A (fun y => cov B y (w y)) C x = τ₂ u A (fun y => cov B y (w y)) C x :=
    hτ u A _ C hu hA (hcov B w hB hw) hC x
  have hC' : τ₁ u A B (fun y => cov C y (w y)) x = τ₂ u A B (fun y => cov C y (w y)) x :=
    hτ u A B _ hu hA hB (hcov C w hC hw) x
  simp only [stepAux]
  rw [hfun, hsum, hA', hB', hC']

/-- **Two towers of bases that agree on smooth tuples agree on smooth tuples.** -/
theorem tower_eq_of_eq_smE
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {base₁ base₂ : Op3 (I := I) (M := M) 0}
    (h : ∀ (X Y Z : TF (I := I) (M := M)), SmE I M X → SmE I M Y → SmE I M Z →
      ∀ y : M, base₁ (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) X Y Z y
        = base₂ (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) X Y Z y) :
    ∀ k : ℕ, ∀ (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C →
      tower cov base₁ k v A B C = tower cov base₂ k v A B C := by
  intro k
  induction k with
  | zero =>
      intro v A B C _ hA hB hC
      have hv0 : v = (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) := Subsingleton.elim _ _
      subst hv0
      exact funext (fun y => h A B C hA hB hC y)
  | succ k ih =>
      intro v A B C hv hA hB hC
      rw [show tower cov base₁ (k + 1) v A B C = step cov (tower cov base₁ k) v A B C from rfl,
        show tower cov base₂ (k + 1) v A B C = step cov (tower cov base₂ k) v A B C from rfl,
        step_eq_stepAux, step_eq_stepAux]
      refine funext (fun x => stepAux_eq_of_eq_smE cov
        (τ₁ := tower cov base₁ k) (τ₂ := tower cov base₂ k)
        (fun u A' B' C' hu hA' hB' hC' => congrFun (ih u A' B' C' hu hA' hB' hC'))
        hcov (v 0) (fun i : Fin k => v i.succ) A B C (hv 0) (fun i => hv i.succ)
        hA hB hC x)

/-- **The tower of the reaction is the tower of the Koszul combination `dR3`** (on smooth field
tuples): the two `Op3 0` bases agree on smooth tuples by `dAOfBase_eq_dR3`. -/
theorem tower_dAOfBase_eq_dR3
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    ∀ k : ℕ, ∀ (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C →
      tower (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.dAOfBase G t) k v A B C
        = tower (Submission.Diff.lcOf (G 0)) (dR3 G t) k v A B C :=
  tower_eq_of_eq_smE (Submission.Diff.lcOf (G 0))
    (fun Y Z hY hZ => Work.Diff.EXT.ATower.lcOf_apply_smE hLC (G 0) Y Z hY hZ)
    (fun X Y Z hX hY hZ y => dAOfBase_eq_dR3 (I := I) (M := M) hLC hflow ht X Y Z hX hY hZ y)

/-- `Fin.snoc` commutes with the canonical smooth extension `smoothExt x ·`. -/
theorem snoc_smoothExt {x : M} {k : ℕ} (v : Fin k → TangentSpace I x) (A : TangentSpace I x) :
    (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
        (Submission.Diff.smoothExt x A))
      = fun j : Fin (k + 1) =>
          Submission.Diff.smoothExt x
            ((Fin.snoc (α := fun _ : Fin (k + 1) => TangentSpace I x) v A) j) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp only [Fin.snoc_last]
  · intro i
    simp only [Fin.snoc_castSucc]

/-- The product of the `sqrt`-norm factors along `Fin.snoc v A` factors at the last slot. -/
theorem prod_snoc_sqrt {x : M} {k : ℕ} (g : Submission.Diff.SMet I M) (v : Fin k → TangentSpace I x)
    (A : TangentSpace I x) :
    (Finset.univ.prod (fun i : Fin (k + 1) =>
        Real.sqrt (g.inner x
          ((Fin.snoc (α := fun _ : Fin (k + 1) => TangentSpace I x) v A) i)
          ((Fin.snoc (α := fun _ : Fin (k + 1) => TangentSpace I x) v A) i))))
      = (Finset.univ.prod (fun i : Fin k => Real.sqrt (g.inner x (v i) (v i))))
        * Real.sqrt (g.inner x A A) := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.snoc_castSucc])
  · rw [Fin.snoc_last]

/-- **The target from the two external inputs**: the uniform bound on the fixed `(0,2)`-Ricci tower
at level `k + 1` (`hcore`, the piece proved in `fixedRicTowerBound`) and the identification of the
tower of `dR3` with that tower (`hswap`, proved in `dR3_tower_eq_tower2`).  The reduction uses the
bridge `tower_dAOfBase_eq_dR3` and the elementary product bookkeeping. -/
theorem dAOfTowerBoundShi_piece_of_inputs
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
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j))
    (hcore : ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ k + 1 → ∀ x : M,
      ∀ (w : Fin m → TangentSpace I x) (a b : TangentSpace I x),
        |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) m
            (fun i => Submission.Diff.smoothExt x (w i)) (Submission.Diff.smoothExt x a)
            (Submission.Diff.smoothExt x b) x|
          ≤ Cj * (Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (w i) (w i))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))
    (hswap : ∀ (t : ℝ) (j : ℕ) (v : Fin j → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → ∀ x : M,
      tower (Submission.Diff.lcOf (G 0)) (dR3 G t) j v A B C x
        = -(Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (j + 1) (Fin.snoc v A) B C x
            + Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (j + 1) (Fin.snoc v B) A C x
            - Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (j + 1) (Fin.snoc v C) A B x)) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.dAOfBase G t) k
            (fun i => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) x|
          ≤ Ck * (1 + Finset.sum (Finset.range (k + 1)) B)
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) := by
  obtain ⟨Cj, hCj0, hCj⟩ := hcore
  refine ⟨3 * Cj, by linarith, ?_⟩
  intro t ht x v a b c
  have ht' : t ∈ Set.Ioo 0 T := ⟨by linarith [hT, ht.1], ht.2⟩
  have hv : ∀ i : Fin k, SmE I M (fun y => Submission.Diff.smoothExt x (v i) y) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x (v i)
  have ha : SmE I M (fun y => Submission.Diff.smoothExt x a y) :=
    Work.Diff.GE.smoothExt_cmdiff x a
  have hb : SmE I M (fun y => Submission.Diff.smoothExt x b y) :=
    Work.Diff.GE.smoothExt_cmdiff x b
  have hc : SmE I M (fun y => Submission.Diff.smoothExt x c y) :=
    Work.Diff.GE.smoothExt_cmdiff x c
  have hterm : ∀ (A P Q : TangentSpace I x),
      |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
          (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x A)) (Submission.Diff.smoothExt x P)
          (Submission.Diff.smoothExt x Q) x|
        ≤ Cj * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
            * Real.sqrt ((G t).inner x A A) * Real.sqrt ((G t).inner x P P)
            * Real.sqrt ((G t).inner x Q Q)) := by
    intro A P Q
    rw [snoc_smoothExt (I := I) v A]
    have h := hCj t ht (k + 1) le_rfl x
      (Fin.snoc (α := fun _ : Fin (k + 1) => TangentSpace I x) v A) P Q
    rw [prod_snoc_sqrt (I := I) (G t) v A] at h
    refine le_trans h (le_of_eq (by ring))
  have h1 := hterm a b c
  have h2 := hterm b a c
  have h3 := hterm c a b
  have hI1 := congrFun (tower_dAOfBase_eq_dR3 (I := I) (M := M) hLC hflow ht' k
    (fun i => Submission.Diff.smoothExt x (v i)) (Submission.Diff.smoothExt x a)
    (Submission.Diff.smoothExt x b) (Submission.Diff.smoothExt x c) hv ha hb hc) x
  have hI2 := hswap t k (fun i => Submission.Diff.smoothExt x (v i))
    (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
    (Submission.Diff.smoothExt x c) hv ha hb hc x
  rw [hI1, hI2]
  set S : ℝ := Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
      * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
      * Real.sqrt ((G t).inner x c c) with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hb1 : |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
        (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x a)) (Submission.Diff.smoothExt x b)
        (Submission.Diff.smoothExt x c) x| ≤ Cj * S :=
    le_trans h1 (le_of_eq (by rw [hS]; try ring))
  have hb2 : |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
        (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x b)) (Submission.Diff.smoothExt x a)
        (Submission.Diff.smoothExt x c) x| ≤ Cj * S :=
    le_trans h2 (le_of_eq (by rw [hS]; try ring))
  have hb3 : |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
        (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x c)) (Submission.Diff.smoothExt x a)
        (Submission.Diff.smoothExt x b) x| ≤ Cj * S :=
    le_trans h3 (le_of_eq (by rw [hS]; try ring))
  have htri : |-(Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
          (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a)) (Submission.Diff.smoothExt x b)
          (Submission.Diff.smoothExt x c) x
        + Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
          (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x b)) (Submission.Diff.smoothExt x a)
          (Submission.Diff.smoothExt x c) x
        - Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
          (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x c)) (Submission.Diff.smoothExt x a)
          (Submission.Diff.smoothExt x b) x)| ≤ 3 * (Cj * S) := by
    rw [abs_neg]
    have hsplit : |(Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
          (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a)) (Submission.Diff.smoothExt x b)
          (Submission.Diff.smoothExt x c) x
        + Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
          (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x b)) (Submission.Diff.smoothExt x a)
          (Submission.Diff.smoothExt x c) x)
        - Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
          (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x c)) (Submission.Diff.smoothExt x a)
          (Submission.Diff.smoothExt x b) x|
        ≤ |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
              (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
                (Submission.Diff.smoothExt x a)) (Submission.Diff.smoothExt x b)
              (Submission.Diff.smoothExt x c) x|
          + |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
              (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
                (Submission.Diff.smoothExt x b)) (Submission.Diff.smoothExt x a)
              (Submission.Diff.smoothExt x c) x|
          + |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
              (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
                (Submission.Diff.smoothExt x c)) (Submission.Diff.smoothExt x a)
              (Submission.Diff.smoothExt x b) x| := by
      have h1' := abs_sub
        (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
            (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
              (Submission.Diff.smoothExt x a)) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) x
          + Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
            (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
              (Submission.Diff.smoothExt x b)) (Submission.Diff.smoothExt x a)
            (Submission.Diff.smoothExt x c) x)
        (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
            (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
              (Submission.Diff.smoothExt x c)) (Submission.Diff.smoothExt x a)
            (Submission.Diff.smoothExt x b) x)
      have h2' := abs_add_le
        (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
            (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
              (Submission.Diff.smoothExt x a)) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) x)
        (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
            (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
              (Submission.Diff.smoothExt x b)) (Submission.Diff.smoothExt x a)
            (Submission.Diff.smoothExt x c) x)
      linarith
    refine le_trans hsplit ?_
    linarith
  refine le_trans htri ?_
  have h1B : (1 : ℝ) ≤ 1 + Finset.sum (Finset.range (k + 1)) B := by
    have h := Finset.sum_nonneg (s := Finset.range (k + 1)) (fun j _ => hB j)
    linarith
  calc 3 * (Cj * S) = 3 * Cj * 1 * S := by ring
    _ ≤ 3 * Cj * (1 + Finset.sum (Finset.range (k + 1)) B) * S := by
        refine mul_le_mul_of_nonneg_right ?_ hS0
        exact mul_le_mul_of_nonneg_left h1B (by linarith)
    _ = (3 * Cj) * (1 + Finset.sum (Finset.range (k + 1)) B)
          * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          * Real.sqrt ((G t).inner x c c) := by rw [hS]; try ring

/-- **The target from the swap input alone** (the core bound `fixedRicTowerBound` is now proved and
is discharged here): so the assignment rests on the single identity `hswap`
(`dR3_tower_eq_tower2`). -/
theorem dAOfTowerBoundShi_piece_of_swap
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
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j))
    (hswap : ∀ (t : ℝ) (j : ℕ) (v : Fin j → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → ∀ x : M,
      tower (Submission.Diff.lcOf (G 0)) (dR3 G t) j v A B C x
        = -(Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (j + 1) (Fin.snoc v A) B C x
            + Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (j + 1) (Fin.snoc v B) A C x
            - Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (j + 1) (Fin.snoc v C) A B x)) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.dAOfBase G t) k
            (fun i => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) x|
          ≤ Ck * (1 + Finset.sum (Finset.range (k + 1)) B)
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) :=
  dAOfTowerBoundShi_piece_of_inputs (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi
    k B hB hA
    (Work.Diff.EXT.ATower.fixedRicTowerBound (I := I) (M := M) hLC G T C hT hC hflow hbound
      hmet hShi k B hB hA)
    hswap


end Helpers

theorem dAOfTowerBoundShi_piece
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
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.dAOfBase G t) k
            (fun i => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) x|
          ≤ Ck * (1 + Finset.sum (Finset.range (k + 1)) B)
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) := by
  -- the smoothness of the base `Ric(G t)` on smooth fields: what the swapped tower identity
  -- `dR3_tower_eq_tower2_of_smF` needs (and what needs `[I.Boundaryless] [T2Space M]`)
  have hbase : ∀ t : ℝ, Work.Diff.EXT.ATower.SmF2
      (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) (G t)) := by
    intro t v A B hv hA hB
    have hcov : CovariantDerivative.ContMDiffCovariantDerivative
        (Submission.Diff.lcOf (G t)) (⊤ : ℕ∞) := (hLC (G t)).1.some
    have hfun : Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) (G t) v A B
        = Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) (G t)
            (Fin.elim0 : Fin 0 → TF (I := I) (M := M)) A B B := by
      funext y
      rfl
    rw [hfun]
    exact Work.Diff.EXT.ConnCov.RicTr.baseRic_sm (I := I) (M := M) (G t) hcov A B B hA hB hB
  exact dAOfTowerBoundShi_piece_of_swap (I := I) (M := M) hLC G T C hT hC hflow hbound hmet
    hShi k B hB hA
    (fun t j v A B C hv hA' hB' hC' x =>
      Work.Diff.EXT.ATower.dR3_tower_eq_tower2_of_smF (I := I) (M := M) G t (hbase t)
        j v A B C hv hA' hB' hC' x)

end Work.Diff.EXT.ATower
