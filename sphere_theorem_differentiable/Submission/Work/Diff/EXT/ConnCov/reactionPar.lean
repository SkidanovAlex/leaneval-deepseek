import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.ConnCov.dAOfBase_fixed_formula
import Submission.Work.Diff.EXT.ATower.DA3Defs
import Submission.Work.Diff.EXT.ATower.dR3_tower_eq_tower2
import Submission.Work.Diff.EXT.ConnCov.RicFlip.BaseRicSmA
import Submission.Work.Diff.EXT.ConnCov.htower_eq_tower2
import Submission.Work.Diff.EXT.ATower.dAOfTowerBoundShi_piece
import Submission.Work.Diff.EXT.ConnCov.RicTr.baseRic_sm
import Submission.Work.Diff.EXT.ATower.fixedRicTowerBound
import Submission.Work.Diff.EXT.ATower.highCountDef
import Submission.Work.Diff.EXT.ATower.deltaAtomAffineBndV

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The parametric reaction bound `reactionPar`

Target: `Work.Diff.EXT.ConnCov.reactionPar` --- the *parametric* bound for the frozen tower of the
reaction `∂_t aOf` along a Ricci flow, i.e. the estimate consumed by the Gronwall induction of
`Submission/Work/Diff/EXT/ConnCov/covKAExt_bound.lean`.

The proof has two halves:

* **the reduction** (`reaction_par_of_fix`): the reaction is (pointwise, on smooth fields) the Koszul
  combination `dR3` of `∇^{G 0}Ric(G t)` (`dAOfBase_eq_dR3`), and the `∇^{G 0}`-tower of
  `dR3` is the same combination of the fixed `(0,2)`-Ricci tower at level `k + 1`
  (`dR3_tower_eq_tower2`).  Hence the target follows from the bound `hFix` on the *honest*
  fixed-connection Ric tower at all levels `m ≤ k + 1`;
* **the crux** (`fixedRicTower2Bound_par'`): that honest tower bound.  It is proved with the
  two-connection flip calculus of `Submission/Work/Diff/EXT/ATower/fixedRicTowerBound.lean`
  (`term_bound_lt`, `bnd1_evalList`, `expandTail`), keeping the *linearity* in the level-`k`
  connection-difference bound `U`:
  + `highCountBound_l`: a term of cost `≤ k+1` contains at most one `δ`-insertion of order
    `≥ k`, so the product of the atom factors is `(1+U)`-linear;
  + `term_bound_par` / `tail_sum_par` / `majorant_par`: the explicit majorant `Cf n =
    A·D^(n+1)·(1+U)^[n = k+1]` satisfies the recursion of the induction;
  + the affine atom bounds (levels `< k` parameter free, level `k` affine in `U`) are supplied by
    `Work.Diff.EXT.ATower.deltaAtomAffineBndV`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Smoothness of `Ric(G t)` on smooth fields -/

/-- The `(0,2)`-Ricci tensor `baseRic2 g` is smooth on smooth fields. -/
theorem baseRic2_smF2 (g : Submission.Diff.SMet I M) [I.Boundaryless] [T2Space M]
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞)) :
    Work.Diff.EXT.ATower.SmF2 (baseRic2 (I := I) (M := M) g) := by
  intro w A B hw hA hB
  have hw0 : w = (Fin.elim0 : Fin 0 → (Π y : M, TangentSpace I y)) := Subsingleton.elim _ _
  subst hw0
  exact Work.Diff.EXT.ConnCov.RicTr.baseRic_sm (I := I) (M := M) g hcov A B B hA hB hB


/-! ## The two-element value tuple and the bridges -/

open Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- `htower` is `tower2` of `baseRic2`, for an *arbitrary* connection and an arbitrary metric in
the base (the two objects differ only by the dummy third value slot). -/
theorem htower_eq_tower2_cov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (g : Submission.Diff.SMet I M) (k : ℕ)
    (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y) (x : M) :
    Work.Diff.EXT.ConnCov.htower cov (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) k
        v A B C x
      = Work.Diff.EXT.ConnCov.tower2 cov
          (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) k v A B x := by
  have h := Work.Diff.EXT.ConnCov.htower_lift23k (I := I) (M := M) cov
    (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) k
  exact congrFun (congrFun (congrFun (congrFun (congrFun h v) A) B) C) x

/-- The two-element tuple of value fields of the honest Ric tower. -/
noncomputable def pairTup2 (A B : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    Fin 2 → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
  fun i => if (i : ℕ) = 0 then A else B

@[simp] theorem pairTup2_zero (A B : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    pairTup2 (I := I) (M := M) A B 0 = A := by
  rw [pairTup2]; exact if_pos rfl

@[simp] theorem pairTup2_one (A B : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    pairTup2 (I := I) (M := M) A B 1 = B := by
  rw [pairTup2]; exact if_neg (by decide)

/-- **The bridge** between the honest `(0,2)`-Ricci tower and the packed tower, in a form that uses
the explicit two-element tuple `pairTup2`. -/
theorem tower2_eq_pDiter2_bridge [I.Boundaryless] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (g : Submission.Diff.SMet I M) (m : ℕ)
    (v : Fin m → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (A B : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.ConnCov.tower2 cov (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) m v A B x
      = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 cov
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 g) m
          (Fin.append v (pairTup2 (I := I) (M := M) A B)
            : Fin (m + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) x :=
  Work.Diff.EXT.ATower.tower2_eq_pDiter2 (I := I) (M := M) cov g m v A B x


/-! ## The two-connection term calculus: the parametric constants -/

open Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- **The `highCount` bookkeeping**. -/
theorem highCountBound_l {R V W : ℕ → ℝ} {U : ℝ} {k : ℕ} (hU : 1 ≤ 1 + U)
    (hV0 : ∀ c, 0 ≤ V c) (hW0 : ∀ c, 0 ≤ W c) (hR0 : ∀ i, 0 ≤ R i)
    (hVW : ∀ c, 1 + V c ≤ (1 + U) ^ (if k ≤ c then 1 else 0) * (1 + W c)) :
    (∀ {n : ℕ} (T : Term n), Work.Diff.EXT.ATower.highCount k T * (k + 1) ≤ costT T) ∧
    (∀ {n : ℕ} (T : Term n),
      boundT R V T ≤ (1 + U) ^ (Work.Diff.EXT.ATower.highCount k T) * boundT R W T) := by
  constructor
  · intro n T
    induction T with
    | leaf i =>
        rw [show Work.Diff.EXT.ATower.highCount k (Term.leaf i) = 0 from rfl, costT_leaf,
          Nat.zero_mul]
        exact Nat.zero_le i
    | @comp a b ord Ψ T ih =>
        rw [show Work.Diff.EXT.ATower.highCount k (Term.comp Ψ T)
              = Work.Diff.EXT.ATower.highCount k T + (if k ≤ ord then 1 else 0) from rfl,
          costT_comp]
        by_cases h : k ≤ ord
        · rw [if_pos h]
          have harith : (Work.Diff.EXT.ATower.highCount k T + 1) * (k + 1)
              = Work.Diff.EXT.ATower.highCount k T * (k + 1) + (k + 1) := by ring
          rw [harith]
          exact Nat.add_le_add ih (Nat.succ_le_succ h)
        · rw [if_neg h]
          exact le_trans ih (Nat.le_add_right _ _)
  · intro n T
    induction T with
    | leaf i =>
        rw [show Work.Diff.EXT.ATower.highCount k (Term.leaf i) = 0 from rfl, boundT_leaf,
          boundT_leaf, pow_zero, one_mul]
    | @comp a b ord Ψ T ih =>
        rw [boundT_comp,
          show Work.Diff.EXT.ATower.highCount k (Term.comp Ψ T)
              = Work.Diff.EXT.ATower.highCount k T + (if k ≤ ord then 1 else 0) from rfl,
          pow_add]
        have hWnn : 0 ≤ boundT R W T := boundT_nonneg R W hR0 hW0 T
        have h1 : (0 : ℝ) ≤ (1 + U) ^ (Work.Diff.EXT.ATower.highCount k T) :=
          pow_nonneg (by linarith) _
        have h2 : (0 : ℝ) ≤ (1 + U) ^ (if k ≤ ord then 1 else 0) := pow_nonneg (by linarith) _
        have h3 := hVW ord
        calc boundT R V T * (1 + V ord)
            ≤ ((1 + U) ^ (Work.Diff.EXT.ATower.highCount k T) * boundT R W T)
                * ((1 + U) ^ (if k ≤ ord then 1 else 0) * (1 + W ord)) :=
              mul_le_mul ih h3 (by linarith [hV0 ord]) (mul_nonneg h1 hWnn)
          _ = (1 + U) ^ (Work.Diff.EXT.ATower.highCount k T)
                * (1 + U) ^ (if k ≤ ord then 1 else 0) * (boundT R W T * (1 + W ord)) := by ring

open Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- **The weighted term bound.** -/
theorem term_bound_par {k n : ℕ} (hn : n ≤ k + 1) (Cf Wt V : ℕ → ℝ) {U A D Msum : ℝ}
    (hU : 1 ≤ 1 + U) (hA0 : 0 ≤ A) (hD1 : 1 ≤ D) (hM0 : 0 ≤ Msum)
    (hV0 : ∀ c, 0 ≤ V c) (hWt0 : ∀ c, 0 ≤ Wt c) (hWtle : ∀ c, Wt c ≤ Msum)
    (hVW : ∀ c, 1 + V c ≤ (1 + U) ^ (if k ≤ c then 1 else 0) * (1 + Wt c))
    (hCf : ∀ j, Cf j = A * D ^ (j + 1) * (if j = k + 1 then 1 + U else 1)) :
    ∀ T ∈ Work.Diff.EXT.ATower.expandTail n,
      Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT Cf V T
        ≤ (1 + U) ^ (if n = k + 1 then 1 else 0) * (1 + Msum) ^ (k + 1) * (A * D ^ n) := by
  intro T hT
  have hCf0 : ∀ i, 0 ≤ Cf i := by
    intro i
    rw [hCf i]
    have h1 : 0 ≤ A * D ^ (i + 1) := mul_nonneg hA0 (pow_nonneg (le_trans zero_le_one hD1) _)
    split_ifs
    · exact mul_nonneg h1 (by linarith)
    · simpa using h1
  obtain ⟨hc1, hc2⟩ := highCountBound_l (R := Cf) (V := V) (W := Wt) (U := U) (k := k)
    hU hV0 hWt0 hCf0 hVW
  have hcost : Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T = n :=
    Work.Diff.EXT.ATower.costT_mem_expandTail n T hT
  have hlo : Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T < n :=
    Work.Diff.EXT.ATower.leafOrd_lt_of_mem_expandTail n T hT
  have hhc' : Work.Diff.EXT.ATower.highCount k T ≤ (if n = k + 1 then 1 else 0) := by
    have h := hc1 (T := T)
    rw [hcost] at h
    by_cases hn' : n = k + 1
    · rw [if_pos hn']
      have h1 : Work.Diff.EXT.ATower.highCount k T * (k + 1) ≤ 1 * (k + 1) := by
        rw [one_mul]; exact le_trans h (le_of_eq hn')
      exact Nat.le_of_mul_le_mul_right h1 (Nat.succ_pos k)
    · rw [if_neg hn']
      have hn'' : n ≤ k := by omega
      have hle : Work.Diff.EXT.ATower.highCount k T * (k + 1) ≤ k := le_trans h hn''
      by_contra hne
      have hpos : 1 ≤ Work.Diff.EXT.ATower.highCount k T :=
        Nat.one_le_iff_ne_zero.mpr (by omega)
      have h2 : k + 1 ≤ Work.Diff.EXT.ATower.highCount k T * (k + 1) := by
        calc k + 1 = 1 * (k + 1) := by ring
          _ ≤ Work.Diff.EXT.ATower.highCount k T * (k + 1) := Nat.mul_le_mul_right _ hpos
      omega
  have hexp : (1 + U) ^ Work.Diff.EXT.ATower.highCount k T
      ≤ (1 + U) ^ (if n = k + 1 then 1 else 0) := pow_le_pow_right₀ (by linarith) hhc'
  have hw := hc2 (T := T)
  have hb := Work.Diff.EXT.ATower.boundT_le (R := Cf) (V := Wt) (S := Msum) hM0 hWt0 hWtle
    hCf0 (T := T)
  have hleaf : Cf (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T) ≤ A * D ^ n := by
    have hb1 : Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T + 1 ≤ n := by omega
    have hne : Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T ≠ k + 1 := by omega
    rw [hCf, if_neg hne]
    have hdp : D ^ (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T + 1) ≤ D ^ n :=
      pow_le_pow_right₀ hD1 hb1
    calc A * D ^ (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T + 1) * 1
        = A * D ^ (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T + 1) := by ring
      _ ≤ A * D ^ n := mul_le_mul_of_nonneg_left hdp hA0
  have hX0 : (0 : ℝ) ≤ (1 + U) ^ (if n = k + 1 then 1 else 0) := pow_nonneg (by linarith) _
  have hY0 : (0 : ℝ) ≤ (1 + Msum) ^ (k + 1) := pow_nonneg (by linarith) _
  have hZ0 : (0 : ℝ) ≤ A * D ^ n := mul_nonneg hA0 (pow_nonneg (le_trans zero_le_one hD1) _)
  have hCn : 0 ≤ Cf (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T) := hCf0 _
  calc Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT Cf V T
      ≤ (1 + U) ^ Work.Diff.EXT.ATower.highCount k T
          * Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT Cf Wt T := hw
    _ ≤ (1 + U) ^ (if n = k + 1 then 1 else 0)
          * Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT Cf Wt T :=
        mul_le_mul_of_nonneg_right hexp
          (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT_nonneg Cf Wt hCf0 hWt0 T)
    _ ≤ (1 + U) ^ (if n = k + 1 then 1 else 0)
          * ((1 + Msum) ^ Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T
              * Cf (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T)) :=
        mul_le_mul_of_nonneg_left hb hX0
    _ ≤ (1 + U) ^ (if n = k + 1 then 1 else 0)
          * ((1 + Msum) ^ (k + 1) * (A * D ^ n)) := by
        refine mul_le_mul_of_nonneg_left ?_ hX0
        rw [hcost]
        refine mul_le_mul ?_ hleaf hCn (by positivity)
        exact pow_le_pow_right₀ (by linarith) hn
    _ = (1 + U) ^ (if n = k + 1 then 1 else 0) * (1 + Msum) ^ (k + 1) * (A * D ^ n) := by ring

open Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- **The bound of the whole tail at level `n`.** -/
theorem tail_sum_par {k n : ℕ} (hn : n ≤ k + 1) (Cf Wt V : ℕ → ℝ) {U A D Msum : ℝ}
    (hU : 1 ≤ 1 + U) (hA0 : 0 ≤ A) (hD1 : 1 ≤ D) (hM0 : 0 ≤ Msum)
    (hV0 : ∀ c, 0 ≤ V c) (hWt0 : ∀ c, 0 ≤ Wt c) (hWtle : ∀ c, Wt c ≤ Msum)
    (hVW : ∀ c, 1 + V c ≤ (1 + U) ^ (if k ≤ c then 1 else 0) * (1 + Wt c))
    (hCf : ∀ j, Cf j = A * D ^ (j + 1) * (if j = k + 1 then 1 + U else 1)) :
    ((Work.Diff.EXT.ATower.expandTail n).map (fun T => boundT Cf V T)).sum
      ≤ (Work.Diff.EXT.ATower.cstLen k : ℝ) * ((1 + U) ^ (if n = k + 1 then 1 else 0)
          * (1 + Msum) ^ (k + 1) * (A * D ^ n)) := by
  have hX0 : (0 : ℝ) ≤ (1 + U) ^ (if n = k + 1 then 1 else 0) := pow_nonneg (by linarith) _
  have hY0 : (0 : ℝ) ≤ (1 + Msum) ^ (k + 1) := pow_nonneg (by linarith) _
  have hZ0 : (0 : ℝ) ≤ A * D ^ n := mul_nonneg hA0 (pow_nonneg (le_trans zero_le_one hD1) _)
  have h0 : 0 ≤ (1 + U) ^ (if n = k + 1 then 1 else 0) * (1 + Msum) ^ (k + 1) * (A * D ^ n) :=
    mul_nonneg (mul_nonneg hX0 hY0) hZ0
  have h1 : ((Work.Diff.EXT.ATower.expandTail n).map (fun T => boundT Cf V T)).sum
      ≤ ((Work.Diff.EXT.ATower.expandTail n).map (fun _ =>
          (1 + U) ^ (if n = k + 1 then 1 else 0) * (1 + Msum) ^ (k + 1) * (A * D ^ n))).sum :=
    List.sum_le_sum (fun T hT => term_bound_par hn Cf Wt V hU hA0 hD1 hM0 hV0 hWt0 hWtle hVW hCf T hT)
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul] at h1
  refine le_trans h1 ?_
  rw [Work.Diff.EXT.ATower.cstLen]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Work.Diff.EXT.ATower.cstLen_ge hn) h0

open Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- **The majorant inequality** of the induction at level `n`. -/
theorem majorant_par {k n : ℕ} (hn : n ≤ k + 1) (Cf : ℕ → ℝ) {U Rmn A D Msum : ℝ}
    (hU : 1 ≤ 1 + U) (hA0 : 0 ≤ A) (hD1 : 1 ≤ D) (hM0 : 0 ≤ Msum)
    (hDge : 1 + (Work.Diff.EXT.ATower.cstLen k : ℝ) * (1 + Msum) ^ (k + 1) ≤ D)
    (hRmn : Rmn ≤ A)
    (hCf : ∀ j, Cf j = A * D ^ (j + 1) * (if j = k + 1 then 1 + U else 1)) :
    Rmn + (Work.Diff.EXT.ATower.cstLen k : ℝ)
        * ((1 + U) ^ (if n = k + 1 then 1 else 0) * (1 + Msum) ^ (k + 1) * (A * D ^ n))
      ≤ Cf n := by
  have hX0 : (0 : ℝ) ≤ (1 + U) ^ (if n = k + 1 then 1 else 0) := pow_nonneg (by linarith) _
  have hY0 : (0 : ℝ) ≤ (1 + Msum) ^ (k + 1) := pow_nonneg (by linarith) _
  have hZ0 : (0 : ℝ) ≤ A * D ^ n := mul_nonneg hA0 (pow_nonneg (le_trans zero_le_one hD1) _)
  have hD0 : 0 ≤ D - 1 := by linarith
  have hkey : (Work.Diff.EXT.ATower.cstLen k : ℝ) * (1 + Msum) ^ (k + 1) ≤ D - 1 := by linarith
  have hun1 : (1 : ℝ) ≤ 1 + U := by linarith
  have hDn1 : (1 : ℝ) ≤ D ^ n := one_le_pow₀ hD1
  rw [hCf n]
  by_cases hn' : n = k + 1
  · simp only [if_pos hn', pow_one]
    have hstep1 : Rmn ≤ (1 + U) * (A * D ^ n) := by
      calc Rmn ≤ A := hRmn
        _ ≤ A * (1 + U) := le_mul_of_one_le_right hA0 hun1
        _ = (1 + U) * A := by ring
        _ ≤ (1 + U) * (A * D ^ n) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc A = A * 1 := (mul_one A).symm
              _ ≤ A * D ^ n := mul_le_mul_of_nonneg_left hDn1 hA0
    have hstep2 : (Work.Diff.EXT.ATower.cstLen k : ℝ)
          * ((1 + U) * (1 + Msum) ^ (k + 1) * (A * D ^ n))
        ≤ (D - 1) * ((1 + U) * (A * D ^ n)) := by
      calc (Work.Diff.EXT.ATower.cstLen k : ℝ)
            * ((1 + U) * (1 + Msum) ^ (k + 1) * (A * D ^ n))
          = ((Work.Diff.EXT.ATower.cstLen k : ℝ) * (1 + Msum) ^ (k + 1))
              * ((1 + U) * (A * D ^ n)) := by ring
        _ ≤ (D - 1) * ((1 + U) * (A * D ^ n)) :=
            mul_le_mul_of_nonneg_right hkey (mul_nonneg (by positivity) hZ0)
    have e3 : A * D ^ (n + 1) * (1 + U)
        = (1 + U) * (A * D ^ n) + (D - 1) * ((1 + U) * (A * D ^ n)) := by
      rw [pow_succ]; ring
    calc Rmn + (Work.Diff.EXT.ATower.cstLen k : ℝ)
          * ((1 + U) * (1 + Msum) ^ (k + 1) * (A * D ^ n))
        ≤ (1 + U) * (A * D ^ n) + (D - 1) * ((1 + U) * (A * D ^ n)) :=
          add_le_add hstep1 hstep2
      _ = A * D ^ (n + 1) * (1 + U) := e3.symm
  · simp only [if_neg hn', pow_zero, one_mul, mul_one]
    have hstep1 : Rmn ≤ A * D ^ n := by
      calc Rmn ≤ A := hRmn
        _ = A * 1 := (mul_one A).symm
        _ ≤ A * D ^ n := mul_le_mul_of_nonneg_left hDn1 hA0
    have hstep2 : (Work.Diff.EXT.ATower.cstLen k : ℝ) * ((1 + Msum) ^ (k + 1) * (A * D ^ n))
        ≤ (D - 1) * (A * D ^ n) := by
      calc (Work.Diff.EXT.ATower.cstLen k : ℝ) * ((1 + Msum) ^ (k + 1) * (A * D ^ n))
          = ((Work.Diff.EXT.ATower.cstLen k : ℝ) * (1 + Msum) ^ (k + 1)) * (A * D ^ n) := by ring
        _ ≤ (D - 1) * (A * D ^ n) := mul_le_mul_of_nonneg_right hkey hZ0
    have e3 : A * D ^ (n + 1) = A * D ^ n + (D - 1) * (A * D ^ n) := by
      rw [pow_succ]; ring
    calc Rmn + (Work.Diff.EXT.ATower.cstLen k : ℝ) * ((1 + Msum) ^ (k + 1) * (A * D ^ n))
        ≤ A * D ^ n + (D - 1) * (A * D ^ n) := add_le_add hstep1 hstep2
      _ = A * D ^ (n + 1) := e3.symm


open Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- **The parametric `Bnd1` bound for the fixed honest Ric tower** at the levels `m ≤ k+1`, from
the affine atom bounds `hatom`. -/
theorem ricTowerBnd1_par
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
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j))
    (hatom : ∃ (W : ℕ → ℝ) (A Cu : ℝ), (∀ c, 0 ≤ W c) ∧ 0 ≤ A ∧ 0 ≤ Cu ∧
      (∀ c, c < k → ∀ t ∈ Set.Ico (T / 2) T,
        Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t
          (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
            (fun s : ℝ => G (t - s)) t c) (W c)) ∧
      (∀ t ∈ Set.Ico (T / 2) T, ∀ ρ : ℝ, 0 ≤ ρ →
        Work.Diff.EXT.ATower.ValBound G t k
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G t) k) ρ →
        Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t
          (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
            (fun s : ℝ => G (t - s)) t k) (A + Cu * ρ))) :
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
      Work.Diff.EXT.ATower.ValBound G t k
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) k) U →
      ∀ m : ℕ, m ≤ k + 1 →
        Work.Diff.EXT.ConnCov.AMB.Bnd1 (I := I) (M := M) (fun _ : ℝ => G 0) t
          (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m)
          (Ch * (1 + Finset.sum (Finset.range k) B + U)) := by
  classical
  obtain ⟨W, A₀, Cu, hW0, hA₀0, hCu0, hWb, hAtop⟩ := hatom
  obtain ⟨R, hR0, hR⟩ := Work.Diff.EXT.ATower.movingRicTowerBnd1 (I := I) (M := M) hLC G T C
    hT hC hflow hbound hmet hShi (k + 1)
  set Kc : ℝ := Real.exp ((Module.finrank ℝ E : ℝ) * C * T) with hKc
  have hKc1 : 1 ≤ Kc := by rw [hKc]; exact Real.one_le_exp (by positivity)
  have hKc0 : 0 ≤ Kc := le_trans zero_le_one hKc1
  set Wt : ℕ → ℝ := fun c => if c < k then W c else if c = k then A₀ + Cu else 0 with hWt
  have hWt0 : ∀ c, 0 ≤ Wt c := by
    intro c
    simp only [hWt]
    split_ifs with h1 h2
    · exact hW0 c
    · exact add_nonneg hA₀0 hCu0
    · exact le_refl 0
  set Msum : ℝ := ∑ c ∈ Finset.range (k + 1), Wt c with hMsum
  have hMsum0 : 0 ≤ Msum := Finset.sum_nonneg (fun c _ => hWt0 c)
  have hWtle : ∀ c, Wt c ≤ Msum := by
    intro c
    by_cases hc : c ≤ k
    · rw [hMsum]
      exact Finset.single_le_sum (f := Wt) (fun i _ => hWt0 i)
        (Finset.mem_range.mpr (by omega))
    · have hcz : Wt c = 0 := by
        simp only [hWt]; rw [if_neg (by omega), if_neg (by omega)]
      rw [hcz]; exact hMsum0
  set A : ℝ := ∑ m ∈ Finset.range (k + 2), R m * (1 + Kc) ^ (m + 2) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (hR0 m) (pow_nonneg (by linarith) _))
  set D : ℝ := 1 + (Work.Diff.EXT.ATower.cstLen k : ℝ) * (1 + Msum) ^ (k + 1) with hDdef
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    have h1 : 0 ≤ (Work.Diff.EXT.ATower.cstLen k : ℝ) * (1 + Msum) ^ (k + 1) := by positivity
    linarith
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  refine ⟨A * D ^ (k + 2), by positivity, ?_⟩
  intro t ht U hU hUk m hm
  set V : ℕ → ℝ := fun c => if c < k then W c else if c = k then A₀ + Cu * U else 0 with hVdef
  have hV0 : ∀ c, 0 ≤ V c := by
    intro c
    simp only [hVdef]
    split_ifs with h1 h2
    · exact hW0 c
    · exact add_nonneg hA₀0 (mul_nonneg hCu0 hU)
    · exact le_refl 0
  have hVW : ∀ c, 1 + V c ≤ (1 + U) ^ (if k ≤ c then 1 else 0) * (1 + Wt c) := by
    intro c
    rcases lt_trichotomy c k with hlt | heq | hgt
    · have hVc : V c = W c := by
        simp only [hVdef]; rw [if_pos hlt]
      have hWc : Wt c = W c := by
        simp only [hWt]; rw [if_pos hlt]
      have hk : (if k ≤ c then (1 : ℕ) else 0) = 0 := if_neg (by omega)
      rw [hVc, hWc, hk, pow_zero, one_mul]
    · rw [heq]
      have hVc : V k = A₀ + Cu * U := by
        simp only [hVdef]
        rw [if_neg (lt_irrefl k)]
        exact if_pos trivial
      have hWc : Wt k = A₀ + Cu := by
        simp only [hWt]
        rw [if_neg (lt_irrefl k)]
        exact if_pos trivial
      have hk : (if k ≤ k then (1 : ℕ) else 0) = 1 := if_pos le_rfl
      rw [hVc, hWc, hk, pow_one]
      nlinarith [hA₀0, hCu0, hU]
    · have hVc : V c = 0 := by
        simp only [hVdef]
        rw [if_neg (by omega), if_neg (by omega)]
      have hWc : Wt c = 0 := by
        simp only [hWt]
        rw [if_neg (by omega), if_neg (by omega)]
      have hk : (if k ≤ c then (1 : ℕ) else 0) = 1 := if_pos (le_of_lt hgt)
      rw [hVc, hWc, hk, pow_one]
      linarith [hU]
  set Cf : ℕ → ℝ := fun n => A * D ^ (n + 1) * (if n = k + 1 then 1 + U else 1) with hCfdef
  have hCf : ∀ j, Cf j = A * D ^ (j + 1) * (if j = k + 1 then 1 + U else 1) := fun j => rfl
  have hCf0 : ∀ j, 0 ≤ Cf j := by
    intro j
    rw [hCf j]
    have h1 : 0 ≤ A * D ^ (j + 1) := mul_nonneg hA0 (pow_nonneg hD0 _)
    split_ifs
    · exact mul_nonneg h1 (by linarith)
    · simpa using h1
  have hmov : ∀ n ≤ k + 1, Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G 0) t
      (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n)
      (R n * (1 + Kc) ^ (n + 2)) := by
    intro n hn
    have h1 : Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G t) t
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n) (R n) := hR n hn t ht
    refine Work.Diff.EXT.ATower.bnd1_of_metric_le (I := I) (M := M) (g₁ := G t) (g₂ := G 0)
      (K := Kc) hKc0 ?_ (hR0 n) h1
    intro y u
    rw [hKc]
    exact Work.Diff.EXT.ATower.sqrt_inner_Gt_le (I := I) (M := M) G T C hmet hC hT ht y u
  have main : ∀ n ≤ k + 1, Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G 0) t
      (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n) (Cf n) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn
    intro F x hF
    set Ĝ : ℝ → Submission.Diff.SMet I M := fun s => G (t - s) with hĜ
    have hĜ0 : Ĝ 0 = G t := by rw [hĜ]; simp
    have hĜt : Ĝ t = G 0 := by rw [hĜ]; simp
    have hbaseadd : Work.Diff.EXT.ConnCov.AMB.SlotAddP
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) :=
      Work.Diff.EXT.ConnCov.RicFlip.ric2_slotAddP (I := I) (M := M) hLC (G t)
    have hbasesm : Work.Diff.EXT.ConnCov.AMB.SmP (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) :=
      Work.Diff.EXT.ConnCov.RicFlip.ric2_smP (I := I) (M := M) hLC (G t)
    have hsmT : ∀ {mm : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term mm),
        Work.Diff.EXT.ConnCov.AMB.SmP (Work.Diff.EXT.ConnCov.RicFlip.evalT Ĝ t
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) T) :=
      fun T => (Work.Diff.EXT.ATower.evalT_good' (I := I) (M := M) hLC Ĝ t
        hbaseadd hbasesm T).2
    have hslot : ∀ {mm : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term mm),
        Work.Diff.EXT.ConnCov.AMB.SlotAddP (Work.Diff.EXT.ConnCov.RicFlip.evalT Ĝ t
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) T) :=
      fun T => (Work.Diff.EXT.ATower.evalT_good' (I := I) (M := M) hLC Ĝ t
        hbaseadd hbasesm T).1
    have hexp := congrFun (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.expand_correct (I := I)
      (M := M) hLC Ĝ t (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) hsmT hslot n F hF) x
    rw [hĜ0] at hexp
    rw [Work.Diff.EXT.ATower.Expand_eq_leaf_cons,
      Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.evalList_cons] at hexp
    have hleafval : Work.Diff.EXT.ConnCov.RicFlip.evalT Ĝ t
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
          (Work.Diff.EXT.ConnCov.RicFlip.Term.leaf n) F x
        = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x := by
      change Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (Ĝ t))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x
        = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x
      rw [hĜt]
    rw [hleafval] at hexp
    have hfix : Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x
        = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x
          - Work.Diff.EXT.ConnCov.RicFlip.evalList Ĝ t
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
              (Work.Diff.EXT.ATower.expandTail n) F x := by
      linarith [hexp]
    have hcorr : Work.Diff.EXT.ConnCov.AMB.Bnd1 Ĝ t
        (Work.Diff.EXT.ConnCov.RicFlip.evalList Ĝ t
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
          (Work.Diff.EXT.ATower.expandTail n))
        ((Work.Diff.EXT.ATower.expandTail n).map
          (fun T => Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT Cf V T)).sum := by
      refine Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.bnd1_evalList (I := I) (M := M) Ĝ t
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) (Work.Diff.EXT.ATower.expandTail n)
        (fun T => Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT Cf V T) ?_
      intro T hT
      have hcost : Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T ≤ n :=
        le_of_eq (Work.Diff.EXT.ATower.costT_mem_expandTail n T hT)
      have hlo : Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T < n :=
        Work.Diff.EXT.ATower.leafOrd_lt_of_mem_expandTail n T hT
      refine Work.Diff.EXT.ATower.term_bound_lt (I := I) (M := M) hLC Ĝ t
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) Cf V n hCf0 hV0 ?_ ?_ T hcost hlo
      · intro j hj
        have hij := ih j hj (by omega)
        have h1 := (Work.Diff.EXT.ATower.bnd1_fam_congr (I := I) (M := M)
          (G₁ := fun _ : ℝ => G 0) (G₂ := Ĝ) (by rw [hĜt])).mp hij
        rw [hĜt]
        exact h1
      · intro ord ho
        have h1 : Work.Diff.EXT.ConnCov.AMB.BndV (fun _ : ℝ => G 0) t
            (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (fun s : ℝ => G (t - s)) t ord)
            (V ord) := by
          by_cases hk : ord < k
          · have hVord : V ord = W ord := by
              simp only [hVdef]; rw [if_pos hk]
            rw [hVord]
            exact hWb ord hk t ht
          · have hok : ord = k := by omega
            rw [hok]
            have hVk : V k = A₀ + Cu * U := by
              simp only [hVdef]
              rw [if_neg (lt_irrefl k)]
              exact if_pos trivial
            rw [hVk]
            exact hAtop t ht U hU hUk
        exact (Work.Diff.EXT.ATower.bndV_fam_congr (I := I) (M := M)
          (G₁ := fun _ : ℝ => G 0) (G₂ := Ĝ) (by rw [hĜt])).mp h1
    have hcorr' : Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G 0) t
        (Work.Diff.EXT.ConnCov.RicFlip.evalList Ĝ t
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
          (Work.Diff.EXT.ATower.expandTail n))
        ((Work.Diff.EXT.ATower.expandTail n).map
          (fun T => Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT Cf V T)).sum :=
      (Work.Diff.EXT.ATower.bnd1_fam_congr (I := I) (M := M) (G₁ := Ĝ)
        (G₂ := fun _ : ℝ => G 0) (by rw [hĜt])).mp hcorr
    have hP0 : (0 : ℝ) ≤ ∏ j : Fin (n + 2),
        (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) :=
      Finset.prod_nonneg (fun j _ => by
        have h := Real.sqrt_nonneg ((G 0).inner x (F j x) (F j x)); linarith)
    have hm := hmov n hn F x hF
    have hc := hcorr' F x hF
    have hs := tail_sum_par (k := k) (n := n) hn Cf Wt V (U := U) (A := A) (D := D)
      (Msum := Msum) (by linarith : (1:ℝ) ≤ 1 + U) hA0 hD1 hMsum0 hV0 hWt0 hWtle hVW hCf
    have hRmn : R n * (1 + Kc) ^ (n + 2) ≤ A := by
      rw [hAdef]
      exact Finset.single_le_sum (f := fun m => R m * (1 + Kc) ^ (m + 2))
        (fun m _ => mul_nonneg (hR0 m) (pow_nonneg (by linarith) _))
        (Finset.mem_range.mpr (by omega))
    have hci := majorant_par (k := k) (n := n) hn Cf (U := U)
      (Rmn := R n * (1 + Kc) ^ (n + 2)) (A := A) (D := D) (Msum := Msum)
      (by linarith : (1:ℝ) ≤ 1 + U) hA0 hD1 hMsum0
      (le_of_eq hDdef.symm) hRmn hCf
    have habs : |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x
          - Work.Diff.EXT.ConnCov.RicFlip.evalList Ĝ t
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
              (Work.Diff.EXT.ATower.expandTail n) F x|
        ≤ |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x|
          + |Work.Diff.EXT.ConnCov.RicFlip.evalList Ĝ t
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
              (Work.Diff.EXT.ATower.expandTail n) F x| := by
      have h := abs_add_le (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x)
        (-(Work.Diff.EXT.ConnCov.RicFlip.evalList Ĝ t
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
          (Work.Diff.EXT.ATower.expandTail n) F x))
      simpa [sub_eq_add_neg] using h
    calc |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x|
        = |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x
            - Work.Diff.EXT.ConnCov.RicFlip.evalList Ĝ t
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
              (Work.Diff.EXT.ATower.expandTail n) F x| := by rw [hfix]
      _ ≤ |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n F x|
            + |Work.Diff.EXT.ConnCov.RicFlip.evalList Ĝ t
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t))
              (Work.Diff.EXT.ATower.expandTail n) F x| := habs
      _ ≤ R n * (1 + Kc) ^ (n + 2)
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x)))
            + ((Work.Diff.EXT.ATower.expandTail n).map
                (fun T => Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT Cf V T)).sum
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) :=
          add_le_add hm hc
      _ ≤ R n * (1 + Kc) ^ (n + 2)
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x)))
            + ((Work.Diff.EXT.ATower.cstLen k : ℝ) * ((1 + U) ^ (if n = k + 1 then 1 else 0)
                * (1 + Msum) ^ (k + 1) * (A * D ^ n)))
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hs hP0)
      _ = (R n * (1 + Kc) ^ (n + 2) + (Work.Diff.EXT.ATower.cstLen k : ℝ)
              * ((1 + U) ^ (if n = k + 1 then 1 else 0) * (1 + Msum) ^ (k + 1) * (A * D ^ n)))
            * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) := by ring
      _ ≤ Cf n * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) :=
          mul_le_mul_of_nonneg_right hci hP0
  have hBnn : (0 : ℝ) ≤ Finset.sum (Finset.range k) B := Finset.sum_nonneg (fun j _ => hB j)
  have h3 : (0 : ℝ) ≤ 1 + Finset.sum (Finset.range k) B + U := by linarith
  have hle : Cf m ≤ (A * D ^ (k + 2)) * (1 + Finset.sum (Finset.range k) B + U) := by
    rw [hCf]
    have hbase : (1 : ℝ) ≤ 1 + Finset.sum (Finset.range k) B + U := by linarith
    have hDm : D ^ (m + 1) ≤ D ^ (k + 2) := pow_le_pow_right₀ hD1 (by omega)
    have hif : (if m = k + 1 then 1 + U else 1) ≤ 1 + Finset.sum (Finset.range k) B + U := by
      by_cases hm' : m = k + 1
      · rw [if_pos hm']; linarith
      · rw [if_neg hm']; linarith
    have h1 : A * D ^ (m + 1) ≤ A * D ^ (k + 2) := mul_le_mul_of_nonneg_left hDm hA0
    have h2 : (0 : ℝ) ≤ if m = k + 1 then 1 + U else 1 := by
      by_cases hm' : m = k + 1
      · rw [if_pos hm']; linarith
      · rw [if_neg hm']; norm_num
    have hCnst : (0 : ℝ) ≤ A * D ^ (k + 2) := mul_nonneg hA0 (pow_nonneg hD0 _)
    calc A * D ^ (m + 1) * (if m = k + 1 then 1 + U else 1)
        ≤ A * D ^ (k + 2) * (1 + Finset.sum (Finset.range k) B + U) :=
          mul_le_mul h1 hif h2 hCnst
      _ = (A * D ^ (k + 2)) * (1 + Finset.sum (Finset.range k) B + U) := by ring
  exact Work.Diff.EXT.ConnCov.AMB.Bnd1_mono_const (hCf0 m) (main m hm) hle


open Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- **The crux**: the sharp parametric bound for the honest fixed-connection Ric tower. -/
theorem fixedRicTower2Bound_par'
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
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
      Work.Diff.EXT.ATower.ValBound G t k
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) k) U →
      ∀ m : ℕ, m ≤ k + 1 → ∀ x : M,
        ∀ (w : Fin m → TangentSpace I x) (a b c : TangentSpace I x),
          |Work.Diff.EXT.ATower.valOp
              (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G 0))
                (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x w a b c|
            ≤ Ch * (1 + Finset.sum (Finset.range k) B + U)
                * (Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (w i) (w i)))
                    * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)) := by
  classical
  have hatom : ∃ (W : ℕ → ℝ) (A Cu : ℝ), (∀ c, 0 ≤ W c) ∧ 0 ≤ A ∧ 0 ≤ Cu ∧
      (∀ c, c < k → ∀ t ∈ Set.Ico (T / 2) T,
        Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t
          (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
            (fun s : ℝ => G (t - s)) t c) (W c)) ∧
      (∀ t ∈ Set.Ico (T / 2) T, ∀ ρ : ℝ, 0 ≤ ρ →
        Work.Diff.EXT.ATower.ValBound G t k
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G t) k) ρ →
        Work.Diff.EXT.ConnCov.AMB.BndV (I := I) (M := M) (fun _ : ℝ => G 0) t
          (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (I := I) (M := M)
            (fun s : ℝ => G (t - s)) t k) (A + Cu * ρ)) := by
    exact Work.Diff.EXT.ATower.deltaAtomAffineBndV (I := I) (M := M) hLC (G := G) (T := T)
      hT C hC hmet k B hB hA
  obtain ⟨Ch, hCh0, hBnd⟩ := ricTowerBnd1_par (I := I) (M := M) hLC G T C hT hC hflow hbound hmet
    hShi k B hB hA hatom
  set Kc : ℝ := Real.exp ((Module.finrank ℝ E : ℝ) * C * T) with hKc
  have hKc1 : 1 ≤ Kc := by rw [hKc]; exact Real.one_le_exp (by positivity)
  have hKc0 : 0 ≤ Kc := le_trans zero_le_one hKc1
  have hKc3 : (0 : ℝ) ≤ (1 + Kc) ^ (k + 3) := pow_nonneg (by linarith) _
  refine ⟨Ch * (1 + Kc) ^ (k + 3), mul_nonneg hCh0 hKc3, ?_⟩
  intro t ht U hU hUk m hm x w a b c
  have hBsum : (0 : ℝ) ≤ Finset.sum (Finset.range k) B := Finset.sum_nonneg (fun j _ => hB j)
  have h1Kc : (0 : ℝ) ≤ 1 + Kc := by linarith
  have hCnn : (0 : ℝ) ≤ Ch * (1 + Finset.sum (Finset.range k) B + U) :=
    mul_nonneg hCh0 (by linarith)
  have hBnd1 := hBnd t ht U hU hUk m hm
  have h1 : Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G t) t
      (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m)
      ((Ch * (1 + Finset.sum (Finset.range k) B + U)) * (1 + Kc) ^ (m + 2)) := by
    refine Work.Diff.EXT.ATower.bnd1_of_metric_le (I := I) (M := M) (g₁ := G 0) (g₂ := G t)
      (K := Kc) hKc0 ?_ hCnn hBnd1
    intro y u
    rw [hKc]
    exact Work.Diff.EXT.ATower.sqrt_inner_G0_le (I := I) (M := M) G T C hmet hC hT ht y u
  have hhom : ∀ (r : ℝ) (F : Fin (m + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
      (y : M),
      Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m (fun j => r • F j) y
        = r ^ (m + 2) * Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m F y := by
    intro r F y
    have h := Work.Diff.EXT.ATower.hom_pDiter2 (I := I) (M := M) hLC (G 0) (G t) m
      (fun _ : Fin (m + 2) => r) F y
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    exact h
  set wf : Fin m → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
    fun i => Submission.Diff.smoothExt x (w i) with hwf
  set g : Fin 2 → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
    pairTup2 (I := I) (M := M) (Submission.Diff.smoothExt x a)
      (Submission.Diff.smoothExt x b) with hg
  have hwfsm : ∀ i, SmE I M (wf i) := fun i => Work.Diff.GE.smoothExt_cmdiff x (w i)
  have hgsm : ∀ i, SmE I M (g i) := by
    intro i
    rw [hg]
    simp only [pairTup2]
    split_ifs
    · exact Work.Diff.GE.smoothExt_cmdiff x a
    · exact Work.Diff.GE.smoothExt_cmdiff x b
  have hFsm : ∀ j, SmE I M (Fin.append wf g j) :=
    Fin.addCases (motive := fun j => SmE I M (Fin.append wf g j))
      (fun i => by rw [Fin.append_left]; exact hwfsm i)
      (fun i => by rw [Fin.append_right]; exact hgsm i)
  have hval : Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ConnCov.htower
        (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x w a b c
      = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m (Fin.append wf g) x := by
    have e1 : Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ConnCov.htower
          (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x w a b c
        = Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) m (fun i => Submission.Diff.smoothExt x (w i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b) x := by
      rw [Work.Diff.EXT.ATower.valOp,
        htower_eq_tower2_cov (I := I) (M := M) (Submission.Diff.lcOf (G 0)) (G t) m]
    have e2 : Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) m wf (Submission.Diff.smoothExt x a)
          (Submission.Diff.smoothExt x b) x
        = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m (Fin.append wf g) x := by
      rw [tower2_eq_pDiter2_bridge (I := I) (M := M) (Submission.Diff.lcOf (G 0)) (G t) m wf
        (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b) x, ← hg]
    rw [e1, ← hwf]
    exact e2
  have hsharp := Work.Diff.EXT.ConnCov.sharp_of_bnd1_homog (I := I) (M := M)
    (G := fun _ : ℝ => G t) t (Work.Diff.EXT.ConnCov.RicFlip.pDiter2
      (Submission.Diff.lcOf (G 0)) (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m)
    (mul_nonneg hCnn (pow_nonneg h1Kc _)) h1 hhom (Fin.append wf g) x hFsm
  have hprod : (∏ j : Fin (m + 2), Real.sqrt ((G t).inner x ((Fin.append wf g) j x)
        ((Fin.append wf g) j x)))
      = (Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (w i) (w i))))
        * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
    have e1 : (∏ i : Fin m, Real.sqrt ((G t).inner x
          ((Fin.append wf g) (Fin.castAdd 2 i) x) ((Fin.append wf g) (Fin.castAdd 2 i) x)))
        = ∏ i : Fin m, Real.sqrt ((G t).inner x (w i) (w i)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Fin.append_left wf g i]
      simp only [hwf, Work.Diff.GE.smoothExt_apply]
    have e2 : (∏ i : Fin 2, Real.sqrt ((G t).inner x
          ((Fin.append wf g) (Fin.natAdd m i) x) ((Fin.append wf g) (Fin.natAdd m i) x)))
        = Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
      rw [Fin.prod_univ_two]
      simp only [Fin.append_right, hg, pairTup2_zero, pairTup2_one,
        Work.Diff.GE.smoothExt_apply]
    rw [Fin.prod_univ_add (a := m) (b := 2) (fun j : Fin (m + 2) =>
      Real.sqrt ((G t).inner x ((Fin.append wf g) j x) ((Fin.append wf g) j x))), e1, e2]
    ring
  rw [hval]
  refine le_trans hsharp ?_
  rw [hprod]
  have hPnn : (0 : ℝ) ≤ Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (w i) (w i)))
      * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
    refine mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ hPnn
  have hc1 : (1 + Kc) ^ (m + 2) ≤ (1 + Kc) ^ (k + 3) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  calc (Ch * (1 + Finset.sum (Finset.range k) B + U)) * (1 + Kc) ^ (m + 2)
      ≤ (Ch * (1 + Finset.sum (Finset.range k) B + U)) * (1 + Kc) ^ (k + 3) :=
        mul_le_mul_of_nonneg_left hc1 hCnn
    _ = (Ch * (1 + Kc) ^ (k + 3)) * (1 + Finset.sum (Finset.range k) B + U) := by ring

theorem reaction_par_of_fix
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
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j))
    (hFix : ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
      Work.Diff.EXT.ATower.ValBound G t k
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) k) U →
      ∀ m : ℕ, m ≤ k + 1 → ∀ x : M,
        ∀ (w : Fin m → TangentSpace I x) (a b c : TangentSpace I x),
          |Work.Diff.EXT.ATower.valOp
              (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G 0))
                (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x w a b c|
            ≤ Ch * (1 + Finset.sum (Finset.range k) B + U)
                * (Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (w i) (w i)))
                    * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b))) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
      Work.Diff.EXT.ATower.ValBound G t k
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) k) U →
      ∀ x : M, ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.dAOfBase G t) k) x v a b c|
          ≤ Cd * (1 + Finset.sum (Finset.range k) B + U)
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
                  * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
                  * Real.sqrt ((G t).inner x c c)) := by
  obtain ⟨Ch, hCh0, hFix⟩ := hFix
  refine ⟨3 * Ch, by linarith, fun t ht U hU hAk x v a b c => ?_⟩
  have ht' : t ∈ Set.Ioo 0 T := ⟨by linarith [hT, ht.1], ht.2⟩
  have hv : ∀ i : Fin k, SmE I M (fun y => Submission.Diff.smoothExt x (v i) y) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x (v i)
  have ha : SmE I M (fun y => Submission.Diff.smoothExt x a y) :=
    Work.Diff.GE.smoothExt_cmdiff x a
  have hb : SmE I M (fun y => Submission.Diff.smoothExt x b y) :=
    Work.Diff.GE.smoothExt_cmdiff x b
  have hc : SmE I M (fun y => Submission.Diff.smoothExt x c y) :=
    Work.Diff.GE.smoothExt_cmdiff x c
  -- the bound of one level-`(k+1)` honest Ric tower term
  have hterm : ∀ (A P Q : TangentSpace I x),
      |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
          (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x A))
          (Submission.Diff.smoothExt x P) (Submission.Diff.smoothExt x Q) x|
        ≤ Ch * (1 + Finset.sum (Finset.range k) B + U)
            * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
                * Real.sqrt ((G t).inner x A A) * Real.sqrt ((G t).inner x P P)
                * Real.sqrt ((G t).inner x Q Q)) := by
    intro A P Q
    have hval := hFix t ht U hU hAk (k + 1) le_rfl x (Fin.snoc v A) P Q P
    have hL : Work.Diff.EXT.ATower.valOp
        (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic (G t)) (k + 1)) x (Fin.snoc v A) P Q P
        = Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
            (fun j : Fin (k + 1) => Submission.Diff.smoothExt x
              ((Fin.snoc (α := fun _ : Fin (k + 1) => TangentSpace I x) v A) j))
            (Submission.Diff.smoothExt x P) (Submission.Diff.smoothExt x Q) x := by
      simp only [Work.Diff.EXT.ATower.valOp]
      rw [htower_eq_tower2_cov (I := I) (M := M) (Submission.Diff.lcOf (G 0)) (G t) (k + 1)]
    rw [hL] at hval
    rw [← Work.Diff.EXT.ATower.snoc_smoothExt (I := I) v A,
      Work.Diff.EXT.ATower.prod_snoc_sqrt (I := I) (G t) v A] at hval
    exact hval
  have h1 := hterm a b c
  have h2 := hterm b a c
  have h3 := hterm c a b
  -- the two structural rewrites
  have hI1 : Work.Diff.EXT.ATower.valOp
      (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.dAOfBase G t) k) x v a b c
      = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ATower.dR3 G t) k
          (fun i => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
          (Submission.Diff.smoothExt x c) x := by
    simp only [Work.Diff.EXT.ATower.valOp]
    exact congrFun (Work.Diff.EXT.ATower.tower_dAOfBase_eq_dR3 (I := I) (M := M) hLC hflow ht' k
      (fun i => Submission.Diff.smoothExt x (v i))
      (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
      (Submission.Diff.smoothExt x c) hv ha hb hc) x
  have hI2 := Work.Diff.EXT.ATower.dR3_tower_eq_tower2_of_smF (I := I) (M := M) G t
    (baseRic2_smF2 (I := I) (M := M) (G t) ((hLC (G t)).1.some)) k
    (fun i => Submission.Diff.smoothExt x (v i))
    (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
    (Submission.Diff.smoothExt x c) hv ha hb hc x
  rw [hI1, hI2]
  -- the arithmetic
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
        (Submission.Diff.smoothExt x c) x| ≤ Ch * (1 + Finset.sum (Finset.range k) B + U) * S := by
    refine le_trans h1 (le_of_eq (by ring))
  have hb2 : |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
        (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x b)) (Submission.Diff.smoothExt x a)
        (Submission.Diff.smoothExt x c) x| ≤ Ch * (1 + Finset.sum (Finset.range k) B + U) * S := by
    refine le_trans h2 (le_of_eq (by ring))
  have hb3 : |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
        (Fin.snoc (fun i : Fin k => Submission.Diff.smoothExt x (v i))
          (Submission.Diff.smoothExt x c)) (Submission.Diff.smoothExt x a)
        (Submission.Diff.smoothExt x b) x| ≤ Ch * (1 + Finset.sum (Finset.range k) B + U) * S := by
    refine le_trans h3 (le_of_eq (by ring))
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
          (Submission.Diff.smoothExt x b) x)| ≤ 3 * (Ch * (1 + Finset.sum (Finset.range k) B + U) * S) := by
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
  refine le_trans htri (le_of_eq (by ring))


/-! ## The parametric honest-Ric-tower bound -/

/-- **The crux**: the parametric bound for the *honest* fixed-connection Ric tower of `G t` at all
levels `m ≤ k + 1`, with the coefficient of the level-`k` connection-difference bound `U` uniform in
`U`. -/

theorem reactionPar
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
    (hA : ∀ j, j < k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ U : ℝ, 0 ≤ U →
      Work.Diff.EXT.ATower.ValBound G t k
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) k) U →
      ∀ x : M, ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.dAOfBase G t) k) x v a b c|
          ≤ Cd * (1 + Finset.sum (Finset.range k) B + U)
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
                  * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
                  * Real.sqrt ((G t).inner x c c)) :=
  reaction_par_of_fix (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi k B hB hA
    (fixedRicTower2Bound_par' (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi k B hB hA)

end Work.Diff.EXT.ConnCov
