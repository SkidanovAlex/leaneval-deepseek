import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.DeltaTower
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.BndVKit
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.GtTowerSuccEqSwap
import Submission.Work.Diff.EXT.ConnCov.bnd1_of_valBound
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.BndVStep

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The δ-tower bound `bndV_deltaTower`

See `Submission/Work/Diff/EXT/ConnCov/bndVKit.lean` for the design and the definitions of the
Leibniz expansion (`selTerm`, `Wterm`, `shiftL`, `shiftR`, `Good`).  This file contains the proof.

Sections:
1. smoothness of the towers on smooth fields, and the linearity of `step` over finite sums
   (`gtTower_smF`, `deltaTower_smE`, `selTerm_smF`, `step_sum`);
2. the metric-tower bound `gtTower_bnd`;
3. the **Leibniz expansion** `tower aOf c = Wterm c + Σ (terms with metric level ≥ 1)`;
4. the bound induction and the passage from the lowered δ-tower (`Wterm`) to the δ-tower itself.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.DTB

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## 1. Smoothness and additivity -/

/-- Smoothness of a finite sum of smooth functions. -/
lemma smF_finset_sum {ι : Type*} (s : Finset ι) (f : ι → M → ℝ)
    (h : ∀ n ∈ s, SmF I M (f n)) :
    SmF I M (fun y : M => ∑ n ∈ s, f n y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y : M => ∑ n ∈ (∅ : Finset ι), f n y) = fun _ => (0 : ℝ) := by
        funext y; simp
      rw [hz]
      exact contMDiff_const
  | insert a t ha ih =>
      have hsplit : (fun y : M => ∑ n ∈ insert a t, f n y)
          = (fun y : M => f a y) + (fun y : M => ∑ n ∈ t, f n y) := by
        funext y
        rw [Finset.sum_insert ha]
        rfl
      rw [hsplit]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih (fun n hn => h n (Finset.mem_insert_of_mem hn)))

/-- Smoothness of a finite sum over `Fin N` of smooth functions. -/
lemma smF_fin_sum {N : ℕ} (f : Fin N → M → ℝ) (h : ∀ n, SmF I M (f n)) :
    SmF I M (fun y : M => ∑ n : Fin N, f n y) :=
  smF_finset_sum Finset.univ f (fun n _ => h n)

/-- **Linearity of the recursion `step` over a finite sum** (the `Fin N`-indexed form of
`Work.Diff.EXT.ConnCov.step_linear_ext`): `step` is additive in its operator argument as soon as
every summand is smooth on smooth fields (so that `mvfderiv` may be distributed). -/
lemma step_sum [I.Boundaryless] [T2Space M] (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {k : ℕ} {ι : Type} [Fintype ι]
    (τ : ι → Op3 (I := I) (M := M) k)
    (hsm : ∀ (n : ι) (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ n v A B C))
    (v : Fin (k + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    step cov (fun v A B C y => ∑ n : ι, τ n v A B C y) v A B C x
      = ∑ n : ι, step cov (τ n) v A B C x := by
  have hw : ∀ j : Fin k, SmE I M ((fun i : Fin k => v i.succ) j) := fun j => hv j.succ
  have hsmn : ∀ n : ι, MDiffAt (τ n (fun i : Fin k => v i.succ) A B C) x :=
    fun n => (hsm n (fun i : Fin k => v i.succ) A B C hw hA hB hC).mdifferentiableAt (by simp)
  have hmv : mvfderiv I (fun y : M => ∑ n : ι, τ n (fun i : Fin k => v i.succ) A B C y) x (v 0 x)
      = ∑ n : ι, mvfderiv I (τ n (fun i : Fin k => v i.succ) A B C) x (v 0 x) :=
    mvfderiv_sum_ka (Finset.univ : Finset ι)
      (fun n : ι => τ n (fun i : Fin k => v i.succ) A B C) (fun n _ => hsmn n)
  simp only [step]
  rw [hmv, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  try ring

/-- **Smoothness of the metric tower on smooth fields.** -/
lemma gtTower_smF (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) :
    ∀ (k : ℕ) (d : Fin k → TF (I := I) (M := M)) (Y Z : TF (I := I) (M := M)),
      (∀ j, SmE I M (d j)) → SmE I M Y → SmE I M Z →
      SmF I M (fun y => gtTower G t k d Y Z y) := by
  intro k
  induction k with
  | zero =>
      intro d Y Z _ hY hZ
      exact inner_pairing_smF (G t) hY hZ
  | succ i ih =>
      intro d Y Z hd hY hZ
      have hfun : (fun y : M => gtTower G t (i + 1) d Y Z y)
          = fun y : M =>
              (tower (lcOf (G 0)) (fun _ => aOf G t) i
                  (fun j : Fin i => d j.castSucc) (d (Fin.last i)) Y Z y
                + tower (lcOf (G 0)) (fun _ => aOf G t) i
                  (fun j : Fin i => d j.castSucc) (d (Fin.last i)) Z Y y) := by
        funext y
        exact gtTower_succ_eq_swap hLC G t i d Y Z hd hY hZ y
      rw [hfun]
      exact (aOfTower_smF hLC G t i _ _ _ _ (fun j => hd j.castSucc) (hd (Fin.last i)) hY hZ).add
        (aOfTower_smF hLC G t i _ _ _ _ (fun j => hd j.castSucc) (hd (Fin.last i)) hZ hY)

/-- Smoothness of a one-slot update of a tuple of smooth fields. -/
lemma smE_update_local {k : ℕ} {v : Fin k → TF (I := I) (M := M)} (i : Fin k)
    {W : TF (I := I) (M := M)} (hv : ∀ j, SmE I M (v j)) (hW : SmE I M W) :
    ∀ j, SmE I M (Function.update v i W j) := by
  intro j
  by_cases h : j = i
  · rw [h, Function.update_self]; exact hW
  · rw [Function.update_of_ne h]; exact hv j

/-- **Smoothness of the δ-tower on smooth fields.**  (Induction on the level, following the
recursion `vstep`; the base case is the smoothness of the connection difference
`covDiff G t X Y = ∇^{g_t}_X Y − ∇^{g_0}_X Y` on smooth fields.) -/
lemma deltaTower_smE (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) :
    ∀ (k : ℕ) (v : Fin k → TF (I := I) (M := M)) (X Y : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M X → SmE I M Y →
      SmE I M (deltaTower G t k v X Y) := by
  have hbase : ∀ X Y : TF (I := I) (M := M), SmE I M X → SmE I M Y →
      SmE I M (covDiff G t X Y) := by
    intro X Y hX hY
    have h1 := lcOf_apply_smE hLC (G t) X Y hX hY
    have h2 := lcOf_apply_smE hLC (G 0) X Y hX hY
    have hfun : covDiff G t X Y
        = (fun y : M => (lcOf (G t)) X y (Y y)) - (fun y : M => (lcOf (G 0)) X y (Y y)) :=
      rfl
    rw [hfun]
    exact h1.sub_section h2
  intro k
  induction k with
  | zero =>
      intro v X Y _ hX hY
      exact hbase X Y hX hY
  | succ k ih =>
      intro v X Y hv hX hY
      have hv' : ∀ i : Fin k, SmE I M (v i.succ) := fun i => hv i.succ
      have hv0 : SmE I M (v 0) := hv 0
      have hU : ∀ i : Fin k, SmE I M (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y)) :=
        fun i => lcOf_apply_smE hLC (G 0) (v i.succ) (v 0) (hv i.succ) hv0
      change SmE I M (vstep (lcOf (G 0)) (deltaTower G t k) v X Y)
      intro x
      have h1x := (lcOf_apply_smE hLC (G 0) (deltaTower G t k (fun i : Fin k => v i.succ) X Y)
        (v 0) (ih _ X Y hv' hX hY) hv0) x
      have h2x : ContMDiffAt I I.tangent ∞ (T% (fun y : M => ∑ i : Fin k,
          deltaTower G t k (Function.update (fun j : Fin k => v j.succ) i
            (fun z => (lcOf (G 0)) (v i.succ) z (v 0 z))) X Y y)) x := by
        exact ContMDiffAt.sum_section (s := (Finset.univ : Finset (Fin k)))
          (fun i _ => (ih _ X Y (smE_update_local i hv' (hU i)) hX hY) x)
      have h3x := (ih _ _ Y hv' (lcOf_apply_smE hLC (G 0) X (v 0) hX hv0) hY) x
      have h4x := (ih _ X _ hv' hX (lcOf_apply_smE hLC (G 0) Y (v 0) hY hv0)) x
      exact ((h1x.sub_section h2x).sub_section h3x).sub_section h4x

/-- Smoothness of one expansion term. -/
lemma selTerm_smF (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) {c i j : ℕ}
    (e : Fin i ⊕ Fin j ≃ Fin c)
    (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    SmF I M (fun y => selTerm G t e v A B C y) := by
  have hd : ∀ a : Fin i, SmE I M (v (e (Sum.inl a))) := fun a => hv _
  exact gtTower_smF hLC G t i (fun a : Fin i => v (e (Sum.inl a)))
    (deltaTower G t j (fun b : Fin j => v (e (Sum.inr b))) B A) C hd
    (deltaTower_smE hLC G t j (fun b : Fin j => v (e (Sum.inr b))) B A (fun b => hv _) hB hA) hC

/-- Smoothness of a finite sum of expansion terms. -/
lemma smF_selTerm_sum (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) {c : ℕ}
    {ι : Type} [Fintype ι]
    (i j : ι → ℕ) (e : (n : ι) → Fin (i n) ⊕ Fin (j n) ≃ Fin c)
    (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    SmF I M (fun y => ∑ n : ι, selTerm G t (e n) v A B C y) :=
  smF_finset_sum Finset.univ _ (fun n _ => selTerm_smF hLC G t (e n) v A B C hv hA hB hC)

/-! ## 2. The metric-tower bound -/

/-- **The metric tower `∇^{g_0,i+1}g_t` is bounded by the `aOf`-tower at level `i`.**  This is
`gtTower_succ_eq_swap` combined with the `Bnd1` bound `h` on the fixed-connection tower of
`aOf G t` at level `i`, read off at the tuple `(d, d(last), Y, Z)` (a `Fin.append` of the direction
tuple with the two value slots). -/
lemma gtTower_bnd [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) {i : ℕ} {C : ℝ}
    (h : AMB.Bnd1 G t (AMB.pack (tower (lcOf (G 0)) (fun _ => aOf G t) i)) C)
    (d : Fin (i + 1) → TF (I := I) (M := M)) (Y Z : TF (I := I) (M := M))
    (hd : ∀ j, SmE I M (d j)) (hY : SmE I M Y) (hZ : SmE I M Z) (x : M) :
    |gtTower G t (i + 1) d Y Z x|
      ≤ 2 * C * ((Finset.univ.prod (fun j : Fin (i + 1) =>
            (1 + Real.sqrt ((G t).inner x (d j x) (d j x)))))
          * (1 + Real.sqrt ((G t).inner x (Y x) (Y x)))
          * (1 + Real.sqrt ((G t).inner x (Z x) (Z x)))) := by
  classical
  -- the two value slots are arbitrary: prove the bound for arbitrary `P, Q`
  have hmain : ∀ (P Q : TF (I := I) (M := M)), SmE I M P → SmE I M Q →
      |tower (lcOf (G 0)) (fun _ => aOf G t) i (fun j : Fin i => d j.castSucc)
          (d (Fin.last i)) P Q x|
        ≤ C * ((∏ j : Fin (i + 1), (1 + Real.sqrt ((G t).inner x (d j x) (d j x))))
            * (1 + Real.sqrt ((G t).inner x (P x) (P x)))
            * (1 + Real.sqrt ((G t).inner x (Q x) (Q x)))) := by
    intro P Q hP hQ
    set g : Fin 2 → TF (I := I) (M := M) := Fin.cases P (fun _ : Fin 1 => Q) with hg
    have hg0 : g 0 = P := by rw [hg]; exact Fin.cases_zero
    have hg1 : g 1 = Q := by rw [hg]; exact Fin.cases_succ 0
    have hFsm : ∀ j : Fin (i + 3), SmE I M (Fin.append (n := 2) d g j) := by
      intro j
      refine Fin.addCases (motive := fun j => SmE I M (Fin.append (n := 2) d g j))
        (fun j1 => ?_) (fun j2 => ?_) j
      · rw [Fin.append_left]; exact hd j1
      · rw [Fin.append_right]; fin_cases j2
        · simpa [hg0]
        · simpa [hg1]
    have hpack : (AMB.pack (tower (lcOf (G 0)) (fun _ => aOf G t) i))
          (Fin.append (n := 2) d g)
        = tower (lcOf (G 0)) (fun _ => aOf G t) i (fun j : Fin i => d j.castSucc)
            (d (Fin.last i)) P Q := by
      funext y
      rw [AMB.pack_apply]
      have e1 : (fun j : Fin i => Fin.append (n := 2) d g (Fin.castAdd 3 j))
          = fun j : Fin i => d j.castSucc := by
        funext j
        rw [show Fin.castAdd 3 j = Fin.castAdd 2 (Fin.castSucc j) from Fin.ext rfl,
          Fin.append_left]
      have e2 : Fin.append (n := 2) d g (Fin.natAdd i (0 : Fin 3)) = d (Fin.last i) := by
        rw [show Fin.natAdd i (0 : Fin 3) = Fin.castAdd 2 (Fin.last i) from Fin.ext rfl,
          Fin.append_left]
      have e3 : Fin.append (n := 2) d g (Fin.natAdd i (1 : Fin 3)) = P := by
        rw [show Fin.natAdd i (1 : Fin 3) = Fin.natAdd (i + 1) (0 : Fin 2) from Fin.ext rfl,
          Fin.append_right, hg0]
      have e4 : Fin.append (n := 2) d g (Fin.natAdd i (2 : Fin 3)) = Q := by
        rw [show Fin.natAdd i (2 : Fin 3) = Fin.natAdd (i + 1) (1 : Fin 2) from Fin.ext rfl,
          Fin.append_right, hg1]
      rw [e1, e2, e3, e4]
    have hb := h (Fin.append (n := 2) d g) x hFsm
    rw [hpack] at hb
    have hprod : (∏ j : Fin (i + 3), (1 + Real.sqrt
          ((G t).inner x (Fin.append (n := 2) d g j x) (Fin.append (n := 2) d g j x))))
        = (∏ j : Fin (i + 1), (1 + Real.sqrt ((G t).inner x (d j x) (d j x))))
          * (1 + Real.sqrt ((G t).inner x (P x) (P x)))
          * (1 + Real.sqrt ((G t).inner x (Q x) (Q x))) := by
      rw [Fin.prod_univ_add (a := i + 1) (b := 2)]
      rw [show (∏ j : Fin (i + 1), (1 + Real.sqrt
            ((G t).inner x (Fin.append (n := 2) d g (Fin.castAdd 2 j) x)
              (Fin.append (n := 2) d g (Fin.castAdd 2 j) x))))
          = ∏ j : Fin (i + 1), (1 + Real.sqrt ((G t).inner x (d j x) (d j x))) from
        Finset.prod_congr rfl (fun j _ => by rw [Fin.append_left])]
      rw [Fin.prod_univ_two, Fin.append_right, Fin.append_right, hg0, hg1]
      ring
    rw [hprod] at hb
    exact hb
  have hYZ := hmain Y Z hY hZ
  have hZY := hmain Z Y hZ hY
  rw [gtTower_succ_eq_swap hLC G t i d Y Z hd hY hZ x]
  calc |tower (lcOf (G 0)) (fun _ => aOf G t) i (fun j : Fin i => d j.castSucc)
            (d (Fin.last i)) Y Z x
          + tower (lcOf (G 0)) (fun _ => aOf G t) i (fun j : Fin i => d j.castSucc)
            (d (Fin.last i)) Z Y x|
      ≤ |tower (lcOf (G 0)) (fun _ => aOf G t) i (fun j : Fin i => d j.castSucc)
            (d (Fin.last i)) Y Z x|
        + |tower (lcOf (G 0)) (fun _ => aOf G t) i (fun j : Fin i => d j.castSucc)
            (d (Fin.last i)) Z Y x| := abs_add_le _ _
    _ ≤ C * ((∏ j : Fin (i + 1), (1 + Real.sqrt ((G t).inner x (d j x) (d j x))))
            * (1 + Real.sqrt ((G t).inner x (Y x) (Y x)))
            * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))))
          + C * ((∏ j : Fin (i + 1), (1 + Real.sqrt ((G t).inner x (d j x) (d j x))))
            * (1 + Real.sqrt ((G t).inner x (Z x) (Z x)))
            * (1 + Real.sqrt ((G t).inner x (Y x) (Y x)))) := add_le_add hYZ hZY
    _ = 2 * C * ((∏ j : Fin (i + 1), (1 + Real.sqrt ((G t).inner x (d j x) (d j x))))
            * (1 + Real.sqrt ((G t).inner x (Y x) (Y x)))
            * (1 + Real.sqrt ((G t).inner x (Z x) (Z x)))) := by ring

/-! ## 3. The bound of one expansion term -/

/-- A bound on the metric tower `∇^{g_0,i}g_t` on arbitrary smooth fields, in the shape produced by
`gtTower_bnd`. -/
def MetricBnd (G : ℝ → SMet I M) (t : ℝ) (i : ℕ) (M₀ : ℝ) : Prop :=
  ∀ (d : Fin i → TF (I := I) (M := M)) (Y Z : TF (I := I) (M := M)),
    (∀ j, SmE I M (d j)) → SmE I M Y → SmE I M Z → ∀ x : M,
      |gtTower G t i d Y Z x|
        ≤ M₀ * ((∏ j : Fin i, (1 + Real.sqrt ((G t).inner x (d j x) (d j x))))
            * (1 + Real.sqrt ((G t).inner x (Y x) (Y x)))
            * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))))

lemma metricBnd_succ [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M)
    (G : ℝ → SMet I M) (t : ℝ) {i : ℕ} {C : ℝ}
    (h : AMB.Bnd1 G t (AMB.pack (tower (lcOf (G 0)) (fun _ => aOf G t) i)) C) :
    MetricBnd G t (i + 1) (2 * C) :=
  fun d Y Z hd hY hZ x => gtTower_bnd hLC G t h d Y Z hd hY hZ x

/-- The product of `(1 + √⟨·,·⟩)` factors is at least `1`. -/
lemma one_le_prod_sqrt (G : ℝ → SMet I M) (t : ℝ) (x : M) {n : ℕ}
    (u : Fin n → TF (I := I) (M := M)) :
    1 ≤ ∏ j : Fin n, (1 + Real.sqrt ((G t).inner x (u j x) (u j x))) := by
  have key : ∀ (n : ℕ) (u : Fin n → TF (I := I) (M := M)),
      1 ≤ ∏ j : Fin n, (1 + Real.sqrt ((G t).inner x (u j x) (u j x))) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
        intro u
        rw [Fin.prod_univ_castSucc]
        have h1 := ih (fun j : Fin n => u j.castSucc)
        have h2 : 1 ≤ 1 + Real.sqrt ((G t).inner x (u (Fin.last n) x) (u (Fin.last n) x)) := by
          have := Real.sqrt_nonneg ((G t).inner x (u (Fin.last n) x) (u (Fin.last n) x))
          linarith
        nlinarith
  exact key n u

/-- `1 ≤ 1 + √⟨u,u⟩`. -/
lemma one_le_one_add_sqrt (G : ℝ → SMet I M) (t : ℝ) (x : M) (u : TangentSpace I x) :
    1 ≤ 1 + Real.sqrt ((G t).inner x u u) := by
  have := Real.sqrt_nonneg ((G t).inner x u u)
  linarith

/-- **The bound of one expansion term.**  The metric factor is bounded by `Mi` (a `MetricBnd` at
level `i ≥ 1`) and the δ factor by `Mj` (the `BndV` bound at level `j`); the direction slots are
distributed by `e : Fin i ⊕ Fin j ≃ Fin c`, so the two products of `(1 + √⟨·,·⟩)`-factors multiply
to the full product over `Fin c`. -/
lemma selTerm_le [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M)
    (G : ℝ → SMet I M) (t : ℝ) {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    {Mi Mj : ℝ} (hMi : 0 ≤ Mi) (hMj : 0 ≤ Mj)
    (hM : MetricBnd G t i Mi) (hδ : AMB.BndV G t (deltaTower G t j) Mj)
    (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ m, SmE I M (v m)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    |selTerm G t e v A B C x|
      ≤ (Mi * (1 + Mj)) * ((∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
          * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
          * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
          * (1 + Real.sqrt ((G t).inner x (C x) (C x)))) := by
  have hdw : ∀ b : Fin j, SmE I M (v (e (Sum.inr b))) := fun b => hv _
  have hδf : SmE I M (deltaTower G t j (fun b : Fin j => v (e (Sum.inr b))) B A) :=
    deltaTower_smE hLC G t j (fun b : Fin j => v (e (Sum.inr b))) B A hdw hB hA
  have h1 := hM (fun a : Fin i => v (e (Sum.inl a)))
      (deltaTower G t j (fun b : Fin j => v (e (Sum.inr b))) B A) C
      (fun a => hv _) hδf hC x
  have h2 := hδ (fun b : Fin j => v (e (Sum.inr b))) B A hdw hB hA x
  set Pa : ℝ := ∏ a : Fin i,
    (1 + Real.sqrt ((G t).inner x (v (e (Sum.inl a)) x) (v (e (Sum.inl a)) x))) with hPa
  set Pb : ℝ := ∏ b : Fin j,
    (1 + Real.sqrt ((G t).inner x (v (e (Sum.inr b)) x) (v (e (Sum.inr b)) x))) with hPb
  set Pc : ℝ := ∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))) with hPc
  set fA : ℝ := 1 + Real.sqrt ((G t).inner x (A x) (A x)) with hfA
  set fB : ℝ := 1 + Real.sqrt ((G t).inner x (B x) (B x)) with hfB
  set fC : ℝ := 1 + Real.sqrt ((G t).inner x (C x) (C x)) with hfC
  set rd : ℝ := Real.sqrt ((G t).inner x
    (deltaTower G t j (fun b : Fin j => v (e (Sum.inr b))) B A x)
    (deltaTower G t j (fun b : Fin j => v (e (Sum.inr b))) B A x)) with hrd
  have h1' : |selTerm G t e v A B C x| ≤ Mi * (Pa * (1 + rd) * fC) := h1
  have h2' : rd ≤ Mj * Pb * fB * fA := h2
  have hPa0 : 0 ≤ Pa := by
    rw [hPa]
    exact Finset.prod_nonneg (fun a _ => by
      have := Real.sqrt_nonneg ((G t).inner x (v (e (Sum.inl a)) x) (v (e (Sum.inl a)) x))
      linarith)
  have hPb0 : 0 ≤ Pb := by
    rw [hPb]
    exact Finset.prod_nonneg (fun b _ => by
      have := Real.sqrt_nonneg ((G t).inner x (v (e (Sum.inr b)) x) (v (e (Sum.inr b)) x))
      linarith)
  have hfA0 : 0 ≤ fA := by rw [hfA]; exact le_of_lt (lt_of_lt_of_le zero_lt_one (one_le_one_add_sqrt G t x (A x)))
  have hfB0 : 0 ≤ fB := by rw [hfB]; exact le_of_lt (lt_of_lt_of_le zero_lt_one (one_le_one_add_sqrt G t x (B x)))
  have hfC0 : 0 ≤ fC := by rw [hfC]; exact le_of_lt (lt_of_lt_of_le zero_lt_one (one_le_one_add_sqrt G t x (C x)))
  have hpb1 : 1 ≤ Pb * fB * fA := by
    have e1 : 1 ≤ Pb := by rw [hPb]; exact one_le_prod_sqrt G t x _
    have e2 : 1 ≤ fB := by rw [hfB]; exact one_le_one_add_sqrt G t x (B x)
    have e3 : 1 ≤ fA := by rw [hfA]; exact one_le_one_add_sqrt G t x (A x)
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ Pb * fB * fA := by gcongr
  have hmerge : Pa * Pb = Pc := by
    rw [hPa, hPb, hPc]
    rw [← Fintype.prod_sum_type (fun s : Fin i ⊕ Fin j =>
      (1 + Real.sqrt ((G t).inner x (v (e s) x) (v (e s) x))))]
    exact Fintype.prod_equiv e _ _ (fun s => rfl)
  have hkey : 1 + rd ≤ (1 + Mj) * (Pb * fB * fA) := by
    have e1 : 1 + rd ≤ 1 + Mj * (Pb * fB * fA) := by linarith
    have e2 : 1 + Mj * (Pb * fB * fA) ≤ (1 + Mj) * (Pb * fB * fA) := by nlinarith [hpb1, hMj]
    linarith
  calc |selTerm G t e v A B C x| ≤ Mi * (Pa * (1 + rd) * fC) := h1'
    _ ≤ Mi * (Pa * ((1 + Mj) * (Pb * fB * fA)) * fC) := by
        apply mul_le_mul_of_nonneg_left _ hMi
        apply mul_le_mul_of_nonneg_right _ hfC0
        exact mul_le_mul_of_nonneg_left hkey hPa0
    _ = (Mi * (1 + Mj)) * (Pc * fA * fB * fC) := by
        rw [← hmerge]; ring

/-- **The bound of a finite sum of expansion terms**, in the shape needed for the induction: the
constant is the sum of the individual constants `Mi n * (1 + Cf n)`. -/
lemma sum_selTerm_le [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M)
    (G : ℝ → SMet I M) (t : ℝ) {c : ℕ} {ι : Type} [Fintype ι]
    (i j : ι → ℕ) (e : (n : ι) → Fin (i n) ⊕ Fin (j n) ≃ Fin c)
    (hi : ∀ n, 1 ≤ i n) (Mi Cf : ι → ℝ) (hMi : ∀ n, 0 ≤ Mi n) (hCf : ∀ n, 0 ≤ Cf n)
    (hM : ∀ n, MetricBnd G t (i n) (Mi n))
    (hδ : ∀ n, AMB.BndV G t (deltaTower G t (j n)) (Cf n))
    (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ m, SmE I M (v m)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    |∑ n : ι, selTerm G t (e n) v A B C x|
      ≤ (∑ n : ι, Mi n * (1 + Cf n)) * ((∏ m : Fin c,
              (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
          * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
          * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
          * (1 + Real.sqrt ((G t).inner x (C x) (C x)))) := by
  set P : ℝ := (∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
      * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
      * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
      * (1 + Real.sqrt ((G t).inner x (C x) (C x))) with hP
  calc |∑ n : ι, selTerm G t (e n) v A B C x|
      ≤ ∑ n : ι, |selTerm G t (e n) v A B C x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n : ι, (Mi n * (1 + Cf n)) * P := by
        apply Finset.sum_le_sum
        intro n _
        rw [hP]
        exact selTerm_le hLC G t (e n) (hMi n) (hCf n) (hM n) (hδ n) v A B C hv hA hB hC x
    _ = (∑ n : ι, Mi n * (1 + Cf n)) * P := by
        rw [Finset.sum_mul]

/-! ## 4. The `aOf`-tower bound in unpacked form -/

/-- The product of `(1 + √⟨·,·⟩)`-factors over a tuple `F : Fin (n+3)` splits at
`F = mkT3 v (trip3 A B C)`. -/
lemma mkT3_prod [T2Space M] (G : ℝ → SMet I M) (t : ℝ) (x : M) {n : ℕ}
    (v : Fin n → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) :
    (∏ j : Fin (n + 3), (1 + Real.sqrt
          ((G t).inner x (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) j x)
            (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) j x))))
      = (∏ m : Fin n, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
        * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
        * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
        * (1 + Real.sqrt ((G t).inner x (C x) (C x))) := by
  rw [Fin.prod_univ_add (a := n) (b := 3), Fin.prod_univ_three]
  rw [show (∏ i : Fin n, (1 + Real.sqrt
        ((G t).inner x (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) (Fin.castAdd 3 i) x)
          (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) (Fin.castAdd 3 i) x))))
      = ∏ m : Fin n, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))) from
    Finset.prod_congr rfl (fun m _ => by rw [Work.Diff.EXT.mkT3_castAdd])]
  rw [Work.Diff.EXT.mkT3_natAdd, Work.Diff.EXT.mkT3_natAdd, Work.Diff.EXT.mkT3_natAdd,
    Work.Diff.EXT.trip3_zero, Work.Diff.EXT.trip3_one, Work.Diff.EXT.trip3_two]
  ring

/-- The `aOf`-tower bound on arbitrary smooth fields, from its `Bnd1` bound (which is what `hA`
provides through `bnd1_of_valBound`). -/
lemma aOf_tower_le [T2Space M] (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) {m : ℕ}
    {Ck : ℝ} (h : AMB.Bnd1 G t (AMB.pack (tower (lcOf (G 0)) (fun _ => aOf G t) m)) Ck)
    (v : Fin m → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ m, SmE I M (v m)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    |tower (lcOf (G 0)) (fun _ => aOf G t) m v A B C x|
      ≤ Ck * ((∏ j : Fin m, (1 + Real.sqrt ((G t).inner x (v j x) (v j x))))
          * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
          * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
          * (1 + Real.sqrt ((G t).inner x (C x) (C x)))) := by
  have hsm : ∀ j : Fin (m + 3), SmE I M (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) j) := by
    intro j
    refine Fin.addCases (motive := fun j => SmE I M (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) j))
      (fun j1 => ?_) (fun j2 => ?_) j
    · rw [Work.Diff.EXT.mkT3_castAdd]; exact hv j1
    · rw [Work.Diff.EXT.mkT3_natAdd]
      have hj : j2 = 0 ∨ j2 = 1 ∨ j2 = 2 := by
        fin_cases j2 <;> simp
      rcases hj with h | h | h <;> subst h
      · rw [Work.Diff.EXT.trip3_zero]; exact hA
      · rw [Work.Diff.EXT.trip3_one]; exact hB
      · rw [Work.Diff.EXT.trip3_two]; exact hC
  have hb := h (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C)) x hsm
  rw [mkT3_prod] at hb
  have hpack : AMB.pack (tower (lcOf (G 0)) (fun _ => aOf G t) m)
      (Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C))
      = tower (lcOf (G 0)) (fun _ => aOf G t) m v A B C := by
    funext y
    rw [AMB.pack_apply]
    have e1 : (fun j : Fin m => Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) (Fin.castAdd 3 j))
        = fun j : Fin m => v j := by
      funext j; rw [Work.Diff.EXT.mkT3_castAdd]
    have e2 : Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) (Fin.natAdd m (0 : Fin 3)) = A := by
      rw [Work.Diff.EXT.mkT3_natAdd, Work.Diff.EXT.trip3_zero]
    have e3 : Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) (Fin.natAdd m (1 : Fin 3)) = B := by
      rw [Work.Diff.EXT.mkT3_natAdd, Work.Diff.EXT.trip3_one]
    have e4 : Work.Diff.EXT.mkT3 v (Work.Diff.EXT.trip3 A B C) (Fin.natAdd m (2 : Fin 3)) = C := by
      rw [Work.Diff.EXT.mkT3_natAdd, Work.Diff.EXT.trip3_two]
    rw [e1, e2, e3, e4]
  rw [hpack] at hb
  exact hb

/-! ## 5. From the lowered δ-tower to the δ-tower -/

/-- Nonnegativity of the metric pairing of a vector with itself. -/
lemma smet_inner_self_nonneg' (g : SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)

/-- **The lowering is an isometry**: a bound on `Wterm c` (the pairing of `∇^{g_0,c}δ` with the
moving metric) gives a bound on the δ-tower itself.  With `r := √⟨∇^{g_0,c}δ, ∇^{g_0,c}δ⟩` the
pairing bound reads `r ^ 2 ≤ D * P * (1 + r)` with `P ≥ 1` the product of the slot norms, whence
`r ≤ (1 + 2 * D) * P`. -/
lemma delta_le_of_wterm [I.Boundaryless] [T2Space M]
    (G : ℝ → SMet I M) (t : ℝ) {c : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ m, SmE I M (v m)) → SmE I M A → SmE I M B → SmE I M C → ∀ x : M,
      |Wterm G t c v A B C x|
        ≤ D * ((∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
            * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
            * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
            * (1 + Real.sqrt ((G t).inner x (C x) (C x))))) :
    AMB.BndV G t (deltaTower G t c) (1 + 2 * D) := by
  intro v X Z hv hX hZ x
  set P' : ℝ := (∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
      * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
      * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))) with hP'
  have hP'1 : 1 ≤ P' := by
    have h1 : 1 ≤ ∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))) :=
      one_le_prod_sqrt G t x v
    have h2 : 1 ≤ 1 + Real.sqrt ((G t).inner x (X x) (X x)) := one_le_one_add_sqrt G t x (X x)
    have h3 : 1 ≤ 1 + Real.sqrt ((G t).inner x (Z x) (Z x)) := one_le_one_add_sqrt G t x (Z x)
    rw [hP']
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ (∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
          * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
          * (1 + Real.sqrt ((G t).inner x (Z x) (Z x))) := by gcongr
  have hP'0 : 0 ≤ P' := le_trans zero_le_one hP'1
  set u : TangentSpace I x := deltaTower G t c v X Z x with hu
  set r : ℝ := Real.sqrt ((G t).inner x u u) with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have huu : 0 ≤ (G t).inner x u u := smet_inner_self_nonneg' (G t) x u
  have hC' : SmE I M (Submission.Diff.smoothExt x u) := Work.Diff.GE.smoothExt_cmdiff x _
  have hb := h v Z X (Submission.Diff.smoothExt x u) hv hZ hX hC' x
  rw [Wterm_apply, Work.Diff.GE.smoothExt_apply] at hb
  have hrsq : (G t).inner x u u = r ^ 2 := by rw [hr, Real.sq_sqrt huu]
  have hb' : r ^ 2 ≤ D * (P' * (1 + r)) := by
    have hL : |(G t).inner x u u| = r ^ 2 := by rw [abs_of_nonneg huu, hrsq]
    rw [hL] at hb
    have haux : (∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
          * (1 + Real.sqrt ((G t).inner x (Z x) (Z x)))
          * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
          * (1 + Real.sqrt ((G t).inner x u u)) = P' * (1 + r) := by
      rw [hP', hr]; ring
    rw [haux] at hb
    exact hb
  have hr2 : r ≤ (1 + 2 * D) * P' := by
    rcases lt_or_ge r 1 with h1 | h1
    · have h2 : 1 ≤ (1 + 2 * D) * P' := by
        have hD1 : (1 : ℝ) ≤ 1 + 2 * D := by linarith
        calc (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ (1 + 2 * D) * P' := mul_le_mul hD1 hP'1 (by norm_num) (by linarith)
      linarith
    · have h4 : P' * (1 + r) ≤ P' * (2 * r) := by
        apply mul_le_mul_of_nonneg_left _ hP'0
        linarith
      have h5 : D * (P' * (1 + r)) ≤ D * (P' * (2 * r)) := mul_le_mul_of_nonneg_left h4 hD
      have h5' : r * r ≤ D * (P' * (1 + r)) := by
        calc r * r = r ^ 2 := by ring
          _ ≤ D * (P' * (1 + r)) := hb'
      have h6 : r * r ≤ (2 * D * P') * r := by
        have e : D * (P' * (2 * r)) = (2 * D * P') * r := by ring
        rw [e] at h5
        linarith
      have h7 : r ≤ 2 * D * P' := le_of_mul_le_mul_right h6 (by linarith)
      have h8 : 2 * D * P' ≤ (1 + 2 * D) * P' := mul_le_mul_of_nonneg_right (by linarith) hP'0
      linarith
  have hrhs : ((1 + 2 * D) * (∏ m : Fin c, (1 + Real.sqrt ((G t).inner x (v m x) (v m x))))
        * (1 + Real.sqrt ((G t).inner x (X x) (X x)))
        * (1 + Real.sqrt ((G t).inner x (Z x) (Z x)))) = (1 + 2 * D) * P' := by
    rw [hP']; ring
  rw [← hrhs] at hr2
  exact hr2

/-! ## 6. The Leibniz expansion -/

/-- A **shuffle** at level `c`: the metric level `i`, the δ level `j`, the identity `i + j = c` and
the distribution of the `c` direction slots between the two factors (`e`). -/
structure Shuffle (c : ℕ) where
  i : ℕ
  j : ℕ
  hij : i + j = c
  e : Fin i ⊕ Fin j ≃ Fin c

/-- One recursion step of the expansion, the metric factor receiving the new direction. -/
noncomputable def Shuffle.stepL {c : ℕ} (s : Shuffle c) : Shuffle (c + 1) where
  i := s.i + 1
  j := s.j
  hij := by have h := s.hij; omega
  e := shiftL s.e

/-- One recursion step of the expansion, the δ factor receiving the new direction. -/
noncomputable def Shuffle.stepR {c : ℕ} (s : Shuffle c) : Shuffle (c + 1) where
  i := s.i
  j := s.j + 1
  hij := by have h := s.hij; omega
  e := shiftR s.e

/-- The `i = 0` term of level `c+1` (the one produced by `Wterm c`). -/
noncomputable def Shuffle.step0 (c : ℕ) : Shuffle (c + 1) where
  i := 1
  j := c
  hij := by omega
  e := shiftL (eC c)

@[simp] theorem Shuffle.stepL_i {c : ℕ} (s : Shuffle c) : (s.stepL).i = s.i + 1 := rfl

@[simp] theorem Shuffle.stepL_j {c : ℕ} (s : Shuffle c) : (s.stepL).j = s.j := rfl

theorem Shuffle.stepL_e {c : ℕ} (s : Shuffle c) : (s.stepL).e = shiftL s.e := rfl

@[simp] theorem Shuffle.stepR_i {c : ℕ} (s : Shuffle c) : (s.stepR).i = s.i := rfl

@[simp] theorem Shuffle.stepR_j {c : ℕ} (s : Shuffle c) : (s.stepR).j = s.j + 1 := rfl

theorem Shuffle.stepR_e {c : ℕ} (s : Shuffle c) : (s.stepR).e = shiftR s.e := rfl

@[simp] theorem Shuffle.step0_i {c : ℕ} : (Shuffle.step0 c).i = 1 := rfl

@[simp] theorem Shuffle.step0_j {c : ℕ} : (Shuffle.step0 c).j = c := rfl

theorem Shuffle.step0_e {c : ℕ} : (Shuffle.step0 c).e = shiftL (eC c) := rfl

/-- The index data of the Leibniz expansion at level `c`: a finite index type and a shuffle for each
of its elements, all with metric level `≥ 1`. -/
structure ExpData (c : ℕ) where
  ι : Type
  ft : Fintype ι
  sh : ι → Shuffle c
  hi : ∀ n, 1 ≤ (sh n).i

attribute [instance] ExpData.ft

namespace ExpData

/-- The empty index data at level `0`. -/
def base : ExpData 0 where
  ι := Empty
  ft := inferInstance
  sh := fun n => n.elim
  hi := fun n => n.elim

/-- The shuffle map of the successor index data. -/
noncomputable def succSh {c : ℕ} (D : ExpData c) : D.ι ⊕ D.ι ⊕ PUnit → Shuffle (c + 1) :=
  Sum.elim (fun a => (D.sh a).stepL)
    (Sum.elim (fun a => (D.sh a).stepR) (fun _ => Shuffle.step0 c))

@[simp] theorem succSh_inl {c : ℕ} (D : ExpData c) (a : D.ι) :
    succSh D (Sum.inl a) = (D.sh a).stepL := rfl

@[simp] theorem succSh_inr_inl {c : ℕ} (D : ExpData c) (a : D.ι) :
    succSh D (Sum.inr (Sum.inl a)) = (D.sh a).stepR := rfl

@[simp] theorem succSh_inr_inr {c : ℕ} (D : ExpData c) (u : PUnit) :
    succSh D (Sum.inr (Sum.inr u)) = Shuffle.step0 c := rfl

/-- The index data at level `c+1` obtained from that at level `c`: the two images of every term plus
the single term coming from the `i = 0` term `Wterm c`. -/
noncomputable def succ {c : ℕ} (D : ExpData c) : ExpData (c + 1) where
  ι := D.ι ⊕ D.ι ⊕ PUnit
  ft := inferInstance
  sh := succSh D
  hi := by
    intro n
    rcases n with a | a | u
    · rw [succSh_inl, Shuffle.stepL_i]; exact Nat.le_add_left 1 _
    · rw [succSh_inr_inl, Shuffle.stepR_i]; exact D.hi a
    · rw [succSh_inr_inr, Shuffle.step0_i]

@[simp] theorem succ_sh_inl {c : ℕ} (D : ExpData c) (a : D.ι) :
    (D.succ).sh (Sum.inl a) = (D.sh a).stepL := rfl

@[simp] theorem succ_sh_inr_inl {c : ℕ} (D : ExpData c) (a : D.ι) :
    (D.succ).sh (Sum.inr (Sum.inl a)) = (D.sh a).stepR := rfl

@[simp] theorem succ_sh_inr_inr {c : ℕ} (D : ExpData c) (u : PUnit) :
    (D.succ).sh (Sum.inr (Sum.inr u)) = Shuffle.step0 c := rfl

end ExpData

/-- **Equality of operators on smooth fields.**  The tower recursion uses `mvfderiv`, which is
additive only on differentiable functions; every identity below is therefore stated as an equality
of *values at smooth tuples*. -/
def OpEq {c : ℕ} (τ σ : Op3 (I := I) (M := M) c) : Prop :=
  ∀ (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M),
    (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → τ v A B C x = σ v A B C x

/-- Smoothness of an operator on smooth tuples. -/
def SmOp {c : ℕ} (τ : Op3 (I := I) (M := M) c) : Prop :=
  ∀ (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
    (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ v A B C)

theorem OpEq.refl {c : ℕ} (τ : Op3 (I := I) (M := M) c) : OpEq τ τ := fun _ _ _ _ _ _ _ _ _ => rfl

theorem OpEq.symm {c : ℕ} {τ σ : Op3 (I := I) (M := M) c} (h : OpEq τ σ) : OpEq σ τ :=
  fun v A B C x hv hA hB hC => (h v A B C x hv hA hB hC).symm

theorem OpEq.trans {c : ℕ} {τ σ ρ : Op3 (I := I) (M := M) c} (h1 : OpEq τ σ) (h2 : OpEq σ ρ) :
    OpEq τ ρ :=
  fun v A B C x hv hA hB hC => (h1 v A B C x hv hA hB hC).trans (h2 v A B C x hv hA hB hC)

theorem OpEq.add {c : ℕ} {τ₁ σ₁ τ₂ σ₂ : Op3 (I := I) (M := M) c}
    (h1 : OpEq τ₁ σ₁) (h2 : OpEq τ₂ σ₂) :
    OpEq (fun v A B C y => τ₁ v A B C y + τ₂ v A B C y)
      (fun v A B C y => σ₁ v A B C y + σ₂ v A B C y) := by
  intro v A B C x hv hA hB hC
  change τ₁ v A B C x + τ₂ v A B C x = σ₁ v A B C x + σ₂ v A B C x
  rw [h1 v A B C x hv hA hB hC, h2 v A B C x hv hA hB hC]

/-- The recursion step respects equalities of operators on smooth tuples. -/
lemma step_congr [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M)
    (G : ℝ → SMet I M) {c : ℕ}
    {τ σ : Op3 (I := I) (M := M) c} (h : OpEq τ σ) :
    OpEq (step (lcOf (G 0)) τ) (step (lcOf (G 0)) σ) := by
  intro v A B C x hv hA hB hC
  have hw : ∀ j : Fin c, SmE I M ((fun i : Fin c => v i.succ) j) := fun j => hv j.succ
  have hv0 : SmE I M (v 0) := hv 0
  have hU : ∀ j : Fin c, SmE I M (fun y => (lcOf (G 0)) (v j.succ) y (v 0 y)) :=
    fun j => lcOf_apply_smE hLC (G 0) (v j.succ) (v 0) (hv j.succ) hv0
  have hAc : SmE I M (fun y => (lcOf (G 0)) A y (v 0 y)) :=
    lcOf_apply_smE hLC (G 0) A (v 0) hA hv0
  have hBc : SmE I M (fun y => (lcOf (G 0)) B y (v 0 y)) :=
    lcOf_apply_smE hLC (G 0) B (v 0) hB hv0
  have hCc : SmE I M (fun y => (lcOf (G 0)) C y (v 0 y)) :=
    lcOf_apply_smE hLC (G 0) C (v 0) hC hv0
  have hfun : τ (fun i : Fin c => v i.succ) A B C = σ (fun i : Fin c => v i.succ) A B C := by
    funext y
    exact h _ A B C y hw hA hB hC
  simp only [step]
  rw [hfun]
  have e1 : (∑ j : Fin c, τ (Function.update (fun i : Fin c => v i.succ) j
        (fun y => (lcOf (G 0)) (v j.succ) y (v 0 y))) A B C x)
      = ∑ j : Fin c, σ (Function.update (fun i : Fin c => v i.succ) j
        (fun y => (lcOf (G 0)) (v j.succ) y (v 0 y))) A B C x :=
    Finset.sum_congr rfl (fun j _ => h _ A B C x (smE_update_local j hw (hU j)) hA hB hC)
  rw [e1,
    h (fun i : Fin c => v i.succ) (fun y => (lcOf (G 0)) A y (v 0 y)) B C x hw hAc hB hC,
    h (fun i : Fin c => v i.succ) A (fun y => (lcOf (G 0)) B y (v 0 y)) C x hw hA hBc hC,
    h (fun i : Fin c => v i.succ) A B (fun y => (lcOf (G 0)) C y (v 0 y)) x hw hA hB hCc]

/-- Linearity of the recursion step in the operator argument, on smooth tuples. -/
lemma step_lin [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M) (G : ℝ → SMet I M)
    (c₁ c₂ : ℝ) {c : ℕ}
    {τ₁ τ₂ : Op3 (I := I) (M := M) c} (h₁ : SmOp τ₁) (h₂ : SmOp τ₂) :
    OpEq (step (lcOf (G 0)) (fun v A B C y => c₁ * τ₁ v A B C y + c₂ * τ₂ v A B C y))
      (fun v A B C y => c₁ * step (lcOf (G 0)) τ₁ v A B C y
        + c₂ * step (lcOf (G 0)) τ₂ v A B C y) :=
  fun v A B C x hv hA hB hC =>
    step_linear_ext (lcOf (G 0)) c₁ c₂ τ₁ τ₂ h₁ h₂ v A B C hv hA hB hC x

/-- Linearity of the recursion step over a finite sum, on smooth tuples. -/
lemma step_sumE [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M) (G : ℝ → SMet I M) {c : ℕ}
    {ι : Type} [Fintype ι]
    (σ : ι → Op3 (I := I) (M := M) c) (h : ∀ n, SmOp (σ n)) :
    OpEq (step (lcOf (G 0)) (fun v A B C y => ∑ n : ι, σ n v A B C y))
      (fun v A B C y => ∑ n : ι, step (lcOf (G 0)) (σ n) v A B C y) :=
  fun v A B C x hv hA hB hC => step_sum (lcOf (G 0)) σ h v A B C hv hA hB hC x

/-- **The one recursion step of the Leibniz expansion, on smooth tuples.**  The recursion `step` on
the expansion term `selTerm G t e` splits into the two terms in which the new direction goes to the
metric factor (`shiftL`) or to the δ factor (`shiftR`).  This is the `OpEq` form of the identity
proved in `step_pairOp` (`bndVStep.lean`): on non-smooth tuples the identity genuinely fails, because
the recursion uses `mvfderiv` (the junk value `0` off the differentiable points). -/
theorem step_selTerm [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M)
    (G : ℝ → SMet I M) (t : ℝ) {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    OpEq (I := I) (M := M) (step (lcOf (G 0)) (selTerm G t e))
      (fun v A B C y => selTerm G t (shiftL e) v A B C y
        + selTerm G t (shiftR e) v A B C y) := by
  intro v A B C x hv hA hB hC
  exact step_pairOp (I := I) (M := M) (lcOf (G 0)) e (gtTower G t i) (deltaTower G t j)
    (fun d Y₁ Y₂ Z hd h₁ h₂ hZ => gtTower_add_val0 (I := I) (M := M) hLC G t i d Y₁ Y₂ Z
      hd h₁ h₂ hZ)
    (fun d X Y hd hX hY => deltaTower_smE (I := I) (M := M) hLC G t j d X Y hd hX hY)
    (fun W W' hW hW' => lcOf_apply_smE hLC (G 0) W W' hW hW')
    v A B C hv hA hB hC x

/-- **The one recursion step of the Leibniz expansion**, in the form used by the expansion (a
hypothesis so that the assembly `expansion_data` can be elaborated against the statement). -/
def StepRule : Prop :=
  ∀ (G' : ℝ → SMet I M) (t' : ℝ) {c i j : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c),
    OpEq (I := I) (M := M) (step (lcOf (G' 0)) (selTerm G' t' e))
      (fun v A B C y => selTerm G' t' (shiftL e) v A B C y
          + selTerm G' t' (shiftR e) v A B C y)

/-- The one-step rule holds. -/
theorem stepRule_holds [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M) :
    StepRule (I := I) (M := M) := by
  intro G t c i j e
  exact step_selTerm hLC G t e

/-- The `i = 0` term is the `Wterm` of the next level. -/
lemma step_Wterm (hr : StepRule (I := I) (M := M)) (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    OpEq (I := I) (M := M) (step (lcOf (G 0)) (Wterm G t c))
      (fun v A B C y => Wterm G t (c + 1) v A B C y
          + selTerm G t (shiftL (eC c)) v A B C y) := by
  intro v A B C x hv hA hB hC
  show step (lcOf (G 0)) (selTerm G t (eC c)) v A B C x
      = selTerm G t (eC (c + 1)) v A B C x + selTerm G t (shiftL (eC c)) v A B C x
  rw [hr G t (eC c) v A B C x hv hA hB hC, shiftR_eC]
  ring

/-- **The Leibniz expansion.**  For every level `c` there is index data `D` such that, for *every*
metric family `G'` and every `t`, the `∇^{g_0}`-tower of `aOf` at level `c` equals the `i = 0` term
`Wterm` plus the sum of the terms of `D`, on *smooth* tuples.  The data does not depend on `G'` or
`t`, which is what allows the constants of the final bound to be chosen from it. -/
lemma expansion_data [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M)
    (hr : StepRule (I := I) (M := M)) :
    ∀ c : ℕ, ∃ D : ExpData c,
      ∀ (G' : ℝ → SMet I M) (t : ℝ),
        OpEq (tower (lcOf (G' 0)) (fun _ => aOf G' t) c)
          (fun v A B C y => Wterm G' t c v A B C y
            + ∑ n : D.ι, selTerm G' t ((D.sh n).e) v A B C y) := by
  intro c
  induction c with
  | zero =>
      refine ⟨{ ι := Empty, ft := inferInstance, sh := fun n => n.elim, hi := fun n => n.elim }, ?_⟩
      intro G' t v A B C x hv hA hB hC
      simp only [tower, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      rw [Wterm_apply]
      rfl
  | succ c ih =>
      obtain ⟨D, hD⟩ := ih
      refine ⟨D.succ, ?_⟩
      intro G' t
      set τ : Op3 (I := I) (M := M) c :=
        fun v A B C y => ∑ n : D.ι, selTerm G' t ((D.sh n).e) v A B C y with hτ
      have hIH : OpEq (tower (lcOf (G' 0)) (fun _ => aOf G' t) c)
          (fun v A B C y => Wterm G' t c v A B C y + τ v A B C y) := by
        intro v A B C x hv hA hB hC
        show tower (lcOf (G' 0)) (fun _ => aOf G' t) c v A B C x
          = Wterm G' t c v A B C x + τ v A B C x
        have hτx : τ v A B C x = ∑ n : D.ι, selTerm G' t ((D.sh n).e) v A B C x := by
          rw [hτ]
        rw [hτx]
        exact hD G' t v A B C x hv hA hB hC
      have hsmW : SmOp (Wterm G' t c) := by
        intro v' A' B' C' hv' hA' hB' hC'
        have hfun : Wterm G' t c v' A' B' C'
            = fun y : M => (G' t).inner y (deltaTower G' t c v' B' A' y) (C' y) := by
          funext y; rw [Wterm_apply]
        rw [hfun]
        exact inner_pairing_smF (G' t)
          (deltaTower_smE hLC G' t c v' B' A' hv' hB' hA') hC'
      have hsmτ : SmOp τ := by
        intro v' A' B' C' hv' hA' hB' hC'
        rw [hτ]
        exact smF_selTerm_sum hLC G' t (fun n : D.ι => (D.sh n).i) (fun n : D.ι => (D.sh n).j)
          (fun n : D.ι => (D.sh n).e) v' A' B' C' hv' hA' hB' hC'
      -- (1) the tower at level `c+1` is the recursed tower at level `c` (definitional)
      have h1 : OpEq (tower (lcOf (G' 0)) (fun _ => aOf G' t) (c + 1))
          (step (lcOf (G' 0)) (tower (lcOf (G' 0)) (fun _ => aOf G' t) c)) :=
        fun _ _ _ _ _ _ _ _ _ => rfl
      -- (2) the recursion step respects the expansion at level `c`
      have h2 : OpEq (step (lcOf (G' 0)) (tower (lcOf (G' 0)) (fun _ => aOf G' t) c))
          (step (lcOf (G' 0)) (fun v A B C y => Wterm G' t c v A B C y + τ v A B C y)) :=
        step_congr hLC G' hIH
      -- (3) linearity in the two summands
      have h3 : OpEq (step (lcOf (G' 0)) (fun v A B C y => Wterm G' t c v A B C y + τ v A B C y))
          (fun v A B C y => step (lcOf (G' 0)) (Wterm G' t c) v A B C y
            + step (lcOf (G' 0)) τ v A B C y) := by
        intro v A B C x hv hA hB hC
        have hfun : (fun v A B C y => Wterm G' t c v A B C y + τ v A B C y)
            = fun v A B C y => (1 : ℝ) * Wterm G' t c v A B C y + 1 * τ v A B C y := by
          funext v A B C y; ring
        rw [hfun,
          step_linear_ext (lcOf (G' 0)) 1 1 (Wterm G' t c) τ hsmW hsmτ v A B C hv hA hB hC x]
        ring
      -- (4) the `i = 0` term and the term-by-term derivative
      have h4 : OpEq (fun v A B C y => step (lcOf (G' 0)) (Wterm G' t c) v A B C y
            + step (lcOf (G' 0)) τ v A B C y)
          (fun v A B C y => (Wterm G' t (c + 1) v A B C y
              + selTerm G' t (shiftL (eC c)) v A B C y)
            + ∑ n : D.ι, (selTerm G' t (shiftL ((D.sh n).e)) v A B C y
                + selTerm G' t (shiftR ((D.sh n).e)) v A B C y)) := by
        refine OpEq.add ?_ ?_
        · intro v A B C x hv hA hB hC
          exact step_Wterm hr G' t c v A B C x hv hA hB hC
        · intro v A B C x hv hA hB hC
          show step (lcOf (G' 0)) τ v A B C x
            = ∑ n : D.ι, (selTerm G' t (shiftL ((D.sh n).e)) v A B C x
                + selTerm G' t (shiftR ((D.sh n).e)) v A B C x)
          calc step (lcOf (G' 0)) τ v A B C x
              = step (lcOf (G' 0))
                  (fun v A B C y => ∑ n : D.ι, selTerm G' t ((D.sh n).e) v A B C y)
                  v A B C x := by rw [hτ]
            _ = ∑ n : D.ι, step (lcOf (G' 0)) (selTerm G' t ((D.sh n).e)) v A B C x :=
                step_sum (lcOf (G' 0)) (fun n : D.ι => selTerm G' t ((D.sh n).e))
                  (fun n => selTerm_smF hLC G' t ((D.sh n).e)) v A B C hv hA hB hC x
            _ = ∑ n : D.ι, (selTerm G' t (shiftL ((D.sh n).e)) v A B C x
                + selTerm G' t (shiftR ((D.sh n).e)) v A B C x) :=
                Finset.sum_congr rfl (fun n _ => hr G' t ((D.sh n).e) v A B C x hv hA hB hC)
      -- (5) the sum over the new index type is the sum of the three pieces
      have h5 : OpEq (fun v A B C y => (Wterm G' t (c + 1) v A B C y
              + selTerm G' t (shiftL (eC c)) v A B C y)
            + ∑ n : D.ι, (selTerm G' t (shiftL ((D.sh n).e)) v A B C y
                + selTerm G' t (shiftR ((D.sh n).e)) v A B C y))
          (fun v A B C y => Wterm G' t (c + 1) v A B C y
            + ∑ n : (D.succ).ι, selTerm G' t (((D.succ).sh n).e) v A B C y) := by
        intro v A B C x hv hA hB hC
        show ((Wterm G' t (c + 1) v A B C x + selTerm G' t (shiftL (eC c)) v A B C x)
              + ∑ n : D.ι, (selTerm G' t (shiftL ((D.sh n).e)) v A B C x
                  + selTerm G' t (shiftR ((D.sh n).e)) v A B C x))
            = Wterm G' t (c + 1) v A B C x
              + ∑ n : (D.succ).ι, selTerm G' t (((D.succ).sh n).e) v A B C x
        have hnewsum : (∑ n : (D.succ).ι, selTerm G' t (((D.succ).sh n).e) v A B C x)
              = (∑ n : D.ι, selTerm G' t (shiftL ((D.sh n).e)) v A B C x)
                + (∑ n : D.ι, selTerm G' t (shiftR ((D.sh n).e)) v A B C x)
                + selTerm G' t (shiftL (eC c)) v A B C x := by
          have e0 : (∑ n : (D.succ).ι, selTerm G' t (((D.succ).sh n).e) v A B C x)
              = ∑ w : D.ι ⊕ D.ι ⊕ PUnit,
                  selTerm G' t ((ExpData.succSh D w).e) v A B C x := rfl
          rw [e0]
          have hs1 : (∑ w : D.ι ⊕ D.ι ⊕ PUnit,
                selTerm G' t ((ExpData.succSh D w).e) v A B C x)
              = (∑ a : D.ι, selTerm G' t ((ExpData.succSh D (Sum.inl a)).e) v A B C x)
                + ∑ b : D.ι ⊕ PUnit,
                    selTerm G' t ((ExpData.succSh D (Sum.inr b)).e) v A B C x :=
            Fintype.sum_sum_type _
          have hs2 : (∑ b : D.ι ⊕ PUnit,
                selTerm G' t ((ExpData.succSh D (Sum.inr b)).e) v A B C x)
              = (∑ a : D.ι,
                    selTerm G' t ((ExpData.succSh D (Sum.inr (Sum.inl a))).e) v A B C x)
                + ∑ u : PUnit,
                    selTerm G' t ((ExpData.succSh D (Sum.inr (Sum.inr u))).e) v A B C x :=
            Fintype.sum_sum_type _
          have hs3 : (∑ u : PUnit,
                selTerm G' t ((ExpData.succSh D (Sum.inr (Sum.inr u))).e) v A B C x)
              = selTerm G' t ((ExpData.succSh D (Sum.inr (Sum.inr PUnit.unit))).e)
                  v A B C x :=
            Fintype.sum_unique _
          rw [hs1, hs2, hs3]
          simp only [ExpData.succSh_inl, ExpData.succSh_inr_inl, ExpData.succSh_inr_inr,
            Shuffle.stepL_e, Shuffle.stepR_e, Shuffle.step0_e]
          ring
        rw [hnewsum, Finset.sum_add_distrib]
        ring_nf
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- Monotonicity of the `BndV` bound in its constant. -/
lemma BndV_mono {G : ℝ → SMet I M} {t : ℝ} {c : ℕ} {C C' : ℝ}
    (h : AMB.BndV G t (deltaTower G t c) C) (hCC : C ≤ C') :
    AMB.BndV G t (deltaTower G t c) C' := by
  intro v X Z hv hX hZ x
  refine le_trans (h v X Z hv hX hZ x) ?_
  have hP1 : 0 ≤ ∏ i : Fin c, (1 + Real.sqrt ((G t).inner x (v i x) (v i x))) := by positivity
  have hP2 : 0 ≤ 1 + Real.sqrt ((G t).inner x (X x) (X x)) := by positivity
  have hP3 : 0 ≤ 1 + Real.sqrt ((G t).inner x (Z x) (Z x)) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hP1)
    hP2) hP3

/-- The constant attached to the level `c+1` in the bound induction, from the constant `Cb` that
bounds all the δ-levels `≤ c`. -/
noncomputable def levelConst (B : ℕ → ℝ) (c : ℕ) (D : ExpData (c + 1)) (Cb : ℝ) : ℝ :=
  B (c + 1) + ∑ n : D.ι, (2 * B ((D.sh n).i - 1)) * (1 + Cb)

lemma levelConst_nonneg (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (c : ℕ) (D : ExpData (c + 1))
    (Cb : ℝ) (hCb : 0 ≤ Cb) : 0 ≤ levelConst B c D Cb := by
  unfold levelConst
  apply add_nonneg (hB _)
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (mul_nonneg (by norm_num) (hB _)) (by linarith)

/-- The bound induction, from the one-step rule `hr` (the statement of
`Work.Diff.EXT.ConnCov.bndV.step_selTerm`).  At every level `c ≤ k` there is a *single* constant
`Cb` bounding the δ-towers `deltaTower G t j` for **all** `j ≤ c`; the expansion at level `c+1` then
gives the bound at level `c+1` in terms of `Cb` (the δ-factors occurring in the expansion all have
level `≤ c`), and the two constants are combined with `max`. -/
lemma bndV_deltaTower_of_step [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hr : StepRule (I := I) (M := M))
    {G : ℝ → SMet I M} {T : ℝ} (hT : 0 < T) (k : ℕ) (Bc : ℕ → ℝ) (hB : ∀ j, 0 ≤ Bc j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      ValBound G t j (tower (lcOf (G 0)) (fun _ => aOf G t) j) (Bc j)) :
    ∃ C : ℕ → ℝ, (∀ c, 0 ≤ C c) ∧ ∀ c, c ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      AMB.BndV G t (deltaTower G t c) (C c) := by
  classical
  -- the expansion data, uniformly in the metric family and the time
  have hDall : ∀ c, ∃ D : ExpData c,
      ∀ (G' : ℝ → SMet I M) (t : ℝ),
        OpEq (tower (lcOf (G' 0)) (fun _ => aOf G' t) c)
          (fun v A B C y => Wterm G' t c v A B C y
            + ∑ n : D.ι, selTerm G' t (D.sh n).e v A B C y) :=
    fun c => expansion_data hLC hr c
  choose D hD using hDall
  -- the `Bnd1` bounds on the `aOf`-tower
  have hBnd1 : ∀ c, c ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      AMB.Bnd1 G t (AMB.pack (tower (lcOf (G 0)) (fun _ => aOf G t) c)) (Bc c) :=
    fun c hc t ht => bnd1_of_valBound hLC G t (hB c) (hA c hc t ht)
  have main : ∀ c, c ≤ k → ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ j, j ≤ c → ∀ t ∈ Set.Ico (T / 2) T, AMB.BndV G t (deltaTower G t j) Cb := by
    intro c
    induction c with
    | zero =>
        intro _
        refine ⟨1 + 2 * Bc 0, ?_, ?_⟩
        · have := hB 0; linarith
        · intro j hj t ht
          have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
          subst hj0
          refine delta_le_of_wterm G t (hD := hB 0) (fun v A B C hv hA' hB' hC' x => ?_)
          have hExp0 := hD 0 G t v A B C x hv hA' hB' hC'
          have hempty : IsEmpty (D 0).ι := ⟨fun n => by
            have h1 : 1 ≤ ((D 0).sh n).i := (D 0).hi n
            have h2 := ((D 0).sh n).hij
            omega⟩
          have hsum0 : (∑ n : (D 0).ι, selTerm G t (((D 0).sh n).e) v A B C x) = 0 := by
            haveI := hempty
            simp
          have hExp : tower (lcOf (G 0)) (fun _ => aOf G t) 0 v A B C x
              = Wterm G t 0 v A B C x := by
            have := hExp0
            simp only [] at this
            rw [hsum0, add_zero] at this
            exact this
          rw [← hExp]
          exact aOf_tower_le hLC G t (hBnd1 0 (by omega) t ht) v A B C hv hA' hB' hC' x
    | succ c ih =>
        intro hc
        obtain ⟨Cb, hCb0, hCbb⟩ := ih (by omega)
        refine ⟨max Cb (1 + 2 * levelConst Bc c (D (c + 1)) Cb), le_max_of_le_left hCb0, ?_⟩
        intro j hj t ht
        rcases eq_or_lt_of_le hj with h | h
        · subst h
          -- the new level: from the expansion at level `c+1`
          refine BndV_mono (delta_le_of_wterm G t
            (hD := levelConst_nonneg Bc hB c (D (c + 1)) Cb hCb0) (fun v A B C hv hA' hB' hC' x => ?_))
            (le_max_right _ _)
          have hExp := hD (c + 1) G t v A B C x hv hA' hB' hC'
          -- the metric-tower bounds at the levels occurring in the expansion
          have hMi : ∀ n : (D (c + 1)).ι,
              MetricBnd G t (((D (c + 1)).sh n).i) (2 * Bc (((D (c + 1)).sh n).i - 1)) := by
            intro n
            have hpos : 1 ≤ ((D (c + 1)).sh n).i := (D (c + 1)).hi n
            have hik : ((D (c + 1)).sh n).i - 1 ≤ k := by
              have h2 := ((D (c + 1)).sh n).hij
              omega
            convert metricBnd_succ hLC G t (hBnd1 _ hik t ht) using 1
            exact (Nat.sub_add_cancel hpos).symm
          -- the δ-bounds at the levels occurring in the expansion
          have hCj : ∀ n : (D (c + 1)).ι,
              AMB.BndV G t (deltaTower G t (((D (c + 1)).sh n).j)) Cb := by
            intro n
            have hjle : ((D (c + 1)).sh n).j ≤ c := by
              have h1 : 1 ≤ ((D (c + 1)).sh n).i := (D (c + 1)).hi n
              have h2 := ((D (c + 1)).sh n).hij
              omega
            exact hCbb _ hjle t ht
          have hS := sum_selTerm_le hLC G t (fun n : (D (c + 1)).ι => ((D (c + 1)).sh n).i)
            (fun n : (D (c + 1)).ι => ((D (c + 1)).sh n).j)
            (fun n : (D (c + 1)).ι => ((D (c + 1)).sh n).e)
            (fun n => (D (c + 1)).hi n)
            (fun n => 2 * Bc (((D (c + 1)).sh n).i - 1)) (fun _ => Cb)
            (fun n => mul_nonneg (by norm_num) (hB _)) (fun _ => hCb0) hMi hCj v A B C hv hA' hB' hC' x
          have hT := aOf_tower_le hLC G t (hBnd1 (c + 1) hc t ht) v A B C hv hA' hB' hC' x
          have hW1 : Wterm G t (c + 1) v A B C x
              = tower (lcOf (G 0)) (fun _ => aOf G t) (c + 1) v A B C x
                - ∑ n : (D (c + 1)).ι, selTerm G t (((D (c + 1)).sh n).e) v A B C x := by
            linarith [hExp]
          rw [hW1, levelConst]
          calc |tower (lcOf (G 0)) (fun _ => aOf G t) (c + 1) v A B C x
                - ∑ n : (D (c + 1)).ι,
                    selTerm G t (((D (c + 1)).sh n).e) v A B C x|
              ≤ |tower (lcOf (G 0)) (fun _ => aOf G t) (c + 1) v A B C x|
                + |∑ n : (D (c + 1)).ι,
                    selTerm G t (((D (c + 1)).sh n).e) v A B C x| := abs_sub _ _
            _ ≤ Bc (c + 1) * ((∏ j : Fin (c + 1),
                    (1 + Real.sqrt ((G t).inner x (v j x) (v j x))))
                  * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
                  * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
                  * (1 + Real.sqrt ((G t).inner x (C x) (C x))))
                + (∑ n : (D (c + 1)).ι,
                    (2 * Bc (((D (c + 1)).sh n).i - 1)) * (1 + Cb))
                  * ((∏ j : Fin (c + 1),
                    (1 + Real.sqrt ((G t).inner x (v j x) (v j x))))
                  * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
                  * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
                  * (1 + Real.sqrt ((G t).inner x (C x) (C x)))) := add_le_add hT hS
            _ = (Bc (c + 1) + ∑ n : (D (c + 1)).ι,
                    (2 * Bc (((D (c + 1)).sh n).i - 1)) * (1 + Cb))
                  * ((∏ j : Fin (c + 1),
                    (1 + Real.sqrt ((G t).inner x (v j x) (v j x))))
                  * (1 + Real.sqrt ((G t).inner x (A x) (A x)))
                  * (1 + Real.sqrt ((G t).inner x (B x) (B x)))
                  * (1 + Real.sqrt ((G t).inner x (C x) (C x)))) := by ring
        · -- the old levels
          exact BndV_mono (hCbb j (by omega) t ht) (le_max_left _ _)
  obtain ⟨Cb, hCb0, hCbb⟩ := main k le_rfl
  refine ⟨fun _ => Cb, fun _ => hCb0, fun c hc t ht => hCbb c hc t ht⟩


theorem bndV_deltaTower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hT : 0 < T)
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ C : ℕ → ℝ, (∀ c, 0 ≤ C c) ∧ ∀ c, c ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ConnCov.AMB.BndV G t (Work.Diff.EXT.ConnCov.DTB.deltaTower G t c) (C c) :=
  bndV_deltaTower_of_step (I := I) (M := M) hLC (stepRule_holds (I := I) (M := M) hLC)
    hT k B hB hA

end Work.Diff.EXT.ConnCov.DTB
