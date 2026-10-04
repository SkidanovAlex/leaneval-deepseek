import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxDecomp
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxBounds

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The δ-tower bound from the `aOf`-tower bound (`hA`)

This module assembles the bound of the fixed-connection δ-tower `V_c = ∇^{g_0,c}δ` of the connection
difference from the hypothesis `hA` (the `ValBound` bounds of the tower of `aOf = g_t ⊙ δ`), using

* the **Leibniz expansion** `tower aOf c = Wterm c + Σ (terms with metric level ≥ 1)`
  (`Work.Diff.EXT.ConnCov.DT.exists_combData`);
* the bound of one expansion term (`Work.Diff.EXT.ConnCov.DT.selTerm_val_bound`), whose metric factor is
  bounded by `hA` at level `m n` (through `gtTower_val_bound`) and whose δ factor is bounded by the
  *induction hypothesis* at level `j n < c`;
* the passage from the bound of the lowering `Wterm c` to the bound of `V_c` itself
  (`TB_of_wterm_bound`), using that the moving metric is an isometry for its own pairing.

The constants are produced by the recursion `newConst` and the whole bound is uniform on the time
interval `Ico (T/2) T`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ConnCov.DT

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The sharp bound of the δ-tower at level `c`**: the `G t`-norm of `∇^{g_0,c}δ` on arbitrary
smooth fields is bounded by `D` times the product of the `(1 + √⟨·,·⟩)`-factors of the directions
and the `√⟨·,·⟩`-factors of the two tensor slots. -/
def TB (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) (D : ℝ) : Prop :=
  ∀ (d : Fin c → TF (I := I) (M := M)) (Y X : TF (I := I) (M := M)) (x : M),
    (∀ p, SmE I M (d p)) → SmE I M Y → SmE I M X →
    Real.sqrt ((G t).inner x (deltaTower G t c d Y X x) (deltaTower G t c d Y X x))
      ≤ D * (Finset.univ.prod (fun p : Fin c =>
            (1 + Real.sqrt ((G t).inner x (d p x) (d p x)))))
          * Real.sqrt ((G t).inner x (Y x) (Y x))
          * Real.sqrt ((G t).inner x (X x) (X x))

/-- The constant produced at level `c`: the `hA`-constant at level `c` plus, for every term of the
expansion, `2 B (m n) D (j n)` (the factor `2` coming from `gtTower_succ_eq_swap`). -/
noncomputable def newConst (Bc : ℕ → ℝ) {c : ℕ} (Dc : CombData c) (Dlow : ℕ → ℝ) : ℝ :=
  Bc c + ∑ n : Dc.ι, 2 * Bc (Dc.m n) * Dlow (Dc.j n)

theorem newConst_nonneg {Bc : ℕ → ℝ} (hB : ∀ j, 0 ≤ Bc j) {c : ℕ} (Dc : CombData c)
    {Dlow : ℕ → ℝ} (hDlow : ∀ j, j < c → 0 ≤ Dlow j) : 0 ≤ newConst Bc Dc Dlow := by
  rw [newConst]
  refine add_nonneg (hB c) (Finset.sum_nonneg (fun n _ => ?_))
  have h1 : Dc.j n < c := by have := Dc.hmj n; omega
  have h2 : 0 ≤ Dlow (Dc.j n) := hDlow _ h1
  nlinarith [hB (Dc.m n), h2]

/-- The explicit value of the lowering `Wterm`. -/
theorem Wterm_apply_eq (G : ℝ → SMet I M) (t : ℝ) (c : ℕ)
    (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (y : M) :
    Wterm G t c v A B C y = (G t).inner y (deltaTower G t c v B A y) (C y) := by
  simp only [Wterm, selTerm, gtTower, gtower, gtBase]

/-- **The bound of the lowering `Wterm c`** from the expansion (the hypothesis `hA` at level `c`)
and the induction hypothesis at the lower levels. -/
theorem wterm_bound_of_expansion [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) (T : ℝ) (hT : 0 < T)
    (k : ℕ) (Bc : ℕ → ℝ) (hB : ∀ j, 0 ≤ Bc j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      ValBound G t j (tower (lcOf (G 0)) (fun _ => aOf G t) j) (Bc j))
    {c : ℕ} (hc : c ≤ k) (Dc : CombData c)
    (hDc : ∀ (G' : ℝ → SMet I M) (t' : ℝ),
      OpEqSel (tower (lcOf (G' 0)) (fun _ => aOf G' t') c)
        (fun v A B C y => Wterm G' t' c v A B C y + CombTerm Dc G' t' v A B C y))
    (Dlow : ℕ → ℝ) (hDlow0 : ∀ j, j < c → 0 ≤ Dlow j)
    (hDlow : ∀ j, j < c → ∀ t ∈ Set.Ico (T / 2) T, TB G t j (Dlow j)) :
    ∀ t ∈ Set.Ico (T / 2) T, ∀ (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
      (x : M), (∀ p, SmE I M (v p)) → SmE I M A → SmE I M B → SmE I M C →
      |Wterm G t c v A B C x|
        ≤ newConst Bc Dc Dlow * ((Finset.univ.prod (fun p : Fin c =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x))) := by
  intro t ht v A B C x hv hA' hB' hC'
  have hm0 : ∀ p : Fin c, 0 ≤ Real.sqrt ((G t).inner x (v p x) (v p x)) :=
    fun p => Real.sqrt_nonneg _
  have hsA : 0 ≤ Real.sqrt ((G t).inner x (A x) (A x)) := Real.sqrt_nonneg _
  have hsB : 0 ≤ Real.sqrt ((G t).inner x (B x) (B x)) := Real.sqrt_nonneg _
  have hsC : 0 ≤ Real.sqrt ((G t).inner x (C x) (C x)) := Real.sqrt_nonneg _
  -- the expansion
  have hex := hDc G t v A B C x hv hA' hB' hC'
  have hW : Wterm G t c v A B C x
      = tower (lcOf (G 0)) (fun _ => aOf G t) c v A B C x
        - ∑ n : Dc.ι,
            selTerm G t c (Dc.m n + 1) (Dc.j n) (Dc.F n) (Dc.G' n) v A B C x := by
    have h : tower (lcOf (G 0)) (fun _ => aOf G t) c v A B C x
        = Wterm G t c v A B C x
          + ∑ n : Dc.ι,
              selTerm G t c (Dc.m n + 1) (Dc.j n) (Dc.F n) (Dc.G' n) v A B C x := hex
    linarith
  -- the bound of the tower (the hypothesis `hA` at level `c`, weakened to `∏ (1 + √·)`)
  have htow : |tower (lcOf (G 0)) (fun _ => aOf G t) c v A B C x|
      ≤ Bc c * ((Finset.univ.prod (fun p : Fin c =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
          * Real.sqrt ((G t).inner x (A x) (A x))
          * Real.sqrt ((G t).inner x (B x) (B x))
          * Real.sqrt ((G t).inner x (C x) (C x))) := by
    have h := aOfTower_val_bound hLC G t c (Bc c) (hA c hc t ht) x v A B C hv hA' hB' hC'
    have hprod : (Finset.univ.prod (fun p : Fin c =>
          Real.sqrt ((G t).inner x (v p x) (v p x))))
        ≤ Finset.univ.prod (fun p : Fin c =>
          (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))) :=
      Finset.prod_le_prod₀ (fun p _ => hm0 p) (fun p _ => by linarith [hm0 p])
    have step : Bc c * (Finset.univ.prod (fun p : Fin c =>
            Real.sqrt ((G t).inner x (v p x) (v p x))))
        ≤ Bc c * (Finset.univ.prod (fun p : Fin c =>
            (1 + Real.sqrt ((G t).inner x (v p x) (v p x))))) :=
      mul_le_mul_of_nonneg_left hprod (hB c)
    have h1 := mul_le_mul_of_nonneg_right step hsA
    have h2 := mul_le_mul_of_nonneg_right h1 hsB
    exact le_trans h (le_trans (mul_le_mul_of_nonneg_right h2 hsC) (le_of_eq (by ring)))
  -- the bound of every expansion term
  have hterm : ∀ n : Dc.ι,
      |selTerm G t c (Dc.m n + 1) (Dc.j n) (Dc.F n) (Dc.G' n) v A B C x|
        ≤ (2 * Bc (Dc.m n) * Dlow (Dc.j n)) * ((Finset.univ.prod (fun p : Fin c =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x))) := by
    intro n
    have hj : Dc.j n < c := by have := Dc.hmj n; omega
    have hmk : Dc.m n ≤ k := by have := Dc.hmj n; omega
    exact selTerm_val_bound (I := I) (M := M) hLC G t x (Dc.hmj n) (by omega) (Dc.F n)
      (Dc.G' n) (Dc.hfinj n) (Dc.hginj n) (Dc.hdisj n)
      (range_union_eq_univ (Dc.hmj n) (Dc.F n) (Dc.G' n) (Dc.hfinj n) (Dc.hginj n)
        (Dc.hdisj n))
      (2 * Bc (Dc.m n)) (Dlow (Dc.j n)) (by linarith [hB (Dc.m n)]) (hDlow0 (Dc.j n) hj)
      (fun d Y Z hd hY hZ =>
        gtTower_val_bound (I := I) (M := M) hLC G t x (Dc.m n) (Bc (Dc.m n))
          (hB (Dc.m n)) ((aOfTower_val_bound hLC G t (Dc.m n) (Bc (Dc.m n))
            (hA (Dc.m n) hmk t ht)) x) d Y Z hd hY hZ)
      (fun d Y X hd hY hX => (hDlow (Dc.j n) hj t ht) d Y X x hd hY hX)
      v A B C hv hA' hB' hC'
  -- the bound of the sum
  have hsum : |∑ n : Dc.ι, selTerm G t c (Dc.m n + 1) (Dc.j n) (Dc.F n) (Dc.G' n) v A B C x|
      ≤ (∑ n : Dc.ι, 2 * Bc (Dc.m n) * Dlow (Dc.j n))
        * ((Finset.univ.prod (fun p : Fin c =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x))) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n _ => hterm n)) ?_
    exact le_of_eq (Finset.sum_mul ..).symm
  -- assembly
  calc |Wterm G t c v A B C x|
      = |tower (lcOf (G 0)) (fun _ => aOf G t) c v A B C x
          - ∑ n : Dc.ι,
              selTerm G t c (Dc.m n + 1) (Dc.j n) (Dc.F n) (Dc.G' n) v A B C x| := by
        rw [hW]
    _ ≤ |tower (lcOf (G 0)) (fun _ => aOf G t) c v A B C x|
          + |∑ n : Dc.ι,
              selTerm G t c (Dc.m n + 1) (Dc.j n) (Dc.F n) (Dc.G' n) v A B C x| := by
        rw [sub_eq_add_neg]
        calc |tower (lcOf (G 0)) (fun _ => aOf G t) c v A B C x
              + -(∑ n : Dc.ι,
                  selTerm G t c (Dc.m n + 1) (Dc.j n) (Dc.F n) (Dc.G' n) v A B C x)|
            ≤ |tower (lcOf (G 0)) (fun _ => aOf G t) c v A B C x|
              + |-(∑ n : Dc.ι,
                  selTerm G t c (Dc.m n + 1) (Dc.j n) (Dc.F n) (Dc.G' n) v A B C x)| :=
              abs_add_le _ _
          _ = _ := by rw [abs_neg]
    _ ≤ Bc c * ((Finset.univ.prod (fun p : Fin c =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x)))
          + (∑ n : Dc.ι, 2 * Bc (Dc.m n) * Dlow (Dc.j n))
            * ((Finset.univ.prod (fun p : Fin c =>
                  (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
                * Real.sqrt ((G t).inner x (A x) (A x))
                * Real.sqrt ((G t).inner x (B x) (B x))
                * Real.sqrt ((G t).inner x (C x) (C x))) := add_le_add htow hsum
    _ = newConst Bc Dc Dlow * ((Finset.univ.prod (fun p : Fin c =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x))) := by
        rw [newConst]; ring

/-- **From the bound of the lowering to the bound of the δ-tower** (the moving metric is an isometry
for its own pairing). -/
theorem TB_of_wterm_bound [I.Boundaryless] [T2Space M]
    (G : ℝ → SMet I M) (t : ℝ) {c : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M),
      (∀ p, SmE I M (v p)) → SmE I M A → SmE I M B → SmE I M C →
      |Wterm G t c v A B C x|
        ≤ D * ((Finset.univ.prod (fun p : Fin c =>
              (1 + Real.sqrt ((G t).inner x (v p x) (v p x)))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x)))) :
    TB G t c D := by
  intro d Y X x hd hY hX
  set P : ℝ := Finset.univ.prod (fun p : Fin c =>
      (1 + Real.sqrt ((G t).inner x (d p x) (d p x)))) with hP
  set sX : ℝ := Real.sqrt ((G t).inner x (X x) (X x)) with hsX
  set sY : ℝ := Real.sqrt ((G t).inner x (Y x) (Y x)) with hsY
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact Finset.prod_nonneg (fun p _ => by
      have := Real.sqrt_nonneg ((G t).inner x (d p x) (d p x)); linarith)
  have hsX0 : 0 ≤ sX := by rw [hsX]; exact Real.sqrt_nonneg _
  have hsY0 : 0 ≤ sY := by rw [hsY]; exact Real.sqrt_nonneg _
  set u : TangentSpace I x := deltaTower G t c d Y X x with hu
  set r : ℝ := Real.sqrt ((G t).inner x u u) with hr
  have hu0 : 0 ≤ (G t).inner x u u := inner_self_nonneg (G t) x u
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hC : SmE I M (Submission.Diff.smoothExt x u) := Work.Diff.GE.smoothExt_cmdiff x u
  have hb := h d X Y (Submission.Diff.smoothExt x u) x hd hX hY hC
  have hbu : Wterm G t c d X Y (Submission.Diff.smoothExt x u) x = r * r := by
    rw [Wterm_apply_eq, ← hu, Work.Diff.GE.smoothExt_apply, hr, Real.mul_self_sqrt hu0]
  have hbr : Real.sqrt ((G t).inner x (Submission.Diff.smoothExt x u x)
      (Submission.Diff.smoothExt x u x)) = r := by
    rw [Work.Diff.GE.smoothExt_apply, hr]
  rw [hbu, hbr, abs_of_nonneg (mul_nonneg hr0 hr0)] at hb
  rw [← hP, ← hsX, ← hsY] at hb
  have hb' : r * r ≤ (D * P * sX * sY) * r := le_trans hb (le_of_eq (by ring))
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (mul_nonneg (mul_nonneg hD hP0) hsY0) hsX0
  · have hle : r ≤ D * P * sX * sY := le_of_mul_le_mul_right hb' hpos
    exact le_trans hle (le_of_eq (by ring))

/-- **The bound at one level** from the expansion data and the lower-level bounds. -/
theorem TB_newConst [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) (T : ℝ) (hT : 0 < T)
    (k : ℕ) (Bc : ℕ → ℝ) (hB : ∀ j, 0 ≤ Bc j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      ValBound G t j (tower (lcOf (G 0)) (fun _ => aOf G t) j) (Bc j))
    {c : ℕ} (hc : c ≤ k) (Dc : CombData c)
    (hDc : ∀ (G' : ℝ → SMet I M) (t' : ℝ),
      OpEqSel (tower (lcOf (G' 0)) (fun _ => aOf G' t') c)
        (fun v A B C y => Wterm G' t' c v A B C y + CombTerm Dc G' t' v A B C y))
    (Dlow : ℕ → ℝ) (hDlow0 : ∀ j, j < c → 0 ≤ Dlow j)
    (hDlow : ∀ j, j < c → ∀ t ∈ Set.Ico (T / 2) T, TB G t j (Dlow j)) :
    ∀ t ∈ Set.Ico (T / 2) T, TB G t c (newConst Bc Dc Dlow) := by
  intro t ht
  refine TB_of_wterm_bound G t (newConst_nonneg hB Dc hDlow0) ?_
  intro v A B C x hv hA' hB' hC'
  exact wterm_bound_of_expansion hLC G T hT k Bc hB hA hc Dc hDc Dlow hDlow0 hDlow t ht v A B C x
    hv hA' hB' hC'

/-- **The uniform δ-tower bound from `hA`.**  There are constants `D c` (for `c ≤ k`), nonnegative,
such that on the whole time interval `Ico (T/2) T` the δ-tower at level `c` satisfies the sharp
bound `TB`. -/
theorem exists_TB [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) (T : ℝ) (hT : 0 < T)
    (k : ℕ) (Bc : ℕ → ℝ) (hB : ∀ j, 0 ≤ Bc j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      ValBound G t j (tower (lcOf (G 0)) (fun _ => aOf G t) j) (Bc j)) :
    ∃ D : ℕ → ℝ, (∀ c, c ≤ k → 0 ≤ D c) ∧
      ∀ c, c ≤ k → ∀ t ∈ Set.Ico (T / 2) T, TB G t c (D c) := by
  classical
  have key : ∀ n, n ≤ k → ∃ D : ℕ → ℝ, (∀ c, c ≤ n → 0 ≤ D c) ∧
      ∀ c, c ≤ n → ∀ t ∈ Set.Ico (T / 2) T, TB G t c (D c) := by
    intro n
    induction n with
    | zero =>
        intro _
        obtain ⟨Dc, hDc⟩ := exists_combData (I := I) (M := M) hLC 0
        refine ⟨fun c => if c = 0 then newConst Bc Dc (fun _ => 0) else 0, ?_, ?_⟩
        · intro c hc
          dsimp only
          rcases eq_or_ne c 0 with h | h
          · rw [if_pos h]
            exact newConst_nonneg hB Dc (fun j hj => by omega)
          · rw [if_neg h]
        · intro c hc t ht
          have hc0 : c = 0 := by omega
          subst hc0
          dsimp only
          rw [if_pos rfl]
          exact TB_newConst hLC G T hT k Bc hB hA (by omega) Dc hDc (fun _ => 0)
            (fun j hj => by omega) (fun j hj => by omega) t ht
    | succ n ih =>
        intro hn
        obtain ⟨Dold, hDold0, hDoldB⟩ := ih (by omega)
        obtain ⟨Dc, hDc⟩ := exists_combData (I := I) (M := M) hLC (n + 1)
        refine ⟨Function.update Dold (n + 1) (newConst Bc Dc Dold), ?_, ?_⟩
        · intro c hc
          rcases eq_or_ne c (n + 1) with h | h
          · subst h
            rw [Function.update_self]
            exact newConst_nonneg hB Dc (fun j hj => hDold0 j (by omega))
          · rw [Function.update_of_ne h]
            exact hDold0 c (by omega)
        · intro c hc t ht
          rcases eq_or_ne c (n + 1) with h | h
          · subst h
            rw [Function.update_self]
            refine TB_newConst hLC G T hT k Bc hB hA (by omega) Dc hDc Dold
              (fun j hj => hDold0 j (by omega)) (fun j hj => fun t ht => ?_) t ht
            exact hDoldB j (by omega) t ht
          · rw [Function.update_of_ne h]
            exact hDoldB c (by omega) t ht
  exact key k le_rfl

end Work.Diff.EXT.ConnCov.DT
