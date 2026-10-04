import Mathlib
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ATower.step_flip
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.RicTr.movingRicHonestTower
import Submission.Work.Diff.EXT.ConnCov.RicTr.deltaTower_bound_of_hA
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.conn_diff_bound_of_shibounds
import Submission.Work.Diff.EXT.ATower.scaleTup
import Submission.Work.Diff.EXT.ATower.pDiter2_multi_homog
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs
import Submission.Work.Diff.EXT.ConnCov.sharp_of_bnd1_homog
import Submission.Work.Diff.EXT.ConnCov.RicFlip.honestTowerBoundUniform
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packedTowerShift
import Submission.Work.Diff.EXT.ConnCov.RicFlip.RicT_props
import Submission.Work.Diff.EXT.ConnCov.RicFlip.insAtomAdd
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TermSlotSm
import Submission.Work.Diff.EXT.ConnCov.htower_eq_tower2
import Submission.Work.Diff.EXT.ATower.movingRicTowerBnd1
import Submission.Work.Diff.EXT.ATower.fixedDeltaAtomBndV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ATower

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Comparing the two metrics on the collapsed slab

`hmet` compares the metrics `G t` and `G 0` on `[0,T)` with the factor `exp (2 n C t)`.  On the
collapsed slab `[T/2,T)` this gives the uniform factor `K := exp (n C T)` for the *square roots* of
the self-pairings, which is what converts the `(1 + √·)`-shaped bound `Bnd1` (and the sharp product)
from one metric to the other. -/

/-- `√(exp z) = exp (z/2)`. -/
lemma sqrt_exp (z : ℝ) : Real.sqrt (Real.exp z) = Real.exp (z / 2) := by
  have h1 : Real.exp z = (Real.exp (z / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]

/-- The `G 0`-norm is at most `K` times the `G t`-norm on the collapsed slab, with
`K = exp (n C T)`. -/
lemma sqrt_inner_G0_le (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hC : 0 ≤ C) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Ico (T / 2) T) (x : M)
    (u : TangentSpace I x) :
    Real.sqrt ((G 0).inner x u u)
      ≤ Real.exp ((Module.finrank ℝ E : ℝ) * C * T) * Real.sqrt ((G t).inner x u u) := by
  have ht0 : t ∈ Set.Ico 0 T := ⟨by linarith [ht.1, hT], ht.2⟩
  have h2 := (hmet t ht0 x u).2
  have hmono : Real.sqrt ((G 0).inner x u u)
      ≤ Real.sqrt (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u) :=
    Real.sqrt_le_sqrt h2
  rw [Real.sqrt_mul (Real.exp_nonneg _), sqrt_exp] at hmono
  refine le_trans hmono ?_
  have hexp : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t / 2)
      ≤ Real.exp ((Module.finrank ℝ E : ℝ) * C * T) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : 0 ≤ ((Module.finrank ℝ E : ℝ)) * C :=
      mul_nonneg (Nat.cast_nonneg _) hC
    have h2 : t ≤ T := le_of_lt ht.2
    nlinarith [h1, h2]
  exact mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _)

/-- The `G t`-norm is at most `K` times the `G 0`-norm on the collapsed slab, with
`K = exp (n C T)`. -/
lemma sqrt_inner_Gt_le (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hC : 0 ≤ C) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Ico (T / 2) T) (x : M)
    (u : TangentSpace I x) :
    Real.sqrt ((G t).inner x u u)
      ≤ Real.exp ((Module.finrank ℝ E : ℝ) * C * T) * Real.sqrt ((G 0).inner x u u) := by
  have ht0 : t ∈ Set.Ico 0 T := ⟨by linarith [ht.1, hT], ht.2⟩
  have h2 := (hmet t ht0 x u).1
  have hmono : Real.sqrt ((G t).inner x u u)
      ≤ Real.sqrt (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u) :=
    Real.sqrt_le_sqrt h2
  rw [Real.sqrt_mul (Real.exp_nonneg _), sqrt_exp] at hmono
  refine le_trans hmono ?_
  have hexp : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t / 2)
      ≤ Real.exp ((Module.finrank ℝ E : ℝ) * C * T) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : 0 ≤ ((Module.finrank ℝ E : ℝ)) * C :=
      mul_nonneg (Nat.cast_nonneg _) hC
    have h2 : t ≤ T := le_of_lt ht.2
    nlinarith [h1, h2]
  exact mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _)

/-- **Metric conversion of the `(1 + √·)`-bound `Bnd1`**: if the `g₁`-norm of every vector is at
most `K` times its `g₂`-norm, a `Bnd1`-bound in `g₁` transfers to `g₂` with the factor
`(1 + K)^N`. -/
lemma bnd1_of_metric_le {g₁ g₂ : Submission.Diff.SMet I M} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x : M, ∀ u : TangentSpace I x,
      Real.sqrt (g₁.inner x u u) ≤ K * Real.sqrt (g₂.inner x u u))
    {t : ℝ} {N : ℕ} {τ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) N}
    {Cc : ℝ} (hCc : 0 ≤ Cc)
    (hτ : Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => g₁) t τ Cc) :
    Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => g₂) t τ (Cc * (1 + K) ^ N) := by
  intro F x hF
  have h0 := hτ F x hF
  have hprod : (∏ j : Fin N, (1 + Real.sqrt (g₁.inner x (F j x) (F j x))))
      ≤ (1 + K) ^ N * ∏ j : Fin N, (1 + Real.sqrt (g₂.inner x (F j x) (F j x))) := by
    have h1 : ∀ j : Fin N, (1 + Real.sqrt (g₁.inner x (F j x) (F j x)))
        ≤ (1 + K) * (1 + Real.sqrt (g₂.inner x (F j x) (F j x))) := by
      intro j
      have hb := h x (F j x)
      have hb0 : 0 ≤ Real.sqrt (g₂.inner x (F j x) (F j x)) := Real.sqrt_nonneg _
      have hstep : (1 + Real.sqrt (g₁.inner x (F j x) (F j x)))
          ≤ 1 + K * Real.sqrt (g₂.inner x (F j x) (F j x)) := by linarith
      have hstep2 : (1 : ℝ) + K * Real.sqrt (g₂.inner x (F j x) (F j x))
          ≤ (1 + K) * (1 + Real.sqrt (g₂.inner x (F j x) (F j x))) := by
        nlinarith [hb0, hK]
      linarith
    calc (∏ j : Fin N, (1 + Real.sqrt (g₁.inner x (F j x) (F j x))))
        ≤ ∏ j : Fin N, (1 + K) * (1 + Real.sqrt (g₂.inner x (F j x) (F j x))) :=
          Finset.prod_le_prod₀ (fun j _ => by
            have := Real.sqrt_nonneg (g₁.inner x (F j x) (F j x)); linarith)
            (fun j _ => h1 j)
      _ = (1 + K) ^ N * ∏ j : Fin N, (1 + Real.sqrt (g₂.inner x (F j x) (F j x))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc |τ F x| ≤ Cc * ∏ j : Fin N, (1 + Real.sqrt (g₁.inner x (F j x) (F j x))) := h0
    _ ≤ Cc * ((1 + K) ^ N * ∏ j : Fin N, (1 + Real.sqrt (g₂.inner x (F j x) (F j x)))) :=
        mul_le_mul_of_nonneg_left hprod hCc
    _ = Cc * (1 + K) ^ N * ∏ j : Fin N, (1 + Real.sqrt (g₂.inner x (F j x) (F j x))) := by ring

/-- **Metric conversion of a sharp product**: the product of the `g₁`-norms is at most `K^N` times
the product of the `g₂`-norms. -/
lemma prod_sqrt_le_of_metric {g₁ g₂ : Submission.Diff.SMet I M} {K : ℝ}
    (h : ∀ x : M, ∀ u : TangentSpace I x,
      Real.sqrt (g₁.inner x u u) ≤ K * Real.sqrt (g₂.inner x u u))
    {N : ℕ} (F : Fin N → (Π y : M, TangentSpace I y)) (x : M) :
    (∏ j : Fin N, Real.sqrt (g₁.inner x (F j x) (F j x)))
      ≤ K ^ N * ∏ j : Fin N, Real.sqrt (g₂.inner x (F j x) (F j x)) := by
  calc (∏ j : Fin N, Real.sqrt (g₁.inner x (F j x) (F j x)))
      ≤ ∏ j : Fin N, K * Real.sqrt (g₂.inner x (F j x) (F j x)) :=
        Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ => h x (F j x))
    _ = K ^ N * ∏ j : Fin N, Real.sqrt (g₂.inner x (F j x) (F j x)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## The flip calculus: bookkeeping

The bound of the fixed tower is obtained by expanding the **moving** Ric tower
`pDiter2 (lcOf (G t)) (ric2 (G t)) n` in terms of the terms of `RicFlip.HonestUnif.Expand n` for the
*reversed* family `G' s = G (t - s)`: with that family the leaves of the calculus are the **fixed**
towers `pDiter2 (lcOf (G 0)) (ric2 (G t)) i` and the atoms are the **fixed** δ-towers
`deltaTowerM G' t ord = ∇^{G 0,ord}(∇^{G 0} − ∇^{G t})`.  The `leaf n` term of the expansion is the
fixed tower itself, so the identity

`pDiter2 (lcOf (G 0)) base n = pDiter2 (lcOf (G t)) base n − Σ_{T ∈ Expand n, T ≠ leaf n} evalT T`

inverts the expansion, and the `n`-th fixed tower is bounded by the `n`-th *moving* tower (Shi) plus
the finitely many terms whose leaves have order `< n` (induction) and whose atoms have order `< n`
(the fixed δ-tower bounds). -/

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif
  Work.Diff.EXT.ConnCov.RicFlip.O in
/-- The bound shapes depend on the family only through the metric at the parameter. -/
lemma bnd1_fam_congr {G₁ G₂ : ℝ → Submission.Diff.SMet I M} {t : ℝ} (h : G₁ t = G₂ t)
    {N : ℕ} {τ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) N} {Cc : ℝ} :
    Work.Diff.EXT.ConnCov.AMB.Bnd1 G₁ t τ Cc ↔ Work.Diff.EXT.ConnCov.AMB.Bnd1 G₂ t τ Cc := by
  simp only [Work.Diff.EXT.ConnCov.AMB.Bnd1, h]

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip in
/-- The `δ`-derivative bound shape depends on the family only through the metric at the parameter. -/
lemma bndV_fam_congr {G₁ G₂ : ℝ → Submission.Diff.SMet I M} {t : ℝ} (h : G₁ t = G₂ t)
    {c : ℕ} {Θ : (Fin c → Work.Diff.EXT.ATower.TF (I := I) (M := M)) →
      Work.Diff.EXT.ATower.TF (I := I) (M := M) → Work.Diff.EXT.ATower.TF (I := I) (M := M) →
      Work.Diff.EXT.ATower.TF (I := I) (M := M)} {Cc : ℝ} :
    Work.Diff.EXT.ConnCov.AMB.BndV G₁ t Θ Cc ↔ Work.Diff.EXT.ConnCov.AMB.BndV G₂ t Θ Cc := by
  simp only [Work.Diff.EXT.ConnCov.AMB.BndV, h]

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- The leaf order of a term is at most its cost. -/
lemma leafOrd_le_costT {n : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term n) :
    Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T
      ≤ Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T := by
  induction T with
  | leaf i => simp only [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd, Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT]; exact le_rfl
  | @comp a b ord Φ T ih =>
      simp only [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd_comp, Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT_comp]
      omega

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- `nextT` raises the leaf order by at most one. -/
lemma leafOrd_mem_nextT {n : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term n)
    (U : Work.Diff.EXT.ConnCov.RicFlip.Term (n + 1))
    (h : U ∈ Work.Diff.EXT.ConnCov.RicFlip.nextT T) :
    Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd U
      ≤ Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T + 1 := by
  induction T with
  | leaf i =>
      rw [Work.Diff.EXT.ConnCov.RicFlip.nextT, List.mem_singleton] at h
      subst h
      simp only [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd]
      omega
  | @comp a b ord Φ S ih =>
      rw [Work.Diff.EXT.ConnCov.RicFlip.nextT, List.mem_append, List.mem_map] at h
      rcases h with ⟨U', hU', rfl⟩ | h
      · simp only [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd_comp]
        exact ih U' hU'
      · rw [List.mem_singleton] at h
        subst h
        simp only [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd_comp]
        omega

/-! ## The `SmP`/`SlotAddP` invariants of the term calculus for an arbitrary base

The flip induction uses the term calculus of `RicFlip.HonestUnif` for the family `s ↦ G (t - s)`
(the time-reversed flow) and the base `ric2 (G t)`.  The two structural inputs of the induction
(`hsmT`, `hslot`) are proved here for an **arbitrary** family and an **arbitrary** base, by induction
on the term. -/

section TermGlue

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip
open Work.Diff.EXT.ConnCov.RicFlip.HonestUnif

variable [I.Boundaryless] [T2Space M]

/-- **The invariants of the iterated packed tower for an arbitrary base**: slot additivity and
smoothness propagate from the base along `AMB.pD` with the Levi-Civita connection. -/
theorem pDiter2_good (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {β : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) 2}
    (hadd : Work.Diff.EXT.ConnCov.AMB.SlotAddP β) (hsm : Work.Diff.EXT.ConnCov.AMB.SmP β) :
    ∀ i, Work.Diff.EXT.ConnCov.AMB.SlotAddP
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf g) β i)
      ∧ Work.Diff.EXT.ConnCov.AMB.SmP
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf g) β i) := by
  intro i
  induction i with
  | zero => exact ⟨hadd, hsm⟩
  | succ i ih =>
      exact ⟨Work.Diff.EXT.ConnCov.RicFlip.pD_SlotAddP (I := I) (M := M) hLC g ih.1 ih.2,
        Work.Diff.EXT.ConnCov.RicFlip.pD_smP (I := I) (M := M) hLC g ih.2⟩

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip in
/-- **The `SmP`/`SlotAddP` invariants of `evalT` for an arbitrary base.** -/
theorem evalT_good' (hLC : Submission.Diff.LCSmooth I M)
    (G' : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {β : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) 2}
    (hadd : Work.Diff.EXT.ConnCov.AMB.SlotAddP β) (hsm : Work.Diff.EXT.ConnCov.AMB.SmP β) :
    ∀ {n : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term n),
      Work.Diff.EXT.ConnCov.AMB.SlotAddP
          (Work.Diff.EXT.ConnCov.RicFlip.evalT G' t β T)
        ∧ Work.Diff.EXT.ConnCov.AMB.SmP
          (Work.Diff.EXT.ConnCov.RicFlip.evalT G' t β T) := by
  intro n T
  induction T with
  | leaf i =>
      exact ⟨(pDiter2_good (I := I) (M := M) hLC (G' t) hadd hsm i).1,
        (pDiter2_good (I := I) (M := M) hLC (G' t) hadd hsm i).2⟩
  | comp Ψ T ih =>
      refine ⟨?_, ?_⟩
      · exact Work.Diff.EXT.ConnCov.RicFlip.SlotAddP_comp (I := I) (M := M) G' t Ψ ih.1
          (fun F hF => Work.Diff.EXT.ConnCov.RicFlip.atomEval_smE (I := I) (M := M) hLC G' t
            Ψ.τ F hF)
          (fun j v W W' hv hW hW' =>
            Work.Diff.EXT.ConnCov.RicFlip.insAtomAdd (I := I) (M := M) hLC G' t _ j v W W'
              hv hW hW')
      · intro F hF
        exact ih.2 _ (fun i => Work.Diff.EXT.ConnCov.RicFlip.osubEval_smE (I := I) (M := M)
          hLC G' t Ψ hF i)

/-! ## The expansion of `Expand` and the leaf isolation -/

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- The tail of `Expand`: the terms of the expansion with the pure tower `leaf m` removed. -/
noncomputable def expandTail : (m : ℕ) →
    List (Work.Diff.EXT.ConnCov.RicFlip.Term (m + 2))
  | 0 => []
  | (m + 1) => Work.Diff.EXT.ConnCov.RicFlip.insStep (Work.Diff.EXT.ConnCov.RicFlip.Term.leaf m)
      ++ (expandTail m).flatMap (fun T =>
        Work.Diff.EXT.ConnCov.RicFlip.nextT T ++ Work.Diff.EXT.ConnCov.RicFlip.insStep T)

theorem expandTail_zero : expandTail 0 = ([] : List (Term 2)) := rfl

theorem expandTail_succ (m : ℕ) :
    expandTail (m + 1) = insStep (Term.leaf m)
      ++ (expandTail m).flatMap (fun T => nextT T ++ insStep T) := rfl

/-- **The expansion list starts with the pure tower**: `Expand m = leaf m :: expandTail m`. -/
theorem Expand_eq_leaf_cons (m : ℕ) :
    Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.Expand m
      = Work.Diff.EXT.ConnCov.RicFlip.Term.leaf m :: expandTail m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.Expand_succ, ih]
      show (Work.Diff.EXT.ConnCov.RicFlip.nextT (Work.Diff.EXT.ConnCov.RicFlip.Term.leaf m)
          ++ Work.Diff.EXT.ConnCov.RicFlip.insStep (Work.Diff.EXT.ConnCov.RicFlip.Term.leaf m))
        ++ (expandTail m).flatMap (fun T =>
            Work.Diff.EXT.ConnCov.RicFlip.nextT T ++ Work.Diff.EXT.ConnCov.RicFlip.insStep T)
        = Work.Diff.EXT.ConnCov.RicFlip.Term.leaf (m + 1)
          :: (Work.Diff.EXT.ConnCov.RicFlip.insStep
                (Work.Diff.EXT.ConnCov.RicFlip.Term.leaf m)
              ++ (expandTail m).flatMap (fun T =>
                Work.Diff.EXT.ConnCov.RicFlip.nextT T
                  ++ Work.Diff.EXT.ConnCov.RicFlip.insStep T))
      rw [show Work.Diff.EXT.ConnCov.RicFlip.nextT
          (Work.Diff.EXT.ConnCov.RicFlip.Term.leaf m)
            = [Work.Diff.EXT.ConnCov.RicFlip.Term.leaf (m + 1)] from rfl]
      rfl

theorem mem_expand_of_mem_expandTail (m : ℕ) (T : Term (m + 2))
    (h : T ∈ expandTail m) : T ∈ Expand m := by
  rw [Expand_eq_leaf_cons]
  exact List.mem_cons_of_mem _ h

theorem costT_mem_expandTail (m : ℕ) (T : Term (m + 2))
    (h : T ∈ expandTail m) : costT T = m :=
  costT_mem_Expand m T (mem_expand_of_mem_expandTail m T h)

/-- **Every term of the tail has leaf order `< m`**: the only term of `Expand m` with leaf order `m`
is the pure tower `leaf m`, which has been removed. -/
theorem leafOrd_lt_of_mem_expandTail : ∀ (m : ℕ) (T : Term (m + 2)),
    T ∈ expandTail m → leafOrd T < m := by
  intro m
  induction m with
  | zero =>
      intro T h
      rw [expandTail_zero] at h
      exact absurd h (List.not_mem_nil)
  | succ m ih =>
      intro T h
      rw [expandTail_succ] at h
      rcases List.mem_append.mp h with h | h
      · rw [insStep, List.mem_map] at h
        obtain ⟨j, _, rfl⟩ := h
        simp only [leafOrd_comp, leafOrd_leaf]
        omega
      · rw [List.mem_flatMap] at h
        obtain ⟨S, hS, hT⟩ := h
        have hSlt := ih S hS
        rcases List.mem_append.mp hT with hT | hT
        · have hle := leafOrd_mem_nextT S T hT
          omega
        · rw [insStep, List.mem_map] at hT
          obtain ⟨j, _, rfl⟩ := hT
          simp only [leafOrd_comp]
          omega

/-! ## A refined term bound with strict leaf orders -/

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- **The bound of a single term, with the leaf hypothesis available only strictly below the level.**
This is `HonestUnif.term_bound` with the two inequalities `costT T ≤ N` (in place of `costT T = m ≤ N`)
and `leafOrd T < N`; it is what makes it possible to *exclude* the pure tower `leaf N` from the
expansion and to solve for it. -/
theorem term_bound_lt (hLC : Submission.Diff.LCSmooth I M)
    (G' : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (base : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) 2)
    (R Bm : ℕ → ℝ) (N : ℕ) (hR : ∀ i, 0 ≤ R i) (hBm : ∀ ord, 0 ≤ Bm ord)
    (hleaf : ∀ j, j < N → Work.Diff.EXT.ConnCov.AMB.Bnd1 G' t
      (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G' t)) base j) (R j))
    (hB : ∀ ord, ord < N → Work.Diff.EXT.ConnCov.AMB.BndV G' t
      (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G' t ord) (Bm ord)) :
    ∀ {n : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term n),
      Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T ≤ N →
      Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T < N →
      Work.Diff.EXT.ConnCov.AMB.Bnd1 G' t
        (Work.Diff.EXT.ConnCov.RicFlip.evalT G' t base T)
        (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT R Bm T) := by
  intro n T
  induction T with
  | leaf i =>
      intro _ hl
      exact hleaf i hl
  | @comp a b ord Ψ T ih =>
      intro hc hl
      rw [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT_comp] at hc
      have hcT : Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T ≤ N := by omega
      have hord : ord < N := by omega
      have hlT : Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T < N := by
        rw [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd_comp] at hl; exact hl
      have h1 := ih hcT hlT
      have h2 := Work.Diff.EXT.ConnCov.RicFlip.Bnd1CompOSub (I := I) (M := M) hLC G' t Ψ
        (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT_nonneg R Bm hR hBm T) h1 (hBm ord)
        (hB ord hord)
      rw [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT_comp]
      exact h2

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip Work.Diff.EXT.ConnCov.RicFlip.HonestUnif in
/-- **The bound constant of a term is bounded by the product of the atom bounds and the leaf
constant**: `boundT R V T ≤ (1 + S) ^ costT T * R (leafOrd T)` as soon as every atom bound is at
most `S`. -/
theorem boundT_le (R V : ℕ → ℝ) (S : ℝ) (hS : 0 ≤ S) (hV0 : ∀ j, 0 ≤ V j) (hV : ∀ j, V j ≤ S)
    (hR : ∀ i, 0 ≤ R i) :
    ∀ {n : ℕ} (T : Work.Diff.EXT.ConnCov.RicFlip.Term n),
      Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT R V T
        ≤ (1 + S) ^ (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T)
            * R (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T) := by
  intro n T
  induction T with
  | leaf i =>
      simp only [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT_leaf,
        Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT_leaf,
        Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd_leaf]
      have h1 : (1 : ℝ) ≤ (1 + S) ^ i := one_le_pow₀ (by linarith)
      exact le_mul_of_one_le_left (hR i) h1
  | @comp a b ord Ψ T ih =>
      rw [Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT_comp,
        Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT_comp,
        Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd_comp]
      have h2 : (1 : ℝ) + V ord ≤ (1 + S) ^ (ord + 1) := by
        have hp : (1 : ℝ) ≤ 1 + S := by linarith
        calc (1 : ℝ) + V ord ≤ 1 + S := by linarith [hV ord]
          _ = (1 + S) ^ 1 := by ring
          _ ≤ (1 + S) ^ (ord + 1) := pow_le_pow_right₀ hp (by omega)
      have h3 : 0 ≤ (1 + S) ^ Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T :=
        pow_nonneg (by linarith) _
      calc Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.boundT R V T * (1 + V ord)
          ≤ ((1 + S) ^ Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T
              * R (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T))
              * (1 + S) ^ (ord + 1) :=
            mul_le_mul ih h2 (by linarith [hV0 ord]) (mul_nonneg h3 (hR _))
        _ = (1 + S) ^ (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.costT T + (ord + 1))
              * R (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T) := by
            rw [mul_assoc,
              mul_comm (R (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.leafOrd T))
                ((1 + S) ^ (ord + 1)),
              ← mul_assoc, ← pow_add]



/-! ## The constants of the uniform fixed-tower bound

The bound of the fixed Ricci tower at level `n` is obtained by *inverting* the term expansion of the
moving tower: the fixed tower is the moving tower minus the sum of the terms of the tail
`expandTail n` of the expansion list.  The constant is therefore a *fixed point* of the recursion

  `Cf n = Rm n + Σ_{T ∈ expandTail n} boundT Cf V T`,

where `Rm n = R n * (1 + K) ^ (n + 2)` converts the moving bound to the initial metric and `V` are
the fixed `δ`-atom bounds.  Rather than solving this recursion (which would need well-founded
recursion), we take the closed-form majorant `Cf n = A * D ^ (n + 1)` with

* `A = Σ_{m ≤ k+1} Rm m` — a crude bound of every `Rm m`,
* `D = 1 + #{terms} * (1 + Σ V) ^ (k + 1)`.

The induction then only needs `Rm n + (number of terms) * V-bound * D ^ n ≤ A * D ^ (n + 1)`, which
holds because `D ^ (n + 1) = D ^ n * D = D ^ n * (1 + #{terms} * V-bound)`. -/

/-- A crude bound of the moving-tower constants: `A = Σ_{m ≤ k + 1} R m * (1 + K) ^ (m + 2)`. -/
noncomputable def cstA (k : ℕ) (R : ℕ → ℝ) (Kc : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (k + 2), R m * (1 + Kc) ^ (m + 2)

/-- The sum of the fixed `δ`-atom bounds up to level `k`. -/
noncomputable def cstS (k : ℕ) (V : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range (k + 1), V j

/-- The product bound of the atom factors at level `≤ k`. -/
noncomputable def cstVB (k : ℕ) (V : ℕ → ℝ) : ℝ := (1 + cstS k V) ^ (k + 1)

/-- The total number of terms in all the tails `expandTail m`, `m ≤ k + 1`. -/
noncomputable def cstLen (k : ℕ) : ℕ :=
  (Finset.range (k + 2)).sum (fun m => (expandTail m).length)

/-- The growth factor `D = 1 + #{terms} * (product bound)`. -/
noncomputable def cstD (k : ℕ) (V : ℕ → ℝ) : ℝ := 1 + (cstLen k : ℝ) * cstVB k V

/-- The bound for the total contribution of the tail at level `n`. -/
noncomputable def cstC (k : ℕ) (R V : ℕ → ℝ) (Kc : ℝ) (n : ℕ) : ℝ :=
  (cstLen k : ℝ) * (cstVB k V * cstA k R Kc * (cstD k V) ^ n)

/-- **The uniform constant of the fixed Ricci tower at level `n`.** -/
noncomputable def ricTowerCst (k : ℕ) (R V : ℕ → ℝ) (Kc : ℝ) : ℕ → ℝ :=
  fun n => cstA k R Kc * (cstD k V) ^ (n + 1)

lemma cstS_nonneg {k : ℕ} {V : ℕ → ℝ} (hV0 : ∀ j, 0 ≤ V j) : 0 ≤ cstS k V :=
  Finset.sum_nonneg (fun j _ => hV0 j)

lemma cstVB_ge_one {k : ℕ} {V : ℕ → ℝ} (hV0 : ∀ j, 0 ≤ V j) : 1 ≤ cstVB k V := by
  rw [cstVB]
  exact one_le_pow₀ (by have := cstS_nonneg (k := k) hV0; linarith)

lemma cstVB_nonneg {k : ℕ} {V : ℕ → ℝ} (hV0 : ∀ j, 0 ≤ V j) : 0 ≤ cstVB k V :=
  le_trans zero_le_one (cstVB_ge_one hV0)

lemma cstD_ge_one {k : ℕ} {V : ℕ → ℝ} (hV0 : ∀ j, 0 ≤ V j) : 1 ≤ cstD k V := by
  rw [cstD]
  have h1 : (0 : ℝ) ≤ (cstLen k : ℝ) * cstVB k V :=
    mul_nonneg (Nat.cast_nonneg _) (cstVB_nonneg (k := k) hV0)
  linarith

lemma cstD_nonneg {k : ℕ} {V : ℕ → ℝ} (hV0 : ∀ j, 0 ≤ V j) : 0 ≤ cstD k V :=
  le_trans zero_le_one (cstD_ge_one hV0)

lemma cstA_nonneg {k : ℕ} {R : ℕ → ℝ} {Kc : ℝ} (hR0 : ∀ j, 0 ≤ R j) (hKc0 : 0 ≤ Kc) :
    0 ≤ cstA k R Kc :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (hR0 m) (pow_nonneg (by linarith) _))

lemma ricTowerCst_nonneg {k : ℕ} {R V : ℕ → ℝ} {Kc : ℝ} (hR0 : ∀ j, 0 ≤ R j)
    (hV0 : ∀ j, 0 ≤ V j) (hKc0 : 0 ≤ Kc) : ∀ n, 0 ≤ ricTowerCst k R V Kc n :=
  fun n => mul_nonneg (cstA_nonneg hR0 hKc0) (pow_nonneg (cstD_nonneg hV0) _)

lemma Rm_le_cstA {k n : ℕ} {R : ℕ → ℝ} {Kc : ℝ} (hR0 : ∀ j, 0 ≤ R j) (hKc0 : 0 ≤ Kc)
    (hn : n ≤ k + 1) : R n * (1 + Kc) ^ (n + 2) ≤ cstA k R Kc := by
  rw [cstA]
  exact Finset.single_le_sum (f := fun m => R m * (1 + Kc) ^ (m + 2)) (a := n)
    (fun m _ => mul_nonneg (hR0 m) (pow_nonneg (by linarith) _))
    (Finset.mem_range.mpr (by omega))

lemma cstLen_ge {k n : ℕ} (hn : n ≤ k + 1) : (expandTail n).length ≤ cstLen k := by
  rw [cstLen]
  exact Finset.single_le_sum (f := fun m => (expandTail m).length) (a := n)
    (fun m _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

/-- **The bound of the constant of a term of the tail**, with the atom-bounds only assumed up to
level `k` (which is where the orders of the terms in `expandTail n`, `n ≤ k + 1`, live). -/
theorem boundT_le_of_cost (k : ℕ) {R V : ℕ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    (hV0 : ∀ j, 0 ≤ V j) (hV : ∀ j, j ≤ k → V j ≤ S) (hR : ∀ i, 0 ≤ R i) :
    ∀ {n : ℕ} (T : Term n), costT T ≤ k + 1 → boundT R V T ≤ (1 + S) ^ costT T * R (leafOrd T) := by
  intro n T
  induction T with
  | leaf i =>
      intro _
      simp only [boundT_leaf, costT_leaf, leafOrd_leaf]
      have h1 : (1 : ℝ) ≤ (1 + S) ^ i := one_le_pow₀ (by linarith)
      exact le_mul_of_one_le_left (hR i) h1
  | @comp a b ord Ψ T ih =>
      intro hc
      rw [costT_comp] at hc
      have hcT : costT T ≤ k + 1 := by omega
      have hord : ord ≤ k := by omega
      have h2 : (1 : ℝ) + V ord ≤ (1 + S) ^ (ord + 1) := by
        have hp : (1 : ℝ) ≤ 1 + S := by linarith
        calc (1 : ℝ) + V ord ≤ 1 + S := by linarith [hV ord hord]
          _ = (1 + S) ^ 1 := by ring
          _ ≤ (1 + S) ^ (ord + 1) := pow_le_pow_right₀ hp (by omega)
      rw [boundT_comp, leafOrd_comp]
      have h3 : 0 ≤ (1 + S) ^ costT T := pow_nonneg (by linarith) _
      calc boundT R V T * (1 + V ord)
          ≤ ((1 + S) ^ costT T * R (leafOrd T)) * (1 + S) ^ (ord + 1) :=
            mul_le_mul (ih hcT) h2 (by linarith [hV0 ord]) (mul_nonneg h3 (hR _))
        _ = (1 + S) ^ (costT T + (ord + 1)) * R (leafOrd T) := by
            rw [mul_assoc, mul_comm (R (leafOrd T)) ((1 + S) ^ (ord + 1)), ← mul_assoc,
              ← pow_add]

/-- **The bound of the constant of a term of the tail at level `n ≤ k + 1`.** -/
theorem boundT_ricTowerCst_le {k n : ℕ} {R V : ℕ → ℝ} {Kc : ℝ} (hR0 : ∀ j, 0 ≤ R j)
    (hV0 : ∀ j, 0 ≤ V j) (hKc0 : 0 ≤ Kc) (hn : n ≤ k + 1) (T : Term (n + 2))
    (hT : T ∈ expandTail n) :
    boundT (ricTowerCst k R V Kc) V T ≤ cstVB k V * cstA k R Kc * (cstD k V) ^ n := by
  have hcost : costT T = n := costT_mem_expandTail n T hT
  have hlo : leafOrd T < n := leafOrd_lt_of_mem_expandTail n T hT
  have hS0 : 0 ≤ cstS k V := cstS_nonneg hV0
  have hVle : ∀ j, j ≤ k → V j ≤ cstS k V := by
    intro j hj
    rw [cstS]
    exact Finset.single_le_sum (f := V) (a := j) (fun m _ => hV0 m)
      (Finset.mem_range.mpr (by omega))
  have h1 := boundT_le_of_cost k (R := ricTowerCst k R V Kc) (V := V) hS0 hV0 hVle
    (ricTowerCst_nonneg hR0 hV0 hKc0) T (by rw [hcost]; omega)
  rw [hcost] at h1
  -- `h1 : boundT … V T ≤ (1 + cstS) ^ n * ricTowerCst … (leafOrd T)`
  have h2 : (1 + cstS k V) ^ n ≤ cstVB k V := by
    rw [cstVB]
    exact pow_le_pow_right₀ (by linarith) hn
  have h3 : (cstD k V) ^ (leafOrd T + 1) ≤ (cstD k V) ^ n :=
    pow_le_pow_right₀ (cstD_ge_one hV0) (by omega)
  have h4 : (0 : ℝ) ≤ (1 + cstS k V) ^ n := pow_nonneg (by linarith) _
  have h5 : (0 : ℝ) ≤ cstA k R Kc := cstA_nonneg hR0 hKc0
  have h6 : (0 : ℝ) ≤ (cstD k V) ^ (leafOrd T + 1) := pow_nonneg (cstD_nonneg hV0) _
  calc boundT (ricTowerCst k R V Kc) V T
      ≤ (1 + cstS k V) ^ n * ricTowerCst k R V Kc (leafOrd T) := h1
    _ = (1 + cstS k V) ^ n * (cstA k R Kc * (cstD k V) ^ (leafOrd T + 1)) := by
        rw [ricTowerCst]
    _ ≤ cstVB k V * (cstA k R Kc * (cstD k V) ^ n) :=
        mul_le_mul h2 (mul_le_mul_of_nonneg_left h3 h5) (mul_nonneg h5 h6)
          (cstVB_nonneg (k := k) hV0)
    _ = cstVB k V * cstA k R Kc * (cstD k V) ^ n := by ring

/-- **The total contribution of the tail at level `n ≤ k + 1`.** -/
theorem sum_boundT_le {k n : ℕ} {R V : ℕ → ℝ} {Kc : ℝ} (hR0 : ∀ j, 0 ≤ R j)
    (hV0 : ∀ j, 0 ≤ V j) (hKc0 : 0 ≤ Kc) (hn : n ≤ k + 1) :
    ((expandTail n).map (fun T => boundT (ricTowerCst k R V Kc) V T)).sum
      ≤ cstC k R V Kc n := by
  have h0 : (0 : ℝ) ≤ cstVB k V * cstA k R Kc * (cstD k V) ^ n :=
    mul_nonneg (mul_nonneg (cstVB_nonneg (k := k) hV0) (cstA_nonneg hR0 hKc0))
      (pow_nonneg (cstD_nonneg hV0) _)
  have h1 : ((expandTail n).map (fun T => boundT (ricTowerCst k R V Kc) V T)).sum
      ≤ ((expandTail n).map
          (fun _ => cstVB k V * cstA k R Kc * (cstD k V) ^ n)).sum :=
    List.sum_le_sum (fun T hT => boundT_ricTowerCst_le hR0 hV0 hKc0 hn T hT)
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul] at h1
  refine le_trans h1 ?_
  rw [cstC]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast cstLen_ge hn) h0

/-- **The key arithmetic of the induction.** -/
theorem cst_main_ineq {k n : ℕ} {R V : ℕ → ℝ} {Kc : ℝ} (hR0 : ∀ j, 0 ≤ R j)
    (hV0 : ∀ j, 0 ≤ V j) (hKc0 : 0 ≤ Kc) (hn : n ≤ k + 1) :
    R n * (1 + Kc) ^ (n + 2) + cstC k R V Kc n ≤ ricTowerCst k R V Kc n := by
  have h1 : R n * (1 + Kc) ^ (n + 2) ≤ cstA k R Kc := Rm_le_cstA hR0 hKc0 hn
  have h2 : cstA k R Kc ≤ cstA k R Kc * (cstD k V) ^ n := by
    have hD : (1 : ℝ) ≤ (cstD k V) ^ n := one_le_pow₀ (cstD_ge_one hV0)
    calc cstA k R Kc = cstA k R Kc * 1 := by ring
      _ ≤ cstA k R Kc * (cstD k V) ^ n :=
          mul_le_mul_of_nonneg_left hD (cstA_nonneg hR0 hKc0)
  have hkey : R n * (1 + Kc) ^ (n + 2) ≤ cstA k R Kc * (cstD k V) ^ n := le_trans h1 h2
  have hexp : cstA k R Kc * (cstD k V) ^ (n + 1)
      = cstA k R Kc * (cstD k V) ^ n
        + (cstLen k : ℝ) * (cstVB k V * cstA k R Kc * (cstD k V) ^ n) := by
    rw [pow_succ, cstD]
    ring
  rw [ricTowerCst, cstC, hexp]
  linarith

end TermGlue

section FixedBnd

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip
open Work.Diff.EXT.ConnCov.RicFlip.HonestUnif

variable [I.Boundaryless] [T2Space M]

/-- The base case of the homogeneity of the packed Ricci tower: `ric2 g` is bilinear in its two
value slots (`Work.Diff.EXT.ricAt_smul_middle_L`, `Work.Diff.EXT.ricAt_smul_last_L`). -/
theorem hom_ric2_clean (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    Work.Diff.EXT.ATower.Hom (ric2 g) := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞) :=
    (hLC g).1.some
  intro c F x
  show ricAt (Submission.Diff.lcOf g) x (c 0 • F 0 x) (c 1 • F 1 x)
    = (∏ j : Fin 2, c j) * ricAt (Submission.Diff.lcOf g) x (F 0 x) (F 1 x)
  rw [Fin.prod_univ_two c,
    Work.Diff.EXT.ricAt_smul_middle_L (I := I) (M := M) g hcov x (c 0) (F 0 x) (c 1 • F 1 x),
    Work.Diff.EXT.ricAt_smul_last_L (I := I) (M := M) g hcov x (c 1) (F 0 x) (F 1 x)]
  ring

/-- **Homogeneity of the packed Ricci tower**: `pDiter2 (lcOf g) (ric2 g') m` is homogeneous of
degree `m + 2` in its `m + 2` slots.  The base case is `hom_ric2_clean`; the step is the
`AMB.pD`-invariance of joint scaling homogeneity (`Work.Diff.EXT.ATower.hom_pD`). -/
theorem hom_pDiter2 (hLC : Submission.Diff.LCSmooth I M)
    (g g' : Submission.Diff.SMet I M) :
    ∀ m, Work.Diff.EXT.ATower.Hom
      (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf g)
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 g') m)
  | 0 => hom_ric2_clean (I := I) (M := M) hLC g'
  | (m + 1) => Work.Diff.EXT.ATower.hom_pD (I := I) (M := M) g
      (hom_pDiter2 hLC g g' m)

/-- **The `Bnd1`-shaped uniform bound of the fixed honest Ricci tower.**

With the *reversed* family `Ĝ s = G (t - s)` (so that `Ĝ 0 = G t` and `Ĝ t = G 0`), the expansion
identity `expand_correct` writes the **moving** tower at level `n` as the sum of the evaluations of
the terms of `Expand n`; the pure tower `leaf n` is evaluated by the **fixed** connection
`∇^{G 0}` and all the other terms (the tail `expandTail n`) have leaf order `< n` and atoms which
are the *fixed* `δ`-towers.  Solving for the pure tower and bounding the tail by the induction
hypothesis (`term_bound_lt`) and the fixed `δ`-atom bounds (`fixedDeltaAtomBndV`) gives the result,
with the constant `ricTowerCst`. -/
theorem fixedRicTowerBnd1
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
    ∃ Cf : ℕ → ℝ, (∀ n, 0 ≤ Cf n) ∧ ∀ n, n ≤ k + 1 → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G 0) t
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n) (Cf n) := by
  classical
  obtain ⟨V, hV0, hV⟩ := Work.Diff.EXT.ATower.fixedDeltaAtomBndV (I := I) (M := M) hLC
    (G := G) hT C hC hflow hbound hmet k B hB hA
  obtain ⟨R, hR0, hR⟩ := Work.Diff.EXT.ATower.movingRicTowerBnd1 (I := I) (M := M) hLC
    G T C hT hC hflow hbound hmet hShi (k + 1)
  set Kc : ℝ := Real.exp ((Module.finrank ℝ E : ℝ) * C * T) with hKc
  have hKc1 : 1 ≤ Kc := by rw [hKc]; exact Real.one_le_exp (by positivity)
  have hKc0 : 0 ≤ Kc := le_trans zero_le_one hKc1
  refine ⟨ricTowerCst k R V Kc, ricTowerCst_nonneg hR0 hV0 hKc0, ?_⟩
  have main : ∀ n, n ≤ k + 1 → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G 0) t
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) n) (ricTowerCst k R V Kc n) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn t ht F x hF
    set Ĝ : ℝ → Submission.Diff.SMet I M := fun s => G (t - s) with hĜ
    have hĜ0 : Ĝ 0 = G t := by rw [hĜ]; simp
    have hĜt : Ĝ t = G 0 := by rw [hĜ]; simp
    have hbaseadd : Work.Diff.EXT.ConnCov.AMB.SlotAddP (ric2 (G t)) :=
      Work.Diff.EXT.ConnCov.RicFlip.ric2_slotAddP (I := I) (M := M) hLC (G t)
    have hbasesm : Work.Diff.EXT.ConnCov.AMB.SmP (ric2 (G t)) :=
      Work.Diff.EXT.ConnCov.RicFlip.ric2_smP (I := I) (M := M) hLC (G t)
    have hsmT : ∀ {m : ℕ} (T : Term m),
        Work.Diff.EXT.ConnCov.AMB.SmP (evalT Ĝ t (ric2 (G t)) T) :=
      fun T => (evalT_good' (I := I) (M := M) hLC Ĝ t hbaseadd hbasesm T).2
    have hslot : ∀ {m : ℕ} (T : Term m),
        Work.Diff.EXT.ConnCov.AMB.SlotAddP (evalT Ĝ t (ric2 (G t)) T) :=
      fun T => (evalT_good' (I := I) (M := M) hLC Ĝ t hbaseadd hbasesm T).1
    -- the expansion of the moving tower
    have hexp := congrFun (Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.expand_correct (I := I) (M := M)
      hLC Ĝ t (ric2 (G t)) hsmT hslot n F hF) x
    rw [hĜ0] at hexp
    rw [Expand_eq_leaf_cons, Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.evalList_cons] at hexp
    have hleafval : evalT Ĝ t (ric2 (G t)) (Term.leaf n) F x
        = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (ric2 (G t)) n F x := by
      change Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (Ĝ t)) (ric2 (G t)) n F x
        = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0)) (ric2 (G t)) n F x
      rw [hĜt]
    rw [hleafval] at hexp
    -- `hexp : fixed + tail = moving`
    have hfix : Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0)) (ric2 (G t)) n F x
        = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t)) (ric2 (G t)) n F x
          - evalList Ĝ t (ric2 (G t)) (expandTail n) F x := by linarith [hexp]
    -- the bound of the tail
    have hcorr : Work.Diff.EXT.ConnCov.AMB.Bnd1 Ĝ t
        (evalList Ĝ t (ric2 (G t)) (expandTail n))
        ((expandTail n).map (boundT (ricTowerCst k R V Kc) V)).sum := by
      refine Work.Diff.EXT.ConnCov.RicFlip.HonestUnif.bnd1_evalList (I := I) (M := M) Ĝ t
        (ric2 (G t)) (expandTail n) (boundT (ricTowerCst k R V Kc) V) ?_
      intro T hT
      have hcost : costT T ≤ n := le_of_eq (costT_mem_expandTail n T hT)
      have hlo : leafOrd T < n := leafOrd_lt_of_mem_expandTail n T hT
      refine term_bound_lt (I := I) (M := M) hLC Ĝ t (ric2 (G t)) (ricTowerCst k R V Kc) V n
        (ricTowerCst_nonneg hR0 hV0 hKc0) hV0 ?_ ?_ T hcost hlo
      · intro j hj
        have hij := ih j hj (by omega) t ht
        have h1 := (bnd1_fam_congr (I := I) (M := M) (G₁ := fun _ : ℝ => G 0) (G₂ := Ĝ)
          (by rw [hĜt])).mp hij
        rw [hĜt]
        exact h1
      · intro ord ho
        have h1 := hV ord (by omega) t ht
        have h2 : Work.Diff.EXT.ConnCov.AMB.BndV (fun s : ℝ => G (t - s)) t
            (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM (fun s : ℝ => G (t - s)) t ord)
            (V ord) :=
          (bndV_fam_congr (I := I) (M := M) (G₁ := fun _ : ℝ => G 0)
            (G₂ := fun s : ℝ => G (t - s)) (by simp)).mp h1
        rw [hĜ]
        exact h2
    -- the moving bound, converted to the initial metric
    have hmov : Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G 0) t
        (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
          (ric2 (G t)) n) (R n * (1 + Kc) ^ (n + 2)) := by
      have h1 : Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G t) t
          (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
            (ric2 (G t)) n) (R n) := hR n hn t ht
      refine bnd1_of_metric_le (I := I) (M := M) (g₁ := G t) (g₂ := G 0) (K := Kc) hKc0 ?_
        (hR0 n) h1
      intro y u
      rw [hKc]
      exact sqrt_inner_Gt_le (I := I) (M := M) G T C hmet hC hT ht y u
    have hcorr' : Work.Diff.EXT.ConnCov.AMB.Bnd1 (fun _ : ℝ => G 0) t
        (evalList Ĝ t (ric2 (G t)) (expandTail n))
        ((expandTail n).map (boundT (ricTowerCst k R V Kc) V)).sum :=
      (bnd1_fam_congr (I := I) (M := M) (G₁ := Ĝ) (G₂ := fun _ : ℝ => G 0)
        (by rw [hĜt])).mp hcorr
    have hP0 : (0 : ℝ) ≤ ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) :=
      Finset.prod_nonneg (fun j _ => by
        have h := Real.sqrt_nonneg ((G 0).inner x (F j x) (F j x)); linarith)
    have hm := hmov F x hF
    have hc := hcorr' F x hF
    have hs := sum_boundT_le (k := k) (n := n) (R := R) (V := V) (Kc := Kc) hR0 hV0 hKc0 hn
    have hci := cst_main_ineq (k := k) (n := n) (R := R) (V := V) (Kc := Kc) hR0 hV0 hKc0 hn
    have habs : |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
            (ric2 (G t)) n F x - evalList Ĝ t (ric2 (G t)) (expandTail n) F x|
        ≤ |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t)) (ric2 (G t)) n F x|
          + |evalList Ĝ t (ric2 (G t)) (expandTail n) F x| := by
      have h := abs_add_le (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
        (ric2 (G t)) n F x) (-(evalList Ĝ t (ric2 (G t)) (expandTail n) F x))
      simpa [sub_eq_add_neg] using h
    calc |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0)) (ric2 (G t)) n F x|
        = |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t)) (ric2 (G t)) n F x
            - evalList Ĝ t (ric2 (G t)) (expandTail n) F x| := by rw [hfix]
      _ ≤ |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G t))
              (ric2 (G t)) n F x|
            + |evalList Ĝ t (ric2 (G t)) (expandTail n) F x| := habs
      _ ≤ R n * (1 + Kc) ^ (n + 2)
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x)))
            + ((expandTail n).map (boundT (ricTowerCst k R V Kc) V)).sum
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) :=
          add_le_add hm hc
      _ ≤ R n * (1 + Kc) ^ (n + 2)
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x)))
            + cstC k R V Kc n
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hs hP0)
      _ = (R n * (1 + Kc) ^ (n + 2) + cstC k R V Kc n)
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) := by ring
      _ ≤ ricTowerCst k R V Kc n
              * ∏ j : Fin (n + 2), (1 + Real.sqrt ((G 0).inner x (F j x) (F j x))) :=
          mul_le_mul_of_nonneg_right hci hP0
  exact main

end FixedBnd


/-! ## The bridge from the target's honest tower to the packed honest tower

The target bounds `Work.Diff.EXT.ConnCov.tower2 (lcOf (G 0)) (baseRic2 (G t)) m`, the `m`-th
covariant derivative of the `(0,2)`-tensor `Ric(G t)`; the term calculus of the previous sections
works with the **packed iterated tower** `RicFlip.pDiter2 (lcOf (G 0)) (ric2 (G t)) m`.  The two are
related by the shift identity for the `(0,3)`-tensor `baseRic` (whose third value slot is a dummy)
and the packed bridge `pack_htower_pDiter2`. -/

section Final

open Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicFlip

private lemma snoc_castAdd3 {j : ℕ}
    (F : Fin (j + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (d : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (i : Fin j) :
    (Fin.snoc F d : Fin (j + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
        (Fin.castAdd 3 i) = F (Fin.castAdd 2 i) := by
  have h : (Fin.castAdd 3 i : Fin (j + 3)) = (Fin.castAdd 2 i).castSucc := Fin.ext rfl
  rw [h]
  exact @Fin.snoc_castSucc (j + 2)
    (fun _ => Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) d F (Fin.castAdd 2 i)

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

private lemma snoc_natAdd2 {j : ℕ}
    (F : Fin (j + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (d : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    (Fin.snoc F d : Fin (j + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
        (Fin.natAdd j (2 : Fin 3)) = d := by
  have h : (Fin.natAdd j (2 : Fin 3) : Fin (j + 3)) = Fin.last (j + 2) := Fin.ext rfl
  rw [h]
  exact @Fin.snoc_last (j + 2)
    (fun _ => Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) d F

/-- The two-element tuple of fields `(A, B)`, used as the two value slots of the honest tower. -/
private noncomputable def pairTup
    (A B : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    Fin 2 → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
  fun i => if (i : ℕ) = 0 then A else B

@[simp] private lemma pairTup_zero (A B : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    pairTup (I := I) (M := M) A B 0 = A := by
  rw [pairTup]
  exact if_pos rfl

@[simp] private lemma pairTup_one (A B : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    pairTup (I := I) (M := M) A B 1 = B := by
  rw [pairTup]
  exact if_neg (by decide)

/-- **The honest tower of `baseRic` is the honest `(0,2)`-tower of `Ric`**, for an arbitrary
connection `cov` (the `(0,3)`-tensor `baseRic g` has a dummy third value slot). -/
private theorem htower_eq_tower2_conn (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (g : Submission.Diff.SMet I M) (k : ℕ)
    (v : Fin k → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (A B C : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.ConnCov.htower cov (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) k
        v A B C x
      = Work.Diff.EXT.ConnCov.tower2 cov
          (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) k v A B x := by
  have h := Work.Diff.EXT.ConnCov.htower_lift23k (I := I) (M := M) cov
    (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) k
  exact congrFun (congrFun (congrFun (congrFun (congrFun h v) A) B) C) x

private lemma append_eq_lambda {j : ℕ} (F : Fin (j + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (d : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    (fun l : Fin (j + 2) => (Fin.snoc F d : Fin (j + 3) →
      Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (Fin.castSucc l)) = F := by
  funext l
  exact @Fin.snoc_castSucc (j + 2)
    (fun _ => Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) d F l

/-- **The bridge**: the honest `(0,2)`-tower of the Ricci tensor is the packed honest tower on the
tuple `(v, A, B)` of the direction fields and the two value fields. -/
theorem tower2_eq_pDiter2 [I.Boundaryless] [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (g : Submission.Diff.SMet I M) (m : ℕ)
    (v : Fin m → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (A B : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (x : M) :
    Work.Diff.EXT.ConnCov.tower2 cov
        (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) m v A B x
      = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 cov
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 g) m
          (Fin.append v (pairTup (I := I) (M := M) A B)) x := by
  set F₂ : Fin (m + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
    Fin.append v (pairTup (I := I) (M := M) A B) with hF₂
  set Fest : Fin (m + 3) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
    Fin.snoc F₂ (0 : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) with hFest
  have e1 : (fun i : Fin m => Fest (Fin.castAdd 3 i)) = v := by
    funext i
    rw [hFest, snoc_castAdd3, hF₂, Fin.append_left]
  have e2 : Fest (Fin.natAdd m (0 : Fin 3)) = A := by
    rw [hFest, snoc_natAdd0, hF₂, Fin.append_right]
    exact pairTup_zero (I := I) (M := M) A B
  have e3 : Fest (Fin.natAdd m (1 : Fin 3)) = B := by
    rw [hFest, snoc_natAdd1, hF₂, Fin.append_right]
    exact pairTup_one (I := I) (M := M) A B
  have e4 : Fest (Fin.natAdd m (2 : Fin 3))
      = (0 : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) := by
    rw [hFest]
    exact snoc_natAdd2 (I := I) (M := M) F₂ 0
  have e5 : (fun l : Fin (m + 2) => Fest (Fin.castSucc l)) = F₂ := by
    rw [hFest]
    exact append_eq_lambda (I := I) (M := M) F₂
      (0 : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
  have hp := congrFun (Work.Diff.EXT.ConnCov.RicFlip.pack_htower_pDiter2 (I := I) (M := M)
    cov g m Fest) x
  calc Work.Diff.EXT.ConnCov.tower2 cov
        (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) g) m v A B x
      = Work.Diff.EXT.ConnCov.htower cov
          (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) m v A B
          (0 : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) x :=
        (htower_eq_tower2_conn (I := I) (M := M) cov g m v A B
          (0 : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) x).symm
    _ = Work.Diff.EXT.ConnCov.AMB.pack (Work.Diff.EXT.ConnCov.htower cov
          (Work.Diff.EXT.ConnCov.baseRic (I := I) (M := M) g) m) Fest x := by
        rw [Work.Diff.EXT.ConnCov.AMB.pack_apply, e1, e2, e3, e4]
    _ = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 cov
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 g) m
          (fun l : Fin (m + 2) => Fest (Fin.castSucc l)) x := hp
    _ = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 cov
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 g) m F₂ x := by rw [e5]
    _ = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 cov
          (Work.Diff.EXT.ConnCov.RicFlip.ric2 g) m
          (Fin.append v (pairTup (I := I) (M := M) A B)) x := by rw [hF₂]

end Final

/-- **The fixed `(0,2)`-tower of the Ricci tensor is uniformly bounded on `[T/2,T)`.**

`Work.Diff.EXT.ConnCov.tower2 (lcOf (G 0)) (baseRic2 (G t)) m` is `∇^{G 0,m}Ric(G t)`: the `m`-fold
covariant derivative of the Ricci tensor of `G t` with respect to the **fixed** background
connection `∇^{G 0}` of the initial metric, evaluated on the canonical smooth extensions of the
vectors.  The statement bounds it uniformly in `t ∈ [T/2,T)`, in `x` and in the vectors, for all
levels `m ≤ k + 1`, from the `∇^{G 0}`-tower bounds `hA` of the connection difference and Shi's
estimate `hShi`.

## Route (the two external inputs are PROVED in the workspace)

Write `R_q := tower2 (lcOf (G t)) (baseRic2 (G t)) q` (the *moving* Ric tower; it is `htower
(lcOf (G t)) (baseRic (G t)) q` by the proved `RicTr.htower_baseRic_eq_tower2`) and
`M_q := tower2 (lcOf (G 0)) (baseRic2 (G t)) q` (the *fixed* Ric tower, the object to bound).  Let
`δ := covDiff G t = lcOf (G t) - lcOf (G 0)`.  The flip identity for one recursion step,
`step2 cov_t τ = step2 cov_0 τ + insAll2 δ τ` (for slot-additive smooth `τ`), gives
`M_{m+1} - R_{m+1} = step2 cov_0 (M_m - R_m) + insAll2 δ R_m` (linearity of `step2` in its
argument), and hence the **telescoping identity**

  `M_m - R_m = Σ_{j<m} (step2 cov_0)^j (insAll2 δ) R_{m-1-j}`.

(Equivalently, eliminating `R` instead of `M`: `M_m - R_m = Σ_{j<m} (step2 cov_t)^j (insAll2 δ)
M_{m-1-j}`.)

The bound is by induction on `m`, using:
* `R_q` — the moving Ric tower bounds, from `hShi` via the PROVED
  `Work.Diff.EXT.ConnCov.RicTr.movingRicHonestTower` (all levels, uniform on the slab);
* `∇^{0,c}δ` — the fixed `δ`-tower bounds, from `hA` via the PROVED
  `Work.Diff.EXT.ConnCov.RicTr.deltaTower_fixed_bound_of_hA` (`c < k + 1`);
* the *Leibniz / slot bookkeeping*: `(step2 cov)^j (insAll2 X) T` is a sum of evaluations of the
  towers `(step2 cov)^b T` (`b ≤ j`) on fields obtained from the original ones by substituting
  *values* of `∇^{cov,a}X` (`a ≤ j - b`) into slots, so the bound follows from the tensoriality
  (value-dependence) of the towers together with the elementary product estimate for the direction
  norms.  (This is the only non-elementary step; it is the `(0,2)`-analogue of the SelSum/term
  calculus of `ConnCov/RicFlip/TermCalc.lean`.)

An *unconditional* variant of the same statement (without `hA`) is true via the `s`-variation route:
differentiate `s ↦ tower2 (lcOf (G s)) (baseRic2 (G t)) m` using the first variation
`Work.Diff.T.lc_variation`; the inserted tensor is then the Koszul combination of `-2∇^{G s}Ric`,
whose `∇^{G s}`-towers are `contr ∇^{G s,·}Rm`, bounded by `hShi` — no gauge data is needed.  That
variant would give the hypothesis `hdA` of
`Submission/Work/Diff/EXT/conn_diff_cov_bounds_v2.lean` outright.

## Why this is the right piece

`Work.Diff.EXT.ConnCov.tower (lcOf (G 0)) (dAOfBase G t) k` — the object of the assignment
`Diff/EXT/ATower/dAOfTowerBoundShi_piece` — is, by the Koszul identity
`Work.Diff.EXT.conn_diff_cov_bounds_v2.aOf_eq_koszul` and the first variation
`...hasDerivAt_aOf` (both proved, axioms `propext, Classical.choice, Quot.sound`), the
Koszul combination `-(ρ(X,Y,Z) + ρ(Y,X,Z) - ρ(Z,X,Y))` of the single tensor
`ρ = ∇^{G 0}Ric(G t)`, whose `∇^{G 0}`-tower at level `k` is (an index re-shuffling of) the fixed
Ricci tower `M_{k+1}` bounded here. -/
theorem fixedRicTowerBound
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
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ k + 1 → ∀ x : M,
      ∀ (w : Fin m → TangentSpace I x) (a b : TangentSpace I x),
        |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) m
            (fun i => Submission.Diff.smoothExt x (w i)) (Submission.Diff.smoothExt x a)
            (Submission.Diff.smoothExt x b) x|
          ≤ Ck * (Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (w i) (w i))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) 
    := by
  classical
  obtain ⟨Cf, hCf0, hCf⟩ := fixedRicTowerBnd1 (I := I) (M := M) hLC G T C hT hC hflow hbound
    hmet hShi k B hB hA
  set Kc : ℝ := Real.exp ((Module.finrank ℝ E : ℝ) * C * T) with hKc
  have hKc1 : 1 ≤ Kc := by rw [hKc]; exact Real.one_le_exp (by positivity)
  have hKc0 : 0 ≤ Kc := le_trans zero_le_one hKc1
  have hsum0 : 0 ≤ ∑ m ∈ Finset.range (k + 2), Cf m := Finset.sum_nonneg (fun m _ => hCf0 m)
  refine ⟨(∑ m ∈ Finset.range (k + 2), Cf m) * Kc ^ (k + 3), ?_, ?_⟩
  · exact mul_nonneg hsum0 (pow_nonneg hKc0 _)
  · intro t ht m hm x w a b
    set wf : Fin m → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
      fun i => Submission.Diff.smoothExt x (w i) with hwf
    set g : Fin 2 → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M) :=
      pairTup (I := I) (M := M) (Submission.Diff.smoothExt x a)
        (Submission.Diff.smoothExt x b) with hg
    have hwfsm : ∀ i, Work.Diff.EXT.ATower.SmE I M (wf i) :=
      fun i => Work.Diff.GE.smoothExt_cmdiff x (w i)
    have hgsm : ∀ i, Work.Diff.EXT.ATower.SmE I M (g i) := by
      intro i
      rw [hg]
      simp only [pairTup]
      split_ifs
      · exact Work.Diff.GE.smoothExt_cmdiff x a
      · exact Work.Diff.GE.smoothExt_cmdiff x b
    have hFsm : ∀ j, Work.Diff.EXT.ATower.SmE I M (Fin.append wf g j) :=
      Fin.addCases (motive := fun j => Work.Diff.EXT.ATower.SmE I M (Fin.append wf g j))
        (fun i => by rw [Fin.append_left]; exact hwfsm i)
        (fun i => by rw [Fin.append_right]; exact hgsm i)
    have hbridge : Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) (G t)) m wf
          (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b) x
        = Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m (Fin.append wf g) x := by
      rw [tower2_eq_pDiter2 (I := I) (M := M) (Submission.Diff.lcOf (G 0)) (G t) m wf
        (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b) x, ← hg]
    have hhom : ∀ (r : ℝ) (F : Fin (m + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
        (y : M),
        Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m (fun j => r • F j) y
          = r ^ (m + 2) * Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m F y := by
      intro r F y
      have h := hom_pDiter2 (I := I) (M := M) hLC (G 0) (G t) m
        (fun _ : Fin (m + 2) => r) F y
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
      exact h
    have hsharp := Work.Diff.EXT.ConnCov.sharp_of_bnd1_homog (I := I) (M := M)
      (G := fun _ : ℝ => G 0) t
      (Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m)
      (hCf0 m) (hCf m hm t ht) hhom (Fin.append wf g) x hFsm
    set A : ℝ := ∏ j : Fin (m + 2),
      Real.sqrt ((G t).inner x ((Fin.append wf g) j x) ((Fin.append wf g) j x)) with hA
    have hA0 : 0 ≤ A := by
      rw [hA]
      exact Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _)
    have hKprod : (∏ j : Fin (m + 2),
          Real.sqrt ((G 0).inner x ((Fin.append wf g) j x) ((Fin.append wf g) j x)))
        ≤ Kc ^ (m + 2) * A := by
      rw [hA]
      exact prod_sqrt_le_of_metric (I := I) (M := M) (g₁ := G 0) (g₂ := G t) (K := Kc)
        (fun y u => by rw [hKc]; exact sqrt_inner_G0_le (I := I) (M := M) G T C hmet hC hT ht y u)
        (Fin.append wf g) x
    have hprod : A = (Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (w i) (w i))))
        * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
      rw [hA]
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
        simp only [Fin.append_right, hg, pairTup_zero, pairTup_one,
          Work.Diff.GE.smoothExt_apply]
      rw [Fin.prod_univ_add (a := m) (b := 2) (fun j : Fin (m + 2) =>
        Real.sqrt ((G t).inner x ((Fin.append wf g) j x) ((Fin.append wf g) j x))), e1, e2]
      ring
    have hcst : Cf m * Kc ^ (m + 2) ≤ (∑ m ∈ Finset.range (k + 2), Cf m) * Kc ^ (k + 3) := by
      have h1 : Cf m ≤ ∑ m ∈ Finset.range (k + 2), Cf m :=
        Finset.single_le_sum (f := Cf) (a := m) (fun i _ => hCf0 i)
          (Finset.mem_range.mpr (by omega))
      have h2 : Kc ^ (m + 2) ≤ Kc ^ (k + 3) := pow_le_pow_right₀ hKc1 (by omega)
      exact mul_le_mul h1 h2 (pow_nonneg hKc0 _) hsum0
    calc |Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) (G t)) m wf
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b) x|
        = |Work.Diff.EXT.ConnCov.RicFlip.pDiter2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.RicFlip.ric2 (G t)) m (Fin.append wf g) x| := by rw [hbridge]
      _ ≤ Cf m * (∏ j : Fin (m + 2),
            Real.sqrt ((G 0).inner x ((Fin.append wf g) j x) ((Fin.append wf g) j x))) := hsharp
      _ ≤ Cf m * (Kc ^ (m + 2) * A) := mul_le_mul_of_nonneg_left hKprod (hCf0 m)
      _ = (Cf m * Kc ^ (m + 2)) * A := by ring
      _ ≤ ((∑ m ∈ Finset.range (k + 2), Cf m) * Kc ^ (k + 3)) * A :=
            mul_le_mul_of_nonneg_right hcst hA0
      _ = ((∑ m ∈ Finset.range (k + 2), Cf m) * Kc ^ (k + 3))
            * (Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (w i) (w i))))
            * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b) := by
          rw [hprod]; ring


end Work.Diff.EXT.ATower
