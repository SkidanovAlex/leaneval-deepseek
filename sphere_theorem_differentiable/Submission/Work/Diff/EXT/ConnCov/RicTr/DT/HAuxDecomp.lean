import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxDefs
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxKernel
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxStepSelTerm
import Submission.Work.Diff.EXT.ATower.LinDefs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Leibniz expansion of the `aOf`-tower (selection form)

`Work.Diff.EXT.ConnCov.deltaTower_bound_of_hA` bounds the fixed-connection δ-tower `V_c` of the
connection difference.  The only input is `hA`, the bound of the tower of
`aOf G t = g_t ⊙ δ`; the bridge is the **Leibniz expansion**

  `tower (lcOf (G 0)) aOf c = Wterm c + Σ (terms with metric level ≥ 1)`

where `Wterm c` is the lowering `g_t ⊙ V_c` of the δ-tower (so that a bound of `Wterm c` gives a
bound of `V_c`, the moving metric being an isometry for its own pairing) and each summand pairs the
metric tower `∇^{g_0,i}g_t` (`i ≥ 1`) with the δ-tower `∇^{g_0,j}δ` (`j = c - i < c`), so that its
bound uses `hA` at level `i - 1` and the *induction hypothesis* at level `j < c`.

The directions of the two factors are distributed by two *selections* `F : Fin i → Fin c` and
`G' : Fin j → Fin c` (injective with disjoint ranges, hence covering, when `i + j = c`), and one
recursion step sends `(i,j,F,G')` to `(i+1,j,FTen F,Gshift G')` and `(i,j+1,Fshift F,GTen G')`
(`Work.Diff.EXT.ConnCov.DT.hAaux.step_selTerm`), while the `i = 0` term `Wterm c` produces the single
term `(1, c, FTen 0, Gshift id)` of the next level.  This module contains the combinatorial
bookkeeping (`CombData`, its successor) and the expansion itself, as an equality of operators on
smooth tuples.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ConnCov.DT

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Operator equality on smooth tuples -/

/-- Equality of `Op3`-operators on *smooth* tuples (the tower recursion uses `mvfderiv`, which is
additive only on differentiable functions, so all identities are stated on smooth tuples). -/
def OpEqSel {k : ℕ} (τ σ : Op3 (I := I) (M := M) k) : Prop :=
  ∀ (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M),
    (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → τ v A B C x = σ v A B C x

/-- Smoothness of an operator on smooth tuples. -/
def SmOpSel {k : ℕ} (τ : Op3 (I := I) (M := M) k) : Prop :=
  ∀ (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
    (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → SmF I M (τ v A B C)

theorem OpEqSel.refl {k : ℕ} (τ : Op3 (I := I) (M := M) k) : OpEqSel τ τ :=
  fun _ _ _ _ _ _ _ _ _ => rfl

theorem OpEqSel.symm {k : ℕ} {τ σ : Op3 (I := I) (M := M) k} (h : OpEqSel τ σ) :
    OpEqSel σ τ :=
  fun v A B C x hv hA hB hC => (h v A B C x hv hA hB hC).symm

theorem OpEqSel.trans {k : ℕ} {τ σ ρ : Op3 (I := I) (M := M) k} (h1 : OpEqSel τ σ)
    (h2 : OpEqSel σ ρ) : OpEqSel τ ρ :=
  fun v A B C x hv hA hB hC => (h1 v A B C x hv hA hB hC).trans (h2 v A B C x hv hA hB hC)

theorem OpEqSel.add {k : ℕ} {τ₁ σ₁ τ₂ σ₂ : Op3 (I := I) (M := M) k}
    (h1 : OpEqSel τ₁ σ₁) (h2 : OpEqSel τ₂ σ₂) :
    OpEqSel (fun v A B C y => τ₁ v A B C y + τ₂ v A B C y)
      (fun v A B C y => σ₁ v A B C y + σ₂ v A B C y) := by
  intro v A B C x hv hA hB hC
  change τ₁ v A B C x + τ₂ v A B C x = σ₁ v A B C x + σ₂ v A B C x
  rw [h1 v A B C x hv hA hB hC, h2 v A B C x hv hA hB hC]

/-- Smoothness of a finite sum of smooth functions. -/
theorem smF_sumT {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (h : ∀ n ∈ s, SmF I M (f n)) :
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

/-- The recursion step respects equality of operators on smooth tuples. -/
theorem step_congr_sel [T2Space M] (hLC : LCSmooth I M) (G : ℝ → SMet I M) {c : ℕ}
    {τ σ : Op3 (I := I) (M := M) c} (h : OpEqSel τ σ) :
    OpEqSel (step (lcOf (G 0)) τ) (step (lcOf (G 0)) σ) := by
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
  have hfun : τ (fun i : Fin c => v i.succ) A B C
      = σ (fun i : Fin c => v i.succ) A B C := by
    funext y
    exact h _ A B C y hw hA hB hC
  simp only [step]
  rw [hfun]
  rw [Finset.sum_congr rfl (fun j _ =>
    h (Function.update (fun i : Fin c => v i.succ) j
        (fun y => (lcOf (G 0)) (v j.succ) y (v 0 y))) A B C x
      (smE_update_aux j hw (hU j)) hA hB hC)]
  rw [h (fun i : Fin c => v i.succ) (fun y => (lcOf (G 0)) A y (v 0 y)) B C x hw hAc hB hC,
    h (fun i : Fin c => v i.succ) A (fun y => (lcOf (G 0)) B y (v 0 y)) C x hw hA hBc hC,
    h (fun i : Fin c => v i.succ) A B (fun y => (lcOf (G 0)) C y (v 0 y)) x hw hA hB hCc]

/-- **Linearity of the recursion step in the operator argument** (two summands). -/
theorem step_add_sel [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M) (G : ℝ → SMet I M)
    {c : ℕ} {τ₁ τ₂ : Op3 (I := I) (M := M) c} (h₁ : SmOpSel τ₁) (h₂ : SmOpSel τ₂) :
    OpEqSel (step (lcOf (G 0)) (fun v A B C y => τ₁ v A B C y + τ₂ v A B C y))
      (fun v A B C y => step (lcOf (G 0)) τ₁ v A B C y + step (lcOf (G 0)) τ₂ v A B C y) := by
  intro v A B C x hv hA hB hC
  have h1 : MDiffAt (τ₁ (fun i : Fin c => v i.succ) A B C) x :=
    (h₁ (fun i : Fin c => v i.succ) A B C (fun j => hv j.succ) hA hB hC).mdifferentiableAt
      (by simp)
  have h2 : MDiffAt (τ₂ (fun i : Fin c => v i.succ) A B C) x :=
    (h₂ (fun i : Fin c => v i.succ) A B C (fun j => hv j.succ) hA hB hC).mdifferentiableAt
      (by simp)
  have hmv : mvfderiv I (fun y : M => τ₁ (fun i : Fin c => v i.succ) A B C y
        + τ₂ (fun i : Fin c => v i.succ) A B C y) x (v 0 x)
      = mvfderiv I (τ₁ (fun i : Fin c => v i.succ) A B C) x (v 0 x)
        + mvfderiv I (τ₂ (fun i : Fin c => v i.succ) A B C) x (v 0 x) :=
    Work.Diff.EXT.ATower.mvfderiv_add_ka h1 h2
  simp only [step]
  rw [hmv, Finset.sum_add_distrib]
  ring

/-- **Linearity of the recursion step over a finite sum.** -/
theorem step_sumT [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M) (G : ℝ → SMet I M)
    {c : ℕ} {ι : Type*} [Fintype ι] (σ : ι → Op3 (I := I) (M := M) c)
    (h : ∀ n, SmOpSel (σ n)) :
    OpEqSel (step (lcOf (G 0)) (fun v A B C y => ∑ n : ι, σ n v A B C y))
      (fun v A B C y => ∑ n : ι, step (lcOf (G 0)) (σ n) v A B C y) := by
  intro v A B C x hv hA hB hC
  have hw : ∀ j : Fin c, SmE I M ((fun i : Fin c => v i.succ) j) := fun j => hv j.succ
  have hsmn : ∀ n : ι, MDiffAt (σ n (fun i : Fin c => v i.succ) A B C) x :=
    fun n => (h n (fun i : Fin c => v i.succ) A B C hw hA hB hC).mdifferentiableAt (by simp)
  have hmv : mvfderiv I (fun y : M => ∑ n : ι, σ n (fun i : Fin c => v i.succ) A B C y) x
        (v 0 x)
      = ∑ n : ι, mvfderiv I (σ n (fun i : Fin c => v i.succ) A B C) x (v 0 x) :=
    Work.Diff.EXT.ATower.mvfderiv_sum_ka (Finset.univ : Finset ι)
      (fun n : ι => σ n (fun i : Fin c => v i.succ) A B C) (fun n _ => hsmn n)
  simp only [step]
  rw [hmv, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  try ring

/-! ## The index bookkeeping of one recursion step -/

theorem FTen_injective {i c : ℕ} {F : Fin i → Fin c} (hf : Function.Injective F) :
    Function.Injective (FTen F) := by
  intro a b h
  induction a using Fin.cases with
  | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ j =>
          simp only [FTen_zero, FTen_succ] at h
          exact absurd h.symm (Fin.succ_ne_zero _)
  | succ a' =>
      induction b using Fin.cases with
      | zero =>
          simp only [FTen_zero, FTen_succ] at h
          exact absurd h (Fin.succ_ne_zero _)
      | succ b' =>
          simp only [FTen_succ] at h
          exact congrArg Fin.succ (hf (Fin.succ_inj.mp h))

theorem Gshift_injective {j c : ℕ} {G' : Fin j → Fin c} (hg : Function.Injective G') :
    Function.Injective (Gshift G') :=
  fun a b h => hg (Fin.succ_inj.mp h)

theorem Fshift_injective {i c : ℕ} {F : Fin i → Fin c} (hf : Function.Injective F) :
    Function.Injective (Fshift F) :=
  fun a b h => hf (Fin.succ_inj.mp h)

theorem GTen_injective {j c : ℕ} {G' : Fin j → Fin c} (hg : Function.Injective G') :
    Function.Injective (GTen G') := by
  intro a b h
  induction a using Fin.cases with
  | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ j =>
          simp only [GTen_zero, GTen_succ] at h
          exact absurd h.symm (Fin.succ_ne_zero _)
  | succ a' =>
      induction b using Fin.cases with
      | zero =>
          simp only [GTen_zero, GTen_succ] at h
          exact absurd h (Fin.succ_ne_zero _)
      | succ b' =>
          simp only [GTen_succ] at h
          exact congrArg Fin.succ (hg (Fin.succ_inj.mp h))

theorem FTen_disjoint_Gshift {i j c : ℕ} (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hdisj : Disjoint (Set.range F) (Set.range G')) :
    Disjoint (Set.range (FTen F)) (Set.range (Gshift G')) := by
  rw [Set.disjoint_left]
  rintro k ⟨a, ha⟩ ⟨b, hb⟩
  induction a using Fin.cases with
  | zero =>
      rw [FTen_zero] at ha
      rw [← ha] at hb
      simp only [Gshift_apply] at hb
      exact Fin.succ_ne_zero (G' b) hb
  | succ a' =>
      simp only [FTen_succ] at ha
      simp only [Gshift_apply] at hb
      rw [← ha] at hb
      exact Set.disjoint_left.mp hdisj ⟨a', rfl⟩ ⟨b, Fin.succ_inj.mp hb⟩

theorem Fshift_disjoint_GTen {i j c : ℕ} (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hdisj : Disjoint (Set.range F) (Set.range G')) :
    Disjoint (Set.range (Fshift F)) (Set.range (GTen G')) := by
  rw [Set.disjoint_left]
  rintro k ⟨a, ha⟩ ⟨b, hb⟩
  induction b using Fin.cases with
  | zero =>
      rw [GTen_zero] at hb
      rw [← hb] at ha
      simp only [Fshift_apply] at ha
      exact Fin.succ_ne_zero (F a) ha
  | succ b' =>
      simp only [GTen_succ] at hb
      simp only [Fshift_apply] at ha
      rw [← hb] at ha
      exact Set.disjoint_left.mp hdisj ⟨a, Fin.succ_inj.mp ha⟩ ⟨b', rfl⟩

theorem cov_FTen_Gshift {i j c : ℕ} (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hcov : ∀ k : Fin c, k ∈ Set.range F ∪ Set.range G') :
    ∀ k : Fin (c + 1), k ∈ Set.range (FTen F) ∪ Set.range (Gshift G') := by
  intro k
  induction k using Fin.cases with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ m =>
      rcases hcov m with h | h
      · obtain ⟨p, rfl⟩ := h
        exact Or.inl ⟨p.succ, by simp only [FTen_succ]⟩
      · obtain ⟨p, rfl⟩ := h
        exact Or.inr ⟨p, by simp only [Gshift_apply]⟩

theorem cov_Fshift_GTen {i j c : ℕ} (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hcov : ∀ k : Fin c, k ∈ Set.range F ∪ Set.range G') :
    ∀ k : Fin (c + 1), k ∈ Set.range (Fshift F) ∪ Set.range (GTen G') := by
  intro k
  induction k using Fin.cases with
  | zero => exact Or.inr ⟨0, rfl⟩
  | succ m =>
      rcases hcov m with h | h
      · obtain ⟨p, rfl⟩ := h
        exact Or.inl ⟨p, by simp only [Fshift_apply]⟩
      · obtain ⟨p, rfl⟩ := h
        exact Or.inr ⟨p.succ, by simp only [GTen_succ]⟩

theorem GTen_id_eq {c : ℕ} : GTen (fun k : Fin c => k) = (fun k : Fin (c + 1) => k) := by
  funext k
  induction k using Fin.cases with
  | zero => rfl
  | succ k => rfl

/-- **The `i = 0` term of a level is the `Wterm` of that level** (the `Fin 0`-selection is
irrelevant, and `GTen id = id`). -/
theorem selTerm_zero_eq_Wterm {c : ℕ} (G : ℝ → SMet I M) (t : ℝ)
    (F : Fin 0 → Fin (c + 1)) (G' : Fin (c + 1) → Fin (c + 1))
    (hG' : G' = fun k => k) :
    selTerm G t (c + 1) 0 (c + 1) F G' = Wterm G t (c + 1) := by
  subst hG'
  funext v A B C y
  simp only [Wterm, selTerm, gtTower, gtower, gtBase]

/-! ## The index data of the expansion -/

/-- The index data of the Leibniz expansion at level `c`: a finite index type, a pair of levels
`(m,j)` with `m + 1 + j = c` (the metric factor's level is `m + 1 ≥ 1`, in *successor form*, so
that no cast between `Fin (m+1)` and `Fin i` is ever needed), and the two (injective, disjoint)
selections of the directions for the metric factor and the δ factor. -/
structure CombData (c : ℕ) where
  ι : Type
  ft : Fintype ι
  m : ι → ℕ
  j : ι → ℕ
  F : (n : ι) → Fin (m n + 1) → Fin c
  G' : (n : ι) → Fin (j n) → Fin c
  hmj : ∀ n, m n + 1 + j n = c
  hfinj : ∀ n, Function.Injective (F n)
  hginj : ∀ n, Function.Injective (G' n)
  hdisj : ∀ n, Disjoint (Set.range (F n)) (Set.range (G' n))

attribute [instance] CombData.ft

/-- The sum of the expansion terms of a data set. -/
noncomputable def CombTerm {c : ℕ} (D : CombData c)
    (G : ℝ → SMet I M) (t : ℝ) : Op3 (I := I) (M := M) c :=
  fun v A B C y => ∑ n : D.ι,
    selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n) v A B C y

/-- The metric-factor part of the sum of the successor data. -/
noncomputable def CombTermL {c : ℕ} (D : CombData c)
    (G : ℝ → SMet I M) (t : ℝ) : Op3 (I := I) (M := M) (c + 1) :=
  fun v A B C y => ∑ n : D.ι,
    selTerm G t (c + 1) (D.m n + 1 + 1) (D.j n) (FTen (D.F n)) (Gshift (D.G' n)) v A B C y

/-- The δ-factor part of the sum of the successor data. -/
noncomputable def CombTermR {c : ℕ} (D : CombData c)
    (G : ℝ → SMet I M) (t : ℝ) : Op3 (I := I) (M := M) (c + 1) :=
  fun v A B C y => ∑ n : D.ι,
    selTerm G t (c + 1) (D.m n + 1) (D.j n + 1) (Fshift (D.F n)) (GTen (D.G' n)) v A B C y

/-- The single term produced by the `i = 0` summand (the `Wterm`) of level `c`. -/
noncomputable def CombTermE (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    Op3 (I := I) (M := M) (c + 1) :=
  selTerm G t (c + 1) 1 c (FTen (fun k : Fin 0 => k.elim0)) (Gshift (fun k : Fin c => k))

/-- The empty data at level `0`. -/
noncomputable def CombData.base : CombData 0 where
  ι := Empty
  ft := inferInstance
  m := fun n => n.elim
  j := fun n => n.elim
  F := fun n => n.elim
  G' := fun n => n.elim
  hmj := fun n => n.elim
  hfinj := fun n => n.elim
  hginj := fun n => n.elim
  hdisj := fun n => n.elim

/-! ### The fields of the successor data -/

/-- The `m`-field of the successor data (the metric level is `succM D n + 1`). -/
def succM {c : ℕ} (D : CombData c) : D.ι ⊕ D.ι ⊕ Fin 1 → ℕ
  | Sum.inl a => D.m a + 1
  | Sum.inr (Sum.inl a) => D.m a
  | Sum.inr (Sum.inr _) => 0

/-- The `j`-field of the successor data. -/
def succJ {c : ℕ} (D : CombData c) : D.ι ⊕ D.ι ⊕ Fin 1 → ℕ
  | Sum.inl a => D.j a
  | Sum.inr (Sum.inl a) => D.j a + 1
  | Sum.inr (Sum.inr _) => c

/-- The `F`-field of the successor data. -/
def succF {c : ℕ} (D : CombData c) :
    (n : D.ι ⊕ D.ι ⊕ Fin 1) → Fin (succM D n + 1) → Fin (c + 1)
  | Sum.inl a => FTen (D.F a)
  | Sum.inr (Sum.inl a) => Fshift (D.F a)
  | Sum.inr (Sum.inr _) => FTen (fun k : Fin 0 => k.elim0)

/-- The `G'`-field of the successor data. -/
def succG {c : ℕ} (D : CombData c) :
    (n : D.ι ⊕ D.ι ⊕ Fin 1) → Fin (succJ D n) → Fin (c + 1)
  | Sum.inl a => Gshift (D.G' a)
  | Sum.inr (Sum.inl a) => GTen (D.G' a)
  | Sum.inr (Sum.inr _) => Gshift (fun k : Fin c => k)

@[simp] theorem succM_inl {c : ℕ} (D : CombData c) (a : D.ι) :
    succM D (Sum.inl a) = D.m a + 1 := rfl

@[simp] theorem succM_inr_inl {c : ℕ} (D : CombData c) (a : D.ι) :
    succM D (Sum.inr (Sum.inl a)) = D.m a := rfl

@[simp] theorem succM_inr_inr {c : ℕ} (D : CombData c) (u : Fin 1) :
    succM D (Sum.inr (Sum.inr u)) = 0 := rfl

@[simp] theorem succJ_inl {c : ℕ} (D : CombData c) (a : D.ι) :
    succJ D (Sum.inl a) = D.j a := rfl

@[simp] theorem succJ_inr_inl {c : ℕ} (D : CombData c) (a : D.ι) :
    succJ D (Sum.inr (Sum.inl a)) = D.j a + 1 := rfl

@[simp] theorem succJ_inr_inr {c : ℕ} (D : CombData c) (u : Fin 1) :
    succJ D (Sum.inr (Sum.inr u)) = c := rfl

@[simp] theorem succF_inl {c : ℕ} (D : CombData c) (a : D.ι) :
    succF D (Sum.inl a) = FTen (D.F a) := rfl

@[simp] theorem succF_inr_inl {c : ℕ} (D : CombData c) (a : D.ι) :
    succF D (Sum.inr (Sum.inl a)) = Fshift (D.F a) := rfl

@[simp] theorem succF_inr_inr {c : ℕ} (D : CombData c) (u : Fin 1) :
    succF D (Sum.inr (Sum.inr u)) = FTen (fun k : Fin 0 => k.elim0) := rfl

@[simp] theorem succG_inl {c : ℕ} (D : CombData c) (a : D.ι) :
    succG D (Sum.inl a) = Gshift (D.G' a) := rfl

@[simp] theorem succG_inr_inl {c : ℕ} (D : CombData c) (a : D.ι) :
    succG D (Sum.inr (Sum.inl a)) = GTen (D.G' a) := rfl

@[simp] theorem succG_inr_inr {c : ℕ} (D : CombData c) (u : Fin 1) :
    succG D (Sum.inr (Sum.inr u)) = Gshift (fun k : Fin c => k) := rfl

/-- **One recursion step of the index data**: every term produces two terms (the metric factor
differentiated, the δ factor differentiated) and the `i = 0` term produces the single term
`(1,c, FTen 0, Gshift id)`. -/
noncomputable def CombData.succ {c : ℕ} (D : CombData c) : CombData (c + 1) where
  ι := D.ι ⊕ D.ι ⊕ Fin 1
  ft := inferInstance
  m := succM D
  j := succJ D
  F := succF D
  G' := succG D
  hmj := by
    rintro (a | a | u)
    · show D.m a + 1 + 1 + D.j a = c + 1
      have := D.hmj a; omega
    · show D.m a + 1 + (D.j a + 1) = c + 1
      have := D.hmj a; omega
    · show (0 : ℕ) + 1 + c = c + 1
      omega
  hfinj := by
    rintro (a | a | u)
    · show Function.Injective (FTen (D.F a))
      exact FTen_injective (D.hfinj a)
    · show Function.Injective (Fshift (D.F a))
      exact Fshift_injective (D.hfinj a)
    · show Function.Injective (FTen (fun k : Fin 0 => k.elim0))
      exact FTen_injective (fun x y _ => x.elim0)
  hginj := by
    rintro (a | a | u)
    · show Function.Injective (Gshift (D.G' a))
      exact Gshift_injective (D.hginj a)
    · show Function.Injective (GTen (D.G' a))
      exact GTen_injective (D.hginj a)
    · show Function.Injective (Gshift (fun k : Fin c => k))
      exact Gshift_injective (fun x y h => h)
  hdisj := by
    rintro (a | a | u)
    · show Disjoint (Set.range (FTen (D.F a))) (Set.range (Gshift (D.G' a)))
      exact FTen_disjoint_Gshift (D.F a) (D.G' a) (D.hdisj a)
    · show Disjoint (Set.range (Fshift (D.F a))) (Set.range (GTen (D.G' a)))
      exact Fshift_disjoint_GTen (D.F a) (D.G' a) (D.hdisj a)
    · show Disjoint (Set.range (FTen (fun k : Fin 0 => k.elim0)))
          (Set.range (Gshift (fun k : Fin c => k)))
      refine FTen_disjoint_Gshift (fun k : Fin 0 => k.elim0) (fun k : Fin c => k) ?_
      rw [Set.disjoint_left]
      rintro k ⟨a, ha⟩ ⟨b, hb⟩
      exact a.elim0

/-- **The summed form of the successor data.** -/
theorem CombTerm_succ_eq {c : ℕ} (D : CombData c)
    (G : ℝ → SMet I M) (t : ℝ) :
    CombTerm D.succ G t
      = fun v A B C y => CombTermL D G t v A B C y + CombTermR D G t v A B C y
          + CombTermE G t c v A B C y := by
  funext v A B C y
  show (∑ n : D.ι ⊕ D.ι ⊕ Fin 1,
      selTerm G t (c + 1) (succM D n + 1) (succJ D n) (succF D n) (succG D n) v A B C y)
    = CombTermL D G t v A B C y + CombTermR D G t v A B C y + CombTermE G t c v A B C y
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_one]
  simp only [CombTermL, CombTermR, CombTermE, succM_inl, succJ_inl, succF_inl, succG_inl,
    succM_inr_inl, succJ_inr_inl, succF_inr_inl, succG_inr_inl, succM_inr_inr, succJ_inr_inr,
    succF_inr_inr, succG_inr_inr, Nat.add_zero, Nat.zero_add]
  ring

/-! ## The expansion -/

/-- **The Leibniz expansion of the `aOf`-tower** (selection form): for every level `c` there is
index data `D` such that, for every metric family `G` and every `t`, the `∇^{g_0}`-tower of `aOf`
is the lowering `Wterm` plus the sum of the terms of `D` (on smooth tuples).  The data does not
depend on `G` or `t`, which is what allows the constants of the final bound to be chosen from it. -/
theorem exists_combData [I.Boundaryless] (hLC : LCSmooth I M) [T2Space M] :
    ∀ c : ℕ, ∃ D : CombData c,
      ∀ (G : ℝ → SMet I M) (t : ℝ),
        OpEqSel (tower (lcOf (G 0)) (fun _ => aOf G t) c)
          (fun v A B C y => Wterm G t c v A B C y + CombTerm D G t v A B C y) := by
  intro c
  induction c with
  | zero =>
      refine ⟨CombData.base, ?_⟩
      intro G t v A B C x hv hA hB hC
      have hzero : CombTerm CombData.base G t v A B C x = 0 := by
        simp only [CombTerm, CombData.base, Fintype.sum_empty]
      show tower (lcOf (G 0)) (fun _ => aOf G t) 0 v A B C x
        = Wterm G t 0 v A B C x + CombTerm CombData.base G t v A B C x
      rw [hzero, add_zero, Wterm]
      simp only [tower, aOf, selTerm, gtTower, gtower, gtBase, deltaTower, vtower, covDiff]
  | succ c ih =>
      obtain ⟨D, hD⟩ := ih
      refine ⟨D.succ, ?_⟩
      intro G t
      have hWsm : SmOpSel (Wterm G t c) := fun v A B C hv hA hB hC =>
        selTerm_sm hLC G t c 0 c (fun k : Fin 0 => k.elim0) (fun k : Fin c => k) v A B C
          hv hA hB hC
      have hσsm : ∀ n : D.ι, SmOpSel (selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n)) :=
        fun n v A B C hv hA hB hC =>
          selTerm_sm hLC G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n) v A B C hv hA hB hC
      have hSumSm : SmOpSel (CombTerm D G t) := by
        intro v A B C hv hA hB hC
        show SmF I M (fun y : M => ∑ n : D.ι,
          selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n) v A B C y)
        exact smF_sumT (Finset.univ : Finset D.ι)
          (fun n : D.ι => selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n) v A B C)
          (fun n _ => hσsm n v A B C hv hA hB hC)
      -- the one-step rule for the `i = 0` summand
      have hWstep : OpEqSel (step (lcOf (G 0)) (Wterm G t c))
          (fun v A B C y => Wterm G t (c + 1) v A B C y + CombTermE G t c v A B C y) := by
        intro v A B C x hv hA hB hC
        have h := Work.Diff.EXT.ConnCov.DT.hAaux.step_selTerm hLC G t (c := c) (i := 0) (j := c)
          (by omega) (fun k : Fin 0 => k.elim0) (fun k : Fin c => k)
          (fun a b _ => a.elim0) (fun a b h => h)
          (by rw [Set.disjoint_left]; rintro k ⟨a, ha⟩ ⟨b, hb⟩; exact a.elim0)
          (by intro k; exact Or.inr ⟨k, rfl⟩)
          (fun d Y₁ Y₂ Z hd hY₁ hY₂ hZ =>
            gtTower_add_val0 hLC G t 0 d Y₁ Y₂ Z hd hY₁ hY₂ hZ)
          v A B C hv hA hB hC x
        rw [show selTerm G t c 0 c (fun k : Fin 0 => k.elim0) (fun k : Fin c => k)
              = Wterm G t c from rfl] at h
        rw [h]
        have hzero : selTerm G t (c + 1) 0 (c + 1) (Fshift (fun k : Fin 0 => k.elim0))
            (GTen (fun k : Fin c => k)) = Wterm G t (c + 1) :=
          selTerm_zero_eq_Wterm G t _ _ GTen_id_eq
        rw [hzero]
        simp only [CombTermE, Nat.zero_add]
        ring
      -- the one-step rule for the summands
      have hσstep : ∀ n : D.ι, ∀ v A B C x,
          (∀ k, SmE I M (v k)) → SmE I M A → SmE I M B → SmE I M C →
          step (lcOf (G 0)) (selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n)) v A B C x
            = selTerm G t (c + 1) (D.m n + 1 + 1) (D.j n) (FTen (D.F n)) (Gshift (D.G' n))
                v A B C x
              + selTerm G t (c + 1) (D.m n + 1) (D.j n + 1) (Fshift (D.F n)) (GTen (D.G' n))
                v A B C x := by
        intro n v A B C x hv hA hB hC
        exact Work.Diff.EXT.ConnCov.DT.hAaux.step_selTerm hLC G t (D.hmj n) (D.F n) (D.G' n)
          (D.hfinj n) (D.hginj n) (D.hdisj n)
          (range_union_eq_univ (D.hmj n) (D.F n) (D.G' n) (D.hfinj n) (D.hginj n)
            (D.hdisj n))
          (fun d Y₁ Y₂ Z hd hY₁ hY₂ hZ =>
            gtTower_add_val0 hLC G t (D.m n + 1) d Y₁ Y₂ Z hd hY₁ hY₂ hZ)
          v A B C hv hA hB hC x
      -- the step of the sum
      have hstepSum : OpEqSel (step (lcOf (G 0)) (CombTerm D G t))
          (fun v A B C y => CombTermL D G t v A B C y + CombTermR D G t v A B C y) := by
        have h := step_sumT (I := I) (M := M) hLC G (c := c) (ι := D.ι)
          (σ := fun n : D.ι => selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n))
          (h := fun n => hσsm n)
        intro v A B C x hv hA hB hC
        have h1 : step (lcOf (G 0))
              (fun v A B C y => ∑ n : D.ι,
                selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n) v A B C y) v A B C x
            = ∑ n : D.ι, step (lcOf (G 0))
                (selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n)) v A B C x :=
          h v A B C x hv hA hB hC
        change step (lcOf (G 0))
              (fun v A B C y => ∑ n : D.ι,
                selTerm G t c (D.m n + 1) (D.j n) (D.F n) (D.G' n) v A B C y) v A B C x
            = CombTermL D G t v A B C x + CombTermR D G t v A B C x
        rw [h1]
        rw [Finset.sum_congr rfl (fun n _ => hσstep n v A B C x hv hA hB hC)]
        simp only [CombTermL, CombTermR]
        rw [Finset.sum_add_distrib]
      refine (OpEqSel.refl
        (tower (lcOf (G 0)) (fun _ => aOf G t) (c + 1))).trans ?_
      refine (step_congr_sel hLC G (hD G t)).trans ?_
      refine (step_add_sel hLC G hWsm hSumSm).trans ?_
      refine (OpEqSel.add hWstep hstepSum).trans ?_
      intro v A B C x hv hA hB hC
      rw [CombTerm_succ_eq]
      simp only [Pi.add_apply]
      ring

end Work.Diff.EXT.ConnCov.DT
