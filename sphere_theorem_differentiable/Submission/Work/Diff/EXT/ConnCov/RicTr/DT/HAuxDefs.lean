import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.DeltaTower

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for `deltaTower_bound_of_hA`

`Work.Diff.EXT.ConnCov.DT.deltaTower G t c` is the `∇^{G 0}`-tower of the connection difference
`δ = covDiff G t`, and `Work.Diff.EXT.ConnCov.DT.Wins G t c` is its lowering (an `Op3 c`).
The bound of the δ-tower from the known bounds of the tower of `aOf G t = g_t(δ ·, ·)` is proved from
the **Leibniz expansion** of the tower of the twisted pairing `pairOp S T`
(`pairOp (gtTower G t i) (deltaTower G t j) : Op3 (i+j)`), which rests on

* `step_dperm`: one recursion step commutes with a reindexing of the *direction* slots by a
  permutation of `Fin k`;
* `step_pairOp`:
  `step (lcOf (G 0)) (pairOp S T) = pairOp (gstep (lcOf (G 0)) S) T
      + dperm (cyc i j) (pairOp S (vstep (lcOf (G 0)) T))`.

Iterating these two relations along binary words produces the family of "word terms"

  `T c w := dperm (wPerm c w) (pairOp (gtTower G t (wArity c w)) (deltaTower G t (c - wArity c w)))`

satisfying `step (T c w) = T (c+1) (cons true w) + T (c+1) (cons false w)`; the resulting decomposition

  `tower (lcOf (G 0)) aOf c = Wins G t c + Σ_{w with a true} T c w`

bounds the δ-tower, since a term `T c w` with a true in `w` has a `deltaTower`-factor of level
`≤ c - 1` (induction hypothesis) and a `gtTower`-factor of level `≤ c` (hypothesis `hA`).

This module contains only *definitions* and their elementary properties (no `sorry`), so that the
lemmas about them can be delegated.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.DT

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Reindexing of the direction slots -/

/-- `dperm σ τ` is the operator `τ` with its direction slots reindexed by the permutation `σ`:
`(dperm σ τ) v A B C x = τ (fun i => v (σ i)) A B C x`. -/
noncomputable def dperm {k : ℕ} (σ : Equiv.Perm (Fin k)) (τ : Op3 (I := I) (M := M) k) :
    Op3 (I := I) (M := M) k :=
  fun v A B C x => τ (fun i => v (σ i)) A B C x

@[simp] theorem dperm_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (τ : Op3 (I := I) (M := M) k)
    (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M) :
    dperm σ τ v A B C x = τ (fun i => v (σ i)) A B C x := rfl

theorem dperm_trans {k : ℕ} (σ τ : Equiv.Perm (Fin k)) (Φ : Op3 (I := I) (M := M) k) :
    dperm σ (dperm τ Φ) = dperm (τ.trans σ) Φ := by
  funext v A B C x
  simp only [dperm]
  rfl

@[simp] theorem dperm_refl {k : ℕ} (Φ : Op3 (I := I) (M := M) k) :
    dperm (Equiv.refl (Fin k)) Φ = Φ := by
  funext v A B C x
  simp only [dperm]
  rfl

/-- `dperm` is additive in its operator argument. -/
theorem dperm_add {k : ℕ} (σ : Equiv.Perm (Fin k)) (Φ Ψ : Op3 (I := I) (M := M) k) :
    dperm σ (fun v A B C x => Φ v A B C x + Ψ v A B C x)
      = fun v A B C x => dperm σ Φ v A B C x + dperm σ Ψ v A B C x := by
  funext v A B C x
  simp only [dperm]

/-! ## Extending a permutation by a fixed point at `0` -/

/-- The extension of `σ : Perm (Fin k)` to `Fin (k+1)`, fixing `0` and shifting the rest. -/
noncomputable def psucc {k : ℕ} (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.ofBijective (fun j : Fin (k + 1) => Fin.cases (0 : Fin (k + 1)) (fun i => (σ i).succ) j) (by
    constructor
    · intro a b h
      induction a using Fin.cases with
      | zero =>
          induction b using Fin.cases with
          | zero => rfl
          | succ j =>
              simp only [Fin.cases_zero, Fin.cases_succ] at h
              exact absurd h.symm (Fin.succ_ne_zero (σ j))
      | succ i =>
          induction b using Fin.cases with
          | zero =>
              simp only [Fin.cases_zero, Fin.cases_succ] at h
              exact absurd h (Fin.succ_ne_zero (σ i))
          | succ j =>
              simp only [Fin.cases_succ, Fin.succ_inj] at h
              exact congrArg Fin.succ (σ.injective h)
    · intro b
      induction b using Fin.cases with
      | zero => exact ⟨0, by simp only [Fin.cases_zero]⟩
      | succ m => exact ⟨(σ.symm m).succ, by
          simp only [Fin.cases_succ]
          exact congrArg Fin.succ (σ.apply_symm_apply m)⟩)

@[simp] theorem psucc_zero {k : ℕ} (σ : Equiv.Perm (Fin k)) : psucc σ 0 = 0 := rfl

@[simp] theorem psucc_succ {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    psucc σ i.succ = (σ i).succ := rfl

/-- The action of `psucc` on a successor, read backwards. -/
theorem psucc_inj {k : ℕ} {σ : Equiv.Perm (Fin k)} {i : Fin k} {j : Fin (k + 1)}
    (h : psucc σ j = i.succ) : ∃ j' : Fin k, j = j'.succ ∧ σ j' = i := by
  induction j using Fin.cases with
  | zero => simp only [psucc_zero] at h; exact absurd h.symm (Fin.succ_ne_zero i)
  | succ j' =>
      refine ⟨j', rfl, ?_⟩
      have h2 : (σ j').succ = i.succ := by simpa only [psucc_succ] using h
      exact Fin.succ_injective _ h2

/-! ## The cycle `0 ↦ 1 ↦ ⋯ ↦ i ↦ 0` -/

/-- The value of the cycle `0 ↦ 1 ↦ ⋯ ↦ i ↦ 0`, as a function of the value. -/
def cycFunN (i k : ℕ) : ℕ := if k < i then k + 1 else if k = i then 0 else k

/-- The value of the inverse of the cycle `0 ↦ 1 ↦ ⋯ ↦ i ↦ 0`, as a function of the value. -/
def cycInvFunN (i m : ℕ) : ℕ := if m = 0 then i else if m ≤ i then m - 1 else m

/-- The value of the cycle `0 ↦ 1 ↦ ⋯ ↦ i ↦ 0` on `Fin (i+j+1)`. -/
def cycFun (i j : ℕ) (k : Fin (i + j + 1)) : ℕ := cycFunN i k.val

/-- The value of the inverse of the cycle `0 ↦ 1 ↦ ⋯ ↦ i ↦ 0`. -/
def cycInvFun (i j : ℕ) (m : Fin (i + j + 1)) : ℕ := cycInvFunN i m.val

theorem cycFunN_val_lt {i k : ℕ} (h : k < i) : cycFunN i k = k + 1 := by
  simp only [cycFunN]; exact if_pos h

theorem cycFunN_val_eq {i k : ℕ} (h : k = i) : cycFunN i k = 0 := by
  simp only [cycFunN]; rw [if_neg (by omega), if_pos h]

theorem cycFunN_val_gt {i k : ℕ} (h : i < k) : cycFunN i k = k := by
  simp only [cycFunN]; rw [if_neg (by omega), if_neg (by omega)]

theorem cycInvFunN_val_zero {i m : ℕ} (h : m = 0) : cycInvFunN i m = i := by
  simp only [cycInvFunN]; exact if_pos h

theorem cycInvFunN_val_pos {i m : ℕ} (h0 : m ≠ 0) (h : m ≤ i) : cycInvFunN i m = m - 1 := by
  simp only [cycInvFunN]; rw [if_neg h0, if_pos h]

theorem cycInvFunN_val_gt {i m : ℕ} (h : i < m) : cycInvFunN i m = m := by
  simp only [cycInvFunN]; rw [if_neg (by omega), if_neg (by omega)]

theorem cycFunN_lt {i j k : ℕ} (hk : k < i + j + 1) : cycFunN i k < i + j + 1 := by
  rcases lt_trichotomy k i with h | h | h
  · rw [cycFunN_val_lt h]; omega
  · rw [cycFunN_val_eq h]; omega
  · rw [cycFunN_val_gt h]; omega

theorem cycInvFunN_lt {i j m : ℕ} (hm : m < i + j + 1) : cycInvFunN i m < i + j + 1 := by
  rcases eq_or_ne m 0 with h | h
  · rw [cycInvFunN_val_zero h]; omega
  · rcases lt_or_ge m (i + 1) with h2 | h2
    · rw [cycInvFunN_val_pos h (by omega)]; omega
    · rw [cycInvFunN_val_gt (by omega)]; omega

theorem cycInvFunN_cycFunN {i j k : ℕ} (hk : k < i + j + 1) :
    cycInvFunN i (cycFunN i k) = k := by
  rcases lt_trichotomy k i with h | h | h
  · rw [cycFunN_val_lt h, cycInvFunN_val_pos (by omega) (by omega)]; omega
  · rw [cycFunN_val_eq h, cycInvFunN_val_zero rfl]; omega
  · rw [cycFunN_val_gt h, cycInvFunN_val_gt h]

theorem cycFunN_cycInvFunN {i j m : ℕ} (hm : m < i + j + 1) :
    cycFunN i (cycInvFunN i m) = m := by
  rcases eq_or_ne m 0 with h | h
  · rw [cycInvFunN_val_zero h, h]
    exact cycFunN_val_eq rfl
  · rcases lt_or_ge m (i + 1) with h2 | h2
    · rw [cycInvFunN_val_pos h (by omega), cycFunN_val_lt (by omega)]; omega
    · rw [cycInvFunN_val_gt (by omega), cycFunN_val_gt (by omega)]

theorem cycFun_lt (i j : ℕ) (k : Fin (i + j + 1)) : cycFun i j k < i + j + 1 :=
  cycFunN_lt k.isLt

theorem cycInvFun_lt (i j : ℕ) (m : Fin (i + j + 1)) : cycInvFun i j m < i + j + 1 :=
  cycInvFunN_lt m.isLt

/-- The cycle `0 ↦ 1 ↦ ⋯ ↦ i ↦ 0` as a permutation of `Fin (i+j+1)`. -/
noncomputable def cyc (i j : ℕ) : Equiv.Perm (Fin (i + j + 1)) :=
  Equiv.ofBijective (fun k => (⟨cycFun i j k, cycFun_lt i j k⟩ : Fin (i + j + 1))) (by
    refine ⟨fun a b h => ?_, fun b => ⟨⟨cycInvFun i j b, cycInvFun_lt i j b⟩, ?_⟩⟩
    · have h' : cycFunN i a.val = cycFunN i b.val := congrArg Fin.val h
      apply Fin.ext
      rw [← cycInvFunN_cycFunN (i := i) (j := j) (k := a.val) a.isLt,
        ← cycInvFunN_cycFunN (i := i) (j := j) (k := b.val) b.isLt, h']
    · apply Fin.ext
      show cycFunN i (cycInvFunN i b.val) = b.val
      exact cycFunN_cycInvFunN b.isLt)

@[simp] theorem cyc_apply_val (i j : ℕ) (k : Fin (i + j + 1)) :
    (cyc i j k).val = cycFunN i k.val := rfl

theorem cyc_apply_lt {i j : ℕ} {k : Fin (i + j + 1)} (h : k.val < i) :
    (cyc i j k).val = k.val + 1 := cycFunN_val_lt h

theorem cyc_apply_eq {i j : ℕ} {k : Fin (i + j + 1)} (h : k.val = i) :
    (cyc i j k).val = 0 := cycFunN_val_eq h

theorem cyc_apply_gt {i j : ℕ} {k : Fin (i + j + 1)} (h : i < k.val) : cyc i j k = k := by
  apply Fin.ext
  exact cycFunN_val_gt h

/-! ## The terms of the Leibniz expansion

A "term" is the twisted pairing `pairOp` of the metric tower `∇^{G 0, i}g_t` with the δ-tower
`∇^{G 0, j}δ`, with the directions distributed by two *selections* `F : Fin i → Fin c` and
`G : Fin j → Fin c` (where `i + j = c`).  Every term of the expansion arises with such a pair of
selections, and the effect of one recursion step is to shift the selections by
`FTen`/`Gshift` (the metric factor receives the new direction) or by `Fshift`/`GTen` (the δ factor
receives it). -/

/-- **The term of the expansion**: the metric tower `∇^{G 0,i}g_t` paired with the δ-tower
`∇^{G 0,j}δ`, with the directions `Fin (i+j)` distributed by the selections `F` and `G`. -/
noncomputable def selTerm (G : ℝ → SMet I M) (t : ℝ) (c i j : ℕ)
    (F : Fin i → Fin c) (G' : Fin j → Fin c) : Op3 (I := I) (M := M) c :=
  fun v A B C y =>
    gtTower G t i (fun k => v (F k)) (deltaTower G t j (fun k => v (G' k)) B A) C y

/-- The `i = 0` term: the lowering of the δ-tower in the direction tuple (with the two section
slots exchanged, so that it is `aOf G t` at level `0`). -/
noncomputable def Wterm (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) : Op3 (I := I) (M := M) c :=
  selTerm G t c 0 c (fun k : Fin 0 => k.elim0) (fun k : Fin c => k)

/-- The new selection of the metric factor when it receives the new direction. -/
def FTen {i c : ℕ} (F : Fin i → Fin c) : Fin (i + 1) → Fin (c + 1) :=
  Fin.cases 0 (fun k => (F k).succ)

/-- The new selection of the δ factor when the *metric* factor receives the new direction. -/
def Gshift {j c : ℕ} (G : Fin j → Fin c) : Fin j → Fin (c + 1) := fun k => (G k).succ

/-- The new selection of the metric factor when the *δ* factor receives the new direction. -/
def Fshift {i c : ℕ} (F : Fin i → Fin c) : Fin i → Fin (c + 1) := fun k => (F k).succ

/-- The new selection of the δ factor when it receives the new direction. -/
def GTen {j c : ℕ} (G : Fin j → Fin c) : Fin (j + 1) → Fin (c + 1) :=
  Fin.cases 0 (fun k => (G k).succ)

@[simp] theorem FTen_zero {i c : ℕ} (F : Fin i → Fin c) : FTen F 0 = 0 := rfl

@[simp] theorem FTen_succ {i c : ℕ} (F : Fin i → Fin c) (k : Fin i) :
    FTen F k.succ = (F k).succ := rfl

@[simp] theorem GTen_zero {j c : ℕ} (G : Fin j → Fin c) : GTen G 0 = 0 := rfl

@[simp] theorem GTen_succ {j c : ℕ} (G : Fin j → Fin c) (k : Fin j) :
    GTen G k.succ = (G k).succ := rfl

@[simp] theorem Fshift_apply {i c : ℕ} (F : Fin i → Fin c) (k : Fin i) :
    Fshift F k = (F k).succ := rfl

@[simp] theorem Gshift_apply {j c : ℕ} (G : Fin j → Fin c) (k : Fin j) :
    Gshift G k = (G k).succ := rfl

/-! ## The bound-carrying predicate -/

/-- `IsComb G t c τ` says that `τ` is a finite sum of expansion terms of level `c` whose metric
factor has level `≥ 1` (so that its level-`j` δ factor has `j < c`), the number of terms being at
most `2^c`. -/
def IsComb (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) (τ : Op3 (I := I) (M := M) c) : Prop :=
  ∃ (N : ℕ) (i j : Fin N → ℕ)
    (F : ∀ n : Fin N, Fin (i n) → Fin c) (G' : ∀ n : Fin N, Fin (j n) → Fin c),
    N ≤ 2 ^ c ∧ (∀ n, 1 ≤ i n) ∧ (∀ n, i n + j n = c) ∧
      (∀ n, Function.Injective (F n)) ∧ (∀ n, Function.Injective (G' n)) ∧
      (∀ n, Disjoint (Set.range (F n)) (Set.range (G' n))) ∧
      τ = ∑ n, selTerm G t c (i n) (j n) (F n) (G' n)

end Work.Diff.EXT.ConnCov.DT
