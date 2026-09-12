import Mathlib
import Submission.Sec3Tower
import Submission.RoughDecay
import Submission.RoughDecay2
import Submission.ProdCount
import Submission.Admissible

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3: the recursive product count (Proposition p:rough decay, Step 7C)

On top of `Submission.ProdCount` (recursive tuple Finsets) and
`Submission.RoughDecay2` (prefix invariance of the level conditions), this
module proves the structural recursion for the count of realizations `x` of
the random vector (each `x j ∈ A j`) whose level conditions (non-decay along
the descendant sequence) hold:

  `countPre (k+1) ≤ countPre k · |A⟨k⟩|`

(the extension of every valid `k`-prefix by the coordinate `k` contributes at
most `|A⟨k⟩|` many `(k+1)`-tuples).  The `q′`-refined version (a factor `q′`
per good level) is a thin layer on top.
-/

open scoped BigOperators

namespace Submission.RoughProduct

attribute [local instance] Classical.propDecidable

open Submission.Sec3Tower
open Submission.Sec3
open Submission.RoughDecay
open Submission.RoughDecay2
open Submission.ProdCount
open Submission.IntFun
open Submission.Admissible

/-! ## 1. Prefix coordinate families and patterns -/

/-- The coordinate family restricted to the first `k ≤ ℓ` coordinates. -/
def preCoord {ℓ k : ℕ} (hk : k ≤ ℓ) (A : Fin ℓ → Finset ℤ) : Fin k → Finset ℤ :=
  fun j => A (Fin.castLE hk j)

/-- The pattern `v` restricted to the first `k ≤ ℓ` coordinates. -/
def preFun {ℓ k : ℕ} (hk : k ≤ ℓ) (v : Fin ℓ → ℤ) : Fin k → ℤ :=
  fun j => v (Fin.castLE hk j)

/-- The restricted coordinate family is compatible with further restriction by
one coordinate (`castSucc` case). -/
lemma preCoord_castSucc {ℓ k : ℕ} {hk' : k + 1 ≤ ℓ} (A : Fin ℓ → Finset ℤ)
    (j : Fin k) :
    preCoord hk' A (Fin.castSucc j) =
      preCoord (Nat.le_trans (Nat.le_succ k) hk') A j := by
  dsimp [preCoord]

/-- The restricted coordinate family agrees with the ambient one at the last
coordinate of the prefix. -/
lemma preCoord_last {ℓ k : ℕ} {hk' : k + 1 ≤ ℓ} (A : Fin ℓ → Finset ℤ) :
    preCoord hk' A (Fin.last k) = A ⟨k, Nat.lt_of_succ_le hk'⟩ := by
  dsimp [preCoord]
  apply congrArg A
  apply Fin.ext
  simp

/-- The restricted pattern is compatible with further restriction by one
coordinate (`castSucc` case). -/
lemma preFun_castSucc {ℓ k : ℕ} {hk' : k + 1 ≤ ℓ} (v : Fin ℓ → ℤ) (j : Fin k) :
    preFun hk' v (Fin.castSucc j) = preFun (Nat.le_trans (Nat.le_succ k) hk') v j := by
  dsimp [preFun]

/-- The restricted pattern agrees with the ambient one at the last coordinate
of the prefix. -/
lemma preFun_last {ℓ k : ℕ} {hk' : k + 1 ≤ ℓ} (v : Fin ℓ → ℤ) :
    preFun hk' v (Fin.last k) = v ⟨k, Nat.lt_of_succ_le hk'⟩ := by
  dsimp [preFun]
  apply congrArg v
  apply Fin.ext
  simp

/-! ## 2. Fiber decomposition of filters over products -/

/-- Extending by a value is injective in the value. -/
lemma extendFin_injective_a {ℓ : ℕ} (y : Fin ℓ → ℤ) :
    Function.Injective (fun a : ℤ => extendFin y a) := by
  intro a₁ a₂ h
  have hlast := congrFun h (Fin.last ℓ)
  simpa [extendFin] using hlast

/-- The recursive product set is compatible with pointwise-equal families. -/
lemma prodFinset_congr {ℓ : ℕ} {B B' : Fin ℓ → Finset ℤ}
    (h : ∀ j : Fin ℓ, B j = B' j) :
    prodFinset ℓ B = prodFinset ℓ B' := by
  classical
  apply Finset.ext
  intro x
  rw [mem_prodFinset, mem_prodFinset]
  apply forall_congr'
  intro j
  rw [h j]

/-- Counting tuples of length `k+1` satisfying `P` by the first `k` coordinates
and the last coordinate value. -/
lemma filter_card_fiber {k : ℕ} (A : Fin (k + 1) → Finset ℤ) (P : (Fin (k + 1) → ℤ) → Prop) :
    ((prodFinset (k + 1) A).filter P).card =
      ∑ y ∈ prodFinset k (fun j : Fin k => A (Fin.castSucc j)),
        ((A (Fin.last k)).filter (fun a : ℤ => P (extendFin y a))).card := by
  classical
  have hdecomp : prodFinset (k + 1) A =
      (prodFinset k (fun j : Fin k => A (Fin.castSucc j))).biUnion
        (fun y : Fin k → ℤ => (A (Fin.last k)).image (fun a : ℤ => extendFin y a)) := by
    rfl
  rw [hdecomp]
  rw [Finset.filter_biUnion]
  let s : Finset (Fin k → ℤ) := prodFinset k (fun j : Fin k => A (Fin.castSucc j))
  have hdisj : (↑s : Set (Fin k → ℤ)).PairwiseDisjoint
      (fun y : Fin k → ℤ => ((A (Fin.last k)).image (fun a : ℤ => extendFin y a)).filter P) := by
    intro y₁ hy₁ y₂ hy₂ hne
    have hst := disjoint_extend_image (Y := A (Fin.last k)) (y₁ := y₁) (y₂ := y₂) hne
    change Disjoint (((A (Fin.last k)).image (fun a : ℤ => extendFin y₁ a)).filter P)
        (((A (Fin.last k)).image (fun a : ℤ => extendFin y₂ a)).filter P)
    rw [Finset.disjoint_left] at hst ⊢
    intro x hx₁ hx₂
    exact (hst (Finset.mem_filter.mp hx₁).1) (Finset.mem_filter.mp hx₂).1
  have hb := Finset.card_biUnion hdisj
  calc
    (((prodFinset k (fun j : Fin k => A (Fin.castSucc j))).biUnion
        (fun y : Fin k → ℤ => ((A (Fin.last k)).image (fun a : ℤ => extendFin y a)).filter P)).card)
        = (∑ y ∈ prodFinset k (fun j : Fin k => A (Fin.castSucc j)),
              (((A (Fin.last k)).image (fun a : ℤ => extendFin y a)).filter P).card) := by
          simpa [s] using hb
    _ = (∑ y ∈ prodFinset k (fun j : Fin k => A (Fin.castSucc j)),
          ((A (Fin.last k)).filter (fun a : ℤ => P (extendFin y a))).card) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.filter_image]
          have hinj := extendFin_injective_a (y := y)
          exact (Finset.card_image_of_injective
            (s := (A (Fin.last k)).filter (fun a : ℤ => P (extendFin y a)))
            (f := fun a : ℤ => extendFin y a) hinj)

/-- The fiber decomposition specialised to prefix coordinate families. -/
lemma filter_card_fiber_pre {ℓ k : ℕ} {hk' : k + 1 ≤ ℓ} (A : Fin ℓ → Finset ℤ)
    (P : (Fin (k + 1) → ℤ) → Prop) :
    ((prodFinset (k + 1) (preCoord hk' A)).filter P).card =
      ∑ y ∈ prodFinset k (preCoord (Nat.le_trans (Nat.le_succ k) hk') A),
        ((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
          P (extendFin y a))).card := by
  classical
  have hf := filter_card_fiber (A := preCoord hk' A) (P := P)
  have hfam : (fun j : Fin k => preCoord hk' A (Fin.castSucc j)) =
      preCoord (Nat.le_trans (Nat.le_succ k) hk') A := by
    funext j
    exact preCoord_castSucc A j
  have hlast : preCoord hk' A (Fin.last k) = A ⟨k, Nat.lt_of_succ_le hk'⟩ := preCoord_last A
  rw [hfam, hlast] at hf
  exact hf

/-! ## 3. The recursion for the prefix count -/

/-- The level condition is independent of the choice of proof `m < K`. -/
lemma levelCond_proof_irrel {K : ℕ} {f : ℤ → ℝ} {p : unitInterval} {T : ℝ}
    {x : Fin K → ℤ} {v : Fin K → ℤ} {t₀ : ℤ} {m : ℕ} {h₁ h₂ : m < K} :
    levelCond f p T x v t₀ m h₁ = levelCond f p T x v t₀ m h₂ := by
  simp [levelCond]

/-- The prefix pattern of length `k+1`, restricted to `k` coordinates, is the
`k`-prefix pattern. -/
lemma preFun_restrict_eq {ℓ k : ℕ} {hk' : k + 1 ≤ ℓ} (v : Fin ℓ → ℤ) :
    restrict (preFun hk' v) = preFun (Nat.le_trans (Nat.le_succ k) hk') v := by
  funext j
  dsimp [preFun, restrict]

/-- The full length-`k+1` condition splits into the conditions at levels
`m < k` (which live on the `k`-prefix) and the condition at the top level
`k`. -/
lemma fullCond_split {ℓ k : ℕ} {hk' : k + 1 ≤ ℓ} {f : ℤ → ℝ} {p : unitInterval}
    {T : ℝ} {I : Finset ℕ} {t₀ : ℤ} {v : Fin ℓ → ℤ} (x : Fin (k + 1) → ℤ) :
    (∀ m : ℕ, m ∈ I → ∀ h : m < k + 1,
        levelCond f p T x (preFun hk' v) t₀ m h) ↔
      (∀ m : ℕ, m ∈ I → ∀ h : m < k,
          levelCond f p T (restrict x) (preFun (Nat.le_trans (Nat.le_succ k) hk') v) t₀ m h) ∧
        (k ∈ I → levelCond f p T x (preFun hk' v) t₀ k (Nat.lt_succ_self k)) := by
  classical
  constructor
  · intro hQ
    constructor
    · intro m hmI hmk
      have hQm := hQ m hmI (Nat.lt_trans hmk (Nat.lt_succ_self k))
      have hrest := (levelCond_eq_of_restrict (f := f) (p := p) (x := x)
          (v := preFun hk' v) (t₀ := t₀) (T := T) (hm := hmk)).2 hQm
      have hpre : restrict (preFun hk' v) = preFun (Nat.le_trans (Nat.le_succ k) hk') v :=
        preFun_restrict_eq v
      simpa [hpre] using hrest
    · intro hkI
      exact hQ k hkI (Nat.lt_succ_self k)
  · intro h m hmI hmk1
    by_cases hmk : m < k
    · have hm' := h.1 m hmI hmk
      have hfull := (levelCond_eq_of_restrict (f := f) (p := p) (x := x)
          (v := preFun hk' v) (t₀ := t₀) (T := T) (hm := hmk)).1 hm'
      have hpre : restrict (preFun hk' v) = preFun (Nat.le_trans (Nat.le_succ k) hk') v :=
        preFun_restrict_eq v
      have hfull' : levelCond f p T x (preFun hk' v) t₀ m (Nat.lt_trans hmk (Nat.lt_succ_self k)) := by
        simpa [hpre] using hfull
      simpa [levelCond_proof_irrel] using hfull'
    · have hmk_eq : m = k := by
        have hlt : m < k + 1 := hmk1
        omega
      subst m
      have htop := h.2 hmI
      simpa [levelCond_proof_irrel] using htop

/-- A filter whose predicate begins with a constant proposition. -/
lemma card_filter_and_const {α : Type} (s : Finset α) (p : Prop) (q : α → Prop) :
    (s.filter (fun a => p ∧ q a)).card = if p then (s.filter q).card else 0 := by
  classical
  by_cases h : p
  · simp [h]
  · simp [h]

/-- The count of length-`k` prefixes (values in the first `k` coordinate
families) whose level conditions at all levels `m ∈ I`, `m < k`, hold. -/
noncomputable def countPre {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (T : ℝ)
    (I : Finset ℕ) (t₀ : ℤ) (A : Fin ℓ → Finset ℤ) (v : Fin ℓ → ℤ) :
    (k : ℕ) → k ≤ ℓ → ℕ :=
  fun k hk =>
    ((prodFinset k (preCoord hk A)).filter
      (fun y : Fin k → ℤ => ∀ m : ℕ, m ∈ I → ∀ h : m < k,
        levelCond f p T y (preFun hk v) t₀ m h)).card

/-- The recursion: every valid `(k+1)`-prefix arises from a valid `k`-prefix by
choosing the last coordinate value (at most `|A⟨k⟩|` choices). -/
lemma countPre_step {ℓ : ℕ} {f : ℤ → ℝ} {p : unitInterval} {T : ℝ} {I : Finset ℕ}
    {t₀ : ℤ} {A : Fin ℓ → Finset ℤ} {v : Fin ℓ → ℤ} {k : ℕ} {hk' : k + 1 ≤ ℓ} :
    countPre f p T I t₀ A v (k + 1) hk' ≤
      countPre f p T I t₀ A v k (Nat.le_trans (Nat.le_succ k) hk') *
        (A ⟨k, Nat.lt_of_succ_le hk'⟩).card := by
  classical
  let hk : k ≤ ℓ := Nat.le_trans (Nat.le_succ k) hk'
  let P : (Fin (k + 1) → ℤ) → Prop := fun x =>
    ∀ m : ℕ, m ∈ I → ∀ h : m < k + 1, levelCond f p T x (preFun hk' v) t₀ m h
  let prefixOk : (Fin k → ℤ) → Prop := fun y =>
    ∀ m : ℕ, m ∈ I → ∀ h : m < k, levelCond f p T y (preFun hk v) t₀ m h
  have hfib := filter_card_fiber_pre (A := A) (P := P) (hk' := hk')
  have hLHS : countPre f p T I t₀ A v (k + 1) hk' =
      (∑ y ∈ prodFinset k (preCoord hk A),
        ((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card) := by
    simpa [countPre, P, hk] using hfib
  have hterm : ∀ y ∈ prodFinset k (preCoord hk A),
      ((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card ≤
        (A ⟨k, Nat.lt_of_succ_le hk'⟩).card * (if prefixOk y then 1 else 0) := by
    intro y hy
    have hiff : ∀ a : ℤ, P (extendFin y a) ↔
        prefixOk y ∧ (k ∈ I → levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k)) := by
      intro a
      have hsa := fullCond_split (f := f) (p := p) (T := T) (I := I) (t₀ := t₀)
          (v := v) (hk' := hk') (x := extendFin y a)
      have hr : restrict (extendFin y a) = y := restrict_extend y a
      simpa [P, prefixOk, hk, hr] using hsa
    by_cases hp : prefixOk y
    · have hle := Finset.card_filter_le (A ⟨k, Nat.lt_of_succ_le hk'⟩) (fun a : ℤ => P (extendFin y a))
      simpa [hp] using hle
    · have hempty : (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a)) = ∅ := by
        apply Finset.ext
        intro a
        constructor
        · intro ha
          have hP := (Finset.mem_filter.mp ha).2
          have hiff_a := (hiff a).1 hP
          exact False.elim (hp hiff_a.1)
        · intro hmem
          simp at hmem
      simp [hempty, hp]
  calc
    countPre f p T I t₀ A v (k + 1) hk'
        = (∑ y ∈ prodFinset k (preCoord hk A),
            ((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card) := hLHS
    _ ≤ (∑ y ∈ prodFinset k (preCoord hk A),
          (A ⟨k, Nat.lt_of_succ_le hk'⟩).card * (if prefixOk y then 1 else 0)) := by
          exact Finset.sum_le_sum hterm
    _ = (A ⟨k, Nat.lt_of_succ_le hk'⟩).card *
          (∑ y ∈ prodFinset k (preCoord hk A), (if prefixOk y then 1 else 0)) := by
          rw [← Finset.mul_sum]
    _ ≤ (A ⟨k, Nat.lt_of_succ_le hk'⟩).card * countPre f p T I t₀ A v k hk := by
          have hcnt : (∑ y ∈ prodFinset k (preCoord hk A), (if prefixOk y then 1 else 0)) =
              countPre f p T I t₀ A v k hk := by
            dsimp [countPre]
            rw [Finset.card_filter]
          rw [hcnt]
    _ = countPre f p T I t₀ A v k (Nat.le_trans (Nat.le_succ k) hk') *
          (A ⟨k, Nat.lt_of_succ_le hk'⟩).card := by
          rw [Nat.mul_comm]


/-- The empty prefix has exactly one valid realization. -/
lemma countPre_zero {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (T : ℝ) (I : Finset ℕ)
    (t₀ : ℤ) (A : Fin ℓ → Finset ℤ) (v : Fin ℓ → ℤ) :
    countPre f p T I t₀ A v 0 (Nat.zero_le ℓ) = 1 := by
  classical
  dsimp [countPre]
  have hred : prodFinset 0 (preCoord (Nat.zero_le ℓ) A) =
      ({fun _ : Fin 0 => (0 : ℤ)} : Finset (Fin 0 → ℤ)) := rfl
  rw [hred]
  have hf : ({fun _ : Fin 0 => (0 : ℤ)} : Finset (Fin 0 → ℤ)).filter
      (fun y : Fin 0 → ℤ => ∀ m : ℕ, m ∈ I → ∀ h : m < 0,
        levelCond f p T y (preFun (Nat.zero_le ℓ) v) t₀ m h) =
      ({fun _ : Fin 0 => (0 : ℤ)} : Finset (Fin 0 → ℤ)) := by
    exact Finset.filter_eq_self.2 (by
      intro y hy m hmI h
      exact False.elim (Nat.not_lt_zero m h))
  rw [hf]
  simp

/-- `castLE (Nat.le_refl ℓ)` is the identity on `Fin ℓ`. -/
lemma castLE_refl_eq {ℓ : ℕ} (j : Fin ℓ) :
    Fin.castLE (Nat.le_refl ℓ) j = j := by
  apply Fin.ext
  simp

/-- The count of all valid `k`-prefixes is at most the product of the first
`k` coordinate cardinalities. -/
lemma countPre_le_prodPre {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (T : ℝ) (I : Finset ℕ)
    (t₀ : ℤ) (A : Fin ℓ → Finset ℤ) (v : Fin ℓ → ℤ) :
    ∀ (k : ℕ) (hk : k ≤ ℓ),
      countPre f p T I t₀ A v k hk ≤ ∏ j : Fin k, (preCoord hk A j).card := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk
      rw [countPre_zero]
      simp
  | succ k ih =>
      intro hk'
      have hstep := countPre_step (f := f) (p := p) (T := T) (I := I) (t₀ := t₀)
          (A := A) (v := v) (k := k) (hk' := hk')
      -- hstep: countPre (k+1) hk' ≤ countPre k (le_trans…)·(A⟨k⟩).card
      have hle := ih (Nat.le_trans (Nat.le_succ k) hk')
      -- hle: countPre k (le_trans…) ≤ ∏_{j : Fin k} (preCoord (le_trans…) A j).card
      have hprod : (∏ j : Fin k, (preCoord (Nat.le_trans (Nat.le_succ k) hk') A j).card) *
            (A ⟨k, Nat.lt_of_succ_le hk'⟩).card =
          ∏ j : Fin (k + 1), (preCoord hk' A j).card := by
        rw [Fin.prod_univ_castSucc]
        have hprod' : (∏ j : Fin k, (preCoord (Nat.le_trans (Nat.le_succ k) hk') A j).card) =
            (∏ j : Fin k, (preCoord hk' A (Fin.castSucc j)).card) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact congrArg Finset.card (preCoord_castSucc A j).symm
        have hlast : (A ⟨k, Nat.lt_of_succ_le hk'⟩).card = (preCoord hk' A (Fin.last k)).card := by
          rw [preCoord_last A]
        rw [hprod', hlast]
      calc
        countPre f p T I t₀ A v (k + 1) hk'
            ≤ countPre f p T I t₀ A v k (Nat.le_trans (Nat.le_succ k) hk') *
                (A ⟨k, Nat.lt_of_succ_le hk'⟩).card := hstep
        _ ≤ (∏ j : Fin k, (preCoord (Nat.le_trans (Nat.le_succ k) hk') A j).card) *
              (A ⟨k, Nat.lt_of_succ_le hk'⟩).card := by
              exact Nat.mul_le_mul_right _ hle
        _ = ∏ j : Fin (k + 1), (preCoord hk' A j).card := hprod

/-- The count of all valid full-length tuples is at most the product of the
coordinate cardinalities. -/
lemma countPre_le_prod {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (T : ℝ) (I : Finset ℕ)
    (t₀ : ℤ) (A : Fin ℓ → Finset ℤ) (v : Fin ℓ → ℤ) :
    countPre f p T I t₀ A v ℓ (Nat.le_refl ℓ) ≤ ∏ j : Fin ℓ, (A j).card := by
  have h := countPre_le_prodPre (f := f) (p := p) (T := T) (I := I) (t₀ := t₀)
      (A := A) (v := v) ℓ (Nat.le_refl ℓ)
  simpa [preCoord, castLE_refl_eq] using h


/-! ## 4. The `q`-refined recursion (one factor `q` per good level) -/

/-- The set of good levels below `k`: `{m ∈ I : m < k ∧ m ∈ G}`. -/
def goodBelow (I G : Finset ℕ) (k : ℕ) : Finset ℕ :=
  I.filter (fun m => m < k ∧ m ∈ G)

/-- Membership in `goodBelow`. -/
lemma mem_goodBelow {I G : Finset ℕ} {k m : ℕ} :
    m ∈ goodBelow I G k ↔ m ∈ I ∧ m < k ∧ m ∈ G := by
  simp [goodBelow]

/-- The product of `q` over the good levels below `k+1` equals that over the
good levels below `k` times the factor `q` (level `k` good) or `1`. -/
lemma goodBelow_prod {I G : Finset ℕ} (hGI : G ⊆ I) {q : ℝ} {k : ℕ} :
    (∏ m ∈ goodBelow I G (k + 1), q) =
      (∏ m ∈ goodBelow I G k, q) * (if k ∈ G then q else 1) := by
  classical
  by_cases hkG : k ∈ G
  · have hkI : k ∈ I := hGI hkG
    have hsplit : goodBelow I G (k + 1) = goodBelow I G k ∪ {k} := by
      apply Finset.ext
      intro m
      rw [mem_goodBelow, Finset.mem_union, Finset.mem_singleton, mem_goodBelow]
      constructor
      · intro h
        rcases h with ⟨hmI, hmk1, hmG⟩
        by_cases hmk : m = k
        · right
          exact hmk
        · left
          exact ⟨hmI, by omega, hmG⟩
      · intro h
        rcases h with h | hmk
        · rcases h with ⟨hmI, hmk', hmG⟩
          exact ⟨hmI, by omega, hmG⟩
        · subst m
          exact ⟨hkI, by omega, hkG⟩
    have hdisj : Disjoint (goodBelow I G k) ({k} : Finset ℕ) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hxk : x = k := Finset.mem_singleton.mp hx2
      have hxlt : x < k := (mem_goodBelow.mp hx1).2.1
      subst x
      exact (Nat.lt_irrefl k) hxlt
    rw [hsplit]
    rw [Finset.prod_union hdisj]
    simp [hkG]
  · have hsplit : goodBelow I G (k + 1) = goodBelow I G k := by
      apply Finset.ext
      intro m
      rw [mem_goodBelow, mem_goodBelow]
      constructor
      · intro h
        rcases h with ⟨hmI, hmk1, hmG⟩
        by_cases hmk : m = k
        · subst m
          exfalso
          exact hkG hmG
        · exact ⟨hmI, by omega, hmG⟩
      · intro h
        rcases h with ⟨hmI, hmk', hmG⟩
        exact ⟨hmI, by omega, hmG⟩
    rw [hsplit]
    simp [hkG]

/-- The refined count bound: each good level below `k` contributes a factor
`q`, every coordinate contributes its cardinality. -/
lemma countPreQ_le {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (T : ℝ) {I G : Finset ℕ}
    (hGI : G ⊆ I) {q : ℝ} (hq : 0 ≤ q) {t₀ : ℤ} {A : Fin ℓ → Finset ℤ} {v : Fin ℓ → ℤ}
    (hstep : ∀ k : ℕ, k ∈ G → ∀ hkℓ : k < ℓ,
      ∀ y ∈ prodFinset k (preCoord (Nat.le_of_lt hkℓ) A),
        (((A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
            levelCond f p T (extendFin y a) (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
          q * ((A ⟨k, hkℓ⟩).card : ℝ)) :
    ∀ (k : ℕ) (hk : k ≤ ℓ),
      (countPre f p T I t₀ A v k hk : ℝ) ≤
        (∏ m ∈ goodBelow I G k, q) * (∏ j : Fin k, ((preCoord hk A j).card : ℝ)) := by
  classical
  intro k
  induction k with
  | zero =>
      intro hk
      rw [countPre_zero]
      simp [goodBelow]
  | succ k ih =>
      intro hk'
      let hk : k ≤ ℓ := Nat.le_trans (Nat.le_succ k) hk'
      let P : (Fin (k + 1) → ℤ) → Prop := fun x =>
        ∀ m : ℕ, m ∈ I → ∀ h : m < k + 1, levelCond f p T x (preFun hk' v) t₀ m h
      let prefixOk : (Fin k → ℤ) → Prop := fun y =>
        ∀ m : ℕ, m ∈ I → ∀ h : m < k, levelCond f p T y (preFun hk v) t₀ m h
      let factor : ℝ := if k ∈ G then q else 1
      have hfactor0 : 0 ≤ factor := by
        by_cases hkG : k ∈ G <;> simp [factor, hkG, hq]
      have hfib := filter_card_fiber_pre (A := A) (P := P) (hk' := hk')
      have hLHS : (countPre f p T I t₀ A v (k + 1) hk' : ℝ) =
          (∑ y ∈ prodFinset k (preCoord hk A),
            (((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card : ℝ)) := by
        have hn : countPre f p T I t₀ A v (k + 1) hk' =
            (∑ y ∈ prodFinset k (preCoord hk A),
              ((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card) := by
          simpa [countPre, P, hk] using hfib
        rw [hn]
        norm_num
      have hterm : ∀ y ∈ prodFinset k (preCoord hk A),
          ((((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card : ℝ) ≤
            ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) *
              (if prefixOk y then factor else 0)) := by
        intro y hy
        have hiff : ∀ a : ℤ, P (extendFin y a) ↔
            prefixOk y ∧ (k ∈ I → levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k)) := by
          intro a
          have hsa := fullCond_split (f := f) (p := p) (T := T) (I := I) (t₀ := t₀)
              (v := v) (hk' := hk') (x := extendFin y a)
          have hr : restrict (extendFin y a) = y := restrict_extend y a
          simpa [P, prefixOk, hk, hr] using hsa
        by_cases hp : prefixOk y
        · have hcard_eq : ((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card =
              ((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                k ∈ I → levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k))).card := by
            apply congrArg Finset.card
            apply Finset.filter_congr
            intro a ha
            simpa [hp] using hiff a
          rw [hcard_eq]
          have hb : ((((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                k ∈ I → levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
              ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor) := by
            by_cases hkI : k ∈ I
            · by_cases hkG : k ∈ G
              · have hfam : preCoord (Nat.le_of_lt (Nat.lt_of_succ_le hk')) A = preCoord hk A := by
                  funext j
                  dsimp [preCoord, hk]
                have hy' : y ∈ prodFinset k (preCoord (Nat.le_of_lt (Nat.lt_of_succ_le hk')) A) := by
                  rw [hfam]
                  exact hy
                have hstep_k := hstep k hkG (Nat.lt_of_succ_le hk') y hy'
                have hsimp : (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      k ∈ I → levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k)) =
                    (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k)) := by
                  apply Finset.filter_congr
                  intro a ha
                  simp [hkI]
                rw [hsimp]
                have hcond_eq : (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      levelCond f p T (extendFin y a) (preFun (Nat.succ_le_of_lt (Nat.lt_of_succ_le hk')) v) t₀ k (Nat.lt_succ_self k)) =
                    (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k)) := by
                  rfl
                have hstep' : ((((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
                    q * ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ)) := by
                  rw [← hcond_eq]
                  exact hstep_k
                have hfac : q * ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) ≤
                    ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor := by
                  simp [factor, hkG]
                  rw [mul_comm]
                exact le_trans hstep' hfac
              · have hle : ((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k))).card ≤
                    (A ⟨k, Nat.lt_of_succ_le hk'⟩).card :=
                  Finset.card_filter_le _ _
                have hsimp : (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      k ∈ I → levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k)) =
                    (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k)) := by
                  apply Finset.filter_congr
                  intro a ha
                  simp [hkI]
                rw [hsimp]
                have hle' : (((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
                    ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor := by
                  have hc : (((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                      levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
                      ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) := by
                    exact_mod_cast hle
                  simpa [factor, hkG] using hc
                exact hle'
            · have hkG' : ¬ k ∈ G := by
                intro hkg
                exact hkI (hGI hkg)
              have hfull : (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ =>
                    k ∈ I → levelCond f p T (extendFin y a) (preFun hk' v) t₀ k (Nat.lt_succ_self k)) =
                  A ⟨k, Nat.lt_of_succ_le hk'⟩ := by
                apply Finset.filter_true_of_mem
                intro a ha
                simp [hkI]
              rw [hfull]
              simp [factor, hkG']
          simpa [hp] using hb
        · have hempty : (A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a)) = ∅ := by
            apply Finset.ext
            intro a
            constructor
            · intro ha
              have hP := (Finset.mem_filter.mp ha).2
              have hiff_a := (hiff a).1 hP
              exact False.elim (hp hiff_a.1)
            · intro hmem
              simp at hmem
          simp [hempty, hp]
      have hsum_le : (∑ y ∈ prodFinset k (preCoord hk A),
            (((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card : ℝ)) ≤
          ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor *
            (countPre f p T I t₀ A v k hk : ℝ) := by
        have h3 : (∑ y ∈ prodFinset k (preCoord hk A), (if prefixOk y then factor else 0)) =
            factor * (countPre f p T I t₀ A v k hk : ℝ) := by
          have hcnt : (∑ y ∈ prodFinset k (preCoord hk A), (if prefixOk y then (1 : ℝ) else 0)) =
              (countPre f p T I t₀ A v k hk : ℝ) := by
            have hcnt' : (∑ y ∈ prodFinset k (preCoord hk A), (if prefixOk y then 1 else 0)) =
                countPre f p T I t₀ A v k hk := by
              dsimp [countPre]
              rw [Finset.card_filter]
            exact_mod_cast hcnt'
          calc
            (∑ y ∈ prodFinset k (preCoord hk A), (if prefixOk y then factor else 0))
                = (∑ y ∈ prodFinset k (preCoord hk A), factor * (if prefixOk y then (1 : ℝ) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  by_cases hp : prefixOk y <;> simp [hp, factor]
            _ = factor * (∑ y ∈ prodFinset k (preCoord hk A), (if prefixOk y then (1 : ℝ) else 0)) := by
                  rw [← Finset.mul_sum]
            _ = factor * (countPre f p T I t₀ A v k hk : ℝ) := by
                  rw [hcnt]
        calc
          (∑ y ∈ prodFinset k (preCoord hk A),
              (((A ⟨k, Nat.lt_of_succ_le hk'⟩).filter (fun a : ℤ => P (extendFin y a))).card : ℝ))
              ≤ (∑ y ∈ prodFinset k (preCoord hk A),
                  ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * (if prefixOk y then factor else 0)) := by
                  exact Finset.sum_le_sum hterm
          _ = ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) *
                (∑ y ∈ prodFinset k (preCoord hk A), (if prefixOk y then factor else 0)) := by
                rw [← Finset.mul_sum]
          _ = ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor * (countPre f p T I t₀ A v k hk : ℝ) := by
                rw [h3]
                ring
      have hmain : (countPre f p T I t₀ A v (k + 1) hk' : ℝ) ≤
          ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor * (countPre f p T I t₀ A v k hk : ℝ) := by
        rw [hLHS]
        exact hsum_le
      have hih := ih hk
      have hprod : (∏ j : Fin k, ((preCoord hk A j).card : ℝ)) *
            ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) =
          ∏ j : Fin (k + 1), ((preCoord hk' A j).card : ℝ) := by
        rw [Fin.prod_univ_castSucc]
        have hprod' : (∏ j : Fin k, ((preCoord hk A j).card : ℝ)) =
            (∏ j : Fin k, ((preCoord hk' A (Fin.castSucc j)).card : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact congrArg (fun s : Finset ℤ => (s.card : ℝ)) (preCoord_castSucc A j).symm
        have hlast : ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) = ((preCoord hk' A (Fin.last k)).card : ℝ) := by
          rw [preCoord_last A]
        rw [hprod', hlast]
      have hgood : (∏ m ∈ goodBelow I G (k + 1), q) =
          (∏ m ∈ goodBelow I G k, q) * factor := by
        have hg := goodBelow_prod (I := I) (G := G) hGI (q := q) (k := k)
        simpa [factor] using hg
      calc
        (countPre f p T I t₀ A v (k + 1) hk' : ℝ)
            ≤ ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor * (countPre f p T I t₀ A v k hk : ℝ) := hmain
        _ ≤ ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor *
              ((∏ m ∈ goodBelow I G k, q) * (∏ j : Fin k, ((preCoord hk A j).card : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hih (mul_nonneg (by exact_mod_cast (Nat.zero_le _)) hfactor0)
        _ = ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * factor * (∏ m ∈ goodBelow I G k, q) *
              (∏ j : Fin k, ((preCoord hk A j).card : ℝ)) := by
              ring
        _ = ((∏ m ∈ goodBelow I G k, q) * factor) *
              (((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ) * (∏ j : Fin k, ((preCoord hk A j).card : ℝ))) := by
              ring
        _ = (∏ m ∈ goodBelow I G (k + 1), q) *
              (∏ j : Fin (k + 1), ((preCoord hk' A j).card : ℝ)) := by
              rw [mul_comm ((A ⟨k, Nat.lt_of_succ_le hk'⟩).card : ℝ)
                (∏ j : Fin k, ((preCoord hk A j).card : ℝ))]
              rw [hprod]
              rw [← hgood]


/-- The refined count bound at the full length `ℓ`: each good level (in `G`)
contributes `q`, every coordinate contributes its cardinality. -/
lemma countPreQ_le_full {ℓ : ℕ} (f : ℤ → ℝ) (p : unitInterval) (T : ℝ) {I G : Finset ℕ}
    (hGI : G ⊆ I) {q : ℝ} (hq : 0 ≤ q) {t₀ : ℤ} {A : Fin ℓ → Finset ℤ} {v : Fin ℓ → ℤ}
    (hstep : ∀ k : ℕ, k ∈ G → ∀ hkℓ : k < ℓ,
      ∀ y ∈ prodFinset k (preCoord (Nat.le_of_lt hkℓ) A),
        (((A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
            levelCond f p T (extendFin y a) (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
          q * ((A ⟨k, hkℓ⟩).card : ℝ)) :
    (countPre f p T I t₀ A v ℓ (Nat.le_refl ℓ) : ℝ) ≤
      (∏ m ∈ goodBelow I G ℓ, q) * (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
  have h := countPreQ_le (f := f) (p := p) (T := T) hGI hq hstep ℓ (Nat.le_refl ℓ)
  have hpre : (∏ j : Fin ℓ, ((preCoord (Nat.le_refl ℓ) A j).card : ℝ)) =
      ∏ j : Fin ℓ, ((A j).card : ℝ) := by
    simp [preCoord]
  simpa [hpre] using h


/-! ## 5. Per-good-level step instantiation (single-interval coordinates) -/

/-- The level-`k` averaged function of an extended tuple is the averaged
function of its `k`-prefix. -/
lemma flvl_extend_eq_avgF {k : ℕ} {f : ℤ → ℝ} {p : unitInterval} (y : Fin k → ℤ) (a : ℤ) :
    flvl f p (extendFin y a) k (Nat.le_of_lt (Nat.lt_succ_self k)) = avgF f p k y := by
  funext t
  dsimp [flvl]
  congr 1
  funext j
  change (extendFin y a) (Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self k)) j) = y j
  have h1 : Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self k)) j = Fin.castSucc j := by
    apply Fin.ext
    simp
  rw [h1]
  exact extendFin_of_lt y a j

/-- The level-`k` descendant point of an extended tuple, with the length-`k+1`
pattern, equals the descendant point of the prefix with the `k`-prefix
pattern. -/
lemma descPoint_extend_eq {ℓ k : ℕ} {hkℓ : k < ℓ} (v : Fin ℓ → ℤ) (y : Fin k → ℤ)
    (a : ℤ) (t₀ : ℤ) :
    descPoint (extendFin y a) (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k
        (Nat.le_of_lt (Nat.lt_succ_self k)) =
      descPoint y (preFun (Nat.le_of_lt hkℓ) v) t₀ k (Nat.le_refl k) := by
  dsimp [descPoint]
  apply congrArg (fun w : ℤ => t₀ - w)
  apply Finset.sum_congr rfl
  intro j hj
  have h1 : Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self k)) j = Fin.castSucc j := by
    apply Fin.ext
    simp
  have h2 : Fin.castLE (Nat.le_refl k) j = j := by
    apply Fin.ext
    simp
  have hx : (extendFin y a) (Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self k)) j) =
      y (Fin.castLE (Nat.le_refl k) j) := by
    rw [h1, h2]
    exact extendFin_of_lt y a j
  have hw : (preFun (Nat.succ_le_of_lt hkℓ) v) (Fin.castLE (Nat.le_of_lt (Nat.lt_succ_self k)) j) =
      (preFun (Nat.le_of_lt hkℓ) v) (Fin.castLE (Nat.le_refl k) j) := by
    rw [h1, h2]
    have hp := preFun_castSucc (v := v) (j := j) (hk' := Nat.succ_le_of_lt hkℓ)
    -- hp : preFun (succ_le_of_lt hkℓ) v (castSucc j) = preFun (le_trans (le_succ k) (succ_le_of_lt hkℓ)) v j
    have hpe : preFun (Nat.le_trans (Nat.le_succ k) (Nat.succ_le_of_lt hkℓ)) v j =
        preFun (Nat.le_of_lt hkℓ) v j := by
      congr 1
    exact hp.trans hpe
  rw [hx, hw, h2]

/-- The level-`k` condition of an extended tuple equals the non-decay of the
`k`-prefix descendant point at the value `a`. -/
lemma levelCond_extend_eq {ℓ k : ℕ} {hkℓ : k < ℓ} {f : ℤ → ℝ} {p : unitInterval}
    {T : ℝ} {v : Fin ℓ → ℤ} {y : Fin k → ℤ} (a : ℤ) {t₀ : ℤ} :
    levelCond f p T (extendFin y a) (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k) ↔
      ¬ decaysAt (avgF f p k y) a T
        (descPoint y (preFun (Nat.le_of_lt hkℓ) v) t₀ k (Nat.le_refl k)) := by
  unfold levelCond
  rw [flvl_extend_eq_avgF]
  apply not_iff_not.mpr
  have hcoord : (extendFin y a) ⟨k, Nat.lt_succ_self k⟩ = a := by
    simp [extendFin]
  have hdesc := descPoint_extend_eq (v := v) (y := y) (a := a) (t₀ := t₀) (hkℓ := hkℓ)
  unfold decaysAt
  rw [hcoord, hdesc]


/-- The per-good-level step for a single-interval coordinate: given the
per-step count bound (with constant `Cq`) at the descendant point of the
prefix, the number of values `a ∈ A⟨k⟩` at which the level-`k` condition
holds is at most `|A⟨k⟩| · 2p·Cq/(εL√(δ₀p))`. -/
theorem perGoodStep_single {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {N : ℕ} (hN1 : 1 ≤ N) {ε L : ℝ} (hε0 : 0 < ε) (hL0 : 0 < L)
    {ℓ k : ℕ} (hkℓ : k < ℓ) {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hfsum : Summable f) (hfmass : norm₁ f ≤ 1) {A : Fin ℓ → Finset ℤ}
    {v : Fin ℓ → ℤ} {y : Fin k → ℤ} (S : Finset (Fin k))
    (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
    (hSbig : ∀ j : Fin k, j ∈ S → (N : ℝ) < |(y j : ℝ)|)
    {c d : ℤ} (hlen : (N : ℤ) ≤ d - c + 1) (hA : A ⟨k, hkℓ⟩ = Finset.Icc c d)
    (Cq : ℝ) {t₀ : ℤ}
    (hbnd : ((((Finset.Icc c d).filter (fun t : ℤ =>
        ¬ decaysAt (avgF f p k y) t (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
          (descPoint y (preFun (Nat.le_of_lt hkℓ) v) t₀ k (Nat.le_refl k)))).card : ℝ) ≤
      ((d : ℝ) - (c : ℝ) + 1) * ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))))) :
    ((((A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
        levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) (extendFin y a)
          (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
      ((A ⟨k, hkℓ⟩).card : ℝ) *
        ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ))))) := by
  let T : ℝ := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)
  let u : ℤ := descPoint y (preFun (Nat.le_of_lt hkℓ) v) t₀ k (Nat.le_refl k)
  have hset : (A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
        levelCond f p T (extendFin y a) (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k)) =
      (Finset.Icc c d).filter (fun a : ℤ => ¬ decaysAt (avgF f p k y) a T u) := by
    rw [hA]
    apply Finset.filter_congr
    intro a ha
    have hlc := levelCond_extend_eq (f := f) (p := p) (T := T) (v := v) (y := y) (a := a)
        (t₀ := t₀) (hkℓ := hkℓ)
    simpa [u] using hlc
  have hlenreal : ((d : ℝ) - (c : ℝ) + 1) = ((A ⟨k, hkℓ⟩).card : ℝ) := by
    rw [hA]
    have hN1i : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN1
    have hpos : 0 ≤ d + 1 - c := by omega
    have hcardz : ((Finset.Icc c d).card : ℤ) = d - c + 1 := by
      rw [Int.card_Icc]
      rw [Int.toNat_of_nonneg hpos]
      ring
    have hL : (d : ℝ) - (c : ℝ) + 1 = ((d - c + 1 : ℤ) : ℝ) := by
      have hz : (d - c + 1 : ℤ) = (d : ℤ) - (c : ℤ) + 1 := by omega
      rw [hz]
      rw [Int.cast_add]
      rw [Int.cast_sub]
      norm_num
    rw [hL]
    exact_mod_cast hcardz.symm
  calc
    ((((A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
        levelCond f p T (extendFin y a) (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k))).card : ℝ))
        = (((Finset.Icc c d).filter (fun a : ℤ => ¬ decaysAt (avgF f p k y) a T u)).card : ℝ) := by
          rw [hset]
    _ ≤ ((d : ℝ) - (c : ℝ) + 1) *
          ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) := by
          simpa [T, u] using hbnd
    _ = ((A ⟨k, hkℓ⟩).card : ℝ) *
          ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) := by
          rw [hlenreal]

/-- The per-good-level step for a two-arm (union of two disjoint intervals)
coordinate: given the two-arm per-step count bound (with constant `Cq`), the
number of level-`k` non-decays in `A⟨k⟩` is at most `|A⟨k⟩|·2p·Cq/(εL√(δ₀p))`. -/
theorem perGoodStep_twoArm {n : ℕ} (hn1 : 1 ≤ n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {N : ℕ} (hN1 : 1 ≤ N) {ε L : ℝ} (hε0 : 0 < ε) (hL0 : 0 < L)
    {ℓ k : ℕ} (hkℓ : k < ℓ) {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hfsum : Summable f) (hfmass : norm₁ f ≤ 1) {A : Fin ℓ → Finset ℤ}
    {v : Fin ℓ → ℤ} {y : Fin k → ℤ} (S : Finset (Fin k))
    (hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ))
    (hSbig : ∀ j : Fin k, j ∈ S → (N : ℝ) < |(y j : ℝ)|)
    {c₁ d₁ c₂ d₂ : ℤ} (hlen₁ : (N : ℤ) ≤ d₁ - c₁ + 1)
    (hlen₂ : (N : ℤ) ≤ d₂ - c₂ + 1)
    (hdisj : Disjoint (Finset.Icc c₁ d₁) (Finset.Icc c₂ d₂))
    (hA : A ⟨k, hkℓ⟩ = Finset.Icc c₁ d₁ ∪ Finset.Icc c₂ d₂)
    (Cq : ℝ) {t₀ : ℤ}
    (hbnd : (((((Finset.Icc c₁ d₁) ∪ (Finset.Icc c₂ d₂)).filter (fun t : ℤ =>
        ¬ decaysAt (avgF f p k y) t (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
          (descPoint y (preFun (Nat.le_of_lt hkℓ) v) t₀ k (Nat.le_refl k)))).card : ℝ) ≤
      (((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1)) *
        ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))))) :
    ((((A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
        levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) (extendFin y a)
          (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
      ((A ⟨k, hkℓ⟩).card : ℝ) *
        ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ))))) := by
  let T : ℝ := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)
  let u : ℤ := descPoint y (preFun (Nat.le_of_lt hkℓ) v) t₀ k (Nat.le_refl k)
  have hset : (A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
        levelCond f p T (extendFin y a) (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k)) =
      ((Finset.Icc c₁ d₁) ∪ (Finset.Icc c₂ d₂)).filter (fun a : ℤ =>
        ¬ decaysAt (avgF f p k y) a T u) := by
    rw [hA]
    apply Finset.filter_congr
    intro a ha
    have hlc := levelCond_extend_eq (f := f) (p := p) (T := T) (v := v) (y := y) (a := a)
        (t₀ := t₀) (hkℓ := hkℓ)
    simpa [u] using hlc
  have hcard_real : ((A ⟨k, hkℓ⟩).card : ℝ) =
      ((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1) := by
    rw [hA]
    have hN1i : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN1
    have hc₁d₁ : c₁ ≤ d₁ := by omega
    have hc₂d₂ : c₂ ≤ d₂ := by omega
    have hcard₁ : ((Finset.Icc c₁ d₁).card : ℝ) = (d₁ : ℝ) - (c₁ : ℝ) + 1 := by
      have hpos : 0 ≤ d₁ + 1 - c₁ := by omega
      have hcardz : ((Finset.Icc c₁ d₁).card : ℤ) = d₁ - c₁ + 1 := by
        rw [Int.card_Icc]
        rw [Int.toNat_of_nonneg hpos]
        ring
      have hL : (d₁ : ℝ) - (c₁ : ℝ) + 1 = ((d₁ - c₁ + 1 : ℤ) : ℝ) := by
        have hz : (d₁ - c₁ + 1 : ℤ) = (d₁ : ℤ) - (c₁ : ℤ) + 1 := by omega
        rw [hz]
        rw [Int.cast_add]
        rw [Int.cast_sub]
        norm_num
      rw [hL]
      exact_mod_cast hcardz
    have hcard₂ : ((Finset.Icc c₂ d₂).card : ℝ) = (d₂ : ℝ) - (c₂ : ℝ) + 1 := by
      have hpos : 0 ≤ d₂ + 1 - c₂ := by omega
      have hcardz : ((Finset.Icc c₂ d₂).card : ℤ) = d₂ - c₂ + 1 := by
        rw [Int.card_Icc]
        rw [Int.toNat_of_nonneg hpos]
        ring
      have hL : (d₂ : ℝ) - (c₂ : ℝ) + 1 = ((d₂ - c₂ + 1 : ℤ) : ℝ) := by
        have hz : (d₂ - c₂ + 1 : ℤ) = (d₂ : ℤ) - (c₂ : ℤ) + 1 := by omega
        rw [hz]
        rw [Int.cast_add]
        rw [Int.cast_sub]
        norm_num
      rw [hL]
      exact_mod_cast hcardz
    have hunion : ((Finset.Icc c₁ d₁) ∪ (Finset.Icc c₂ d₂)).card =
        (Finset.Icc c₁ d₁).card + (Finset.Icc c₂ d₂).card := by
      exact Finset.card_union_of_disjoint hdisj
    rw [hunion]
    rw [Nat.cast_add]
    rw [hcard₁, hcard₂]
  calc
    ((((A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
        levelCond f p T (extendFin y a) (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k))).card : ℝ))
        = ((((Finset.Icc c₁ d₁) ∪ (Finset.Icc c₂ d₂)).filter (fun a : ℤ =>
            ¬ decaysAt (avgF f p k y) a T u)).card : ℝ) := by
          rw [hset]
    _ ≤ (((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1)) *
          ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) := by
          simpa [T, u] using hbnd
    _ = ((A ⟨k, hkℓ⟩).card : ℝ) *
          ((2 * (p : ℝ) * Cq) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) := by
          rw [hcard_real]


/-! ## 6. The countPreQ_le_full instantiation (per-good-level steps from the
admissible data) -/

/-- The per-level `hstep` bound for every good level, derived from the
admissible coordinate structure and the scale-free per-step bounds. -/
theorem rough_product_bound {n : ℕ} (hn1 : 1 ≤ n) {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀)
    (hδle : δ₀ ≤ δ) (hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ))
    {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε L : ℝ} (hε0 : 0 < ε) (hL0 : 0 < L) {N : ℕ} (hN1 : 1 ≤ N)
    {ℓ : ℕ} {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t) (hfsum : Summable f)
    (hfmass : norm₁ f ≤ 1) {A : Fin ℓ → Finset ℤ} (hAdm : Admissible N n ℓ δ A)
    {v : Fin ℓ → ℤ} (t₀ : ℤ) {I G : Finset ℕ} (hGI : G ⊆ I)
    (hIlt : ∀ m ∈ I, m < ℓ)
    (hG : ∀ m : ℕ, m ∈ G ↔ m ∈ I ∧ δ₀ * (n : ℝ) ≤ m)
    (Cq₁ : ℝ) (hCq₁pos : 0 < Cq₁) (Cq₂ : ℝ) (hCq₂pos : 0 < Cq₂)
    (hPer₁ : perStepProp Cq₁) (hPer₂ : twoArmProp Cq₂) :
    (countPre f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) I t₀ A v ℓ (Nat.le_refl ℓ) : ℝ) ≤
        (∏ m ∈ G, ((2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ))))) *
          (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
  classical
  let q : ℝ := (2 * (p : ℝ) * (Cq₁ + Cq₂)) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hdenpos : 0 < ε * L * Real.sqrt (δ₀ * (p : ℝ)) := by positivity
  -- the hstep hypothesis of countPreQ_le_full
  have hstep : ∀ (k : ℕ), k ∈ G → ∀ hkℓ : k < ℓ,
      ∀ y ∈ prodFinset k (preCoord (Nat.le_of_lt hkℓ) A),
        (((A ⟨k, hkℓ⟩).filter (fun a : ℤ =>
            levelCond f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) (extendFin y a)
              (preFun (Nat.succ_le_of_lt hkℓ) v) t₀ k (Nat.lt_succ_self k))).card : ℝ) ≤
          q * ((A ⟨k, hkℓ⟩).card : ℝ) := by
    intro k hkG hkℓ y hy
    let S : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j : Fin k => smallIndex n δ (j.val))
    have hkg0 : δ₀ * (n : ℝ) ≤ k := ((hG k).1 hkG).2
    have hScard : δ₀ * (n : ℝ) ≤ (S.card : ℝ) := by
      dsimp [S]
      exact bigCoordSet_card hδ₀ hδle hkg0 hslack
    have hSbig : ∀ j : Fin k, j ∈ S → (N : ℝ) < |(y j : ℝ)| := by
      intro j hj
      have hsmall : smallIndex n δ (j.val) := (Finset.mem_filter.mp hj).2
      have hmem : y j ∈ (preCoord (Nat.le_of_lt hkℓ) A) j := (mem_prodFinset _ y).1 hy j
      have hyA : y j ∈ A (Fin.castLE (Nat.le_of_lt hkℓ) j) := by
        dsimp [preCoord] at hmem
        exact hmem
      exact big_of_small hAdm (hi := by simpa using hsmall) hyA
    have hdenpos : 0 < ε * L * Real.sqrt (δ₀ * (p : ℝ)) := by positivity
    have hq₁ : ((2 * (p : ℝ) * Cq₁) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ≤ q := by
      dsimp [q]
      have hnum : (2 * (p : ℝ) * Cq₁) ≤ (2 * (p : ℝ) * (Cq₁ + Cq₂)) := by
        have hm : Cq₁ ≤ Cq₁ + Cq₂ := by linarith [hCq₂pos.le]
        exact mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * (p : ℝ))
      exact (div_le_div_of_nonneg_right hnum hdenpos.le)
    have hq₂ : ((2 * (p : ℝ) * Cq₂) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ≤ q := by
      dsimp [q]
      have hnum : (2 * (p : ℝ) * Cq₂) ≤ (2 * (p : ℝ) * (Cq₁ + Cq₂)) := by
        have hm : Cq₂ ≤ Cq₁ + Cq₂ := by linarith [hCq₁pos.le]
        exact mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * (p : ℝ))
      exact (div_le_div_of_nonneg_right hnum hdenpos.le)
    have hlen_nonneg : ∀ c d : ℤ, (N : ℤ) ≤ d - c + 1 →
        0 ≤ ((d : ℝ) - (c : ℝ) + 1) := by
      intro c d hlen
      have hz : (0 : ℤ) ≤ d - c + 1 := by omega
      exact_mod_cast hz
    by_cases hsmallK : smallIndex n δ k
    · rcases (hAdm.1 ⟨k, hkℓ⟩ hsmallK) with ⟨c₁, d₁, c₂, d₂, hcov, hlen₁, hlen₂, hdisj, hbig⟩
      let u : ℤ := descPoint y (preFun (Nat.le_of_lt hkℓ) v) t₀ k (Nat.le_refl k)
      have hbnd₀ := hPer₂ hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass y S hScard hSbig
          c₁ d₁ c₂ d₂ u hlen₁ hlen₂ hε0 hL0
      have hqstep : (((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1)) *
            ((2 * (p : ℝ) * Cq₂) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ≤
          (((d₁ : ℝ) - (c₁ : ℝ) + 1) + ((d₂ : ℝ) - (c₂ : ℝ) + 1)) * q := by
        exact mul_le_mul_of_nonneg_left hq₂
          (add_nonneg (hlen_nonneg c₁ d₁ hlen₁) (hlen_nonneg c₂ d₂ hlen₂))
      have hps := perGoodStep_twoArm hn1 hδ₀ hp₀ hp₁ hN1 hε0 hL0 hkℓ hfpos hfsum hfmass
          (y := y) S hScard hSbig hlen₁ hlen₂ hdisj hcov (Cq := Cq₁ + Cq₂) (t₀ := t₀)
          (by exact le_trans hbnd₀ hqstep)
      simpa [q, mul_comm] using hps
    · rcases single_interval_of_large hAdm (i := ⟨k, hkℓ⟩) hsmallK with ⟨c, d, hcov, hlen⟩
      let u : ℤ := descPoint y (preFun (Nat.le_of_lt hkℓ) v) t₀ k (Nat.le_refl k)
      have hbnd₀ := hPer₁ hn1 hδ₀ hp₀ hp₁ hN1 hfpos hfsum hfmass y S hScard hSbig c d u hlen hε0 hL0
      have hqstep : ((d : ℝ) - (c : ℝ) + 1) *
            ((2 * (p : ℝ) * Cq₁) / (ε * L * Real.sqrt (δ₀ * (p : ℝ)))) ≤
          ((d : ℝ) - (c : ℝ) + 1) * q := by
        exact mul_le_mul_of_nonneg_left hq₁ (hlen_nonneg c d hlen)
      have hps := perGoodStep_single hn1 hδ₀ hp₀ hp₁ hN1 hε0 hL0 hkℓ hfpos hfsum hfmass
          (y := y) S hScard hSbig hlen hcov (Cq := Cq₁ + Cq₂) (t₀ := t₀)
          (by exact le_trans hbnd₀ hqstep)
      simpa [q, mul_comm] using hps
  -- apply the refined count bound
  have hcount := countPreQ_le_full (f := f) (p := p) (T := roughT ε L (N : ℝ) (n : ℝ) (p : ℝ))
      hGI hq hstep
  have hgoodset : goodBelow I G ℓ = G := by
    apply Finset.ext
    intro m
    rw [mem_goodBelow]
    constructor
    · intro h
      rcases h with ⟨hmI, hmlt, hmG⟩
      exact hmG
    · intro hmG
      have hmI : m ∈ I := hGI hmG
      have hmlt : m < ℓ := hIlt m hmI
      exact ⟨hmI, hmlt, hmG⟩
  -- hcount : countPre ≤ (∏ goodBelow I G ℓ q)·∏|A|
  -- but hcount's q-product and card product: match targets: ∏ over goodBelow with q = ∏ over G with q; and (A j).card product ✓
  have htarget : (countPre f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) I t₀ A v ℓ (Nat.le_refl ℓ) : ℝ) ≤
      (∏ m ∈ G, q) * (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
    -- hcount's RHS: (∏ m ∈ goodBelow I G ℓ, q)·(∏ j, ((preCoord (Nat.le_refl ℓ) A j).card : ℝ))
    have hpre : (∏ j : Fin ℓ, ((preCoord (Nat.le_refl ℓ) A j).card : ℝ)) =
        ∏ j : Fin ℓ, ((A j).card : ℝ) := by
      simp [preCoord]
    calc
      (countPre f p (roughT ε L (N : ℝ) (n : ℝ) (p : ℝ)) I t₀ A v ℓ (Nat.le_refl ℓ) : ℝ)
          ≤ (∏ m ∈ goodBelow I G ℓ, q) * (∏ j : Fin ℓ, ((preCoord (Nat.le_refl ℓ) A j).card : ℝ)) := hcount
      _ = (∏ m ∈ G, q) * (∏ j : Fin ℓ, ((preCoord (Nat.le_refl ℓ) A j).card : ℝ)) := by
          rw [hgoodset]
      _ = (∏ m ∈ G, q) * (∏ j : Fin ℓ, ((A j).card : ℝ)) := by
          rw [hpre]
  simpa [q] using htarget


/-- The level condition is unchanged when the pattern function is replaced by
a pointwise-equal one. -/
lemma levelCond_pattern_congr {K : ℕ} {f : ℤ → ℝ} {p : unitInterval} {T : ℝ}
    {x : Fin K → ℤ} {w₁ w₂ : Fin K → ℤ} (hw : w₁ = w₂) {t₀ : ℤ} {m : ℕ}
    {hm : m < K} :
    levelCond f p T x w₁ t₀ m hm ↔ levelCond f p T x w₂ t₀ m hm := by
  rw [hw]

end Submission.RoughProduct
