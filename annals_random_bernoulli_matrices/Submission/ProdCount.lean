import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 3: product-count infrastructure (recursive tuple Finsets)

Proposition `p: rough decay` is proved by counting realizations of the random
vector `X ∈ A₁ × … × A_ℓ`.  This module provides the finite set of such
tuples as a recursively built `Finset (Fin ℓ → ℤ)` (adding coordinates at the
top, `Fin.last`), with

- the three `extend`/`restrict` round-trip identities,
- membership: `x ∈ prodFinset ℓ A ↔ ∀ j, x j ∈ A j`,
- cardinality: `(prodFinset ℓ A).card = ∏ j, (A j).card`.
-/

open scoped BigOperators

namespace Submission.ProdCount

attribute [local instance] Classical.propDecidable

/-- Restrict a tuple of length `ℓ+1` to its first `ℓ` coordinates. -/
def restrict {ℓ : ℕ} (x : Fin (ℓ + 1) → ℤ) : Fin ℓ → ℤ :=
  fun j => x (Fin.castSucc j)

/-- Extend a tuple of length `ℓ` by one value at the top coordinate. -/
def extendFin {ℓ : ℕ} (y : Fin ℓ → ℤ) (a : ℤ) : Fin (ℓ + 1) → ℤ :=
  fun j => if h : j.val < ℓ then y ⟨j.val, h⟩ else a

/-- The value of an extended tuple at the new top coordinate. -/
lemma extendFin_last {ℓ : ℕ} (y : Fin ℓ → ℤ) (a : ℤ) :
    extendFin y a (Fin.last ℓ) = a := by
  simp [extendFin]

/-- The value of an extended tuple on the first `ℓ` coordinates agrees with
the base tuple. -/
lemma extendFin_of_lt {ℓ : ℕ} (y : Fin ℓ → ℤ) (a : ℤ) (j : Fin ℓ) :
    extendFin y a (Fin.castSucc j) = y j := by
  simp [extendFin]

/-- Restricting an extended tuple gives back the base tuple. -/
lemma restrict_extend {ℓ : ℕ} (y : Fin ℓ → ℤ) (a : ℤ) :
    restrict (extendFin y a) = y := by
  funext j
  exact extendFin_of_lt y a j

/-- A tuple equals the extension of its own restriction by its top value. -/
lemma extend_restrict {ℓ : ℕ} (x : Fin (ℓ + 1) → ℤ) :
    extendFin (restrict x) (x (Fin.last ℓ)) = x := by
  funext j
  by_cases hj : j.val < ℓ
  · have hx : j = Fin.castSucc ⟨j.val, hj⟩ := by
      apply Fin.ext
      simp
    rw [hx]
    simp [extendFin, restrict, hj]
  · have hval : j.val = ℓ := by
      have hlt : j.val < ℓ + 1 := j.isLt
      omega
    have hjlast : j = Fin.last ℓ := by
      apply Fin.ext
      simp [hval]
    rw [hjlast]
    simp [extendFin]

/-- The recursive finite set of tuples `x : Fin ℓ → ℤ` with `x j ∈ A j`. -/
def prodFinset : (ℓ : ℕ) → (Fin ℓ → Finset ℤ) → Finset (Fin ℓ → ℤ)
  | 0, _ => {fun _ : Fin 0 => (0 : ℤ)}
  | ℓ + 1, A =>
      (prodFinset ℓ (fun j : Fin ℓ => A (Fin.castSucc j))).biUnion
        (fun y : Fin ℓ → ℤ => (A (Fin.last ℓ)).image (fun a : ℤ => extendFin y a))

/-- Membership in a length-`ℓ+1` product set (recursive unfolding). -/
lemma mem_prodFinset_succ {ℓ : ℕ} (A : Fin (ℓ + 1) → Finset ℤ) (x : Fin (ℓ + 1) → ℤ) :
    x ∈ prodFinset (ℓ + 1) A ↔
      restrict x ∈ prodFinset ℓ (fun j : Fin ℓ => A (Fin.castSucc j)) ∧
        x (Fin.last ℓ) ∈ A (Fin.last ℓ) := by
  classical
  dsimp [prodFinset]
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro h
    rcases h with ⟨y, hy, a, ha, hx⟩
    constructor
    · rw [← hx]
      rw [restrict_extend]
      exact hy
    · rw [← hx]
      rw [extendFin_last]
      exact ha
  · intro h
    rcases h with ⟨hy, ha⟩
    refine ⟨restrict x, hy, x (Fin.last ℓ), ha, ?_⟩
    exact extend_restrict x

/-- Membership: `x ∈ prodFinset ℓ A` iff every coordinate belongs. -/
lemma mem_prodFinset {ℓ : ℕ} (A : Fin ℓ → Finset ℤ) (x : Fin ℓ → ℤ) :
    x ∈ prodFinset ℓ A ↔ ∀ j : Fin ℓ, x j ∈ A j := by
  classical
  induction ℓ with
  | zero =>
      constructor
      · intro h j
        exact Fin.elim0 j
      · intro h
        rw [show prodFinset 0 A = ({fun _ : Fin 0 => (0 : ℤ)} : Finset (Fin 0 → ℤ)) by rfl]
        rw [Finset.mem_singleton]
        funext j
        exact Fin.elim0 j
  | succ ℓ ih =>
      constructor
      · intro hx j
        have hsplit := (mem_prodFinset_succ A x).1 hx
        by_cases hj : j = Fin.last ℓ
        · subst j
          exact hsplit.2
        · have hlt : j.val < ℓ := by
            have hlt' : j.val < ℓ + 1 := j.isLt
            have hne : j.val ≠ ℓ := by
              intro hv
              apply hj
              apply Fin.ext
              exact hv
            omega
          let j' : Fin ℓ := ⟨j.val, hlt⟩
          have hjcast : j = Fin.castSucc j' := by
            apply Fin.ext
            simp [j']
          have hy := (ih (fun k : Fin ℓ => A (Fin.castSucc k)) (restrict x)).1 hsplit.1
          have hval : x (Fin.castSucc j') ∈ A (Fin.castSucc j') := hy j'
          rwa [hjcast]
      · intro hx
        apply (mem_prodFinset_succ A x).2
        constructor
        · exact (ih (fun k : Fin ℓ => A (Fin.castSucc k)) (restrict x)).2
            (by intro j; exact hx (Fin.castSucc j))
        · exact hx (Fin.last ℓ)


/-! ## 2. Cardinality -/

/-- The image `Y → extendFin y` has the cardinality of `Y`. -/
lemma card_image_extend {ℓ : ℕ} (Y : Finset ℤ) (y : Fin ℓ → ℤ) :
    (Y.image (fun a : ℤ => extendFin y a)).card = Y.card := by
  apply Finset.card_image_of_injective (s := Y) (f := fun a : ℤ => extendFin y a)
  intro a₁ a₂ h
  have hlast := congrFun h (Fin.last ℓ)
  simpa [extendFin] using hlast

/-- Distinct base tuples give disjoint extended images. -/
lemma disjoint_extend_image {ℓ : ℕ} (Y : Finset ℤ) {y₁ y₂ : Fin ℓ → ℤ} (hne : y₁ ≠ y₂) :
    Disjoint (Y.image (fun a : ℤ => extendFin y₁ a))
      (Y.image (fun a : ℤ => extendFin y₂ a)) := by
  rw [Finset.disjoint_left]
  intro z hzs hzt
  rcases Finset.mem_image.mp hzs with ⟨a₁, ha₁, hz₁⟩
  rcases Finset.mem_image.mp hzt with ⟨a₂, ha₂, hz₂⟩
  apply hne
  have hy₁ : restrict z = y₁ := by
    rw [← hz₁]
    exact restrict_extend y₁ a₁
  have hy₂ : restrict z = y₂ := by
    rw [← hz₂]
    exact restrict_extend y₂ a₂
  calc
    y₁ = restrict z := hy₁.symm
    _ = y₂ := hy₂

/-- Cardinality of the recursive product set:
`(prodFinset ℓ A).card = ∏ j, (A j).card`. -/
lemma prodFinset_card {ℓ : ℕ} (A : Fin ℓ → Finset ℤ) :
    (prodFinset ℓ A).card = ∏ j : Fin ℓ, (A j).card := by
  classical
  induction ℓ with
  | zero =>
      simp [prodFinset]
  | succ ℓ ih =>
      let A' : Fin ℓ → Finset ℤ := fun j => A (Fin.castSucc j)
      have hmain : (prodFinset (ℓ + 1) A).card =
          (A (Fin.last ℓ)).card * (prodFinset ℓ A').card := by
        dsimp [prodFinset, A']
        let s : Finset (Fin ℓ → ℤ) := prodFinset ℓ (fun j : Fin ℓ => A (Fin.castSucc j))
        have hdisj : (↑s : Set (Fin ℓ → ℤ)).PairwiseDisjoint
            (fun y : Fin ℓ → ℤ => (A (Fin.last ℓ)).image (fun a : ℤ => extendFin y a)) := by
          intro y₁ hy₁ y₂ hy₂ hne
          exact disjoint_extend_image (Y := A (Fin.last ℓ)) (y₁ := y₁) (y₂ := y₂) hne
        have hb := Finset.card_biUnion hdisj
        calc
          (s.biUnion (fun y : Fin ℓ → ℤ => (A (Fin.last ℓ)).image (fun a : ℤ => extendFin y a))).card
              = (∑ y ∈ s, ((A (Fin.last ℓ)).image (fun a : ℤ => extendFin y a)).card) := hb
          _ = (∑ y ∈ s, (A (Fin.last ℓ)).card) := by
                apply Finset.sum_congr rfl
                intro y hy
                exact card_image_extend (Y := A (Fin.last ℓ)) (y := y)
          _ = (A (Fin.last ℓ)).card * s.card := by
                rw [Finset.sum_const]
                calc
                  s.card • (A (Fin.last ℓ)).card = s.card * (A (Fin.last ℓ)).card := by simp
                  _ = (A (Fin.last ℓ)).card * s.card := Nat.mul_comm _ _
      calc
        (prodFinset (ℓ + 1) A).card = (A (Fin.last ℓ)).card * (prodFinset ℓ A').card := hmain
        _ = (A (Fin.last ℓ)).card * (∏ j : Fin ℓ, (A' j).card) := by
              rw [ih A']
        _ = ∏ j : Fin (ℓ + 1), (A j).card := by
              rw [Fin.prod_univ_castSucc]
              dsimp [A']
              rw [mul_comm]

end Submission.ProdCount
