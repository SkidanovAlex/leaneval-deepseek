/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2) of the
formalisation of Jaikin-Zapirain--Linton, "On the coherence of one-relator groups
and their group algebras".
-/
import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# Splitting a relator around a generator occurring exactly once

If the reduced word of `u : FreeGroup α` contains the letter `(x, b)` exactly once and the letter
`(x, !b)` not at all, then that word splits as `L₁ ++ [(x, b)] ++ L₂` with no letter of `L₁` or `L₂`
carrying the generator `x`, and consequently

`u = FreeGroup.mk L₁ * (FreeGroup.of x) ^ ε * FreeGroup.mk L₂`,  `ε = ±1`,

with `ε = 1` for `b = true` and `ε = -1` for `b = false`.

The additional hypothesis `2 ≤ relatorNorm u` is exactly what guarantees that the complement
`{a : α // a ≠ x}` is nonempty (otherwise `u` would be a single letter of norm `1`), which is why
the statement can produce an element `y ≠ x`.  Note that `y` itself is otherwise unused: the
content of the lemma is the decomposition, the sign `ε` and the "no other `x`" condition.
-/

namespace Work.OROneRel

universe u

-- the existential binder `y` of the target statement is deliberately unused (it only records that
-- `α \ {x}` is nonempty), so silence the corresponding linter warning
set_option linter.unusedVariables false

/-- `FreeGroup.toWord` does not depend on the chosen `DecidableEq` instance: any two instances are
equal by `Subsingleton (DecidableEq α)`.  (This bridges the classical instance used inside the
noncomputable definition of `relatorNorm` with an arbitrary explicit one.) -/
private theorem toWord_decEq_congr {α : Type u} (i j : DecidableEq α) (w : FreeGroup α) :
    @FreeGroup.toWord α i w = @FreeGroup.toWord α j w :=
  congrArg (fun k => @FreeGroup.toWord α k w) (Subsingleton.elim i j)

/-- `relatorNorm` is the length of the reduced word, computed with the classical decidability
instance (which is the one used inside its definition). -/
private theorem relatorNorm_eq_toWord_length {α : Type u} (w : FreeGroup α) :
    relatorNorm w = (@FreeGroup.toWord α (Classical.decEq α) w).length := rfl

/-- A list with exactly one occurrence of `a` splits as `L₁ ++ [a] ++ L₂` with `a` absent from both
`L₁` and `L₂`. -/
private theorem exists_split_of_count_eq_one {γ : Type*} [BEq γ] [LawfulBEq γ] {a : γ}
    {l : List γ} (h : l.count a = 1) :
    ∃ L₁ L₂ : List γ, l = L₁ ++ [a] ++ L₂ ∧ a ∉ L₁ ∧ a ∉ L₂ := by
  revert h
  induction l with
  | nil => intro h; simp at h
  | cons c t ih =>
    intro h
    by_cases hca : c = a
    · -- the head is the unique occurrence: nothing is lost from the tail
      have h0 : t.count a = 0 := by
        rw [hca, List.count_cons_self] at h
        omega
      have hmem : a ∉ t := List.count_eq_zero.mp h0
      refine ⟨[], t, ?_, by simp, hmem⟩
      simp [hca]
    · -- the head is not the occurrence: recurse into the tail
      rw [List.count_cons_of_ne hca] at h
      obtain ⟨L₁, L₂, hsplit, hL₁, hL₂⟩ := ih h
      refine ⟨c :: L₁, L₂, ?_, ?_, hL₂⟩
      · rw [hsplit]; simp
      · intro hmem
        rcases List.mem_cons.mp hmem with h1 | h1
        · exact hca h1.symm
        · exact hL₁ h1

theorem exists_letter_once_data {α : Type u} [DecidableEq α] (u : FreeGroup α) (x : α) (b : Bool)
    (hcount : (FreeGroup.toWord u).count (x, b) = 1 ∧
      (FreeGroup.toWord u).count (x, !b) = 0)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u) :
    ∃ (L₁ L₂ : List (α × Bool)) (ε : ℤ) (y : {a : α // a ≠ x}),
      FreeGroup.toWord u = L₁ ++ [(x, b)] ++ L₂ ∧
      (∀ p ∈ L₁ ++ L₂, p.1 ≠ x) ∧
      (FreeGroup.of x) ^ ε = FreeGroup.mk [(x, b)] ∧
      u = FreeGroup.mk L₁ * (FreeGroup.of x) ^ ε * FreeGroup.mk L₂ ∧
      (ε = 1 ∨ ε = -1) := by
  obtain ⟨hc1, hc0⟩ := hcount
  -- split the reduced word at its unique occurrence of `(x, b)`
  obtain ⟨L₁, L₂, hsplit, hL1, hL2⟩ := exists_split_of_count_eq_one hc1
  have hnotmem : (x, !b) ∉ FreeGroup.toWord u := List.count_eq_zero.mp hc0
  -- no letter outside the distinguished occurrence involves the generator `x`
  have hx : ∀ p ∈ L₁ ++ L₂, p.1 ≠ x := by
    intro p hp hpx
    have hpw : p ∈ FreeGroup.toWord u := by
      rw [hsplit]
      rcases List.mem_append.mp hp with h | h
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))
      · exact List.mem_append.mpr (Or.inr h)
    have hpneb : p ≠ (x, b) := by
      rcases List.mem_append.mp hp with h | h
      · intro he; exact hL1 (he ▸ h)
      · intro he; exact hL2 (he ▸ h)
    have hpne0 : p ≠ (x, !b) := fun he => hnotmem (he ▸ hpw)
    -- a pair with first coordinate `x` is `(x, b)` or `(x, !b)`
    have hcases : p.2 = b ∨ p.2 = !b := by
      cases b <;> cases p.2 <;> simp
    rcases hcases with hc | hc
    · exact hpneb (Prod.ext hpx hc)
    · exact hpne0 (Prod.ext hpx hc)
  -- `2 ≤ relatorNorm u` makes `L₁ ++ L₂` nonempty, hence produces a generator `≠ x`
  have h2 : 2 ≤ (FreeGroup.toWord u).length := by
    have h2' : 2 ≤ (@FreeGroup.toWord α (Classical.decEq α) u).length := by
      rw [← relatorNorm_eq_toWord_length]; exact hn
    have hw : (@FreeGroup.toWord α (Classical.decEq α) u) = FreeGroup.toWord u :=
      toWord_decEq_congr _ _ u
    rwa [← hw]
  have hpos : 1 ≤ L₁.length + L₂.length := by
    rw [hsplit] at h2
    simp only [List.length_append, List.length_singleton] at h2
    omega
  have hne : L₁ ++ L₂ ≠ [] := by
    intro h
    have : (L₁ ++ L₂).length = 0 := by simp [h]
    rw [List.length_append] at this
    omega
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil (L₁ ++ L₂) hne
  have hpx := hx p hp
  -- the one-letter word `(x, b)` is `(of x) ^ (±1)`
  have hsign : (FreeGroup.of x) ^ (if b then (1 : ℤ) else -1) = FreeGroup.mk [(x, b)] := by
    cases b
    · show (FreeGroup.of x) ^ (-1 : ℤ) = FreeGroup.mk [(x, false)]
      rw [zpow_neg_one]; rfl
    · show (FreeGroup.of x) ^ (1 : ℤ) = FreeGroup.mk [(x, true)]
      rw [zpow_one]; rfl
  have heps : (if b then (1 : ℤ) else -1) = 1 ∨ (if b then (1 : ℤ) else -1) = -1 := by
    cases b <;> simp
  -- `u` is the product of the three pieces
  have hu : u = FreeGroup.mk L₁ * (FreeGroup.of x) ^ (if b then (1 : ℤ) else -1) *
      FreeGroup.mk L₂ := by
    have hmk : FreeGroup.mk (L₁ ++ [(x, b)] ++ L₂) =
        FreeGroup.mk L₁ * FreeGroup.mk [(x, b)] * FreeGroup.mk L₂ := by
      rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    calc u = FreeGroup.mk (FreeGroup.toWord u) := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (L₁ ++ [(x, b)] ++ L₂) := by rw [hsplit]
      _ = FreeGroup.mk L₁ * FreeGroup.mk [(x, b)] * FreeGroup.mk L₂ := hmk
      _ = FreeGroup.mk L₁ * (FreeGroup.of x) ^ (if b then (1 : ℤ) else -1) *
            FreeGroup.mk L₂ := by rw [← hsign]
  exact ⟨L₁, L₂, (if b then (1 : ℤ) else -1), ⟨p.1, hpx⟩, hsplit, hx, hsign, hu, heps⟩

end Work.OROneRel
