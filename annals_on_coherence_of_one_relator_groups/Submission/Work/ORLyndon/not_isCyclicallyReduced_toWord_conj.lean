import Mathlib

namespace Work.ORLyndon

namespace ORLyndonConjAux

open FreeGroup

/-- A word of the shape `c ++ M ++ invRev c` with `c ≠ []` is never cyclically reduced: its first
letter is the head of `c` and its last letter is the inverse of that same head, so the two cancel.

(This is the copy, in this directory, of `not_isCyclicallyReduced_append_invRev'`,
made so that this module does not depend on the import chain leading to
`Work.OROneRel.exists_common_power`; that chain currently clashes with the duplicate declaration
`Work.OROneRel.mk_flatten_replicate` in `Submission/Work/OROneRel/magnus_step_root.lean`, which would
make the umbrella `Submission.Work.ORLyndon.All` unbuildable.) -/
theorem not_isCyclicallyReduced_append_invRev' {α : Type*} {M c : List (α × Bool)} (hc : c ≠ []) :
    ¬ FreeGroup.IsCyclicallyReduced (c ++ M ++ FreeGroup.invRev c) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hc
  intro hcyc
  have hhead : ((x :: xs) ++ M ++ FreeGroup.invRev (x :: xs)).head? = some x := by simp
  have hlast : ((x :: xs) ++ M ++ FreeGroup.invRev (x :: xs)).getLast? = some (x.1, !x.2) := by
    have hq : FreeGroup.invRev [x] = [(x.1, !x.2)] := by simp [FreeGroup.invRev]
    rw [FreeGroup.invRev_cons, hq]
    have hassoc : (x :: xs) ++ M ++ (FreeGroup.invRev xs ++ [(x.1, !x.2)])
        = ((x :: xs) ++ M ++ FreeGroup.invRev xs) ++ [(x.1, !x.2)] := by
      simp only [List.append_assoc]
    rw [hassoc, List.getLast?_concat]
  have hb : x ∈ ((x :: xs) ++ M ++ FreeGroup.invRev (x :: xs)).head? := by
    rw [hhead]; exact Option.mem_def.mpr rfl
  have ha : (x.1, !x.2) ∈ ((x :: xs) ++ M ++ FreeGroup.invRev (x :: xs)).getLast? := by
    rw [hlast]; exact Option.mem_def.mpr rfl
  have hcancel := hcyc.2 _ ha _ hb rfl
  rcases x with ⟨y, b⟩
  cases b <;> simp at hcancel


/-- `invRev` of a constant block of length `n` is the constant block with the letter flipped. -/
lemma invRev_replicate {α : Type*} (a : α) (b : Bool) (n : ℕ) :
    FreeGroup.invRev (List.replicate n (a, b)) = List.replicate n (a, !b) := by
  simp [FreeGroup.invRev, List.map_replicate]

/-- The reduced word of a nonnegative power of a generator. -/
lemma toWord_zpow_of_nonneg {α : Type*} [DecidableEq α] (a : α) (n : ℕ) :
    (FreeGroup.of a ^ (n : ℤ)).toWord = List.replicate n (a, true) := by
  rw [zpow_natCast, FreeGroup.toWord_of_pow]

/-- The reduced word of a nonpositive power of a generator. -/
lemma toWord_zpow_of_neg {α : Type*} [DecidableEq α] (a : α) (n : ℕ) :
    (FreeGroup.of a ^ (-(n : ℤ))).toWord = List.replicate n (a, false) := by
  rw [zpow_neg, FreeGroup.toWord_inv, zpow_natCast, FreeGroup.toWord_of_pow]
  simp [FreeGroup.invRev, List.map_replicate]

/-- The reduced word of an arbitrary integral power of a generator is a constant block. -/
theorem toWord_of_zpow {α : Type*} [DecidableEq α] (a : α) (k : ℤ) :
    (FreeGroup.of a ^ k).toWord = List.replicate k.natAbs (a, decide (0 < k)) := by
  rcases Int.eq_nat_or_neg k with ⟨n, h | h⟩
  · subst h
    rcases n with _ | m
    · simp
    · rw [toWord_zpow_of_nonneg]
      simp
      omega
  · subst h
    rcases n with _ | m
    · simp
    · rw [toWord_zpow_of_neg]
      simp
      omega

private lemma mem_getLast?_replicate {γ : Type*} {x : γ} {n : ℕ} {y : γ}
    (h : y ∈ (List.replicate n x).getLast?) : y = x := by
  rw [List.getLast?_replicate] at h
  split at h
  · simp at h
  · simpa [eq_comm] using h

private lemma mem_head?_replicate {γ : Type*} {x : γ} {n : ℕ} {y : γ}
    (h : y ∈ (List.replicate n x).head?) : y = x := by
  rw [List.head?_replicate] at h
  split at h
  · simp at h
  · simpa [eq_comm] using h

/-- A word of the shape `c ++ d ++ invRev c` where `c` is a constant block over one letter and
`d` is a nonempty constant block over a different letter is reduced. -/
lemma isReduced_replicate_append_replicate_append_invRev
    {α : Type*} {a₁ a₂ : α} (h : a₁ ≠ a₂) (b d : Bool) {m n : ℕ} (hn : n ≠ 0) :
    FreeGroup.IsReduced (List.replicate m (a₁, b) ++ List.replicate n (a₂, d)
      ++ FreeGroup.invRev (List.replicate m (a₁, b))) := by
  have hInv : FreeGroup.invRev (List.replicate m (a₁, b)) = List.replicate m (a₁, !b) :=
    invRev_replicate a₁ b m
  have hB : List.replicate n (a₂, d) ≠ [] := by
    intro hh
    exact hn (by simpa using congrArg List.length hh)
  rw [hInv]
  unfold FreeGroup.IsReduced
  refine List.IsChain.append ?_ ?_ ?_
  · refine List.IsChain.append ?_ ?_ ?_
    · exact List.isChain_replicate_of_rel m (by intro _; rfl)
    · exact List.isChain_replicate_of_rel n (by intro _; rfl)
    · rintro x hx y hy hxy
      rw [mem_getLast?_replicate hx, mem_head?_replicate hy] at hxy
      exact absurd hxy h
  · exact List.isChain_replicate_of_rel m (by intro _; rfl)
  · rintro x hx y hy hxy
    rw [List.getLast?_append_of_ne_nil (List.replicate m (a₁, b)) hB] at hx
    rw [mem_getLast?_replicate hx, mem_head?_replicate hy] at hxy
    exact absurd hxy.symm h

end ORLyndonConjAux

open ORLyndonConjAux

/-- A conjugate `t ^ k * x ^ s * t ^ (-k)` of a nontrivial power `x ^ s` (`k, s ≠ 0`, `x ≠ t`) is
not cyclically reduced: its maximal reduced word starts with `t ^{±1}` and ends with `t ^{∓1}`, so
its first and last letters cancel. -/
theorem not_isCyclicallyReduced_toWord_conj {α : Type*} [DecidableEq α] (t x : α) (k s : ℤ)
    (hxt : x ≠ t) (hk : k ≠ 0) (hs : s ≠ 0) :
    ¬ FreeGroup.IsCyclicallyReduced
      (FreeGroup.toWord (FreeGroup.of t ^ k * FreeGroup.of x ^ s * FreeGroup.of t ^ (-k))) := by
  classical
  set A : List (α × Bool) := List.replicate k.natAbs (t, decide (0 < k)) with hA
  set B : List (α × Bool) := List.replicate s.natAbs (x, decide (0 < s)) with hB
  have hknabs : k.natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using hk
  have hsnabs : s.natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using hs
  -- The two "signs" of `k` are opposite.
  have hcomp : decide (0 < -k) = !decide (0 < k) := by
    by_cases h : 0 < k
    · have h2 : ¬ (0 < -k) := by omega
      rw [decide_eq_true h, decide_eq_false h2]; rfl
    · have h2 : 0 < -k := by omega
      rw [decide_eq_false h, decide_eq_true h2]; rfl
  -- Reduced words of the three factors.
  have htoA : FreeGroup.toWord (FreeGroup.of t ^ k) = A := by
    rw [hA]; exact toWord_of_zpow t k
  have htoB : FreeGroup.toWord (FreeGroup.of x ^ s) = B := by
    rw [hB]; exact toWord_of_zpow x s
  have htoC : FreeGroup.toWord (FreeGroup.of t ^ (-k)) = FreeGroup.invRev A := by
    rw [hA, toWord_of_zpow, Int.natAbs_neg, hcomp, invRev_replicate]
  -- The concatenation of the three reduced words is reduced.
  have hred : FreeGroup.IsReduced (A ++ B ++ FreeGroup.invRev A) := by
    simpa only [hA, hB] using
      isReduced_replicate_append_replicate_append_invRev (a₁ := t) (a₂ := x) (Ne.symm hxt)
        (decide (0 < k)) (decide (0 < s)) (m := k.natAbs) (n := s.natAbs) hsnabs
  have hAne : A ≠ [] := by
    rw [hA]
    intro hh
    exact hknabs (by simpa using congrArg List.length hh)
  -- The concatenation represents the group element.
  have hW : FreeGroup.mk (A ++ B ++ FreeGroup.invRev A)
      = FreeGroup.of t ^ k * FreeGroup.of x ^ s * FreeGroup.of t ^ (-k) := by
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    rw [← htoC, ← htoB, ← htoA]
    rw [FreeGroup.mk_toWord, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
  have htoW : FreeGroup.toWord (FreeGroup.of t ^ k * FreeGroup.of x ^ s * FreeGroup.of t ^ (-k))
      = A ++ B ++ FreeGroup.invRev A := by
    have h1 : FreeGroup.toWord (FreeGroup.of t ^ k * FreeGroup.of x ^ s * FreeGroup.of t ^ (-k))
        = FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A) := by
      rw [← hW, FreeGroup.toWord_mk]
    exact h1.trans hred.reduce_eq
  rw [htoW]
  exact not_isCyclicallyReduced_append_invRev' (M := B) hAne

end Work.ORLyndon
