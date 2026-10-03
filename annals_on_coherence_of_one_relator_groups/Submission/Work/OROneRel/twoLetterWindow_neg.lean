import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetter_cycle_decor

namespace Work.OROneRel

/-!
# The window of the two-letter Freiheitssatz, for the mirror weight

This file proves the mirror (`a ↦ -q`, `b ↦ p`) of `Work.OROneRel.window_eq_band_tlW`
(`Submission/Work/OROneRel/twoLetterFreiheitssatz.lean`): the walk of `a ^ p * b ^ q` now runs over
the levels `0, -q, …, -pq` (the `a`-block) and then `-pq, -pq + p, …, -p` (the `b`-block), i.e.
inside the band `[-pq, 0]` and touching both of its ends.  The window obligations therefore force
`lo = -pq` and `hi = 0`.

The proof is the direct computation, mirroring the `tlW` case: the decorated word is the staircase
above, so the walk is bounded below by `-pq` and above by `0`, attains both levels, and any strictly
wider window is contradicted by `hone` applied to the shift `k = ∓1`.
-/

/-- The mirror weight `a = 0 ↦ -q`, `b = 1 ↦ p` (the negation of `tlW p q`). -/
abbrev tlWneg (p q : ℕ) : Fin 2 → ℤ := fun x => if x = 0 then -(q : ℤ) else (p : ℤ)

/-- **The decorated walk of the two-letter relator for the mirror weight.**  The `a`-block is read at
the levels `0, -q, …, -(p-1)q` and the `b`-block at `-pq, -pq + p, …, -p`. -/
theorem decor_tlU_neg (p q : ℕ) :
    decor (tlWneg p q) 0 (wordOf (tlU p q))
      = List.ofFn (fun j : Fin p => (((0 : Fin 2), -((j : ℤ) * (q : ℤ))), true))
        ++ List.ofFn (fun k : Fin q =>
            (((1 : Fin 2), -((p : ℤ) * (q : ℤ)) + (k : ℤ) * (p : ℤ)), true)) := by
  have hword : wordOf (tlU p q)
      = List.replicate p ((0 : Fin 2), true) ++ List.replicate q ((1 : Fin 2), true) := by
    rw [tlU]
    exact wordOf_of_pow_mul_of_pow (0 : Fin 2) (1 : Fin 2) (by decide) p q
  rw [hword, decor_append, decor_replicate_true, decor_replicate_true, lsig_replicate_true,
    show tlWneg p q 0 = -(q : ℤ) from by simp [tlWneg],
    show tlWneg p q 1 = (p : ℤ) from by simp [tlWneg]]
  congr 1
  · rw [List.ofFn_injective.eq_iff]; funext j; simp
  · rw [List.ofFn_injective.eq_iff]; funext k
    simp only [Prod.mk.injEq, true_and, and_true]
    ring

/-- **The walk of the two-letter relator stays in the band `[-pq, 0]`.** -/
theorem walk_levels_neg (p q : ℕ) :
    ∀ e ∈ decor (tlWneg p q) 0 (wordOf (tlU p q)),
      -((p : ℤ) * (q : ℤ)) ≤ e.1.2 ∧ e.1.2 ≤ 0 ∧
        -((p : ℤ) * (q : ℤ)) ≤ e.1.2 + tlWneg p q e.1.1 ∧ e.1.2 + tlWneg p q e.1.1 ≤ 0 := by
  intro e he
  rw [decor_tlU_neg] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    have hj : (j : ℤ) + 1 ≤ (p : ℤ) := by
      exact_mod_cast (by have := j.isLt; omega : (j : ℕ) + 1 ≤ p)
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
    have hQ : (0 : ℤ) ≤ (q : ℤ) := by positivity
    rw [show tlWneg p q (0 : Fin 2) = -(q : ℤ) from by simp [tlWneg]]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
    have hk : (k : ℤ) + 1 ≤ (q : ℤ) := by
      exact_mod_cast (by have := k.isLt; omega : (k : ℕ) + 1 ≤ q)
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have hP : (0 : ℤ) ≤ (p : ℤ) := by positivity
    rw [show tlWneg p q (1 : Fin 2) = (p : ℤ) from by simp [tlWneg]]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **The walk attains the top level `0`.** -/
theorem walk_src_zero_neg (p q : ℕ) (hp : 1 ≤ p) :
    ∃ e ∈ decor (tlWneg p q) 0 (wordOf (tlU p q)), e.1.2 = (0 : ℤ) := by
  refine ⟨(((0 : Fin 2), -(((0 : ℤ)) * (q : ℤ))), true), ?_, ?_⟩
  · rw [decor_tlU_neg]
    exact List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨⟨0, hp⟩, by simp⟩))
  · simp

/-- **The walk attains the bottom level `-pq`.** -/
theorem walk_tgt_neg (p q : ℕ) (hp : 1 ≤ p) :
    ∃ e ∈ decor (tlWneg p q) 0 (wordOf (tlU p q)),
      e.1.2 + tlWneg p q e.1.1 = -((p : ℤ) * (q : ℤ)) := by
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; simp
  refine ⟨(((0 : Fin 2), -(((p - 1 : ℕ) : ℤ) * (q : ℤ))), true), ?_, ?_⟩
  · rw [decor_tlU_neg]
    exact List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨⟨p - 1, by omega⟩, by simp [hcast]⟩))
  · show -(((p - 1 : ℕ) : ℤ) * (q : ℤ)) + tlWneg p q (0 : Fin 2) = -((p : ℤ) * (q : ℤ))
    rw [show tlWneg p q (0 : Fin 2) = -(q : ℤ) from by simp [tlWneg], hcast]
    ring

/-- **The window of the two-letter Freiheitssatz, for the mirror weight `c 0 = -q`, `c 1 = p`.**
The walk of `a ^ p * b ^ q` on the levels is `0, -q, …, -pq, -pq + p, …, 0`, so `hwin` and `hone`
force `lo = -pq` and `hi = 0`.  (The analogous statement for the weight `tlW p q` is
`Work.OROneRel.window_eq_band_tlW`, proved in
`Submission/Work/OROneRel/twoLetterFreiheitssatz.lean`; the present statement is its image under the
letter-level negation `i ↦ -i`, since `decor (-tlW p q) 0 w` is the level-negation of
`decor (tlW p q) 0 w` and `winE (-c) lo hi = winE c (-hi) (-lo)`.) -/
theorem twoLetterWindow_neg (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {lo hi : ℤ}
    (hwin : ∀ e ∈ Work.OROneRel.decor (fun x : Fin 2 => if x = 0 then -(q : ℤ) else (p : ℤ)) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈
        Work.OROneRel.winE (fun x : Fin 2 => if x = 0 then -(q : ℤ) else (p : ℤ)) lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ e ∈ Work.OROneRel.decor (fun x : Fin 2 => if x = 0 then -(q : ℤ) else (p : ℤ)) 0
          (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
          lo ≤ e.1.2 + k ∧
            lo ≤ e.1.2 + (fun x : Fin 2 => if x = 0 then -(q : ℤ) else (p : ℤ)) e.1.1 + k ∧
            e.1.2 + k ≤ hi ∧
            e.1.2 + (fun x : Fin 2 => if x = 0 then -(q : ℤ) else (p : ℤ)) e.1.1 + k ≤ hi)) :
    lo = -((p : ℤ) * (q : ℤ)) ∧ hi = 0 := by
  -- Restate the hypotheses with the named mirror weight `tlWneg p q` (definitionally the lambda).
  have hwin' : ∀ e ∈ decor (tlWneg p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlWneg p q) lo hi := hwin
  have hone' : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ e ∈ decor (tlWneg p q) 0 (wordOf (tlU p q)),
          lo ≤ e.1.2 + k ∧ lo ≤ e.1.2 + tlWneg p q e.1.1 + k ∧ e.1.2 + k ≤ hi ∧
            e.1.2 + tlWneg p q e.1.1 + k ≤ hi) := hone
  have hget : ∀ e ∈ decor (tlWneg p q) 0 (wordOf (tlU p q)),
      lo ≤ e.1.2 ∧ e.1.2 ≤ hi ∧ lo ≤ e.1.2 + tlWneg p q e.1.1 ∧
        e.1.2 + tlWneg p q e.1.1 ≤ hi := by
    intro e he
    have h := hwin' e he
    rw [mem_winE] at h
    exact h
  -- `hwin` gives `lo ≤ 0` and `-pq ≤ hi` (from the two ends of the walk).
  obtain ⟨ea, hea, hA⟩ := walk_src_zero_neg p q hp
  obtain ⟨eb, heb, hB⟩ := walk_tgt_neg p q hp
  have hhi0 : 0 ≤ hi := by
    have h := (hget ea hea).2.1
    omega
  have hlopq : lo ≤ -((p : ℤ) * (q : ℤ)) := by
    have h := (hget eb heb).2.2.1
    omega
  -- Widening the window downwards is contradicted by the shift `k = -1`.
  have hlo : lo = -((p : ℤ) * (q : ℤ)) := by
    rcases lt_or_ge lo (-((p : ℤ) * (q : ℤ))) with hlt | hge
    · exfalso
      refine (hone' (-1) (by norm_num)) ?_
      intro e he
      obtain ⟨h1, h2, h3, h4⟩ := walk_levels_neg p q e he
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · omega
  -- Widening the window upwards is contradicted by the shift `k = 1`.
  have hhi : hi = 0 := by
    rcases lt_or_ge 0 hi with hlt | hge
    · exfalso
      refine (hone' 1 (by norm_num)) ?_
      intro e he
      obtain ⟨h1, h2, h3, h4⟩ := walk_levels_neg p q e he
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · omega
  exact ⟨hlo, hhi⟩

end Work.OROneRel
