import Mathlib
import Submission.Work.WilG4c.CellParamDefs

namespace Work.WilG4c

/-!
  Surjectivity of the prefix map onto the levels of `κ`.

  `lvl p N κ m` is the projection of `κ ⊆ ℝ^{p+N}` to the first `p+m` coordinates, defined
  by the downward recursion `lvl p N κ m = projLast (lvl p N κ (m+1))` for `m < N`.  Here we
  show that every `x` in the level-`m` set is the prefix `prefl m hm z` of some point `z ∈ κ`
  (the dual of `prefl_mem_lvl`, which shows the converse).  The proof is the downward
  induction on `N - m`: at level `N` the prefix is the point itself, and below it a point of
  `lvl p N κ m` is `Fin.init` of a point of `lvl p N κ (m+1)` obtained by `projLast`.
-/

/-- At level `N`, the prefix is the point itself. -/
private lemma prefl_eq_self {p N : ℕ} (hm : N ≤ N) (z : Fin (p+N) → ℝ) :
    prefl N hm z = z := by
  funext i
  exact congrArg z (Fin.ext rfl)

theorem exists_prefl_aux (p N : ℕ) (κ : Set (Fin (p+N) → ℝ)) (m : ℕ) (hm : m ≤ N)
    (x : Fin (p+m) → ℝ) (hx : x ∈ Work.WilG4c.lvl p N κ m) :
    ∃ z : Fin (p+N) → ℝ, z ∈ κ ∧ Work.WilG4c.prefl m hm z = x := by
  have key : ∀ k, ∀ m, N - m = k → ∀ (hm : m ≤ N) (x : Fin (p+m) → ℝ),
      x ∈ lvl p N κ m → ∃ z : Fin (p+N) → ℝ, z ∈ κ ∧ prefl m hm z = x := by
    intro k
    induction k with
    | zero =>
      -- `N - m = 0` with `m ≤ N` forces `m = N`, where `lvl` is `κ` itself.
      intro m hmk hm x hx
      have hmN : m = N := by omega
      subst hmN
      rw [lvl_self] at hx
      exact ⟨x, hx, prefl_eq_self hm x⟩
    | succ k ih =>
      intro m hmk hm x hx
      have hlt : m < N := by omega
      -- Below the top level `lvl p N κ m` is the projection of `lvl p N κ (m+1)`.
      rw [lvl_succ κ hlt] at hx
      obtain ⟨t, ht⟩ := hx
      have hm1 : m + 1 ≤ N := hlt
      have hk' : N - (m+1) = k := by omega
      -- Inductively, the point `Fin.snoc x t` of the level-`(m+1)` set is the prefix of `z ∈ κ`.
      obtain ⟨z, hz, hzpre⟩ := ih (m+1) hk' hm1 (Fin.snoc x t) ht
      refine ⟨z, hz, ?_⟩
      have hinit : Fin.init (prefl (m+1) hm1 z) = prefl m hm z := by
        rw [prefl_init m hm1 z]
      have hsnoc : (Fin.init (Fin.snoc (α := fun _ => ℝ) x t) : Fin (p+m) → ℝ) = x := by
        funext i
        simp [Fin.init, Fin.snoc]
      calc prefl m hm z = Fin.init (prefl (m+1) hm1 z) := hinit.symm
        _ = Fin.init (Fin.snoc (α := fun _ => ℝ) x t) := by rw [hzpre]
        _ = x := hsnoc
  exact key (N - m) m rfl hm x hx

end Work.WilG4c
