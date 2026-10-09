import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Splitting a `σ`-palindrome of signed letters

Let `σ : X ≃ X` be an involution of the alphabet and let `L : List (X × Bool)` be a word of signed
letters such that the letterwise map `p ↦ (σ p.1, !p.2)` turns `L` into its reverse.  Then `L` splits
as `L = L₁ ++ L₂` with `L₁ = FreeGroup.invRev (L₂.map (fun p => (σ p.1, p.2)))`.

Concretely, such an `L` is of the shape `M ++ M.reverse.map (fun p ↦ (σ p.1, !p.2))`, and one takes
`L₁ := M`, `L₂ := M.reverse.map (fun p ↦ (σ p.1, !p.2))`.
-/

namespace Work.SSGRoute

open FreeGroup

/-- A `σ`-palindrome is a concatenation `M ++ M.reverse.map (fun p => (σ p.1, !p.2))`.

`List.bidirectionalRec` peels the word from both ends: the outer letters `a`, `b` satisfy
`(σ a.1, !a.2) = b`, the middle `l` is again a `σ`-palindrome (here `σ` is an involution, so the
condition at the front and at the back coincide), and `M := a :: M'` for `M'` the middle half. -/
private lemma palindrome_factor {X : Type*} (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (L : List (X × Bool))
    (hL : L.map (fun p => (σ p.1, !p.2)) = L.reverse) :
    ∃ M : List (X × Bool), L = M ++ M.reverse.map (fun p => (σ p.1, !p.2)) := by
  induction L using List.bidirectionalRec with
  | nil => exact ⟨[], by simp⟩
  | singleton a =>
      -- A one-letter palindrome would need `!a.2 = a.2`.
      exfalso
      have h2 : (σ a.1, !a.2) = a := by simpa using hL
      have h3 : (!a.2) = a.2 := congrArg Prod.snd h2
      obtain ⟨x, b⟩ := a
      cases b <;> simp_all
  | cons_append a l b ih =>
      have h' : (σ a.1, !a.2) :: (l.map (fun p => (σ p.1, !p.2)) ++ [(σ b.1, !b.2)])
          = b :: (l.reverse ++ [a]) := by
        simpa using hL
      obtain ⟨h1, h2⟩ := List.cons.inj h'
      -- `h1 : (σ a.1, !a.2) = b`, and `σ` is an involution, so `(σ b.1, !b.2) = a`.
      have htb : (fun p : X × Bool => (σ p.1, !p.2)) b = a := by
        rw [← h1]
        obtain ⟨x, c⟩ := a
        simp [hσ x]
      -- the middle letters form a `σ`-palindrome again
      have h3 : l.map (fun p => (σ p.1, !p.2)) = l.reverse := by
        apply List.append_cancel_right (bs := [a])
        simpa [htb] using h2
      obtain ⟨M, hM⟩ := ih h3
      refine ⟨a :: M, ?_⟩
      rw [hM]
      simp [List.reverse_cons, h1, List.append_assoc]

theorem split_sigmaPalindrome {X : Type*} (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (L : List (X × Bool))
    (hL : L.map (fun p => (σ p.1, !p.2)) = L.reverse) :
    ∃ L₁ L₂ : List (X × Bool), L = L₁ ++ L₂ ∧
      FreeGroup.invRev (L₂.map (fun p => (σ p.1, p.2))) = L₁ := by
  obtain ⟨M, hM⟩ := palindrome_factor σ hσ L hL
  refine ⟨M, M.reverse.map (fun p => (σ p.1, !p.2)), hM, ?_⟩
  -- `L₂.map (fun p => (σ p.1, p.2)) = M.reverse.map (fun p => (p.1, !p.2)) = FreeGroup.invRev M`
  have hst : (fun p : X × Bool => (σ (σ p.1), !p.2)) = (fun p : X × Bool => (p.1, !p.2)) := by
    funext p; rw [hσ p.1]
  have hstep : ((M.reverse.map (fun p => (σ p.1, !p.2))).map (fun p => (σ p.1, p.2)))
      = FreeGroup.invRev M := by
    simp only [FreeGroup.invRev, List.map_map, Function.comp_def]
    rw [hst, ← List.map_reverse]
  rw [hstep, FreeGroup.invRev_invRev]

end Work.SSGRoute
