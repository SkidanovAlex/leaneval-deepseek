import Mathlib
import Submission.Commons.GroupTheory.FreeGroup.abHom_mk_toAdd

namespace Commons.GroupTheory.FreeGroup

/-- Reversing a list does not change the `ℤ`-sum of its `f`-images. -/
theorem sum_map_reverse {α : Type*} (f : α → ℤ) (l : List α) :
    (l.reverse.map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.reverse_cons, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring

/-- **Pairing lemma.**  If `c` classifies the letters of `α` and two letters with the same
class have `f`-values summing to an even integer, then lists `A`, `B` with the same
`c`-sequence have `f`-sums adding up to an even integer: pair up the letters of `A` with the
letters of `B` and sum the (even) pair contributions. -/
theorem dvd_sum_add_of_map_eq {α : Type*} {n : ℕ} (f : α → ℤ) (c : α → Fin n)
    (hf : ∀ a b : α, c a = c b → (2 : ℤ) ∣ f a + f b) :
    ∀ (A B : List α), B.map c = A.map c → (2 : ℤ) ∣ (A.map f).sum + (B.map f).sum := by
  intro A
  induction A with
  | nil =>
    intro B h
    have hlen : B.length = 0 := by
      have := congrArg List.length h
      simpa using this
    obtain rfl : B = [] := List.eq_nil_of_length_eq_zero hlen
    simp
  | cons a A' ih =>
    intro B h
    cases B with
    | nil => simp at h
    | cons b B' =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨p, hp⟩ := hf a b h1.symm
      obtain ⟨q, hq⟩ := ih B' h2
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      exact ⟨p + q, by
        have key : f a + (A'.map f).sum + (f b + (B'.map f).sum)
            = (f a + f b) + ((A'.map f).sum + (B'.map f).sum) := by ring
        rw [key, hp, hq]; ring⟩

/-- **Even exponent sums.**  If the generator sequence of `A` is the reverse of the
generator sequence of `B` (equivalently `B.reverse.map Prod.fst = A.map Prod.fst`), then
every coordinate of the abelianisation of `FreeGroup.mk (A ++ B)` is even.  (Each letter of
`B` pairs with a letter of `A` of the same generator, and the two contributions `±1 + ±1`
are even.) -/
theorem abHom_mk_append_even (n : ℕ) (A B : List (Fin n × Bool))
    (h : B.reverse.map Prod.fst = A.map Prod.fst) (u : Fin n) :
    (2 : ℤ) ∣ (abHom n (FreeGroup.mk (A ++ B))).toAdd u := by
  rw [abHom_mk_toAdd, List.map_append, List.sum_append]
  have hf : ∀ a b : Fin n × Bool, Prod.fst a = Prod.fst b →
      (2 : ℤ) ∣ (if a.1 = u then (if a.2 then (1 : ℤ) else -1) else 0)
        + (if b.1 = u then (if b.2 then (1 : ℤ) else -1) else 0) := by
    intro a b hab
    have hb : b.1 = u ↔ a.1 = u := by rw [hab]
    by_cases ha : a.1 = u
    · rw [if_pos ha, if_pos (hb.mpr ha)]
      cases a.2 <;> cases b.2 <;> simp
    · rw [if_neg ha, if_neg (fun hc => ha (hb.mp hc))]
      simp
  have key := dvd_sum_add_of_map_eq
    (fun l : Fin n × Bool => if l.1 = u then (if l.2 then (1 : ℤ) else -1) else 0)
    Prod.fst hf A B.reverse h
  rwa [sum_map_reverse] at key

end Commons.GroupTheory.FreeGroup
