import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02

/-!
# Area BG: reusable technical lemmas for Bender–Glauberman Lemma 3.3

Two elementary facts used in the first case of BG Lemma 3.3 (`Work.BG.lemma33Case1`):

* the `mod 2` step for a class function `χ` which is even at `1`: for an element `g` whose
  centralizer index `n = |G : C_G(g)|` is odd, `Gorenstein 4.2.10` gives that
  `n * χ g / 2` is an algebraic integer, and since `n` is odd this forces `χ g ≡ 0 (mod 2)`;
* the pairing step: the sum of a `g`-invariant function with algebraic-integer values over a
  finite `g`-stable, `g`-fixed-point-free set is twice an algebraic integer (the set splits
  into two-element orbits `{x, g x}` on which the summand takes the same value).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Odd multiplier.**  If `n` is an odd natural number and `n * x` is twice an algebraic
integer with `x` itself an algebraic integer, then `x` is twice an algebraic integer.

Indeed `n * x = 2 * z` with `z` an algebraic integer, and `n` odd gives `n - 1 = 2 * m`, so
`x = n * x - (n - 1) * x = 2 * (z - m * x)`. -/
theorem algIntModTwo_of_odd_mul {n : ℕ} (hn : Odd n) {x : ℂ} (hint : IsIntegral ℤ x)
    (h : IsIntegral ℤ ((n : ℂ) * x / 2)) : AlgIntModTwo x 0 := by
  obtain ⟨m, hm⟩ := hn
  refine ⟨(n : ℂ) * x / 2 - (m : ℂ) * x, h.sub ((isIntegral_natCast m).mul hint), ?_⟩
  have hthis : (n : ℂ) = 2 * (m : ℂ) + 1 := by rw [hm]; push_cast; ring
  rw [hthis]
  ring

/-- **Pairing step.**  If `g` is a fixed-point-free involution on a finset `s` and `f` is
`g`-invariant with algebraic-integer values, then `∑_{x∈s} f x` is twice an algebraic
integer.  (The set splits into the two-element orbits `{x, g x}`, on each of which the
summand takes the same value, so the total is `2 · ∑_{x ∈ s, x < g x} f x`.) -/
theorem even_sum_of_free_involution {ι : Type*} [DecidableEq ι] (g : ι → ι)
    (hg : ∀ x, g (g x) = x) (f : ι → ℂ) (hf : ∀ x, f (g x) = f x)
    (hint : ∀ x, IsIntegral ℤ (f x)) :
    ∀ s : Finset ι, (∀ x ∈ s, g x ∈ s) → (∀ x ∈ s, g x ≠ x) →
      ∃ z : ℂ, IsIntegral ℤ z ∧ ∑ x ∈ s, f x = 2 * z := by
  suffices key : ∀ n : ℕ, ∀ s : Finset ι, s.card = n →
      (∀ x ∈ s, g x ∈ s) → (∀ x ∈ s, g x ≠ x) →
        ∃ z : ℂ, IsIntegral ℤ z ∧ ∑ x ∈ s, f x = 2 * z by
    intro s hs hfix
    exact key s.card s rfl hs hfix
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
    intro s hcard hs hfix
    rcases Finset.eq_empty_or_nonempty s with h0 | ⟨a, ha⟩
    · exact ⟨0, isIntegral_zero, by simp [h0]⟩
    · have hga : g a ∈ s := hs a ha
      have hne : g a ≠ a := hfix a ha
      have hane : a ≠ g a := fun h => hne h.symm
      have hga' : g a ∈ s.erase a := Finset.mem_erase.mpr ⟨hne, hga⟩
      set s' : Finset ι := (s.erase a).erase (g a) with hs'def
      have hs'_sub : s' ⊆ s := by
        intro x hx
        have h1 : x ∈ s.erase a := (Finset.mem_erase.mp hx).2
        exact (Finset.mem_erase.mp h1).2
      have hs'_ne_a : ∀ x ∈ s', x ≠ a := fun x hx => (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hs'_ne_ga : ∀ x ∈ s', x ≠ g a := fun x hx => (Finset.mem_erase.mp hx).1
      have hcard' : s'.card < n := by
        have h1 : s'.card = (s.erase a).card - 1 := Finset.card_erase_of_mem hga'
        have h2 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
        have h3 : 2 ≤ s.card := by
          have hle : ({a, g a} : Finset ι).card ≤ s.card := by
            apply Finset.card_le_card
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ha
            · exact Finset.mem_singleton.mp hx ▸ hga
          have hpair : ({a, g a} : Finset ι).card = 2 := by
            rw [Finset.pair_comm]; exact Finset.card_pair hne
          rwa [hpair] at hle
        omega
      have hs' : ∀ x ∈ s', g x ∈ s' := by
        intro x hx
        have hxs : x ∈ s := hs'_sub hx
        have hxne_a : x ≠ a := hs'_ne_a x hx
        have hxne_ga : x ≠ g a := hs'_ne_ga x hx
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hs x hxs⟩⟩
        · intro h
          have h2 : g (g x) = g (g a) := by rw [h]
          rw [hg x, hg a] at h2
          exact hxne_a h2
        · intro h
          have h2 : g (g x) = g a := by rw [h]
          rw [hg x] at h2
          exact hxne_ga h2
      have hfix' : ∀ x ∈ s', g x ≠ x := fun x hx => hfix x (hs'_sub hx)
      obtain ⟨z, hz, hzsum⟩ := IH s'.card hcard' s' rfl hs' hfix'
      have hdecomp : s = insert a (insert (g a) s') := by
        rw [← Finset.insert_erase ha]
        congr 1
        rw [← Finset.insert_erase hga']
      have hai : a ∉ insert (g a) s' := by
        intro h
        rcases Finset.mem_insert.mp h with h' | h'
        · exact hane h'
        · exact absurd rfl (hs'_ne_a a h')
      have hgai : g a ∉ s' := fun h => hs'_ne_ga (g a) h rfl
      have hsplit : ∑ x ∈ s, f x = 2 * f a + ∑ x ∈ s', f x := by
        rw [hdecomp, Finset.sum_insert hai, Finset.sum_insert hgai, hf a]
        ring
      exact ⟨z + f a, hz.add (hint a), by rw [hsplit, hzsum]; ring⟩

end Work.BG
