import Mathlib

namespace Commons.NumberTheory.Diophantine

/-- The number of integer divisors of `z` equals twice the number of positive
divisors of `z.natAbs`. -/
lemma card_intDivisors (z : ℤ) : z.divisors.card = 2 * z.natAbs.divisors.card := by
  classical
  unfold Int.divisors
  rw [Finset.card_disjUnion, Finset.card_map, Finset.card_map]
  ring

theorem card_sq_sub_sq_le_divisors (Y : Finset ℤ) (e : ℤ) (he : e ≠ 0) :
    ((Y.product Y).filter (fun p : ℤ × ℤ => p.1 ^ 2 - p.2 ^ 2 = e)).card
      ≤ 2 * (e.natAbs).divisors.card := by
  classical
  set S := (Y.product Y).filter (fun p : ℤ × ℤ => p.1 ^ 2 - p.2 ^ 2 = e) with hS
  have hmaps : Set.MapsTo (fun p : ℤ × ℤ => p.1 - p.2) (↑S : Set (ℤ × ℤ))
      (↑e.divisors : Set ℤ) := by
    intro p hp
    simp only [Finset.mem_coe, hS, Finset.mem_filter] at hp
    obtain ⟨-, hval⟩ := hp
    rw [Finset.mem_coe, Int.mem_divisors]
    exact ⟨⟨p.1 + p.2, by rw [← hval]; ring⟩, he⟩
  have hinj : (↑S : Set (ℤ × ℤ)).InjOn (fun p : ℤ × ℤ => p.1 - p.2) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, hS, Finset.mem_filter] at hp hq
    obtain ⟨-, hpe⟩ := hp
    obtain ⟨-, hqe⟩ := hq
    have hne : p.1 - p.2 ≠ 0 := by
      intro h
      apply he
      rw [← hpe]
      have h12 : p.1 = p.2 := by linarith
      rw [h12]; ring
    have hp1 : (p.1 - p.2) * (p.1 + p.2) = e := by rw [← hpe]; ring
    have hq1 : (q.1 - q.2) * (q.1 + q.2) = e := by rw [← hqe]; ring
    have hpq' : p.1 - p.2 = q.1 - q.2 := hpq
    have hsum : p.1 + p.2 = q.1 + q.2 := by
      apply mul_left_cancel₀ hne
      rw [hp1, hpq', hq1]
    exact Prod.ext (by linarith) (by linarith)
  have h1 := Finset.card_le_card_of_injOn (fun p : ℤ × ℤ => p.1 - p.2) hmaps hinj
  rw [card_intDivisors] at h1
  exact h1

end Commons.NumberTheory.Diophantine
