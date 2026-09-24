import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.sum_primes_inv_le_loglog

namespace Work.NumberTheory.Chen.BTermCount

/-- A product of two primes, written with the smaller factor first, determines the two factors:
if `a ≤ b` and `c ≤ d` are primes with `a * b = c * d`, then `a = c` and `b = d`.
(Uniqueness of factorisation into two primes; the order hypothesis removes the ambiguity
`{a,b} = {c,d}`.) -/
private lemma prime_mul_prime_eq {a b c d : ℕ}
    (ha : a.Prime) (_hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (hab : a ≤ b) (hcd : c ≤ d) (h : a * b = c * d) : a = c ∧ b = d := by
  have h1 : a ∣ c * d := by rw [← h]; exact dvd_mul_right a b
  rcases (ha.dvd_mul).mp h1 with hac | had
  · -- `a ∣ c`, so `a = c` and cancelling gives `b = d`.
    have hca : c = a := (Nat.Prime.dvd_iff_eq hc ha.ne_one).mp hac
    exact ⟨hca.symm, Nat.mul_left_cancel ha.pos (by rw [h, hca])⟩
  · -- `a ∣ d`, so `a = d`; then `a * b = c * a` forces `b = c`, and sorting gives `a = c`, `b = d`.
    have hda : d = a := (Nat.Prime.dvd_iff_eq hd ha.ne_one).mp had
    have hbc : b = c := Nat.mul_left_cancel ha.pos (by rw [h, hda, mul_comm c a])
    have hac : a = c := le_antisymm (hbc ▸ hab) (hda ▸ hcd)
    exact ⟨hac, hbc.trans (hac.symm.trans hda.symm)⟩

/-- **Count of ordered prime pairs with bounded product.**
The number of pairs `(p, q)` of primes with `Y ≤ p ≤ q ≤ N` and `p * q ≤ N` is at most `N`:
the map `(p,q) ↦ p * q` is injective on these pairs (uniqueness of factorisation into
two primes, `prime_mul_prime_eq`) and takes values in `{1, …, N}`.  Since
`Real.log (Real.log (N + 3)) + 3 ≥ 1` for `N ≥ 2`, this is in particular
`≤ N * (log log (N + 3) + 3)`. -/
theorem semiPairCount_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y N : ℕ, 2 ≤ N →
      ((( Finset.Icc Y N ×ˢ Finset.Icc Y N ).filter
          (fun t : ℕ × ℕ => t.1.Prime ∧ t.2.Prime ∧ t.1 ≤ t.2 ∧ t.1 * t.2 ≤ N)).card : ℝ)
        ≤ C * (N : ℝ) * (Real.log (Real.log ((N : ℝ) + 3)) + 3) := by
  refine ⟨1, one_pos, ?_⟩
  intro Y N hN
  rw [one_mul]
  set S : Finset (ℕ × ℕ) := (Finset.Icc Y N ×ˢ Finset.Icc Y N).filter
      (fun t : ℕ × ℕ => t.1.Prime ∧ t.2.Prime ∧ t.1 ≤ t.2 ∧ t.1 * t.2 ≤ N) with hS
  -- The product map is injective on `S` and lands in `{1, …, N}`, so `S.card ≤ N`.
  have hcard : (S.card : ℝ) ≤ (N : ℝ) := by
    have hinj : Set.InjOn (fun t : ℕ × ℕ => t.1 * t.2) ↑S := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_product] at ha hb
      obtain ⟨⟨-, -⟩, hap, haq, hale, -⟩ := ha
      obtain ⟨⟨-, -⟩, hbp, hbq, hble, -⟩ := hb
      obtain ⟨h1, h2⟩ := prime_mul_prime_eq hap haq hbp hbq hale hble hab
      exact Prod.ext h1 h2
    have hmap : Set.MapsTo (fun t : ℕ × ℕ => t.1 * t.2) ↑S ↑(Finset.Icc 1 N) := by
      intro t ht
      simp only [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_product] at ht
      obtain ⟨⟨-, -⟩, htp, htq, -, htN⟩ := ht
      simp only [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero htp.ne_zero htq.ne_zero), htN⟩
    have h := Finset.card_le_card_of_injOn (fun t : ℕ × ℕ => t.1 * t.2) hmap hinj
    rw [Nat.card_Icc] at h
    simp only [Nat.add_sub_cancel] at h
    exact_mod_cast h
  -- `log log (N + 3) ≥ 0` for `N ≥ 2`, since `N + 3 ≥ 5 > e`.
  have hloglog : 0 ≤ Real.log (Real.log ((N : ℝ) + 3)) := by
    apply Real.log_nonneg
    rw [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (N : ℝ) + 3)]
    have h5 : (5 : ℝ) ≤ (N : ℝ) + 3 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    linarith [Real.exp_one_lt_three]
  calc (S.card : ℝ) ≤ (N : ℝ) := hcard
    _ = (N : ℝ) * 1 := (mul_one _).symm
    _ ≤ (N : ℝ) * (Real.log (Real.log ((N : ℝ) + 3)) + 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end Work.NumberTheory.Chen.BTermCount
