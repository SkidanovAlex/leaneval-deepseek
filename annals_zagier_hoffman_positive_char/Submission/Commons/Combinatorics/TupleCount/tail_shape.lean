import Mathlib

set_option autoImplicit false

namespace Commons.Combinatorics.TupleCount

/-- If `d` divides the sum of `s` and the sum of every (nonempty) tail of `s`, then `d` divides
every element of `s`. -/
lemma dvd_of_drop_dvd_sum {d : ℕ} {s : List ℕ} (h0 : d ∣ s.sum)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ s.length → d ∣ (s.drop k).sum) :
    ∀ x ∈ s, d ∣ x := by
  induction s with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
    intro x hx
    have ht_sum : d ∣ t.sum := by
      have h1 := h 1 le_rfl (by simp)
      simpa using h1
    rcases List.mem_cons.mp hx with hxa | hxt
    · rw [hxa]
      have hthis : d ∣ a + t.sum := by simpa using h0
      exact (Nat.dvd_add_iff_left ht_sum).mpr hthis
    · refine ih ht_sum ?_ x hxt
      intro k hk1 hk2
      have hk : d ∣ ((a :: t).drop (k + 1)).sum := h (k + 1) (by omega) (by simp; omega)
      simpa using hk

/-- If `d ≥ 2` divides `x`, with `1 ≤ x ≤ 2d`, then `x = d` or `x = 2d`. -/
lemma eq_or_eq_of_dvd_le_two {d x : ℕ} (hd : 2 ≤ d) (hx1 : 1 ≤ x) (hdvd : d ∣ x)
    (hx : x ≤ 2 * d) : x = d ∨ x = 2 * d := by
  rcases hdvd with ⟨c, rfl⟩
  have hdpos : 0 < d := by omega
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc; simp at hx1
    · exact hc
  have hc2 : c ≤ 2 := by
    have hle : d * c ≤ d * 2 := by simpa [Nat.mul_comm] using hx
    exact Nat.le_of_mul_le_mul_left hle hdpos
  have hc : c = 1 ∨ c = 2 := by omega
  rcases hc with rfl | rfl
  · left; ring
  · right; ring

/-- For a list of naturals all bounded below by `d`, `d * length ≤ sum`. -/
lemma length_mul_le_sum {l : List ℕ} {d : ℕ} (h : ∀ x ∈ l, d ≤ x) : l.length * d ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.forall_mem_cons] at h
    obtain ⟨ha, ht⟩ := h
    have ih' := ih ht
    have hrec : (t.length + 1) * d = t.length * d + d := by ring
    rw [List.length_cons, List.sum_cons, hrec]
    omega

theorem tail_shape {q w : ℕ} (hq : 3 ≤ q) (hw : w ≤ 2 * q - 2) {ℓ : List ℕ}
    (hne : ℓ ≠ []) (hpos : ∀ x ∈ ℓ, 1 ≤ x) (hnd : ∀ x ∈ ℓ, ¬ q ∣ x) (hsum : ℓ.sum = w)
    (hdiv : ∀ k : ℕ, 1 ≤ k → k ≤ ℓ.length → (q - 1) ∣ (ℓ.drop k).sum) :
    (ℓ.length = 1 ∧ ℓ = [w]) ∨ (ℓ = [w - (q - 1), q - 1]) := by
  rcases ℓ with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · have ha1 : 1 ≤ a := hpos a List.mem_cons_self
    have htsum : a + t.sum = w := by simpa using hsum
    -- every element of `t` is divisible by `q - 1`
    have ht_sum_dvd : (q - 1) ∣ t.sum := by
      have h1 := hdiv 1 le_rfl (by simp)
      simpa using h1
    have ht_dvd : ∀ x ∈ t, (q - 1) ∣ x := by
      refine dvd_of_drop_dvd_sum ht_sum_dvd ?_
      intro k hk1 hk2
      have hk : (q - 1) ∣ ((a :: t).drop (k + 1)).sum := hdiv (k + 1) (by omega) (by simp; omega)
      simpa using hk
    have ht_ge : ∀ x ∈ t, q - 1 ≤ x := by
      intro x hx
      exact Nat.le_of_dvd (by have := hpos x (List.mem_cons_of_mem a hx); omega) (ht_dvd x hx)
    have ht_le_w : ∀ x ∈ t, x ≤ w := by
      intro x hx
      have hmem : x ∈ (a :: t) := List.mem_cons_of_mem a hx
      have := List.le_sum_of_mem hmem
      rwa [hsum] at this
    -- the tail has length at most 1
    have htlen : t.length ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ t.length := by omega
      have hsumge : t.length * (q - 1) ≤ t.sum := length_mul_le_sum ht_ge
      have h2ge : 2 * (q - 1) ≤ t.sum := le_trans (Nat.mul_le_mul_right (q - 1) h2) hsumge
      have : 2 * (q - 1) = 2 * q - 2 := by omega
      omega
    rcases t with _ | ⟨b, t'⟩
    · -- t = []
      left
      refine ⟨by simp, ?_⟩
      have : a = w := by simpa using htsum
      simp [this]
    · rcases t' with _ | ⟨c, t''⟩
      · -- t = [b]
        right
        have hb_mem : b ∈ [b] := by simp
        have hbge : q - 1 ≤ b := ht_ge b hb_mem
        have hbdvd : (q - 1) ∣ b := ht_dvd b hb_mem
        have hble : b ≤ 2 * q - 2 := by have := ht_le_w b hb_mem; omega
        have hclass : b = q - 1 ∨ b = 2 * (q - 1) := by
          refine eq_or_eq_of_dvd_le_two (d := q - 1) (x := b) (by omega) (by omega) hbdvd ?_
          omega
        have hab : a + b = w := by simpa using htsum
        rcases hclass with hb | hb
        · have : a = w - (q - 1) := by omega
          rw [this, hb]
        · exfalso
          have : 2 * (q - 1) = 2 * q - 2 := by omega
          omega
      · -- t = b :: c :: t'' : length at least 2, contradiction
        exfalso
        simp at htlen

end Commons.Combinatorics.TupleCount
