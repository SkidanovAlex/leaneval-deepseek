import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-- For a natural number `n` and a complex number `z`, the real scalar action of `n` on `z`
coincides with multiplication by `(n : ℂ)`. -/
lemma normSumMultiset_real_nat_smul_complex (n : ℕ) (z : ℂ) :
    (n : ℝ) • z = (n : ℂ) * z := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_smul, ih, Nat.cast_succ, add_mul]; simp

/-- If every element of a multiset of complex numbers has norm `1`, the sum of their norms
equals the cardinality (as a real number). -/
lemma normSumMultiset_map_norm_sum_eq_card {s : Multiset ℂ} (h : ∀ z ∈ s, ‖z‖ = 1) :
    (s.map fun x => ‖x‖).sum = (s.card : ℝ) := by
  have hmap : (s.map fun x => ‖x‖) = s.map fun _ => (1 : ℝ) :=
    Multiset.map_congr rfl (fun x hx => h x hx)
  rw [hmap]
  simp [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]

theorem norm_sum_multiset {s : Multiset ℂ} (h1 : ∀ z ∈ s, ‖z‖ = 1)
    (h2 : ‖s.sum‖ = (s.card : ℝ)) : ∀ z ∈ s, z = s.sum / (s.card : ℂ) := by
  revert h1 h2
  refine Multiset.induction_on s ?base ?step
  · intro h1 h2 z hz; simp at hz
  · intro z t ih h1 h2 w hw
    rw [Multiset.sum_cons, Multiset.card_cons] at h2 ⊢
    have h1z : ‖z‖ = 1 := h1 z (Multiset.mem_cons_self z t)
    have h1t : ∀ a ∈ t, ‖a‖ = 1 := fun a ha => h1 a (Multiset.mem_cons_of_mem ha)
    have hle : ‖t.sum‖ ≤ (t.card : ℝ) := by
      rw [← normSumMultiset_map_norm_sum_eq_card h1t]; exact norm_multiset_sum_le t
    have hge : (t.card : ℝ) ≤ ‖t.sum‖ := by
      have hb := norm_add_le z t.sum
      rw [h2, h1z] at hb
      push_cast at hb
      linarith
    have hcard : ‖t.sum‖ = (t.card : ℝ) := le_antisymm hle hge
    have heq : ‖z + t.sum‖ = ‖z‖ + ‖t.sum‖ := by
      rw [h2, h1z, hcard]; push_cast; ring
    have hsmul : ‖t.sum‖ • z = ‖z‖ • t.sum := norm_add_eq_iff_real.mp heq
    rw [h1z, hcard] at hsmul
    have hsmul' : t.sum = (t.card : ℝ) • z := by simpa using hsmul.symm
    have htz : t.sum = (t.card : ℂ) * z := by
      rw [hsmul', normSumMultiset_real_nat_smul_complex]
    have hkey : z + t.sum = ((t.card + 1 : ℕ) : ℂ) * z := by
      rw [htz]; push_cast; ring
    have hc : ((t.card + 1 : ℕ) : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact Nat.succ_ne_zero t.card
    rw [Multiset.mem_cons] at hw
    rcases hw with hwz | hw
    · rw [hwz, hkey, mul_div_cancel_left₀ z hc]
    · have htpos : t.card ≠ 0 := by
        intro hc0
        rw [Multiset.card_eq_zero] at hc0
        rw [hc0] at hw
        simp at hw
      have hwz' : w = z := by
        have hw1 := ih h1t hcard w hw
        rw [hw1, htz, mul_div_cancel_left₀ z (Nat.cast_ne_zero.mpr htpos)]
      rw [hwz', hkey, mul_div_cancel_left₀ z hc]

end Work.CharCore
