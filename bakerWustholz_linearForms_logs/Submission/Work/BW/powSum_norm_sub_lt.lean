import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The norm of a sum of a multiset of elements of a seminormed additive commutative group is
bounded by the sum of the norms. -/
theorem multiset_norm_sum_le {α : Type*} {E : Type*} [SeminormedAddCommGroup E]
    (s : Multiset α) (f : α → E) :
    ‖(s.map f).sum‖ ≤ (s.map (fun x => ‖f x‖)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
      exact (norm_add_le (f a) (Multiset.map f s).sum).trans (add_le_add le_rfl ih)

theorem powSum_norm_sub_lt (P : Polynomial ℤ) (hP : P.Monic) (p k : ℕ) {H : ℝ}
    (hroot : ∀ z : ℂ, (P.map (Int.castRingHom ℂ)).IsRoot z → ‖z‖ ≤ H)
    (hbig : (P.natDegree : ℝ) * H ^ (k * p) + (P.natDegree : ℝ) * H ^ k < (p : ℝ)) :
    ‖((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ (k * p))).sum
      - ((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ k)).sum‖ < (p : ℝ) := by
  classical
  set R : Multiset ℂ := (P.map (Int.castRingHom ℂ)).roots with hR
  set c : ℝ := H ^ (k * p) + H ^ k with hc
  have hQne : (P.map (Int.castRingHom ℂ)) ≠ 0 := (hP.map (Int.castRingHom ℂ)).ne_zero
  have hcard : R.card = P.natDegree := by
    rw [hR]
    exact IsAlgClosed.card_roots_map_eq_natDegree_of_injective P (RingHom.injective_int _)
  have hbigc : (P.natDegree : ℝ) * c < (p : ℝ) := by
    rw [hc, mul_add]
    exact hbig
  by_cases hR0 : R = 0
  · -- the multiset of roots is empty: both sums vanish, and `p > 0`
    have hcard0 : R.card = 0 := by rw [hR0]; simp
    have hnd : P.natDegree = 0 := by rw [← hcard]; exact hcard0
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have h' : (P.natDegree : ℝ) * H ^ (k * p) + (P.natDegree : ℝ) * H ^ k = 0 := by
        rw [hnd]; simp
      rw [h'] at hbig
      exact hbig
    have h1 : (R.map (fun z => z ^ (k * p))).sum = 0 := by rw [hR0]; simp
    have h2 : (R.map (fun z => z ^ k)).sum = 0 := by rw [hR0]; simp
    simpa [h1, h2] using hp0
  · -- there is at least one root, hence `H ≥ 0`
    obtain ⟨z0, hz0⟩ := Multiset.exists_mem_of_ne_zero hR0
    have hz0mem : z0 ∈ (P.map (Int.castRingHom ℂ)).roots := by rw [← hR]; exact hz0
    have hz0root : (P.map (Int.castRingHom ℂ)).IsRoot z0 :=
      (Polynomial.mem_roots hQne).mp hz0mem
    have hH0 : 0 ≤ H := le_trans (norm_nonneg z0) (hroot z0 hz0root)
    have hcpos : 0 ≤ c := by
      rw [hc]
      exact add_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _)
    have hbound : (R.map (fun z => ‖z ^ (k * p) - z ^ k‖)).sum ≤ (R.card : ℝ) * c := by
      have hpoint : ∀ x ∈ R.map (fun z => ‖z ^ (k * p) - z ^ k‖), x ≤ c := by
        intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        have hzmem : z ∈ (P.map (Int.castRingHom ℂ)).roots := by rw [← hR]; exact hz
        have hzroot : (P.map (Int.castRingHom ℂ)).IsRoot z :=
          (Polynomial.mem_roots hQne).mp hzmem
        have hzH : ‖z‖ ≤ H := hroot z hzroot
        rw [hc]
        calc ‖z ^ (k * p) - z ^ k‖ ≤ ‖z ^ (k * p)‖ + ‖z ^ k‖ := norm_sub_le _ _
          _ = ‖z‖ ^ (k * p) + ‖z‖ ^ k := by rw [norm_pow, norm_pow]
          _ ≤ H ^ (k * p) + H ^ k :=
              add_le_add (pow_le_pow_left₀ (norm_nonneg z) hzH _)
                (pow_le_pow_left₀ (norm_nonneg z) hzH _)
      have := Multiset.sum_le_card_nsmul (R.map (fun z => ‖z ^ (k * p) - z ^ k‖)) c hpoint
      simpa [Multiset.card_map, nsmul_eq_mul] using this
    calc ‖(R.map (fun z => z ^ (k * p))).sum - (R.map (fun z => z ^ k)).sum‖
        = ‖(R.map (fun z => z ^ (k * p) - z ^ k)).sum‖ := by rw [Multiset.sum_map_sub]
      _ ≤ (R.map (fun z => ‖z ^ (k * p) - z ^ k‖)).sum := multiset_norm_sum_le R (fun z => z ^ (k * p) - z ^ k)
      _ ≤ (R.card : ℝ) * c := hbound
      _ ≤ (P.natDegree : ℝ) * c := by
          apply mul_le_mul_of_nonneg_right _ hcpos
          rw [hcard]
      _ < (p : ℝ) := hbigc

end Work.BW
