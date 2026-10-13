import Mathlib

universe a

namespace Work.DSM5b

theorem mem_pow_ideal_sum_prod {R : Type a} [CommRing R] {ι : Type a}
    (t : ι → R) (M : ℕ) (a : R) (ha : a ∈ (Ideal.span (Set.range t)) ^ M) :
    ∃ (B : Finset (Fin M → ι)) (d : (Fin M → ι) → R), a = ∑ b ∈ B, d b * ∏ k, t (b k) := by
  classical
  -- `(span (range t)) ^ M` equals the span of the M-fold products of generators.
  have hmem : a ∈ Submodule.span R (Set.range (fun b : Fin M → ι => ∏ k, t (b k))) := by
    rw [Submodule.span_pow] at ha
    refine Submodule.span_le.mpr ?_ ha
    rintro y hy
    rw [Set.mem_pow_iff_prod] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    apply Submodule.subset_span
    have hf' : ∀ i : Fin M, ∃ j : ι, t j = f i := fun i => hf i
    choose b hb using hf'
    exact ⟨b, Finset.prod_congr rfl (fun i _ => hb i)⟩
  clear ha
  -- Every element of the span of the products is such a sum: induct on the span.
  suffices h : ∀ x ∈ Submodule.span R (Set.range (fun b : Fin M → ι => ∏ k, t (b k))),
      ∃ (B : Finset (Fin M → ι)) (d : (Fin M → ι) → R), x = ∑ b ∈ B, d b * ∏ k, t (b k) by
    exact h a hmem
  intro x hx
  exact Submodule.span_induction
    (p := fun y _ => ∃ (B : Finset (Fin M → ι)) (d : (Fin M → ι) → R),
      y = ∑ b ∈ B, d b * ∏ k, t (b k))
    (fun y hy => by
      obtain ⟨b, rfl⟩ := hy
      exact ⟨{b}, fun _ => 1, by simp⟩)
    ⟨∅, fun _ => 0, by simp⟩
    (fun y z _ _ hy hz => by
      obtain ⟨B₁, d₁, h₁⟩ := hy
      obtain ⟨B₂, d₂, h₂⟩ := hz
      refine ⟨B₁ ∪ B₂, fun b => (if b ∈ B₁ then d₁ b else 0) + (if b ∈ B₂ then d₂ b else 0), ?_⟩
      rw [h₁, h₂]
      rw [show ∑ b ∈ B₁ ∪ B₂,
            ((if b ∈ B₁ then d₁ b else 0) + (if b ∈ B₂ then d₂ b else 0)) * (∏ k, t (b k))
          = ∑ b ∈ B₁ ∪ B₂,
            (((if b ∈ B₁ then d₁ b else 0) * (∏ k, t (b k)))
             + ((if b ∈ B₂ then d₂ b else 0) * (∏ k, t (b k))))
          from Finset.sum_congr rfl (fun b _ => add_mul _ _ _)]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.sum_subset (Finset.subset_union_left :
            B₁ ⊆ B₁ ∪ B₂) ?_]
        · exact Finset.sum_congr rfl (fun b hb => by rw [ite_eq_left hb])
        · intro b _ hnb
          rw [ite_eq_right hnb, zero_mul]
      · rw [← Finset.sum_subset (Finset.subset_union_right :
            B₂ ⊆ B₁ ∪ B₂) ?_]
        · exact Finset.sum_congr rfl (fun b hb => by rw [ite_eq_left hb])
        · intro b _ hnb
          rw [ite_eq_right hnb, zero_mul])
    (fun c y _ hy => by
      obtain ⟨B, d, h⟩ := hy
      refine ⟨B, fun b => c * d b, ?_⟩
      rw [smul_eq_mul, h, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by rw [mul_assoc]))
    hx

end Work.DSM5b
