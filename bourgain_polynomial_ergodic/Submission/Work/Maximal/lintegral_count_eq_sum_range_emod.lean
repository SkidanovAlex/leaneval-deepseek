import Mathlib
import Submission.Work.Maximal.mstWideLat_defs

namespace Work.Maximal

/-- The residue-class decomposition of a `tsum` over `ℤ`: every integer is uniquely
`Q * x + m` with `m ∈ {0, …, Q-1}`, so summing over `ℤ` is the same as summing over the
residue classes `m` and then over the quotients `x`.  The bijection used is the Euclidean
division `Int.divModEquiv`, `(x, m) ↦ x * Q + m`. -/
lemma tsum_int_eq_sum_range_emod (Q : ℕ) [NeZero Q] (G : ℤ → ENNReal) :
    ∑' n : ℤ, G n = ∑ m ∈ Finset.range Q, ∑' x : ℤ, G ((Q : ℤ) * x + (m : ℤ)) := by
  have hsymm : ∀ t : ℤ × Fin Q, (Int.divModEquiv Q).symm t = t.1 * (Q : ℤ) + (t.2 : ℤ) :=
    fun t => Int.divModEquiv_symm_apply Q t
  symm
  calc ∑ m ∈ Finset.range Q, (∑' x : ℤ, G ((Q : ℤ) * x + (m : ℤ)))
      = ∑' m : Fin Q, ∑' x : ℤ, G ((Q : ℤ) * (x : ℤ) + ((m : ℕ) : ℤ)) := by
        rw [tsum_fintype (f := fun m : Fin Q => ∑' x : ℤ, G ((Q : ℤ) * (x : ℤ) + ((m : ℕ) : ℤ)))]
        exact (Fin.sum_univ_eq_sum_range
          (fun m : ℕ => ∑' x : ℤ, G ((Q : ℤ) * (x : ℤ) + (m : ℤ))) Q).symm
    _ = ∑' m : Fin Q, ∑' x : ℤ, G ((x : ℤ) * (Q : ℤ) + ((m : ℕ) : ℤ)) := by
        refine tsum_congr (fun m => tsum_congr (fun x => ?_))
        rw [mul_comm (x : ℤ) (Q : ℤ)]
    _ = ∑' t : ℤ × Fin Q, G (t.1 * (Q : ℤ) + (t.2 : ℤ)) :=
        ((ENNReal.tsum_prod' (f := fun t : ℤ × Fin Q => G (t.1 * (Q : ℤ) + (t.2 : ℤ)))).trans
          (ENNReal.tsum_comm
            (f := fun x : ℤ => fun m : Fin Q => G (x * (Q : ℤ) + (m : ℤ))))).symm
    _ = ∑' n : ℤ, G n := by
        rw [← Equiv.tsum_eq (Int.divModEquiv Q).symm G]
        exact tsum_congr fun t => by rw [hsymm t]

theorem lintegral_count_eq_sum_range_emod {Q : ℕ} (hQ : 0 < Q) (F : ℤ → ENNReal) :
    ∫⁻ n : ℤ, F n ∂MeasureTheory.Measure.count
      = ∑ m ∈ Finset.range Q,
          ∫⁻ x : ℤ, F ((Q : ℤ) * x + (m : ℤ)) ∂MeasureTheory.Measure.count := by
  simp_rw [MeasureTheory.lintegral_count]
  exact @tsum_int_eq_sum_range_emod Q ⟨ne_of_gt hQ⟩ F

end Work.Maximal
