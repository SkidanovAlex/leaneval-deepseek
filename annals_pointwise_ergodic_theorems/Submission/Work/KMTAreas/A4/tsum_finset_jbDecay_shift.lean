import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

theorem tsum_finset_jbDecay_shift (s : Finset ℕ) {ε : ℝ} (hε0 : 0 < ε) :
    ∑' m : ℤ, ∑ y ∈ s, ε * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ)))
      = (s.card : ℝ) * (ε * ∑' u : ℤ, Work.Analysis.InverseTheory.jbDecay 12 (ε * (u : ℝ))) := by
  classical
  have hsumm : ∀ y : ℕ, Summable (fun m : ℤ => ε * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ)))) :=
    fun y => (summable_jbDecay_twelve_shift hε0 (y:ℤ)).mul_left ε
  have hreindex : ∀ y : ℕ, (∑' m : ℤ, jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))))
      = ∑' u : ℤ, jbDecay 12 (ε * (u:ℝ)) := by
    intro y
    rw [← Equiv.tsum_eq (Equiv.subRight (y:ℤ)) (fun u : ℤ => jbDecay 12 (ε * (u:ℝ)))]
    refine tsum_congr fun m => ?_
    have h : ε * (((Equiv.subRight (y:ℤ)) m : ℤ) : ℝ) = ε * ((m:ℝ) - (y:ℝ)) := by
      rw [Equiv.subRight_apply]
      push_cast
      ring
    rw [h]
  rw [Summable.tsum_finsetSum (fun y _ => hsumm y)]
  have h1 : ∑ y ∈ s, (∑' m : ℤ, ε * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))))
      = ∑ y ∈ s, (ε * ∑' u : ℤ, jbDecay 12 (ε * (u:ℝ))) := by
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [tsum_mul_left, hreindex y]
  rw [h1, Finset.sum_const, nsmul_eq_mul]

end Work.KMTAreas.A4
