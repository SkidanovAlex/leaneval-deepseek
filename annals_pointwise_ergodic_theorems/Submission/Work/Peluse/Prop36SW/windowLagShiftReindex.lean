import Mathlib
import Submission.Work.Peluse.Basic
import Submission.Work.Peluse.TransferUp.correlation_shift

namespace Work.Peluse.Prop36SW

theorem windowLagShiftReindex {M K : ℕ} {f : ℤ → ℂ} (hsup : Work.Peluse.SupportIn f M)
    {a b : ℤ} (ha1 : 1 ≤ a) (ha2 : a ≤ K) :
    (∑ x ∈ Work.Peluse.symIcc (M + K), f (x + a) * star (f (x + b)))
      = ∑ u ∈ Work.Peluse.symIcc M, f u * star (f (u + (b - a))) := by
  -- the shifted point `u - a` lies in the wide window whenever `u ∈ [-M,M]`
  have hmem : ∀ u : ℤ, u ∈ Work.Peluse.symIcc M → u - a ∈ Work.Peluse.symIcc (M + K) := by
    intro u hu
    simp only [Work.Peluse.symIcc, Finset.mem_Icc] at hu ⊢
    omega
  -- reindex `x ↦ x + a`
  have hA : (∑ x ∈ Work.Peluse.symIcc (M + K), f (x + a) * star (f (x + b)))
      = ∑ u ∈ (Work.Peluse.symIcc (M + K)).image (fun x => x + a),
          f u * star (f (u + (b - a))) := by
    have h1 : (∑ x ∈ Work.Peluse.symIcc (M + K), f (x + a) * star (f (x + b)))
        = ∑ x ∈ Work.Peluse.symIcc (M + K),
            (fun u : ℤ => f u * star (f (u + (b - a)))) (x + a) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      show f (x + a) * star (f (x + b)) = f (x + a) * star (f ((x + a) + (b - a)))
      rw [show (x + a) + (b - a) = x + b by ring]
    rw [h1, (Finset.sum_image (fun x _ y _ h => by omega))]
  -- drop the points of the image outside `[-M,M]`: there `f` vanishes
  have hB : (∑ u ∈ (Work.Peluse.symIcc (M + K)).image (fun x => x + a),
          f u * star (f (u + (b - a))))
      = ∑ u ∈ Work.Peluse.symIcc M, f u * star (f (u + (b - a))) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro u hu
      exact Finset.mem_image.mpr ⟨u - a, hmem u hu, by ring⟩
    · intro u _ hnu
      have hM : M < u.natAbs := by
        simp only [Work.Peluse.symIcc, Finset.mem_Icc] at hnu
        by_contra hcon
        have hcon' : u.natAbs ≤ M := not_lt.mp hcon
        apply hnu
        have hle : |u| ≤ (M : ℤ) := by
          have : ((u.natAbs : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast hcon'
          rwa [Int.natCast_natAbs] at this
        exact abs_le.mp hle
      rw [hsup u hM, zero_mul]
  rw [hA, hB]

end Work.Peluse.Prop36SW
