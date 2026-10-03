import Mathlib
import Submission.Work.Peluse.TransferUp.window_pair_sum
import Submission.Work.Peluse.TransferUp.correlation_shift
import Submission.Work.Peluse.TransferUp.support_shift_vanishes

namespace Work.Peluse.TransferUp

private def winSum (c : ℤ) (H : ℕ) (G : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H, G (x + c * (n : ℤ))

private noncomputable def corr (c : ℤ) (G : ℤ → ℂ) (e : ℤ) : ℂ :=
  ∑' x : ℤ, G x * star (G (x + c * e))

theorem windowSum_sq_eq_corr {H : ℕ} (c : ℤ) {G : ℤ → ℂ} (hG : Work.Peluse.FinSuppZ G) :
    (∑' x : ℤ, ‖∑ n ∈ Finset.Icc 1 H, G (x + c * (n : ℤ))‖ ^ 2)
      = ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((H - e.natAbs : ℕ)) : ℝ) * (∑' x : ℤ, G x * star (G (x + c * e))) := by
  classical
  change ((∑' x : ℤ, ‖winSum c H G x‖ ^ 2 : ℝ) : ℂ)
      = ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((H - e.natAbs : ℕ)) : ℝ) * corr c G e
  obtain ⟨N, hN⟩ := hG
  set K : ℕ := N + c.natAbs * H with hK
  have hmem : ∀ x : ℤ, x ∈ symIcc K ↔ x.natAbs ≤ K := by
    intro x
    rw [symIcc, Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs]
    exact Int.ofNat_le
  have hlt : ∀ x : ℤ, x ∉ symIcc K → K < x.natAbs := by
    intro x hx
    by_contra hcon
    exact hx ((hmem x).mpr (not_lt.mp hcon))
  have hvan : ∀ x : ℤ, K < x.natAbs → ∀ n ∈ Finset.Icc 1 H, G (x + c * (n:ℤ)) = 0 := by
    intro x hx n hn
    exact support_shift_vanishes (N := N) (H := H) c hN x (by rw [← hK]; exact hx) n hn
  have hL : ((∑' x : ℤ, ‖winSum c H G x‖ ^ 2 : ℝ) : ℂ)
      = ∑' x : ℤ, winSum c H G x * star (winSum c H G x) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun x => ?_)
    rw [Complex.sq_norm]
    exact (Complex.mul_conj _).symm
  rw [hL]
  have hmain : (∑' x : ℤ, winSum c H G x * star (winSum c H G x))
      = ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((H - e.natAbs : ℕ)) : ℂ) * corr c G e := by
    have s1 : (∑' x : ℤ, winSum c H G x * star (winSum c H G x))
        = ∑ b ∈ symIcc K, winSum c H G b * star (winSum c H G b) := by
      refine tsum_eq_sum (s := symIcc K) (fun b hb => ?_)
      have hb0 : winSum c H G b = 0 := by
        simp only [winSum]
        exact Finset.sum_eq_zero (fun n hn => hvan b (hlt b hb) n hn)
      rw [hb0, star_zero, mul_zero]
    have s2 : (∑ b ∈ symIcc K, winSum c H G b * star (winSum c H G b))
        = ∑ b ∈ symIcc K, ∑ n ∈ Finset.Icc 1 H, ∑ m ∈ Finset.Icc 1 H,
            G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp only [winSum]
      rw [star_sum, Finset.sum_mul_sum]
    have s3 : (∑ b ∈ symIcc K, ∑ n ∈ Finset.Icc 1 H, ∑ m ∈ Finset.Icc 1 H,
            G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))))
        = ∑ n ∈ Finset.Icc 1 H, ∑ m ∈ Finset.Icc 1 H, ∑ b ∈ symIcc K,
            G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
    have hback : ∀ n ∈ Finset.Icc 1 H, ∀ m ∈ Finset.Icc 1 H,
        (∑ b ∈ symIcc K, G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))))
          = ∑' b : ℤ, G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))) := by
      intro n hn m hm
      exact (tsum_eq_sum (s := symIcc K) (fun b hb => by
        rw [hvan b (hlt b hb) n hn, hvan b (hlt b hb) m hm]
        simp)).symm
    have s4 : (∑ n ∈ Finset.Icc 1 H, ∑ m ∈ Finset.Icc 1 H, ∑ b ∈ symIcc K,
            G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))))
        = ∑ n ∈ Finset.Icc 1 H, ∑ m ∈ Finset.Icc 1 H,
            ∑' b : ℤ, G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))) := by
      refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => hback n hn m hm))
    have hcorr : ∀ n ∈ Finset.Icc 1 H, ∀ m ∈ Finset.Icc 1 H,
        (∑' b : ℤ, G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))))
          = corr c G ((m:ℤ) - (n:ℤ)) := by
      intro n hn m hm
      have h1 := correlation_shift (c * (n:ℤ)) (c * (m:ℤ)) G
      have h2 : (∑' x : ℤ, G x * star (G (x + (c * (m:ℤ) - c * (n:ℤ)))))
          = ∑' x : ℤ, G x * star (G (x + c * ((m:ℤ) - (n:ℤ)))) := by
        refine tsum_congr (fun x => ?_)
        rw [show c * (m:ℤ) - c * (n:ℤ) = c * ((m:ℤ) - (n:ℤ)) from by ring]
      exact h1.trans h2
    have s5 : (∑ n ∈ Finset.Icc 1 H, ∑ m ∈ Finset.Icc 1 H,
            ∑' b : ℤ, G (b + c * (n:ℤ)) * star (G (b + c * (m:ℤ))))
        = ∑ n ∈ Finset.Icc 1 H, ∑ m ∈ Finset.Icc 1 H, corr c G ((m:ℤ) - (n:ℤ)) := by
      refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => hcorr n hn m hm))
    have s6 : (∑ n ∈ Finset.Icc 1 H, ∑ m ∈ Finset.Icc 1 H, corr c G ((m:ℤ) - (n:ℤ)))
        = ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
            (((H - e.natAbs : ℕ)) : ℂ) * corr c G e :=
      window_pair_sum H (corr c G)
    exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))
  rw [hmain]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Complex.ofReal_natCast]

end Work.Peluse.TransferUp
