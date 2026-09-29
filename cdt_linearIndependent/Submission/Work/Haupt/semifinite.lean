import Mathlib
import Submission.Work.Haupt.qp_defs
import Submission.Work.Haupt.sf_aux
import Submission.Work.Haupt.sf_helpers
import Submission.Work.Haupt.sfTerm_shift
import Submission.Work.Haupt.qpInf_shift_mul
import Submission.Work.Haupt.semifinite_zero

namespace Work.Haupt

open scoped BigOperators
open Filter Topology

theorem semifinite {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) (m : ℕ)
    (hE : ∀ w : ℂ, ∏' n : ℕ, (1 + w * q ^ n) = ∑' n : ℕ, qhalf q n * w ^ n / qpNat q q n) :
    (∑' n : ℤ, sfTerm q z m n) = qpNat q q m * qpNat (-q/z) q m * qpInf (-z) q := by
  rcases eq_or_ne q 0 with hqzero | hq0
  · subst hqzero
    exact semifinite_zero z hz m
  · -- the q ≠ 0 case
    have hterm : ∀ N : ℕ, sfTerm q z m ((N:ℤ) - m)
        = (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ)))
            * (qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N) := by
      intro N; exact sfTerm_shift hq0 hq hz m N
    -- vanishing of the far negative terms
    have hzero : ∀ n : ℤ, n < -(m:ℤ) → sfTerm q z m n = 0 := by
      intro n hn
      rcases n with j | k
      · exfalso
        have h1 : (0:ℤ) ≤ (j:ℤ) := Int.natCast_nonneg j
        have h2 : (j:ℤ) < 0 := lt_of_lt_of_le hn (by simp)
        exact (not_lt.mpr h1) h2
      · have hk : m + 1 ≤ k + 1 := by
          rw [Int.negSucc_eq] at hn
          omega
        have he : (Int.negSucc k) = (-((k+1 : ℕ) : ℤ)) := by
          rw [Int.negSucc_eq]; push_cast; ring
        rw [he]
        exact sfTerm_neg_eq_zero hq (m := m) (k := k+1) hk
    -- the reindexing `n = N - m`
    have hbij : (∑' n : ℤ, sfTerm q z m n)
        = ∑' N : ℕ, (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ)))
            * (qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N) := by
      refine tsum_eq_tsum_of_ne_zero_bij
        (f := fun n : ℤ => sfTerm q z m n)
        (g := fun N : ℕ => (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ)))
            * (qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N))
        (fun x : ↑(Function.support (fun N : ℕ => (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ)))
            * (qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N))) =>
              (((x : ℕ)) : ℤ) - (m : ℤ)) ?_ ?_ ?_
      · intro x y hxy
        have hxy' : (((x:ℕ)) : ℤ) - (m:ℤ) = (((y:ℕ)) : ℤ) - (m:ℤ) := hxy
        have h' : (((x:ℕ)) : ℤ) = (((y:ℕ)) : ℤ) := by
          have h2 := congrArg (fun t : ℤ => t + (m:ℤ)) hxy'
          rwa [sub_add_cancel, sub_add_cancel] at h2
        exact Subtype.ext (Int.ofNat_inj.mp h')
      · intro n hn
        have hn0 : sfTerm q z m n ≠ 0 := Function.mem_support.mp hn
        have hnge : -(m:ℤ) ≤ n := by
          by_contra hlt
          exact hn0 (hzero n (lt_of_not_ge hlt))
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ((N:ℤ)) = n + (m:ℤ) :=
          ⟨(n + (m:ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩
        have hgne : (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ)))
            * (qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N) ≠ 0 := by
          refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
          · exact qpNat_self_ne_zero hq m
          · exact qhalf_ne_zero hq0 (m+1)
          · exact zpow_ne_zero _ hz
          · refine div_ne_zero (mul_ne_zero (qhalf_ne_zero hq0 N) ?_) ?_
            · exact pow_ne_zero _ (mul_ne_zero (zpow_ne_zero _ hq0) hz)
            · exact qpNat_self_ne_zero hq N
        refine ⟨⟨N, Function.mem_support.mpr hgne⟩, ?_⟩
        show ((N:ℤ)) - (m:ℤ) = n
        omega
      · intro x
        exact hterm (x : ℕ)
    have hsumh : (∑' N : ℕ, qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N)
        = qpInf (-(q^(-(m:ℤ)) * z)) q := by
      simpa [qpInf] using (hE (q^(-(m:ℤ)) * z)).symm
    calc (∑' n : ℤ, sfTerm q z m n)
        = ∑' N : ℕ, (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ)))
            * (qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N) := hbij
      _ = (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ)))
            * (∑' N : ℕ, qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N) := tsum_mul_left
      _ = (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ))) * qpInf (-(q^(-(m:ℤ)) * z)) q := by
            rw [hsumh]
      _ = qpNat q q m * qpNat (-q/z) q m * qpInf (-z) q := by
            rw [show (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ))) * qpInf (-(q^(-(m:ℤ)) * z)) q
                 = qpNat q q m * (qhalf q (m+1) * z^(-(m:ℤ))
                     * qpInf (-(q^(-(m:ℤ)) * z)) q) from by ring,
                qpInf_shift_mul hq0 hq hz m, mul_assoc]

end Work.Haupt
