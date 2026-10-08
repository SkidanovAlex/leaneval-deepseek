import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.Counting

/-!
## §4 (11): the number of subgroups of order `r` in `L₂(q)`

`hcount` (`Work.GW2.L2PrimeSubgroupCountProp`) says that for an odd prime `r ≠ p` with
`r ∣ (q + ε)/2` (`ε = ±1`, `q = pF ^ kF`) the number of subgroups of `PSL(2, GF pF kF)` of
order `r` equals `q (q - ε) / 2`, i.e. in integer form `2 N = q (q - ε)`.

Here `k` and `k'` are the even and odd halves of `q ∓ 1` (`2k = q + 1`, `2k' = q - 1`, or the
other way round).  Since `r ∣ k`, the hypothesis `r ∣ (q + ε)/2` holds with `ε` the sign that
makes `(q + ε)/2 = k`, and `q - ε = 2 k'`.  Cancelling the factor `2` gives `N = q k'`.
-/

theorem PrimeCount (hcount : Work.GW2.L2PrimeSubgroupCountProp)
    (pF kF k k' r : ℕ) [Fact pF.Prime]
    (hodd : Odd pF) (hq5 : 5 ≤ pF ^ kF)
    (hk : Even k) (hk' : Odd k')
    (hdisj : (2 * k = pF ^ kF + 1 ∧ 2 * k' = pF ^ kF - 1) ∨
             (2 * k = pF ^ kF - 1 ∧ 2 * k' = pF ^ kF + 1))
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ pF) (hrk : r ∣ k) :
    {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) | Nat.card Y = r}.ncard = pF ^ kF * k' := by
  classical
  have hq1 : 1 ≤ pF ^ kF := le_trans (by norm_num) hq5
  have hdvdk : (r : ℤ) ∣ (k : ℤ) := Int.ofNat_dvd.mpr hrk
  have hcast : ((pF ^ kF - 1 : ℕ) : ℤ) = ((pF ^ kF : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub hq1]; norm_num
  rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `2k = q + 1`, `2k' = q - 1`, `ε = 1`
    have hq : ((pF ^ kF : ℕ) : ℤ) + 1 = 2 * (k : ℤ) := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) h1
      push_cast at h
      rw [← Nat.cast_pow] at h
      linarith
    have hq' : ((pF ^ kF : ℕ) : ℤ) - 1 = 2 * (k' : ℤ) := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) h2
      push_cast at h
      rw [hcast] at h
      linarith
    have hdvd : (r : ℤ) ∣ ((pF ^ kF : ℕ) + (1 : ℤ)) / 2 := by
      have hdiv : ((pF ^ kF : ℕ) + (1 : ℤ)) / 2 = (k : ℤ) := by
        rw [hq, Int.mul_ediv_cancel_left (k : ℤ) (by norm_num : (2 : ℤ) ≠ 0)]
      rw [hdiv]; exact hdvdk
    have hc := hcount pF kF hodd hq5 r hr hr2 hrp (1 : ℤ) (Or.inl rfl) hdvd
    have hmain :
        ({Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) |
            Nat.card Y = r}.ncard : ℤ) = ((pF ^ kF * k' : ℕ) : ℤ) := by
      have h2eq : 2 * ({Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) |
            Nat.card Y = r}.ncard : ℤ) = 2 * ((pF ^ kF * k' : ℕ) : ℤ) := by
        rw [hc, hq']
        push_cast
        ring
      linarith
    exact_mod_cast hmain
  · -- `2k = q - 1`, `2k' = q + 1`, `ε = -1`
    have hq : ((pF ^ kF : ℕ) : ℤ) - 1 = 2 * (k : ℤ) := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) h1
      push_cast at h
      rw [hcast] at h
      linarith
    have hq' : ((pF ^ kF : ℕ) : ℤ) + 1 = 2 * (k' : ℤ) := by
      have h := congrArg (fun n : ℕ => (n : ℤ)) h2
      push_cast at h
      rw [← Nat.cast_pow] at h
      linarith
    have hdvd : (r : ℤ) ∣ ((pF ^ kF : ℕ) + (-1 : ℤ)) / 2 := by
      have hdiv : ((pF ^ kF : ℕ) + (-1 : ℤ)) / 2 = (k : ℤ) := by
        have hh : ((pF ^ kF : ℕ) + (-1 : ℤ)) = ((pF ^ kF : ℕ) : ℤ) - 1 := by ring
        rw [hh, hq, Int.mul_ediv_cancel_left (k : ℤ) (by norm_num : (2 : ℤ) ≠ 0)]
      rw [hdiv]; exact hdvdk
    have hc := hcount pF kF hodd hq5 r hr hr2 hrp (-1 : ℤ) (Or.inr rfl) hdvd
    have hmain :
        ({Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) |
            Nat.card Y = r}.ncard : ℤ) = ((pF ^ kF * k' : ℕ) : ℤ) := by
      have h2eq : 2 * ({Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) |
            Nat.card Y = r}.ncard : ℤ) = 2 * ((pF ^ kF * k' : ℕ) : ℤ) := by
        rw [hc]
        have hh : ((pF ^ kF : ℕ) : ℤ) - (-1) = ((pF ^ kF : ℕ) : ℤ) + 1 := by ring
        rw [hh, hq']
        push_cast
        ring
      linarith
    exact_mod_cast hmain

end Work.CORE4.Counting
