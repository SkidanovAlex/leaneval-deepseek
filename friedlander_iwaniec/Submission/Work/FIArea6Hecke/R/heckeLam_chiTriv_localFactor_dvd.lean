import Mathlib
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Work.FIArea6Hecke.R.logDerivBoundAux
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.heckeLam_one

namespace Work.FIArea6Hecke.R

/-- **The local Euler factor of the Hecke `L`-series of the principal strict character at a prime
dividing the conductor is trivial.**

For `p` prime with `p ∣ 4d`, every prime ideal of `ℚ(i)` above `p` divides the modulus `(4d)`, so
the Hecke eigenvalue `λ(p^e) = ∑_{|z|²=p^e} ψ(z)` vanishes for every `e ≥ 1`: a primary `z` with
`|z|² = p^e` has norm divisible by `p`, and `p ∣ 4d` makes `gnorm z` non-coprime to `4d`, whence
`z` is not a unit modulo `4d` and `χ(z) = 0`.  Only the `e = 0` term (`λ(1) = χ(1) = 1`) survives,
so the local factor is `1`. -/
theorem heckeLam_chiTriv_localFactor_dvd {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ 4 * d) :
    ∀ s : ℂ, 1 < s.re →
      (∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 (p ^ e)
          * (((p : ℂ) ^ (-s)) ^ e)) = 1 := by
  classical
  have hne : NeZero (4 * d) := ⟨by omega⟩
  intro s hs
  -- For every `e ≥ 1` the Hecke eigenvalue `λ(p^e)` vanishes.
  have hzero : ∀ e : ℕ, e ≠ 0 →
      Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 (p ^ e) = 0 := by
    intro e he
    unfold Work.FIArea5.S16Hecke.heckeLam
    refine Finset.sum_eq_zero (fun z hz => ?_)
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hprim, hgn⟩ := hz
    rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]
    simp only [Work.FIArea6Hecke.R.chiTriv]
    rw [if_neg]
    intro hU
    -- `z` is a unit modulo `4d`, so `gnorm z = p^e` is coprime to `4d`; but `p` divides both.
    have hcop := (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime z).mp hU
    rw [hgn] at hcop
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p he) hpd) hcop
  -- Only the `e = 0` term contributes.
  rw [tsum_eq_single 0 (fun e he => ?_)]
  · rw [pow_zero, pow_zero, mul_one, Work.FIArea5.S16Hecke.heckeLam_one]
    simp only [Work.FIArea6Hecke.R.chiTriv]
    rw [if_pos (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_one (d := d))]
  · rw [hzero e he, zero_mul]

end Work.FIArea6Hecke.R
