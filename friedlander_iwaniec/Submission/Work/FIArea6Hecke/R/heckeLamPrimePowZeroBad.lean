import Mathlib
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core

namespace Work.FIArea6Hecke.R

/-- **Vanishing of the Hecke eigenvalue at prime powers dividing the conductor.**

Let `χ` be a character modulo `4d` vanishing off the units (a *strict* character), `p` a rational
prime dividing `4d` and `e ≥ 1`.  Then `λ(p^e) = 0`.

Indeed, every Gaussian integer `z` of norm `p^e` has `gnorm z` divisible by `p`, and since `p ∣ 4d`
the norm `gnorm z` is *not* coprime to `4d`; by the residue-ring unit criterion
(`GaussUnit.isUnitMod4d_iff_coprime`) such a `z` is therefore not a unit modulo `4d`, so the strict
character satisfies `χ(z) = 0`, and each term `ψ(z) = χ(z)(z/|z|)^m` of the defining sum of `λ`
vanishes. -/
theorem heckeLamPrimePowZeroBad (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (p : ℕ) (hp : p.Prime) (hpd : p ∣ 4 * d) (e : ℕ) (he : 1 ≤ e) :
    Work.FIArea5.S16Hecke.heckeLam chi m (p ^ e) = 0 := by
  classical
  haveI : NeZero (4 * d) := ⟨by omega⟩
  unfold Work.FIArea5.S16Hecke.heckeLam
  refine Finset.sum_eq_zero (fun z hz => ?_)
  rw [Finset.mem_filter] at hz
  obtain ⟨-, _hzprim, hzgn⟩ := hz
  -- `z` of norm `p ^ e` is not a unit modulo `4d` when `p ∣ 4d` and `e ≥ 1`.
  have hnotu : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d z := by
    intro hU
    have hcop := (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime (d := d) z).mp hU
    rw [hzgn] at hcop
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p (by omega)) hpd) hcop
  rw [Work.FIArea5.S16Hecke.psi, hchi.2 z hnotu, zero_mul]

end Work.FIArea6Hecke.R
