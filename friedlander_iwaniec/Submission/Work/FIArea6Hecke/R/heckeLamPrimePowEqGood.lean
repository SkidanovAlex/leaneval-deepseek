import Mathlib
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core

namespace Work.FIArea6Hecke.R

/-- **Local equality of a strict character and its conductor partner at good prime powers.**

For a rational prime `p ∤ 4d` and any exponent `e`, the Hecke eigenvalue `λ(p^e)` attached to a
strict character `χ` mod `4d` agrees with the one attached to its primitive conductor partner
`χ₀`.  Indeed, every primary `z` of norm `p^e` has `(|z|², 4d) = 1`, hence is a unit modulo `4d`,
where `χ` and `χ₀` agree by construction; the sums defining `λ` are therefore termwise equal. -/
theorem heckeLamPrimePowEqGood (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (M : GaussianInt)
    (chi₀ : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hpart : Work.FIArea6Hecke.R.IsConductorPartner d chi M chi₀)
    (p : ℕ) (hp : p.Prime) (hpd : ¬ p ∣ 4 * d) (e : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam chi m (p ^ e)
      = Work.FIArea5.S16Hecke.heckeLam chi₀ m (p ^ e) := by
  classical
  unfold Work.FIArea5.S16Hecke.heckeLam
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.mem_filter] at hz
  obtain ⟨-, hzprim, hzgn⟩ := hz
  have hN : NeZero (4 * d) := ⟨by omega⟩
  have hzu : Work.FIArea5.S16Hecke.IsUnitMod4d d z := by
    rw [Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime (d := d) z, hzgn]
    exact (hp.coprime_iff_not_dvd.mpr hpd).pow_left e
  have hzchi : chi₀ z = chi z := hpart.2.2.2.2.2.2.2 z hzprim hzu
  simp only [Work.FIArea5.S16Hecke.psi, hzchi]

end Work.FIArea6Hecke.R
