import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.pinComplex
import Submission.Work.Drive.N2Lead.polarArc_eq_sqrt

namespace Work.Drive.N2Lead

theorem mobiusPolarArcDn {ηs : ℝ} (hηs : 0 < ηs) (w : ℝ) :
    let θ : ℝ := 3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs)
    Real.sqrt (ηs / -Real.cos (2 * θ)) * Complex.exp ((θ : ℂ) * Complex.I)
      = star (Work.Drive.N2Lead.arcZ ηs w) := by
  show Real.sqrt (ηs / -Real.cos (2 * (3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs))))
      * Complex.exp (((3 * Real.pi / 2 + (1 / 2) * Real.arctan (w / ηs) : ℝ) : ℂ)
          * Complex.I)
      = star (Work.Drive.N2Lead.arcZ ηs w)
  set t : ℝ := Real.arctan (w / ηs) with ht
  set θ : ℝ := 3 * Real.pi / 2 + (1 / 2) * t with hθ
  set φU : ℝ := Real.pi / 2 - (1 / 2) * Real.arctan ((-w) / ηs) with hφU
  -- the polar parametrisation of the upper arc, applied at `-w`
  have hmain : Real.sqrt (ηs / -Real.cos (2 * φU)) * Complex.exp ((φU : ℂ) * Complex.I)
      = Complex.I * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I) := by
    obtain ⟨h1, -⟩ := polarArc_eq_sqrt hηs (-w)
    have harg : ((ηs : ℂ) - (((-w : ℝ)) : ℂ) * Complex.I)
        = (ηs : ℂ) + (w : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg] at h1
    exact h1
  have hRHS : star (Work.Drive.N2Lead.arcZ ηs w)
      = -(Complex.I * Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I)) := by
    have hconj : star (Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I))
        = Complex.sqrt ((ηs : ℂ) + (w : ℂ) * Complex.I) := by
      have h := conj_sqrt_ofReal_add_mul_I hηs.le (-w)
      simpa [Complex.star_def, Complex.ofReal_neg, neg_mul, sub_neg_eq_add, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using h
    have hI : star (Complex.I) = -Complex.I := by
      simpa [Complex.star_def] using Complex.conj_I
    rw [Work.Drive.N2Lead.arcZ, star_mul, hconj, hI]
    ring
  rw [hRHS]
  -- reduce to the polar identity at `-w`
  have harctan : Real.arctan ((-w) / ηs) = -t := by
    rw [ht, show (-w) / ηs = -(w / ηs) by ring, Real.arctan_neg]
  have hφval : φU = θ - Real.pi := by
    rw [hφU, hθ, harctan]; ring
  have hcos2 : Real.cos (2 * θ) = Real.cos (2 * φU) := by
    have h2 : 2 * θ = 2 * φU + 2 * Real.pi := by rw [hφval]; ring
    rw [h2, Real.cos_add_two_pi]
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) = -Complex.exp ((φU : ℂ) * Complex.I) := by
    have h2 : (θ : ℂ) = (φU : ℂ) + (Real.pi : ℂ) := by rw [hφval]; push_cast; ring
    rw [h2]
    have h3 : ((φU : ℂ) + (Real.pi : ℂ)) * Complex.I
        = (φU : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by ring
    rw [h3, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hcos2, hexp, mul_neg, hmain]

end Work.Drive.N2Lead
