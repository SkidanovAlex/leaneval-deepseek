import Mathlib
import Submission.Work.FIArea4.Vflip.KK_eq_tsum_gm
import Submission.Work.FIArea4.WdyadDefs2
import Submission.Work.FIArea4.Wdyad_expansion
import Submission.Work.FIArea4.WdyadPoisson
import Submission.Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow

namespace Work.FIArea4.Vflip

open scoped FourierTransform BigOperators
open Finset

noncomputable section

/-- Summability of `𝓕 F (k/q) * z k` for a multiplier `z` bounded by `1`, when `𝓕 F` decays like
`|x| ^ (-b)` with `b > 1`. -/
lemma summable_fourier_mul {F : ℝ → ℂ} {b : ℝ} (hb : 1 < b)
    (hF' : (FourierTransform.fourier F) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (q : ℕ) (hq : 0 < q) (z : ℤ → ℂ) (hz : ∀ k, ‖z k‖ ≤ 1) :
    Summable (fun k : ℤ => FourierTransform.fourier F ((k:ℝ)/(q:ℝ)) * z k) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hsum : Summable (fun k : ℤ => FourierTransform.fourier F ((k:ℝ)/(q:ℝ))) :=
    Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow hb hF' hqR
  have hnorm : Summable (fun k : ℤ => ‖FourierTransform.fourier F ((k:ℝ)/(q:ℝ))‖) := hsum.norm
  refine Summable.of_norm_bounded (g := fun k : ℤ => ‖FourierTransform.fourier F ((k:ℝ)/(q:ℝ))‖) ?_ ?_
  · simpa using hnorm
  · intro k
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hz k)

/-- The main identity, for a general `F` with decay `|x|^(-b)`, `b > 1`: the local kernel `KK`
of the dyadic dual form, with `F` replaced by its Fourier transform, equals the sum over the
arithmetic progressions `r a + [d₁,d₂]ℤ`. -/
theorem KK_eq_tsum_gen (F : ℝ → ℂ) (hcont : Continuous F) {b : ℝ} (hb : 1 < b)
    (hF : F =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (hF' : (FourierTransform.fourier F) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (R S d1 d2 a : ℕ) (hS : 1 ≤ S) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (hflat : ∃ m : ℕ, Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 = m ^ 2) :
    Work.FIArea4.KK (FourierTransform.fourier F) R d1 d2 a
      = ∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
          ∑' m : ℤ, F ((r * a : ℝ) + (m : ℝ) * (Nat.lcm d1 d2 : ℝ)) := by
  unfold Work.FIArea4.KK
  set q : ℕ := Nat.lcm d1 d2 with hq
  have hqpos : 0 < q := by rw [hq]; exact Nat.lcm_pos (by omega) (by omega)
  -- Poisson step, for a general shift `c`
  have hPoi : ∀ r : ℕ,
      (1 / (q:ℝ)) * ∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
        * Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) / (q:ℝ))
      = ∑' m : ℤ, F ((r:ℝ)*(a:ℝ) + (m:ℝ)*(q:ℝ)) := by
    intro r
    have hmain := poisson_residue F hcont hb hF hF' q hqpos ((r:ℝ)*(a:ℝ))
    have hmain2 : (∑' m : ℤ, F ((r:ℝ)*(a:ℝ) + (m:ℝ)*(q:ℝ)))
        = (1 / (q:ℝ)) * ∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
            * Complex.exp (2 * Real.pi * Complex.I * ((((r:ℝ)*(a:ℝ)) : ℝ) : ℂ) * (k:ℝ) / (q:ℝ)) := by
      have h2 : (∑' m : ℤ, F ((r:ℝ)*(a:ℝ) + ((m * (q:ℤ) : ℤ) : ℝ)))
          = ∑' m : ℤ, F ((r:ℝ)*(a:ℝ) + (m:ℝ)*(q:ℝ)) := by
        apply tsum_congr; intro m; congr 1; push_cast; ring
      rw [← h2, hmain]
    rw [hmain2]
    congr 1
    apply tsum_congr; intro k
    congr 1
    congr 1
    push_cast; ring
  simp only [wChar_eq_ite d1 d2 hflat]
  let Ef : ℕ → ℤ → ℂ := fun r k => Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) / (q:ℝ))
  change 1 / (q:ℝ) * ∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
          * (∑ r ∈ Finset.Ioc R (2*R), (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0) * Ef r k)
      = ∑ r ∈ Finset.Ioc R (2*R) with r.Coprime (d1*d2),
          ∑' m : ℤ, F ((r:ℝ)*(a:ℝ) + (m:ℝ)*(q:ℝ))
  have hswap : (∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
        * (∑ r ∈ Finset.Ioc R (2*R), (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0) * Ef r k))
      = ∑ r ∈ Finset.Ioc R (2*R), (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0)
        * (∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ)) * Ef r k) := by
    have hsum : ∀ r ∈ Finset.Ioc R (2*R), Summable (fun k : ℤ =>
        FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
          * ((if Nat.Coprime r (d1*d2) then (1:ℂ) else 0) * Ef r k)) := by
      intro r hr
      refine summable_fourier_mul hb hF' q hqpos _ (fun k => ?_)
      have hEfv : Ef r k = Complex.exp (2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) / (q:ℝ)) := rfl
      rw [hEfv, norm_mul, norm_exp_unit r a q k, mul_one]
      by_cases h : Nat.Coprime r (d1*d2)
      · rw [if_pos h]; norm_num
      · rw [if_neg h]; norm_num
    rw [show (∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
          * (∑ r ∈ Finset.Ioc R (2*R), (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0) * Ef r k))
        = ∑' k : ℤ, ∑ r ∈ Finset.Ioc R (2*R),
            FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
          * ((if Nat.Coprime r (d1*d2) then (1:ℂ) else 0) * Ef r k) from by
      apply tsum_congr; intro k
      rw [Finset.mul_sum]]
    rw [Summable.tsum_finsetSum (f := fun r (k : ℤ) =>
        FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
          * ((if Nat.Coprime r (d1*d2) then (1:ℂ) else 0) * Ef r k)) hsum]
    apply Finset.sum_congr rfl; intro r hr
    rw [show (∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ))
          * ((if Nat.Coprime r (d1*d2) then (1:ℂ) else 0) * Ef r k))
        = ∑' k : ℤ, (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0)
          * (FourierTransform.fourier F ((k:ℝ)/(q:ℝ)) * Ef r k) from by
      apply tsum_congr; intro k; ring]
    rw [tsum_mul_left]
  rw [hswap, Finset.mul_sum]
  rw [show (∑ r ∈ Finset.Ioc R (2*R), 1 / (q:ℝ) * ((if Nat.Coprime r (d1*d2) then (1:ℂ) else 0)
        * (∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ)) * Ef r k)))
      = ∑ r ∈ Finset.Ioc R (2*R), (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0)
        * (1 / (q:ℝ) * (∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ)) * Ef r k)) from by
      apply Finset.sum_congr rfl; intro r hr; ring]
  rw [show (∑ r ∈ Finset.Ioc R (2*R), (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0)
        * (1 / (q:ℝ) * (∑' k : ℤ, FourierTransform.fourier F ((k:ℝ)/(q:ℝ)) * Ef r k)))
      = ∑ r ∈ Finset.Ioc R (2*R), (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0)
        * (∑' m : ℤ, F ((r:ℝ)*(a:ℝ) + (m:ℝ)*(q:ℝ))) from by
      apply Finset.sum_congr rfl; intro r hr
      rw [hPoi r]]
  rw [show (∑ r ∈ Finset.Ioc R (2*R), (if Nat.Coprime r (d1*d2) then (1:ℂ) else 0)
        * (∑' m : ℤ, F ((r:ℝ)*(a:ℝ) + (m:ℝ)*(q:ℝ))))
      = ∑ r ∈ Finset.Ioc R (2*R) with r.Coprime (d1*d2),
          ∑' m : ℤ, F ((r:ℝ)*(a:ℝ) + (m:ℝ)*(q:ℝ)) from by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro r hr
      by_cases h : Nat.Coprime r (d1*d2)
      · rw [if_pos h, if_pos h, one_mul]
      · rw [if_neg h, if_neg h, zero_mul]]

end

end Work.FIArea4.Vflip
