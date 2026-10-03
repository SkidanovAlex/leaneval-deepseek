import Mathlib
import Submission.Work.FIArea4.WdyadDefs2
import Submission.Work.FIArea4.Wdyad_expansion
import Submission.Work.FIArea4.WdyadSetup
import Submission.Work.FIArea4.Wdyad_le_majorant
import Submission.Work.FIArea4.WdyadBilinearDefs
import Submission.Work.FIArea4.WdyadPoisson
import Submission.Work.FIArea4.Wdyad_Expo_bilinear
import Submission.Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators FourierTransform

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The bilinear form of the dyadic dual variance with an arbitrary majorant

`Work.FIArea4.Wdyad_bilinear` bounds the dyadic dual variance `Wdyad D R S γ` by the bilinear form
with kernel `KK (𝓕 (gmajorC S))`, for the specific Gaussian majorant `gmajorC S`.

Here we replace the Gaussian by an arbitrary continuous function `F` whose Fourier transform decays
like `|x| ^ (-b)`, `b > 1`, which is real and nonnegative and which dominates `1` on the interval
`(S, 2S]`.  The two mathematical inputs are exactly as in `Wdyad_bilinear`:

* the majorant bound `Wdyad D R S γ ≤ ∑_r ∑'_s (F s).re · ‖TZ r s‖²` (`Wdyad_le_majorant_gen`),
* the Poisson expansion of `TZ` (`Wdyad_expansion`) followed by an exchange of summation
  (`ExpoGen_bilinear`, a kernel-agnostic version of `Wdyad_Expo_bilinear`).
-/

/-! ## The Poisson-expanded class sum for an arbitrary kernel -/

/-- `Work.FIArea4.Expo` with the Fourier transform of the Gaussian majorant replaced by an
arbitrary kernel `G`. -/
def ExpoGen (G : ℝ → ℂ) (D R : ℕ) (γ : ℕ → ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
    (if Nat.Coprime r (d1 * d2) then
      ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) *
        ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ) *
        ((1 / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
          ∑' k : ℤ, G ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (Nat.lcm d1 d2),
              γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
                  ((Nat.lcm d1 d2 : ℕ) : ℝ))))
    else 0)

/-- `Expo` is the special case of `ExpoGen` for the Fourier transform of the Gaussian. -/
lemma Expo_eq_ExpoGen (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (r : ℕ) :
    Work.FIArea4.Expo D R S γ r
      = ExpoGen (FourierTransform.fourier (gmajorC (S : ℝ))) D R γ r := rfl

/-! ## Exchanging the summation in the Poisson-expanded form -/

/-- Kernel-agnostic form of `Work.FIArea4.Wdyad_Expo_bilinear`: for any kernel `G` whose values
along `k / [d₁,d₂]` are summable, the sum over `r` of the Poisson-expanded class sums is the
bilinear form with kernel `KK G`. -/
theorem ExpoGen_bilinear (G : ℝ → ℂ) (D R : ℕ) (γ : ℕ → ℕ → ℂ)
    (hGsum : ∀ d1 d2 : ℕ, 1 ≤ d1 → 1 ≤ d2 →
      Summable fun k : ℤ => G ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ))) :
    ∑ r ∈ Finset.Ioc R (2 * R), ExpoGen G D R γ r
      = ∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
          ∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK G R d1 d2 a := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    simp [ExpoGen]
  · simp only [ExpoGen]
    rw [sum_comm_three]
    refine Finset.sum_congr rfl (fun d1 hd1 => Finset.sum_congr rfl (fun d2 hd2 => ?_))
    obtain ⟨hd1a, -⟩ := Finset.mem_Ioc.mp hd1
    obtain ⟨hd2a, -⟩ := Finset.mem_Ioc.mp hd2
    exact expo_block G R γ (by omega) (by omega) (hGsum d1 d2 (by omega) (by omega))

/-! ## The majorant bound for an arbitrary real majorant -/

/-- `Work.FIArea4.Wdyad_le_majorant` with the Gaussian replaced by an arbitrary real, nonnegative
majorant `F` that dominates `1` on `(S, 2S]`. -/
lemma Wdyad_le_majorant_gen (F : ℝ → ℂ) (D R S : ℕ) (hS : 1 ≤ S) (γ : ℕ → ℕ → ℂ)
    (hreal : ∀ x, ∃ r : ℝ, 0 ≤ r ∧ F x = (r : ℂ))
    (hge : ∀ x, (S : ℝ) < x → x ≤ 2 * (S : ℝ) → 1 ≤ (F x).re)
    (hFsum : Summable fun s : ℤ => F (s : ℝ)) :
    Wdyad D R S γ ≤ ∑ r ∈ Finset.Ioc R (2 * R),
      ∑' s : ℤ, (F (s : ℝ)).re * Complex.normSq (TZ D R S γ r s) := by
  have hre_nonneg : ∀ x, 0 ≤ (F x).re := by
    intro x
    obtain ⟨r, hr, hFx⟩ := hreal x
    rw [hFx, Complex.ofReal_re]
    exact hr
  have hFnorm : Summable fun s : ℤ => ‖F (s : ℝ)‖ := hFsum.norm
  have hsum_r : ∀ r : ℕ,
      Summable fun z : ℤ => (F (z : ℝ)).re * Complex.normSq (TZ D R S γ r z) := by
    intro r
    refine Summable.of_norm_bounded
      (hFnorm.mul_right ((∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d‖) ^ 2)) ?_
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
    calc |(F (z : ℝ)).re| * Complex.normSq (TZ D R S γ r z)
        ≤ ‖F (z : ℝ)‖ * Complex.normSq (TZ D R S γ r z) :=
          mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (Complex.normSq_nonneg _)
      _ ≤ ‖F (z : ℝ)‖ * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, ‖γ a d‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (normSq_TZ_le D R S γ r z) (norm_nonneg _)
  rw [Wdyad]
  have hinner : ∀ r : ℕ,
      (∑ s ∈ Finset.Ioc S (2 * S),
        Complex.normSq (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
          γ a d * Mentry d a r s))
        = ∑ s ∈ Finset.Ioc S (2 * S), Complex.normSq (TZ D R S γ r (s : ℤ)) := by
    intro r
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [TZ_ofNat]
  simp_rw [hinner]
  refine Finset.sum_le_sum (fun r _ => ?_)
  set K : Finset ℤ := (Finset.Ioc S (2 * S)).image (fun s : ℕ => (s : ℤ)) with hK
  have hKmem : ∀ z ∈ K, ∃ s ∈ Finset.Ioc S (2 * S), (s : ℤ) = z := by
    intro z hz
    rw [hK, Finset.mem_image] at hz
    obtain ⟨s, hs, hsz⟩ := hz
    exact ⟨s, hs, hsz⟩
  have hsum_image :
      ∑ z ∈ K, Complex.normSq (TZ D R S γ r z)
        = ∑ s ∈ Finset.Ioc S (2 * S), Complex.normSq (TZ D R S γ r (s : ℤ)) := by
    rw [hK, Finset.sum_image]
    intro a _ b _ h
    exact Nat.cast_injective h
  rw [← hsum_image]
  calc ∑ z ∈ K, Complex.normSq (TZ D R S γ r z)
      ≤ ∑ z ∈ K, (F (z : ℝ)).re * Complex.normSq (TZ D R S γ r z) := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        obtain ⟨s, hs, hsz⟩ := hKmem z hz
        have hs1 : S < s := (Finset.mem_Ioc.mp hs).1
        have hs2 : s ≤ 2 * S := (Finset.mem_Ioc.mp hs).2
        have hzr : (z : ℝ) = (s : ℝ) := by rw [← hsz]; push_cast; ring
        have hge' : 1 ≤ (F (z : ℝ)).re := by
          rw [hzr]
          refine hge (s : ℝ) ?_ ?_
          · exact_mod_cast hs1
          · exact_mod_cast hs2
        calc Complex.normSq (TZ D R S γ r z)
            = 1 * Complex.normSq (TZ D R S γ r z) := (one_mul _).symm
          _ ≤ (F (z : ℝ)).re * Complex.normSq (TZ D R S γ r z) :=
              mul_le_mul_of_nonneg_right hge' (Complex.normSq_nonneg _)
    _ ≤ ∑' z : ℤ, (F (z : ℝ)).re * Complex.normSq (TZ D R S γ r z) :=
        Summable.sum_le_tsum K (fun z _ => mul_nonneg (hre_nonneg _) (Complex.normSq_nonneg _))
          (hsum_r r)

/-! ## The real part of the complex `s`-sum -/

/-- For a real, nonnegative `F`, the real part of `∑'_s F s · ‖TZ r s‖²` (a complex sum) is the
real sum `∑'_s (F s).re · ‖TZ r s‖²`. -/
lemma tsum_re_mul_normSq (F : ℝ → ℂ) (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (r : ℕ)
    (hreal : ∀ x, ∃ r : ℝ, 0 ≤ r ∧ F x = (r : ℂ)) :
    (∑' s : ℤ, (F (s : ℝ)).re * Complex.normSq (TZ D R S γ r s))
      = (∑' s : ℤ, F (s : ℝ) * ((Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ)).re := by
  have hcast : ((∑' s : ℤ, (F (s : ℝ)).re * Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ)
      = ∑' s : ℤ, F (s : ℝ) * ((Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun s => ?_)
    obtain ⟨rs, hrs, hFs⟩ := hreal (s : ℝ)
    rw [hFs, Complex.ofReal_re, Complex.ofReal_mul]
  rw [← hcast, Complex.ofReal_re]

/-! ## The main theorem -/

theorem Wdyad_bilinear_gen (S : ℕ) (hS : 1 ≤ S) (D R : ℕ) (hD : 1 ≤ D) (γ : ℕ → ℕ → ℂ)
    (F : ℝ → ℂ) (hcont : Continuous F) {b : ℝ} (hb : 1 < b)
    (hF : F =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (hF' : (FourierTransform.fourier F) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (hreal : ∀ x, ∃ r : ℝ, 0 ≤ r ∧ F x = (r : ℂ))
    (hge : ∀ x, (S : ℝ) < x → x ≤ 2 * (S : ℝ) → 1 ≤ (F x).re) :
    Work.FIArea4.Wdyad D R S γ ≤
      (∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
          ∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
              Work.FIArea4.KK (FourierTransform.fourier F) R d1 d2 a).re := by
  have hFsum : Summable fun s : ℤ => F (s : ℝ) := by
    have h := Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow (G := F) hb hF (d := 1)
      one_pos
    simpa using h
  have hGsum : ∀ d1 d2 : ℕ, 1 ≤ d1 → 1 ≤ d2 →
      Summable fun k : ℤ =>
        (FourierTransform.fourier F) ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ)) := by
    intro d1 d2 hd1 hd2
    have hq : (0 : ℝ) < (Nat.lcm d1 d2 : ℕ) := by
      have hpos : 0 < Nat.lcm d1 d2 := Nat.lcm_pos (by omega) (by omega)
      exact_mod_cast hpos
    exact Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow
      (G := FourierTransform.fourier F) hb hF' hq
  have h3 : ∀ r : ℕ,
      (∑' s : ℤ, F (s : ℝ) * ((Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ))
        = ExpoGen (FourierTransform.fourier F) D R γ r := by
    intro r
    exact Wdyad_expansion F hcont hb hF hF' D R S hD γ r
  calc Wdyad D R S γ
      ≤ ∑ r ∈ Finset.Ioc R (2 * R),
          ∑' s : ℤ, (F (s : ℝ)).re * Complex.normSq (TZ D R S γ r s) :=
        Wdyad_le_majorant_gen F D R S hS γ hreal hge hFsum
    _ = ∑ r ∈ Finset.Ioc R (2 * R), (ExpoGen (FourierTransform.fourier F) D R γ r).re := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [tsum_re_mul_normSq F D R S γ r hreal, h3 r]
    _ = (∑ r ∈ Finset.Ioc R (2 * R), ExpoGen (FourierTransform.fourier F) D R γ r).re := by
        rw [Complex.re_sum]
    _ = (∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
          ∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
              KK (FourierTransform.fourier F) R d1 d2 a).re := by
        rw [ExpoGen_bilinear (FourierTransform.fourier F) D R γ hGsum]

end

end Work.FIArea4.Vflip
