import Mathlib
import Submission.Work.FIArea4.box_defs
import Submission.Work.FIArea4.flat_aux
import Submission.Work.FIArea4.Wdyad_diff_part_le_unif
import Submission.Work.FIArea4.UnitsFlat.bump_uniform
import Submission.Work.FIArea4.UnitsFlat.flat_part_units
import Submission.Work.FIArea4.Vflip.Wdyad_bilinear_gen

/-!
# FI (11.23) for the flat part of the workspace's own `flat_block_le`

This is the assembly `Wdyad_le_1123`: the dyadic dual variance is bounded by

`C (D^{-1/2} R S + (S R^{3/4} + D R + D √(RS)) (DR)^ε) ‖γ‖²`

by splitting the Poisson-expanded bilinear form into its flat (`♭`) and non-flat (`♦`) parts and
applying

* `Work.FIArea4.UnitsFlat.flat_part_units_of_block` (the flat part, with the per-pair AM–GM input
  `Work.FIArea4.flat_block_le`), and
* `Work.FIArea4.Wdyad_diff_part_le_unif` (the non-flat part),

with the uniform bump majorant `Work.FIArea4.UnitsFlat.bump_majorant_uniform_units`.
-/

namespace Work.FIArea4.UnitsFlat

open Finset
open scoped BigOperators FourierTransform

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **FI (11.23)** for the dyadic dual variance: the `DR` term of the flat/diff split is present,
and the `ε`-powers are `(DR)^ε`. -/
theorem Wdyad_le_1123_units (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      Work.FIArea4.Wdyad D R S γ ≤ C * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
          + ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε))
        * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  obtain ⟨C₀, hC₀pos, hbump⟩ := bump_majorant_uniform_units
  obtain ⟨Cf, hCfpos, hCf⟩ := flat_part_units_of_block Work.FIArea4.flat_block_le
  obtain ⟨Cd, hCdpos, hCd⟩ := Wdyad_diff_part_le_unif ε hε C₀ hC₀pos
  refine ⟨2 * (Cf + Cd), by positivity, ?_⟩
  intro D R S γ hD hR hS
  obtain ⟨f, F, hfnn, hf1, hfge, hfsupp, hfcont, hFeq, hFdec⟩ := hbump S hS
  set E : ℝ := ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)
    with hE
  have hEnn : 0 ≤ E := by
    rw [hE]
    exact Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hM : Work.FIArea4.BumpData S f F C₀ := ⟨hfnn, hf1, hfsupp, hfcont, hC₀pos, hFeq, hFdec⟩
  have hFeq' : F = FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) := funext hFeq
  have hcontC : Continuous fun x : ℝ => (f x : ℂ) := Complex.continuous_ofReal.comp hfcont
  have hsupp_c : HasCompactSupport fun x : ℝ => (f x : ℂ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc ((S:ℝ)/2) (5*(S:ℝ)/2)) isCompact_Icc ?_
    intro x hx
    rw [Function.mem_support] at hx
    have hx' : f x ≠ 0 := by simpa using hx
    obtain ⟨h1, h2⟩ := hfsupp x hx'
    exact ⟨h1, h2⟩
  have hF_bigO : (fun x : ℝ => (f x : ℂ)) =O[Filter.cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    have hev : (fun x : ℝ => (f x : ℂ)) =ᶠ[Filter.cocompact ℝ] 0 := by
      rw [← Filter.coclosedCompact_eq_cocompact, ← hasCompactSupport_iff_eventuallyEq]
      exact hsupp_c
    filter_upwards [hev] with x hx
    simp only [hx, Pi.zero_apply, norm_zero]
    positivity
  have hF'_bigO : (FourierTransform.fourier fun x : ℝ => (f x : ℂ))
      =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-(2:ℝ))) := by
    refine Asymptotics.IsBigO.of_bound C₀ ?_
    have hev : ∀ᶠ x : ℝ in Filter.cocompact ℝ, (1:ℝ) ≤ |x| := by
      refine Filter.mem_of_superset
        (isCompact_Icc (a := (-1:ℝ)) (b := 1)).compl_mem_cocompact ?_
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      show (1:ℝ) ≤ |x|
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    filter_upwards [hev] with ξ hξ
    have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have hax : 0 < |ξ| := by linarith
    have hmain : (S:ℝ) * (1 + (S:ℝ)*|ξ|) ^ (-(2:ℝ)) ≤ |ξ| ^ (-(2:ℝ)) := by
      rw [Real.rpow_neg (by positivity) 2, Real.rpow_neg (abs_nonneg ξ) 2,
        Real.rpow_two, Real.rpow_two, inv_eq_one_div, inv_eq_one_div, mul_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hξ, hS1, abs_nonneg ξ, sq_nonneg |ξ|, sq_nonneg ((S:ℝ) * |ξ|),
        mul_nonneg (sub_nonneg.mpr hS1) (mul_nonneg (abs_nonneg ξ) (abs_nonneg ξ)),
        mul_nonneg (sub_nonneg.mpr hS1) (sq_nonneg |ξ|)]
    have key : ‖F ξ‖ ≤ C₀ * ‖|ξ| ^ (-(2:ℝ))‖ := by
      calc ‖F ξ‖ ≤ C₀ * (S:ℝ) * (1 + (S:ℝ)*|ξ|) ^ (-(2:ℝ)) := hFdec ξ
        _ = C₀ * ((S:ℝ) * (1 + (S:ℝ)*|ξ|) ^ (-(2:ℝ))) := by ring
        _ ≤ C₀ * |ξ| ^ (-(2:ℝ)) := mul_le_mul_of_nonneg_left hmain hC₀pos.le
        _ = C₀ * ‖|ξ| ^ (-(2:ℝ))‖ := by
              rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) _)]
    simpa only [hFeq'] using key
  have hbil := Work.FIArea4.Vflip.Wdyad_bilinear_gen S hS D R hD γ (fun x : ℝ => (f x : ℂ))
    hcontC (by norm_num : (1:ℝ) < 2) hF_bigO hF'_bigO
    (fun x => ⟨f x, hfnn x, rfl⟩)
    (fun x h1 h2 => by simpa using hfge x h1 h2)
  rw [← hFeq'] at hbil
  set Af : ℂ := ∑ d1 ∈ Finset.Ioc D (2 * D),
          ∑ d2 ∈ (Finset.Ioc D (2 * D)).filter (fun d2 =>
              Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ∑ a ∈ Finset.range (Nat.lcm d1 d2),
              γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a with hAfdef
  set Ad : ℂ := ∑ d1 ∈ Finset.Ioc D (2 * D),
          ∑ d2 ∈ (Finset.Ioc D (2 * D)).filter (fun d2 =>
              Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ∑ a ∈ Finset.range (Nat.lcm d1 d2),
              γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a with hAddef
  have hsplit : (∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a) = Af + Ad := by
    rw [hAfdef, hAddef, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d1 _ => ?_)
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d2 _ => ?_)
    by_cases h : Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
        = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2
    · simp [h]
    · simp [h]
  have hWle : Wdyad D R S γ ≤ (∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a).re := hbil
  have hre : (∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a).re ≤ ‖Af‖ + ‖Ad‖ := by
    rw [hsplit, Complex.add_re]
    exact le_trans (add_le_add (Complex.re_le_norm Af) (Complex.re_le_norm Ad)) le_rfl
  have hAf' : ‖Af‖ ≤ Cf * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * E := by
    rw [hAfdef, hE]
    exact hCf S hS f F C₀ hM D R γ hD hR
  have hAd' : ‖Ad‖ ≤ Cd * (((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε)) * E := by
    rw [hAddef, hE]
    exact hCd S hS F hFdec D R γ hD hR
  set Tgt : ℝ := (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
      + ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
          + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε) with hTgt
  have hFbT : (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
      + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) ≤ Tgt := by
    rw [hTgt]
    have hsup : 0 ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    have hDR0 : (1:ℝ) ≤ (D : ℝ) * (R : ℝ) := by
      have h1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
      have h2 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
      nlinarith
    have hDR : (1:ℝ) ≤ (((D : ℝ) * (R : ℝ)) ^ ε) := Real.one_le_rpow hDR0 hε.le
    have hD : 0 ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) := by positivity
    have hcomp : (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
        ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((D : ℝ) * (R : ℝ)) ^ ε) := by
      nlinarith [hDR, hD]
    have hsum : (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) * (((D : ℝ) * (R : ℝ)) ^ ε)
        ≤ ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
            + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε) := by
      have h1 : 0 ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) * (((D : ℝ) * (R : ℝ)) ^ ε) := by
        positivity
      have h2 : 0 ≤ (D : ℝ) * (R : ℝ) * (((D : ℝ) * (R : ℝ)) ^ ε) :=
        mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) ε)
      rw [add_mul, add_mul]
      linarith
    linarith
  have hNbT : ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε) ≤ Tgt := by
    rw [hTgt]
    have h0 : 0 ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
    linarith
  have hTgtnn : 0 ≤ Tgt := by
    rw [hTgt]
    have h1 : 0 ≤ ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
        + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε) := by
      have ha : 0 ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) := by positivity
      have hb : 0 ≤ (D : ℝ) * (R : ℝ) := by positivity
      have hc : 0 ≤ (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ)) := by positivity
      have hd : 0 ≤ (((D : ℝ) * (R : ℝ)) ^ ε) := Real.rpow_nonneg (by positivity) ε
      nlinarith [ha, hb, hc, hd]
    have h2 : 0 ≤ (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ) := by positivity
    linarith
  have hCfn : 0 ≤ Cf := hCfpos.le
  have hCdn : 0 ≤ Cd := hCdpos.le
  calc Wdyad D R S γ
      ≤ (∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ Finset.Ioc D (2 * D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a).re := hWle
    _ ≤ ‖Af‖ + ‖Ad‖ := hre
    _ ≤ Cf * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
            + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * E
          + Cd * (((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε)) * E :=
        add_le_add hAf' hAd'
    _ ≤ (2 * (Cf + Cd)) * Tgt * E := by
        have h1 : Cf * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * E
            ≤ Cf * Tgt * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFbT hCfn) hEnn
        have h2 : Cd * (((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε)) * E
            ≤ Cd * Tgt * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNbT hCdn) hEnn
        have h3 : Cd * Tgt * E + Cf * Tgt * E = (Cf + Cd) * Tgt * E := by ring
        have h4 : (Cf + Cd) * Tgt * E ≤ (2 * (Cf + Cd)) * Tgt * E := by
          have := mul_nonneg (by linarith : (0:ℝ) ≤ Cf + Cd) (mul_nonneg hTgtnn hEnn)
          linarith
        linarith [h1, h2, h3, h4]
    _ = (2 * (Cf + Cd)) * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
          + ((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * (R : ℝ)
              + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε)) * E := by
        rw [hTgt]

end

end Work.FIArea4.UnitsFlat
