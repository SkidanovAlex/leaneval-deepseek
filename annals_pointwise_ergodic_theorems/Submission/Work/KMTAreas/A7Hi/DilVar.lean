import Mathlib
import Submission.Work.KMTAreas.A7.LacDevHormanderSetup
import Submission.Work.KMTAreas.A7.LacDevSymDefs
import Submission.Work.KMTAreas.A7.lacDevPerScaleSym
import Submission.Work.KMTAreas.A7.lacDevLin_tsum_eq
import Submission.Work.KMTAreas.tsum_inv_sq_shift_le
import Submission.Work.KMTAreas.A7.LacDevAssembly
import Submission.Work.KMTAreas.A7.lacDevL2
import Submission.Work.KMTAreas.A7.variationalNorm_le_sqSum
import Submission.Work.KMTAreas.A7.lacDilTriVar
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.KMTAreas.A7

noncomputable section

/-! ## The distance to the nearest integer -/

lemma nearDist_eq_abs (θ : ℝ) : nearDist θ = |θ - (nearInt θ : ℝ)| := rfl

lemma abs_sub_nearInt_le_half (θ : ℝ) : |θ - (nearInt θ : ℝ)| ≤ 1 / 2 := by
  have h1 : ((nearInt θ : ℤ) : ℝ) ≤ θ + 1 / 2 := Int.floor_le (θ + 1 / 2)
  have h2 : θ + 1 / 2 < ((nearInt θ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (θ + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

/-! ## The exponential gap `zGap θ = ‖1 - e^{2πiθ}‖ = 2 |sin (π θ)|` -/

lemma chr_one_eq (θ : ℝ) :
    Work.KMTAreas.ADev.chr 1 θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
  rw [Work.KMTAreas.ADev.chr]
  congr 1
  push_cast
  ring

lemma zGap_eq (θ : ℝ) : zGap θ = 2 * |Real.sin (Real.pi * θ)| := by
  rw [zGap, chr_one_eq]
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * θ)
  rw [show (2 * Real.pi * θ) / 2 = Real.pi * θ by ring] at h
  rw [norm_sub_rev] at h
  rw [h, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Shifting `θ` by the integer `nearInt θ` changes `sin (π θ)` at most by a sign. -/
lemma sin_pi_eq (θ : ℝ) :
    Real.sin (Real.pi * θ)
      = (-1) ^ (nearInt θ) * Real.sin (Real.pi * (θ - (nearInt θ : ℝ))) := by
  have h := Real.sin_add_int_mul_pi (Real.pi * (θ - (nearInt θ : ℝ))) (nearInt θ)
  rwa [show Real.pi * (θ - (nearInt θ : ℝ)) + ((nearInt θ : ℤ) : ℝ) * Real.pi
        = Real.pi * θ by ring] at h

lemma abs_sin_pi_eq (θ : ℝ) :
    |Real.sin (Real.pi * θ)| = |Real.sin (Real.pi * (θ - (nearInt θ : ℝ)))| := by
  rw [sin_pi_eq θ, abs_mul]
  have h : |(-1 : ℝ) ^ (nearInt θ)| = 1 := by rw [abs_zpow]; simp
  rw [h, one_mul]

/-- For `|x| ≤ π/2` one has `|sin x| = sin |x|`. -/
lemma sin_abs_eq (x : ℝ) (hx : |x| ≤ Real.pi / 2) : |Real.sin x| = Real.sin |x| := by
  have hpx : -Real.pi < x := by
    have := (abs_le.mp hx).1
    linarith [Real.pi_pos]
  rcases lt_or_ge x 0 with h0 | h0
  · rw [abs_of_neg h0, Real.sin_neg, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt h0 hpx)]
  · rw [abs_of_nonneg h0,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0
        (by linarith [(abs_le.mp hx).2, Real.pi_pos]))]

/-- The sign-free form of `zGap`: `|sin (π θ)| = sin (π · nearDist θ)`. -/
lemma abs_sin_pi_eq' (θ : ℝ) :
    |Real.sin (Real.pi * θ)| = Real.sin (Real.pi * |θ - (nearInt θ : ℝ)|) := by
  have h1 : |Real.pi * (θ - (nearInt θ : ℝ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left (abs_sub_nearInt_le_half θ) (le_of_lt Real.pi_pos)
  rw [abs_sin_pi_eq θ, sin_abs_eq _ h1, abs_mul, abs_of_pos Real.pi_pos]

lemma two_mul_nearDist_le_abs_sin (θ : ℝ) :
    2 * nearDist θ ≤ |Real.sin (Real.pi * θ)| := by
  rw [nearDist_eq_abs, abs_sin_pi_eq']
  have h := Real.mul_le_sin (x := Real.pi * |θ - (nearInt θ : ℝ)|) (by positivity)
    (by
      rw [show Real.pi / 2 = Real.pi * (1 / 2) by ring]
      exact mul_le_mul_of_nonneg_left (abs_sub_nearInt_le_half θ) (le_of_lt Real.pi_pos))
  have hX : (2 / Real.pi) * (Real.pi * |θ - (nearInt θ : ℝ)|)
      = 2 * |θ - (nearInt θ : ℝ)| := by
    field_simp
  linarith [h, hX]

lemma four_mul_nearDist_le_zGap (θ : ℝ) : 4 * nearDist θ ≤ zGap θ := by
  have h := two_mul_nearDist_le_abs_sin θ
  rw [zGap_eq]
  linarith

lemma zGap_le_two_pi_nearDist (θ : ℝ) : zGap θ ≤ 2 * Real.pi * nearDist θ := by
  rw [nearDist_eq_abs, zGap_eq, abs_sin_pi_eq']
  have h := Real.sin_le (x := Real.pi * |θ - (nearInt θ : ℝ)|) (by positivity)
  linarith

/-! ## Separation of the integers other than `nearInt θ` -/

lemma half_le_abs_sub_of_ne_nearInt (θ : ℝ) {k : ℤ} (hk : k ≠ nearInt θ) :
    (1 : ℝ) / 2 ≤ |θ - (k : ℝ)| := by
  have hne : k - nearInt θ ≠ 0 := sub_ne_zero.mpr hk
  have h1 : (1 : ℤ) ≤ |k - nearInt θ| := Int.one_le_abs hne
  have h2 : (1 : ℝ) ≤ |(k : ℝ) - (nearInt θ : ℝ)| := by
    have h1' : (1 : ℝ) ≤ ((|k - nearInt θ| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_abs, Int.cast_sub] at h1'
  have h4 : |(k : ℝ) - (nearInt θ : ℝ)| ≤ |(k : ℝ) - θ| + |θ - (nearInt θ : ℝ)| := by
    calc |(k : ℝ) - (nearInt θ : ℝ)| = |((k : ℝ) - θ) + (θ - (nearInt θ : ℝ))| := by ring_nf
      _ ≤ |(k : ℝ) - θ| + |θ - (nearInt θ : ℝ)| := abs_add_le _ _
  rw [abs_sub_comm (k : ℝ) θ] at h4
  have h5 : |θ - (nearInt θ : ℝ)| ≤ 1 / 2 := abs_sub_nearInt_le_half θ
  linarith

lemma abs_int_sub_nearInt_le_two (θ : ℝ) {k : ℤ} (hk : k ≠ nearInt θ) :
    |(k : ℝ) - (nearInt θ : ℝ)| ≤ 2 * |θ - (k : ℝ)| := by
  have h1 : (1 : ℝ) / 2 ≤ |θ - (k : ℝ)| := half_le_abs_sub_of_ne_nearInt θ hk
  have h4 : |(k : ℝ) - (nearInt θ : ℝ)| ≤ |(k : ℝ) - θ| + |θ - (nearInt θ : ℝ)| := by
    calc |(k : ℝ) - (nearInt θ : ℝ)| = |((k : ℝ) - θ) + (θ - (nearInt θ : ℝ))| := by ring_nf
      _ ≤ |(k : ℝ) - θ| + |θ - (nearInt θ : ℝ)| := abs_add_le _ _
  rw [abs_sub_comm (k : ℝ) θ] at h4
  have h5 : |θ - (nearInt θ : ℝ)| ≤ 1 / 2 := abs_sub_nearInt_le_half θ
  linarith

/-! ## The packaged statement -/

theorem nearIntFacts (θ : ℝ) :
    Work.KMTAreas.A7.nearDist θ ≤ 1 / 2 ∧
      4 * Work.KMTAreas.A7.nearDist θ ≤ Work.KMTAreas.A7.zGap θ ∧
      Work.KMTAreas.A7.zGap θ ≤ 2 * Real.pi * Work.KMTAreas.A7.nearDist θ ∧
      (∀ k : ℤ, k ≠ Work.KMTAreas.A7.nearInt θ → (1 : ℝ) / 2 ≤ |θ - (k : ℝ)|) ∧
      (∀ k : ℤ, k ≠ Work.KMTAreas.A7.nearInt θ →
        |(k : ℝ) - (Work.KMTAreas.A7.nearInt θ : ℝ)| ≤ 2 * |θ - (k : ℝ)|) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [nearDist_eq_abs]; exact abs_sub_nearInt_le_half θ
  · exact four_mul_nearDist_le_zGap θ
  · exact zGap_le_two_pi_nearDist θ
  · intro k hk; exact half_le_abs_sub_of_ne_nearInt θ hk
  · intro k hk; exact abs_int_sub_nearInt_le_two θ hk

lemma abs_sub_nearInt_le_half' (θ : ℝ) : |θ - (nearInt θ : ℝ)| ≤ 1 / 2 := by
  have h1 : ((nearInt θ : ℤ) : ℝ) ≤ θ + 1 / 2 := by
    rw [nearInt]; exact Int.floor_le (θ + 1 / 2)
  have h2 : θ + 1 / 2 < ((nearInt θ : ℤ) : ℝ) + 1 := by
    rw [nearInt]; exact Int.lt_floor_add_one (θ + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

/-- Periodicity of the triangular symbol. -/
lemma triSym_periodic (L : ℕ) : Function.Periodic (Work.KMTAreas.ADev.triSym L) 1 :=
  Work.KMTAreas.ADev.triSym_one_periodic L

local notation "NN" L => ((2 : ℤ) ^ L)

/-- The shifted atom at scale `2^L` intersected with `[-2^L, 2^L]` is the image of `range (2^L)`. -/
lemma shiftAtom_eq_image (L : ℕ) (τ : ℤ) (hτ : τ ∈ Finset.Ico (0 : ℤ) (NN L)) :
    (Finset.Icc (-(NN L)) (NN L)).filter (Work.Analysis.Hilbert.shiftAtom L τ)
      = (Finset.range (2 ^ L)).image (fun a : ℕ => -τ + (a : ℤ)) := by
  have hτ' : 0 ≤ τ ∧ τ < NN L := by
    rw [Finset.mem_Ico] at hτ; exact hτ
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range,
    Work.Analysis.Hilbert.shiftAtom]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have h5 : 0 ≤ n + τ := by omega
    have h6 : n + τ < ((2 ^ L : ℕ) : ℤ) := by
      have h7 : n + τ < NN L := by omega
      simpa using h7
    refine ⟨(n + τ).toNat, ?_, ?_⟩
    · omega
    · rw [Int.toNat_of_nonneg h5]
      ring
  · rintro ⟨a, ha, rfl⟩
    have haZ : ((a : ℤ)) < NN L := by
      have : (a : ℤ) < ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast ha
      simpa using this
    have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

/-- Each shifted dyadic kernel has total mass `1` on the supported interval. -/
lemma shiftKernel_sum (L : ℕ) (τ : ℤ) (hτ : τ ∈ Finset.Ico (0 : ℤ) (NN L)) :
    (∑ n ∈ Finset.Icc (-(NN L)) (NN L), Work.Analysis.Hilbert.shiftKernel L τ n) = 1 := by
  classical
  have hcard : ((Finset.Icc (-(NN L)) (NN L)).filter
      (Work.Analysis.Hilbert.shiftAtom L τ)).card = 2 ^ L := by
    rw [shiftAtom_eq_image L τ hτ]
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro a b hab
      have h2 : ((a : ℤ)) = ((b : ℤ)) := add_left_cancel hab
      exact_mod_cast h2
  have hstep : ∀ n : ℤ, Work.Analysis.Hilbert.shiftKernel L τ n
      = (if Work.Analysis.Hilbert.shiftAtom L τ n then (((2 : ℝ) ^ L))⁻¹ else 0) := by
    intro n
    by_cases h : Work.Analysis.Hilbert.shiftAtom L τ n <;>
      simp [Work.Analysis.Hilbert.shiftKernel, h]
  calc (∑ n ∈ Finset.Icc (-(NN L)) (NN L), Work.Analysis.Hilbert.shiftKernel L τ n)
      = ∑ n ∈ Finset.Icc (-(NN L)) (NN L),
          (if Work.Analysis.Hilbert.shiftAtom L τ n then (((2 : ℝ) ^ L))⁻¹ else 0) :=
        Finset.sum_congr rfl fun n _ => hstep n
    _ = (↑((Finset.Icc (-(NN L)) (NN L)).filter
            (Work.Analysis.Hilbert.shiftAtom L τ)).card : ℝ) * (((2 : ℝ) ^ L))⁻¹ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
        rw [hcard]
        rw [show ((2 ^ L : ℕ) : ℝ) = (2 : ℝ) ^ L by push_cast; ring]
        exact mul_inv_cancel₀ (by positivity)

/-- **The mass of the triangular kernel.** -/
lemma triKernel_sum (L : ℕ) :
    (∑ j ∈ Finset.Icc (-(NN L)) (NN L), Work.Analysis.Hilbert.triKernel L j) = 1 := by
  have h2L : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hstep : ∀ j : ℤ, ((2 : ℝ) ^ L) * Work.Analysis.Hilbert.triKernel L j
      = ∑ τ ∈ Finset.Ico (0 : ℤ) (NN L), Work.Analysis.Hilbert.shiftKernel L τ j := by
    intro j
    rw [← Work.Analysis.Hilbert.shiftKernel_average L j]
    rw [mul_div_cancel₀]
    exact ne_of_gt h2L
  have hmul : ((2 : ℝ) ^ L) * (∑ j ∈ Finset.Icc (-(NN L)) (NN L),
      Work.Analysis.Hilbert.triKernel L j) = (2 : ℝ) ^ L := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun τ hτ => shiftKernel_sum L τ hτ)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [show (((Finset.Ico (0 : ℤ) (NN L)).card : ℕ) : ℝ) = (2 : ℝ) ^ L from by
      rw [Int.card_Ico]
      have h2 : ((2 : ℤ) ^ L) = ((2 ^ L : ℕ) : ℤ) := by push_cast; ring
      rw [sub_zero, h2, Int.toNat_natCast]
      push_cast
      ring]
  have h1 : ((2 : ℝ) ^ L) * (∑ j ∈ Finset.Icc (-(NN L)) (NN L),
      Work.Analysis.Hilbert.triKernel L j) = (2 : ℝ) ^ L * 1 := by rw [hmul, mul_one]
  exact mul_left_cancel₀ (ne_of_gt h2L) h1

/-- The elementary exponential bound `‖e^{is} - 1‖ ≤ |s|`. -/
lemma norm_exp_I_mul_sub_one_le (s : ℝ) :
    ‖Complex.exp (Complex.I * (s : ℂ)) - 1‖ ≤ |s| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h4 : |s / 2| = |s| / 2 := by rw [abs_div]; norm_num
  have hs : |Real.sin (s / 2)| ≤ |s| / 2 := by
    have h : |Real.sin (s / 2)| ≤ |s / 2| := Real.abs_sin_le_abs
    rwa [h4] at h
  linarith

/-- The triangular symbol deviates from `1` by a linear term. -/
lemma triSym_sub_one_le (L : ℕ) (θ : ℝ) :
    ‖Work.KMTAreas.ADev.triSym L θ - 1‖ ≤ 2 * Real.pi * (2 : ℝ) ^ L * |θ| := by
  have hsum1 : (∑ j ∈ Finset.Icc (-(NN L)) (NN L),
      ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, triKernel_sum L]
    norm_num
  have hsplit : Work.KMTAreas.ADev.triSym L θ - 1
      = ∑ j ∈ Finset.Icc (-(NN L)) (NN L),
          ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ)
            * (Work.KMTAreas.ADev.chr j θ - 1) := by
    have hone : (1 : ℂ) = ∑ j ∈ Finset.Icc (-(NN L)) (NN L),
        ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ) := hsum1.symm
    calc Work.KMTAreas.ADev.triSym L θ - 1
        = (∑ j ∈ Finset.Icc (-(NN L)) (NN L),
              ((Work.KMTAreas.ADev.triK L j : ℝ) : ℂ) * Work.KMTAreas.ADev.chr j θ)
            - (∑ j ∈ Finset.Icc (-(NN L)) (NN L),
              ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ)) := by
          rw [Work.KMTAreas.ADev.triSym, hone]
      _ = ∑ j ∈ Finset.Icc (-(NN L)) (NN L),
            (((Work.KMTAreas.ADev.triK L j : ℝ) : ℂ) * Work.KMTAreas.ADev.chr j θ
              - ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ)) :=
          (by rw [Finset.sum_sub_distrib])
      _ = ∑ j ∈ Finset.Icc (-(NN L)) (NN L),
            ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ)
              * (Work.KMTAreas.ADev.chr j θ - 1) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have htk : ((Work.KMTAreas.ADev.triK L j : ℝ) : ℂ)
              = ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ) := by
            congr 1
          rw [htk]
          ring
  rw [hsplit]
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ j ∈ Finset.Icc (-(NN L)) (NN L),
      ‖((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ) * (Work.KMTAreas.ADev.chr j θ - 1)‖
        ≤ Work.Analysis.Hilbert.triKernel L j * (2 * Real.pi * (2 : ℝ) ^ L * |θ|) := by
    intro j hj
    have hjabs : |(j : ℝ)| ≤ (2 : ℝ) ^ L := by
      have hj' : -(((2 : ℤ) ^ L)) ≤ j ∧ j ≤ ((2 : ℤ) ^ L) := Finset.mem_Icc.mp hj
      have hcast : (((((2 : ℤ) ^ L)) : ℤ) : ℝ) = (2 : ℝ) ^ L := by push_cast; ring
      have h1 : -(2 : ℝ) ^ L ≤ (j : ℝ) := by
        have h2 : (((-(((2 : ℤ) ^ L)) : ℤ)) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj'.1
        push_cast at h2
        exact h2
      have h2 : (j : ℝ) ≤ (2 : ℝ) ^ L := by
        have h3 : (j : ℝ) ≤ (((((2 : ℤ) ^ L)) : ℤ) : ℝ) := by exact_mod_cast hj'.2
        rwa [hcast] at h3
      rw [abs_le]
      exact ⟨h1, h2⟩
    have hchr : ‖Work.KMTAreas.ADev.chr j θ - 1‖ ≤ 2 * Real.pi * |(j : ℝ)| * |θ| := by
      have hsub : Work.KMTAreas.ADev.chr j θ
          = Complex.exp (Complex.I * ((2 * Real.pi * (j : ℝ) * θ : ℝ) : ℂ)) := by
        rw [Work.KMTAreas.ADev.chr]
        congr 1
        push_cast
        ring
      rw [hsub]
      have h2 : |2 * Real.pi * (j : ℝ) * θ| = 2 * Real.pi * |(j : ℝ)| * |θ| := by
        simp only [abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc ‖Complex.exp (Complex.I * ↑(2 * Real.pi * (j : ℝ) * θ)) - 1‖
          ≤ |2 * Real.pi * (j : ℝ) * θ| := norm_exp_I_mul_sub_one_le _
        _ = 2 * Real.pi * |(j : ℝ)| * |θ| := h2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_max_left _ _)]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_left _ _)
    refine hchr.trans ?_
    have h3 : (0 : ℝ) ≤ 2 * Real.pi * |θ| := by positivity
    nlinarith [hjabs, h3]
  set c : ℝ := 2 * Real.pi * (2 : ℝ) ^ L * |θ| with hc
  refine (Finset.sum_le_sum hpt).trans ?_
  have hle : (∑ j ∈ Finset.Icc (-(NN L)) (NN L),
      Work.Analysis.Hilbert.triKernel L j) ≤ 1 := le_of_eq (triKernel_sum L)
  calc (∑ j ∈ Finset.Icc (-(NN L)) (NN L),
        Work.Analysis.Hilbert.triKernel L j * c)
      ≤ 1 * c := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hle (by rw [hc]; positivity)
    _ = c := one_mul c

/-- The triangular symbol deviates from `1` by at most `4 · 2^L · zGap θ`. -/
lemma triSym_sub_one_le_zGap {θ : ℝ} (hnear : 4 * nearDist θ ≤ zGap θ) (L : ℕ) :
    ‖(1 : ℂ) - Work.KMTAreas.ADev.triSym L θ‖ ≤ 4 * (2 : ℝ) ^ L * zGap θ := by
  set n₀ : ℤ := nearInt θ with hn₀
  set d : ℝ := |θ - (n₀ : ℝ)| with hd
  have hdle : d ≤ 1 / 2 := by rw [hd, hn₀]; exact abs_sub_nearInt_le_half' θ
  have hdnn : 0 ≤ d := by rw [hd]; positivity
  have hper : Work.KMTAreas.ADev.triSym L θ = Work.KMTAreas.ADev.triSym L (θ - (n₀ : ℝ)) := by
    have h := (triSym_periodic L).int_mul n₀ (θ - (n₀ : ℝ))
    simp only [zsmul_eq_mul, mul_one] at h
    have harg : θ - (n₀ : ℝ) + (n₀ : ℝ) = θ := by ring
    rw [harg] at h
    exact h
  have h1 := triSym_sub_one_le L (θ - (n₀ : ℝ))
  have h2 : ‖(1 : ℂ) - Work.KMTAreas.ADev.triSym L θ‖
      = ‖Work.KMTAreas.ADev.triSym L (θ - (n₀ : ℝ)) - 1‖ := by
    rw [hper, norm_sub_rev]
  have h3 : |θ - (n₀ : ℝ)| = d := by rw [hd]
  rw [h2]
  rw [h3] at h1
  refine h1.trans ?_
  have h2L : (0 : ℝ) ≤ (2 : ℝ) ^ L := by positivity
  have hnear' : 4 * d ≤ zGap θ := by
    have hdd : d = nearDist θ := by rw [hd, hn₀, nearDist]
    rw [hdd]
    exact hnear
  have h4 : d ≤ zGap θ / 4 := by linarith
  have hznn : 0 ≤ zGap θ := by linarith
  have hstep : 2 * Real.pi * (2 : ℝ) ^ L * d ≤ 2 * Real.pi * (2 : ℝ) ^ L * (zGap θ / 4) := by
    refine mul_le_mul_of_nonneg_left h4 ?_
    positivity
  have hstep2 : 2 * Real.pi * (2 : ℝ) ^ L * (zGap θ / 4) ≤ 4 * (2 : ℝ) ^ L * zGap θ := by
    have hprod : (0 : ℝ) ≤ (2 : ℝ) ^ L * zGap θ := mul_nonneg h2L hznn
    have hpi : Real.pi < 4 := Real.pi_lt_four
    rw [show 2 * Real.pi * (2 : ℝ) ^ L * (zGap θ / 4)
        = (Real.pi / 2) * ((2 : ℝ) ^ L * zGap θ) by ring]
    nlinarith [hprod, hpi]
  linarith

/-- **Fourier decay of the triangular symbol.**  In the regime `2 ^ L · zGap θ ≫ 1` the symbol is
small with a quantitative bound.  Proof by summation by parts: multiplying the symbol by
`1 - chr 1 θ` telescopes the tent kernel, whose total variation is `O(2^{-L})`. -/
lemma zGap_mul_triSym_le (L : ℕ) (θ : ℝ) :
    zGap θ * ‖Work.KMTAreas.ADev.triSym L θ‖ ≤ 5 / (2 : ℝ) ^ L := by
  set N : ℤ := (2 : ℤ) ^ L with hN
  have hNpos : (1 : ℤ) ≤ N := by rw [hN]; exact one_le_pow₀ (by norm_num)
  have hNcast : ((N : ℤ) : ℝ) = (2 : ℝ) ^ L := by rw [hN]; push_cast; ring
  have hNposr : (0 : ℝ) < (N : ℝ) := by rw [hNcast]; positivity
  have hzs : ∀ j : ℤ, ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ) ≠ 0 → (2 : ℝ) ^ L ≤ |(j : ℝ)| → False := by
    intro j h hle
    rw [Work.Analysis.Hilbert.triKernel_eq_zero_of_le (k := L) hle] at h
    exact h rfl
  have hsumm_g : ∀ g : ℤ → ℂ,
      Summable (fun j : ℤ => ((Work.Analysis.Hilbert.triKernel L j : ℝ) : ℂ) * g j) := by
    intro g
    refine summable_of_ne_finset_zero (s := Finset.Icc (-N) N) (fun j hj => ?_)
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    have h1 : (2 : ℝ) ^ L ≤ |(j : ℝ)| := by
      have hNge : (0 : ℝ) ≤ (2 : ℝ) ^ L := by positivity
      rcases hj with h1 | h1
      · have h2 : (j : ℝ) ≤ -(((N : ℤ)) : ℝ) := by
          have h2' : j ≤ -N := by omega
          exact_mod_cast h2'
        rw [hNcast] at h2
        have h3 : (j : ℝ) ≤ 0 := by linarith
        rw [abs_of_nonpos h3]
        linarith
      · have h2 : (((N : ℤ)) : ℝ) < (j : ℝ) := by
          have h2' : N < j := by omega
          exact_mod_cast h2'
        rw [hNcast] at h2
        have h3 : 0 ≤ (j : ℝ) := by linarith
        rw [abs_of_nonneg h3]
        linarith
    rw [Work.Analysis.Hilbert.triKernel_eq_zero_of_le (k := L) h1, Complex.ofReal_zero,
      zero_mul]
  have hsumm1 : Summable (fun j : ℤ => (((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
      * Work.KMTAreas.ADev.chr j θ) := hsumm_g (fun j => Work.KMTAreas.ADev.chr j θ)
  have hsumm2 : Summable (fun j : ℤ => (((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
      * Work.KMTAreas.ADev.chr (j + 1) θ) :=
    hsumm_g (fun j => Work.KMTAreas.ADev.chr (j + 1) θ)
  have hsumm3 : Summable (fun j : ℤ => (((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ)) : ℂ)
      * Work.KMTAreas.ADev.chr j θ) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(N + 1)) (N + 1)) (fun j hj => ?_)
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    have h1 : (2 : ℝ) ^ L ≤ |((j - 1 : ℤ) : ℝ)| := by
      have hNge : (0 : ℝ) ≤ (2 : ℝ) ^ L := by positivity
      have hjc : ((j - 1 : ℤ) : ℝ) = (j : ℝ) - 1 := by push_cast; ring
      rcases hj with h1 | h1
      · have h2 : (j : ℝ) ≤ -(((N : ℤ)) : ℝ) := by
          have h2' : j ≤ -N := by omega
          exact_mod_cast h2'
        rw [hNcast] at h2
        rw [hjc]
        have h3 : (j : ℝ) - 1 ≤ 0 := by linarith
        rw [abs_of_nonpos h3]
        linarith
      · have h2' : N + 2 ≤ j := by omega
        have h2 : (((N + 2 : ℤ)) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h2'
        push_cast at h2
        rw [hNcast] at h2
        rw [hjc]
        have hone : (1 : ℝ) ≤ (2 : ℝ) ^ L := one_le_pow₀ (by norm_num)
        have h3 : 0 ≤ (j : ℝ) - 1 := by linarith
        rw [abs_of_nonneg h3]
        linarith
    rw [Work.Analysis.Hilbert.triKernel_eq_zero_of_le (k := L) h1, Complex.ofReal_zero,
      zero_mul]
  -- the telescoping identity
  have hshift : (∑' j : ℤ, (((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
      * Work.KMTAreas.ADev.chr (j + 1) θ)
      = ∑' j : ℤ, (((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ)) : ℂ)
          * Work.KMTAreas.ADev.chr j θ := by
    rw [← Equiv.tsum_eq (Equiv.addRight (1 : ℤ))
      (fun i : ℤ => (((Work.Analysis.Hilbert.triKernel L (i - 1) : ℝ)) : ℂ)
        * Work.KMTAreas.ADev.chr i θ)]
    refine tsum_congr fun i => ?_
    simp only [Equiv.coe_addRight]
    congr 2
    ring

  have hkey : (1 - Work.KMTAreas.ADev.chr 1 θ) * Work.KMTAreas.ADev.triSym L θ
      = ∑' j : ℤ, ((((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
          - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ))
          * Work.KMTAreas.ADev.chr j θ := by
    rw [← triKernel_sym_eq_tsum L θ, ← tsum_mul_left]
    rw [show (∑' j : ℤ, (1 - Work.KMTAreas.ADev.chr 1 θ)
          * ((((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
            * Work.KMTAreas.ADev.chr j θ))
        = ∑' j : ℤ, ((((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
            * Work.KMTAreas.ADev.chr j θ
          - (((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
            * Work.KMTAreas.ADev.chr (j + 1) θ) from by
      refine tsum_congr fun j => ?_
      have hch : Work.KMTAreas.ADev.chr (j + 1) θ
          = Work.KMTAreas.ADev.chr j θ * Work.KMTAreas.ADev.chr 1 θ :=
        Work.KMTAreas.ADev.chr_add j 1 θ
      rw [hch]
      ring]
    rw [Summable.tsum_sub hsumm1 hsumm2, hshift]
    rw [← Summable.tsum_sub hsumm1 hsumm3]
    refine tsum_congr fun j => by ring
  -- the finite variation bound
  have hdiff : ∀ j : ℤ, ‖(((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
      - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ)‖ ≤ 1 / (N : ℝ) ^ 2 := by
    intro j
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 : Work.Analysis.Hilbert.triKernel L j
        = max 0 (((2 : ℝ) ^ L - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L)) := rfl
    have h2 : Work.Analysis.Hilbert.triKernel L (j - 1)
        = max 0 (((2 : ℝ) ^ L - |((j - 1 : ℤ) : ℝ)|) / (2 : ℝ) ^ (2 * L)) := rfl
    rw [h1, h2]
    have hnum : |(((2 : ℝ) ^ L - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L))
        - ((2 : ℝ) ^ L - |((j - 1 : ℤ) : ℝ)|) / (2 : ℝ) ^ (2 * L)|
        ≤ 1 / (2 : ℝ) ^ (2 * L) := by
      rw [← sub_div, abs_div, abs_of_pos (by positivity : (0:ℝ) < (2:ℝ)^(2*L))]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have hjc : ((j - 1 : ℤ) : ℝ) = (j : ℝ) - 1 := by push_cast; ring
      rw [hjc]
      have h := abs_abs_sub_abs_le_abs_sub ((j : ℝ) - 1) (j : ℝ)
      have h2 : |((j : ℝ) - 1) - (j : ℝ)| = 1 := by
        rw [show ((j : ℝ) - 1) - (j : ℝ) = -1 by ring]
        norm_num
      rw [h2] at h
      simpa using h
    calc |max 0 (((2 : ℝ) ^ L - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L))
          - max 0 (((2 : ℝ) ^ L - |((j - 1 : ℤ) : ℝ)|) / (2 : ℝ) ^ (2 * L))|
        ≤ |(((2 : ℝ) ^ L - |(j : ℝ)|) / (2 : ℝ) ^ (2 * L))
            - ((2 : ℝ) ^ L - |((j - 1 : ℤ) : ℝ)|) / (2 : ℝ) ^ (2 * L)| :=
          abs_max_zero_sub_max_zero _ _
      _ ≤ 1 / (2 : ℝ) ^ (2 * L) := hnum
      _ = 1 / ((2 : ℝ) ^ L) ^ 2 := by
          rw [show (2 : ℝ) ^ (2 * L) = ((2 : ℝ) ^ L) ^ 2 by
            rw [show 2 * L = L * 2 by ring, pow_mul]]
      _ = 1 / (N : ℝ) ^ 2 := by rw [hNcast]
  have hsupp : ∀ j : ℤ, j ∉ Finset.Icc (-(N + 1)) (N + 1) →
      ((((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
        - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ)) = 0 := by
    intro j hj
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    have key : ∀ m : ℤ, N ≤ |m| → (((Work.Analysis.Hilbert.triKernel L m : ℝ)) : ℂ) = 0 := by
      intro m hm
      have hm' : (2 : ℝ) ^ L ≤ |(m : ℝ)| := by
        have h := (Int.cast_le (R := ℝ)).mpr hm
        rw [hNcast, Int.cast_abs] at h
        exact h
      rw [Work.Analysis.Hilbert.triKernel_eq_zero_of_le (k := L) hm', Complex.ofReal_zero]
    rcases hj with h1 | h1
    · have hjle : j ≤ -(N + 2) := by omega
      have h2 : N ≤ |j| := by
        rw [abs_of_nonpos (by omega : j ≤ 0)]
        omega
      have h3 : N ≤ |j - 1| := by
        rw [abs_of_nonpos (by omega : j - 1 ≤ 0)]
        omega
      rw [key j h2, key (j - 1) h3, sub_zero]
    · have hjle : N + 2 ≤ j := by omega
      have h2 : N ≤ |j| := by
        rw [abs_of_nonneg (by omega : 0 ≤ j)]
        omega
      have h3 : N ≤ |j - 1| := by
        rw [abs_of_nonneg (by omega : 0 ≤ j - 1)]
        omega
      rw [key j h2, key (j - 1) h3, sub_zero]
  have hsum_le : ∑' j : ℤ, ‖(((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
      - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ)‖ ≤ 5 / (2 : ℝ) ^ L := by
    rw [tsum_eq_sum (s := Finset.Icc (-(N + 1)) (N + 1)) (fun j hj => by
      rw [hsupp j hj, norm_zero])]
    refine (Finset.sum_le_sum (fun j _ => hdiff j)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc (-(N + 1)) (N + 1)).card : ℝ) ≤ 2 * (N : ℝ) + 3 := by
      have hcardZ : ((Finset.Icc (-(N + 1)) (N + 1)).card : ℤ) ≤ 2 * N + 3 := by
        rw [Int.card_Icc]
        have h : N + 1 + 1 - (-(N + 1)) = 2 * N + 3 := by ring
        rw [h]
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ 2 * N + 3)]
      exact_mod_cast hcardZ
    have h1 : (0 : ℝ) ≤ (((N : ℝ)) ^ 2)⁻¹ := by positivity
    calc ((Finset.Icc (-(N + 1)) (N + 1)).card : ℝ) * (1 / (N : ℝ) ^ 2)
        ≤ (2 * (N : ℝ) + 3) * (1 / (N : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ 5 / (N : ℝ) := by
          have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
          rw [show (2 * (N : ℝ) + 3) * (1 / (N : ℝ) ^ 2) = (2 * (N : ℝ) + 3) / (N : ℝ) ^ 2 by ring]
          rw [div_le_div_iff₀ (by positivity) hNposr]
          nlinarith [hNposr, hN1]
      _ = 5 / (2 : ℝ) ^ L := by rw [hNcast]
  calc zGap θ * ‖Work.KMTAreas.ADev.triSym L θ‖
      = ‖(1 - Work.KMTAreas.ADev.chr 1 θ) * Work.KMTAreas.ADev.triSym L θ‖ := by
        rw [norm_mul]; rfl
    _ = ‖∑' j : ℤ, ((((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
          - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ))
          * Work.KMTAreas.ADev.chr j θ‖ := by rw [hkey]
    _ ≤ ∑' j : ℤ, ‖((((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
          - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ))
          * Work.KMTAreas.ADev.chr j θ‖ := by
        have hsummnorm : Summable (fun j : ℤ => ‖((((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
            - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ))
            * Work.KMTAreas.ADev.chr j θ‖) := by
          refine summable_of_ne_finset_zero (s := Finset.Icc (-(N + 1)) (N + 1)) (fun j hj => ?_)
          have h1 : ((((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
              - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ)) = 0 := hsupp j hj
          rw [h1, zero_mul, norm_zero]
        exact norm_tsum_le_tsum_norm hsummnorm
    _ = ∑' j : ℤ, ‖(((Work.Analysis.Hilbert.triKernel L j : ℝ)) : ℂ)
          - ((Work.Analysis.Hilbert.triKernel L (j - 1) : ℝ) : ℂ)‖ := by
        refine tsum_congr fun j => ?_
        rw [norm_mul, Work.KMTAreas.ADev.norm_chr, mul_one]
    _ ≤ 5 / (2 : ℝ) ^ L := hsum_le

/-- **The Fourier transform of a Schwartz function is Lipschitz at the origin.**  Since `𝓕K` is a
Schwartz function its derivative is bounded by a constant `C`, and the mean value inequality on
`[0, y]` gives `‖𝓕K y - 𝓕K 0‖ ≤ C |y|`. -/
theorem fourierLipschitzAtZero (K : SchwartzMap ℝ ℂ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ℝ,
      ‖FourierTransform.fourier (K : ℝ → ℂ) y - FourierTransform.fourier (K : ℝ → ℂ) 0‖
        ≤ L * |y| := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.Analysis.Fourier.schwartz_decay_real (SchwartzMap.derivCLM ℝ ℂ (𝓕 K : SchwartzMap ℝ ℂ)) 0
  have hCd : ∀ t : ℝ, ‖deriv (⇑(𝓕 K : SchwartzMap ℝ ℂ)) t‖ ≤ C := by
    intro t
    have h := hC t
    rw [SchwartzMap.derivCLM_apply] at h
    have hexp : (1 + |t|) ^ (-(↑(0 : ℕ) : ℝ)) = 1 := by
      rw [show (-(↑(0 : ℕ) : ℝ)) = 0 by norm_num, Real.rpow_zero]
    rw [hexp, mul_one] at h
    exact h
  refine ⟨C, hCpos.le, fun y => ?_⟩
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (f := ⇑(𝓕 K : SchwartzMap ℝ ℂ))
    (s := Set.uIcc (0 : ℝ) y) (x := 0) (y := y) (C := C)
    (fun z _ => (SchwartzMap.hasDerivAt (𝓕 K : SchwartzMap ℝ ℂ) z).differentiableAt)
    (fun z _ => hCd z)
    (convex_uIcc (0 : ℝ) y) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [sub_zero, Real.norm_eq_abs] at hmain
  exact hmain

/-- **Schwartz decay of the derivative.**  For a complex-valued Schwartz function `K` on `ℝ` there
is `B > 0` with `‖K' t‖ ≤ B / (1 + |t|)²` for every real `t`. -/
lemma schwartzMap_deriv_decay (K : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ‖deriv (⇑K) t‖ ≤ B / (1 + |t|) ^ 2 := by
  obtain ⟨B, hBpos, hB⟩ :=
    Commons.Analysis.Fourier.schwartz_decay_real (SchwartzMap.derivCLM ℝ ℂ K) 2
  refine ⟨B, hBpos, fun t => ?_⟩
  have h := hB t
  rw [SchwartzMap.derivCLM_apply] at h
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  have hexp : (1 + |t|) ^ (-((2 : ℕ) : ℝ)) = 1 / (1 + |t|) ^ 2 := by
    rw [show (-((2 : ℕ) : ℝ)) = (-2 : ℝ) by norm_num]
    exact Work.KMTAreas.A7.rpow_neg_two_eq hpos
  rw [hexp] at h
  calc ‖deriv ⇑K t‖ ≤ B * (1 / (1 + |t|) ^ 2) := h
    _ = B / (1 + |t|) ^ 2 := by ring

/-- **Schwartz functions are Lipschitz with decay.**  If `‖K' z‖ ≤ B / (1 + |z|)²` for all `z`,
then for `|v| ≤ 1` and all `u`, `‖K (u - v) - K u‖ ≤ 16 B |v| / (1 + |u|)²`.

The mean value inequality is applied on the segment `[u - |v|, u + |v|]`; on that segment
`1 + |z| ≥ (1 + |u|)/4`, whence `‖K' z‖ ≤ 16 B / (1 + |u|)²`. -/
lemma schwartzMap_diff_le (K : SchwartzMap ℝ ℂ) {B : ℝ} (hB : 0 < B)
    (hBd : ∀ t : ℝ, ‖deriv (⇑K) t‖ ≤ B / (1 + |t|) ^ 2) (u v : ℝ) (hv : |v| ≤ 1) :
    ‖K (u - v) - K u‖ ≤ 16 * B * |v| / (1 + |u|) ^ 2 := by
  have h4pos : (0 : ℝ) < (1 + |u|) / 4 := by positivity
  have hseg : ∀ z ∈ Set.Icc (u - |v|) (u + |v|), ‖deriv (⇑K) z‖ ≤ 16 * B / (1 + |u|) ^ 2 := by
    intro z hz
    rw [Set.mem_Icc] at hz
    have hzu : |z - u| ≤ |v| := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hzlow : (1 + |u|) / 4 ≤ 1 + |z| := by
      have h1 : |u| ≤ |z| + |z - u| := by
        have h := abs_sub_le z 0 (z - u)
        rw [sub_zero, zero_sub, abs_neg] at h
        rwa [show z - (z - u) = u by ring] at h
      rcases le_or_gt (|u|) 1 with h | h
      · nlinarith [abs_nonneg z, hzu, hv]
      · nlinarith [abs_nonneg z, hzu, hv]
    have hzpos : (0 : ℝ) < 1 + |z| := by linarith [abs_nonneg z]
    have hsq : ((1 + |u|) / 4) ^ 2 ≤ (1 + |z|) ^ 2 := pow_le_pow_left₀ h4pos.le hzlow 2
    have h1 : 1 / (1 + |z|) ^ 2 ≤ 1 / ((1 + |u|) / 4) ^ 2 :=
      one_div_le_one_div_of_le (pow_pos h4pos 2) hsq
    have h2 : 1 / ((1 + |u|) / 4) ^ 2 = 16 / (1 + |u|) ^ 2 := by
      rw [div_pow]
      norm_num
    calc ‖deriv ⇑K z‖ ≤ B / (1 + |z|) ^ 2 := hBd z
      _ = B * (1 / (1 + |z|) ^ 2) := by ring
      _ ≤ B * (16 / (1 + |u|) ^ 2) := mul_le_mul_of_nonneg_left (by rw [← h2]; exact h1) hB.le
      _ = 16 * B / (1 + |u|) ^ 2 := by ring
  have hmvt : ‖K (u - v) - K u‖ ≤ 16 * B / (1 + |u|) ^ 2 * |v| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := ⇑K)
      (s := Set.Icc (u - |v|) (u + |v|)) (x := u) (y := u - v) (C := 16 * B / (1 + |u|) ^ 2)
      (fun z _ => (K.hasDerivAt z).differentiableAt) hseg (convex_Icc _ _)
      ⟨by linarith [abs_nonneg v], by linarith [abs_nonneg v]⟩
      ⟨by linarith [le_abs_self v], by linarith [neg_le_abs v]⟩
    have hnorm : ‖(u - v) - u‖ = |v| := by
      rw [Real.norm_eq_abs, show (u - v) - u = -v by ring, abs_neg]
    rwa [hnorm] at h
  calc ‖K (u - v) - K u‖ ≤ 16 * B / (1 + |u|) ^ 2 * |v| := hmvt
    _ = 16 * B * |v| / (1 + |u|) ^ 2 := by ring

/-- The bump kernel with a *real* scalar: `bumpKernM K m j = ((1/m : ℝ) : ℂ) * K (j/m)`; this
normal form keeps the scalar a coerced real number, which is what the norm computation needs. -/
lemma bumpKernM_eq (K : SchwartzMap ℝ ℂ) (m : ℕ) (j : ℤ) :
    Work.KMTAreas.A7.bumpKernM K m j
      = (((1 : ℝ) / (m : ℝ) : ℝ) : ℂ) * K ((j : ℝ) / (m : ℝ)) := by
  rw [Work.KMTAreas.A7.bumpKernM]
  push_cast
  ring

/-- **The smoothness (Hörmander) estimate for the single-scale bump kernel.**  For `|y| ≤ m` and
all integers `x`, `‖bumpKernM K m (x - y) - bumpKernM K m x‖ ≤ B |y| / (m + |x|)²`. -/
theorem bumpKernSmooth (K : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (y : ℤ), |(y : ℝ)| ≤ (m : ℝ) → ∀ x : ℤ,
      ‖bumpKernM K m (x - y) - bumpKernM K m x‖
        ≤ B * |(y : ℝ)| / ((m : ℝ) + |(x : ℝ)|) ^ 2 := by
  obtain ⟨B, hB, hBd⟩ := schwartzMap_deriv_decay K
  refine ⟨16 * B, by positivity, ?_⟩
  intro m hm y hy x
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set u : ℝ := (x : ℝ) / (m : ℝ) with hu
  set v : ℝ := (y : ℝ) / (m : ℝ) with hv
  have hv1 : |v| ≤ 1 := by
    rw [hv, abs_div, abs_of_pos hmR]
    exact (div_le_one hmR).mpr hy
  have hvabs : |v| = |(y : ℝ)| / (m : ℝ) := by rw [hv, abs_div, abs_of_pos hmR]
  have huabs : |u| = |(x : ℝ)| / (m : ℝ) := by rw [hu, abs_div, abs_of_pos hmR]
  have hkey : ‖K (u - v) - K u‖ ≤ 16 * B * |(y : ℝ)| / (m : ℝ)
      / (1 + |(x : ℝ)| / (m : ℝ)) ^ 2 := by
    have h := schwartzMap_diff_le K hB hBd u v hv1
    rw [hvabs, huabs] at h
    calc ‖K (u - v) - K u‖
        ≤ 16 * B * (|(y : ℝ)| / (m : ℝ)) / (1 + |(x : ℝ)| / (m : ℝ)) ^ 2 := h
      _ = 16 * B * |(y : ℝ)| / (m : ℝ) / (1 + |(x : ℝ)| / (m : ℝ)) ^ 2 := by ring
  have harg : (((x - y : ℤ) : ℝ)) / (m : ℝ) = u - v := by
    rw [Int.cast_sub, hu, hv]
    ring
  have hsplit : Work.KMTAreas.A7.bumpKernM K m (x - y) - Work.KMTAreas.A7.bumpKernM K m x
      = (((1 : ℝ) / (m : ℝ) : ℝ) : ℂ) * (K (u - v) - K u) := by
    rw [bumpKernM_eq K m (x - y), bumpKernM_eq K m x, harg]
    ring
  calc ‖Work.KMTAreas.A7.bumpKernM K m (x - y) - Work.KMTAreas.A7.bumpKernM K m x‖
      = (1 / (m : ℝ)) * ‖K (u - v) - K u‖ := by
        rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
    _ ≤ (1 / (m : ℝ)) * (16 * B * |(y : ℝ)| / (m : ℝ)
          / (1 + |(x : ℝ)| / (m : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 16 * B * |(y : ℝ)| / ((m : ℝ) + |(x : ℝ)|) ^ 2 := by
        field_simp

/-- The integral against the counting measure of a nonnegative function on a set `S ⊆ ℤ` is the
supremum of its finite partial sums, so a uniform bound on the finite partial sums bounds it. -/
theorem lintegralCount_le_of_finset_le {S : Set ℤ} {g : ℤ → ENNReal} {B : ℝ}
    (h : ∀ F : Finset ℤ, (∀ x ∈ F, x ∈ S) → ∑ x ∈ F, g x ≤ ENNReal.ofReal B) :
    ∫⁻ x in S, g x ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal B := by
  classical
  -- The counting measure on `ℤ` restricted to `S` is the counting measure on the subtype `S`,
  -- so the integral is the (extended) sum of `g` over `S`.
  have hS : S.Countable := Set.countable_univ.mono (Set.subset_univ S)
  rw [MeasureTheory.lintegral_countable (f := g) hS]
  simp only [MeasureTheory.Measure.count_singleton, mul_one]
  -- An `ℝ≥0∞`-sum is the supremum of its finite partial sums.
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro t
  -- Each finite subset of `S` is the image of a finset of `ℤ` contained in `S`, and the
  -- hypothesis bounds the corresponding sum.
  have hsub : ∀ x ∈ t.image Subtype.val, x ∈ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, -, rfl⟩
    exact a.property
  have himg : ∑ a ∈ t, g a = ∑ x ∈ t.image Subtype.val, g x :=
    (Finset.sum_image (f := g) (s := t) (g := Subtype.val)
      (fun a _ b _ hab => Subtype.ext hab)).symm
  rw [himg]
  exact h _ hsub


/-! ## Helpers -/

/-- Summability is preserved by zeroing out the term at `0`. -/
lemma summable_ite_zero {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] {g : ℤ → E} (hg : Summable g) :
    Summable (fun j : ℤ => if j = 0 then 0 else g j) := by
  have h1 : (fun j : ℤ => (if j = 0 then 0 else g j))
      = g - fun j : ℤ => (if j = 0 then g 0 else 0) := by
    funext j
    by_cases hj : j = 0 <;> simp [hj]
  rw [h1]
  exact hg.sub (summable_of_ne_finset_zero (s := ({0} : Finset ℤ)) (fun j hj => by
    rw [if_neg (by simpa using hj)]))

/-- `((x.natAbs : ℕ) : ℝ) = |(x : ℝ)|`. -/
lemma natAbs_cast_real (x : ℤ) : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by
  rw [← Int.cast_abs, ← Nat.cast_natAbs]

/-- Schwartz decay of `𝓕K`. -/
lemma fourier_decay_sq (K : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, ‖(𝓕 K) x‖ ≤ B * ((1 + |x|) ^ 2)⁻¹ := by
  obtain ⟨B, hBpos, hB⟩ := Commons.Analysis.Fourier.schwartz_decay_real (𝓕 K) 2
  refine ⟨B, hBpos, fun x => ?_⟩
  have hx : (0 : ℝ) ≤ 1 + |x| := by positivity
  have he : (1 + |x|) ^ (-((2 : ℕ) : ℝ)) = ((1 + |x|) ^ 2)⁻¹ := by
    rw [show (-((2 : ℕ) : ℝ)) = -(2 : ℝ) by norm_num, Real.rpow_neg hx, Real.rpow_two]
  simpa only [he] using hB x

/-- Scaled lacunary tail: `∑_{j ≠ 0} ((1 + m |j|)^2)⁻¹ ≤ 2 B / m²` whenever `B` bounds the
`ℤ`-series `∑_j 1/(1+j²)`. -/
lemma tsum_scaled_tail_le (m : ℕ) (hm : 1 ≤ m) (B : ℝ)
    (hBsumm : Summable (fun j : ℤ => (1 : ℝ) / (1 + (j : ℝ) ^ 2)))
    (hBle : ∑' j : ℤ, (1 : ℝ) / (1 + (j : ℝ) ^ 2) ≤ B) :
    ∑' j : ℤ, (if j = 0 then 0 else ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹)
      ≤ 2 * B / (m : ℝ) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hRsum : Summable (fun j : ℤ => (2 / (m : ℝ) ^ 2) * (1 / (1 + (j : ℝ) ^ 2))) :=
    hBsumm.mul_left _
  have hle : ∀ j : ℤ, (if j = 0 then 0 else ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹)
      ≤ (2 / (m : ℝ) ^ 2) * (1 / (1 + (j : ℝ) ^ 2)) := by
    intro j
    by_cases hj : j = 0
    · rw [if_pos hj]; positivity
    · rw [if_neg hj]
      have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
        have h2 : (1 : ℝ) ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast h1
        rwa [Int.cast_abs] at h2
      have hsq : (1 : ℝ) ≤ ((j : ℝ)) ^ 2 := by
        rw [← sq_abs]; nlinarith [hj1]
      have hpos1 : (0 : ℝ) < (m : ℝ) * |(j : ℝ)| := by positivity
      have h1 : ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹ ≤ (((m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹ := by
        refine inv_anti₀ (by positivity) ?_
        nlinarith [hm1, abs_nonneg (j : ℝ)]
      have h2 : (((m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹
          ≤ (2 / (m : ℝ) ^ 2) * (1 / (1 + (j : ℝ) ^ 2)) := by
        rw [mul_pow, sq_abs,
          show ((m : ℝ) ^ 2 * (j : ℝ) ^ 2)⁻¹
            = (1 / (m : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2) by field_simp]
        have hkey : (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 * (1 / (1 + (j : ℝ) ^ 2)) := by
          rw [show (2 : ℝ) * (1 / (1 + (j : ℝ) ^ 2)) = 2 / (1 + (j : ℝ) ^ 2) by ring]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hsq]
        calc (1 / (m : ℝ) ^ 2) * (1 / (j : ℝ) ^ 2)
            ≤ (1 / (m : ℝ) ^ 2) * (2 * (1 / (1 + (j : ℝ) ^ 2))) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
          _ = (2 / (m : ℝ) ^ 2) * (1 / (1 + (j : ℝ) ^ 2)) := by ring
      linarith
  have hLsum : Summable (fun j : ℤ =>
      (if j = 0 then 0 else ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹)) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) hle hRsum
    by_cases hj : j = 0
    · rw [if_pos hj]
    · rw [if_neg hj]; positivity
  calc ∑' j : ℤ, (if j = 0 then 0 else ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹)
      ≤ ∑' j : ℤ, (2 / (m : ℝ) ^ 2) * (1 / (1 + (j : ℝ) ^ 2)) :=
        Summable.tsum_le_tsum hle hLsum hRsum
    _ = (2 / (m : ℝ) ^ 2) * (∑' j : ℤ, (1 / (1 + (j : ℝ) ^ 2))) := tsum_mul_left
    _ ≤ (2 / (m : ℝ) ^ 2) * B := mul_le_mul_of_nonneg_left hBle (by positivity)
    _ = 2 * B / (m : ℝ) ^ 2 := by ring

/-- **Quadratic decay of the bump symbol.**  For a Schwartz kernel whose Fourier transform is
`L₀`-Lipschitz at the origin, the symbol `bumpSym K m θ = ∑_k 𝓕K (m (k - θ))` satisfies
`|bumpSym K m θ - ∫K| ≤ A/m² + A m d(θ)` and `|bumpSym K m θ| ≤ A/m² + A (1 + m d(θ))^{-2}`. -/
theorem bumpSymQuad (K : SchwartzMap ℝ ℂ) {L₀ : ℝ} (hL₀ : 0 ≤ L₀)
    (hlip : ∀ y : ℝ, ‖FourierTransform.fourier (K : ℝ → ℂ) y
        - FourierTransform.fourier (K : ℝ → ℂ) 0‖ ≤ L₀ * |y|) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ : ℝ,
      ‖Work.KMTAreas.ADev.bumpSym K m θ - lacConst K‖
          ≤ A * ((m : ℝ) ^ 2)⁻¹ + A * ((m : ℝ) * nearDist θ) ∧
      ‖Work.KMTAreas.ADev.bumpSym K m θ‖
          ≤ A * ((m : ℝ) ^ 2)⁻¹ + A * ((1 + (m : ℝ) * nearDist θ) ^ 2)⁻¹ := by
  obtain ⟨B, hBpos, hB⟩ := fourier_decay_sq K
  obtain ⟨B₀, hB₀nn, hB₀⟩ := Work.KMTAreas.tsum_inv_sq_shift_le
  have hB₀summ : Summable (fun j : ℤ => (1 : ℝ) / (1 + (j : ℝ) ^ 2)) := by
    simpa using (hB₀ 0).1
  have hB₀le : ∑' j : ℤ, (1 : ℝ) / (1 + (j : ℝ) ^ 2) ≤ B₀ := by
    simpa using (hB₀ 0).2
  have hbase : Summable (fun j : ℤ => ((1 + |(j : ℝ)|) ^ 2)⁻¹) := by
    refine summable_int_one_add_abs_neg_two.congr (fun j => ?_)
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |(j : ℝ)|), Real.rpow_two]
  have hcoe : ∀ y : ℝ, FourierTransform.fourier (K : ℝ → ℂ) y = (𝓕 K) y :=
    fun y => congrFun (SchwartzMap.fourier_coe K).symm y
  refine ⟨8 * B * B₀ + B + L₀ + 1, by positivity, ?_⟩
  intro m hm θ
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  set n₀ : ℤ := nearInt θ with hn₀
  set d : ℝ := |θ - (n₀ : ℝ)| with hd
  have hdle : d ≤ 1 / 2 := by rw [hd, hn₀]; exact abs_sub_nearInt_le_half' θ
  have hdnn : 0 ≤ d := by rw [hd]; positivity
  set f : ℤ → ℂ := fun j => (𝓕 K) ((m : ℝ) * (((j : ℝ) + (n₀ : ℝ)) - θ)) with hf
  have hreindex : Work.KMTAreas.ADev.bumpSym K m θ = ∑' j : ℤ, f j := by
    rw [Work.KMTAreas.ADev.bumpSym]
    rw [← Equiv.tsum_eq (Equiv.addRight n₀)
      (fun k : ℤ => FourierTransform.fourier (K : ℝ → ℂ) ((m : ℝ) * ((k : ℝ) - θ)))]
    refine tsum_congr fun j => ?_
    simp only [Equiv.coe_addRight]
    rw [hcoe]
    congr 2
    push_cast
    ring
  have hterm : ∀ j : ℤ, ‖f j‖ ≤ (4 * B) * ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹ := by
    intro j
    have hd2 : |(n₀ : ℝ) - θ| = d := by rw [hd, abs_sub_comm]
    have htri : |(j : ℝ)| ≤ |(j : ℝ) + (n₀ : ℝ) - θ| + d := by
      calc |(j : ℝ)| = |((j : ℝ) + (n₀ : ℝ) - θ) + (θ - (n₀ : ℝ))| := by ring_nf
        _ ≤ |(j : ℝ) + (n₀ : ℝ) - θ| + |θ - (n₀ : ℝ)| := abs_add_le _ _
        _ = |(j : ℝ) + (n₀ : ℝ) - θ| + d := by rw [hd]
    have hmv : |(m : ℝ) * (((j : ℝ) + (n₀ : ℝ)) - θ)|
        = (m : ℝ) * |(j : ℝ) + (n₀ : ℝ) - θ| := by
      rw [abs_mul, abs_of_nonneg hmpos.le]
    have hlow : (1 + (m : ℝ) * |(j : ℝ)|) / 2
        ≤ 1 + |(m : ℝ) * (((j : ℝ) + (n₀ : ℝ)) - θ)| := by
      rw [hmv]
      rcases eq_or_ne j 0 with h0 | h0
      · subst h0
        have harg0 : |(((0 : ℤ) : ℝ) + (n₀ : ℝ)) - θ| = d := by
          rw [hd, abs_sub_comm]; norm_num
        rw [harg0]
        have : (0 : ℝ) ≤ (m : ℝ) * d := mul_nonneg hmpos.le hdnn
        norm_num
        linarith
      · have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
          have h1 : (1 : ℤ) ≤ |j| := Int.one_le_abs h0
          have h2 : (1 : ℝ) ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast h1
          rwa [Int.cast_abs] at h2
        have h2 : |(j : ℝ)| / 2 ≤ |(j : ℝ) + (n₀ : ℝ) - θ| := by
          linarith [htri, hdle]
        nlinarith [h2, hmpos, hj1]
    have hstep : ((1 + |(m : ℝ) * (((j : ℝ) + (n₀ : ℝ)) - θ)|) ^ 2)⁻¹
        ≤ 4 * ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹ := by
      have hA : (0 : ℝ) < (1 + (m : ℝ) * |(j : ℝ)|) / 2 := by positivity
      have hB2 : (0 : ℝ) < 1 + |(m : ℝ) * (((j : ℝ) + (n₀ : ℝ)) - θ)| := by positivity
      have h1 : ((1 + |(m : ℝ) * (((j : ℝ) + (n₀ : ℝ)) - θ)|) ^ 2)⁻¹
          ≤ (((1 + (m : ℝ) * |(j : ℝ)|) / 2) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (by nlinarith [hlow])
      have h2 : (((1 + (m : ℝ) * |(j : ℝ)|) / 2) ^ 2)⁻¹
          = 4 * ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹ := by
        have h : ((1 + (m : ℝ) * |(j : ℝ)|) / 2) ^ 2
            = ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2) / 4 := by ring
        rw [h, div_eq_mul_inv, mul_inv, inv_inv]
        ring
      linarith [h1, le_of_eq h2]
    calc ‖f j‖ = ‖(𝓕 K) ((m : ℝ) * (((j : ℝ) + (n₀ : ℝ)) - θ))‖ := rfl
      _ ≤ B * ((1 + |(m : ℝ) * (((j : ℝ) + (n₀ : ℝ)) - θ)|) ^ 2)⁻¹ := hB _
      _ ≤ B * (4 * ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hstep hBpos.le
      _ = (4 * B) * ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹ := by ring
  have hGsumm : Summable (fun j : ℤ => ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hbase
    have h1 : (1 : ℝ) + |(j : ℝ)| ≤ 1 + (m : ℝ) * |(j : ℝ)| := by
      nlinarith [hm1, abs_nonneg (j : ℝ)]
    have h2 : (1 + |(j : ℝ)|) ^ 2 ≤ (1 + (m : ℝ) * |(j : ℝ)|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    exact inv_anti₀ (by positivity) h2
  have hfsum : Summable f :=
    Summable.of_norm_bounded (hGsumm.mul_left (4 * B)) hterm
  have hsplit := Summable.tsum_eq_add_tsum_ite hfsum 0
  have htail_bound : ‖∑' j : ℤ, (if j = 0 then 0 else f j)‖ ≤ (4 * B) * (2 * B₀ / (m : ℝ) ^ 2) := by
    set X : ℤ → ℝ := fun j => ((1 + (m : ℝ) * |(j : ℝ)|) ^ 2)⁻¹ with hX
    have hsummite : Summable (fun j : ℤ => (if j = 0 then 0 else f j)) := summable_ite_zero hfsum
    have hnorm : (fun j : ℤ => ‖(if j = 0 then 0 else f j)‖)
        = fun j : ℤ => (if j = 0 then 0 else ‖f j‖) := by
      funext j
      by_cases hj : j = 0 <;> simp [hj]
    have hsummL : Summable (fun j : ℤ => (if j = 0 then 0 else ‖f j‖)) := by
      rw [← hnorm]
      exact hsummite.norm
    have hsummR : Summable (fun j : ℤ => (4 * B) * (if j = 0 then 0 else X j)) := by
      rw [show (fun j : ℤ => (4 * B) * (if j = 0 then 0 else X j))
          = fun j : ℤ => (if j = 0 then 0 else (4 * B) * X j) from by
        funext j
        by_cases hj : j = 0 <;> simp [hj]]
      exact summable_ite_zero (hGsumm.mul_left (4 * B))
    have hle : ∀ j : ℤ, (if j = 0 then 0 else ‖f j‖) ≤ (4 * B) * (if j = 0 then 0 else X j) := by
      intro j
      by_cases hj : j = 0
      · rw [if_pos hj, if_pos hj]
        exact le_of_eq (mul_zero (4 * B)).symm
      · rw [if_neg hj, if_neg hj]
        exact hterm j
    calc ‖∑' j : ℤ, (if j = 0 then 0 else f j)‖
        ≤ ∑' j : ℤ, ‖(if j = 0 then 0 else f j)‖ := norm_tsum_le_tsum_norm hsummite.norm
      _ = ∑' j : ℤ, (if j = 0 then 0 else ‖f j‖) := by rw [hnorm]
      _ ≤ ∑' j : ℤ, (4 * B) * (if j = 0 then 0 else X j) :=
          Summable.tsum_le_tsum hle hsummL hsummR
      _ = (4 * B) * (∑' j : ℤ, (if j = 0 then 0 else X j)) := tsum_mul_left
      _ ≤ (4 * B) * (2 * B₀ / (m : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hX]
          exact tsum_scaled_tail_le m hm B₀ hB₀summ hB₀le
  have hf0_dev : ‖f 0 - (𝓕 K) 0‖ ≤ L₀ * (m * d) := by
    have h := hlip ((m : ℝ) * (((0 : ℤ) : ℝ) + (n₀ : ℝ) - θ))
    rw [hcoe] at h
    have harg : (m : ℝ) * (((0 : ℤ) : ℝ) + (n₀ : ℝ) - θ) = (m : ℝ) * ((n₀ : ℝ) - θ) := by
      norm_num
    rw [harg] at h
    have habs : |(m : ℝ) * ((n₀ : ℝ) - θ)| = m * d := by
      rw [abs_mul, abs_of_nonneg hmpos.le, hd, abs_sub_comm]
    rw [habs] at h
    simpa only [hcoe, hf, Int.cast_zero, zero_add] using h
  have hf0_le : ‖f 0‖ ≤ B * ((1 + (m : ℝ) * nearDist θ) ^ 2)⁻¹ := by
    have h := hB ((m : ℝ) * (((0 : ℤ) : ℝ) + (n₀ : ℝ) - θ))
    have harg : (m : ℝ) * (((0 : ℤ) : ℝ) + (n₀ : ℝ) - θ) = (m : ℝ) * ((n₀ : ℝ) - θ) := by
      norm_num
    rw [harg] at h
    have habs : |(m : ℝ) * ((n₀ : ℝ) - θ)| = m * nearDist θ := by
      rw [abs_mul, abs_of_nonneg hmpos.le, abs_sub_comm, nearDist, ← hn₀]
    rw [habs] at h
    simpa only [hf, Int.cast_zero, zero_add] using h
  have hlc : lacConst K = (𝓕 K) 0 := lacConst_eq_fourier_zero K
  have hA1 : 8 * B * B₀ ≤ 8 * B * B₀ + B + L₀ + 1 := by nlinarith [hBpos, hB₀nn, hL₀]
  have hA2 : B ≤ 8 * B * B₀ + B + L₀ + 1 := by nlinarith [hBpos, hB₀nn, hL₀]
  have hA3 : L₀ ≤ 8 * B * B₀ + B + L₀ + 1 := by nlinarith [hBpos, hB₀nn, hL₀]
  have htl : (4 * B) * (2 * B₀ / (m : ℝ) ^ 2) = (8 * B * B₀) * ((m : ℝ) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]; ring
  rw [hreindex, hlc, hsplit]
  constructor
  · calc ‖(f 0 + ∑' j : ℤ, (if j = 0 then 0 else f j)) - (𝓕 K) 0‖
        = ‖(f 0 - (𝓕 K) 0) + ∑' j : ℤ, (if j = 0 then 0 else f j)‖ := by ring_nf
      _ ≤ ‖f 0 - (𝓕 K) 0‖ + ‖∑' j : ℤ, (if j = 0 then 0 else f j)‖ := norm_add_le _ _
      _ ≤ L₀ * (m * d) + (8 * B * B₀) * ((m : ℝ) ^ 2)⁻¹ := by
          rw [← htl]; exact add_le_add hf0_dev htail_bound
      _ ≤ (8 * B * B₀ + B + L₀ + 1) * ((m : ℝ) ^ 2)⁻¹
            + (8 * B * B₀ + B + L₀ + 1) * (m * nearDist θ) := by
          have h1 : (8 * B * B₀) * ((m : ℝ) ^ 2)⁻¹ ≤ (8 * B * B₀ + B + L₀ + 1) * ((m : ℝ) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hA1 (by positivity)
          have h2 : L₀ * (m * d) ≤ (8 * B * B₀ + B + L₀ + 1) * (m * nearDist θ) := by
            have hd' : d = nearDist θ := by rw [hd, nearDist, hn₀]
            rw [hd']
            have hmd : 0 ≤ (m : ℝ) * nearDist θ :=
              mul_nonneg hmpos.le (by rw [nearDist]; positivity)
            exact mul_le_mul_of_nonneg_right hA3 hmd
          linarith
  · calc ‖f 0 + ∑' j : ℤ, (if j = 0 then 0 else f j)‖
        ≤ ‖f 0‖ + ‖∑' j : ℤ, (if j = 0 then 0 else f j)‖ := norm_add_le _ _
      _ ≤ B * ((1 + (m : ℝ) * nearDist θ) ^ 2)⁻¹ + (8 * B * B₀) * ((m : ℝ) ^ 2)⁻¹ := by
          rw [← htl]; exact add_le_add hf0_le htail_bound
      _ ≤ (8 * B * B₀ + B + L₀ + 1) * ((m : ℝ) ^ 2)⁻¹
            + (8 * B * B₀ + B + L₀ + 1) * ((1 + (m : ℝ) * nearDist θ) ^ 2)⁻¹ := by
          have h1 : B * ((1 + (m : ℝ) * nearDist θ) ^ 2)⁻¹
              ≤ (8 * B * B₀ + B + L₀ + 1) * ((1 + (m : ℝ) * nearDist θ) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hA2 (by positivity)
          have h2 : (8 * B * B₀) * ((m : ℝ) ^ 2)⁻¹
              ≤ (8 * B * B₀ + B + L₀ + 1) * ((m : ℝ) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hA1 (by positivity)
          linarith


/-! ## Lacunary summation -/

/-- A `2`-lacunary `ℕ`-valued sequence grows by a factor `2 ^ k` over `k` steps. -/
lemma two_pow_mul_le_of_lac (σ : ℕ → ℕ) (hσ : ∀ n, 2 * σ n ≤ σ (n + 1)) (n k : ℕ) :
    2 ^ k * σ n ≤ σ (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc 2 ^ (k + 1) * σ n = 2 * (2 ^ k * σ n) := by ring
        _ ≤ 2 * σ (n + k) := Nat.mul_le_mul_left 2 ih
        _ ≤ σ (n + k + 1) := hσ (n + k)
        _ = σ (n + (k + 1)) := by rw [Nat.add_assoc]

/-- The geometric series `∑ (1/2)^k` is summable with value `2`. -/
lemma half_pow_summable : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
  summable_geometric_of_norm_lt_one (by norm_num)

lemma tsum_half_pow : (∑' k : ℕ, (1 / 2 : ℝ) ^ k) = 2 := by
  rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

/-- `∑_{n ∈ S} (1/2)^{n - n₀} ≤ 2` when every `n ∈ S` is at least `n₀`. -/
lemma geom_sub_sum_le_two (S : Finset ℕ) (n₀ : ℕ) (h : ∀ n ∈ S, n₀ ≤ n) :
    ∑ n ∈ S, (1 / 2 : ℝ) ^ (n - n₀) ≤ 2 := by
  have hinj : Set.InjOn (fun n => n - n₀) (↑S : Set ℕ) := by
    intro a ha b hb hab
    simp only at hab
    have h1 : a - n₀ + n₀ = b - n₀ + n₀ := by rw [hab]
    rwa [Nat.sub_add_cancel (h a ha), Nat.sub_add_cancel (h b hb)] at h1
  rw [← Finset.sum_image hinj]
  calc ∑ k ∈ S.image (fun n => n - n₀), (1 / 2 : ℝ) ^ k
      ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k := half_pow_summable.sum_le_tsum _ (fun k _ => by positivity)
    _ = 2 := tsum_half_pow

/-- `∑_{n ∈ S} (1/2)^{N - n} ≤ 2` when every `n ∈ S` is at most `N`. -/
lemma geom_reflect_sum_le_two (S : Finset ℕ) (N : ℕ) (h : ∀ n ∈ S, n ≤ N) :
    ∑ n ∈ S, (1 / 2 : ℝ) ^ (N - n) ≤ 2 := by
  have hinj : Set.InjOn (fun n => N - n) (↑S : Set ℕ) := by
    intro a ha b hb hab
    have h1 : a ≤ N := h a ha
    have h2 : b ≤ N := h b hb
    simp only at hab
    omega
  rw [← Finset.sum_image hinj]
  calc ∑ k ∈ S.image (fun n => N - n), (1 / 2 : ℝ) ^ k
      ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k := half_pow_summable.sum_le_tsum _ (fun k _ => by positivity)
    _ = 2 := tsum_half_pow

/-- **Tail of a lacunary sequence.**  If every `n ∈ S` satisfies `c ≤ σ n` then the reciprocals
sum at most `2/c`. -/
lemma lacunary_sum_inv_le (σ : ℕ → ℕ) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (S : Finset ℕ)
    {c : ℝ} (hc : 0 < c) (hS : ∀ n ∈ S, c ≤ (σ n : ℝ)) :
    ∑ n ∈ S, ((σ n : ℝ))⁻¹ ≤ 2 / c := by
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]; simp only [Finset.sum_empty]; positivity
  · obtain ⟨n₀, hn₀S, hmin⟩ : ∃ n₀ ∈ S, ∀ n ∈ S, n₀ ≤ n :=
      ⟨S.min' hne, S.min'_mem hne, fun n hn => S.min'_le n hn⟩
    have hcn₀ : c ≤ (σ n₀ : ℝ) := hS n₀ hn₀S
    have hσn₀pos : (0 : ℝ) < (σ n₀ : ℝ) := lt_of_lt_of_le hc hcn₀
    have hgrowth : ∀ n ∈ S, (2 : ℝ) ^ (n - n₀) * (σ n₀ : ℝ) ≤ (σ n : ℝ) := by
      intro n hn
      have hnat : 2 ^ (n - n₀) * σ n₀ ≤ σ n := by
        have := two_pow_mul_le_of_lac σ hσ2 n₀ (n - n₀)
        rwa [Nat.add_sub_of_le (hmin n hn)] at this
      have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at hcast
      exact hcast
    have hterm : ∀ n ∈ S, ((σ n : ℝ))⁻¹ ≤ (1 / 2 : ℝ) ^ (n - n₀) * ((σ n₀ : ℝ))⁻¹ := by
      intro n hn
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (n - n₀) * (σ n₀ : ℝ) := by positivity
      calc ((σ n : ℝ))⁻¹ ≤ (((2 : ℝ) ^ (n - n₀)) * (σ n₀ : ℝ))⁻¹ :=
            inv_anti₀ hpos (hgrowth n hn)
        _ = (1 / 2 : ℝ) ^ (n - n₀) * ((σ n₀ : ℝ))⁻¹ := by
            rw [mul_inv, ← inv_pow, show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num]
    calc ∑ n ∈ S, ((σ n : ℝ))⁻¹
        ≤ ∑ n ∈ S, (1 / 2 : ℝ) ^ (n - n₀) * ((σ n₀ : ℝ))⁻¹ := Finset.sum_le_sum hterm
      _ = ((σ n₀ : ℝ))⁻¹ * (∑ n ∈ S, (1 / 2 : ℝ) ^ (n - n₀)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ ((σ n₀ : ℝ))⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left (geom_sub_sum_le_two S n₀ hmin) (by positivity)
      _ ≤ 2 / c := by
          have h1 : (1 : ℝ) / (σ n₀ : ℝ) ≤ 1 / c := one_div_le_one_div_of_le hc hcn₀
          have h2 : (2 : ℝ) / (σ n₀ : ℝ) ≤ 2 / c := by
            have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
            simpa [div_eq_mul_inv] using this
          have h3 : ((σ n₀ : ℝ))⁻¹ * 2 = 2 / (σ n₀ : ℝ) := by ring
          rw [h3]
          exact h2

/-- **Head of a lacunary sequence.**  If every `n ∈ S` satisfies `σ n ≤ c` then the scales
themselves sum at most `2 c`. -/
lemma lacunary_sum_le (σ : ℕ → ℕ) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (S : Finset ℕ)
    {c : ℝ} (hc : 0 ≤ c) (hS : ∀ n ∈ S, (σ n : ℝ) ≤ c) :
    ∑ n ∈ S, (σ n : ℝ) ≤ 2 * c := by
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]; simp only [Finset.sum_empty]; linarith
  · obtain ⟨N, hNS, hmax⟩ : ∃ N ∈ S, ∀ n ∈ S, n ≤ N :=
      ⟨S.max' hne, S.max'_mem hne, fun n hn => S.le_max' n hn⟩
    have hterm : ∀ n ∈ S, (σ n : ℝ) ≤ (σ N : ℝ) * (1 / 2 : ℝ) ^ (N - n) := by
      intro n hn
      have hnat : 2 ^ (N - n) * σ n ≤ σ N := by
        have := two_pow_mul_le_of_lac σ hσ2 n (N - n)
        rwa [Nat.add_sub_of_le (hmax n hn)] at this
      have hcast : ((2 : ℝ) ^ (N - n)) * (σ n : ℝ) ≤ (σ N : ℝ) := by
        have h := (Nat.cast_le (α := ℝ)).mpr hnat
        push_cast at h
        exact h
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (N - n) := by positivity
      have hgoal : (σ n : ℝ) ≤ (σ N : ℝ) / (2 : ℝ) ^ (N - n) := by
        rw [le_div_iff₀ hpos]
        linarith
      have hhalf : (σ N : ℝ) / (2 : ℝ) ^ (N - n)
          = (σ N : ℝ) * (1 / 2 : ℝ) ^ (N - n) := by
        rw [div_eq_mul_inv, ← inv_pow, show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num]
      rwa [hhalf] at hgoal
    calc ∑ n ∈ S, (σ n : ℝ)
        ≤ ∑ n ∈ S, (σ N : ℝ) * (1 / 2 : ℝ) ^ (N - n) := Finset.sum_le_sum hterm
      _ = (σ N : ℝ) * (∑ n ∈ S, (1 / 2 : ℝ) ^ (N - n)) := by rw [Finset.mul_sum]
      _ ≤ (σ N : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left (geom_reflect_sum_le_two S N hmax) (by positivity)
      _ ≤ 2 * c := by
          have : (σ N : ℝ) ≤ c := hS N hNS
          linarith



theorem lacSumMin {σ : ℕ → ℕ} (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
    (d : ℝ) (hd : 0 ≤ d) (U : Finset ℕ) :
    ∑ n ∈ U, min ((σ n : ℝ) * d) (((σ n : ℝ) * d)⁻¹) ≤ 4 := by
  set w : ℕ → ℝ := fun n => (σ n : ℝ) * d with hw
  have hhead : ∑ n ∈ U.filter (fun n => w n ≤ 1), min (w n) ((w n)⁻¹) ≤ 2 := by
    refine (Finset.sum_le_sum fun n _ => min_le_left _ _).trans ?_
    rcases (U.filter (fun n => w n ≤ 1)).eq_empty_or_nonempty with h | hne
    · rw [h]; simp
    · obtain ⟨N, hNmem, hNmax⟩ : ∃ N ∈ U.filter (fun n => w n ≤ 1),
          ∀ n ∈ U.filter (fun n => w n ≤ 1), n ≤ N :=
        ⟨(U.filter _).max' hne, Finset.max'_mem _ hne, fun n hn => Finset.le_max' _ n hn⟩
      have hwN : w N ≤ 1 := (Finset.mem_filter.mp hNmem).2
      have hterm : ∀ n ∈ U.filter (fun n => w n ≤ 1), w n ≤ (1 / 2 : ℝ) ^ (N - n) := by
        intro n hn
        have hnN : n ≤ N := hNmax n hn
        have hgrowth : w n * (2 : ℝ) ^ (N - n) ≤ w N := by
          have hnat := two_pow_mul_le_of_lac σ hσ2 n (N - n)
          have hk : n + (N - n) = N := Nat.add_sub_of_le hnN
          rw [hk] at hnat
          have hcast : ((2 : ℝ) ^ (N - n)) * (σ n : ℝ) ≤ (σ N : ℝ) := by
            have h := (Nat.cast_le (α := ℝ)).mpr hnat
            push_cast at h
            exact h
          calc w n * (2 : ℝ) ^ (N - n)
              = (((2 : ℝ) ^ (N - n)) * (σ n : ℝ)) * d := by rw [hw]; ring
            _ ≤ (σ N : ℝ) * d := mul_le_mul_of_nonneg_right hcast hd
            _ = w N := by rw [hw]
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (N - n) := by positivity
        calc w n ≤ w N / (2 : ℝ) ^ (N - n) := by rw [le_div_iff₀ hpos]; linarith
          _ ≤ 1 / (2 : ℝ) ^ (N - n) := by
              rw [div_le_div_iff₀ hpos hpos]
              nlinarith [hwN, hpos.le]
          _ = (1 / 2 : ℝ) ^ (N - n) := by
              rw [one_div, ← inv_pow, show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num]
      exact (Finset.sum_le_sum hterm).trans (geom_reflect_sum_le_two _ N hNmax)
  have htail : ∑ n ∈ U.filter (fun n => ¬ (w n ≤ 1)), min (w n) ((w n)⁻¹) ≤ 2 := by
    refine (Finset.sum_le_sum fun n _ => min_le_right _ _).trans ?_
    rcases (U.filter (fun n => ¬ (w n ≤ 1))).eq_empty_or_nonempty with h | hne
    · rw [h]; simp
    · obtain ⟨m, hm_mem, hm_min⟩ : ∃ m ∈ U.filter (fun n => ¬ (w n ≤ 1)),
          ∀ n ∈ U.filter (fun n => ¬ (w n ≤ 1)), m ≤ n :=
        ⟨(U.filter _).min' hne, Finset.min'_mem _ hne, fun n hn => Finset.min'_le _ n hn⟩
      have hwm : 1 < w m := not_le.mp (Finset.mem_filter.mp hm_mem).2
      have hterm : ∀ n ∈ U.filter (fun n => ¬ (w n ≤ 1)), (w n)⁻¹ ≤ (1 / 2 : ℝ) ^ (n - m) := by
        intro n hn
        have hmn : m ≤ n := hm_min n hn
        have hgrowth : w m * (2 : ℝ) ^ (n - m) ≤ w n := by
          have hnat := two_pow_mul_le_of_lac σ hσ2 m (n - m)
          have hk : m + (n - m) = n := Nat.add_sub_of_le hmn
          rw [hk] at hnat
          have hcast : ((2 : ℝ) ^ (n - m)) * (σ m : ℝ) ≤ (σ n : ℝ) := by
            have h := (Nat.cast_le (α := ℝ)).mpr hnat
            push_cast at h
            exact h
          calc w m * (2 : ℝ) ^ (n - m)
              = (((2 : ℝ) ^ (n - m)) * (σ m : ℝ)) * d := by rw [hw]; ring
            _ ≤ (σ n : ℝ) * d := mul_le_mul_of_nonneg_right hcast hd
            _ = w n := by rw [hw]
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (n - m) := by positivity
        have hlt : (2 : ℝ) ^ (n - m) < w n := by nlinarith [hgrowth, hwm, hpos]
        calc (w n)⁻¹ ≤ (((2 : ℝ) ^ (n - m)))⁻¹ := inv_anti₀ hpos (le_of_lt hlt)
          _ = (1 / 2 : ℝ) ^ (n - m) := by
              rw [← inv_pow, show ((2 : ℝ))⁻¹ = 1 / 2 by norm_num]
      exact (Finset.sum_le_sum hterm).trans (geom_sub_sum_le_two _ m hm_min)
  have hcover : ∑ n ∈ U, min (w n) ((w n)⁻¹)
      = ∑ n ∈ U.filter (fun n => w n ≤ 1), min (w n) ((w n)⁻¹)
        + ∑ n ∈ U.filter (fun n => ¬ (w n ≤ 1)), min (w n) ((w n)⁻¹) :=
    (Finset.sum_filter_add_sum_filter_not U (fun n => w n ≤ 1) _).symm
  rw [hcover]
  linarith


/-! ## The discrete Hörmander condition for the linearised deviation kernels -/

/-- Telescoping bound with a shift: `∑_{n ∈ S} (1/(a+n-1) - 1/(a+n)) ≤ 1/(a+R-1)`. -/
lemma sum_shift_sub_le (S : Finset ℕ) (a R : ℝ) (ha : 0 < a) (hR : 1 ≤ R)
    (hS : ∀ n ∈ S, R ≤ (n : ℝ)) :
    ∑ n ∈ S, (1 / (a + (n : ℝ) - 1) - 1 / (a + (n : ℝ))) ≤ 1 / (a + R - 1) := by
  rcases S.eq_empty_or_nonempty with h | hne
  · rw [h]; simp only [Finset.sum_empty]
    exact div_nonneg zero_le_one (by linarith)
  · obtain ⟨m, hmS, hmin⟩ : ∃ m ∈ S, ∀ n ∈ S, m ≤ n :=
      ⟨S.min' hne, S.min'_mem hne, fun n hn => S.min'_le n hn⟩
    obtain ⟨M, hMS, hmax⟩ : ∃ M ∈ S, ∀ n ∈ S, n ≤ M :=
      ⟨S.max' hne, S.max'_mem hne, fun n hn => S.le_max' n hn⟩
    have hmR : R ≤ (m : ℝ) := hS m hmS
    have hmM : m ≤ M := hmin M hMS
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := le_trans hR hmR
    have hsub : S ⊆ Finset.Icc m M := fun n hn => Finset.mem_Icc.mpr ⟨hmin n hn, hmax n hn⟩
    have hnonneg : ∀ n ∈ Finset.Icc m M, n ∉ S →
        (0 : ℝ) ≤ 1 / (a + (n : ℝ) - 1) - 1 / (a + (n : ℝ)) := by
      intro n hn _
      have hmn : m ≤ n := (Finset.mem_Icc.mp hn).1
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
        linarith
      have hpos : 0 < a + (n : ℝ) - 1 := by linarith
      have hle : 1 / (a + (n : ℝ)) ≤ 1 / (a + (n : ℝ) - 1) :=
        one_div_le_one_div_of_le hpos (by linarith)
      linarith
    have htel : ∑ n ∈ Finset.Icc m M, (1 / (a + (n : ℝ) - 1) - 1 / (a + (n : ℝ)))
        = 1 / (a + (m : ℝ) - 1) - 1 / (a + (M : ℝ)) := by
      have h := Finset.sum_Icc_sub (f := fun k : ℕ => (1 : ℝ) / (a + (k : ℝ) - 1)) hmM
      have h2 : ∑ i ∈ Finset.Icc m M,
            ((1 : ℝ) / (a + ((i + 1 : ℕ) : ℝ) - 1) - 1 / (a + (i : ℝ) - 1))
          = (1 : ℝ) / (a + ((M + 1 : ℕ) : ℝ) - 1) - 1 / (a + (m : ℝ) - 1) := h
      have h3 : ∑ i ∈ Finset.Icc m M,
            ((1 : ℝ) / (a + ((i + 1 : ℕ) : ℝ) - 1) - 1 / (a + (i : ℝ) - 1))
          = ∑ i ∈ Finset.Icc m M, (1 / (a + (i : ℝ)) - 1 / (a + (i : ℝ) - 1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [h3] at h2
      have h4 : ∑ i ∈ Finset.Icc m M, (1 / (a + (i : ℝ) - 1) - 1 / (a + (i : ℝ)))
          = -(∑ i ∈ Finset.Icc m M, (1 / (a + (i : ℝ)) - 1 / (a + (i : ℝ) - 1))) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h4, h2]
      have hc : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by norm_num
      rw [hc]
      ring
    calc ∑ n ∈ S, (1 / (a + (n : ℝ) - 1) - 1 / (a + (n : ℝ)))
        ≤ ∑ n ∈ Finset.Icc m M, (1 / (a + (n : ℝ) - 1) - 1 / (a + (n : ℝ))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      _ = 1 / (a + (m : ℝ) - 1) - 1 / (a + (M : ℝ)) := htel
      _ ≤ 1 / (a + (m : ℝ) - 1) := by
          have h1 : 0 < a + (M : ℝ) := by linarith [hR, hmR]
          have h2 : 0 < 1 / (a + (M : ℝ)) := by positivity
          linarith
      _ ≤ 1 / (a + R - 1) := by
          have h1 : 0 < a + R - 1 := by linarith [hR, ha]
          have h2 : a + R - 1 ≤ a + (m : ℝ) - 1 := by linarith [hmR]
          exact one_div_le_one_div_of_le h1 h2

/-- `∑_{n ∈ S} (a+n)^{-2} ≤ 1/(a+R-1)` for `n ≥ R ≥ 1` and `a > 0`. -/
lemma sum_shift_inv_sq_le (S : Finset ℕ) (a R : ℝ) (ha : 0 < a) (hR : 1 ≤ R)
    (hS : ∀ n ∈ S, R ≤ (n : ℝ)) :
    ∑ n ∈ S, (a + (n : ℝ)) ^ (-2 : ℝ) ≤ 1 / (a + R - 1) := by
  have hterm : ∀ n ∈ S, (a + (n : ℝ)) ^ (-2 : ℝ)
      ≤ 1 / (a + (n : ℝ) - 1) - 1 / (a + (n : ℝ)) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans hR (hS n hn)
    have hpos : 0 < a + (n : ℝ) - 1 := by linarith
    have hpos2 : 0 < a + (n : ℝ) := by linarith
    rw [rpow_neg_two_eq hpos2]
    have h1 : (1 : ℝ) / (a + (n : ℝ) - 1) - 1 / (a + (n : ℝ))
        = 1 / ((a + (n : ℝ) - 1) * (a + (n : ℝ))) := by
      field_simp
      ring
    rw [h1]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hpos, hn1]
  exact (Finset.sum_le_sum hterm).trans (sum_shift_sub_le S a R ha hR hS)

/-- **Restricted telescope.**  A sum of `(a+|x|)^{-2}` over integers of modulus at least `R` is
bounded by `2/(a+R-1)`. -/
lemma telescope_abs_restricted (F : Finset ℤ) (a R : ℝ) (ha : 0 < a) (hR : 1 ≤ R)
    (hF : ∀ x ∈ F, R ≤ |(x : ℝ)|) :
    ∑ x ∈ F, (a + |(x : ℝ)|) ^ (-2 : ℝ) ≤ 2 / (a + R - 1) := by
  have hne : ∀ x ∈ F, x ≠ 0 := by
    intro x hx hx0
    have h := hF x hx
    rw [hx0] at h
    simp at h
    linarith
  set P := F.filter (fun x : ℤ => 0 < x) with hP
  set N := F.filter (fun x : ℤ => x < 0) with hN
  have hcover : F = P ∪ N := by
    ext x
    simp only [hP, hN, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inr ⟨hx, h⟩
      · exact absurd h (hne x hx)
      · exact Or.inl ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro x hxP hxN
    have h1 : 0 < x := (Finset.mem_filter.mp hxP).2
    have h2 : x < 0 := (Finset.mem_filter.mp hxN).2
    linarith
  have hPbound : ∑ x ∈ P, (a + |(x : ℝ)|) ^ (-2 : ℝ) ≤ 1 / (a + R - 1) := by
    have hinj : Set.InjOn (fun x : ℤ => x.natAbs) (↑P : Set ℤ) := by
      intro p hp q hq hpq
      have hp' : 0 < p := (Finset.mem_filter.mp hp).2
      have hq' : 0 < q := (Finset.mem_filter.mp hq).2
      have h1 : ((p.natAbs : ℕ) : ℤ) = p := Int.natAbs_of_nonneg (le_of_lt hp')
      have h2 : ((q.natAbs : ℕ) : ℤ) = q := Int.natAbs_of_nonneg (le_of_lt hq')
      have hpq' : p.natAbs = q.natAbs := hpq
      rw [← h1, ← h2, hpq']
    have hrew : ∑ x ∈ P, (a + |(x : ℝ)|) ^ (-2 : ℝ)
        = ∑ x ∈ P, (a + ((x.natAbs : ℕ) : ℝ)) ^ (-2 : ℝ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(natAbs_cast_real x).symm]
    have hsum2 : ∑ x ∈ P, (a + ((x.natAbs : ℕ) : ℝ)) ^ (-2 : ℝ)
        = ∑ n ∈ P.image (fun x : ℤ => x.natAbs), (a + (n : ℝ)) ^ (-2 : ℝ) :=
      (Finset.sum_image (f := fun n : ℕ => (a + (n : ℝ)) ^ (-2 : ℝ))
        (g := fun x : ℤ => x.natAbs) hinj).symm
    rw [hrew, hsum2]
    refine sum_shift_inv_sq_le _ a R ha hR ?_
    intro n hn
    obtain ⟨x, hxP, rfl⟩ := Finset.mem_image.mp hn
    have hx := hF x (Finset.mem_of_mem_filter x hxP)
    rwa [← natAbs_cast_real x] at hx
  have hNbound : ∑ x ∈ N, (a + |(x : ℝ)|) ^ (-2 : ℝ) ≤ 1 / (a + R - 1) := by
    have hinj : Set.InjOn (fun x : ℤ => x.natAbs) (↑N : Set ℤ) := by
      intro p hp q hq hpq
      have hp' : p < 0 := (Finset.mem_filter.mp hp).2
      have hq' : q < 0 := (Finset.mem_filter.mp hq).2
      have h1 : ((p.natAbs : ℕ) : ℤ) = -p := (Int.natCast_natAbs p).trans (abs_of_neg hp')
      have h2 : ((q.natAbs : ℕ) : ℤ) = -q := (Int.natCast_natAbs q).trans (abs_of_neg hq')
      have hpq' : p.natAbs = q.natAbs := hpq
      have hgoal : -p = -q := by rw [← h1, ← h2, hpq']
      linarith
    have hrew : ∑ x ∈ N, (a + |(x : ℝ)|) ^ (-2 : ℝ)
        = ∑ x ∈ N, (a + ((x.natAbs : ℕ) : ℝ)) ^ (-2 : ℝ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(natAbs_cast_real x).symm]
    have hsum2 : ∑ x ∈ N, (a + ((x.natAbs : ℕ) : ℝ)) ^ (-2 : ℝ)
        = ∑ n ∈ N.image (fun x : ℤ => x.natAbs), (a + (n : ℝ)) ^ (-2 : ℝ) :=
      (Finset.sum_image (f := fun n : ℕ => (a + (n : ℝ)) ^ (-2 : ℝ))
        (g := fun x : ℤ => x.natAbs) hinj).symm
    rw [hrew, hsum2]
    refine sum_shift_inv_sq_le _ a R ha hR ?_
    intro n hn
    obtain ⟨x, hxN, rfl⟩ := Finset.mem_image.mp hn
    have hx := hF x (Finset.mem_of_mem_filter x hxN)
    rwa [← natAbs_cast_real x] at hx
  have htotal : ∑ x ∈ F, (a + |(x : ℝ)|) ^ (-2 : ℝ)
      = ∑ x ∈ P, (a + |(x : ℝ)|) ^ (-2 : ℝ) + ∑ x ∈ N, (a + |(x : ℝ)|) ^ (-2 : ℝ) := by
    rw [hcover, Finset.sum_union hdisj]
  rw [htotal]
  calc ∑ x ∈ P, (a + |(x : ℝ)|) ^ (-2 : ℝ) + ∑ x ∈ N, (a + |(x : ℝ)|) ^ (-2 : ℝ)
      ≤ 1 / (a + R - 1) + 1 / (a + R - 1) := add_le_add hPbound hNbound
    _ = 2 / (a + R - 1) := by ring

/-- **Tail of the Hörmander condition.**  For a scale smaller than `|y|`, the sum of the
differences of the deviation kernel at lag `y` over `|x| ≥ 2|y|` is `O(σ n / |y|)`. -/
lemma devKern_tail_sum (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) (y : ℤ), y ≠ 0 →
      (σ n : ℝ) ≤ |(y : ℝ)| → ∀ F : Finset ℤ, (∀ x ∈ F, 2 * |(y : ℝ)| ≤ |(x : ℝ)|) →
      ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
        ≤ C * (σ n : ℝ) / |(y : ℝ)| := by
  obtain ⟨A, hApos, hA⟩ := devKernM_norm_le K
  refine ⟨4 * A + 1, by positivity, ?_⟩
  intro σ hσ1 n y hy hσy F hF
  have hym : (1 : ℝ) ≤ |(y : ℝ)| := le_trans (by exact_mod_cast hσ1 n) hσy
  have hsum1 : ∑ x ∈ F, (1 + |(((x - y : ℤ)) : ℝ)|) ^ (-2 : ℝ) ≤ 2 / |(y : ℝ)| := by
    have hinj : Set.InjOn (fun x : ℤ => x - y) (↑F : Set ℤ) := by
      intro p _ q _ h
      linarith
    have hreindex : ∑ x ∈ F, (1 + |(((x - y : ℤ)) : ℝ)|) ^ (-2 : ℝ)
        = ∑ u ∈ F.image (fun x : ℤ => x - y), (1 + |((u : ℤ) : ℝ)|) ^ (-2 : ℝ) :=
      (Finset.sum_image (f := fun u : ℤ => (1 + |((u : ℤ) : ℝ)|) ^ (-2 : ℝ))
        (g := fun x : ℤ => x - y) hinj).symm
    rw [hreindex]
    have hmain := telescope_abs_restricted (F.image (fun x : ℤ => x - y)) 1 |(y : ℝ)|
      (by norm_num) hym ?_
    · have hc : (1 : ℝ) + |(y : ℝ)| - 1 = |(y : ℝ)| := by ring
      rwa [hc] at hmain
    · intro u hu
      obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hu
      have hx := hF x hxF
      have hcast : (((x - y : ℤ)) : ℝ) = (x : ℝ) - (y : ℝ) := by push_cast; ring
      rw [hcast]
      have h1 : |(y : ℝ)| ≤ |(x : ℝ)| - |(y : ℝ)| := by linarith
      have h2 : |(x : ℝ)| - |(y : ℝ)| ≤ |(x : ℝ) - (y : ℝ)| := abs_sub_abs_le_abs_sub _ _
      linarith
  have hsum2 : ∑ x ∈ F, (1 + |((x : ℤ) : ℝ)|) ^ (-2 : ℝ) ≤ 2 / (1 + 2 * |(y : ℝ)| - 1) :=
    telescope_abs_restricted F 1 (2 * |(y : ℝ)|) (by norm_num) (by linarith) hF
  have h2' : 2 / (1 + 2 * |(y : ℝ)| - 1) ≤ 2 / |(y : ℝ)| := by
    have h1 : (1 : ℝ) + 2 * |(y : ℝ)| - 1 = 2 * |(y : ℝ)| := by ring
    rw [h1]
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * |(y : ℝ)|) (by linarith : (0 : ℝ) < |(y : ℝ)|)]
    linarith
  calc ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
      ≤ ∑ x ∈ F, (A * (σ n : ℝ) * (1 + |(((x - y : ℤ)) : ℝ)|) ^ (-2 : ℝ)
          + A * (σ n : ℝ) * (1 + |((x : ℤ) : ℝ)|) ^ (-2 : ℝ)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have h1 : devKern K σ n (x - y) = devKernM K (σ n) (x - y) :=
          devKern_eq_devKernM K σ n (x - y)
        have h2 : devKern K σ n x = devKernM K (σ n) x := devKern_eq_devKernM K σ n x
        rw [h1, h2]
        exact (norm_sub_le _ _).trans (add_le_add (hA (σ n) (hσ1 n) (x - y)) (hA (σ n) (hσ1 n) x))
    _ = A * (σ n : ℝ) * (∑ x ∈ F, (1 + |(((x - y : ℤ)) : ℝ)|) ^ (-2 : ℝ))
        + A * (σ n : ℝ) * (∑ x ∈ F, (1 + |((x : ℤ) : ℝ)|) ^ (-2 : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ A * (σ n : ℝ) * (2 / |(y : ℝ)|) + A * (σ n : ℝ) * (2 / |(y : ℝ)|) := by
        refine add_le_add ?_ ?_
        · refine mul_le_mul_of_nonneg_left hsum1 ?_
          exact mul_nonneg hApos.le (by positivity)
        · refine mul_le_mul_of_nonneg_left (le_trans hsum2 h2') ?_
          exact mul_nonneg hApos.le (by positivity)
    _ = (4 * A) * (σ n : ℝ) / |(y : ℝ)| := by
        rw [div_eq_mul_inv]
        ring
    _ ≤ (4 * A + 1) * (σ n : ℝ) / |(y : ℝ)| := by
        have hpos : 0 < |(y : ℝ)| := by linarith
        have hσnn : (0 : ℝ) ≤ (σ n : ℝ) := by positivity
        have h1 : (4 * A) * (σ n : ℝ) ≤ (4 * A + 1) * (σ n : ℝ) := by nlinarith
        calc (4 * A) * (σ n : ℝ) / |(y : ℝ)|
            = ((4 * A) * (σ n : ℝ)) * (|(y : ℝ)|)⁻¹ := by ring
          _ ≤ ((4 * A + 1) * (σ n : ℝ)) * (|(y : ℝ)|)⁻¹ :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = (4 * A + 1) * (σ n : ℝ) / |(y : ℝ)| := by ring

/-- The triangular kernel vanishes on `|j| ≥ 2 ^ L`. -/
lemma Work.Analysis.Hilbert.triKernel_eq_zero_of_le_abs (L : ℕ) {j : ℤ}
    (h : (2 : ℝ) ^ L ≤ |(j : ℝ)|) : Work.Analysis.Hilbert.triKernel L j = 0 := by
  rw [Work.Analysis.Hilbert.triKernel]
  refine max_eq_left ?_
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  linarith

/-- The triangular kernel is supported (at the level `lacLev σ n`) on `|x| ≤ 2 ^ lacLev σ n`. -/
lemma triKernel_diff_sum (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) (y : ℤ)
    (hyle : |(y : ℝ)| ≤ (σ n : ℝ)) (F : Finset ℤ) :
    ∑ x ∈ F, |Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
        - Work.Analysis.Hilbert.triKernel (lacLev σ n) x|
      ≤ 16 * |(y : ℝ)| / (σ n : ℝ) := by
  set l := lacLev σ n with hl
  set K₃ : ℤ := 3 * 2 ^ l with hK₃def
  have hm2le : (σ n : ℝ) ≤ 2 * (2 : ℝ) ^ l := by
    have h := le_two_pow_lacLev (σ := σ) n
    calc (σ n : ℝ) ≤ ((2 ^ (lacLev σ n + 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * (2 : ℝ) ^ l := by rw [hl]; push_cast; ring
  have hm2pos : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hK₃pos : (0 : ℤ) < K₃ := by
    rw [hK₃def]
    have h2 : (0 : ℤ) < 2 ^ l := pow_pos (by norm_num) l
    linarith
  have hK₃cast : ((K₃ : ℤ) : ℝ) = 3 * (2 : ℝ) ^ l := by
    rw [hK₃def]; push_cast; ring
  have hvan : ∀ x : ℤ, x ∉ Finset.Icc (-K₃) K₃ →
      Work.Analysis.Hilbert.triKernel l (x - y) - Work.Analysis.Hilbert.triKernel l x = 0 := by
    intro x hx
    have hxnot : ¬((-K₃) ≤ x ∧ x ≤ K₃) := Finset.mem_Icc.not.mp hx
    have hxabs : ((K₃ : ℤ) : ℝ) < |(x : ℝ)| := by
      rcases lt_or_ge x (-K₃) with h1 | h1
      · have h2' : (x : ℝ) < -((K₃ : ℤ) : ℝ) := by exact_mod_cast h1
        rw [abs_of_neg (by linarith), hK₃cast]
        linarith
      · have h2 : K₃ < x := by
          by_contra hcon
          exact hxnot ⟨h1, not_lt.mp hcon⟩
        have h2' : ((K₃ : ℤ) : ℝ) < (x : ℝ) := by exact_mod_cast h2
        rw [abs_of_pos (by linarith), hK₃cast]
        linarith
    have htri1 : Work.Analysis.Hilbert.triKernel l x = 0 := by
      refine Work.Analysis.Hilbert.triKernel_eq_zero_of_le_abs l ?_
      have h2 : (2 : ℝ) ^ l ≤ ((K₃ : ℤ) : ℝ) := by
        rw [hK₃cast]
        linarith [hm2pos]
      linarith
    have htri2 : Work.Analysis.Hilbert.triKernel l (x - y) = 0 := by
      refine Work.Analysis.Hilbert.triKernel_eq_zero_of_le_abs l ?_
      have hxy : ((x - y : ℤ) : ℝ) = (x : ℝ) - (y : ℝ) := by push_cast; ring
      rw [hxy]
      have h1 : ((K₃ : ℤ) : ℝ) - |(y : ℝ)| ≤ |(x : ℝ) - (y : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (x : ℝ) (y : ℝ)
        linarith [abs_sub_comm (x:ℝ) (y:ℝ)]
      have h2 : (2 : ℝ) ^ l ≤ ((K₃ : ℤ) : ℝ) - |(y : ℝ)| := by
        rw [hK₃cast]
        linarith [hm2le, hyle]
      linarith
    rw [htri1, htri2, sub_self]
  have hfilter : ∑ x ∈ F, |Work.Analysis.Hilbert.triKernel l (x - y)
        - Work.Analysis.Hilbert.triKernel l x|
      = ∑ x ∈ F.filter (fun x : ℤ => x ∈ Finset.Icc (-K₃) K₃),
          |Work.Analysis.Hilbert.triKernel l (x - y) - Work.Analysis.Hilbert.triKernel l x| := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun x : ℤ => x ∈ Finset.Icc (-K₃) K₃)]
    have hzero : ∑ x ∈ F.filter (fun x : ℤ => x ∉ Finset.Icc (-K₃) K₃),
        |Work.Analysis.Hilbert.triKernel l (x - y) - Work.Analysis.Hilbert.triKernel l x| = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [hvan x (Finset.mem_filter.mp hx).2, abs_zero]
    rw [hzero, add_zero]
  rw [hfilter]
  have hpoint : ∀ x : ℤ, |Work.Analysis.Hilbert.triKernel l (x - y)
      - Work.Analysis.Hilbert.triKernel l x| ≤ |(y : ℝ)| / (4 : ℝ) ^ l := by
    intro x
    have h := triKernel_lip l (x - y) x
    have hcast : (((x - y : ℤ)) : ℝ) - ((x : ℤ) : ℝ) = -(y : ℝ) := by push_cast; ring
    rw [hcast, abs_neg] at h
    exact h
  have hcard : (Finset.Icc (-K₃) K₃).card ≤ 6 * 2 ^ l + 1 := by
    rw [Int.card_Icc]
    have : K₃ + 1 - (-K₃) = 6 * 2 ^ l + 1 := by
      rw [hK₃def]; ring
    rw [this]
    simp
  calc ∑ x ∈ F.filter (fun x : ℤ => x ∈ Finset.Icc (-K₃) K₃),
        |Work.Analysis.Hilbert.triKernel l (x - y) - Work.Analysis.Hilbert.triKernel l x|
      ≤ ∑ x ∈ F.filter (fun x : ℤ => x ∈ Finset.Icc (-K₃) K₃), |(y : ℝ)| / (4 : ℝ) ^ l :=
        Finset.sum_le_sum fun x _ => hpoint x
    _ ≤ ∑ x ∈ Finset.Icc (-K₃) K₃, |(y : ℝ)| / (4 : ℝ) ^ l :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => (Finset.mem_filter.mp hx).2) (fun x _ _ => by positivity)
    _ ≤ (6 * 2 ^ l + 1) * (|(y : ℝ)| / (4 : ℝ) ^ l) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ 16 * |(y : ℝ)| / (σ n : ℝ) := by
        have h4l : (4 : ℝ) ^ l = ((2 : ℝ) ^ l) ^ 2 := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
          ring
        have h6 : (6 * (2 : ℝ) ^ l + 1) / (4 : ℝ) ^ l ≤ 16 / (σ n : ℝ) := by
          rw [h4l]
          have hm1 : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
          have hpos : (0 : ℝ) < ((2 : ℝ) ^ l) ^ 2 := by positivity
          have hσpos : (0 : ℝ) < (σ n : ℝ) := by
            have hn1 := hσ1 n
            exact_mod_cast (lt_of_lt_of_le zero_lt_one hn1)
          rw [div_le_div_iff₀ hpos hσpos]
          nlinarith [hm2le, hm1, hm2pos]
        calc (6 * 2 ^ l + 1) * (|(y : ℝ)| / (4 : ℝ) ^ l)
            = |(y : ℝ)| * ((6 * 2 ^ l + 1) / (4 : ℝ) ^ l) := by ring
          _ ≤ |(y : ℝ)| * (16 / (σ n : ℝ)) :=
              mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
          _ = 16 * |(y : ℝ)| / (σ n : ℝ) := by ring


/-- **Head of the Hörmander condition.**  For a scale larger than `|y|`, the sum of the differences
of the deviation kernel at lag `y` over `|x| ≥ 2|y|` is `O(|y| / σ n)`. -/
lemma devKern_head_sum (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (n : ℕ) (y : ℤ), y ≠ 0 →
      |(y : ℝ)| < (σ n : ℝ) → ∀ F : Finset ℤ, (∀ x ∈ F, 2 * |(y : ℝ)| ≤ |(x : ℝ)|) →
      ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖ ≤ C * |(y : ℝ)| / (σ n : ℝ) := by
  obtain ⟨B, hBpos, hB⟩ := bumpKernSmooth K
  refine ⟨2 * B + 16 * ‖lacConst K‖ + 1, by positivity, ?_⟩
  intro σ hσ1 n y hy hylt F hF
  have hm1 : (1 : ℝ) ≤ (σ n : ℝ) := by exact_mod_cast hσ1 n
  have hmpos : (0 : ℝ) < (σ n : ℝ) := by linarith
  have hyle : |(y : ℝ)| ≤ (σ n : ℝ) := le_of_lt hylt
  have hy1 : (1 : ℝ) ≤ |(y : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |y| := Int.one_le_abs hy
    have h2 : (1 : ℝ) ≤ ((|y| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_abs] at h2
  have hym2 : (1 : ℝ) ≤ 2 * |(y : ℝ)| := by linarith
  have hsum : ∑ x ∈ F, ((σ n : ℝ) + |(x : ℝ)|) ^ (-2 : ℝ) ≤ 2 / (σ n : ℝ) := by
    have hmain := telescope_abs_restricted F (σ n : ℝ) (2 * |(y : ℝ)|) hmpos hym2 hF
    have h1 : 0 < (σ n : ℝ) + 2 * |(y : ℝ)| - 1 := by linarith
    calc ∑ x ∈ F, ((σ n : ℝ) + |(x : ℝ)|) ^ (-2 : ℝ)
        ≤ 2 / ((σ n : ℝ) + 2 * |(y : ℝ)| - 1) := hmain
      _ ≤ 2 / (σ n : ℝ) := by
          rw [div_le_div_iff₀ h1 hmpos]
          linarith
  have hbump : ∑ x ∈ F, ‖bumpKern K σ n (x - y) - bumpKern K σ n x‖
      ≤ 2 * B * |(y : ℝ)| / (σ n : ℝ) := by
    have hterm : ∀ x ∈ F, ‖bumpKern K σ n (x - y) - bumpKern K σ n x‖
        ≤ B * |(y : ℝ)| * ((σ n : ℝ) + |(x : ℝ)|) ^ (-2 : ℝ) := by
      intro x _
      have h := hB (σ n) (hσ1 n) y hyle x
      have hgoal : ‖bumpKern K σ n (x - y) - bumpKern K σ n x‖
          = ‖bumpKernM K (σ n) (x - y) - bumpKernM K (σ n) x‖ := by
        rw [bumpKern_eq_bumpKernM, bumpKern_eq_bumpKernM]
      rw [hgoal]
      calc ‖bumpKernM K (σ n) (x - y) - bumpKernM K (σ n) x‖
          ≤ B * |(y : ℝ)| / ((σ n : ℝ) + |(x : ℝ)|) ^ 2 := h
        _ = B * |(y : ℝ)| * ((σ n : ℝ) + |(x : ℝ)|) ^ (-2 : ℝ) := by
            rw [div_eq_mul_inv, rpow_neg_two_eq (by positivity), one_div]
    calc ∑ x ∈ F, ‖bumpKern K σ n (x - y) - bumpKern K σ n x‖
        ≤ ∑ x ∈ F, B * |(y : ℝ)| * ((σ n : ℝ) + |(x : ℝ)|) ^ (-2 : ℝ) :=
          Finset.sum_le_sum hterm
      _ = B * |(y : ℝ)| * (∑ x ∈ F, ((σ n : ℝ) + |(x : ℝ)|) ^ (-2 : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ B * |(y : ℝ)| * (2 / (σ n : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * B * |(y : ℝ)| / (σ n : ℝ) := by ring
  have htri : ∑ x ∈ F, ‖lacConst K * (Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
        - Work.Analysis.Hilbert.triKernel (lacLev σ n) x)‖
      ≤ 16 * ‖lacConst K‖ * |(y : ℝ)| / (σ n : ℝ) := by
    have hmain := triKernel_diff_sum σ hσ1 n y hyle F
    calc ∑ x ∈ F, ‖lacConst K * (Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
          - Work.Analysis.Hilbert.triKernel (lacLev σ n) x)‖
        = ∑ x ∈ F, ‖lacConst K‖ * |Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
            - Work.Analysis.Hilbert.triKernel (lacLev σ n) x| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          have hcast : (((Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y) : ℝ)) : ℂ)
              - (((Work.Analysis.Hilbert.triKernel (lacLev σ n) x : ℝ)) : ℂ)
              = (((Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
                  - Work.Analysis.Hilbert.triKernel (lacLev σ n) x : ℝ)) : ℂ) := by
            push_cast
            ring
          rw [hcast, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = ‖lacConst K‖ * (∑ x ∈ F, |Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
            - Work.Analysis.Hilbert.triKernel (lacLev σ n) x|) := by
          rw [Finset.mul_sum]
      _ ≤ ‖lacConst K‖ * (16 * |(y : ℝ)| / (σ n : ℝ)) :=
          mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
      _ = 16 * ‖lacConst K‖ * |(y : ℝ)| / (σ n : ℝ) := by ring
  have hpoint : ∀ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
      ≤ ‖bumpKern K σ n (x - y) - bumpKern K σ n x‖
        + ‖lacConst K * (Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
            - Work.Analysis.Hilbert.triKernel (lacLev σ n) x)‖ := by
    intro x _
    have hcast : ∀ (p q c : ℂ) (r s : ℝ),
        (p - c * ((r : ℝ) : ℂ)) - (q - c * ((s : ℝ) : ℂ))
          = (p - q) - c * (((r : ℝ) : ℂ) - ((s : ℝ) : ℂ)) := by
      intro p q c r s
      ring
    have h1 : devKern K σ n (x - y) - devKern K σ n x
        = (bumpKern K σ n (x - y) - bumpKern K σ n x)
          - lacConst K * (Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
            - Work.Analysis.Hilbert.triKernel (lacLev σ n) x) := by
      rw [devKern, devKern]
      exact hcast _ _ _ _ _
    rw [h1]
    exact norm_sub_le _ _
  calc ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
      ≤ ∑ x ∈ F, (‖bumpKern K σ n (x - y) - bumpKern K σ n x‖
          + ‖lacConst K * (Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
            - Work.Analysis.Hilbert.triKernel (lacLev σ n) x)‖) :=
        Finset.sum_le_sum hpoint
    _ = (∑ x ∈ F, ‖bumpKern K σ n (x - y) - bumpKern K σ n x‖)
        + ∑ x ∈ F, ‖lacConst K * (Work.Analysis.Hilbert.triKernel (lacLev σ n) (x - y)
            - Work.Analysis.Hilbert.triKernel (lacLev σ n) x)‖ :=
        Finset.sum_add_distrib
    _ ≤ 2 * B * |(y : ℝ)| / (σ n : ℝ) + 16 * ‖lacConst K‖ * |(y : ℝ)| / (σ n : ℝ) :=
        add_le_add hbump htri
    _ ≤ (2 * B + 16 * ‖lacConst K‖ + 1) * |(y : ℝ)| / (σ n : ℝ) := by
        have h1 : 2 * B * |(y : ℝ)| / (σ n : ℝ) + 16 * ‖lacConst K‖ * |(y : ℝ)| / (σ n : ℝ)
            = (2 * B + 16 * ‖lacConst K‖) * |(y : ℝ)| / (σ n : ℝ) := by ring
        rw [h1]
        have h2 : (2 * B + 16 * ‖lacConst K‖) * (|(y : ℝ)| / (σ n : ℝ))
            ≤ (2 * B + 16 * ‖lacConst K‖ + 1) * (|(y : ℝ)| / (σ n : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · linarith
          · positivity
        calc (2 * B + 16 * ‖lacConst K‖) * |(y : ℝ)| / (σ n : ℝ)
            = (2 * B + 16 * ‖lacConst K‖) * (|(y : ℝ)| / (σ n : ℝ)) := by ring
          _ ≤ (2 * B + 16 * ‖lacConst K‖ + 1) * (|(y : ℝ)| / (σ n : ℝ)) := h2
          _ = (2 * B + 16 * ‖lacConst K‖ + 1) * |(y : ℝ)| / (σ n : ℝ) := by ring


/-- **The discrete Hörmander condition for the linearised deviation kernels.** -/
theorem lacDevHormander (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
      (U : Finset ℕ) (ω : ℕ → Bool) (y : ℤ), y ≠ 0 →
      ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
        ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ₑ
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := devKern_head_sum K
  obtain ⟨C₂, hC₂pos, hC₂⟩ := devKern_tail_sum K
  refine ⟨2 * C₁ + 2 * C₂ + 1, by positivity, ?_⟩
  intro σ hσ1 hσ2 U ω y hy
  have hset : {x : ℤ | 2 * y.natAbs ≤ x.natAbs} = {x : ℤ | 2 * |(y : ℝ)| ≤ |(x : ℝ)|} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [← natAbs_cast_real x, ← natAbs_cast_real y]
    constructor <;> intro h <;> exact_mod_cast h
  have hypos : (0 : ℝ) < |(y : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |y| := Int.one_le_abs hy
    have h2 : (1 : ℝ) ≤ ((|y| : ℤ) : ℝ) := by exact_mod_cast h1
    have h3 : (1 : ℝ) ≤ |(y : ℝ)| := by rwa [Int.cast_abs] at h2
    linarith
  rw [hset]
  refine lintegralCount_le_of_finset_le (B := 2 * C₁ + 2 * C₂ + 1) ?_
  intro F hF
  have hnorm : (fun x : ℤ => ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ₑ)
      = fun x : ℤ => ENNReal.ofReal ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ := by
    funext x
    simp
  rw [hnorm, ← ENNReal.ofReal_sum_of_nonneg (fun x _ => norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpoint : ∀ x : ℤ, ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖
      ≤ ∑ n ∈ U, ‖devKern K σ n (x - y) - devKern K σ n x‖ := by
    intro x
    have h1 : lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x
        = ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n
            * (devKern K σ n (x - y) - devKern K σ n x) := by
      rw [lacDevLin, lacDevLin, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (Work.KMTAreas.ADev.norm_bSign_le ω n)
  have hhead : ∑ n ∈ U.filter (fun n => |(y : ℝ)| < (σ n : ℝ)),
        ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖ ≤ 2 * C₁ := by
    have hterm : ∀ n ∈ U.filter (fun n => |(y : ℝ)| < (σ n : ℝ)),
        ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
          ≤ C₁ * |(y : ℝ)| / (σ n : ℝ) := by
      intro n hn
      exact hC₁ σ hσ1 n y hy (Finset.mem_filter.mp hn).2 F hF
    calc ∑ n ∈ U.filter (fun n => |(y : ℝ)| < (σ n : ℝ)),
          ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
        ≤ ∑ n ∈ U.filter (fun n => |(y : ℝ)| < (σ n : ℝ)),
            C₁ * |(y : ℝ)| / (σ n : ℝ) := Finset.sum_le_sum hterm
      _ = C₁ * |(y : ℝ)| * (∑ n ∈ U.filter (fun n => |(y : ℝ)| < (σ n : ℝ)),
            ((σ n : ℝ))⁻¹) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by rw [div_eq_mul_inv]
      _ ≤ C₁ * |(y : ℝ)| * (2 / |(y : ℝ)|) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine lacunary_sum_inv_le σ hσ2 _ hypos ?_
          intro n hn
          exact le_of_lt (Finset.mem_filter.mp hn).2
      _ = 2 * C₁ := by
          field_simp
  have htail : ∑ n ∈ U.filter (fun n => ¬ (|(y : ℝ)| < (σ n : ℝ))),
        ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖ ≤ 2 * C₂ := by
    have hterm : ∀ n ∈ U.filter (fun n => ¬ (|(y : ℝ)| < (σ n : ℝ))),
        ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
          ≤ C₂ * (σ n : ℝ) / |(y : ℝ)| := by
      intro n hn
      exact hC₂ σ hσ1 n y hy (not_lt.mp (Finset.mem_filter.mp hn).2) F hF
    calc ∑ n ∈ U.filter (fun n => ¬ (|(y : ℝ)| < (σ n : ℝ))),
          ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
        ≤ ∑ n ∈ U.filter (fun n => ¬ (|(y : ℝ)| < (σ n : ℝ))),
            C₂ * (σ n : ℝ) / |(y : ℝ)| := Finset.sum_le_sum hterm
      _ = C₂ / |(y : ℝ)| * (∑ n ∈ U.filter (fun n => ¬ (|(y : ℝ)| < (σ n : ℝ))),
            (σ n : ℝ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ C₂ / |(y : ℝ)| * (2 * |(y : ℝ)|) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine lacunary_sum_le σ hσ2 _ (abs_nonneg _) ?_
          intro n hn
          exact not_lt.mp (Finset.mem_filter.mp hn).2
      _ = 2 * C₂ := by
          field_simp
  calc ∑ x ∈ F, ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖
      ≤ ∑ x ∈ F, ∑ n ∈ U, ‖devKern K σ n (x - y) - devKern K σ n x‖ :=
        Finset.sum_le_sum fun x _ => hpoint x
    _ = ∑ n ∈ U, ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖ := Finset.sum_comm
    _ = ∑ n ∈ U.filter (fun n => |(y : ℝ)| < (σ n : ℝ)),
          ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖
        + ∑ n ∈ U.filter (fun n => ¬ (|(y : ℝ)| < (σ n : ℝ))),
          ∑ x ∈ F, ‖devKern K σ n (x - y) - devKern K σ n x‖ :=
        (Finset.sum_filter_add_sum_filter_not U (fun n => |(y : ℝ)| < (σ n : ℝ)) _).symm
    _ ≤ 2 * C₁ + 2 * C₂ := add_le_add hhead htail
    _ ≤ 2 * C₁ + 2 * C₂ + 1 := by linarith


/-- `∑_{n ∈ U} ((σ n : ℝ)^2)⁻¹ ≤ 2`. -/
lemma sum_inv_sq_scale_le_two (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (U : Finset ℕ) :
    ∑ n ∈ U, (((σ n : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
  refine (Finset.sum_le_sum fun n _ => ?_).trans (sum_inv_scale_le_two σ hσ1 hσ2 U)
  have h1 : (1 : ℝ) ≤ ((σ n : ℕ) : ℝ) := by exact_mod_cast hσ1 n
  have hpos : (0 : ℝ) < ((σ n : ℕ) : ℝ) := by linarith
  have hinv0 : (0 : ℝ) ≤ (((σ n : ℕ) : ℝ))⁻¹ := by positivity
  have hinv1 : (((σ n : ℕ) : ℝ))⁻¹ ≤ 1 := by
    have h := one_div_le_one_div_of_le (a := (1 : ℝ)) (b := ((σ n : ℕ) : ℝ)) one_pos h1
    simpa [one_div] using h
  rw [← inv_pow, pow_two]
  nlinarith [hinv0, hinv1]

/-- **The uniform symbol bound for the linearised deviation kernel.** -/
theorem lacDevSymBound (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
      (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ),
      ‖∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ‖ ≤ C := by
  obtain ⟨L₀, hL₀, hlip⟩ := fourierLipschitzAtZero K
  obtain ⟨A, hApos, hAb⟩ := bumpSymQuad K hL₀ hlip
  have hAnn : (0 : ℝ) ≤ A := hApos.le
  have hcnn : (0 : ℝ) ≤ ‖lacConst K‖ := norm_nonneg _
  set M : ℝ := max (A / 4 + 8 * ‖lacConst K‖) (4 * Real.pi ^ 2 * A + 64 * ‖lacConst K‖) with hM
  have hK1 : A / 4 + 8 * ‖lacConst K‖ ≤ M := by rw [hM]; exact le_max_left _ _
  have hK2 : 4 * Real.pi ^ 2 * A + 64 * ‖lacConst K‖ ≤ M := by rw [hM]; exact le_max_right _ _
  have hMnn : (0 : ℝ) ≤ M :=
    le_trans (by positivity : (0 : ℝ) ≤ A / 4 + 8 * ‖lacConst K‖) hK1
  refine ⟨2 * A + 4 * M + 1, by linarith, ?_⟩
  intro σ hσ1 hσ2 U ω θ
  obtain ⟨hnd_le, h4z, h2πz, hfar, hdbl⟩ := nearIntFacts θ
  have hz0 : 0 ≤ zGap θ := norm_nonneg _
  have hbound : ∀ n ∈ U,
      ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ
          - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
        ≤ A * ((((σ n : ℕ) : ℝ)) ^ 2)⁻¹
          + M * min (((σ n : ℕ) : ℝ) * zGap θ) ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by
    intro n _
    obtain ⟨hb1, hb2⟩ := hAb (σ n) (hσ1 n) θ
    have ht1 : ‖(1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
        ≤ 4 * (2 : ℝ) ^ (lacLev σ n) * zGap θ := triSym_sub_one_le_zGap h4z (lacLev σ n)
    have hσpos : (0 : ℝ) < ((σ n : ℕ) : ℝ) := by
      have hn1 := hσ1 n
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hn1)
    have h2l_le : (2 : ℝ) ^ (lacLev σ n) ≤ 2 * ((σ n : ℕ) : ℝ) := by
      have h := pow_lacLev_le hσ1 n
      calc (2 : ℝ) ^ (lacLev σ n) = (((2 : ℕ) ^ lacLev σ n : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 * σ n : ℕ) : ℝ) := by exact_mod_cast h
        _ = 2 * ((σ n : ℕ) : ℝ) := by push_cast; ring
    have h2l_ge : ((σ n : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ (lacLev σ n) := by
      have h := le_two_pow_lacLev (σ := σ) n
      calc ((σ n : ℕ) : ℝ) ≤ ((2 ^ (lacLev σ n + 1) : ℕ) : ℝ) := by exact_mod_cast h
        _ = 2 * (2 : ℝ) ^ (lacLev σ n) := by push_cast; ring
    by_cases hcase : ((σ n : ℕ) : ℝ) * zGap θ ≤ 1
    · have hmin : min (((σ n : ℕ) : ℝ) * zGap θ) ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹)
          = ((σ n : ℕ) : ℝ) * zGap θ := by
        refine min_eq_left ?_
        rcases eq_or_lt_of_le (mul_nonneg hσpos.le hz0) with h0 | hpos
        · rw [← h0, inv_zero]
        · rw [inv_eq_one_div, le_div_iff₀ hpos]
          nlinarith [hcase, hpos]
      have htri : ‖lacConst K * ((1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖
          ≤ 8 * ‖lacConst K‖ * (((σ n : ℕ) : ℝ) * zGap θ) := by
        rw [norm_mul]
        calc ‖lacConst K‖ * ‖(1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
            ≤ ‖lacConst K‖ * (4 * (2 : ℝ) ^ (lacLev σ n) * zGap θ) :=
              mul_le_mul_of_nonneg_left ht1 hcnn
          _ ≤ ‖lacConst K‖ * (4 * (2 * ((σ n : ℕ) : ℝ)) * zGap θ) := by
              refine mul_le_mul_of_nonneg_left ?_ hcnn
              nlinarith [h2l_le, hz0]
          _ = 8 * ‖lacConst K‖ * (((σ n : ℕ) : ℝ) * zGap θ) := by ring
      have hsplit : Work.KMTAreas.ADev.bumpSym K (σ n) θ
            - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ
          = (Work.KMTAreas.ADev.bumpSym K (σ n) θ - lacConst K)
            + lacConst K * ((1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ) := by ring
      rw [hsplit, hmin]
      have hkey : A * (((σ n : ℕ) : ℝ) * nearDist θ)
            + 8 * ‖lacConst K‖ * (((σ n : ℕ) : ℝ) * zGap θ)
          ≤ M * (((σ n : ℕ) : ℝ) * zGap θ) := by
        have hσd : A * (((σ n : ℕ) : ℝ) * nearDist θ)
            ≤ (A / 4) * (((σ n : ℕ) : ℝ) * zGap θ) := by
          have h1 : ((σ n : ℕ) : ℝ) * nearDist θ ≤ (((σ n : ℕ) : ℝ) * zGap θ) / 4 := by
            nlinarith [h4z, hσpos]
          have h2 := mul_le_mul_of_nonneg_left h1 hAnn
          linarith [h2]
        have h2 : (A / 4 + 8 * ‖lacConst K‖) * (((σ n : ℕ) : ℝ) * zGap θ)
            ≤ M * (((σ n : ℕ) : ℝ) * zGap θ) :=
          mul_le_mul_of_nonneg_right hK1 (mul_nonneg hσpos.le hz0)
        have h3 : (A / 4 + 8 * ‖lacConst K‖) * (((σ n : ℕ) : ℝ) * zGap θ)
            = (A / 4) * (((σ n : ℕ) : ℝ) * zGap θ)
              + 8 * ‖lacConst K‖ * (((σ n : ℕ) : ℝ) * zGap θ) := by ring
        linarith [hσd, h2, h3]
      calc ‖(Work.KMTAreas.ADev.bumpSym K (σ n) θ - lacConst K)
              + lacConst K * ((1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖
          ≤ ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ - lacConst K‖
            + ‖lacConst K * ((1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖ :=
            norm_add_le _ _
        _ ≤ (A * ((((σ n : ℕ) : ℝ)) ^ 2)⁻¹ + A * (((σ n : ℕ) : ℝ) * nearDist θ))
              + 8 * ‖lacConst K‖ * (((σ n : ℕ) : ℝ) * zGap θ) := add_le_add hb1 htri
        _ ≤ A * ((((σ n : ℕ) : ℝ)) ^ 2)⁻¹ + M * (((σ n : ℕ) : ℝ) * zGap θ) := by
            linarith [hkey]
    · have hge : 1 ≤ ((σ n : ℕ) : ℝ) * zGap θ := le_of_lt (not_le.mp hcase)
      have hwpos : 0 < ((σ n : ℕ) : ℝ) * zGap θ := lt_of_lt_of_le one_pos hge
      have hzpos : 0 < zGap θ := by
        rcases (mul_pos_iff.mp hwpos) with h | h
        · exact h.2
        · exact absurd h.2 (not_lt.mpr hz0)
      have hinv1 : (((σ n : ℕ) : ℝ) * zGap θ)⁻¹ ≤ 1 :=
        (inv_le_one₀ hwpos).mpr hge
      have hmin : min (((σ n : ℕ) : ℝ) * zGap θ) ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹)
          = ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by
        refine min_eq_right ?_
        linarith
      have htri2 : ‖lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
          ≤ 64 * ‖lacConst K‖ * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by
        rw [norm_mul]
        have htri_le : ‖Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
            ≤ 5 / ((2 : ℝ) ^ (lacLev σ n) * zGap θ) := by
          have h := zGap_mul_triSym_le (lacLev σ n) θ
          rw [le_div_iff₀ (by positivity)]
          calc ‖Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
                * ((2 : ℝ) ^ (lacLev σ n) * zGap θ)
              = zGap θ * ‖Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
                * (2 : ℝ) ^ (lacLev σ n) := by ring
            _ ≤ (5 / (2 : ℝ) ^ (lacLev σ n)) * (2 : ℝ) ^ (lacLev σ n) :=
                mul_le_mul_of_nonneg_right h (by positivity)
            _ = 5 := by field_simp
        have hkey : 5 / ((2 : ℝ) ^ (lacLev σ n) * zGap θ)
            ≤ 64 * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by
          rw [inv_eq_one_div, show (64 : ℝ) * (1 / (((σ n : ℕ) : ℝ) * zGap θ))
              = 64 / (((σ n : ℕ) : ℝ) * zGap θ) by ring]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h2l : (0 : ℝ) < (2 : ℝ) ^ (lacLev σ n) := by positivity
          nlinarith [h2l_ge, hzpos, h2l]
        calc ‖lacConst K‖ * ‖Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
            ≤ ‖lacConst K‖ * (5 / ((2 : ℝ) ^ (lacLev σ n) * zGap θ)) :=
              mul_le_mul_of_nonneg_left htri_le hcnn
          _ ≤ ‖lacConst K‖ * (64 * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹)) :=
              mul_le_mul_of_nonneg_left hkey hcnn
          _ = 64 * ‖lacConst K‖ * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by ring
      have h1 : A * ((1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2)⁻¹
          ≤ 4 * Real.pi ^ 2 * A * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by
        have hpipos : 0 < 2 * Real.pi := by positivity
        have hle : ((σ n : ℕ) : ℝ) * zGap θ / (2 * Real.pi)
            ≤ 1 + ((σ n : ℕ) : ℝ) * nearDist θ := by
          rw [div_le_iff₀ hpipos]
          have hh : ((σ n : ℕ) : ℝ) * zGap θ
              ≤ ((σ n : ℕ) : ℝ) * (2 * Real.pi * nearDist θ) :=
            mul_le_mul_of_nonneg_left h2πz hσpos.le
          nlinarith [hh, hpipos, hσpos]
        have hsq : (((σ n : ℕ) : ℝ) * zGap θ / (2 * Real.pi)) ^ 2
            ≤ (1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hle 2
        have h1' : ((1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2)⁻¹
            ≤ ((((σ n : ℕ) : ℝ) * zGap θ / (2 * Real.pi)) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) hsq
        have h2' : ((((σ n : ℕ) : ℝ) * zGap θ / (2 * Real.pi)) ^ 2)⁻¹
            = 4 * Real.pi ^ 2 * (((((σ n : ℕ) : ℝ) * zGap θ) ^ 2)⁻¹) := by
          rw [div_pow, div_eq_mul_inv, mul_inv, inv_inv]
          ring
        have h3 : (((((σ n : ℕ) : ℝ) * zGap θ) ^ 2)⁻¹) ≤ ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by
          rw [← inv_pow]
          nlinarith [hinv1, (inv_pos.mpr hwpos).le]
        calc A * ((1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2)⁻¹
            ≤ A * (4 * Real.pi ^ 2 * (((((σ n : ℕ) : ℝ) * zGap θ) ^ 2)⁻¹)) := by
              rw [← h2']
              exact mul_le_mul_of_nonneg_left h1' hAnn
          _ = 4 * Real.pi ^ 2 * A * (((((σ n : ℕ) : ℝ) * zGap θ) ^ 2)⁻¹) := by ring
          _ ≤ 4 * Real.pi ^ 2 * A * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      rw [hmin]
      have hstep : A * ((1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2)⁻¹
            + 64 * ‖lacConst K‖ * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) ≤ M * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by
        have hw_inv_nn : (0 : ℝ) ≤ ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := (inv_pos.mpr hwpos).le
        have h2 := mul_le_mul_of_nonneg_right hK2 hw_inv_nn
        have h3 : (4 * Real.pi ^ 2 * A + 64 * ‖lacConst K‖) * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹)
            = 4 * Real.pi ^ 2 * A * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹)
              + 64 * ‖lacConst K‖ * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by ring
        linarith [h1, h2, h3]
      calc ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ
              - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
          ≤ ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ‖
            + ‖lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖ := norm_sub_le _ _
        _ ≤ (A * ((((σ n : ℕ) : ℝ)) ^ 2)⁻¹
              + A * ((1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2)⁻¹)
              + 64 * ‖lacConst K‖ * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := add_le_add hb2 htri2
        _ ≤ A * ((((σ n : ℕ) : ℝ)) ^ 2)⁻¹ + M * ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹) := by
            linarith [hstep]
  have h1 : ∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ
      = ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n
          * (Work.KMTAreas.ADev.bumpSym K (σ n) θ
              - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ) := by
    rw [lacDevLin_tsum_eq K σ hσ1 U ω θ]
    exact Finset.sum_congr rfl fun n _ => by rw [lacDevPerScaleSym K σ hσ1 n θ]
  rw [h1]
  have hstep : ∑ n ∈ U, ‖Work.KMTAreas.ADev.bSign ω n
        * (Work.KMTAreas.ADev.bumpSym K (σ n) θ
            - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖
      ≤ ∑ n ∈ U, ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ
            - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖ := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (Work.KMTAreas.ADev.norm_bSign_le ω n)
  calc ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n
        * (Work.KMTAreas.ADev.bumpSym K (σ n) θ
            - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖
      ≤ ∑ n ∈ U, ‖Work.KMTAreas.ADev.bSign ω n
          * (Work.KMTAreas.ADev.bumpSym K (σ n) θ
              - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ U, ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ
            - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖ := hstep
    _ ≤ ∑ n ∈ U, (A * ((((σ n : ℕ) : ℝ)) ^ 2)⁻¹
          + M * min (((σ n : ℕ) : ℝ) * zGap θ) ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹)) :=
        Finset.sum_le_sum hbound
    _ = A * (∑ n ∈ U, ((((σ n : ℕ) : ℝ)) ^ 2)⁻¹)
        + M * (∑ n ∈ U, min (((σ n : ℕ) : ℝ) * zGap θ) ((((σ n : ℕ) : ℝ) * zGap θ)⁻¹)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ A * 2 + M * 4 := by
        refine add_le_add (mul_le_mul_of_nonneg_left (sum_inv_sq_scale_le_two σ hσ1 hσ2 U) hAnn) ?_
        exact mul_le_mul_of_nonneg_left (lacSumMin hσ1 hσ2 (zGap θ) hz0 U) hMnn
    _ ≤ 2 * A + 4 * M + 1 := by linarith


/-! ## The assembly of the lacunary bump-dilation variational estimate -/

/-- The `eLpNorm` of an `ℝ≥0∞`-valued function on `ℤ` (counting measure) is the `L^p` "norm". -/
theorem eLpNorm_count_ennreal_eq (p : ℝ) (hp : 0 < p) (F : ℤ → ℝ≥0∞) :
    MeasureTheory.eLpNorm F (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = (∫⁻ y : ℤ, F y ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  exact congrArg (fun z => z ^ (1 / p)) (lintegral_congr fun y => by rw [enorm_eq_self])

/-- **Minkowski's inequality for `ℝ≥0∞`-valued functions on `ℤ`** (two terms). -/
theorem eLpNorm_count_add_le (p : ℝ) (hp : 1 ≤ p) (F G : ℤ → ℝ≥0∞) :
    MeasureTheory.eLpNorm (fun y : ℤ => F y + G y) (ENNReal.ofReal p)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ MeasureTheory.eLpNorm F (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        + MeasureTheory.eLpNorm G (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [eLpNorm_count_ennreal_eq p hp0 (fun y : ℤ => F y + G y),
    eLpNorm_count_ennreal_eq p hp0 F, eLpNorm_count_ennreal_eq p hp0 G]
  exact ENNReal.lintegral_Lp_add_le (μ := MeasureTheory.Measure.count)
    (measurable_of_countable F).aemeasurable (measurable_of_countable G).aemeasurable hp

/-- The variational norm of the deviation sequence is dominated by the values square function. -/
theorem dev_var_le_sqSum (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (r : NNReal) (hr : 2 ≤ r)
    (f : ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => devOp K σ n f x) ≤
      ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) *
        (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  variationalNorm_le_sqSum hr _

/-- The variational norm of the (scaled) triangular smoothing sequence is the scalar times the
variational norm of the smoothing sequence. -/
theorem tri_var_smul (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (r : NNReal) (hr : 1 ≤ r)
    (f : ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => lacConst K * triSmooth σ n f x) =
      ‖lacConst K‖ₑ * PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => triSmooth σ n f x) := by
  have hfun : (fun n : ℕ => lacConst K * triSmooth σ n f x)
      = lacConst K • (fun n : ℕ => triSmooth σ n f x) := rfl
  rw [hfun]
  exact Submission.PointwiseErgodicTheorems.variationalNorm_smul hr (lacConst K) _

/-- **The assembly step.**  From the two halves one obtains the target estimate. -/
theorem lacunaryBumpDilationVar_of_pieces (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r)
    (K : SchwartzMap ℝ ℂ)
    (hTri : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) →
      (∀ n, 2 * σ n ≤ σ (n + 1)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => triSmooth σ n f x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C₁ * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count)
    (hDev : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) →
      (∀ n, 2 * σ n ≤ σ (n + 1)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C₂ * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
      (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / (σ n : ℝ)) * K ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨C₁, hC₁pos, hTri'⟩ := hTri
  obtain ⟨C₂, hC₂pos, hDev'⟩ := hDev
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hr2 : (2 : NNReal) ≤ r := le_of_lt hr
  have hcne : ‖lacConst K‖ₑ ≠ ⊤ := enorm_ne_top
  set D : ℝ := 2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  refine ⟨(‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1, by positivity, ?_⟩
  intro σ hσ1 hσ2 f
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bumpOp K σ n f x)
      ≤ ‖lacConst K‖ₑ * PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => triSmooth σ n f x)
        + ENNReal.ofReal D * (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    intro x
    have hseq : (fun n : ℕ => bumpOp K σ n f x)
        = (fun n : ℕ => lacConst K * triSmooth σ n f x) + (fun n : ℕ => devOp K σ n f x) := by
      funext n
      rw [Pi.add_apply, bump_decomp K σ n f x]
    rw [hseq]
    refine (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _).trans ?_
    rw [tri_var_smul K σ r hr1 f x]
    refine add_le_add le_rfl ?_
    rw [hD]
    exact dev_var_le_sqSum K σ r hr2 f x
  have hpt' : ∀ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bumpOp K σ n f x)‖ₑ
      ≤ ‖‖lacConst K‖ₑ * PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => triSmooth σ n f x)
        + ENNReal.ofReal D * (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)‖ₑ :=
    fun x => by simpa only [enorm_eq_self] using hpt x
  have hbump : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ∑' j : ℤ, (1 / (σ n : ℝ)) * K ((j : ℝ) / (σ n)) * f (x - j)))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bumpOp K σ n f x) :=
    rfl
  rw [hbump]
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt').trans ?_
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (eLpNorm_count_add_le p hp.le
      (fun x : ℤ => ‖lacConst K‖ₑ * PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => triSmooth σ n f x))
      (fun x : ℤ => ENNReal.ofReal D * (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))).trans ?_
  rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal hcne hp0 hptop,
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal ENNReal.ofReal_ne_top hp0 hptop]
  set A : ℝ≥0∞ := MeasureTheory.eLpNorm f (ENNReal.ofReal p)
      (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
  set A₁ : ℝ≥0∞ := MeasureTheory.eLpNorm
      (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => triSmooth σ n f x))
      (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
  set A₂ : ℝ≥0∞ := MeasureTheory.eLpNorm
      (fun x : ℤ => (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
  have hcoef : ‖lacConst K‖ₑ * ENNReal.ofReal C₁ + ENNReal.ofReal D * ENNReal.ofReal C₂
      ≤ ENNReal.ofReal ((‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1) := by
    have hreal : ‖lacConst K‖ₑ.toReal * C₁ + D * C₂
        ≤ (‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1 := by
      nlinarith [hC₁pos, hC₂pos, hDpos, ENNReal.toReal_nonneg (a := ‖lacConst K‖ₑ)]
    calc ‖lacConst K‖ₑ * ENNReal.ofReal C₁ + ENNReal.ofReal D * ENNReal.ofReal C₂
        = ENNReal.ofReal (‖lacConst K‖ₑ.toReal) * ENNReal.ofReal C₁
            + ENNReal.ofReal D * ENNReal.ofReal C₂ := by
            conv_lhs => rw [← ENNReal.ofReal_toReal hcne]
      _ = ENNReal.ofReal (‖lacConst K‖ₑ.toReal * C₁) + ENNReal.ofReal (D * C₂) := by
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hDpos.le]
      _ = ENNReal.ofReal (‖lacConst K‖ₑ.toReal * C₁ + D * C₂) := by
          rw [ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hC₁pos.le)
            (mul_nonneg hDpos.le hC₂pos.le)]
      _ ≤ ENNReal.ofReal ((‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1) :=
          ENNReal.ofReal_le_ofReal hreal
  calc ‖lacConst K‖ₑ * A₁ + ENNReal.ofReal D * A₂
      ≤ ‖lacConst K‖ₑ * (ENNReal.ofReal C₁ * A) + ENNReal.ofReal D * (ENNReal.ofReal C₂ * A) := by
        have h1 : A₁ ≤ ENNReal.ofReal C₁ * A := hTri' σ hσ1 hσ2 f
        have h2 : A₂ ≤ ENNReal.ofReal C₂ * A := hDev' σ hσ1 hσ2 f
        gcongr
    _ = (‖lacConst K‖ₑ * ENNReal.ofReal C₁ + ENNReal.ofReal D * ENNReal.ofReal C₂) * A := by ring
    _ ≤ ENNReal.ofReal ((‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1) * A := by
        gcongr

/-- The Jones--Seeger--Wright (JSW) / Lépingle lacunary variational estimate for discrete low-pass (bump) convolution operators on `ℤ`: for a fixed Schwartz kernel `K` and a `2`-lacunary sequence of integral scales `σ`, the `r`-variation (`2 < r`) of the family `f ↦ (K_{σ_n} * f)(x) = Σ_j (1/σ_n) K (j/σ_n) f (x - j)` is bounded on `ℓ^p(ℤ)`, `1 < p < ∞`, by a constant times `‖f‖_{ℓ^p}`.  This is stated verbatim in `Submission/Work/KMTAreas/A7/lacunaryBumpDilationVar.lean` (which derives it from `Work.KMTAreas.A7.lacDilTriVar` [proved] and `Work.KMTAreas.A7.lacDilDevSqSum` [a stub]); below the stub the chain is `Submission/Work/KMTAreas/A7/LacDevAssembly.lean` (`lacDilDevSqSum_of_inputs`, proved, from `Work.KMTAreas.A7.lacDevSymBound` and `Work.KMTAreas.A7.lacDevHormander` — the only two unproved inputs of the chain — plus the proved `Work.KMTAreas.A7.lacDevL2`).  Copy the poisoned wrappers into your own file (do not import `lacDilDevSqSum`, `LacDevAssembly` or `lacunaryBumpDilationVar`, whose unproved content would contaminate the dependency check).  Related proved material: `lacDilTriVar.lean`, `LacDevBasics.lean`, `lacDevL2.lean`, `LacDevHormanderSetup.lean`, `lacDevBumpSymQuad.lean`, `lacDevPerScaleSym.lean`, `LacDevSymDefs.lean`, `LacDevDefs.lean`, `variationalNorm_le_sqSum.lean`. -/
theorem DilVar (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
      (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / (σ n : ℝ)) * K ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨Csym, hCsympos, hsym⟩ := lacDevSymBound K
  obtain ⟨A2, hA2pos, hA2⟩ := lacDevL2 K Csym hCsympos hsym
  obtain ⟨Ak, hAkpos, hAk⟩ := lacDevHormander K
  obtain ⟨Cdev, hCdevpos, hDev⟩ :=
    lacDilDevSqSum_of_inputs p hp K Csym hCsympos hsym ⟨A2, hA2pos, hA2⟩ ⟨Ak, hAkpos, hAk⟩
  exact lacunaryBumpDilationVar_of_pieces p hp r hr K (lacDilTriVar p hp r hr)
    ⟨Cdev, hCdevpos, hDev⟩

end
end Work.KMTAreas.A7Hi
