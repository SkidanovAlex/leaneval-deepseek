import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_maximal_l2
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_circle_method_inputs
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_major_arc_model
import Submission.Commons.Analysis.ExponentialSums.pure_power_major_arc_multiplier
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality
import Submission.Commons.Analysis.ExponentialSums.weyl_minor_arc_decay
import Submission.Commons.Analysis.ExponentialSums.hua_bound
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_dyadic_reduction_z
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_shift_transfer
import Submission.Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family
import Submission.Commons.Analysis.Fourier.quadratic_shift_fourier_coeff_conj

/-!
# The `ℓ²` maximal inequality for the pure `d`-th power density kernels

This file proves `Commons.Analysis.ExponentialSums.pure_power_kernel_maximal_l2`, the
`d`-th power generalisation of `quadratic_kernel_maximal_l2`.

The development mirrors the quadratic chain (`pure_power_*` in place of `quadratic_*`):
the major/minor dichotomy, the model and its uniform `O(N^{-c})` approximation, the
per-`q`-block maximal estimate, the dyadic reduction and the `ℤ → ℕ` transfer.
-/

namespace Commons.Analysis.ExponentialSums

open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology

noncomputable section

/-! ## The pure-power profile and the major-arc model -/

/-- The pure `d`-th power oscillatory profile `v_d(x) = ∫_0^1 e^{2πi x s^d} ds`. -/
noncomputable def powProfile (d : ℕ) (x : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ))

/-- The complete-sum weight of a single major-arc term of the `d`-th power model. -/
noncomputable def powWeight (d : ℕ) (q : ℕ) (a : ℕ) : ℂ :=
  ((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q,
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ)))

/-- A single major-arc term of the `d`-th power model. -/
noncomputable def powModelTerm (d : ℕ) (N q : ℕ) (a : ℕ) (l : ℤ) (α : ℝ) : ℂ :=
  powWeight d q a * powProfile d (((α - (a : ℝ) / (q : ℝ) - (l : ℝ)) * (N : ℝ) ^ d))

/-- The `q`-th major-arc block of the `d`-th power model. -/
noncomputable def powMajorArcBlock (d : ℕ) (δ : ℝ) (N : ℕ) (α : ℝ) (q : ℕ) : ℂ :=
  ∑ a ∈ Finset.range q,
    if Nat.gcd a q = 1 then
      ∑ l ∈ Finset.Icc (-2 : ℤ) 2,
        if |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ (N : ℝ) ^ (-((d : ℝ) - δ))
          then powModelTerm d N q a l α else 0
    else 0

/-- The major-arc model of the `d`-th power kernel. -/
noncomputable def powMajorArcModel (d : ℕ) (δ : ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ δ)), powMajorArcBlock d δ N α q

/-- The true `d`-th power Weyl kernel `N⁻¹ ∑_{n<N} e(α n^d)`. -/
noncomputable def powKernel (d : ℕ) (N : ℕ) (α : ℝ) : ℂ :=
  ((N : ℝ)⁻¹ : ℂ) * Finset.sum (Finset.range N)
    (fun n => Complex.exp (2 * Real.pi * Complex.I * (((α * (n : ℝ) ^ d : ℝ)) : ℂ)))

lemma powProfile_apply (d : ℕ) (x : ℝ) :
    powProfile d x
      = ∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ)) := rfl

/-- `‖v_d(x)‖ ≤ 1`. -/
lemma norm_powProfile_le_one (d : ℕ) (x : ℝ) : ‖powProfile d x‖ ≤ 1 := by
  rw [powProfile]
  have hnorm : ∀ s : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ))‖ = 1 := by
    intro s
    have hcast : 2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ)
        = ((2 * Real.pi * (x * s ^ d) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (show (0 : ℝ) ≤ 1 by norm_num)
    (f := fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ)))
  refine le_trans h ?_
  simp only [hnorm]
  simp

/-- Van der Corput (pseudo-projection) decay of the profile, from
`pure_power_pseudo_projection_bound`. -/
theorem powProfile_decay (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖powProfile d x‖ ≤ C * (|x| ^ ((1 : ℝ) / (d : ℝ)))⁻¹ := by
  obtain ⟨C, hCpos, hC⟩ := pure_power_pseudo_projection_bound d hd
  refine ⟨C, hCpos, fun x hx => ?_⟩
  have h1 : ‖powProfile d x‖ ≤ C / (1 + 1 * |x| ^ ((1 : ℝ) / (d : ℝ))) := by
    have h := hC 1 x (by norm_num)
    have hEq : ‖powProfile d x‖
        = ‖∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
            ((x * (((1:ℕ):ℝ)) ^ d * s ^ d : ℝ) : ℂ))‖ := by
      congr 1
      rw [powProfile]
      apply intervalIntegral.integral_congr
      intro s hs
      congr 1
      push_cast
      rw [one_pow, mul_one]
    have h' : ‖∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
            ((x * (((1:ℕ):ℝ)) ^ d * s ^ d : ℝ) : ℂ))‖
        ≤ C / (1 + (((1:ℕ):ℝ)) * |x| ^ ((1 : ℝ) / (d : ℝ))) := h
    have hone : (1 : ℝ) + (((1:ℕ):ℝ)) * |x| ^ ((1 : ℝ) / (d : ℝ))
        = 1 + 1 * |x| ^ ((1 : ℝ) / (d : ℝ)) := by norm_num
    rw [hone] at h'
    exact hEq.le.trans h'
  have hpow1 : (1 : ℝ) ≤ |x| ^ ((1 : ℝ) / (d : ℝ)) :=
    Real.one_le_rpow hx (by positivity)
  have hden : (1 : ℝ) ≤ 1 + |x| ^ ((1 : ℝ) / (d : ℝ)) := by linarith
  refine le_trans h1 ?_
  calc C / (1 + 1 * |x| ^ ((1 : ℝ) / (d : ℝ)))
      ≤ C / |x| ^ ((1 : ℝ) / (d : ℝ)) :=
        div_le_div_of_nonneg_left hCpos.le (by linarith) (by linarith)
    _ = C * (|x| ^ ((1 : ℝ) / (d : ℝ)))⁻¹ := by rw [div_eq_mul_inv]

/-- The plateau bound `‖v_d(x) - 1‖ ≤ 2π|x|` (mean value). -/
theorem powProfile_sub_one_le (d : ℕ) (hd : 2 ≤ d) (x : ℝ) :
    ‖powProfile d x - 1‖ ≤ 2 * Real.pi * |x| := by
  have hpt : ∀ s : ℝ, 0 ≤ s →
      ‖Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ)) - 1‖
        ≤ 4 * Real.pi * |x| * s ^ d := by
    intro s hs
    have hrw : 2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ)
        = ((2 * Real.pi * x * s ^ d : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have h := Commons.Analysis.ExponentialSums.norm_exp_mul_I_sub_one_le (2 * Real.pi * x * s ^ d)
    rw [hrw]
    refine le_trans h (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      abs_of_nonneg (pow_nonneg hs d)]
    ring_nf
  have hsub : powProfile d x - 1
      = ∫ s in (0 : ℝ)..1,
          (Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ)) - 1) := by
    rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) (0:ℝ) 1)
      (Continuous.intervalIntegrable continuous_const (0:ℝ) 1),
      intervalIntegral.integral_const, powProfile]
    norm_num
  rw [hsub]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)) ?_
  have hmono : (∫ s in (0 : ℝ)..1,
        ‖Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ)) - 1‖)
      ≤ ∫ s in (0 : ℝ)..1, 4 * Real.pi * |x| * s ^ d :=
    intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (Continuous.intervalIntegrable (by fun_prop) (0:ℝ) 1)
      (Continuous.intervalIntegrable (by fun_prop) (0:ℝ) 1)
      (fun s hs => hpt s hs.1)
  refine le_trans hmono ?_
  rw [intervalIntegral.integral_const_mul]
  have hval : (∫ s in (0 : ℝ)..1, s ^ d) = ((d : ℝ) + 1)⁻¹ := by
    rw [integral_pow, one_pow, zero_pow (Nat.succ_ne_zero d), sub_zero]
    rw [one_div]
  rw [hval]
  have h3 : ((d : ℝ) + 1)⁻¹ ≤ (3 : ℝ)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hxnn : (0 : ℝ) ≤ |x| := abs_nonneg x
  have h4π : (0 : ℝ) ≤ 4 * Real.pi * |x| := by positivity
  have hfin : 4 * Real.pi * |x| * ((d : ℝ) + 1)⁻¹ ≤ 4 * Real.pi * |x| * (3 : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_left h3 h4π
  have h2π : 4 * Real.pi * |x| * (3 : ℝ)⁻¹ ≤ 2 * Real.pi * |x| := by
    have h43 : (0 : ℝ) ≤ |x| := hxnn
    nlinarith [Real.pi_pos, h43]
  linarith [hfin, h2π]


/-! ## The model collapses to a single major-arc term -/

/-- Uniqueness of the major-arc representation at the natural radius `N^{-(d-δ)}`. -/
lemma pow_majorArc_single_unique (d : ℕ) (hd : 2 ≤ d) {δ : ℝ} {N : ℕ} {α : ℝ}
    (hδ4 : δ ≤ 1 / 4) (hN : 3 ≤ N)
    {q q' : ℕ} {a a' : ℕ} {l l' : ℤ}
    (hqδ : q ≤ Nat.floor ((N : ℝ) ^ δ)) (ha : a < q) (hg : Nat.gcd a q = 1)
    (hqδ' : q' ≤ Nat.floor ((N : ℝ) ^ δ)) (ha' : a' < q') (hg' : Nat.gcd a' q' = 1)
    (h₁ : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ (N : ℝ) ^ (-((d:ℝ) - δ)))
    (h₂ : |α - (a' : ℝ) / (q' : ℝ) - (l' : ℝ)| ≤ (N : ℝ) ^ (-((d:ℝ) - δ))) :
    q = q' ∧ a = a' ∧ l = l' := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h
    · subst h0
      have : (0:ℝ) ≤ (Nat.floor ((N:ℝ)^δ) : ℝ) := by positivity
      omega
    · exact h
  have hqpos' : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with h0 | h
    · subst h0
      have : (0:ℝ) ≤ (Nat.floor ((N:ℝ)^δ) : ℝ) := by positivity
      omega
    · exact h
  have hfloor : ∀ n : ℕ, n ≤ Nat.floor ((N:ℝ)^δ) → (n:ℝ) ≤ (N:ℝ)^δ := fun n hn =>
    le_trans (by exact_mod_cast hn) (Nat.floor_le (Real.rpow_nonneg hNpos.le δ))
  have hqR : (q:ℝ) ≤ (N:ℝ)^(1/4:ℝ) := by
    have h1 : (q:ℝ) ≤ (N:ℝ)^δ := hfloor q hqδ
    have h2 : (N:ℝ)^δ ≤ (N:ℝ)^(1/4:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hδ4
    linarith
  have hqR' : (q':ℝ) ≤ (N:ℝ)^(1/4:ℝ) := by
    have h1 : (q':ℝ) ≤ (N:ℝ)^δ := hfloor q' hqδ'
    have h2 : (N:ℝ)^δ ≤ (N:ℝ)^(1/4:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hδ4
    linarith
  have hsep : 2 * (N : ℝ) ^ (-((d:ℝ) - δ)) < ((q:ℝ)*(q':ℝ))⁻¹ := by
    have hprod : (q:ℝ)*(q':ℝ) ≤ (N:ℝ)^(1/2:ℝ) := by
      calc (q:ℝ)*(q':ℝ) ≤ (N:ℝ)^(1/4:ℝ) * (N:ℝ)^(1/4:ℝ) :=
            mul_le_mul hqR hqR' (by positivity) (by positivity)
        _ = (N:ℝ)^(1/2:ℝ) := by
            rw [← Real.rpow_add hNpos]
            norm_num
    have hpos : (0:ℝ) < (q:ℝ)*(q':ℝ) := by positivity
    have h1 : (N:ℝ)^(-((1:ℝ)/2)) ≤ ((q:ℝ)*(q':ℝ))⁻¹ := by
      have h1' : ((N:ℝ)^((1:ℝ)/2))⁻¹ ≤ ((q:ℝ)*(q':ℝ))⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos hNpos _) hpos).mpr hprod
      rwa [← Real.rpow_neg hNpos.le ((1:ℝ)/2)] at h1'
    have h2 : 2 * (N:ℝ)^(-((d:ℝ)-δ)) ≤ 2 * (N:ℝ)^(-(7/4:ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      have hd' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      linarith
    have h3 : 2 * (N:ℝ)^(-((7:ℝ)/4)) < (N:ℝ)^(-((1:ℝ)/2)) := by
      have hN54 : (2:ℝ) < (N:ℝ)^((5:ℝ)/4) := by
        have h3' : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        have h5' : (3:ℝ) < (N:ℝ)^((5:ℝ)/4) :=
          calc (3:ℝ) = (3:ℝ)^(1:ℝ) := (Real.rpow_one 3).symm
            _ < (3:ℝ)^((5:ℝ)/4) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
            _ ≤ (N:ℝ)^((5:ℝ)/4) := Real.rpow_le_rpow (by norm_num) h3' (by norm_num)
        linarith
      have h4 : (N:ℝ)^(-((7:ℝ)/4)) = (N:ℝ)^(-((1:ℝ)/2)) * (N:ℝ)^(-((5:ℝ)/4)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      have h5 : (N:ℝ)^(-((5:ℝ)/4)) = ((N:ℝ)^((5:ℝ)/4))⁻¹ :=
        Real.rpow_neg hNpos.le ((5:ℝ)/4)
      have h1' : 2 * (N:ℝ)^(-((5:ℝ)/4)) < 1 := by
        rw [h5, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hNpos _)]
        exact hN54
      have h2' : (0:ℝ) < (N:ℝ)^(-((1:ℝ)/2)) := Real.rpow_pos_of_pos hNpos _
      rw [h4]
      calc 2 * ((N:ℝ)^(-((1:ℝ)/2)) * (N:ℝ)^(-((5:ℝ)/4)))
          = (N:ℝ)^(-((1:ℝ)/2)) * (2 * (N:ℝ)^(-((5:ℝ)/4))) := by ring
        _ < (N:ℝ)^(-((1:ℝ)/2)) * 1 := mul_lt_mul_of_pos_left h1' h2'
        _ = (N:ℝ)^(-((1:ℝ)/2)) := by ring
    exact lt_of_le_of_lt h2 (lt_of_lt_of_le h3 h1)
  exact majorArc_term_unique (q₁ := q) (q₂ := q') (a₁ := a) (a₂ := a') (l₁ := l) (l₂ := l')
    hqpos hqpos' ha ha' hg hg' h₁ h₂ hsep

/-- If a valid major-arc triple exists, the `d`-th power model collapses to that single term. -/
lemma powMajorArcModel_eq_single (d : ℕ) (hd : 2 ≤ d) {δ : ℝ} {N : ℕ} {α : ℝ} (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (hN : 3 ≤ N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h : ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ δ) ∧ x.2.1 < x.1 ∧
        Nat.gcd x.2.1 x.1 = 1 ∧ x.2.2 ∈ Finset.Icc (-2 : ℤ) 2 ∧
        |α - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)| ≤ (N : ℝ) ^ (-((d:ℝ) - δ))) :
    powMajorArcModel d δ N α = powModelTerm d N h.choose.1 h.choose.2.1 h.choose.2.2 α := by
  obtain ⟨hq1, hqfl, ha, hgcd, hl, hdist⟩ := h.choose_spec
  have hblk : powMajorArcBlock d δ N α h.choose.1
      = powModelTerm d N h.choose.1 h.choose.2.1 h.choose.2.2 α := by
    rw [powMajorArcBlock]
    rw [Finset.sum_eq_single (s := Finset.range h.choose.1) (f := fun a =>
      (if Nat.gcd a h.choose.1 = 1 then
        ∑ l ∈ Finset.Icc (-2:ℤ) 2,
          if |α - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
            then powModelTerm d N h.choose.1 a l α else 0
        else 0 : ℂ)) h.choose.2.1
      (fun a hamem hane => by
        by_cases hg : Nat.gcd a h.choose.1 = 1
        · rw [if_pos hg]
          refine Finset.sum_eq_zero (s := Finset.Icc (-2:ℤ) 2) (f := fun l =>
            (if |α - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
                then powModelTerm d N h.choose.1 a l α else 0 : ℂ)) (fun l hlmem => ?_)
          by_cases hc : |α - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
          · rw [if_pos hc]
            exact absurd (pow_majorArc_single_unique d hd (δ := δ) (N := N) (α := α) hδ4 hN
              (q := h.choose.1) (q' := h.choose.1) (a := a) (a' := h.choose.2.1)
              (l := l) (l' := h.choose.2.2)
              hqfl (Finset.mem_range.mp hamem) hg hqfl ha hgcd hc hdist).2.1 hane
          · rw [if_neg hc]
        · rw [if_neg hg])
      (fun hnot => absurd (Finset.mem_range.mpr ha) hnot)]
    rw [if_pos hgcd]
    rw [Finset.sum_eq_single (s := Finset.Icc (-2:ℤ) 2) (f := fun l =>
      (if |α - (h.choose.2.1:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
          then powModelTerm d N h.choose.1 h.choose.2.1 l α else 0 : ℂ)) h.choose.2.2
      (fun l hlmem hlne => by
        by_cases hc : |α - (h.choose.2.1:ℝ)/(h.choose.1:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
        · rw [if_pos hc]
          exact absurd (pow_majorArc_single_unique d hd (δ := δ) (N := N) (α := α) hδ4 hN
            (q := h.choose.1) (q' := h.choose.1) (a := h.choose.2.1) (a' := h.choose.2.1)
            (l := l) (l' := h.choose.2.2)
            hqfl ha hgcd hqfl ha hgcd hc hdist).2.2 hlne
        · rw [if_neg hc])
      (fun hnot => absurd hl hnot)]
    rw [if_pos hdist]
  rw [powMajorArcModel]
  rw [Finset.sum_eq_single (s := Finset.Icc 1 (Nat.floor ((N : ℝ) ^ δ)))
    (f := powMajorArcBlock d δ N α) h.choose.1
    (fun q hqmem hqne => by
      rw [powMajorArcBlock]
      refine Finset.sum_eq_zero (s := Finset.range q) (f := fun a =>
        (if Nat.gcd a q = 1 then
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            if |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
              then powModelTerm d N q a l α else 0
          else 0 : ℂ)) (fun a hamem => ?_)
      by_cases hg : Nat.gcd a q = 1
      · rw [if_pos hg]
        refine Finset.sum_eq_zero (s := Finset.Icc (-2:ℤ) 2) (f := fun l =>
          (if |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
              then powModelTerm d N q a l α else 0 : ℂ)) (fun l hlmem => ?_)
        by_cases hc : |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
        · rw [if_pos hc]
          exact absurd (pow_majorArc_single_unique d hd (δ := δ) (N := N) (α := α) hδ4 hN
            (q := q) (q' := h.choose.1) (a := a) (a' := h.choose.2.1) (l := l) (l' := h.choose.2.2)
            (Finset.mem_Icc.mp hqmem).2 (Finset.mem_range.mp hamem) hg
            hqfl ha hgcd hc hdist).1 hqne
        · rw [if_neg hc]
      · rw [if_neg hg])
    (fun hnot => absurd (Finset.mem_Icc.mpr ⟨hq1, hqfl⟩) hnot)]
  exact hblk

/-- If no valid major-arc triple exists, the `d`-th power model vanishes. -/
lemma powMajorArcModel_eq_zero (d : ℕ) {δ : ℝ} {N : ℕ} {α : ℝ}
    (h : ¬ ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ δ) ∧ x.2.1 < x.1 ∧
        Nat.gcd x.2.1 x.1 = 1 ∧ x.2.2 ∈ Finset.Icc (-2 : ℤ) 2 ∧
        |α - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)| ≤ (N : ℝ) ^ (-((d:ℝ) - δ))) :
    powMajorArcModel d δ N α = 0 := by
  rw [powMajorArcModel]
  refine Finset.sum_eq_zero (s := Finset.Icc 1 (Nat.floor ((N : ℝ) ^ δ)))
    (f := powMajorArcBlock d δ N α) (fun q hqmem => ?_)
  rw [powMajorArcBlock]
  refine Finset.sum_eq_zero (s := Finset.range q) (f := fun a =>
    (if Nat.gcd a q = 1 then
      ∑ l ∈ Finset.Icc (-2:ℤ) 2,
        if |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
          then powModelTerm d N q a l α else 0
      else 0 : ℂ)) (fun a hamem => ?_)
  by_cases hg : Nat.gcd a q = 1
  · rw [if_pos hg]
    refine Finset.sum_eq_zero (s := Finset.Icc (-2:ℤ) 2) (f := fun l =>
      (if |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
          then powModelTerm d N q a l α else 0 : ℂ)) (fun l hlmem => ?_)
    by_cases hc : |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ (N:ℝ)^(-((d:ℝ)-δ))
    · rw [if_pos hc]
      exact absurd ⟨(q, a, l), (Finset.mem_Icc.mp hqmem).1, (Finset.mem_Icc.mp hqmem).2,
        Finset.mem_range.mp hamem, hg, hlmem, hc⟩ h
    · rw [if_neg hc]
  · rw [if_neg hg]

/-- The complete-sum weight is bounded by one. -/
lemma norm_powWeight_le_one (d q : ℕ) (a : ℕ) : ‖powWeight d q a‖ ≤ 1 := by
  rw [powWeight, norm_mul]
  have h1 : ‖((q : ℂ))⁻¹‖ = (q : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
  have h2 : ‖∑ r ∈ Finset.range q,
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ)))‖ ≤ (q : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ r ∈ Finset.range q,
        ‖Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ)))‖ ≤ 1 := by
      intro r _
      rw [show 2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ))
            = (((2 * Real.pi * (a : ℝ) * (r : ℝ) ^ d / (q : ℝ)) : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
    calc ∑ r ∈ Finset.range q,
          ‖Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ)))‖
        ≤ ∑ _r ∈ Finset.range q, (1 : ℝ) := Finset.sum_le_sum this
      _ = (q : ℝ) := by simp
  rw [h1]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  · calc (q : ℝ)⁻¹ * ‖∑ r ∈ Finset.range q,
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ)))‖
        ≤ (q : ℝ)⁻¹ * (q : ℝ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 := by rw [inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt hq) : (q : ℝ) ≠ 0)]

/-- Every model term is bounded by one. -/
lemma norm_powModelTerm_le_one (d N q : ℕ) (a : ℕ) (l : ℤ) (α : ℝ) :
    ‖powModelTerm d N q a l α‖ ≤ 1 := by
  rw [powModelTerm, norm_mul]
  exact mul_le_one₀ (norm_powWeight_le_one d q a) (norm_nonneg _) (norm_powProfile_le_one d _)

/-! ## The complete-sum weight cap (Hua) -/

/-- The exponent `σ_d = 2^{-(d+1)}` of the dyadic `q`-block decay. -/
noncomputable def powSig (d : ℕ) : ℝ := ((2 : ℝ) ^ (d + 1))⁻¹

lemma powSig_pos (d : ℕ) : 0 < powSig d := by
  rw [powSig]; positivity

/-- **Cap for the complete-sum weights.**  For a reduced `a/q` with `2^m ≤ q`,
`‖q⁻¹ ∑_{r<q} e(a r^d/q)‖ ≤ A · 2^{-m σ_d}` with `A = A(d)`. -/
theorem powWeight_cap (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q m : ℕ) (a : ℤ), 1 ≤ q → 2 ^ m ≤ q → Int.gcd a (q : ℤ) = 1 →
      ‖((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q,
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ)))‖
        ≤ A * (2 : ℝ) ^ (-(m : ℝ) * powSig d) := by
  obtain ⟨C, hCpos, hC⟩ := hua_bound d (by omega) (ε := powSig d) (powSig_pos d)
  refine ⟨max C 1 + 1, by positivity, fun q m a hq hq2m hgcd => ?_⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have h2m : (2 : ℝ) ^ m ≤ (q : ℝ) := by exact_mod_cast hq2m
  have hsig : powSig d = (4 * (2 : ℝ) ^ (d - 1))⁻¹ := by
    rw [powSig, show d + 1 = (d - 1) + 2 by omega, pow_add]
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    ring_nf
  have hsum_eq : (∑ r ∈ Finset.range q,
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ))))
      = ∑ r ∈ Finset.range q, Complex.exp (↑(2 * Real.pi * a * (r : ℝ) ^ d / q) * Complex.I) := by
    refine Finset.sum_congr rfl (fun r hr => ?_)
    congr 1
    push_cast
    ring
  have hbase := hC q a (by omega) hgcd
  rw [← hsum_eq] at hbase
  have hPpos : (0 : ℝ) < (2 : ℝ) ^ (d - 1) := by positivity
  have hPpos4 : (0 : ℝ) < 4 * (2 : ℝ) ^ (d - 1) := by positivity
  have h3 : ((4 * (2 : ℝ) ^ (d - 1))⁻¹) ≤ (((2 : ℝ) ^ (d - 1))⁻¹) :=
    inv_anti₀ hPpos (by linarith)
  have he0 : -(1 / (2 : ℝ) ^ (d - 1)) + powSig d ≤ 0 := by
    have h1 : (1 / (2 : ℝ) ^ (d - 1)) = ((2 : ℝ) ^ (d - 1))⁻¹ := one_div _
    rw [h1, hsig]
    linarith [(inv_pos.mpr hPpos4).le]
  have hesig : -(1 / (2 : ℝ) ^ (d - 1)) + powSig d ≤ -powSig d := by
    have h1 : (1 / (2 : ℝ) ^ (d - 1)) = ((2 : ℝ) ^ (d - 1))⁻¹ := one_div _
    rw [h1, hsig]
    have hid : 2 * (4 * (2 : ℝ) ^ (d - 1))⁻¹ = (2 * (2 : ℝ) ^ (d - 1))⁻¹ := by
      field_simp
      norm_num
    have h4 : (2 * (2 : ℝ) ^ (d - 1))⁻¹ ≤ ((2 : ℝ) ^ (d - 1))⁻¹ :=
      inv_anti₀ hPpos (by linarith)
    linarith [hid, h4, (inv_pos.mpr hPpos4).le]
  have hE : (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + powSig d)
      ≤ (2 : ℝ) ^ (-(m : ℝ) * powSig d) := by
    have hstep1 : (q : ℝ) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + powSig d)
        ≤ ((2 : ℝ) ^ m) ^ (-(1 / (2 : ℝ) ^ (d - 1)) + powSig d) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2m he0
    rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hstep1
    refine le_trans hstep1 (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmm : (m : ℝ) * (-(1 / (2 : ℝ) ^ (d - 1)) + powSig d) ≤ (m : ℝ) * (-powSig d) :=
      mul_le_mul_of_nonneg_left hesig hm
    calc (m : ℝ) * (-(1 / (2 : ℝ) ^ (d - 1)) + powSig d) ≤ (m : ℝ) * (-powSig d) := hmm
      _ = -(m : ℝ) * powSig d := by ring
  have hC1 : C ≤ max C 1 + 1 := by linarith [le_max_left C 1]
  calc ‖((q : ℂ))⁻¹ * ∑ r ∈ Finset.range q,
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (r : ℂ) ^ d / (q : ℂ)))‖
      ≤ C * (2 : ℝ) ^ (-(m : ℝ) * powSig d) :=
        le_trans hbase (mul_le_mul_of_nonneg_left hE hCpos.le)
    _ ≤ (max C 1 + 1) * (2 : ℝ) ^ (-(m : ℝ) * powSig d) :=
        mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg (by norm_num) _)

/-! ## Numerical summability with the block exponent `σ` -/

/-- `∑_m 2^{-m σ} (m+2)^4` converges for `σ > 0`. -/
lemma summable_rpow_sig_mul_quartic {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ) * σ) * ((m : ℝ) + 2) ^ 4) := by
  have hr : ‖(2 : ℝ) ^ (-σ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpoly : ∀ m : ℕ, ((m : ℝ) + 2) ^ 4 ≤ 81 * ((m : ℝ) ^ 4 + 1) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    · have h1 : ((m : ℝ) + 2) ≤ 3 * (m : ℝ) := by
        have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      have h2 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
      calc ((m : ℝ) + 2) ^ 4 ≤ (3 * (m : ℝ)) ^ 4 := pow_le_pow_left₀ h2 h1 4
        _ = 81 * (m : ℝ) ^ 4 := by ring
        _ ≤ 81 * ((m : ℝ) ^ 4 + 1) := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ (m : ℝ) by positivity) 4]
  have hgen : Summable (fun m : ℕ => ((m : ℝ) + 2) ^ 4 * ((2 : ℝ) ^ (-σ)) ^ m) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) ^ 4 * ((2 : ℝ) ^ (-σ)) ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 4 hr
    have h2 : Summable (fun m : ℕ => ((2 : ℝ) ^ (-σ)) ^ m) :=
      summable_geometric_of_norm_lt_one hr
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((h1.mul_left 81).add (h2.mul_left 81))
    have h4 := mul_le_mul_of_nonneg_right (hpoly m)
      (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ (-σ)) ^ m)
    calc (((m : ℝ) + 2) ^ 4) * ((2 : ℝ) ^ (-σ)) ^ m
        ≤ (81 * ((m : ℝ) ^ 4 + 1)) * ((2 : ℝ) ^ (-σ)) ^ m := h4
      _ = 81 * (((m : ℝ) ^ 4) * ((2 : ℝ) ^ (-σ)) ^ m)
            + 81 * (((2 : ℝ) ^ (-σ)) ^ m) := by ring
  refine hgen.congr (fun m => ?_)
  rw [mul_comm, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Weighted Cauchy--Schwarz for the block sum, with an arbitrary splitting exponent. -/
lemma block_cauchy_sig {τ : ℝ} (hτ : 0 < τ) (d : ℕ → ℝ≥0∞) :
    (∑' m : ℕ, d m) ^ (2 : ℝ)
      ≤ (∑' m : ℕ, ((2 : ℝ≥0∞) ^ (-(m : ℝ) * τ)) ^ (2 : ℝ)) *
        (∑' m : ℕ, (((2 : ℝ≥0∞) ^ ((m : ℝ) * τ)) * d m) ^ (2 : ℝ)) := by
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count (p := 2) (q := 2)
    (f := fun m : ℕ => (2 : ℝ≥0∞) ^ (-(m : ℝ) * τ))
    (g := fun m : ℕ => (2 : ℝ≥0∞) ^ ((m : ℝ) * τ) * d m)
    (by rw [Real.holderConjugate_iff]; norm_num)
    (Measurable.aemeasurable (measurable_of_countable _))
    (Measurable.aemeasurable (measurable_of_countable _))
  rw [lintegral_count, lintegral_count, lintegral_count] at hhold
  simp only [Pi.mul_apply] at hhold
  have h2 : (∑' m : ℕ, (2 : ℝ≥0∞) ^ (-(m : ℝ) * τ) * ((2 : ℝ≥0∞) ^ ((m : ℝ) * τ) * d m))
      = ∑' m : ℕ, d m := by
    apply tsum_congr; intro m
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), show -(m : ℝ) * τ + (m : ℝ) * τ = 0 by ring,
      ENNReal.rpow_zero, one_mul]
  rw [h2] at hhold
  calc (∑' m : ℕ, d m) ^ (2 : ℝ)
      ≤ (((∑' m : ℕ, ((2 : ℝ≥0∞) ^ (-(m : ℝ) * τ)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) *
          ((∑' m : ℕ, (((2 : ℝ≥0∞) ^ ((m : ℝ) * τ)) * d m) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)))) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hhold (by norm_num)
    _ = (∑' m : ℕ, ((2 : ℝ≥0∞) ^ (-(m : ℝ) * τ)) ^ (2 : ℝ)) *
        (∑' m : ℕ, (((2 : ℝ≥0∞) ^ ((m : ℝ) * τ)) * d m) ^ (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

lemma tsum_block_weight_sig_lt_top {τ : ℝ} (hτ : 0 < τ) :
    (∑' m : ℕ, ((2 : ℝ≥0∞) ^ (-(m : ℝ) * τ)) ^ (2 : ℝ)) < ∞ := by
  have hW : (∑' m : ℕ, ((2 : ℝ≥0∞) ^ (-(m : ℝ) * τ)) ^ (2 : ℝ))
      = ∑' m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(m : ℝ) * (2 * τ))) := by
    apply tsum_congr; intro m
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
    rw [h2, ← ENNReal.rpow_mul,
      ENNReal.ofReal_rpow_of_pos (x := 2) (show (0 : ℝ) < 2 by norm_num)]
    congr 1
    ring
  have hsum : Summable (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ) * (2 * τ))) := by
    have heq : (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ) * (2 * τ)))
        = fun m : ℕ => ((2 : ℝ) ^ (-(2 * τ))) ^ m := by
      funext m
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; push_cast; ring
    rw [heq]
    exact summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  rw [hW, ← ENNReal.ofReal_tsum_of_nonneg (fun m => Real.rpow_nonneg (by norm_num) _) hsum]
  exact ENNReal.ofReal_lt_top

lemma two_rpow_sig_sq_C (σ τ C : ℝ) (m : ℕ) :
    (2 : ℝ) ^ ((m : ℝ) * (2 * τ)) * (C * (2 : ℝ) ^ (-(m : ℝ) * σ) * ((m : ℝ) + 2) ^ 2) ^ 2
      = C ^ 2 * ((2 : ℝ) ^ (-(m : ℝ) * (2 * σ - 2 * τ)) * ((m : ℝ) + 2) ^ 4) := by
  have hX : ((2 : ℝ) ^ (-(m : ℝ) * σ)) ^ 2 = (2 : ℝ) ^ (-(m : ℝ) * (2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; push_cast; ring
  have h2 : (2 : ℝ) ^ ((m : ℝ) * (2 * τ)) * (2 : ℝ) ^ (-(m : ℝ) * (2 * σ))
      = (2 : ℝ) ^ (-(m : ℝ) * (2 * σ - 2 * τ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  rw [mul_pow, mul_pow, hX]
  rw [show (((m : ℝ) + 2) ^ 2) ^ 2 = ((m : ℝ) + 2) ^ 4 by ring]
  calc (2 : ℝ) ^ ((m : ℝ) * (2 * τ)) *
        (C ^ 2 * (2 : ℝ) ^ (-(m : ℝ) * (2 * σ)) * ((m : ℝ) + 2) ^ 4)
      = C ^ 2 * ((2 : ℝ) ^ ((m : ℝ) * (2 * τ)) * (2 : ℝ) ^ (-(m : ℝ) * (2 * σ)))
          * ((m : ℝ) + 2) ^ 4 := by ring
    _ = C ^ 2 * ((2 : ℝ) ^ (-(m : ℝ) * (2 * σ - 2 * τ)) * ((m : ℝ) + 2) ^ 4) := by
        rw [h2]; ring

lemma tsum_scaled_K_sig_lt_top {σ τ C : ℝ} (hC : 0 ≤ C) (hτσ : τ < σ) (hτ : 0 < τ) :
    (∑' m : ℕ, ((2 : ℝ≥0∞) ^ ((m : ℝ) * τ)) ^ (2 : ℝ) *
      ENNReal.ofReal (C * (2 : ℝ) ^ (-(m : ℝ) * σ) * ((m : ℝ) + 2) ^ 2) ^ 2) < ∞ := by
  have h1 : ∀ m : ℕ, ((2 : ℝ≥0∞) ^ ((m : ℝ) * τ)) ^ (2 : ℝ)
      = ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * (2 * τ))) := by
    intro m
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
    rw [h2, ← ENNReal.rpow_mul,
      ENNReal.ofReal_rpow_of_pos (x := 2) (show (0 : ℝ) < 2 by norm_num)]
    congr 1
    ring
  simp only [h1]
  rw [show (fun m : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) * (2 * τ))) *
      ENNReal.ofReal (C * (2 : ℝ) ^ (-(m : ℝ) * σ) * ((m : ℝ) + 2) ^ 2) ^ 2)
      = fun m : ℕ => ENNReal.ofReal (C ^ 2 * ((2 : ℝ) ^ (-(m : ℝ) * (2 * σ - 2 * τ))
          * ((m : ℝ) + 2) ^ 4)) from by
    funext m
    rw [← ENNReal.ofReal_pow (by
        have h : (0 : ℝ) ≤ (2 : ℝ) ^ (-(m : ℝ) * σ) := Real.rpow_nonneg (by norm_num) _
        positivity) 2,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    congr 1
    exact two_rpow_sig_sq_C σ τ C m]
  have hsum : Summable (fun m : ℕ => C ^ 2 * ((2 : ℝ) ^ (-(m : ℝ) * (2 * σ - 2 * τ))
      * ((m : ℝ) + 2) ^ 4)) :=
    (summable_rpow_sig_mul_quartic (by linarith : 0 < 2 * σ - 2 * τ)).mul_left (C ^ 2)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (-(m : ℝ) * (2 * σ - 2 * τ)) := Real.rpow_nonneg (by norm_num) _
    positivity) hsum]
  exact ENNReal.ofReal_lt_top



/-! ## The dyadic `q`-block decomposition of the `d`-th power model -/

/-- The `q`-layer of the `m`-th dyadic block of the `d`-th power model. -/
noncomputable def powMajorArcModelBlock (d : ℕ) (m N : ℕ) (α : ℝ) (q : ℕ) : ℂ :=
  if 2 ^ m ≤ q ∧ q < 2 ^ (m + 1) then powMajorArcBlock d ((1 : ℝ) / 4) N α q else 0

lemma pow_sum_block_eq_block (d : ℕ) (N : ℕ) (α : ℝ) (q : ℕ) (hq1 : 1 ≤ q)
    (hq2 : q ≤ Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4))) :
    (∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1),
        powMajorArcModelBlock d m N α q)
      = powMajorArcBlock d ((1 : ℝ) / 4) N α q := by
  have hmem : Nat.log 2 q ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (log2_le_floor_pow_quarter hq1 hq2))
  have hlog : 2 ^ (Nat.log 2 q) ≤ q ∧ q < 2 ^ (Nat.log 2 q + 1) :=
    ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) q⟩
  have hblk : powMajorArcModelBlock d (Nat.log 2 q) N α q
      = powMajorArcBlock d ((1 : ℝ) / 4) N α q := by
    rw [powMajorArcModelBlock, if_pos hlog]
  rw [← hblk]
  refine Finset.sum_eq_single (f := fun m => powMajorArcModelBlock d m N α q) (Nat.log 2 q) ?_ ?_
  · intro m hm hmne
    show powMajorArcModelBlock d m N α q = 0
    rw [powMajorArcModelBlock, if_neg]
    rintro ⟨h1, h2⟩
    exact hmne (Nat.log_eq_of_pow_le_of_lt_pow h1 h2).symm
  · intro hnot; exact absurd hmem hnot

/-- Exact dyadic-block decomposition of the `d`-th power model. -/
theorem powMajorArcModel_eq_sum_block (d : ℕ) (N : ℕ) (α : ℝ) :
    powMajorArcModel d ((1 : ℝ) / 4) N α
      = ∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) + 1),
          ∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4))),
            powMajorArcModelBlock d m N α q := by
  rw [powMajorArcModel]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
  exact (pow_sum_block_eq_block d N α q hq1 hq2).symm

/-- The model is bounded by one (at most one major-arc term is active). -/
theorem norm_powMajorArcModel_le_one (d : ℕ) (hd : 2 ≤ d) {N : ℕ} (hN : 3 ≤ N) {α : ℝ}
    (h0 : 0 ≤ α) (h1 : α ≤ 1) : ‖powMajorArcModel d ((1 : ℝ) / 4) N α‖ ≤ 1 := by
  by_cases h : ∃ x : ℕ × ℕ × ℤ,
      1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4)) ∧ x.2.1 < x.1 ∧
      Nat.gcd x.2.1 x.1 = 1 ∧ x.2.2 ∈ Finset.Icc (-2 : ℤ) 2 ∧
      |α - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)| ≤ (N : ℝ) ^ (-((d:ℝ) - 1/4))
  · rw [powMajorArcModel_eq_single d hd (by norm_num) (by norm_num) hN h0 h1 h]
    exact norm_powModelTerm_le_one d N h.choose.1 h.choose.2.1 h.choose.2.2 α
  · rw [powMajorArcModel_eq_zero d h]
    simp

/-! ## The `q`-block (`Nat.log 2`-graded) decomposition -/

noncomputable def powModelQBlock (d : ℕ) (m N : ℕ) (θ : ℝ) : ℂ :=
  ∑ q ∈ (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)))).filter (fun q => Nat.log 2 q = m),
    powMajorArcBlock d ((1:ℝ)/4) N θ q

lemma pow_sum_modelQBlock_eq (d : ℕ) (m N : ℕ) (θ : ℝ) :
    (∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
        if 2 ^ m ≤ q ∧ q < 2 ^ (m + 1) then powMajorArcBlock d ((1:ℝ)/4) N θ q else 0)
      = powModelQBlock d m N θ := by
  rw [powModelQBlock, filter_log_eq_filter_pow, Finset.sum_filter]

lemma powMajorArcModel_eq_sum_modelQBlock (d : ℕ) (N : ℕ) (θ : ℝ) :
    powMajorArcModel d ((1:ℝ)/4) N θ
      = ∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) + 1), powModelQBlock d m N θ := by
  rw [powMajorArcModel_eq_sum_block]
  apply Finset.sum_congr rfl
  intro m hm
  rw [show (∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
      powMajorArcModelBlock d m N θ q)
      = (∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
          if 2 ^ m ≤ q ∧ q < 2 ^ (m + 1) then powMajorArcBlock d ((1:ℝ)/4) N θ q else 0) from by
    apply Finset.sum_congr rfl
    intro q hq
    rw [powMajorArcModelBlock]]
  exact pow_sum_modelQBlock_eq d m N θ

lemma pow_conj_model_eq_sum_block (d : ℕ) (k : ℕ) (θ : ℝ) :
    (starRingEnd ℂ (powMajorArcModel d ((1:ℝ)/4) (2^k) θ))
      = ∑ m ∈ Finset.range (Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1),
          (starRingEnd ℂ (powModelQBlock d m (2^k) θ)) := by
  rw [powMajorArcModel_eq_sum_modelQBlock]
  simp only [map_sum]

/-! ## Measurability and crude bounds -/

lemma continuous_powProfile (d : ℕ) : Continuous (powProfile d) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : ℝ) (s : ℝ) =>
      Complex.exp (2 * Real.pi * Complex.I * ((x * s ^ d : ℝ) : ℂ))) (by fun_prop) 0 1

lemma measurable_powModelTerm (d N q : ℕ) (a : ℕ) (l : ℤ) :
    Measurable (fun α : ℝ => powModelTerm d N q a l α) := by
  unfold powModelTerm
  have hc : Continuous (fun α : ℝ => (α - (a : ℝ) / (q : ℝ) - (l : ℝ)) * (N : ℝ) ^ d) := by
    fun_prop
  exact measurable_const.mul ((continuous_powProfile d).comp hc).measurable

lemma measurable_powMajorArcBlock (d : ℕ) (δ : ℝ) (N q : ℕ) :
    Measurable (fun α : ℝ => powMajorArcBlock d δ N α q) := by
  unfold powMajorArcBlock
  refine Finset.measurable_sum _ (fun a _ => ?_)
  refine Measurable.ite (by measurability) ?_ measurable_const
  refine Finset.measurable_sum _ (fun l _ => ?_)
  exact Measurable.ite (by measurability) (measurable_powModelTerm d N q a l) measurable_const

lemma measurable_powModelQBlock (d : ℕ) (m N : ℕ) :
    Measurable (fun θ : ℝ => powModelQBlock d m N θ) := by
  unfold powModelQBlock
  exact Finset.measurable_sum _ (fun q _ => measurable_powMajorArcBlock d ((1:ℝ)/4) N q)

lemma norm_powMajorArcBlock_le (d : ℕ) (δ : ℝ) (N q : ℕ) (α : ℝ) :
    ‖powMajorArcBlock d δ N α q‖ ≤ 5 * (q : ℝ) := by
  rw [powMajorArcBlock]
  have h1 : ‖∑ a ∈ Finset.range q,
      (if Nat.gcd a q = 1 then
        ∑ l ∈ Finset.Icc (-2 : ℤ) 2,
          (if |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ (N : ℝ) ^ (-((d : ℝ) - δ))
            then powModelTerm d N q a l α else 0)
        else 0 : ℂ)‖ ≤ ∑ _a ∈ Finset.range q, (5 : ℝ) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a _ => ?_))
    by_cases hg : Nat.gcd a q = 1
    · rw [if_pos hg]
      have h2 : ‖∑ l ∈ Finset.Icc (-2 : ℤ) 2,
          (if |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ (N : ℝ) ^ (-((d : ℝ) - δ))
            then powModelTerm d N q a l α else 0 : ℂ)‖
          ≤ ∑ _l ∈ Finset.Icc (-2 : ℤ) 2, (1 : ℝ) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l _ => ?_))
        by_cases hl : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ (N : ℝ) ^ (-((d : ℝ) - δ))
        · rw [if_pos hl]; exact norm_powModelTerm_le_one d N q a l α
        · rw [if_neg hl]; simp
      refine le_trans h2 (le_of_eq ?_)
      simp
    · rw [if_neg hg]
      simp
  refine le_trans h1 (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma norm_powModelQBlock_le (d : ℕ) (m N : ℕ) (θ : ℝ) :
    ‖powModelQBlock d m N θ‖
      ≤ 5 * ((Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) : ℝ))^2 := by
  set Q := Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) with hQ
  have hQnn : (0:ℝ) ≤ (Q : ℝ) := by positivity
  calc ‖∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = m),
        powMajorArcBlock d ((1:ℝ)/4) N θ q‖
      ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = m),
          ‖powMajorArcBlock d ((1:ℝ)/4) N θ q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = m), 5 * (q : ℝ) :=
        Finset.sum_le_sum (fun q _ => norm_powMajorArcBlock_le d ((1:ℝ)/4) N q θ)
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, 5 * (q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun q _ _ => by positivity)
    _ = 5 * ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 5 * (Q : ℝ)^2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) :=
              Finset.sum_le_sum (fun q hq => by
                exact_mod_cast (Finset.mem_Icc.mp hq).2)
          _ = (Q : ℝ) * Q := by
              rw [Finset.sum_const, nsmul_eq_mul]
              simp
          _ = (Q : ℝ)^2 := by ring

/-! ## The maximal operators and the block split -/

noncomputable def powTkMax (d : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, (starRingEnd ℂ (powMajorArcModel d ((1:ℝ)/4) (2^k) θ)) *
    (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
    Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))

noncomputable def powTkBlockMax (d : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (m k : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, (starRingEnd ℂ (powModelQBlock d m (2^k) θ)) *
    (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
    Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))

lemma pow_intervalIntegrable_block (d : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (m k : ℕ) (x : ℤ) :
    IntervalIntegrable (fun θ : ℝ => (starRingEnd ℂ (powModelQBlock d m (2^k) θ)) *
      (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
      Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))) volume 0 1 := by
  rw [intervalIntegrable_iff]
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
        Real.volume_Ioc]; norm_num⟩
  refine MeasureTheory.Integrable.of_bound ?_
    (5 * ((Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) : ℝ))^2 * (∑ j ∈ s, ‖g j‖)) ?_
  · exact (((Complex.continuous_conj.measurable.comp
      (measurable_powModelQBlock d m (2^k))).mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with θ
    rw [norm_mul, norm_mul, norm_exp_pure_imag x θ]
    have hP := norm_modelP_le g s θ
    have hb := norm_powModelQBlock_le d m (2^k) θ
    calc ‖(starRingEnd ℂ (powModelQBlock d m (2^k) θ))‖ *
            ‖∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖ * 1
        = ‖powModelQBlock d m (2^k) θ‖ *
            ‖∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖ := by
          rw [Complex.norm_conj, mul_one]
      _ ≤ (5 * ((Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) : ℝ))^2) * (∑ j ∈ s, ‖g j‖) := by
          apply mul_le_mul hb hP (by positivity) (by positivity)

lemma pow_TkMax_eq_sum_block (d : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (x : ℤ) :
    powTkMax d g s k x
      = ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
          powTkBlockMax d g s m k x := by
  rw [powTkMax]
  simp only [powTkBlockMax]
  rw [show (∫ θ in (0:ℝ)..1, (starRingEnd ℂ (powMajorArcModel d ((1:ℝ)/4) (2^k) θ)) *
        (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
        Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))))
      = ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
          ∫ θ in (0:ℝ)..1, (starRingEnd ℂ (powModelQBlock d m (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
            Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))) from ?_]
  · rw [show (∫ θ in (0:ℝ)..1, (starRingEnd ℂ (powMajorArcModel d ((1:ℝ)/4) (2^k) θ)) *
        (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
        Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))))
        = ∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.range
              (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (powModelQBlock d m (2^k) θ))) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))) from by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only
      rw [pow_conj_model_eq_sum_block]]
    rw [show (∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.range
              (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (powModelQBlock d m (2^k) θ))) *
          (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
          Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ))))
        = ∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.range
              (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (powModelQBlock d m (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))) *
            Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))) from by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only
      rw [Finset.sum_mul, Finset.sum_mul]]
    rw [intervalIntegral.integral_finsetSum]
    intro m hm
    exact pow_intervalIntegrable_block d g s m k x

lemma pow_Tsup_le_tsum (d : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    (⨆ k : ℕ, ‖powTkMax d g s k x‖ₑ)
      ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ := by
  refine iSup_le (fun k => ?_)
  calc ‖powTkMax d g s k x‖ₑ
      = ‖∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            powTkBlockMax d g s m k x‖ₑ := by rw [pow_TkMax_eq_sum_block]
    _ ≤ ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            ‖powTkBlockMax d g s m k x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ := by
        calc ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
              ‖powTkBlockMax d g s m k x‖ₑ
            ≤ ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
              ⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ :=
              Finset.sum_le_sum (fun m _ => le_iSup (fun k => ‖powTkBlockMax d g s m k x‖ₑ) k)
          _ ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ := ENNReal.sum_le_tsum _

/-- The block maximal bound implies the model maximal bound, with block exponent `τ`. -/
lemma pow_lintegral_Tsup_sq_le (d : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) {τ : ℝ} (hτ : 0 < τ)
    (K : ℕ → ℝ≥0∞) (G : ℝ≥0∞)
    (hblk : ∀ m : ℕ,
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
        ≤ K m * G) :
    ∫⁻ x : ℤ, (⨆ k : ℕ, ‖powTkMax d g s k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
        (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G := by
  have h1 : ∫⁻ x : ℤ, (⨆ k : ℕ, ‖powTkMax d g s k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (∑' m : ℕ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))^(2:ℝ)
          ∂MeasureTheory.Measure.count := by
    apply lintegral_mono; intro x
    exact ENNReal.rpow_le_rpow (pow_Tsup_le_tsum d g s x) (by norm_num)
  have hinner : ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
        (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count
      ≤ (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G := by
    calc ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
          (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count
        = ∑' m : ℕ, ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
            (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))^(2:ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_tsum (fun m => AEMeasurable.pow_const
            (Measurable.aemeasurable (measurable_of_countable _)) 2)
      _ ≤ ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m) * G :=
          ENNReal.tsum_le_tsum (fun m => ?_)
      _ = (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G := by
          rw [ENNReal.tsum_mul_right]
    calc ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
          (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))^(2:ℝ) ∂MeasureTheory.Measure.count
        = ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
            (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_congr (fun x => by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)])
      _ = ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
            ∫⁻ x : ℤ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ)^(2:ℝ)
              ∂MeasureTheory.Measure.count :=
          lintegral_const_mul _ (Measurable.pow_const (measurable_of_countable _) 2)
      _ ≤ ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * (K m * G) := by
          gcongr
          exact hblk m
      _ = (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m) * G := by rw [mul_assoc]
  refine le_trans h1 ?_
  calc ∫⁻ x : ℤ, (∑' m : ℕ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))^(2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
          (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
            (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => block_cauchy_sig hτ
          (fun m => ⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))
    _ = (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
          ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
            (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_const_mul _ (measurable_of_countable _)
    _ ≤ (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
          ((∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G) := by
        gcongr
    _ = (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
          (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G := by rw [mul_assoc]

/-- **Assembly of the model maximal estimate from the per-`q`-block maximal estimate.** -/
theorem pow_model_maximal_of_block (d : ℕ) (hd : 2 ≤ d)
    (hm : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ),
      (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2)^2 *
          ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖powTkMax d g s k m‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hblk⟩ := hm
  set τ : ℝ := powSig d / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith [powSig_pos d]
  have hτσ : τ < powSig d := by rw [hτdef]; linarith [powSig_pos d]
  set W : ℝ≥0∞ := ∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ) with hW
  set D : ℝ≥0∞ := ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
    ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2)^2) with hD
  have hWfin : W < ∞ := by rw [hW]; exact tsum_block_weight_sig_lt_top hτpos
  have hDfin : D < ∞ := by rw [hD]; exact tsum_scaled_K_sig_lt_top hCpos.le hτσ hτpos
  have hWD : W * D ≠ ∞ := ne_top_of_lt (ENNReal.mul_lt_top hWfin hDfin)
  refine ⟨Real.sqrt ((W * D).toReal) + 1, by positivity, ?_⟩
  intro g s hgs
  have hA : W * D ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := by
    have h5 : (W * D).toReal ≤ (Real.sqrt ((W * D).toReal) + 1)^2 := by
      rw [add_sq, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (W * D).toReal)]
      linarith [Real.sqrt_nonneg ((W * D).toReal)]
    calc W * D = ENNReal.ofReal ((W * D).toReal) := (ENNReal.ofReal_toReal hWD).symm
      _ ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := ENNReal.ofReal_le_ofReal h5
  have key : ∫⁻ m : ℤ, (⨆ k : ℕ, ‖powTkMax d g s k m‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ W * D * (∫⁻ m : ℤ, ‖g m‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
    have hK : ∀ m : ℕ,
        ∫⁻ x : ℤ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ)^(2:ℝ)
            ∂MeasureTheory.Measure.count
          ≤ (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2)^2)
              * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
      intro m
      exact hblk m g s hgs
    simpa only [hW, hD] using pow_lintegral_Tsup_sq_le d g s hτpos
      (fun m => ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2)^2)
      (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) hK
  refine le_trans key ?_
  exact mul_le_mul_of_nonneg_right hA (by positivity)


/-! ## The dilation, the sharp core and the profile error -/

/-- The dyadic dilation `(2^k)^d` of the `d`-th power scale. -/
noncomputable def powDil (d k : ℕ) : ℝ := ((2 : ℝ) ^ k) ^ d

lemma powDil_pos (d k : ℕ) : 0 < powDil d k := by rw [powDil]; positivity

lemma powDil_eq_nat (d k : ℕ) : powDil d k = (((2 ^ k : ℕ) : ℝ)) ^ d := by
  rw [powDil]; push_cast; ring

lemma powDil_mono (d : ℕ) {i j : ℕ} (h : i ≤ j) : powDil d i ≤ powDil d j := by
  rw [powDil, powDil]
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h) d

lemma powDil_rpow (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    (powDil d k) ^ ((1 : ℝ) / (d : ℝ)) = (2 : ℝ) ^ k := by
  rw [powDil, ← Real.rpow_natCast (((2:ℝ)^k)) d, ← Real.rpow_mul (by positivity)]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [show (d : ℝ) * ((1:ℝ)/(d:ℝ)) = 1 by field_simp, Real.rpow_one]

/-- The natural major-arc radius `N^{-(d-1/4)}` at the dyadic scale `N = 2^k`. -/
noncomputable def powArcRad (d k : ℕ) : ℝ := ((2 ^ k : ℕ) : ℝ) ^ (-((d : ℝ) - 1/4))

lemma powArcRad_pos (d k : ℕ) : 0 < powArcRad d k := by
  rw [powArcRad]; positivity

lemma powArcRad_antitone (d : ℕ) (hd : 1 ≤ d) {k k' : ℕ} (h : k ≤ k') :
    powArcRad d k' ≤ powArcRad d k := by
  rw [powArcRad, powArcRad]
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ ?_
  · exact_mod_cast Nat.pow_le_pow_right (by norm_num) h
  · have hdpos : (0:ℝ) < (d:ℝ) - 1/4 := by
      have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      linarith
    linarith

/-- `powArcRad d k < 1/2` for `d ≥ 2`, `k ≥ 1`. -/
lemma powArcRad_two_pow (d k : ℕ) :
    powArcRad d k = (((2:ℝ)^k)) ^ (-((d:ℝ) - 1/4)) := by
  rw [powArcRad]
  congr 1
  push_cast
  ring

lemma powArcRad_lt_half (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (hk : 1 ≤ k) : powArcRad d k < 1/2 := by
  rw [powArcRad_two_pow]
  have h1 : (1:ℝ) ≤ ((2:ℝ)^k) := one_le_pow₀ (by norm_num)
  have h2 : (2:ℝ) ≤ ((2:ℝ)^k) := by
    calc (2:ℝ) = (2:ℝ)^1 := by norm_num
      _ ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
  have hexp : -((d:ℝ) - 1/4) ≤ -(7/4:ℝ) := by
    have hd' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    linarith
  have hz : (-(7/4:ℝ)) ≤ 0 := by norm_num
  have h3 : (2:ℝ) < (2:ℝ)^((7:ℝ)/4) := by
    calc (2:ℝ) = (2:ℝ)^(1:ℝ) := (Real.rpow_one 2).symm
      _ < (2:ℝ)^((7:ℝ)/4) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have h4 : (0:ℝ) < (2:ℝ)^((7:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
  have h7 : (2:ℝ)^(-(7/4:ℝ)) < 1/2 := by
    rw [show (-(7/4:ℝ)) = -((7:ℝ)/4) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (1:ℝ)/2 = ((2:ℝ))⁻¹ by norm_num]
    exact (inv_lt_inv₀ h4 (by norm_num : (0:ℝ) < 2)).mpr h3
  have step1 : (((2:ℝ)^k)) ^ (-((d:ℝ) - 1/4)) ≤ (((2:ℝ)^k)) ^ (-(7/4:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h1 hexp
  have step2 : (((2:ℝ)^k)) ^ (-(7/4:ℝ)) ≤ (2:ℝ) ^ (-(7/4:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 2) h2 hz
  linarith [step1, step2, h7]

/-- The dilation is smaller than the natural major-arc radius. -/
lemma pow_inv_powDil_le_powArcRad (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    (powDil d k)⁻¹ ≤ powArcRad d k := by
  rw [powDil_eq_nat, powArcRad]
  set X : ℝ := (((2 ^ k : ℕ) : ℝ)) with hX
  have hX1 : (1:ℝ) ≤ X := by
    rw [hX]
    have : (1:ℕ) ≤ 2^k := Nat.one_le_two_pow
    exact_mod_cast this
  rw [← Real.rpow_natCast X d, ← Real.rpow_neg (by linarith : (0:ℝ) ≤ X)]
  refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
  linarith

open Classical in
/-- The sharp term of a single major-arc term at dyadic scale `k`. -/
noncomputable def powSharpTerm (d : ℕ) (q a : ℕ) (l : ℤ) (k : ℕ) (θ : ℝ) : ℂ :=
  powWeight d q a *
    (if |powDil d k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))| ≤ 1 then (1:ℂ) else 0)

open Classical in
/-- The single major-arc term of the block at dyadic scale `k`, restricted to its arc. -/
noncomputable def powModelTermArc (d : ℕ) (q a : ℕ) (l : ℤ) (k : ℕ) (θ : ℝ) : ℂ :=
  if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k then powModelTerm d (2^k) q a l θ else 0

open Classical in
/-- The **sharp core** of the `m`-th dyadic block at scale `k`. -/
noncomputable def powBlockCore (d : ℕ) (m k : ℕ) (θ : ℝ) : ℂ :=
  ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2 : ℤ) 2,
    starRingEnd ℂ (powWeight d i.1 i.2) *
      (if |powDil d k * (θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ))| ≤ 1 then (1:ℂ) else 0)

open Classical in
/-- The sharp core written as a weighted periodised-neighbourhood sum. -/
noncomputable def powBlockCorePer (d : ℕ) (m k : ℕ) (θ : ℝ) : ℂ :=
  ∑ i ∈ blockPair m, starRingEnd ℂ (powWeight d i.1 i.2) *
      (if ∃ l : ℤ, |θ + (l:ℝ) - (i.2:ℝ)/(i.1:ℝ)| ≤ (powDil d k)⁻¹ then (1:ℂ) else 0)

/-- The **error** of the `m`-th block at scale `k`: model minus sharp core. -/
noncomputable def powBlockErr (d : ℕ) (m k : ℕ) (θ : ℝ) : ℂ :=
  starRingEnd ℂ (powModelQBlock d m (2^k) θ) -
    (if 4*m+4 ≤ k then powBlockCore d m k θ else 0)

open Classical in
/-- The weighted frequency set of the `m`-th block, with the `d`-power complete-sum weights. -/
noncomputable def powBlockT (d : ℕ) (m : ℕ) : Finset (ℝ × ℂ) :=
  (blockPair m).image (fun i => ((i.2:ℝ)/(i.1:ℝ), starRingEnd ℂ (powWeight d i.1 i.2)))

lemma mem_powBlockT {d m : ℕ} {p : ℝ × ℂ} :
    p ∈ powBlockT d m ↔ ∃ i ∈ blockPair m,
      ((i.2:ℝ)/(i.1:ℝ), starRingEnd ℂ (powWeight d i.1 i.2)) = p := by
  rw [powBlockT, Finset.mem_image]

lemma powBlockT_card_le (d m : ℕ) : (powBlockT d m).card ≤ 2^(2*m+1) :=
  le_trans (Finset.card_image_le) (blockPair_card_le m)

lemma log_powBlockT_le (d m : ℕ) :
    Real.log (((powBlockT d m).card : ℝ) + 2) ≤ 2 * ((m:ℝ) + 2) := by
  have hcard : ((powBlockT d m).card : ℝ) ≤ (2:ℝ)^(2*m+1) := by
    have h := powBlockT_card_le d m
    calc ((powBlockT d m).card : ℝ) ≤ ((2^(2*m+1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (2:ℝ)^(2*m+1) := by push_cast; ring
  have hlog : Real.log (((powBlockT d m).card : ℝ) + 2) ≤ Real.log ((2:ℝ)^(2*m+1) + 2) := by
    refine Real.log_le_log ?_ ?_
    · positivity
    · linarith
  have h2 : Real.log ((2:ℝ)^(2*m+1) + 2) ≤ 2 * ((m:ℝ) + 2) := by
    have h3 : (2:ℝ)^(2*m+1) + 2 ≤ (2:ℝ)^(2*m+2) := by
      have hp : (2:ℝ)^(2*m+2) = 2 * (2:ℝ)^(2*m+1) := by
        rw [show 2*m+2 = (2*m+1)+1 by omega, pow_succ]; ring
      rw [hp]
      have hp1 : (2:ℝ) ≤ (2:ℝ)^(2*m+1) := by
        calc (2:ℝ) = (2:ℝ)^1 := by norm_num
          _ ≤ (2:ℝ)^(2*m+1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    refine le_trans (Real.log_le_log (by positivity) h3) ?_
    rw [Real.log_pow]
    have h4 : (0:ℝ) ≤ ((2*m+2 : ℕ) : ℝ) := by positivity
    have h5 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      norm_num at h
      linarith
    have h6 : ((2*m+2 : ℕ) : ℝ) * Real.log 2 ≤ ((2*m+2 : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h5 h4
    rw [mul_one] at h6
    have h7 : ((2*m+2 : ℕ) : ℝ) = 2 * ((m:ℝ) + 1) := by push_cast; ring
    rw [h7] at h6 ⊢
    linarith
  exact le_trans hlog h2

/-- Two distinct block frequencies never differ by an integer. -/
lemma powBlockT_freq_ne_zero {m : ℕ} {i i' : ℕ × ℕ} (hi : i ∈ blockPair m)
    (hi' : i' ∈ blockPair m) (hne : i ≠ i') (l : ℤ) :
    (i.2:ℝ)/i.1 - (i'.2:ℝ)/i'.1 + (l:ℝ) ≠ 0 := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hi
  obtain ⟨h1', h2', h3', h4'⟩ := mem_blockPair.mp hi'
  have hq1 : 0 < i.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1
  have hq2 : 0 < i'.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1'
  have b1 : (0:ℝ) ≤ (i.2:ℝ)/i.1 := by positivity
  have b1' : (i.2:ℝ)/i.1 < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast h3
  have b2 : (0:ℝ) ≤ (i'.2:ℝ)/i'.1 := by positivity
  have b2' : (i'.2:ℝ)/i'.1 < 1 := by rw [div_lt_one (by positivity)]; exact_mod_cast h3'
  have hlt1 : (l:ℝ) < 1 := by linarith
  have hgt1 : (-1:ℝ) < (l:ℝ) := by linarith
  have hl0 : l = 0 := by
    have h2'' : l < (1:ℤ) := by exact_mod_cast hlt1
    have h1'' : (-1:ℤ) < l := by exact_mod_cast hgt1
    omega
  rw [hl0] at h
  simp only [Int.cast_zero, add_zero] at h
  have hfr : (i.2:ℝ)/i.1 = (i'.2:ℝ)/i'.1 := by linarith
  obtain ⟨hqeq, haeq⟩ := frac_eq_of_coprime hq1 hq2
    (Nat.coprime_iff_gcd_eq_one.mpr h4) (Nat.coprime_iff_gcd_eq_one.mpr h4') h3 h3' hfr
  exact hne (Prod.ext hqeq haeq)

/-- **Separation of the frequencies of a block at scale `m`**: distinct frequencies are at least
`4^{-m-1}` apart (the frequencies are the same reduced rationals as in the quadratic case). -/
lemma powBlockT_sep (d : ℕ) (m : ℕ) :
    ∀ p ∈ powBlockT d m, ∀ q ∈ powBlockT d m, p ≠ q →
      ∀ (l : ℤ), 4 ^ (-(m:ℝ) - 1) ≤ |p.1 - q.1 + (l:ℝ)| := by
  intro p hp q hq hpq l
  rw [mem_powBlockT] at hp hq
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨i', hi', rfl⟩ := hq
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hi
  obtain ⟨h1', h2', h3', h4'⟩ := mem_blockPair.mp hi'
  have hq1 : 0 < i.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1
  have hq2 : 0 < i'.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1'
  have hii : i ≠ i' := by
    intro heq
    exact hpq (by rw [heq])
  have hne : (i.2:ℝ)/i.1 + ((0:ℤ):ℝ) ≠ (i'.2:ℝ)/i'.1 + (((-l : ℤ)):ℝ) := by
    intro hcontra
    refine powBlockT_freq_ne_zero hi hi' hii l ?_
    push_cast at hcontra
    linarith
  have hsep := majorArc_shift_sep (q₁ := i.1) (q₂ := i'.1) (a₁ := i.2) (a₂ := i'.2)
    (l₁ := 0) (l₂ := -l) hq1 hq2 hne
  simp only [Int.cast_zero, Int.cast_neg, add_zero] at hsep
  have hqq : (4:ℝ)^(-(m:ℝ)-1) ≤ ((i.1:ℝ)*(i'.1:ℝ))⁻¹ := by
    have hq1' : (i.1:ℝ) < (2:ℝ)^(m+1) := by exact_mod_cast h2
    have hq2' : (i'.1:ℝ) < (2:ℝ)^(m+1) := by exact_mod_cast h2'
    have hprod : (i.1:ℝ)*(i'.1:ℝ) ≤ (4:ℝ)^(m+1) := by
      rw [show (4:ℝ)^(m+1) = (2:ℝ)^(m+1) * (2:ℝ)^(m+1) by rw [← mul_pow]; norm_num]
      exact mul_le_mul hq1'.le hq2'.le (by positivity) (by positivity)
    calc (4:ℝ)^(-(m:ℝ)-1) = ((4:ℝ)^(m+1))⁻¹ := by
          rw [show (-(m:ℝ)-1) = -(((m+1 : ℕ) : ℝ)) by push_cast; ring,
            Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), ← Real.rpow_natCast (4:ℝ) (m+1)]
      _ ≤ ((i.1:ℝ)*(i'.1:ℝ))⁻¹ :=
          (inv_le_inv₀ (by positivity) (by positivity)).mpr hprod
  calc (4:ℝ)^(-(m:ℝ)-1) ≤ ((i.1:ℝ)*(i'.1:ℝ))⁻¹ := hqq
    _ ≤ |(i.2:ℝ)/(i.1:ℝ) - ((i'.2:ℝ)/(i'.1:ℝ) + (-(l:ℝ)))| := hsep
    _ = |(i.2:ℝ)/(i.1:ℝ) - (i'.2:ℝ)/(i'.1:ℝ) + (l:ℝ)| := by
        congr 1
        ring

open Classical in
/-- The single-frequency sharp-core identification at scale `k`: on `θ ∈ (0,1)`, for a frequency
`c ∈ [0,1)` and radius `r < 1/2` the sum of the sharp indicators `1_{|θ - c - l| ≤ r}` over
`l ∈ [-2,2]` is the periodised indicator. -/
lemma pow_sharpCore_sum_eq_periodic (d : ℕ) (k : ℕ) (c θ : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr0 : 0 < (powDil d k)⁻¹)
    (hr : (powDil d k)⁻¹ < 1 / 2) :
    (∑ l ∈ Finset.Icc (-2 : ℤ) 2,
        (if |powDil d k * (θ - c - (l : ℝ))| ≤ 1 then (1 : ℂ) else 0))
      = (if ∃ l : ℤ, |θ + (l : ℝ) - c| ≤ (powDil d k)⁻¹ then (1 : ℂ) else 0) := by
  have hpos : 0 < powDil d k := powDil_pos d k
  have hiff : ∀ l : ℤ, (|powDil d k * (θ - c - (l:ℝ))| ≤ 1)
      ↔ (|θ - c - (l:ℝ)| ≤ (powDil d k)⁻¹) := by
    intro l
    rw [abs_mul, abs_of_pos hpos, inv_eq_one_div, le_div_iff₀ hpos]
    constructor <;> intro h <;> linarith
  have hpt : ∀ l : ℤ, (if |powDil d k * (θ - c - (l:ℝ))| ≤ 1 then (1:ℂ) else 0)
      = (if |θ - c - (l:ℝ)| ≤ (powDil d k)⁻¹ then (1:ℂ) else 0) := by
    intro l
    by_cases h : |powDil d k * (θ - c - (l:ℝ))| ≤ 1
    · rw [if_pos h, if_pos ((hiff l).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hiff l).mpr hh))]
  rw [Finset.sum_congr rfl (fun l _ => hpt l)]
  exact sharpCore_sum_eq_periodic c θ ((powDil d k)⁻¹) hc0 hc1 hθ0 hθ1 hr0 hr

open Classical in
/-- **The block-level sharp-core identification.** -/
theorem powBlockCore_eq_periodic (d : ℕ) (hd : 2 ≤ d) (m k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) : powBlockCore d m k θ = powBlockCorePer d m k θ := by
  rw [powBlockCore, powBlockCorePer]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hmem := mem_blockPair.mp hi
  have hq1 : 1 ≤ i.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  have hqpos : (0:ℝ) < (i.1 : ℝ) := by exact_mod_cast hq1
  set c : ℝ := (i.2:ℝ)/(i.1:ℝ) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hqpos]; exact_mod_cast hmem.2.2.1
  have hr0 : (0:ℝ) < (powDil d k)⁻¹ := inv_pos.mpr (powDil_pos d k)
  have hr : (powDil d k)⁻¹ < 1/2 := by
    have h2 := pow_inv_powDil_le_powArcRad d hd k
    have h3 : powArcRad d k < 1/2 := powArcRad_lt_half d hd hk
    linarith
  have hinner := pow_sharpCore_sum_eq_periodic d k c θ hc0 hc1 hθ0 hθ1 hr0 hr
  rw [← Finset.mul_sum, hinner]

open Classical in
/-- The `q`-block of the model at scale `k` as a sum over arc-restricted terms. -/
lemma pow_majorArcBlock_two_pow_eq_sum (d : ℕ) (q k : ℕ) (θ : ℝ) :
    powMajorArcBlock d ((1:ℝ)/4) (2^k) θ q
      = ∑ a ∈ Finset.range q, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
          (if Nat.gcd a q = 1 then powModelTermArc d q a l k θ else 0) := by
  have hmb : powMajorArcBlock d ((1:ℝ)/4) (2^k) θ q
      = ∑ a ∈ Finset.range q, (if Nat.gcd a q = 1 then
          (∑ l ∈ Finset.Icc (-2:ℤ) 2, (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k
            then powModelTerm d (2^k) q a l θ else 0)) else 0) := by
    rw [powMajorArcBlock]; rfl
  rw [hmb]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  by_cases hg : Nat.gcd a q = 1
  · rw [if_pos hg]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [if_pos hg, powModelTermArc]
  · rw [if_neg hg, Finset.sum_eq_zero]
    intro l hl; rw [if_neg hg]

lemma pow_modelTerm_eq_weight_mul_powProfile (d N q a : ℕ) (l : ℤ) (θ : ℝ) :
    powModelTerm d N q a l θ
      = powWeight d q a * powProfile d (((θ - (a:ℝ)/(q:ℝ) - (l:ℝ)) * (N:ℝ)^d)) := rfl

lemma norm_powModelTerm_le_weight (d N q a : ℕ) (l : ℤ) (θ : ℝ) :
    ‖powModelTerm d N q a l θ‖ ≤ ‖powWeight d q a‖ := by
  rw [pow_modelTerm_eq_weight_mul_powProfile, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (norm_powProfile_le_one d _)

lemma pow_modelTermArc_eq_zero_of_not_act (d : ℕ) {k : ℕ} (q a : ℕ) (l : ℤ) (θ : ℝ)
    (h : ¬ |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k) : powModelTermArc d q a l k θ = 0 := by
  rw [powModelTermArc, if_neg h]

lemma pow_sharpTerm_eq_zero_of_not_act (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (q a : ℕ) (l : ℤ) (θ : ℝ)
    (h : ¬ |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k) : powSharpTerm d q a l k θ = 0 := by
  rw [powSharpTerm]
  have h2 : ¬ |powDil d k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))| ≤ 1 := by
    intro hc
    apply h
    have h4 : (0:ℝ) < powDil d k := powDil_pos d k
    have hc' : powDil d k * |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ 1 := by
      rwa [abs_mul, abs_of_pos h4] at hc
    have hb : |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ (powDil d k)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ h4]
      linarith
    linarith [pow_inv_powDil_le_powArcRad d hd k]
  rw [if_neg h2, mul_zero]

lemma norm_powModelTermArc_sub_sharp_le (d : ℕ) (hd : 2 ≤ d) {k : ℕ} (q a : ℕ) (l : ℤ) (θ : ℝ) :
    ‖powModelTermArc d q a l k θ - powSharpTerm d q a l k θ‖
      ≤ ‖powWeight d q a‖ * ‖powProfile d (powDil d k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ)))
          - (if |powDil d k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))| ≤ 1 then (1:ℂ) else 0)‖ := by
  by_cases harc : |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k
  · have h1 : powModelTermArc d q a l k θ = powModelTerm d (2^k) q a l θ := by
      rw [powModelTermArc, if_pos harc]
    have htm : powModelTerm d (2^k) q a l θ
        = powWeight d q a * powProfile d (powDil d k * (θ - (a:ℝ)/(q:ℝ) - (l:ℝ))) := by
      rw [powModelTerm, powDil_eq_nat]
      congr 2
      ring
    rw [h1, htm, powSharpTerm, ← mul_sub]
    exact le_of_eq (norm_mul _ _)
  · rw [pow_modelTermArc_eq_zero_of_not_act d q a l θ harc,
      pow_sharpTerm_eq_zero_of_not_act d hd q a l θ harc, sub_zero, norm_zero]
    positivity

lemma conj_powWeight_ite (d q a : ℕ) (b : Prop) [Decidable b] :
    starRingEnd ℂ (powWeight d q a * (if b then (1:ℂ) else 0))
      = starRingEnd ℂ (powWeight d q a) * (if b then (1:ℂ) else 0) := by
  rw [map_mul, conj_ite_one_zero]

lemma powBlockCore_eq_sum_sharpTerm (d : ℕ) (m k : ℕ) (θ : ℝ) :
    powBlockCore d m k θ
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
          starRingEnd ℂ (powSharpTerm d i.1 i.2 l k θ) := by
  rw [powBlockCore]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rw [powSharpTerm, conj_powWeight_ite]

open Classical in
lemma pow_modelQBlock_two_pow_eq_blockPair (d : ℕ) {m k : ℕ} (hk : 4*m+4 ≤ k) (θ : ℝ) :
    starRingEnd ℂ (powModelQBlock d m (2^k) θ)
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
          starRingEnd ℂ (powModelTermArc d i.1 i.2 l k θ) := by
  have h1 : starRingEnd ℂ (powModelQBlock d m (2^k) θ)
      = ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-2:ℤ) 2, starRingEnd ℂ (powModelTermArc d q a l k θ) := by
    rw [powModelQBlock, blockQ_eq m k hk, map_sum]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [pow_majorArcBlock_two_pow_eq_sum, map_sum]
    have hstep : ∀ a : ℕ,
        starRingEnd ℂ (∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if Nat.gcd a q = 1 then powModelTermArc d q a l k θ else 0))
          = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-2:ℤ) 2,
              starRingEnd ℂ (powModelTermArc d q a l k θ) else 0) := by
      intro a
      rw [map_sum]
      rw [Finset.sum_congr rfl (fun l hl => conj_ite_zero _ (powModelTermArc d q a l k θ))]
      exact sum_ite_gcd_eq a q (fun l => starRingEnd ℂ (powModelTermArc d q a l k θ))
    rw [Finset.sum_congr rfl (fun a ha => hstep a)]
    rw [← Finset.sum_filter]
  rw [h1, sum_blockPair m]

lemma pow_blockErr_eq_sum (d : ℕ) {m k : ℕ} (hk : 4*m+4 ≤ k) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    powBlockErr d m k θ = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
        starRingEnd ℂ (powModelTermArc d i.1 i.2 l k θ - powSharpTerm d i.1 i.2 l k θ) := by
  rw [powBlockErr, if_pos hk, pow_modelQBlock_two_pow_eq_blockPair d hk θ,
    powBlockCore_eq_sum_sharpTerm]
  simp_rw [← Finset.sum_sub_distrib, ← map_sub]


/-! ## The profile error of the dyadic blocks -/

/-- `powProfile d 0 = 1`. -/
lemma powProfile_zero (d : ℕ) : powProfile d 0 = 1 := by
  rw [powProfile]
  simp

/-- **Replacement of the profile by a sharp core.**  For `x ≠ 0`,
`∑_k ‖v_d(2^{dk} x) − 1_{|2^{dk}x| ≤ 1}‖ ≤ C`. -/
theorem powProfile_replace_sharp_tsum_le (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ≠ 0 →
      (∑' k : ℕ, ‖powProfile d (powDil d k * x)
        - (if |powDil d k * x| ≤ 1 then (1:ℂ) else 0)‖) ≤ C := by
  obtain ⟨C0, hC0pos, hdecay⟩ := powProfile_decay d hd
  have hC0le : C0 ≤ max C0 2 := le_max_left _ _
  refine ⟨8 * Real.pi / 3 + 2 * (max C0 2) + 1, by positivity, fun x hx => ?_⟩
  set C1 : ℝ := max C0 2 with hC1
  have hC1pos : 0 < C1 := lt_of_lt_of_le (by norm_num) (le_max_right C0 2)
  have hdecay' : ∀ y : ℝ, 1 ≤ |y| → ‖powProfile d y‖ ≤ C1 * (|y| ^ ((1:ℝ)/(d:ℝ)))⁻¹ :=
    fun y hy => le_trans (hdecay y hy) (mul_le_mul_of_nonneg_right hC0le (by positivity))
  have hxabs : (0:ℝ) < |x| := abs_pos.mpr hx
  have habs : ∀ k : ℕ, |powDil d k * x| = powDil d k * |x| := fun k => by
    rw [abs_mul, abs_of_nonneg (powDil_pos d k).le]
  have hmono : ∀ i j, i ≤ j → |powDil d i * x| ≤ |powDil d j * x| := by
    intro i j hij
    rw [habs i, habs j]
    exact mul_le_mul_of_nonneg_right (powDil_mono d hij) (abs_nonneg x)
  have hex : ∃ k : ℕ, 1 < |powDil d k * x| := by
    have htop : Tendsto (fun k : ℕ => (4:ℝ)^k * |x|) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 4)).atTop_mul_const hxabs
    obtain ⟨k, hk⟩ := (htop.eventually (eventually_gt_atTop (1:ℝ))).exists
    refine ⟨k, ?_⟩
    rw [habs k]
    have h4k : (4:ℝ)^k ≤ powDil d k := by
      rw [powDil]
      calc (4:ℝ)^k = ((2:ℝ)^k)^2 := by rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul]; ring
        _ ≤ ((2:ℝ)^k)^d := pow_le_pow_right₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hd
    have : (4:ℝ)^k * |x| ≤ powDil d k * |x| :=
      mul_le_mul_of_nonneg_right h4k (abs_nonneg x)
    linarith
  set j : ℕ := Nat.find hex with hjdef
  have hj_spec : 1 < |powDil d j * x| := Nat.find_spec hex
  have hj_min : ∀ i, i < j → |powDil d i * x| ≤ 1 :=
    fun i hi => not_lt.mp (Nat.find_min hex hi)
  have hj_le : ∀ i, j ≤ i → 1 < |powDil d i * x| :=
    fun i hi => lt_of_lt_of_le hj_spec (hmono j i hi)
  set f : ℕ → ℝ := fun k => ‖powProfile d (powDil d k * x)
      - (if |powDil d k * x| ≤ 1 then (1:ℂ) else 0)‖ with hf
  have hfk : ∀ k : ℕ, f k = ‖powProfile d (powDil d k * x)
      - (if powDil d k * |x| ≤ 1 then (1:ℂ) else 0)‖ := by
    intro k
    rw [hf]
    simp only [habs k]
  have hcond_le : ∀ i, i < j → powDil d i * |x| ≤ 1 := fun i hi => by
    rw [← habs i]; exact hj_min i hi
  have hcond_gt : ∀ i, j ≤ i → 1 < powDil d i * |x| := fun i hi => by
    rw [← habs i]; exact hj_le i hi
  have hnonneg : ∀ k, 0 ≤ f k := fun k => norm_nonneg _
  have hf_bound : ∀ k, f k ≤ (if k < j then 2 * Real.pi * (powDil d k * |x|) else 0)
      + C1 * (|x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * (1/2)^k := by
    intro k
    have h2nn : (0:ℝ) ≤ C1 * (|x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * (1/2:ℝ)^k := by positivity
    rw [hfk k]
    rcases lt_or_ge k j with hk | hk
    · rw [if_pos hk, if_pos (hcond_le k hk)]
      have h1 : ‖powProfile d (powDil d k * x) - 1‖ ≤ 2 * Real.pi * (powDil d k * |x|) := by
        have h := powProfile_sub_one_le d hd (powDil d k * x)
        rw [habs k] at h
        exact h
      linarith [h1, h2nn]
    · rw [if_neg (not_lt.mpr hk), if_neg (not_le.mpr (hcond_gt k hk)), sub_zero]
      have hkd := hdecay' (powDil d k * x) (le_of_lt (by rw [habs k]; exact hcond_gt k hk))
      have h2 : (powDil d k * |x|) ^ ((1:ℝ)/(d:ℝ))
          = (2:ℝ)^k * |x| ^ ((1:ℝ)/(d:ℝ)) := by
        rw [Real.mul_rpow (powDil_pos d k).le (abs_nonneg x), powDil_rpow d (by omega) k]
      rw [habs k, h2] at hkd
      have h3 : ((2:ℝ)^k * |x| ^ ((1:ℝ)/(d:ℝ)))⁻¹
          = (|x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * (1/2)^k := by
        rw [mul_inv]
        have h4 : ((2:ℝ)^k)⁻¹ = (1/2:ℝ)^k := by
          rw [show (1:ℝ)/2 = ((2:ℝ))⁻¹ by norm_num, ← inv_pow]
        rw [h4]; ring
      rw [h3] at hkd
      linarith [hkd]
  have hsumg : Summable (fun k : ℕ => (if k < j then 2 * Real.pi * (powDil d k * |x|) else 0)
      + C1 * (|x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * (1/2)^k) := by
    refine Summable.add ?_ ?_
    · refine summable_of_ne_finset_zero (s := Finset.range j) ?_
      intro k hk
      rw [Finset.mem_range] at hk
      exact if_neg hk
    · exact (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
  have hsumf : Summable f := Summable.of_nonneg_of_le hnonneg hf_bound hsumg
  rw [← Summable.sum_add_tsum_nat_add j hsumf]
  have hd2 : (4:ℝ) ≤ (2:ℝ)^d := by
    calc (4:ℝ) = (2:ℝ)^2 := by norm_num
      _ ≤ (2:ℝ)^d := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hd
  have hden : (0:ℝ) < (2:ℝ)^d - 1 := by linarith
  have hfin : ∑ i ∈ Finset.range j, f i ≤ 8 * Real.pi / 3 := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]; simp; positivity
    have h1 : ∑ i ∈ Finset.range j, f i
        ≤ ∑ i ∈ Finset.range j, 2 * Real.pi * (powDil d i * |x|) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hij : i < j := Finset.mem_range.mp hi
      rw [hfk i, if_pos (hcond_le i hij)]
      have h := powProfile_sub_one_le d hd (powDil d i * x)
      rw [habs i] at h
      exact h
    refine le_trans h1 ?_
    have hgeo : ∑ i ∈ Finset.range j, powDil d i
        = (((2:ℝ)^d)^j - 1) / ((2:ℝ)^d - 1) := by
      have h2d1 : ((2:ℝ)^d) ≠ 1 := by
        have h : (2:ℝ)^1 < (2:ℝ)^d := pow_lt_pow_right₀ (by norm_num) (by omega)
        linarith
      have hpd : ∀ i : ℕ, powDil d i = ((2:ℝ)^d)^i := by
        intro i
        rw [powDil, ← pow_mul, ← pow_mul, Nat.mul_comm]
      calc ∑ i ∈ Finset.range j, powDil d i
          = ∑ i ∈ Finset.range j, ((2:ℝ)^d)^i :=
            Finset.sum_congr rfl (fun i _ => hpd i)
        _ = (((2:ℝ)^d)^j - 1) / ((2:ℝ)^d - 1) := geom_sum_eq h2d1 j
    have hpowj : ((2:ℝ)^d)^j = powDil d j := by
      rw [powDil, ← pow_mul, ← pow_mul, Nat.mul_comm]
    have hxj : |x| * powDil d j ≤ (2:ℝ)^d := by
      have h1 := hj_min (j - 1) (by omega)
      rw [habs (j - 1)] at h1
      have e1 : powDil d j = powDil d (j - 1) * (2:ℝ)^d := by
        have hj : (2:ℝ)^j = (2:ℝ)^(j-1) * 2 := by
          conv_lhs => rw [show j = (j-1)+1 by omega]
          rw [pow_succ]
        rw [powDil, powDil, hj, mul_pow]
      rw [e1]
      nlinarith [h1, powDil_pos d (j-1), abs_nonneg x]
    have h43 : |x| * (powDil d j / ((2:ℝ)^d - 1)) ≤ 4/3 := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [hxj, hd2, hden]
    calc ∑ i ∈ Finset.range j, 2 * Real.pi * (powDil d i * |x|)
        = 2 * Real.pi * |x| * ∑ i ∈ Finset.range j, powDil d i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 2 * Real.pi * |x| * ((powDil d j - 1) / ((2:ℝ)^d - 1)) := by
          rw [hgeo, hpowj]
      _ ≤ 2 * Real.pi * |x| * (powDil d j / ((2:ℝ)^d - 1)) := by
          have h5 : (powDil d j - 1) / ((2:ℝ)^d - 1) ≤ powDil d j / ((2:ℝ)^d - 1) :=
            div_le_div_of_nonneg_right (by linarith [powDil_pos d j]) hden.le
          have hp : (0:ℝ) ≤ 2 * Real.pi * |x| := by positivity
          exact mul_le_mul_of_nonneg_left h5 hp
      _ = 2 * Real.pi * (|x| * (powDil d j / ((2:ℝ)^d - 1))) := by ring
      _ ≤ 2 * Real.pi * (4/3) := by
          have hp : (0:ℝ) ≤ 2 * Real.pi := by positivity
          exact mul_le_mul_of_nonneg_left h43 hp
      _ = 8 * Real.pi / 3 := by ring
  have htail : ∑' i : ℕ, f (i + j) ≤ 2 * C1 := by
    have hle : ∀ i : ℕ, f (i + j) ≤ C1 * ((2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * (1/2)^i := by
      intro i
      have hji : ¬ (i + j < j) := by omega
      have hb := hf_bound (i + j)
      rw [if_neg hji, zero_add] at hb
      refine le_trans hb ?_
      rw [pow_add]
      have he : C1 * (|x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * ((1/2:ℝ)^i * (1/2)^j)
          = C1 * ((2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * (1/2)^i := by
        rw [mul_inv]
        have h4 : ((2:ℝ)^j)⁻¹ = (1/2:ℝ)^j := by
          rw [show (1:ℝ)/2 = ((2:ℝ))⁻¹ by norm_num, ← inv_pow]
        rw [h4]; ring
      rw [he]
    have hsumg : Summable (fun i : ℕ => C1 * ((2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * (1/2)^i) :=
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
    have hsumf' : Summable (fun i : ℕ => f (i + j)) :=
      hsumf.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hcmp := Summable.tsum_le_tsum hle hsumf' hsumg
    have hval : (∑' i : ℕ, C1 * ((2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ * (1/2:ℝ)^i)
        = 2 * (C1 * ((2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)))⁻¹) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    rw [hval] at hcmp
    have h2jpos : (0:ℝ) < (2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)) := by
      have h1 : (0:ℝ) < powDil d j := powDil_pos d j
      have h2 : (0:ℝ) < |x| ^ ((1:ℝ)/(d:ℝ)) := Real.rpow_pos_of_pos hxabs _
      positivity
    have hj1 : (1:ℝ) ≤ (2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)) := by
      have hy1 : 1 < powDil d j * |x| := by rw [← habs j]; exact hj_spec
      have hz : (0:ℝ) < (1:ℝ)/(d:ℝ) := by positivity
      have h1 : (powDil d j * |x|) ^ ((1:ℝ)/(d:ℝ))
          = (2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)) := by
        rw [Real.mul_rpow (powDil_pos d j).le (abs_nonneg x), powDil_rpow d (by omega) j]
      rw [← h1]
      exact le_of_lt (Real.one_lt_rpow hy1 hz)
    have h2jinv : ((2:ℝ)^j * |x| ^ ((1:ℝ)/(d:ℝ)))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ h2jpos]; exact hj1
    nlinarith [hcmp, hC1pos, h2jinv]
  linarith [hfin, htail]

/-- The real-valued profile replacement error at dyadic scale `K`. -/
noncomputable def powErrVal (d : ℕ) (x : ℝ) (K : ℕ) : ℝ :=
  ‖powProfile d (powDil d K * x) - (if |powDil d K * x| ≤ 1 then (1:ℂ) else 0)‖

/-- The `ℝ≥0∞`-valued profile replacement error at dyadic scale `K`. -/
noncomputable def powErrNorm (d : ℕ) (q a : ℕ) (l : ℤ) (K : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (powErrVal d (θ - (a:ℝ)/(q:ℝ) - (l:ℝ)) K)

/-- Uniform bound on the profile replacement error. -/
lemma powErrVal_le (d : ℕ) (hd : 2 ≤ d) (x : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℕ,
      powErrVal d x K ≤ M * ((1:ℝ)/2)^K * |x| ^ (-((1:ℝ)/(d:ℝ))) := by
  obtain ⟨C, hCpos, hdecay⟩ := powProfile_decay d hd
  refine ⟨max (2*Real.pi) C, lt_of_lt_of_le (by positivity) (le_max_left _ _), fun K => ?_⟩
  set M : ℝ := max (2*Real.pi) C with hM
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set y : ℝ := powDil d K * x with hy
  have hyabs : |y| = powDil d K * |x| := by rw [hy, abs_mul, abs_of_nonneg (powDil_pos d K).le]
  have hpoweq : (powDil d K * |x|) ^ (-((1:ℝ)/(d:ℝ)))
      = ((2:ℝ)^K)⁻¹ * |x| ^ (-((1:ℝ)/(d:ℝ))) := by
    rw [Real.mul_rpow (powDil_pos d K).le (abs_nonneg x), powDil, ← Real.rpow_natCast (((2:ℝ)^K)) d,
      ← Real.rpow_mul (by positivity)]
    congr 1
    rw [show (d:ℝ) * (-((1:ℝ)/(d:ℝ))) = -1 by field_simp]
    rw [Real.rpow_neg_one]
  have hmain : ‖powProfile d y - (if |y| ≤ 1 then (1:ℂ) else 0)‖ ≤ M * |y| ^ (-((1:ℝ)/(d:ℝ))) := by
    by_cases hyl : |y| ≤ 1
    · rw [if_pos hyl]
      have h1 := powProfile_sub_one_le d hd y
      have h2 : (2*Real.pi) * |y| ≤ M * |y| ^ (-((1:ℝ)/(d:ℝ))) := by
        rcases eq_or_lt_of_le (abs_nonneg y) with h0 | h0
        · rw [← h0, Real.zero_rpow (x := -((1:ℝ)/(d:ℝ))) (by
            rw [neg_ne_zero]; positivity)]; simp
        · have h1' : (1:ℝ) ≤ |y| ^ (-((1:ℝ)/(d:ℝ))) := by
            have hc : (-((1:ℝ)/(d:ℝ))) ≤ 0 := by
              rw [neg_nonpos]
              have hdpos : (0:ℝ) < (d:ℝ) := by positivity
              exact le_of_lt (div_pos one_pos hdpos)
            have hh := Real.rpow_le_rpow_of_nonpos (x := |y|) (y := 1)
              (z := -((1:ℝ)/(d:ℝ))) h0 hyl hc
            simpa using hh
          have hM' : (2*Real.pi) ≤ M := le_max_left _ _
          calc (2*Real.pi) * |y| ≤ (2*Real.pi) * 1 :=
                mul_le_mul_of_nonneg_left hyl (by positivity)
            _ ≤ M * |y| ^ (-((1:ℝ)/(d:ℝ))) :=
                mul_le_mul hM' h1' (by norm_num) (by positivity)
      linarith
    · rw [if_neg hyl, sub_zero]
      have h1 := hdecay y (le_of_lt (lt_of_not_ge hyl))
      have h2 : C / (|y| ^ ((1:ℝ)/(d:ℝ))) ≤ C * |y| ^ (-((1:ℝ)/(d:ℝ))) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg (abs_nonneg y)]
      have h3 : C ≤ M := le_max_right _ _
      have h4 : 0 ≤ |y| ^ (-((1:ℝ)/(d:ℝ))) := Real.rpow_nonneg (abs_nonneg y) _
      calc ‖powProfile d y‖ ≤ C / |y| ^ ((1:ℝ)/(d:ℝ)) := by
            rw [div_eq_mul_inv]
            exact h1
        _ ≤ C * |y| ^ (-((1:ℝ)/(d:ℝ))) := h2
        _ ≤ M * |y| ^ (-((1:ℝ)/(d:ℝ))) := mul_le_mul_of_nonneg_right h3 h4
  have hfal : ((2:ℝ)^K)⁻¹ = ((1:ℝ)/2)^K := by
    rw [show (1:ℝ)/2 = ((2:ℝ))⁻¹ by norm_num, ← inv_pow]
  calc powErrVal d x K = ‖powProfile d y - (if |y| ≤ 1 then (1:ℂ) else 0)‖ := by
        rw [powErrVal, hy]
    _ ≤ M * |y| ^ (-((1:ℝ)/(d:ℝ))) := hmain
    _ = M * (((2:ℝ)^K)⁻¹ * |x| ^ (-((1:ℝ)/(d:ℝ)))) := by rw [hyabs, hpoweq]
    _ = M * ((1:ℝ)/2)^K * |x| ^ (-((1:ℝ)/(d:ℝ))) := by rw [hfal]; ring

/-- The profile replacement error is summable along the dyadic scales. -/
lemma summable_powErrVal (d : ℕ) (hd : 2 ≤ d) (x : ℝ) : Summable (powErrVal d x) := by
  obtain ⟨M, hMpos, hM⟩ := powErrVal_le d hd x
  have hgeo : Summable (fun K : ℕ => ((1:ℝ)/2)^K) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hmaj : Summable (fun K : ℕ => M * |x| ^ (-((1:ℝ)/(d:ℝ))) * ((1:ℝ)/2)^K) :=
    (hgeo.mul_left (M * |x| ^ (-((1:ℝ)/(d:ℝ))))).congr (fun K => by ring)
  refine Summable.of_nonneg_of_le (fun K => norm_nonneg _) (fun K => ?_) hmaj
  calc powErrVal d x K ≤ M * ((1:ℝ)/2)^K * |x| ^ (-((1:ℝ)/(d:ℝ))) := hM K
    _ = M * |x| ^ (-((1:ℝ)/(d:ℝ))) * ((1:ℝ)/2)^K := by ring

lemma enorm_eq_ofReal_norm''' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- The profile errors of the `m`-th block form an `ℓ¹`-in-scale family. -/
lemma powErrNorm_tsum_le (d : ℕ) (hd : 2 ≤ d) {Cf : ℝ} (hCf0 : 0 ≤ Cf)
    (hCf : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, powErrVal d x k) ≤ Cf) :
    ∀ (q a : ℕ) (l : ℤ) (θ : ℝ),
      (∑' K : ℕ, powErrNorm d q a l K θ) ≤ ENNReal.ofReal Cf := by
  intro q a l θ
  set x : ℝ := θ - (a:ℝ)/(q:ℝ) - (l:ℝ) with hx
  have h1 : (∑' K : ℕ, powErrNorm d q a l K θ)
      = ENNReal.ofReal (∑' K : ℕ, powErrVal d x K) := by
    simp only [powErrNorm, powErrVal, ← hx]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun K => norm_nonneg _) (summable_powErrVal d hd x)]
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hx0 : x = 0
  · have hz : ∀ K, powErrVal d x K = 0 := by
      intro K
      have h0 : powDil d K * x = 0 := by rw [hx0, mul_zero]
      rw [powErrVal, h0, powProfile_zero]
      norm_num
    simp only [hz, tsum_zero]
    exact hCf0
  · exact hCf x hx0


/-! ## The block operators: structural bounds -/

open Classical in
/-- The partial-block expansion of the `m`-th model block at scale `k`. -/
theorem star_powModelQBlock_eq_sum (d : ℕ) {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) :
    starRingEnd ℂ (powModelQBlock d m (2^k) θ)
      = ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter
            (fun q => q ≤ Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4))),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-2:ℤ) 2, starRingEnd ℂ (powModelTermArc d q a l k θ) := by
  rw [powModelQBlock, blockQ_eq_filter_le m k hk, map_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [pow_majorArcBlock_two_pow_eq_sum, map_sum]
  have hstep : ∀ a : ℕ,
      starRingEnd ℂ (∑ l ∈ Finset.Icc (-2:ℤ) 2,
          (if Nat.gcd a q = 1 then powModelTermArc d q a l k θ else 0))
        = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            starRingEnd ℂ (powModelTermArc d q a l k θ) else 0) := by
    intro a
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun l hl => conj_ite_zero _ (powModelTermArc d q a l k θ))]
    exact sum_ite_gcd_eq a q (fun l => starRingEnd ℂ (powModelTermArc d q a l k θ))
  rw [Finset.sum_congr rfl (fun a ha => hstep a)]
  rw [← Finset.sum_filter]



/-! ## The active index set at the natural radius -/

open Classical in
/-- The active index set of the `m`-th dyadic block at scale `k`. -/
noncomputable def powActIdx (d : ℕ) (m k : ℕ) (θ : ℝ) : Finset ((ℕ × ℕ) × ℤ) :=
  (blockPair m ×ˢ Finset.Icc (-2 : ℤ) 2).filter
    (fun p => |θ - (p.1.2 : ℝ)/(p.1.1 : ℝ) - (p.2 : ℝ)| ≤ powArcRad d k)

lemma mem_powActIdx {d m k : ℕ} {θ : ℝ} {p : (ℕ × ℕ) × ℤ} :
    p ∈ powActIdx d m k θ ↔ p.1 ∈ blockPair m ∧ p.2 ∈ Finset.Icc (-2:ℤ) 2 ∧
      |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ powArcRad d k := by
  rw [powActIdx, Finset.mem_filter, Finset.mem_product]
  tauto

lemma powActIdx_eq_filter (d m k : ℕ) (θ : ℝ) :
    powActIdx d m k θ = (allIdx m).filter
      (fun p => |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ powArcRad d k) := rfl

lemma powActIdx_subset (d : ℕ) (hd : 1 ≤ d) {m : ℕ} {θ : ℝ} {k k' : ℕ} (h : k ≤ k') :
    powActIdx d m k' θ ⊆ powActIdx d m k θ := by
  intro p hp
  rw [mem_powActIdx] at hp ⊢
  exact ⟨hp.1, hp.2.1, le_trans hp.2.2 (powArcRad_antitone d hd h)⟩

/-- At most one index of a dyadic block is active at any frequency, for `k ≥ 2m+3`. -/
lemma powActIdx_card_le_one (d : ℕ) (hd : 2 ≤ d) {m k : ℕ} (hk : 2*m + 3 ≤ k) (θ : ℝ) :
    (powActIdx d m k θ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  rw [mem_powActIdx] at hp hq
  obtain ⟨hp1, hp2, hparc⟩ := hp
  obtain ⟨hq1, hq2, hqarc⟩ := hq
  have hmemP := mem_blockPair.mp hp1
  have hmemQ := mem_blockPair.mp hq1
  have hppos : 0 < p.1.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  have hqpos : 0 < q.1.1 := by
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  have hk1 : 1 ≤ k := by omega
  by_cases hqa : p.1 = q.1
  · have hqarc' : |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ)| ≤ powArcRad d k := by
      have h := hqarc
      rw [← hqa] at h
      exact h
    have hl : p.2 = q.2 := by
      by_contra hne
      have h2r : 2 * powArcRad d k < 1 := by
        have h1 := powArcRad_lt_half d hd hk1
        linarith
      have hkey : |(p.2:ℝ) - (q.2:ℝ)| ≤ 2 * powArcRad d k := by
        have h := abs_sub_zero (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))
          (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ))
        rw [show (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))
              - (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (q.2:ℝ)) = (q.2:ℝ) - (p.2:ℝ) by ring,
          abs_sub_comm] at h
        linarith
      have hcast : (((p.2 - q.2 : ℤ)) : ℝ) = (p.2:ℝ) - (q.2:ℝ) := by push_cast; ring
      have hlt : |((p.2 - q.2 : ℤ) : ℝ)| < 1 := by rw [hcast]; linarith
      rw [← Int.cast_abs] at hlt
      have h2 : |p.2 - q.2| < (1:ℤ) := by exact_mod_cast hlt
      rw [abs_lt] at h2
      exact hne (by omega)
    exact Prod.ext hqa hl
  · have hp_lt : (p.1.1:ℝ) < (2:ℝ)^(m+1) := by
      have := hmemP.2.1
      exact_mod_cast this
    have hq_lt : (q.1.1:ℝ) < (2:ℝ)^(m+1) := by
      have := hmemQ.2.1
      exact_mod_cast this
    have hppos' : (0:ℝ) < (p.1.1:ℝ) := by exact_mod_cast hppos
    have hqpos' : (0:ℝ) < (q.1.1:ℝ) := by exact_mod_cast hqpos
    have hpow : (2:ℝ)^(m+1) * (2:ℝ)^(m+1) = (2:ℝ)^(2*m+2) := by
      rw [← pow_add]
      congr 1
      ring
    have hprod : ((p.1.1:ℝ) * (q.1.1:ℝ)) ≤ (2:ℝ)^(2*m+2) := by
      have hpq : (p.1.1:ℝ) * (q.1.1:ℝ) < (2:ℝ)^(m+1) * (2:ℝ)^(m+1) :=
        mul_lt_mul hp_lt (le_of_lt hq_lt) hqpos' (by positivity)
      rw [hpow] at hpq
      exact le_of_lt hpq
    have hsep : 2 * powArcRad d k < ((p.1.1:ℝ) * (q.1.1:ℝ))⁻¹ := by
      refine lt_of_lt_of_le ?_ ((inv_le_inv₀ (by positivity) (by positivity)).mpr hprod)
      have hk' : (2 * (m:ℝ) + 3) ≤ (k:ℝ) := by exact_mod_cast hk
      have hd' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hexp : (1:ℝ) - (k:ℝ) * ((d:ℝ) - 1/4) < -(((2*m+2 : ℕ)) : ℝ) := by
        have h4 : (7/4:ℝ) ≤ (d:ℝ) - 1/4 := by linarith
        have h5 : (7/4:ℝ) * (k:ℝ) ≤ ((d:ℝ) - 1/4) * (k:ℝ) :=
          mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg k)
        push_cast
        nlinarith
      have hA : powArcRad d k = (2:ℝ)^(-((k:ℝ) * ((d:ℝ) - 1/4))) := by
        rw [powArcRad_two_pow, ← Real.rpow_natCast (2:ℝ) k,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      have h2 : 2 * powArcRad d k = (2:ℝ)^((1:ℝ) - (k:ℝ) * ((d:ℝ) - 1/4)) := by
        calc 2 * powArcRad d k
            = (2:ℝ)^(1:ℝ) * (2:ℝ)^(-((k:ℝ) * ((d:ℝ) - 1/4))) := by
                rw [Real.rpow_one, hA]
          _ = (2:ℝ)^((1:ℝ) + -((k:ℝ) * ((d:ℝ) - 1/4))) :=
                (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
          _ = (2:ℝ)^((1:ℝ) - (k:ℝ) * ((d:ℝ) - 1/4)) := by
                ring_nf
      rw [h2, ← Real.rpow_natCast (2:ℝ) (2*m+2), ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
    have huniq := majorArc_term_unique hppos hqpos hmemP.2.2.1 hmemQ.2.2.1
      (Nat.coprime_iff_gcd_eq_one.mp hmemP.2.2.2) (Nat.coprime_iff_gcd_eq_one.mp hmemQ.2.2.2)
      hparc hqarc hsep
    obtain ⟨h1, h2, h3⟩ := huniq
    exact absurd (Prod.ext (Prod.ext h1 h2) h3) (fun h' => hqa (congrArg Prod.fst h'))

/-- The active index set of a dyadic block has at most `80` elements. -/
lemma card_powActIdx_le_eighty (d : ℕ) (hd : 2 ≤ d) {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) :
    (powActIdx d m k θ).card ≤ 80 := by
  by_cases h : 2*m+3 ≤ k
  · exact le_trans (powActIdx_card_le_one d hd h θ) (by norm_num)
  · have hm1 : m ≤ 1 := by omega
    have hsub : powActIdx d m k θ ⊆ ((Finset.range 4) ×ˢ (Finset.range 4)) ×ˢ
        (Finset.Icc (-2:ℤ) 2) := by
      intro p hp
      obtain ⟨hmem, hl, _⟩ := mem_powActIdx.mp hp
      obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hmem
      have hm4 : 2^(m+1) ≤ 4 := by
        calc 2^(m+1) = 2^m * 2 := by rw [pow_succ]
          _ ≤ 2^1 * 2 := Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by norm_num) hm1)
          _ = 4 := by norm_num
      rw [Finset.mem_product, Finset.mem_product]
      exact ⟨⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, hl⟩
    calc (powActIdx d m k θ).card
        ≤ (((Finset.range 4) ×ˢ (Finset.range 4)) ×ˢ (Finset.Icc (-2:ℤ) 2)).card :=
          Finset.card_le_card hsub
      _ = 80 := by simp [Finset.card_product]

open Classical in
/-- The `m`-th model block at scale `k` is bounded by the active-index sum. -/
theorem norm_star_powModelQBlock_le_actIdx (d : ℕ) {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ) :
    ‖starRingEnd ℂ (powModelQBlock d m (2^k) θ)‖
      ≤ ∑ p ∈ powActIdx d m k θ, ‖powWeight d p.1.1 p.1.2‖ := by
  rw [star_powModelQBlock_eq_sum d hk θ]
  set Q : ℕ := Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) with hQ
  have h1 : ‖∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2, starRingEnd ℂ (powModelTermArc d q a l k θ)‖
      ≤ ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k then ‖powWeight d q a‖ else 0) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun q hq => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a ha => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l hl => ?_))
    rw [Complex.norm_conj]
    by_cases harc : |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k
    · rw [if_pos harc, powModelTermArc, if_pos harc]
      exact norm_powModelTerm_le_weight d (2^k) q a l θ
    · rw [if_neg harc, pow_modelTermArc_eq_zero_of_not_act d q a l θ harc, norm_zero]
  have h2 : ∑ q ∈ (Finset.Ico (2^m) (2^(m+1))).filter (fun q => q ≤ Q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k then ‖powWeight d q a‖ else 0)
      ≤ ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k then ‖powWeight d q a‖ else 0) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun q hq hnot => ?_)
    positivity
  have h3 : ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
          ∑ l ∈ Finset.Icc (-2:ℤ) 2,
            (if |θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ powArcRad d k then ‖powWeight d q a‖ else 0)
      = ∑ p ∈ powActIdx d m k θ, ‖powWeight d p.1.1 p.1.2‖ := by
    rw [← sum_blockPair m (F := fun (i : ℕ × ℕ) => ∑ l ∈ Finset.Icc (-2:ℤ) 2,
      (if |θ - (i.2:ℝ)/(i.1:ℝ) - (l:ℝ)| ≤ powArcRad d k then ‖powWeight d i.1 i.2‖ else 0))]
    rw [← Finset.sum_product (blockPair m) (Finset.Icc (-2:ℤ) 2)
      (fun p : (ℕ × ℕ) × ℤ => (if |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ powArcRad d k
        then ‖powWeight d p.1.1 p.1.2‖ else 0))]
    rw [powActIdx_eq_filter, allIdx, ← Finset.sum_filter]
  linarith [h1, h2, h3]

open Classical in
/-- The profile error of the `m`-th block at scale `k ≥ 4m+4` is bounded by the active profile
sum. -/
theorem norm_powBlockErr_le_actIdx (d : ℕ) (hd : 2 ≤ d) {m k : ℕ} (hk : 4*m+4 ≤ k) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ‖powBlockErr d m k θ‖ ≤ ∑ p ∈ powActIdx d m k θ, ‖powWeight d p.1.1 p.1.2‖ *
      ‖powProfile d (powDil d k * (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)))
        - (if |powDil d k * (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))| ≤ 1 then (1:ℂ) else 0)‖ := by
  set g : (ℕ × ℕ) × ℤ → ℝ := fun p =>
    ‖powProfile d (powDil d k * (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)))
      - (if |powDil d k * (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ))| ≤ 1 then (1:ℂ) else 0)‖ with hg
  rw [pow_blockErr_eq_sum d hk θ hθ0 hθ1]
  rw [← Finset.sum_product (blockPair m) (Finset.Icc (-2:ℤ) 2)
    (fun p : (ℕ × ℕ) × ℤ =>
      starRingEnd ℂ (powModelTermArc d p.1.1 p.1.2 p.2 k θ - powSharpTerm d p.1.1 p.1.2 p.2 k θ))]
  calc ‖∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
          starRingEnd ℂ (powModelTermArc d p.1.1 p.1.2 p.2 k θ - powSharpTerm d p.1.1 p.1.2 p.2 k θ)‖
      ≤ ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
          (if |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ powArcRad d k
            then ‖powWeight d p.1.1 p.1.2‖ * g p else 0) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p hp => ?_))
        by_cases harc : |θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)| ≤ powArcRad d k
        · rw [if_pos harc, Complex.norm_conj]
          simpa only [hg] using norm_powModelTermArc_sub_sharp_le d hd (k := k) p.1.1 p.1.2 p.2 θ
        · rw [if_neg harc]
          have h1 := pow_modelTermArc_eq_zero_of_not_act d p.1.1 p.1.2 p.2 θ harc
          have h2 := pow_sharpTerm_eq_zero_of_not_act d hd p.1.1 p.1.2 p.2 θ harc
          rw [h1, h2, sub_zero, map_zero, norm_zero]
    _ = ∑ p ∈ powActIdx d m k θ, ‖powWeight d p.1.1 p.1.2‖ * g p := by
        rw [powActIdx_eq_filter, allIdx, ← Finset.sum_filter]

open Classical in
/-- The cap for the weights of the `m`-th block. -/
theorem exists_powWeight_cap (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (i : ℕ × ℕ), i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d) := by
  obtain ⟨A, hApos, hA⟩ := powWeight_cap d hd
  refine ⟨A, hApos, fun m i hi => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hi
  have hq1 : 1 ≤ i.1 := le_trans Nat.one_le_two_pow h1
  have hgcd : Int.gcd (i.2 : ℤ) (i.1 : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]; simp only [Int.natAbs_natCast]; exact_mod_cast h4
  have h := hA i.1 m (i.2 : ℤ) hq1 h1 hgcd
  simpa [powWeight] using h

open Classical in
lemma sum_powWeight_le (d : ℕ) {m k : ℕ} (θ : ℝ) (A : ℝ)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d)) :
    (∑ p ∈ powActIdx d m k θ, ‖powWeight d p.1.1 p.1.2‖)
      ≤ (powActIdx d m k θ).card * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by
  calc ∑ p ∈ powActIdx d m k θ, ‖powWeight d p.1.1 p.1.2‖
      ≤ ∑ _p ∈ powActIdx d m k θ, (A * (2:ℝ)^(-(m:ℝ)*powSig d)) :=
        Finset.sum_le_sum (fun p hp => hA p.1 ((mem_powActIdx.mp hp).1))
    _ = (powActIdx d m k θ).card * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

open Classical in
lemma norm_star_powModelQBlock_le_cap (d : ℕ) (hd : 2 ≤ d) {m k : ℕ} (hk : 4*m ≤ k) (θ : ℝ)
    (A : ℝ)
    (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d)) :
    ‖starRingEnd ℂ (powModelQBlock d m (2^k) θ)‖ ≤ 80 * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by
  have h1 := norm_star_powModelQBlock_le_actIdx d hk θ
  have h2 := sum_powWeight_le d (m := m) (k := k) θ A hA
  have h3 := card_powActIdx_le_eighty d hd hk θ
  have hcap : 0 ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d) := by positivity
  calc ‖starRingEnd ℂ (powModelQBlock d m (2^k) θ)‖
      ≤ ∑ p ∈ powActIdx d m k θ, ‖powWeight d p.1.1 p.1.2‖ := h1
    _ ≤ (powActIdx d m k θ).card * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := h2
    _ ≤ 80 * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by
        apply mul_le_mul_of_nonneg_right _ hcap
        exact_mod_cast h3

/-- For `k < 4m` the `m`-th dyadic block of the model at scale `2^k` is empty. -/
lemma powModelQBlock_eq_zero_of_lt (d : ℕ) {m k : ℕ} (hk : k < 4*m) (θ : ℝ) :
    powModelQBlock d m (2^k) θ = 0 := by
  have hempty : (Finset.Icc 1 (Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)))).filter
      (fun q => Nat.log 2 q = m) = ∅ := by
    rw [filter_log_eq_filter_pow, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqQ⟩, h2m, _⟩ := hq
    have hQ : Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) < 2^m := by
      rw [Nat.floor_lt (by positivity)]
      push_cast
      rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_natCast (2:ℝ) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
      have hk' : (k:ℝ) < 4 * (m:ℝ) := by exact_mod_cast hk
      linarith
    omega
  rw [powModelQBlock, hempty, Finset.sum_empty]

/-! ## The profile-error maximal estimate -/

/-- The profile error of the `m`-th block at a large scale, bounded by the active-index sum. -/
lemma pow_blockErr_enorm_le_tail (d : ℕ) (hd : 2 ≤ d) {m K : ℕ} (hK : 4*m+4 ≤ K) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d)) :
    ‖powBlockErr d m K θ‖ₑ ≤ ∑ p ∈ powActIdx d m (4*m+4) θ,
      ENNReal.ofReal (A * (2:ℝ)^(-(m:ℝ)*powSig d)) * powErrNorm d p.1.1 p.1.2 p.2 K θ := by
  set cap : ℝ := A * (2:ℝ)^(-(m:ℝ)*powSig d) with hcapdef
  have hcap0 : 0 ≤ cap := by rw [hcapdef]; positivity
  have h1 := norm_powBlockErr_le_actIdx d hd hK θ hθ0 hθ1
  have h2 : ‖powBlockErr d m K θ‖
      ≤ ∑ p ∈ powActIdx d m (4*m+4) θ, cap * powErrVal d (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)) K := by
    refine le_trans h1 ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (powActIdx_subset d (by omega) hK) ?_) ?_
    · intro p hp hnp
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · refine Finset.sum_le_sum (fun p hp => ?_)
      exact mul_le_mul_of_nonneg_right (hA p.1 (mem_powActIdx.mp hp).1) (norm_nonneg _)
  calc ‖powBlockErr d m K θ‖ₑ
      = ENNReal.ofReal ‖powBlockErr d m K θ‖ := enorm_eq_ofReal_norm''' _
    _ ≤ ENNReal.ofReal (∑ p ∈ powActIdx d m (4*m+4) θ,
          cap * powErrVal d (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)) K) :=
        ENNReal.ofReal_le_ofReal h2
    _ = ∑ p ∈ powActIdx d m (4*m+4) θ,
          ENNReal.ofReal (cap * powErrVal d (θ - (p.1.2:ℝ)/(p.1.1:ℝ) - (p.2:ℝ)) K) :=
        ENNReal.ofReal_sum_of_nonneg (fun p hp => mul_nonneg hcap0 (norm_nonneg _))
    _ = ∑ p ∈ powActIdx d m (4*m+4) θ,
          ENNReal.ofReal cap * powErrNorm d p.1.1 p.1.2 p.2 K θ := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [powErrNorm, ENNReal.ofReal_mul hcap0]

/-- The profile errors of the `m`-th block form a square-summable family along the scales. -/
theorem pow_blockErr_tsum_sq_le (d : ℕ) (hd : 2 ≤ d) (A Cf : ℝ) (hA0 : 0 < A) (hCf0 : 0 < Cf)
    (hA : ∀ (m : ℕ) (i : ℕ × ℕ), i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d))
    (hCf : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, powErrVal d x k) ≤ Cf)
    (m : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑' K : ℕ, ‖powBlockErr d m K θ‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal ((A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d)) ^ 2) := by
  set cap : ℝ := A * (2:ℝ)^(-(m:ℝ)*powSig d) with hcapdef
  have hcap0 : 0 ≤ cap := by rw [hcapdef]; positivity
  set D : ℝ := A * (160 + Cf) with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun s => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun K => 4*m+4 ≤ K)]
  have hsmall : (∑ K ∈ s.filter (fun K => ¬ 4*m+4 ≤ K), ‖powBlockErr d m K θ‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal ((160*cap)^2) := by
    set t : Finset ℕ := s.filter (fun K => ¬ 4*m+4 ≤ K) with ht
    have hstep : ∀ K ∈ t, ‖powBlockErr d m K θ‖ₑ ^ (2:ℝ)
        ≤ (if 4*m ≤ K then (ENNReal.ofReal (80*cap))^2 else 0) := by
      intro K hK
      have hKlt : K < 4*m+4 := by
        rw [ht, Finset.mem_filter] at hK
        omega
      rw [ENNReal.rpow_two]
      by_cases hK4 : 4*m ≤ K
      · rw [if_pos hK4, enorm_eq_ofReal_norm''']
        have hb : ‖powBlockErr d m K θ‖ ≤ 80*cap := by
          rw [powBlockErr, if_neg (by omega : ¬ 4*m+4 ≤ K), sub_zero, hcapdef]
          exact norm_star_powModelQBlock_le_cap d hd hK4 θ A (le_of_lt hA0) (hA m)
        exact pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal hb) 2
      · rw [if_neg hK4]
        have hz : ‖powBlockErr d m K θ‖ = 0 := by
          rw [powBlockErr, if_neg (by omega : ¬ 4*m+4 ≤ K), sub_zero,
            powModelQBlock_eq_zero_of_lt d (by omega : K < 4*m), map_zero, norm_zero]
        rw [enorm_eq_ofReal_norm''', hz]
        simp
    have hsub2 : t.filter (fun K => 4*m ≤ K) ⊆ Finset.Ico (4*m) (4*m+4) := by
      intro K hK
      rw [Finset.mem_filter] at hK
      rw [ht, Finset.mem_filter] at hK
      rw [Finset.mem_Ico]
      omega
    have hcard : (t.filter (fun K => 4*m ≤ K)).card ≤ 4 := by
      calc (t.filter (fun K => 4*m ≤ K)).card ≤ (Finset.Ico (4*m) (4*m+4)).card :=
            Finset.card_le_card hsub2
        _ = 4 := by simp
    calc ∑ K ∈ t, ‖powBlockErr d m K θ‖ₑ ^ (2:ℝ)
        ≤ ∑ K ∈ t, (if 4*m ≤ K then (ENNReal.ofReal (80*cap))^2 else 0) :=
          Finset.sum_le_sum hstep
      _ = ∑ K ∈ t.filter (fun K => 4*m ≤ K), (ENNReal.ofReal (80*cap))^2 := by
          rw [← Finset.sum_filter]
      _ = ((t.filter (fun K => 4*m ≤ K)).card : ℝ≥0∞) * (ENNReal.ofReal (80*cap))^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4:ℝ≥0∞) * (ENNReal.ofReal (80*cap))^2 := by
          gcongr
          exact_mod_cast hcard
      _ = ENNReal.ofReal ((160*cap)^2) := by
          rw [← ENNReal.ofReal_pow (mul_nonneg (by norm_num) hcap0)]
          have h4 : (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) := by norm_num
          rw [h4, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
          congr 1
          ring
  have htail : (∑ K ∈ s.filter (fun K => 4*m+4 ≤ K), ‖powBlockErr d m K θ‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal ((A * Cf * (2:ℝ)^(-(m:ℝ)*powSig d))^2) := by
    set t : Finset ℕ := s.filter (fun K => 4*m+4 ≤ K) with ht
    have hstep : ∀ K ∈ t, ‖powBlockErr d m K θ‖ₑ ^ (2:ℝ)
        ≤ (∑ p ∈ powActIdx d m (4*m+4) θ,
            ENNReal.ofReal cap * powErrNorm d p.1.1 p.1.2 p.2 K θ)^2 := by
      intro K hK
      have hK4 : 4*m+4 ≤ K := by
        rw [ht, Finset.mem_filter] at hK
        exact hK.2
      rw [ENNReal.rpow_two]
      exact pow_le_pow_left₀ (by positivity)
        (pow_blockErr_enorm_le_tail d hd hK4 θ hθ0 hθ1 A (le_of_lt hA0) (hA m)) 2
    calc ∑ K ∈ t, ‖powBlockErr d m K θ‖ₑ ^ (2:ℝ)
        ≤ ∑ K ∈ t, (∑ p ∈ powActIdx d m (4*m+4) θ,
            ENNReal.ofReal cap * powErrNorm d p.1.1 p.1.2 p.2 K θ)^2 := Finset.sum_le_sum hstep
      _ ≤ ∑' K : ℕ, (∑ p ∈ powActIdx d m (4*m+4) θ,
            ENNReal.ofReal cap * powErrNorm d p.1.1 p.1.2 p.2 K θ)^2 := ENNReal.sum_le_tsum _
      _ = ∑' K : ℕ, ∑ p ∈ powActIdx d m (4*m+4) θ,
            (ENNReal.ofReal cap * powErrNorm d p.1.1 p.1.2 p.2 K θ)^2 := by
          refine tsum_congr (fun K => ?_)
          rw [sq_sum_eq_of_card_le_one
            (powActIdx_card_le_one d hd (m := m) (k := 4*m+4) (by omega) θ)]
      _ = ∑ p ∈ powActIdx d m (4*m+4) θ, ∑' K : ℕ,
            (ENNReal.ofReal cap * powErrNorm d p.1.1 p.1.2 p.2 K θ)^2 := ennreal_tsum_finsetSum _ _
      _ = ∑ p ∈ powActIdx d m (4*m+4) θ, (ENNReal.ofReal cap)^2 *
            ∑' K : ℕ, (powErrNorm d p.1.1 p.1.2 p.2 K θ)^2 := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr (fun K => by rw [mul_pow])
      _ ≤ ∑ p ∈ powActIdx d m (4*m+4) θ, (ENNReal.ofReal cap)^2 *
            (∑' K : ℕ, powErrNorm d p.1.1 p.1.2 p.2 K θ)^2 := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          exact mul_le_mul_right sq_le_tsum_sq _
      _ ≤ (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := by
          have hcard : (powActIdx d m (4*m+4) θ).card ≤ 1 :=
            powActIdx_card_le_one d hd (by omega) θ
          calc ∑ p ∈ powActIdx d m (4*m+4) θ, (ENNReal.ofReal cap)^2 *
                (∑' K : ℕ, powErrNorm d p.1.1 p.1.2 p.2 K θ)^2
              ≤ ∑ _p ∈ powActIdx d m (4*m+4) θ,
                  (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := by
                refine Finset.sum_le_sum (fun p hp => ?_)
                exact mul_le_mul_right (pow_le_pow_left₀ (by positivity)
                  (powErrNorm_tsum_le d hd (le_of_lt hCf0) hCf p.1.1 p.1.2 p.2 θ) 2) _
            _ = ((powActIdx d m (4*m+4) θ).card : ℝ≥0∞) *
                  ((ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 1 * ((ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2) := by
                gcongr
                exact_mod_cast hcard
            _ = (ENNReal.ofReal cap)^2 * (ENNReal.ofReal Cf)^2 := one_mul _
      _ = ENNReal.ofReal ((A * Cf * (2:ℝ)^(-(m:ℝ)*powSig d))^2) := by
          rw [hcapdef, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine le_trans (add_le_add htail hsmall) ?_
  calc ENNReal.ofReal ((A * Cf * (2:ℝ)^(-(m:ℝ)*powSig d))^2) + ENNReal.ofReal ((160*cap)^2)
      = ENNReal.ofReal ((A * Cf * (2:ℝ)^(-(m:ℝ)*powSig d))^2 + (160*cap)^2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((D * (2:ℝ)^(-(m:ℝ)*powSig d))^2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcapdef, hDdef]
        have hs : (0:ℝ) ≤ (2:ℝ)^(-(m:ℝ)*powSig d) := Real.rpow_nonneg (by norm_num) _
        nlinarith [sq_nonneg (A * (2:ℝ)^(-(m:ℝ)*powSig d)), sq_nonneg ((2:ℝ)^(-(m:ℝ)*powSig d)),
          sq_nonneg (Cf * (2:ℝ)^(-(m:ℝ)*powSig d)), le_of_lt hA0, le_of_lt hCf0, hs]


/-! ## The weighted core and the per-block maximal estimate -/

/-- The profile error of the `m`-th block, as a multiplier on `(0,1)` (extended by `0`). -/
noncomputable def powErrMult (d : ℕ) (m K : ℕ) (θ : ℝ) : ℂ :=
  if 0 < θ ∧ θ < 1 then powBlockErr d m K θ else 0

lemma measurable_powBlockCore (d : ℕ) (m k : ℕ) :
    Measurable (fun θ : ℝ => powBlockCore d m k θ) := by
  unfold powBlockCore
  refine Finset.measurable_sum _ (fun i hi => ?_)
  refine Finset.measurable_sum _ (fun l hl => ?_)
  refine Measurable.mul measurable_const ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (by fun_prop) measurable_const

lemma measurable_powBlockErr (d : ℕ) (m K : ℕ) :
    Measurable (fun θ : ℝ => powBlockErr d m K θ) := by
  unfold powBlockErr
  refine Measurable.sub ?_ ?_
  · exact Complex.continuous_conj.measurable.comp (measurable_powModelQBlock d m (2^K))
  · by_cases h4 : 4*m+4 ≤ K
    · simpa [h4] using measurable_powBlockCore d m K
    · simpa [h4] using measurable_const (a := (0:ℂ))

lemma measurable_powErrMult (d : ℕ) (m K : ℕ) :
    Measurable (powErrMult d m K) := by
  unfold powErrMult
  refine Measurable.ite (by measurability) ?_ measurable_const
  exact measurable_powBlockErr d m K

lemma powErrMult_hsum (d : ℕ) (hd : 2 ≤ d) (A Cf : ℝ) (hA0 : 0 < A) (hCf0 : 0 < Cf)
    (hA : ∀ (m : ℕ) (i : ℕ × ℕ), i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d))
    (hCf : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, powErrVal d x k) ≤ Cf)
    (m : ℕ) (θ : ℝ) :
    Summable (fun K : ℕ => ‖powErrMult d m K θ‖ ^ 2) ∧
      (∑' K : ℕ, ‖powErrMult d m K θ‖ ^ 2)
        ≤ (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d))^2 := by
  by_cases hθ : 0 < θ ∧ θ < 1
  · have hmain := pow_blockErr_tsum_sq_le d hd A Cf hA0 hCf0 hA hCf m θ hθ.1 hθ.2
    have hE0 : (0:ℝ) ≤ (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d))^2 := by positivity
    have hfin : ∀ t : Finset ℕ,
        ∑ K ∈ t, ‖powBlockErr d m K θ‖ ^ 2
          ≤ (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d))^2 := by
      intro t
      have h1 : ∑ K ∈ t, ‖powBlockErr d m K θ‖ₑ ^ (2:ℝ)
          ≤ ENNReal.ofReal ((A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d))^2) :=
        le_trans (ENNReal.sum_le_tsum t) hmain
      rw [Finset.sum_congr rfl (fun K hK =>
        Commons.Analysis.Fourier.enorm_complex_pow_two (powBlockErr d m K θ))] at h1
      rw [← ENNReal.ofReal_sum_of_nonneg (fun K hK => sq_nonneg _)] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hE0).mp h1
    have heq : ∀ K, powErrMult d m K θ = powBlockErr d m K θ := fun K => by
      rw [powErrMult, if_pos hθ]
    constructor
    · simpa only [heq] using summable_of_sum_range_le (fun K => sq_nonneg _)
        (fun n => by simpa using hfin (Finset.range n))
    · simpa only [heq] using Real.tsum_le_of_sum_range_le (fun K => sq_nonneg _)
        (fun n => by simpa using hfin (Finset.range n))
  · have hz : ∀ K, powErrMult d m K θ = 0 := fun K => by rw [powErrMult, if_neg hθ]
    constructor
    · simpa [hz] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
    · have hz' : (∑' K : ℕ, ‖powErrMult d m K θ‖ ^ 2) = 0 := by
        rw [show (fun K : ℕ => ‖powErrMult d m K θ‖ ^ 2) = fun _ : ℕ => (0:ℝ) from
          funext (fun K => by rw [hz K]; norm_num)]
        rw [tsum_zero]
      rw [hz']
      exact sq_nonneg _

lemma norm_powBlockCore_le (d : ℕ) (m k : ℕ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d)) (θ : ℝ) :
    ‖powBlockCore d m k θ‖ ≤ ((allIdx m).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by
  rw [powBlockCore_eq_sum_sharpTerm]
  rw [show (∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-2:ℤ) 2,
        starRingEnd ℂ (powSharpTerm d i.1 i.2 l k θ))
      = ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
        starRingEnd ℂ (powSharpTerm d p.1.1 p.1.2 p.2 k θ) from
    (Finset.sum_product (blockPair m) (Finset.Icc (-2:ℤ) 2)
      (fun p : (ℕ × ℕ) × ℤ => starRingEnd ℂ (powSharpTerm d p.1.1 p.1.2 p.2 k θ))).symm]
  calc ‖∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
        starRingEnd ℂ (powSharpTerm d p.1.1 p.1.2 p.2 k θ)‖
      ≤ ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
          ‖starRingEnd ℂ (powSharpTerm d p.1.1 p.1.2 p.2 k θ)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2, ‖powWeight d p.1.1 p.1.2‖ := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp1 : p.1 ∈ blockPair m := (Finset.mem_product.mp hp).1
        rw [Complex.norm_conj, powSharpTerm, norm_mul]
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        split_ifs <;> simp
    _ ≤ ((allIdx m).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by
        rw [allIdx]
        calc ∑ p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2, ‖powWeight d p.1.1 p.1.2‖
            ≤ ∑ _p ∈ blockPair m ×ˢ Finset.Icc (-2:ℤ) 2,
                (A * (2:ℝ)^(-(m:ℝ)*powSig d)) :=
              Finset.sum_le_sum (fun p hp => hA p.1 (Finset.mem_product.mp hp).1)
          _ = ((blockPair m ×ˢ Finset.Icc (-2:ℤ) 2).card : ℝ) *
                (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by
              rw [Finset.sum_const, nsmul_eq_mul]

lemma norm_powBlockErr_le_generic (d : ℕ) (hd : 2 ≤ d) {m K : ℕ} (hk : 4*m ≤ K) (θ : ℝ)
    (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d)) :
    ‖powBlockErr d m K θ‖
      ≤ (80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by
  have hc : 0 ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d) := by positivity
  have hcard : (0:ℝ) ≤ ((allIdx m).card : ℝ) := by positivity
  rw [powBlockErr]
  by_cases h4 : 4*m+4 ≤ K
  · rw [if_pos h4]
    refine le_trans (norm_sub_le _ _) ?_
    calc ‖starRingEnd ℂ (powModelQBlock d m (2^K) θ)‖ + ‖powBlockCore d m K θ‖
        ≤ 80 * (A * (2:ℝ)^(-(m:ℝ)*powSig d))
            + ((allIdx m).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) :=
          add_le_add (norm_star_powModelQBlock_le_cap d hd hk θ A hA0 hA)
            (norm_powBlockCore_le d m K A hA0 hA θ)
      _ = (80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) := by ring
  · rw [if_neg h4, sub_zero]
    refine le_trans (norm_star_powModelQBlock_le_cap d hd hk θ A hA0 hA) ?_
    calc 80 * (A * (2:ℝ)^(-(m:ℝ)*powSig d))
        ≤ (80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) :=
          mul_le_mul_of_nonneg_right (by linarith) hc

/-- The profile errors of the `m`-th dyadic block are an `ℓ²` maximal family. -/
theorem powErrMult_maximal_le (d : ℕ) (hd : 2 ≤ d) (A Cf : ℝ) (hA0 : 0 < A) (hCf0 : 0 < Cf)
    (hA : ∀ (m : ℕ) (i : ℕ × ℕ), i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d))
    (hCf : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, powErrVal d x k) ≤ Cf)
    (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ) (hgs : ∀ n, n ∉ s → g n = 0) :
    ∫⁻ x : ℤ, (⨆ K : ℕ, ‖∫ θ in (0:ℝ)..1, powErrMult d m K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d))^2) *
        ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  set E : ℝ := A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d) with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hbound : ∀ K : ℕ, ∃ C : ℝ, ∀ θ : ℝ, ‖powErrMult d m K θ‖ ≤ C := by
    intro K
    by_cases hk : 4*m ≤ K
    · refine ⟨(80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)*powSig d)), fun θ => ?_⟩
      by_cases hθ : 0 < θ ∧ θ < 1
      · rw [powErrMult, if_pos hθ]
        exact norm_powBlockErr_le_generic d hd hk θ A (le_of_lt hA0) (hA m)
      · rw [powErrMult, if_neg hθ, norm_zero]; positivity
    · refine ⟨1, fun θ => ?_⟩
      by_cases hθ : 0 < θ ∧ θ < 1
      · rw [powErrMult, if_pos hθ, powBlockErr, if_neg (by omega : ¬ 4*m+4 ≤ K), sub_zero,
          powModelQBlock_eq_zero_of_lt d (by omega : K < 4*m), map_zero, norm_zero]
        norm_num
      · rw [powErrMult, if_neg hθ, norm_zero]; norm_num
  have hsum : ∀ θ, Summable (fun K : ℕ => ‖powErrMult d m K θ‖ ^ 2) ∧
      ∑' K : ℕ, ‖powErrMult d m K θ‖ ^ 2 ≤ E ^ 2 := fun θ => by
    rw [hEdef]; exact powErrMult_hsum d hd A Cf hA0 hCf0 hA hCf m θ
  have hsquare := multiplier_square_function_l2' (fun K => powErrMult d m K) E
    (fun K => measurable_powErrMult d m K) hbound hsum g s hgs
  rw [hEdef] at hsquare ⊢
  calc ∫⁻ x : ℤ, (⨆ K : ℕ, ‖∫ θ in (0:ℝ)..1, powErrMult d m K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, 2 * ∑' K : ℕ, ‖∫ θ in (0:ℝ)..1, powErrMult d m K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => by
          simp only [ENNReal.rpow_two]
          exact sq_iSup_le_two_tsum_sq)
    _ = 2 * ∫⁻ x : ℤ, ∑' K : ℕ, ‖∫ θ in (0:ℝ)..1, powErrMult d m K θ *
        (∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
        * Complex.exp (-(2*Real.pi*Complex.I*(x:ℂ)*(θ:ℂ)))‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        lintegral_const_mul' 2 _ (by norm_num)
    _ ≤ 2 * (ENNReal.ofReal ((A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d))^2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :=
        mul_le_mul_right hsquare 2
    _ = ENNReal.ofReal (2 * (A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d))^2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        have h2 : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
        rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

lemma norm_powErrMult_le {d m k : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ θ, ‖powBlockErr d m k θ‖ ≤ B) (θ : ℝ) : ‖powErrMult d m k θ‖ ≤ B := by
  by_cases hθ : 0 < θ ∧ θ < 1
  · rw [powErrMult, if_pos hθ]; exact hB θ
  · rw [powErrMult, if_neg hθ, norm_zero]; exact hB0

/-- A uniform bound on the block error (crude, for integrability). -/
lemma norm_powBlockErr_le_const (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i : ℕ × ℕ, i ∈ blockPair m →
      ‖powWeight d i.1 i.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (k : ℕ) (θ : ℝ), ‖powBlockErr d m k θ‖ ≤ B := by
  refine ⟨max 1 ((80 + ((allIdx m).card : ℝ)) * (A * (2:ℝ)^(-(m:ℝ)*powSig d))), ?_, fun k θ => ?_⟩
  · exact le_trans zero_le_one (le_max_left _ _)
  · by_cases hk : 4*m ≤ k
    · exact le_trans (norm_powBlockErr_le_generic d hd hk θ A hA0 hA) (le_max_right _ _)
    · have hz : powBlockErr d m k θ = 0 := by
        rw [powBlockErr, if_neg (by omega : ¬ 4*m+4 ≤ k), sub_zero,
          powModelQBlock_eq_zero_of_lt d (by omega : k < 4*m), map_zero]
      rw [hz, norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)

lemma powBlockT_injOn (d m : ℕ) :
    ∀ i ∈ blockPair m, ∀ i' ∈ blockPair m,
      ((i.2:ℝ)/(i.1:ℝ), starRingEnd ℂ (powWeight d i.1 i.2))
        = ((i'.2:ℝ)/(i'.1:ℝ), starRingEnd ℂ (powWeight d i'.1 i'.2)) → i = i' := by
  intro i hi i' hi' heq
  obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hi
  obtain ⟨h1', h2', h3', h4'⟩ := mem_blockPair.mp hi'
  have hfr : (i.2:ℝ)/(i.1:ℝ) = (i'.2:ℝ)/(i'.1:ℝ) := congrArg Prod.fst heq
  have hq1 : 0 < i.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1
  have hq2 : 0 < i'.1 := lt_of_lt_of_le (Nat.two_pow_pos m) h1'
  obtain ⟨hqeq, haeq⟩ := frac_eq_of_coprime hq1 hq2
    (Nat.coprime_iff_gcd_eq_one.mpr h4) (Nat.coprime_iff_gcd_eq_one.mpr h4') h3 h3' hfr
  exact Prod.ext hqeq haeq

lemma powBlockCore_eq_weighted (d : ℕ) (hd : 2 ≤ d) {m k : ℕ} (hk : 1 ≤ k) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    powBlockCore d m k θ = ∑ p ∈ powBlockT d m, p.2 * perNbhd p.1 ((powDil d k)⁻¹) θ := by
  rw [powBlockCore_eq_periodic d hd m k hk θ hθ0 hθ1, powBlockCorePer, powBlockT]
  rw [Finset.sum_image (powBlockT_injOn d m)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [perNbhd]

/-- **The per-`q`-block maximal estimate for the `d`-th power model.** -/
theorem pow_block_maximal_of_circle (d : ℕ) (hd : 2 ≤ d) (H : CircleNeighborhoodMaximal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2)^2 *
          ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨Cwγ, hCwγpos, hCwγ⟩ := weighted_core_maximal H
  obtain ⟨A, hApos, hgauss⟩ := exists_powWeight_cap d hd
  obtain ⟨Cf, hCfpos, hCf0⟩ := powProfile_replace_sharp_tsum_le d hd
  have hCf' : ∀ x : ℝ, x ≠ 0 → (∑' k : ℕ, powErrVal d x k) ≤ Cf := by
    intro x hx
    refine le_trans (le_of_eq ?_) (hCf0 x hx)
    refine tsum_congr (fun k => ?_)
    rw [powErrVal]
  refine ⟨2 * (4 * Cwγ * A + 2 * A * (160 + Cf)), by positivity, fun m g s hgs => ?_⟩
  set P : ℝ → ℂ := fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))
    with hPdef
  have hPcont : Continuous P := by
    rw [hPdef]
    refine continuous_finsetSum _ (fun n hn => ?_)
    fun_prop
  have hPm : Measurable P := hPcont.measurable
  have hPbd : ∀ θ, ‖P θ‖ ≤ ∑ n ∈ s, ‖g n‖ := by
    intro θ
    rw [hPdef]
    calc ‖∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖
        ≤ ∑ n ∈ s, ‖g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ := norm_sum_le _ _
      _ = ∑ n ∈ s, ‖g n‖ := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rw [norm_mul]
          have : ‖Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ = 1 := by
            rw [show 2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)
                  = (((2*Real.pi*(n:ℝ)*θ : ℝ)) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]
          rw [this, mul_one]
  set Ef : ℤ → ℝ → ℂ := fun x θ => Complex.exp (-(2*Real.pi*Complex.I*((x:ℤ):ℂ)*(θ:ℂ))) with hEf
  set CoreFam : ℕ → ℤ → ℂ := fun j x => ∫ θ in (0:ℝ)..1,
      (if d*(4*m+4)-1 ≤ j then ∑ p ∈ powBlockT d m, p.2 * perNbhd p.1 ((2:ℝ)^(-(j:ℝ)-1)) θ else 0) *
        P θ * Ef x θ with hCoreFam
  set ErrFam : ℕ → ℤ → ℂ := fun K x => ∫ θ in (0:ℝ)..1, powErrMult d m K θ * P θ * Ef x θ
    with hErrFam
  have hcap0 : 0 ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d) := by positivity
  have hcap : ∀ p ∈ powBlockT d m, ‖p.2‖ ≤ A * (2:ℝ)^(-(m:ℝ)*powSig d) := by
    intro p hp
    rw [mem_powBlockT] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [Complex.norm_conj]
    exact hgauss m i hi
  -- the core bound
  have hj₀δ : (2:ℝ)^(-(((d*(4*m+4)-1 : ℕ)):ℝ)-1) ≤ (4:ℝ)^(-(m:ℝ)-1)/3 := by
    have hcast : (((d*(4*m+4)-1 : ℕ)):ℝ) = (d*(4*m+4) : ℝ) - 1 := by
      rw [Nat.cast_sub (by nlinarith [hd] : 1 ≤ d*(4*m+4))]; push_cast; ring
    rw [hcast]
    have h1 : (2:ℝ)^(-((d*(4*m+4) : ℝ) - 1) - 1) = (2:ℝ)^(-(d*(4*m+4) : ℝ)) := by
      congr 1; ring
    rw [h1]
    have h4 : (4:ℝ)^(-(m:ℝ)-1) = (2:ℝ)^(-2*((m:ℝ)+1)) := by
      rw [show (4:ℝ) = (2:ℝ)^(2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1; ring
    rw [h4]
    have hexp : -(d*(4*m+4) : ℝ) ≤ -2*((m:ℝ)+1) - 2 := by
      have hd' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      push_cast
      nlinarith
    calc (2:ℝ)^(-(d*(4*m+4) : ℝ)) ≤ (2:ℝ)^(-2*((m:ℝ)+1)-2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (2:ℝ)^(-2*((m:ℝ)+1)) / 4 := by
          rw [show -2*((m:ℝ)+1)-2 = (-2*((m:ℝ)+1)) + (-2) by ring,
            Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          rw [show (2:ℝ)^(-2:ℝ) = 1/4 by norm_num]
          ring
      _ ≤ (2:ℝ)^(-2*((m:ℝ)+1)) / 3 := by
          have hp : (0:ℝ) < (2:ℝ)^(-2*((m:ℝ)+1)) := Real.rpow_pos_of_pos (by norm_num) _
          linarith
  have hcore_raw := hCwγ (powBlockT d m) (A * (2:ℝ)^(-(m:ℝ)*powSig d)) ((4:ℝ)^(-(m:ℝ)-1))
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 4) _) hcap0 hcap (powBlockT_sep d m)
    (d*(4*m+4)-1) (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hj₀δ g s hgs
  have hlognn : 0 ≤ Real.log (((powBlockT d m).card:ℝ)+2) := by
    refine Real.log_nonneg ?_
    have h : (0:ℝ) ≤ ((powBlockT d m).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hlog2 : Real.log (((powBlockT d m).card:ℝ)+2)^2 ≤ (2*((m:ℝ)+2))^2 := by
    have h := log_powBlockT_le d m
    have h2 : (0:ℝ) ≤ 2*((m:ℝ)+2) := by positivity
    nlinarith [h, hlognn]
  have hcore : ∫⁻ x : ℤ, (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((4 * Cwγ * A * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2)^2) *
        ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
    refine le_trans hcore_raw ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have hp1 : (0:ℝ) ≤ Cwγ * (A * (2:ℝ)^(-(m:ℝ)*powSig d))
        * Real.log (((powBlockT d m).card:ℝ)+2)^2 := by positivity
    have hp2 : (0:ℝ) ≤ (4 * Cwγ * A * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2) := by positivity
    calc (Cwγ * (A * (2:ℝ)^(-(m:ℝ)*powSig d))
          * Real.log (((powBlockT d m).card:ℝ)+2)^2)^2
        ≤ (Cwγ * (A * (2:ℝ)^(-(m:ℝ)*powSig d)) * (2*((m:ℝ)+2))^2)^2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = (4 * Cwγ * A * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2)^2 := by ring
  -- the error bound
  have herr_raw := powErrMult_maximal_le d hd A Cf hApos hCfpos hgauss hCf' m g s hgs
  have herr : ∫⁻ x : ℤ, (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((2 * A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d))^2) *
        ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
    refine le_trans herr_raw ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have hp : (0:ℝ) ≤ A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d) := by positivity
    nlinarith [hp]
  -- a uniform bound for the error, for integrability
  obtain ⟨B, hB0, hB⟩ := norm_powBlockErr_le_const d hd m A hApos.le (hgauss m)
  -- integrability of the two pieces
  have hint_core : ∀ k x, IntervalIntegrable (fun θ =>
      (if 4*m+4 ≤ k then powBlockCore d m k θ else 0) * P θ * Ef x θ) volume 0 1 := by
    intro k x
    refine intervalIntegrable_mul_exp (f := fun θ => (if 4*m+4 ≤ k then powBlockCore d m k θ else 0))
      (P := P) (Cf := ((allIdx m).card : ℝ) * (A * (2:ℝ)^(-(m:ℝ)*powSig d)))
      (CP := ∑ n ∈ s, ‖g n‖) ?_ hPm ?_ hPbd x
    · by_cases hk : 4*m+4 ≤ k
      · simpa [hk] using measurable_powBlockCore d m k
      · simpa [hk] using measurable_const (a := (0:ℂ))
    · intro θ
      by_cases hk : 4*m+4 ≤ k
      · rw [if_pos hk]
        exact norm_powBlockCore_le d m k A hApos.le (hgauss m) θ
      · rw [if_neg hk, norm_zero]
        positivity
  have hint_err : ∀ k x, IntervalIntegrable (fun θ =>
      powErrMult d m k θ * P θ * Ef x θ) volume 0 1 :=
    fun k x => intervalIntegrable_mul_exp (f := fun θ => powErrMult d m k θ) (P := P)
      (Cf := B) (CP := ∑ n ∈ s, ‖g n‖) (measurable_powErrMult d m k) hPm
      (fun θ => norm_powErrMult_le hB0 (hB k) θ) hPbd x
  -- the decomposition of the block operator
  have hCore_eq : ∀ (k : ℕ) (x : ℤ),
      (∫ θ in (0:ℝ)..1, (if 4*m+4 ≤ k then powBlockCore d m k θ else 0) * P θ * Ef x θ)
        = CoreFam (d*k-1) x := by
    intro k x
    rw [hCoreFam]
    refine intervalIntegral_eq_of_eq_Ioo (fun θ hθ0 hθ1 => ?_)
    by_cases hk : 4*m+4 ≤ k
    · have h2k : d*(4*m+4)-1 ≤ d*k-1 := by
        have hle : d*(4*m+4) ≤ d*k := Nat.mul_le_mul_left d hk
        omega
      rw [if_pos hk, if_pos h2k]
      have hrad : (2:ℝ)^(-(((d*k-1 : ℕ)):ℝ)-1) = (powDil d k)⁻¹ := by
        have h1dk : 1 ≤ d*k := by
          have h := Nat.mul_le_mul hd hk
          omega
        have hcast : (((d*k-1 : ℕ)):ℝ) = (d*k : ℝ) - 1 := by
          rw [Nat.cast_sub h1dk]; push_cast; ring
        have h2 : -(((d*k-1 : ℕ)):ℝ)-1 = -(((d*k : ℕ)) : ℝ) := by
          rw [hcast]; push_cast; ring
        rw [h2, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast (2:ℝ) (d*k)]
        congr 1
        rw [powDil, ← pow_mul, Nat.mul_comm]
      rw [powBlockCore_eq_weighted d hd (by omega : 1 ≤ k) θ hθ0 hθ1, hrad]
    · have h2k : ¬ (d*(4*m+4)-1 ≤ d*k-1) := by
        intro hc
        have hlt : d*k < d*(4*m+4) :=
          Nat.mul_lt_mul_of_pos_left (not_le.mp hk) (by omega : 0 < d)
        have h2 : d*k - 1 < d*(4*m+4) - 1 := by
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            have hd4 : 2 ≤ d*(4*m+4) := by
              have hmul : 2 * (4*m+4) ≤ d*(4*m+4) := Nat.mul_le_mul_right _ hd
              omega
            omega
          · exact Nat.sub_lt_sub_right (by
              have := Nat.mul_le_mul hd hkpos
              omega : 1 ≤ d*k) hlt
        omega
      rw [if_neg hk, if_neg h2k, zero_mul, zero_mul]
  have hErr_eq : ∀ (K : ℕ) (x : ℤ),
      (∫ θ in (0:ℝ)..1, powBlockErr d m K θ * P θ * Ef x θ) = ErrFam K x := by
    intro K x
    rw [hErrFam]
    refine intervalIntegral_eq_of_eq_Ioo (fun θ hθ0 hθ1 => ?_)
    rw [powErrMult, if_pos ⟨hθ0, hθ1⟩]
  have hint_err' : ∀ k x, IntervalIntegrable (fun θ =>
      powBlockErr d m k θ * P θ * Ef x θ) volume 0 1 :=
    fun k x => intervalIntegrable_mul_exp (f := fun θ => powBlockErr d m k θ) (P := P)
      (Cf := B) (CP := ∑ n ∈ s, ‖g n‖) (measurable_powBlockErr d m k) hPm
      (fun θ => hB k θ) hPbd x
  have hTk_eq : ∀ (k : ℕ) (x : ℤ), powTkBlockMax d g s m k x
      = (∫ θ in (0:ℝ)..1, (if 4*m+4 ≤ k then powBlockCore d m k θ else 0) * P θ * Ef x θ)
        + ErrFam k x := by
    intro k x
    rw [powTkBlockMax]
    have h1 : (∫ θ in (0:ℝ)..1, starRingEnd ℂ (powModelQBlock d m (2^k) θ) * P θ * Ef x θ)
        = ∫ θ in (0:ℝ)..1, (((if 4*m+4 ≤ k then powBlockCore d m k θ else 0) * P θ * Ef x θ)
            + (powBlockErr d m k θ * P θ * Ef x θ)) := by
      refine intervalIntegral.integral_congr (fun θ hθ => ?_)
      have h2 : starRingEnd ℂ (powModelQBlock d m (2^k) θ)
          = (if 4*m+4 ≤ k then powBlockCore d m k θ else 0) + powBlockErr d m k θ := by
        rw [powBlockErr, add_sub_cancel]
      rw [h2]
      ring
    rw [h1, intervalIntegral.integral_add (hint_core k x) (hint_err' k x), hErr_eq k x]
  have hdec : ∀ (k : ℕ) (x : ℤ), ‖powTkBlockMax d g s m k x‖ₑ
      ≤ ‖CoreFam (d*k-1) x‖ₑ + ‖ErrFam k x‖ₑ := by
    intro k x
    rw [hTk_eq k x]
    calc ‖(∫ θ in (0:ℝ)..1, (if 4*m+4 ≤ k then powBlockCore d m k θ else 0) * P θ * Ef x θ)
          + ErrFam k x‖ₑ
        ≤ ‖(∫ θ in (0:ℝ)..1, (if 4*m+4 ≤ k then powBlockCore d m k θ else 0) * P θ * Ef x θ)‖ₑ
          + ‖ErrFam k x‖ₑ := by
          rw [enorm_eq_ofReal_norm''', enorm_eq_ofReal_norm''', enorm_eq_ofReal_norm''',
            ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ = ‖CoreFam (d*k-1) x‖ₑ + ‖ErrFam k x‖ₑ := by rw [hCore_eq k x]
  have hsup : ∀ x : ℤ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ)^(2:ℝ)
      ≤ 2 * (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ)
        + 2 * (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ) := by
    intro x
    have h1 : (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ) ≤
        (⨆ j : ℕ, ‖CoreFam j x‖ₑ) + (⨆ K : ℕ, ‖ErrFam K x‖ₑ) :=
      iSup_le (fun k => le_trans (hdec k x) (add_le_add
        (le_iSup (fun j => ‖CoreFam j x‖ₑ) (d*k-1))
        (le_iSup (fun K => ‖ErrFam K x‖ₑ) k)))
    rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two]
    calc (⨆ k, ‖powTkBlockMax d g s m k x‖ₑ)^2
        ≤ ((⨆ j, ‖CoreFam j x‖ₑ) + (⨆ K, ‖ErrFam K x‖ₑ))^2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = (⨆ j, ‖CoreFam j x‖ₑ)^2 + 2*((⨆ j, ‖CoreFam j x‖ₑ)*(⨆ K, ‖ErrFam K x‖ₑ))
          + (⨆ K, ‖ErrFam K x‖ₑ)^2 := by ring
      _ ≤ (⨆ j, ‖CoreFam j x‖ₑ)^2 + ((⨆ j, ‖CoreFam j x‖ₑ)^2 + (⨆ K, ‖ErrFam K x‖ₑ)^2)
          + (⨆ K, ‖ErrFam K x‖ₑ)^2 := by
          refine add_le_add (add_le_add le_rfl ?_) le_rfl
          calc 2*((⨆ j, ‖CoreFam j x‖ₑ)*(⨆ K, ‖ErrFam K x‖ₑ))
              = 2 * (⨆ j, ‖CoreFam j x‖ₑ) * (⨆ K, ‖ErrFam K x‖ₑ) := by ring
            _ ≤ (⨆ j, ‖CoreFam j x‖ₑ)^2 + (⨆ K, ‖ErrFam K x‖ₑ)^2 :=
              two_mul_le_sq_add_sq (⨆ j, ‖CoreFam j x‖ₑ) (⨆ K, ‖ErrFam K x‖ₑ)
      _ = 2 * (⨆ j, ‖CoreFam j x‖ₑ)^2 + 2 * (⨆ K, ‖ErrFam K x‖ₑ)^2 := by ring_nf
  -- the assembly
  set I : ℝ≥0∞ := ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count with hI
  set Kc : ℝ := 4 * Cwγ * A * (2:ℝ)^(-(m:ℝ)*powSig d) * ((m:ℝ)+2)^2 with hKc
  set Ke : ℝ := 2 * A * (160 + Cf) * (2:ℝ)^(-(m:ℝ)*powSig d) with hKe
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hKe0 : 0 ≤ Ke := by rw [hKe]; positivity
  have hfin : 2 * (ENNReal.ofReal (Kc^2) * I) + 2 * (ENNReal.ofReal (Ke^2) * I)
      ≤ ENNReal.ofReal ((2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)*powSig d)
          * ((m:ℝ)+2)^2)^2) * I := by
    have hx : (0:ℝ) < (2:ℝ)^(-(m:ℝ)*powSig d) := Real.rpow_pos_of_pos (by norm_num) _
    have hm2 : (1:ℝ) ≤ ((m:ℝ)+2)^2 := by
      have h : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      nlinarith
    have hsum : (2:ℝ≥0∞) * ENNReal.ofReal (Kc^2) + (2:ℝ≥0∞) * ENNReal.ofReal (Ke^2)
        ≤ ENNReal.ofReal ((2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)*powSig d)
            * ((m:ℝ)+2)^2)^2) := by
      have h2 : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
      rw [h2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hKc, hKe]
      exact const_key (4 * Cwγ * A) (2 * A * (160 + Cf)) ((2:ℝ)^(-(m:ℝ)*powSig d)) (((m:ℝ)+2)^2)
        (by positivity) (by positivity) (le_of_lt hx) hm2
    calc 2 * (ENNReal.ofReal (Kc^2) * I) + 2 * (ENNReal.ofReal (Ke^2) * I)
        = ((2:ℝ≥0∞) * ENNReal.ofReal (Kc^2) + (2:ℝ≥0∞) * ENNReal.ofReal (Ke^2)) * I := by ring
      _ ≤ ENNReal.ofReal ((2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)*powSig d)
            * ((m:ℝ)+2)^2)^2) * I := mul_le_mul_left hsum I
  calc ∫⁻ x : ℤ, (⨆ k : ℕ, ‖powTkBlockMax d g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (2 * (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ)
          + 2 * (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_mono hsup
    _ = 2 * ∫⁻ x : ℤ, (⨆ j : ℕ, ‖CoreFam j x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
        + 2 * ∫⁻ x : ℤ, (⨆ K : ℕ, ‖ErrFam K x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [lintegral_add_left (measurable_of_countable _),
          lintegral_const_mul' 2 _ (by norm_num), lintegral_const_mul' 2 _ (by norm_num)]
    _ ≤ 2 * (ENNReal.ofReal (Kc^2) * I) + 2 * (ENNReal.ofReal (Ke^2) * I) := by
        rw [hKc, hKe, hI]
        exact add_le_add (mul_le_mul_right hcore 2) (mul_le_mul_right herr 2)
    _ ≤ ENNReal.ofReal ((2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)*powSig d)
          * ((m:ℝ)+2)^2)^2) * I := hfin
    _ = ENNReal.ofReal (2 * (4 * Cwγ * A + 2 * A * (160 + Cf)) * (2:ℝ)^(-(m:ℝ)*powSig d)
          * ((m:ℝ)+2)^2) ^ 2 * ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [hI, ← ENNReal.ofReal_pow (by positivity)]



/-- **Major-arc approximation for the `d`-th power kernel.** -/
theorem pow_kernel_major_arc_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ), 3 ≤ N → ∀ (a : ℤ) (q : ℕ) (l : ℤ) (α : ℝ), 1 ≤ q →
        (q : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) → Int.gcd a (q : ℤ) = 1 →
        |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ (N : ℝ) ^ (-((d:ℝ) - 1/4)) →
        ‖powKernel d N α
          - ((q : ℂ)⁻¹ * Finset.sum (Finset.range q) (fun r =>
              Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) * (r : ℝ) ^ d / (q : ℝ) : ℝ)) : ℂ))))
            * (∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
                ((((α - (a : ℝ) / (q : ℝ) - (l : ℝ)) * (N : ℝ) ^ d * s ^ d : ℝ)) : ℂ)))‖
        ≤ C * ((N : ℝ) ^ c)⁻¹ := by
  obtain ⟨C, hCpos, hasym⟩ := pure_power_major_arc_approx d hd
  refine ⟨1/2, max C 1 * (2^d + 1) + 1, by norm_num, by positivity, ?_⟩
  intro N hN a q l α hq hqδ hgcd hb
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  -- the kernel as an exponential sum in the shifted form
  have hker : powKernel d N α = ((N : ℂ))⁻¹ * Finset.sum (Finset.range N) (fun n =>
      Complex.exp (2 * Real.pi * Complex.I *
        ((((a:ℝ)/(q:ℝ) + (α - (a:ℝ)/(q:ℝ) - (l:ℝ))) * (n:ℝ)^d : ℝ) : ℂ))) := by
    rw [powKernel]
    congr 1
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [show (a:ℝ)/(q:ℝ) + (α - (a:ℝ)/(q:ℝ) - (l:ℝ)) = α - (l:ℝ) by ring]
    rw [show (α * (n:ℝ)^d : ℝ)
        = ((α - (l:ℝ)) * (n:ℝ)^d) - (-(l * ((n:ℤ))^d) : ℤ) by push_cast; ring]
    exact exp_phase_shift_int ((α - (l:ℝ)) * (n:ℝ)^d) (-(l * ((n:ℤ))^d))
  rw [hker]
  -- the explicit factor in the form used by `hasym`
  have hfac : ((q : ℂ)⁻¹ * Finset.sum (Finset.range q) (fun r =>
        Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) * (r : ℝ) ^ d / (q : ℝ) : ℝ)) : ℂ))))
      = (q : ℂ)⁻¹ * Finset.sum (Finset.range q) (fun r =>
        Complex.exp (2 * Real.pi * Complex.I *
          ((((a : ℝ) / (q : ℝ) * (r : ℝ) ^ d : ℝ)) : ℂ))) := by
    congr 1
    exact Finset.sum_congr rfl (fun r hr => by congr 1; push_cast; ring)
  rw [hfac]
  refine le_trans (hasym N q a (α - (a:ℝ)/(q:ℝ) - (l:ℝ)) hq (by omega)) ?_
  -- the error bound
  have hbound : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| * (q : ℝ) * ((N : ℝ) + (q : ℝ))^d / (N : ℝ)
      + (q : ℝ) / (N : ℝ) ≤ (2^d + 1) * (N : ℝ) ^ (-(1/2:ℝ)) := by
    have hb1 : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| ≤ (N : ℝ) ^ (-((d:ℝ) - 1/4)) := hb
    have hq_le : (q : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) := hqδ
    have hNq : (N : ℝ) + (q : ℝ) ≤ 2 * (N : ℝ) := by
      have h3 : (N : ℝ) ^ ((1:ℝ)/4) ≤ (N : ℝ) := by
        calc (N : ℝ) ^ ((1:ℝ)/4) ≤ (N : ℝ) ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
          _ = (N : ℝ) := Real.rpow_one _
      linarith
    have h1 : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| * (q : ℝ) ≤ (N : ℝ)^(-((d:ℝ) - 1/2)) := by
      have h1a : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| * (q : ℝ)
          ≤ (N : ℝ)^(-((d:ℝ) - 1/4)) * (N : ℝ)^((1:ℝ)/4) :=
        mul_le_mul hb1 hq_le (by positivity) (Real.rpow_nonneg (by positivity) _)
      have h1b : (N : ℝ)^(-((d:ℝ) - 1/4)) * (N : ℝ)^((1:ℝ)/4)
          = (N : ℝ)^(-((d:ℝ) - 1/2)) := by
        rw [← Real.rpow_add hNr]
        congr 1
        ring
      exact h1a.trans_eq h1b
    have h2 : ((N : ℝ) + (q : ℝ))^d / (N : ℝ) ≤ (2:ℝ)^d * (N : ℝ)^((d:ℝ) - 1) := by
      have hNd : ((N:ℝ))^d = (N:ℝ)^((d:ℝ)-1) * (N:ℝ) := by
        rw [← Real.rpow_natCast (N:ℝ) d]
        conv_lhs => rw [show ((d:ℝ)) = ((d:ℝ) - 1) + 1 by ring]
        rw [Real.rpow_add hNr, Real.rpow_one]
      rw [div_le_iff₀ hNr]
      calc ((N : ℝ) + (q : ℝ))^d ≤ (2 * (N : ℝ))^d :=
            pow_le_pow_left₀ (by positivity) hNq d
        _ = (2:ℝ)^d * (N : ℝ)^d := by rw [mul_pow]
        _ = (2:ℝ)^d * (N : ℝ)^((d:ℝ) - 1) * (N : ℝ) := by rw [hNd]; ring
    have h3 : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| * (q : ℝ) * ((N : ℝ) + (q : ℝ))^d / (N : ℝ)
        ≤ (2:ℝ)^d * (N : ℝ)^(-(1:ℝ)/2) := by
      have h3a : |α - (a : ℝ) / (q : ℝ) - (l : ℝ)| * (q : ℝ) * ((N : ℝ) + (q : ℝ))^d / (N : ℝ)
          = (|α - (a : ℝ) / (q : ℝ) - (l : ℝ)| * (q : ℝ))
            * (((N : ℝ) + (q : ℝ))^d / (N : ℝ)) := by ring
      rw [h3a]
      refine le_trans (mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg (by positivity) _)) ?_
      refine le_of_eq ?_
      calc (N : ℝ) ^ (-((d:ℝ) - 1/2)) * ((2:ℝ)^d * (N : ℝ)^((d:ℝ) - 1))
          = (2:ℝ)^d * ((N : ℝ) ^ (-((d:ℝ) - 1/2)) * (N : ℝ)^((d:ℝ) - 1)) := by ring
        _ = (2:ℝ)^d * (N : ℝ)^(-(1:ℝ)/2) := by
            rw [← Real.rpow_add hNr]
            congr 1
            ring
    have h4 : (q : ℝ) / (N : ℝ) ≤ (N : ℝ)^(-(1:ℝ)/2) := by
      have h5 : (q : ℝ) / (N : ℝ) ≤ (N : ℝ)^((1:ℝ)/4) / (N : ℝ) :=
        div_le_div_of_nonneg_right hq_le hNr.le
      have h6 : (N : ℝ)^((1:ℝ)/4) / (N : ℝ) = (N : ℝ)^(-(3:ℝ)/4) := by
        rw [div_eq_mul_inv,
          show (N:ℝ)⁻¹ = (N:ℝ)^(-(1:ℝ)) from (Real.rpow_neg_one (N:ℝ)).symm,
          ← Real.rpow_add hNr]
        congr 1
        ring
      have h7 : (N : ℝ)^(-(3:ℝ)/4) ≤ (N : ℝ)^(-(1:ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      exact h5.trans (h6.trans_le h7)
    linarith [h3, h4, show (0:ℝ) < (2:ℝ)^d by positivity,
      show (0:ℝ) ≤ (N:ℝ)^(-(1:ℝ)/2) by positivity]
  have hC1 : C ≤ max C 1 := le_max_left _ _
  have hCpos' : 0 < max C 1 := lt_of_lt_of_le hCpos hC1
  have hfin : C * (|α - (a : ℝ) / (q : ℝ) - (l : ℝ)| * (q : ℝ) * ((N : ℝ) + (q : ℝ))^d / (N : ℝ)
        + (q : ℝ) / (N : ℝ))
      ≤ (max C 1 * (2^d + 1) + 1) * ((N : ℝ) ^ (1/2:ℝ))⁻¹ := by
    have h2 : C * (|α - (a : ℝ) / (q : ℝ) - (l : ℝ)| * (q : ℝ) * ((N : ℝ) + (q : ℝ))^d / (N : ℝ)
        + (q : ℝ) / (N : ℝ)) ≤ C * ((2^d + 1) * (N : ℝ)^(-(1/2:ℝ))) :=
      mul_le_mul_of_nonneg_left hbound hCpos.le
    have h3 : C * ((2^d + 1) * (N : ℝ)^(-(1/2:ℝ)))
        ≤ (max C 1 * ((2:ℝ)^d + 1)) * (N:ℝ)^(-(1/2:ℝ)) := by
      have h3a : C * ((2:ℝ)^d + 1) ≤ max C 1 * ((2:ℝ)^d + 1) :=
        mul_le_mul_of_nonneg_right hC1 (by positivity)
      have h3b : C * ((2^d + 1) * (N : ℝ)^(-(1/2:ℝ)))
          = (C * ((2:ℝ)^d + 1)) * (N:ℝ)^(-(1/2:ℝ)) := by ring
      rw [h3b]
      exact mul_le_mul_of_nonneg_right h3a (by positivity)
    have h4 : (max C 1 * ((2:ℝ)^d + 1)) * (N:ℝ)^(-(1/2:ℝ))
        ≤ (max C 1 * (2^d + 1) + 1) * ((N:ℝ)^(1/2:ℝ))⁻¹ := by
      have h4a : (N:ℝ)^(-(1/2:ℝ)) = ((N:ℝ)^(1/2:ℝ))⁻¹ := Real.rpow_neg hNr.le _
      rw [h4a]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    linarith [h2, h3, h4]
  exact hfin

/-- **Minor-arc decay for the `d`-th power kernel.** -/
theorem pow_kernel_minor_arc_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ ν C : ℝ, 0 < ν ∧ 0 < C ∧
      ∀ (N : ℕ), 3 ≤ N → ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
        (∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q → q ≤ Nat.floor ((N:ℝ)^((1:ℝ)/4)) → a < q →
            Nat.gcd a q = 1 → (N:ℝ)^(-((d:ℝ) - 1/4)) < |α - (a:ℝ)/(q:ℝ) - (l:ℝ)|) →
        ‖powKernel d N α‖ ≤ C * (N:ℝ)^(-ν) := by
  obtain ⟨C, ν, hC0, hν0, hdecay⟩ := weyl_minor_arc_decay d hd ((1:ℝ)/4)
    (by norm_num) (by norm_num)
  refine ⟨ν, C, hν0, hC0, fun N hN α hα0 hα1 hnoarc => ?_⟩
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hsf : (Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℕ) ≠ 0 := by
    refine Nat.pos_iff_ne_zero.mp ?_
    refine Nat.le_floor ?_
    have h2 : (1:ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hN1 (by norm_num)
    simpa using h2
  have hαne : α ≠ 0 := by
    intro h0
    have h := hnoarc 1 0 0 (by norm_num) (by
      refine Nat.le_floor ?_
      have h2 : (1:ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hN1 (by norm_num)
      simpa using h2) (by norm_num) (by norm_num)
    rw [h0] at h
    simp only [Nat.cast_one, div_one, Int.cast_zero, mul_zero, sub_zero, zero_sub, abs_neg,
      abs_zero] at h
    linarith [Real.rpow_pos_of_pos hNr (-((d:ℝ) - 1/4))]
  -- the minor-arc condition in the form required by Weyl's inequality
  have hminor : ∀ (q : ℤ) (a : ℤ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) →
      (N : ℝ) ^ (-((d:ℝ) - 1/4)) < |α - (a : ℝ) / (q : ℝ)| := by
    intro q a hq hqle
    have hqle_floor : (q:ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := hqle
    have hqpos : (0:ℤ) < q := by omega
    set r : ℤ := a % q with hr
    have hr0 : 0 ≤ r := hr ▸ Int.emod_nonneg a (ne_of_gt hqpos)
    have hrlt : r < q := hr ▸ Int.emod_lt_of_pos a hqpos
    set m : ℤ := a / q with hm
    have hdecZ : a = q * m + r := by
      have h := Int.mul_ediv_add_emod a q
      rw [← hm, ← hr] at h
      exact h.symm
    set rn : ℕ := r.toNat with hrn
    have hrcast : (rn : ℤ) = r := hrn ▸ Int.toNat_of_nonneg hr0
    have hqnat : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
    have hrnlt : rn < q.toNat := by
      have : ((rn : ℤ)) < q := by rw [hrcast]; exact hrlt
      rw [← hqnat] at this
      exact_mod_cast this
    have hqnatpos : 0 < q.toNat := by
      have : (0:ℤ) < q := hqpos
      rw [← hqnat] at this
      omega
    set d' : ℕ := Nat.gcd rn q.toNat with hdd
    have hddq : d' ∣ q.toNat := hdd ▸ Nat.gcd_dvd_right rn q.toNat
    have hddr : d' ∣ rn := hdd ▸ Nat.gcd_dvd_left rn q.toNat
    have hdpos : 0 < d' := Nat.pos_of_dvd_of_pos hddq hqnatpos
    set q₁ : ℕ := q.toNat / d' with hq1
    set r₁ : ℕ := rn / d' with hr1
    have hq1d : q₁ * d' = q.toNat := hq1 ▸ Nat.div_mul_cancel hddq
    have hr1d : r₁ * d' = rn := hr1 ▸ Nat.div_mul_cancel hddr
    have hcop : Nat.gcd r₁ q₁ = 1 := by
      have hpos : 0 < Nat.gcd rn q.toNat := by rw [← hdd]; exact hdpos
      have h := Nat.coprime_div_gcd_div_gcd (m := rn) (n := q.toNat) hpos
      rw [hq1, hr1]
      exact Nat.coprime_iff_gcd_eq_one.mp h
    have hr1lt : r₁ < q₁ := by
      have h3 : rn / d' < q.toNat / d' := Nat.div_lt_div_of_lt_of_dvd hddq hrnlt
      rw [hq1, hr1]; exact h3
    have hq1le : q₁ ≤ q.toNat := hq1 ▸ Nat.div_le_self q.toNat d'
    have hq1leN : q₁ ≤ Nat.floor ((N:ℝ)^((1:ℝ)/4)) := by
      refine Nat.le_floor ?_
      have h1 : (q₁:ℝ) ≤ (q.toNat:ℝ) := by exact_mod_cast hq1le
      have h3 : (q.toNat:ℝ) = (q:ℝ) := by exact_mod_cast hqnat
      rw [h3] at h1
      linarith [h1, hqle_floor]
    have hfr : (r₁:ℝ)/(q₁:ℝ) = (rn:ℝ)/(q.toNat:ℝ) := by
      have h1 : (rn:ℝ) = (r₁:ℝ) * (d':ℝ) := by rw [← hr1d]; push_cast; ring
      have h2 : (q.toNat:ℝ) = (q₁:ℝ) * (d':ℝ) := by rw [← hq1d]; push_cast; ring
      rw [h1, h2]
      have hd'ne : (d':ℝ) ≠ 0 := by positivity
      field_simp
    have hfr2 : (rn:ℝ)/(q:ℝ) = (r₁:ℝ)/(q₁:ℝ) := by
      have hq' : (q:ℝ) = (q.toNat:ℝ) := by exact_mod_cast hqnat.symm
      rw [hfr, hq']
    have haq : (a:ℝ)/(q:ℝ) = (m:ℝ) + (r₁:ℝ)/(q₁:ℝ) := by
      have h1 : (a:ℝ) = (q:ℝ) * (m:ℝ) + (rn:ℝ) := by
        have hZ : a = q * m + ((rn:ℤ)) := by rw [hrcast]; exact hdecZ
        exact_mod_cast hZ
      have hqR : (0:ℝ) < (q:ℝ) := by
        have : (0:ℤ) < q := hqpos
        exact_mod_cast this
      rw [h1, add_div, mul_div_cancel_left₀ _ (ne_of_gt hqR), hfr2]
    have hq1pos : 1 ≤ q₁ := by
      rcases Nat.eq_zero_or_pos q₁ with h0 | hp
      · rw [h0, zero_mul] at hq1d
        omega
      · exact hp
    by_cases hml : |m| ≤ 2
    · have hmI : m ∈ Finset.Icc (-2 : ℤ) 2 := by
        rw [Finset.mem_Icc]
        have h := abs_le.mp hml
        omega
      have h := hnoarc q₁ r₁ m hq1pos hq1leN hr1lt hcop
      have habs : |α - (a:ℝ)/(q:ℝ)| = |α - (r₁:ℝ)/(q₁:ℝ) - (m:ℝ)| := by
        rw [haq]; congr 1; ring
      rwa [habs]
    · have hm3 : (3:ℝ) ≤ |(m:ℝ)| := by
        have hZ : (3:ℤ) ≤ |m| := by
          have : (2:ℤ) < |m| := by exact_mod_cast (lt_of_not_ge hml)
          omega
        exact_mod_cast hZ
      have hsmall : (N:ℝ)^(-((d:ℝ) - 1/4)) < 1 := by
        have hd4 : (0:ℝ) < (d:ℝ) - 1/4 := by
          have hd' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
          linarith
        have hlt := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1)
          (by exact_mod_cast (by omega : 1 < N) : (1:ℝ) < (N:ℝ)) hd4
        rw [Real.one_rpow] at hlt
        rw [Real.rpow_neg hNr.le]
        exact inv_lt_one_of_one_lt₀ hlt
      have hbig : (1:ℝ) < |α - (a:ℝ)/(q:ℝ)| := by
        rw [haq]
        have h2 : |α - ((m:ℝ) + (r₁:ℝ)/(q₁:ℝ))| = |(α - (r₁:ℝ)/(q₁:ℝ)) - (m:ℝ)| := by
          congr 1; ring
        rw [h2]
        have h3 : (r₁:ℝ)/(q₁:ℝ) < 1 := by
          rw [div_lt_one (by positivity)]; exact_mod_cast hr1lt
        have h4 : (0:ℝ) ≤ (r₁:ℝ)/(q₁:ℝ) := by positivity
        have h5 : |α - (r₁:ℝ)/(q₁:ℝ)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        have h6 : |(m:ℝ)| ≤ |(α - (r₁:ℝ)/(q₁:ℝ)) - (m:ℝ)| + |α - (r₁:ℝ)/(q₁:ℝ)| := by
          have h := abs_sub_le ((m:ℝ)) (α - (r₁:ℝ)/(q₁:ℝ)) 0
          simp only [sub_zero] at h
          have heq : (m:ℝ) - (α - (r₁:ℝ)/(q₁:ℝ)) = -((α - (r₁:ℝ)/(q₁:ℝ)) - (m:ℝ)) := by ring
          rw [heq, abs_neg] at h
          exact h
        linarith
      linarith
  have hkey := hdecay N (Polynomial.C α * Polynomial.X ^ d) (by
      rw [Polynomial.natDegree_C_mul hαne, Polynomial.natDegree_X_pow])
    (by omega) (by
      intro q a hq hqle
      have h := hminor q a hq hqle
      have hexp : -(d:ℝ) + 1/4 = -((d:ℝ) - 1/4) := by ring
      simpa only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        Polynomial.leadingCoeff_X_pow, mul_one, hexp] using h)
  refine le_trans (le_of_eq ?_) hkey
  have hsum : (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ↑(α * ↑n ^ d)))
      = (∑ x ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I *
          ↑(Polynomial.eval (x:ℝ) (Polynomial.C α * Polynomial.X ^ d)))) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hev : Polynomial.eval (x:ℝ) (Polynomial.C α * Polynomial.X ^ d) = α * (x:ℝ)^d := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hev]
  rw [powKernel, Complex.ofReal_natCast, hsum]

/-- **The `d`-th power model approximates the kernel uniformly.** -/
theorem pow_kernel_major_arc_model (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ), 3 ≤ N → ∀ (α : ℝ), 0 ≤ α → α ≤ 1 →
      ‖powKernel d N α - powMajorArcModel d ((1:ℝ)/4) N α‖ ≤ C * ((N : ℝ) ^ c)⁻¹ := by
  obtain ⟨c1, C1, hc1, hC1, hmaj⟩ := pow_kernel_major_arc_bound d hd
  obtain ⟨ν, C2, hν, hC2, hmin⟩ := pow_kernel_minor_arc_bound d hd
  refine ⟨min c1 ν, max C1 C2 + 1, lt_min hc1 hν, by positivity, ?_⟩
  intro N hN α hα0 hα1
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hstep : ∀ {c C : ℝ}, (c = c1 ∨ c = ν) → 0 ≤ C → C ≤ max C1 C2 →
      C * ((N:ℝ) ^ c)⁻¹ ≤ (max C1 C2 + 1) * ((N:ℝ) ^ (min c1 ν))⁻¹ := by
    intro c C hc hC hCle
    have hc' : min c1 ν ≤ c := by
      rcases hc with h | h <;> rw [h]
      · exact min_le_left _ _
      · exact min_le_right _ _
    have h1 : C ≤ max C1 C2 + 1 := by linarith
    have h2 : ((N:ℝ) ^ c)⁻¹ ≤ ((N:ℝ) ^ (min c1 ν))⁻¹ := by
      rw [← Real.rpow_neg hNr.le, ← Real.rpow_neg hNr.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  by_cases harc : ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) ∧
      x.2.1 < x.1 ∧ Nat.gcd x.2.1 x.1 = 1 ∧ x.2.2 ∈ Finset.Icc (-2 : ℤ) 2 ∧
      |α - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)| ≤ (N : ℝ) ^ (-((d:ℝ) - 1/4))
  · have hfloor : (harc.choose.1 : ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := by
      have h1 : ((Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℕ) : ℝ) ≤ (N:ℝ)^((1:ℝ)/4) :=
        Nat.floor_le (by positivity)
      have h2 : (harc.choose.1 : ℝ) ≤ ((Nat.floor ((N:ℝ)^((1:ℝ)/4)) : ℕ) : ℝ) := by
        exact_mod_cast harc.choose_spec.2.1
      linarith
    have hgcd' : Int.gcd (harc.choose.2.1 : ℤ) (harc.choose.1 : ℤ) = 1 := by
      rw [Int.gcd_eq_natAbs]
      simp only [Int.natAbs_natCast]
      exact_mod_cast harc.choose_spec.2.2.2.1
    have hmodel : powModelTerm d N harc.choose.1 harc.choose.2.1 harc.choose.2.2 α
        = ((harc.choose.1 : ℂ)⁻¹ * Finset.sum (Finset.range harc.choose.1) (fun r =>
              Complex.exp (2 * Real.pi * Complex.I *
                ((((harc.choose.2.1 : ℝ) * (r : ℝ) ^ d / (harc.choose.1 : ℝ) : ℝ)) : ℂ))))
            * (∫ s in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I *
                ((((α - (harc.choose.2.1 : ℝ) / (harc.choose.1 : ℝ) - (harc.choose.2.2 : ℝ))
                  * (N : ℝ) ^ d * s ^ d : ℝ)) : ℂ))) := by
      rw [powModelTerm, powWeight, powProfile]
      refine congrArg₂ (fun x y => x * y) ?_ ?_
      · congr 1
        exact Finset.sum_congr rfl (fun r hr => by congr 1; push_cast; ring)
      · apply intervalIntegral.integral_congr
        intro s hs
        congr 1
    rw [powMajorArcModel_eq_single d hd (by norm_num) (by norm_num) hN hα0 hα1 harc, hmodel]
    exact le_trans (hmaj N hN (harc.choose.2.1 : ℤ) harc.choose.1 harc.choose.2.2 α
      harc.choose_spec.1 hfloor hgcd' harc.choose_spec.2.2.2.2.2)
      (hstep (Or.inl rfl) hC1.le (le_max_left _ _))
  · rw [powMajorArcModel_eq_zero d harc]
    have hnoarc : ∀ (q : ℕ) (a : ℕ) (l : ℤ), 1 ≤ q →
        q ≤ Nat.floor ((N:ℝ)^((1:ℝ)/4)) → a < q → Nat.gcd a q = 1 →
        (N:ℝ)^(-((d:ℝ) - 1/4)) < |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| := by
      intro q a l hq hqfl ha hgcd
      by_cases hl3 : |(l:ℝ)| < 3
      · have hlmem : l ∈ Finset.Icc (-2 : ℤ) 2 := by
          rw [abs_lt] at hl3
          rw [Finset.mem_Icc]
          constructor
          · have : (-3:ℤ) < l := by exact_mod_cast hl3.1
            omega
          · have : l < (3:ℤ) := by exact_mod_cast hl3.2
            omega
        by_contra hcon
        exact harc ⟨(q, a, l), hq, hqfl, ha, hgcd, hlmem, not_lt.mp hcon⟩
      · have hl3' : (3:ℝ) ≤ |(l:ℝ)| := not_lt.mp hl3
        have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
        have h1 : |α - (a:ℝ)/(q:ℝ)| ≤ 1 := by
          rw [abs_le]
          constructor
          · have h2 : (a:ℝ)/(q:ℝ) ≤ 1 := by rw [div_le_one hqR]; exact_mod_cast (le_of_lt ha)
            linarith
          · have h2 : (0:ℝ) ≤ (a:ℝ)/(q:ℝ) := by positivity
            linarith
        have h2 : (2:ℝ) ≤ |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| := by
          have h3 : |(l:ℝ)| ≤ |α - (a:ℝ)/(q:ℝ) - (l:ℝ)| + |α - (a:ℝ)/(q:ℝ)| := by
            have h := abs_sub_le ((l:ℝ)) (α - (a:ℝ)/(q:ℝ)) 0
            simp only [sub_zero] at h
            have heq : (l:ℝ) - (α - (a:ℝ)/(q:ℝ)) = -((α - (a:ℝ)/(q:ℝ)) - (l:ℝ)) := by ring
            rw [heq, abs_neg] at h
            exact h
          linarith
        have h4 : (N:ℝ)^(-((d:ℝ) - 1/4)) < 2 := by
          have hd' : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
          have h5 : -((d:ℝ) - 1/4) ≤ -(7/4:ℝ) := by linarith
          have h6 : (N:ℝ)^(-(7/4:ℝ)) ≤ (3:ℝ)^(-(7/4:ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hN) (by norm_num)
          have h7 : (3:ℝ)^(-(7/4:ℝ)) < 2 := by
            have h9 : (1:ℝ) < (3:ℝ)^((7:ℝ)/4) := by
              calc (1:ℝ) = (1:ℝ)^((7:ℝ)/4) := (Real.one_rpow _).symm
                _ < (3:ℝ)^((7:ℝ)/4) := Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
            rw [show (-(7/4:ℝ)) = -((7:ℝ)/4) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
            have := inv_lt_one_of_one_lt₀ h9
            linarith
          linarith [Real.rpow_le_rpow_of_exponent_le hN1 h5]
        linarith
    refine le_trans ?_ (hstep (Or.inr rfl) hC2.le (le_max_right _ _))
    simpa only [sub_zero, Real.rpow_neg hNr.le] using hmin N hN α hα0 hα1 hnoarc


/-! ## The circle-method error term for the `d`-th power kernel -/

/-- The conjugate of the `d`-th power Weyl kernel, written as a conjugated exponential sum. -/
lemma conj_powKernel (d : ℕ) (N : ℕ) (θ : ℝ) :
    starRingEnd ℂ (powKernel d N θ)
      = ((N : ℂ))⁻¹ * ∑ i ∈ Finset.range N,
          Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ d) * θ))) := by
  rw [powKernel, map_mul, map_sum]
  congr 1
  · rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring

/-- Continuity of a single model term in the frequency. -/
lemma continuous_powModelTerm (d N q : ℕ) (a : ℕ) (l : ℤ) :
    Continuous (fun α : ℝ => powModelTerm d N q a l α) := by
  unfold powModelTerm
  exact continuous_const.mul ((continuous_powProfile d).comp (by fun_prop))

/-- Measurability of the major-arc model in the frequency. -/
lemma measurable_powMajorArcModel (d : ℕ) (δ : ℝ) (N : ℕ) :
    Measurable (fun α : ℝ => powMajorArcModel d δ N α) := by
  unfold powMajorArcModel powMajorArcBlock
  refine Finset.measurable_sum _ (fun q _ => ?_)
  refine Finset.measurable_sum _ (fun a _ => ?_)
  refine Measurable.ite (by measurability) ?_ measurable_const
  refine Finset.measurable_sum _ (fun l _ => ?_)
  exact Measurable.ite (by measurability) (measurable_powModelTerm d N q a l) measurable_const

lemma measurable_powKernel (d N : ℕ) : Measurable (powKernel d N) := by
  unfold powKernel
  fun_prop

lemma continuous_powKernel (d N : ℕ) : Continuous (powKernel d N) := by
  unfold powKernel
  fun_prop

/-- The major-arc model, multiplied by a continuous function, is interval integrable. -/
lemma intervalIntegrable_powMajorArcModel_mul (d : ℕ) (hd : 2 ≤ d) {N : ℕ}
    (hN : 3 ≤ N) {f : ℝ → ℂ} (hf : Continuous f) :
    IntervalIntegrable (fun θ : ℝ =>
      (starRingEnd ℂ (powMajorArcModel d ((1:ℝ)/4) N θ)) * f θ)
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  refine IntegrableOn.of_bound ?_ ?_ (1 * D) ?_
  · rw [Real.volume_Ioc]; simp
  · refine ((Complex.continuous_conj.measurable.comp
      (measurable_powMajorArcModel d ((1:ℝ)/4) N)).mul hf.measurable).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (fun θ hθ => ?_))
    have hθI : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hθ.1, hθ.2⟩
    have hb := norm_powMajorArcModel_le_one d hd hN hθI.1 hθI.2
    have hbD := hD θ hθI
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hb hbD (norm_nonneg _) (by positivity)



open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology

/-! ## Fourier identity for the `d`-th power shifts -/

theorem pow_shift_fourier_coeff_conj (d : ℕ) (g : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → g n = 0) (N : ℕ) (k : ℤ) :
    (∫ θ in (0:ℝ)..1,
        ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ d) * θ))))
          * (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ))))
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, g (k + (i : ℤ) ^ d) := by
  have hpt : ∀ θ : ℝ,
      ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ d) * θ))))
          * (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ)))
      = (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ d - k : ℤ) : ℝ)) * θ)) := by
    intro θ
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro m _
    have hexp : Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ d - k : ℤ) : ℝ)) * θ))
        = Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ d) * θ)))
          * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  have hint : ∀ i : ℕ,
      (∫ θ in (0:ℝ)..1, ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ d - k : ℤ) : ℝ)) * θ)))
        = ∑ m ∈ s, g m * (if (m - (i : ℤ) ^ d - k) = 0 then 1 else 0) := by
    intro i
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m _
      rw [intervalIntegral.integral_const_mul, Commons.Analysis.Fourier.integral_exp_two_pi_int]
    · intro m _
      exact Continuous.intervalIntegrable (by fun_prop) 0 1
  have hstep : ∀ i : ℕ,
      (∑ m ∈ s, g m * (if (m - (i : ℤ) ^ d - k) = 0 then 1 else 0))
        = g (k + (i : ℤ) ^ d) := by
    intro i
    have hiff : ∀ m : ℤ, (m - (i : ℤ) ^ d - k = 0) ↔ (m = k + (i : ℤ) ^ d) := by
      intro m; constructor <;> intro h <;> omega
    have hstep' : ∀ m : ℤ, g m * (if m = k + (i : ℤ) ^ d then 1 else 0)
        = if m = k + (i : ℤ) ^ d then g m else 0 := by
      intro m; by_cases h : m = k + (i : ℤ) ^ d <;> simp [h]
    simp only [hiff, hstep', Finset.sum_ite_eq']
    by_cases hb : (k + (i : ℤ) ^ d) ∈ s
    · simp [hb]
    · simp [hb, hs (k + (i : ℤ) ^ d) hb]
  rw [show (∫ θ in (0:ℝ)..1,
        ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
            Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ d) * θ))))
          * (∑ m ∈ s, g m * Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) * θ)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) * θ))))
      = ∫ θ in (0:ℝ)..1, (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ d - k : ℤ) : ℝ)) * θ))
      from intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum
        (f := fun (i : ℕ) (θ : ℝ) => ∑ m ∈ s,
          g m * Complex.exp (2 * Real.pi * Complex.I * ((((m - (i : ℤ) ^ d - k : ℤ) : ℝ)) * θ)))]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hint i, hstep i]
  · intro i _
    exact Continuous.intervalIntegrable (by fun_prop) 0 1



open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology

private lemma mem_range_lt_pow_succ_log {N i : ℕ} (hi : i < N) : i < 2 ^ (Nat.log 2 N + 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  omega

private lemma norm_ofReal_sum_norm (d : ℕ) (s : Finset ℕ) (g : ℤ → ℂ) (m : ℤ) :
    ‖∑ i ∈ s, (((‖g (m + (i : ℤ) ^ d)‖ : ℝ) : ℂ))‖
      = ∑ i ∈ s, ‖g (m + (i : ℤ) ^ d)‖ := by
  rw [← Complex.ofReal_sum, Complex.norm_real]
  exact Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))

theorem pow_dyadic_reduction_z (d : ℕ)
    (h : ∃ C : ℝ, 0 < C ∧
      ∀ g : ℤ → ℂ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
        MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
          (iSup fun k : ℕ => enorm (((2 : ℝ) ^ k)⁻¹ *
            Finset.sum (Finset.range (2 ^ k)) (fun i => g (m + (i : ℤ) ^ d)))) ^ (2 : ℝ))
          ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun m : ℤ => (enorm (g m)) ^ (2 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : ℤ → ℂ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
        MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
          (iSup fun N : ℕ => enorm ((N : ℝ)⁻¹ *
            Finset.sum (Finset.range N) (fun i => g (m + (i : ℤ) ^ d)))) ^ (2 : ℝ))
          ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun m : ℤ => (enorm (g m)) ^ (2 : ℝ)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := h
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro g hg
  set G : ℤ → ℂ := fun n => ((‖g n‖ : ℝ) : ℂ) with hGdef
  have hG : ∃ s : Finset ℤ, ∀ n, n ∉ s → G n = 0 := by
    obtain ⟨s, hs⟩ := hg
    exact ⟨s, fun n hn => by simp [hGdef, hs n hn]⟩
  have hGnorm : ∀ n : ℤ, ‖G n‖ = ‖g n‖ := by
    intro n
    rw [hGdef, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  set D : ℤ → ℝ≥0∞ := fun m => ⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ *
      ∑ i ∈ Finset.range (2 ^ k), G (m + (i : ℤ) ^ d)‖ₑ with hDdef
  have hkey : ∀ m : ℤ, ∀ N : ℕ,
      ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + (i : ℤ) ^ d)‖ₑ ≤ 2 * D m := by
    intro m N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [Nat.cast_zero, Finset.range_zero, Finset.sum_empty, mul_zero, enorm_zero]
      positivity
    · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have h1 : ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + (i : ℤ) ^ d)‖ₑ
          = ENNReal.ofReal ((N : ℝ)⁻¹ * ‖∑ i ∈ Finset.range N, g (m + (i : ℤ) ^ d)‖) := by
        rw [← ofReal_norm, Complex.norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [h1]
      set k : ℕ := Nat.log 2 N with hk
      have hk1 : 2 ^ k ≤ N := Nat.pow_log_le_self 2 (by omega)
      have hcast : ((2 : ℝ) ^ k) ≤ (N : ℝ) := by exact_mod_cast hk1
      have hsum : ∑ i ∈ Finset.range N, ‖g (m + (i : ℤ) ^ d)‖
          ≤ ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + (i : ℤ) ^ d)‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [Finset.mem_range] at hi ⊢
          have hk2 := mem_range_lt_pow_succ_log hi
          simpa [hk] using hk2
        · intro i _ _; positivity
      have hcoef : (N : ℝ)⁻¹ ≤ 2 * ((2 : ℝ) ^ (k + 1))⁻¹ := by
        have h2k : 0 < ((2 : ℝ) ^ k) := by positivity
        have hle : (N : ℝ)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := (inv_le_inv₀ hNpos h2k).2 hcast
        calc (N : ℝ)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := hle
          _ = 2 * ((2 : ℝ) ^ (k + 1))⁻¹ := by rw [pow_succ]; field_simp
      have hstep : (N : ℝ)⁻¹ * ‖∑ i ∈ Finset.range N, g (m + (i : ℤ) ^ d)‖
          ≤ 2 * (((2 : ℝ) ^ (k + 1))⁻¹
              * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + (i : ℤ) ^ d)‖) := by
        calc (N : ℝ)⁻¹ * ‖∑ i ∈ Finset.range N, g (m + (i : ℤ) ^ d)‖
            ≤ (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ‖g (m + (i : ℤ) ^ d)‖ :=
              mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
          _ ≤ (N : ℝ)⁻¹ * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + (i : ℤ) ^ d)‖ :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ ≤ (2 * ((2 : ℝ) ^ (k + 1))⁻¹)
                * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + (i : ℤ) ^ d)‖ :=
              mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun i _ => norm_nonneg _))
          _ = 2 * (((2 : ℝ) ^ (k + 1))⁻¹
                * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + (i : ℤ) ^ d)‖) := by ring
      refine le_trans (ENNReal.ofReal_le_ofReal hstep) ?_
      have h4 : ENNReal.ofReal (2 * (((2 : ℝ) ^ (k + 1))⁻¹
            * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + (i : ℤ) ^ d)‖))
          = 2 * ENNReal.ofReal (((2 : ℝ) ^ (k + 1))⁻¹
            * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + (i : ℤ) ^ d)‖) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        exact ENNReal.ofReal_ofNat 2
      rw [h4]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have h5 : ENNReal.ofReal (((2 : ℝ) ^ (k + 1))⁻¹
            * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + (i : ℤ) ^ d)‖)
          = ‖((2 : ℝ) ^ (k + 1))⁻¹
              * ∑ i ∈ Finset.range (2 ^ (k + 1)), G (m + (i : ℤ) ^ d)‖ₑ := by
        rw [← ofReal_norm]
        congr 1
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        congr 1
        rw [hGdef]
        exact (norm_ofReal_sum_norm d _ g m).symm
      rw [h5, hDdef]
      exact le_iSup (fun k : ℕ => ‖((2 : ℝ) ^ k)⁻¹
        * ∑ i ∈ Finset.range (2 ^ k), G (m + (i : ℤ) ^ d)‖ₑ) (k + 1)
  have hsup : ∀ m : ℤ, (⨆ N : ℕ,
      ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + (i : ℤ) ^ d)‖ₑ) ≤ 2 * D m :=
    fun m => iSup_le (fun N => hkey m N)
  calc MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
        (iSup fun N : ℕ => enorm ((N : ℝ)⁻¹ *
          Finset.sum (Finset.range N) (fun i => g (m + (i : ℤ) ^ d)))) ^ (2 : ℝ))
      ≤ ∫⁻ m, (2 * D m) ^ (2 : ℝ) ∂Measure.count :=
        lintegral_mono (fun m => ENNReal.rpow_le_rpow (hsup m) (by norm_num))
    _ = ∫⁻ m, 4 * (D m) ^ (2 : ℝ) ∂Measure.count := by
        refine lintegral_congr (fun m => ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
    _ = 4 * ∫⁻ m, (D m) ^ (2 : ℝ) ∂Measure.count :=
        lintegral_const_mul' 4 _ (by simp)
    _ ≤ 4 * (ENNReal.ofReal (C₀ ^ 2)
          * ∫⁻ m, ‖G m‖ₑ ^ (2 : ℝ) ∂Measure.count) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        simpa only [hDdef] using hbound G hG
    _ = ENNReal.ofReal ((2 * C₀) ^ 2)
          * ∫⁻ m, ‖g m‖ₑ ^ (2 : ℝ) ∂Measure.count := by
        have hGint : ∫⁻ m, ‖G m‖ₑ ^ (2 : ℝ) ∂Measure.count
            = ∫⁻ m, ‖g m‖ₑ ^ (2 : ℝ) ∂Measure.count := by
          refine lintegral_congr (fun m => ?_)
          have h : ‖G m‖ = ‖g m‖ := hGnorm m
          rw [← ofReal_norm, ← ofReal_norm, h]
        have h4 : ENNReal.ofReal ((2 * C₀) ^ 2) = 4 * ENNReal.ofReal (C₀ ^ 2) := by
          rw [show ((2 * C₀) ^ 2 : ℝ) = 4 * C₀ ^ 2 by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
          congr 1
          exact ENNReal.ofReal_ofNat 4
        rw [hGint, h4]
        ring



open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology

private def natExtend (g : ℕ → ℝ) : ℤ → ℂ := fun n => if 0 ≤ n then (g n.toNat : ℂ) else 0

private lemma natExtend_of_nonneg (g : ℕ → ℝ) {n : ℤ} (hn : 0 ≤ n) :
    natExtend g n = (g n.toNat : ℂ) := by
  rw [natExtend, if_pos hn]

private lemma natExtend_cast (g : ℕ → ℝ) (m : ℕ) : natExtend g (m : ℤ) = (g m : ℂ) := by
  rw [natExtend_of_nonneg g (Int.natCast_nonneg m), Int.toNat_natCast]

private lemma natExtend_neg (g : ℕ → ℝ) {n : ℤ} (hn : n < 0) : natExtend g n = 0 := by
  rw [natExtend, if_neg (not_le.mpr hn)]

private lemma natExtend_add_pow (d : ℕ) (g : ℕ → ℝ) (m i : ℕ) :
    natExtend g ((m : ℤ) + (i : ℤ) ^ d) = (g (m + i ^ d) : ℂ) := by
  have h0 : (0 : ℤ) ≤ (m : ℤ) + (i : ℤ) ^ d := by positivity
  rw [natExtend_of_nonneg g h0]
  have h2 : ((m : ℤ) + (i : ℤ) ^ d).toNat = m + i ^ d := by
    have hcast : ((m : ℤ) + (i : ℤ) ^ d) = ((m + i ^ d : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]
  rw [h2]

private lemma natExtend_sum (d : ℕ) (g : ℕ → ℝ) (m N : ℕ) :
    (∑ i ∈ Finset.range N, natExtend g ((m : ℤ) + (i : ℤ) ^ d))
      = ((∑ i ∈ Finset.range N, g (m + i ^ d) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => natExtend_add_pow d g m i)

private lemma enorm_complex_coe (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

private lemma enorm_real_coe_mul (a S : ℝ) :
    ‖(a : ℂ) * (S : ℂ)‖ₑ = ‖a * S‖ₑ := by
  rw [← Complex.ofReal_mul, enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

private noncomputable def Zmax (d : ℕ) (G : ℤ → ℂ) (n : ℤ) : ℝ≥0∞ :=
  (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, G (n + (i : ℤ) ^ d))‖ₑ) ^ (2 : ℝ)

private noncomputable def Zl2 (G : ℤ → ℂ) (n : ℤ) : ℝ≥0∞ := ‖G n‖ₑ ^ (2 : ℝ)

private noncomputable def Nmax (d : ℕ) (g : ℕ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, g (m + i ^ d))‖ₑ) ^ (2 : ℝ)

private noncomputable def Nl2 (g : ℕ → ℝ) (m : ℕ) : ℝ≥0∞ := ‖g m‖ₑ ^ (2 : ℝ)

private lemma enorm_step (d : ℕ) (g : ℕ → ℝ) (m N : ℕ) :
    ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, g (m + i ^ d))‖ₑ
      = ‖(N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, natExtend g ((m : ℤ) + (i : ℤ) ^ d))‖ₑ := by
  rw [natExtend_sum d g m N]
  exact (enorm_real_coe_mul (N : ℝ)⁻¹ (∑ i ∈ Finset.range N, g (m + i ^ d))).symm

private lemma integrand_eq (d : ℕ) (g : ℕ → ℝ) (m : ℕ) :
    Nmax d g m = Zmax d (natExtend g) (m : ℤ) := by
  simp only [Nmax, Zmax]
  rw [iSup_congr (fun N => enorm_step d g m N)]

private def natIciEquiv : ℕ ≃ Set.Ici (0 : ℤ) where
  toFun m := ⟨(m : ℤ), Int.natCast_nonneg m⟩
  invFun n := n.1.toNat
  left_inv m := Int.toNat_natCast m
  right_inv n := by
    ext
    exact Int.toNat_of_nonneg n.2

private lemma natIciEquiv_coe (m : ℕ) : ((natIciEquiv m : Set.Ici (0 : ℤ)) : ℤ) = (m : ℤ) := rfl

private lemma natExtend_support (g : ℕ → ℝ) :
    Function.support (fun n : ℤ => ‖natExtend g n‖ₑ ^ (2 : ℝ)) ⊆ Set.Ici (0 : ℤ) := by
  intro n hn
  rw [Set.mem_Ici]
  by_contra h
  rw [Function.mem_support] at hn
  refine hn ?_
  rw [natExtend_neg g (lt_of_not_ge h)]
  simp

private lemma natExtend_tsum (g : ℕ → ℝ) :
    (∑' n : ℤ, Zl2 (natExtend g) n) = (∑' m : ℕ, Nl2 g m) := by
  simp only [Zl2, Nl2]
  rw [← tsum_subtype_eq_of_support_subset (natExtend_support g)]
  rw [← Equiv.tsum_eq natIciEquiv (fun b : Set.Ici (0 : ℤ) => ‖natExtend g (b : ℤ)‖ₑ ^ (2 : ℝ))]
  refine tsum_congr (fun m => ?_)
  rw [natIciEquiv_coe, natExtend_cast, enorm_complex_coe]

theorem pow_shift_transfer (d : ℕ)
    (h : ∃ C : ℝ, 0 < C ∧
      ∀ g : ℤ → ℂ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
        MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
          (iSup fun N : ℕ => enorm ((N : ℝ)⁻¹ *
            Finset.sum (Finset.range N) (fun i => g (m + (i : ℤ) ^ d)))) ^ (2 : ℝ))
          ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun n : ℤ => (enorm (g n)) ^ (2 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
        MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℕ =>
          (iSup fun N : ℕ => enorm ((N : ℝ)⁻¹ *
            Finset.sum (Finset.range N) (fun i => g (m + i ^ d)))) ^ (2 : ℝ))
          ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun m : ℕ => (enorm (g m)) ^ (2 : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨C, hCpos, ?_⟩
  intro g hg
  have hGsupp : ∃ s : Finset ℤ, ∀ n, n ∉ s → natExtend g n = 0 := by
    obtain ⟨s, hs⟩ := hg
    refine ⟨s.image (Nat.cast), ?_⟩
    intro n hn
    by_cases hn0 : 0 ≤ n
    · rw [natExtend_of_nonneg g hn0]
      have hmem : n.toNat ∉ s := by
        intro hmem
        apply hn
        rw [Finset.mem_image]
        exact ⟨n.toNat, hmem, Int.toNat_of_nonneg hn0⟩
      rw [hs _ hmem]
      simp
    · rw [natExtend_neg g (lt_of_not_ge hn0)]
  have hbound := hC (natExtend g) hGsupp
  have hbound' : (∑' n : ℤ, Zmax d (natExtend g) n)
      ≤ ENNReal.ofReal (C ^ 2) * (∑' n : ℤ, Zl2 (natExtend g) n) := by
    simpa only [Zmax, Zl2, lintegral_count] using hbound
  change MeasureTheory.lintegral MeasureTheory.Measure.count (Nmax d g)
      ≤ ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count (Nl2 g)
  calc
    MeasureTheory.lintegral MeasureTheory.Measure.count (Nmax d g)
        = ∑' m : ℕ, Nmax d g m := lintegral_count _
    _ = ∑' m : ℕ, Zmax d (natExtend g) (m : ℤ) := tsum_congr (fun m => integrand_eq d g m)
    _ ≤ ∑' n : ℤ, Zmax d (natExtend g) n :=
          ENNReal.tsum_comp_le_tsum_of_injective Nat.cast_injective _
    _ ≤ ENNReal.ofReal (C ^ 2) * (∑' n : ℤ, Zl2 (natExtend g) n) := hbound'
    _ = ENNReal.ofReal (C ^ 2) * (∑' m : ℕ, Nl2 g m) := by rw [natExtend_tsum g]
    _ = ENNReal.ofReal (C ^ 2) * MeasureTheory.lintegral MeasureTheory.Measure.count (Nl2 g) := by
          rw [lintegral_count]



theorem pow_dyadic_of_model (d : ℕ) (hd : 2 ≤ d)
    (hmodel : ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (Commons.Analysis.ExponentialSums.powMajorArcModel d ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖((2:ℝ)^k)⁻¹ * ∑ i ∈ Finset.range (2^k), g (m + (i:ℤ)^d)‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C^2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  classical
  obtain ⟨A, hApos, hAbound⟩ := hmodel
  obtain ⟨cm, Cm, hcmpos, hCmpos, hmaj⟩ := pow_kernel_major_arc_model d hd
  -- the geometric ratio of the error family
  set r : ℝ := (2 : ℝ) ^ (-cm) with hr
  have hrpos : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  -- the error symbol
  set psi : ℕ → ℝ → ℂ := fun k θ =>
      if k < 2 then 0
      else if θ ∈ Set.Icc (0 : ℝ) 1 then
        (starRingEnd ℂ (powKernel d (2 ^ k) θ) -
         starRingEnd ℂ (powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k) θ))
      else 0 with hpsi
  set Ab : ℕ → ℝ := fun k => if k < 2 then 0 else Cm * r ^ k with hAb
  have hAbnn : ∀ k, 0 ≤ Ab k := by
    intro k
    simp only [hAb]
    by_cases hk : k < 2
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      exact mul_nonneg (le_of_lt hCmpos) (pow_nonneg (le_of_lt hrpos) k)
  have hAb_summable : Summable Ab := by
    refine Summable.of_nonneg_of_le (f := fun k : ℕ => Cm * r ^ k) hAbnn (fun k => ?_) ?_
    · simp only [hAb]
      by_cases hk : k < 2
      · simp only [hk, ↓reduceIte]
        positivity
      · simp only [hk, ↓reduceIte]
        exact le_rfl
    · refine (summable_geometric_iff_norm_lt_one.mpr ?_).mul_left Cm
      rw [Real.norm_eq_abs, abs_of_pos hrpos]
      exact hrlt
  have hpsi_meas : ∀ k, Measurable (psi k) := by
    intro k
    simp only [hpsi]
    by_cases hk : k < 2
    · simp only [hk, ↓reduceIte]
      exact measurable_const
    · simp only [hk, ↓reduceIte]
      refine Measurable.ite measurableSet_Icc ?_ measurable_const
      exact ((Complex.continuous_conj.measurable).comp (measurable_powKernel d (2 ^ k))).sub
        ((Complex.continuous_conj.measurable).comp (measurable_powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k)))
  have hpow : ∀ k : ℕ, (((2 : ℝ) ^ k) ^ cm)⁻¹ = r ^ k := by
    intro k
    rw [hr]
    calc (((2 : ℝ) ^ k) ^ cm)⁻¹
        = ((2 : ℝ) ^ ((k : ℝ) * cm))⁻¹ := by
          rw [← Real.rpow_natCast (2 : ℝ) k, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (-((k : ℝ) * cm)) := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ((2 : ℝ) ^ (-cm)) ^ k := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (-cm)) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
  have hpsi_bd : ∀ k θ, ‖psi k θ‖ ≤ Ab k := by
    intro k θ
    simp only [hpsi, hAb]
    by_cases hk : k < 2
    · simp only [hk, ↓reduceIte]
      simp
    · simp only [hk, ↓reduceIte]
      by_cases hθ : θ ∈ Set.Icc (0 : ℝ) 1
      · rw [if_pos hθ, ← map_sub, Complex.norm_conj]
        have h3 : 3 ≤ 2 ^ k := by
          have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          norm_num at h4 ⊢
          omega
        have hm := hmaj (2 ^ k) h3 θ hθ.1 hθ.2
        have hbase : (((2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
        rw [hbase] at hm
        have hCoefk : Cm * (((2 : ℝ) ^ k) ^ cm)⁻¹ = Cm * r ^ k := by rw [hpow k]
        rw [← hCoefk]
        exact hm
      · rw [if_neg hθ]
        simp only [norm_zero]
        positivity
  set S : ℝ := ∑' k, Ab k with hS
  have hSnn : 0 ≤ S := by rw [hS]; exact tsum_nonneg hAbnn
  set D : ℝ := 16 * A ^ 2 + 16 * S ^ 2 + 32 with hD
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  set C : ℝ := Real.sqrt D + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hCsq : D ≤ C ^ 2 := by
    rw [hC]
    nlinarith [Real.sq_sqrt hDnn, Real.sqrt_nonneg D]
  refine ⟨C, hCpos, ?_⟩
  intro g hg
  obtain ⟨s, hgs⟩ := hg
  set G : ℝ≥0∞ := ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2 : ℝ) ∂Measure.count with hG
  set P : ℝ → ℂ := fun θ => ∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (θ : ℂ)) with hP
  set W : ℤ → ℝ → ℂ := fun m θ => Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (θ : ℂ))) with hW
  set Mfun : ℕ → ℤ → ℂ := fun k m => ∫ θ in (0 : ℝ)..1,
      (starRingEnd ℂ (powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k) θ)) * P θ * W m θ with hMfun
  set Efun : ℕ → ℤ → ℂ := fun k m => ∫ θ in (0 : ℝ)..1,
      psi k θ * P θ * W m θ with hEfun
  -- the Fourier identity for the actual square-shift operator
  have hQfourier : ∀ k m, ((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k), g (m + (i : ℤ) ^ d)
      = ∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (powKernel d (2 ^ k) θ)) * P θ * W m θ := by
    intro k m
    have h := pow_shift_fourier_coeff_conj d g s hgs (2 ^ k) m
    have hcoef : (↑(((2 : ℝ) ^ k)⁻¹) : ℂ) = (((2 ^ k : ℕ) : ℂ))⁻¹ := by push_cast; rfl
    have hconv : (∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (powKernel d (2 ^ k) θ)) * P θ * W m θ)
        = (∫ θ in (0 : ℝ)..1, (((2 ^ k : ℕ) : ℂ))⁻¹ *
              (∑ i ∈ Finset.range (2 ^ k),
                Complex.exp (-(2 * Real.pi * Complex.I * (((i : ℝ) ^ d) * θ))))
            * (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℝ) * θ)))
            * Complex.exp (-(2 * Real.pi * Complex.I * ((m : ℝ) * θ)))) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      simp only [conj_powKernel d, hP, hW]
      have hpoly : (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (θ : ℂ)))
          = (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℝ) * θ))) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        push_cast
        ring
      have hexp : Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (θ : ℂ)))
          = Complex.exp (-(2 * Real.pi * Complex.I * ((m : ℝ) * θ))) := by
        congr 1
        push_cast
        ring
      rw [hpoly, hexp]
    rw [hconv, h, hcoef]
  -- the error symbol on the range of integration
  have hpsi_pt : ∀ k, 2 ≤ k → ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
      psi k θ = (starRingEnd ℂ (powKernel d (2 ^ k) θ) -
                 starRingEnd ℂ (powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k) θ)) := by
    intro k hk θ hθ
    have hθI : θ ∈ Set.Icc (0 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
    simp only [hpsi]
    rw [if_neg (by omega : ¬ (k < 2)), if_pos hθI]
  have hME : ∀ k, 2 ≤ k → ∀ m,
      (∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (powKernel d (2 ^ k) θ)) * P θ * W m θ)
        = Mfun k m + Efun k m := by
    intro k hk m
    rw [hMfun, hEfun]
    dsimp only
    have hPW : Continuous (fun θ : ℝ => P θ * W m θ) := by rw [hP, hW]; fun_prop
    have hN3 : 3 ≤ 2 ^ k := by
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      norm_num at h4 ⊢
      omega
    have hIntM : IntervalIntegrable
        (fun θ : ℝ => (starRingEnd ℂ (powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k) θ)) * P θ * W m θ)
        volume 0 1 :=
      IntervalIntegrable.congr (fun θ _ => by ring)
        (intervalIntegrable_powMajorArcModel_mul d hd hN3 hPW)
    have hE_eq : (∫ θ in (0 : ℝ)..1, psi k θ * P θ * W m θ)
        = (∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (powKernel d (2 ^ k) θ)) * P θ * W m θ)
          - (∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k) θ)) * P θ * W m θ) := by
      rw [show (∫ θ in (0 : ℝ)..1, psi k θ * P θ * W m θ)
            = ∫ θ in (0 : ℝ)..1,
              ((starRingEnd ℂ (powKernel d (2 ^ k) θ) -
                starRingEnd ℂ (powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k) θ)) * P θ * W m θ) from
          intervalIntegral.integral_congr (fun θ hθ => by rw [hpsi_pt k hk θ hθ])]
      rw [show (∫ θ in (0 : ℝ)..1,
              ((starRingEnd ℂ (powKernel d (2 ^ k) θ) -
                starRingEnd ℂ (powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k) θ)) * P θ * W m θ))
            = ∫ θ in (0 : ℝ)..1,
              ((starRingEnd ℂ (powKernel d (2 ^ k) θ) * P θ * W m θ) -
               (starRingEnd ℂ (powMajorArcModel d ((1 : ℝ) / 4) (2 ^ k) θ) * P θ * W m θ)) from
          intervalIntegral.integral_congr (fun θ _ => by ring)]
      rw [intervalIntegral.integral_sub]
      · refine Continuous.intervalIntegrable ?_ 0 1
        have hPc : Continuous P := by rw [hP]; fun_prop
        have hWc : Continuous (fun θ : ℝ => W m θ) := by rw [hW]; fun_prop
        exact ((Complex.continuous_conj.comp (continuous_powKernel d (2 ^ k))).mul hPc).mul hWc
      · exact hIntM
    rw [hE_eq]
    ring
  -- the pointwise maximal decomposition
  have hpoint : ∀ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k),
        g (m + (i : ℤ) ^ d)‖ₑ) ^ (2 : ℝ)
      ≤ (16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
        + 16 * ((‖g m‖ₑ) ^ (2 : ℝ) + (‖g (m + 1)‖ₑ) ^ (2 : ℝ)) := by
    intro m
    have hsplit : (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k),
          g (m + (i : ℤ) ^ d)‖ₑ)
        ≤ (⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ)
          + (‖g m‖ₑ + ‖g (m + 1)‖ₑ) := by
      refine iSup_le (fun k => ?_)
      by_cases hk : k < 2
      · have hcoef : ‖(↑(((2 : ℝ) ^ k)⁻¹) : ℂ)‖ₑ ≤ 1 := by
          have h : ‖(↑(((2 : ℝ) ^ k)⁻¹) : ℂ)‖ₑ = ‖(((2 : ℝ) ^ k)⁻¹ : ℝ)‖ₑ := by
            rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
          rw [h, Real.enorm_eq_ofReal_abs,
              abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹), ENNReal.ofReal_le_one,
              inv_le_one₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
          exact one_le_pow₀ (by norm_num)
        have hsum : ‖∑ i ∈ Finset.range (2 ^ k), g (m + (i : ℤ) ^ d)‖ₑ
            ≤ ‖g m‖ₑ + ‖g (m + 1)‖ₑ := by
          refine le_trans (enorm_sum_le _ _) ?_
          have h2 : 2 ^ k = 1 ∨ 2 ^ k = 2 := by interval_cases k <;> norm_num
          rcases h2 with h2 | h2
          · rw [h2, Finset.sum_range_one]
            have h0 : (↑(0:ℕ) : ℤ) ^ d = (0:ℤ) := by
              rw [show (↑(0:ℕ) : ℤ) = (0:ℤ) by norm_num, zero_pow (by omega : d ≠ 0)]
            rw [h0, add_zero]
            simpa using le_self_add (a := ‖g m‖ₑ) (b := ‖g (m + 1)‖ₑ)
          · rw [h2, Finset.sum_range_succ, Finset.sum_range_one]
            have h0 : (↑(0:ℕ) : ℤ) ^ d = (0:ℤ) := by
              rw [show (↑(0:ℕ) : ℤ) = (0:ℤ) by norm_num, zero_pow (by omega : d ≠ 0)]
            have h1 : (↑(1:ℕ) : ℤ) ^ d = (1:ℤ) := by
              rw [show (↑(1:ℕ) : ℤ) = (1:ℤ) by norm_num, one_pow]
            rw [h0, h1, add_zero]
        calc ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k), g (m + (i : ℤ) ^ d)‖ₑ
            = ‖(↑(((2 : ℝ) ^ k)⁻¹) : ℂ)‖ₑ
              * ‖∑ i ∈ Finset.range (2 ^ k), g (m + (i : ℤ) ^ d)‖ₑ := enorm_mul _ _
          _ ≤ 1 * (‖g m‖ₑ + ‖g (m + 1)‖ₑ) := mul_le_mul' hcoef hsum
          _ = ‖g m‖ₑ + ‖g (m + 1)‖ₑ := one_mul _
          _ ≤ (⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) + (‖g m‖ₑ + ‖g (m + 1)‖ₑ) :=
              le_add_of_nonneg_left (by positivity)
      · have hk2 : 2 ≤ k := by omega
        rw [hQfourier k m, hME k hk2 m]
        calc ‖Mfun k m + Efun k m‖ₑ ≤ ‖Mfun k m‖ₑ + ‖Efun k m‖ₑ := enorm_add_le _ _
          _ ≤ (⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) :=
              add_le_add (le_iSup (fun j : ℕ => ‖Mfun j m‖ₑ) k) (le_iSup (fun j : ℕ => ‖Efun j m‖ₑ) k)
          _ ≤ (⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) + (‖g m‖ₑ + ‖g (m + 1)‖ₑ) :=
              le_self_add
    have h1 := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      ((⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ)) (‖g m‖ₑ + ‖g (m + 1)‖ₑ)
      (p := 2) (by norm_num)
    have h2 := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      (⨆ k : ℕ, ‖Mfun k m‖ₑ) (⨆ k : ℕ, ‖Efun k m‖ₑ) (p := 2) (by norm_num)
    have h3 := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      (‖g m‖ₑ) (‖g (m + 1)‖ₑ) (p := 2) (by norm_num)
    have h4 : ((2 : ℝ≥0∞) ^ (2 : ℝ)) = 4 := by norm_num [ENNReal.rpow_natCast]
    rw [h4] at h1 h2 h3
    calc (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k), g (m + (i : ℤ) ^ d)‖ₑ) ^ (2 : ℝ)
        ≤ ((⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) + (‖g m‖ₑ + ‖g (m + 1)‖ₑ)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hsplit (by norm_num)
      _ ≤ 4 * (((⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ)) ^ (2 : ℝ)
            + (‖g m‖ₑ + ‖g (m + 1)‖ₑ) ^ (2 : ℝ)) := h1
      _ ≤ 4 * (4 * ((⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
            + (‖g m‖ₑ + ‖g (m + 1)‖ₑ) ^ (2 : ℝ)) := by
          refine mul_le_mul_right ?_ 4
          exact add_le_add h2 le_rfl
      _ ≤ 4 * (4 * ((⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
            + 4 * ((‖g m‖ₑ) ^ (2 : ℝ) + (‖g (m + 1)‖ₑ) ^ (2 : ℝ))) := by
          refine mul_le_mul_right ?_ 4
          exact add_le_add le_rfl h3
      _ = 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)
            + 16 * ((‖g m‖ₑ) ^ (2 : ℝ) + (‖g (m + 1)‖ₑ) ^ (2 : ℝ)) := by ring
  -- measurability of the pieces
  have hMmeas : Measurable (fun m : ℤ => 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)) := by
    refine Measurable.const_mul ?_ 16
    exact (Measurable.iSup (fun k => (measurable_of_countable (fun m : ℤ => Mfun k m)).enorm)).pow_const 2
  have hEmeas : Measurable (fun m : ℤ => 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)) := by
    refine Measurable.const_mul ?_ 16
    exact (Measurable.iSup (fun k => (measurable_of_countable (fun m : ℤ => Efun k m)).enorm)).pow_const 2
  have hxy : Measurable (fun m : ℤ => 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
      + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)) := hMmeas.add hEmeas
  have hameas : Measurable (fun m : ℤ => (‖g m‖ₑ) ^ (2 : ℝ)) :=
    (measurable_of_countable (fun m : ℤ => g m)).enorm.pow_const 2
  have hbmeas : Measurable (fun m : ℤ => (‖g (m + 1)‖ₑ) ^ (2 : ℝ)) :=
    (measurable_of_countable (fun m : ℤ => g (m + 1))).enorm.pow_const 2
  -- the bounds coming from the hypothesis and from the family lemma
  have hSm : ∫⁻ m : ℤ, (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count
      ≤ ENNReal.ofReal (A ^ 2) * G := by
    rw [hMfun, hP, hW, hG]
    exact hAbound g s hgs
  have hSe : ∫⁻ m : ℤ, (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count
      ≤ ENNReal.ofReal (S ^ 2) * G := by
    have hfam := Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family
      psi Ab hAbnn hpsi_meas hpsi_bd hAb_summable g s hgs
    rw [hEfun, hP, hW, hS, hG]
    exact hfam
  -- integral identities
  have hIa : ∫⁻ m : ℤ, 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count
      = 16 * (∫⁻ m : ℤ, (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count) :=
    lintegral_const_mul' 16 _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)
  have hIb : ∫⁻ m : ℤ, 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count
      = 16 * (∫⁻ m : ℤ, (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count) :=
    lintegral_const_mul' 16 _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)
  have hIc : ∫⁻ m : ℤ, 16 * ((‖g m‖ₑ) ^ (2 : ℝ) + (‖g (m + 1)‖ₑ) ^ (2 : ℝ)) ∂Measure.count
      = 16 * (G + G) := by
    rw [lintegral_const_mul' 16 _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)]
    congr 1
    rw [lintegral_add_left hameas, ← hG,
        lintegral_count_add_one (fun m : ℤ => (‖g m‖ₑ) ^ (2 : ℝ)), ← hG]
  have hIsum : ∫⁻ m : ℤ, ((16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
          + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
        + 16 * ((‖g m‖ₑ) ^ (2 : ℝ) + (‖g (m + 1)‖ₑ) ^ (2 : ℝ))) ∂Measure.count
      = (∫⁻ m : ℤ, (16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
            + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)) ∂Measure.count)
        + (∫⁻ m : ℤ, 16 * ((‖g m‖ₑ) ^ (2 : ℝ) + (‖g (m + 1)‖ₑ) ^ (2 : ℝ)) ∂Measure.count) :=
    lintegral_add_left hxy _
  have hIxy : ∫⁻ m : ℤ, (16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
          + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)) ∂Measure.count
      = (∫⁻ m : ℤ, 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count)
        + (∫⁻ m : ℤ, 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count) :=
    lintegral_add_left hMmeas _
  -- coefficient comparison
  have hcoe : (16 : ℝ≥0∞) * ENNReal.ofReal (A ^ 2) + 16 * ENNReal.ofReal (S ^ 2) + 32
      ≤ ENNReal.ofReal (C ^ 2) := by
    have h1 : ENNReal.ofReal D
        = 16 * ENNReal.ofReal (A ^ 2) + 16 * ENNReal.ofReal (S ^ 2) + 32 := by
      rw [hD]
      rw [ENNReal.ofReal_add (by positivity) (by norm_num : (0 : ℝ) ≤ 32),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
          ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [← h1]
    exact ENNReal.ofReal_le_ofReal hCsq
  calc ∫⁻ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k),
          g (m + (i : ℤ) ^ d)‖ₑ) ^ (2 : ℝ) ∂Measure.count
      ≤ ∫⁻ m : ℤ, ((16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
            + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
          + 16 * ((‖g m‖ₑ) ^ (2 : ℝ) + (‖g (m + 1)‖ₑ) ^ (2 : ℝ))) ∂Measure.count :=
        lintegral_mono hpoint
    _ = (16 * (∫⁻ m : ℤ, (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count)
          + 16 * (∫⁻ m : ℤ, (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂Measure.count))
          + 16 * (G + G) := by
        rw [hIsum, hIxy, hIa, hIb, hIc]
    _ ≤ (16 * (ENNReal.ofReal (A ^ 2) * G) + 16 * (ENNReal.ofReal (S ^ 2) * G)) + 16 * (G + G) := by
        exact add_le_add (add_le_add (mul_le_mul_right hSm 16) (mul_le_mul_right hSe 16)) le_rfl
    _ = (16 * ENNReal.ofReal (A ^ 2) + 16 * ENNReal.ofReal (S ^ 2) + 32) * G := by ring
    _ ≤ ENNReal.ofReal (C ^ 2) * G := mul_le_mul_left hcoe G



/-! ## The model maximal estimate and the target -/

/-- **The `ℓ²` maximal estimate for the major-arc model of the `d`-th power kernel.**
Assembled from the circle-form neighbourhood maximal (`CircleNeighborhoodMaximal`), whose
the last analytic input is the fixed-bump smooth-window maximal estimate
`FWS.LastMile.bump_smoothOp_maximal_l2`. -/
theorem pow_model_maximal (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖∫ θ in (0:ℝ)..1,
            (starRingEnd ℂ (powMajorArcModel d ((1:ℝ)/4) (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m:ℂ) * (θ:ℂ)))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  have H : CircleNeighborhoodMaximal :=
    circleNeighborhoodMaximal_of_multiplierMaximal
      (LThOp.realLineMultiplierMaximal_of_sepWinTarget
        (Commons.Analysis.Fourier.SepWin.target_of_components
          (Commons.Analysis.Fourier.SepWin.smoothWindowMaximal_of_inline (by
            obtain ⟨C, hCpos, hC⟩ := FWPortBump.smooth_window_of_fixed_bump
              FWS.LastMile.bump_smoothOp_maximal_l2
            refine ⟨C, hCpos, fun K lam hlam φ hφ h1 h0 hbd f hf => ?_⟩
            have := hC K lam hlam φ hφ h1 h0 hbd f hf
            simpa only [Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm] using this))))
  obtain ⟨A, hA, hAb⟩ := pow_model_maximal_of_block d hd (pow_block_maximal_of_circle d hd H)
  exact ⟨A, hA, fun g s hgs => by simpa only [powTkMax] using hAb g s hgs⟩

/-- **The `ℓ²` maximal inequality for the pure `d`-th power density kernels.**  For every
`d ≥ 2` there is `C` with
`∫⁻_m (⨆_N ‖N⁻¹ ∑_{i<N} g (m + i^d)‖)² dcount ≤ C² ∫⁻_m ‖g m‖² dcount`
for every finitely supported `g : ℕ → ℝ`. -/
theorem pure_power_kernel_maximal_l2 (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + i ^ d)‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ m, ‖g m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
  pow_shift_transfer d
    (pow_dyadic_reduction_z d (pow_dyadic_of_model d hd (pow_model_maximal d hd)))

end

end Commons.Analysis.ExponentialSums
