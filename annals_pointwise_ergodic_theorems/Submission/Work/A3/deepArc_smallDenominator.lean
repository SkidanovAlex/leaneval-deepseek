import Mathlib
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality
import Submission.Commons.Analysis.ExponentialSums.poly_phase_residue_split
import Submission.Work.A3.expSum_pure_fresnel
import Submission.Work.A3.block_deep_condition
import Submission.Work.A3.final_exponent_bound

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section


lemma Qreal_eval_intCast (Q : Polynomial ℤ) (n : ℤ) :
    (Qreal Q).eval ((n : ℝ)) = (((Q.eval n : ℤ)) : ℝ) := by
  have h := Polynomial.eval₂_at_apply (f := Int.castRingHom ℝ) (r := n) (p := Q)
  simpa [Qreal, Polynomial.eval_map] using h

lemma Qreal_natDegree (Q : Polynomial ℤ) : (Qreal Q).natDegree = Q.natDegree := by
  rw [Qreal, Polynomial.natDegree_map_eq_of_injective (Int.cast_injective)]

lemma Qreal_leadingCoeff (Q : Polynomial ℤ) :
    (Qreal Q).leadingCoeff = ((Q.leadingCoeff : ℤ) : ℝ) := by
  rw [Qreal, Polynomial.leadingCoeff_map_of_injective (Int.cast_injective)]
  rfl

/-- `a^u * (a^{-v})^y = a^{u - v*y}` for `0 < a`. -/
lemma rpow_neg_pow_mul (a : ℝ) (ha : 0 < a) (u v y : ℝ) :
    a ^ u * (a ^ (-v)) ^ y = a ^ (u - v * y) := by
  have h1 : a ^ (-v) = (a ^ v)⁻¹ := Real.rpow_neg ha.le v
  rw [h1]
  have h2 : (a ^ v)⁻¹ ^ y = ((a ^ v) ^ y)⁻¹ := Real.inv_rpow (Real.rpow_nonneg ha.le v) y
  rw [h2]
  have h3 : (a ^ v) ^ y = a ^ (v * y) := (Real.rpow_mul ha.le v y).symm
  rw [h3]
  have h4 : (a ^ (v * y))⁻¹ = a ^ (-(v * y)) := (Real.rpow_neg ha.le (v * y)).symm
  rw [h4]
  rw [← Real.rpow_add ha]
  congr 1

/-- Approximation of a real number `c` with `|c| ≤ 1/2` by a unit fraction `a/q`
(`|a| = 1`, `q ≥ 1`) with error at most `2/q²`. -/
lemma exists_unit_fraction_approx {c : ℝ} (hc : c ≠ 0) (hc1 : |c| ≤ 1 / 2) :
    ∃ (a : ℤ) (q : ℕ), 1 ≤ q ∧ Int.gcd a (q : ℤ) = 1 ∧
      |c - (a : ℝ) / (q : ℝ)| ≤ 2 / (q : ℝ) ^ 2 ∧
      1 / (q : ℝ) ≤ |c| ∧ (q : ℝ) ≤ 2 / |c| := by
  have hγ0 : 0 < |c| := abs_pos.mpr hc
  have hγ1 : |c| ≤ 1 := by linarith
  set q : ℕ := Nat.ceil (1 / |c|) with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    exact Nat.one_le_ceil_iff.mpr (by positivity)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hle : 1 / |c| ≤ (q : ℝ) := by rw [hqdef]; exact Nat.le_ceil _
  have hlt : (q : ℝ) < 1 / |c| + 1 := by
    rw [hqdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hupper : 1 / (q : ℝ) ≤ |c| := by
    rw [div_le_iff₀ hqpos]
    have h := (div_le_iff₀ hγ0).mp hle
    linarith [h]
  have hq2 : (q : ℝ) ≤ 2 / |c| := by
    have h2 : 2 ≤ 1 / |c| := by rw [le_div_iff₀ hγ0]; linarith
    have h3 : (2 : ℝ) / |c| = 2 * (1 / |c|) := by ring
    rw [h3]
    linarith
  have hlower : |c| / (1 + |c|) ≤ 1 / (q : ℝ) := by
    have h1 : 1 / (1 / |c| + 1) < 1 / (q : ℝ) := one_div_lt_one_div_of_lt (by positivity) hlt
    have h2 : 1 / (1 / |c| + 1) = |c| / (1 + |c|) := by
      field_simp
    linarith [h1, h2.le]
  have hkey : |(|c|) - 1 / (q : ℝ)| ≤ 2 / (q : ℝ) ^ 2 := by
    have hsub : 0 ≤ |c| - 1 / (q : ℝ) := by linarith
    rw [abs_of_nonneg hsub]
    have hstep : |c| - 1 / (q : ℝ) ≤ |c| - |c| / (1 + |c|) := by linarith
    have hval : |c| - |c| / (1 + |c|) = |c| ^ 2 / (1 + |c|) := by
      field_simp
      ring
    have hsq : (|c| / (1 + |c|)) ^ 2 ≤ (1 / (q : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlower 2
    have hone : (1 / (q : ℝ)) ^ 2 = 1 / (q : ℝ) ^ 2 := by rw [div_pow]; norm_num
    rw [hval] at hstep
    have hfin : |c| ^ 2 / (1 + |c|) ≤ 2 / (q : ℝ) ^ 2 := by
      have hq2pos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
      have h1 : |c| ^ 2 ≤ (1 + |c|) ^ 2 * (1 / (q : ℝ) ^ 2) := by
        have h := hsq
        rw [div_pow, hone, div_le_iff₀ (by positivity : (0:ℝ) < (1 + |c|) ^ 2)] at h
        linarith [h]
      have h2 : |c| ^ 2 / (1 + |c|) ≤ (1 + |c|) * (1 / (q : ℝ) ^ 2) := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + |c|)]
        nlinarith [h1]
      have h3 : (1 + |c|) * (1 / (q : ℝ) ^ 2) ≤ 2 * (1 / (q : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      have h4 : (2 : ℝ) * (1 / (q : ℝ) ^ 2) = 2 / (q : ℝ) ^ 2 := by ring
      linarith [h2, h3, h4]
    linarith [hstep, hfin]
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · refine ⟨-1, q, hq1, ?_, ?_, hupper, hq2⟩
    · rw [Int.gcd_eq_natAbs]
      norm_num [Int.natAbs_neg]
    · have harg : c - ((-1 : ℤ) : ℝ) / (q : ℝ) = -(|c| - 1 / (q : ℝ)) := by
        rw [abs_of_neg hneg]
        push_cast
        ring
      rw [harg, abs_neg]
      exact hkey
  · refine ⟨1, q, hq1, ?_, ?_, hupper, hq2⟩
    · rw [Int.gcd_one_left]
    · have harg : c - ((1 : ℤ) : ℝ) / (q : ℝ) = |c| - 1 / (q : ℝ) := by
        rw [abs_of_pos hpos]
        norm_num
      rw [harg]
      exact hkey

/-- **Weyl's inequality on a block.** -/
lemma blockWeyl_bound (d : ℕ) (hd : 2 ≤ d) {C₀ c₀ φ : ℝ} (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (hφ : 0 < φ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (f : Polynomial ℝ) (x₀ : ℤ), 2 ≤ M →
        f.natDegree = d →
        |f.leadingCoeff| ≤ 1 / 2 →
        |f.leadingCoeff| * (M : ℝ) ≤ C₀ →
        c₀ * (M : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) ≤
          (2 * Real.pi * (d.factorial : ℝ)) * |f.leadingCoeff| * (M : ℝ) ^ d →
        ‖∑ x ∈ Finset.range M,
            Complex.exp (((2 * Real.pi * f.eval ((x₀ : ℝ) + (x : ℝ)) : ℝ) : ℂ) * Complex.I)‖
          ≤ C * (M : ℝ) ^ (1 - (2 : ℝ) ^ (1 - (d : ℝ)) * ((d : ℝ) / ((d : ℝ) + 1)) + φ) := by
  obtain ⟨Cw, hCwpos, hCw⟩ :=
    Commons.Analysis.ExponentialSums.weyl_inequality d (by omega) (ε := φ) hφ (t := 2)
      (by norm_num)
  set K₁ : ℝ := 2 * C₀ + 3 + 4 * Real.pi * (d.factorial : ℝ) / c₀ with hK₁def
  have hK₁pos : 0 < K₁ := by rw [hK₁def]; positivity
  refine ⟨Cw * K₁ ^ ((2 : ℝ) ^ (1 - (d : ℝ))), by positivity, ?_⟩
  intro M f x₀ hM hdeg hlc1 hlc2 hdeep
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hγpos : 0 < |f.leadingCoeff| := by
    refine abs_pos.mpr ?_
    intro h0
    have hf0 : f = 0 := by
      by_contra hne
      exact Polynomial.leadingCoeff_ne_zero.mpr hne h0
    rw [hf0] at hdeg
    simp at hdeg
    omega
  obtain ⟨a, q, hq1, hgcd, happ, hqup, hq2le⟩ :=
    exists_unit_fraction_approx (c := f.leadingCoeff) (abs_pos.mp hγpos) hlc1
  have hq1Z : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq1
  have hqR : (((q : ℤ)) : ℝ) = (q : ℝ) := by push_cast; ring
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hweyl := hCw x₀ M a (q : ℤ) f hq1Z hgcd hdeg (by rw [hqR]; exact happ)
  set X : ℝ := (M : ℝ) ^ (-((d : ℝ) / ((d : ℝ) + 1))) with hXdef
  have hXpos : 0 < X := Real.rpow_pos_of_pos hMpos _
  have hd2' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- (a) `1/M ≤ X`
  have h_inv : (M : ℝ)⁻¹ ≤ X := by
    rw [hXdef]
    have hexp : (-1 : ℝ) ≤ -((d : ℝ) / ((d : ℝ) + 1)) := by
      have h2 : (d : ℝ) / ((d : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith
    have := Real.rpow_le_rpow_of_exponent_le hM1 hexp
    rwa [Real.rpow_neg_one] at this
  -- (b) `1/M^{d-1} ≤ X`
  have h_inv2 : ((M : ℝ) ^ (d - 1))⁻¹ ≤ X := by
    have hcast : (M : ℝ) ^ (d - 1) = (M : ℝ) ^ (((d - 1 : ℕ)) : ℝ) := by
      rw [Real.rpow_natCast]
    have hexp2 : -(((d - 1 : ℕ)) : ℝ) ≤ -((d : ℝ) / ((d : ℝ) + 1)) := by
      have h1 : (((d - 1 : ℕ)) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
      rw [h1]
      have h2 : (d : ℝ) / ((d : ℝ) + 1) ≤ (d : ℝ) - 1 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hd2']
      linarith
    calc ((M : ℝ) ^ (d - 1))⁻¹ = ((M : ℝ) ^ (((d - 1 : ℕ)) : ℝ))⁻¹ := by rw [hcast]
      _ = (M : ℝ) ^ (-(((d - 1 : ℕ)) : ℝ)) := (Real.rpow_neg hMpos.le _).symm
      _ ≤ (M : ℝ) ^ (-((d : ℝ) / ((d : ℝ) + 1))) :=
          Real.rpow_le_rpow_of_exponent_le hM1 hexp2
      _ = X := hXdef.symm
  have h_lc : |f.leadingCoeff| ≤ C₀ * (M : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hMpos]
    exact hlc2
  have hterm1 : 2 / (((q : ℤ)) : ℝ) ≤ 2 * C₀ * X := by
    rw [hqR]
    have h1 : 2 / (q : ℝ) ≤ 2 * |f.leadingCoeff| := by
      rw [show (2 : ℝ) / (q : ℝ) = 2 * (1 / (q : ℝ)) by ring]
      nlinarith [hqup]
    nlinarith [h1, h_lc, h_inv, hXpos, hC₀]
  have hterm2 : (((q : ℤ)) : ℝ) / ((M : ℝ) ^ d)
      ≤ (4 * Real.pi * (d.factorial : ℝ) / c₀) * X := by
    rw [hqR]
    have h1 : (q : ℝ) / ((M : ℝ) ^ d) ≤ (2 / |f.leadingCoeff|) / ((M : ℝ) ^ d) :=
      div_le_div_of_nonneg_right hq2le (by positivity)
    have h2 : (2 / |f.leadingCoeff|) / ((M : ℝ) ^ d)
        = 2 / (|f.leadingCoeff| * ((M : ℝ) ^ d)) := by field_simp
    have h3 : (2 : ℝ) / (|f.leadingCoeff| * ((M : ℝ) ^ d))
        ≤ (4 * Real.pi * (d.factorial : ℝ) / c₀) * X := by
      rw [hXdef, Real.rpow_neg hMpos.le]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < |f.leadingCoeff| * ((M : ℝ) ^ d))]
      rw [show (4 * Real.pi * (d.factorial : ℝ) / c₀) * ((M : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))⁻¹
            * (|f.leadingCoeff| * ((M : ℝ) ^ d))
          = 4 * Real.pi * (d.factorial : ℝ) * (|f.leadingCoeff| * ((M : ℝ) ^ d))
              / (c₀ * (M : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))) by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < c₀ * (M : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))]
      linarith [hdeep]
    linarith [h1, h2.le, h3]
  have hterm3 : 1 / (M : ℝ) ≤ X := by simpa [one_div] using h_inv
  have hterm4 : 2 / ((M : ℝ) ^ (d - 1)) ≤ 2 * X := by
    rw [show (2 : ℝ) / ((M : ℝ) ^ (d - 1)) = 2 * ((M : ℝ) ^ (d - 1))⁻¹ by field_simp]
    nlinarith [h_inv2]
  have hBnn : 0 ≤ 2 / (((q : ℤ)) : ℝ) + 1 / (M : ℝ) + 2 / (M : ℝ) ^ (d - 1)
      + (((q : ℤ)) : ℝ) / (M : ℝ) ^ d := by positivity
  have hB : 2 / (((q : ℤ)) : ℝ) + 1 / (M : ℝ) + 2 / (M : ℝ) ^ (d - 1) + (((q : ℤ)) : ℝ) / (M : ℝ) ^ d
      ≤ K₁ * X := by
    have hsum : 2 / (((q : ℤ)) : ℝ) + 1 / (M : ℝ) + 2 / (M : ℝ) ^ (d - 1)
        + (((q : ℤ)) : ℝ) / (M : ℝ) ^ d
        ≤ 2 * C₀ * X + X + 2 * X + (4 * Real.pi * (d.factorial : ℝ) / c₀) * X := by
      linarith [hterm1, hterm2, hterm3, hterm4]
    have hfin : 2 * C₀ * X + X + 2 * X + (4 * Real.pi * (d.factorial : ℝ) / c₀) * X
        = K₁ * X := by rw [hK₁def]; ring
    linarith [hsum, hfin.le]
  calc ‖∑ x ∈ Finset.range M,
        Complex.exp (((2 * Real.pi * f.eval ((x₀ : ℝ) + (x : ℝ)) : ℝ) : ℂ) * Complex.I)‖
      ≤ Cw * (M : ℝ) ^ (1 + φ) *
          (2 / ((q : ℤ) : ℝ) + 1 / (M : ℝ) + 2 / (M : ℝ) ^ (d - 1) + ((q : ℤ) : ℝ) / (M : ℝ) ^ d)
            ^ ((2 : ℝ) ^ (1 - (d : ℝ))) := hweyl
    _ ≤ Cw * (M : ℝ) ^ (1 + φ) * (K₁ * X) ^ ((2 : ℝ) ^ (1 - (d : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow hBnn hB (Real.rpow_nonneg (by norm_num) _)
    _ = (Cw * K₁ ^ ((2 : ℝ) ^ (1 - (d : ℝ)))) *
          (M : ℝ) ^ (1 - (2 : ℝ) ^ (1 - (d : ℝ)) * ((d : ℝ) / ((d : ℝ) + 1)) + φ) := by
        calc Cw * (M : ℝ) ^ (1 + φ) * (K₁ * X) ^ ((2 : ℝ) ^ (1 - (d : ℝ)))
            = Cw * (M : ℝ) ^ (1 + φ)
                * (K₁ ^ ((2 : ℝ) ^ (1 - (d : ℝ))) * X ^ ((2 : ℝ) ^ (1 - (d : ℝ)))) := by
              rw [Real.mul_rpow hK₁pos.le hXpos.le]
          _ = Cw * (M : ℝ) ^ (1 + φ)
                * (K₁ ^ ((2 : ℝ) ^ (1 - (d : ℝ)))
                    * ((M : ℝ) ^ (-((d : ℝ) / ((d : ℝ) + 1)))) ^ ((2 : ℝ) ^ (1 - (d : ℝ)))) := by
              rw [hXdef]
          _ = Cw * K₁ ^ ((2 : ℝ) ^ (1 - (d : ℝ)))
                * ((M : ℝ) ^ (1 + φ)
                    * ((M : ℝ) ^ (-((d : ℝ) / ((d : ℝ) + 1)))) ^ ((2 : ℝ) ^ (1 - (d : ℝ)))) := by
              ring
          _ = Cw * K₁ ^ ((2 : ℝ) ^ (1 - (d : ℝ)))
                * (M : ℝ) ^ ((1 + φ) - ((d : ℝ) / ((d : ℝ) + 1)) * ((2 : ℝ) ^ (1 - (d : ℝ)))) := by
              rw [rpow_neg_pow_mul (M : ℝ) hMpos (1 + φ) ((d : ℝ) / ((d : ℝ) + 1))
                ((2 : ℝ) ^ (1 - (d : ℝ)))]
          _ = (Cw * K₁ ^ ((2 : ℝ) ^ (1 - (d : ℝ)))) *
                (M : ℝ) ^ (1 - (2 : ℝ) ^ (1 - (d : ℝ)) * ((d : ℝ) / ((d : ℝ) + 1)) + φ) := by
              have hexp : (1 : ℝ) + φ - (d : ℝ) / ((d : ℝ) + 1) * (2 : ℝ) ^ (1 - (d : ℝ))
                  = 1 - (2 : ℝ) ^ (1 - (d : ℝ)) * ((d : ℝ) / ((d : ℝ) + 1)) + φ := by ring
              rw [hexp]


/-- Reindexing `∑_{n ∈ [1,N]}` as `∑_{x < N}` with `n = 1 + x`. -/
lemma sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, g n) = ∑ x ∈ Finset.range N, g (1 + x) := by
  have h : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [h, Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_cancel]

/-- Factorisation of one term of the residue decomposition: the `a/q`-part of the phase is
`q`-periodic. -/
lemma exp_factor_block (Q : Polynomial ℤ) (a : ℤ) (β : ℝ) (q : ℕ) (θ : ℝ)
    (hθ : θ = (a : ℝ) / (q : ℝ) + β) (hq : 1 ≤ q) (r p : ℕ) :
    Complex.exp (-(2 * Real.pi * Complex.I *
        (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ) * θ)))
      = Complex.exp (-(2 * Real.pi * Complex.I *
          (((a : ℝ) / (q : ℝ)) * ((Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ))))
        * Complex.exp (-(2 * Real.pi * Complex.I *
          (β * ((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ)))) := by
  subst hθ
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hdvd : (q : ℤ) ∣ Q.eval (((1 + (p * q + r) : ℕ)) : ℤ) - Q.eval ((1 + r : ℕ) : ℤ) := by
    have h := Polynomial.sub_dvd_eval_sub (((1 + (p * q + r) : ℕ)) : ℤ) (((1 + r : ℕ)) : ℤ) Q
    have h2 : (((1 + (p * q + r) : ℕ)) : ℤ) - (((1 + r : ℕ)) : ℤ) = (p : ℤ) * (q : ℤ) := by
      push_cast; ring
    rw [h2] at h
    exact dvd_trans (Dvd.intro (p : ℤ) (by ring)) h
  obtain ⟨t, ht⟩ := hdvd
  have hAB : (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ))
      - (((Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ)) = (q : ℝ) * (t : ℝ) := by
    have hcast : (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) - Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ))
        = ((q : ℤ) : ℝ) * ((t : ℤ) : ℝ) := by rw [ht]; push_cast; ring
    have hABz : (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) - Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ))
        = (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ))
          - (((Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ)) := by push_cast; ring
    rw [hABz, show ((q : ℤ) : ℝ) = (q : ℝ) by push_cast; ring] at hcast
    exact hcast
  have hqa : ((a : ℝ) / (q : ℝ)) * ((q : ℝ) * (t : ℝ)) = (a : ℝ) * (t : ℝ) := by
    field_simp
  have hreal : (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ)) * ((a : ℝ) / (q : ℝ) + β)
      = ((a : ℝ) / (q : ℝ)) * (((Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ))
        + β * (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ)) + (a : ℝ) * (t : ℝ) := by
    have hdif : (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ)) * ((a : ℝ) / (q : ℝ) + β)
        - (((a : ℝ) / (q : ℝ)) * (((Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ))
          + β * (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ)))
        = ((a : ℝ) / (q : ℝ)) * ((((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ))
            - (((Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ))) := by ring
    have hval : (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ)) * ((a : ℝ) / (q : ℝ) + β)
        - (((a : ℝ) / (q : ℝ)) * (((Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ))
          + β * (((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ))) = (a : ℝ) * (t : ℝ) := by
      rw [hdif, hAB, hqa]
    linarith [hval]
  have hc := congrArg ((↑) : ℝ → ℂ) hreal
  push_cast at hc
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(a * t), ?_⟩
  push_cast
  rw [hc]
  ring

lemma expSum_residue_split_gen (Q : Polynomial ℤ) (N q : ℕ) (a : ℤ) (β : ℝ) (θ : ℝ)
    (hθ : θ = (a : ℝ) / (q : ℝ) + β) (hq : 1 ≤ q) :
    Work.A3.expSum Q N θ
      = ∑ r ∈ Finset.range q,
          Complex.exp (-(2 * Real.pi * Complex.I *
            (((a : ℝ) / (q : ℝ)) * ((Q.eval ((1 + r : ℕ) : ℤ) : ℤ) : ℝ))))
          * (∑ p ∈ Finset.range ((N + q - 1 - r) / q),
              Complex.exp (-(2 * Real.pi * Complex.I *
                (β * ((Q.eval ((1 + (p * q + r) : ℕ) : ℤ) : ℤ) : ℝ))))) := by
  rw [expSum]
  rw [sum_Icc_one_eq_range (g := (fun n : ℕ => Complex.exp (-(2 * Real.pi * Complex.I *
      (((Q.eval (n : ℤ) : ℤ) : ℝ) * θ))))) N]
  rw [Commons.Analysis.ExponentialSums.sum_range_residue_split
      (fun x : ℕ => Complex.exp (-(2 * Real.pi * Complex.I *
        (((Q.eval (((1 + x : ℕ)) : ℤ) : ℤ) : ℝ) * θ)))) N q (by omega)]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  exact exp_factor_block Q a β q θ hθ hq r p


/-- Bookkeeping bound for the block decomposition, with no hypothesis on the leading
coefficient `ℓ`: the hypothesis `N ≥ 16(ℓ+1)^4 + 64` already forces `2ℓ qn ≤ N`. -/
lemma block_coeff_bound_local (d : ℕ) (hd : 2 ≤ d) {ℓ qn N β Mr : ℝ}
    (hℓpos : 0 < ℓ) (hqn1 : 1 ≤ qn) (hN : 16 * (ℓ + 1) ^ 4 + 64 ≤ N)
    (hqn_sq : qn * qn ≤ N) (hMr2 : 2 ≤ Mr) (hMrN : Mr ≤ 2 * N / qn)
    (hβup : |β| ≤ 1 / (qn * N ^ ((d : ℝ) / 2))) :
    |β| * ℓ * qn ^ d ≤ 1 / 2 ∧ |β| * ℓ * qn ^ d * Mr ≤ 2 * ℓ := by
  have hℓ0 : (0 : ℝ) ≤ ℓ := le_of_lt hℓpos
  have hqn0 : (0 : ℝ) < qn := lt_of_lt_of_le zero_lt_one hqn1
  have hqn0' : (0 : ℝ) ≤ qn := le_of_lt hqn0
  have hNge : (64 : ℝ) ≤ N := by
    have h4 : (0 : ℝ) ≤ (ℓ + 1) ^ 4 := by positivity
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  set S : ℝ := Real.sqrt N with hSdef
  have hSnn : 0 ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg N
  have hSpos : 0 < S := by rw [hSdef]; exact Real.sqrt_pos_of_pos hNpos
  have hS2 : S ^ 2 = N := by rw [hSdef]; exact Real.sq_sqrt (le_of_lt hNpos)
  have hSge2 : 2 ≤ S := by
    rw [hSdef]
    exact (Real.le_sqrt (by norm_num) (le_of_lt hNpos)).mpr (by nlinarith)
  have hqnS : qn ≤ S := by
    have h := Real.sqrt_le_sqrt hqn_sq
    rw [Real.sqrt_mul_self hqn0', ← hSdef] at h
    exact h
  -- the key consequence of `N ≥ 16(ℓ+1)^4 + 64`:  `2(ℓ+1) ≤ S`
  have h2l1 : 2 * (ℓ + 1) ≤ S := by
    have h16 : 16 * (ℓ + 1) ^ 4 ≤ S ^ 2 := by
      rw [hS2]
      linarith [hN]
    have h4 : 4 * (ℓ + 1) ^ 2 ≤ S := by
      have hsq : (4 * (ℓ + 1) ^ 2) ^ 2 ≤ S ^ 2 := by
        rw [show (4 * (ℓ + 1) ^ 2) ^ 2 = 16 * (ℓ + 1) ^ 4 by ring]
        exact h16
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4 * (ℓ + 1) ^ 2),
        Real.sqrt_sq hSnn] at h
    have hge1 : (1 : ℝ) ≤ 2 * (ℓ + 1) := by linarith
    calc 2 * (ℓ + 1) = (2 * (ℓ + 1)) * 1 := by ring
      _ ≤ (2 * (ℓ + 1)) * (2 * (ℓ + 1)) := mul_le_mul_of_nonneg_left hge1 (by positivity)
      _ = 4 * (ℓ + 1) ^ 2 := by ring
      _ ≤ S := h4
  -- hence `2 ℓ qn ≤ N`
  have h2 : 2 * (ℓ * qn) ≤ S ^ 2 := by
    have h2l : 2 * ℓ ≤ S := by linarith
    calc 2 * (ℓ * qn) = (2 * ℓ) * qn := by ring
      _ ≤ S * S := mul_le_mul h2l hqnS hqn0' hSnn
      _ = S ^ 2 := by ring
  have hpowd : N ^ ((d : ℝ) / 2) = S ^ d := by
    rw [hSdef, Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hNpos)]
    congr 1
    ring
  have hβup' : |β| ≤ 1 / (qn * S ^ d) := by rw [← hpowd]; exact hβup
  have hdsplit : d = 2 + (d - 2) := (Nat.add_sub_cancel' hd).symm
  have hd1' : d - 1 = (d - 2) + 1 := by omega
  have hSpow : S ^ d = S ^ 2 * S ^ (d - 2) := by rw [← pow_add, ← hdsplit]
  have hqpow : qn ^ d = qn ^ 2 * qn ^ (d - 2) := by rw [← pow_add, ← hdsplit]
  have hqd1 : qn ^ (d - 1) = qn * qn ^ (d - 2) := by rw [hd1', pow_succ]; ring
  have hbound1 : ℓ * qn / S ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < S ^ 2)]
    linarith
  have hbound2 : qn ^ (d - 2) / S ^ (d - 2) ≤ 1 := by
    rw [div_le_one (pow_pos hSpos (d - 2))]
    exact pow_le_pow_left₀ hqn0' hqnS (d - 2)
  have hA : |β| * ℓ * qn ^ d ≤ (ℓ * qn / S ^ 2) * (qn ^ (d - 2) / S ^ (d - 2)) := by
    have hnn : 0 ≤ ℓ * qn ^ d := mul_nonneg hℓ0 (pow_nonneg hqn0' d)
    have h1 : |β| * ℓ * qn ^ d ≤ (1 / (qn * S ^ d)) * ℓ * qn ^ d := by
      calc |β| * ℓ * qn ^ d = |β| * (ℓ * qn ^ d) := by ring
        _ ≤ (1 / (qn * S ^ d)) * (ℓ * qn ^ d) := mul_le_mul_of_nonneg_right hβup' hnn
        _ = (1 / (qn * S ^ d)) * ℓ * qn ^ d := by ring
    have heq : (1 / (qn * S ^ d)) * ℓ * qn ^ d
        = (ℓ * qn / S ^ 2) * (qn ^ (d - 2) / S ^ (d - 2)) := by
      rw [hSpow, hqpow]
      field_simp
    rw [heq] at h1
    exact h1
  have hgoal1 : |β| * ℓ * qn ^ d ≤ 1 / 2 := by
    refine le_trans hA ?_
    calc (ℓ * qn / S ^ 2) * (qn ^ (d - 2) / S ^ (d - 2)) ≤ (1 / 2) * 1 :=
          mul_le_mul hbound1 hbound2 (by positivity) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hA2 : |β| * ℓ * qn ^ d ≤ ℓ * qn ^ (d - 1) / S ^ d := by
    have hnn : 0 ≤ ℓ * qn ^ d := mul_nonneg hℓ0 (pow_nonneg hqn0' d)
    have h1 : |β| * ℓ * qn ^ d ≤ (1 / (qn * S ^ d)) * ℓ * qn ^ d := by
      calc |β| * ℓ * qn ^ d = |β| * (ℓ * qn ^ d) := by ring
        _ ≤ (1 / (qn * S ^ d)) * (ℓ * qn ^ d) := mul_le_mul_of_nonneg_right hβup' hnn
        _ = (1 / (qn * S ^ d)) * ℓ * qn ^ d := by ring
    have heq : (1 / (qn * S ^ d)) * ℓ * qn ^ d = ℓ * qn ^ (d - 1) / S ^ d := by
      rw [hqpow, hqd1]
      field_simp
    rw [heq] at h1
    exact h1
  have hB : |β| * ℓ * qn ^ d * Mr ≤ (ℓ * qn ^ (d - 1) / S ^ d) * (2 * N / qn) := by
    have hb : 0 ≤ ℓ * qn ^ (d - 1) / S ^ d :=
      div_nonneg (mul_nonneg hℓ0 (pow_nonneg hqn0' _)) (le_of_lt (pow_pos hSpos d))
    exact mul_le_mul hA2 hMrN (by linarith) hb
  have heqB : (ℓ * qn ^ (d - 1) / S ^ d) * (2 * N / qn)
      = 2 * ℓ * (qn ^ (d - 2) / S ^ (d - 2)) := by
    rw [hqd1, hSpow, ← hS2]
    field_simp
  have hgoal2 : |β| * ℓ * qn ^ d * Mr ≤ 2 * ℓ := by
    rw [heqB] at hB
    refine le_trans hB ?_
    calc 2 * ℓ * (qn ^ (d - 2) / S ^ (d - 2)) ≤ 2 * ℓ * 1 :=
          mul_le_mul_of_nonneg_left hbound2 (by linarith)
      _ = 2 * ℓ := by ring
  exact ⟨hgoal1, hgoal2⟩

theorem deepArc_smallDenominator (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1 / 2) :
    ∃ C θ : ℝ, 0 < θ ∧ 0 < C ∧
      ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
        (q : ℝ) ≤ (N : ℝ) ^ ε₀ → (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) →
        ((N : ℝ) / (q : ℝ)) ^ ((Q.natDegree : ℝ) / (Q.natDegree + 1)) / 100
          ≤ |β| * (N : ℝ) ^ Q.natDegree →
        |β| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)) →
        ‖Work.A3.expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C * (N : ℝ) ^ (1 - θ) := by
  set d : ℕ := Q.natDegree with hddef
  have hd2 : 2 ≤ d := hddef ▸ hd
  have hQ0 : Q ≠ 0 := by
    intro h0
    have h1 : Q.natDegree = 0 := by rw [h0]; simp
    rw [hddef, h1] at hd
    omega
  have hL0 : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
  set ℓ : ℝ := |((Q.leadingCoeff : ℤ) : ℝ)| with hℓdef
  have hℓpos : 0 < ℓ := by
    rw [hℓdef]
    exact abs_pos.mpr (by exact_mod_cast hL0)
  set cdeep : ℝ := 2 * Real.pi * (d.factorial : ℝ) * ℓ / 100 with hcdeepdef
  have hcdeeppos : 0 < cdeep := by rw [hcdeepdef]; positivity
  set c₀ : ℝ := cdeep / 2 ^ (d + 1) with hc₀def
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; positivity
  set C₀ : ℝ := 2 * ℓ with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; linarith
  set θ' : ℝ := (2 : ℝ) ^ (1 - (d : ℝ)) * ((d : ℝ) / ((d : ℝ) + 1)) with hθ'def
  have hθ'pos : 0 < θ' := by rw [hθ'def]; positivity
  set φ : ℝ := θ' / 2 with hφdef
  have hφpos : 0 < φ := by rw [hφdef]; linarith
  obtain ⟨Cw, hCwpos, hCw⟩ := blockWeyl_bound d hd2 hC₀pos hc₀pos hφpos
  set N₀ : ℝ := 16 * (ℓ + 1) ^ 4 + 64 with hN₀def
  have hN₀pos : 0 < N₀ := by rw [hN₀def]; positivity
  have hN₀4 : (4 : ℝ) ≤ N₀ := by
    rw [hN₀def]
    have h1 : (0 : ℝ) ≤ (ℓ + 1) ^ 4 := by positivity
    linarith
  set θ : ℝ := (1 - ε₀) * θ' / 2 with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    have h1 : (0 : ℝ) < 1 - ε₀ := by linarith
    positivity
  refine ⟨(Cw * 2 ^ (1 - θ' + φ) + 1) * (N₀ ^ θ + 1), θ, hθpos, by positivity, ?_⟩
  intro N a q β hN hq hcop hqε hqsqrt hβdeep hβup
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hnorm : ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ (N : ℝ) := norm_expSum_le Q N _
  by_cases hNsmall : (N : ℝ) < N₀
  · have hNθ : (N : ℝ) ^ θ ≤ N₀ ^ θ := Real.rpow_le_rpow hNpos.le hNsmall.le hθpos.le
    have hsplitN : (N : ℝ) ≤ (N : ℝ) ^ (1 - θ) * N₀ ^ θ := by
      have h1 : (N : ℝ) ^ (1 - θ) * (N : ℝ) ^ θ = (N : ℝ) := by
        rw [← Real.rpow_add hNpos, show (1 : ℝ) - θ + θ = 1 by ring, Real.rpow_one]
      calc (N : ℝ) ≤ (N : ℝ) ^ (1 - θ) * (N : ℝ) ^ θ := by rw [h1]
        _ ≤ (N : ℝ) ^ (1 - θ) * N₀ ^ θ :=
            mul_le_mul_of_nonneg_left hNθ (Real.rpow_nonneg hNpos.le (1 - θ))
    have hC1 : (N : ℝ) ^ (1 - θ) * N₀ ^ θ
        ≤ ((Cw * 2 ^ (1 - θ' + φ) + 1) * (N₀ ^ θ + 1)) * (N : ℝ) ^ (1 - θ) := by
      have hp : (0 : ℝ) ≤ (N : ℝ) ^ (1 - θ) := Real.rpow_nonneg hNpos.le _
      have h3 : (0 : ℝ) < N₀ ^ θ := Real.rpow_pos_of_pos hN₀pos θ
      have h4 : (0 : ℝ) ≤ Cw * 2 ^ (1 - θ' + φ) := by positivity
      have h5 : N₀ ^ θ ≤ (Cw * 2 ^ (1 - θ' + φ) + 1) * (N₀ ^ θ + 1) := by
        nlinarith [h3, h4]
      calc (N : ℝ) ^ (1 - θ) * N₀ ^ θ
          ≤ (N : ℝ) ^ (1 - θ) * ((Cw * 2 ^ (1 - θ' + φ) + 1) * (N₀ ^ θ + 1)) :=
            mul_le_mul_of_nonneg_left h5 hp
        _ = ((Cw * 2 ^ (1 - θ' + φ) + 1) * (N₀ ^ θ + 1)) * (N : ℝ) ^ (1 - θ) := by ring
    linarith [hnorm, hsplitN, hC1]
  · push_neg at hNsmall
    have hNge : N₀ ≤ (N : ℝ) := hNsmall
    have hN4 : (4 : ℝ) ≤ (N : ℝ) := le_trans hN₀4 hNge
    set qn : ℕ := q.toNat with hqndef
    have hq0z : (0 : ℤ) ≤ q := by omega
    have hqnc : (qn : ℤ) = q := Int.toNat_of_nonneg hq0z
    have hqn1 : 1 ≤ qn := by
      have h : (1 : ℤ) ≤ (qn : ℤ) := by rw [hqnc]; exact hq
      omega
    have hqnR : (qn : ℝ) = (q : ℝ) := by rw [← Int.cast_natCast, hqnc]
    have hqn1R : (1 : ℝ) ≤ (qn : ℝ) := by exact_mod_cast hqn1
    have hqnpos : (0 : ℝ) < (qn : ℝ) := by exact_mod_cast (by omega : 0 < qn)
    have hqnsqrt : (qn : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by rw [hqnR]; exact hqsqrt
    have hqnε' : (qn : ℝ) ≤ (N : ℝ) ^ ε₀ := by rw [hqnR]; exact hqε
    have hβne : β ≠ 0 := by
      intro h0
      rw [h0, abs_zero, zero_mul] at hβdeep
      have h2 : (0 : ℝ) < ((N : ℝ) / (q : ℝ)) ^ ((d : ℝ) / ((d : ℝ) + 1)) / 100 := by
        apply div_pos _ (by norm_num)
        exact Real.rpow_pos_of_pos (by positivity) _
      linarith [hβdeep, h2]
    set M : ℝ := (N : ℝ) / (qn : ℝ) with hMdef
    have hMpos : 0 < M := by rw [hMdef]; positivity
    have hsqrt2 : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (N : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hNpos.le
    have hsqrt_nn : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hNpos.le _
    have hsqrt_le : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) / 2 := by
      nlinarith [hsqrt2, hsqrt_nn, hN4]
    have hqn_half : (qn : ℝ) ≤ (N : ℝ) / 2 := le_trans hqnsqrt hsqrt_le
    have hsqrt_le4 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) / 4 := by
      rw [← Real.sqrt_eq_rpow]
      have hN16 : (16 : ℝ) ≤ (N : ℝ) := by
        have h0 : (0 : ℝ) ≤ (ℓ + 1) ^ 4 := by positivity
        have h2 : 16 * (ℓ + 1) ^ 4 + 64 ≤ (N : ℝ) := by
          have h := hNge
          rwa [hN₀def] at h
        linarith
      have hsq : (N : ℝ) ≤ ((N : ℝ) / 4) ^ 2 := by nlinarith [hN16, hNpos.le]
      calc Real.sqrt (N : ℝ) ≤ Real.sqrt (((N : ℝ) / 4) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = (N : ℝ) / 4 := Real.sqrt_sq (by linarith)
    have hqn_quarter : (qn : ℝ) ≤ (N : ℝ) / 4 := le_trans hqnsqrt hsqrt_le4
    have hM1 : (1 : ℝ) ≤ M := by
      rw [hMdef, le_div_iff₀ hqnpos]
      have h2 : (N : ℝ) / 2 ≤ (N : ℝ) := by nlinarith [hN4]
      nlinarith [hqn_half, h2]
    have hqn_sq : (qn : ℝ) * (qn : ℝ) ≤ (N : ℝ) := by
      nlinarith [hsqrt2, hqnsqrt, hqnpos, hsqrt_nn]
    have hNbig : 16 * (ℓ + 1) ^ 4 + 64 ≤ (N : ℝ) := by
      rw [hN₀def] at hNge
      exact hNge
    have hθ'le : θ' ≤ 1 := by
      rw [hθ'def]
      have h1 : (2 : ℝ) ^ (1 - (d : ℝ)) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
        linarith
      have h1' : (0 : ℝ) ≤ (2 : ℝ) ^ (1 - (d : ℝ)) := Real.rpow_nonneg (by norm_num) _
      have h2 : (d : ℝ) / ((d : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have h2' : (0 : ℝ) ≤ (d : ℝ) / ((d : ℝ) + 1) := by positivity
      nlinarith [h1, h1', h2, h2']
    have hφle : φ ≤ 1 := by rw [hφdef]; linarith
    have hβup' : |β| ≤ 1 / ((qn : ℝ) * (N : ℝ) ^ ((d : ℝ) / 2)) := by
      rw [hqnR]
      simpa [hddef] using hβup
    have hβdeep' : ((N : ℝ) / (qn : ℝ)) ^ ((d : ℝ) / ((d : ℝ) + 1)) / 100
        ≤ |β| * (N : ℝ) ^ d := by
      rw [hqnR]
      simpa [hddef] using hβdeep
    have hblockbound : ∀ r ∈ Finset.range qn,
        ‖(∑ p ∈ Finset.range ((N + qn - 1 - r) / qn),
            Complex.exp (-(2 * Real.pi * Complex.I *
              (β * (((Q.eval ((1 + (p * qn + r) : ℕ) : ℤ) : ℤ) : ℝ))))))‖
          ≤ Cw * (2 * M) ^ (1 - θ' + φ) := by
      intro r hr
      set Mr : ℕ := (N + qn - 1 - r) / qn with hMrdef
      let fr : Polynomial ℝ := Polynomial.C (-β) *
        ((Qreal Q).comp (Polynomial.C ((qn : ℝ)) * Polynomial.X + Polynomial.C (((1 + r : ℕ) : ℝ))))
      have hA_nat : (Polynomial.C ((qn : ℝ)) * Polynomial.X + Polynomial.C (((1 + r : ℕ) : ℝ))).natDegree = 1 :=
        Polynomial.natDegree_linear (by positivity : ((qn : ℝ)) ≠ 0)
      have hA_lc : (Polynomial.C ((qn : ℝ)) * Polynomial.X + Polynomial.C (((1 + r : ℕ) : ℝ))).leadingCoeff = (qn : ℝ) :=
        Polynomial.leadingCoeff_linear (by positivity : ((qn : ℝ)) ≠ 0)
      have hcomp_nat : ((Qreal Q).comp (Polynomial.C ((qn : ℝ)) * Polynomial.X + Polynomial.C (((1 + r : ℕ) : ℝ)))).natDegree = d := by
        rw [Polynomial.natDegree_comp, hA_nat, mul_one, Qreal_natDegree, ← hddef]
      have hcomp_lc : ((Qreal Q).comp (Polynomial.C ((qn : ℝ)) * Polynomial.X + Polynomial.C (((1 + r : ℕ) : ℝ)))).leadingCoeff
          = ((Q.leadingCoeff : ℤ) : ℝ) * (qn : ℝ) ^ d := by
        rw [Polynomial.leadingCoeff_comp (by rw [hA_nat]; norm_num), hA_lc, Qreal_leadingCoeff,
          Qreal_natDegree, ← hddef]
      have hfr_nat : fr.natDegree = d := by
        simp only [fr]
        rw [Polynomial.natDegree_C_mul (by simpa using hβne), hcomp_nat]
      have hfr_lc : fr.leadingCoeff = -β * ((Q.leadingCoeff : ℤ) : ℝ) * (qn : ℝ) ^ d := by
        simp only [fr]
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hcomp_lc]
        ring
      have hfr_lcabs : |fr.leadingCoeff| = |β| * ℓ * (qn : ℝ) ^ d := by
        rw [hfr_lc, hℓdef, abs_mul, abs_mul, abs_neg,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (qn : ℝ) ^ d)]
      have hfr_eval : ∀ p : ℕ, fr.eval ((p : ℝ))
          = -β * ((Q.eval (((1 + (p * qn + r) : ℕ)) : ℤ) : ℤ) : ℝ) := by
        intro p
        simp only [fr]
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
        have hAeval : (Polynomial.C ((qn : ℝ)) * Polynomial.X
            + Polynomial.C (((1 + r : ℕ) : ℝ))).eval ((p : ℝ))
            = (qn : ℝ) * (p : ℝ) + (((1 + r : ℕ)) : ℝ) := by
          rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
            Polynomial.eval_C]
        rw [hAeval]
        rw [show (qn : ℝ) * (p : ℝ) + (((1 + r : ℕ)) : ℝ)
            = ((((1 + (p * qn + r) : ℕ)) : ℤ) : ℝ) by push_cast; ring]
        rw [Qreal_eval_intCast]
      have hsum_eq : (∑ p ∈ Finset.range Mr, Complex.exp (-(2 * Real.pi * Complex.I *
            (β * (((Q.eval ((1 + (p * qn + r) : ℕ) : ℤ) : ℤ) : ℝ))))))
          = ∑ x ∈ Finset.range Mr, Complex.exp (((2 * Real.pi * fr.eval (((0 : ℤ) : ℝ) + (x : ℝ)) : ℝ) : ℂ) * Complex.I) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [show (((0 : ℤ) : ℝ)) + (p : ℝ) = (p : ℝ) by push_cast; ring]
        rw [hfr_eval p]
        congr 1
        push_cast
        ring
      have hMr_hi : Mr * qn ≤ N + qn := by
        have h := Nat.div_mul_le_self (N + qn - 1 - r) qn
        rw [hMrdef]
        omega
      have hMr_leR : (Mr : ℝ) ≤ 2 * (N : ℝ) / (qn : ℝ) := by
        have hcast : (Mr : ℝ) * (qn : ℝ) ≤ (N : ℝ) + (qn : ℝ) := by
          have h := hMr_hi
          exact_mod_cast h
        have h1 : (Mr : ℝ) ≤ ((N : ℝ) + (qn : ℝ)) / (qn : ℝ) := by
          rw [le_div_iff₀ hqnpos]
          linarith [hcast]
        have h2 : ((N : ℝ) + (qn : ℝ)) / (qn : ℝ) = M + 1 := by
          rw [hMdef, add_div, div_self (ne_of_gt hqnpos)]
        have h3 : M + 1 ≤ 2 * M := by linarith [hM1]
        have h4 : 2 * M = 2 * (N : ℝ) / (qn : ℝ) := by rw [hMdef]; ring
        linarith [h1, h2.le, h3, h4.le]
      have hMr_lo : N ≤ Mr * qn + qn := by
        have hr' : r ≤ qn - 1 := by
          have h := Finset.mem_range.mp hr
          omega
        have h1 : N + qn - 1 - r < (Mr + 1) * qn := by
          have h2 : (N + qn - 1 - r) / qn < Mr + 1 := by
            rw [← hMrdef]
            exact Nat.lt_succ_self _
          exact Nat.lt_mul_of_div_lt h2 (by omega)
        have hA : N ≤ N + qn - 1 - r := by omega
        have hB : N + qn - 1 - r < Mr * qn + qn := by
          have h3 : (Mr + 1) * qn = Mr * qn + qn := by ring
          omega
        omega
      have hqnMr : (N : ℝ) / 2 ≤ (qn : ℝ) * (Mr : ℝ) := by
        have h : (N : ℝ) ≤ (Mr : ℝ) * (qn : ℝ) + (qn : ℝ) := by
          have h' := hMr_lo
          exact_mod_cast h'
        have h2 : (qn : ℝ) ≤ (N : ℝ) / 2 := hqn_half
        nlinarith [h, h2]
      have hMr_ge2 : (2 : ℝ) ≤ (Mr : ℝ) := by
        have h : (N : ℝ) ≤ (Mr : ℝ) * (qn : ℝ) + (qn : ℝ) := by
          have h' := hMr_lo
          exact_mod_cast h'
        have h1 : (N : ℝ) / 2 ≤ (Mr : ℝ) * (qn : ℝ) := by linarith
        have h2 : (Mr : ℝ) * (qn : ℝ) ≤ (Mr : ℝ) * ((N : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hqn_quarter (by positivity)
        have hN4pos : (0 : ℝ) < (N : ℝ) / 4 := by linarith
        have h6 : ((N : ℝ) / 2) / ((N : ℝ) / 4) = 2 := by
          field_simp
          norm_num
        have h5 : ((N : ℝ) / 2) / ((N : ℝ) / 4) ≤ (Mr : ℝ) :=
          (div_le_iff₀ hN4pos).mpr (le_trans h1 h2)
        linarith [h5, h6.le]
      have hMr2 : 2 ≤ Mr := by exact_mod_cast hMr_ge2
      have hbc := block_coeff_bound_local d hd2 hℓpos hqn1R hNbig hqn_sq hMr_ge2 hMr_leR hβup'
      have hlc1 : |fr.leadingCoeff| ≤ 1 / 2 := by
        rw [hfr_lcabs]
        exact hbc.1
      have hlc2 : |fr.leadingCoeff| * (Mr : ℝ) ≤ C₀ := by
        rw [hfr_lcabs, hC₀def]
        linarith [hbc.2]
      have hdeep_b : c₀ * (Mr : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
          ≤ (2 * Real.pi * (d.factorial : ℝ)) * |fr.leadingCoeff| * (Mr : ℝ) ^ d := by
        rw [hfr_lcabs]
        exact block_deep_condition d hd2 hℓpos hcdeepdef.symm hc₀def.symm hqn1R hMr_ge2
          hMr_leR hqnMr hβdeep'
      have hweyl := hCw Mr fr 0 hMr2 hfr_nat hlc1 hlc2 hdeep_b
      rw [← hsum_eq] at hweyl
      have h2M : (2 : ℝ) * M = 2 * (N : ℝ) / (qn : ℝ) := by rw [hMdef]; ring
      have hMrpow : (Mr : ℝ) ^ (1 - θ' + φ) ≤ (2 * M) ^ (1 - θ' + φ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by linarith [hθ'le, hφle])
        rw [h2M]
        exact hMr_leR
      refine le_trans hweyl ?_
      rw [show (1 : ℝ) - (2 : ℝ) ^ (1 - (d : ℝ)) * ((d : ℝ) / ((d : ℝ) + 1)) + φ = 1 - θ' + φ by
        rw [hθ'def]]
      exact mul_le_mul_of_nonneg_left hMrpow hCwpos.le
    have hsplit := expSum_residue_split_gen Q N qn a β ((a : ℝ) / (q : ℝ) + β)
      (by rw [hqnR]) hqn1
    have hfinal : ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ Cw * 2 ^ (1 - θ' + φ) * (N : ℝ) ^ (1 - θ) := by
      rw [hsplit]
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (g := fun _ => Cw * (2 * M) ^ (1 - θ' + φ))
        (fun r hr => ?_)) ?_
      · have hcr : ‖Complex.exp (-(2 * Real.pi * Complex.I *
            (((a : ℝ) / (qn : ℝ)) * (((Q.eval ((1 + r : ℕ) : ℤ) : ℤ)) : ℝ))))‖ = 1 := by
          rw [Complex.norm_exp, Real.exp_eq_one_iff]
          simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
            Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        rw [norm_mul, hcr, one_mul]
        exact hblockbound r hr
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hkey := final_exponent_bound hε₀1 hθ'pos hφdef.symm hθdef.symm hN1 hqn1R hMdef.symm hqnε' hθ'le
        calc (qn : ℝ) * (Cw * (2 * M) ^ (1 - θ' + φ))
            = Cw * ((qn : ℝ) * (2 ^ (1 - θ' + φ) * M ^ (1 - θ' + φ))) := by
              rw [Real.mul_rpow (by norm_num) hMpos.le]
              ring
          _ ≤ Cw * (2 ^ (1 - θ' + φ) * (N : ℝ) ^ (1 - θ)) :=
              mul_le_mul_of_nonneg_left hkey hCwpos.le
          _ = Cw * 2 ^ (1 - θ' + φ) * (N : ℝ) ^ (1 - θ) := by ring
    have hbig : Cw * 2 ^ (1 - θ' + φ) ≤ (Cw * 2 ^ (1 - θ' + φ) + 1) * (N₀ ^ θ + 1) := by
      have h1 : (0 : ℝ) < N₀ ^ θ := Real.rpow_pos_of_pos hN₀pos θ
      have h2 : (1 : ℝ) ≤ N₀ ^ θ + 1 := by linarith
      have h3 : (0 : ℝ) ≤ Cw * 2 ^ (1 - θ' + φ) := by positivity
      have h5 : (0 : ℝ) ≤ Cw * 2 ^ (1 - θ' + φ) * N₀ ^ θ := mul_nonneg h3 h1.le
      nlinarith [h1, h2, h3, h5]
    calc ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ Cw * 2 ^ (1 - θ' + φ) * (N : ℝ) ^ (1 - θ) := hfinal
      _ ≤ ((Cw * 2 ^ (1 - θ' + φ) + 1) * (N₀ ^ θ + 1)) * (N : ℝ) ^ (1 - θ) := by
          exact mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hNpos.le (1 - θ))

end

end Work.A3
