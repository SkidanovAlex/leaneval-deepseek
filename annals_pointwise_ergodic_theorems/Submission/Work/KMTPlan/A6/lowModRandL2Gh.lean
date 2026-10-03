import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBAux
import Submission.Work.KMTPlan.A6.tmRandSymbG_l2
import Submission.Work.KMTPlan.A6.randSymb_sup_le_of_lipschitz
import Submission.Work.KMTPlan.A6.iwSymbolSet_narrow_bound
import Submission.Work.KMTPlan.A6.nonAliasing_diffFreqs
import Submission.Work.KMTAreas.A7.randSymb_Tm_g_lp


set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- The weight `(2^{-dk}N^d x)^j` of the modified `g`-side bump `φ̃_{N,k,j}(t)`. -/
noncomputable def gWeight (P : Polynomial ℤ) (N k : ℕ) (x : ℝ) (j : ℤ) : ℂ :=
  ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * x : ℝ)) : ℂ) ^ j

theorem varphitildeNtj_eq_gWeight_mul (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t x : ℝ) :
    varphitildeNtj P N k j t x
      = gWeight P N k x j * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x := rfl

/-- The scaled frequency variable `2^{d(Log N - k)}|x|` of the `g`-side bump at the index `m`. -/
noncomputable def gxi (P : Polynomial ℤ) (a : ℕ → NNReal) (k : ℕ) (x : ℝ) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ ((P.natDegree : ℝ)
      * ((Work.Analysis.EndVar.logN (Nat.floor (a m)) : ℝ) - (k : ℝ))) * |x|

theorem gxi_mono (P : Polynomial ℤ) (Λ : NNReal) (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (k : ℕ) (x : ℝ) :
    Monotone (gxi P a k x) := by
  intro p q hpq
  have hf : Nat.floor (a p) ≤ Nat.floor (a q) := lacunary_floor_mono Λ hΛ ha hpq
  have hlog : Work.Analysis.EndVar.logN (Nat.floor (a p))
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a q)) := logN_mono hf
  have hlogR : ((Work.Analysis.EndVar.logN (Nat.floor (a p)) : ℝ))
      ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a q)) : ℝ)) := by exact_mod_cast hlog
  have hexp : (P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN (Nat.floor (a p)) : ℝ) - (k : ℝ))
      ≤ (P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN (Nat.floor (a q)) : ℝ) - (k : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hpow : (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN (Nat.floor (a p)) : ℝ) - (k : ℝ)))
      ≤ (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN (Nat.floor (a q)) : ℝ) - (k : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  unfold gxi
  exact mul_le_mul_of_nonneg_right hpow (abs_nonneg x)

theorem gxi_apply (P : Polynomial ℤ) (a : ℕ → NNReal) (k : ℕ) (x : ℝ) (m : ℕ) :
    gxi P a k x m
      = (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN (Nat.floor (a m)) : ℝ) - (k : ℝ))) * |x| := rfl

/-- The exponent arithmetic behind the weight bounds. -/
theorem two_rpow_split_weight (d k : ℕ) (L : ℝ) :
    (2 : ℝ) ^ (-((d : ℝ) * (k : ℝ))) * ((2 : ℝ) ^ ((d : ℝ) * L))
      = (2 : ℝ) ^ ((d : ℝ) * (L - (k : ℝ))) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem two_pow_logN_pow_natDegree (d : ℕ) (N : ℕ) :
    ((2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ))) ^ d
      = (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ))) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ))) d,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- For the twist `j = 1` the weight is bounded by `2^d` times the scaled variable. -/
theorem gWeight_one_norm_le_aux (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ) (x : ℝ) :
    ‖gWeight P N k x 1‖ ≤ (2 : ℝ) ^ P.natDegree
      * ((2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hNlt : (N : ℝ) < 2 * (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) :=
    lt_two_mul_pow_logN N
  have hNd : (N : ℝ) ^ P.natDegree
      < (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ))) := by
    have h1 : ((N : ℝ)) ^ P.natDegree
        < (2 * (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ))) ^ P.natDegree :=
      pow_lt_pow_left₀ hNlt (by positivity) (by omega)
    rw [mul_pow, two_pow_logN_pow_natDegree] at h1
    exact h1
  have hnorm : ‖gWeight P N k x 1‖
      = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * |x| := by
    unfold gWeight
    rw [zpow_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos h2pos _),
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) _)]
  rw [hnorm]
  have hstep : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree
      ≤ (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) := by
    have h1 : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree
        < (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
          * ((2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ ((P.natDegree : ℝ)
              * ((Work.Analysis.EndVar.logN N : ℝ)))) :=
      mul_lt_mul_of_pos_left hNd (Real.rpow_pos_of_pos h2pos _)
    have h2 : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
          * ((2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ ((P.natDegree : ℝ)
              * ((Work.Analysis.EndVar.logN N : ℝ))))
        = (2 : ℝ) ^ P.natDegree * ((2 : ℝ) ^ ((P.natDegree : ℝ)
            * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) := by
      rw [← two_rpow_split_weight P.natDegree k ((Work.Analysis.EndVar.logN N : ℝ))]
      ring
    rw [h2] at h1
    exact le_of_lt h1
  calc (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * |x|
      = ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree) * |x| := by
        ring
    _ ≤ ((2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) * |x| :=
        mul_le_mul_of_nonneg_right hstep (abs_nonneg x)
    _ = (2 : ℝ) ^ P.natDegree * ((2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|) := by ring

/-- For the twist `j = 1` the weight is bounded by `2^{d+1}` on the support of the bump. -/
theorem gWeight_one_norm_le (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ) (x : ℝ)
    (hxi : (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x| ≤ 1) :
    ‖gWeight P N k x 1‖ ≤ (2 : ℝ) ^ (P.natDegree + 1) := by
  refine le_trans (gWeight_one_norm_le_aux P hd N k x) ?_
  have h1 : (2 : ℝ) ^ P.natDegree
      * ((2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|)
      ≤ (2 : ℝ) ^ P.natDegree * 1 :=
    mul_le_mul_of_nonneg_left hxi (by positivity)
  refine le_trans h1 ?_
  rw [mul_one, pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) P.natDegree]

/-- **The scaled variable is bounded by `2^d` times the real base `|2^{-dk}N^d x|`**, since
`2^{Log N} ≤ 2N`. -/
theorem gxi_le_two_pow_mul_base (P : Polynomial ℤ) (N k : ℕ) (x : ℝ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|
      ≤ (2 : ℝ) ^ P.natDegree
        * (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * |x| := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hL : (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ≤ 2 * (N : ℝ) :=
    two_pow_logN_le_two_mul_N hN
  have hLnp : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ)))
      ≤ (2 : ℝ) ^ P.natDegree * (N : ℝ) ^ P.natDegree := by
    have h1 : ((2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ))) ^ P.natDegree
        ≤ (2 * (N : ℝ)) ^ P.natDegree := pow_le_pow_left₀ (by positivity) hL _
    rw [two_pow_logN_pow_natDegree, mul_pow] at h1
    exact h1
  have hsplit : (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))
      = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
        * (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ))) :=
    (two_rpow_split_weight P.natDegree k ((Work.Analysis.EndVar.logN N : ℝ))).symm
  calc (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|
      = ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
          * (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ)))) * |x| := by
        rw [hsplit]
    _ ≤ ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
          * ((2 : ℝ) ^ P.natDegree * (N : ℝ) ^ P.natDegree)) * |x| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLnp (Real.rpow_pos_of_pos h2pos _).le) (abs_nonneg x)
    _ = (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
          * (N : ℝ) ^ P.natDegree * |x| := by ring

/-- For the twist `j = -1` the weight is bounded by `2^{2d+1}` on the support of the bump
(`2^{d(Log N - k)}|x| ≥ 2^{-(d+1)}` and `N ≥ 1`). -/
theorem gWeight_neg_one_norm_le (P : Polynomial ℤ) (N k : ℕ) (x : ℝ) (hN : 1 ≤ N)
    (hlo : (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1))
      ≤ (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|) :
    ‖gWeight P N k x (-1)‖ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, abs_zero, mul_zero] at hlo
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)) := Real.rpow_pos_of_pos h2pos _
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set Z : ℝ := (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * |x| with hZ
  have hZpos : 0 < Z := by rw [hZ]; positivity
  have hnorm : ‖gWeight P N k x (-1)‖ = Z⁻¹ := by
    rw [hZ]
    unfold gWeight
    rw [zpow_neg_one, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos h2pos _),
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) _)]
  rw [hnorm]
  have hkey : (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)) ≤ (2 : ℝ) ^ P.natDegree * Z := by
    rw [hZ]
    refine le_trans hlo ?_
    calc (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|
        ≤ (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
            * (N : ℝ) ^ P.natDegree * |x| := gxi_le_two_pow_mul_base P N k x hN
      _ = (2 : ℝ) ^ P.natDegree
            * ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
              * (N : ℝ) ^ P.natDegree * |x|) := by ring
  have h1 : ((2 : ℝ) ^ P.natDegree * Z)⁻¹ ≤ ((2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)))⁻¹ :=
    (inv_le_inv₀ (by positivity) (Real.rpow_pos_of_pos h2pos _)).mpr hkey
  rw [mul_inv] at h1
  have h2 : ((2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)))⁻¹ = (2 : ℝ) ^ (P.natDegree + 1) := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show -(-((P.natDegree : ℝ) + 1)) = ((P.natDegree + 1 : ℕ) : ℝ) by push_cast; ring]
    rw [Real.rpow_natCast]
  have h3 : Z⁻¹ ≤ (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree + 1) := by
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ P.natDegree := by positivity
    have h5 := mul_le_mul_of_nonneg_left h1 h4
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ P.natDegree ≠ 0), one_mul,
      h2] at h5
    exact h5
  refine le_trans h3 ?_
  rw [← pow_add]
  exact le_of_eq (by congr 1; omega)

/-! ## Support facts for the unmodified `g`-side bump -/

theorem varphitildeNt_xi_le_one (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ) (t x : ℝ)
    (h : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x ≠ 0) :
    (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x| ≤ 1 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hle := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k t x h
  have h1 := mul_le_mul_of_nonneg_left hle
    (Real.rpow_pos_of_pos h2pos ((P.natDegree : ℝ)
      * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))).le
  rw [← Real.rpow_add h2pos] at h1
  have hexp : (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
      + (P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) = 0 := by ring
  rw [hexp, Real.rpow_zero] at h1
  exact h1

theorem varphitildeNt_annulus_lower (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ)
    (t x : ℝ) (hk : 1 ≤ k)
    (h : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x ≠ 0) :
    (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1))
      < (2 : ℝ) ^ ((P.natDegree : ℝ)
          * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x| := by
  have hN : Work.KMTAreas.A7.varphitildeN P.natDegree N k x ≠ 0 := by
    intro h0
    exact h (by rw [Work.KMTAreas.A7.varphitildeNt, h0, zero_mul])
  exact (Work.KMTPlan.A6.varphitildeN_annulus hd hk hN).1

/-- **Pointwise bound of the modified `g`-side bump** for `j ∈ {-1,0,1}` (the twists actually
used) and `N ≥ 1`: the modified bump is at most `2^{2d+1}` in modulus.  On the support of the
unmodified bump the weight `(2^{-dk}N^d x)^j` is at most `2^d` for `j ≥ 0` and at most `2^{2d+1}`
for `j = -1` (where `2^{d(Log N - k)}|x| ≥ 2^{-(d+1)}`). -/
theorem varphitildeNtj_pointwise (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ) (j : ℤ)
    (t x : ℝ) (hN : 1 ≤ N) (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (h : k ≠ 0 ∨ 0 ≤ j) :
    ‖varphitildeNtj P N k j t x‖ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) := by
  by_cases hj0 : j = 0
  · subst hj0
    rw [varphitildeNtj_zero]
    refine le_trans (varphitildeNt_norm_le_one P P.natDegree N k t x) ?_
    exact one_le_pow₀ (by norm_num)
  · rw [varphitildeNtj_eq_gWeight_mul]
    by_cases hV : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x = 0
    · rw [hV, mul_zero, norm_zero]; positivity
    · have hV1 : ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x‖ ≤ 1 :=
        varphitildeNt_norm_le_one P P.natDegree N k t x
      have hxi := varphitildeNt_xi_le_one P hd N k t x hV
      have hW : ‖gWeight P N k x j‖ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with h1 | h1 | h1
        · subst h1
          refine le_trans (gWeight_neg_one_norm_le P N k x hN ?_) le_rfl
          rcases h with hk | hk
          · exact (varphitildeNt_annulus_lower P hd N k t x (by omega) hV).le
          · omega
        · exact absurd h1 hj0
        · subst h1
          refine le_trans (gWeight_one_norm_le P hd N k x hxi) ?_
          exact pow_le_pow_right₀ (by norm_num) (by omega)
      calc ‖gWeight P N k x j * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x‖
          = ‖gWeight P N k x j‖ * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x‖ :=
            norm_mul _ _
        _ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) * 1 := mul_le_mul hW hV1 (norm_nonneg _) (by positivity)
        _ = _ := mul_one _

/-! ## The `k ≥ 1` total-variation bound (counting through the level window) -/

theorem varphitildeNtj_tv_kpos_aux (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    {a : ℕ → NNReal} (ha1 : ∀ n, 1 ≤ a n) (k : ℕ) (hk : 1 ≤ k) (j : ℤ)
    (hj : j = 1 ∨ j = -1) (t x : ℝ) (K M : ℕ)
    (hcard : ((Finset.range (K + 1)).filter
      (fun m => Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a m)) k t x ≠ 0)).card
        ≤ 3 * M) :
    ∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a (n + 1))) k j t x
        - varphitildeNtj P (Nat.floor (a n)) k j t x‖
      ≤ 6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * M := by
  classical
  have hN1 : ∀ m : ℕ, 1 ≤ Nat.floor (a m) := fun m => Nat.le_floor (by exact_mod_cast ha1 m)
  have hB : (0 : ℝ) < (2 : ℝ) ^ (2 * P.natDegree + 1) := by positivity
  have hpt : ∀ m : ℕ,
      ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) := by
    intro m
    have hjmem : j ∈ ({-1, 0, 1} : Finset ℤ) := by
      rcases hj with h | h <;> rw [h] <;> simp
    exact varphitildeNtj_pointwise P hd (Nat.floor (a m)) k j t x (hN1 m) hjmem (Or.inl (by omega))
  have hsub : ((Finset.range (K + 1)).filter
        (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0))
      ⊆ ((Finset.range (K + 1)).filter
        (fun m => Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a m)) k t x ≠ 0)) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, fun h0 => hm.2 ?_⟩
    rw [varphitildeNtj_eq_gWeight_mul, h0, mul_zero]
  have hcard2 : ((Finset.range (K + 1)).filter
      (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0)).card ≤ 3 * M :=
    le_trans (Finset.card_le_card hsub) hcard
  have hsum_eq : (∑ m ∈ (Finset.range (K + 1)).filter
        (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0),
        ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖)
      = ∑ m ∈ Finset.range (K + 1), ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖ := by
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun m hm hnot => ?_)
    simp only [Finset.mem_filter, not_and] at hnot
    by_cases hm0 : varphitildeNtj P (Nat.floor (a m)) k j t x = 0
    · rw [hm0, norm_zero]
    · exact absurd hm0 (hnot hm)
  have h1 : (∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a (n + 1))) k j t x‖)
      ≤ ∑ m ∈ Finset.range (K + 1), ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖ := by
    linarith [Finset.sum_range_succ' (fun m : ℕ => ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖) K,
      norm_nonneg (varphitildeNtj P (Nat.floor (a 0)) k j t x)]
  have h2 : (∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a n)) k j t x‖)
      ≤ ∑ m ∈ Finset.range (K + 1), ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖ := by
    linarith [Finset.sum_range_succ (fun m : ℕ => ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖) K,
      norm_nonneg (varphitildeNtj P (Nat.floor (a K)) k j t x)]
  calc ∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a (n + 1))) k j t x
          - varphitildeNtj P (Nat.floor (a n)) k j t x‖
      ≤ ∑ n ∈ Finset.range K, (‖varphitildeNtj P (Nat.floor (a (n + 1))) k j t x‖
          + ‖varphitildeNtj P (Nat.floor (a n)) k j t x‖) :=
        Finset.sum_le_sum (fun n _ => norm_sub_le _ _)
    _ = (∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a (n + 1))) k j t x‖)
          + ∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a n)) k j t x‖ :=
        Finset.sum_add_distrib
    _ ≤ 2 * ∑ m ∈ Finset.range (K + 1), ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖ := by
        linarith
    _ = 2 * ∑ m ∈ (Finset.range (K + 1)).filter
          (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0),
          ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖ := by rw [hsum_eq]
    _ ≤ 2 * ((2 : ℝ) ^ (2 * P.natDegree + 1)
          * (((Finset.range (K + 1)).filter
              (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0)).card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc ∑ m ∈ (Finset.range (K + 1)).filter
              (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0),
              ‖varphitildeNtj P (Nat.floor (a m)) k j t x‖
            ≤ ∑ _m ∈ (Finset.range (K + 1)).filter
                (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0),
                (2 : ℝ) ^ (2 * P.natDegree + 1) := Finset.sum_le_sum (fun m _ => hpt m)
          _ = (((Finset.range (K + 1)).filter
                (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0)).card : ℝ)
                * (2 : ℝ) ^ (2 * P.natDegree + 1) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = (2 : ℝ) ^ (2 * P.natDegree + 1) * (((Finset.range (K + 1)).filter
                (fun m => varphitildeNtj P (Nat.floor (a m)) k j t x ≠ 0)).card : ℝ) := by ring
    _ ≤ 2 * ((2 : ℝ) ^ (2 * P.natDegree + 1) * (3 * M : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hB.le) (by norm_num)
        exact_mod_cast hcard2
    _ = 6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * M := by push_cast; ring

/-! ## The `k = 0`, `j = 1` total-variation bound (crossing of the level `2^d`) -/

/-- The walk `N^d |x|` is at most `2^d` times the scaled variable `2^{d Log N}|x|`. -/
theorem gNr_le (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (a : ℕ → NNReal) (x : ℝ) (m : ℕ) :
    (Nat.floor (a m) : ℝ) ^ P.natDegree * |x|
      ≤ (2 : ℝ) ^ P.natDegree * gxi P a 0 x m := by
  unfold gxi
  have hlt := lt_two_mul_pow_logN (Nat.floor (a m))
  have h1 : ((Nat.floor (a m) : ℝ)) ^ P.natDegree
      < (2 * (2 : ℝ) ^ (((Work.Analysis.EndVar.logN (Nat.floor (a m)) : ℤ) : ℝ)))
        ^ P.natDegree := pow_lt_pow_left₀ hlt (by positivity) (by omega)
  rw [mul_pow, two_pow_logN_pow_natDegree] at h1
  calc (Nat.floor (a m) : ℝ) ^ P.natDegree * |x|
      ≤ (2 : ℝ) ^ P.natDegree
          * (2 : ℝ) ^ ((P.natDegree : ℝ)
            * ((Work.Analysis.EndVar.logN (Nat.floor (a m)) : ℝ))) * |x| :=
        mul_le_mul_of_nonneg_right h1.le (abs_nonneg x)
    _ = (2 : ℝ) ^ P.natDegree * gxi P a 0 x m := by
        simp only [gxi_apply, Nat.cast_zero, sub_zero]
        ring

theorem varphitildeNtj_tv_k0_one (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (Λ : NNReal)
    (hΛ : 1 < Λ) {a : ℕ → NNReal} (ha : PointwiseErgodicTheorems.Lacunary Λ a)
    (ha1 : ∀ n, 1 ≤ a n) (t x : ℝ) (K : ℕ) {C2 : ℝ}
    (hC2 : ∑ n ∈ Finset.range K, ‖Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x‖ ≤ C2) :
    ∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
        - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖
      ≤ (2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ (P.natDegree + 2) := by
  classical
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hd0 : P.natDegree ≠ 0 := by omega
  -- the product form of the twisted bump
  have hUWV : ∀ m : ℕ, varphitildeNtj P (Nat.floor (a m)) 0 1 t x
      = ((((Nat.floor (a m) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ) * Gfam P a 0 t m x := by
    intro m
    rw [varphitildeNtj_eq_gWeight_mul]
    congr 1
    unfold gWeight
    rw [show (2 : ℝ) ^ (-((P.natDegree : ℝ) * ((0 : ℕ) : ℝ))) = 1 by
      rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero], one_mul, zpow_one]
  -- the monotone walk
  have hWrmono : Monotone (fun m : ℕ => (Nat.floor (a m) : ℝ) ^ P.natDegree * |x|) := by
    intro p q hpq
    have h1 : Nat.floor (a p) ≤ Nat.floor (a q) := lacunary_floor_mono Λ hΛ ha hpq
    have h2 : ((Nat.floor (a p) : ℝ)) ≤ ((Nat.floor (a q) : ℝ)) := by exact_mod_cast h1
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) h2 _) (abs_nonneg x)
  have hWr0 : 0 ≤ (Nat.floor (a 0) : ℝ) ^ P.natDegree * |x| := by positivity
  -- norms
  have hWnorm : ∀ m : ℕ, ‖((((Nat.floor (a m) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)‖
      = (Nat.floor (a m) : ℝ) ^ P.natDegree * |x| := by
    intro m
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
  have hWdiff : ∀ n : ℕ,
      ‖((((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)
          - ((((Nat.floor (a n) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)‖
        = (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x|
          - (Nat.floor (a n) : ℝ) ^ P.natDegree * |x| := by
    intro n
    have hmono : ((Nat.floor (a n) : ℝ)) ≤ ((Nat.floor (a (n + 1)) : ℝ)) := by
      have := lacunary_floor_mono Λ hΛ ha (Nat.le_succ n)
      exact_mod_cast this
    have hpow : ((Nat.floor (a n) : ℝ)) ^ P.natDegree
        ≤ ((Nat.floor (a (n + 1)) : ℝ)) ^ P.natDegree :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hmono _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * x
          - (Nat.floor (a n) : ℝ) ^ P.natDegree * x
        = (((Nat.floor (a (n + 1)) : ℝ)) ^ P.natDegree
            - ((Nat.floor (a n) : ℝ)) ^ P.natDegree) * x by ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr hpow)]
    ring
  -- the pointwise bound of the twisted bump on its support
  have hVapp : ∀ m : ℕ, Gfam P a 0 t m x = Work.KMTAreas.A7.varphitildeNt P P.natDegree
      (Nat.floor (a m)) 0 t x := fun m => rfl
  have hpt : ∀ m : ℕ, varphitildeNtj P (Nat.floor (a m)) 0 1 t x ≠ 0 →
      ‖varphitildeNtj P (Nat.floor (a m)) 0 1 t x‖ ≤ (2 : ℝ) ^ (P.natDegree + 1) := by
    intro m hm
    have hVm : Gfam P a 0 t m x ≠ 0 := by
      intro h0
      exact hm (by rw [hUWV m, h0, mul_zero])
    have hxi : gxi P a 0 x m ≤ 1 :=
      varphitildeNt_xi_le_one P hd (Nat.floor (a m)) 0 t x (by rw [← hVapp m]; exact hVm)
    have hWm : ‖((((Nat.floor (a m) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)‖
        ≤ (2 : ℝ) ^ P.natDegree := by
      rw [hWnorm]
      have h2 := gNr_le P hd a x m
      have h3 : (2 : ℝ) ^ P.natDegree * gxi P a 0 x m ≤ (2 : ℝ) ^ P.natDegree * 1 :=
        mul_le_mul_of_nonneg_left hxi (by positivity)
      linarith [h2, h3]
    have hV1 : ‖Gfam P a 0 t m x‖ ≤ 1 :=
      varphitildeNt_norm_le_one P P.natDegree (Nat.floor (a m)) 0 t x
    calc ‖varphitildeNtj P (Nat.floor (a m)) 0 1 t x‖
        = ‖((((Nat.floor (a m) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ) * Gfam P a 0 t m x‖ := by
          rw [hUWV m]
      _ = ‖((((Nat.floor (a m) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)‖ * ‖Gfam P a 0 t m x‖ :=
          norm_mul _ _
      _ ≤ (2 : ℝ) ^ P.natDegree * 1 := mul_le_mul hWm hV1 (norm_nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ (P.natDegree + 1) := by
          rw [mul_one]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
  -- the bound on the cut
  have honCut : ∀ n : ℕ, (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree →
      ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
          - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖
        ≤ (2 : ℝ) ^ P.natDegree * ‖Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x‖
          + ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x|
              - (Nat.floor (a n) : ℝ) ^ P.natDegree * |x|) := by
    intro n hn
    have hWn : ‖((((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)‖
        ≤ (2 : ℝ) ^ P.natDegree := by rw [hWnorm]; exact hn
    have hVn : ‖Gfam P a 0 t n x‖ ≤ 1 :=
      varphitildeNt_norm_le_one P P.natDegree (Nat.floor (a n)) 0 t x
    have hdecomp : varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
          - varphitildeNtj P (Nat.floor (a n)) 0 1 t x
        = ((((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)
            * (Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x)
          + (((((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)
              - ((((Nat.floor (a n) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)) * Gfam P a 0 t n x := by
      rw [hUWV (n + 1), hUWV n]; ring
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖((((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)‖
        * ‖Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x‖
        ≤ (2 : ℝ) ^ P.natDegree * ‖Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x‖ :=
      mul_le_mul_of_nonneg_right hWn (norm_nonneg _)
    have h2 : ‖((((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)
          - ((((Nat.floor (a n) : ℝ) ^ P.natDegree * x : ℝ)) : ℂ)‖ * ‖Gfam P a 0 t n x‖
        ≤ ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x|
            - (Nat.floor (a n) : ℝ) ^ P.natDegree * |x|) := by
      rw [hWdiff n]
      have h3 : (0 : ℝ) ≤ (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x|
          - (Nat.floor (a n) : ℝ) ^ P.natDegree * |x| := by
        have := hWrmono (Nat.le_succ n); linarith
      exact mul_le_of_le_one_right h3 hVn
    linarith
  -- the weight-variation sum over the cut
  have hsumWcut : ∑ n ∈ (Finset.range K).filter
        (fun n => (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree),
        ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x|
          - (Nat.floor (a n) : ℝ) ^ P.natDegree * |x|)
      ≤ (2 : ℝ) ^ P.natDegree :=
    sum_diff_filter_le hWrmono hWr0 K (c := (2 : ℝ) ^ P.natDegree) (by positivity)
  -- the V-variation sum over the cut
  have hsumVcut : ∑ n ∈ (Finset.range K).filter
        (fun n => (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree),
        ‖Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x‖ ≤ C2 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => norm_nonneg _)) hC2
  have hC2nn : 0 ≤ C2 := le_trans (Finset.sum_nonneg (fun n _ => norm_nonneg _)) hC2
  have hon : ∑ n ∈ (Finset.range K).filter
        (fun n => (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree),
        ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
          - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖
      ≤ (2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ P.natDegree := by
    calc ∑ n ∈ (Finset.range K).filter
          (fun n => (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree),
          ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
            - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖
        ≤ ∑ n ∈ (Finset.range K).filter
            (fun n => (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree),
            ((2 : ℝ) ^ P.natDegree * ‖Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x‖
              + ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x|
                  - (Nat.floor (a n) : ℝ) ^ P.natDegree * |x|)) :=
          Finset.sum_le_sum (fun n hn => honCut n (Finset.mem_filter.mp hn).2)
      _ = (2 : ℝ) ^ P.natDegree
            * ∑ n ∈ (Finset.range K).filter
                (fun n => (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree),
                ‖Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x‖
          + ∑ n ∈ (Finset.range K).filter
              (fun n => (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree),
              ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x|
                - (Nat.floor (a n) : ℝ) ^ P.natDegree * |x|) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ P.natDegree * C2 + (2 : ℝ) ^ P.natDegree :=
          add_le_add (mul_le_mul_of_nonneg_left hsumVcut (by positivity)) hsumWcut
      _ ≤ (2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ P.natDegree := by
          have hmono : (2 : ℝ) ^ P.natDegree ≤ (2 : ℝ) ^ (P.natDegree + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          nlinarith [hC2nn, hmono, pow_pos h2pos P.natDegree]
  -- the off-cut bound: off the cut the `(n+1)`-th bump vanishes, so at most one term survives
  have hVzero : ∀ n : ℕ,
      ¬ ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree) →
      Gfam P a 0 t (n + 1) x = 0 := by
    intro n hncut
    have hncut' : (2 : ℝ) ^ P.natDegree
        < (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| := not_le.mp hncut
    have hle := gNr_le P hd a x (n + 1)
    have hxi1 : 1 < gxi P a 0 x (n + 1) := by
      nlinarith [hncut', hle, pow_pos h2pos P.natDegree]
    have harg : 1 ≤ |Work.KMTPlan.A6.GZ P a (n + 1) * x| := by
      rw [Work.KMTPlan.A6.GZ, abs_mul, abs_of_pos (Real.rpow_pos_of_pos h2pos _)]
      have h := hxi1
      unfold gxi at h
      simp only [Nat.cast_zero, sub_zero] at h
      exact h.le
    rw [Work.KMTPlan.A6.Gfam_zero_eq_Gph, Work.KMTPlan.A6.Gph,
      Work.KMTContract.kmtEta_zero harg, zero_mul]
  have hUn : ∀ n : ℕ,
      ¬ ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree) →
      varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
          - varphitildeNtj P (Nat.floor (a n)) 0 1 t x ≠ 0 →
      varphitildeNtj P (Nat.floor (a n)) 0 1 t x ≠ 0 := by
    intro n hncut hndiff h0
    apply hndiff
    rw [hUWV (n + 1), hVzero n hncut, mul_zero, h0, sub_zero]
  have hoff : ∑ n ∈ (Finset.range K).filter
        (fun n => ¬ ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree)),
        ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
          - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖
      ≤ (2 : ℝ) ^ (P.natDegree + 1) := by
    set Toff : Finset ℕ := ((Finset.range K).filter
        (fun n => ¬ ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree))).filter
        (fun n => varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
          - varphitildeNtj P (Nat.floor (a n)) 0 1 t x ≠ 0) with hToff
    have hToffsub : Toff ⊆ (Finset.range K).filter
        (fun n => gxi P a 0 x n ≤ 1 ∧ 1 < gxi P a 0 x (n + 1)) := by
      intro n hn
      rw [hToff, Finset.mem_filter, Finset.mem_filter] at hn
      obtain ⟨⟨hnK, hncut⟩, hndiff⟩ := hn
      rw [Finset.mem_filter]
      have hncut' : (2 : ℝ) ^ P.natDegree
          < (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| := not_le.mp hncut
      have hle := gNr_le P hd a x (n + 1)
      have hxi1 : 1 < gxi P a 0 x (n + 1) := by
        nlinarith [hncut', hle, pow_pos h2pos P.natDegree]
      have hU0 : varphitildeNtj P (Nat.floor (a n)) 0 1 t x ≠ 0 := hUn n hncut hndiff
      have hVn : Gfam P a 0 t n x ≠ 0 := by
        intro h0
        exact hU0 (by rw [hUWV n, h0, mul_zero])
      have hxin : gxi P a 0 x n ≤ 1 :=
        varphitildeNt_xi_le_one P hd (Nat.floor (a n)) 0 t x (by rw [← hVapp n]; exact hVn)
      exact ⟨hnK, hxin, hxi1⟩
    have hTcard : Toff.card ≤ 1 :=
      le_trans (Finset.card_le_card hToffsub)
        (card_crossing_le_one (gxi_mono P Λ hΛ ha 0 x) K (c := 1))
    have hsub : Toff ⊆ (Finset.range K).filter
        (fun n => ¬ ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree)) :=
      fun n hn => (Finset.mem_filter.mp (by rw [hToff] at hn; exact hn)).1
    have hsum_eq : ∑ n ∈ (Finset.range K).filter
          (fun n => ¬ ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree)),
          ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
            - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖
        = ∑ n ∈ Toff, ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
            - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖ := by
      refine (Finset.sum_subset hsub (fun n hn hnot => ?_)).symm
      rw [hToff, Finset.mem_filter, not_and] at hnot
      by_cases hd0' : varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
          - varphitildeNtj P (Nat.floor (a n)) 0 1 t x = 0
      · rw [hd0', norm_zero]
      · exact absurd hd0' (hnot hn)
    calc ∑ n ∈ (Finset.range K).filter
          (fun n => ¬ ((Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree)),
          ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
            - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖
        = ∑ n ∈ Toff, ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
            - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖ := hsum_eq
      _ ≤ ∑ _n ∈ Toff, (2 : ℝ) ^ (P.natDegree + 1) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [hToff, Finset.mem_filter, Finset.mem_filter] at hn
          obtain ⟨⟨-, hncut⟩, hndiff⟩ := hn
          have hU0 : varphitildeNtj P (Nat.floor (a n)) 0 1 t x ≠ 0 := hUn n hncut hndiff
          rw [hUWV (n + 1), hVzero n hncut, mul_zero, zero_sub, norm_neg]
          exact hpt n hU0
      _ = (Toff.card : ℝ) * (2 : ℝ) ^ (P.natDegree + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 : ℝ) ^ (P.natDegree + 1) := by
          have h1 : (Toff.card : ℝ) ≤ 1 := by exact_mod_cast hTcard
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2 : ℝ) ^ (P.natDegree + 1) := one_mul _
  -- combine the two parts
  have hcombine := Finset.sum_filter_add_sum_filter_not (s := Finset.range K)
    (p := fun n => (Nat.floor (a (n + 1)) : ℝ) ^ P.natDegree * |x| ≤ (2 : ℝ) ^ P.natDegree)
    (f := fun n => ‖varphitildeNtj P (Nat.floor (a (n + 1))) 0 1 t x
      - varphitildeNtj P (Nat.floor (a n)) 0 1 t x‖)
  rw [← hcombine]
  have hpow2 : (2 : ℝ) ^ P.natDegree + (2 : ℝ) ^ (P.natDegree + 1)
      ≤ (2 : ℝ) ^ (P.natDegree + 2) := by
    rw [show (2 : ℝ) ^ (P.natDegree + 2) = (2 : ℝ) ^ (P.natDegree + 1) * 2 by rw [pow_succ],
      show (2 : ℝ) ^ (P.natDegree + 1) = (2 : ℝ) ^ P.natDegree * 2 by rw [pow_succ]]
    linarith [pow_pos h2pos P.natDegree]
  linarith [hon, hoff, hpow2]

/-! ## The level count for the `g`-side bump at heights `k ≥ 1` -/

theorem lowModRandG_level_count (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) {Λ : NNReal}
    (hΛ : 1 < Λ) {a : ℕ → NNReal} (ha : PointwiseErgodicTheorems.Lacunary Λ a) {k : ℕ} (hk : 1 ≤ k)
    {t x : ℝ} {K M : ℕ}
    (hM : ∀ j : ℤ, ((Finset.range (K + 1)).filter
      (fun m => Work.Analysis.EndVar.logN (Nat.floor (a m)) = j)).card ≤ M) :
    ((Finset.range (K + 1)).filter
      (fun m => Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a m)) k t x ≠ 0)).card
      ≤ 3 * M := by
  classical
  set S : Finset ℕ := (Finset.range (K + 1)).filter (fun m => Gfam P a k t m x ≠ 0) with hS
  by_cases hne : S.Nonempty
  · obtain ⟨m₀, hm₀⟩ := hne
    have hm₀U : Gfam P a k t m₀ x ≠ 0 := (Finset.mem_filter.mp hm₀).2
    have hx0 : x ≠ 0 := by
      intro hx0
      have hzero : ∀ N : ℕ, Work.KMTAreas.A7.varphitildeN P.natDegree N k 0 = 0 := by
        intro N
        have hkne : k ≠ 0 := by omega
        simp only [Work.KMTAreas.A7.varphitildeN, if_neg hkne]
        simp [Work.KMTContract.kmtEta_one (by norm_num : |(0 : ℝ)| ≤ 1 / 2)]
      have hgoal : Gfam P a k t m₀ x = 0 := by
        rw [show Gfam P a k t m₀ x
            = Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a m₀)) k x
              * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a m₀) : ℝ) * t) * x)
            from rfl,
          hx0, hzero (Nat.floor (a m₀)), zero_mul]
      exact hm₀U hgoal
    have hxpos : 0 < |x| := abs_pos.mpr hx0
    set j₀ : ℤ := Work.Analysis.EndVar.logN (Nat.floor (a m₀)) with hj₀
    have hsub : S ⊆ (Finset.Icc (j₀ - 1) (j₀ + 1)).biUnion (fun j =>
          ((Finset.range (K + 1)).filter (fun m => Work.Analysis.EndVar.logN (Nat.floor (a m)) = j))) := by
      intro m hm
      have hmU : Gfam P a k t m x ≠ 0 := (Finset.mem_filter.mp hm).2
      have h1 : Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a m)) k x ≠ 0 := by
        intro h0
        exact hmU (by
          rw [show Gfam P a k t m x
              = Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a m)) k x
                * Work.KMTAreas.A7.ee
                    (Work.KMTAreas.A7.PevalR P ((Nat.floor (a m) : ℝ) * t) * x) from rfl,
            h0, zero_mul])
      have h2 : Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a m₀)) k x ≠ 0 := by
        intro h0
        exact hm₀U (by
          rw [show Gfam P a k t m₀ x
              = Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a m₀)) k x
                * Work.KMTAreas.A7.ee
                    (Work.KMTAreas.A7.PevalR P ((Nat.floor (a m₀) : ℝ) * t) * x) from rfl,
            h0, zero_mul])
      have hlev := level_close_G hd hk hxpos h1 h2
      refine Finset.mem_biUnion.mpr ⟨Work.Analysis.EndVar.logN (Nat.floor (a m)), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        rw [abs_le] at hlev
        obtain ⟨hlev1, hlev2⟩ := hlev
        constructor <;> omega
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1, rfl⟩
    calc S.card
        ≤ ((Finset.Icc (j₀ - 1) (j₀ + 1)).biUnion (fun j =>
            ((Finset.range (K + 1)).filter (fun m => Work.Analysis.EndVar.logN (Nat.floor (a m)) = j)))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.Icc (j₀ - 1) (j₀ + 1),
            ((Finset.range (K + 1)).filter (fun m => Work.Analysis.EndVar.logN (Nat.floor (a m)) = j)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.Icc (j₀ - 1) (j₀ + 1), M :=
          Finset.sum_le_sum (fun j _ => hM j)
      _ ≤ 3 * M := by
          rw [Finset.sum_const, smul_eq_mul]
          have h3 : (Finset.Icc (j₀ - 1) (j₀ + 1)).card ≤ 3 := by
            rw [Int.card_Icc]
            have hthis : ((j₀ + 1) + 1 - (j₀ - 1) : ℤ) = 3 := by ring
            rw [hthis]
            simp
          exact Nat.mul_le_mul_right _ h3
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-! ## Clamping with the pointwise bound `B` -/

theorem lowModRandG_clamped_bound_le {T : Set ℕ} [DecidablePred (· ∈ T)]
    (hT : ∀ {n j m : ℕ}, n ≤ j → j ≤ m → n ∈ T → m ∈ T → j ∈ T)
    {ψ : ℕ → ℝ → ℂ} {ε : ℕ → ℂ} {K : ℕ} {x : ℝ} {Cv B : ℝ} (hB : 0 ≤ B)
    (hψ : ∀ n, ‖ψ n x‖ ≤ B)
    (hvar : ∑ n ∈ Finset.range K, ‖ψ (n + 1) x - ψ n x‖ ≤ Cv)
    (hε : ∀ n, ‖ε n‖ ≤ 1) :
    ‖Work.KMTAreas.A7.randSymb (fun n ξ => if n ∈ T then ψ n ξ else 0) ε K x‖ ≤ Cv + 2 * B := by
  classical
  set d : ℕ → ℂ := fun n => ψ n x with hd
  set c : ℕ → ℂ := fun n => if n ∈ T then d n else 0 with hc
  have hsym : (Work.KMTAreas.A7.randSymb (fun n ξ => if n ∈ T then ψ n ξ else 0) ε K) x
      = ∑ n ∈ Finset.range K, ε n * (c (n + 1) - c n) := by
    simp only [Work.KMTAreas.A7.randSymb]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hc, hd]
  have hterm : ∀ n : ℕ, ‖c (n + 1) - c n‖ ≤ ‖d (n + 1) - d n‖ +
      (if (n ∈ T ↔ n + 1 ∈ T) then 0 else B : ℝ) := by
    intro n
    have hdn : ‖d n‖ ≤ B := hψ n
    have hdn1 : ‖d (n + 1)‖ ≤ B := hψ (n + 1)
    by_cases h1 : n ∈ T <;> by_cases h2 : n + 1 ∈ T
    · have hc1 : c n = d n := by simp [hc, h1]
      have hc2 : c (n + 1) = d (n + 1) := by simp [hc, h2]
      have hij : (n ∈ T ↔ n + 1 ∈ T) := ⟨fun _ => h2, fun _ => h1⟩
      rw [hc1, hc2, if_pos hij]; simp
    · have hc1 : c n = d n := by simp [hc, h1]
      have hc2 : c (n + 1) = 0 := by simp [hc, h2]
      have hij : ¬ (n ∈ T ↔ n + 1 ∈ T) := fun hh => h2 (hh.mp h1)
      rw [hc1, hc2, if_neg hij]
      simp only [zero_sub, norm_neg]
      linarith [norm_nonneg (d (n + 1) - d n)]
    · have hc1 : c n = 0 := by simp [hc, h1]
      have hc2 : c (n + 1) = d (n + 1) := by simp [hc, h2]
      have hij : ¬ (n ∈ T ↔ n + 1 ∈ T) := fun hh => h1 (hh.mpr h2)
      rw [hc1, hc2, if_neg hij]
      simp only [sub_zero]
      linarith [norm_nonneg (d (n + 1) - d n)]
    · have hc1 : c n = 0 := by simp [hc, h1]
      have hc2 : c (n + 1) = 0 := by simp [hc, h2]
      have hij : (n ∈ T ↔ n + 1 ∈ T) := ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
      rw [hc1, hc2, if_pos hij]; simp
  have hjump : ∑ n ∈ Finset.range K, (if (n ∈ T ↔ n + 1 ∈ T) then (0 : ℝ) else B)
      = (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) * B := by
    have h1 : ∀ n : ℕ, (if (n ∈ T ↔ n + 1 ∈ T) then (0 : ℝ) else B)
        = ((if ¬ (n ∈ T ↔ n + 1 ∈ T) then (1 : ℕ) else 0 : ℕ) : ℝ) * B := by
      intro n
      by_cases h : (n ∈ T ↔ n + 1 ∈ T) <;> simp [h]
    rw [Finset.sum_congr rfl (fun n _ => h1 n), ← Finset.sum_mul, ← Nat.cast_sum,
      Finset.sum_boole]
    simp
  have hcard : (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) ≤ 2 := by
    have := card_jump_le_two hT K
    exact_mod_cast this
  have hsum : ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖ ≤ Cv + 2 * B := by
    have h1 : ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖
        ≤ ∑ n ∈ Finset.range K, (‖d (n + 1) - d n‖
            + (if (n ∈ T ↔ n + 1 ∈ T) then 0 else B : ℝ)) :=
      Finset.sum_le_sum fun n _ => hterm n
    have h2 : ∑ n ∈ Finset.range K, (‖d (n + 1) - d n‖
            + (if (n ∈ T ↔ n + 1 ∈ T) then 0 else B : ℝ))
        = (∑ n ∈ Finset.range K, ‖d (n + 1) - d n‖)
          + ∑ n ∈ Finset.range K, (if (n ∈ T ↔ n + 1 ∈ T) then 0 else B : ℝ) :=
      Finset.sum_add_distrib
    rw [h2, hjump] at h1
    have h3 : (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) * B ≤ 2 * B :=
      mul_le_mul_of_nonneg_right hcard hB
    have h4 : (∑ n ∈ Finset.range K, ‖d (n + 1) - d n‖)
        = ∑ n ∈ Finset.range K, ‖ψ (n + 1) x - ψ n x‖ := by simp only [hd]
    rw [h4] at h1
    linarith
  calc ‖(Work.KMTAreas.A7.randSymb (fun n ξ => if n ∈ T then ψ n ξ else 0) ε K) x‖
      = ‖∑ n ∈ Finset.range K, ε n * (c (n + 1) - c n)‖ := by rw [hsym]
    _ ≤ ∑ n ∈ Finset.range K, ‖ε n * (c (n + 1) - c n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖ := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hε n)
    _ ≤ Cv + 2 * B := hsum

/-! ## The total-variation bound for the twisted family -/

theorem varphitildeNtj_varBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (Lη : ℝ) (hLη : 0 < Lη)
    (hη : ∀ u v : ℝ, ‖Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta v‖ ≤ Lη * |u - v|)
    (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (k : ℕ) (j : ℤ) (t x : ℝ) (K : ℕ),
      j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k = 0 ∧ j = -1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a (n + 1))) k j t x
          - varphitildeNtj P (Nat.floor (a n)) k j t x‖ ≤ Cv := by
  classical
  obtain ⟨Mlev, hMlev⟩ := lacunaryLevel
  obtain ⟨C1, hC1nn, hC1⟩ := randSymbG_TV_kpos P hd Λ hΛ
  obtain ⟨C2, hC2nn, hC2⟩ := randSymbG_TV_k0 P hd Λ hΛ Lη hLη hη
  have hd1 : 1 ≤ P.natDegree := by omega
  have hnn1 : (0 : ℝ) ≤ 6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * (Mlev Λ : ℝ) := by positivity
  have hnn2 : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ (P.natDegree + 2) := by
    positivity
  refine ⟨max C1 C2 + (6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * (Mlev Λ : ℝ))
      + ((2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ (P.natDegree + 2)) + 1,
    by positivity, ?_⟩
  intro a ha ha1 k j t x K hj hjk ht
  have hj' : j = 1 ∨ j = 0 ∨ j = -1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    tauto
  have hleC1 : C1 ≤ max C1 C2 + (6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * (Mlev Λ : ℝ))
      + ((2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ (P.natDegree + 2)) + 1 := by
    linarith [hnn1, hnn2, le_max_left C1 C2]
  have hleC2 : C2 ≤ max C1 C2 + (6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * (Mlev Λ : ℝ))
      + ((2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ (P.natDegree + 2)) + 1 := by
    linarith [hnn1, hnn2, le_max_right C1 C2]
  have hleM : 6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * (Mlev Λ : ℝ)
      ≤ max C1 C2 + (6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * (Mlev Λ : ℝ))
      + ((2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ (P.natDegree + 2)) + 1 := by
    have hmax : 0 ≤ max C1 C2 := le_trans hC1nn (le_max_left C1 C2)
    linarith [hnn2, hmax]
  have hleK0 : (2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ (P.natDegree + 2)
      ≤ max C1 C2 + (6 * (2 : ℝ) ^ (2 * P.natDegree + 1) * (Mlev Λ : ℝ))
      + ((2 : ℝ) ^ (P.natDegree + 1) * C2 + (2 : ℝ) ^ (P.natDegree + 2)) + 1 := by
    have hmax : 0 ≤ max C1 C2 := le_trans hC1nn (le_max_left C1 C2)
    linarith [hnn1, hmax]
  rcases hj' with h1 | h0 | hm1
  · -- `j = 1`
    subst h1
    rcases eq_or_ne k 0 with hk | hk
    · subst hk
      refine le_trans (varphitildeNtj_tv_k0_one P hd1 Λ hΛ ha ha1 t x K
        (hC2 a t x K ha ha1 ht)) hleK0
    · have hk1 : 1 ≤ k := by omega
      have hcnt : ((Finset.range (K + 1)).filter
          (fun m => Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a m)) k t x ≠ 0)).card
            ≤ 3 * Mlev Λ :=
        lowModRandG_level_count P hd1 hΛ ha hk1
          (fun jl => hMlev a Λ hΛ ha ha1 jl (Finset.range (K + 1)))
      refine le_trans (varphitildeNtj_tv_kpos_aux P hd1 ha1 k hk1 1 (Or.inl rfl) t x K
        (Mlev Λ) hcnt) hleM
  · -- `j = 0`
    subst h0
    have heq : ∑ n ∈ Finset.range K, ‖varphitildeNtj P (Nat.floor (a (n + 1))) k 0 t x
          - varphitildeNtj P (Nat.floor (a n)) k 0 t x‖
        = ∑ n ∈ Finset.range K, ‖Gfam P a k t (n + 1) x - Gfam P a k t n x‖ := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [varphitildeNtj_zero, varphitildeNtj_zero]
    rw [heq]
    rcases eq_or_ne k 0 with hk | hk
    · subst hk
      exact le_trans (hC2 a t x K ha ha1 ht) hleC2
    · exact le_trans (hC1 a k t x K (by omega) ha ha1 ht) hleC1
  · -- `j = -1`, hence `k ≠ 0`
    rw [hm1]
    have hk1 : 1 ≤ k := by
      by_contra h
      push_neg at h
      exact hjk ⟨by omega, hm1⟩
    have hcnt : ((Finset.range (K + 1)).filter
        (fun m => Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a m)) k t x ≠ 0)).card
          ≤ 3 * Mlev Λ :=
      lowModRandG_level_count P hd1 hΛ ha hk1
        (fun jl => hMlev a Λ hΛ ha ha1 jl (Finset.range (K + 1)))
    refine le_trans (varphitildeNtj_tv_kpos_aux P hd1 ha1 k hk1 (-1) (Or.inr rfl) t x K
      (Mlev Λ) hcnt) hleM

/-! ## Support and measurability of the anchored clamped family -/

theorem lowModRandG_support_of {ρ : ℝ} {P : Polynomial ℤ} {C₀ : ℕ} {a : ℕ → NNReal}
    {l₁ l₂ k₁ k₂ n : ℕ} {j : ℤ} {t x : ℝ}
    (h : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t n x ≠ 0) :
    n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n ∧
      varphitildeNtj P (Nat.floor (a n)) k₂ j t x ≠ 0 := by
  by_cases h0 : n = 0
  · simp only [lowModSymbG, if_pos h0] at h
    exact absurd rfl h
  · simp only [lowModSymbG, if_neg h0] at h
    by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [if_pos hls] at h
      exact ⟨h0, hls, h⟩
    · simp only [if_neg hls] at h
      exact absurd rfl h

theorem lowModRandG_symbsupport (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ K : ℕ) (j : ℤ) (t : ℝ) (ε : ℕ → ℂ) :
    ∀ x : ℝ, Work.KMTAreas.A7.randSymb
        (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t) ε K x ≠ 0 →
      |x| ≤ (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ) := by
  intro x hx
  obtain ⟨n, -, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hx
  obtain ⟨-, -, hbump⟩ := lowModRandG_support_of (h := hn)
  have hbump' : Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t x ≠ 0 :=
    fun h0 => hbump (by rw [varphitildeNtj_eq_gWeight_mul, h0, mul_zero])
  have hsupp := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree (Nat.floor (a n))
    k₂ t x hbump'
  have hlog0 : (0 : ℝ) ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by
    exact_mod_cast Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n))
  have hexp : (P.natDegree : ℝ)
        * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))
      ≤ (((P.natDegree * k₂ : ℕ)) : ℝ) := by
    have hdn : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [hdn, hlog0]
  calc |x| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))) := hsupp
    _ ≤ (2 : ℝ) ^ ((((P.natDegree * k₂ : ℕ)) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2 : ℝ) ^ ((((P.natDegree * k₂ : ℕ)) : ℤ)) := by
        rw [Work.KMTPlan.A6.two_zpow_eq_rpow]

theorem measurable_lowModSymbG (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j : ℤ) (t : ℝ) (h : k₂ ≠ 0 ∨ 0 ≤ j)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (m : ℕ) :
    Measurable (fun ξ : ℝ => lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t m ξ) := by
  by_cases h0 : m = 0
  · simp only [lowModSymbG, h0, if_true]; exact measurable_const
  · simp only [lowModSymbG, if_neg h0]
    by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
    · simp only [if_pos hls]
      obtain ⟨S, -, hS⟩ := varphitildeNtj_bounds P (Nat.floor (a m)) k₂ j h
      exact ((hS t ht).1.continuous).measurable
    · simp only [if_neg hls]; exact measurable_const

/-! ## The pointwise bound of the randomised clamped symbol -/

theorem randSymb_lowModSymbG_sup_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ)
    (Lη : ℝ) (hLη : 0 < Lη)
    (hη : ∀ u v : ℝ, ‖Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta v‖ ≤ Lη * |u - v|)
    (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ)
      (ε : ℕ → ℂ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → (∀ n, ‖ε n‖ ≤ 1) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 → j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₂ = 0 ∧ j = -1) →
      ∀ x : ℝ,
        ‖Work.KMTAreas.A7.randSymb (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t) ε K x‖ ≤ C := by
  classical
  obtain ⟨Cv, hCvnn, hCv⟩ := varphitildeNtj_varBound P hd Lη hLη hη Λ hΛ
  refine ⟨Cv + 2 * (2 : ℝ) ^ (2 * P.natDegree + 1), by positivity, ?_⟩
  intro ρ a l₁ l₂ k₁ k₂ K t j ε hLac ha1 hε ht hj hjk x
  have hN1 : ∀ m : ℕ, 1 ≤ Nat.floor (a m) := fun m => Nat.le_floor (by exact_mod_cast ha1 m)
  have hkj : k₂ ≠ 0 ∨ 0 ≤ j := by
    by_cases hk : k₂ = 0
    · right
      rcases (by simpa using hj : j = -1 ∨ j = 0 ∨ j = 1) with h | h | h
      · exact absurd ⟨hk, h⟩ hjk
      · omega
      · omega
    · exact Or.inl hk
  have hBnn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) := by positivity
  have hψ : ∀ m : ℕ, ‖(fun m ξ => varphitildeNtj P (Nat.floor (a m)) k₂ j t ξ) m x‖
      ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) :=
    fun m => varphitildeNtj_pointwise P (by omega) (Nat.floor (a m)) k₂ j t x (hN1 m) hj hkj
  have hvar : ∑ n ∈ Finset.range K,
        ‖(fun m ξ => varphitildeNtj P (Nat.floor (a m)) k₂ j t ξ) (n + 1) x
          - (fun m ξ => varphitildeNtj P (Nat.floor (a m)) k₂ j t ξ) n x‖ ≤ Cv :=
    hCv a hLac ha1 k₂ j t x K hj hjk ht
  have hbound := lowModRandG_clamped_bound_le
    (T := {n : ℕ | n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n})
    (hT := by
      intro n jj m hnj hjm hn hm
      have hn' : n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n := hn
      have hm' : m ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m := hm
      refine ⟨?_, lowSmallSet_conv Λ hΛ hLac hnj hjm hn'.2 hm'.2⟩
      omega)
    (ψ := fun m ξ => varphitildeNtj P (Nat.floor (a m)) k₂ j t ξ) hBnn hψ hvar hε
  have hcongr : (fun n ξ => if n ∈ {n : ℕ | n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n}
        then (fun m ξ => varphitildeNtj P (Nat.floor (a m)) k₂ j t ξ) n ξ else 0)
      = lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t := by
    funext n ξ
    simp only [lowModSymbG, Set.mem_setOf_eq]
    by_cases h0 : n = 0
    · simp [h0]
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n <;> simp [h0, hls]
  rw [hcongr] at hbound
  exact hbound
/-- **The `ℓ²`-bound for the randomised `g`-side packets of Case B, with the structural
hypotheses of the available library** (the mirror of `Work.KMTPlan.A6.lowModRandL2Fh`).  This is
the interface `Work.KMTPlan.A6.LowModRandL2G'` of
`Submission/Work/KMTPlan/A6/LowModelVarCaseBAux.lean`: for `2 ≤ P.natDegree`, an `AreaA1` and
`1 ≤ C₀` (available in the context of the proof) there are `ρ₀ > 0`, and for every `ρ ∈ (0,ρ₀]` a
threshold `B` and a constant family `C : NNReal → NNReal` such that for every twist
`j ∈ {-1,0,1}` other than the forbidden pair `(k₂,j) = (0,-1)`, every lacunary `a`, every sign
family `‖ε n‖ ≤ 1`, every `t ∈ [1/2,1]`, every truncation `K`, every `l₁ l₂ k₁ k₂` with
`B ≤ lcL l₁ l₂ k₁ k₂` and every `g ∈ ℓ²`,
`‖Tm ρ l₂ (randSymb (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t) ε K) g‖₂ ≤ C(Λ)‖g‖₂`,
where `lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t` is the anchored, `lowSmallSet`-clamped family of
modified `g`-side bumps `φ̃_{N,k₂,j}(t)`, `N = ⌊a n⌋`.

For `j = 0` this is the proved `Work.KMTPlan.A6.tmRandSymbG_l2` (same structural hypotheses and
conclusion shape, modulo the harmless `B ≤ lcL`).  For `j ∈ {-1,1}` the modified profile
`ξ ↦ (2^{-dk₂}N^dξ)^j φ̃_{N,k₂}(ξ)` is bounded by `4` on the annulus/bottom support of the
`g`-side bump and has the smoothness/support data supplied by `varphitildeNtj_bounds`; the two
ingredients are the same as for the `f`-side: the pointwise bound of the randomised symbol from a
total-variation bound of the bump family (the `randSymb_bounded_of_varBound` mechanism, with the
`g`-side estimates of `Submission/Work/KMTAreas/A7/randSymbG_aux.lean`, in particular
`level_close_G`) and the narrow-support non-aliasing `ℓ²`-bound of `Tm`
(`iwSymbolSet_narrow_bound` + `eLpNorm_iwConv_two_le_of_symbol_bound`). -/
theorem lowModRandL2Gh (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    Work.KMTPlan.A6.LowModRandL2G' P hd hA1 C₀ hC₀ := by
  obtain ⟨Lη, hLη, hη⟩ := kmtEta_lipschitz
  refine ⟨min 1 (1 / (2 * (C₀ : ℝ))), lt_min zero_lt_one (by positivity), ?_⟩
  intro ρ hρ hρρ₀
  have hρ1 : ρ ≤ 1 := le_trans hρρ₀ (min_le_left _ _)
  have hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 2 := by
    have h := le_trans hρρ₀ (min_le_right _ _)
    have h2 : ρ * (2 * (C₀ : ℝ)) ≤ 1 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (C₀ : ℝ))).mp h
    nlinarith
  obtain ⟨Crho, hCrhoP, hNA, _⟩ := hA1 ρ hρ hρ1
  obtain ⟨L0, hL0⟩ := L_le_of_threshold_fail ρ hρ C₀ hC₀ (max Crho 2)
    (le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_right _ _)) hρC₀
  obtain ⟨Cc, hCcP, hCc⟩ := iw_height_card_le (ρ := ρ) hρ
  have hcrux : ∀ Lam : NNReal, 1 < Lam → ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Lam a → (∀ n, 1 ≤ a n) → (∀ n, ‖ε n‖ ≤ 1) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₂ = 0 ∧ j = -1) →
        ∀ x : ℝ,
          ‖Work.KMTAreas.A7.randSymb (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t) ε K x‖ ≤ C :=
    fun Lam hLam => by
      obtain ⟨C, hC, hb⟩ := randSymb_lowModSymbG_sup_le P hd C₀ Lη hLη hη Lam hLam
      exact ⟨C, hC, fun a l₁ l₂ k₁ k₂ K t j ε hLac ha1 hε ht hj hjk =>
        hb ρ a l₁ l₂ k₁ k₂ K t j ε hLac ha1 hε ht hj hjk⟩
  let cpsi : NNReal → ℝ := fun Lam => if h : 1 < Lam then Classical.choose (hcrux Lam h) else 1
  have hcpsiP : ∀ Lam : NNReal, 1 < Lam → 0 < cpsi Lam := by
    intro Lam hLam
    simp only [cpsi, dif_pos hLam]
    exact (Classical.choose_spec (hcrux Lam hLam)).1
  have hcpsiB : ∀ (Lam : NNReal) (hLam : 1 < Lam) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ)
      (t : ℝ) (j : ℤ) (ε : ℕ → ℂ),
      PointwiseErgodicTheorems.Lacunary Lam a → (∀ n, 1 ≤ a n) → (∀ n, ‖ε n‖ ≤ 1) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 → j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k₂ = 0 ∧ j = -1) →
      ∀ x : ℝ,
        ‖Work.KMTAreas.A7.randSymb (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t) ε K x‖ ≤ cpsi Lam := by
    intro Lam hLam a l₁ l₂ k₁ k₂ K t j ε hLac ha1 hε ht hj hjk
    simp only [cpsi, dif_pos hLam]
    exact (Classical.choose_spec (hcrux Lam hLam)).2 a l₁ l₂ k₁ k₂ K t j ε hLac ha1 hε ht hj hjk
  let Kf : ℝ := max 1 (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) *
    (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4))
  have hKf1 : 1 ≤ Kf := le_max_left _ _
  refine ⟨0, fun Lam => Real.toNNReal (Kf * cpsi Lam + 1), ?_⟩
  intro a Lam l₁ l₂ k₁ k₂ K t j ε g hLam hLac ha1 hε ht hj hjk hB hg
  let psig : ℕ → ℝ → ℂ := lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j t
  have hpsiran : ∀ x : ℝ, ‖Work.KMTAreas.A7.randSymb psig ε K x‖ ≤ cpsi Lam :=
    hcpsiB Lam hLam a l₁ l₂ k₁ k₂ K t j ε hLac ha1 hε ht hj hjk
  have hkj : k₂ ≠ 0 ∨ 0 ≤ j := by
    by_cases hk : k₂ = 0
    · right
      rcases (by simpa using hj : j = -1 ∨ j = 0 ∨ j = 1) with h | h | h
      · exact absurd ⟨hk, h⟩ hjk
      · omega
      · omega
    · exact Or.inl hk
  have hmeaspsig : ∀ m : ℕ, Measurable (psig m) :=
    fun m => measurable_lowModSymbG P ρ C₀ a l₁ l₂ k₁ k₂ j t hkj ht m
  have hmeas : Measurable (Work.KMTAreas.A7.randSymb psig ε K) := by
    unfold Work.KMTAreas.A7.randSymb
    refine Finset.measurable_sum _ (fun n _ => ?_)
    exact Measurable.const_mul (Measurable.sub (hmeaspsig (n + 1)) (hmeaspsig n)) (ε n)
  have hsupparc : ∀ x : ℝ, Work.KMTAreas.A7.randSymb psig ε K x ≠ 0 →
      x ∈ realArc ((((P.natDegree * k₂ : ℕ)) : ℕ) : ℤ) := by
    intro x hx
    have h := lowModRandG_symbsupport P ρ C₀ a l₁ l₂ k₁ k₂ K j t ε x (by simpa only [psig] using hx)
    rw [realArc, Set.mem_Icc]
    exact abs_le.mp h
  have hsym : ∀ ξ : Circ, ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
      (periodize (Work.KMTAreas.A7.randSymb psig ε K)) ξ‖ ≤ Kf * cpsi Lam + 1 := by
    intro ξ
    by_cases hthr : (k₂ : ℝ) + (max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 2 ≤
        (2 : ℝ) ^ (((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) / (C₀ : ℝ) - 2)
    · set k : ℤ := ⌊-(max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ with hk
      have hsuppn : ∀ x : ℝ, Work.KMTAreas.A7.randSymb psig ε K x ≠ 0 → x ∈ realArc k := by
        intro x hx
        obtain ⟨n, -, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hx
        obtain ⟨-, hls, hbump⟩ := lowModRandG_support_of (h := by simpa only [psig] using hn)
        have hbump' : Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t x ≠ 0 :=
          fun h0 => hbump (by rw [varphitildeNtj_eq_gWeight_mul, h0, mul_zero])
        have hindex := (lowSmallSet_iff.mp hls).1
        have hle := narrow_of_index_G P hd ρ (max Crho 2) (by positivity) C₀ hC₀ hindex hthr
          x hbump'
        rw [realArc, Set.mem_Icc]
        exact abs_le.mp hle
      have hgood : GoodMajorArcs ρ (max Crho 2) l₂ k := by
        show (k : ℝ) ≤ -(max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        exact Int.floor_le _
      have hgood' : GoodMajorArcs ρ Crho l₂ k := by
        have h1 : Crho * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤
            (max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hg : (k : ℝ) ≤ -(max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := hgood
        show (k : ℝ) ≤ -Crho * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        linarith
      have hNA' : NonAliasing k (Work.KMTAreas.A7.diffFreqs ρ l₂) :=
        nonAliasing_mono (hNA l₂ k hgood') (tmDiffFreqs_subset ρ l₂)
      have h2 : (2 : ℝ) ^ (k + 1) < 1 :=
        Work.Analysis.IWMultiplier.two_pow_succ_lt_one_of_goodMajorArcs hgood (le_max_right _ _) hρ
      have hper : ∀ ξ : Circ, ‖periodize (Work.KMTAreas.A7.randSymb psig ε K) ξ‖ ≤ cpsi Lam :=
        fun ξ => Work.Analysis.IWMultiplier.periodize_norm_le h2 hsuppn (fun x => hpsiran x) ξ
      have hSIA : SupportedInArc k (periodize (Work.KMTAreas.A7.randSymb psig ε K)) :=
        supportedInArc_periodize' hsuppn
      have hb := norm_iwSymbolSet_le_of_nonAliasing hNA' hSIA (le_of_lt (hcpsiP Lam hLam)) hper ξ
      have hK : cpsi Lam ≤ Kf * cpsi Lam + 1 := by nlinarith [hKf1, hcpsiP Lam hLam]
      exact le_trans hb hK
    · have hk2L : k₂ ≤ lcL l₁ l₂ k₁ k₂ := by rw [lcL]; omega
      have hl2L : l₂ ≤ lcL l₁ l₂ k₁ k₂ := by rw [lcL]; omega
      have hL : lcL l₁ l₂ k₁ k₂ ≤ L0 := hL0 (lcL l₁ l₂ k₁ k₂) k₂ l₂ hk2L hl2L hthr
      have hk2 : k₂ ≤ L0 := le_trans hk2L hL
      have hl2 : l₂ ≤ L0 := le_trans hl2L hL
      have hper : ∀ ξ : Circ, ‖periodize (Work.KMTAreas.A7.randSymb psig ε K) ξ‖
          ≤ (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) * cpsi Lam := by
        intro ξ
        refine norm_periodize_le (phi := Work.KMTAreas.A7.randSymb psig ε K)
          (R := (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ)) (C := cpsi Lam)
          (2 ^ (P.natDegree * L0)) ?_ ?_ (fun x => hpsiran x) ξ
        · rw [zpow_natCast]
          have hle : P.natDegree * k₂ ≤ P.natDegree * L0 := Nat.mul_le_mul_left _ hk2
          calc (2 : ℝ) ^ (P.natDegree * k₂) ≤ (2 : ℝ) ^ (P.natDegree * L0) :=
                pow_le_pow_right₀ (by norm_num) hle
            _ = ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) := by push_cast; ring
        · intro x hx
          by_contra hne
          have hmem := hsupparc x hne
          rw [realArc, Set.mem_Icc] at hmem
          have habs : |x| ≤ (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ) := abs_le.mpr hmem
          rw [zpow_natCast] at habs hx
          linarith
      have hcard : ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) ≤
          Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) := by
        have hsub : (Work.KMTAreas.A7.diffFreqs ρ l₂).card ≤ (iwArithFreqs ρ l₂).card :=
          Finset.card_le_card (tmDiffFreqs_subset ρ l₂)
        have h1 : ((iwArithFreqs ρ l₂).card : ℝ) ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) :=
          hCc l₂
        have h2 : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L0 : ℝ)) :=
          (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mpr (by
            have : (l₂ : ℝ) ≤ (L0 : ℝ) := by exact_mod_cast hl2
            nlinarith [hρ.le])
        have h3 : (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) :=
          (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mpr h2
        calc ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
            ≤ ((iwArithFreqs ρ l₂).card : ℝ) := by exact_mod_cast hsub
          _ ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) := h1
          _ ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) := mul_le_mul_of_nonneg_left h3 hCcP.le
      have hb := norm_iwSymbolSet_le (Work.KMTAreas.A7.diffFreqs ρ l₂)
        (C := (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) * cpsi Lam) hper ξ
      have hKf : Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) *
          (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) ≤ Kf := le_max_right _ _
      calc ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
              (periodize (Work.KMTAreas.A7.randSymb psig ε K)) ξ‖
          ≤ ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) *
              ((2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) * cpsi Lam) := hb
        _ ≤ (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ)))) *
              ((2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) * cpsi Lam) := by
            apply mul_le_mul_of_nonneg_right hcard
            exact mul_nonneg (by positivity) (hcpsiP Lam hLam).le
        _ = (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) *
              (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4)) * cpsi Lam := by ring
        _ ≤ Kf * cpsi Lam := mul_le_mul_of_nonneg_right hKf (hcpsiP Lam hLam).le
        _ ≤ Kf * cpsi Lam + 1 := by linarith
  have hPhi : MemLp (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
      (periodize (Work.KMTAreas.A7.randSymb psig ε K))) ⊤ circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet _
      (Work.Analysis.IonescuWainger.memLp_periodize (φ := Work.KMTAreas.A7.randSymb psig ε K)
        (R := (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ)) (C := cpsi Lam) hmeas
        (zpow_nonneg (by norm_num) _)
        (fun x hx => by
          by_contra hne
          have hmem := hsupparc x hne
          rw [realArc, Set.mem_Icc] at hmem
          have habs : |x| ≤ (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ) := abs_le.mpr hmem
          rw [zpow_natCast] at habs hx
          linarith)
        (fun x => hpsiran x))
  have hmain := eLpNorm_iwConv_two_le_of_symbol_bound (Work.KMTAreas.A7.diffFreqs ρ l₂)
    (periodize (Work.KMTAreas.A7.randSymb psig ε K)) (Kf * cpsi Lam + 1)
    (by nlinarith [hcpsiP Lam hLam, hKf1]) hsym hPhi g hg
  change MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs ρ l₂)
      (periodize (Work.KMTAreas.A7.randSymb psig ε K)) g) 2 MeasureTheory.Measure.count
      ≤ ((Real.toNNReal (Kf * cpsi Lam + 1) : NNReal) : ENNReal)
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
  exact hmain


end

end Work.KMTPlan.A6
