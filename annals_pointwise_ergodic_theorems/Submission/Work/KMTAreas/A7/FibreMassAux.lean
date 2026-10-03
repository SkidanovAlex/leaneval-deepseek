/-
# The fibre mass bound of the §6 model approximation (the `l₂ = 0` column)

The analytic core of `Work.KMTAreas.A7.FibreMassStatement`: for `N ≥ 1`, a period `q > 0` of the
non-zero arithmetic frequency `α₁`, the `ℓ¹(ℤ²)` mass of the Fourier coefficients of the symbol

  `(θ₁,θ₂) ↦ φ_N(θ₁) φ̃_N(θ₂) weylAvg P N α₁ 0 θ₁ θ₂`

is at most `C q² (1 + S²/N) 2^{k₁+dk₂} / N` (`S = 2^{k₁}+2^{dk₂}`, `d = P.natDegree`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedRMass
import Submission.Work.KMTAreas.A7.fibre_mZ_zero
import Submission.Work.KMTAreas.A7.dp_weylAvg_eq_sum_momPhaseDeriv
import Submission.Work.KMTAreas.A7.integral_iteratedDeriv_bumps_le
import Submission.Work.KMTAreas.A7.contDiff_hasCompactSupport_fibreSymbol

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## §1  The constants -/

/-- The `L¹`-constant of the bump `φ_N`. -/
noncomputable def fibBumpCφ (P : Polynomial ℤ) : ℝ :=
  Classical.choose (integral_iteratedDeriv_bumps_le P)

/-- The `L¹`-constant of the bump `φ̃_N`. -/
noncomputable def fibBumpCψ (P : Polynomial ℤ) : ℝ :=
  Classical.choose (Classical.choose_spec (integral_iteratedDeriv_bumps_le P))

/-- The constant of the sharp symbol-difference estimate. -/
noncomputable def fibM0C (P : Polynomial ℤ) : ℝ :=
  Classical.choose (Work.A7.ModelApproxCore_M0_deriv_bound P)

theorem fibBumpCφ_pos (P : Polynomial ℤ) : 0 < fibBumpCφ P :=
  (Classical.choose_spec (Classical.choose_spec (integral_iteratedDeriv_bumps_le P))).1

theorem fibBumpCψ_pos (P : Polynomial ℤ) : 0 < fibBumpCψ P :=
  (Classical.choose_spec (Classical.choose_spec (integral_iteratedDeriv_bumps_le P))).2.1

theorem fibM0C_pos (P : Polynomial ℤ) : 0 < fibM0C P :=
  (Classical.choose_spec (Work.A7.ModelApproxCore_M0_deriv_bound P)).1

/-- The bump `L¹`-bound for `φ_N`, in the `∫`-form. -/
theorem fibBumpCφ_bound (P : Polynomial ℤ) (N k m : ℕ) (hm : m ≤ 2) :
    (∫ ξ : ℝ, ‖iteratedDeriv m (varphiN N k) ξ‖)
      ≤ fibBumpCφ P * (Work.KMTPlan.A6.lothN N / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1) :=
  (Classical.choose_spec (Classical.choose_spec
    (integral_iteratedDeriv_bumps_le P))).2.2.1 N k m hm

/-- The bump `L¹`-bound for `φ̃_N`, in the `∫`-form. -/
theorem fibBumpCψ_bound (P : Polynomial ℤ) (N k m : ℕ) (hm : m ≤ 2) :
    (∫ ξ : ℝ, ‖iteratedDeriv m (varphitildeN P.natDegree N k) ξ‖)
      ≤ fibBumpCψ P * Work.KMTPlan.A6.lopsN P.natDegree N k ^ ((m : ℝ) - 1) :=
  (Classical.choose_spec (Classical.choose_spec
    (integral_iteratedDeriv_bumps_le P))).2.2.2 N k m hm

/-- The sharp symbol-difference derivative estimate of §6. -/
theorem fibM0C_bound (P : Polynomial ℤ) (N q j₁ j₂ k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ)
    (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) (hN : 1 ≤ N) (hq : 0 < q)
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0)
    (hξ₁ : |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ))
    (hξ₂ : |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree) :
    ‖Work.KMTAreas.A7.M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖
      ≤ fibM0C P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ ((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ) - 1) :=
  (Classical.choose_spec (Work.A7.ModelApproxCore_M0_deriv_bound P)).2 N q j₁ j₂ k₁ k₂
    α₁ α₂ ξ₁ ξ₂ hj₁ hj₂ hN hq h₁ h₂ hξ₁ hξ₂

/-- The final constant of the fibre mass bound.  The factor `6400 · 2^{d+1}` absorbs the
frequency arithmetic of the two-radii derivative bound (see `FibreMassHbdDefs.fibHbdC`): if `B =
λ₂N^d ≥ 1` the loss is `(N/2^{Log N})^{d+1} ≤ 2^{d+1}`, and if `B < 1` (which can only happen at
`N = 1`) the loss is the factor `2` from `N ≤ 2·2^{Log N}`. -/
noncomputable def fibConst (P : Polynomial ℤ) : ℝ :=
  max 1 (6400 * (2 : ℝ) ^ (P.natDegree + 1) * fibM0C P * fibBumpCφ P * fibBumpCψ P)

theorem fibConst_pos (P : Polynomial ℤ) : 0 < fibConst P := lt_of_lt_of_le one_pos (le_max_left _ _)

/-! ## §2  Support of the bumps and vanishing of their derivatives -/

/-- `2^{k-Log N} ≤ 2^{k+1}/N`. -/
theorem pow_two_logN_le_box (N k : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ (2 : ℝ) ^ (k + 1) / (N : ℝ) := by
  have h := Work.KMTPlan.A6.lole_pow_div_of_abs_le (N := N) (k := k) hN
    (ξ := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
    (le_of_eq (abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)))
  rwa [abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)] at h

/-- `2^{d(k-Log N)} ≤ 2^{d(k+1)}/N^d`. -/
theorem pow_two_logN_le_box_pow (d N k : ℕ) (hN : 1 ≤ N) :
    (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      ≤ (2 : ℝ) ^ (d * (k + 1)) / (N : ℝ) ^ d := by
  have h := Work.KMTPlan.A6.lole_pow_div_pow_of_abs_le (N := N) (k := k) (d := d) hN
    (ξ := (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
    (le_of_eq (abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)))
  rwa [abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)] at h

/-- At degree `0` and bottom scale, `φ̃_N` is the plain cutoff `η`. -/
theorem varphitildeN_zero_zero (N : ℕ) : varphitildeN 0 N 0 = Work.KMTContract.kmtEta := by
  funext ξ
  rw [varphitildeN, if_pos rfl]
  congr 1
  push_cast
  rw [zero_mul, Real.rpow_zero, one_mul]

/-- At degree `0` and positive scale, `φ̃_N` vanishes identically. -/
theorem varphitildeN_zero_pos (N k : ℕ) (hk : k ≠ 0) : varphitildeN 0 N k = 0 := by
  funext ξ
  rw [varphitildeN, if_neg hk]
  push_cast
  simp only [zero_mul, Real.rpow_zero, one_mul, sub_self]
  rfl

theorem varphiN_abs_le_box (N k : ℕ) (hN : 1 ≤ N) {ξ : ℝ} (h : varphiN N k ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ (k + 1) / (N : ℝ) :=
  Work.KMTPlan.A6.lole_pow_div_of_abs_le hN (varphiN_support N k ξ h)

theorem varphitildeN_abs_le_box (d N k : ℕ) (hN : 1 ≤ N) {ξ : ℝ}
    (h : varphitildeN d N k ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ (d * (k + 1)) / (N : ℝ) ^ d := by
  rcases eq_or_ne d 0 with hd | hd
  · subst hd
    simp only [Nat.cast_zero, zero_mul, pow_zero, Nat.pow_zero, div_one] at h ⊢
    rcases eq_or_ne k 0 with hk | hk
    · subst hk
      rw [varphitildeN_zero_zero] at h
      have h1 : ¬ (1 ≤ |ξ|) := fun hc => h (Work.KMTContract.kmtEta_zero hc)
      linarith [not_le.mp h1]
    · rw [varphitildeN_zero_pos N k hk] at h
      exact absurd rfl h
  · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    exact (Work.KMTPlan.A6.lovarphitildeN_ne_zero_abs_le d N k hd1 h).trans
      (pow_two_logN_le_box_pow d N k hN)

theorem iteratedDeriv_varphiN_eq_zero_of_box (N k a : ℕ) (hN : 1 ≤ N) {ξ : ℝ}
    (h : (2 : ℝ) ^ (k + 1) / (N : ℝ) < |ξ|) :
    iteratedDeriv a (varphiN N k) ξ = 0 := by
  have hset : {y : ℝ | (2 : ℝ) ^ (k + 1) / (N : ℝ) < |y|} ∈ 𝓝 ξ :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds h
  refine iteratedDeriv_eq_zero_of_eventuallyEq_zero (varphiN N k) ?_ a
  filter_upwards [hset] with y hy
  exact Work.KMTPlan.A6.lovarphiN_eq_zero_of_lt
    (lt_of_le_of_lt (pow_two_logN_le_box N k hN) hy)

theorem iteratedDeriv_varphitildeN_eq_zero_of_box (d N k b : ℕ) (hN : 1 ≤ N) {ξ : ℝ}
    (h : (2 : ℝ) ^ (d * (k + 1)) / (N : ℝ) ^ d < |ξ|) :
    iteratedDeriv b (varphitildeN d N k) ξ = 0 := by
  rcases eq_or_ne d 0 with hd | hd
  · subst hd
    simp only [Nat.cast_zero, zero_mul, pow_zero, Nat.pow_zero, div_one] at h
    rcases eq_or_ne k 0 with hk | hk
    · subst hk
      have hset : {y : ℝ | (1 : ℝ) < |y|} ∈ 𝓝 ξ :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds h
      refine iteratedDeriv_eq_zero_of_eventuallyEq_zero (varphitildeN 0 N 0) ?_ b
      filter_upwards [hset] with y hy
      rw [varphitildeN_zero_zero]
      exact Work.KMTContract.kmtEta_zero (le_of_lt hy)
    · rw [varphitildeN_zero_pos N k hk]
      simp
  · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    have hset : {y : ℝ | (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) < |y|}
        ∈ 𝓝 ξ := (isOpen_lt continuous_const continuous_abs).mem_nhds
      (lt_of_le_of_lt (pow_two_logN_le_box_pow d N k hN) h)
    refine iteratedDeriv_eq_zero_of_eventuallyEq_zero (varphitildeN d N k) ?_ b
    filter_upwards [hset] with y hy
    exact Work.KMTPlan.A6.lovarphitildeN_eq_zero_of_lt hd1 hy

/-! ## §3  The derivatives of the Weyl average

The `ξ`-derivatives of `weylAvg` are the finite sums of `momPhaseDeriv`; since `m_Z(α₁,α₂) = 0`
on the fibre, they are also the derivatives of the symbol difference `M₀`, whose sharp bound is
`fibM0C_bound`. -/

theorem dp_weylAvg_le (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (hmZ : mZ P q α₁ α₂ = 0) (hN : 1 ≤ N) (hq : 0 < q) (hs₁ : q • α₁ = 0) (hs₂ : q • α₂ = 0)
    {j₁ j₂ : ℕ} (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) {x y : ℝ}
    (hx : |x| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ))
    (hy : |y| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree) :
    ‖Work.KMTPlan.A6.dp j₁ j₂ (fun a b => weylAvg P N α₁ α₂ a b) x y‖
      ≤ fibM0C P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ ((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ) - 1) := by
  have h := dp_weylAvg_eq_sum_momPhaseDeriv P N α₁ α₂ x y j₁ j₂
  rw [h]
  have hid : Work.KMTAreas.A7.M0deriv P N q α₁ α₂ x y j₁ j₂
      = ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          momPhaseDeriv P N α₁ α₂ x y (n : ℤ) j₁ j₂ := by
    rw [Work.KMTAreas.A7.M0deriv, hmZ, zero_mul, sub_zero]
  rw [← hid]
  exact fibM0C_bound P N q j₁ j₂ k₁ k₂ α₁ α₂ x y hj₁ hj₂ hN hq hs₁ hs₂ hx hy

/-! ## §4  The Leibniz expansion of the symbol -/

/-- The `∂₁^{i₁}∂₂^{i₂}`-derivative of `φ_N ⊗ φ̃_N · weylAvg`, expanded. -/
theorem dp_symbol_eq_leibniz (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (i₁ i₂ : ℕ) (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ 2) (x y : ℝ) :
    Work.KMTPlan.A6.dp i₁ i₂ (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * weylAvg P N α₁ α₂ a b) x y
      = ∑ b' ∈ Finset.range (i₂ + 1), ∑ a' ∈ Finset.range (i₁ + 1),
          ((i₂.choose b' : ℂ) * (i₁.choose a' : ℂ))
            * (iteratedDeriv a' (varphiN N k₁) x)
            * (Work.KMTPlan.A6.dp (i₁ - a') b' (fun a b => weylAvg P N α₁ α₂ a b) x y)
            * (iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y) := by
  have hφ : ContDiff ℝ 2 (varphiN N k₁) :=
    (Work.KMTPlan.A6.contDiff4_varphiN N k₁).of_le (by norm_num)
  have hψ : ContDiff ℝ 2 (varphitildeN P.natDegree N k₂) :=
    (Work.KMTPlan.A6.contDiff4_varphitildeN P.natDegree N k₂).of_le (by norm_num)
  have hw : ContDiff ℝ 4 (fun p : ℝ × ℝ => weylAvg P N α₁ α₂ p.1 p.2) :=
    Work.KMTPlan.A6.contDiff4_weylAvg P N α₁ α₂
  have hσ : (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * weylAvg P N α₁ α₂ a b)
      = (fun a b => ∑ k ∈ ({()} : Finset Unit),
          (fun (_ : Unit) a b => weylAvg P N α₁ α₂ a b) k a b
            * (fun (_ : Unit) a => varphiN N k₁ a) k a
            * (fun (_ : Unit) b => varphitildeN P.natDegree N k₂ b) k b) := by
    funext a b
    simp only [Finset.sum_singleton]
    ring
  rw [hσ, Work.KMTPlan.A6.lodp_finset_sum_mul_three ({()} : Finset Unit)
    (fun (_ : Unit) a b => weylAvg P N α₁ α₂ a b) (fun (_ : Unit) a => varphiN N k₁ a)
    (fun (_ : Unit) b => varphitildeN P.natDegree N k₂ b) i₁ i₂ hi₁ hi₂ y x
    (fun _ _ a => (Work.KMTPlan.A6.cdp_fiber₂ (fun a b => weylAvg P N α₁ α₂ a b) 4 hw a).of_le (by norm_num))
    (fun _ _ i₂' hi₂' => (Work.KMTPlan.A6.cdp_fiber₁
        (Work.KMTPlan.A6.dp2 i₂' (fun a b => weylAvg P N α₁ α₂ a b)) 2
        (Work.KMTPlan.A6.cdp_contDiff_dp2_iter (fun a b => weylAvg P N α₁ α₂ a b) 2 i₂'
          (hw.of_le (by exact_mod_cast (by omega : 2 + i₂' ≤ 4)))) y).of_le (by norm_num))
    (fun _ _ => hφ) (fun _ _ => hψ)]
  simp only [Finset.sum_singleton]
  refine Finset.sum_congr rfl (fun b' _ => Finset.sum_congr rfl (fun a' _ => ?_))
  first
    | rfl
    | simp only [Work.KMTPlan.A6.dp, Work.KMTPlan.A6.dp1, Work.KMTPlan.A6.dp2]

/-! ## §5  The pointwise weighted bound (support argument) -/

theorem pointwise_weighted_bound (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (hmZ : mZ P q α₁ α₂ = 0) (hN : 1 ≤ N) (hq : 0 < q) (hs₁ : q • α₁ = 0) (hs₂ : q • α₂ = 0)
    {j₁ j₂ a' b' : ℕ} (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) (x y : ℝ) :
    ‖iteratedDeriv a' (varphiN N k₁) x‖
        * ‖Work.KMTPlan.A6.dp j₁ j₂ (fun a b => weylAvg P N α₁ α₂ a b) x y‖
        * ‖iteratedDeriv b' (varphitildeN P.natDegree N k₂) y‖
      ≤ (fibM0C P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ ((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ) - 1))
        * (‖iteratedDeriv a' (varphiN N k₁) x‖
            * ‖iteratedDeriv b' (varphitildeN P.natDegree N k₂) y‖) := by
  by_cases hx : |x| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ)
  · by_cases hy : |y| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree
    · have hle := dp_weylAvg_le P N q k₁ k₂ α₁ α₂ hmZ hN hq hs₁ hs₂ hj₁ hj₂ hx hy
      refine (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle (norm_nonneg _)) (norm_nonneg _)).trans (le_of_eq ?_)
      ring
    · have h0 : iteratedDeriv b' (varphitildeN P.natDegree N k₂) y = 0 :=
        iteratedDeriv_varphitildeN_eq_zero_of_box _ _ _ _ hN (lt_of_not_ge hy)
      simp [h0]
  · have h0 : iteratedDeriv a' (varphiN N k₁) x = 0 :=
      iteratedDeriv_varphiN_eq_zero_of_box _ _ _ hN (lt_of_not_ge hx)
    simp [h0]

/-! ## §6  The `L¹`-bound for the derivatives of the symbol -/

/-- All derivatives of `φ̃_N` up to order `2` have compact support. -/
theorem hcs_iteratedDeriv_varphitildeN (d N k m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m (varphitildeN d N k)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_varphitildeN d N k
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_varphitildeN d N k).deriv
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_varphitildeN d N k).deriv).deriv

/-- The `(a',b'')`-th term of the Leibniz expansion of the symbol is integrable. -/
theorem integrable_ibp_term (P : Polynomial ℤ) (N k₁ k₂ a' b'' : ℕ) (ha : a' ≤ 2) (hb : b'' ≤ 2) :
    Integrable (fun z : ℝ × ℝ => ‖iteratedDeriv a' (varphiN N k₁) z.1‖
      * ‖iteratedDeriv b'' (varphitildeN P.natDegree N k₂) z.2‖) := by
  have hcd1 : ContDiff ℝ 4 (varphiN N k₁) := Work.KMTPlan.A6.contDiff4_varphiN N k₁
  have hcd2 : ContDiff ℝ 4 (varphitildeN P.natDegree N k₂) :=
    Work.KMTPlan.A6.contDiff4_varphitildeN P.natDegree N k₂
  have hcont : Continuous (fun z : ℝ × ℝ => ‖iteratedDeriv a' (varphiN N k₁) z.1‖
      * ‖iteratedDeriv b'' (varphitildeN P.natDegree N k₂) z.2‖) :=
    (((hcd1.continuous_iteratedDeriv a' (by exact_mod_cast (by omega : a' ≤ 4))).comp
        continuous_fst).norm.mul
      ((hcd2.continuous_iteratedDeriv b'' (by exact_mod_cast (by omega : b'' ≤ 4))).comp
        continuous_snd).norm)
  refine hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      (K := tsupport (fun x : ℝ => iteratedDeriv a' (varphiN N k₁) x)
        ×ˢ tsupport (fun y : ℝ => iteratedDeriv b'' (varphitildeN P.natDegree N k₂) y))
      ((hcs_iteratedDeriv_varphiN N k₁ a' ha).isCompact.prod
        (hcs_iteratedDeriv_varphitildeN P.natDegree N k₂ b'' hb).isCompact) ?_)
  intro z hz
  rw [Function.mem_support] at hz
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hz
  exact ⟨subset_tsupport _ (norm_ne_zero_iff.mp h1), subset_tsupport _ (norm_ne_zero_iff.mp h2)⟩

end

end Work.KMTAreas.A7
