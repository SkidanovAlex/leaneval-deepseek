import Mathlib
import Submission.Work.KMTAreas.A7.LoErrAux
import Submission.Work.KMTPlan.A6.M0_iteratedDeriv
import Submission.Work.KMTAreas.A7.M0DerivBound
import Submission.Work.A7.ModelApproxCore_M0_deriv_bound
import Submission.Work.KMTAreas.A7.fourierDecay_varphitildeN
import Submission.Work.KMTAreas.A7.LoBumpBounds

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

noncomputable section

/-! ## A separable finite sum under the `lintegral`

This is the integration step that converts the pointwise bound `lodp_symD_pointwise_le` into an
estimate of `∫⁻∫⁻ ‖dp j₁ j₂ symD‖`: a finite sum `∑_j c_j f_j(x) g_j(y)` with nonnegative `c_j`
integrates to at most `∑_j c_j (∫⁻ f_j) (∫⁻ g_j)`. -/

theorem lolintegral_ofReal_sum_separable {ι : Type*} (J : Finset ι) (c : ι → ℝ)
    (f g : ι → ℝ → ℝ)
    (hc : ∀ j ∈ J, 0 ≤ c j) (hf0 : ∀ j ∈ J, ∀ x, 0 ≤ f j x) (hg0 : ∀ j ∈ J, ∀ y, 0 ≤ g j y)
    (hfm : ∀ j ∈ J, Measurable (fun x : ℝ => ENNReal.ofReal (f j x)))
    (hgm : ∀ j ∈ J, Measurable (fun y : ℝ => ENNReal.ofReal (g j y)))
    {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (∫⁻ x in s, ∫⁻ y in t, ENNReal.ofReal (∑ j ∈ J, c j * f j x * g j y))
      ≤ ∑ j ∈ J, ENNReal.ofReal (c j) * (∫⁻ x, ENNReal.ofReal (f j x))
          * (∫⁻ y, ENNReal.ofReal (g j y)) := by
  have hinner : ∀ x : ℝ, (∫⁻ y in t, ENNReal.ofReal (∑ j ∈ J, c j * f j x * g j y))
      = ∑ j ∈ J, ENNReal.ofReal (c j * f j x) * (∫⁻ y in t, ENNReal.ofReal (g j y)) := by
    intro x
    change (∫⁻ y, ENNReal.ofReal (∑ j ∈ J, c j * f j x * g j y) ∂(volume.restrict t)) = _
    rw [show (fun y : ℝ => ENNReal.ofReal (∑ j ∈ J, c j * f j x * g j y))
        = fun y : ℝ => ∑ j ∈ J, ENNReal.ofReal (c j * f j x * g j y) from by
      funext y
      exact ENNReal.ofReal_sum_of_nonneg (fun j hj => by
        have := hc j hj; have := hf0 j hj x; have := hg0 j hj y; positivity)]
    have hmeas : ∀ j ∈ J, AEMeasurable
        (fun y : ℝ => ENNReal.ofReal (c j * f j x * g j y)) (volume.restrict t) := by
      intro j hj
      have h1 : AEMeasurable (fun y : ℝ => ENNReal.ofReal (g j y)) (volume.restrict t) :=
        (hgm j hj).aemeasurable.restrict
      have h2 := h1.const_mul (ENNReal.ofReal (c j * f j x))
      rwa [show (fun y : ℝ => ENNReal.ofReal (c j * f j x) * ENNReal.ofReal (g j y))
          = fun y : ℝ => ENNReal.ofReal (c j * f j x * g j y) from by
        funext y
        exact (ENNReal.ofReal_mul (by have := hc j hj; have := hf0 j hj x; positivity)).symm] at h2
    rw [MeasureTheory.lintegral_finsetSum' J hmeas]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [show (fun y : ℝ => ENNReal.ofReal (c j * f j x * g j y))
        = fun y : ℝ => ENNReal.ofReal (c j * f j x) * ENNReal.ofReal (g j y) from by
      funext y
      exact ENNReal.ofReal_mul (by have := hc j hj; have := hf0 j hj x; positivity)]
    exact MeasureTheory.lintegral_const_mul'' _ ((hgm j hj).aemeasurable.restrict)
  have houter : ∀ x : ℝ,
      (∑ j ∈ J, ENNReal.ofReal (c j * f j x) * (∫⁻ y in t, ENNReal.ofReal (g j y)))
      ≤ ∑ j ∈ J, ENNReal.ofReal (c j * f j x) * (∫⁻ y, ENNReal.ofReal (g j y)) := by
    intro x
    refine Finset.sum_le_sum (fun j hj => ?_)
    exact mul_le_mul_right (by
      rw [← MeasureTheory.lintegral_indicator ht]
      exact lintegral_mono (fun y => Set.indicator_le_self t _ y)) _
  have hfm' : ∀ j ∈ J, AEMeasurable (fun x : ℝ => ENNReal.ofReal (c j * f j x)
      * (∫⁻ y, ENNReal.ofReal (g j y))) volume := by
    intro j hj
    have hmj : Measurable (fun x : ℝ => ENNReal.ofReal (c j * f j x)) := by
      rw [show (fun x : ℝ => ENNReal.ofReal (c j * f j x))
          = fun x : ℝ => ENNReal.ofReal (c j) * ENNReal.ofReal (f j x) from by
        funext x; exact ENNReal.ofReal_mul (hc j hj)]
      exact (hfm j hj).const_mul _
    exact (hmj.mul_const _).aemeasurable
  calc (∫⁻ x in s, ∫⁻ y in t, ENNReal.ofReal (∑ j ∈ J, c j * f j x * g j y))
      = ∫⁻ x in s, ∑ j ∈ J, ENNReal.ofReal (c j * f j x) * (∫⁻ y in t, ENNReal.ofReal (g j y)) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall (fun x => hinner x))
    _ ≤ ∫⁻ x in s, ∑ j ∈ J, ENNReal.ofReal (c j * f j x) * (∫⁻ y, ENNReal.ofReal (g j y)) :=
        lintegral_mono houter
    _ ≤ ∫⁻ x, ∑ j ∈ J, ENNReal.ofReal (c j * f j x) * (∫⁻ y, ENNReal.ofReal (g j y)) := by
        rw [← MeasureTheory.lintegral_indicator hs]
        exact lintegral_mono (fun x => Set.indicator_le_self s _ x)
    _ = ∑ j ∈ J, ∫⁻ x, ENNReal.ofReal (c j * f j x) * (∫⁻ y, ENNReal.ofReal (g j y)) := by
        rw [MeasureTheory.lintegral_finsetSum' J hfm']
    _ ≤ ∑ j ∈ J, ENNReal.ofReal (c j) * (∫⁻ x, ENNReal.ofReal (f j x))
          * (∫⁻ y, ENNReal.ofReal (g j y)) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hmj : Measurable (fun x : ℝ => ENNReal.ofReal (c j * f j x)) := by
          rw [show (fun x : ℝ => ENNReal.ofReal (c j * f j x))
              = fun x : ℝ => ENNReal.ofReal (c j) * ENNReal.ofReal (f j x) from by
            funext x; exact ENNReal.ofReal_mul (hc j hj)]
          exact (hfm j hj).const_mul _
        calc ∫⁻ x, ENNReal.ofReal (c j * f j x) * (∫⁻ y, ENNReal.ofReal (g j y))
            = (∫⁻ x, ENNReal.ofReal (c j * f j x)) * (∫⁻ y, ENNReal.ofReal (g j y)) :=
              MeasureTheory.lintegral_mul_const'' _ hmj.aemeasurable
          _ = (ENNReal.ofReal (c j) * (∫⁻ x, ENNReal.ofReal (f j x)))
                * (∫⁻ y, ENNReal.ofReal (g j y)) := by
              rw [show (fun x : ℝ => ENNReal.ofReal (c j * f j x))
                  = fun x : ℝ => ENNReal.ofReal (c j) * ENNReal.ofReal (f j x) from by
                funext x; exact ENNReal.ofReal_mul (hc j hj)]
              rw [MeasureTheory.lintegral_const_mul'' _ (hfm j hj).aemeasurable]
          _ ≤ ENNReal.ofReal (c j) * (∫⁻ x, ENNReal.ofReal (f j x))
                * (∫⁻ y, ENNReal.ofReal (g j y)) := le_of_eq rfl

/-! ## The main statement

The statement is exactly the one requested by the requester.  The supporting development above
provides:

* `losymD_eq_window` / `losymD_eq_window_finset` — `symD` is a *finite* sum on any bounded region
  (the window `[-5,5]` of representatives of the aliasing fibre);
* `lodp_finset_sum_mul_three` — the two-variable Leibniz rule together with the finite-sum rule;
* `M0_iteratedDeriv` (imported) — the identification of the `(ξ₁,ξ₂)`-iterated derivatives of `M₀`
  with the hand-differentiated object `M0deriv`;
* `lodp_symD_pointwise_le` — the pointwise bound on `‖dp j₁ j₂ symD x y‖` obtained by combining the
  Leibniz identity with the sharp single-scale `M₀` estimate `ModelApproxCore_M0_deriv_bound` and
  the support of the bumps;
* `varphiN_lintegral_deriv_le`, `varphitildeN_lintegral_deriv_le` (separate modules) — the `L¹`
  masses of the derivatives of the bumps;
* `lintegral_kmtEta_deriv_le`, `lole_pow_div_of_abs_le`, `lole_pow_div_pow_of_abs_le`,
  `locontDiff_symDF_snd`, `locontDiff_iteratedDeriv_symDF`, ...

What remains to be assembled is (i) the `lintegral` bound obtained by integrating
`lodp_symD_pointwise_le` against the two bump-mass estimates (a finite separable sum, see
`lolintegral_ofReal_sum_separable` in `_a6mine`), and (ii) the final arithmetic of the constants
`K, D`. -/




/-! ## The finite window of representatives of the aliasing fibre -/

/-- The window `[-5,5]` of representatives of the aliasing fibre. -/
def lomWindow : Finset ℤ := Finset.Icc (-5) 5

theorem lomem_mWindow (m : ℤ) : m ∈ lomWindow ↔ -5 ≤ m ∧ m ≤ 5 := by
  simp [lomWindow]

theorem losix_le_or_le_neg_six_of_notMem_mWindow {m : ℤ} (h : m ∉ lomWindow) :
    (6 : ℤ) ≤ m ∨ m ≤ -6 := by
  rw [lomem_mWindow] at h
  push Not at h
  omega

/-! ## The support radius of the bumps -/

theorem lologN_nonneg (N : ℕ) : 0 ≤ Work.Analysis.EndVar.logN N := by
  unfold Work.Analysis.EndVar.logN
  exact Int.natCast_nonneg _

theorem lotoNat_logN_le (N : ℕ) :
    (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℤ) ≤ Work.Analysis.EndVar.logN N := by
  rw [Int.toNat_of_nonneg (lologN_nonneg N)]

/-- If `k + 3 ≤ Log N` then the support radius `2^{k - Log N}` of the bump is at most `1/8`. -/
theorem lorpow_two_logN_le_eighth (N k : ℕ)
    (h : k + 3 ≤ (Work.Analysis.EndVar.logN N).toNat) :
    (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ 1 / 8 := by
  have h1 : ((k : ℤ) + 3) ≤ Work.Analysis.EndVar.logN N := by
    have h2 : ((k + 3 : ℕ) : ℤ) ≤ ((Work.Analysis.EndVar.logN N).toNat : ℤ) := by
      exact_mod_cast h
    push_cast at h2
    linarith [h2, lotoNat_logN_le N]
  have h2 : ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ -3 := by
    have h1' : (k : ℝ) + 3 ≤ (Work.Analysis.EndVar.logN N : ℝ) := by exact_mod_cast h1
    linarith
  have h3 : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ (2 : ℝ) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  have h4 : ((2 : ℝ) ^ (-3 : ℝ)) = 1 / 8 := by
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [h4] at h3
  exact h3

theorem loabs_six_le_abs_of_notMem {m : ℤ} (hm : m ∉ lomWindow) :
    (6 : ℝ) ≤ |((m : ℤ) : ℝ)| := by
  rcases losix_le_or_le_neg_six_of_notMem_mWindow hm with hm' | hm'
  · rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ m))]
    exact_mod_cast hm'
  · rw [abs_of_nonpos (by exact_mod_cast (by omega : m ≤ 0))]
    exact_mod_cast (by omega : (6 : ℤ) ≤ -m)

/-- For `m` outside the window and `|u| ≤ 5`, the point `u + m` is at distance at least `1` from
the origin. -/
theorem loone_le_abs_add_of_notMem {u : ℝ} (hu : |u| ≤ 5) {m : ℤ} (hm : m ∉ lomWindow) :
    (1 : ℝ) ≤ |u + (m : ℤ)| := by
  have hm6 : (6 : ℝ) ≤ |((m : ℤ) : ℝ)| := loabs_six_le_abs_of_notMem hm
  have htri : |(-((m : ℤ) : ℝ))| - |u| ≤ |(-((m : ℤ) : ℝ)) - u| := abs_sub_abs_le_abs_sub _ _
  rw [abs_neg] at htri
  have harg : -((m : ℤ) : ℝ) - u = -(u + (m : ℤ)) := by ring
  rw [harg, abs_neg] at htri
  linarith

theorem lovarphiN_eq_zero_of_lt {N k : ℕ} {ξ : ℝ}
    (h : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |ξ|) :
    Work.KMTAreas.A7.varphiN N k ξ = 0 := by
  by_contra hne
  exact absurd (Work.KMTAreas.A7.varphiN_support N k ξ hne) (not_le.mpr h)

/-- **`φ_N` vanishes away from the window `[-5,5]`.** -/
theorem lovarphiN_eq_zero_of_window {N k : ℕ} (h : k + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {c x : ℝ} (hc : |c| ≤ 1) (hx : |x| ≤ 4) {m : ℤ} (hm : m ∉ lomWindow) :
    Work.KMTAreas.A7.varphiN N k (x - c + m) = 0 := by
  have hrad : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ 1 / 8 :=
    lorpow_two_logN_le_eighth N k h
  have hxc : |x - c| ≤ 5 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [le_abs_self x, neg_le_abs x, le_abs_self c, neg_le_abs c]
  exact lovarphiN_eq_zero_of_lt (lt_of_le_of_lt hrad (by linarith [loone_le_abs_add_of_notMem hxc hm]))

/-- **`φ̃_N` vanishes outside its sharp support radius** `2^{d(k - Log N)}`. -/
theorem lovarphitildeN_ne_zero_abs_le (d N k : ℕ) (hd : 1 ≤ d) {ξ : ℝ}
    (h : Work.KMTAreas.A7.varphitildeN d N k ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have key : ∀ (a : ℝ), Work.KMTContract.kmtEta ((2 : ℝ) ^ a * ξ) ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-a) := by
    intro a ha
    have h2 : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
    have hlt : (2 : ℝ) ^ a * |ξ| < 1 := by
      have h1 : ¬ (1 ≤ |(2 : ℝ) ^ a * ξ|) := fun hc => ha (Work.KMTContract.kmtEta_zero hc)
      have h2' : |(2 : ℝ) ^ a * ξ| < 1 := lt_of_not_ge h1
      rwa [abs_mul, abs_of_pos h2] at h2'
    have hb := Work.KMTAreas.A7.abs_le_of_rpow_mul_lt_one (L := a) (k := 0) (by simpa using hlt)
    simpa using hb
  by_cases hk : k = 0
  · subst hk
    rw [Work.KMTAreas.A7.varphitildeN, if_pos rfl] at h
    have hb := key ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) h
    have he : -((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))
        = (d : ℝ) * ((0 : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by ring
    rw [he] at hb
    simpa using hb
  · rw [Work.KMTAreas.A7.varphitildeN, if_neg hk] at h
    have hbor : Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ) ≠ 0 ∨
        Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (by rw [hc.1, hc.2, sub_zero])
    rcases hbor with hc | hc
    · have hb := key ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) hc
      have he : -((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))
          = (d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by ring
      rw [he] at hb
      exact hb
    · have hb := key ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) hc
      have he : -((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))
          = (d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) - (d : ℝ) := by ring
      rw [he] at hb
      refine hb.trans ?_
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **`φ̃_N` vanishes away from the window `[-5,5]`.** -/
theorem lovarphitildeN_eq_zero_of_window (P : ℤ[X]) (hd : 1 ≤ P.natDegree) {N k : ℕ}
    (h : k + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {c y : ℝ} (hc : |c| ≤ 1) (hy : |y| ≤ 4) {m : ℤ} (hm : m ∉ lomWindow) :
    Work.KMTAreas.A7.varphitildeN P.natDegree N k (y - c + m) = 0 := by
  have hyc : |y - c| ≤ 5 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [le_abs_self y, neg_le_abs y, le_abs_self c, neg_le_abs c]
  have harg : (1 : ℝ) ≤ |y - c + (m : ℤ)| := loone_le_abs_add_of_notMem hyc hm
  by_contra hne
  have hb := lovarphitildeN_ne_zero_abs_le P.natDegree N k hd hne
  have hle : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      ≤ 1 / 8 := by
    have hkd : (k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) ≤ 0 := by
      have h1 : ((k : ℤ) + 3) ≤ Work.Analysis.EndVar.logN N := by
        have h2 : ((k + 3 : ℕ) : ℤ) ≤ ((Work.Analysis.EndVar.logN N).toNat : ℤ) := by
          exact_mod_cast h
        push_cast at h2
        linarith [h2, lotoNat_logN_le N]
      have h1' : (k : ℝ) + 3 ≤ (Work.Analysis.EndVar.logN N : ℝ) := by exact_mod_cast h1
      linarith
    have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    have hexp : (P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
        ≤ (k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) := by
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ (P.natDegree : ℝ) - 1) hkd
      linarith
    calc (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
        ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ ≤ 1 / 8 := lorpow_two_logN_le_eighth N k h
  linarith

/-! ## The arithmetic frequencies and the period `perQ` -/

theorem loperQ_smul_left (γ₁ γ₂ : Analysis.IonescuWainger.Circle) : perQ γ₁ γ₂ • γ₁ = 0 :=
  addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_lcm_left _ _)

theorem loperQ_smul_right (γ₁ γ₂ : Analysis.IonescuWainger.Circle) : perQ γ₁ γ₂ • γ₂ = 0 :=
  addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_lcm_right _ _)

theorem loperQ_pos {γ₁ γ₂ : Analysis.IonescuWainger.Circle} (h₁ : IsOfFinAddOrder γ₁) (h₂ : IsOfFinAddOrder γ₂) :
    0 < perQ γ₁ γ₂ := by
  rw [perQ]
  exact Nat.lcm_pos (addOrderOf_pos_iff.mpr h₁) (addOrderOf_pos_iff.mpr h₂)

theorem logamR_abs_le_one (γ : Analysis.IonescuWainger.Circle) : |gamR γ| ≤ 1 := by
  have h : (0 : ℝ) ≤ (AddCircle.equivIco (1 : ℝ) 0 γ).val
      ∧ (AddCircle.equivIco (1 : ℝ) 0 γ).val < 1 := by
    have h0 := (AddCircle.equivIco (1 : ℝ) 0 γ).2
    rw [Set.mem_Ico] at h0
    simpa using h0
  have hg : gamR γ = (AddCircle.equivIco (1 : ℝ) 0 γ).val := rfl
  rw [hg, abs_of_nonneg h.1]
  exact h.2.le

/-! ## The finite-sum form of `symD`

`symD` is by definition a double `tsum` over the representatives `m₁,m₂ ∈ ℤ` of the aliasing
fibres.  Because the bumps `φ_N`, `φ̃_N` are supported in `|ξ| ≤ 1/8`, all but the terms with
`m₁,m₂` in the window `[-5,5]` vanish on any bounded region; this section states that reduction.
-/

/-- The term of the aliasing sum of `symD` at the pair `(γ₁,γ₂,m₁,m₂)`. -/
def losymDTerm (P : ℤ[X]) (N k₁ k₂ : ℕ) (γ₁ γ₂ : Analysis.IonescuWainger.Circle)
    (m₁ m₂ : ℤ) (x y : ℝ) : ℂ :=
  M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
    * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
    * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))

theorem losymDTerm_eq (P : ℤ[X]) (N k₁ k₂ : ℕ) (γ₁ γ₂ : Analysis.IonescuWainger.Circle)
    (m₁ m₂ : ℤ) (x y : ℝ) :
    losymDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y
      = M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)) := rfl

/-- The term vanishes when the second representative is outside the window. -/
theorem losymDTerm_eq_zero_right (P : ℤ[X]) (hd : 1 ≤ P.natDegree) {N k₁ k₂ : ℕ}
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {γ₁ γ₂ : Analysis.IonescuWainger.Circle} (hc₂ : |gamR γ₂| ≤ 1)
    {m₁ m₂ : ℤ} (hm₂ : m₂ ∉ lomWindow) {x y : ℝ} (hy : |y| ≤ 4) :
    losymDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y = 0 := by
  have hz : varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)) = 0 :=
    lovarphitildeN_eq_zero_of_window P hd hk₂ hc₂ hy hm₂
  rw [losymDTerm_eq]
  rw [mul_eq_zero_of_right _ hz]

/-- The term vanishes when the first representative is outside the window. -/
theorem losymDTerm_eq_zero_left (P : ℤ[X]) {N k₁ k₂ : ℕ}
    (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {γ₁ γ₂ : Analysis.IonescuWainger.Circle} (hc₁ : |gamR γ₁| ≤ 1)
    {m₁ m₂ : ℤ} (hm₁ : m₁ ∉ lomWindow) {x y : ℝ} (hx : |x| ≤ 4) :
    losymDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y = 0 := by
  have hz : varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ)) = 0 :=
    lovarphiN_eq_zero_of_window hk₁ hc₁ hx hm₁
  rw [losymDTerm_eq]
  rw [show (M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)))
      = (M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ)) from by ring,
    hz, mul_zero]

/-- **The finite-window form of `symD`.** -/
theorem losymD_eq_window (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 1 ≤ P.natDegree)
    (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {x y : ℝ} (hx : |x| ≤ 4) (hy : |y| ≤ 4) :
    symD ρ P N l₁ l₂ k₁ k₂ x y =
      ∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂,
        ∑ m₁ ∈ lomWindow, ∑ m₂ ∈ lomWindow, losymDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y := by
  change (∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂, ∑' m₁ : ℤ, ∑' m₂ : ℤ,
      losymDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y) = _
  refine Finset.sum_congr rfl (fun γ₁ hγ₁ => Finset.sum_congr rfl (fun γ₂ hγ₂ => ?_))
  have hc₁ : |gamR γ₁| ≤ 1 := logamR_abs_le_one γ₁
  have hc₂ : |gamR γ₂| ≤ 1 := logamR_abs_le_one γ₂
  have hinner : ∀ m₁ : ℤ, (∑' m₂ : ℤ, losymDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y)
      = ∑ m₂ ∈ lomWindow, losymDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y := by
    intro m₁
    refine tsum_eq_sum (fun m₂ hm₂ => ?_)
    exact losymDTerm_eq_zero_right P hd hk₂ hc₂ hm₂ hy
  rw [tsum_congr hinner]
  refine tsum_eq_sum (fun m₁ hm₁ => ?_)
  refine Finset.sum_eq_zero (fun m₂ hm₂ => ?_)
  exact losymDTerm_eq_zero_left P hk₁ hc₁ hm₁ hx

/-! ## The product-finset form -/

/-- The index set of the finite sum representing `symD`. -/
def losymIdx (ρ : ℝ) (l₁ l₂ : ℕ) :
    Finset (((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) :=
  ((diffFreqs ρ l₁ ×ˢ diffFreqs ρ l₂) ×ˢ lomWindow) ×ˢ lomWindow

/-- The `M₀`-factor of a term of `symD`. -/
def losymDF (P : ℤ[X]) (N : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) :
    ℝ → ℝ → ℂ :=
  fun a b => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
    (a - gamR k.1.1.1 + (k.1.2 : ℝ)) (b - gamR k.1.1.2 + (k.2 : ℝ))

/-- The `φ_N`-factor of a term of `symD`. -/
def losymDPhi (N k₁ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) : ℝ → ℂ :=
  fun a => varphiN N k₁ (a - gamR k.1.1.1 + (k.1.2 : ℝ))

/-- The `φ̃_N`-factor of a term of `symD`. -/
def losymDPsi (P : ℤ[X]) (N k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) : ℝ → ℂ :=
  fun b => varphitildeN P.natDegree N k₂ (b - gamR k.1.1.2 + (k.2 : ℝ))

theorem losymDF_apply (P : ℤ[X]) (N k₁ k₂ : ℕ) (γ₁ γ₂ : Analysis.IonescuWainger.Circle)
    (m₁ m₂ : ℤ) (x y : ℝ) :
    losymDF P N (((γ₁, γ₂), m₁), m₂) x y * losymDPhi N k₁ (((γ₁, γ₂), m₁), m₂) x
      * losymDPsi P N k₂ (((γ₁, γ₂), m₁), m₂) y
      = losymDTerm P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y := rfl

/-- **The finite-window form of `symD`, indexed by the product finset.** -/
theorem losymD_eq_window_finset (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 1 ≤ P.natDegree)
    (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {x y : ℝ} (hx : |x| ≤ 4) (hy : |y| ≤ 4) :
    symD ρ P N l₁ l₂ k₁ k₂ x y =
      ∑ k ∈ losymIdx ρ l₁ l₂, losymDF P N k x y * losymDPhi N k₁ k x * losymDPsi P N k₂ k y := by
  rw [losymD_eq_window ρ P N l₁ l₂ k₁ k₂ hd hk₁ hk₂ hx hy]
  simp only [losymIdx, Finset.sum_product]
  refine Finset.sum_congr rfl (fun γ₁ h₁ => Finset.sum_congr rfl (fun γ₂ h₂ =>
    Finset.sum_congr rfl (fun m₁ h₃ => Finset.sum_congr rfl (fun m₂ h₄ => ?_))))
  exact (losymDF_apply P N k₁ k₂ γ₁ γ₂ m₁ m₂ x y).symm

/-! ## Smoothness of the differentiated symbol along the two coordinate axes -/

/-- `M0deriv` at `(0,0)` is `M0` itself. -/
theorem loM0deriv_zero_zero (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (x y : ℝ) :
    M0deriv P N q α₁ α₂ x y 0 0 = M0 P N q α₁ α₂ x y := by
  have hsum : (∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ x y (n : ℤ) 0 0)
      = ∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ x y (n : ℤ) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [momPhaseDeriv, pow_zero, mul_one]
  have hint : mTildeDeriv P N x y 0 0 = mTilde P N x y := by
    rw [mTildeDeriv, mTilde]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [pow_zero, mul_one]
  rw [M0deriv, M0, weylAvg, hsum, hint]

theorem loderiv_M0deriv_fst (P : Polynomial ℤ) (N q : ℕ) (α₁ α₂ : Analysis.IonescuWainger.Circle)
    (y : ℝ) (i₁ i₂ : ℕ) :
    deriv (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂)
      = fun a : ℝ => M0deriv P N q α₁ α₂ a y (i₁ + 1) i₂ := by
  funext a
  have hfun : (fun a' : ℝ => M0deriv P N q α₁ α₂ a' y i₁ i₂)
      = (fun a' : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a' y (n : ℤ) i₁ i₂)
        - (fun a' : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a' y i₁ i₂) := rfl
  have h1 : HasDerivAt (fun a' : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a' y (n : ℤ) i₁ i₂)
      ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a y (n : ℤ) (i₁ + 1) i₂) a :=
    HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => M0Aux.hasDerivAt_momPhaseDeriv_fst P N α₁ α₂ y (n : ℤ) i₁ i₂ a))
  have h2 : HasDerivAt (fun a' : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a' y i₁ i₂)
      (mZ P q α₁ α₂ * mTildeDeriv P N a y (i₁ + 1) i₂) a :=
    (M0Aux.hasDerivAt_mTildeDeriv_fst P N y i₁ i₂ a).const_mul _
  have h := h1.sub h2
  have hval : ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a y (n : ℤ) (i₁ + 1) i₂)
      - mZ P q α₁ α₂ * mTildeDeriv P N a y (i₁ + 1) i₂
      = M0deriv P N q α₁ α₂ a y (i₁ + 1) i₂ := rfl
  rw [hfun]
  rw [← hval]
  exact h.deriv

theorem loiteratedDeriv_M0deriv_fst (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (y : ℝ) (i₁ i₂ m : ℕ) :
    iteratedDeriv m (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂)
      = fun a : ℝ => M0deriv P N q α₁ α₂ a y (i₁ + m) i₂ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ, ih, loderiv_M0deriv_fst]
      simp [Nat.add_assoc]

theorem lodifferentiable_M0deriv_fst (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (y : ℝ) (i₁ i₂ : ℕ) :
    Differentiable ℝ (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂) := by
  have hfun : (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂)
      = (fun a : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a y (n : ℤ) i₁ i₂)
        - (fun a : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a y i₁ i₂) := rfl
  rw [hfun]
  refine Differentiable.sub ?_ ?_
  · exact (Differentiable.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => M0Aux.differentiable_momPhaseDeriv_fst P N α₁ α₂ y (n : ℤ) i₁ i₂)).const_mul _
  · exact (M0Aux.differentiable_mTildeDeriv_fst P N y i₁ i₂).const_mul _

theorem lodifferentiable_M0deriv_snd_zero (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (a : ℝ) (i₂ : ℕ) :
    Differentiable ℝ (fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 i₂) := by
  have hfun : (fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 i₂)
      = (fun b : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a b (n : ℤ) 0 i₂)
        - (fun b : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a b 0 i₂) := rfl
  rw [hfun]
  refine Differentiable.sub ?_ ?_
  · exact (Differentiable.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => M0Aux.differentiable_momPhaseDeriv_snd P N α₁ α₂ a (n : ℤ) 0 i₂)).const_mul _
  · exact (M0Aux.differentiable_mTildeDeriv_snd P N a i₂).const_mul _

theorem loM0deriv_contDiff_two_fst (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (y : ℝ) (i₁ i₂ : ℕ) :
    ContDiff ℝ 2 (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂) := by
  refine contDiff_of_differentiable_iteratedDeriv (fun m hm => ?_)
  rw [loiteratedDeriv_M0deriv_fst]
  exact lodifferentiable_M0deriv_fst P N q α₁ α₂ y (i₁ + m) i₂

theorem loderiv_M0deriv_snd_zero (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (a : ℝ) (j : ℕ) :
    deriv (fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 j)
      = fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 (j + 1) := by
  funext b
  have hfun : (fun b' : ℝ => M0deriv P N q α₁ α₂ a b' 0 j)
      = (fun b' : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            momPhaseDeriv P N α₁ α₂ a b' (n : ℤ) 0 j)
        - (fun b' : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a b' 0 j) := rfl
  have h1 : HasDerivAt (fun b' : ℝ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a b' (n : ℤ) 0 j)
      ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a b (n : ℤ) 0 (j + 1)) b :=
    HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Finset.Ioc (N / 2) N)
      (fun n _ => M0Aux.hasDerivAt_momPhaseDeriv_snd P N α₁ α₂ a (n : ℤ) 0 j b))
  have h2 : HasDerivAt (fun b' : ℝ => mZ P q α₁ α₂ * mTildeDeriv P N a b' 0 j)
      (mZ P q α₁ α₂ * mTildeDeriv P N a b 0 (j + 1)) b :=
    (M0Aux.hasDerivAt_mTildeDeriv_snd P N a j b).const_mul _
  have h := h1.sub h2
  have hval : ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
        momPhaseDeriv P N α₁ α₂ a b (n : ℤ) 0 (j + 1))
      - mZ P q α₁ α₂ * mTildeDeriv P N a b 0 (j + 1)
      = M0deriv P N q α₁ α₂ a b 0 (j + 1) := rfl
  rw [hfun]
  rw [← hval]
  exact h.deriv

/-- The iterated derivative of `M0` in its *second* variable is `M0deriv` with first index `0`. -/
theorem loiteratedDeriv_M0_snd (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (a : ℝ) (m : ℕ) :
    iteratedDeriv m (fun b : ℝ => M0 P N q α₁ α₂ a b)
      = fun b : ℝ => M0deriv P N q α₁ α₂ a b 0 m := by
  induction m with
  | zero =>
      funext b
      rw [iteratedDeriv_zero]
      exact (loM0deriv_zero_zero P N q α₁ α₂ a b).symm
  | succ m ih =>
      rw [iteratedDeriv_succ, ih, loderiv_M0deriv_snd_zero]

theorem loM0_contDiff_two_snd (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (a : ℝ) :
    ContDiff ℝ 2 (fun b : ℝ => M0 P N q α₁ α₂ a b) := by
  refine contDiff_of_differentiable_iteratedDeriv (n := (2 : ℕ∞)) (fun m hm => ?_)
  rw [loiteratedDeriv_M0_snd P N q α₁ α₂ a m]
  exact lodifferentiable_M0deriv_snd_zero P N q α₁ α₂ a m

/-- The iterated derivatives of a shift of `M0deriv` in its first variable. -/
theorem loM0deriv_contDiff_two_fst_comp (P : Polynomial ℤ) (N q : ℕ)
    (α₁ α₂ : Analysis.IonescuWainger.Circle) (y s : ℝ) (i₁ i₂ : ℕ) :
    ContDiff ℝ 2 (fun a : ℝ => M0deriv P N q α₁ α₂ (a + s) y i₁ i₂) := by
  have h1 : ContDiff ℝ 2 (fun a : ℝ => M0deriv P N q α₁ α₂ a y i₁ i₂) :=
    loM0deriv_contDiff_two_fst P N q α₁ α₂ y i₁ i₂
  have h2 : ContDiff ℝ 2 (fun a : ℝ => a + s) := by fun_prop
  simpa [Function.comp_def] using h1.comp h2

/-! ## The Leibniz expansion of `dp` on the finite sum forms of `symD` -/

lemma lofun_sum_eq {ι : Type*} (S : Finset ι) (g : ι → ℝ → ℂ) :
    (fun b : ℝ => ∑ k ∈ S, g k b) = ∑ k ∈ S, g k := by
  funext b
  simp [Finset.sum_apply]

theorem lodp_finset_sum_mul_three {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℝ → ℂ)
    (φ ψ : ι → ℝ → ℂ)
    (j₁ j₂ : ℕ) (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) (y : ℝ) (x : ℝ)
    (hFb : ∀ k ∈ S, ∀ a : ℝ, ContDiff ℝ 2 (fun b : ℝ => F k a b))
    (hFc : ∀ k ∈ S, ∀ i₂ : ℕ, i₂ ≤ j₂ →
      ContDiff ℝ 2 (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => F k a b) y))
    (hφ : ∀ k ∈ S, ContDiff ℝ 2 (φ k)) (hψ : ∀ k ∈ S, ContDiff ℝ 2 (ψ k)) :
    dp j₁ j₂ (fun a b => ∑ k ∈ S, F k a b * φ k a * ψ k b) x y
      = ∑ k ∈ S, ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
          ((j₂.choose i₂ : ℂ) * (j₁.choose i₁ : ℂ))
            * (iteratedDeriv i₁ (φ k) x)
            * (iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => F k a b) y) x)
            * (iteratedDeriv (j₂ - i₂) (ψ k) y) := by
  have hj₂' : (j₂ : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj₂
  have hj₁' : (j₁ : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj₁
  have hstep1 : (fun a : ℝ => iteratedDeriv j₂ (fun b : ℝ => ∑ k ∈ S, F k a b * φ k a * ψ k b) y)
      = fun a : ℝ => ∑ k ∈ S, φ k a * (∑ i₂ ∈ Finset.range (j₂ + 1),
          (j₂.choose i₂ : ℂ) * iteratedDeriv i₂ (fun b : ℝ => F k a b) y
            * iteratedDeriv (j₂ - i₂) (ψ k) y) := by
    funext a
    rw [lofun_sum_eq S (fun k b => F k a b * φ k a * ψ k b)]
    rw [iteratedDeriv_sum (f := fun k b => F k a b * φ k a * ψ k b) (I := S) (x := y)
      (fun k hk => ((((hFb k hk a).contDiffAt).of_le hj₂').mul contDiffAt_const).mul
        (((hψ k hk).contDiffAt).of_le hj₂'))]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hA : ContDiffAt ℝ (j₂ : WithTop ℕ∞) (fun b : ℝ => F k a b) y :=
      ((hFb k hk a).contDiffAt).of_le hj₂'
    have hB : ContDiffAt ℝ (j₂ : WithTop ℕ∞) (ψ k) y := ((hψ k hk).contDiffAt).of_le hj₂'
    have hfun : (fun b : ℝ => F k a b * φ k a * ψ k b)
        = fun b : ℝ => φ k a * (F k a b * ψ k b) := by
      funext b; ring
    rw [hfun, iteratedDeriv_const_mul (φ k a) (hA.mul hB)]
    rw [show (fun b : ℝ => F k a b * ψ k b) = (fun b : ℝ => F k a b) * (ψ k) from rfl,
      iteratedDeriv_mul hA hB]
  change iteratedDeriv j₁
    (fun a : ℝ => iteratedDeriv j₂ (fun b : ℝ => ∑ k ∈ S, F k a b * φ k a * ψ k b) y) x = _
  rw [hstep1]
  rw [lofun_sum_eq S (fun k a => φ k a * (∑ i₂ ∈ Finset.range (j₂ + 1),
          (j₂.choose i₂ : ℂ) * iteratedDeriv i₂ (fun b : ℝ => F k a b) y
            * iteratedDeriv (j₂ - i₂) (ψ k) y))]
  rw [iteratedDeriv_sum (f := fun k a => φ k a * (∑ i₂ ∈ Finset.range (j₂ + 1),
          (j₂.choose i₂ : ℂ) * iteratedDeriv i₂ (fun b : ℝ => F k a b) y
            * iteratedDeriv (j₂ - i₂) (ψ k) y)) (I := S) (x := x)
      (fun k hk => (((hφ k hk).contDiffAt).of_le hj₁').mul (by
        refine ContDiffAt.sum (fun i₂ hi₂ => ?_)
        exact ((contDiffAt_const (c := (j₂.choose i₂ : ℂ))).mul
          (((hFc k hk i₂ (by have := Finset.mem_range.mp hi₂; omega)).contDiffAt).of_le
            hj₁')).mul contDiffAt_const))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkeq : (fun a : ℝ => φ k a * (∑ i₂ ∈ Finset.range (j₂ + 1),
        (j₂.choose i₂ : ℂ) * iteratedDeriv i₂ (fun b : ℝ => F k a b) y
          * iteratedDeriv (j₂ - i₂) (ψ k) y))
      = ∑ i₂ ∈ Finset.range (j₂ + 1), (fun a : ℝ => ((j₂.choose i₂ : ℂ)
          * iteratedDeriv (j₂ - i₂) (ψ k) y)
          * (φ k a * iteratedDeriv i₂ (fun b : ℝ => F k a b) y)) := by
    funext a
    rw [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i₂ _ => by ring)
  rw [hkeq]
  rw [iteratedDeriv_sum (f := fun i₂ a => ((j₂.choose i₂ : ℂ)
        * iteratedDeriv (j₂ - i₂) (ψ k) y) * (φ k a * iteratedDeriv i₂ (fun b : ℝ => F k a b) y))
      (I := Finset.range (j₂ + 1)) (x := x) (fun i₂ hi₂ => contDiffAt_const.mul
        ((((hφ k hk).contDiffAt).of_le hj₁').mul
          (((hFc k hk i₂ (by have := Finset.mem_range.mp hi₂; omega)).contDiffAt).of_le hj₁')))]
  refine Finset.sum_congr rfl (fun i₂ hi₂ => ?_)
  have hi₂' : i₂ ≤ j₂ := by have := Finset.mem_range.mp hi₂; omega
  have hA : ContDiffAt ℝ (j₁ : WithTop ℕ∞) (fun a : ℝ => φ k a) x :=
    ((hφ k hk).contDiffAt).of_le hj₁'
  have hB : ContDiffAt ℝ (j₁ : WithTop ℕ∞)
      (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => F k a b) y) x :=
    ((hFc k hk i₂ hi₂').contDiffAt).of_le hj₁'
  rw [iteratedDeriv_const_mul (f := fun a : ℝ => φ k a * iteratedDeriv i₂ (fun b : ℝ => F k a b) y)
    ((j₂.choose i₂ : ℂ) * iteratedDeriv (j₂ - i₂) (ψ k) y) (hA.mul hB)]
  rw [show (fun a : ℝ => φ k a * iteratedDeriv i₂ (fun b : ℝ => F k a b) y)
        = (φ k) * (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => F k a b) y) from rfl,
      iteratedDeriv_mul hA hB]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i₁ _ => ?_)
  ring

/-! ## The mixed partials of the terms of `symD` -/

theorem loiteratedDeriv_symDPhi (N k₁ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) (m : ℕ) :
    iteratedDeriv m (losymDPhi N k₁ k)
      = fun x : ℝ => iteratedDeriv m (varphiN N k₁) (x - gamR k.1.1.1 + (k.1.2 : ℝ)) := by
  have hfun : losymDPhi N k₁ k
      = fun a : ℝ => varphiN N k₁ (a + ((k.1.2 : ℝ) - gamR k.1.1.1)) := by
    funext a
    simp only [losymDPhi]
    rw [show a - gamR k.1.1.1 + (k.1.2 : ℝ) = a + ((k.1.2 : ℝ) - gamR k.1.1.1) from by ring]
  rw [hfun, iteratedDeriv_comp_add_const]
  funext x
  rw [show x + ((k.1.2 : ℝ) - gamR k.1.1.1) = x - gamR k.1.1.1 + (k.1.2 : ℝ) from by ring]

theorem loiteratedDeriv_symDPsi (P : ℤ[X]) (N k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) (m : ℕ) :
    iteratedDeriv m (losymDPsi P N k₂ k)
      = fun x : ℝ => iteratedDeriv m (varphitildeN P.natDegree N k₂)
          (x - gamR k.1.1.2 + (k.2 : ℝ)) := by
  have hfun : losymDPsi P N k₂ k
      = fun a : ℝ => varphitildeN P.natDegree N k₂ (a + ((k.2 : ℝ) - gamR k.1.1.2)) := by
    funext a
    simp only [losymDPsi]
    rw [show a - gamR k.1.1.2 + (k.2 : ℝ) = a + ((k.2 : ℝ) - gamR k.1.1.2) from by ring]
  rw [hfun, iteratedDeriv_comp_add_const]
  funext x
  rw [show x + ((k.2 : ℝ) - gamR k.1.1.2) = x - gamR k.1.1.2 + (k.2 : ℝ) from by ring]

theorem losymDF_iteratedDeriv (P : ℤ[X]) (N k₁ k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ)
    (i₁ i₂ : ℕ) (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ 2) (x y : ℝ) :
    iteratedDeriv i₁ (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => losymDF P N k a b) y) x
      = M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
          (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ)) i₁ i₂ := by
  have hstep : (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => losymDF P N k a b) y)
      = fun a : ℝ => iteratedDeriv i₂
          (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
            (a + ((k.1.2 : ℝ) - gamR k.1.1.1)) b) (y + ((k.2 : ℝ) - gamR k.1.1.2)) := by
    funext a
    have hfe : (fun b : ℝ => losymDF P N k a b)
        = fun b : ℝ => (fun b' : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
            (a + ((k.1.2 : ℝ) - gamR k.1.1.1)) b') (b + ((k.2 : ℝ) - gamR k.1.1.2)) := by
      funext b
      simp only [losymDF]
      rw [show a - gamR k.1.1.1 + (k.1.2 : ℝ) = a + ((k.1.2 : ℝ) - gamR k.1.1.1) from by ring,
        show b - gamR k.1.1.2 + (k.2 : ℝ) = b + ((k.2 : ℝ) - gamR k.1.1.2) from by ring]
    rw [hfe, iteratedDeriv_comp_add_const]
  rw [hstep]
  have hgoal : iteratedDeriv i₁ (fun a : ℝ => iteratedDeriv i₂
        (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
          (a + ((k.1.2 : ℝ) - gamR k.1.1.1)) b) (y + ((k.2 : ℝ) - gamR k.1.1.2))) x
      = iteratedDeriv i₁ (fun u : ℝ => iteratedDeriv i₂
        (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2 u b)
          (y + ((k.2 : ℝ) - gamR k.1.1.2))) (x + ((k.1.2 : ℝ) - gamR k.1.1.1)) :=
    congrFun (iteratedDeriv_comp_add_const i₁ (fun u : ℝ => iteratedDeriv i₂
      (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2 u b)
        (y + ((k.2 : ℝ) - gamR k.1.1.2))) ((k.1.2 : ℝ) - gamR k.1.1.1)) x
  rw [hgoal]
  have h := M0_iteratedDeriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2 hi₁ hi₂
    (x + ((k.1.2 : ℝ) - gamR k.1.1.1)) (y + ((k.2 : ℝ) - gamR k.1.1.2))
  rw [h]
  rw [show x + ((k.1.2 : ℝ) - gamR k.1.1.1) = x - gamR k.1.1.1 + (k.1.2 : ℝ) from by ring,
    show y + ((k.2 : ℝ) - gamR k.1.1.2) = y - gamR k.1.1.2 + (k.2 : ℝ) from by ring]

/-! ## Support of the derivatives of the bumps -/

theorem loiteratedDeriv_varphiN_eq_zero_of_radius (N k m : ℕ) {ξ : ℝ}
    (h : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |ξ|) :
    iteratedDeriv m (varphiN N k) ξ = 0 := by
  have hpos : 0 < (|ξ| - (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) / 2 := by
    linarith
  have heq : (varphiN N k) =ᶠ[𝓝 ξ] (fun _ => (0 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds ξ hpos] with x hx
    refine lovarphiN_eq_zero_of_lt ?_
    have h1 : dist x ξ < (|ξ| - (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) / 2 := hx
    rw [dist_eq_norm, Real.norm_eq_abs] at h1
    have h2 : |ξ| - |x| ≤ |x - ξ| := by
      have h3 := abs_sub_abs_le_abs_sub ξ x
      rw [abs_sub_comm] at h3
      exact h3
    linarith
  rw [Filter.EventuallyEq.iteratedDeriv_eq m heq]
  simp

theorem lovarphitildeN_eq_zero_of_lt {d N k : ℕ} (hd : 1 ≤ d) {ξ : ℝ}
    (h : (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) < |ξ|) :
    varphitildeN d N k ξ = 0 := by
  by_contra hne
  exact absurd (lovarphitildeN_ne_zero_abs_le d N k hd hne) (not_le.mpr h)

theorem loiteratedDeriv_varphitildeN_eq_zero_of_radius (d N k m : ℕ) (hd : 1 ≤ d) {ξ : ℝ}
    (h : (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) < |ξ|) :
    iteratedDeriv m (varphitildeN d N k) ξ = 0 := by
  have hpos : 0 < (|ξ| - (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) / 2 := by
    linarith
  have heq : (varphitildeN d N k) =ᶠ[𝓝 ξ] (fun _ => (0 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds ξ hpos] with x hx
    refine lovarphitildeN_eq_zero_of_lt hd ?_
    have h1 : dist x ξ < (|ξ|
        - (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) / 2 := hx
    rw [dist_eq_norm, Real.norm_eq_abs] at h1
    have h2 : |ξ| - |x| ≤ |x - ξ| := by
      have h3 := abs_sub_abs_le_abs_sub ξ x
      rw [abs_sub_comm] at h3
      exact h3
    linarith
  rw [Filter.EventuallyEq.iteratedDeriv_eq m heq]
  simp

/-! ## The pointwise bound for the derivatives of `symD` -/

theorem louScale_pos {ρ : ℝ} (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ Work.KMTAreas.A7.uScale ρ L := by
  rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  have hpow : ((1 : ℤ) : ℝ) ≤ ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    rw [Nat.cast_one, Int.cast_one, one_mul]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : (1 : ℤ) ≤ ⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    Int.le_floor.mpr hpow
  have h0 : (0 : ℤ) ≤ ⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    le_trans (by norm_num) hfl
  have h3 : (1 : ℤ) ≤ ((⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]
    exact hfl
  exact_mod_cast h3

theorem lole_logN_toNat (N l₁ l₂ k₁ k₂ : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hC2 : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) {k : ℕ} (hk : k ≤ max k₁ k₂) :
    k + 3 ≤ (Work.Analysis.EndVar.logN N).toNat := by
  have hu : 1 ≤ Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) := louScale_pos (le_of_lt hρ) _
  omega

/-! ## Smoothness of the pieces of a term of `symD` -/

theorem locontDiff_symDPhi (N k₁ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) :
    ContDiff ℝ 2 (losymDPhi N k₁ k) := by
  have h : ContDiff ℝ 2 (fun a : ℝ => a - gamR k.1.1.1 + (k.1.2 : ℝ)) := by fun_prop
  exact (contDiff_varphiN N k₁).comp h

theorem locontDiff_symDPsi (P : ℤ[X]) (N k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) :
    ContDiff ℝ 2 (losymDPsi P N k₂ k) := by
  have h : ContDiff ℝ 2 (fun b : ℝ => b - gamR k.1.1.2 + (k.2 : ℝ)) := by fun_prop
  exact (contDiff_varphitildeN P.natDegree N k₂).comp h

theorem locontDiff_symDF_snd (P : ℤ[X]) (N : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) (a : ℝ) :
    ContDiff ℝ 2 (fun b : ℝ => losymDF P N k a b) := by
  have h1 : ContDiff ℝ 2 (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (a - gamR k.1.1.1 + (k.1.2 : ℝ)) b) :=
    loM0_contDiff_two_snd P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (a - gamR k.1.1.1 + (k.1.2 : ℝ))
  have h2 : ContDiff ℝ 2 (fun b : ℝ => M0 P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (a - gamR k.1.1.1 + (k.1.2 : ℝ)) (b - gamR k.1.1.2 + (k.2 : ℝ))) :=
    h1.comp (by fun_prop)
  simpa [losymDF] using h2

theorem locontDiff_iteratedDeriv_symDF (P : ℤ[X]) (N k₁ k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ)
    (i₂ : ℕ) (hi₂ : i₂ ≤ 2) (y : ℝ) :
    ContDiff ℝ 2 (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => losymDF P N k a b) y) := by
  have hgoal : (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => losymDF P N k a b) y)
      = (fun a : ℝ => M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
          (a + ((k.1.2 : ℝ) - gamR k.1.1.1))
          (y + ((k.2 : ℝ) - gamR k.1.1.2)) 0 i₂) := by
    funext a
    have h := losymDF_iteratedDeriv P N k₁ k₂ k 0 i₂ (by norm_num) hi₂ a y
    rw [iteratedDeriv_zero] at h
    rw [h]
    congr 1 <;> ring
  rw [hgoal]
  exact loM0deriv_contDiff_two_fst_comp P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (y + ((k.2 : ℝ) - gamR k.1.1.2)) ((k.1.2 : ℝ) - gamR k.1.1.1) 0 i₂

/-! ## The Leibniz identity for `symD` -/

theorem lodp_symD_eq_leibniz (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 2 ≤ P.natDegree)
    (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (j₁ j₂ : ℕ) (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) {x y : ℝ} (hx : |x| < 4) (hy : |y| < 4) :
    dp j₁ j₂ (symD ρ P N l₁ l₂ k₁ k₂) x y
      = ∑ k ∈ losymIdx ρ l₁ l₂, ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
          ((j₂.choose i₂ : ℂ) * (j₁.choose i₁ : ℂ))
            * (iteratedDeriv i₁ (losymDPhi N k₁ k) x)
            * (iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => losymDF P N k a b) y) x)
            * (iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y) := by
  have h2 : ∀ a : ℝ, |a| < 4 → (fun b : ℝ => symD ρ P N l₁ l₂ k₁ k₂ a b)
      =ᶠ[𝓝 y] (fun b : ℝ => ∑ k ∈ losymIdx ρ l₁ l₂,
        losymDF P N k a b * losymDPhi N k₁ k a * losymDPsi P N k₂ k b) := by
    intro a ha
    filter_upwards [Metric.ball_mem_nhds y (by linarith : (0 : ℝ) < 4 - |y|)] with b hb
    have hb4 : |b| < 4 := by
      have h1 : dist b y < 4 - |y| := hb
      rw [dist_eq_norm, Real.norm_eq_abs] at h1
      have h3 := abs_sub_abs_le_abs_sub b y
      linarith
    exact losymD_eq_window_finset ρ P N l₁ l₂ k₁ k₂ (by omega) hk₁ hk₂ (le_of_lt ha) (le_of_lt hb4)
  have h3 : (fun a : ℝ => dp2 j₂ (symD ρ P N l₁ l₂ k₁ k₂) a y)
      =ᶠ[𝓝 x] (fun a : ℝ => dp2 j₂ (fun a b => ∑ k ∈ losymIdx ρ l₁ l₂,
        losymDF P N k a b * losymDPhi N k₁ k a * losymDPsi P N k₂ k b) a y) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < 4 - |x|)] with a ha
    have ha4 : |a| < 4 := by
      have h1 : dist a x < 4 - |x| := ha
      rw [dist_eq_norm, Real.norm_eq_abs] at h1
      have h3 := abs_sub_abs_le_abs_sub a x
      linarith
    exact Filter.EventuallyEq.iteratedDeriv_eq j₂ (h2 a ha4)
  have h4 := Filter.EventuallyEq.iteratedDeriv_eq j₁ h3
  change iteratedDeriv j₁ (fun a : ℝ => dp2 j₂ (symD ρ P N l₁ l₂ k₁ k₂) a y) x = _
  rw [h4]
  change dp j₁ j₂ (fun a b => ∑ k ∈ losymIdx ρ l₁ l₂,
    losymDF P N k a b * losymDPhi N k₁ k a * losymDPsi P N k₂ k b) x y = _
  exact lodp_finset_sum_mul_three (losymIdx ρ l₁ l₂) (fun k => losymDF P N k) (fun k => losymDPhi N k₁ k)
    (fun k => losymDPsi P N k₂ k) j₁ j₂ hj₁ hj₂ y x
    (fun k hk a => locontDiff_symDF_snd P N k a)
    (fun k hk i₂ hi₂ => locontDiff_iteratedDeriv_symDF P N k₁ k₂ k i₂ (le_trans hi₂ hj₂) y)
    (fun k hk => locontDiff_symDPhi N k₁ k)
    (fun k hk => locontDiff_symDPsi P N k₂ k)

/-! ## The pointwise bound -/

theorem lochoose_le_four {j i : ℕ} (hj : j ≤ 2) : ((j.choose i : ℕ) : ℝ) ≤ 4 := by
  have h1 : j.choose i ≤ 2 ^ j := Nat.choose_le_two_pow j i
  have h2 : 2 ^ j ≤ 4 := by interval_cases j <;> norm_num
  have h3 : j.choose i ≤ 4 := le_trans h1 h2
  exact_mod_cast h3

theorem lole_pow_div_of_abs_le {N k : ℕ} (hN : 1 ≤ N) {ξ : ℝ}
    (hξ : |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :
    |ξ| ≤ (2 : ℝ) ^ (k + 1) / (N : ℝ) := by
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
    have h' : N ≤ 2 ^ (Nat.log 2 (max N 2) + 1) := le_trans (le_max_left _ _) (le_of_lt h)
    have h'' : ((N : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by exact_mod_cast h'
    rw [Nat.cast_pow] at h''
    simp only [Nat.cast_ofNat] at h''
    rw [show ((2 : ℝ) ^ (Nat.log 2 (max N 2) + 1))
        = (2 : ℝ) ^ ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ) from
      (Real.rpow_natCast 2 (Nat.log 2 (max N 2) + 1)).symm] at h''
    have hL : ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ)
        = (Work.Analysis.EndVar.logN N : ℝ) + 1 := by
      rw [Work.Analysis.EndVar.logN]; push_cast; ring
    rwa [hL] at h''
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hk1 : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (N : ℝ)
      ≤ (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
    calc (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (N : ℝ)
        ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
            * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hNle (le_of_lt h2pos)
      _ = (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1
          push_cast
          ring
  have hk : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (N : ℝ)
      ≤ (2 : ℝ) ^ (k + 1) := by
    rw [Real.rpow_natCast] at hk1
    exact hk1
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (N:ℝ))]
  exact le_trans (mul_le_mul_of_nonneg_right hξ (by positivity)) hk

theorem lole_pow_div_pow_of_abs_le {N k d : ℕ} (hN : 1 ≤ N) {ξ : ℝ}
    (hξ : |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) :
    |ξ| ≤ (2 : ℝ) ^ (d * (k + 1)) / (N : ℝ) ^ d := by
  have hNle : (N : ℝ) ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2)
    have h' : N ≤ 2 ^ (Nat.log 2 (max N 2) + 1) := le_trans (le_max_left _ _) (le_of_lt h)
    have h'' : ((N : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by exact_mod_cast h'
    rw [Nat.cast_pow] at h''
    simp only [Nat.cast_ofNat] at h''
    rw [show ((2 : ℝ) ^ (Nat.log 2 (max N 2) + 1))
        = (2 : ℝ) ^ ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ) from
      (Real.rpow_natCast 2 (Nat.log 2 (max N 2) + 1)).symm] at h''
    have hL : ((Nat.log 2 (max N 2) + 1 : ℕ) : ℝ)
        = (Work.Analysis.EndVar.logN N : ℝ) + 1 := by
      rw [Work.Analysis.EndVar.logN]; push_cast; ring
    rwa [hL] at h''
  have hNd : (N : ℝ) ^ d ≤ ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) ^ d :=
    pow_le_pow_left₀ (by positivity) hNle d
  have hexp : (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
        * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) ^ d
      = (2 : ℝ) ^ ((d * (k + 1) : ℕ) : ℝ) := by
    rw [show ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) ^ d
        = (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℝ) + 1) * (d : ℝ)) by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) d,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ d)]
  calc |ξ| * (N : ℝ) ^ d
      ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) * (N : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hξ (by positivity)
    _ ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
          * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) + 1)) ^ d :=
        mul_le_mul_of_nonneg_left hNd (by positivity)
    _ = (2 : ℝ) ^ ((d * (k + 1) : ℕ) : ℝ) := hexp
    _ = (2 : ℝ) ^ (d * (k + 1)) := by rw [Real.rpow_natCast]

theorem lodp_symD_pointwise_le (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 2 ≤ P.natDegree)
    (hN : 1 ≤ N) (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (j₁ j₂ : ℕ) (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) {x y : ℝ} (hx : |x| < 4) (hy : |y| < 4)
    {C_M : ℝ} (hC_M : 0 ≤ C_M)
    (hM0 : ∀ (N q j₁ j₂ k₁ k₂ : ℕ) (α₁ α₂ : Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ),
      j₁ ≤ 2 → j₂ ≤ 2 → 1 ≤ N → 0 < q → q • α₁ = 0 → q • α₂ = 0 →
      |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) →
      |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree →
      ‖Work.KMTAreas.A7.M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖
        ≤ C_M * (q : ℝ) ^ 2
          * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ ((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ) - 1)) :
    ‖dp j₁ j₂ (symD ρ P N l₁ l₂ k₁ k₂) x y‖
      ≤ ∑ k ∈ losymIdx ρ l₁ l₂, ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
          (16 * (C_M * (perQ k.1.1.1 k.1.1.2) ^ 2
              * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
              * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1)))
          * ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖
          * ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖ := by
  rw [lodp_symD_eq_leibniz ρ P N l₁ l₂ k₁ k₂ hd hk₁ hk₂ j₁ j₂ hj₁ hj₂ hx hy]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun k hk => ?_)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun i₂ hi₂ => ?_)
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun i₁ hi₁ => ?_)
  have hi₁' : i₁ ≤ j₁ := by have := Finset.mem_range.mp hi₁; omega
  have hi₂' : i₂ ≤ j₂ := by have := Finset.mem_range.mp hi₂; omega
  have hC : ‖((j₂.choose i₂ : ℂ) * (j₁.choose i₁ : ℂ))‖ ≤ 16 := by
    rw [norm_mul]
    have h1 := lochoose_le_four (j := j₂) (i := i₂) hj₂
    have h2 := lochoose_le_four (j := j₁) (i := i₁) hj₁
    rw [Complex.norm_natCast, Complex.norm_natCast]
    nlinarith [abs_of_nonneg (show (0:ℝ) ≤ ((j₂.choose i₂ : ℕ) : ℝ) by positivity),
      abs_of_nonneg (show (0:ℝ) ≤ ((j₁.choose i₁ : ℕ) : ℝ) by positivity)]
  have hsupp₁ : ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖ ≠ 0 →
      |x - gamR k.1.1.1 + (k.1.2 : ℝ)|
        ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
    intro h1
    by_contra hlt
    rw [not_le] at hlt
    refine h1 ?_
    simp only [loiteratedDeriv_symDPhi N k₁ k i₁, loiteratedDeriv_varphiN_eq_zero_of_radius N k₁ i₁ hlt,
      norm_zero]
  have hsupp₂ : ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖ ≠ 0 →
      |y - gamR k.1.1.2 + (k.2 : ℝ)|
        ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
    intro h1
    by_contra hlt
    rw [not_le] at hlt
    refine h1 ?_
    simp only [loiteratedDeriv_symDPsi P N k₂ k (j₂ - i₂),
      loiteratedDeriv_varphitildeN_eq_zero_of_radius P.natDegree N k₂ (j₂ - i₂) (by omega) hlt,
      norm_zero]
  rw [norm_mul, norm_mul, norm_mul,
    losymDF_iteratedDeriv P N k₁ k₂ k (j₁ - i₁) i₂ (by omega) (by omega) x y]
  by_cases h1 : ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖ = 0
  · rw [h1]; simp
  by_cases h2 : ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖ = 0
  · rw [h2]; simp
  have hmem : k.1.1.1 ∈ iwArithFreqs ρ l₁ ∧ k.1.1.2 ∈ iwArithFreqs ρ l₂ := by
    have h1 := Finset.mem_product.mp hk
    have h2 := Finset.mem_product.mp h1.1
    have h3 := Finset.mem_product.mp h2.1
    have hsub : ∀ l : ℕ, diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
      intro l γ hγ
      unfold diffFreqs at hγ
      split_ifs at hγ with h
      · rw [h]; exact hγ
      · exact (Finset.mem_sdiff.mp hγ).1
    exact ⟨hsub l₁ h3.1, hsub l₂ h3.2⟩
  have hper : 0 < perQ k.1.1.1 k.1.1.2 := by
    obtain ⟨q₁, hq₁, hγ₁⟩ := mem_iwArithFreqs.mp hmem.1
    obtain ⟨q₂, hq₂, hγ₂⟩ := mem_iwArithFreqs.mp hmem.2
    have ho₁ : addOrderOf k.1.1.1 ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hγ₁) (pos_of_mem_iwP hq₁)).ne'
    have ho₂ : addOrderOf k.1.1.2 ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hγ₂) (pos_of_mem_iwP hq₂)).ne'
    rw [perQ]
    exact Nat.lcm_pos (Nat.pos_of_ne_zero ho₁) (Nat.pos_of_ne_zero ho₂)
  have hξ₁ := lole_pow_div_of_abs_le hN (hsupp₁ h1)
  have hξ₂ : |y - gamR k.1.1.2 + (k.2 : ℝ)|
      ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree := by
    refine lole_pow_div_pow_of_abs_le hN (hsupp₂ h2)
  have hM := hM0 N (perQ k.1.1.1 k.1.1.2) (j₁ - i₁) i₂ k₁ k₂ k.1.1.1 k.1.1.2
    (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ))
    (by omega) (by omega) hN hper (loperQ_smul_left _ _) (loperQ_smul_right _ _) hξ₁ hξ₂
  have hK : ‖Work.KMTAreas.A7.M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
      (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ)) (j₁ - i₁) i₂‖
      ≤ C_M * (perQ k.1.1.1 k.1.1.2 : ℝ) ^ 2
        * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
        * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1) := by
    have hexp : ((j₁ - i₁ : ℕ) : ℤ) = (j₁ : ℤ) - (i₁ : ℤ) := by omega
    calc ‖Work.KMTAreas.A7.M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
          (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ)) (j₁ - i₁) i₂‖
        ≤ C_M * (perQ k.1.1.1 k.1.1.2 : ℝ) ^ 2
          * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ (((j₁ - i₁ : ℕ) : ℤ) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1) := hM
      _ = C_M * (perQ k.1.1.1 k.1.1.2 : ℝ) ^ 2
          * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1) := by
          rw [hexp]
  calc ‖((j₂.choose i₂ : ℂ) * (j₁.choose i₁ : ℂ))‖ * ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖
        * ‖Work.KMTAreas.A7.M0deriv P N (perQ k.1.1.1 k.1.1.2) k.1.1.1 k.1.1.2
            (x - gamR k.1.1.1 + (k.1.2 : ℝ)) (y - gamR k.1.1.2 + (k.2 : ℝ)) (j₁ - i₁) i₂‖
        * ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖
      ≤ (16 * ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖
          * (C_M * (perQ k.1.1.1 k.1.1.2 : ℝ) ^ 2
            * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
            * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1)))
        * ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖ := by
        refine mul_le_mul (mul_le_mul ?_ hK (norm_nonneg _) (by positivity)) le_rfl
          (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    _ = (16 * (C_M * (perQ k.1.1.1 k.1.1.2) ^ 2
            * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
            * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1)))
          * ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖
          * ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖ := by ring


/-! ## The continuous scale `2^{Log N}` and the arithmetic of the bump masses

The estimates of the two bump masses bound the `L¹` mass of the `m`-th derivative of the bumps by
`C · (2^{Log N} / 2^k)^{m-1}`.  Combined with the factor `N^{(j₁-i₁)+d i₂-1}` of the single-scale
estimate `ModelApproxCore_M0_deriv_bound` this produces the exponent `(j₁-2) + d(j₂-1)` of the
final bound, because `2^{Log N}` is comparable to `N` (within a factor `2`).  This section
collects that elementary bookkeeping. -/

/-- The continuous scale `2^{Log N}`, `Log N = ⌊log₂ N⌋`. -/
noncomputable def lothN (N : ℕ) : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)

/-- The scale `2^{d(Log N - k)}` of the second bump. -/
noncomputable def lopsN (d N k : ℕ) : ℝ :=
  ((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) / (2 : ℝ) ^ (d * k)

theorem lothN_pos (N : ℕ) : 0 < lothN N := Real.rpow_pos_of_pos (by norm_num) _

theorem lopsN_pos (d N k : ℕ) : 0 < lopsN d N k := by
  rw [lopsN]; positivity

/-- `lopsN d N k` is the `d`-th power of the elementary scale `2^{Log N}/2^k`. -/
theorem lopsN_eq (d N k : ℕ) : lopsN d N k = (lothN N / (2 : ℝ) ^ k) ^ d := by
  have h2 : ((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
      = ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ d := by
    rw [← Real.rpow_natCast (2 : ℝ) d, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_comm ((d : ℕ) : ℝ) ((Work.Analysis.EndVar.logN N : ℤ) : ℝ),
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have h3 : (2 : ℝ) ^ (d * k) = ((2 : ℝ) ^ k) ^ d := by
    rw [mul_comm d k, pow_mul]
  rw [lopsN, lothN, h2, h3, ← div_pow]

/-- `2^{Log N} ≤ N` for `N ≥ 2`. -/
theorem lothN_le {N : ℕ} (hN : 2 ≤ N) : lothN N ≤ (N : ℝ) := by
  have hx : max N 2 ≠ 0 := by omega
  have h := Nat.pow_log_le_self 2 hx
  have hmax : max N 2 = N := max_eq_left (by omega)
  rw [hmax] at h
  rw [lothN, Work.Analysis.EndVar.logN]
  simp only [Int.cast_natCast, Real.rpow_natCast]
  rw [hmax]
  exact_mod_cast h

/-- `N ≤ 2 · 2^{Log N}`. -/
theorem lole_two_mul_thN (N : ℕ) : (N : ℝ) ≤ 2 * lothN N := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
  have hN : N ≤ 2 ^ (Nat.log 2 (max N 2) + 1) := le_trans (le_max_left N 2) (le_of_lt h)
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (max N 2) + 1) := by
    have h2 : (N : ℝ) ≤ (((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hN
    simpa using h2
  rw [lothN, Work.Analysis.EndVar.logN]
  simp only [Int.cast_natCast, Real.rpow_natCast]
  calc (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (max N 2) + 1) := hNr
    _ = 2 * (2 : ℝ) ^ (Nat.log 2 (max N 2)) := by rw [pow_succ]; ring

/-- A power of a number in `[1/2,1]` with exponent at least `-G` is at most `2^G`. -/
theorem lorpow_le_two_pow {c r G : ℝ} (h1 : 1 / 2 ≤ c) (h2 : c ≤ 1) (hG : 0 ≤ G)
    (hr : -G ≤ r) : c ^ r ≤ (2 : ℝ) ^ G := by
  by_cases hr0 : 0 ≤ r
  · calc c ^ r ≤ 1 ^ r := Real.rpow_le_rpow (by linarith) h2 hr0
      _ = 1 := Real.one_rpow r
      _ ≤ (2 : ℝ) ^ G := Real.one_le_rpow (by norm_num) hG
  · have hr0' : r < 0 := not_le.mp hr0
    calc c ^ r ≤ (1 / 2) ^ r := Real.rpow_le_rpow_of_nonpos (by norm_num) h1 (le_of_lt hr0')
      _ = (2 : ℝ) ^ (-r) := by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
            Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2) r,
            ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) r]
      _ ≤ (2 : ℝ) ^ G := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **The comparison of the elementary scale with `N`.**  For `r ∈ [-d,d]` the `r`-th power of
`2^{Log N}/2^k` is at most `2^d · N^r · 2^{kd}`. -/
theorem loscale_factor_le {N k : ℕ} (hN : 2 ≤ N) {d : ℕ} (hd : 1 ≤ d) {r : ℝ}
    (hr₁ : -(d : ℝ) ≤ r) (hr₂ : r ≤ (d : ℝ)) :
    (lothN N / (2 : ℝ) ^ k) ^ r ≤ (2 : ℝ) ^ d * (N : ℝ) ^ r * (2 : ℝ) ^ (k * d) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hcpos : 0 < lothN N / (N : ℝ) := div_pos (lothN_pos N) hNpos
  set c : ℝ := lothN N / (N : ℝ) with hc
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hNpos]; exact lothN_le hN
  have hc2 : (1 : ℝ) / 2 ≤ c := by
    rw [hc, le_div_iff₀ hNpos]
    have := lole_two_mul_thN N
    linarith
  have hΘeq : lothN N = c * (N : ℝ) := by
    rw [hc]; field_simp
  have hsplit : (lothN N / (2 : ℝ) ^ k) ^ r = c ^ r * (N : ℝ) ^ r * ((2 : ℝ) ^ k) ^ (-r) := by
    rw [hΘeq,
      show c * (N : ℝ) / (2 : ℝ) ^ k = c * (N : ℝ) * ((2 : ℝ) ^ k)⁻¹ from by ring,
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ c * (N : ℝ))
        (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹),
      Real.mul_rpow (le_of_lt hcpos) (le_of_lt hNpos),
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) r,
      ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) r]
  rw [hsplit]
  have hdr : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hcr : c ^ r ≤ (2 : ℝ) ^ d := by
    simpa using lorpow_le_two_pow hc2 hc1 hdr (by linarith)
  have h2r : ((2 : ℝ) ^ k) ^ (-r) ≤ (2 : ℝ) ^ (k * d) := by
    rw [← Real.rpow_natCast (2 : ℝ) k,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((k : ℕ) : ℝ) (-r),
      ← Real.rpow_natCast (2 : ℝ) (k * d)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    push_cast
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have h : -r ≤ (d : ℝ) := by linarith
    have hml := mul_le_mul_of_nonneg_left h hk
    linarith
  have hNrpos : 0 < (N : ℝ) ^ r := Real.rpow_pos_of_pos hNpos r
  calc c ^ r * (N : ℝ) ^ r * ((2 : ℝ) ^ k) ^ (-r)
      ≤ (2 : ℝ) ^ d * (N : ℝ) ^ r * ((2 : ℝ) ^ k) ^ (-r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcr (le_of_lt hNrpos))
          (by positivity)
    _ ≤ (2 : ℝ) ^ d * (N : ℝ) ^ r * (2 : ℝ) ^ (k * d) :=
        mul_le_mul_of_nonneg_left h2r (by positivity)

/-! ## The `L¹` masses of the two bump factors -/

theorem lolintegral_symDPhi_le (N k₁ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ)
    (i₁ : ℕ) (hi₁ : i₁ ≤ 2) {Cφ : ℝ}
    (hφb : ∀ (N k m : ℕ), m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (varphiN N k) ξ‖)
        ≤ ENNReal.ofReal (Cφ * (lothN N / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1))) :
    (∫⁻ x : ℝ, ENNReal.ofReal ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖)
      ≤ ENNReal.ofReal (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((i₁ : ℝ) - 1)) := by
  have h1 : (∫⁻ x : ℝ, ENNReal.ofReal ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖)
      = ∫⁻ x : ℝ, ENNReal.ofReal
          ‖iteratedDeriv i₁ (varphiN N k₁) (x - gamR k.1.1.1 + (k.1.2 : ℝ))‖ := by
    refine lintegral_congr (fun x => ?_)
    simp only [loiteratedDeriv_symDPhi N k₁ k i₁]
  rw [h1]
  have h2 : (∫⁻ x : ℝ, ENNReal.ofReal
        ‖iteratedDeriv i₁ (varphiN N k₁) (x - gamR k.1.1.1 + (k.1.2 : ℝ))‖)
      = ∫⁻ x : ℝ, ENNReal.ofReal ‖iteratedDeriv i₁ (varphiN N k₁) x‖ := by
    rw [show (fun x : ℝ => ENNReal.ofReal
          ‖iteratedDeriv i₁ (varphiN N k₁) (x - gamR k.1.1.1 + (k.1.2 : ℝ))‖)
        = fun x : ℝ => (fun z : ℝ => ENNReal.ofReal ‖iteratedDeriv i₁ (varphiN N k₁) z‖)
            (x + ((k.1.2 : ℝ) - gamR k.1.1.1)) from by
          funext x
          rw [show x - gamR k.1.1.1 + (k.1.2 : ℝ) = x + ((k.1.2 : ℝ) - gamR k.1.1.1)
            from by ring]]
    rw [MeasureTheory.lintegral_add_right_eq_self
      (fun z : ℝ => ENNReal.ofReal ‖iteratedDeriv i₁ (varphiN N k₁) z‖)
      ((k.1.2 : ℝ) - gamR k.1.1.1)]
  rw [h2]
  exact hφb N k₁ i₁ hi₁

theorem lolintegral_symDPsi_le (P : ℤ[X]) (N k₂ : ℕ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ)
    (n : ℕ) (hn : n ≤ 2) {Cψ : ℝ}
    (hψb : ∀ (N k m : ℕ), m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (varphitildeN P.natDegree N k) ξ‖)
        ≤ ENNReal.ofReal (Cψ * (lopsN P.natDegree N k) ^ ((m : ℝ) - 1))) :
    (∫⁻ y : ℝ, ENNReal.ofReal ‖iteratedDeriv n (losymDPsi P N k₂ k) y‖)
      ≤ ENNReal.ofReal (Cψ * (lopsN P.natDegree N k₂) ^ ((n : ℝ) - 1)) := by
  have h1 : (∫⁻ y : ℝ, ENNReal.ofReal ‖iteratedDeriv n (losymDPsi P N k₂ k) y‖)
      = ∫⁻ y : ℝ, ENNReal.ofReal
          ‖iteratedDeriv n (varphitildeN P.natDegree N k₂) (y - gamR k.1.1.2 + (k.2 : ℝ))‖ := by
    refine lintegral_congr (fun y => ?_)
    simp only [loiteratedDeriv_symDPsi P N k₂ k n]
  rw [h1]
  have h2 : (∫⁻ y : ℝ, ENNReal.ofReal
        ‖iteratedDeriv n (varphitildeN P.natDegree N k₂) (y - gamR k.1.1.2 + (k.2 : ℝ))‖)
      = ∫⁻ y : ℝ, ENNReal.ofReal ‖iteratedDeriv n (varphitildeN P.natDegree N k₂) y‖ := by
    rw [show (fun y : ℝ => ENNReal.ofReal
          ‖iteratedDeriv n (varphitildeN P.natDegree N k₂) (y - gamR k.1.1.2 + (k.2 : ℝ))‖)
        = fun y : ℝ => (fun z : ℝ =>
            ENNReal.ofReal ‖iteratedDeriv n (varphitildeN P.natDegree N k₂) z‖)
            (y + ((k.2 : ℝ) - gamR k.1.1.2)) from by
          funext y
          rw [show y - gamR k.1.1.2 + (k.2 : ℝ) = y + ((k.2 : ℝ) - gamR k.1.1.2)
            from by ring]]
    rw [MeasureTheory.lintegral_add_right_eq_self
      (fun z : ℝ => ENNReal.ofReal ‖iteratedDeriv n (varphitildeN P.natDegree N k₂) z‖)
      ((k.2 : ℝ) - gamR k.1.1.2)]
  rw [h2]
  exact hψb N k₂ n hn

/-! ## The combination of the `M₀`-mass with the two bump masses -/

/-- **The exponent bookkeeping.**  The product of the single-scale factor
`N^{(j₁-i₁)+d i₂-1}`, the first bump mass `(2^{Log N}/2^{k₁})^{i₁-1}` and the second bump mass
`(2^{d(Log N-k₂)})^{j₂-i₂-1}` is bounded by
`N^{(j₁-2)+d(j₂-1)} · 2^{1+d+k₁+d k₂}`. -/
theorem losymD_N_mass_le {N d k₁ k₂ i₁ i₂ j₁ j₂ : ℕ} (hN : 2 ≤ N) (hd : 1 ≤ d)
    (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ j₂) (hj₂ : j₂ ≤ 2) :
    (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1))
        * (lothN N / (2 : ℝ) ^ k₁) ^ ((i₁ : ℝ) - 1)
        * (lopsN d N k₂) ^ (((j₂ - i₂ : ℕ) : ℝ) - 1)
      ≤ (N : ℝ) ^ ((j₁ : ℝ) - 2 + (d : ℝ) * ((j₂ : ℝ) - 1))
        * (2 : ℝ) ^ (1 + d + k₁ + d * k₂) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hXpos : (0 : ℝ) < lothN N / (2 : ℝ) ^ k₁ := div_pos (lothN_pos N) (by positivity)
  have hZpos : (0 : ℝ) < lothN N / (2 : ℝ) ^ k₂ := div_pos (lothN_pos N) (by positivity)
  have hnd1 : (((j₂ - i₂ : ℕ) : ℝ) - 1) ≤ 1 := by
    have h : ((j₂ - i₂ : ℕ) : ℝ) ≤ 2 := by
      have h' : j₂ - i₂ ≤ 2 := by omega
      exact_mod_cast h'
    linarith
  have hnd2 : (-1 : ℝ) ≤ ((j₂ - i₂ : ℕ) : ℝ) - 1 := by
    have h : (0 : ℝ) ≤ ((j₂ - i₂ : ℕ) : ℝ) := by positivity
    linarith
  have hs₁ : (lothN N / (2 : ℝ) ^ k₁) ^ ((i₁ : ℝ) - 1)
      ≤ (2 : ℝ) ^ 1 * (N : ℝ) ^ ((i₁ : ℝ) - 1) * (2 : ℝ) ^ (k₁ * 1) :=
    loscale_factor_le hN (d := 1) (by norm_num) (r := (i₁ : ℝ) - 1)
      (by have h : (0 : ℝ) ≤ (i₁ : ℝ) := Nat.cast_nonneg i₁
          have h1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
          linarith)
      (by have h : (i₁ : ℝ) ≤ 2 := by exact_mod_cast hi₁
          have h1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
          linarith)
  have hs₂ : (lothN N / (2 : ℝ) ^ k₂) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))
      ≤ (2 : ℝ) ^ d * (N : ℝ) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1)) * (2 : ℝ) ^ (k₂ * d) :=
    loscale_factor_le hN hd (r := (d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))
      (by have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          have h := mul_le_mul_of_nonneg_left hnd2 hdnn
          linarith)
      (by have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          have h := mul_le_mul_of_nonneg_left hnd1 hdnn
          linarith)
  have hcast : ((j₂ - i₂ : ℕ) : ℝ) = (j₂ : ℝ) - (i₂ : ℝ) := Nat.cast_sub hi₂
  have hexp : (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1 : ℤ) : ℝ)
      + ((i₁ : ℝ) - 1) + (d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1)
      = (j₁ : ℝ) - 2 + (d : ℝ) * ((j₂ : ℝ) - 1) := by
    rw [hcast]; push_cast; ring
  have hmain : (lothN N / (2 : ℝ) ^ k₁) ^ ((i₁ : ℝ) - 1)
        * (lothN N / (2 : ℝ) ^ k₂) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))
      ≤ ((2 : ℝ) ^ 1 * (N : ℝ) ^ ((i₁ : ℝ) - 1) * (2 : ℝ) ^ (k₁ * 1))
        * ((2 : ℝ) ^ d * (N : ℝ) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))
          * (2 : ℝ) ^ (k₂ * d)) :=
    mul_le_mul hs₁ hs₂ (le_of_lt (Real.rpow_pos_of_pos hZpos _))
      (by have := Real.rpow_pos_of_pos hNpos ((i₁ : ℝ) - 1); positivity)
  have h2merge : (2 : ℝ) ^ 1 * (2 : ℝ) ^ d * (2 : ℝ) ^ (k₁ * 1) * (2 : ℝ) ^ (k₂ * d)
      = (2 : ℝ) ^ (1 + d + k₁ + d * k₂) := by
    rw [Nat.mul_one, Nat.mul_comm k₂ d, ← pow_add, ← pow_add, ← pow_add]
  have hNrmerge : (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1 : ℤ) : ℝ)
        * (N : ℝ) ^ ((i₁ : ℝ) - 1) * (N : ℝ) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))
      = (N : ℝ) ^ ((j₁ : ℝ) - 2 + (d : ℝ) * ((j₂ : ℝ) - 1)) := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, hexp]
  rw [← Real.rpow_intCast (N : ℝ) (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1)),
    lopsN_eq d N k₂,
    ← Real.rpow_natCast (lothN N / (2 : ℝ) ^ k₂) d,
    ← Real.rpow_mul (le_of_lt hZpos) ((d : ℕ) : ℝ) (((j₂ - i₂ : ℕ) : ℝ) - 1)]
  calc (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1 : ℤ) : ℝ)
        * (lothN N / (2 : ℝ) ^ k₁) ^ ((i₁ : ℝ) - 1)
        * (lothN N / (2 : ℝ) ^ k₂) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))
      = (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1 : ℤ) : ℝ)
        * ((lothN N / (2 : ℝ) ^ k₁) ^ ((i₁ : ℝ) - 1)
          * (lothN N / (2 : ℝ) ^ k₂) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))) := by ring
    _ ≤ (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1 : ℤ) : ℝ)
        * (((2 : ℝ) ^ 1 * (N : ℝ) ^ ((i₁ : ℝ) - 1) * (2 : ℝ) ^ (k₁ * 1))
          * ((2 : ℝ) ^ d * (N : ℝ) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))
            * (2 : ℝ) ^ (k₂ * d))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((2 : ℝ) ^ 1 * (2 : ℝ) ^ d * (2 : ℝ) ^ (k₁ * 1) * (2 : ℝ) ^ (k₂ * d))
        * ((N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1 : ℤ) : ℝ)
          * (N : ℝ) ^ ((i₁ : ℝ) - 1) * (N : ℝ) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))) := by
        ring
    _ = (2 : ℝ) ^ (1 + d + k₁ + d * k₂)
        * ((N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ) + (d : ℤ) * (i₂ : ℤ) - 1 : ℤ) : ℝ)
          * (N : ℝ) ^ ((i₁ : ℝ) - 1) * (N : ℝ) ^ ((d : ℝ) * (((j₂ - i₂ : ℕ) : ℝ) - 1))) := by
        rw [h2merge]
    _ = (2 : ℝ) ^ (1 + d + k₁ + d * k₂)
        * (N : ℝ) ^ ((j₁ : ℝ) - 2 + (d : ℝ) * ((j₂ : ℝ) - 1)) := by rw [hNrmerge]
    _ = (N : ℝ) ^ ((j₁ : ℝ) - 2 + (d : ℝ) * ((j₂ : ℝ) - 1))
        * (2 : ℝ) ^ (1 + d + k₁ + d * k₂) := by ring

/-! ## The finite index set, the counting bounds, and the integration step -/

/-- The index set of the finite form of `symD`: the frequency pair, the two fibre representatives
and the two orders of differentiation. -/
def losymDJ (ρ : ℝ) (l₁ l₂ j₁ j₂ : ℕ) :
    Finset ((((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ)
      × (ℕ × ℕ)) :=
  (losymIdx ρ l₁ l₂) ×ˢ ((Finset.range (j₂ + 1)) ×ˢ (Finset.range (j₁ + 1)))

theorem locard_mWindow : lomWindow.card = 11 := by
  rw [lomWindow, Int.card_Icc]; decide

private theorem lodiffFreqs_subset (ρ : ℝ) (l : ℕ) : diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
  intro γ hγ
  unfold diffFreqs at hγ
  split_ifs at hγ with h
  · rw [h]; exact hγ
  · exact (Finset.mem_sdiff.mp hγ).1

/-- The number of index tuples of the finite form of `symD`: at most `1089 = 11·11·9` times the
number of frequency pairs. -/
theorem locard_symDJ_le (ρ : ℝ) (l₁ l₂ j₁ j₂ : ℕ) (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) :
    ((losymDJ ρ l₁ l₂ j₁ j₂).card : ℝ)
      ≤ 1089 * (((diffFreqs ρ l₁).card * (diffFreqs ρ l₂).card : ℕ) : ℝ) := by
  have hA : (0 : ℝ) ≤ (((diffFreqs ρ l₁).card * (diffFreqs ρ l₂).card : ℕ) : ℝ) := by positivity
  have hJ : (((j₂ + 1 : ℕ) : ℝ)) * ((j₁ + 1 : ℕ) : ℝ) ≤ 9 := by
    have h1 : ((j₁ + 1 : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast (show j₁ + 1 ≤ 3 by omega)
    have h2 : ((j₂ + 1 : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast (show j₂ + 1 ≤ 3 by omega)
    have h1n : (0 : ℝ) ≤ ((j₁ + 1 : ℕ) : ℝ) := by positivity
    have h2n : (0 : ℝ) ≤ ((j₂ + 1 : ℕ) : ℝ) := by positivity
    nlinarith [h1, h2, h1n, h2n]
  have hc : ((losymDJ ρ l₁ l₂ j₁ j₂).card : ℝ)
      = 121 * ((((diffFreqs ρ l₁).card * (diffFreqs ρ l₂).card : ℕ) : ℝ)
          * (((j₂ + 1 : ℕ) : ℝ) * ((j₁ + 1 : ℕ) : ℝ))) := by
    rw [losymDJ, losymIdx, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
      locard_mWindow]
    push_cast
    ring
  rw [hc]
  calc 121 * ((((diffFreqs ρ l₁).card * (diffFreqs ρ l₂).card : ℕ) : ℝ)
        * (((j₂ + 1 : ℕ) : ℝ) * ((j₁ + 1 : ℕ) : ℝ)))
      ≤ 121 * ((((diffFreqs ρ l₁).card * (diffFreqs ρ l₂).card : ℕ) : ℝ) * 9) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hJ hA
    _ = 1089 * (((diffFreqs ρ l₁).card * (diffFreqs ρ l₂).card : ℕ) : ℝ) := by norm_num; ring

/-- The number of exact-height arithmetic frequencies at the level `l ≤ L` grows at most like
`2^{2^{ρL}}`. -/
theorem locard_diffFreqs_le (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l L : ℕ, l ≤ L →
      ((diffFreqs ρ l).card : ℝ) ≤ C * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))) := by
  obtain ⟨C, hC, hCl⟩ := Work.Analysis.IonescuWainger.iw_height_card_le hρ
  refine ⟨C, hC, fun l L hl => ?_⟩
  have hcard : ((diffFreqs ρ l).card : ℝ) ≤ ((iwArithFreqs ρ l).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (lodiffFreqs_subset ρ l)
  refine hcard.trans ((hCl l).trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  have hexp : ρ * (l : ℝ) ≤ ρ * (L : ℝ) := by
    have h : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
    nlinarith [le_of_lt hρ]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- The hypothesis `hC2` of the target forces `N ≥ 2` (indeed `N ≥ 8`). -/
theorem lotwo_le_of_hC2 {N k₁ k₂ L : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ L + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat) : 2 ≤ N := by
  have hu : 1 ≤ Work.KMTAreas.A7.uScale ρ L := louScale_pos (le_of_lt hρ) L
  have h3 : 3 ≤ (Work.Analysis.EndVar.logN N).toNat := by omega
  have hto : (Work.Analysis.EndVar.logN N).toNat = Nat.log 2 (max N 2) := by
    rw [Work.Analysis.EndVar.logN, Int.toNat_natCast]
  rw [hto] at h3
  have hpow : (8 : ℕ) ≤ 2 ^ Nat.log 2 (max N 2) := by
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [← h8]
    exact Nat.pow_le_pow_right (by norm_num) h3
  have hle : 2 ^ Nat.log 2 (max N 2) ≤ max N 2 :=
    Nat.pow_log_le_self 2 (by omega)
  omega

/-! ## The constant of a term of `symD` -/

/-- The constant multiplying a term of the finite form of `symD` (the `M₀`-mass). -/
noncomputable def losymDKer (P : ℤ[X]) (N j₁ k₁ k₂ : ℕ) (C_M : ℝ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ)
    (i₁ i₂ : ℕ) : ℝ :=
  16 * (C_M * (perQ k.1.1.1 k.1.1.2) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
    * (N : ℝ) ^ (((j₁ : ℤ) - (i₁ : ℤ)) + (P.natDegree : ℤ) * (i₂ : ℤ) - 1))

/-- The same constant with the exponent already reduced to `(j₁-2) + d(j₂-1)`. -/
noncomputable def losymDKer2 (P : ℤ[X]) (N j₁ j₂ k₁ k₂ : ℕ) (C_M : ℝ)
    (k : ((Analysis.IonescuWainger.Circle × Analysis.IonescuWainger.Circle) × ℤ) × ℤ) : ℝ :=
  16 * (C_M * (perQ k.1.1.1 k.1.1.2) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
    * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1)))

/-! ## The integration of the pointwise bound -/

/-- **The integrated bound for `dp j₁ j₂ symD`.**  Integrating the pointwise bound
`lodp_symD_pointwise_le` against the two bump masses gives the bound with the exponent
`(j₁-2) + d(j₂-1)` which appears in the final estimate. -/
theorem losymD_dp_lintegral_le (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (hd : 2 ≤ P.natDegree)
    (hN : 2 ≤ N) (hk₁ : k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hk₂ : k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (j₁ j₂ : ℕ) (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2)
    {C_M Cφ Cψ : ℝ} (hCM : 0 ≤ C_M) (hCφ : 0 ≤ Cφ) (hCψ : 0 ≤ Cψ)
    (hM0 : ∀ (N q j₁ j₂ k₁ k₂ : ℕ) (α₁ α₂ : Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ),
      j₁ ≤ 2 → j₂ ≤ 2 → 1 ≤ N → 0 < q → q • α₁ = 0 → q • α₂ = 0 →
      |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) →
      |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree →
      ‖Work.KMTAreas.A7.M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖
        ≤ C_M * (q : ℝ) ^ 2
          * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ ((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ) - 1))
    (hφb : ∀ (N k m : ℕ), m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (varphiN N k) ξ‖)
        ≤ ENNReal.ofReal (Cφ * (lothN N / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1)))
    (hψb : ∀ (N k m : ℕ), m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (varphitildeN P.natDegree N k) ξ‖)
        ≤ ENNReal.ofReal (Cψ * (lopsN P.natDegree N k) ^ ((m : ℝ) - 1))) :
    (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal ‖dp j₁ j₂ (symD ρ P N l₁ l₂ k₁ k₂) x y‖)
      ≤ ENNReal.ofReal (((losymDJ ρ l₁ l₂ j₁ j₂).card : ℝ)
          * (∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂, ((perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2)
          * (16 * C_M * (2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ))
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1))) := by
  classical
  -- the pointwise bound, restricted to the unit square
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal ‖dp j₁ j₂ (symD ρ P N l₁ l₂ k₁ k₂) x y‖
        ≤ ENNReal.ofReal (∑ k ∈ losymIdx ρ l₁ l₂,
            ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
              losymDKer P N j₁ k₁ k₂ C_M k i₁ i₂
                * ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖
                * ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖) := by
    intro x hx y hy
    have hx4 : |x| < 4 := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hy4 : |y| < 4 := by
      rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := lodp_symD_pointwise_le ρ P N l₁ l₂ k₁ k₂ hd (by omega) hk₁ hk₂ j₁ j₂ hj₁ hj₂
      hx4 hy4 hCM hM0
    simpa only [losymDKer, Work.A7.Sval] using h
  -- the reindexing
  have hreindex : ∀ x y : ℝ,
      (∑ k ∈ losymIdx ρ l₁ l₂, ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
          losymDKer P N j₁ k₁ k₂ C_M k i₁ i₂
            * ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖
            * ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖)
      = ∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂,
          losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
            * ‖iteratedDeriv jj.2.2 (losymDPhi N k₁ jj.1) x‖
            * ‖iteratedDeriv (j₂ - jj.2.1) (losymDPsi P N k₂ jj.1) y‖ := by
    intro x y
    rw [losymDJ]
    simp only [Finset.sum_product]
  -- the double integral of the pointwise bound
  have hstep1 : (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal ‖dp j₁ j₂ (symD ρ P N l₁ l₂ k₁ k₂) x y‖)
      ≤ ∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (∑ k ∈ losymIdx ρ l₁ l₂,
            ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
              losymDKer P N j₁ k₁ k₂ C_M k i₁ i₂
                * ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖
                * ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖) := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hy
    exact hpt x hx y hy
  refine hstep1.trans ?_
  rw [show (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (∑ k ∈ losymIdx ρ l₁ l₂,
          ∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
            losymDKer P N j₁ k₁ k₂ C_M k i₁ i₂
              * ‖iteratedDeriv i₁ (losymDPhi N k₁ k) x‖
              * ‖iteratedDeriv (j₂ - i₂) (losymDPsi P N k₂ k) y‖))
      = ∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂,
            losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
              * ‖iteratedDeriv jj.2.2 (losymDPhi N k₁ jj.1) x‖
              * ‖iteratedDeriv (j₂ - jj.2.1) (losymDPsi P N k₂ jj.1) y‖) from by
    refine lintegral_congr (fun x => ?_)
    refine lintegral_congr (fun y => ?_)
    exact congrArg ENNReal.ofReal (hreindex x y)]
  refine (lolintegral_ofReal_sum_separable (losymDJ ρ l₁ l₂ j₁ j₂)
      (fun jj => losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1)
      (fun jj x => ‖iteratedDeriv jj.2.2 (losymDPhi N k₁ jj.1) x‖)
      (fun jj y => ‖iteratedDeriv (j₂ - jj.2.1) (losymDPsi P N k₂ jj.1) y‖)
      ?_ ?_ ?_ ?_ ?_ measurableSet_Icc measurableSet_Icc).trans ?_
  · -- nonnegativity of the constants
    intro jj hjj
    rw [losymDKer]
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    refine mul_nonneg (by norm_num) ?_
    refine mul_nonneg (mul_nonneg (mul_nonneg hCM (sq_nonneg _)) ?_) ?_
    · exact add_nonneg (by norm_num) (div_nonneg (sq_nonneg _) (le_of_lt hNpos))
    · exact zpow_nonneg (le_of_lt hNpos) _
  · intro jj hjj x; exact norm_nonneg _
  · intro jj hjj y; exact norm_nonneg _
  · -- measurability in `x`
    intro jj hjj
    have hmem : jj.1 ∈ losymIdx ρ l₁ l₂ ∧
        jj.2 ∈ (Finset.range (j₂ + 1)).product (Finset.range (j₁ + 1)) := by
      rw [losymDJ] at hjj
      exact Finset.mem_product.mp hjj
    have hi₁ : jj.2.2 ≤ 2 := by
      have h := (Finset.mem_product.mp hmem.2).2
      have := Finset.mem_range.mp h
      omega
    exact ((locontDiff_symDPhi N k₁ jj.1).continuous_iteratedDeriv jj.2.2
      (by exact_mod_cast hi₁)).norm.measurable.ennreal_ofReal
  · -- measurability in `y`
    intro jj hjj
    have hmem : jj.1 ∈ losymIdx ρ l₁ l₂ ∧
        jj.2 ∈ (Finset.range (j₂ + 1)).product (Finset.range (j₁ + 1)) := by
      rw [losymDJ] at hjj
      exact Finset.mem_product.mp hjj
    have hi₂ : jj.2.1 ≤ j₂ := by
      have h := (Finset.mem_product.mp hmem.2).1
      have := Finset.mem_range.mp h
      omega
    exact ((locontDiff_symDPsi P N k₂ jj.1).continuous_iteratedDeriv (j₂ - jj.2.1)
      (by exact_mod_cast (by omega : j₂ - jj.2.1 ≤ 2))).norm.measurable.ennreal_ofReal
  · -- the sum over the index set
    have hstep2 : (∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂,
          ENNReal.ofReal (losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1)
            * (∫⁻ x : ℝ, ENNReal.ofReal ‖iteratedDeriv jj.2.2 (losymDPhi N k₁ jj.1) x‖)
            * (∫⁻ y : ℝ, ENNReal.ofReal
                ‖iteratedDeriv (j₂ - jj.2.1) (losymDPsi P N k₂ jj.1) y‖))
        ≤ ∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂,
          ENNReal.ofReal (losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1
            * ((2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ))) := by
      refine Finset.sum_le_sum (fun jj hjj => ?_)
      have hmem : jj.1 ∈ losymIdx ρ l₁ l₂ ∧
          jj.2 ∈ (Finset.range (j₂ + 1)).product (Finset.range (j₁ + 1)) := by
        rw [losymDJ] at hjj
        exact Finset.mem_product.mp hjj
      have hi₁ : jj.2.2 ≤ 2 := by
        have h := (Finset.mem_product.mp hmem.2).2
        have := Finset.mem_range.mp h
        omega
      have hi₂ : jj.2.1 ≤ j₂ := by
        have h := (Finset.mem_product.mp hmem.2).1
        have := Finset.mem_range.mp h
        omega
      have hX := lolintegral_symDPhi_le N k₁ jj.1 jj.2.2 hi₁ hφb
      have hY := lolintegral_symDPsi_le P N k₂ jj.1 (j₂ - jj.2.1)
        (by omega : j₂ - jj.2.1 ≤ 2) hψb
      have hmass := losymD_N_mass_le (N := N) (d := P.natDegree) (k₁ := k₁) (k₂ := k₂)
        (i₁ := jj.2.2) (i₂ := jj.2.1) (j₁ := j₁) (j₂ := j₂) hN (by omega) hi₁ hi₂ hj₂
      have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
      have hSq : (0 : ℝ) ≤ (perQ jj.1.1.1.1 jj.1.1.1.2 : ℝ) ^ 2 := sq_nonneg _
      have hW : (0 : ℝ) ≤ 1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) :=
        add_nonneg (by norm_num) (div_nonneg (sq_nonneg _) (le_of_lt hNpos))
      have hnn1 : (0 : ℝ) ≤ losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1 := by
        rw [losymDKer]
        refine mul_nonneg (by norm_num) ?_
        refine mul_nonneg (mul_nonneg (mul_nonneg hCM hSq) hW) ?_
        exact zpow_nonneg (le_of_lt hNpos) _
      have hXA : (0 : ℝ) ≤ Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1) :=
        mul_nonneg hCφ (Real.rpow_nonneg (div_nonneg (le_of_lt (lothN_pos N)) (by positivity)) _)
      have hnn2 : (0 : ℝ) ≤ losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
          * (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1)) := mul_nonneg hnn1 hXA
      have hcoef : (0 : ℝ) ≤ 16 * (C_M * (perQ jj.1.1.1.1 jj.1.1.1.2 : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))) * (Cφ * Cψ) :=
        mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCM hSq) hW))
          (mul_nonneg hCφ hCψ)
      have hreal : losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
            * (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1))
            * (Cψ * (lopsN P.natDegree N k₂) ^ ((((j₂ - jj.2.1 : ℕ) : ℝ)) - 1))
          ≤ losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1
            * ((2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ)) := by
        calc losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
              * (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1))
              * (Cψ * (lopsN P.natDegree N k₂) ^ ((((j₂ - jj.2.1 : ℕ) : ℝ)) - 1))
            = 16 * (C_M * (perQ jj.1.1.1.1 jj.1.1.1.2 : ℝ) ^ 2
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))) * (Cφ * Cψ)
              * ((N : ℝ) ^ (((j₁ : ℤ) - (jj.2.2 : ℤ)) + (P.natDegree : ℤ) * (jj.2.1 : ℤ) - 1)
                * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1)
                * (lopsN P.natDegree N k₂) ^ ((((j₂ - jj.2.1 : ℕ) : ℝ)) - 1)) := by
              rw [losymDKer]; ring
          _ ≤ 16 * (C_M * (perQ jj.1.1.1.1 jj.1.1.1.2 : ℝ) ^ 2
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))) * (Cφ * Cψ)
              * ((N : ℝ) ^ ((j₁ : ℝ) - 2 + (P.natDegree : ℝ) * ((j₂ : ℝ) - 1))
                * (2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂)) :=
              mul_le_mul_of_nonneg_left hmass hcoef
          _ = losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1
              * ((2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ)) := by
              rw [show (N : ℝ) ^ ((j₁ : ℝ) - 2 + (P.natDegree : ℝ) * ((j₂ : ℝ) - 1))
                  = (N : ℝ) ^ ((((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1) : ℤ) : ℝ)
                  from by congr 1; push_cast; ring,
                Real.rpow_intCast, losymDKer2]
              ring
      calc ENNReal.ofReal (losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1)
            * (∫⁻ x : ℝ, ENNReal.ofReal ‖iteratedDeriv jj.2.2 (losymDPhi N k₁ jj.1) x‖)
            * (∫⁻ y : ℝ, ENNReal.ofReal ‖iteratedDeriv (j₂ - jj.2.1) (losymDPsi P N k₂ jj.1) y‖)
          ≤ ENNReal.ofReal (losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1)
            * ENNReal.ofReal (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1))
            * ENNReal.ofReal (Cψ * (lopsN P.natDegree N k₂) ^ ((((j₂ - jj.2.1 : ℕ) : ℝ)) - 1)) := by
            refine mul_le_mul (mul_le_mul le_rfl hX (zero_le) (zero_le)) hY
              (zero_le) (zero_le)
        _ = ENNReal.ofReal (losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
              * (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1))
              * (Cψ * (lopsN P.natDegree N k₂) ^ ((((j₂ - jj.2.1 : ℕ) : ℝ)) - 1))) := by
            rw [show ENNReal.ofReal (losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1)
                  * ENNReal.ofReal (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1))
                = ENNReal.ofReal (losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
                    * (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1)))
                from (ENNReal.ofReal_mul hnn1).symm,
              show ENNReal.ofReal (losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
                    * (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1)))
                  * ENNReal.ofReal (Cψ * (lopsN P.natDegree N k₂) ^ ((((j₂ - jj.2.1 : ℕ) : ℝ)) - 1))
                = ENNReal.ofReal (losymDKer P N j₁ k₁ k₂ C_M jj.1 jj.2.2 jj.2.1
                    * (Cφ * (lothN N / (2 : ℝ) ^ k₁) ^ ((jj.2.2 : ℝ) - 1))
                    * (Cψ * (lopsN P.natDegree N k₂) ^ ((((j₂ - jj.2.1 : ℕ) : ℝ)) - 1)))
                from (ENNReal.ofReal_mul hnn2).symm]
        _ ≤ ENNReal.ofReal (losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1
              * ((2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ))) :=
            ENNReal.ofReal_le_ofReal hreal
    refine hstep2.trans ?_
    rw [show (∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂,
          ENNReal.ofReal (losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1
            * ((2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ))))
        = ENNReal.ofReal (∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂,
            losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1
              * ((2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ))) from by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro jj hjj
      have hs2nn : (0 : ℝ) ≤ losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1 := by
        rw [losymDKer2]
        have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
        refine mul_nonneg (by norm_num) ?_
        refine mul_nonneg (mul_nonneg (mul_nonneg hCM (sq_nonneg _)) ?_) ?_
        · exact add_nonneg (by norm_num) (div_nonneg (sq_nonneg _) (le_of_lt hNpos))
        · exact zpow_nonneg (le_of_lt hNpos) _
      exact mul_nonneg hs2nn (mul_nonneg (by positivity) (mul_nonneg hCφ hCψ))]
    rw [← Finset.sum_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsum : (∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂, losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1)
        ≤ ((losymDJ ρ l₁ l₂ j₁ j₂).card : ℝ)
          * (16 * (C_M * (∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂,
                ((perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2)
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
              * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1)))) := by
      rw [show (∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂, losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1)
          = ∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂, (16 * (C_M
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
              * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1))))
            * (perQ jj.1.1.1.1 jj.1.1.1.2 : ℝ) ^ 2 from by
        refine Finset.sum_congr rfl (fun jj hjj => ?_)
        rw [losymDKer2]; ring]
      have hmid : (∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂,
            (16 * (C_M * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
              * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1))))
            * (perQ jj.1.1.1.1 jj.1.1.1.2 : ℝ) ^ 2)
          ≤ ∑ _jj ∈ losymDJ ρ l₁ l₂ j₁ j₂,
              (16 * (C_M * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
                * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1))))
              * (∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂, ((perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2) := by
        refine Finset.sum_le_sum (fun jj hjj => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hmem : jj.1 ∈ losymIdx ρ l₁ l₂ ∧
            jj.2 ∈ (Finset.range (j₂ + 1)).product (Finset.range (j₁ + 1)) := by
          rw [losymDJ] at hjj
          exact Finset.mem_product.mp hjj
        have h1 : jj.1.1.1 ∈ diffFreqs ρ l₁ ×ˢ diffFreqs ρ l₂ := by
          rw [losymIdx] at hmem
          exact (Finset.mem_product.mp (Finset.mem_product.mp hmem.1).1).1
        have h2 : jj.1.1.1.1 ∈ diffFreqs ρ l₁ ∧ jj.1.1.1.2 ∈ diffFreqs ρ l₂ :=
          Finset.mem_product.mp h1
        refine le_trans (Finset.single_le_sum (f := fun γ₂ => ((perQ jj.1.1.1.1 γ₂ : ℕ) : ℝ) ^ 2)
            (fun γ₂ hγ₂ => by positivity) h2.2) ?_
        exact Finset.single_le_sum
          (f := fun γ₁ => ∑ γ₂ ∈ diffFreqs ρ l₂, ((perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2)
          (fun γ₁ hγ₁ => Finset.sum_nonneg (fun γ₂ hγ₂ => by positivity)) h2.1
      refine hmid.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact le_of_eq (by ring)
    calc (∑ jj ∈ losymDJ ρ l₁ l₂ j₁ j₂, losymDKer2 P N j₁ j₂ k₁ k₂ C_M jj.1)
          * ((2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ))
        ≤ (((losymDJ ρ l₁ l₂ j₁ j₂).card : ℝ)
            * (16 * (C_M * (∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂,
                  ((perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2)
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
                * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1)))))
          * ((2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ)) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = ((losymDJ ρ l₁ l₂ j₁ j₂).card : ℝ)
            * (∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂, ((perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2)
            * (16 * C_M * (2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ))
            * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1)) := by ring


end

lemma loBumpBounds (P : Polynomial ℤ) :
    ∃ Cφ Cψ : ℝ, 0 < Cφ ∧ 0 < Cψ ∧
      (∀ (N k m : ℕ), m ≤ 2 →
        (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (Work.KMTAreas.A7.varphiN N k) ξ‖)
          ≤ ENNReal.ofReal (Cφ * (Work.KMTPlan.A6.lothN N / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1))) ∧
      (∀ (N k m : ℕ), m ≤ 2 →
        (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (Work.KMTAreas.A7.varphitildeN P.natDegree N k) ξ‖)
          ≤ ENNReal.ofReal (Cψ * (Work.KMTPlan.A6.lopsN P.natDegree N k) ^ ((m : ℝ) - 1))) := by
  simpa only [Work.KMTPlan.A6.lothN, Work.KMTPlan.A6.lopsN] using Work.KMTAreas.A7.LoBumpBounds P

/-- **The `ξ`-derivative bound for the symbol difference `Work.KMTPlan.A6.symD` at arithmetic heights `(0,0)`.**
This is the `l₁ = l₂ = 0` form of `Work.KMTPlan.A6.symD_deriv_bound`: at height `0` the arithmetic
frequency set is the singleton `{0}`, so `perQ 0 0 = 1` and no `2^{ρl}` factor occurs. -/
theorem loSymD_deriv_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ K D : ℝ, 0 ≤ K ∧ 0 < D ∧
      ∀ (ρ : ℝ) (N k₁ k₂ : ℕ), 0 < ρ → ρ ≤ 1 → 2 ≤ N →
        k₁ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat →
        k₂ + 3 ≤ (Work.Analysis.EndVar.logN N).toNat →
        ∀ (j₁ j₂ : ℕ), j₁ ≤ 2 → j₂ ≤ 2 →
          (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
              ENNReal.ofReal ‖Work.KMTPlan.A6.dp j₁ j₂ (Work.KMTPlan.A6.symD ρ P N 0 0 k₁ k₂) x y‖)
            ≤ ENNReal.ofReal (D * (2 : ℝ) ^ (K * (((max k₁ k₂ : ℕ) : ℝ)))
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
                * (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1))) := by
  obtain ⟨CM, hCMpos, hM0⟩ := Work.A7.ModelApproxCore_M0_deriv_bound P
  obtain ⟨Cφ, Cψ, hCφpos, hCψpos, hφb, hψb⟩ := loBumpBounds P
  refine ⟨(P.natDegree : ℝ) + 1, 1089 * 16 * CM * Cφ * Cψ * 2 ^ (1 + P.natDegree),
    by positivity, by positivity, ?_⟩
  intro ρ N k₁ k₂ hρ hρ1 hN hk₁ hk₂ j₁ j₂ hj₁ hj₂
  have hCφ : (0 : ℝ) ≤ Cφ := hCφpos.le
  have hCψ : (0 : ℝ) ≤ Cψ := hCψpos.le
  have hCM : (0 : ℝ) ≤ CM := hCMpos.le
  -- the level-`0` arithmetic: `diffFreqs ρ 0 = {0}`, `perQ 0 0 = 1`, and the cardinality bound
  have hdf0 : Work.KMTAreas.A7.diffFreqs ρ 0 = {0} := by
    rw [Work.KMTAreas.A7.diffFreqs, if_pos rfl]
    exact Work.KMTAreas.A7.iwArithFreqs_zero ρ
  have hcard : ((Work.KMTPlan.A6.losymDJ ρ 0 0 j₁ j₂).card : ℝ) ≤ 1089 := by
    have h := Work.KMTPlan.A6.locard_symDJ_le ρ 0 0 j₁ j₂ hj₁ hj₂
    rw [hdf0] at h
    simpa using h
  have hsum1 : (∑ γ₁ ∈ Work.KMTAreas.A7.diffFreqs ρ 0,
      ∑ γ₂ ∈ Work.KMTAreas.A7.diffFreqs ρ 0,
        ((Work.KMTPlan.A6.perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2) = 1 := by
    rw [hdf0]
    simp [Work.KMTPlan.A6.perQ]
  -- the `2`-power transfer: `2^{1+d+k₁+d k₂} ≤ 2^{1+d} · 2^{(1+d)L}`
  have hp2 : (2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂)
      ≤ 2 ^ (1 + P.natDegree) * 2 ^ ((1 + P.natDegree) * (max k₁ k₂)) := by
    have hk : 1 + P.natDegree + k₁ + P.natDegree * k₂
        ≤ (1 + P.natDegree) + (1 + P.natDegree) * (max k₁ k₂) := by
      have h1 : k₁ ≤ max k₁ k₂ := Nat.le_max_left _ _
      have h2 : k₂ ≤ max k₁ k₂ := Nat.le_max_right _ _
      nlinarith
    calc (2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂)
        ≤ 2 ^ ((1 + P.natDegree) + (1 + P.natDegree) * (max k₁ k₂)) :=
          pow_le_pow_right₀ (by norm_num) hk
      _ = 2 ^ (1 + P.natDegree) * 2 ^ ((1 + P.natDegree) * (max k₁ k₂)) := by rw [pow_add]
  have hKL : (2 : ℝ) ^ ((1 + P.natDegree) * (max k₁ k₂))
      = (2 : ℝ) ^ (((P.natDegree : ℝ) + 1) * ((max k₁ k₂ : ℕ) : ℝ)) := by
    rw [show ((P.natDegree : ℝ) + 1) * ((max k₁ k₂ : ℕ) : ℝ)
          = (((1 + P.natDegree) * (max k₁ k₂) : ℕ) : ℝ) by push_cast; ring]
    exact (Real.rpow_natCast (2 : ℝ) ((1 + P.natDegree) * (max k₁ k₂))).symm
  have hY : 16 * CM * (2 ^ (1 + P.natDegree) * 2 ^ ((1 + P.natDegree) * (max k₁ k₂)))
        * (Cφ * Cψ)
      = 16 * CM * 2 ^ (1 + P.natDegree)
        * (2 : ℝ) ^ (((P.natDegree : ℝ) + 1) * ((max k₁ k₂ : ℕ) : ℝ)) * (Cφ * Cψ) := by
    rw [hKL]; ring
  have hbase : (0 : ℝ) ≤ 1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) := by positivity
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (((j₁ : ℤ) - 2) + (P.natDegree : ℤ) * ((j₂ : ℤ) - 1)) :=
    zpow_nonneg (by positivity) _
  have hX : 16 * CM * (2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ)
      ≤ 16 * CM * (2 ^ (1 + P.natDegree) * 2 ^ ((1 + P.natDegree) * (max k₁ k₂)))
        * (Cφ * Cψ) := by
    refine mul_le_mul_of_nonneg_right ?_ (show (0 : ℝ) ≤ Cφ * Cψ by positivity)
    exact mul_le_mul_of_nonneg_left hp2 (by positivity)
  refine (losymD_dp_lintegral_le ρ P N 0 0 k₁ k₂ hd hN hk₁ hk₂ j₁ j₂ hj₁ hj₂ hCM hCφ hCψ
    hM0 hφb hψb).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hsum1, mul_one]
  have h1 : ((Work.KMTPlan.A6.losymDJ ρ 0 0 j₁ j₂).card : ℝ)
        * (16 * CM * (2 : ℝ) ^ (1 + P.natDegree + k₁ + P.natDegree * k₂) * (Cφ * Cψ))
      ≤ 1089 * (16 * CM * (2 ^ (1 + P.natDegree) * 2 ^ ((1 + P.natDegree) * (max k₁ k₂)))
          * (Cφ * Cψ)) :=
    mul_le_mul hcard hX (by positivity) (by positivity)
  have h2 := mul_le_mul_of_nonneg_right h1 hbase
  have h3 := mul_le_mul_of_nonneg_right h2 h0
  refine h3.trans (le_of_eq ?_)
  rw [hY]
  ring


end Work.KMTPlan.A6
