import Mathlib
import Submission.Work.ZeroDensity.Zeta.sinTailAux
import Submission.Work.ZeroDensity.Ingham.AfeSelf.oscillatoryIoiBound

namespace Work.ZeroDensity.Zeta.SinSelf

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-! ### Derivative and real-arithmetic helpers -/

lemma hasDerivAt_phaseL (t : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun u : ℝ => u - t * Real.log u) (1 - t / v) v := by
  have h := (hasDerivAt_id v).sub ((Real.hasDerivAt_log hv.ne').const_mul t)
  have he : (1 : ℝ) - t * v⁻¹ = 1 - t / v := by rw [div_eq_mul_inv]
  rwa [he] at h

lemma hasDerivAt_phaseDerivL (t : ℝ) {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun u : ℝ => 1 - t / u) (t / v ^ 2) v := by
  have h1 : HasDerivAt (fun u : ℝ => t * u⁻¹) (t * (-(v ^ 2)⁻¹)) v :=
    (hasDerivAt_inv hv).const_mul t
  have h2 : HasDerivAt (fun u : ℝ => 1 - t * u⁻¹) (0 - t * (-(v ^ 2)⁻¹)) v :=
    (hasDerivAt_const v (1 : ℝ)).sub h1
  have he : (0 : ℝ) - t * (-(v ^ 2)⁻¹) = t / v ^ 2 := by ring
  have hfun : (fun u : ℝ => 1 - t * u⁻¹) = fun u : ℝ => 1 - t / u := by
    funext u; rw [div_eq_mul_inv]
  rw [he, hfun] at h2
  exact h2

lemma hasDerivAt_wneg {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (fun u : ℝ => u ^ (-(1/2) : ℝ)) (-(1/2) * v ^ (-(3/2) : ℝ)) v := by
  have h := Real.hasDerivAt_rpow_const (x := v) (p := -(1/2)) (Or.inl hv)
  have he : (-(1/2) : ℝ) - 1 = -(3/2) := by norm_num
  rwa [he] at h

lemma rpow_neg_half_le_one {x : ℝ} (hx : 1 ≤ x) : x ^ (-(1/2) : ℝ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)

lemma rpow_neg_half_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-(1/2) : ℝ) ≤ a ^ (-(1/2) : ℝ) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : a ^ (1/2 : ℝ) ≤ b ^ (1/2 : ℝ) := Real.rpow_le_rpow ha.le hab (by norm_num)
  have e1 : a ^ (-(1/2) : ℝ) = (a ^ (1/2 : ℝ))⁻¹ := by
    rw [show (-(1/2) : ℝ) = -(1/2) by ring, Real.rpow_neg ha.le]
  have e2 : b ^ (-(1/2) : ℝ) = (b ^ (1/2 : ℝ))⁻¹ := by
    rw [show (-(1/2) : ℝ) = -(1/2) by ring, Real.rpow_neg hb.le]
  rw [e1, e2]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hb (1/2)) (Real.rpow_pos_of_pos ha (1/2))).mpr h1

lemma sqrt_le_half {t : ℝ} (ht : 4 ≤ t) : Real.sqrt t ≤ t / 2 := by
  have ht0 : 0 < t := by linarith
  calc Real.sqrt t ≤ Real.sqrt ((t / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = |t / 2| := Real.sqrt_sq_eq_abs (t / 2)
    _ = t / 2 := abs_of_nonneg (by linarith)

lemma sqrt_le_self {t : ℝ} (ht : 1 ≤ t) : Real.sqrt t ≤ t := by
  have ht0 : 0 < t := by linarith
  calc Real.sqrt t ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = |t| := Real.sqrt_sq_eq_abs t
    _ = t := abs_of_nonneg ht0.le

lemma inv_sqrt_mul_sqrt_le {c t : ℝ} (hc : 0 < c) (hle : Real.sqrt t ≤ 2 * Real.sqrt c) :
    (Real.sqrt c)⁻¹ * Real.sqrt t ≤ 2 := by
  rw [inv_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.mpr hc)]
  exact hle

/-! ### The oscillatory bound for one piece -/

lemma oscPiece {t μ : ℝ} (hμ : 0 < μ) {c d : ℝ} (hcd : c ≤ d) (hc : 1 ≤ c) (ht : 0 ≤ t)
    (hμmem : ∀ x ∈ Set.Icc c d, μ ≤ |1 - t / x|) :
    ‖∫ v in c..d, ((v ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((v - t * Real.log v : ℝ) : ℂ))‖ ≤
      4 * (c ^ (-(1/2) : ℝ)) / μ := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hp1 : ∀ x ∈ Set.Icc c d, (0 : ℝ) < x := fun x hx => lt_of_lt_of_le hc0 hx.1
  refine Work.ZeroDensity.Ingham.AfeSelf.oscillatoryIocBound
    (φ := fun v : ℝ => v - t * Real.log v)
    (ψ := fun v : ℝ => 1 - t / v) (χ := fun v : ℝ => t / v ^ 2)
    (w := fun v : ℝ => v ^ (-(1/2) : ℝ))
    (w' := fun v : ℝ => (-(1/2)) * v ^ (-(3/2) : ℝ))
    (a := c) (b := d) (μ := μ) hcd hμ ?_ ?_ ?_ ?_ hμmem ?_ ?_ ?_ ?_
  · intro x hx; exact hasDerivAt_phaseL t (hp1 x hx)
  · intro x hx; exact hasDerivAt_phaseDerivL t (ne_of_gt (hp1 x hx))
  · refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
    intro x hx; exact pow_ne_zero 2 (ne_of_gt (hp1 x hx))
  · intro x hx; exact div_nonneg ht (sq_nonneg x)
  · intro x hx; exact hasDerivAt_wneg (ne_of_gt (hp1 x hx))
  · refine ContinuousOn.mul continuousOn_const ?_
    exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hp1 x hx)))
  · intro x hx; exact Real.rpow_nonneg (le_of_lt (hp1 x hx)) _
  · intro x hx
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt (hp1 x hx)) _)

lemma oscPieceNeg {t : ℝ} (ht : 0 ≤ t) {c d : ℝ} (hcd : c ≤ d) (hc : 1 ≤ c) :
    ‖∫ v in c..d, ((v ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((-v - t * Real.log v) : ℝ) : ℂ))‖ ≤
      4 * (c ^ (-(1/2) : ℝ)) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hp1 : ∀ x ∈ Set.Icc c d, (0 : ℝ) < x := fun x hx => lt_of_lt_of_le hc0 hx.1
  have hφ : ∀ x ∈ Set.Icc c d, HasDerivAt (fun v : ℝ => -v - t * Real.log v) (-1 - t / x) x := by
    intro x hx
    have hx0 : 0 < x := hp1 x hx
    have h1 : HasDerivAt (fun u : ℝ => t * Real.log u) (t * x⁻¹) x :=
      (Real.hasDerivAt_log hx0.ne').const_mul t
    have h2 : HasDerivAt (fun u : ℝ => -u - t * Real.log u) (-1 - t * x⁻¹) x :=
      (hasDerivAt_id x).neg.sub h1
    have he : -1 - t * x⁻¹ = -1 - t / x := by rw [div_eq_mul_inv]
    rwa [he] at h2
  have hψ : ∀ x ∈ Set.Icc c d, HasDerivAt (fun v : ℝ => -1 - t / v) (t / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hp1 x hx)
    have h1 : HasDerivAt (fun u : ℝ => t * u⁻¹) (t * (-(x ^ 2)⁻¹)) x :=
      (hasDerivAt_inv hx0).const_mul t
    have h2 : HasDerivAt (fun u : ℝ => -1 - t * u⁻¹) (0 - t * (-(x ^ 2)⁻¹)) x :=
      (hasDerivAt_const x (-1 : ℝ)).sub h1
    have he : (0 : ℝ) - t * (-(x ^ 2)⁻¹) = t / x ^ 2 := by ring
    have hfun : (fun u : ℝ => -1 - t * u⁻¹) = fun u : ℝ => -1 - t / u := by
      funext u; rw [div_eq_mul_inv]
    rw [he, hfun] at h2
    exact h2
  have hχc : ContinuousOn (fun v : ℝ => t / v ^ 2) (Set.Icc c d) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
    intro x hx; exact pow_ne_zero 2 (ne_of_gt (hp1 x hx))
  have hχ : ∀ x ∈ Set.Icc c d, 0 ≤ t / x ^ 2 := fun x _ => div_nonneg ht (sq_nonneg x)
  have hψμ : ∀ x ∈ Set.Icc c d, (1 : ℝ) ≤ |-1 - t / x| := by
    intro x hx
    have hx0 : 0 < x := hp1 x hx
    have htx : 0 ≤ t / x := div_nonneg ht hx0.le
    have hle : -1 - t / x ≤ 0 := by linarith
    rw [abs_of_nonpos hle]; linarith
  have hw : ∀ x ∈ Set.Icc c d, HasDerivAt (fun v : ℝ => v ^ (-(1/2) : ℝ))
      ((-(1/2)) * x ^ (-(3/2) : ℝ)) x := fun x hx => hasDerivAt_wneg (ne_of_gt (hp1 x hx))
  have hw'c : ContinuousOn (fun v : ℝ => (-(1/2)) * v ^ (-(3/2) : ℝ)) (Set.Icc c d) := by
    refine ContinuousOn.mul continuousOn_const ?_
    exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hp1 x hx)))
  have hw0 : ∀ x ∈ Set.Icc c d, 0 ≤ x ^ (-(1/2) : ℝ) :=
    fun x hx => Real.rpow_nonneg (le_of_lt (hp1 x hx)) _
  have hw' : ∀ x ∈ Set.Icc c d, (-(1/2)) * x ^ (-(3/2) : ℝ) ≤ 0 :=
    fun x hx => mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (Real.rpow_nonneg (le_of_lt (hp1 x hx)) _)
  have hosc := Work.ZeroDensity.Ingham.AfeSelf.oscillatoryIocBound
    (φ := fun v : ℝ => -v - t * Real.log v)
    (ψ := fun v : ℝ => -1 - t / v) (χ := fun v : ℝ => t / v ^ 2)
    (w := fun v : ℝ => v ^ (-(1/2) : ℝ))
    (w' := fun v : ℝ => (-(1/2)) * v ^ (-(3/2) : ℝ))
    (a := c) (b := d) (μ := 1) hcd one_pos hφ hψ hχc hχ hψμ hw hw'c hw0 hw'
  exact hosc.trans (by have := rpow_neg_half_le_one hc; linarith)

/-! ### Continuity of the concrete integrand -/

lemma continuousOn_rpow_neg_half :
    ContinuousOn (fun v : ℝ => v ^ (-(1/2) : ℝ)) (Set.Ioi 0) := by
  refine ContinuousOn.congr (f := fun v : ℝ => Real.exp (Real.log v * (-(1/2)))) ?_ ?_
  · have hlog : ContinuousOn Real.log (Set.Ioi 0) :=
      Real.continuousOn_log.mono (fun x hx => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact ne_of_gt hx)
    exact Real.continuous_exp.comp_continuousOn (hlog.mul_const (-(1/2)))
  · intro x hx
    exact Real.rpow_def_of_pos hx (-(1/2))

lemma continuousOn_fresnelI (t : ℝ) {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun v : ℝ => ((v ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((v - t * Real.log v : ℝ) : ℂ))) (Set.Ici A) := by
  have hlog : ContinuousOn Real.log (Set.Ici A) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le hA hx))
  have hphase : ContinuousOn (fun v : ℝ => v - t * Real.log v) (Set.Ici A) :=
    continuousOn_id.sub (hlog.const_mul t)
  have hexp : ContinuousOn
      (fun v : ℝ => Complex.exp (Complex.I * ((v - t * Real.log v : ℝ) : ℂ))) (Set.Ici A) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hphase))
  have hrpow : ContinuousOn (fun v : ℝ => ((v ^ (-(1/2) : ℝ) : ℝ) : ℂ)) (Set.Ici A) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_rpow_neg_half.mono (fun x hx => lt_of_lt_of_le hA hx))
  exact hrpow.mul hexp

/-! ### Rewriting the complex-power integrands -/

lemma rewrite_expI {t A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∫ v in A..B, (v : ℂ) ^ (SinAux.ct t) * Complex.exp (Complex.I * (v : ℂ)))
      = ∫ v in A..B, ((v ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((v - t * Real.log v : ℝ) : ℂ)) := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hAB] at hx
  have hx0 : 0 < x := lt_of_lt_of_le hA0 hx.1
  show (x : ℂ) ^ (-(1/2 : ℂ) - (t : ℂ) * Complex.I) * Complex.exp (Complex.I * (x : ℂ))
      = ((x ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((x - t * Real.log x : ℝ) : ℂ))
  exact (SinAux.cpow_exp_I_phase t x hx0).trans (by rfl)

lemma rewrite_expNegI {t A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∫ v in A..B, (v : ℂ) ^ (SinAux.ct t) * Complex.exp (-(Complex.I * (v : ℂ))))
      = ∫ v in A..B, ((v ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-v - t * Real.log v) : ℝ) : ℂ)) := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hAB] at hx
  have hx0 : 0 < x := lt_of_lt_of_le hA0 hx.1
  show (x : ℂ) ^ (-(1/2 : ℂ) - (t : ℂ) * Complex.I) * Complex.exp (-(Complex.I * (x : ℂ)))
      = ((x ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((-x - t * Real.log x) : ℝ) : ℂ))
  exact (SinAux.cpow_exp_negI_phase t x hx0).trans (by rfl)

theorem expNegI_boundSelf : ∀ t : ℝ, 0 ≤ t → ∀ A B : ℝ, 1 ≤ A → A ≤ B →
    ‖∫ v in A..B, (v : ℂ) ^ (SinAux.ct t) * Complex.exp (-(Complex.I * (v : ℂ)))‖ ≤ 4 := by
  intro t ht A B hA hAB
  rw [rewrite_expNegI hA hAB]
  exact (oscPieceNeg (t := t) ht hAB hA).trans (by have := rpow_neg_half_le_one hA; linarith)

theorem expI_boundSelf : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 4 ≤ t → ∀ A B : ℝ, 1 ≤ A → A ≤ B →
    ‖∫ v in A..B, (v : ℂ) ^ (SinAux.ct t) * Complex.exp (Complex.I * (v : ℂ))‖ ≤ C := by
  refine ⟨30, by norm_num, ?_⟩
  intro t ht A B hA hAB
  have ht0 : 0 < t := by linarith
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hhalf : Real.sqrt t ≤ t / 2 := sqrt_le_half ht
  have hhalf' : t / 2 ≤ t - Real.sqrt t := by linarith [Real.sqrt_nonneg t]
  have hmid : t - Real.sqrt t ≤ t + Real.sqrt t := by linarith [Real.sqrt_nonneg t]
  have hpos_mid : 0 < t - Real.sqrt t := by linarith [hhalf]
  rw [rewrite_expI hA hAB]
  set f : ℝ → ℂ := fun v => ((v ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((v - t * Real.log v : ℝ) : ℂ)) with hf
  have hfcontA : ContinuousOn f (Set.Ici A) := continuousOn_fresnelI t hA0
  have hF : ∀ x y : ℝ, A ≤ x → A ≤ y → IntervalIntegrable f volume x y := by
    intro x y hx hy
    refine (hfcontA.mono ?_).intervalIntegrable
    intro z hz
    rcases Set.mem_uIcc.mp hz with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact le_trans (le_min hx hy) (le_trans (min_le_left x y) h1)
    · exact le_trans (le_min hx hy) (le_trans (min_le_right x y) h1)
  have hadd : ∀ a b c : ℝ, A ≤ a → a ≤ b → b ≤ c →
      ∫ v in a..c, f v = (∫ v in a..b, f v) + ∫ v in b..c, f v := by
    intro a b c ha hab hbc
    have hab' : A ≤ b := le_trans ha hab
    have hac' : A ≤ c := le_trans hab' hbc
    exact (intervalIntegral.integral_add_adjacent_intervals (hF a b ha hab')
      (hF b c hab' hac')).symm
  have P1 : ∀ {c d : ℝ}, 1 ≤ c → c ≤ d → d ≤ t / 2 → ‖∫ v in c..d, f v‖ ≤ 4 := by
    intro c d hc hcd hd
    have hmem : ∀ x ∈ Set.Icc c d, (1 : ℝ) ≤ |1 - t / x| := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hc) hx.1
      have hxt : x ≤ t / 2 := le_trans hx.2 hd
      have h2 : 2 ≤ t / x := by rw [le_div_iff₀ hx0]; linarith
      have habs : |1 - t / x| = t / x - 1 := by
        rw [abs_of_nonpos (by linarith : 1 - t / x ≤ 0)]; ring
      rw [habs]; linarith
    have hosc := oscPiece (t := t) (μ := 1) one_pos hcd hc ht0.le hmem
    exact hosc.trans (by have := rpow_neg_half_le_one hc; linarith)
  have P2 : ∀ {c d : ℝ}, t / 2 ≤ c → c ≤ d → d ≤ t - Real.sqrt t → ‖∫ v in c..d, f v‖ ≤ 8 := by
    intro c d hc hcd hd
    have hcpos : 0 < c := by linarith
    have hmem : ∀ x ∈ Set.Icc c d, (Real.sqrt t)⁻¹ ≤ |1 - t / x| := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hcpos hx.1
      have hxt : x ≤ t := le_trans (le_trans hx.2 hd) (by linarith [Real.sqrt_nonneg t])
      have habs : |1 - t / x| = t / x - 1 := by
        rw [abs_of_nonpos (by
          have : 1 ≤ t / x := (le_div_iff₀ hx0).mpr (by linarith)
          linarith)]; ring
      rw [habs]
      have hkey : (Real.sqrt t)⁻¹ ≤ t / x - 1 := by
        rw [div_sub_one (ne_of_gt hx0), le_div_iff₀ hx0, inv_mul_eq_div]
        have h1 : x / Real.sqrt t ≤ Real.sqrt t := by
          rw [div_le_iff₀ (Real.sqrt_pos.mpr ht0)]
          nlinarith [Real.sq_sqrt ht0.le]
        have h2 : Real.sqrt t ≤ t - x := by linarith [le_trans hx.2 hd]
        linarith
      exact hkey
    have hosc := oscPiece (t := t) (μ := (Real.sqrt t)⁻¹) (by positivity) hcd (by linarith) ht0.le hmem
    rw [div_inv_eq_mul] at hosc
    refine hosc.trans ?_
    have hsqrt : Real.sqrt t ≤ 2 * Real.sqrt c := by
      have hsq1 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0.le
      have hsq2 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hcpos.le
      nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg c, hc, hsq1, hsq2]
    have he : c ^ (-(1/2) : ℝ) = (Real.sqrt c)⁻¹ := by
      rw [show (-(1/2) : ℝ) = -(1/2) by ring, Real.rpow_neg hcpos.le, ← Real.sqrt_eq_rpow]
    rw [he, show 4 * (Real.sqrt c)⁻¹ * Real.sqrt t = 4 * ((Real.sqrt c)⁻¹ * Real.sqrt t) by ring]
    have := inv_sqrt_mul_sqrt_le hcpos hsqrt
    linarith
  have P3 : ∀ {c d : ℝ}, t - Real.sqrt t ≤ c → c ≤ d → d ≤ t + Real.sqrt t →
      ‖∫ v in c..d, f v‖ ≤ 4 := by
    intro c d hc hcd hd
    have hle : ∀ᵐ x ∂volume, x ∈ Set.Ioc c d → ‖f x‖ ≤ (t - Real.sqrt t) ^ (-(1/2) : ℝ) := by
      filter_upwards with x hx
      have hxge : t - Real.sqrt t ≤ x := le_trans hc (le_of_lt hx.1)
      have hx0 : 0 < x := lt_of_lt_of_le hpos_mid hxge
      rw [hf, norm_mul, SinAux.norm_ofReal_complex, SinAux.norm_exp_I_mul, mul_one]
      rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact rpow_neg_half_anti hpos_mid hxge
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := c) (b := d)
      (f := f) (g := fun _ : ℝ => (t - Real.sqrt t) ^ (-(1/2) : ℝ)) hcd hle intervalIntegrable_const
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    refine h.trans ?_
    have hdc : d - c ≤ 2 * Real.sqrt t := by linarith [Real.sqrt_nonneg t]
    have hM2 : (t - Real.sqrt t) ^ (-(1/2) : ℝ) * (2 * Real.sqrt t) ≤ 4 := by
      have he : (t - Real.sqrt t) ^ (-(1/2) : ℝ) = (Real.sqrt (t - Real.sqrt t))⁻¹ := by
        rw [show (-(1/2) : ℝ) = -(1/2) by ring, Real.rpow_neg hpos_mid.le, ← Real.sqrt_eq_rpow]
      rw [he]
      have hle2 : Real.sqrt t ≤ 2 * Real.sqrt (t - Real.sqrt t) := by
        have hsq1 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0.le
        have hsq2 : (Real.sqrt (t - Real.sqrt t)) ^ 2 = t - Real.sqrt t := Real.sq_sqrt hpos_mid.le
        nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg (t - Real.sqrt t), hhalf]
      rw [inv_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.mpr hpos_mid)]
      linarith
    have hnn : 0 ≤ (t - Real.sqrt t) ^ (-(1/2) : ℝ) := Real.rpow_nonneg hpos_mid.le _
    nlinarith [mul_le_mul_of_nonneg_left hdc hnn]
  have P4 : ∀ {c d : ℝ}, t + Real.sqrt t ≤ c → c ≤ d → ‖∫ v in c..d, f v‖ ≤ 8 := by
    intro c d hc hcd
    have hcpos : 0 < c := by linarith [sqrt_le_self (by linarith : (1:ℝ) ≤ t)]
    have hmem : ∀ x ∈ Set.Icc c d, (2 * Real.sqrt t)⁻¹ ≤ |1 - t / x| := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hcpos hx.1
      have hxt : t ≤ x := le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg t)) (le_trans hc hx.1)
      have hsubn : 0 ≤ 1 - t / x := by
        rw [sub_nonneg, div_le_one hx0]; exact hxt
      have habs : |1 - t / x| = 1 - t / x := abs_of_nonneg hsubn
      rw [habs]
      have hden : 0 < t + Real.sqrt t := by positivity
      have hstep1 : t / x ≤ t / (t + Real.sqrt t) :=
        div_le_div_of_nonneg_left ht0.le hden (le_trans hc hx.1)
      have hstep2 : (2 * Real.sqrt t)⁻¹ ≤ 1 - t / (t + Real.sqrt t) := by
        rw [inv_eq_one_div]
        have he : 1 - t / (t + Real.sqrt t) = Real.sqrt t / (t + Real.sqrt t) := by
          field_simp; ring
        rw [he, le_div_iff₀ hden, div_mul_eq_mul_div, one_mul,
          div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt t)]
        nlinarith [Real.sq_sqrt ht0.le, sqrt_le_self (by linarith : (1:ℝ) ≤ t)]
      linarith
    have hosc := oscPiece (t := t) (μ := (2 * Real.sqrt t)⁻¹) (by positivity) hcd (by linarith) ht0.le hmem
    rw [div_inv_eq_mul] at hosc
    refine hosc.trans ?_
    have hle : Real.sqrt t ≤ Real.sqrt c :=
      Real.sqrt_le_sqrt (le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg t)) hc)
    have he : c ^ (-(1/2) : ℝ) = (Real.sqrt c)⁻¹ := by
      rw [show (-(1/2) : ℝ) = -(1/2) by ring, Real.rpow_neg hcpos.le, ← Real.sqrt_eq_rpow]
    rw [he, show 4 * (Real.sqrt c)⁻¹ * (2 * Real.sqrt t)
      = 8 * ((Real.sqrt c)⁻¹ * Real.sqrt t) by ring]
    have h2 : (Real.sqrt c)⁻¹ * Real.sqrt t ≤ 1 := by
      rw [inv_mul_eq_div, div_le_one (Real.sqrt_pos.mpr hcpos)]
      exact hle
    linarith
  rcases le_total B (t / 2) with hB1 | hB1
  · exact le_trans (P1 hA hAB hB1) (by norm_num)
  · rcases le_total A (t / 2) with hA1 | hA1
    · have hs1 := hadd A (t / 2) B le_rfl hA1 hB1
      rw [hs1]
      have h1 : ‖∫ v in A..t / 2, f v‖ ≤ 4 := P1 hA hA1 le_rfl
      rcases le_total B (t - Real.sqrt t) with hB2 | hB2
      · have h2 : ‖∫ v in t / 2..B, f v‖ ≤ 8 := P2 le_rfl hB1 hB2
        exact le_trans ((norm_add_le _ _).trans (add_le_add h1 h2)) (by norm_num)
      · rcases le_total B (t + Real.sqrt t) with hB3 | hB3
        · have hs2 := hadd (t / 2) (t - Real.sqrt t) B hA1 hhalf' hB2
          rw [hs2]
          have h2 : ‖∫ v in t / 2..t - Real.sqrt t, f v‖ ≤ 8 := P2 le_rfl hhalf' le_rfl
          have h3 : ‖∫ v in (t - Real.sqrt t)..B, f v‖ ≤ 4 := P3 le_rfl hB2 hB3
          have hb : ‖(∫ v in t / 2..t - Real.sqrt t, f v)
              + (∫ v in (t - Real.sqrt t)..B, f v)‖ ≤ 8 + 4 :=
            (norm_add_le _ _).trans (add_le_add h2 h3)
          exact le_trans ((norm_add_le _ _).trans (add_le_add h1 hb)) (by norm_num)
        · have hs2 := hadd (t / 2) (t - Real.sqrt t) B hA1 hhalf' hB2
          rw [hs2]
          have hs3 := hadd (t - Real.sqrt t) (t + Real.sqrt t) B (le_trans hA1 hhalf') hmid hB3
          rw [hs3]
          have h2 : ‖∫ v in t / 2..t - Real.sqrt t, f v‖ ≤ 8 := P2 le_rfl hhalf' le_rfl
          have h3 : ‖∫ v in (t - Real.sqrt t)..(t + Real.sqrt t), f v‖ ≤ 4 := P3 le_rfl hmid le_rfl
          have h4 : ‖∫ v in (t + Real.sqrt t)..B, f v‖ ≤ 8 := P4 le_rfl hB3
          have hb : ‖(∫ v in (t - Real.sqrt t)..(t + Real.sqrt t), f v)
              + (∫ v in (t + Real.sqrt t)..B, f v)‖ ≤ 4 + 8 :=
            (norm_add_le _ _).trans (add_le_add h3 h4)
          have hc : ‖(∫ v in t / 2..t - Real.sqrt t, f v)
              + ((∫ v in (t - Real.sqrt t)..(t + Real.sqrt t), f v)
                + (∫ v in (t + Real.sqrt t)..B, f v))‖ ≤ 8 + (4 + 8) :=
            (norm_add_le _ _).trans (add_le_add h2 hb)
          exact le_trans ((norm_add_le _ _).trans (add_le_add h1 hc)) (by norm_num)
    · rcases le_total B (t - Real.sqrt t) with hB2 | hB2
      · exact le_trans (P2 hA1 hAB hB2) (by norm_num)
      · rcases le_total A (t - Real.sqrt t) with hA2 | hA2
        · have hs1 := hadd A (t - Real.sqrt t) B le_rfl hA2 hB2
          rw [hs1]
          have h1 : ‖∫ v in A..t - Real.sqrt t, f v‖ ≤ 8 := P2 hA1 hA2 le_rfl
          rcases le_total B (t + Real.sqrt t) with hB3 | hB3
          · have h2 : ‖∫ v in (t - Real.sqrt t)..B, f v‖ ≤ 4 := P3 le_rfl hB2 hB3
            exact le_trans ((norm_add_le _ _).trans (add_le_add h1 h2)) (by norm_num)
          · have hs2 := hadd (t - Real.sqrt t) (t + Real.sqrt t) B hA2 hmid hB3
            rw [hs2]
            have h2 : ‖∫ v in (t - Real.sqrt t)..(t + Real.sqrt t), f v‖ ≤ 4 := P3 le_rfl hmid le_rfl
            have h3 : ‖∫ v in (t + Real.sqrt t)..B, f v‖ ≤ 8 := P4 le_rfl hB3
            have hb : ‖(∫ v in (t - Real.sqrt t)..(t + Real.sqrt t), f v)
                + (∫ v in (t + Real.sqrt t)..B, f v)‖ ≤ 4 + 8 :=
              (norm_add_le _ _).trans (add_le_add h2 h3)
            exact le_trans ((norm_add_le _ _).trans (add_le_add h1 hb)) (by norm_num)
        · rcases le_total B (t + Real.sqrt t) with hB3 | hB3
          · exact le_trans (P3 hA2 hAB hB3) (by norm_num)
          · rcases le_total A (t + Real.sqrt t) with hA3 | hA3
            · have hs1 := hadd A (t + Real.sqrt t) B le_rfl hA3 hB3
              rw [hs1]
              have h1 : ‖∫ v in A..t + Real.sqrt t, f v‖ ≤ 4 := P3 hA2 hA3 le_rfl
              have h2 : ‖∫ v in (t + Real.sqrt t)..B, f v‖ ≤ 8 := P4 le_rfl hB3
              exact le_trans ((norm_add_le _ _).trans (add_le_add h1 h2)) (by norm_num)
            · exact le_trans (P4 hA3 hAB) (by norm_num)

end

end Work.ZeroDensity.Zeta.SinSelf
