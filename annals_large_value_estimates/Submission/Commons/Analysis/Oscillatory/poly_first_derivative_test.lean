import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Polynomial

open MeasureTheory Set
open scoped Real Interval

namespace Commons.Analysis.Oscillatory

noncomputable section





lemma sign_const_of_abs_lower_bound {a b : ℝ} {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Icc a b)) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ t ∈ Set.Icc a b, lam ≤ |g t|) :
    (∀ t ∈ Set.Icc a b, lam ≤ g t) ∨ (∀ t ∈ Set.Icc a b, g t ≤ -lam) := by
  rcases lt_or_ge (g a) 0 with hga | hga
  · right
    intro t ht
    by_contra hcon
    push Not at hcon
    have ht_ne : (lam ≤ |g t|) := h t ht
    have hgt : 0 ≤ g t := by
      rcases lt_or_ge (g t) 0 with hlt0 | hge0
      · rw [abs_of_neg hlt0] at ht_ne; linarith
      · exact hge0
    have hcont' : ContinuousOn g (Set.Icc a t) :=
      hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)
    have h0mem : (0:ℝ) ∈ Set.Icc (g a) (g t) := ⟨le_of_lt hga, hgt⟩
    have h0im : (0:ℝ) ∈ g '' Set.Icc a t := intermediate_value_Icc ht.1 hcont' h0mem
    rcases h0im with ⟨c, hc, hceq⟩
    have hcmem : c ∈ Set.Icc a b := ⟨hc.1, le_trans hc.2 ht.2⟩
    have := h c hcmem
    rw [hceq, abs_zero] at this
    linarith
  · left
    intro t ht
    by_contra hcon
    push Not at hcon
    have ht_ne : (lam ≤ |g t|) := h t ht
    have hgt : g t ≤ -lam := by
      rcases lt_or_ge (g t) 0 with hlt0 | hgt0
      · rw [abs_of_neg hlt0] at ht_ne; linarith
      · rw [abs_of_nonneg hgt0] at ht_ne; linarith
    have hcont' : ContinuousOn g (Set.Icc a t) :=
      hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)
    have h0mem : (0:ℝ) ∈ Set.Icc (g t) (g a) := ⟨by linarith, hga⟩
    have h0im : (0:ℝ) ∈ g '' Set.Icc a t := intermediate_value_Icc' ht.1 hcont' h0mem
    rcases h0im with ⟨c, hc, hceq⟩
    have hcmem : c ∈ Set.Icc a b := ⟨hc.1, le_trans hc.2 ht.2⟩
    have := h c hcmem
    rw [hceq, abs_zero] at this
    linarith

lemma deriv_fun_neg (g : ℝ → ℝ) : deriv (fun x => -g x) = fun x => -deriv g x := by
  funext x
  simp only [deriv]
  rw [fderiv_fun_neg]
  simp

theorem vdc_first_deriv_mono {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hφ : ContDiff ℝ 2 φ)
    (hmono : MonotoneOn (deriv φ) (Set.Icc a b))
    (hbound : ∀ x ∈ Set.Icc a b, lam ≤ |deriv φ x|) :
    ‖∫ t in a..b, Complex.exp (Complex.I * (φ t : ℂ))‖ ≤ 4 / lam := by
  rcases eq_or_lt_of_le hab with hab_eq | hlt
  · subst hab_eq
    simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  have hle : a ≤ b := le_of_lt hlt
  have hderiv_cont : Continuous (deriv φ) := hφ.continuous_deriv (by norm_num)
  have hsgn := sign_const_of_abs_lower_bound hderiv_cont.continuousOn hlam hbound
  have hne : ∀ x ∈ Set.Icc a b, deriv φ x ≠ 0 := by
    intro x hx h0
    have := hbound x hx
    rw [h0, abs_zero] at this
    linarith
  set g : ℝ → ℝ := fun x => (deriv φ x)⁻¹ with hgdef
  have hg_anti : AntitoneOn g (Set.Icc a b) := by
    intro x hx y hy hxy
    have h1 : deriv φ x ≤ deriv φ y := hmono hx hy hxy
    rw [hgdef]
    rcases hsgn with hp | hn
    · exact inv_anti₀ (by linarith [hp x hx]) h1
    · have h2 : -deriv φ y ≤ -deriv φ x := by linarith [h1]
      have h3 : 0 < -deriv φ y := by linarith [hn y hy]
      have h4 := inv_anti₀ h3 h2
      rw [inv_neg, inv_neg] at h4
      linarith
  have hg_bound : ∀ x ∈ Set.Icc a b, |g x| ≤ lam⁻¹ := by
    intro x hx
    rw [hgdef, abs_inv]
    exact inv_anti₀ hlam (hbound x hx)
  have hdφ : Differentiable ℝ (deriv φ) := by
    rw [← iteratedDeriv_one]
    exact hφ.differentiable_iteratedDeriv 1 (by norm_num)
  have hg_diff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ g x := by
    intro x hx
    rw [hgdef]
    exact (hdφ.differentiableAt).inv (hne x hx)
  have hdg_nonpos : ∀ x ∈ Set.Ioo a b, deriv g x ≤ 0 := by
    intro x hx
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
    exact AntitoneOn.derivWithin_nonpos hg_anti
  have hint_deriv_g : IntervalIntegrable (deriv g) volume a b := by
    have hmono_g : MonotoneOn (fun x => -g x) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hle]
      exact hg_anti.neg
    have h := MonotoneOn.intervalIntegrable_deriv hmono_g
    rw [deriv_fun_neg] at h
    have h2 := h.neg
    rw [show (-(fun x => -deriv g x)) = (fun x => deriv g x) from by funext x; simp] at h2
    exact h2
  have hFTC : ∫ x in a..b, deriv g x = g b - g a :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x hx => hg_diff x (by rwa [Set.uIcc_of_le hle] at hx)) hint_deriv_g
  have hInt_g : ∫ x in a..b, |deriv g x| ≤ 2 * lam⁻¹ := by
    have hcong : ∫ x in a..b, |deriv g x| = ∫ x in a..b, (-deriv g x) :=
      intervalIntegral.integral_congr_uIoo (fun x hx => by
        rw [Set.uIoo_of_le hle] at hx
        exact abs_of_nonpos (hdg_nonpos x hx))
    rw [hcong, intervalIntegral.integral_neg, hFTC]
    have h1 : g a ≤ lam⁻¹ := le_trans (le_abs_self _) (hg_bound a ⟨le_rfl, hle⟩)
    have h2 : -g b ≤ lam⁻¹ := le_trans (neg_le_abs _) (hg_bound b ⟨hle, le_rfl⟩)
    linarith
  set v : ℝ → ℂ := fun t => Complex.exp (Complex.I * (φ t : ℂ)) with hvdef
  set u : ℝ → ℂ := fun t => -(Complex.I) * ((g t : ℝ) : ℂ) with hudef
  set u' : ℝ → ℂ := fun t => -(Complex.I) * ((deriv g t : ℝ) : ℂ) with hu'def
  set v' : ℝ → ℂ := fun t => Complex.exp (Complex.I * (φ t : ℂ)) * (Complex.I * ((deriv φ t : ℝ) : ℂ)) with hv'def
  have hu_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hle] at hx
    rw [hu'def]
    have h1 : HasDerivAt (fun t => ((g t : ℝ) : ℂ)) ((deriv g x : ℝ) : ℂ) x :=
      (hg_diff x hx').hasDerivAt.ofReal_comp
    exact h1.const_mul (-(Complex.I))
  have hv_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x := by
    intro x hx
    rw [hvdef, hv'def]
    have h1 : HasDerivAt (fun t => ((φ t : ℝ) : ℂ)) ((deriv φ x : ℝ) : ℂ) x :=
      (hφ.differentiable (by norm_num)).differentiableAt.hasDerivAt.ofReal_comp
    exact (h1.const_mul Complex.I).cexp
  have hu'_int : IntervalIntegrable u' volume a b := by
    rw [hu'def]
    have hcopy : IntervalIntegrable (deriv g) volume a b := hint_deriv_g
    rw [intervalIntegrable_iff] at hcopy ⊢
    have hL : Integrable (fun x => ((deriv g x : ℝ) : ℂ)) (volume.restrict (Ι a b)) := by
      simpa [Function.comp_def] using Complex.ofRealCLM.integrable_comp hcopy.integrable
    exact hL.const_mul (-(Complex.I))
  have hv'_int : IntervalIntegrable v' volume a b := by
    rw [hv'def]
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    apply Continuous.mul
    · exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hφ.continuous))
    · exact continuous_const.mul (Complex.continuous_ofReal.comp hderiv_cont)
  have hibp : ∫ t in a..b, v t = u b * v b - u a * v a - ∫ t in a..b, u' t * v t := by
    have h0 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv hv_deriv hu'_int hv'_int
    rw [← h0]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hle] at ht
    rw [hudef, hv'def, hvdef]
    simp only []
    have hgt_ne : deriv φ t ≠ 0 := hne t ht'
    have hgval : g t * deriv φ t = 1 := by
      rw [hgdef]; exact inv_mul_cancel₀ hgt_ne
    have hcast : ((g t : ℝ) : ℂ) * ((deriv φ t : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hgval, Complex.ofReal_one]
    have hII : -(Complex.I) * Complex.I = (1:ℂ) := by rw [neg_mul, Complex.I_mul_I]; ring
    have key : -(Complex.I) * ((g t : ℝ) : ℂ) * (Complex.exp (Complex.I * ↑(φ t)) * (Complex.I * ↑(deriv φ t)))
        = Complex.exp (Complex.I * (φ t : ℂ)) := by
      calc -(Complex.I) * ((g t : ℝ) : ℂ) * (Complex.exp (Complex.I * ↑(φ t)) * (Complex.I * ↑(deriv φ t)))
          = (-(Complex.I) * Complex.I) * (((g t : ℝ) : ℂ) * ((deriv φ t : ℝ) : ℂ)) * Complex.exp (Complex.I * (φ t : ℂ)) := by ring
        _ = Complex.exp (Complex.I * (φ t : ℂ)) := by rw [hII, hcast]; ring
    exact key.symm
  have hnu : ∀ x, ‖u x‖ = |g x| := by
    intro x
    rw [hudef]
    simp [Complex.norm_I]
  have hnv : ∀ x, ‖v x‖ = 1 := by
    intro x
    have hvv : v x = Complex.exp (((φ x : ℝ) : ℂ) * Complex.I) := by
      rw [hvdef, mul_comm]
    rw [hvv]
    exact Complex.norm_exp_ofReal_mul_I (φ x)
  have hnu' : ∀ x, ‖u' x‖ = |deriv g x| := by
    intro x
    rw [hu'def]
    simp [Complex.norm_I]
  calc ‖∫ t in a..b, v t‖
      = ‖u b * v b - u a * v a - ∫ t in a..b, u' t * v t‖ := by rw [hibp]
    _ ≤ ‖u b * v b‖ + ‖u a * v a‖ + ‖∫ t in a..b, u' t * v t‖ := by
        calc ‖u b * v b - u a * v a - ∫ t in a..b, u' t * v t‖
            ≤ ‖u b * v b - u a * v a‖ + ‖∫ t in a..b, u' t * v t‖ := norm_sub_le _ _
          _ ≤ (‖u b * v b‖ + ‖u a * v a‖) + ‖∫ t in a..b, u' t * v t‖ := by
              gcongr; exact norm_sub_le _ _
    _ ≤ (|g b| + |g a|) + ∫ t in a..b, |deriv g t| := by
        have h1 : ‖u b * v b‖ = |g b| := by rw [norm_mul, hnu, hnv, mul_one]
        have h2 : ‖u a * v a‖ = |g a| := by rw [norm_mul, hnu, hnv, mul_one]
        have h3 : ‖∫ t in a..b, u' t * v t‖ ≤ ∫ t in a..b, |deriv g t| := by
          calc ‖∫ t in a..b, u' t * v t‖ ≤ ∫ t in a..b, ‖u' t * v t‖ :=
                intervalIntegral.norm_integral_le_integral_norm hle
            _ = ∫ t in a..b, |deriv g t| := by
                apply intervalIntegral.integral_congr
                intro t ht
                simp only [hnu', hnv, norm_mul, mul_one]
        rw [h1, h2] at *
        linarith
    _ ≤ 4 * lam⁻¹ := by
        have h1 : |g b| ≤ lam⁻¹ := hg_bound b ⟨hle, le_rfl⟩
        have h2 : |g a| ≤ lam⁻¹ := hg_bound a ⟨le_rfl, hle⟩
        linarith [hInt_g]
    _ = 4 / lam := by rw [div_eq_mul_inv]



lemma sign_const_of_ne {c d : ℝ} {g : ℝ → ℝ} (hcont : ContinuousOn g (Set.Icc c d))
    (hne : ∀ x ∈ Set.Ioo c d, g x ≠ 0) :
    (∀ x ∈ Set.Ioo c d, 0 < g x) ∨ (∀ x ∈ Set.Ioo c d, g x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨x1, hx1, hx1'⟩ := h.1
  obtain ⟨x2, hx2, hx2'⟩ := h.2
  have h1 : g x1 < 0 := lt_of_le_of_ne hx1' (hne x1 hx1)
  have h2 : 0 < g x2 := lt_of_le_of_ne hx2' (Ne.symm (hne x2 hx2))
  rcases le_total x1 x2 with hle | hle
  · have hseg : Set.Icc x1 x2 ⊆ Set.Icc c d :=
      fun x hx => ⟨le_trans (le_of_lt hx1.1) hx.1, le_trans hx.2 (le_of_lt hx2.2)⟩
    have hcont' : ContinuousOn g (Set.Icc x1 x2) := hcont.mono hseg
    have hmem : (0:ℝ) ∈ Set.Icc (g x1) (g x2) := ⟨le_of_lt h1, le_of_lt h2⟩
    obtain ⟨z, hz, hzeq⟩ := intermediate_value_Icc hle hcont' hmem
    exact hne z ⟨lt_of_lt_of_le hx1.1 hz.1, lt_of_le_of_lt hz.2 hx2.2⟩ hzeq
  · have hseg : Set.Icc x2 x1 ⊆ Set.Icc c d :=
      fun x hx => ⟨le_trans (le_of_lt hx2.1) hx.1, le_trans hx.2 (le_of_lt hx1.2)⟩
    have hcont' : ContinuousOn g (Set.Icc x2 x1) := hcont.mono hseg
    have hmem : (0:ℝ) ∈ Set.Icc (g x1) (g x2) := ⟨le_of_lt h1, le_of_lt h2⟩
    obtain ⟨z, hz, hzeq⟩ := intermediate_value_Icc' hle hcont' hmem
    exact hne z ⟨lt_of_lt_of_le hx2.1 hz.1, lt_of_le_of_lt hz.2 hx1.2⟩ hzeq

lemma deriv_pi_eval (P : Polynomial ℝ) (t : ℝ) :
    deriv (fun s => 2 * Real.pi * P.eval s) t = 2 * Real.pi * (P.derivative).eval t := by
  rw [deriv_const_mul _ (Polynomial.differentiable P).differentiableAt, Polynomial.deriv]

lemma contDiff_pi_eval (P : Polynomial ℝ) :
    ContDiff ℝ 2 (fun s => 2 * Real.pi * P.eval s) := by
  have h : ContDiff ℝ 2 (fun s => P.eval s) := by
    have := Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) P (2 : ℕ∞)
    simpa using this
  exact contDiff_const.mul h

lemma integral_exp_comm (φ : ℝ → ℝ) (a b : ℝ) :
    (∫ t in a..b, Complex.exp (↑(φ t) * Complex.I))
      = ∫ t in a..b, Complex.exp (Complex.I * (φ t : ℂ)) := by
  apply intervalIntegral.integral_congr
  intro t ht
  simp only []
  rw [mul_comm]

lemma abs_eval_ge_on_Icc_of_on_Ioo {c d ρ : ℝ} (hcd : c < d) {q : Polynomial ℝ}
    (h : ∀ x ∈ Set.Ioo c d, ρ ≤ |q.eval x|) :
    ∀ x ∈ Set.Icc c d, ρ ≤ |q.eval x| := by
  have hc : Continuous fun x => |q.eval x| := continuous_abs.comp (Polynomial.continuous q)
  have hclosed : IsClosed {x : ℝ | ρ ≤ |q.eval x|} := isClosed_le continuous_const hc
  have hsub : Set.Ioo c d ⊆ {x : ℝ | ρ ≤ |q.eval x|} := h
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo hcd.ne] at hcl
  exact fun x hx => hcl hx

lemma integral_indicator_Icc (B : Set ℝ) (hB : B ⊆ Set.Icc (0:ℝ) 1) (hBm : MeasurableSet B) :
    ∫ x in (0:ℝ)..1, B.indicator (fun _ => (1:ℝ)) x = volume.real B := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← MeasureTheory.integral_indicator (μ := volume) measurableSet_Icc]
  rw [Set.indicator_indicator]
  rw [Set.inter_eq_right.mpr hB]
  exact MeasureTheory.integral_indicator_one hBm



lemma strict_mono_enum_Icc (S : Finset ℝ) (h0 : 0 ∈ S) (hnonneg : ∀ x ∈ S, 0 ≤ x)
    (hlt : ∀ x ∈ S, x < 1) :
    ∃ (n : ℕ) (t : ℕ → ℝ), n ≤ S.card ∧ t 0 = 0 ∧ t n = 1 ∧
      (∀ i < n, t i ∈ S) ∧
      (∀ i < n, t i < t (i+1)) ∧
      (∀ i < n, ∀ x, t i < x → x < t (i+1) → x ∉ S) := by
  classical
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨0, h0⟩
  let t : ℕ → ℝ := fun i => if h : i < S.card then S.orderEmbOfFin rfl ⟨i, h⟩ else 1
  refine ⟨S.card, t, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [t]
    rw [dif_pos hpos, Finset.orderEmbOfFin_zero (s := S) rfl hpos]
    refine le_antisymm (Finset.min'_le S 0 h0) ?_
    exact hnonneg _ (Finset.min'_mem S ⟨0, h0⟩)
  · simp only [t]
    exact dif_neg (lt_irrefl S.card)
  · intro i hi
    simp only [t]
    rw [dif_pos hi]
    exact Finset.orderEmbOfFin_mem S rfl ⟨i, hi⟩
  · intro i hi
    have hine : i < S.card := hi
    simp only [t]
    rw [dif_pos hine]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hlt' | heq
    · rw [dif_pos hlt']
      exact (S.orderEmbOfFin rfl).strictMono (Nat.lt_succ_self i)
    · rw [dif_neg (by omega : ¬ (i + 1 < S.card))]
      have hieq : i = S.card - 1 := by omega
      subst hieq
      rw [Finset.orderEmbOfFin_last (s := S) rfl hpos]
      exact (Finset.max'_lt_iff S ⟨0, h0⟩).mpr hlt
  · intro i hi x hx1 hx2 hxS
    have hine : i < S.card := hi
    simp only [t] at hx1 hx2
    rw [dif_pos hine] at hx1
    have hxrange : x ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin S rfl]; exact hxS
    obtain ⟨j, hj⟩ := hxrange
    have hlt1 : S.orderEmbOfFin rfl ⟨i, hine⟩ < S.orderEmbOfFin rfl j := by rw [hj]; exact hx1
    have hij : (⟨i, hine⟩ : Fin S.card) < j := (S.orderEmbOfFin rfl).lt_iff_lt.mp hlt1
    have hij' : i < j.val := by rw [Fin.lt_def] at hij; simpa using hij
    have hji : j.val < i + 1 := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hlt' | heq
      · rw [dif_pos hlt'] at hx2
        have h2 : S.orderEmbOfFin rfl j < S.orderEmbOfFin rfl ⟨i+1, hlt'⟩ := by rw [hj]; exact hx2
        have h3 : j < (⟨i+1, hlt'⟩ : Fin S.card) := (S.orderEmbOfFin rfl).lt_iff_lt.mp h2
        rw [Fin.lt_def] at h3; simpa using h3
      · omega
    omega



lemma intervalIntegrable_indicator_one (B : Set ℝ) (hBm : MeasurableSet B) (a b : ℝ) :
    IntervalIntegrable (B.indicator (fun _ => (1:ℝ))) volume a b := by
  have hle : ∀ x, ‖B.indicator (fun _ : ℝ => (1:ℝ)) x‖ ≤ 1 := by
    intro x
    rcases em (x ∈ B) with hx | hx
    · rw [Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp
  have hvol : volume (Set.Ioc a b) < ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hvol' : volume (Set.Ioc b a) < ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hm : Measurable (B.indicator (fun _ : ℝ => (1:ℝ))) := measurable_const.indicator hBm
  refine ⟨?_, ?_⟩
  · exact IntegrableOn.of_bound hvol hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hle)
  · exact IntegrableOn.of_bound hvol' hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hle)

lemma norm_int_exp_neg (φ : ℝ → ℝ) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (Complex.I * ((-(φ t) : ℝ) : ℂ))‖
      = ‖∫ t in a..b, Complex.exp (Complex.I * (φ t : ℂ))‖ := by
  have hfun : (fun t => Complex.exp (Complex.I * ((-(φ t) : ℝ) : ℂ)))
      = (fun t => (starRingEnd ℂ) (Complex.exp (Complex.I * (φ t : ℂ)))) := by
    funext t
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hfun, intervalIntegral.intervalIntegral_conj, Complex.norm_conj]

lemma vdc_first_deriv {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hφ : ContDiff ℝ 2 φ)
    (hmono : MonotoneOn (deriv φ) (Set.Icc a b) ∨ AntitoneOn (deriv φ) (Set.Icc a b))
    (hbound : ∀ x ∈ Set.Icc a b, lam ≤ |deriv φ x|) :
    ‖∫ t in a..b, Complex.exp (Complex.I * (φ t : ℂ))‖ ≤ 4 / lam := by
  rcases hmono with h | h
  · exact vdc_first_deriv_mono hab hlam hφ h hbound
  · have hψ : ContDiff ℝ 2 (fun t => -φ t) := hφ.neg
    have hmonoψ : MonotoneOn (deriv (fun t => -φ t)) (Set.Icc a b) := by
      rw [deriv_fun_neg]
      exact h.neg
    have hboundψ : ∀ x ∈ Set.Icc a b, lam ≤ |deriv (fun t => -φ t) x| := by
      intro x hx
      rw [deriv_fun_neg]
      simp only [abs_neg]
      exact hbound x hx
    have hmain := vdc_first_deriv_mono hab hlam hψ hmonoψ hboundψ
    rw [← norm_int_exp_neg φ a b]
    simpa using hmain


theorem poly_first_derivative_test (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Polynomial ℝ), P.natDegree ≤ k → ∀ ρ : ℝ, 0 < ρ →
      ‖∫ t in (0:ℝ)..1, Complex.exp (↑(2 * Real.pi * P.eval t) * Complex.I)‖
        ≤ C / ρ + (MeasureTheory.volume {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ |(P.derivative).eval t| < ρ}).toReal := by
  classical
  refine ⟨6 * k + 4, by positivity, ?_⟩
  intro P hPk ρ hρ
  set B : Set ℝ := {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ |(P.derivative).eval t| < ρ} with hBdef
  set f : ℝ → ℝ := fun t => 2 * Real.pi * P.eval t with hfdef
  have hfc : ContDiff ℝ 2 f := by rw [hfdef]; exact contDiff_pi_eval P
  have hderivf : ∀ x, deriv f x = 2 * Real.pi * (P.derivative).eval x := fun x => by rw [hfdef, deriv_pi_eval]
  have hconv : (∫ t in (0:ℝ)..1, Complex.exp (↑(2 * Real.pi * P.eval t) * Complex.I))
      = ∫ t in (0:ℝ)..1, Complex.exp (Complex.I * (f t : ℂ)) := by
    rw [hfdef]; exact integral_exp_comm _ _ _
  rw [hconv]
  have hBm : MeasurableSet B := by
    rw [hBdef]
    exact measurableSet_Icc.inter
      (isOpen_lt (continuous_abs.comp (Polynomial.continuous _)) continuous_const).measurableSet
  have hBsub : B ⊆ Set.Icc (0:ℝ) 1 := fun t ht => ht.1
  by_cases hdeg : P.derivative.derivative = 0
  · -- Case A: P' constant
    have hconst : P.derivative = Polynomial.C ((P.derivative).coeff 0) :=
      Polynomial.eq_C_of_derivative_eq_zero hdeg
    have hQeval : ∀ t, (P.derivative).eval t = (P.derivative).coeff 0 := fun t => by rw [hconst]; simp
    have hderivfc : ∀ x, deriv f x = 2 * Real.pi * (P.derivative).coeff 0 := fun x => by rw [hderivf x, hQeval]
    by_cases hcρ : |(P.derivative).coeff 0| < ρ
    · have hBeq : B = Set.Icc (0:ℝ) 1 := by
        rw [hBdef]; ext t; constructor
        · intro ht; exact ht.1
        · intro ht
          rw [Set.mem_ofPred_eq]
          exact ⟨ht, by rw [hQeval]; exact hcρ⟩
      rw [hBeq, Real.volume_Icc]
      simp only [sub_zero, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1)]
      have h1 : ‖∫ t in (0:ℝ)..1, Complex.exp (Complex.I * (f t : ℂ))‖ ≤ 1 := by
        calc _ ≤ ∫ t in (0:ℝ)..1, ‖Complex.exp (Complex.I * (f t : ℂ))‖ :=
              intervalIntegral.norm_integral_le_integral_norm zero_le_one
          _ = ∫ t in (0:ℝ)..1, (1:ℝ) := by
              apply intervalIntegral.integral_congr
              intro t ht
              simp only []
              have hcomm : Complex.I * (f t : ℂ) = ((f t : ℝ) : ℂ) * Complex.I := by rw [mul_comm]
              rw [hcomm]
              exact Complex.norm_exp_ofReal_mul_I (f t)
          _ = 1 := by rw [intervalIntegral.integral_const]; simp
      have : (0:ℝ) ≤ (6 * (k:ℝ) + 4) / ρ := by positivity
      linarith
    · push Not at hcρ
      have hBempty : B = ∅ := by
        rw [hBdef]; ext t; constructor
        · intro ht
          rw [Set.mem_ofPred_eq] at ht
          exact absurd (by rw [hQeval] at ht; exact ht.2) (not_lt.mpr hcρ)
        · intro ht; exact ht.elim
      rw [hBempty, MeasureTheory.measure_empty, ENNReal.toReal_zero, add_zero]
      have hmono : MonotoneOn (deriv f) (Set.Icc (0:ℝ) 1) := by
        intro x hx y hy hxy
        rw [hderivfc x, hderivfc y]
      have hbnd : ∀ x ∈ Set.Icc (0:ℝ) 1, 2 * Real.pi * ρ ≤ |deriv f x| := by
        intro x hx
        rw [hderivfc x, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        exact mul_le_mul_of_nonneg_left hcρ (by positivity)
      have hvdc := vdc_first_deriv zero_le_one (by positivity : (0:ℝ) < 2 * Real.pi * ρ) hfc (Or.inl hmono) hbnd
      calc ‖∫ t in (0:ℝ)..1, Complex.exp (Complex.I * (f t : ℂ))‖ ≤ 4 / (2 * Real.pi * ρ) := hvdc
        _ ≤ (6 * (k:ℝ) + 4) / ρ := by
            have h1 : (4:ℝ) / (2 * Real.pi * ρ) ≤ 2 / ρ := by
              rw [div_le_div_iff₀ (by positivity) hρ]
              nlinarith [Real.pi_gt_three]
            have h2 : (2:ℝ) / ρ ≤ (6 * (k:ℝ) + 4) / ρ := by
              apply div_le_div_of_nonneg_right _ (le_of_lt hρ)
              linarith
            linarith
  · -- Case B
    have hR2ne : P.derivative - Polynomial.C ρ ≠ 0 := by
      intro h
      apply hdeg
      have h2 : Polynomial.derivative (P.derivative - Polynomial.C ρ) = 0 := by rw [h, Polynomial.derivative_zero]
      rwa [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] at h2
    have hR3ne : P.derivative + Polynomial.C ρ ≠ 0 := by
      intro h
      apply hdeg
      have h2 : Polynomial.derivative (P.derivative + Polynomial.C ρ) = 0 := by rw [h, Polynomial.derivative_zero]
      rwa [Polynomial.derivative_add, Polynomial.derivative_C, add_zero] at h2
    set W : Polynomial ℝ := P.derivative.derivative * (P.derivative - Polynomial.C ρ) * (P.derivative + Polynomial.C ρ) with hW
    have hWne : W ≠ 0 := by
      rw [hW]; exact mul_ne_zero (mul_ne_zero hdeg hR2ne) hR3ne
    set Sw : Finset ℝ := W.roots.toFinset with hRw
    set S : Finset ℝ := insert 0 (Sw.filter (fun t => t ∈ Set.Ioo (0:ℝ) 1)) with hS
    have h0S : (0:ℝ) ∈ S := by rw [hS]; exact Finset.mem_insert_self _ _
    have hSnonneg : ∀ x ∈ S, 0 ≤ x := by
      intro x hx
      rw [hS] at hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact le_of_eq h.symm
      · rw [Finset.mem_filter] at h; exact le_of_lt h.2.1
    have hSlt : ∀ x ∈ S, x < 1 := by
      intro x hx
      rw [hS] at hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; norm_num
      · rw [Finset.mem_filter] at h; exact h.2.2
    have hcard : S.card ≤ 3 * k + 1 := by
      have h1 : S.card ≤ (Sw.filter (fun t => t ∈ Set.Ioo (0:ℝ) 1)).card + 1 := by
        rw [hS]; exact Finset.card_insert_le _ _
      have h2 : (Sw.filter (fun t => t ∈ Set.Ioo (0:ℝ) 1)).card ≤ Sw.card := Finset.card_filter_le _ _
      have hWd : W.natDegree ≤ 3 * k := by
        rw [hW]
        calc (P.derivative.derivative * (P.derivative - Polynomial.C ρ) * (P.derivative + Polynomial.C ρ)).natDegree
            ≤ (P.derivative.derivative * (P.derivative - Polynomial.C ρ)).natDegree + (P.derivative + Polynomial.C ρ).natDegree :=
                Polynomial.natDegree_mul_le
          _ ≤ ((P.derivative.derivative).natDegree + (P.derivative - Polynomial.C ρ).natDegree)
                + (P.derivative + Polynomial.C ρ).natDegree := by
                have := Polynomial.natDegree_mul_le (p := P.derivative.derivative) (q := P.derivative - Polynomial.C ρ)
                linarith
          _ ≤ 3 * k := by
                have hA : (P.derivative.derivative).natDegree ≤ k := by
                  calc (P.derivative.derivative).natDegree ≤ (P.derivative).natDegree - 1 := Polynomial.natDegree_derivative_le _
                    _ ≤ (P.derivative).natDegree := Nat.sub_le _ _
                    _ ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le _
                    _ ≤ P.natDegree := Nat.sub_le _ _
                    _ ≤ k := hPk
                have hB : (P.derivative - Polynomial.C ρ).natDegree ≤ k := by
                  calc (P.derivative - Polynomial.C ρ).natDegree ≤ max (P.derivative).natDegree (Polynomial.C ρ).natDegree := Polynomial.natDegree_sub_le _ _
                    _ ≤ k := by
                        have h1 : (P.derivative).natDegree ≤ k := le_trans (le_trans (Polynomial.natDegree_derivative_le _) (Nat.sub_le _ _)) hPk
                        rw [Polynomial.natDegree_C]; exact max_le h1 (Nat.zero_le _)
                have hC : (P.derivative + Polynomial.C ρ).natDegree ≤ k := by
                  calc (P.derivative + Polynomial.C ρ).natDegree ≤ max (P.derivative).natDegree (Polynomial.C ρ).natDegree := Polynomial.natDegree_add_le _ _
                    _ ≤ k := by
                        have h1 : (P.derivative).natDegree ≤ k := le_trans (le_trans (Polynomial.natDegree_derivative_le _) (Nat.sub_le _ _)) hPk
                        rw [Polynomial.natDegree_C]; exact max_le h1 (Nat.zero_le _)
                omega
      have hSw : Sw.card ≤ 3 * k := by
        rw [hRw]
        calc (W.roots.toFinset).card ≤ W.roots.card := Multiset.toFinset_card_le _
          _ ≤ W.natDegree := Polynomial.card_roots' _
          _ ≤ 3 * k := hWd
      omega
    obtain ⟨n, t, hnle, ht0, htn, htS, htinc, htnoS⟩ := strict_mono_enum_Icc S h0S hSnonneg hSlt
    have hn : n ≤ 3 * k + 1 := le_trans hnle hcard
    -- per-piece bound
    have hpiece : ∀ i, i < n →
        ‖∫ u in (t i)..(t (i+1)), Complex.exp (Complex.I * (f u : ℂ))‖
          ≤ 2 / (Real.pi * ρ) + ∫ u in (t i)..(t (i+1)), B.indicator (fun _ => (1:ℝ)) u := by
      intro i hi
      have hcd : t i < t (i+1) := htinc i hi
      have hc0 : 0 ≤ t i := hSnonneg (t i) (htS i hi)
      have hd1 : t (i+1) ≤ 1 := by
        by_cases h : i + 1 < n
        · exact le_of_lt (hSlt (t (i+1)) (htS (i+1) h))
        · have h' : i + 1 = n := by omega
          rw [h', htn]
      have hnoSmem : ∀ x, t i < x → x < t (i+1) → x ∉ S := fun x => htnoS i hi x
      have hWx : ∀ x, t i < x → x < t (i+1) → W.eval x ≠ 0 := by
        intro x hx1 hx2 hx0
        exact hnoSmem x hx1 hx2 (by
          rw [hS]
          apply Finset.mem_insert.mpr; right
          rw [Finset.mem_filter]
          refine ⟨?_, ⟨lt_of_le_of_lt hc0 hx1, lt_of_lt_of_le hx2 hd1⟩⟩
          rw [hRw, Multiset.mem_toFinset, Polynomial.mem_roots']
          exact ⟨hWne, by rw [Polynomial.IsRoot.def]; exact hx0⟩)
      have hfac : ∀ x, t i < x → x < t (i+1) →
          (P.derivative.derivative).eval x * ((P.derivative).eval x - ρ) * ((P.derivative).eval x + ρ) ≠ 0 := by
        intro x hx1 hx2
        have h := hWx x hx1 hx2
        simp only [hW, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C] at h
        exact h
      have hQ2nz : ∀ x, t i < x → x < t (i+1) → (P.derivative.derivative).eval x ≠ 0 := by
        intro x hx1 hx2 h0
        exact hfac x hx1 hx2 (by rw [h0]; ring)
      have hQnz : ∀ x, t i < x → x < t (i+1) → (P.derivative).eval x ≠ ρ := by
        intro x hx1 hx2 h0
        exact hfac x hx1 hx2 (by rw [h0]; ring)
      have hQnzm : ∀ x, t i < x → x < t (i+1) → (P.derivative).eval x ≠ -ρ := by
        intro x hx1 hx2 h0
        exact hfac x hx1 hx2 (by rw [h0]; ring)
      have hQ2cont : ContinuousOn (fun x => (P.derivative.derivative).eval x) (Set.Icc (t i) (t (i+1))) :=
        (Polynomial.continuous _).continuousOn
      have hP'mono : MonotoneOn (fun x => (P.derivative).eval x) (Set.Icc (t i) (t (i+1))) ∨
          AntitoneOn (fun x => (P.derivative).eval x) (Set.Icc (t i) (t (i+1))) := by
        rcases sign_const_of_ne hQ2cont (fun x hx => hQ2nz x hx.1 hx.2) with hp | hn
        · left
          refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (Polynomial.continuous _).continuousOn
            (Polynomial.differentiable _).differentiableOn ?_
          intro x hx
          rw [interior_Icc] at hx
          rw [Polynomial.deriv]
          exact le_of_lt (hp x hx)
        · right
          refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (Polynomial.continuous _).continuousOn
            (Polynomial.differentiable _).differentiableOn ?_
          intro x hx
          rw [interior_Icc] at hx
          rw [Polynomial.deriv]
          exact le_of_lt (hn x hx)
      have hmonoF : MonotoneOn (deriv f) (Set.Icc (t i) (t (i+1))) ∨
          AntitoneOn (deriv f) (Set.Icc (t i) (t (i+1))) := by
        rcases hP'mono with h | h
        · left; intro x hx y hy hxy
          rw [hderivf x, hderivf y]
          exact mul_le_mul_of_nonneg_left (h hx hy hxy) (by positivity)
        · right; intro x hx y hy hxy
          rw [hderivf x, hderivf y]
          exact mul_le_mul_of_nonneg_left (h hx hy hxy) (by positivity)
      set m : ℝ := (t i + t (i+1)) / 2 with hmdef
      have hm_mem : m ∈ Set.Ioo (t i) (t (i+1)) := by
        rw [hmdef]; exact ⟨by linarith, by linarith⟩
      have hsgnR : (∀ x ∈ Set.Ioo (t i) (t (i+1)), ρ < (P.derivative).eval x) ∨
          (∀ x ∈ Set.Ioo (t i) (t (i+1)), (P.derivative).eval x < ρ) := by
        have hcont : ContinuousOn (fun x => (P.derivative).eval x - ρ) (Set.Icc (t i) (t (i+1))) :=
          (Polynomial.continuous _).continuousOn.sub continuousOn_const
        rcases sign_const_of_ne hcont (fun x hx => by
          intro h0; exact hQnz x hx.1 hx.2 (by linarith)) with h | h
        · left; intro x hx; have := h x hx; linarith
        · right; intro x hx; have := h x hx; linarith
      have hsgnM : (∀ x ∈ Set.Ioo (t i) (t (i+1)), (P.derivative).eval x < -ρ) ∨
          (∀ x ∈ Set.Ioo (t i) (t (i+1)), -ρ < (P.derivative).eval x) := by
        have hcont : ContinuousOn (fun x => (P.derivative).eval x + ρ) (Set.Icc (t i) (t (i+1))) :=
          (Polynomial.continuous _).continuousOn.add continuousOn_const
        rcases sign_const_of_ne hcont (fun x hx => by
          intro h0; exact hQnzm x hx.1 hx.2 (by linarith)) with h | h
        · right; intro x hx; have := h x hx; linarith
        · left; intro x hx; have := h x hx; linarith
      by_cases hgood : ρ < (P.derivative).eval m ∨ (P.derivative).eval m < -ρ
      · have hge : ∀ x ∈ Set.Ioo (t i) (t (i+1)), ρ ≤ |(P.derivative).eval x| := by
          intro x hx
          rcases hgood with hg | hg
          · have hx' : ρ < (P.derivative).eval x := by
              rcases hsgnR with h | h
              · exact h x hx
              · exact absurd (h m hm_mem) (not_lt.mpr (le_of_lt hg))
            rw [abs_of_pos (by linarith)]; exact le_of_lt hx'
          · have hx' : (P.derivative).eval x < -ρ := by
              rcases hsgnM with h | h
              · exact h x hx
              · exact absurd (h m hm_mem) (not_lt.mpr (le_of_lt hg))
            rw [abs_of_neg (by linarith)]; linarith
        have hgeIcc : ∀ x ∈ Set.Icc (t i) (t (i+1)), ρ ≤ |(P.derivative).eval x| :=
          abs_eval_ge_on_Icc_of_on_Ioo hcd hge
        have hbnd : ∀ x ∈ Set.Icc (t i) (t (i+1)), 2 * Real.pi * ρ ≤ |deriv f x| := by
          intro x hx
          rw [hderivf x, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
          exact mul_le_mul_of_nonneg_left (hgeIcc x hx) (by positivity)
        have hvdc := vdc_first_deriv (le_of_lt hcd) (by positivity : (0:ℝ) < 2 * Real.pi * ρ) hfc hmonoF hbnd
        have heqvdc : (4:ℝ) / (2 * Real.pi * ρ) = 2 / (Real.pi * ρ) := by
          have h2 : (2:ℝ) ≠ 0 := by norm_num
          have e1 : (4:ℝ) = 2 * 2 := by norm_num
          have e2 : (2:ℝ) * Real.pi * ρ = 2 * (Real.pi * ρ) := by ring
          rw [e1, e2, mul_div_mul_left _ _ h2]
        have hnn : 0 ≤ ∫ u in (t i)..(t (i+1)), B.indicator (fun _ => (1:ℝ)) u :=
          intervalIntegral.integral_nonneg (le_of_lt hcd) (fun u hu => by
            by_cases h : u ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h])
        calc ‖∫ u in (t i)..(t (i+1)), Complex.exp (Complex.I * (f u : ℂ))‖
            ≤ 4 / (2 * Real.pi * ρ) := hvdc
          _ = 2 / (Real.pi * ρ) := heqvdc
          _ ≤ 2 / (Real.pi * ρ) + ∫ u in (t i)..(t (i+1)), B.indicator (fun _ => (1:ℝ)) u := by linarith
      · push Not at hgood
        have hbad : ∀ x ∈ Set.Ioo (t i) (t (i+1)), |(P.derivative).eval x| < ρ := by
          intro x hx
          have hR : (P.derivative).eval x < ρ := by
            rcases hsgnR with h | h
            · exact absurd (h m hm_mem) (not_lt.mpr hgood.1)
            · exact h x hx
          have hM : -ρ < (P.derivative).eval x := by
            rcases hsgnM with h | h
            · exact absurd (h m hm_mem) (not_lt.mpr hgood.2)
            · exact h x hx
          rw [abs_lt]; exact ⟨hM, hR⟩
        have hsubB : Set.Ioo (t i) (t (i+1)) ⊆ B := by
          intro x hx
          rw [hBdef]
          exact ⟨⟨le_of_lt (lt_of_le_of_lt hc0 hx.1), le_of_lt (lt_of_lt_of_le hx.2 hd1)⟩, hbad x hx⟩
        have hIntB_eq : ∫ u in (t i)..(t (i+1)), B.indicator (fun _ => (1:ℝ)) u = t (i+1) - t i := by
          have hcong : ∫ u in (t i)..(t (i+1)), B.indicator (fun _ => (1:ℝ)) u = ∫ u in (t i)..(t (i+1)), (1:ℝ) := by
            apply intervalIntegral.integral_congr_uIoo
            intro u hu
            rw [Set.uIoo_of_le (le_of_lt hcd)] at hu
            exact Set.indicator_of_mem (hsubB hu) _
          rw [hcong, intervalIntegral.integral_const]; simp
        have hbound : ‖∫ u in (t i)..(t (i+1)), Complex.exp (Complex.I * (f u : ℂ))‖ ≤ t (i+1) - t i := by
          calc _ ≤ ∫ u in (t i)..(t (i+1)), ‖Complex.exp (Complex.I * (f u : ℂ))‖ :=
                intervalIntegral.norm_integral_le_integral_norm (le_of_lt hcd)
            _ = ∫ u in (t i)..(t (i+1)), (1:ℝ) := by
                apply intervalIntegral.integral_congr
                intro u hu
                simp only []
                have hcomm : Complex.I * (f u : ℂ) = ((f u : ℝ) : ℂ) * Complex.I := by rw [mul_comm]
                rw [hcomm]
                exact Complex.norm_exp_ofReal_mul_I (f u)
            _ = t (i+1) - t i := by rw [intervalIntegral.integral_const]; simp
        rw [hIntB_eq]
        have : 0 ≤ 2 / (Real.pi * ρ) := by positivity
        linarith
    -- summation
    have hintF : ∀ j < n, IntervalIntegrable (fun u => Complex.exp (Complex.I * (f u : ℂ))) volume (t j) (t (j+1)) := by
      intro j hj
      apply ContinuousOn.intervalIntegrable
      exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hfc.continuous))).continuousOn
    have hintB : ∀ j < n, IntervalIntegrable (B.indicator (fun _ => (1:ℝ))) volume (t j) (t (j+1)) :=
      fun j hj => intervalIntegrable_indicator_one B hBm _ _
    have hsumF := intervalIntegral.sum_integral_adjacent_intervals (a := t) (n := n) (μ := volume)
      (f := fun u => Complex.exp (Complex.I * (f u : ℂ))) hintF
    rw [ht0, htn] at hsumF
    have hsumB := intervalIntegral.sum_integral_adjacent_intervals (a := t) (n := n) (μ := volume)
      (f := B.indicator (fun _ => (1:ℝ))) hintB
    rw [ht0, htn] at hsumB
    have hmain : ‖∫ u in (0:ℝ)..1, Complex.exp (Complex.I * (f u : ℂ))‖
        ≤ (6 * (k:ℝ) + 4) / ρ + (volume B).toReal := by
      calc ‖∫ u in (0:ℝ)..1, Complex.exp (Complex.I * (f u : ℂ))‖
          = ‖∑ j ∈ Finset.range n, ∫ u in (t j)..(t (j+1)), Complex.exp (Complex.I * (f u : ℂ))‖ := by
              rw [hsumF]
        _ ≤ ∑ j ∈ Finset.range n, ‖∫ u in (t j)..(t (j+1)), Complex.exp (Complex.I * (f u : ℂ))‖ :=
              norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range n, (2 / (Real.pi * ρ) + ∫ u in (t j)..(t (j+1)), B.indicator (fun _ => (1:ℝ)) u) :=
              Finset.sum_le_sum (fun j hj => hpiece j (Finset.mem_range.mp hj))
        _ = n * (2 / (Real.pi * ρ)) + ∑ j ∈ Finset.range n, ∫ u in (t j)..(t (j+1)), B.indicator (fun _ => (1:ℝ)) u := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = n * (2 / (Real.pi * ρ)) + ∫ u in (0:ℝ)..1, B.indicator (fun _ => (1:ℝ)) u := by rw [hsumB]
        _ = n * (2 / (Real.pi * ρ)) + volume.real B := by rw [integral_indicator_Icc B hBsub hBm]
        _ = n * (2 / (Real.pi * ρ)) + (volume B).toReal := by rw [measureReal_def]
        _ ≤ (6 * (k:ℝ) + 4) / ρ + (volume B).toReal := by
              have hnR : (n:ℝ) ≤ 3 * (k:ℝ) + 1 := by exact_mod_cast hn
              have hstep : (n:ℝ) * (2 / (Real.pi * ρ)) ≤ (6 * (k:ℝ) + 4) / ρ := by
                have h1 : 2 / (Real.pi * ρ) ≤ 2 / ρ := by
                  apply div_le_div_of_nonneg_left (by norm_num) hρ
                  nlinarith [Real.pi_gt_three]
                have h2 : (n:ℝ) * (2 / (Real.pi * ρ)) ≤ (n:ℝ) * (2 / ρ) :=
                  mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
                have h3 : (n:ℝ) * (2 / ρ) ≤ (3 * (k:ℝ) + 1) * (2 / ρ) :=
                  mul_le_mul_of_nonneg_right hnR (by positivity)
                have h4 : (3 * (k:ℝ) + 1) * (2 / ρ) = (6 * (k:ℝ) + 2) / ρ := by ring
                have h5 : (6 * (k:ℝ) + 2) / ρ ≤ (6 * (k:ℝ) + 4) / ρ :=
                  div_le_div_of_nonneg_right (by linarith) (le_of_lt hρ)
                linarith [h2, h3, h4, h5]
              linarith
    exact hmain

end

end Commons.Analysis.Oscillatory