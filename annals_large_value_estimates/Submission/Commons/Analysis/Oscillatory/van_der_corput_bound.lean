import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test

open scoped Real ComplexConjugate Topology
open MeasureTheory Set Filter

namespace Commons.Analysis.Oscillatory

noncomputable section

/-- The oscillatory phase exponential `exp(I φ t)`. -/
def osc (φ : ℝ → ℝ) (t : ℝ) : ℂ := Complex.exp (Complex.I * (φ t : ℂ))

lemma osc_norm (φ : ℝ → ℝ) (t : ℝ) : ‖osc φ t‖ = 1 := by
  have h : Complex.I * (φ t : ℂ) = ((φ t : ℝ) : ℂ) * Complex.I := by ring
  rw [osc, h]
  exact Complex.norm_exp_ofReal_mul_I (φ t)

lemma osc_neg_conj (φ : ℝ → ℝ) (t : ℝ) : osc (fun x => -φ x) t = conj (osc φ t) := by
  rw [osc, osc, ← Complex.exp_conj]
  congr 1
  rw [map_mul]
  simp only [Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- Sign constancy of a continuous function with `|g| ≥ λ > 0` on an open interval. -/
lemma sign_const_Ioo {a b : ℝ} {g : ℝ → ℝ} (hcont : ContinuousOn g (Set.Ioo a b))
    {lam : ℝ} (hlam : 0 < lam) (h : ∀ t ∈ Set.Ioo a b, lam ≤ |g t|) :
    (∀ t ∈ Set.Ioo a b, lam ≤ g t) ∨ (∀ t ∈ Set.Ioo a b, g t ≤ -lam) := by
  by_contra hc
  push_neg at hc
  obtain ⟨hs, hsmem, hslt⟩ := hc.1
  obtain ⟨ht, htmem, htgt⟩ := hc.2
  have hsle : g hs ≤ -lam := by
    have h1 : lam ≤ |g hs| := h hs hsmem
    rcases lt_or_ge (g hs) 0 with hlt0 | hge0
    · rw [abs_of_neg hlt0] at h1; linarith
    · rw [abs_of_nonneg hge0] at h1; linarith
  have htge : lam ≤ g ht := by
    have h2 : lam ≤ |g ht| := h ht htmem
    rcases lt_or_ge (g ht) 0 with hlt0 | hge0
    · rw [abs_of_neg hlt0] at h2; linarith
    · rwa [abs_of_nonneg hge0] at h2
  rcases le_total hs ht with hle | hle
  · have hseg : Set.Icc hs ht ⊆ Set.Ioo a b := by
      intro x hx
      exact ⟨lt_of_lt_of_le hsmem.1 hx.1, lt_of_le_of_lt hx.2 htmem.2⟩
    have hcont' : ContinuousOn g (Set.Icc hs ht) := hcont.mono hseg
    have h0 : (0:ℝ) ∈ Set.Icc (g hs) (g ht) := ⟨by linarith, by linarith⟩
    obtain ⟨c, hcseg, hceq⟩ := intermediate_value_Icc hle hcont' h0
    have hcmem : c ∈ Set.Ioo a b := hseg hcseg
    have hthis : lam ≤ |g c| := h c hcmem
    rw [hceq, abs_zero] at hthis
    linarith
  · have hseg : Set.Icc ht hs ⊆ Set.Ioo a b := by
      intro x hx
      exact ⟨lt_of_lt_of_le htmem.1 hx.1, lt_of_le_of_lt hx.2 hsmem.2⟩
    have hcont' : ContinuousOn g (Set.Icc ht hs) := hcont.mono hseg
    have h0 : (0:ℝ) ∈ Set.Icc (g hs) (g ht) := ⟨by linarith, by linarith⟩
    obtain ⟨c, hcseg, hceq⟩ := intermediate_value_Icc' hle hcont' h0
    have hcmem : c ∈ Set.Ioo a b := hseg hcseg
    have hthis : lam ≤ |g c| := h c hcmem
    rw [hceq, abs_zero] at hthis
    linarith

/-- On an open set, `C^n` gives continuity of the ordinary iterated derivative. -/
lemma continuousOn_iteratedDeriv_of_isOpen {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    {n m : ℕ} (hmn : m ≤ n) (h : ContDiffOn ℝ n f s) :
    ContinuousOn (iteratedDeriv m f) s := by
  have hU : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hcont := h.continuousOn_iteratedDerivWithin (by exact_mod_cast hmn) hU
  refine hcont.congr ?_
  intro x hx
  exact (iteratedDerivWithin_of_isOpen hs hx).symm

/-- Positive growth of `g` from a lower bound on its derivative. -/
lemma growth_of_deriv_bound {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ g (Set.Ioo a b))
    {d : ℝ} (hd : ∀ x ∈ Set.Ioo a b, d ≤ deriv g x) :
    ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → d * (y - x) ≤ g y - g x := by
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hinter : interior (Set.Icc a b) = Set.Ioo a b := interior_Icc
  set h' : ℝ → ℝ := fun x => g x - d * x with hh'
  have hh'cont : ContinuousOn h' (Set.Icc a b) := by
    rw [hh']
    exact hcont.sub (continuousOn_id.const_mul d)
  have hh'diff : DifferentiableOn ℝ h' (interior (Set.Icc a b)) := by
    rw [hinter]
    intro x hx
    have hg := hdiff x hx
    have hl : DifferentiableAt ℝ (fun y : ℝ => d * y) x := by fun_prop
    exact hg.sub hl.differentiableWithinAt
  have hh'ge : ∀ x ∈ interior (Set.Icc a b), 0 ≤ deriv h' x := by
    rw [hinter]
    intro x hx
    have hg : DifferentiableAt ℝ g x := (hdiff x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
    have hl : HasDerivAt (fun y : ℝ => d * y) d x := by
      simpa using (hasDerivAt_id x).const_mul d
    have hsub : HasDerivAt h' (deriv g x - d) x := by
      rw [hh']; exact hg.hasDerivAt.sub hl
    rw [hsub.deriv]
    have := hd x hx
    linarith
  have hmono : MonotoneOn h' (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg hconv hh'cont hh'diff hh'ge
  intro x y hx hy hxy
  have hle := hmono hx hy hxy
  rw [hh'] at hle
  rw [mul_sub]
  linarith

end

end Commons.Analysis.Oscillatory

namespace Commons.Analysis.Oscillatory

noncomputable section

/-- Predicate: "the van der Corput bound with exponent `1/k` holds with constant `C`",
phrased with the hypothesis on the open interval `(a,b)`. -/
def vdcBound (k : ℕ) (C : ℝ) : Prop :=
  0 < C ∧ ∀ {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} {lam : ℝ}, 0 < lam →
    ContDiffOn ℝ k φ (Set.Icc a b) →
    (∀ t ∈ Set.Ioo a b, lam ≤ |iteratedDeriv k φ t|) →
    ‖∫ t in a..b, osc φ t‖ ≤ C / lam ^ ((1:ℝ)/k)

/-- Base case `k = 2`, positive curvature. -/
theorem vdc_two_pos {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc a b))
    (h2 : ∀ t ∈ Set.Ioo a b, lam ≤ iteratedDeriv 2 φ t) :
    ‖∫ t in a..b, osc φ t‖ ≤ 1000 / lam ^ ((1:ℝ)/2) := by
  rcases eq_or_lt_of_le hab with hEq | hlt
  · subst hEq
    simp
    positivity
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  set F : ℝ → ℝ := fun x => φ x / (2 * Real.pi) with hFdef
  have hFcont : ContDiffOn ℝ 2 F (Set.Icc a b) := by
    rw [hFdef]; exact hφ.div_const (2 * Real.pi)
  have hderiv1 : ∀ x ∈ Set.Ioo a b, deriv F x = deriv φ x / (2 * Real.pi) := by
    intro x hx
    have hd : HasDerivAt φ (deriv φ x) x :=
      (Submission.SdtOscB.differentiableAt_F_of_Ioo φ hφ hx).hasDerivAt
    have hd' : HasDerivAt F (deriv φ x / (2 * Real.pi)) x := by
      rw [hFdef]; exact hd.div_const _
    exact hd'.deriv
  have hderiv2 : ∀ x ∈ Set.Ioo a b, deriv (deriv F) x = iteratedDeriv 2 φ x / (2 * Real.pi) := by
    intro x hx
    have hcong : deriv F =ᶠ[𝓝 x] (fun y => deriv φ y / (2 * Real.pi)) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hderiv1 y hy
    have hd2 : HasDerivAt (fun y => deriv φ y / (2 * Real.pi))
        (deriv (deriv φ) x / (2 * Real.pi)) x :=
      (Submission.SdtOscB.hasDerivAt_deriv_F_of_Ioo φ hφ hx).div_const _
    have hd3 : HasDerivAt (deriv F) (deriv (deriv φ) x / (2 * Real.pi)) x :=
      hd2.congr_of_eventuallyEq hcong
    rw [hd3.deriv]
    congr 1
    rw [show iteratedDeriv 2 φ = deriv (deriv φ) from by
      rw [iteratedDeriv_succ, iteratedDeriv_one]]
  have hpp : ∀ x ∈ Set.Ioo a b, lam / (2 * Real.pi) ≤ deriv (deriv F) x := by
    intro x hx
    rw [hderiv2 x hx]
    exact div_le_div_of_nonneg_right (h2 x hx) (le_of_lt hpi)
  have key := Submission.SdtOscB.exp_integral_second_deriv_le (a := a) (b := b) hab F
    (δ := lam / (2 * Real.pi)) (by positivity) hFcont hpp
  have hcong : Set.EqOn (fun x => osc φ x)
      (fun x => Complex.exp (↑(2 * Real.pi * F x) * Complex.I)) (Set.uIcc a b) := by
    intro x hx
    simp only [osc]
    congr 1
    have harg : 2 * Real.pi * F x = φ x := by
      rw [hFdef]; field_simp
    rw [harg]; ring
  have hcongint : (∫ t in a..b, osc φ t)
      = (∫ x in a..b, Complex.exp (↑(2 * Real.pi * F x) * Complex.I)) :=
    intervalIntegral.integral_congr hcong
  have hsqrt2pi : Real.sqrt (2 * Real.pi) ≤ 10 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [Real.pi_lt_four]⟩
  have hsqrtlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  rw [hcongint]
  calc
    ‖∫ x in a..b, Complex.exp (↑(2 * Real.pi * F x) * Complex.I)‖
        ≤ 100 / Real.sqrt (lam / (2 * Real.pi)) := key
    _ = 100 * Real.sqrt (2 * Real.pi) / Real.sqrt lam := by
          rw [Real.sqrt_div (le_of_lt hlam) (2 * Real.pi)]
          field_simp
    _ ≤ 1000 / Real.sqrt lam := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hsqrtlam)
          nlinarith [hsqrt2pi]
    _ = 1000 / lam ^ ((1:ℝ)/2) := by rw [Real.sqrt_eq_rpow]

/-- Base case `k = 2`. -/
theorem vdc_two : ∃ C, vdcBound 2 C := by
  refine ⟨1000, by norm_num, ?_⟩
  intro a b hab φ lam hlam hφ hh
  rcases eq_or_lt_of_le hab with hEq | hlt
  · subst hEq; simp; positivity
  have hcont : ContinuousOn (iteratedDeriv 2 φ) (Set.Ioo a b) :=
    continuousOn_iteratedDeriv_of_isOpen isOpen_Ioo (by norm_num)
      (hφ.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  rcases sign_const_Ioo hcont hlam hh with hpos | hneg
  · exact vdc_two_pos hab hlam hφ hpos
  · have hφ' : ContDiffOn ℝ 2 (fun x => -φ x) (Set.Icc a b) := hφ.neg
    have h2' : ∀ t ∈ Set.Ioo a b, lam ≤ iteratedDeriv 2 (fun x => -φ x) t := by
      intro t ht
      rw [iteratedDeriv_fun_neg]
      have := hneg t ht
      linarith
    have hb := vdc_two_pos hab hlam hφ' h2'
    have heqnorm : ‖∫ t in a..b, osc φ t‖ = ‖∫ t in a..b, osc (fun x => -φ x) t‖ := by
      have hcj : (∫ t in a..b, osc (fun x => -φ x) t) = conj (∫ t in a..b, osc φ t) := by
        rw [show (fun t => osc (fun x => -φ x) t) = (fun t => conj (osc φ t)) from
          funext (fun t => osc_neg_conj φ t)]
        exact intervalIntegral.intervalIntegral_conj
      rw [hcj, Complex.norm_conj]
    rw [heqnorm]
    exact hb

end

end Commons.Analysis.Oscillatory

namespace Commons.Analysis.Oscillatory

noncomputable section

lemma rpow_mu_self {lam : ℝ} (hlam : 0 < lam) {k : ℕ} (hk : k ≠ 0) :
    (lam ^ ((k:ℝ)/((k:ℝ)+1))) ^ ((1:ℝ)/(k:ℝ)) = lam ^ ((1:ℝ)/((k:ℝ)+1)) := by
  rw [← Real.rpow_mul (le_of_lt hlam)]
  congr 1
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
  field_simp

lemma rpow_mu_div {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    lam ^ ((k:ℝ)/((k:ℝ)+1)) / lam = 1 / lam ^ ((1:ℝ)/((k:ℝ)+1)) := by
  rw [div_eq_mul_inv, one_div]
  rw [← Real.rpow_neg (le_of_lt hlam) ((1:ℝ)/((k:ℝ)+1))]
  rw [← Real.rpow_neg_one]
  rw [← Real.rpow_add hlam]
  congr 1
  have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
  field_simp
  ring

/-- The induction step (positive case): from the level-`k` bound derive the level-`k+1`
bound, assuming `φ^(k+1) ≥ lam`. -/
theorem vdc_step_pos (k : ℕ) (hk : 2 ≤ k) (C : ℝ) (hC : vdcBound k C)
    {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hφ : ContDiffOn ℝ (k+1) φ (Set.Icc a b))
    (hpos : ∀ t ∈ Set.Ioo a b, lam ≤ iteratedDeriv (k+1) φ t) :
    ‖∫ t in a..b, osc φ t‖ ≤ (2*C + 2) / lam ^ ((1:ℝ)/(k+1)) := by
  have hCpos : 0 < C := hC.1
  have hCbound : ∀ {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} {lam : ℝ}, 0 < lam →
      ContDiffOn ℝ k φ (Set.Icc a b) →
      (∀ t ∈ Set.Ioo a b, lam ≤ |iteratedDeriv k φ t|) →
      ‖∫ t in a..b, osc φ t‖ ≤ C / lam ^ ((1:ℝ)/k) := hC.2
  rcases eq_or_lt_of_le hab with hEq | hlt
  · subst hEq
    simp only [intervalIntegral.integral_same, norm_zero]
    exact div_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos hlam _))
  set μ : ℝ := lam ^ ((k:ℝ)/((k:ℝ)+1)) with hμdef
  have hμpos : 0 < μ := Real.rpow_pos_of_pos hlam _
  have hμpow : μ ^ ((1:ℝ)/(k:ℝ)) = lam ^ ((1:ℝ)/((k:ℝ)+1)) := rpow_mu_self hlam (by omega)
  have hμdiv : μ / lam = 1 / lam ^ ((1:ℝ)/((k:ℝ)+1)) := rpow_mu_div hlam k
  have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hlt
  set g : ℝ → ℝ := fun x => iteratedDerivWithin k φ (Set.Icc a b) x with hgdef
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    rw [hgdef]
    exact hφ.continuousOn_iteratedDerivWithin (by exact_mod_cast Nat.le_succ k) hU
  have hgdiff : DifferentiableOn ℝ g (Set.Ioo a b) := by
    rw [hgdef]
    exact (hφ.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self k) hU).mono
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hderivg : ∀ x ∈ Set.Ioo a b, deriv g x = iteratedDeriv (k+1) φ x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hnh : Set.Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have h1 : deriv g x = derivWithin g (Set.Icc a b) x := (derivWithin_of_mem_nhds hnh).symm
    have h2 : derivWithin g (Set.Icc a b) x
        = iteratedDerivWithin (k+1) φ (Set.Icc a b) x := by
      rw [hgdef, iteratedDerivWithin_succ]
    have h3 : iteratedDerivWithin (k+1) φ (Set.Icc a b) x = iteratedDeriv (k+1) φ x :=
      iteratedDerivWithin_eq_iteratedDeriv hU (hφ.contDiffAt hnh) hxIcc
    rw [h1, h2, h3]
  have hgr : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      lam * (y - x) ≤ g y - g x :=
    growth_of_deriv_bound hlt hgcont hgdiff (fun x hx => by rw [hderivg x hx]; exact hpos x hx)
  rcases Submission.SdtOscSplit.exists_band_split hab hμpos hlam g hgcont hgr with
    ⟨p, q, hap, hpq, hqb, hleft, hright, hlen⟩
  set f : ℝ → ℂ := fun t => osc φ t with hfdef
  have hosc_cont : ContinuousOn f (Set.Icc a b) := by
    rw [hfdef]
    have h1 : ContinuousOn (fun t : ℝ => Complex.I * (φ t : ℂ)) (Set.Icc a b) :=
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ.continuousOn)
    exact Complex.continuous_exp.comp_continuousOn h1
  have hsub_ap : Set.Icc a p ⊆ Set.Icc a b := fun x hx =>
    ⟨hx.1, le_trans hx.2 (le_trans hpq hqb)⟩
  have hsub_pb : Set.Icc p b ⊆ Set.Icc a b := fun x hx => ⟨le_trans hap hx.1, hx.2⟩
  have hsub_pq : Set.Icc p q ⊆ Set.Icc a b := fun x hx => ⟨le_trans hap hx.1, le_trans hx.2 hqb⟩
  have hsub_qb : Set.Icc q b ⊆ Set.Icc a b := fun x hx => ⟨le_trans (le_trans hap hpq) hx.1, hx.2⟩
  have hfI_ap : IntervalIntegrable f volume a p := by
    have hc : ContinuousOn f (Set.uIcc a p) := by
      rw [Set.uIcc_of_le hap]; exact hosc_cont.mono hsub_ap
    exact hc.intervalIntegrable
  have hfI_pb : IntervalIntegrable f volume p b := by
    have hc : ContinuousOn f (Set.uIcc p b) := by
      rw [Set.uIcc_of_le (le_trans hpq hqb)]; exact hosc_cont.mono hsub_pb
    exact hc.intervalIntegrable
  have hfI_pq : IntervalIntegrable f volume p q := by
    have hc : ContinuousOn f (Set.uIcc p q) := by
      rw [Set.uIcc_of_le hpq]; exact hosc_cont.mono hsub_pq
    exact hc.intervalIntegrable
  have hfI_qb : IntervalIntegrable f volume q b := by
    have hc : ContinuousOn f (Set.uIcc q b) := by
      rw [Set.uIcc_of_le hqb]; exact hosc_cont.mono hsub_qb
    exact hc.intervalIntegrable
  have hsplit : (∫ t in a..b, f t)
      = (∫ t in a..p, f t) + ((∫ t in p..q, f t) + (∫ t in q..b, f t)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hfI_ap hfI_pb,
        ← intervalIntegral.integral_add_adjacent_intervals hfI_pq hfI_qb]
  have hLeft : ∀ t ∈ Set.Ioo a p, μ ≤ |iteratedDeriv k φ t| := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b :=
      ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (le_trans hpq hqb)⟩
    have hnh : Set.Icc a b ∈ 𝓝 t :=
      Icc_mem_nhds ht.1 (lt_of_lt_of_le ht.2 (le_trans hpq hqb))
    have hgt : g t = iteratedDeriv k φ t := by
      rw [hgdef]
      exact iteratedDerivWithin_eq_iteratedDeriv hU ((hφ.contDiffAt hnh).of_le (by exact_mod_cast Nat.le_succ k)) htIcc
    have h1 : iteratedDeriv k φ t ≤ -μ := by rw [← hgt]; exact hleft t ht
    rw [abs_of_neg (by linarith)]
    linarith
  have hRight : ∀ t ∈ Set.Ioo q b, μ ≤ |iteratedDeriv k φ t| := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b :=
      ⟨le_trans (le_trans hap hpq) (le_of_lt ht.1), le_of_lt ht.2⟩
    have hnh : Set.Icc a b ∈ 𝓝 t :=
      Icc_mem_nhds (lt_of_le_of_lt (le_trans hap hpq) ht.1) ht.2
    have hgt : g t = iteratedDeriv k φ t := by
      rw [hgdef]
      exact iteratedDerivWithin_eq_iteratedDeriv hU ((hφ.contDiffAt hnh).of_le (by exact_mod_cast Nat.le_succ k)) htIcc
    have h1 : μ ≤ iteratedDeriv k φ t := by rw [← hgt]; exact hright t ht
    rw [abs_of_nonneg (by linarith)]
    exact h1
  have hIHa : ‖∫ t in a..p, f t‖ ≤ C / lam ^ ((1:ℝ)/((k:ℝ)+1)) := by
    have := hCbound (a := a) (b := p) hap (φ := φ) (lam := μ) hμpos ((hφ.mono hsub_ap).of_le (by exact_mod_cast Nat.le_succ k)) hLeft
    rwa [hμpow] at this
  have hIHb : ‖∫ t in q..b, f t‖ ≤ C / lam ^ ((1:ℝ)/((k:ℝ)+1)) := by
    have := hCbound (a := q) (b := b) hqb (φ := φ) (lam := μ) hμpos ((hφ.mono hsub_qb).of_le (by exact_mod_cast Nat.le_succ k)) hRight
    rwa [hμpow] at this
  have hmid : ‖∫ t in p..q, f t‖ ≤ 2 / lam ^ ((1:ℝ)/((k:ℝ)+1)) := by
    have h1 : ‖∫ t in p..q, f t‖ ≤ q - p := by
      calc ‖∫ t in p..q, f t‖ ≤ ∫ t in p..q, ‖f t‖ :=
              intervalIntegral.norm_integral_le_integral_norm hpq
        _ = ∫ t in p..q, (1:ℝ) := by
              apply intervalIntegral.integral_congr
              intro t ht
              rw [hfdef]; exact osc_norm φ t
        _ = q - p := by rw [intervalIntegral.integral_const]; simp
    have h2 : q - p ≤ 2 / lam ^ ((1:ℝ)/((k:ℝ)+1)) := by
      calc q - p ≤ 2 * μ / lam := hlen
        _ = 2 * (μ / lam) := by ring
        _ = 2 * (1 / lam ^ ((1:ℝ)/((k:ℝ)+1))) := by rw [hμdiv]
        _ = 2 / lam ^ ((1:ℝ)/((k:ℝ)+1)) := by ring
    linarith
  have hnorm : ‖∫ t in a..b, f t‖
      ≤ ‖∫ t in a..p, f t‖ + (‖∫ t in p..q, f t‖ + ‖∫ t in q..b, f t‖) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  calc ‖∫ t in a..b, f t‖
      ≤ ‖∫ t in a..p, f t‖ + (‖∫ t in p..q, f t‖ + ‖∫ t in q..b, f t‖) := hnorm
    _ ≤ C / lam ^ ((1:ℝ)/((k:ℝ)+1)) +
          (2 / lam ^ ((1:ℝ)/((k:ℝ)+1)) + C / lam ^ ((1:ℝ)/((k:ℝ)+1))) := by
          linarith [hIHa, hmid, hIHb]
    _ = (2*C + 2) / lam ^ ((1:ℝ)/((k:ℝ)+1)) := by ring_nf

end

end Commons.Analysis.Oscillatory

namespace Commons.Analysis.Oscillatory

noncomputable section

/-- The induction step for the van der Corput bound. -/
theorem vdc_step (k : ℕ) (hk : 2 ≤ k) (C : ℝ) (hC : vdcBound k C) :
    vdcBound (k+1) (2*C + 2) := by
  refine ⟨by linarith [hC.1], ?_⟩
  intro a b hab φ lam hlam hφ hh
  rw [show ((k+1 : ℕ) : ℝ) = (k:ℝ) + 1 from by push_cast; ring]
  rcases eq_or_lt_of_le hab with hEq | hlt
  · subst hEq
    simp only [intervalIntegral.integral_same, norm_zero]
    exact div_nonneg (by linarith [hC.1]) (le_of_lt (Real.rpow_pos_of_pos hlam _))
  have hcont : ContinuousOn (iteratedDeriv (k+1) φ) (Set.Ioo a b) :=
    continuousOn_iteratedDeriv_of_isOpen isOpen_Ioo (by norm_num)
      (hφ.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  rcases sign_const_Ioo hcont hlam hh with hpos | hneg
  · exact vdc_step_pos k hk C hC hab hlam hφ hpos
  · have hφ' : ContDiffOn ℝ (k+1) (fun x => -φ x) (Set.Icc a b) := hφ.neg
    have hpos' : ∀ t ∈ Set.Ioo a b, lam ≤ iteratedDeriv (k+1) (fun x => -φ x) t := by
      intro t ht
      rw [iteratedDeriv_fun_neg]
      have := hneg t ht
      linarith
    have hb := vdc_step_pos k hk C hC hab hlam hφ' hpos'
    have heqnorm : ‖∫ t in a..b, osc φ t‖ = ‖∫ t in a..b, osc (fun x => -φ x) t‖ := by
      have hcj : (∫ t in a..b, osc (fun x => -φ x) t) = conj (∫ t in a..b, osc φ t) := by
        rw [show (fun t => osc (fun x => -φ x) t) = (fun t => conj (osc φ t)) from
          funext (fun t => osc_neg_conj φ t)]
        exact intervalIntegral.intervalIntegral_conj
      rw [hcj, Complex.norm_conj]
    rw [heqnorm]
    exact hb

/-- The van der Corput bound holds for every `k ≥ 2` (with `Ioo` hypothesis). -/
theorem vdc_exists (k : ℕ) (hk : 2 ≤ k) : ∃ C, vdcBound k C :=
  Nat.le_induction vdc_two (fun k hk ih => by
    obtain ⟨C, hC⟩ := ih
    exact ⟨2*C+2, vdc_step k hk C hC⟩) k hk

end

end Commons.Analysis.Oscillatory

namespace Commons.Analysis.Oscillatory

noncomputable section

/-- **van der Corput's lemma** (oscillatory integral form): if `φ` is `k` times
continuously differentiable on `[a,b]` (with `k ≥ 2`) and `|φ^(k)| ≥ lam > 0`
there, then the oscillatory integral of `exp(I φ)` over `[a,b]` is
`O(lam^(-1/k))`, with a constant depending only on `k`. -/
theorem van_der_corput_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} {lam : ℝ}, 0 < lam →
      ContDiffOn ℝ k φ (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, lam ≤ |iteratedDeriv k φ t|) →
      ‖∫ t in a..b, Complex.exp (Complex.I * φ t)‖ ≤ C / lam ^ ((1 : ℝ) / k) := by
  obtain ⟨C, hC⟩ := vdc_exists k hk
  refine ⟨C, hC.1, ?_⟩
  intro a b hab φ lam hlam hφ hh
  exact hC.2 hab hlam hφ (fun t ht => hh t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

end

end Commons.Analysis.Oscillatory
