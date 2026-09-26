import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.HFN.HalfFunnel.lowBadAux
import Submission.Work.HFN.HalfFunnel.lowBad_Aexp_tail
import Submission.Work.HFN.HalfFunnel.lowBad_Tspike_bound
import Submission.Work.Asymptotics.Kaxis_Swindow_bound
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.KaxisMid.Classify
import Submission.Work.Asymptotics.Kaxis_principal_part_bound

/-!
# The pole-subtracted kernel on the bad lines, in the region form

This file proves `Work.Asymptotics.HalfFunnel.lowBad_kernel_spike_b`: for `d ∈ {8, 24}` and every
kernel datum `ℓ`, the difference between the CKMRV kernel along the contour and its translate
pole `tpole` is bounded, uniformly over the region

  `{τ ∈ ℍ : |Re τ| < 1, 1/2 ≤ Im τ ≤ 2, |Re τ| > 3/4}`  and  `0 < t ≤ lowT = 3`.

That region is exactly `lowBadSet` (`lowBadSet_of_region`), so the statement is the "region form"
of the decomposition usually stated for `lowBadSet`; the hypotheses are spelled out because the
caller does not have `lowBadSet τ` available syntactically.

The proof splits at the spike window `|t - Im τ| ≤ 1/8`:

* inside the window, `Work.Asymptotics.HalfFunnel.lowBad_Tspike_bound` bounds `K - tpole` directly;
* outside, `K` itself is bounded and `‖tpole‖ ≤ 1/(2π |t - Im τ|) ≤ 4/π`.

The bound on `K` off the window (`offspike_bound`) is the content of the file.  On `lowBadSet` the
contour `z = it` meets the `SL(2,ℤ)`-orbit of `τ` only for `Re τ = ±1`, at the two heights
`t = Im τ` (the translate pole, excluded by `|t - Im τ| ≥ 1/8`) and `t = (Im τ)⁻¹` (the *removable*
`S`-branch).  Accordingly:

* if `t` is away from `(Im τ)⁻¹` or `τ` is away from the bad lines, the coincidence divisor is
  bounded below on the resulting *compact* set of parameters, and joint continuity of the kernel
  off the divisor (`continuousOn_Kfun_clean`) gives the bound (`offspike_far_bound`);
* in the `S`-window, `K` is bounded by the local theorem `Work.Asymptotics.Kaxis_Swindow_bound`,
  which is uniform on the compact set of centres with `|y⁻¹ - y| ≥ 1/16`; a finite subcover and
  the min/max of the local constants (`swindow_uniform`) make it uniform globally;
* for small `t`, the cusp bound `Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded` applies.
-/

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory UpperHalfPlane

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-! ## 1. The region of the statement -/

/-- The hypotheses of `lowBad_kernel_spike_b` on `τ` produce a point of `lowBadSet`. -/
lemma lowBadSet_of_region {τ : ℍ} (hre : |τ.re| < 1) (him1 : (1 : ℝ) / 2 ≤ τ.im)
    (him2 : τ.im ≤ 2) (h74 : 3 / 4 < |τ.re|) : lowBadSet τ := by
  obtain ⟨hr1, hr2⟩ := abs_lt.mp hre
  have hne1 : τ.re ≠ 1 / 2 := by intro h; rw [h] at h74; norm_num at h74
  have hne2 : τ.re ≠ -(1 / 2) := by intro h; rw [h] at h74; norm_num at h74
  have hdisj : 3 / 4 < τ.re ∨ τ.re < -(3 / 4) := by
    rcases lt_abs.mp h74 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  refine ⟨⟨hr1, hr2, ?_, ?_⟩, him1, him2, hdisj⟩
  · have hsq : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hpos : (0 : ℝ) < (τ.re - 1 / 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne1)
    have him : (1 / 2 : ℝ) ^ 2 ≤ τ.im ^ 2 := by nlinarith
    have hlt : (1 / 2 : ℝ) ^ 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by rw [hsq]; linarith
    nlinarith [norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))]
  · have hsq : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hpos : (0 : ℝ) < (τ.re + 1 / 2) ^ 2 :=
      sq_pos_of_ne_zero (by intro h; exact hne2 (by linarith))
    have him : (1 / 2 : ℝ) ^ 2 ≤ τ.im ^ 2 := by nlinarith
    have hlt : (1 / 2 : ℝ) ^ 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by rw [hsq]; linarith
    nlinarith [norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ))]

/-! ## 2. The compact parameter box -/

/-- The closed box of parameters containing the closure of `lowBadSet`. -/
def kbox : Set ℍ := {τ : ℍ | 3 / 4 ≤ |τ.re| ∧ |τ.re| ≤ 1 ∧ 1 / 2 ≤ τ.im ∧ τ.im ≤ 2}

lemma mem_kbox {τ : ℍ} (hτ : lowBadSet τ) : τ ∈ kbox := by
  obtain ⟨hr1, hr2⟩ := lowBadSet_re_abs_bounds hτ
  obtain ⟨him1, him2⟩ := lowBadSet_im_bounds hτ
  exact ⟨le_of_lt hr1, le_of_lt hr2, him1, him2⟩

lemma kbox_subset_badStrip : kbox ⊆ badStrip := by
  rintro τ ⟨-, hre1, him1, him2⟩
  exact ⟨him1, him2, hre1⟩

lemma isCompact_kbox : IsCompact kbox := by
  have hcl : IsClosed kbox := by
    have h1 : IsClosed {τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} :=
      isClosed_le continuous_const (continuous_abs.comp UpperHalfPlane.continuous_re)
    have h2 : IsClosed {τ : ℍ | |τ.re| ≤ (1 : ℝ)} :=
      isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
    have h3 : IsClosed {τ : ℍ | (1 / 2 : ℝ) ≤ τ.im} :=
      isClosed_le continuous_const UpperHalfPlane.continuous_im
    have h4 : IsClosed {τ : ℍ | τ.im ≤ (2 : ℝ)} :=
      isClosed_le UpperHalfPlane.continuous_im continuous_const
    have hset : kbox = ({τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} ∩ {τ : ℍ | |τ.re| ≤ (1 : ℝ)}) ∩
        ({τ : ℍ | (1 / 2 : ℝ) ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ (2 : ℝ)}) := by
      ext τ; simp only [kbox, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
    rw [hset]
    exact (h1.inter h2).inter (h3.inter h4)
  exact IsCompact.of_isClosed_subset isCompact_badStrip hcl kbox_subset_badStrip

/-! ## 3. Coincidences of the contour with the orbit: only at `Re τ = ±1` -/

/-- `tsign τ` is `±1`. -/
lemma tsign_eq_or (τ : ℍ) : tsign τ = 1 ∨ tsign τ = -1 := by
  unfold tsign; split <;> norm_num

/-- `|Re τ - tsign τ| = 1 - |Re τ|` for `3/4 ≤ |Re τ| ≤ 1`. -/
lemma abs_re_sub_tsign {τ : ℍ} (h1 : 3 / 4 ≤ |τ.re|) (h2 : |τ.re| ≤ 1) :
    |τ.re - tsign τ| = 1 - |τ.re| := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h2
  have hne : τ.re ≠ 0 := by intro h; rw [h, abs_zero] at h1; norm_num at h1
  rcases lt_or_gt_of_ne hne with h | h
  · have ha : |τ.re| = -τ.re := abs_of_neg h
    unfold tsign
    rw [if_neg (not_lt.mpr h.le), show τ.re - (-1) = τ.re + 1 by ring,
      abs_of_nonneg (by linarith), ha]
    ring
  · have ha : |τ.re| = τ.re := abs_of_pos h
    unfold tsign
    rw [if_pos h, show τ.re - 1 = -(1 - τ.re) by ring, abs_neg,
      abs_of_nonneg (by linarith), ha]

/-- The translate `τ - tsign τ` lies in CKMRV's fundamental domain `𝒟`. -/
lemma vadd_neg_tsign_mem_DomainD {τ : ℍ} (hre : 3 / 4 ≤ |τ.re|) (hre1 : |τ.re| ≤ 1)
    (him : 1 / 2 ≤ τ.im) : (-(tsign τ : ℝ)) +ᵥ τ ∈ Work.Asymptotics.DomainD := by
  have habs : |τ.re - tsign τ| ≤ 1 / 4 := by
    rw [abs_re_sub_tsign hre hre1]; linarith
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp habs
  set w : ℍ := (-(tsign τ : ℝ)) +ᵥ τ with hw
  have hwre : w.re = τ.re - tsign τ := by rw [hw, UpperHalfPlane.vadd_re]; ring
  have hwim : w.im = τ.im := by rw [hw, UpperHalfPlane.vadd_im]
  have hwrlo : -1 / 4 ≤ w.re := by rw [hwre]; linarith
  have hwrhi : w.re ≤ 1 / 4 := by rw [hwre]; linarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have hs : ‖(w : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (w.re - 1 / 2) ^ 2 + w.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hkey : (1 / 2 : ℝ) ^ 2 < (w.re - 1 / 2) ^ 2 + w.im ^ 2 := by
      have h' : w.re - 1 / 2 ≤ -1 / 4 := by linarith
      nlinarith [hwim, him, h', sq_nonneg (w.re - 1 / 2)]
    have hlt : (1 / 2 : ℝ) ^ 2 < ‖(w : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by rw [hs]; exact hkey
    nlinarith [norm_nonneg ((w : ℂ) - (1 / 2 : ℂ))]
  · have hs : ‖(w : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (w.re + 1 / 2) ^ 2 + w.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hkey : (1 / 2 : ℝ) ^ 2 < (w.re + 1 / 2) ^ 2 + w.im ^ 2 := by
      have h' : (1 / 4 : ℝ) ≤ w.re + 1 / 2 := by linarith
      nlinarith [hwim, him, h', sq_nonneg (w.re + 1 / 2)]
    have hlt : (1 / 2 : ℝ) ^ 2 < ‖(w : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by rw [hs]; exact hkey
    nlinarith [norm_nonneg ((w : ℂ) + (1 / 2 : ℂ))]

/-- **Coincidences on the contour force `Re τ = ±1`.**  For `τ` in the compact box and `t > 0`,
`j τ = j (it)` implies `Re τ = ±1`, and the height `t` is one of `Im τ`, `(Im τ)⁻¹`. -/
lemma j_eq_imagAxis_forces {τ : ℍ} (hre : 3 / 4 ≤ |τ.re|) (hre1 : |τ.re| ≤ 1)
    (him : 1 / 2 ≤ τ.im) {t : ℝ} (ht : 0 < t)
    (h : jInvariantFun τ = jInvariantFun (imagAxis t ht)) :
    (τ.re = 1 ∨ τ.re = -1) ∧ (t = τ.im ∨ t = (τ.im)⁻¹) := by
  set n : ℝ := tsign τ with hn
  set w : ℍ := (-(n : ℝ)) +ᵥ τ with hw
  have hwre : w.re = τ.re - n := by rw [hw, UpperHalfPlane.vadd_re]; ring
  have hwim : w.im = τ.im := by rw [hw, UpperHalfPlane.vadd_im]
  have hwD : w ∈ Work.Asymptotics.DomainD := by
    rw [hw, hn]
    exact vadd_neg_tsign_mem_DomainD hre hre1 him
  have hjw : jInvariantFun w = jInvariantFun τ := by
    rcases lt_or_ge 0 τ.re with hpos | hneg
    · have hn1 : n = 1 := by rw [hn]; unfold tsign; rw [if_pos hpos]
      rw [hw, hn1, show -(1 : ℝ) = (-1 : ℝ) by norm_num]
      have hh := KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
      rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ by rw [← vadd_assoc]; norm_num] at hh
      exact hh.symm
    · have hn1 : n = -1 := by rw [hn]; unfold tsign; rw [if_neg (not_lt.mpr hneg)]
      rw [hw, hn1, show -(-1 : ℝ) = (1 : ℝ) by norm_num]
      exact KernelFacts.jInvariantFun_vadd_one τ
  have hzre : ((imagAxis t ht : ℍ) : ℂ).re = 0 := by simp [imagAxis]
  have hzw : jInvariantFun w = jInvariantFun (imagAxis t ht) := by rw [hjw]; exact h
  have hn1 : n = 1 ∨ n = -1 := by rw [hn]; exact tsign_eq_or τ
  rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hwD hzre hzw with hzw' | hzS
  · -- `i t = τ - n`
    have hw0 : w.re = 0 := by
      have h2 : (imagAxis t ht).re = w.re := congrArg UpperHalfPlane.re hzw'
      rw [← UpperHalfPlane.coe_re, hzre] at h2
      exact h2.symm
    have htre : τ.re = n := by rw [hwre] at hw0; linarith
    have hres : τ.re = 1 ∨ τ.re = -1 := by
      rcases hn1 with h' | h' <;> rw [htre, h'] <;> simp
    have himw : t = τ.im := by
      have h2 : (imagAxis t ht).im = w.im := congrArg UpperHalfPlane.im hzw'
      rw [hwim] at h2
      simpa [imagAxis] using h2
    exact ⟨hres, Or.inl himw⟩
  · -- `i t = S (τ - n)`, hence `τ - n = i/t`
    have h2 : ((ModularGroup.S • w : ℍ) : ℂ) = (-(w : ℂ))⁻¹ := by
      rw [UpperHalfPlane.modular_S_smul]
    have h3 : (t : ℂ) * Complex.I = (-(w : ℂ))⁻¹ := by
      have h1 : ((imagAxis t ht : ℍ) : ℂ) = ((ModularGroup.S • w : ℍ) : ℂ) := by rw [hzS]
      have h4 : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
      rw [h4] at h1
      rw [h1, h2]
    have h4 : ((t : ℂ) * Complex.I)⁻¹ = -(w : ℂ) := by rw [h3, inv_inv]
    have h5 : (w : ℂ) = -(((t : ℂ) * Complex.I)⁻¹) := by rw [h4, neg_neg]
    have hwcoe2 : (w : ℂ) = Complex.I / (t : ℂ) := by
      rw [h5]
      field_simp
      rw [sq, Complex.I_mul_I]; ring
    have hI : Complex.I / (t : ℂ) = ((t)⁻¹ : ℝ) * Complex.I := by
      rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm]
    have hwre0 : w.re = 0 := by rw [← UpperHalfPlane.coe_re, hwcoe2, hI]; simp
    have hwim1 : w.im = t⁻¹ := by rw [← UpperHalfPlane.coe_im, hwcoe2, hI]; simp
    have htre : τ.re = n := by rw [hwre] at hwre0; linarith
    have hres' : τ.re = 1 ∨ τ.re = -1 := by
      rcases hn1 with h' | h' <;> rw [htre, h'] <;> simp
    have htim : t = (τ.im)⁻¹ := by
      have h2 : τ.im = t⁻¹ := by rw [← hwim, hwim1]
      rw [h2, inv_inv]
    exact ⟨hres', Or.inr htim⟩

/-! ## 4. The translate pole away from its window -/

/-- Off the spike window, the translate pole is bounded by `4/π`. -/
lemma norm_tpole_le_of_sep {τ : ℍ} {t : ℝ} (hsep : (1 / 8 : ℝ) ≤ |t - τ.im|) :
    ‖tpole τ t‖ ≤ 4 / Real.pi := by
  have hnum : ‖(tsign τ : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div]
    have h1 : ‖(tsign τ : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      rcases tsign_eq_or τ with h | h <;> rw [h] <;> norm_num
    have h2 : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [h1, h2]
  have hden : |t - τ.im| ≤ ‖((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))‖ := by
    have h1 := Complex.abs_im_le_norm ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))
    have h2 : (((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))).im = t - τ.im := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_im]
      ring
    rwa [h2] at h1
  rw [tpole, norm_div, hnum]
  have hpos : 0 < |t - τ.im| := lt_of_lt_of_le (by norm_num) hsep
  have h1 : (1 / (2 * Real.pi)) / ‖((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))‖
      ≤ (1 / (2 * Real.pi)) / |t - τ.im| :=
    div_le_div_of_nonneg_left (by positivity) hpos hden
  have h2 : (1 / (2 * Real.pi)) / |t - τ.im| ≤ 4 / Real.pi := by
    rw [div_le_iff₀ hpos]
    have h3 : (4 / Real.pi) * (1 / 8) ≤ (4 / Real.pi) * |t - τ.im| := by
      apply mul_le_mul_of_nonneg_left hsep; positivity
    have h4 : (4 / Real.pi) * (1 / 8) = 1 / (2 * Real.pi) := by
      field_simp; ring
    linarith [h3, h4.le, h4.ge]
  linarith [h1, h2]

/-! ## 5. The continuous contour point -/

/-- The continuous version `i · max t δc` of the contour point `i t`. -/
def caxis (δc : ℝ) (hδc : 0 < δc) (t : ℝ) : ℍ :=
  ⟨((max t δc : ℝ) : ℂ) * Complex.I, by
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
      mul_zero, add_zero]
    exact lt_of_lt_of_le hδc (le_max_right _ _)⟩

lemma caxis_re (δc : ℝ) (hδc : 0 < δc) (t : ℝ) : (caxis δc hδc t).re = 0 := by
  rw [← UpperHalfPlane.coe_re, caxis]; simp

lemma caxis_im (δc : ℝ) (hδc : 0 < δc) (t : ℝ) : (caxis δc hδc t).im = max t δc := by
  rw [← UpperHalfPlane.coe_im, caxis]
  simp [Complex.mul_im]

lemma caxis_eq_imagAxis {δc t : ℝ} (hδc : 0 < δc) (ht : δc ≤ t) :
    caxis δc hδc t = imagAxis t (lt_of_lt_of_le hδc ht) := by
  apply UpperHalfPlane.ext
  show ((max t δc : ℝ) : ℂ) * Complex.I = (t : ℂ) * Complex.I
  rw [max_eq_left ht]

lemma continuous_caxis (δc : ℝ) (hδc : 0 < δc) : Continuous (caxis δc hδc) := by
  rw [continuous_induced_rng (f := UpperHalfPlane.coe)]
  show Continuous (fun t : ℝ => (((max t δc : ℝ) : ℂ) * Complex.I))
  exact (Complex.continuous_ofReal.comp
    (continuous_max.comp (continuous_id.prodMk continuous_const))).mul continuous_const

/-! ## 6. Boundedness on a compact parameter set off the divisor -/

/-- On a compact set of parameters on which the contour point is never a coincidence and `t` is
bounded below, the kernel is bounded. -/
theorem compact_caxis_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {δc : ℝ} (hδc : 0 < δc) {P : Set (ℍ × ℝ)} (hPc : IsCompact P)
    (hPt : ∀ p ∈ P, δc ≤ p.2)
    (hne : ∀ p ∈ P, jInvariantFun p.1 ≠ jInvariantFun (caxis δc hδc p.2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ P, ‖Kaxis (Kfun ℓ d) p.1 p.2‖ ≤ C := by
  let g : ℍ × ℝ → ℍ × ℍ := fun p => (p.1, caxis δc hδc p.2)
  have hcont : Continuous g :=
    continuous_fst.prodMk ((continuous_caxis δc hδc).comp continuous_snd)
  have himg : IsCompact (g '' P) := hPc.image hcont
  have hsubimg : g '' P ⊆ {q : ℍ × ℍ | jInvariantFun q.1 ≠ jInvariantFun q.2} := by
    rintro q ⟨p, hp, rfl⟩
    exact hne p hp
  have hKc : ContinuousOn (fun q : ℍ × ℍ => Kfun ℓ d q.1 q.2) (g '' P) :=
    (continuousOn_Kfun_clean ℓ d hd).mono hsubimg
  obtain ⟨C, hC⟩ := himg.exists_bound_of_continuousOn hKc
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  have h1 : ‖Kfun ℓ d p.1 (caxis δc hδc p.2)‖ ≤ C := hC (g p) (Set.mem_image_of_mem g hp)
  have h2 : Kaxis (Kfun ℓ d) p.1 p.2 = Kfun ℓ d p.1 (caxis δc hδc p.2) := by
    rw [Kaxis, dif_pos (lt_of_lt_of_le hδc (hPt p hp))]
    congr 1
    exact (caxis_eq_imagAxis hδc (hPt p hp)).symm
  rw [h2]
  exact le_trans h1 (le_max_left _ _)

/-! ## 7. The cusp bound on `lowBadSet` -/

/-- For small `t` the kernel is bounded on the bad-line region. -/
theorem lowBad_cusp_bound' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ δc Cc : ℝ, 0 < δc ∧ 0 ≤ Cc ∧ ∀ (τ : ℍ) (t : ℝ),
      lowBadSet τ → 0 < t → t ≤ δc → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ Cc := by
  obtain ⟨δc, hδc, hb⟩ := Kaxis_cusp_of_bounded ℓ d hd (K := badStrip)
    isCompact_badStrip.isBounded
  obtain ⟨c, hc, hcb⟩ := hb 0 le_rfl
  refine ⟨δc, c, hδc, hc.le, fun τ t hτ ht htδ => ?_⟩
  have h := hcb τ t (mem_badStrip hτ) ht htδ
  rwa [Real.rpow_zero, mul_one] at h

/-! ## 8. The far part: away from the `S`-window or from the bad lines -/

/-- Off the translate-pole window, the kernel is bounded as soon as the contour point is separated
from the `S`-conjugate height `(Im τ)⁻¹`, or `τ` is separated from the bad lines. -/
theorem offspike_far_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {δc δU ηU : ℝ} (hδc : 0 < δc) (hδU : 0 < δU) (hηU : 0 < ηU) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ), τ ∈ kbox → δc ≤ t → t ≤ lowT →
      (1 / 8 : ℝ) ≤ |t - τ.im| → (ηU ≤ |t - (τ.im)⁻¹| ∨ δU ≤ 1 - |τ.re|) →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  have hIm : Continuous (fun p : ℍ × ℝ => p.1.im) :=
    UpperHalfPlane.continuous_im.comp continuous_fst
  have hRe : Continuous (fun p : ℍ × ℝ => p.1.re) :=
    UpperHalfPlane.continuous_re.comp continuous_fst
  have hinv : Continuous (fun p : ℍ × ℝ => (p.1.im)⁻¹) :=
    hIm.inv₀ (fun p => ne_of_gt p.1.im_pos)
  set P : Set (ℍ × ℝ) := ((kbox ×ˢ Set.Icc δc lowT) ∩
      {p : ℍ × ℝ | (1 / 8 : ℝ) ≤ |p.2 - p.1.im|}) ∩
      ({p : ℍ × ℝ | ηU ≤ |p.2 - (p.1.im)⁻¹|} ∪ {p : ℍ × ℝ | δU ≤ 1 - |p.1.re|}) with hP
  have hPc : IsCompact P := by
    rw [hP]
    exact ((isCompact_kbox.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp (continuous_snd.sub hIm)))).inter_right
      ((isClosed_le continuous_const (continuous_abs.comp (continuous_snd.sub hinv))).union
        (isClosed_le continuous_const (continuous_const.sub (continuous_abs.comp hRe))))
  have hPt : ∀ p ∈ P, δc ≤ p.2 := by
    intro p hp
    rw [hP] at hp
    exact hp.1.1.2.1
  have hne : ∀ p ∈ P, jInvariantFun p.1 ≠ jInvariantFun (caxis δc hδc p.2) := by
    intro p hp hcontra
    rw [hP] at hp
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_prod] at hp
    obtain ⟨⟨⟨hbox, htIcc⟩, hmargin⟩, hdisj⟩ := hp
    have hle : δc ≤ p.2 := htIcc.1
    have htpos : 0 < p.2 := lt_of_lt_of_le hδc hle
    have hca : caxis δc hδc p.2 = imagAxis p.2 htpos := caxis_eq_imagAxis hδc hle
    have hj : jInvariantFun p.1 = jInvariantFun (imagAxis p.2 htpos) := by
      rw [← hca]; exact hcontra
    have hres := j_eq_imagAxis_forces hbox.1 hbox.2.1 hbox.2.2.1 htpos hj
    rcases hdisj with hd | hd
    · rcases hres.2 with h | h
      · rw [h] at hmargin
        simp at hmargin
        norm_num at hmargin
      · rw [h] at hd
        simp at hd
        linarith [hηU]
    · rcases hres.1 with h | h
      · rw [h] at hd
        simp at hd
        linarith [hδU]
      · rw [h] at hd
        simp at hd
        linarith [hδU]
  obtain ⟨C, hC, hb⟩ := compact_caxis_bound ℓ d hd hδc hPc hPt hne
  refine ⟨C, hC, fun τ t hbox ht1 ht2 hmargin hdisj => hb (τ, t) ?_⟩
  rw [hP]
  exact ⟨⟨⟨hbox, ht1, ht2⟩, hmargin⟩, hdisj⟩

/-! ## 9. The principal part is bounded off the window -/

/-- The principal part `(-i)(n/2π)/((t - Im τ) + i(Re τ - n))` is bounded by `4/π` when
`|t - Im τ| ≥ 1/8`. -/
lemma norm_pp_le {τ : ℍ} {t : ℝ} {n : ℤ} (hn : n = 1 ∨ n = -1)
    (hsep : (1 / 8 : ℝ) ≤ |t - τ.im|) :
    ‖(-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹‖
      ≤ 4 / Real.pi := by
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_inv]
  have hn1 : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
  have hπ : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hnum : ‖(n : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, hn1, hπ]
  rw [hnum]
  have hz : |t - τ.im| ≤ ‖((t : ℂ) - (τ.im : ℂ)
      + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))‖ := by
    have h1 := Complex.abs_re_le_norm
      ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))
    have h2 : ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ)).re
        = t - τ.im := by
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rwa [h2] at h1
  have hpos : 0 < |t - τ.im| := lt_of_lt_of_le (by norm_num) hsep
  have h1 : (‖((t : ℂ) - (τ.im : ℂ)
      + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))‖)⁻¹ ≤ (|t - τ.im|)⁻¹ :=
    inv_anti₀ hpos hz
  have h2 : (|t - τ.im|)⁻¹ ≤ 8 := by
    rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 8)]
    linarith
  calc (1 / (2 * Real.pi)) * (‖((t : ℂ) - (τ.im : ℂ)
        + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))‖)⁻¹
      ≤ (1 / (2 * Real.pi)) * (|t - τ.im|)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * 8 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 4 / Real.pi := by field_simp; norm_num

/-! ## 10. The `S`-window, uniformly on the compact set of centres -/

/-- The uniform `S`-window bound.  On the region where `|(Im τ)⁻¹ - Im τ| ≥ 1/16` (i.e. the
centre `Im τ` lies in a compact set avoiding the elliptic point `1`), where the contour point is
within the local `S`-window of height `(Im τ)⁻¹`, and where `τ` is close to the bad lines, the
kernel is bounded by the maximum of the local constants plus the bound `4/π` on the principal
part. -/
theorem swindow_uniform (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ δU ηU CU : ℝ, 0 < δU ∧ 0 < ηU ∧ 0 ≤ CU ∧ ηU ≤ 1 / 16 ∧
      ∀ (τ : ℍ) (t : ℝ), lowBadSet τ → 0 < t → (1 / 16 : ℝ) ≤ |(τ.im)⁻¹ - τ.im| →
        |t - (τ.im)⁻¹| < ηU → 1 - |τ.re| < δU → (1 / 8 : ℝ) ≤ |t - τ.im| →
        ‖Kaxis (Kfun ℓ d) τ t‖ ≤ CU + 4 / Real.pi := by
  have hloc : ∀ y : ℝ, 0 < y → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (τ : ℍ) (n : ℤ) (t η : ℝ) (ht : 0 < t), (n = 1 ∨ n = -1) →
        |τ.re - (n : ℝ)| < δ → |τ.im - y| < δ → 0 < η → η ≤ δ →
        |t - (τ.im)⁻¹| < η → η ≤ |t - τ.im| →
        jInvariantFun τ ≠ jInvariantFun (imagAxis t ht) →
        ‖Kaxis (Kfun ℓ d) τ t - (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
          ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹‖ ≤ C :=
    fun y hy => Kaxis_Swindow_bound ℓ d hd hy
  choose δf Cf hrest using hloc
  have hδf : ∀ y (hy : 0 < y), 0 < δf y hy := fun y hy => (hrest y hy).1
  have hCf : ∀ y (hy : 0 < y), 0 ≤ Cf y hy := fun y hy => (hrest y hy).2.1
  have hfbd : ∀ y (hy : 0 < y) (τ : ℍ) (n : ℤ) (t η : ℝ) (ht : 0 < t),
      (n = 1 ∨ n = -1) → |τ.re - (n : ℝ)| < δf y hy → |τ.im - y| < δf y hy →
      0 < η → η ≤ δf y hy → |t - (τ.im)⁻¹| < η → η ≤ |t - τ.im| →
      jInvariantFun τ ≠ jInvariantFun (imagAxis t ht) →
      ‖Kaxis (Kfun ℓ d) τ t - (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹‖ ≤ Cf y hy :=
    fun y hy => (hrest y hy).2.2
  -- the compact set of admissible centres
  set Cset : Set ℝ := {y : ℝ | 1 / 2 ≤ y ∧ y ≤ 2 ∧ y ^ 2 / 256 ≤ (y ^ 2 - 1) ^ 2} with hCset
  have hCset_closed : IsClosed Cset := by
    have hset : Cset = ({y : ℝ | 1 / 2 ≤ y} ∩ {y : ℝ | y ≤ 2}) ∩
        {y : ℝ | y ^ 2 / 256 ≤ (y ^ 2 - 1) ^ 2} := by
      rw [hCset]; ext y; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
    rw [hset]
    exact ((isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_id continuous_const)).inter
      (isClosed_le (by fun_prop) (by fun_prop))
  have hCset_sub : Cset ⊆ Set.Icc (1 / 2 : ℝ) 2 := fun y hy => by rw [hCset] at hy; exact ⟨hy.1, hy.2.1⟩
  have hCset_compact : IsCompact Cset :=
    IsCompact.of_isClosed_subset isCompact_Icc hCset_closed hCset_sub
  have hCset_abs : ∀ {y : ℝ}, y ∈ Cset → (1 / 16 : ℝ) ≤ |y⁻¹ - y| := by
    intro y hy
    rw [hCset] at hy
    obtain ⟨hy1, -, hy3⟩ := hy
    have hypos : 0 < y := by linarith
    have h1 : (y / 16) ^ 2 ≤ (y ^ 2 - 1) ^ 2 := by
      have h2 : y ^ 2 / 256 = (y / 16) ^ 2 := by ring
      rw [h2] at hy3; exact hy3
    have h3 : |y / 16| ≤ |y ^ 2 - 1| := sq_le_sq.mp h1
    have h4 : y / 16 ≤ |y ^ 2 - 1| := by
      rwa [abs_of_nonneg (by linarith)] at h3
    have h5 : |y⁻¹ - y| = |y ^ 2 - 1| / y := by
      have h6 : y⁻¹ - y = (1 - y ^ 2) / y := by field_simp
      rw [h6, abs_div, abs_of_pos hypos, abs_sub_comm]
    rw [h5, le_div_iff₀ hypos]
    linarith
  have hpoly_of_abs : ∀ {y : ℝ}, 0 < y → (1 / 16 : ℝ) ≤ |y⁻¹ - y| →
      y ^ 2 / 256 ≤ (y ^ 2 - 1) ^ 2 := by
    intro y hypos hy
    have h5 : |y⁻¹ - y| = |y ^ 2 - 1| / y := by
      have h6 : y⁻¹ - y = (1 - y ^ 2) / y := by field_simp
      rw [h6, abs_div, abs_of_pos hypos, abs_sub_comm]
    rw [h5] at hy
    have h1 : y / 16 ≤ |y ^ 2 - 1| := by
      rw [le_div_iff₀ hypos] at hy
      linarith
    have h2 : |y / 16| ≤ |y ^ 2 - 1| := by rwa [abs_of_nonneg (by linarith)]
    have h3 := sq_le_sq.mpr h2
    have h4 : (y / 16) ^ 2 = y ^ 2 / 256 := by ring
    rw [h4] at h3
    exact h3
  -- a finite subcover by the local windows
  have hcover : Cset ⊆ ⋃ y : {y : ℝ // 0 < y},
      Set.Ioo (y.1 - δf y.1 y.2 / 2) (y.1 + δf y.1 y.2 / 2) := by
    intro y hy
    rw [hCset] at hy
    have hypos : 0 < y := by linarith [hy.1]
    refine Set.mem_iUnion.mpr ⟨⟨y, hypos⟩, ?_⟩
    rw [Set.mem_Ioo]
    have h := hδf y hypos
    constructor <;> linarith
  obtain ⟨F, hF⟩ := hCset_compact.elim_finite_subcover
    (fun y : {y : ℝ // 0 < y} => Set.Ioo (y.1 - δf y.1 y.2 / 2) (y.1 + δf y.1 y.2 / 2))
    (fun _ => isOpen_Ioo) hcover
  have h2mem : (2 : ℝ) ∈ Cset := by rw [hCset]; norm_num
  have hFne : F.Nonempty := by
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hF h2mem)
    obtain ⟨hyF, -⟩ := Set.mem_iUnion.mp hy
    exact ⟨y, hyF⟩
  set δU : ℝ := F.inf' hFne (fun y => δf y.1 y.2 / 2) with hδU
  set CU : ℝ := F.sup' hFne (fun y => Cf y.1 y.2) with hCU
  have hδUpos : 0 < δU := by
    rw [hδU, Finset.lt_inf'_iff hFne]
    intro y _
    have h := hδf y.1 y.2
    linarith
  have hCUnn : 0 ≤ CU := by
    rw [hCU]
    obtain ⟨y, hyF⟩ := hFne
    exact le_trans (hCf y.1 y.2) (Finset.le_sup' (f := fun y : {y : ℝ // 0 < y} => Cf y.1 y.2) hyF)
  refine ⟨δU, min δU (1 / 16), CU, hδUpos, lt_min hδUpos (by norm_num), hCUnn,
    min_le_right _ _, ?_⟩
  intro τ t hτ ht habs hnear hslack hsep
  have him1 : (1 / 2 : ℝ) ≤ τ.im := hτ.2.1
  have himpos : 0 < τ.im := lt_of_lt_of_le (by norm_num) him1
  have hyC : τ.im ∈ Cset := by
    rw [hCset]
    exact ⟨him1, hτ.2.2.1, hpoly_of_abs himpos habs⟩
  obtain ⟨yc, hyc⟩ := Set.mem_iUnion.mp (hF hyC)
  obtain ⟨hycF, hycU⟩ := Set.mem_iUnion.mp hyc
  rw [Set.mem_Ioo] at hycU
  have hycpos : 0 < yc.1 := yc.2
  have hδU_le : δU ≤ δf yc.1 yc.2 := by
    rw [hδU]
    have h1 : F.inf' hFne (fun y => δf y.1 y.2 / 2) ≤ δf yc.1 yc.2 / 2 :=
      Finset.inf'_le (f := fun y : {y : ℝ // 0 < y} => δf y.1 y.2 / 2) hycF
    linarith
  have hCU_le : Cf yc.1 yc.2 ≤ CU := by
    rw [hCU]
    exact Finset.le_sup' (f := fun y : {y : ℝ // 0 < y} => Cf y.1 y.2) hycF
  have him_yc : |τ.im - yc.1| < δf yc.1 yc.2 := by
    have h1 : τ.im - yc.1 < δf yc.1 yc.2 / 2 := by linarith [hycU.2]
    have h2 : -(δf yc.1 yc.2 / 2) < τ.im - yc.1 := by linarith [hycU.1]
    rw [abs_lt]
    constructor <;> linarith
  -- the integer `n = ±1` with `(n : ℝ) = tsign τ`
  obtain ⟨n, hn1, hncast⟩ : ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ (n : ℝ) = tsign τ := by
    rcases tsign_eq_or τ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩
  have hre34 : (3 / 4 : ℝ) ≤ |τ.re| := le_of_lt (lowBadSet_re_abs_bounds hτ).1
  have hre1 : |τ.re| ≤ 1 := le_of_lt (lowBadSet_re_abs_bounds hτ).2
  have hre_n : |τ.re - (n : ℝ)| < δf yc.1 yc.2 := by
    have h1 : |τ.re - tsign τ| = 1 - |τ.re| := abs_re_sub_tsign hre34 hre1
    have h2 : τ.re - (n : ℝ) = τ.re - tsign τ := by rw [hncast]
    rw [h2, h1]
    linarith [hslack, hδU_le]
  have hjne : jInvariantFun τ ≠ jInvariantFun (imagAxis t ht) := by
    intro hcon
    have hlt : |τ.re| < 1 := (lowBadSet_re_abs_bounds hτ).2
    have hres := j_eq_imagAxis_forces hre34 hre1 him1 ht hcon
    rcases hres.1 with h | h <;> rw [h] at hlt <;> norm_num at hlt
  have hηU : (0 : ℝ) < min δU (1 / 16) := lt_min hδUpos (by norm_num)
  have hηUδ : min δU (1 / 16) ≤ δf yc.1 yc.2 := le_trans (min_le_left _ _) hδU_le
  have hηU16 : min δU (1 / 16) ≤ (1 / 16 : ℝ) := min_le_right _ _
  have hηsep : min δU (1 / 16) ≤ |t - τ.im| :=
    le_trans hηU16 (le_trans (by norm_num) hsep)
  have hloc_apply := hfbd yc.1 yc.2 τ n t (min δU (1 / 16)) ht hn1 hre_n him_yc hηU
    hηUδ hnear hηsep hjne
  have hpp := norm_pp_le (τ := τ) (t := t) hn1 hsep
  have htri : ‖Kaxis (Kfun ℓ d) τ t‖ ≤
      ‖Kaxis (Kfun ℓ d) τ t - (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹‖
      + ‖(-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
        ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹‖ := by
    have h := norm_add_le (Kaxis (Kfun ℓ d) τ t -
        (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
          ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹)
      ((-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
          ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹)
    rwa [sub_add_cancel] at h
  linarith [htri, hloc_apply, hpp, hCU_le]

/-! ## 11. Boundedness off the spike window -/

/-- Off the spike window `|t - Im τ| ≤ 1/8` the kernel is bounded on the bad-line region. -/
theorem offspike_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (t : ℝ),
      lowBadSet τ → 0 < t → t ≤ lowT → (1 / 8 : ℝ) ≤ |t - τ.im| →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨δc, Cc, hδc, hCc, hcusp⟩ := lowBad_cusp_bound' ℓ d hd
  obtain ⟨δU, ηU, CU, hδU, hηU, hCU, hηU16, hswin⟩ := swindow_uniform ℓ d hd
  obtain ⟨Cfar, hCfar, hfar⟩ := offspike_far_bound ℓ d hd hδc hδU hηU
  refine ⟨max Cc (max (CU + 4 / Real.pi) Cfar), ?_, fun τ t hτ ht htT hsep => ?_⟩
  · exact le_trans hCc (le_max_left _ _)
  · by_cases htc : t ≤ δc
    · exact le_trans (hcusp τ t hτ ht htc) (le_max_left _ _)
    · have htδc : δc ≤ t := le_of_lt (not_le.mp htc)
      have htk : τ ∈ kbox := mem_kbox hτ
      by_cases hfar1 : ηU ≤ |t - (τ.im)⁻¹|
      · exact le_trans (hfar τ t htk htδc htT hsep (Or.inl hfar1))
          (le_trans (le_max_right _ _) (le_max_right _ _))
      · rw [not_le] at hfar1
        by_cases hfar2 : δU ≤ 1 - |τ.re|
        · exact le_trans (hfar τ t htk htδc htT hsep (Or.inr hfar2))
            (le_trans (le_max_right _ _) (le_max_right _ _))
        · rw [not_le] at hfar2
          have hy : (1 / 16 : ℝ) ≤ |(τ.im)⁻¹ - τ.im| := by
            have h3 : |t - τ.im| ≤ |t - (τ.im)⁻¹| + |(τ.im)⁻¹ - τ.im| := by
              have h4 : t - τ.im = (t - (τ.im)⁻¹) + ((τ.im)⁻¹ - τ.im) := by ring
              calc |t - τ.im| = |(t - (τ.im)⁻¹) + ((τ.im)⁻¹ - τ.im)| := by rw [h4]
                _ ≤ _ := abs_add_le _ _
            linarith [h3, hsep, hfar1, hηU16]
          exact le_trans (hswin τ t hτ ht hy hfar1 hfar2 hsep)
            (le_trans (le_max_left _ _) (le_max_right _ _))

/-! ## 12. The main theorem -/

theorem lowBad_kernel_spike_b (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      |τ.re| < 1 → (1 : ℝ) / 2 ≤ τ.im → τ.im ≤ 2 → 3 / 4 < |τ.re| → 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ C := by
  obtain ⟨Csp, hCsp, hsp⟩ := lowBad_Tspike_bound ℓ d hd
  obtain ⟨Coff, hCoff, hoff⟩ := offspike_bound ℓ d hd
  refine ⟨max Csp (Coff + 4 / Real.pi), ?_, fun τ t hre him1 him2 h74 ht htT => ?_⟩
  · exact le_trans hCsp (le_max_left _ _)
  · have hτ : lowBadSet τ := lowBadSet_of_region hre him1 him2 h74
    by_cases hwin : |t - τ.im| ≤ 1 / 8
    · exact le_trans (hsp τ t hτ ht htT hwin) (le_max_left _ _)
    · have hoffn : (1 / 8 : ℝ) ≤ |t - τ.im| := le_of_lt (not_le.mp hwin)
      have hb := hoff τ t hτ ht htT hoffn
      have hp := norm_tpole_le_of_sep (τ := τ) (t := t) hoffn
      refine le_trans (le_trans (norm_sub_le _ _) (add_le_add hb hp)) ?_
      exact le_max_right _ _

end Work.HFN.HalfFunnel
