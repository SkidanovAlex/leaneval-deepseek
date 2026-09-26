import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.HFN.HalfFunnel.lowBad_Aexp_tail
import Submission.Work.Asymptotics.KaxisMid.Main
import Submission.Work.Asymptotics.KaxisMid.exists_local_bound_coincidence
import Submission.Work.Asymptotics.KaxisMid.Classify
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Residues.KPlusClear_TS
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Residues.AfunMinus_neg_one
import Submission.Work.Asymptotics.Kaxis_Swindow_bound
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.continuousOn_Kfun_clean

set_option maxHeartbeats 1000000

/-!
# Boundedness of the CKMRV kernel on the bad-line region, away from the spike

This file proves `Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux`.

On `lowBadSet` the parameter `τ` lies in the fundamental domain `𝒟` (`|Re τ| > 3/4`,
`1/2 ≤ Im τ ≤ 2`), and the contour point `z = i t` meets the `SL(2,ℤ)`-orbit of `τ` only in the
limit `Re τ → ±1`, at the two heights `t = Im τ` (the genuine translate pole `z = τ - n`) and
`t = 1/Im τ` (the *removable* `S`-branch `z = S (τ - n)`, whose cleared kernel vanishes by
`KPlusClear_TS` / `KMinusClear_TS`).

The hypothesis `1/8 ≤ |t - Im τ|` removes the genuine pole.  The `S`-branch is handled by the
one-zero bound for the cleared value function `AfunFun` at the `S`-branch point
(`Work.Asymptotics.AfunFun_S_vadd_zero`) together with the uniform lower bound for the difference
quotient of `j`.

The proof is split into a "far" region (separated from `1/Im τ`, or `τ` away from the bad lines;
compactness, since there the coincidence divisor no longer vanishes) and a "near" region (the
`S`-window).
-/

noncomputable section

open MeasureTheory UpperHalfPlane

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-! ## 0. Elementary facts about `lowBadSet` -/

lemma kaux_re_abs_bounds {τ : ℍ} (hτ : lowBadSet τ) : 3 / 4 < |τ.re| ∧ |τ.re| < 1 := by
  obtain ⟨hD, -, -, hre⟩ := hτ
  refine ⟨?_, ?_⟩
  · rcases hre with h | h
    · rw [abs_of_pos (by linarith [hD.1])]; exact h
    · rw [abs_of_neg (by linarith [hD.2.1])]; linarith
  · rw [abs_lt]; exact ⟨hD.1, hD.2.1⟩

lemma kaux_im_bounds {τ : ℍ} (hτ : lowBadSet τ) : 1 / 2 ≤ τ.im ∧ τ.im ≤ 2 :=
  ⟨hτ.2.1, hτ.2.2.1⟩

/-! ## 1. The translate `τ - tsign τ` -/

/-- On `lowBadSet`, `tsign τ = 1` when `Re τ > 0` and `tsign τ = -1` when `Re τ < 0`. -/
lemma lowBadSet_tsign {τ : ℍ} (hτ : lowBadSet τ) :
    (0 < τ.re → tsign τ = 1) ∧ (τ.re < 0 → tsign τ = -1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold tsign; rw [if_pos h]
  · unfold tsign; rw [if_neg (not_lt.mpr h.le)]

/-- `|Re τ - tsign τ| = 1 - |Re τ|` when `3/4 ≤ |Re τ| ≤ 1`. -/
lemma tsign_abs_of_abs_re {τ : ℍ} (hre : 3 / 4 ≤ |τ.re|) (hre1 : |τ.re| ≤ 1) :
    |τ.re - tsign τ| = 1 - |τ.re| := by
  obtain ⟨h2, h3⟩ := abs_le.mp hre1
  have hne : τ.re ≠ 0 := by
    intro h; rw [h, abs_zero] at hre; norm_num at hre
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

/-- `|Re τ - tsign τ| = 1 - |Re τ|` on `lowBadSet`. -/
lemma lowBadSet_tsign_abs {τ : ℍ} (hτ : lowBadSet τ) :
    |τ.re - tsign τ| = 1 - |τ.re| := by
  obtain ⟨hr1, hr2⟩ := kaux_re_abs_bounds hτ
  exact tsign_abs_of_abs_re (le_of_lt hr1) (le_of_lt hr2)

/-- The translate `τ - tsign τ` lies in the CKMRV fundamental domain for
`3/4 ≤ |Re τ| ≤ 1`, `1/2 ≤ Im τ`. -/
lemma translate_mem_DomainD {τ : ℍ} (hre : 3 / 4 ≤ |τ.re|) (hre1 : |τ.re| ≤ 1)
    (him : 1 / 2 ≤ τ.im) :
    (-(tsign τ : ℝ)) +ᵥ τ ∈ Work.Asymptotics.DomainD := by
  have habs : |τ.re - tsign τ| ≤ 1 / 4 := by
    rw [tsign_abs_of_abs_re hre hre1]; linarith
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

lemma kaux_translate_mem_DomainD {τ : ℍ} (hτ : lowBadSet τ) :
    (-(tsign τ : ℝ)) +ᵥ τ ∈ Work.Asymptotics.DomainD := by
  obtain ⟨hr1, hr2⟩ := kaux_re_abs_bounds hτ
  exact translate_mem_DomainD (le_of_lt hr1) (le_of_lt hr2) (kaux_im_bounds hτ).1


/-! ## 2. The compact box of parameters and a total contour point -/

/-- The closed box of parameters containing the closure of `lowBadSet`. -/
def badBox : Set ℍ := {τ : ℍ | 3 / 4 ≤ |τ.re| ∧ |τ.re| ≤ 1 ∧ 1 / 2 ≤ τ.im ∧ τ.im ≤ 2}

lemma mem_badBox {τ : ℍ} (hτ : lowBadSet τ) : τ ∈ badBox := by
  obtain ⟨hr1, hr2⟩ := kaux_re_abs_bounds hτ
  obtain ⟨him1, him2⟩ := kaux_im_bounds hτ
  exact ⟨le_of_lt hr1, le_of_lt hr2, him1, him2⟩

lemma isCompact_badBox : IsCompact badBox := by
  have h1 : IsClosed {τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} :=
    isClosed_le continuous_const (continuous_abs.comp UpperHalfPlane.continuous_re)
  have h2 : IsClosed {τ : ℍ | |τ.re| ≤ (1 : ℝ)} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  have h3 : IsClosed {τ : ℍ | (1 / 2 : ℝ) ≤ τ.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h4 : IsClosed {τ : ℍ | τ.im ≤ (2 : ℝ)} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have heq : badBox = {τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} ∩ {τ : ℍ | |τ.re| ≤ (1 : ℝ)} ∩
      {τ : ℍ | (1 / 2 : ℝ) ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ (2 : ℝ)} := by
    ext τ; simp [badBox, and_assoc]
  have hcl : IsClosed badBox := by
    rw [heq]; exact ((h1.inter h2).inter h3).inter h4
  refine IsCompact.of_isClosed_subset isCompact_badStrip hcl ?_
  rintro τ ⟨h5, h6, h7, h8⟩
  exact ⟨h7, h8, h6⟩

/-- The point `i · max t δc`, a total continuous version of the contour point `i t`. -/
def axisPt (δc : ℝ) (hδc : 0 < δc) (t : ℝ) : ℍ :=
  ⟨((max t δc : ℝ) : ℂ) * Complex.I, by
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
      mul_zero, add_zero]
    exact lt_of_lt_of_le hδc (le_max_right _ _)⟩

lemma axisPt_re (δc : ℝ) (hδc : 0 < δc) (t : ℝ) : (axisPt δc hδc t).re = 0 := by
  rw [← UpperHalfPlane.coe_re, axisPt]
  simp

lemma axisPt_im (δc : ℝ) (hδc : 0 < δc) (t : ℝ) : (axisPt δc hδc t).im = max t δc := by
  rw [← UpperHalfPlane.coe_im, axisPt]
  simp only [UpperHalfPlane.coe_mk]
  rw [Complex.mul_im]
  simp

lemma axisPt_eq_imagAxis {δc t : ℝ} (hδc : 0 < δc) (ht : δc ≤ t) :
    axisPt δc hδc t = Work.Kernels.imagAxis t (lt_of_lt_of_le hδc ht) := by
  apply UpperHalfPlane.ext
  show ((max t δc : ℝ) : ℂ) * Complex.I = (t : ℂ) * Complex.I
  rw [max_eq_left ht]

lemma continuous_axisPt (δc : ℝ) (hδc : 0 < δc) : Continuous (axisPt δc hδc) := by
  rw [continuous_induced_rng (f := UpperHalfPlane.coe)]
  show Continuous (fun t : ℝ => (((max t δc : ℝ) : ℂ) * Complex.I))
  exact (Complex.continuous_ofReal.comp
    (continuous_max.comp (continuous_id.prodMk continuous_const))).mul continuous_const

/-! ## 3. Non-vanishing of the `j`-difference away from the two height windows -/

lemma jInvariantFun_ne_of_far {τ z : ℍ} (hre : 3 / 4 ≤ |τ.re|) (hre1 : |τ.re| ≤ 1)
    (him : 1 / 2 ≤ τ.im) (hzre : (z : ℂ).re = 0) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hsep : (1 / 8 : ℝ) ≤ |z.im - τ.im|)
    (hsep2 : η ≤ |z.im - (τ.im)⁻¹| ∨ δ ≤ 1 - |τ.re|) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
  intro hcoin
  set n := tsign τ with hn
  set w : ℍ := (-(n : ℝ)) +ᵥ τ with hw
  have hwre : w.re = τ.re - n := by rw [hw, UpperHalfPlane.vadd_re]; ring
  have hwim : w.im = τ.im := by rw [hw, UpperHalfPlane.vadd_im]
  have hwr : |τ.re - n| = 1 - |τ.re| := by
    rw [hn]; exact tsign_abs_of_abs_re hre hre1
  have hwD : w ∈ Work.Asymptotics.DomainD := by
    rw [hw, hn]; exact translate_mem_DomainD hre hre1 him
  have hjw : Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun τ := by
    rcases lt_or_ge 0 τ.re with h | h
    · have hn1 : n = 1 := by rw [hn]; unfold tsign; rw [if_pos h]
      rw [hw, hn1, show -(1 : ℝ) = (-1 : ℝ) by norm_num]
      have hh := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
      rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ by rw [← vadd_assoc]; norm_num] at hh
      exact hh.symm
    · have hn1 : n = -1 := by rw [hn]; unfold tsign; rw [if_neg (not_lt.mpr h)]
      rw [hw, hn1, show -(-1 : ℝ) = (1 : ℝ) by norm_num]
      exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ
  have hzw : Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun z := by
    rw [hjw]; exact hcoin
  rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hwD hzre hzw with h | h
  · have hzim : z.im = τ.im := by rw [h, hwim]
    have : |z.im - τ.im| = 0 := by rw [hzim]; simp
    rw [this] at hsep; norm_num at hsep
  · have hw_eq : w = ModularGroup.S • z := by rw [h, Work.HFN.S_smul_S_smul]
    have hzcoe : (z : ℂ) = ((z.im : ℝ) : ℂ) * Complex.I := by
      have h := Complex.re_add_im (z : ℂ)
      have hre : (z : ℂ).re = 0 := hzre
      have him : (z : ℂ).im = z.im := UpperHalfPlane.coe_im z
      rw [hre, him, Complex.ofReal_zero, zero_add] at h
      exact h.symm
    have hScoe : ((ModularGroup.S • z : ℍ) : ℂ) = (-(z : ℂ))⁻¹ := by
      rw [UpperHalfPlane.modular_S_smul]
    have hwcoe : (w : ℂ) = (-(z : ℂ))⁻¹ := by rw [hw_eq]; exact hScoe
    have hwcoe2 : (w : ℂ) = Complex.I / (z.im : ℂ) := by
      rw [hwcoe, hzcoe]
      field_simp
      rw [sq, Complex.I_mul_I]; ring
    have hI : Complex.I / (z.im : ℂ) = ((z.im)⁻¹ : ℝ) * Complex.I := by
      rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm]
    have hwre0 : w.re = 0 := by
      rw [← UpperHalfPlane.coe_re, hwcoe2, hI]; simp
    have hwim1 : w.im = (z.im)⁻¹ := by
      rw [← UpperHalfPlane.coe_im, hwcoe2, hI]; simp
    have h1 : τ.re - n = 0 := by rw [← hwre, hwre0]
    have h2 : 1 - |τ.re| = 0 := by rw [← hwr, h1, abs_zero]
    have hinv : (z.im)⁻¹ = τ.im := by rw [← hwim1, hwim]
    have h3 : z.im = (τ.im)⁻¹ := by rw [← hinv, inv_inv]
    rcases hsep2 with h4 | h4
    · have h5 : |z.im - (τ.im)⁻¹| = 0 := by rw [h3]; simp
      rw [h5] at h4; linarith
    · rw [h2] at h4; linarith

/-! ## 4. The uniform lower bound for the `j`-difference on the far set -/

lemma mul_im_iff {τ : ℍ} {t η : ℝ} (him : 1 / 2 ≤ τ.im) :
    η ≤ |t - (τ.im)⁻¹| ↔ η * τ.im ≤ |t * τ.im - 1| := by
  have hpos : 0 < τ.im := by linarith
  have h1 : t - (τ.im)⁻¹ = (t * τ.im - 1) / τ.im := by field_simp
  rw [h1, abs_div, abs_of_pos hpos, le_div_iff₀ hpos]

lemma far_jdiff_lower {δc η δ : ℝ} (hδc : 0 < δc) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ : ℍ) (t : ℝ), τ ∈ badBox → δc ≤ t → t ≤ lowT →
      (1 / 8 : ℝ) ≤ |t - τ.im| →
      (η ≤ |t - τ.im⁻¹| ∨ δ ≤ 1 - |τ.re|) →
      c ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (axisPt δc hδc t)‖ := by
  set P : Set (ℍ × ℝ) := badBox ×ˢ Set.Icc δc lowT with hP
  have hPc : IsCompact P := isCompact_badBox.prod isCompact_Icc
  have hPcl : IsClosed P := hP ▸ isCompact_badBox.isClosed.prod isClosed_Icc
  set G : ℍ × ℝ → ℝ := fun p =>
    ‖Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPt δc hδc p.2)‖ with hG
  have hGc : Continuous G := by
    rw [hG]
    exact ((Work.Asymptotics.KaxisMid.continuous_jInvariantFun.comp continuous_fst).sub
      (Work.Asymptotics.KaxisMid.continuous_jInvariantFun.comp
        ((continuous_axisPt δc hδc).comp continuous_snd))).norm
  have hTcl : IsClosed {p : ℍ × ℝ |
      (1 / 8 : ℝ) ≤ |p.2 - p.1.im| ∧
        (η * p.1.im ≤ |p.2 * p.1.im - 1| ∨ δ ≤ 1 - |p.1.re|)} := by
    refine IsClosed.inter ?_ ?_
    · exact isClosed_le continuous_const
        (continuous_abs.comp (continuous_snd.sub
          (UpperHalfPlane.continuous_im.comp continuous_fst)))
    · refine IsClosed.union ?_ ?_
      · exact isClosed_le
          (continuous_const.mul (UpperHalfPlane.continuous_im.comp continuous_fst))
          (continuous_abs.comp ((continuous_snd.mul
            (UpperHalfPlane.continuous_im.comp continuous_fst)).sub continuous_const))
      · exact isClosed_le continuous_const
          (continuous_const.sub (continuous_abs.comp
            (UpperHalfPlane.continuous_re.comp continuous_fst)))
  set S : Set (ℍ × ℝ) := P ∩ {p : ℍ × ℝ |
      (1 / 8 : ℝ) ≤ |p.2 - p.1.im| ∧
        (η * p.1.im ≤ |p.2 * p.1.im - 1| ∨ δ ≤ 1 - |p.1.re|)} with hS
  have hScl : IsClosed S := hS ▸ hPcl.inter hTcl
  have hSc : IsCompact S := hPc.of_isClosed_subset hScl (by rw [hS]; exact Set.inter_subset_left)
  rcases S.eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun τ t hτ ht1 ht2 hsep hsep2 => ?_⟩
    exfalso
    have hmem : (τ, t) ∈ S := by
      refine ⟨⟨hτ, ht1, ht2⟩, hsep, ?_⟩
      rcases hsep2 with h | h
      · exact Or.inl ((mul_im_iff hτ.2.2.1).mp h)
      · exact Or.inr h
    rw [hE] at hmem
    exact (Set.mem_empty_iff_false _).mp hmem
  · obtain ⟨p₀, hp₀, hmin⟩ := hSc.exists_isMinOn hne hGc.continuousOn
    have hp₀P : p₀.1 ∈ badBox ∧ δc ≤ p₀.2 ∧ p₀.2 ≤ lowT := by
      have := hp₀.1; rw [hP] at this; exact this
    have hcond := hp₀.2
    have hne0 : Work.Kernels.jInvariantFun p₀.1 ≠
        Work.Kernels.jInvariantFun (axisPt δc hδc p₀.2) := by
      have him1 : (axisPt δc hδc p₀.2).im = p₀.2 := by
        rw [axisPt_im, max_eq_left hp₀P.2.1]
      refine jInvariantFun_ne_of_far hp₀P.1.1 hp₀P.1.2.1 hp₀P.1.2.2.1
        (axisPt_re δc hδc p₀.2) hη hδ ?_ ?_
      · rw [him1]; exact hcond.1
      · rcases hcond.2 with h | h
        · exact Or.inl (by rw [him1]; exact (mul_im_iff hp₀P.1.2.2.1).mpr h)
        · exact Or.inr h
    have hpos : 0 < G p₀ := by
      rw [hG]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hne0)
    refine ⟨G p₀, hpos, fun τ t hτ ht1 ht2 hsep hsep2 => ?_⟩
    have hmem : (τ, t) ∈ S := by
      refine ⟨⟨hτ, ht1, ht2⟩, hsep, ?_⟩
      rcases hsep2 with h | h
      · exact Or.inl ((mul_im_iff hτ.2.2.1).mp h)
      · exact Or.inr h
    have := hmin hmem
    rw [hG] at this ⊢
    exact this

/-! ## 5. The cusp bound and the far bound -/

theorem lowBad_cusp_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ δc Cc : ℝ, 0 < δc ∧ 0 ≤ Cc ∧ ∀ (τ : ℍ) (t : ℝ),
      lowBadSet τ → 0 < t → t ≤ δc → ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cc := by
  obtain ⟨δc, hδc, hb⟩ := Kaxis_cusp_of_bounded ℓ d hd
    (K := badStrip) isCompact_badStrip.isBounded
  obtain ⟨c, hc, hcb⟩ := hb 0 le_rfl
  refine ⟨δc, c, hδc, hc.le, fun τ t hτ ht htδ => ?_⟩
  have h := hcb τ t (mem_badStrip hτ) ht htδ
  rwa [Real.rpow_zero, mul_one] at h

theorem lowBad_far_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ),
        Work.Asymptotics.HalfFunnel.lowBadSet τ → 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
        (1 / 8 : ℝ) ≤ |t - τ.im| →
        (η ≤ |t - τ.im⁻¹| ∨ δ ≤ 1 - |τ.re|) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨δc₀, Cc, hδc₀, hCc, hcusp⟩ := lowBad_cusp_bound ℓ d hd
  set δc : ℝ := min δc₀ (1 / 2) with hδcdef
  have hδc : 0 < δc := lt_min hδc₀ (by norm_num)
  have hδcle : δc ≤ δc₀ := min_le_left _ _
  have hcuspc : ∀ (τ : ℍ) (t : ℝ), lowBadSet τ → 0 < t → t ≤ δc →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cc :=
    fun τ t h1 h2 h3 => hcusp τ t h1 h2 (le_trans h3 hδcle)
  obtain ⟨R₁, hR₁, hb₁⟩ := Work.Asymptotics.KaxisMid.exists_scale_bound_of_isCompact
    isCompact_badBox
  obtain ⟨R₂, hR₂, hb₂⟩ := Work.Asymptotics.KaxisMid.exists_scale_bound_of_isCompact
    (isCompact_Icc.image (continuous_axisPt δc hδc))
  obtain ⟨M, hM, hbM⟩ := Work.Asymptotics.KaxisMid.exists_bound_KfunClear_of_scale_bounds ℓ d hd
    hR₁ hR₂ hb₁ hb₂
  obtain ⟨e₁, he₁, hbD₁⟩ := Work.Asymptotics.KaxisMid.exists_lower_DeltaFun isCompact_badBox
  obtain ⟨e₂, he₂, hbD₂⟩ := Work.Asymptotics.KaxisMid.exists_lower_DeltaFun
    (isCompact_Icc.image (continuous_axisPt δc hδc))
  obtain ⟨cj, hcj, hbj⟩ := far_jdiff_lower (δc := δc) (η := η) (δ := δ) hδc hη hδ
  have hdenpos : 0 < e₁ * e₂ ^ (if d = 8 then 1 else 2) * cj := by positivity
  refine ⟨max Cc (M / (e₁ * e₂ ^ (if d = 8 then 1 else 2) * cj)),
    le_max_of_le_right (by positivity), ?_⟩
  intro τ t hτ ht htT hsep hsep2
  by_cases htc : t ≤ δc
  · exact le_trans (hcuspc τ t hτ ht htc) (le_max_left _ _)
  · push_neg at htc
    have ht1 : δc ≤ t := le_of_lt htc
    have hτbox : τ ∈ badBox := mem_badBox hτ
    have hz : axisPt δc hδc t = Work.Kernels.imagAxis t ht := axisPt_eq_imagAxis hδc ht1
    have hzctr : axisPt δc hδc t ∈ axisPt δc hδc '' Set.Icc δc lowT :=
      ⟨t, ⟨ht1, htT⟩, rfl⟩
    have hzim : (axisPt δc hδc t).im = t := by rw [axisPt_im, max_eq_left ht1]
    have hjne' : Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun (axisPt δc hδc t) := by
      refine jInvariantFun_ne_of_far hτbox.1 hτbox.2.1 hτbox.2.2.1 (axisPt_re δc hδc t)
        hη hδ ?_ ?_
      · rw [hzim]; exact hsep
      · rcases hsep2 with h | h
        · exact Or.inl (by rw [hzim]; exact h)
        · exact Or.inr h
    have hM' := hbM τ hτbox (axisPt δc hδc t) hzctr
    have hD₁ := hbD₁ τ hτbox
    have hD₂ := hbD₂ (axisPt δc hδc t) hzctr
    have hJ := hbj τ t hτbox ht1 htT hsep hsep2
    have hK1 := Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ (axisPt δc hδc t) hjne'
    have hK2 := Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ (axisPt δc hδc t) hjne'
    have hPne : Work.Kernels.growthPrefactor d τ (axisPt δc hδc t) ≠ 0 :=
      Work.Asymptotics.growthPrefactor_ne_zero d hjne'
    have hKfun : Work.Kernels.Kfun ℓ d τ (axisPt δc hδc t) =
        Work.Kernels.KfunClear ℓ d τ (axisPt δc hδc t) /
          Work.Kernels.growthPrefactor d τ (axisPt δc hδc t) := by
      rw [eq_div_iff hPne, Work.Kernels.Kfun, Work.Kernels.KfunClear, hK1, hK2]
      ring
    have hpre : e₁ * e₂ ^ (if d = 8 then 1 else 2) * cj ≤
        ‖Work.Kernels.growthPrefactor d τ (axisPt δc hδc t)‖ := by
      rw [Work.Asymptotics.KaxisMid.norm_growthPrefactor]
      have h2 : e₂ ^ (if d = 8 then 1 else 2) ≤
          ‖Work.Kernels.DeltaFun (axisPt δc hδc t)‖ ^ (if d = 8 then 1 else 2) :=
        pow_le_pow_left₀ he₂.le hD₂ _
      have h3 : (0 : ℝ) ≤ e₂ ^ (if d = 8 then 1 else 2) := pow_nonneg he₂.le _
      have h5 : e₁ * e₂ ^ (if d = 8 then 1 else 2) ≤
          ‖Work.Kernels.DeltaFun τ‖ *
            ‖Work.Kernels.DeltaFun (axisPt δc hδc t)‖ ^ (if d = 8 then 1 else 2) :=
        mul_le_mul hD₁ h2 h3 (norm_nonneg _)
      exact mul_le_mul h5 hJ hcj.le
        (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    have hprepos : 0 < ‖Work.Kernels.growthPrefactor d τ (axisPt δc hδc t)‖ :=
      lt_of_lt_of_le hdenpos hpre
    rw [Work.Kernels.Kaxis, dif_pos ht, ← hz, hKfun, norm_div]
    rw [div_le_iff₀ hprepos]
    calc ‖Work.Kernels.KfunClear ℓ d τ (axisPt δc hδc t)‖
        ≤ M := hM'
      _ = M / (e₁ * e₂ ^ (if d = 8 then 1 else 2) * cj) *
            (e₁ * e₂ ^ (if d = 8 then 1 else 2) * cj) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hdenpos)]
      _ ≤ M / (e₁ * e₂ ^ (if d = 8 then 1 else 2) * cj) *
            ‖Work.Kernels.growthPrefactor d τ (axisPt δc hδc t)‖ :=
          mul_le_mul_of_nonneg_left hpre (by positivity)
      _ ≤ max Cc (M / (e₁ * e₂ ^ (if d = 8 then 1 else 2) * cj)) *
            ‖Work.Kernels.growthPrefactor d τ (axisPt δc hδc t)‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)


/-! ## 6. Two analytic helpers for the `S`-window -/

/-- The Euclidean box `{‖x‖ ≤ R, c ≤ Im x} ⊆ ℂ` is compact. -/
lemma isCompact_box_im (R c : ℝ) : IsCompact {x : ℂ | ‖x‖ ≤ R ∧ c ≤ x.im} := by
  have hcl : IsClosed {x : ℂ | ‖x‖ ≤ R ∧ c ≤ x.im} :=
    (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl, ?_⟩
  exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
    (fun x hx => by rw [Metric.mem_closedBall, dist_zero_right]; exact hx.1)

/-- Uniform bound for the cleared value function `AfunFun` on a product of two compact
Euclidean boxes in the upper half plane. -/
lemma exists_bound_AfunFun_prod (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {s₁ s₂ : Set ℂ} (h₁ : IsCompact s₁) (h₂ : IsCompact s₂)
    (h₁' : ∀ z ∈ s₁, 0 < z.im) (h₂' : ∀ z ∈ s₂, 0 < z.im) :
    ∃ B : ℝ, 0 < B ∧ ∀ (τ w : ℍ), (τ : ℂ) ∈ s₁ → (w : ℂ) ∈ s₂ →
      ‖Work.Asymptotics.AfunFun ℓ d τ w‖ ≤ B := by
  have hpair : ContinuousOn (fun p : ℂ × ℂ =>
      (UpperHalfPlane.ofComplex p.1, UpperHalfPlane.ofComplex p.2)) (s₁ ×ˢ s₂) :=
    ((continuousOn_ofComplex_im_pos.mono (fun u hu => h₁' u hu)).comp
        continuous_fst.continuousOn (fun p hp => hp.1)).prodMk
      ((continuousOn_ofComplex_im_pos.mono (fun u hu => h₂' u hu)).comp
        continuous_snd.continuousOn (fun p hp => hp.2))
  obtain ⟨B₀, hB₀⟩ := (h₁.prod h₂).exists_bound_of_continuousOn
    ((Work.Asymptotics.continuous_AfunFun ℓ d).continuousOn.comp hpair (fun p _ => Set.mem_univ _))
  refine ⟨max B₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun τ w hτ hw => ?_⟩
  have h1 : ‖Work.Asymptotics.AfunFun ℓ d τ w‖ =
      ‖Work.Asymptotics.AfunFun ℓ d (UpperHalfPlane.ofComplex (τ : ℂ))
        (UpperHalfPlane.ofComplex (w : ℂ))‖ := by
    rw [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply]
  rw [h1]
  exact le_trans (hB₀ ((τ : ℂ), (w : ℂ)) ⟨hτ, hw⟩) (le_max_left _ _)

/-- **Uniform difference-quotient lower bound for `j` on a compact arc of the imaginary
axis.**  On `[a,b] ∌ 1`, the local linear lower bound of `exists_diffQuotient_lower_general`
holds with constants uniform in `t₀`. -/
theorem exists_diffQuotient_lower_uniform (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hne : b < 1 ∨ 1 < a) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ (t₀ : ℝ), a ≤ t₀ → t₀ ≤ b → ∀ (τ z : UpperHalfPlane),
      ‖(τ : ℂ) - Complex.I * (t₀ : ℂ)‖ < ρ →
      ‖(z : ℂ) - Complex.I * (t₀ : ℂ)‖ < ρ →
      c * ‖(τ : ℂ) - (z : ℂ)‖ ≤
        ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
  classical
  have hloc : ∀ t : {t : ℝ // t ∈ Set.Icc a b}, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
      ∀ (τ z : ℍ), ‖(τ : ℂ) - Complex.I * ((t : ℝ) : ℂ)‖ < ρ →
        ‖(z : ℂ) - Complex.I * ((t : ℝ) : ℂ)‖ < ρ →
        c * ‖(τ : ℂ) - (z : ℂ)‖ ≤
          ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
    intro t
    have h0 : 0 < (t : ℝ) := lt_of_lt_of_le ha t.2.1
    have h1 : (t : ℝ) ≠ 1 := by
      rcases hne with h | h
      · exact ne_of_lt (lt_of_le_of_lt t.2.2 h)
      · exact ne_of_gt (lt_of_lt_of_le h t.2.1)
    obtain ⟨ρ, hρ, c, hc, hb⟩ :=
      Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general h0 h1
    have hcen : (((Work.Kernels.imagAxis (t : ℝ) h0 : ℍ)) : ℂ) =
        Complex.I * ((t : ℝ) : ℂ) := by
      show ((t : ℝ) : ℂ) * Complex.I = Complex.I * ((t : ℝ) : ℂ)
      rw [mul_comm]
    refine ⟨ρ, c, hρ, hc, fun τ z hτ hz => ?_⟩
    exact hb τ z (by rwa [hcen]) (by rwa [hcen])
  choose ρf cf hρf hcf hbf using hloc
  have hcover : Set.Icc a b ⊆ ⋃ t : {t : ℝ // t ∈ Set.Icc a b},
      {x : ℝ | |x - (t : ℝ)| < ρf t / 8} := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    simp only [Set.mem_setOf_eq]
    rw [sub_self, abs_zero]
    linarith [hρf ⟨x, hx⟩]
  have hopen : ∀ t : {t : ℝ // t ∈ Set.Icc a b},
      IsOpen {x : ℝ | |x - (t : ℝ)| < ρf t / 8} := fun t =>
    isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : {t : ℝ // t ∈ Set.Icc a b} => {x : ℝ | |x - (t : ℝ)| < ρf t / 8}) hopen hcover
  have hsne : s.Nonempty := by
    have hmem := hs (Set.left_mem_Icc.mpr hab)
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨t, ht, -⟩ := hmem
    exact ⟨t, ht⟩
  refine ⟨s.inf' hsne (fun t => ρf t / 8), s.inf' hsne cf, ?_, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro t ht
    linarith [hρf t]
  · rw [Finset.lt_inf'_iff]
    intro t ht
    exact hcf t
  · intro t₀ ht₀a ht₀b τ z hτ hz
    have hmem := hs (Set.mem_Icc.mpr ⟨ht₀a, ht₀b⟩)
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨t, ht, htmem⟩ := hmem
    have htmem' : |t₀ - (t : ℝ)| < ρf t / 8 := htmem
    have hρle : s.inf' hsne (fun t => ρf t / 8) ≤ ρf t / 8 := Finset.inf'_le _ ht
    have hcle : s.inf' hsne cf ≤ cf t := Finset.inf'_le _ ht
    have hbi : ‖Complex.I * (t₀ : ℂ) - Complex.I * ((t : ℝ) : ℂ)‖ = |t₀ - (t : ℝ)| := by
      rw [← mul_sub, norm_mul, Complex.norm_I, one_mul, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖(τ : ℂ) - Complex.I * ((t : ℝ) : ℂ)‖ < ρf t := by
      have hsplit : (τ : ℂ) - Complex.I * ((t : ℝ) : ℂ) =
          ((τ : ℂ) - Complex.I * (t₀ : ℂ)) + (Complex.I * (t₀ : ℂ) - Complex.I * ((t : ℝ) : ℂ)) :=
        by ring
      rw [hsplit]
      calc ‖((τ : ℂ) - Complex.I * (t₀ : ℂ)) +
            (Complex.I * (t₀ : ℂ) - Complex.I * ((t : ℝ) : ℂ))‖
          ≤ ‖(τ : ℂ) - Complex.I * (t₀ : ℂ)‖ +
            ‖Complex.I * (t₀ : ℂ) - Complex.I * ((t : ℝ) : ℂ)‖ := norm_add_le _ _
        _ < s.inf' hsne (fun t => ρf t / 8) + ρf t / 8 :=
            add_lt_add hτ (by rw [hbi]; exact htmem')
        _ ≤ ρf t / 8 + ρf t / 8 := by linarith
        _ < ρf t := by linarith [hρf t]
    have h2 : ‖(z : ℂ) - Complex.I * ((t : ℝ) : ℂ)‖ < ρf t := by
      have hsplit : (z : ℂ) - Complex.I * ((t : ℝ) : ℂ) =
          ((z : ℂ) - Complex.I * (t₀ : ℂ)) + (Complex.I * (t₀ : ℂ) - Complex.I * ((t : ℝ) : ℂ)) :=
        by ring
      rw [hsplit]
      calc ‖((z : ℂ) - Complex.I * (t₀ : ℂ)) +
            (Complex.I * (t₀ : ℂ) - Complex.I * ((t : ℝ) : ℂ))‖
          ≤ ‖(z : ℂ) - Complex.I * (t₀ : ℂ)‖ +
            ‖Complex.I * (t₀ : ℂ) - Complex.I * ((t : ℝ) : ℂ)‖ := norm_add_le _ _
        _ < s.inf' hsne (fun t => ρf t / 8) + ρf t / 8 :=
            add_lt_add hz (by rw [hbi]; exact htmem')
        _ ≤ ρf t / 8 + ρf t / 8 := by linarith
        _ < ρf t := by linarith [hρf t]
    exact le_trans (mul_le_mul_of_nonneg_right hcle (norm_nonneg _)) (hbf t τ z h1 h2)


/-! ## 7. The `S`-window bound -/

lemma AfunFun_S_zpole_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) :
    Work.Asymptotics.AfunFun ℓ d τ
      (ModularGroup.S • ((-(tsign τ : ℝ)) +ᵥ τ)) = 0 := by
  set σ : ℍ := (-(tsign τ : ℝ)) +ᵥ τ with hσdef
  obtain ⟨m, hm, hmr⟩ : ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ (m : ℝ) = tsign τ := by
    rcases lt_or_ge 0 τ.re with h | h
    · exact ⟨1, Or.inl rfl, by unfold tsign; rw [if_pos h]; norm_num⟩
    · exact ⟨-1, Or.inr rfl, by unfold tsign; rw [if_neg (not_lt.mpr h)]; norm_num⟩
  have hτ : τ = (m : ℝ) +ᵥ σ := by
    rw [hσdef, hmr, ← vadd_assoc]; norm_num
  rw [hτ]
  exact Work.Asymptotics.AfunFun_S_vadd_zero ℓ d hd m hm σ

lemma sSre (τ : ℍ) : (ModularGroup.S • τ).re = -τ.re / ‖(τ : ℂ)‖ ^ 2 := by
  have h1 : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  rw [← UpperHalfPlane.coe_re, h1, inv_neg, Complex.neg_re, Complex.inv_re,
    Complex.normSq_eq_norm_sq, UpperHalfPlane.coe_re]
  ring

lemma jInvariantFun_ne_axis (τ : ℍ) (hD : τ ∈ Work.Asymptotics.DomainD) (hre : τ.re ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro hcoin
  have hzre : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = 0 := by
    show ((t : ℂ) * Complex.I).re = 0
    simp
  rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hD hzre hcoin with h | h
  · have h2 : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = τ.re := by rw [← h]; rfl
    rw [hzre] at h2; exact hre h2.symm
  · have h2 : (ModularGroup.S • τ).re = 0 := by rw [← h]; exact hzre
    rw [sSre] at h2
    have h4 : ‖(τ : ℂ)‖ ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 ?_
      exact norm_ne_zero_iff.mpr (fun hh => hre (by rw [← UpperHalfPlane.coe_re, hh]; rfl))
    rcases div_eq_zero_iff.mp h2 with h5 | h5
    · exact hre (neg_eq_zero.mp h5)
    · exact absurd h5 h4

theorem lowBad_near_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ η δ C : ℝ, 0 < η ∧ 0 < δ ∧ 0 ≤ C ∧
      ∀ (τ : ℍ) (t : ℝ), lowBadSet τ → 0 < t → t ≤ lowT →
        (1 / 8 : ℝ) ≤ |t - τ.im| → |t - τ.im⁻¹| < η → 1 - |τ.re| < δ →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨ρ₁, c₁, hρ₁, hc₁, hdq₁⟩ :=
    exists_diffQuotient_lower_uniform (1 / 2) (1 - 1 / 100) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  obtain ⟨ρ₂, c₂, hρ₂, hc₂, hdq₂⟩ :=
    exists_diffQuotient_lower_uniform (1 + 1 / 100) 2 (by norm_num) (by norm_num)
      (Or.inr (by norm_num))
  set ρD : ℝ := min ρ₁ ρ₂ with hρDdef
  set cD : ℝ := min c₁ c₂ with hcDdef
  have hρD : 0 < ρD := lt_min hρ₁ hρ₂
  have hcD : 0 < cD := lt_min hc₁ hc₂
  obtain ⟨B, hB, hbB⟩ := exists_bound_AfunFun_prod ℓ d (isCompact_box_im 3 (1 / 4))
    (isCompact_box_im 3 (1 / 16))
    (fun z hz => by linarith [hz.2]) (fun z hz => by linarith [hz.2])
  set ρN : ℝ := 1 / 32 with hρNdef
  have hρN : 0 < ρN := by rw [hρNdef]; norm_num
  set η : ℝ := min (1 / 256) (ρD / 8) with hηdef
  set δ : ℝ := min (1 / 1024) (ρD / 64) with hδdef
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hη256 : η ≤ 1 / 256 := min_le_left _ _
  have hδ1024 : δ ≤ 1 / 1024 := min_le_left _ _
  have hηρ : η ≤ ρD / 8 := min_le_right _ _
  have hδρ : δ ≤ ρD / 64 := min_le_right _ _
  refine ⟨η, δ, 2 * B / (ρN * cD), hη, hδ, by positivity, ?_⟩
  intro τ t hτ ht htT hsep hnear hclo
  obtain ⟨hrlo, hrhi⟩ := kaux_re_abs_bounds hτ
  have hτne : τ.re ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hrlo; norm_num at hrlo
  set s : ℝ := τ.im with hs
  have hs1 : (1 / 2 : ℝ) ≤ s := by rw [hs]; exact (kaux_im_bounds hτ).1
  have hs2 : s ≤ 2 := by rw [hs]; exact (kaux_im_bounds hτ).2
  have hspos : 0 < s := by linarith
  set σ : ℍ := (-(tsign τ : ℝ)) +ᵥ τ with hσdef
  have hσre : σ.re = τ.re - tsign τ := by rw [hσdef, UpperHalfPlane.vadd_re]; ring
  have hσim : σ.im = s := by rw [hσdef, UpperHalfPlane.vadd_im, hs]
  have hσabs : |σ.re| = 1 - |τ.re| := by
    rw [hσre]; exact tsign_abs_of_abs_re (le_of_lt hrlo) (le_of_lt hrhi)
  have hσne : (σ : ℂ) ≠ 0 := σ.ne_zero
  set ζ : ℍ := ModularGroup.S • σ with hζdef
  have hζcoe : (ζ : ℂ) = (-(σ : ℂ))⁻¹ := by
    rw [hζdef, UpperHalfPlane.modular_S_smul]
  have hζre : ζ.re = -σ.re / ‖(σ : ℂ)‖ ^ 2 := by
    rw [← UpperHalfPlane.coe_re, hζcoe, inv_neg, Complex.neg_re, Complex.inv_re,
      Complex.normSq_eq_norm_sq]
    simp only [UpperHalfPlane.coe_re]
    ring
  have hσre_ne : σ.re ≠ 0 := by
    intro h0; have := hσabs; rw [h0, abs_zero] at this; linarith
  have hζre_ne : ζ.re ≠ 0 := by
    rw [hζre]
    exact div_ne_zero (neg_ne_zero.mpr hσre_ne)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hσne))
  have hζim : (8 / 65 : ℝ) ≤ ζ.im := by
    rw [hζdef, Work.Asymptotics.KaxisMid.KbcAux2.im_S, hσim]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖(σ : ℂ)‖ ^ 2)]
    have h1 : ‖(σ : ℂ)‖ ^ 2 = σ.re ^ 2 + s ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im, hσim]
      ring
    have h2 : σ.re ^ 2 ≤ 1 / 16 := by
      have h3 : |σ.re| ≤ 1 / 4 := by rw [hσabs]; linarith
      nlinarith [sq_abs σ.re, abs_nonneg σ.re, h3]
    rw [h1]
    nlinarith [hs1, h2]
  have hζ0 : Work.Asymptotics.AfunFun ℓ d τ ζ = 0 := by
    rw [hζdef, hσdef]; exact AfunFun_S_zpole_zero ℓ d hd τ
  have hjσ : Work.Kernels.jInvariantFun σ = Work.Kernels.jInvariantFun τ := by
    rw [hσdef]
    rcases lt_or_ge 0 τ.re with h | h
    · have h1 : tsign τ = 1 := by unfold tsign; rw [if_pos h]
      rw [h1, show -(1 : ℝ) = (-1 : ℝ) by norm_num]
      have hh := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
      rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ by rw [← vadd_assoc]; norm_num] at hh
      exact hh.symm
    · have h1 : tsign τ = -1 := by unfold tsign; rw [if_neg (not_lt.mpr h)]
      rw [h1, show -(-1 : ℝ) = (1 : ℝ) by norm_num]
      exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ
  have hjζ : Work.Kernels.jInvariantFun ζ = Work.Kernels.jInvariantFun τ := by
    rw [hζdef, Work.Kernels.KernelFacts.jInvariantFun_S_smul]; exact hjσ
  set w₁ : ℍ := ModularGroup.S • (Work.Kernels.imagAxis s hspos) with hw₁def
  have hw₁coe : (w₁ : ℂ) = Complex.I * ((s⁻¹ : ℝ) : ℂ) := by
    rw [hw₁def, UpperHalfPlane.modular_S_smul]
    show (-(((Work.Kernels.imagAxis s hspos : ℍ) : ℂ)))⁻¹ = Complex.I * ((s⁻¹ : ℝ) : ℂ)
    rw [show ((Work.Kernels.imagAxis s hspos : ℍ) : ℂ) = (s : ℂ) * Complex.I from rfl]
    rw [inv_neg, mul_inv_rev, Complex.inv_I, ← Complex.ofReal_inv]
    ring
  have hζw₁ : ‖(ζ : ℂ) - (w₁ : ℂ)‖ ≤ 4 * δ := by
    have h1 : ‖(ζ : ℂ) - (w₁ : ℂ)‖ =
        ‖(σ : ℂ) - ((Work.Kernels.imagAxis s hspos : ℍ) : ℂ)‖ / (‖(σ : ℂ)‖ * s) := by
      rw [hζdef, hw₁def, Work.Asymptotics.KaxisMid.KbcAux2.norm_S_sub_S]
      rw [show ((Work.Kernels.imagAxis s hspos : ℍ) : ℂ) = (s : ℂ) * Complex.I from rfl]
      rw [show ‖(s : ℂ) * Complex.I‖ = s from by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hspos]]
    have h2 : ‖(σ : ℂ) - ((Work.Kernels.imagAxis s hspos : ℍ) : ℂ)‖ = |σ.re| := by
      have h2' : (σ : ℂ) - ((Work.Kernels.imagAxis s hspos : ℍ) : ℂ) = (σ.re : ℂ) := by
        rw [show ((Work.Kernels.imagAxis s hspos : ℍ) : ℂ) = (s : ℂ) * Complex.I from rfl]
        apply Complex.ext <;>
          simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
            UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hσim]
      rw [h2', Complex.norm_real, Real.norm_eq_abs]
    rw [h1, h2]
    have h3 : |σ.re| < δ := by rw [hσabs]; exact hclo
    have h4 : (1 : ℝ) / 2 ≤ ‖(σ : ℂ)‖ := by
      have h5 := Complex.abs_im_le_norm (σ : ℂ)
      rw [UpperHalfPlane.coe_im, hσim, abs_of_pos hspos] at h5
      exact le_trans hs1 h5
    have h6 : |σ.re| / (‖(σ : ℂ)‖ * s) ≤ |σ.re| / (1 / 4) := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
      nlinarith [h4, hs1]
    calc |σ.re| / (‖(σ : ℂ)‖ * s) ≤ |σ.re| / (1 / 4) := h6
      _ = 4 * |σ.re| := by ring
      _ ≤ 4 * δ := by linarith
  have hζw : ‖(ζ : ℂ) - Complex.I * ((s⁻¹ : ℝ) : ℂ)‖ < ρD := by
    rw [← hw₁coe]
    have h4δ : 4 * δ < ρD := by have := hδρ; linarith
    linarith [hζw₁]
  have hzw : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - Complex.I * ((s⁻¹ : ℝ) : ℂ)‖ < ρD := by
    have h1 : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - Complex.I * ((s⁻¹ : ℝ) : ℂ) =
        ((t - s⁻¹ : ℝ) : ℂ) * Complex.I := by
      rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
      push_cast
      ring
    rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith [hnear, hηρ, hρD]
  have hsinv1 : (1 / 2 : ℝ) ≤ s⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hspos]; linarith [hs2]
  have hsinv2 : s⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hspos]; linarith [hs1]
  have hsep_inv : (1 / 100 : ℝ) ≤ |1 - s⁻¹| := by
    have h7 : |s⁻¹ - s| = |1 - s⁻¹| * (1 + s) := by
      rw [show s⁻¹ - s = -(1 - s⁻¹) * (1 + s) by field_simp; ring]
      rw [abs_mul, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 1 + s)]
    have h8 : (1 / 8 : ℝ) ≤ |t - s| := by rw [hs]; exact hsep
    have h9 : |s⁻¹ - s| ≥ 1 / 8 - η := by
      have h10 : |t - s| ≤ |t - s⁻¹| + |s⁻¹ - s| := abs_sub_le t s⁻¹ s
      linarith
    have h13 : 1 / 8 - η ≥ 31 / 256 := by linarith [hη256]
    have h9' : (1 / 8 - η : ℝ) ≤ |1 - s⁻¹| * (1 + s) := by rw [← h7]; exact h9
    have h16 : |1 - s⁻¹| * (1 + s) ≤ |1 - s⁻¹| * 3 := by
      have := abs_nonneg (1 - s⁻¹); nlinarith [hs2]
    have h15 : (31 / 256 : ℝ) ≤ |1 - s⁻¹| * 3 := by linarith
    have h17 : (31 / 256 : ℝ) / 3 ≤ |1 - s⁻¹| := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith
    linarith
  have harc : (s⁻¹ ≤ 1 - 1 / 100 ∧ 1 / 2 ≤ s⁻¹) ∨ (1 + 1 / 100 ≤ s⁻¹ ∧ s⁻¹ ≤ 2) := by
    rcases le_or_gt s⁻¹ 1 with h | h
    · exact Or.inl ⟨by
        have h1 : (0 : ℝ) ≤ 1 - s⁻¹ := by linarith
        have h2 : |1 - s⁻¹| = 1 - s⁻¹ := abs_of_nonneg h1
        linarith [hsep_inv, h2], hsinv1⟩
    · exact Or.inr ⟨by
        have h1 : 1 - s⁻¹ ≤ 0 := by linarith
        have h2 : |1 - s⁻¹| = s⁻¹ - 1 := by rw [abs_of_nonpos h1]; ring
        linarith [hsep_inv, h2], hsinv2⟩
  have htsw : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖ =
      ‖(ζ : ℂ) - ((Work.Kernels.imagAxis t ht : ℍ) : ℂ)‖ := norm_sub_rev _ _
  have hJ : cD * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖ ≤
      ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) -
        Work.Kernels.jInvariantFun τ‖ := by
    rcases harc with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h := hdq₁ s⁻¹ hb ha ζ (Work.Kernels.imagAxis t ht)
        (lt_of_lt_of_le hζw (by rw [hρDdef]; exact min_le_left _ _))
        (lt_of_lt_of_le hzw (by rw [hρDdef]; exact min_le_left _ _))
      rw [hjζ] at h
      calc cD * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖
          ≤ c₁ * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖ :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
        _ = c₁ * ‖(ζ : ℂ) - ((Work.Kernels.imagAxis t ht : ℍ) : ℂ)‖ := by rw [htsw]
        _ ≤ ‖Work.Kernels.jInvariantFun τ -
              Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := h
        _ = ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) -
              Work.Kernels.jInvariantFun τ‖ := norm_sub_rev _ _
    · have h := hdq₂ s⁻¹ ha hb ζ (Work.Kernels.imagAxis t ht)
        (lt_of_lt_of_le hζw (by rw [hρDdef]; exact min_le_right _ _))
        (lt_of_lt_of_le hzw (by rw [hρDdef]; exact min_le_right _ _))
      rw [hjζ] at h
      calc cD * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖
          ≤ c₂ * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ = c₂ * ‖(ζ : ℂ) - ((Work.Kernels.imagAxis t ht : ℍ) : ℂ)‖ := by rw [htsw]
        _ ≤ ‖Work.Kernels.jInvariantFun τ -
              Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := h
        _ = ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) -
              Work.Kernels.jInvariantFun τ‖ := norm_sub_rev _ _
  have hζit_pos : 0 < ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
    intro h
    have h1 : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = 0 := by
      show ((t : ℂ) * Complex.I).re = 0
      simp
    have h0 : (ζ : ℂ).re = 0 := by rw [← h]; exact h1
    exact hζre_ne (by rw [← UpperHalfPlane.coe_re]; exact h0)
  have hρNζ : ρN < ζ.im := by rw [hρNdef]; linarith [hζim]
  have hτnorm : ‖(τ : ℂ)‖ ≤ 3 := by
    have h1 : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      ring
    have h2 : τ.re ^ 2 ≤ 1 := by
      have := abs_lt.mp hrhi; nlinarith [this.1, this.2]
    have h3 : τ.im ^ 2 ≤ 4 := by nlinarith [hs2, hspos, hs]
    nlinarith [norm_nonneg (τ : ℂ)]
  have hζnorm : ‖(ζ : ℂ)‖ ≤ 2 := by
    rw [hζcoe, norm_inv, norm_neg]
    have h4 : (1 / 2 : ℝ) ≤ ‖(σ : ℂ)‖ := by
      have h5 := Complex.abs_im_le_norm (σ : ℂ)
      rw [UpperHalfPlane.coe_im, hσim, abs_of_pos hspos] at h5
      exact le_trans hs1 h5
    rw [inv_eq_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < ‖(σ : ℂ)‖)]
    linarith
  have hbd : ∀ w : ℍ, ‖(w : ℂ) - (ζ : ℂ)‖ ≤ ρN → ‖Work.Asymptotics.AfunFun ℓ d τ w‖ ≤ B := by
    intro w hw
    refine hbB τ w ⟨hτnorm, by rw [UpperHalfPlane.coe_im]; linarith [hs1, hs]⟩ ⟨?_, ?_⟩
    · have h1 : ‖(w : ℂ)‖ ≤ ‖(ζ : ℂ)‖ + ‖(w : ℂ) - (ζ : ℂ)‖ := by
        have hh := norm_add_le (ζ : ℂ) ((w : ℂ) - (ζ : ℂ))
        rwa [add_sub_cancel] at hh
      rw [hρNdef] at hw
      linarith [hζnorm]
    · show (1 / 16 : ℝ) ≤ w.im
      have h1 : |(w : ℂ).im - (ζ : ℂ).im| ≤ ‖(w : ℂ) - (ζ : ℂ)‖ := by
        rw [show (w : ℂ).im - (ζ : ℂ).im = ((w : ℂ) - (ζ : ℂ)).im by simp]
        exact Complex.abs_im_le_norm _
      have h0 : ‖(w : ℂ) - (ζ : ℂ)‖ ≤ (1 / 32 : ℝ) := by rw [hρNdef] at hw; exact hw
      have h2 : -((1 / 32 : ℝ)) ≤ w.im - ζ.im := by
        have h3 := (abs_le.mp (le_trans h1 h0)).1
        simp only [UpperHalfPlane.coe_im] at h3
        exact h3
      have h9 : (1 / 16 : ℝ) ≤ ζ.im - 1 / 32 := by linarith [hζim]
      linarith
  have hw0 : ‖(ζ : ℂ) - (ζ : ℂ)‖ < ρN / 2 := by
    rw [sub_self, norm_zero]; positivity
  have hone := Work.Asymptotics.KaxisMid.KbcAux2.one_zero_apply
    (f := fun w : ℍ => Work.Asymptotics.AfunFun ℓ d τ w)
    (Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ)
    (c := ζ) (r := ρN) (M := B) hρN hρNζ hbd (w₀ := ζ) hw0 hζ0
  have hzclose : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖ < ρN / 2 := by
    have h1 : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖ ≤
        ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - Complex.I * ((s⁻¹ : ℝ) : ℂ)‖ +
          ‖Complex.I * ((s⁻¹ : ℝ) : ℂ) - (ζ : ℂ)‖ := by
      have hh := norm_add_le (((Work.Kernels.imagAxis t ht : ℍ) : ℂ) -
        Complex.I * ((s⁻¹ : ℝ) : ℂ)) (Complex.I * ((s⁻¹ : ℝ) : ℂ) - (ζ : ℂ))
      rwa [sub_add_sub_cancel] at hh
    have h2 : ‖Complex.I * ((s⁻¹ : ℝ) : ℂ) - (ζ : ℂ)‖ =
        ‖(ζ : ℂ) - Complex.I * ((s⁻¹ : ℝ) : ℂ)‖ := norm_sub_rev _ _
    have h3 : ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - Complex.I * ((s⁻¹ : ℝ) : ℂ)‖ < η := by
      have h4 : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - Complex.I * ((s⁻¹ : ℝ) : ℂ) =
          ((t - s⁻¹ : ℝ) : ℂ) * Complex.I := by
        rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
        push_cast
        ring
      rw [h4, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hnear
    have h7 : η + 4 * δ < ρN / 2 := by
      rw [hρNdef]
      linarith [hη256, hδ1024]
    have h8 : ‖(ζ : ℂ) - Complex.I * ((s⁻¹ : ℝ) : ℂ)‖ ≤ 4 * δ := by
      rw [← hw₁coe]; exact hζw₁
    rw [h2] at h1
    linarith [h1, h3, h8, h7]
  have hA := hone (Work.Kernels.imagAxis t ht) hzclose
  have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
    jInvariantFun_ne_axis τ hτ.1 hτne ht
  have hKz : Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht) =
      -Work.Asymptotics.AfunFun ℓ d τ (Work.Kernels.imagAxis t ht) /
        (Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) - Work.Kernels.jInvariantFun τ) := by
    have hne' : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) -
        Work.Kernels.jInvariantFun τ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [eq_div_iff hne', show Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) -
      Work.Kernels.jInvariantFun τ = -(Work.Kernels.jInvariantFun τ -
      Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) by ring, mul_neg,
      Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd τ (Work.Kernels.imagAxis t ht) hne]
  have hden : 0 < ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) -
      Work.Kernels.jInvariantFun τ‖ := by
    have := hJ
    have h2 := mul_pos hcD hζit_pos
    linarith
  rw [Work.Kernels.Kaxis, dif_pos ht, hKz, norm_div, norm_neg, div_le_iff₀ hden]
  calc ‖Work.Asymptotics.AfunFun ℓ d τ (Work.Kernels.imagAxis t ht)‖
      ≤ (2 * B / ρN) * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖ := hA
    _ = (2 * B / (ρN * cD)) *
          (cD * ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (ζ : ℂ)‖) := by
        field_simp
    _ ≤ (2 * B / (ρN * cD)) *
          ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) - Work.Kernels.jInvariantFun τ‖ :=
        mul_le_mul_of_nonneg_left hJ (by positivity)


/-! ## 8. The target theorem -/

theorem lowBad_Kaxis_bound_aux (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
      (1 / 8 : ℝ) ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨ηn, δn, Cn, hηn, hδn, hCn, hnear⟩ := lowBad_near_bound ℓ d hd
  obtain ⟨Cf, hCf, hfar⟩ := lowBad_far_bound ℓ d hd ηn δn hηn hδn
  refine ⟨max Cf Cn, le_trans hCf (le_max_left _ _), fun τ t hτ ht htT hsep => ?_⟩
  by_cases h1 : |t - τ.im⁻¹| < ηn
  · by_cases h2 : 1 - |τ.re| < δn
    · exact le_trans (hnear τ t hτ ht htT hsep h1 h2) (le_max_right _ _)
    · exact le_trans (hfar τ t hτ ht htT hsep (Or.inr (not_lt.mp h2)))
        (le_max_left _ _)
  · exact le_trans (hfar τ t hτ ht htT hsep (Or.inl (not_lt.mp h1)))
      (le_max_left _ _)

end Work.HFN.HalfFunnel
