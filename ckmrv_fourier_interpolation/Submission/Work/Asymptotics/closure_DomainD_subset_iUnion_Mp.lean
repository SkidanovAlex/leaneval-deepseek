/-
# The six translates of `𝓕` cover the closure of `𝒟`

CKMRV (Prop. 3.2(1), proof) write the `Γ(2)`-fundamental domain `𝒟` (their (3.12)) as the union
of the six `SL(2,ℤ)`-translates of the standard fundamental domain `𝓕` (their (3.13)), cut out by
`M' = (I, T⁻¹, STS, S, ST⁻¹, TS)`.  The companion file `Mp_smul_mem_closure_DomainD` proves the
containment `Mp i • closure 𝓕 ⊆ closure 𝒟`; the present file proves the converse covering
statement

  `closure 𝒟 ⊆ ⋃ i, Mp i • closure 𝓕`,

i.e. that the six *closed* translates of `𝓕` already cover `closure 𝒟`.

The route is elementary geometry.  Since `⋃ i, Mp i '' closure 𝓕` is closed (a finite union of
images of a closed set under the homeomorphisms `τ ↦ Mp i • τ`), it suffices to cover the open
domain `𝒟`, and the covering is read off pointwise:

* if `Re z ≥ 0` then `z` lies in the translate `Mp 0 • 𝓕` (identity) when `|z| ≥ 1` (left half of
  the right half-strip) resp. `|z - 1| ≥ 1`, and otherwise in `Mp 4 • 𝓕` resp. `Mp 5 • 𝓕`;
* if `Re z ≤ 0` then `z` lies in `Mp 1 • 𝓕` (`z ↦ z + 1`) when `|z| ≥ 1` resp. `|z + 1| ≥ 1`, and
  otherwise in `Mp 3 • 𝓕` (`z ↦ -1/z`) resp. `Mp 2 • 𝓕`.

The pointwise statements are proved for the inverse transports
`(Mp i)⁻¹ • z ∈ closure 𝓕 = {0 ≤ Re ≤ 1, |z| ≥ 1, |z - 1| ≥ 1}`, which avoids having to produce
the witnesses in `ℍ` by hand; the characteristic function of `closure 𝓕` is established once
(`closure_DomainF_eq`) by an explicit "push into the interior" construction.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainTiling
import Submission.Work.Asymptotics.Mp_smul_mem_closure_DomainD

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-! ### Elementary comparisons of `‖·‖` with `normSq` -/

private lemma one_lt_norm_iff {v : ℂ} : 1 < ‖v‖ ↔ 1 < Complex.normSq v := by
  rw [Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg v]

private lemma one_le_norm_iff {v : ℂ} : 1 ≤ ‖v‖ ↔ 1 ≤ Complex.normSq v := by
  rw [Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg v]

/-! ### The action of `S`, `T`, `T⁻¹` on the coordinates -/

private lemma coe_T_smul (z : ℍ) : (((T : SL(2,ℤ)) • z : ℍ) : ℂ) = (z:ℂ) + 1 := by
  have h := ModularGroup.coe_T_zpow_smul_eq z (n := 1)
  simpa using h

private lemma coe_T_inv_smul (z : ℍ) : (((T⁻¹ : SL(2,ℤ)) • z : ℍ) : ℂ) = (z:ℂ) - 1 := by
  have h := ModularGroup.coe_T_zpow_smul_eq z (n := -1)
  rw [sub_eq_add_neg]
  simpa using h

private lemma coe_S_smul (z : ℍ) : (((S : SL(2,ℤ)) • z : ℍ) : ℂ) = -((z:ℂ))⁻¹ := by
  have h := modular_S_smul z
  rw [h]
  simp

/-! ### The coordinate formulas for the six inverse transports `(Mp i)⁻¹` -/

private lemma inv_Mp0 (z : ℍ) : (((Mp 0)⁻¹ • z : ℍ) : ℂ) = (z:ℂ) := by
  rw [show (Mp 0)⁻¹ = 1 by decide, one_smul]

private lemma inv_Mp1 (z : ℍ) : (((Mp 1)⁻¹ • z : ℍ) : ℂ) = (z:ℂ) + 1 := by
  rw [show (Mp 1)⁻¹ = T by decide, coe_T_smul]

private lemma inv_Mp2 (z : ℍ) : (((Mp 2)⁻¹ • z : ℍ) : ℂ) = (z:ℂ) / (1 + (z:ℂ)) := by
  rw [show (Mp 2)⁻¹ = S * T⁻¹ * S by decide, mul_smul, mul_smul, coe_S_smul, coe_T_inv_smul,
    coe_S_smul]
  have hz : (z:ℂ) ≠ 0 := z.ne_zero
  have h1 : (1 + (z:ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [UpperHalfPlane.coe_im] at this
    linarith [z.im_pos]
  have h2 : (-1 - (z:ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [UpperHalfPlane.coe_im] at this
    linarith [z.im_pos]
  field_simp
  ring

private lemma inv_Mp3 (z : ℍ) : (((Mp 3)⁻¹ • z : ℍ) : ℂ) = -((z:ℂ))⁻¹ := by
  rw [show (Mp 3)⁻¹ = -S by decide, SL_neg_smul, coe_S_smul]

private lemma inv_Mp4 (z : ℍ) : (((Mp 4)⁻¹ • z : ℍ) : ℂ) = 1 - ((z:ℂ))⁻¹ := by
  rw [show (Mp 4)⁻¹ = -(T * S) by decide, SL_neg_smul, mul_smul, coe_T_smul, coe_S_smul]
  ring

private lemma inv_Mp5 (z : ℍ) : (((Mp 5)⁻¹ • z : ℍ) : ℂ) = -((z:ℂ) - 1)⁻¹ := by
  rw [show (Mp 5)⁻¹ = -(S * T⁻¹) by decide, SL_neg_smul, mul_smul, coe_S_smul, coe_T_inv_smul]

/-! ### Coordinate formulas for `z`, `z - 1`, `z + 1`, `1 + z` -/

private lemma normSq_coe (z : ℍ) : Complex.normSq (z:ℂ) = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring

private lemma normSq_coe_sub_one (z : ℍ) :
    Complex.normSq ((z:ℂ) - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring

private lemma normSq_coe_add_one (z : ℍ) :
    Complex.normSq ((z:ℂ) + 1) = (z.re + 1) ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring

private lemma normSq_one_add_coe (z : ℍ) :
    Complex.normSq (1 + (z:ℂ)) = (1 + z.re) ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring

private lemma normSq_sub_half (z : ℍ) :
    Complex.normSq ((z:ℂ) - (1/2 : ℂ)) = (z.re - 1/2) ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma normSq_add_half (z : ℍ) :
    Complex.normSq ((z:ℂ) + (1/2 : ℂ)) = (z.re + 1/2) ^ 2 + z.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  norm_num
  ring

/-! ### The closure of `𝓕` -/

/-- The closure of the standard fundamental domain `𝓕` is described by the four non-strict
inequalities defining it. -/
private lemma closure_DomainF_eq :
    closure DomainF = {z : ℍ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ ‖(z : ℂ)‖ ∧ 1 ≤ ‖(z : ℂ) - 1‖} := by
  refine subset_antisymm ?_ ?_
  · refine closure_minimal (fun z hz => ?_) ?_
    · rw [mem_DomainF] at hz
      exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
    · have h1 : IsClosed {z : ℍ | 0 ≤ z.re} :=
        isClosed_le continuous_const UpperHalfPlane.continuous_re
      have h2 : IsClosed {z : ℍ | z.re ≤ 1} :=
        isClosed_le UpperHalfPlane.continuous_re continuous_const
      have h3 : IsClosed {z : ℍ | 1 ≤ ‖(z : ℂ)‖} :=
        isClosed_le continuous_const (continuous_norm.comp continuous_coe)
      have h4 : IsClosed {z : ℍ | 1 ≤ ‖(z : ℂ) - 1‖} :=
        isClosed_le continuous_const (continuous_norm.comp (continuous_coe.sub continuous_const))
      simpa only [Set.ofPred_and] using h1.inter (h2.inter (h3.inter h4))
  · rintro z ⟨hx0, hx1, hn0, hn1⟩
    have hy : 0 < z.im := z.im_pos
    have hns0 : (1:ℝ) ≤ z.re ^ 2 + z.im ^ 2 := by
      have h : (1:ℝ) ≤ Complex.normSq (z:ℂ) := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (z:ℂ)]
      rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
      nlinarith
    have hns1 : (1:ℝ) ≤ (1 - z.re) ^ 2 + z.im ^ 2 := by
      have h : (1:ℝ) ≤ Complex.normSq ((z:ℂ) - 1) := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ((z:ℂ) - 1)]
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
      nlinarith
    let w : ℝ → ℂ := fun t =>
      (((1 - |t|) * z.re + |t| / 2 : ℝ) : ℂ) + ((z.im + |t| : ℝ) : ℂ) * Complex.I
    have hwim : ∀ t : ℝ, (w t).im = z.im + |t| := by
      intro t
      simp only [w, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
      ring
    have hwre : ∀ t : ℝ, (w t).re = (1 - |t|) * z.re + |t| / 2 := by
      intro t
      simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
      ring
    let F : ℝ → ℍ := fun t => ⟨w t, by rw [hwim t]; positivity⟩
    have hFcoe : ∀ t : ℝ, ((F t : ℍ) : ℂ) = w t := fun t => UpperHalfPlane.coe_mk _ _
    have hcont : Continuous F := by
      refine (UpperHalfPlane.isEmbedding_coe.continuous_iff).mpr ?_
      show Continuous fun t : ℝ =>
        (((1 - |t|) * z.re + |t| / 2 : ℝ) : ℂ) + ((z.im + |t| : ℝ) : ℂ) * Complex.I
      fun_prop
    have hmem : ∀ t : ℝ, 0 < t → t < 1 → F t ∈ DomainF := by
      intro t ht0 ht1
      have htabs : |t| = t := abs_of_pos ht0
      rw [mem_DomainF]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← UpperHalfPlane.coe_re, hFcoe t, hwre t, htabs]
        nlinarith [hx0, hx1, ht0, ht1]
      · rw [← UpperHalfPlane.coe_re, hFcoe t, hwre t, htabs]
        nlinarith [hx0, hx1, ht0, ht1]
      · rw [one_lt_norm_iff, hFcoe t]
        have hns : Complex.normSq (w t) = ((1 - t) * z.re + t / 2) ^ 2 + (z.im + t) ^ 2 := by
          rw [Complex.normSq_apply, hwre t, hwim t, htabs]
          ring
        rw [hns]
        have hB : z.im ^ 2 < (z.im + t) ^ 2 := by nlinarith
        by_cases hz : z.re ≤ 1 / 2
        · have hxt : z.re ≤ (1 - t) * z.re + t / 2 := by nlinarith
          have hsum : 0 ≤ ((1 - t) * z.re + t / 2) + z.re := by nlinarith
          have hA : z.re ^ 2 ≤ ((1 - t) * z.re + t / 2) ^ 2 := by nlinarith [hxt, hsum]
          nlinarith [hns0, hA, hB]
        · have hz' : 1 / 2 < z.re := not_le.mp hz
          have hxt : 1 - z.re ≤ (1 - t) * z.re + t / 2 := by nlinarith
          have hsum : 0 ≤ ((1 - t) * z.re + t / 2) + (1 - z.re) := by nlinarith
          have hA : (1 - z.re) ^ 2 ≤ ((1 - t) * z.re + t / 2) ^ 2 := by nlinarith [hxt, hsum]
          nlinarith [hns1, hA, hB]
      · rw [one_lt_norm_iff, hFcoe t]
        have hns : Complex.normSq (w t - 1) =
            ((1 - t) * z.re + t / 2 - 1) ^ 2 + (z.im + t) ^ 2 := by
          rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
            hwre t, hwim t, htabs]
          ring
        rw [hns]
        have hB : z.im ^ 2 < (z.im + t) ^ 2 := by nlinarith
        by_cases hz : z.re ≤ 1 / 2
        · have hxt : z.re ≤ 1 - ((1 - t) * z.re + t / 2) := by nlinarith
          have hsum : 0 ≤ (1 - ((1 - t) * z.re + t / 2)) + z.re := by nlinarith
          have hA : z.re ^ 2 ≤ ((1 - t) * z.re + t / 2 - 1) ^ 2 := by nlinarith [hxt, hsum]
          nlinarith [hns0, hA, hB]
        · have hz' : 1 / 2 < z.re := not_le.mp hz
          have hxt : (1 - t) * z.re + t / 2 - 1 ≤ -(1 - z.re) := by nlinarith
          have hsum : 0 ≤ -(1 - z.re) - ((1 - t) * z.re + t / 2 - 1) := by nlinarith
          have hA : (1 - z.re) ^ 2 ≤ ((1 - t) * z.re + t / 2 - 1) ^ 2 := by nlinarith [hxt, hsum]
          nlinarith [hns1, hA, hB]
    have hw0 : F 0 = z := by
      apply UpperHalfPlane.coe_injective
      rw [hFcoe 0]
      simp only [w, abs_zero, zero_div, sub_zero, one_mul, zero_add, add_zero]
      exact Complex.re_add_im (z:ℂ)
    have h0mem : (0:ℝ) ∈ closure (Set.Ioo (0:ℝ) 1) := by
      rw [closure_Ioo (by norm_num)]; exact ⟨le_refl 0, zero_le_one⟩
    have himg : F 0 ∈ closure (F '' Set.Ioo (0:ℝ) 1) :=
      mem_closure_image hcont.continuousAt h0mem
    have hsub : F '' Set.Ioo (0:ℝ) 1 ⊆ DomainF := by
      rintro _ ⟨t, ht, rfl⟩
      exact hmem t ht.1 ht.2
    have hfin : F 0 ∈ closure DomainF := closure_mono hsub himg
    rwa [hw0] at hfin

/-! ### The two "arc" conditions satisfied on `𝒟` -/

private lemma arc_right_of_mem_DomainD {z : ℍ} (hz : z ∈ DomainD) :
    z.re * (1 - z.re) ≤ z.im ^ 2 := by
  obtain ⟨-, -, h3, -⟩ := hz
  have h : (1 / 4 : ℝ) ≤ (z.re - 1/2) ^ 2 + z.im ^ 2 := by
    have hh : (1 / 4 : ℝ) ≤ Complex.normSq ((z:ℂ) - (1/2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((z:ℂ) - (1/2 : ℂ))]
    rwa [normSq_sub_half] at hh
  nlinarith

private lemma arc_left_of_mem_DomainD {z : ℍ} (hz : z ∈ DomainD) :
    -(z.re) * (1 + z.re) ≤ z.im ^ 2 := by
  obtain ⟨-, -, -, h4⟩ := hz
  have h : (1 / 4 : ℝ) ≤ (z.re + 1/2) ^ 2 + z.im ^ 2 := by
    have hh : (1 / 4 : ℝ) ≤ Complex.normSq ((z:ℂ) + (1/2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((z:ℂ) + (1/2 : ℂ))]
    rwa [normSq_add_half] at hh
  nlinarith

/-! ### The six pointwise covering statements -/

/-- Right half-strip, `0 ≤ Re z ≤ 1/2`, `|z| ≥ 1`: the identity covers. -/
private lemma case_R1 {z : ℍ} (hx0 : 0 ≤ z.re) (hx : z.re ≤ 1/2) (hn : 1 ≤ ‖(z:ℂ)‖) :
    (Mp 0)⁻¹ • z ∈ closure DomainF := by
  have hid : (Mp 0)⁻¹ • z = z := by rw [show (Mp 0)⁻¹ = 1 by decide, one_smul]
  rw [hid, closure_DomainF_eq]
  refine ⟨hx0, by linarith, hn, ?_⟩
  rw [one_le_norm_iff]
  rw [one_le_norm_iff, normSq_coe] at hn
  rw [normSq_coe_sub_one]
  nlinarith

/-- Right half-strip, `1/2 ≤ Re z ≤ 1`, `|z - 1| ≥ 1`: the identity covers. -/
private lemma case_R3 {z : ℍ} (hx : 1/2 ≤ z.re) (hx1 : z.re ≤ 1) (hn : 1 ≤ ‖(z:ℂ) - 1‖) :
    (Mp 0)⁻¹ • z ∈ closure DomainF := by
  have hid : (Mp 0)⁻¹ • z = z := by rw [show (Mp 0)⁻¹ = 1 by decide, one_smul]
  rw [hid, closure_DomainF_eq]
  refine ⟨by linarith, hx1, ?_, hn⟩
  rw [one_le_norm_iff]
  rw [one_le_norm_iff, normSq_coe_sub_one] at hn
  rw [normSq_coe]
  nlinarith

/-- Right half-strip, `0 ≤ Re z ≤ 1/2`, `|z| ≤ 1`: the translate `Mp 4 • 𝓕` covers. -/
private lemma case_R2 {z : ℍ} (hx0 : 0 ≤ z.re) (hx : z.re ≤ 1/2) (hn : ‖(z:ℂ)‖ ≤ 1)
    (harc : z.re * (1 - z.re) ≤ z.im ^ 2) : (Mp 4)⁻¹ • z ∈ closure DomainF := by
  set w : ℍ := (Mp 4)⁻¹ • z with hwdef
  have hwcoe : (w : ℂ) = 1 - ((z:ℂ))⁻¹ := by rw [hwdef]; exact inv_Mp4 z
  have hz : (z:ℂ) ≠ 0 := z.ne_zero
  have hzpos : 0 < Complex.normSq (z:ℂ) := Complex.normSq_pos.mpr hz
  have hzns : Complex.normSq (z:ℂ) = z.re ^ 2 + z.im ^ 2 := normSq_coe z
  have hz1ns : Complex.normSq ((z:ℂ) - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := normSq_coe_sub_one z
  have hre : w.re = 1 - z.re / Complex.normSq (z:ℂ) := by
    rw [← UpperHalfPlane.coe_re, hwcoe, Complex.sub_re, Complex.one_re, Complex.inv_re,
      UpperHalfPlane.coe_re]
  rw [closure_DomainF_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    have hkey : z.re ≤ Complex.normSq (z:ℂ) := by rw [hzns]; nlinarith
    have := (div_le_one hzpos).mpr hkey
    linarith
  · rw [hre]
    have : 0 ≤ z.re / Complex.normSq (z:ℂ) := div_nonneg hx0 hzpos.le
    linarith
  · rw [one_le_norm_iff, hwcoe]
    have hsplit : (1:ℂ) - ((z:ℂ))⁻¹ = ((z:ℂ) - 1) / (z:ℂ) := by field_simp
    rw [hsplit, Complex.normSq_div, le_div_iff₀ hzpos, one_mul, hz1ns, hzns]
    nlinarith
  · rw [one_le_norm_iff, hwcoe]
    have hsplit : (1:ℂ) - ((z:ℂ))⁻¹ - 1 = -((z:ℂ))⁻¹ := by ring
    rw [hsplit, Complex.normSq_neg, Complex.normSq_inv]
    have hle : Complex.normSq (z:ℂ) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (z:ℂ)]
    exact (one_le_inv₀ hzpos).mpr hle

/-- Right half-strip, `1/2 ≤ Re z ≤ 1`, `|z - 1| ≤ 1`: the translate `Mp 5 • 𝓕` covers. -/
private lemma case_R4 {z : ℍ} (hx : 1/2 ≤ z.re) (hx1 : z.re ≤ 1) (hn : ‖(z:ℂ) - 1‖ ≤ 1)
    (harc : z.re * (1 - z.re) ≤ z.im ^ 2) : (Mp 5)⁻¹ • z ∈ closure DomainF := by
  set w : ℍ := (Mp 5)⁻¹ • z with hwdef
  have hwcoe : (w : ℂ) = -((z:ℂ) - 1)⁻¹ := by rw [hwdef]; exact inv_Mp5 z
  have hz1 : (z:ℂ) - 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [UpperHalfPlane.coe_im] at him
    linarith [z.im_pos]
  have hz1pos : 0 < Complex.normSq ((z:ℂ) - 1) := Complex.normSq_pos.mpr hz1
  have hzns : Complex.normSq (z:ℂ) = z.re ^ 2 + z.im ^ 2 := normSq_coe z
  have hz1ns : Complex.normSq ((z:ℂ) - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := normSq_coe_sub_one z
  have hre : w.re = -((z.re - 1) / Complex.normSq ((z:ℂ) - 1)) := by
    rw [← UpperHalfPlane.coe_re, hwcoe, Complex.neg_re, Complex.inv_re, Complex.sub_re,
      Complex.one_re, UpperHalfPlane.coe_re]
  rw [closure_DomainF_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    have : (z.re - 1) / Complex.normSq ((z:ℂ) - 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hz1pos.le
    linarith
  · rw [hre, ← neg_div]
    have hkey : -(z.re - 1) ≤ Complex.normSq ((z:ℂ) - 1) := by rw [hz1ns]; nlinarith
    exact (div_le_one hz1pos).mpr hkey
  · rw [one_le_norm_iff, hwcoe]
    rw [Complex.normSq_neg, Complex.normSq_inv]
    have hle : Complex.normSq ((z:ℂ) - 1) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ((z:ℂ) - 1)]
    exact (one_le_inv₀ hz1pos).mpr hle
  · rw [one_le_norm_iff, hwcoe]
    have hsplit : -((z:ℂ) - 1)⁻¹ - 1 = -(z:ℂ) / ((z:ℂ) - 1) := by field_simp; ring
    rw [hsplit, Complex.normSq_div, Complex.normSq_neg, le_div_iff₀ hz1pos, one_mul, hzns, hz1ns]
    nlinarith

/-- Left half-strip, `-1/2 ≤ Re z ≤ 0`, `|z| ≥ 1`: the translate `Mp 1 • 𝓕` covers. -/
private lemma case_L1 {z : ℍ} (hx0 : -1/2 ≤ z.re) (hx : z.re ≤ 0) (hn : 1 ≤ ‖(z:ℂ)‖) :
    (Mp 1)⁻¹ • z ∈ closure DomainF := by
  set w : ℍ := (Mp 1)⁻¹ • z with hwdef
  have hwcoe : (w : ℂ) = (z:ℂ) + 1 := by rw [hwdef]; exact inv_Mp1 z
  have hzns : Complex.normSq (z:ℂ) = z.re ^ 2 + z.im ^ 2 := normSq_coe z
  have hzans : Complex.normSq ((z:ℂ) + 1) = (z.re + 1) ^ 2 + z.im ^ 2 := normSq_coe_add_one z
  have hre : w.re = z.re + 1 := by
    rw [← UpperHalfPlane.coe_re, hwcoe, Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re]
  rw [closure_DomainF_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; linarith
  · rw [hre]; linarith
  · rw [one_le_norm_iff, hwcoe, hzans]
    rw [one_le_norm_iff, normSq_coe] at hn
    nlinarith
  · rw [one_le_norm_iff, hwcoe]
    have hsplit : (z:ℂ) + 1 - 1 = (z:ℂ) := by ring
    rw [hsplit, ← one_le_norm_iff]
    exact hn

/-- Left half-strip, `-1 ≤ Re z ≤ -1/2`, `|z + 1| ≥ 1`: the translate `Mp 1 • 𝓕` covers. -/
private lemma case_L3 {z : ℍ} (hx0 : -1 ≤ z.re) (hx : z.re ≤ -1/2) (hn : 1 ≤ ‖(z:ℂ) + 1‖) :
    (Mp 1)⁻¹ • z ∈ closure DomainF := by
  set w : ℍ := (Mp 1)⁻¹ • z with hwdef
  have hwcoe : (w : ℂ) = (z:ℂ) + 1 := by rw [hwdef]; exact inv_Mp1 z
  have hzns : Complex.normSq (z:ℂ) = z.re ^ 2 + z.im ^ 2 := normSq_coe z
  have hzans : Complex.normSq ((z:ℂ) + 1) = (z.re + 1) ^ 2 + z.im ^ 2 := normSq_coe_add_one z
  have hre : w.re = z.re + 1 := by
    rw [← UpperHalfPlane.coe_re, hwcoe, Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re]
  rw [closure_DomainF_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; linarith
  · rw [hre]; linarith
  · rw [one_le_norm_iff, hwcoe, hzans]
    rw [one_le_norm_iff, hzans] at hn
    exact hn
  · rw [one_le_norm_iff, hwcoe]
    have hsplit : (z:ℂ) + 1 - 1 = (z:ℂ) := by ring
    rw [hsplit, normSq_coe]
    rw [one_le_norm_iff, hzans] at hn
    nlinarith

/-- Left half-strip, `-1/2 ≤ Re z ≤ 0`, `|z| ≤ 1`: the translate `Mp 3 • 𝓕` covers. -/
private lemma case_L2 {z : ℍ} (hx0 : -1/2 ≤ z.re) (hx : z.re ≤ 0) (hn : ‖(z:ℂ)‖ ≤ 1)
    (harc : -(z.re) * (1 + z.re) ≤ z.im ^ 2) : (Mp 3)⁻¹ • z ∈ closure DomainF := by
  set w : ℍ := (Mp 3)⁻¹ • z with hwdef
  have hwcoe : (w : ℂ) = -((z:ℂ))⁻¹ := by rw [hwdef]; exact inv_Mp3 z
  have hz : (z:ℂ) ≠ 0 := z.ne_zero
  have hzpos : 0 < Complex.normSq (z:ℂ) := Complex.normSq_pos.mpr hz
  have hzns : Complex.normSq (z:ℂ) = z.re ^ 2 + z.im ^ 2 := normSq_coe z
  have hzans : Complex.normSq ((z:ℂ) + 1) = (z.re + 1) ^ 2 + z.im ^ 2 := normSq_coe_add_one z
  have hre : w.re = -(z.re / Complex.normSq (z:ℂ)) := by
    rw [← UpperHalfPlane.coe_re, hwcoe, Complex.neg_re, Complex.inv_re, UpperHalfPlane.coe_re]
  rw [closure_DomainF_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    have : z.re / Complex.normSq (z:ℂ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx hzpos.le
    linarith
  · rw [hre, ← neg_div]
    have hkey : -z.re ≤ Complex.normSq (z:ℂ) := by rw [hzns]; nlinarith
    exact (div_le_one hzpos).mpr hkey
  · rw [one_le_norm_iff, hwcoe]
    rw [Complex.normSq_neg, Complex.normSq_inv]
    have hle : Complex.normSq (z:ℂ) ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (z:ℂ)]
    exact (one_le_inv₀ hzpos).mpr hle
  · rw [one_le_norm_iff, hwcoe]
    have hsplit : -((z:ℂ))⁻¹ - 1 = -((z:ℂ) + 1) / (z:ℂ) := by field_simp; ring
    rw [hsplit, Complex.normSq_div, Complex.normSq_neg, le_div_iff₀ hzpos, one_mul, hzans, hzns]
    nlinarith

/-- Left half-strip, `-1 ≤ Re z ≤ -1/2`, `|z + 1| ≤ 1`: the translate `Mp 2 • 𝓕` covers. -/
private lemma case_L4 {z : ℍ} (hx0 : -1 ≤ z.re) (hx : z.re ≤ -1/2) (hn : ‖(z:ℂ) + 1‖ ≤ 1)
    (harc : -(z.re) * (1 + z.re) ≤ z.im ^ 2) : (Mp 2)⁻¹ • z ∈ closure DomainF := by
  set w : ℍ := (Mp 2)⁻¹ • z with hwdef
  have hwcoe : (w : ℂ) = (z:ℂ) / (1 + (z:ℂ)) := by rw [hwdef]; exact inv_Mp2 z
  have hz1 : (1 + (z:ℂ)) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [UpperHalfPlane.coe_im] at him
    linarith [z.im_pos]
  have hz1pos : 0 < Complex.normSq (1 + (z:ℂ)) := Complex.normSq_pos.mpr hz1
  have hzns : Complex.normSq (z:ℂ) = z.re ^ 2 + z.im ^ 2 := normSq_coe z
  have hzans : Complex.normSq (1 + (z:ℂ)) = (1 + z.re) ^ 2 + z.im ^ 2 := normSq_one_add_coe z
  have hre : w.re = (z.re * (1 + z.re) + z.im * z.im) / Complex.normSq (1 + (z:ℂ)) := by
    rw [← UpperHalfPlane.coe_re, hwcoe, Complex.div_re, normSq_one_add_coe, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  rw [closure_DomainF_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    have hnum : 0 ≤ z.re * (1 + z.re) + z.im * z.im := by nlinarith
    exact div_nonneg hnum hz1pos.le
  · rw [hre]
    have hkey : z.re * (1 + z.re) + z.im * z.im ≤ Complex.normSq (1 + (z:ℂ)) := by
      rw [hzans]; nlinarith
    exact (div_le_one hz1pos).mpr hkey
  · rw [one_le_norm_iff, hwcoe]
    rw [Complex.normSq_div, le_div_iff₀ hz1pos, one_mul, hzns, hzans]
    nlinarith
  · rw [one_le_norm_iff, hwcoe]
    have hsplit : (z:ℂ) / (1 + (z:ℂ)) - 1 = -(1 + (z:ℂ))⁻¹ := by field_simp; ring
    rw [hsplit, Complex.normSq_neg, Complex.normSq_inv]
    have hle : Complex.normSq (1 + (z:ℂ)) ≤ 1 := by
      have h' : ‖1 + (z:ℂ)‖ ≤ 1 := by simpa [add_comm] using hn
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (1 + (z:ℂ))]
    exact (one_le_inv₀ hz1pos).mpr hle

/-! ### The covering theorem -/

theorem closure_DomainD_subset_iUnion_Mp :
    closure Work.Asymptotics.DomainD ⊆
      ⋃ i : Fin 6, (fun τ : UpperHalfPlane => (Work.Asymptotics.Mp i) • τ) ''
        (closure Work.Asymptotics.DomainF) := by
  haveI : ContinuousSMul SL(2, ℤ) ℍ :=
    MulAction.continuousSMul_compHom (f := SpecialLinearGroup.mapGL ℝ)
      continuous_of_discreteTopology
  -- the union of the six closed translates is closed
  have hclosed : IsClosed (⋃ i : Fin 6, (fun τ : ℍ => Mp i • τ) '' closure DomainF) := by
    refine isClosed_iUnion_of_finite (fun i => ?_)
    have hset : (fun τ : ℍ => Mp i • τ) '' closure DomainF =
        (fun τ : ℍ => (Mp i)⁻¹ • τ) ⁻¹' closure DomainF := by
      ext τ
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        show (Mp i)⁻¹ • (Mp i • σ) ∈ closure DomainF
        rw [← mul_smul, inv_mul_cancel, one_smul]
        exact hσ
      · intro h
        refine ⟨(Mp i)⁻¹ • τ, h, ?_⟩
        show Mp i • ((Mp i)⁻¹ • τ) = τ
        rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [hset]
    exact isClosed_closure.preimage (continuous_const_smul (Mp i)⁻¹)
  refine closure_minimal ?_ hclosed
  intro z hz
  have hzD : z ∈ DomainD := hz
  rw [mem_DomainD] at hz
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  have harc1 : z.re * (1 - z.re) ≤ z.im ^ 2 := arc_right_of_mem_DomainD hzD
  have harc2 : -(z.re) * (1 + z.re) ≤ z.im ^ 2 := arc_left_of_mem_DomainD hzD
  have key : ∀ (i : Fin 6), (Mp i)⁻¹ • z ∈ closure DomainF →
      z ∈ (fun τ : ℍ => Mp i • τ) '' closure DomainF := by
    intro i h
    refine ⟨(Mp i)⁻¹ • z, h, ?_⟩
    show Mp i • ((Mp i)⁻¹ • z) = z
    rw [← mul_smul, mul_inv_cancel, one_smul]
  rw [Set.mem_iUnion]
  by_cases hright : 0 ≤ z.re
  · by_cases hhalf : z.re ≤ 1 / 2
    · by_cases hn : 1 ≤ ‖(z:ℂ)‖
      · exact ⟨0, key 0 (case_R1 hright hhalf hn)⟩
      · have hn' : ‖(z:ℂ)‖ ≤ 1 := (not_le.mp hn).le
        exact ⟨4, key 4 (case_R2 hright hhalf hn' harc1)⟩
    · have hhalf' : 1 / 2 ≤ z.re := (not_le.mp hhalf).le
      by_cases hn : 1 ≤ ‖(z:ℂ) - 1‖
      · exact ⟨0, key 0 (case_R3 hhalf' hz2.le hn)⟩
      · have hn' : ‖(z:ℂ) - 1‖ ≤ 1 := (not_le.mp hn).le
        exact ⟨5, key 5 (case_R4 hhalf' hz2.le hn' harc1)⟩
  · have hleft : z.re < 0 := not_le.mp hright
    by_cases hhalf : -1 / 2 ≤ z.re
    · by_cases hn : 1 ≤ ‖(z:ℂ)‖
      · exact ⟨1, key 1 (case_L1 hhalf hleft.le hn)⟩
      · have hn' : ‖(z:ℂ)‖ ≤ 1 := (not_le.mp hn).le
        exact ⟨3, key 3 (case_L2 hhalf hleft.le hn' harc2)⟩
    · have hhalf' : z.re ≤ -1 / 2 := (not_le.mp hhalf).le
      by_cases hn : 1 ≤ ‖(z:ℂ) + 1‖
      · exact ⟨1, key 1 (case_L3 hz1.le hhalf' hn)⟩
      · have hn' : ‖(z:ℂ) + 1‖ ≤ 1 := (not_le.mp hn).le
        exact ⟨2, key 2 (case_L4 hz1.le hhalf' hn' harc2)⟩

end Work.Asymptotics
