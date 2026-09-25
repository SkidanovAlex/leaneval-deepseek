import Mathlib
import Submission.Work.NN.Newton.pushforward_setup
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.NN.Final.holderNorm_one_comp_le

/-!
# Componentwise Hölder norms for vector- and operator-valued functions

`vNorm k α F Ω` is the sum over the components of the `C^{k,α}`-norms of `F : ℂⁿ → ℂⁿ` on `Ω`;
`mNorm k α T Ω` is the sum over the components of the `C^{k,α}`-norms of the two families
`(T z e_j)`, `(T z (i e_j))` (the values on the real basis) together with those of the
coefficient families `linCoef (T z) p`, `antiCoef (T z) p` (the `ℂ`-linear and `ℂ`-antilinear
coefficients of `T z`).

These bookkeeping norms let the calculus of `pushforward_small` be done in a few steps instead of
term by term.
-/

noncomputable section

set_option maxHeartbeats 1600000

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

open Work.NN.Core

variable {n : ℕ}

/-- Componentwise `C^{k,α}` size of a vector-valued function. -/
noncomputable def vNorm (k : ℕ) (α : ℝ) (F : Cn n → Cn n) (Ω : Set (Cn n)) : ℝ≥0∞ :=
  ∑ j, Work.CR.Flat.holderNorm k α (fun z => F z j) Ω

lemma vNorm_apply_le (k : ℕ) (α : ℝ) (F : Cn n → Cn n) (Ω : Set (Cn n)) (j : Fin n) :
    Work.CR.Flat.holderNorm k α (fun z => F z j) Ω ≤ vNorm k α F Ω :=
  Finset.single_le_sum (f := fun j => Work.CR.Flat.holderNorm k α (fun z => F z j) Ω)
    (fun _ _ => bot_le) (Finset.mem_univ j)

lemma vNorm_le_sum (k : ℕ) (α : ℝ) (F : Cn n → Cn n) (Ω : Set (Cn n)) (c : Fin n → ℝ≥0∞)
    (h : ∀ j, Work.CR.Flat.holderNorm k α (fun z => F z j) Ω ≤ c j) :
    vNorm k α F Ω ≤ ∑ j, c j :=
  Finset.sum_le_sum fun j _ => h j

/-! ## The coefficient vectors of a real-linear map -/

/-- The `ℂ`-linear coefficient vector of a real-linear map. -/
def linCoef (T : Cn n →L[ℝ] Cn n) (k : Fin n) : Cn n :=
  fun j => (1 / 2 : ℂ) * ((T (Pi.single k 1)) j - Complex.I * (T (Pi.single k (Complex.I : ℂ))) j)

/-- The `ℂ`-antilinear coefficient vector of a real-linear map. -/
def antiCoef (T : Cn n →L[ℝ] Cn n) (k : Fin n) : Cn n :=
  fun j => (1 / 2 : ℂ) * ((T (Pi.single k 1)) j + Complex.I * (T (Pi.single k (Complex.I : ℂ))) j)

lemma linCoef_apply (T : Cn n →L[ℝ] Cn n) (k : Fin n) (j : Fin n) :
    (linCoef T k) j
      = (1 / 2 : ℂ) * ((T (Pi.single k 1)) j - Complex.I * (T (Pi.single k (Complex.I : ℂ))) j) :=
  rfl

lemma antiCoef_apply (T : Cn n →L[ℝ] Cn n) (k : Fin n) (j : Fin n) :
    (antiCoef T k) j
      = (1 / 2 : ℂ) * ((T (Pi.single k 1)) j + Complex.I * (T (Pi.single k (Complex.I : ℂ))) j) :=
  rfl

lemma re_eq_add_conj (u : ℂ) : ((u + Complex.conjCLE u) / 2) = (u.re : ℂ) := by
  rw [Complex.conjCLE_apply, Complex.add_conj]
  push_cast
  ring

lemma im_eq_sub_conj (u : ℂ) : ((u - Complex.conjCLE u) / (2 * Complex.I)) = (u.im : ℂ) := by
  rw [Complex.conjCLE_apply, Complex.sub_conj]
  push_cast
  try field_simp
  try ring_nf

/-- **The real-basis decomposition of a real-linear map `ℂⁿ → ℂⁿ`**: every real-linear `T` is
the sum of its `ℂ`-linear and `ℂ`-antilinear parts, applied coefficientwise. -/
lemma clm_apply_eq_sum (T : Cn n →L[ℝ] Cn n) (u : Cn n) (j : Fin n) :
    (T u) j = ∑ p : Fin n,
      ((linCoef T p) j * u p + (antiCoef T p) j * Complex.conjCLE (u p)) := by
  have hdecomp : u = ∑ p, (((u p).re : ℝ) • (Pi.single p (1 : ℂ) : Cn n)
      + ((u p).im : ℝ) • (Pi.single p (Complex.I : ℂ) : Cn n)) := by
    funext m
    rw [Finset.sum_apply, Finset.sum_eq_single m]
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Complex.real_smul, mul_one]
      exact (Complex.re_add_im (u m)).symm
    · intro p _ hp
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hp), smul_zero,
        add_zero]
    · intro hm; exact absurd (Finset.mem_univ m) hm
  conv_lhs => rw [hdecomp]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  have hr : ((u p) + Complex.conjCLE (u p)) / 2 = ((u p).re : ℂ) := by
    rw [Complex.conjCLE_apply, Complex.add_conj]; push_cast; ring
  have hi : ((u p) - Complex.conjCLE (u p)) / (2 * Complex.I) = ((u p).im : ℂ) := by
    rw [Complex.conjCLE_apply, Complex.sub_conj]; push_cast; try field_simp; try ring_nf
  rw [← hr, ← hi, linCoef_apply, antiCoef_apply]
  field_simp
  ring_nf
  rw [show Complex.I ^ 2 = -1 from by rw [pow_two, Complex.I_mul_I]]
  ring

/-- Componentwise `C^{k,α}` size of a continuous-linear-map valued function. -/
noncomputable def mNorm (k : ℕ) (α : ℝ) (T : Cn n → Cn n →L[ℝ] Cn n) (Ω : Set (Cn n)) : ℝ≥0∞ :=
  (∑ j, vNorm k α (fun z => T z (Pi.single j 1)) Ω
    + ∑ j, vNorm k α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω)
  + ∑ p, (vNorm k α (fun z => linCoef (T z) p) Ω + vNorm k α (fun z => antiCoef (T z) p) Ω)

lemma mNorm_basis_le_one (k : ℕ) (α : ℝ) (T : Cn n → Cn n →L[ℝ] Cn n) (Ω : Set (Cn n))
    (j : Fin n) : vNorm k α (fun z => T z (Pi.single j 1)) Ω ≤ mNorm k α T Ω :=
  calc vNorm k α (fun z => T z (Pi.single j 1)) Ω
      ≤ ∑ j, vNorm k α (fun z => T z (Pi.single j 1)) Ω :=
        Finset.single_le_sum (f := fun j => vNorm k α (fun z => T z (Pi.single j 1)) Ω)
          (fun _ _ => bot_le) (Finset.mem_univ j)
    _ ≤ (∑ j, vNorm k α (fun z => T z (Pi.single j 1)) Ω
          + ∑ j, vNorm k α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω) := le_add_right le_rfl
    _ ≤ mNorm k α T Ω := le_add_right le_rfl

lemma mNorm_basis_le_I (k : ℕ) (α : ℝ) (T : Cn n → Cn n →L[ℝ] Cn n) (Ω : Set (Cn n))
    (j : Fin n) : vNorm k α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω ≤ mNorm k α T Ω :=
  calc vNorm k α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω
      ≤ ∑ j, vNorm k α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω :=
        Finset.single_le_sum (f := fun j => vNorm k α
          (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω) (fun _ _ => bot_le)
          (Finset.mem_univ j)
    _ ≤ (∑ j, vNorm k α (fun z => T z (Pi.single j 1)) Ω
          + ∑ j, vNorm k α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω) := le_add_left le_rfl
    _ ≤ mNorm k α T Ω := le_add_right le_rfl

lemma mNorm_coef_le (k : ℕ) (α : ℝ) (T : Cn n → Cn n →L[ℝ] Cn n) (Ω : Set (Cn n))
    (p : Fin n) : vNorm k α (fun z => linCoef (T z) p) Ω ≤ mNorm k α T Ω :=
  calc vNorm k α (fun z => linCoef (T z) p) Ω
      ≤ vNorm k α (fun z => linCoef (T z) p) Ω + vNorm k α (fun z => antiCoef (T z) p) Ω :=
        le_add_right le_rfl
    _ ≤ ∑ p, (vNorm k α (fun z => linCoef (T z) p) Ω
          + vNorm k α (fun z => antiCoef (T z) p) Ω) :=
        Finset.single_le_sum (f := fun p => vNorm k α (fun z => linCoef (T z) p) Ω
          + vNorm k α (fun z => antiCoef (T z) p) Ω) (fun _ _ => bot_le) (Finset.mem_univ p)
    _ ≤ mNorm k α T Ω := le_add_left le_rfl

lemma mNorm_anti_le (k : ℕ) (α : ℝ) (T : Cn n → Cn n →L[ℝ] Cn n) (Ω : Set (Cn n))
    (p : Fin n) : vNorm k α (fun z => antiCoef (T z) p) Ω ≤ mNorm k α T Ω :=
  calc vNorm k α (fun z => antiCoef (T z) p) Ω
      ≤ vNorm k α (fun z => linCoef (T z) p) Ω + vNorm k α (fun z => antiCoef (T z) p) Ω :=
        le_add_left le_rfl
    _ ≤ ∑ p, (vNorm k α (fun z => linCoef (T z) p) Ω
          + vNorm k α (fun z => antiCoef (T z) p) Ω) :=
        Finset.single_le_sum (f := fun p => vNorm k α (fun z => linCoef (T z) p) Ω
          + vNorm k α (fun z => antiCoef (T z) p) Ω) (fun _ _ => bot_le) (Finset.mem_univ p)
    _ ≤ mNorm k α T Ω := le_add_left le_rfl

/-! ## The constant functions -/

lemma iteratedFDerivWithin_zero_const (c : ℂ) (Ω : Set (Cn n)) (y : Cn n) :
    iteratedFDerivWithin ℝ 0 (fun _ : Cn n => c) Ω y
      = ContinuousMultilinearMap.uncurry0 ℝ (Cn n) c := by
  ext m
  rw [iteratedFDerivWithin_zero_apply, ContinuousMultilinearMap.uncurry0_apply]

lemma iteratedFDerivWithin_one_const (c : ℂ) (Ω : Set (Cn n)) (x : Cn n) :
    iteratedFDerivWithin ℝ 1 (fun _ : Cn n => c) Ω x = 0 := by
  have h0 : iteratedFDerivWithin ℝ 0 (fun _ : Cn n => c) Ω
      = Function.const (Cn n) (ContinuousMultilinearMap.uncurry0 ℝ (Cn n) c) :=
    funext fun y => iteratedFDerivWithin_zero_const c Ω y
  ext m
  rw [iteratedFDerivWithin_succ_apply_left, h0, fderivWithin_const]
  rfl

lemma holderNorm_one_const_le {α : ℝ} (c : ℂ) (Ω : Set (Cn n)) :
    Work.CR.Flat.holderNorm 1 α (fun _ : Cn n => c) Ω ≤ ENNReal.ofReal ‖c‖ := by
  have hI0 : Work.CR.Flat.iterDerivNorm 0 (fun _ : Cn n => c) Ω ≤ ENNReal.ofReal ‖c‖ := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun x _ => le_rfl
  have hS0 : Work.CR.Flat.holderSeminorm 0 α (fun _ : Cn n => c) Ω ≤ 0 := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun _ => ?_
    rw [iteratedFDerivWithin_zero_const, iteratedFDerivWithin_zero_const, sub_self, norm_zero,
      zero_div]
    simp
  have hI1 : Work.CR.Flat.iterDerivNorm 1 (fun _ : Cn n => c) Ω ≤ 0 := by
    rw [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun x _ => ?_
    rw [iteratedFDerivWithin_one_const]
    simp
  have hS1 : Work.CR.Flat.holderSeminorm 1 α (fun _ : Cn n => c) Ω ≤ 0 := by
    rw [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun _ => ?_
    rw [iteratedFDerivWithin_one_const, iteratedFDerivWithin_one_const, sub_zero, norm_zero,
      zero_div]
    simp
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_one]
  refine (add_le_add (add_le_add hI0 hS0) (add_le_add hI1 hS1)).trans ?_
  simp

/-! ## Sums, scalar multiples, conjugation -/

lemma vNorm_add_le {k : ℕ} {α : ℝ} {F G : Cn n → Cn n} {Ω : Set (Cn n)}
    (hF : ∀ j, ContDiffOn ℝ (k : ℕ∞) (fun z => F z j) Ω)
    (hG : ∀ j, ContDiffOn ℝ (k : ℕ∞) (fun z => G z j) Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    vNorm k α (fun z => F z + G z) Ω ≤ vNorm k α F Ω + vNorm k α G Ω := by
  unfold vNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : (fun z => (F z + G z) j) = (fun z => F z j) + (fun z => G z j) := by
    funext z; rfl
  rw [h1]
  exact Work.CR.Flat.Holder.holderNorm_add_le (hF j) (hG j) hΩ

lemma vNorm_smul_const {k : ℕ} {α : ℝ} (c : ℂ) {F : Cn n → Cn n} {Ω : Set (Cn n)}
    (hF : ∀ j, ContDiffOn ℝ (k : ℕ∞) (fun z => F z j) Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    vNorm k α (fun z => c • F z) Ω = ENNReal.ofReal ‖c‖ * vNorm k α F Ω := by
  unfold vNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (fun z => (c • F z) j) = c • (fun z => F z j) := by
    funext z; rw [Pi.smul_apply, smul_eq_mul]; rfl
  rw [h1]
  exact Work.CR.Flat.Holder.holderNorm_smul c (hF j) hΩ

/-- Componentwise complex conjugation of a vector-valued function. -/
def conjVec (F : Cn n → Cn n) : Cn n → Cn n := fun z j => Complex.conjLIE (F z j)

lemma vNorm_conjVec_eq {k : ℕ} {α : ℝ} {F : Cn n → Cn n} {Ω : Set (Cn n)}
    (hΩ : UniqueDiffOn ℝ Ω) : vNorm k α (conjVec F) Ω = vNorm k α F Ω := by
  unfold vNorm conjVec
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := Work.CR.Flat.Holder.iDN_comp_lie Complex.conjLIE (fun z => F z j) i Ω hΩ
  have h2 := Work.CR.Flat.Holder.hSN_comp_lie Complex.conjLIE (fun z => F z j) i α Ω hΩ
  simp only [Work.CR.Flat.Holder.iDN_complex_eq] at h1
  simp only [Work.CR.Flat.Holder.hSN_complex_eq] at h2
  rw [h1, h2]

lemma contDiffOn_conj_comp {k : ℕ} {Ω : Set (Cn n)} {f : Cn n → ℂ}
    (hf : ContDiffOn ℝ k f Ω) :
    ContDiffOn ℝ k (fun z => Complex.conjCLE (f z)) Ω := by
  have h : (fun z => Complex.conjCLE (f z)) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ f := rfl
  rw [h]
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hf

/-! ## The pairing of an operator-valued function with a vector-valued function -/

lemma holderNorm_conj_comp_eq {k : ℕ} {α : ℝ} {f : Cn n → ℂ} {Ω : Set (Cn n)}
    (hΩ : UniqueDiffOn ℝ Ω) :
    Work.CR.Flat.holderNorm k α (fun z => Complex.conjCLE (f z)) Ω
      = Work.CR.Flat.holderNorm k α f Ω := by
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun z => Complex.conjCLE (f z)) = (fun z => Complex.conjLIE (f z)) := by
    funext z
    rw [Complex.conjCLE_apply, Complex.conjLIE_apply]
  have h1 := Work.CR.Flat.Holder.iDN_comp_lie Complex.conjLIE f i Ω hΩ
  have h2 := Work.CR.Flat.Holder.hSN_comp_lie Complex.conjLIE f i α Ω hΩ
  simp only [Work.CR.Flat.Holder.iDN_complex_eq] at h1
  simp only [Work.CR.Flat.Holder.hSN_complex_eq] at h2
  rw [hfun, h1, h2]

/-- The product rule for the `C^{1,α}`-norm, with the constant `8` isolated. -/
lemma holderNorm_mul_le_eight {α : ℝ} {f g : Cn n → ℂ} {Ω : Set (Cn n)}
    (hf : ContDiffOn ℝ (1 : ℕ∞) f Ω) (hg : ContDiffOn ℝ (1 : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω)
    (hf' : Work.CR.Flat.holderNorm 1 α f Ω ≠ ⊤)
    (hg' : Work.CR.Flat.holderNorm 1 α g Ω ≠ ⊤) :
    Work.CR.Flat.holderNorm 1 α (fun x => f x * g x) Ω
      ≤ ENNReal.ofReal 8 * (Work.CR.Flat.holderNorm 1 α f Ω
          * Work.CR.Flat.holderNorm 1 α g Ω) := by
  refine (Work.CR.Flat.Holder.holderNorm_mul_le hf hg hΩ hf' hg').trans (le_of_eq ?_)
  rw [show ((↑(1:ℕ) : ℝ≥0∞) + 1) * 2 ^ ((1:ℕ) + 1) = ENNReal.ofReal 8 from by norm_num]
  rw [mul_assoc]

/-- **The workhorse.**  Bound on one component of the pairing of a `C^{1,α}`
continuous-linear-map-valued function with a `C^{1,α}` vector-valued function. -/
lemma holderNorm_clm_apply_le {α : ℝ} {Ω : Set (Cn n)} (hΩ : UniqueDiffOn ℝ Ω)
    {T : Cn n → Cn n →L[ℝ] Cn n} {F : Cn n → Cn n} (j : Fin n)
    (hT1 : ∀ p, ContDiffOn ℝ (1 : ℕ∞) (fun z => (linCoef (T z) p) j) Ω)
    (hT2 : ∀ p, ContDiffOn ℝ (1 : ℕ∞) (fun z => (antiCoef (T z) p) j) Ω)
    (hF : ∀ p, ContDiffOn ℝ (1 : ℕ∞) (fun z => F z p) Ω)
    (hf1 : ∀ p, Work.CR.Flat.holderNorm 1 α (fun z => (linCoef (T z) p) j) Ω ≠ ⊤)
    (hf2 : ∀ p, Work.CR.Flat.holderNorm 1 α (fun z => (antiCoef (T z) p) j) Ω ≠ ⊤)
    (hfF : ∀ p, Work.CR.Flat.holderNorm 1 α (fun z => F z p) Ω ≠ ⊤) :
    Work.CR.Flat.holderNorm 1 α (fun z => (T z (F z)) j) Ω
      ≤ ENNReal.ofReal 8 * (mNorm 1 α T Ω * vNorm 1 α F Ω) := by
  have hdiag : ∀ (a f : Fin n → ℝ≥0∞), (∑ p, a p * f p) ≤ (∑ p, a p) * (∑ p, f p) := by
    intro a f
    rw [Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    exact Finset.single_le_sum (f := fun q => a p * f q) (fun q _ => by positivity)
      (Finset.mem_univ p)
  have hconj : ∀ p, Work.CR.Flat.holderNorm 1 α
      (fun z => Complex.conjCLE (F z p)) Ω
      = Work.CR.Flat.holderNorm 1 α (fun z => F z p) Ω :=
    fun p => holderNorm_conj_comp_eq (α := α) hΩ
  have hfconj : ∀ p, Work.CR.Flat.holderNorm 1 α
      (fun z => Complex.conjCLE (F z p)) Ω ≠ ⊤ := fun p => (hconj p) ▸ hfF p
  have hFc : ∀ p, ContDiffOn ℝ (1 : ℕ∞) (fun z => Complex.conjCLE (F z p)) Ω :=
    fun p => contDiffOn_conj_comp (hF p)
  have hsum1 : (∑ p, (Work.CR.Flat.holderNorm 1 α (fun z => (linCoef (T z) p) j) Ω
        + Work.CR.Flat.holderNorm 1 α (fun z => (antiCoef (T z) p) j) Ω))
      ≤ mNorm 1 α T Ω := by
    calc (∑ p, (Work.CR.Flat.holderNorm 1 α (fun z => (linCoef (T z) p) j) Ω
          + Work.CR.Flat.holderNorm 1 α (fun z => (antiCoef (T z) p) j) Ω))
        ≤ ∑ p, (vNorm 1 α (fun z => linCoef (T z) p) Ω
            + vNorm 1 α (fun z => antiCoef (T z) p) Ω) :=
          Finset.sum_le_sum fun p _ => add_le_add
            (vNorm_apply_le 1 α (fun z => linCoef (T z) p) Ω j)
            (vNorm_apply_le 1 α (fun z => antiCoef (T z) p) Ω j)
      _ ≤ mNorm 1 α T Ω := le_add_left le_rfl
  have hsum2 : (∑ p, Work.CR.Flat.holderNorm 1 α (fun z => F z p) Ω) = vNorm 1 α F Ω := rfl
  have hfun : (fun z => (T z (F z)) j) = fun z => ∑ p,
      ((linCoef (T z) p) j * F z p
        + (antiCoef (T z) p) j * Complex.conjCLE (F z p)) :=
    funext fun z => clm_apply_eq_sum (T z) (F z) j
  rw [hfun]
  calc Work.CR.Flat.holderNorm 1 α (fun z => ∑ p,
        ((linCoef (T z) p) j * F z p
          + (antiCoef (T z) p) j * Complex.conjCLE (F z p))) Ω
      ≤ ∑ p, Work.CR.Flat.holderNorm 1 α (fun z =>
          ((linCoef (T z) p) j * F z p
            + (antiCoef (T z) p) j * Complex.conjCLE (F z p))) Ω :=
        Work.CR.Flat.Holder.holderNorm_sum_le Finset.univ
          (fun p _ => ((hT1 p).mul (hF p)).add ((hT2 p).mul (hFc p))) hΩ
    _ ≤ ∑ p, (ENNReal.ofReal 8
          * (Work.CR.Flat.holderNorm 1 α (fun z => (linCoef (T z) p) j) Ω
            * Work.CR.Flat.holderNorm 1 α (fun z => F z p) Ω)
        + ENNReal.ofReal 8
          * (Work.CR.Flat.holderNorm 1 α (fun z => (antiCoef (T z) p) j) Ω
            * Work.CR.Flat.holderNorm 1 α (fun z => Complex.conjCLE (F z p)) Ω)) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have heq : (fun z => ((linCoef (T z) p) j * F z p
              + (antiCoef (T z) p) j * Complex.conjCLE (F z p)))
            = (fun z => (linCoef (T z) p) j * F z p)
              + (fun z => (antiCoef (T z) p) j * Complex.conjCLE (F z p)) := rfl
        rw [heq]
        refine (Work.CR.Flat.Holder.holderNorm_add_le ((hT1 p).mul (hF p))
          ((hT2 p).mul (hFc p)) hΩ).trans (add_le_add ?_ ?_)
        · exact holderNorm_mul_le_eight (hT1 p) (hF p) hΩ (hf1 p) (hfF p)
        · exact holderNorm_mul_le_eight (hT2 p) (hFc p) hΩ (hf2 p) (hfconj p)
    _ = ENNReal.ofReal 8 * ∑ p, ((Work.CR.Flat.holderNorm 1 α (fun z => (linCoef (T z) p) j) Ω
            + Work.CR.Flat.holderNorm 1 α (fun z => (antiCoef (T z) p) j) Ω)
          * Work.CR.Flat.holderNorm 1 α (fun z => F z p) Ω) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hconj p, ← mul_add, ← add_mul]
        try congr 1
        try rw [add_mul]
    _ ≤ ENNReal.ofReal 8 * (mNorm 1 α T Ω * vNorm 1 α F Ω) := by
        refine mul_le_mul' le_rfl ?_
        exact (hdiag _ _).trans (mul_le_mul' hsum1 (le_of_eq hsum2))



/-! ## Smoothness bookkeeping -/

lemma contDiffOn_clm_component {n : ℕ} {k : ℕ} {Ω : Set (Cn n)} {T : Cn n → Cn n →L[ℝ] Cn n}
    (hT : ContDiffOn ℝ (k : ℕ∞) T Ω) (u : Cn n) (j : Fin n) :
    ContDiffOn ℝ (k : ℕ∞) (fun z => (T z u) j) Ω := by
  have h2 : ContDiffOn ℝ (k : ℕ∞) (fun _ : Cn n => u) Ω := contDiffOn_const
  exact (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ).contDiff.comp_contDiffOn (hT.clm_apply h2)

lemma contDiffOn_linCoef_component {n : ℕ} {k : ℕ} {Ω : Set (Cn n)} {T : Cn n → Cn n →L[ℝ] Cn n}
    (hT : ContDiffOn ℝ (k : ℕ∞) T Ω) (p j : Fin n) :
    ContDiffOn ℝ (k : ℕ∞) (fun z => (linCoef (T z) p) j) Ω := by
  have h1 := contDiffOn_clm_component hT (Pi.single p (1 : ℂ)) j
  have h2 := contDiffOn_clm_component hT (Pi.single p (Complex.I : ℂ)) j
  have h3 : ContDiffOn ℝ (k : ℕ∞)
      (fun z => Complex.I * (T z (Pi.single p (Complex.I : ℂ))) j) Ω :=
    h2.const_smul Complex.I
  have h4 : ContDiffOn ℝ (k : ℕ∞) (fun z => (T z (Pi.single p (1 : ℂ))) j
      - Complex.I * (T z (Pi.single p (Complex.I : ℂ))) j) Ω := h1.sub h3
  have h5 := h4.const_smul (1 / 2 : ℂ)
  convert h5 using 1
  ext z
  rfl

lemma contDiffOn_antiCoef_component {n : ℕ} {k : ℕ} {Ω : Set (Cn n)} {T : Cn n → Cn n →L[ℝ] Cn n}
    (hT : ContDiffOn ℝ (k : ℕ∞) T Ω) (p j : Fin n) :
    ContDiffOn ℝ (k : ℕ∞) (fun z => (antiCoef (T z) p) j) Ω := by
  have h1 := contDiffOn_clm_component hT (Pi.single p (1 : ℂ)) j
  have h2 := contDiffOn_clm_component hT (Pi.single p (Complex.I : ℂ)) j
  have h3 : ContDiffOn ℝ (k : ℕ∞)
      (fun z => Complex.I * (T z (Pi.single p (Complex.I : ℂ))) j) Ω :=
    h2.const_smul Complex.I
  have h4 : ContDiffOn ℝ (k : ℕ∞) (fun z => (T z (Pi.single p (1 : ℂ))) j
      + Complex.I * (T z (Pi.single p (Complex.I : ℂ))) j) Ω := h1.add h3
  have h5 := h4.const_smul (1 / 2 : ℂ)
  convert h5 using 1
  ext z
  rfl

/-- All the component families whose `C^{k,α}`-norms enter `mNorm` are `C^k`. -/
def SmoothFun (k : ℕ) (Ω : Set (Cn n)) (T : Cn n → Cn n →L[ℝ] Cn n) : Prop :=
  (∀ p j, ContDiffOn ℝ (k : ℕ∞) (fun z => (T z (Pi.single p 1)) j) Ω) ∧
  (∀ p j, ContDiffOn ℝ (k : ℕ∞) (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω) ∧
  (∀ p j, ContDiffOn ℝ (k : ℕ∞) (fun z => (linCoef (T z) p) j) Ω) ∧
  (∀ p j, ContDiffOn ℝ (k : ℕ∞) (fun z => (antiCoef (T z) p) j) Ω)

lemma SmoothFun.of_contDiffOn {n : ℕ} {k : ℕ} {Ω : Set (Cn n)} {T : Cn n → Cn n →L[ℝ] Cn n}
    (hT : ContDiffOn ℝ (k : ℕ∞) T Ω) : SmoothFun k Ω T :=
  ⟨fun p j => contDiffOn_clm_component hT _ j, fun p j => contDiffOn_clm_component hT _ j,
    fun p j => contDiffOn_linCoef_component hT p j, fun p j => contDiffOn_antiCoef_component hT p j⟩

/-! ## Additivity and linearity of `mNorm` -/

section Add

variable {α : ℝ} {Ω : Set (Cn n)}

lemma linCoef_add {n : ℕ} (T S : Cn n →L[ℝ] Cn n) (p : Fin n) :
    linCoef (T + S) p = linCoef T p + linCoef S p := by
  funext j
  simp only [linCoef, ContinuousLinearMap.add_apply, Pi.add_apply]
  ring

lemma antiCoef_add {n : ℕ} (T S : Cn n →L[ℝ] Cn n) (p : Fin n) :
    antiCoef (T + S) p = antiCoef T p + antiCoef S p := by
  funext j
  simp only [antiCoef, ContinuousLinearMap.add_apply, Pi.add_apply]
  ring

lemma linCoef_sub {n : ℕ} (T S : Cn n →L[ℝ] Cn n) (p : Fin n) :
    linCoef (T - S) p = linCoef T p - linCoef S p := by
  funext j
  simp only [linCoef, ContinuousLinearMap.sub_apply, Pi.sub_apply]
  ring

lemma antiCoef_sub {n : ℕ} (T S : Cn n →L[ℝ] Cn n) (p : Fin n) :
    antiCoef (T - S) p = antiCoef T p - antiCoef S p := by
  funext j
  simp only [antiCoef, ContinuousLinearMap.sub_apply, Pi.sub_apply]
  ring

lemma vNorm_sub_le' {n : ℕ} {k : ℕ} {α : ℝ} {F G : Cn n → Cn n} {Ω : Set (Cn n)}
    (hF : ∀ j, ContDiffOn ℝ (k : ℕ∞) (fun z => F z j) Ω)
    (hG : ∀ j, ContDiffOn ℝ (k : ℕ∞) (fun z => G z j) Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    vNorm k α (fun z => F z - G z) Ω ≤ vNorm k α F Ω + vNorm k α G Ω := by
  have hneg : ∀ j, ContDiffOn ℝ (k : ℕ∞) (fun z => (-G z) j) Ω := fun j => (hG j).neg
  have heq : (fun z => F z - G z) = (fun z => F z) + (fun z => -G z) := by funext z; rfl
  rw [heq]
  refine (vNorm_add_le hF hneg hΩ).trans (add_le_add le_rfl ?_)
  have hcongr : vNorm k α (fun z => -G z) Ω = vNorm k α G Ω := by
    unfold vNorm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (fun z => (-G z) j) = -(fun z => G z j) from rfl]
    exact Work.CR.Flat.Holder.holderNorm_neg (hG j) hΩ
  rw [hcongr]

end Add


lemma holderNorm_congr {k : ℕ} {α : ℝ} {f g : Cn n → ℂ} {Ω : Set (Cn n)}
    (h : ∀ x ∈ Ω, f x = g x) :
    Work.CR.Flat.holderNorm k α f Ω = Work.CR.Flat.holderNorm k α g Ω := by
  have h1 : ∀ i, Work.CR.Flat.iterDerivNorm i f Ω = Work.CR.Flat.iterDerivNorm i g Ω := by
    intro i
    have := Work.CR.Flat.Holder.iDN_congr (i := i) h
    simpa only [Work.CR.Flat.Holder.iDN_complex_eq] using this
  have h2 : ∀ i, Work.CR.Flat.holderSeminorm i α f Ω = Work.CR.Flat.holderSeminorm i α g Ω := by
    intro i
    have := Work.CR.Flat.Holder.hSN_congr (i := i) (α := α) h
    simpa only [Work.CR.Flat.Holder.hSN_complex_eq] using this
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i, h2 i]

lemma vNorm_congr {k : ℕ} {α : ℝ} {F G : Cn n → Cn n} {Ω : Set (Cn n)}
    (h : ∀ x ∈ Ω, F x = G x) : vNorm k α F Ω = vNorm k α G Ω := by
  unfold vNorm
  exact Finset.sum_congr rfl fun j _ => holderNorm_congr fun x hx => by rw [h x hx]

lemma mNorm_congr {k : ℕ} {α : ℝ} {T S : Cn n → Cn n →L[ℝ] Cn n} {Ω : Set (Cn n)}
    (h : ∀ x ∈ Ω, T x = S x) : mNorm k α T Ω = mNorm k α S Ω := by
  have h1 : ∀ j, vNorm k α (fun z => T z (Pi.single j 1)) Ω
      = vNorm k α (fun z => S z (Pi.single j 1)) Ω :=
    fun j => vNorm_congr fun x hx => by rw [h x hx]
  have h2 : ∀ j, vNorm k α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω
      = vNorm k α (fun z => S z (Pi.single j (Complex.I : ℂ))) Ω :=
    fun j => vNorm_congr fun x hx => by rw [h x hx]
  have h3 : ∀ p, vNorm k α (fun z => linCoef (T z) p) Ω
      = vNorm k α (fun z => linCoef (S z) p) Ω :=
    fun p => vNorm_congr fun x hx => by rw [h x hx]
  have h4 : ∀ p, vNorm k α (fun z => antiCoef (T z) p) Ω
      = vNorm k α (fun z => antiCoef (S z) p) Ω :=
    fun p => vNorm_congr fun x hx => by rw [h x hx]
  have hsum3 : (∑ p, (vNorm k α (fun z => linCoef (T z) p) Ω
        + vNorm k α (fun z => antiCoef (T z) p) Ω))
      = ∑ p, (vNorm k α (fun z => linCoef (S z) p) Ω
        + vNorm k α (fun z => antiCoef (S z) p) Ω) :=
    Finset.sum_congr rfl fun p _ => by rw [h3 p, h4 p]
  unfold mNorm
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  rw [Finset.sum_congr rfl (fun j _ => h2 j)]
  rw [hsum3]

lemma vNorm_const_le {α : ℝ} {u : Cn n} {Ω : Set (Cn n)} :
    vNorm 1 α (fun _ : Cn n => u) Ω ≤ ENNReal.ofReal (∑ j, ‖u j‖) := by
  refine (vNorm_le_sum 1 α _ Ω (fun j => ENNReal.ofReal ‖u j‖)
    (fun j => holderNorm_one_const_le (u j) Ω)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _)]

end Work.NN.Newton
