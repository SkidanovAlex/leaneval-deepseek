import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.norm_conv_le
import Submission.Work.Diff.STE.Comp.holder3
import Submission.Work.Diff.STE.Comp.conv_tsum_mass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Young's inequality for the `r`-fold convolution of coefficient families on `ℤ^ι`

`Work.Diff.STE.conv` is the convolution of coefficient families (the Fourier side of a pointwise
product), and `iConv r d = d 0 * (d 1 * (... * d (r-1)))` is its `r`-fold iterate.

The target is `Work.Diff.STE.Comp.young_conv_lp` (Young's convolution inequality for `r` factors
with target exponent `2`); it is deduced from the general form `young_conv_lp_gen` with an arbitrary
target exponent `Q ≥ 1`, proved by induction on the number of factors: peel off the first factor and
apply the two-factor Young inequality `young_conv_two`.

Ingredients of this file (all proved here):
* `young_two_nn` -- Young's inequality for two nonnegative families, from the three-function Hölder
  inequality `Work.Diff.STE.Comp.holder3` and the discrete Tonelli theorem
  `Work.Diff.STE.Comp.conv_tsum_mass`, together with the degenerate case of an `ℓ¹` factor
  (`conv_l1_lr`);
* `norm_conv_tsum_le` -- the triangle inequality for the convolution;
* `young_conv_two` -- the complex-valued two-factor Young inequality;
* the elementary `Real.rpow` bookkeeping lemmas and the translation invariance of `tsum`/`Summable`
  on the group `ι → ℤ`.
-/

noncomputable section

namespace Work.Diff.STE.Comp

open scoped BigOperators

lemma rpow_pow_inv {x s : ℝ} (hx : 0 ≤ x) (hs : s ≠ 0) : (x ^ s) ^ (1 / s) = x := by
  rw [← Real.rpow_mul hx, one_div, mul_inv_cancel₀ hs, Real.rpow_one]

lemma rpow_inv_pow {x s : ℝ} (hx : 0 ≤ x) (hs : s ≠ 0) : (x ^ (1 / s)) ^ s = x := by
  rw [← Real.rpow_mul hx, one_div, inv_mul_cancel₀ hs, Real.rpow_one]

lemma rpow_sub_one_mul {x s : ℝ} (hx : 0 ≤ x) (hs : s ≠ 0) : x ^ (s - 1) * x = x ^ s := by
  have h1 : x ^ (s - 1) * x ^ (1 : ℝ) = x ^ s := by
    rw [← Real.rpow_add' hx (by intro h; exact hs (by linarith))]
    congr 1
    ring
  simpa using h1

theorem conv_l1_lr {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : (ι → ℤ) → ℝ)
    (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k) {r : ℝ} (hr : 1 ≤ r)
    (hf' : Summable f) (hg' : Summable fun k => g k ^ r) :
    Summable (fun k => (∑' l, f l * g (k - l)) ^ r) ∧
      (∑' k, (∑' l, f l * g (k - l)) ^ r) ^ (1 / r)
        ≤ (∑' k, f k) * (∑' k, g k ^ r) ^ (1 / r) := by
  rcases eq_or_lt_of_le hr with hr1 | hr1
  · subst hr1
    have hg'' : Summable g := by simpa using hg'
    obtain ⟨h1, h2⟩ := conv_tsum_mass f g hf hg hf' hg''
    refine ⟨?_, ?_⟩
    · simpa using h1
    · simp only [Real.rpow_one, one_div, inv_one]
      exact le_of_eq h2
  · have hr0 : 0 < r := lt_trans zero_lt_one hr1
    have hrne : r ≠ 0 := ne_of_gt hr0
    have hW : 0 ≤ ∑' k : ι → ℤ, f k := tsum_nonneg hf
    have hV : 0 ≤ ∑' k : ι → ℤ, g k ^ r := tsum_nonneg fun k => Real.rpow_nonneg (hg k) r
    have hrm1 : r - 1 ≠ 0 := by linarith
    have hconj : r.HolderConjugate (r / (r - 1)) := by
      refine ⟨?_, hr0, by positivity⟩
      rw [inv_one, inv_div]
      field_simp
      ring
    -- exponents
    have heA : (1 / r) * r = 1 := by field_simp
    have heB : (1 - 1 / r) * (r / (r - 1)) = 1 := by field_simp
    have heD : (1 - 1 / r) * r = r - 1 := by field_simp
    have heC : (1 : ℝ) / r + (1 - 1 / r) ≠ 0 := by norm_num
    have hexp : 1 / (r / (r - 1)) = 1 - 1 / r := by field_simp
    have hpoint : ∀ k : ι → ℤ, (∑' l, f l * g (k - l)) ≤
        (∑' l, f l * g (k - l) ^ r) ^ (1 / r) * (∑' l, f l) ^ (1 - 1 / r) := by
      intro k
      have hU0 : 0 ≤ ∑' l, f l * g (k - l) ^ r :=
        tsum_nonneg fun l => mul_nonneg (hf l) (Real.rpow_nonneg (hg _) r)
      have hF : ∀ l, 0 ≤ f l ^ (1 / r) * g (k - l) :=
        fun l => mul_nonneg (Real.rpow_nonneg (hf l) _) (hg _)
      have hG : ∀ l, 0 ≤ f l ^ (1 - 1 / r) := fun l => Real.rpow_nonneg (hf l) _
      have hidA : ∀ l, (f l ^ (1 / r) * g (k - l)) ^ r = f l * g (k - l) ^ r := by
        intro l
        rw [Real.mul_rpow (Real.rpow_nonneg (hf l) _) (hg _), ← Real.rpow_mul (hf l), heA,
            Real.rpow_one]
      have hidB : ∀ l, (f l ^ (1 - 1 / r)) ^ (r / (r - 1)) = f l := by
        intro l
        rw [← Real.rpow_mul (hf l), heB, Real.rpow_one]
      have hff : ∀ l, f l ^ (1 / r) * f l ^ (1 - 1 / r) = f l := by
        intro l
        rw [← Real.rpow_add' (hf l) heC]
        norm_num
      have hidC : ∀ l, f l ^ (1 / r) * g (k - l) * f l ^ (1 - 1 / r) = f l * g (k - l) := by
        intro l
        rw [show f l ^ (1 / r) * g (k - l) * f l ^ (1 - 1 / r)
              = (f l ^ (1 / r) * f l ^ (1 - 1 / r)) * g (k - l) from by ring, hff l]
      have hsumU : Summable fun l => f l * g (k - l) ^ r := by
        refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hf l) (Real.rpow_nonneg (hg _) r))
          (fun l => ?_) (hf'.mul_left (∑' j, g j ^ r))
        calc f l * g (k - l) ^ r ≤ f l * (∑' j, g j ^ r) :=
              mul_le_mul_of_nonneg_left
                (hg'.le_tsum (k - l) (fun j _ => Real.rpow_nonneg (hg j) r)) (hf l)
          _ = (∑' j, g j ^ r) * f l := mul_comm _ _
      have hsumF : Summable fun l => (f l ^ (1 / r) * g (k - l)) ^ r :=
        hsumU.congr fun l => (hidA l).symm
      have hsumG : Summable fun l => (f l ^ (1 - 1 / r)) ^ (r / (r - 1)) :=
        hf'.congr fun l => (hidB l).symm
      have hh := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hconj hF hG hsumF hsumG
      calc (∑' l, f l * g (k - l))
          = ∑' l, f l ^ (1 / r) * g (k - l) * f l ^ (1 - 1 / r) :=
            tsum_congr fun l => (hidC l).symm
        _ ≤ (∑' l, (f l ^ (1 / r) * g (k - l)) ^ r) ^ (1 / r) *
              (∑' l, (f l ^ (1 - 1 / r)) ^ (r / (r - 1))) ^ (1 / (r / (r - 1))) := hh.2
        _ = (∑' l, f l * g (k - l) ^ r) ^ (1 / r) * (∑' l, f l) ^ (1 - 1 / r) := by
            rw [tsum_congr hidA, tsum_congr hidB, hexp]
    have hk : ∀ k : ι → ℤ, (∑' l, f l * g (k - l)) ^ r ≤
        (∑' l, f l) ^ (r - 1) * (∑' l, f l * g (k - l) ^ r) := by
      intro k
      have hU0 : 0 ≤ ∑' l, f l * g (k - l) ^ r :=
        tsum_nonneg fun l => mul_nonneg (hf l) (Real.rpow_nonneg (hg _) r)
      have hT0 : 0 ≤ ∑' l, f l * g (k - l) := tsum_nonneg fun l => mul_nonneg (hf l) (hg _)
      calc (∑' l, f l * g (k - l)) ^ r
          ≤ ((∑' l, f l * g (k - l) ^ r) ^ (1 / r) * (∑' l, f l) ^ (1 - 1 / r)) ^ r :=
            Real.rpow_le_rpow hT0 (hpoint k) hr0.le
        _ = (∑' l, f l) ^ (r - 1) * (∑' l, f l * g (k - l) ^ r) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hU0 _) (Real.rpow_nonneg hW _),
                ← Real.rpow_mul hU0, ← Real.rpow_mul hW, heA, heD, Real.rpow_one]
            ring
    obtain ⟨hmassS, hmassV⟩ :=
      conv_tsum_mass f (fun l => g l ^ r) hf (fun l => Real.rpow_nonneg (hg l) r) hf' hg'
    have hsumm : Summable fun k => (∑' l, f l * g (k - l)) ^ r :=
      Summable.of_nonneg_of_le
        (fun k => Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg (hf l) (hg _)) r)
        hk (hmassS.mul_left ((∑' l, f l) ^ (r - 1)))
    refine ⟨hsumm, ?_⟩
    have hbound : (∑' k, (∑' l, f l * g (k - l)) ^ r) ≤ (∑' l, f l) ^ r * (∑' l, g l ^ r) := by
      calc (∑' k, (∑' l, f l * g (k - l)) ^ r)
          ≤ ∑' k, (∑' l, f l) ^ (r - 1) * (∑' l, f l * g (k - l) ^ r) :=
            Summable.tsum_le_tsum hk hsumm (hmassS.mul_left _)
        _ = (∑' l, f l) ^ (r - 1) * (∑' k, ∑' l, f l * g (k - l) ^ r) := tsum_mul_left
        _ = (∑' l, f l) ^ (r - 1) * ((∑' l, f l) * (∑' l, g l ^ r)) := by rw [hmassV]
        _ = (∑' l, f l) ^ r * (∑' l, g l ^ r) := by
            rw [← mul_assoc, rpow_sub_one_mul hW hrne]
    calc (∑' k, (∑' l, f l * g (k - l)) ^ r) ^ (1 / r)
        ≤ ((∑' l, f l) ^ r * (∑' l, g l ^ r)) ^ (1 / r) :=
          Real.rpow_le_rpow (tsum_nonneg fun k => Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg (hf l) (hg _)) r)
            hbound (by positivity)
      _ = (∑' l, f l) * (∑' l, g l ^ r) ^ (1 / r) := by
          rw [Real.mul_rpow (Real.rpow_nonneg hW r) hV, rpow_pow_inv hW hrne]

lemma mul_rpow_add {x t : ℝ} (hx : 0 ≤ x) (ht : 1 + t ≠ 0) : x * x ^ t = x ^ (1 + t) := by
  have h1 : x ^ (1 : ℝ) * x ^ t = x ^ (1 + t) := (Real.rpow_add' hx ht).symm
  simpa using h1

lemma tsum_translate {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → ℤ) → ℝ) (k : ι → ℤ) :
    (∑' l : ι → ℤ, h (k - l)) = ∑' l, h l := by
  let e : (ι → ℤ) ≃ (ι → ℤ) :=
    { toFun := fun l => k - l
      invFun := fun l => k - l
      left_inv := by intro l; simp
      right_inv := by intro l; simp }
  simpa [e] using (Equiv.tsum_eq e h)

lemma summable_translate {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → ℤ) → ℝ) (k : ι → ℤ)
    (hh : Summable h) : Summable fun l => h (k - l) := by
  let e : (ι → ℤ) ≃ (ι → ℤ) :=
    { toFun := fun l => k - l
      invFun := fun l => k - l
      left_inv := by intro l; simp
      right_inv := by intro l; simp }
  have h1 := (Equiv.summable_iff (f := h) e).2 hh
  simpa [e, Function.comp_def] using h1

lemma conv_comm_nn {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : (ι → ℤ) → ℝ) (k : ι → ℤ) :
    (∑' l, f l * g (k - l)) = ∑' l, g l * f (k - l) := by
  calc (∑' l, f l * g (k - l)) = ∑' l, g (k - l) * f l := tsum_congr fun l => mul_comm _ _
    _ = ∑' l, g l * f (k - l) := by
        simpa using tsum_translate (fun l : ι → ℤ => g l * f (k - l)) k

theorem young_two_nn {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : (ι → ℤ) → ℝ)
    (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k)
    {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hsum : p⁻¹ + q⁻¹ = 1 + r⁻¹)
    (hf' : Summable fun k => f k ^ p) (hg' : Summable fun k => g k ^ q) :
    Summable (fun k => (∑' l, f l * g (k - l)) ^ r) ∧
      (∑' k, (∑' l, f l * g (k - l)) ^ r) ^ (1 / r)
        ≤ (∑' k, f k ^ p) ^ (1 / p) * (∑' k, g k ^ q) ^ (1 / q) := by
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    have hqr : q = r := by
      have h := hsum
      rw [inv_one] at h
      exact inv_inj.mp (by linarith : q⁻¹ = r⁻¹)
    subst hqr
    have hf'' : Summable f := by simpa using hf'
    obtain ⟨h1, h2⟩ := conv_l1_lr f g hf hg hq hf'' hg'
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    simp [Real.rpow_one]
  · rcases eq_or_lt_of_le hq with hq1 | hq1
    · subst hq1
      have hpr : p = r := by
        have h := hsum
        rw [inv_one] at h
        exact inv_inj.mp (by linarith : p⁻¹ = r⁻¹)
      subst hpr
      have hg'' : Summable g := by simpa using hg'
      obtain ⟨h1, h2⟩ := conv_l1_lr g f hg hf hp hg'' hf'
      refine ⟨h1.congr (fun k => by rw [conv_comm_nn f g k]), ?_⟩
      have hL : (∑' k, (∑' l, f l * g (k - l)) ^ p) = ∑' k, (∑' l, g l * f (k - l)) ^ p :=
        tsum_congr fun k => by rw [conv_comm_nn f g k]
      rw [hL]
      refine h2.trans (le_of_eq ?_)
      simp [Real.rpow_one, mul_comm]
    · have hp0 : 0 < p := lt_trans zero_lt_one hp1
      have hq0 : 0 < q := lt_trans zero_lt_one hq1
      have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
      have hpne : p ≠ 0 := hp0.ne'
      have hqne : q ≠ 0 := hq0.ne'
      have hrne : r ≠ 0 := hr0.ne'
      have hrp : 0 < r - p := by
        have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
        have hrinv : r⁻¹ < p⁻¹ := by linarith [hsum]
        exact sub_pos.mpr ((inv_lt_inv₀ hr0 hp0).mp hrinv)
      have hrq : 0 < r - q := by
        have hpinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
        have hrinv : r⁻¹ < q⁻¹ := by linarith [hsum]
        exact sub_pos.mpr ((inv_lt_inv₀ hr0 hq0).mp hrinv)
      have hrpne : r - p ≠ 0 := ne_of_gt hrp
      have hrqne : r - q ≠ 0 := ne_of_gt hrq
      have hS : 0 ≤ ∑' l : ι → ℤ, f l ^ p := tsum_nonneg fun l => Real.rpow_nonneg (hf l) p
      have hT : 0 ≤ ∑' l : ι → ℤ, g l ^ q := tsum_nonneg fun l => Real.rpow_nonneg (hg l) q
      have hbpos : 0 < p * r / (r - p) := by positivity
      have hcpos : 0 < q * r / (r - q) := by positivity
      have hbrep : (p * r / (r - p))⁻¹ = p⁻¹ - r⁻¹ := by field_simp
      have hcrep : (q * r / (r - q))⁻¹ = q⁻¹ - r⁻¹ := by field_simp
      have hsum3 : p⁻¹ + q⁻¹ - r⁻¹ = 1 := by linarith [hsum]
      have hexp : r⁻¹ + (p * r / (r - p))⁻¹ + (q * r / (r - q))⁻¹ = 1 := by
        rw [hbrep, hcrep]
        linarith [hsum3]
      have he1 : (p * r / (r - p))⁻¹ * r = (r - p) / p := by field_simp
      have he2 : (q * r / (r - q))⁻¹ * r = (r - q) / q := by field_simp
      have he3 : 1 + (r - p) / p = r / p := by field_simp; ring
      have he4 : 1 + (r - q) / q = r / q := by field_simp; ring
      have he5 : r / p * (1 / r) = 1 / p := by field_simp
      have he6 : r / q * (1 / r) = 1 / q := by field_simp
      -- exponent identities for the three families
      have hB : ∀ l, (f l ^ (1 - p / r)) ^ (p * r / (r - p)) = f l ^ p := by
        intro l
        rw [← Real.rpow_mul (hf l)]
        congr 1
        field_simp
      have hpoint : ∀ k : ι → ℤ, (∑' l, f l * g (k - l)) ≤
          (∑' l, f l ^ p * g (k - l) ^ q) ^ (1 / r) *
            (∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹) *
            (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹) := by
        intro k
        have hWsumm : Summable fun l => f l ^ p * g (k - l) ^ q := by
          refine Summable.of_nonneg_of_le
            (fun l => mul_nonneg (Real.rpow_nonneg (hf l) p) (Real.rpow_nonneg (hg _) q))
            (fun l => ?_) (hf'.mul_left (∑' j, g j ^ q))
          calc f l ^ p * g (k - l) ^ q ≤ f l ^ p * (∑' j, g j ^ q) :=
                mul_le_mul_of_nonneg_left
                  (hg'.le_tsum (k - l) (fun j _ => Real.rpow_nonneg (hg j) q))
                  (Real.rpow_nonneg (hf l) p)
            _ = (∑' j, g j ^ q) * f l ^ p := mul_comm _ _
        have hA : ∀ l, ((f l ^ p * g (k - l) ^ q) ^ (1 / r)) ^ r = f l ^ p * g (k - l) ^ q :=
          fun l => rpow_inv_pow
            (mul_nonneg (Real.rpow_nonneg (hf l) p) (Real.rpow_nonneg (hg _) q)) hrne
        have hC : ∀ l, (g (k - l) ^ (1 - q / r)) ^ (q * r / (r - q)) = g (k - l) ^ q := by
          intro l
          rw [← Real.rpow_mul (hg _)]
          congr 1
          field_simp
        have hABC : ∀ l, (f l ^ p * g (k - l) ^ q) ^ (1 / r) * f l ^ (1 - p / r) *
            g (k - l) ^ (1 - q / r) = f l * g (k - l) := by
          intro l
          have hfp : (f l ^ p) ^ (1 / r) = f l ^ (p / r) := by
            rw [← Real.rpow_mul (hf l)]
            congr 1
            ring
          have hgq : (g (k - l) ^ q) ^ (1 / r) = g (k - l) ^ (q / r) := by
            rw [← Real.rpow_mul (hg _)]
            congr 1
            ring
          have hf1 : f l ^ (p / r) * f l ^ (1 - p / r) = f l := by
            rw [← Real.rpow_add' (hf l)
                  (by rw [show p / r + (1 - p / r) = 1 by ring]; norm_num),
                show p / r + (1 - p / r) = 1 by ring, Real.rpow_one]
          have hg1 : g (k - l) ^ (q / r) * g (k - l) ^ (1 - q / r) = g (k - l) := by
            rw [← Real.rpow_add' (hg _)
                  (by rw [show q / r + (1 - q / r) = 1 by ring]; norm_num),
                show q / r + (1 - q / r) = 1 by ring, Real.rpow_one]
          rw [Real.mul_rpow (Real.rpow_nonneg (hf l) p) (Real.rpow_nonneg (hg _) q), hfp, hgq,
            show (f l ^ (p / r) * g (k - l) ^ (q / r)) * f l ^ (1 - p / r) * g (k - l) ^ (1 - q / r)
              = (f l ^ (p / r) * f l ^ (1 - p / r)) *
                (g (k - l) ^ (q / r) * g (k - l) ^ (1 - q / r)) from by ring,
            hf1, hg1]
        have hAs : Summable fun l => ((f l ^ p * g (k - l) ^ q) ^ (1 / r)) ^ r :=
          hWsumm.congr fun l => (hA l).symm
        have hBs : Summable fun l => (f l ^ (1 - p / r)) ^ (p * r / (r - p)) :=
          hf'.congr fun l => (hB l).symm
        have hCs : Summable fun l => (g (k - l) ^ (1 - q / r)) ^ (q * r / (r - q)) :=
          (summable_translate (fun j => g j ^ q) k hg').congr fun l => (hC l).symm
        have hh := holder3 (a := r) (b := p * r / (r - p)) (c := q * r / (r - q))
          (fun l => (f l ^ p * g (k - l) ^ q) ^ (1 / r))
          (fun l => f l ^ (1 - p / r)) (fun l => g (k - l) ^ (1 - q / r))
          (fun l => Real.rpow_nonneg
            (mul_nonneg (Real.rpow_nonneg (hf l) p) (Real.rpow_nonneg (hg _) q)) _)
          (fun l => Real.rpow_nonneg (hf l) _)
          (fun l => Real.rpow_nonneg (hg _) _)
          hr0 hbpos hcpos hexp hAs hBs hCs
        calc (∑' l, f l * g (k - l))
            = ∑' l, (f l ^ p * g (k - l) ^ q) ^ (1 / r) * f l ^ (1 - p / r) *
                g (k - l) ^ (1 - q / r) := tsum_congr fun l => (hABC l).symm
          _ ≤ (∑' l, f l ^ p * g (k - l) ^ q) ^ (1 / r) *
                (∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹) *
                (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹) := by
              refine hh.2.trans (le_of_eq ?_)
              rw [tsum_congr hA, tsum_congr hB, tsum_congr hC,
                  tsum_translate (fun j => g j ^ q) k]
              simp only [one_div]
      have hWmass : Summable (fun k : ι → ℤ => ∑' l, f l ^ p * g (k - l) ^ q) ∧
          (∑' k, ∑' l, f l ^ p * g (k - l) ^ q) = (∑' l, f l ^ p) * (∑' l, g l ^ q) :=
        conv_tsum_mass (fun l => f l ^ p) (fun l => g l ^ q)
          (fun l => Real.rpow_nonneg (hf l) p) (fun l => Real.rpow_nonneg (hg l) q) hf' hg'
      have hMul : ((∑' l, f l ^ p) * (∑' l, g l ^ q)) *
            ((∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r) *
              (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r)) =
          (∑' l, f l ^ p) ^ (r / p) * (∑' l, g l ^ q) ^ (r / q) := by
        rw [show ((∑' l, f l ^ p) * (∑' l, g l ^ q)) *
              ((∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r) *
                (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r))
            = ((∑' l, f l ^ p) * (∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r)) *
              ((∑' l, g l ^ q) * (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r)) from by ring]
        rw [mul_rpow_add hS (by rw [he1, he3]; exact ne_of_gt (by positivity)),
            mul_rpow_add hT (by rw [he2, he4]; exact ne_of_gt (by positivity)),
            he1, he3, he2, he4]
      have hk : ∀ k : ι → ℤ, (∑' l, f l * g (k - l)) ^ r ≤
          (∑' l, f l ^ p * g (k - l) ^ q) *
            ((∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r) *
              (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r)) := by
        intro k
        have hW : 0 ≤ ∑' l, f l ^ p * g (k - l) ^ q :=
          tsum_nonneg fun l => mul_nonneg (Real.rpow_nonneg (hf l) p) (Real.rpow_nonneg (hg _) q)
        have hT0 : 0 ≤ ∑' l, f l * g (k - l) := tsum_nonneg fun l => mul_nonneg (hf l) (hg _)
        calc (∑' l, f l * g (k - l)) ^ r
            ≤ ((∑' l, f l ^ p * g (k - l) ^ q) ^ (1 / r) *
                (∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹) *
                (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹)) ^ r :=
              Real.rpow_le_rpow hT0 (hpoint k) hr0.le
          _ = (∑' l, f l ^ p * g (k - l) ^ q) *
                ((∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r) *
                  (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r)) := by
              rw [Real.mul_rpow
                    (mul_nonneg (Real.rpow_nonneg hW _) (Real.rpow_nonneg hS _))
                    (Real.rpow_nonneg hT _),
                  Real.mul_rpow (Real.rpow_nonneg hW _) (Real.rpow_nonneg hS _),
                  rpow_inv_pow hW hrne, ← Real.rpow_mul hS, ← Real.rpow_mul hT]
              ring
      have hsumm : Summable fun k => (∑' l, f l * g (k - l)) ^ r :=
        Summable.of_nonneg_of_le
          (fun k => Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg (hf l) (hg _)) r)
          hk (hWmass.1.mul_right ((∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r) *
              (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r)))
      refine ⟨hsumm, ?_⟩
      have hbound : (∑' k, (∑' l, f l * g (k - l)) ^ r) ≤
          (∑' l, f l ^ p) ^ (r / p) * (∑' l, g l ^ q) ^ (r / q) := by
        calc (∑' k, (∑' l, f l * g (k - l)) ^ r)
            ≤ ∑' k, (∑' l, f l ^ p * g (k - l) ^ q) *
                ((∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r) *
                  (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r)) :=
              Summable.tsum_le_tsum hk hsumm
                (hWmass.1.mul_right ((∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r) *
                  (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r)))
          _ = (∑' l, f l ^ p) * (∑' l, g l ^ q) *
                ((∑' l, f l ^ p) ^ ((p * r / (r - p))⁻¹ * r) *
                  (∑' l, g l ^ q) ^ ((q * r / (r - q))⁻¹ * r)) := by
              rw [tsum_mul_right, hWmass.2]
          _ = (∑' l, f l ^ p) ^ (r / p) * (∑' l, g l ^ q) ^ (r / q) := hMul
      calc (∑' k, (∑' l, f l * g (k - l)) ^ r) ^ (1 / r)
          ≤ ((∑' l, f l ^ p) ^ (r / p) * (∑' l, g l ^ q) ^ (r / q)) ^ (1 / r) :=
            Real.rpow_le_rpow
              (tsum_nonneg fun k => Real.rpow_nonneg
                (tsum_nonneg fun l => mul_nonneg (hf l) (hg _)) r)
              hbound (by positivity)
        _ = (∑' l, f l ^ p) ^ (1 / p) * (∑' l, g l ^ q) ^ (1 / q) := by
            rw [Real.mul_rpow (Real.rpow_nonneg hS _) (Real.rpow_nonneg hT _),
                ← Real.rpow_mul hS, ← Real.rpow_mul hT, he5, he6]

/-- Young's inequality on `ℤ^ι`.  `iConv r d` is the `r`-fold convolution
`d 0 * (d 1 * (… * d (r-1)))` of coefficient families (`Work.Diff.STE.conv`), built by recursion
on `r` (the `r = 0` case is unused and set to `0`).
Claim: if `p : Fin r → ℝ` has `1 ≤ p m` for all `m` and `∑ m, (p m)⁻¹ = r - 1/2`, then
`(∑' k, ‖iConv r d k‖²)^{1/2} ≤ ∏ m, (∑' k, ‖d m k‖^{p m})^{1/p m}`.

Proof route.  Prove first the general form with an arbitrary target exponent
`Q : ℝ`, `1 ≤ Q`: if `∑ m, (p m)⁻¹ = r - 1 + (Q)⁻¹` and each `p m ≥ 1`, then
`(∑' k, ‖iConv r d k‖ ^ Q) ^ (1/Q) ≤ ∏ m, (∑' k, ‖d m k‖ ^ (p m)) ^ ((p m)⁻¹)`.
* `r = 1`: the conditions force `p 0 = Q` and the claim is an identity.
* `r ≥ 2`: peel off `d 0`, applying the **two-factor** Young inequality
  `‖f * g‖_Q ≤ ‖f‖_p ‖g‖_{p'}` with `1/p + 1/p' = 1 + 1/Q` (whose proof is: pointwise
  `(|f|*|g|)(x) ≤ (Σ_y |f y|^p |g (x-y)|^Q)^{1/Q} ‖f‖_p^{1-p/Q} ‖g‖_{p'}^{1-p'/Q}` by Hölder with
  the three exponents `Q`, `Qp/(Q-p)`, `Qp'/(Q-p')`, then sum over `x`) — this is the only
  genuine mathematics, and it is `MeasureTheory`-free: use the discrete Hölder
  `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg`.
  Then apply the induction hypothesis with `r-1` factors and target exponent `P` defined by
  `1/P = 1 + 1/Q - 1/(p 0)`: the remaining reciprocals `∑_{m ≥ 1}(p m)⁻¹` equal
  `(r-1) - 1 + 1/P` automatically, and `P ≥ 1` follows from `1/p 0 ≥ 1/Q` (which is a consequence
  of the hypothesis, since all `1/(p m) ≤ 1/Q · ... `; check `1/(p 0) ≥ 1/Q` directly from
  `∑(p m)⁻¹ = r - 1 + 1/Q` and `1/(p m) ≤ 1`).
Finally specialize `Q = 2`. -/
noncomputable def iConv {ι : Type*} : (r : ℕ) → (Fin r → (ι → ℤ) → ℂ) → (ι → ℤ) → ℂ
  | 0, _ => 0
  | 1, d => d 0
  | (r+2), d => Work.Diff.STE.conv (d 0) (iConv (r+1) (fun i => d i.succ))

theorem norm_conv_tsum_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c e : (ι → ℤ) → ℂ)
    (k : ι → ℤ) :
    ‖Work.Diff.STE.conv c e k‖ ≤ ∑' l : ι → ℤ, ‖c l‖ * ‖e (k - l)‖ := by
  by_cases h : Summable (fun l : ι → ℤ => c l * e (k - l))
  · have h1 : Summable (fun l : ι → ℤ => ‖c l * e (k - l)‖) := h.norm
    calc ‖Work.Diff.STE.conv c e k‖ = ‖∑' l : ι → ℤ, c l * e (k - l)‖ := rfl
      _ ≤ ∑' l : ι → ℤ, ‖c l * e (k - l)‖ := norm_tsum_le_tsum_norm h1
      _ = ∑' l : ι → ℤ, ‖c l‖ * ‖e (k - l)‖ := tsum_congr fun l => norm_mul _ _
  · rw [Work.Diff.STE.conv, tsum_eq_zero_of_not_summable h, norm_zero]
    exact tsum_nonneg fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem young_conv_two {ι : Type*} [Fintype ι] [DecidableEq ι] (c e : (ι → ℤ) → ℂ)
    {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hsum : p⁻¹ + q⁻¹ = 1 + r⁻¹)
    (hc : Summable fun k => ‖c k‖ ^ p) (he : Summable fun k => ‖e k‖ ^ q) :
    Summable (fun k => ‖Work.Diff.STE.conv c e k‖ ^ r) ∧
      (∑' k : ι → ℤ, ‖Work.Diff.STE.conv c e k‖ ^ r) ^ (1 / r)
        ≤ (∑' k, ‖c k‖ ^ p) ^ (1 / p) * (∑' k, ‖e k‖ ^ q) ^ (1 / q) := by
  obtain ⟨hsumm, hbound⟩ := young_two_nn (fun k => ‖c k‖) (fun k => ‖e k‖)
    (fun k => norm_nonneg _) (fun k => norm_nonneg _) hp hq hr hsum hc he
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hpt : ∀ k, ‖Work.Diff.STE.conv c e k‖ ^ r ≤ (∑' l, ‖c l‖ * ‖e (k - l)‖) ^ r :=
    fun k => Real.rpow_le_rpow (norm_nonneg _) (norm_conv_tsum_le c e k) hr0
  have hsumm' : Summable fun k => ‖Work.Diff.STE.conv c e k‖ ^ r :=
    Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (norm_nonneg _) r) hpt hsumm
  refine ⟨hsumm', ?_⟩
  have hnn1 : 0 ≤ ∑' k : ι → ℤ, ‖Work.Diff.STE.conv c e k‖ ^ r :=
    tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) r
  calc (∑' k : ι → ℤ, ‖Work.Diff.STE.conv c e k‖ ^ r) ^ (1 / r)
      ≤ (∑' k, (∑' l, ‖c l‖ * ‖e (k - l)‖) ^ r) ^ (1 / r) :=
        Real.rpow_le_rpow hnn1 (Summable.tsum_le_tsum hpt hsumm' hsumm)
          (le_of_lt (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hr)))
    _ ≤ (∑' k, ‖c k‖ ^ p) ^ (1 / p) * (∑' k, ‖e k‖ ^ q) ^ (1 / q) := hbound

theorem young_conv_lp_gen {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : 1 ≤ r)
    (d : Fin r → (ι → ℤ) → ℂ) (p : Fin r → ℝ) (Q : ℝ) (hQ : 1 ≤ Q)
    (hp : ∀ m, 1 ≤ p m) (hsum : ∑ m, (p m)⁻¹ = (r : ℝ) - 1 + Q⁻¹)
    (hsm : ∀ m, Summable fun k : ι → ℤ => ‖d m k‖ ^ (p m)) :
    Summable (fun k : ι → ℤ => ‖iConv r d k‖ ^ Q) ∧
      (∑' k : ι → ℤ, ‖iConv r d k‖ ^ Q) ^ (1 / Q)
        ≤ ∏ m, (∑' k : ι → ℤ, ‖d m k‖ ^ (p m)) ^ ((p m)⁻¹) := by
  have key : ∀ n : ℕ, ∀ (Q : ℝ), 1 ≤ Q → ∀ (d : Fin (n + 1) → (ι → ℤ) → ℂ)
      (p : Fin (n + 1) → ℝ),
      (∀ m, 1 ≤ p m) → (∑ m, (p m)⁻¹ = ((n + 1 : ℕ) : ℝ) - 1 + Q⁻¹) →
      (∀ m, Summable fun k : ι → ℤ => ‖d m k‖ ^ (p m)) →
      Summable (fun k : ι → ℤ => ‖iConv (n + 1) d k‖ ^ Q) ∧
        (∑' k : ι → ℤ, ‖iConv (n + 1) d k‖ ^ Q) ^ (1 / Q)
          ≤ ∏ m, (∑' k : ι → ℤ, ‖d m k‖ ^ (p m)) ^ ((p m)⁻¹) := by
    intro n
    induction n with
    | zero =>
      intro Q hQ d p hp hsum hsm
      have h0 : (p 0)⁻¹ = Q⁻¹ := by
        have h := hsum
        rw [Fin.sum_univ_one] at h
        simpa using h
      have hp0 : p 0 = Q := inv_inj.mp h0
      rw [← hp0]
      constructor
      · simpa [iConv] using hsm 0
      · have hprod := Fin.prod_univ_one
          (fun m : Fin 1 => (∑' k : ι → ℤ, ‖d m k‖ ^ (p m)) ^ ((p m)⁻¹))
        rw [hprod]
        simp only [one_div, iConv]
        exact le_rfl
    | succ n ih =>
      intro Q hQ d p hp hsum hsm
      have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
      have hp0ge1 : 1 ≤ p 0 := hp 0
      have hp0pos : 0 < p 0 := lt_of_lt_of_le zero_lt_one hp0ge1
      have hN : ((Nat.succ n + 1 : ℕ) : ℝ) - 1 = ((n + 1 : ℕ) : ℝ) := by
        push_cast; ring
      have htail : ∑ i : Fin (n + 1), (p i.succ)⁻¹ ≤ ((n + 1 : ℕ) : ℝ) := by
        calc ∑ i : Fin (n + 1), (p i.succ)⁻¹ ≤ ∑ _i : Fin (n + 1), (1 : ℝ) :=
              Finset.sum_le_sum fun i _ => inv_le_one_of_one_le₀ (hp i.succ)
          _ = ((n + 1 : ℕ) : ℝ) := by simp
      have hp0geQ : Q⁻¹ ≤ (p 0)⁻¹ := by
        have h := hsum
        rw [Fin.sum_univ_succ] at h
        linarith [hN, htail]
      have hc0 : 0 < 1 + Q⁻¹ - (p 0)⁻¹ := by
        have h1 : (p 0)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp0ge1
        have h2 : 0 < Q⁻¹ := inv_pos.mpr hQpos
        linarith
      have hc1 : 1 + Q⁻¹ - (p 0)⁻¹ ≤ 1 := by linarith [hp0geQ]
      have hP'pos : 0 < (1 + Q⁻¹ - (p 0)⁻¹)⁻¹ := inv_pos.mpr hc0
      have hP'one : 1 ≤ (1 + Q⁻¹ - (p 0)⁻¹)⁻¹ := (one_le_inv₀ hc0).mpr hc1
      have hP'inv : ((1 + Q⁻¹ - (p 0)⁻¹)⁻¹)⁻¹ = 1 + Q⁻¹ - (p 0)⁻¹ := inv_inv _
      have hsumt : ∑ i : Fin (n + 1), (p i.succ)⁻¹
          = ((n + 1 : ℕ) : ℝ) - 1 + ((1 + Q⁻¹ - (p 0)⁻¹)⁻¹)⁻¹ := by
        have h := hsum
        rw [Fin.sum_univ_succ] at h
        rw [hP'inv]
        linarith [hN]
      obtain ⟨hsummt, hboundt⟩ := ih ((1 + Q⁻¹ - (p 0)⁻¹)⁻¹) hP'one
        (fun i => d i.succ) (fun i => p i.succ) (fun m => hp m.succ) hsumt
        (fun m => hsm m.succ)
      have hconj : (p 0)⁻¹ + ((1 + Q⁻¹ - (p 0)⁻¹)⁻¹)⁻¹ = 1 + Q⁻¹ := by
        rw [hP'inv]; ring
      obtain ⟨hsumm2, hbound2⟩ := young_conv_two (c := d 0)
        (e := iConv (n + 1) (fun i => d i.succ)) hp0ge1 hP'one hQ
        hconj (hsm 0) hsummt
      have hiconv : iConv (n + 1 + 1) d
          = Work.Diff.STE.conv (d 0) (iConv (n + 1) (fun i => d i.succ)) := rfl
      constructor
      · rw [hiconv]; exact hsumm2
      · rw [hiconv]
        calc (∑' k, ‖Work.Diff.STE.conv (d 0) (iConv (n + 1) (fun i => d i.succ)) k‖ ^ Q) ^ (1 / Q)
            ≤ (∑' k, ‖d 0 k‖ ^ (p 0)) ^ (1 / (p 0)) *
                (∑' k, ‖iConv (n + 1) (fun i => d i.succ) k‖ ^ ((1 + Q⁻¹ - (p 0)⁻¹)⁻¹)) ^
                  (1 / ((1 + Q⁻¹ - (p 0)⁻¹)⁻¹)) := hbound2
          _ ≤ (∑' k, ‖d 0 k‖ ^ (p 0)) ^ (1 / (p 0)) *
                ∏ m : Fin (n + 1), (∑' k, ‖d m.succ k‖ ^ (p m.succ)) ^ ((p m.succ)⁻¹) :=
              mul_le_mul_of_nonneg_left hboundt
                (Real.rpow_nonneg (tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _) _)
          _ = ∏ m : Fin (n + 1 + 1), (∑' k, ‖d m k‖ ^ (p m)) ^ ((p m)⁻¹) := by
              conv_rhs => rw [Fin.prod_univ_succ]
              simp only [one_div]
  obtain ⟨n, hn⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  subst hn
  exact key n Q hQ d p hp hsum hsm
theorem young_conv_lp {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : 1 ≤ r)
    (d : Fin r → (ι → ℤ) → ℂ) (p : Fin r → ℝ)
    (hp : ∀ m, 1 ≤ p m) (hsum : ∑ m, (p m)⁻¹ = (r : ℝ) - 1 / 2)
    (hsm : ∀ m, Summable fun k : ι → ℤ => ‖d m k‖ ^ (p m)) :
    Summable (fun k : ι → ℤ => ‖iConv r d k‖ ^ 2) ∧
      (∑' k : ι → ℤ, ‖iConv r d k‖ ^ 2) ^ (1 / 2 : ℝ)
        ≤ ∏ m, (∑' k : ι → ℤ, ‖d m k‖ ^ (p m)) ^ ((p m)⁻¹) := by
  have h := young_conv_lp_gen hr d p 2 (by norm_num) hp (by norm_num at hsum ⊢; linarith) hsm
  simpa using h

end Work.Diff.STE.Comp
