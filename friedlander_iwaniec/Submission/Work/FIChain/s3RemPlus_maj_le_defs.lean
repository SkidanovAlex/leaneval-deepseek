/-
# `Submission.Work.FIChain.s3RemPlus_maj_le_defs` — the joint rectangle integrand of REM

The final step of the `z`-average of the REM majorant (`Work.FIChain.s3RemPlus_maj_le`) performs
the relaxation of the per-`ℓ` substituted integrals

    Σ_{ℓ ≤ M} τ(ℓ)² ∫_{v=ℓ·zc}^{ℓ·e·zc} dv/v ∫_{w=ℓ}^{min (sc·v/Cm)(x/Cm)} dw/w G_ℓ(v,w)

(`M := ⌊x/Cm⌋₊`, `G_ℓ(v,w) = [v ≤ x]·s3RemSub x Cm ℓ (sc x B) v w`) to the COMMON rectangle
`[zc, M·e·zc] × [1, x/Cm]`, where the `ℓ`-sum can be pulled inside the two integrals and bounded
pointwise by `(R′)` via `Work.FIChain.Ksub_le`.

This file fixes the integrand of that common rectangle:

* `Fsub x Cm B ℓ v w` — the `ℓ`-th summand of `Ksub`, i.e.

      [ℓ·zc ≤ v ≤ ℓ·e·zc ∧ ℓ ≤ w ∧ v ≤ x] · τ(ℓ)² · s3RemSub x Cm ℓ (sc x B) v w,

  written with the **fixed-range** form `s3RemSubF` of `s3RemSub` so that it is *jointly measurable*
  in `(v,w)` and globally bounded on the rectangle (both needed for the Fubini/integrability
  bookkeeping).  On `w ≤ x` (in particular on the `w`-range `[1, x/Cm]`) the two forms agree, so
  `Ksub` is exactly the `ℓ`-sum of `Fsub` there (`Ksub_eq_sum_Fsub_of_le`).

* `s3RemSubF` — the fixed-range form of `s3RemSub`:

      s3RemSubF x Cm N ℓ sc v w
        = Σ_{d ≤ N} [d·ℓ ≤ w] · (|cfR (ℓ·d) ⌊min (sc·v) x⌋₊| + |cfR (ℓ·d) ⌊max v (Cm·w)⌋₊|),

  equal to `s3RemSub x Cm ℓ sc v w` as soon as `w ≤ N·ℓ` (`s3RemSub_eq_s3RemSubF`).

Definitions and their elementary properties only; the analytic lemmas live in the companion files
`remTerm_zavg_le_rect`, `sum_rect_Fsub_le`, `Ksub_rect_zavg_le`.
-/
import Mathlib
import Submission.Work.FIChain.s3RemPlus_maj
import Submission.Work.FIChain.measurable_s3halves

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The fixed-range form of `s3RemSub` -/

/-- The fixed-range form of the substituted majorant `s3RemSub`: the `d`-range `1 ≤ d ≤ ⌊w/ℓ⌋₊`
is replaced by `1 ≤ d ≤ N` with the indicator `d·ℓ ≤ w` (equal to `s3RemSub` whenever
`⌊w/ℓ⌋₊ ≤ N`). -/
def s3RemSubF (x Cm N ℓ : ℕ) (sc : ℝ) (v w : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (if (d : ℝ) * (ℓ : ℝ) ≤ w then
      (|cfR (ℓ * d) ⌊min (sc * v) (x : ℝ)⌋₊| + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|)
    else 0)

lemma measurable_s3RemSubF (x Cm N ℓ : ℕ) (sc : ℝ) :
    Measurable (fun p : ℝ × ℝ => s3RemSubF x Cm N ℓ sc p.1 p.2) := by
  unfold s3RemSubF
  refine Finset.measurable_sum _ (fun d _ => ?_)
  refine Measurable.ite (measurableSet_le (measurable_const : Measurable (fun _ : ℝ × ℝ => ((d : ℝ) * (ℓ : ℝ)))) measurable_snd) ?_ measurable_const
  refine Measurable.add ?_ ?_
  · refine (measurable_cfR_const (ℓ * d) ?_).abs
    fun_prop
  · refine (measurable_cfR_const (ℓ * d) ?_).abs
    fun_prop

lemma s3RemSubF_nonneg (x Cm N ℓ : ℕ) (sc v w : ℝ) :
    0 ≤ s3RemSubF x Cm N ℓ sc v w := by
  unfold s3RemSubF
  refine Finset.sum_nonneg (fun d _ => ?_)
  by_cases hd : (d : ℝ) * (ℓ : ℝ) ≤ w
  · rw [if_pos hd]; positivity
  · rw [if_neg hd]

/-- `s3RemSub` is the fixed-range sum as soon as `1 ≤ ℓ` and `w ≤ N·ℓ`. -/
lemma s3RemSub_eq_s3RemSubF (x Cm N ℓ : ℕ) (sc : ℝ) {v w : ℝ} (hℓ1 : 1 ≤ ℓ)
    (hN : w ≤ (N : ℝ) * (ℓ : ℝ)) :
    s3RemSub x Cm ℓ sc v w = s3RemSubF x Cm N ℓ sc v w := by
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  set t : ℕ → ℝ := fun d =>
    (|cfR (ℓ * d) ⌊min (sc * v) (x : ℝ)⌋₊| + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|) with ht
  by_cases hw0 : 0 ≤ w
  · have hfl : ⌊w / (ℓ : ℝ)⌋₊ ≤ N := by
      have h1 : w / (ℓ : ℝ) ≤ (N : ℝ) := by
        rw [div_le_iff₀ hℓpos]
        simpa using hN
      have h2 : ⌊w / (ℓ : ℝ)⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_mono h1
      simpa using h2
    rw [s3RemSub, s3RemSubF]
    have h1 : (∑ d ∈ Finset.Icc 1 ⌊w / (ℓ : ℝ)⌋₊,
            (if (d : ℝ) * (ℓ : ℝ) ≤ w then t d else 0))
        = ∑ d ∈ Finset.Icc 1 N, (if (d : ℝ) * (ℓ : ℝ) ≤ w then t d else 0) := by
      refine Finset.sum_subset (s₁ := Finset.Icc 1 ⌊w / (ℓ : ℝ)⌋₊) (s₂ := Finset.Icc 1 N)
        (fun d hd => ?_) (fun d hd hdnot => ?_)
      · rw [Finset.mem_Icc] at hd ⊢
        exact ⟨hd.1, le_trans hd.2 hfl⟩
      · rw [Finset.mem_Icc] at hd
        rw [if_neg]
        intro hcon
        refine hdnot (Finset.mem_Icc.mpr ⟨hd.1, ?_⟩)
        have h2 : (d : ℝ) ≤ w / (ℓ : ℝ) := by
          rw [le_div_iff₀ hℓpos]
          exact_mod_cast hcon
        exact Nat.le_floor h2
    have h2 : (∑ d ∈ Finset.Icc 1 ⌊w / (ℓ : ℝ)⌋₊,
          (if (d : ℝ) * (ℓ : ℝ) ≤ w then t d else 0))
        = ∑ d ∈ Finset.Icc 1 ⌊w / (ℓ : ℝ)⌋₊, t d := by
      refine Finset.sum_congr rfl (fun d hd => ?_)
      rw [Finset.mem_Icc] at hd
      rw [if_pos]
      have h3 : (d : ℝ) ≤ w / (ℓ : ℝ) :=
        le_trans (by exact_mod_cast hd.2) (Nat.floor_le (div_nonneg hw0 hℓpos.le))
      rw [le_div_iff₀ hℓpos] at h3
      linarith [h3]
    rw [← h1, h2]
  · have hwneg : w < 0 := not_le.mp hw0
    have hfl : ⌊w / (ℓ : ℝ)⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr (lt_trans (div_neg_of_neg_of_pos hwneg hℓpos) one_pos)
    rw [s3RemSub, hfl, Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) > (0 : ℕ)),
      Finset.sum_empty]
    symm
    refine Finset.sum_eq_zero (fun d hd => ?_)
    rw [if_neg]
    intro hcon
    have h1 : (0 : ℝ) ≤ (d : ℝ) * (ℓ : ℝ) := by positivity
    linarith

/-! ## 2. The joint rectangle integrand -/

/-- The `ℓ`-th summand of the joint substituted integrand on the common rectangle `[zc, M·e·zc] ×
[1, x/Cm]`: the `ℓ`-indicators times `τ(ℓ)²·s3RemSub` (in fixed-range form, so jointly
measurable in `(v,w)`). -/
def Fsub (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (v w : ℝ) : ℝ :=
  if (ℓ : ℝ) * zc x B ≤ v ∧ v ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧ (ℓ : ℝ) ≤ w ∧
      v ≤ (x : ℝ) then
    ((ℓ.divisors.card : ℝ)) ^ 2 * s3RemSubF x Cm x ℓ (sc x B) v w
  else 0

/-- The indicator defining `Fsub`, as a measurable set. -/
lemma measurableSet_Fsub_cond (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) :
    MeasurableSet {p : ℝ × ℝ |
      (ℓ : ℝ) * zc x B ≤ p.1 ∧ p.1 ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧
        (ℓ : ℝ) ≤ p.2 ∧ p.1 ≤ (x : ℝ)} := by
  have hA : MeasurableSet {p : ℝ × ℝ | (ℓ : ℝ) * zc x B ≤ p.1} :=
    measurableSet_le (measurable_const : Measurable (fun _ : ℝ × ℝ => (ℓ : ℝ) * zc x B)) measurable_fst
  have hB : MeasurableSet {p : ℝ × ℝ | p.1 ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B)} :=
    measurableSet_le measurable_fst
      (measurable_const : Measurable (fun _ : ℝ × ℝ => (ℓ : ℝ) * (Real.exp 1 * zc x B)))
  have hC : MeasurableSet {p : ℝ × ℝ | (ℓ : ℝ) ≤ p.2} :=
    measurableSet_le (measurable_const : Measurable (fun _ : ℝ × ℝ => (ℓ : ℝ))) measurable_snd
  have hD : MeasurableSet {p : ℝ × ℝ | p.1 ≤ (x : ℝ)} :=
    measurableSet_le measurable_fst (measurable_const : Measurable (fun _ : ℝ × ℝ => (x : ℝ)))
  have hset : {p : ℝ × ℝ | (ℓ : ℝ) * zc x B ≤ p.1 ∧ p.1 ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧
      (ℓ : ℝ) ≤ p.2 ∧ p.1 ≤ (x : ℝ)}
      = {p : ℝ × ℝ | (ℓ : ℝ) * zc x B ≤ p.1}
        ∩ ({p : ℝ × ℝ | p.1 ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B)}
          ∩ ({p : ℝ × ℝ | (ℓ : ℝ) ≤ p.2} ∩ {p : ℝ × ℝ | p.1 ≤ (x : ℝ)})) := by
    ext p
    simp [Set.mem_inter_iff, and_assoc]
  rw [hset]
  exact hA.inter (hB.inter (hC.inter hD))

lemma Fsub_nonneg (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (v w : ℝ) : 0 ≤ Fsub x Cm B ℓ v w := by
  unfold Fsub
  by_cases h : (ℓ : ℝ) * zc x B ≤ v ∧ v ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧ (ℓ : ℝ) ≤ w ∧
      v ≤ (x : ℝ)
  · rw [if_pos h]
    exact mul_nonneg (by positivity) (s3RemSubF_nonneg _ _ _ _ _ _ _)
  · rw [if_neg h]

lemma measurable_Fsub (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) :
    Measurable (fun p : ℝ × ℝ => Fsub x Cm B ℓ p.1 p.2) := by
  unfold Fsub
  refine Measurable.ite (measurableSet_Fsub_cond x Cm B ℓ) ?_ measurable_const
  exact (measurable_const : Measurable (fun _ : ℝ × ℝ => ((ℓ.divisors.card : ℝ)) ^ 2)).mul
    (measurable_s3RemSubF x Cm x ℓ (sc x B))

/-- On the `w`-range `w ≤ x` the joint integrand `Ksub` is the `ℓ`-sum of `Fsub`. -/
lemma Ksub_eq_sum_Fsub_of_le (x Cm : ℕ) (B : ℝ) {v w : ℝ} (hw : w ≤ (x : ℝ)) :
    Ksub x Cm B v w = ∑ ℓ ∈ Finset.Icc 1 x, Fsub x Cm B ℓ v w := by
  rw [Ksub]
  refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
  rw [Finset.mem_Icc] at hℓ
  unfold Fsub
  by_cases h : (ℓ : ℝ) * zc x B ≤ v ∧ v ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧ (ℓ : ℝ) ≤ w ∧
      v ≤ (x : ℝ)
  · rw [if_pos h, if_pos h, s3RemSub_eq_s3RemSubF x Cm x ℓ (sc x B) hℓ.1 ?_]
    have h1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ.1
    nlinarith [hw, h1]
  · rw [if_neg h, if_neg h]

/-- Crude bound for the fixed-range form: every `d`-term is at most `4·Ã(x)` provided both
`(1.7)`-scales stay `≤ x`. -/
lemma abs_s3RemSubF_le (x Cm N ℓ : ℕ) (sc v w : ℝ) (hvx : v ≤ (x : ℝ))
    (hCw : (Cm : ℝ) * w ≤ (x : ℝ)) :
    |s3RemSubF x Cm N ℓ sc v w| ≤ (N : ℝ) * (4 * AcountAtilC x) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hm1 : ⌊min (sc * v) (x : ℝ)⌋₊ ≤ x :=
    le_trans (Nat.floor_mono (min_le_right _ _)) (by simp)
  have hm2 : ⌊max v ((Cm : ℝ) * w)⌋₊ ≤ x :=
    le_trans (Nat.floor_mono (max_le hvx hCw)) (by simp)
  unfold s3RemSubF
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ d ∈ Finset.Icc 1 N,
      |(if (d : ℝ) * (ℓ : ℝ) ≤ w then
        (|cfR (ℓ * d) ⌊min (sc * v) (x : ℝ)⌋₊| + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|)
        else 0)| ≤ 4 * AcountAtilC x := by
    intro d _
    by_cases hd : (d : ℝ) * (ℓ : ℝ) ≤ w
    · rw [if_pos hd, abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
      have e1 := AcountAtilC_mono_nat hm1
      have e2 := AcountAtilC_mono_nat hm2
      have h1 := abs_cfR_le (ℓ * d) ⌊min (sc * v) (x : ℝ)⌋₊
      have h2 := abs_cfR_le (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊
      linarith
    · rw [if_neg hd, abs_zero]
      positivity
  calc ∑ d ∈ Finset.Icc 1 N,
        |(if (d : ℝ) * (ℓ : ℝ) ≤ w then
          (|cfR (ℓ * d) ⌊min (sc * v) (x : ℝ)⌋₊| + |cfR (ℓ * d) ⌊max v ((Cm : ℝ) * w)⌋₊|)
          else 0)|
      ≤ ∑ _d ∈ Finset.Icc 1 N, (4 * AcountAtilC x) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 1 N).card : ℝ) * (4 * AcountAtilC x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (4 * AcountAtilC x) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_Icc_one_le N

/-- Crude bound for `Fsub` on the rectangle: for `v ≤ x` and `Cm·w ≤ x` the value is at most
`τ(ℓ)²·x·4·Ã(x)`. -/
lemma abs_Fsub_le (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (v w : ℝ) (hvx : v ≤ (x : ℝ))
    (hCw : (Cm : ℝ) * w ≤ (x : ℝ)) :
    |Fsub x Cm B ℓ v w| ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  unfold Fsub
  by_cases h : (ℓ : ℝ) * zc x B ≤ v ∧ v ≤ (ℓ : ℝ) * (Real.exp 1 * zc x B) ∧ (ℓ : ℝ) ≤ w ∧
      v ≤ (x : ℝ)
  · rw [if_pos h, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((ℓ.divisors.card : ℝ)) ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact abs_s3RemSubF_le x Cm x ℓ (sc x B) v w hvx hCw
  · rw [if_neg h, abs_zero]
    positivity

/-- Global bound for `Fsub` on the rectangle in terms of `x` alone. -/
lemma abs_Fsub_le_global (x Cm : ℕ) (B : ℝ) (ℓ : ℕ) (v w : ℝ) (hℓx : ℓ ≤ x)
    (hvx : v ≤ (x : ℝ)) (hCw : (Cm : ℝ) * w ≤ (x : ℝ)) :
    |Fsub x Cm B ℓ v w| ≤ (x : ℝ) ^ 2 * ((x : ℝ) * (4 * AcountAtilC x)) := by
  have hAnn : 0 ≤ AcountAtilC x := AcountAtilC_nonneg x
  have hcard : ((ℓ.divisors.card : ℝ)) ^ 2 ≤ (x : ℝ) ^ 2 := by
    have h1 : ((ℓ.divisors.card : ℝ)) ≤ (ℓ : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self ℓ
    have h2 : ((ℓ : ℝ)) ≤ (x : ℝ) := by exact_mod_cast hℓx
    calc ((ℓ.divisors.card : ℝ)) ^ 2 ≤ ((ℓ : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ ≤ (x : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  refine le_trans (abs_Fsub_le x Cm B ℓ v w hvx hCw) ?_
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

end

end Work.FIChain
