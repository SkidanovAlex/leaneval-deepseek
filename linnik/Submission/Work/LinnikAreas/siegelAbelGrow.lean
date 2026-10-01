import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.pairCountHeight_dom
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count
import Submission.Work.LinnikAreas.sum_mul_exp_neg_le_of_count_head

/-!
# AREA 6 — the per-layer Abel lemmas of the *improved* high-zero route

`Work.LinnikAreas.siegelRestHighCoupled` (`Submission/Work/LinnikAreas/siegelRestHighCoupled.lean`)
bounds the high-zero mass `restHighZeroSum` from the coupled Deuring--Heilbronn height estimate
`Siegel.DHLogFreeHeightCoupled c`, for `c ≤ 3`.  The bottleneck is the *σ-blind* tail of its Abel
splitting, whose `q`-exponent is `-(1+ε)(49/10/c - 1)`: it must beat the `q^{-1/2}` that Siegel's
theorem supplies, which forces `c ≤ 3.277`.  The classical (and the chapter's own) constant is
`67/14 = 4.786`, so that route is unusable as it stands.

This file supplies the pieces of the *fix* (the full recipe is in
`Submission/Work/LinnikAreas/NOTES_area6_route.md`): split each dyadic height layer at the
threshold `λ* = (1+1/100)𝓛/c` and

* bound the **head** (`λ ≤ λ*`) by the coupled count, using the upper-threshold Abel lemma
  `sum_mul_exp_neg_le_of_count_head` (`Work.LinnikAreas.siegelHeadAbel`);
* bound the **tail** (`λ > λ*`) by the *λ₁-free* log-free family count in the height direction
  (`LogFreeFamHeight (5/2) (3/2)`, provable from Jutila's and Huxley's family counts by
  `Work.ZeroDensity.Assembly.logFreeFamHeight_of_cores`), using the lower-threshold Abel lemma
  `sum_mul_exp_neg_le_of_count` (`Work.LinnikAreas.siegelTailAbel`).

The tail contributes `≪ D·q^{-(49/10-5/2)(1+1/100)/c}` (`D = h^{3/2}` for a layer of real height
`h`), which after the kernel weight `4/(h𝓛)²` and the dyadic sum over `h = 2^{j+1}` is
`≪ 𝓛^{-2}q^{-(49/10-5/2)(1+1/100)/c}` — enough against `λ₁𝓛^{-1/2}` (Siegel) whenever
`(49/10-5/2)(1+1/100)/c > 1/2`, i.e. `c < 4.848`, and in particular for the classical
`c = 67/14`.  The head is bounded by the existing machinery (`layer_sum_first_le`,
`rpowLayerGeom`) as before once the σ-blind tail is removed.

`tail_layer_bound` is the arithmetic core of the tail: the dyadic layer sum
`Σ_j (4^j)⁻¹(2^{j+1})^{3/2} ≤ 16` together with `e^{-(49/10-5/2)λ*} ≤ q^{-1/2}` for `c ≤ 24/5`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- `4^{-j}·2^{(j+1)t} ≤ 2^t·(3/4)^j` for `t ≤ 3/2` (copied from
`siegelRestHighCoupled.lean`, where it is private). -/
private lemma pow_two_decay_gen {t : ℝ} (ht : t ≤ 3 / 2) (j : ℕ) :
    ((4 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ ((j + 1 : ℕ) * t) ≤ (2 : ℝ) ^ t * ((3 / 4 : ℝ) ^ j) := by
  have h4 : ((4 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ (-(2 : ℝ))) ^ j := by
    rw [← inv_pow]
    congr 1
    norm_num
  have h3 : (2 : ℝ) ^ ((j + 1 : ℕ) * t) = (2 : ℝ) ^ t * ((2 : ℝ) ^ t) ^ j := by
    rw [show (((j + 1 : ℕ) : ℝ) * t) = t + ((j : ℝ) * t) by push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [← Real.rpow_natCast ((2 : ℝ) ^ t) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hkey : (2 : ℝ) ^ (-(2 : ℝ)) * (2 : ℝ) ^ t ≤ (3 / 4 : ℝ) := by
    have h1 : (2 : ℝ) ^ (-(2 : ℝ)) * (2 : ℝ) ^ t = (2 : ℝ) ^ (t - 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [h1]
    have h2 : (2 : ℝ) ^ (t - 2) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
    refine le_trans h2 ?_
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h5 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    rw [(one_div (Real.sqrt 2)).symm, div_le_iff₀ hpos]
    nlinarith [h5]
  rw [h4, h3]
  calc ((2 : ℝ) ^ (-(2 : ℝ))) ^ j * ((2 : ℝ) ^ t * ((2 : ℝ) ^ t) ^ j)
      = (2 : ℝ) ^ t * (((2 : ℝ) ^ (-(2 : ℝ))) * ((2 : ℝ) ^ t)) ^ j := by
        rw [mul_pow]; ring
    _ ≤ (2 : ℝ) ^ t * ((3 / 4 : ℝ) ^ j) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
        exact pow_le_pow_left₀ (by positivity) hkey j

/-- **The head of the Abel splitting, against the coupled (`λ₁`-saving) count.**
For a finite set `S` of zero-pairs all of whose `λ` is `≤ lam`, the mass is at most
`C·λ₁·e^B·(lam+1)·e^{max 0 ((B-49/10)lam)}` whenever the coupled count
`N(t) ≤ C·λ₁·e^{Bt}` holds on `(0, lam+1]`.  (This is the *upper*-threshold Abel lemma
`Work.LinnikAreas.sum_mul_exp_neg_le_of_count_head`, with no restriction `B < 49/10` —
which is exactly what is needed for the tall height layers.) -/
lemma siegelHeadAbel {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q)
    (β₁ : ℂ) {C lam1 B lam T₀ : ℝ} (hC : 0 < C) (hlam1 : 0 < lam1) (hlam0 : 0 < lam)
    (hT₀ : 1 ≤ T₀)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ lam + 1 →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T₀ ≤ C * lam1 * Real.exp (B * t))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log q ≤ T₀)
    (hlamS : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ lam) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ Real.exp (49 / 10) * (C * lam1 * Real.exp B * (lam + 1)
          * Real.exp (max 0 ((B - 49 / 10) * lam))) := by
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hlam0' : ∀ z ∈ S, 0 ≤ Work.LinnikContract.lamOf q z.2 := by
    intro z hz
    rw [Work.LinnikContract.lamOf]
    exact mul_nonneg (by have := boxMaxZeroAux.zeroMult_re_lt_one z.1 (hzm z hz); linarith) hlogq.le
  have hcount' : ∀ t : ℝ, 0 < t → t ≤ lam + 1 →
      (∑ z ∈ S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t),
        (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)) ≤ (C * lam1) * Real.exp (B * t) := by
    intro t ht0 ht1
    refine le_trans (pairCountHeight_dom hq χ₁ β₁
      (S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)) ?_
    simpa only [mul_assoc] using hcnt t ht0 ht1
  have hbase := sum_mul_exp_neg_le_of_count_head (a := 49 / 10) (B := B) (C := C * lam1)
    (lam0 := lam) S
    (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
    (fun z => Work.LinnikContract.lamOf q z.2)
    (by norm_num) (fun z _ => Nat.cast_nonneg _) hlam0' hlamS hlam0.le (by positivity) hcount'
  refine le_trans hbase ?_
  have h1 : (1 : ℝ) ≤ Real.exp (49 / 10) := Real.one_le_exp (by norm_num)
  have h2 : (0 : ℝ) ≤ C * lam1 * Real.exp B * (lam + 1)
      * Real.exp (max 0 ((B - 49 / 10) * lam)) := by positivity
  calc C * lam1 * Real.exp B * (lam + 1) * Real.exp (max 0 ((B - 49 / 10) * lam))
      = 1 * (C * lam1 * Real.exp B * (lam + 1)
          * Real.exp (max 0 ((B - 49 / 10) * lam))) := by ring
    _ ≤ Real.exp (49 / 10) * (C * lam1 * Real.exp B * (lam + 1)
          * Real.exp (max 0 ((B - 49 / 10) * lam))) := mul_le_mul_of_nonneg_right h1 h2

/-- **The tail of the Abel splitting, against the `λ₁`-*free* log-free family count.**
For a finite set `S` of zero-pairs all of whose `λ` is `≥ lam`, if the *family* count
`N(t) ≤ C₂·e^{(5/2)t}·D` holds on `(0, log q]` then the mass is at most
`100·C₂·D·e^{-(49/10-5/2)lam}`.  The threshold `lam` is what produces the saving: the count
grows like `e^{(5/2)t}` while the weight decays like `e^{-(49/10)t}`. -/
lemma siegelTailAbel {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q)
    (β₁ : ℂ) {C₂ D lam T₀ : ℝ} (hC₂ : 0 < C₂) (hD : 0 < D) (hlam0 : 0 < lam)
    (hT₀ : 1 ≤ T₀)
    (hgrow : ∀ t : ℝ, 0 < t → t ≤ Real.log q →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T₀
        ≤ C₂ * Real.exp ((5 / 2) * t) * D)
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log q ≤ T₀)
    (hlamS : ∀ z ∈ S, lam ≤ Work.LinnikContract.lamOf q z.2) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ 100 * C₂ * D * Real.exp (-(49 / 10 - 5 / 2) * lam) := by
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hmain := sum_mul_exp_neg_le_of_count S
    (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
    (fun z => Work.LinnikContract.lamOf q z.2)
    (a₀ := 49 / 10) (Λ := lam) (L := Real.log q) (D := C₂ * D) (lam₁ := 1) (c := 5 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) hlam0 (by norm_num)
    (fun z _ => Nat.cast_nonneg _) hlamS
    (fun z hz => by
      have hpos : 0 < z.2.re := zeroMult_re_pos z.1 (hzm z hz)
      rw [Work.LinnikContract.lamOf]
      have h2 : 1 - z.2.re < 1 := by linarith
      nlinarith [hlogq])
    (fun t htL htU => by
      have ht0 : 0 < t := lt_of_lt_of_le hlam0 htL
      refine le_trans (pairCountHeight_dom hq χ₁ β₁
        (S.filter (fun z => Work.LinnikContract.lamOf q z.2 ≤ t))
        (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => him z (Finset.mem_filter.mp hz).1)
        (fun z hz => hexc z (Finset.mem_filter.mp hz).1)) ?_
      calc Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T₀
          ≤ C₂ * Real.exp ((5 / 2) * t) * D := hgrow t ht0 htU
        _ = (C₂ * D) * 1 * Real.exp ((5 / 2) * t) := by ring)
  refine le_trans hmain ?_
  have hden : 0 < 1 - Real.exp ((5 : ℝ) / 2 - 49 / 10) := by
    have h : Real.exp ((5 : ℝ) / 2 - 49 / 10) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  rw [div_le_iff₀ hden]
  have hexp5 : Real.exp (5 / 2) ≤ 27 := by
    have h3 : Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have h4 : (Real.exp 1) ^ 3 ≤ 3 ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
    have h5 : Real.exp (5 / 2 : ℝ) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
    have h6 : (3 : ℝ) ^ 3 = 27 := by norm_num
    linarith [h5, h4, h6, h3.le, h3.ge]
  have hden2 : (1 / 2 : ℝ) ≤ 1 - Real.exp ((5 : ℝ) / 2 - 49 / 10) := by
    have he2 : (2 : ℝ) ≤ Real.exp (2 : ℝ) := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have h2 : Real.exp (2 : ℝ) = (Real.exp 1) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h2]; nlinarith [Real.exp_pos 1]
    have h2 : Real.exp ((5 : ℝ) / 2 - 49 / 10) ≤ 1 / 2 := by
      have hle : ((5 : ℝ) / 2 - 49 / 10) ≤ -(2 : ℝ) := by norm_num
      have h3 : Real.exp ((5 : ℝ) / 2 - 49 / 10) ≤ Real.exp (-(2 : ℝ)) :=
        Real.exp_le_exp.mpr hle
      have h4 : Real.exp (-(2 : ℝ)) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 2)]
        linarith
      linarith
    linarith
  have hbase : (0 : ℝ) < C₂ * D * Real.exp (-(49 / 10 - 5 / 2) * lam) := by positivity
  rw [show (C₂ * D) * 1 * Real.exp (5 / 2) * Real.exp ((5 / 2 - 49 / 10) * lam)
      = C₂ * D * Real.exp (-(49 / 10 - 5 / 2) * lam) * Real.exp (5 / 2) by
        rw [show (5 : ℝ) / 2 - 49 / 10 = -(49 / 10 - 5 / 2) by ring]; ring]
  rw [show 100 * C₂ * D * Real.exp (-(49 / 10 - 5 / 2) * lam)
        * (1 - Real.exp (5 / 2 - 49 / 10))
      = C₂ * D * Real.exp (-(49 / 10 - 5 / 2) * lam)
        * (100 * (1 - Real.exp (5 / 2 - 49 / 10))) by ring]
  refine mul_le_mul_of_nonneg_left ?_ hbase.le
  nlinarith [hexp5, hden2]

/-- **One dyadic height layer: head (coupled count) + tail (λ₁-free family count).** -/
lemma high_layer_massGrow {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) {C C₂ D lam1 B lam T₀ : ℝ}
    (hC : 0 < C) (hC₂ : 0 < C₂) (hD : 0 < D) (hlam1 : 0 < lam1) (hB : 0 < B)
    (hlam0 : 0 < lam) (hT₀ : 1 ≤ T₀)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ lam + 1 →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T₀ ≤ C * lam1 * Real.exp (B * t))
    (hgrow : ∀ t : ℝ, 0 < t → t ≤ Real.log q →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T₀
        ≤ C₂ * Real.exp ((5 / 2) * t) * D)
    (v : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ v, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ v, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ v, |z.2.im| * Real.log q ≤ T₀) :
    (∑ z ∈ v, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
      ≤ Real.exp (49 / 10) * (C * lam1 * Real.exp B * (lam + 1)
          * Real.exp (max 0 ((B - 49 / 10) * lam)))
        + 100 * C₂ * D * Real.exp (-(49 / 10 - 5 / 2) * lam) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not v
    (fun z : DirichletCharacter ℂ q × ℂ => Work.LinnikContract.lamOf q z.2 ≤ lam)
    (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
      * Real.exp (-(49 / 10) * Work.LinnikContract.lamOf q z.2))
  rw [← hsplit]
  refine add_le_add ?_ ?_
  · exact siegelHeadAbel hq χ₁ β₁ hC hlam1 hlam0 hT₀ hcnt _
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
  · exact siegelTailAbel hq χ₁ β₁ hC₂ hD hlam0 hT₀ hgrow _
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)
      (fun z hz => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hz).2))

/-- **The `λ₁`-free tail layer sum.**  For `c ∈ (0, 24/5]`, `𝓛 ≥ 10`,
`λ* = (1+1/100)𝓛/c` and the dyadic layers `h_j = 2^{j+1}`,

`Σ_j (4^j)⁻¹·h_j^{3/2}·e^{-(49/10-5/2)λ*} ≤ 100·C₂·16·q^{-1/2}`:

the layer sum `Σ_j (4^j)⁻¹(2^{j+1})^{3/2} ≤ 16` is geometric (`pow_two_decay_gen` at `t = 3/2`),
and `e^{-(49/10-5/2)λ*} = q^{-(49/10-5/2)(1+1/100)/c} ≤ q^{-1/2}` because
`(49/10-5/2)(1+1/100)/c ≥ 1/2` for `c ≤ 24/5`. -/
lemma tail_layer_bound {q : ℕ} [NeZero q] {c C₂ : ℝ} (hC₂ : 0 < C₂) (hc : 0 < c)
    (hc3 : c ≤ 24 / 5) (hL : 10 ≤ Real.log q) (s : Finset ℕ) :
    (∑ j ∈ s, ((4 : ℝ) ^ j)⁻¹ * (100 * C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
        * Real.exp (-(49 / 10 - 5 / 2) * ((1 + 1 / 100) * Real.log q / c))))
      ≤ 100 * C₂ * 16 * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have h1 : (1 : ℝ) < (q : ℝ) := by
      by_contra hle
      push_neg at hle
      have h0 : Real.log (q : ℝ) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
      linarith
    exact h1.le
  have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  have hqpow : Real.exp (-(49 / 10 - 5 / 2) * ((1 + 1 / 100) * Real.log q / c))
      ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [show Real.exp (-(49 / 10 - 5 / 2) * ((1 + 1 / 100) * Real.log q / c))
        = (q : ℝ) ^ (-(49 / 10 - 5 / 2) * ((1 + 1 / 100) / c)) by
      rw [Real.rpow_def_of_pos hq0]
      congr 1
      ring]
    refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
    rw [neg_mul, neg_le_neg_iff,
      show (49 / 10 - 5 / 2) * ((1 + 1 / 100) / c)
        = (49 / 10 - 5 / 2) * (1 + 1 / 100) / c by ring]
    rw [le_div_iff₀ hc]
    nlinarith [hc3]
  have hlayersum : (∑ j ∈ s, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)) ≤ 16 := by
    have key : ∀ j : ℕ, ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
        = (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (3 / 2)) := by
      intro j
      rw [← Real.rpow_natCast (2 : ℝ) (j + 1),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((j + 1 : ℕ) : ℝ) (3 / 2)]
    have hpt : ∀ j : ℕ, ((4 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (3 / 2))
        ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * ((3 / 4 : ℝ) ^ j) :=
      fun j => pow_two_decay_gen (by norm_num : (3 : ℝ) / 2 ≤ 3 / 2) j
    calc (∑ j ∈ s, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ))
        = (∑ j ∈ s, ((4 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (3 / 2))) :=
          Finset.sum_congr rfl (fun j _ => by rw [key j])
      _ ≤ ∑ j ∈ s, (2 : ℝ) ^ (3 / 2 : ℝ) * ((3 / 4 : ℝ) ^ j) :=
          Finset.sum_le_sum (fun j _ => hpt j)
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * ∑ j ∈ s, ((3 / 4 : ℝ) ^ j) := by rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * 4 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ j ∈ s, ((3 / 4 : ℝ) ^ j) ≤ ∑' j : ℕ, ((3 / 4 : ℝ) ^ j) :=
                Summable.sum_le_tsum s (fun i _ => by positivity)
                  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num))
            _ = 4 := by
                rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num)]
                norm_num
      _ ≤ 16 := by
          have h24 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
            have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
              (by norm_num : (3 : ℝ) / 2 ≤ 2)
            have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
            rwa [h4] at h
          nlinarith
  calc (∑ j ∈ s, ((4 : ℝ) ^ j)⁻¹ * (100 * C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)
        * Real.exp (-(49 / 10 - 5 / 2) * ((1 + 1 / 100) * Real.log q / c))))
      = 100 * C₂ * Real.exp (-(49 / 10 - 5 / 2) * ((1 + 1 / 100) * Real.log q / c))
          * (∑ j ∈ s, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ 100 * C₂ * (q : ℝ) ^ (-(1 / 2 : ℝ))
          * (∑ j ∈ s, ((4 : ℝ) ^ j)⁻¹ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqpow (by positivity)) (by positivity)
    _ ≤ 100 * C₂ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * 16 :=
        mul_le_mul_of_nonneg_left hlayersum (by positivity)
    _ = 100 * C₂ * 16 * (q : ℝ) ^ (-(1 / 2 : ℝ)) := by ring


end Work.LinnikAreas
