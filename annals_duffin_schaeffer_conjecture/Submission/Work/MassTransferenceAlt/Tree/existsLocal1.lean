/-
# The local level construction (`R ≤ 1` version)

This file proves `Work.MassTransferenceAlt.Tree.existsLocal1`: the local level
construction of the Beresnevich–Velani proof of the mass transference principle
(`k = 1`, `f(r) = r^d`, `0 < d < 1`), in the form needed for the root interval
`[0,1]` of the Cantor tree, where the parent radius `R = 1/2` is *not* necessarily
at most `Rabs d`.  Accordingly the hypothesis is only `R ≤ 1`.

The construction is the inductive one described in the docstring of
`Work.MassTransferenceAlt.Tree.existsLocal`: starting from the empty family and a
threshold `ε`, each step applies the proven covering lemma
`Work.MassTransferenceAlt.Kgb.exists_kgb` to the parent ball `Iv B R`, with

* forbidden index set `T ∪ F_k` (`F_k` the indices used so far),
* forbidden region `U_k = ⋃_{i ∈ F_k} Iv (c i) (4 ρ i)`,
* thickening `δ_k = R / (32 * (|F_k| + 1))`,
* radius threshold `ε_k`,

and maintains the package `IsLoc` of properties `(P1)`–`(P5)` restricted to the
sub-levels built so far (the structure `Partial` below).  The two estimates fed to
the covering lemma are `∑_{i ∈ F_k} ρ i ≤ R / 2^40` (from `(P2)`, the within-level
disjointness of the enlarged intervals inside `Iv B R`, and `L` sub-levels) and
`2 δ_k |F_k| ≤ R / 16`, whence `H¹ (thickening δ_k U_k ∩ Iv B R) ≤ R / 4`.
-/
import Mathlib
import Submission.Work.MassTransferenceAlt.Basic
import Submission.Work.MassTransferenceAlt.Tree.Defs
import Submission.Work.MassTransferenceAlt.Kgb.exists_kgb

namespace Work.MassTransferenceAlt.Tree

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-! ## Arithmetic and measure preliminaries -/

/-- For `0 < ρ ≤ Rabs d` and `d < 1` the threefold dilation of `Iv (c i) (ρ i)` is
contained in the enlarged interval: `3 ρ ≤ ρ ^ d`. -/
private lemma three_mul_le_rpow (d : ℝ) (hd1 : d < 1) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ρ ≤ Rabs d) : 3 * ρ ≤ ρ ^ d := by
  have hpos : 0 < ρ ^ (1 - d) := Real.rpow_pos_of_pos hρ0 _
  have hle : ρ ^ (1 - d) ≤ (Rabs d) ^ (1 - d) := Real.rpow_le_rpow hρ0.le hρ (by linarith)
  have hR : (Rabs d) ^ (1 - d) = ((2:ℝ)^40)⁻¹ := Rabs_rpow hd1
  have hinv : (2:ℝ)^40 ≤ (ρ ^ (1 - d))⁻¹ := by
    rw [hR] at hle
    rw [show (2:ℝ)^40 = (((2:ℝ)^40)⁻¹)⁻¹ by rw [inv_inv]]
    exact (inv_le_inv₀ (by positivity) hpos).mpr hle
  have hd_eq : ρ ^ d = ρ * (ρ ^ (1 - d))⁻¹ := by
    have h2 : ρ ^ d = ρ ^ ((1:ℝ) - (1 - d)) := by congr 1; ring
    rw [h2, Real.rpow_sub hρ0, Real.rpow_one, div_eq_mul_inv]
  rw [hd_eq]
  have h3 : (3:ℝ) ≤ (ρ ^ (1 - d))⁻¹ := le_trans (by norm_num) hinv
  nlinarith [hρ0]

private lemma Iv_three_subset_Fenl {d : ℝ} (hd1 : d < 1) {c ρ : ℕ → ℝ} {i : ℕ}
    (h0 : 0 < ρ i) (h : ρ i ≤ Rabs d) : Iv (c i) (3 * ρ i) ⊆ Fenl d c ρ i :=
  Iv_mono (three_mul_le_rpow d hd1 h0 h)

private lemma div_two_rpow_pos {δ d : ℝ} (hδ : 0 < δ) : 0 < (δ / 2) ^ (1 / d) :=
  Real.rpow_pos_of_pos (by linarith) _

private lemma div_two_rpow_pow {δ d : ℝ} (hδ : 0 ≤ δ) (hd : d ≠ 0) :
    ((δ / 2) ^ (1 / d)) ^ d = δ / 2 := by
  rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ δ / 2), one_div_mul_cancel hd, Real.rpow_one]

private lemma pow_le_div_two_of_le {δ d x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hd : 0 < d)
    (h : x ≤ (δ / 2) ^ (1 / d)) : x ^ d ≤ δ / 2 := by
  have h1 : x ^ d ≤ ((δ / 2) ^ (1 / d)) ^ d := Real.rpow_le_rpow hx h hd.le
  rwa [div_two_rpow_pow hδ (ne_of_gt hd)] at h1

private lemma pow_le_half_mul_pow {M x d : ℝ} (hM : 0 < M) (hx : 0 ≤ x) (hd : 0 < d)
    (h : x ≤ M / 2 / 2 ^ (1 / d)) : x ^ d ≤ (1 / 2) * M ^ d := by
  have hx' : x ≤ M / (2 * 2 ^ (1 / d)) := by rw [div_div] at h; exact h
  have hpow : x ^ d ≤ (M / (2 * 2 ^ (1 / d))) ^ d := Real.rpow_le_rpow hx hx' hd.le
  rw [Real.div_rpow hM.le (by positivity)] at hpow
  have hden : (2 * (2:ℝ) ^ (1/d)) ^ d = (2:ℝ)^d * 2 := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by norm_num) _),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), show (1/d) * d = 1 by field_simp,
      Real.rpow_one]
  rw [hden] at hpow
  have h2d : (1:ℝ) ≤ (2:ℝ)^d := Real.one_le_rpow (by norm_num) hd.le
  have hMd : 0 ≤ M^d := Real.rpow_nonneg hM.le d
  calc x^d ≤ M^d / ((2:ℝ)^d * 2) := hpow
    _ ≤ M^d / (1 * 2) := div_le_div_of_nonneg_left hMd (by norm_num) (by nlinarith)
    _ = (1/2) * M^d := by ring

/-- If the enlarged intervals of a finite family lie inside `Iv B R` and are pairwise
disjoint, their total `ρ^d`-mass is at most `R`. -/
private lemma sum_pow_le_of_Fenl_disjoint {d : ℝ} (c ρ : ℕ → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (B R : ℝ) (hR : 0 ≤ R) (F : Finset ℕ)
    (hsub : ∀ i ∈ F, Fenl d c ρ i ⊆ Iv B R)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (Fenl d c ρ i) (Fenl d c ρ j)) :
    ∑ i ∈ F, (ρ i) ^ d ≤ R := by
  have hpair : (↑F : Set ℕ).PairwiseDisjoint (fun b => Fenl d c ρ b) :=
    fun a ha b hb hab => hdisj a ha b hb hab
  have hmeas : ∀ b ∈ F, MeasurableSet (Fenl d c ρ b) :=
    fun b _ => (isClosed_Iv (c b) ((ρ b) ^ d)).measurableSet
  have hEq := measure_biUnion_finset (μ := MeasureTheory.Measure.hausdorffMeasure 1) hpair hmeas
  have hle : MeasureTheory.Measure.hausdorffMeasure 1 (⋃ b ∈ F, Fenl d c ρ b)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (Iv B R) := by
    refine measure_mono ?_
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨b, hb, hzb⟩ := hz
    exact hsub b hb hzb
  have hIv : MeasureTheory.Measure.hausdorffMeasure 1 (Iv B R) = ENNReal.ofReal (2 * R) :=
    hausdorffMeasure_one_Iv B R hR
  have hval : ∀ b ∈ F, MeasureTheory.Measure.hausdorffMeasure 1 (Fenl d c ρ b)
      = ENNReal.ofReal (2 * (ρ b) ^ d) := fun b _ => hausdorffMeasure_one_Iv (c b) ((ρ b)^d)
        (Real.rpow_nonneg (hρ b) d)
  have hfin : MeasureTheory.Measure.hausdorffMeasure 1 (⋃ b ∈ F, Fenl d c ρ b)
      = ENNReal.ofReal (∑ b ∈ F, 2 * (ρ b) ^ d) := by
    rw [hEq]
    rw [show (∑ b ∈ F, MeasureTheory.Measure.hausdorffMeasure 1 (Fenl d c ρ b))
        = ∑ b ∈ F, ENNReal.ofReal (2 * (ρ b)^d) from Finset.sum_congr rfl hval]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => by have := hρ b; positivity)]
  have hmain : ENNReal.ofReal (∑ b ∈ F, 2 * (ρ b) ^ d) ≤ ENNReal.ofReal (2 * R) := by
    rw [← hfin, ← hIv]; exact hle
  have hreal : ∑ b ∈ F, 2 * (ρ b) ^ d ≤ 2 * R :=
    (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hmain
  have h2 : ∑ b ∈ F, 2 * (ρ b) ^ d = 2 * ∑ b ∈ F, (ρ b) ^ d := by
    rw [Finset.mul_sum]
  rw [h2] at hreal
  linarith

/-- **Sum of the radii of one sub-level.**  If `0 < R ≤ 1`, `0 < d < 1`, `L ≥ 1`, `F` is a
finite family of indices with `0 < ρ i ≤ thrC d R L` and total mass `∑ (ρ i)^d ≤ R`, then
`∑ ρ i ≤ R / (2^40 * L)`. -/
private lemma level_sum_le_one {d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (B R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1) (L : ℕ) (hL : 1 ≤ L)
    (F : Finset ℕ) (hpos : ∀ i ∈ F, 0 < ρ i) (hthr : ∀ i ∈ F, ρ i ≤ thrC d R L)
    (hmass : ∑ i ∈ F, (ρ i) ^ d ≤ R) :
    ∑ i ∈ F, ρ i ≤ R / (2^40 * L) := by
  have hthr_rpow : (thrC d R L) ^ (1 - d) ≤ R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ)) :=
    thrC_rpow hR0 hd1 hL
  have hpt : ∀ i ∈ F, ρ i ≤ (thrC d R L) ^ (1 - d) * (ρ i) ^ d := by
    intro i hi
    have hpi := hpos i hi
    have h2 : (ρ i) ^ (1 - d) ≤ (thrC d R L) ^ (1 - d) :=
      Real.rpow_le_rpow hpi.le (hthr i hi) (by linarith)
    have h3 : ρ i = (ρ i) ^ d * (ρ i) ^ (1 - d) := by
      rw [← Real.rpow_add hpi, show d + (1 - d) = (1:ℝ) by ring, Real.rpow_one]
    calc ρ i = (ρ i) ^ d * (ρ i) ^ (1 - d) := h3
      _ ≤ (ρ i) ^ d * (thrC d R L) ^ (1 - d) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hpi.le d)
      _ = (thrC d R L) ^ (1 - d) * (ρ i) ^ d := by ring
  have hsum_nonneg : 0 ≤ ∑ i ∈ F, (ρ i) ^ d :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hρ i) d)
  have hLpos : (0:ℝ) < (2:ℝ)^40 * (L:ℝ) := by
    have : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    positivity
  have hstep : (R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ))) * R ≤ R / ((2:ℝ)^40 * (L : ℝ)) := by
    have h1 : R ^ (1 - d) * R = R ^ (1 - d + 1) := by
      rw [Real.rpow_add hR0, Real.rpow_one]
    have h2 : (1:ℝ) ≤ 1 - d + 1 := by linarith
    have h3 : R ^ (1 - d + 1) ≤ R ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hR0 hR1 h2
    have h4 : R ^ (1 - d + 1) ≤ R := by rw [Real.rpow_one] at h3; exact h3
    rw [div_mul_eq_mul_div]
    rw [show R ^ (1 - d) * R = R ^ (1 - d + 1) from h1]
    exact (div_le_div_iff_of_pos_right hLpos).mpr h4
  calc ∑ i ∈ F, ρ i
      ≤ ∑ i ∈ F, (thrC d R L) ^ (1 - d) * (ρ i) ^ d := Finset.sum_le_sum hpt
    _ = (thrC d R L) ^ (1 - d) * ∑ i ∈ F, (ρ i) ^ d := by rw [Finset.mul_sum]
    _ ≤ (R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ))) * ∑ i ∈ F, (ρ i) ^ d :=
        mul_le_mul_of_nonneg_right hthr_rpow hsum_nonneg
    _ ≤ (R ^ (1 - d) / ((2:ℝ)^40 * (L : ℝ))) * R :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ R / ((2:ℝ)^40 * (L : ℝ)) := hstep

/-- **The measure of the thickening of the forbidden region.**  If the total `ρ`-mass of a
finite family is at most `R / 2^40` and `2 δ |s| ≤ R / 16`, then the `δ`-thickening of the
union of the `4`-dilations of its members has `1`-dimensional Hausdorff measure at most
`R / 4` inside `Iv B R`. -/
private lemma thickening_measure_bound {c ρ : ℕ → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (s : Finset ℕ)
    (B R δ : ℝ) (hδ0 : 0 ≤ δ) (hR0 : 0 < R) (hsum : ∑ i ∈ s, ρ i ≤ R / 2^40)
    (hcard : 2 * δ * s.card ≤ R / 16) :
    MeasureTheory.Measure.hausdorffMeasure 1
      (Metric.thickening δ (⋃ i ∈ (s : Set ℕ), Iv (c i) (4 * ρ i)) ∩ Iv B R) ≤
      ENNReal.ofReal (R / 4) := by
  refine le_trans (measure_mono Set.inter_subset_left) ?_
  refine le_trans (measure_thickening_biUnion_Iv_le hρ s δ hδ0) ?_
  apply ENNReal.ofReal_le_ofReal
  have hsum' : ∑ i ∈ s, 2 * (4 * ρ i + δ) = 8 * (∑ i ∈ s, ρ i) + 2 * δ * s.card := by
    have e : ∀ i ∈ s, 2 * (4 * ρ i + δ) = 8 * ρ i + 2 * δ := fun i _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [hsum']
  have h1 : 8 * (∑ i ∈ s, ρ i) ≤ 8 * (R / 2^40) := by linarith [hsum]
  have h2 : 8 * (R / 2^40) = R * (8 / 2^40) := by ring
  have hnum : (8:ℝ) / 2^40 ≤ 3/16 := by norm_num
  have h3 : R * (8 / 2^40) ≤ R * (3/16) := mul_le_mul_of_nonneg_left hnum hR0.le
  have h4 : R * (3/16) + R / 16 = R / 4 := by ring
  linarith [h1, h2, h3, h4, hcard]



/-! ## The indices used by the sub-levels built so far -/

/-- The set of indices used by the first `n` sub-levels. -/
def usedIdx (SL : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ := (Finset.range n).biUnion SL

@[simp] lemma mem_usedIdx {SL : ℕ → Finset ℕ} {n i : ℕ} :
    i ∈ usedIdx SL n ↔ ∃ j < n, i ∈ SL j := by
  simp [usedIdx]

@[simp] lemma usedIdx_zero (SL : ℕ → Finset ℕ) : usedIdx SL 0 = ∅ := by
  simp [usedIdx]

lemma usedIdx_succ (SL : ℕ → Finset ℕ) (n : ℕ) :
    usedIdx SL (n + 1) = usedIdx SL n ∪ SL n := by
  ext i
  rw [mem_usedIdx, Finset.mem_union, mem_usedIdx]
  constructor
  · rintro ⟨j, hj, hij⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
    · exact Or.inl ⟨j, h, hij⟩
    · exact Or.inr (h ▸ hij)
  · rintro (⟨j, hj, hij⟩ | hi)
    · exact ⟨j, lt_trans hj (Nat.lt_succ_self n), hij⟩
    · exact ⟨n, Nat.lt_succ_self n, hi⟩

/-- The thickening parameter of the forbidden region at the next sub-level. -/
noncomputable def delta (R : ℝ) (s : Finset ℕ) : ℝ := R / (32 * ((s.card : ℝ) + 1))

lemma delta_pos {R : ℝ} (hR : 0 < R) (s : Finset ℕ) : 0 < delta R s := by
  rw [delta]
  exact div_pos hR (by positivity)

lemma delta_sixteen {R : ℝ} (hR : 0 < R) (s : Finset ℕ) : 16 * delta R s ≤ R := by
  have hc : (0:ℝ) < 32 * ((s.card : ℝ) + 1) := by positivity
  have h1 : (1:ℝ) ≤ (s.card : ℝ) + 1 := by
    have : (0:ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    linarith
  rw [delta, ← mul_div_assoc, div_le_iff₀ hc]
  nlinarith

lemma delta_card {R : ℝ} (hR : 0 < R) (s : Finset ℕ) : 2 * delta R s * s.card ≤ R / 16 := by
  have hc : (0:ℝ) < 32 * ((s.card : ℝ) + 1) := by positivity
  rw [delta]
  rw [show 2 * (R / (32 * ((s.card : ℝ) + 1))) * s.card
        = (2 * R * s.card) / (32 * ((s.card : ℝ) + 1)) by ring]
  rw [div_le_div_iff₀ hc (by norm_num : (0:ℝ) < 16)]
  nlinarith [hR.le]

/-- Adjoining a new sub-level `S` at position `n` to a sequence of sub-levels `SL`. -/
def extendLevel (SL : ℕ → Finset ℕ) (n : ℕ) (S : Finset ℕ) : ℕ → Finset ℕ :=
  fun j => if j < n then SL j else if j = n then S else ∅

@[simp] lemma mem_extendLevel {SL : ℕ → Finset ℕ} {S : Finset ℕ} {n j i : ℕ} :
    i ∈ extendLevel SL n S j ↔ (j < n ∧ i ∈ SL j) ∨ (j = n ∧ i ∈ S) := by
  rw [extendLevel]
  by_cases hj : j < n
  · simp [hj, ne_of_lt hj]
  · by_cases hje : j = n
    · simp [hj, hje]
    · simp [hj, hje]

lemma extendLevel_of_lt {SL : ℕ → Finset ℕ} {S : Finset ℕ} {n j : ℕ} (hj : j < n) :
    extendLevel SL n S j = SL j := by
  rw [extendLevel, if_pos hj]

@[simp] lemma extendLevel_self (SL : ℕ → Finset ℕ) (n : ℕ) (S : Finset ℕ) :
    extendLevel SL n S n = S := by
  rw [extendLevel]
  simp

lemma extendLevel_of_gt {SL : ℕ → Finset ℕ} {S : Finset ℕ} {n j : ℕ} (hj : n < j) :
    extendLevel SL n S j = ∅ := by
  rw [extendLevel]
  have h1 : ¬ j < n := by omega
  have h2 : ¬ j = n := by omega
  rw [if_neg h1, if_neg h2]

lemma usedIdx_extend (SL : ℕ → Finset ℕ) (n : ℕ) (S : Finset ℕ) :
    usedIdx (extendLevel SL n S) (n + 1) = usedIdx SL n ∪ S := by
  ext i
  rw [mem_usedIdx, Finset.mem_union, mem_usedIdx]
  constructor
  · rintro ⟨j, hj, hij⟩
    rw [mem_extendLevel] at hij
    rcases hij with ⟨hjn, hij⟩ | ⟨hje, hij⟩
    · exact Or.inl ⟨j, hjn, hij⟩
    · exact Or.inr hij
  · rintro (⟨j, hj, hij⟩ | hi)
    · exact ⟨j, lt_trans hj (Nat.lt_succ_self n), by rw [mem_extendLevel]; exact Or.inl ⟨hj, hij⟩⟩
    · exact ⟨n, Nat.lt_succ_self n, by rw [mem_extendLevel]; exact Or.inr ⟨rfl, hi⟩⟩

/-! ## The inductive invariant -/

/-- **The invariant of the inductive construction of a local level.**

`Partial d c ρ B R T L n SL ε` says that the sub-levels `SL 0, …, SL (n-1)` are a valid
beginning of a local level of the ball `Iv B R` with `L` sub-levels, avoiding the finite
forbidden index set `T`, and that `ε` is a valid radius threshold for sub-level `n`:
properties `(P1)`–`(P5)` of `IsLoc` hold for the sub-levels built so far, together with
the arithmetic facts needed to run the next application of `exists_kgb`. -/
structure Partial (d : ℝ) (c ρ : ℕ → ℝ) (B R : ℝ) (T : Finset ℕ) (L : ℕ)
    (n : ℕ) (SL : ℕ → Finset ℕ) (ε : ℝ) : Prop where
  /-- there is nothing above the constructed sub-levels -/
  empty_above : ∀ j, n ≤ j → SL j = ∅
  /-- all children have positive radius -/
  pos : ∀ j, j < n → ∀ i ∈ SL j, 0 < ρ i
  /-- all children are below the radius threshold -/
  le_thrC : ∀ j, j < n → ∀ i ∈ SL j, ρ i ≤ thrC d R L
  /-- the enlarged interval of every child is inside the parent ball -/
  sub_parent : ∀ j, j < n → ∀ i ∈ SL j, Fenl d c ρ i ⊆ Iv B R
  /-- the enlarged intervals of a sub-level are pairwise disjoint -/
  discFenl : ∀ j, j < n → ∀ i ∈ SL j, ∀ i' ∈ SL j, i ≠ i' →
      Disjoint (Fenl d c ρ i) (Fenl d c ρ i')
  /-- the threefold dilations of all children built so far are pairwise disjoint -/
  disc3 : ∀ j, j < n → ∀ i ∈ SL j, ∀ j', j' < n → ∀ i' ∈ SL j', i ≠ i' →
      Disjoint (Iv (c i) (3 * ρ i)) (Iv (c i') (3 * ρ i'))
  /-- every sub-level carries mass `R / 16` -/
  mass : ∀ j, j < n → R / 16 ≤ ∑ i ∈ SL j, (ρ i) ^ d
  /-- geometric decay of the radii across sub-levels -/
  decay : ∀ j j', j < n → j' < n → j < j' → ∀ i ∈ SL j, ∀ i' ∈ SL j',
      (ρ i') ^ d ≤ ((1:ℝ) / 2) ^ (j' - j) * (ρ i) ^ d
  /-- every sub-level is nonempty -/
  nonempty : ∀ j, j < n → (SL j).Nonempty
  /-- the sub-levels use disjoint index sets -/
  discIdx : ∀ j j', j < n → j' < n → j ≠ j' → Disjoint (SL j) (SL j')
  /-- the indices used so far avoid `T` -/
  fresh : ∀ j, j < n → ∀ i ∈ SL j, i ∉ T
  /-- the threshold is positive -/
  eps_pos : 0 < ε
  /-- the threshold is below the radius threshold of the level -/
  eps_le_thrC : ε ≤ thrC d R L
  /-- the arithmetic of the threshold for the next application of `exists_kgb` -/
  eps_arith : ε ^ d ≤ delta R (usedIdx SL n) / 2
  /-- the threshold is small compared with the radii of the previous sub-level -/
  eps_decay : ∀ j, j + 1 = n → ∀ i ∈ SL j, ε ^ d ≤ (1/2 : ℝ) * (ρ i) ^ d



/-! ## The induction step -/

/-- **The induction step of the local level construction.**  Adjoin one sub-level to a
partial level, using the covering lemma `exists_kgb` with forbidden region the `4`-dilations
of the children built so far. -/
theorem partial_succ {d : ℝ} {c ρ : ℕ → ℝ} {B R : ℝ} {T : Finset ℕ} {L : ℕ}
    (hd0 : 0 < d) (hd1 : d < 1) (hρ : ∀ i, 0 ≤ ρ i)
    (hρfin : ∀ ε : ℝ, 0 < ε → {i : ℕ | ε ≤ ρ i}.Finite)
    (hfull : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc a b ∩ LSenl d c ρ)
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc a b))
    (hR0 : 0 < R) (hR1 : R ≤ 1) (hB0 : 0 ≤ B - R) (hB1 : B + R ≤ 1) (hL : 1 ≤ L)
    {n : ℕ} (hn : n < L) {SL : ℕ → Finset ℕ} {ε : ℝ}
    (h : Partial d c ρ B R T L n SL ε) :
    ∃ (S : Finset ℕ) (ε' : ℝ), Partial d c ρ B R T L (n + 1) (extendLevel SL n S) ε'
      ∧ (∀ i ∈ S, i ∉ T) := by
  classical
  set s : Finset ℕ := usedIdx SL n with hs
  have hRLpos : (0:ℝ) < (2:ℝ)^40 * (L:ℝ) := by
    have h1 : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    positivity
  have hnL : (n:ℝ) ≤ (L:ℝ) := by
    have h1 : n ≤ L := le_of_lt hn
    exact_mod_cast h1
  -- the mass of one sub-level is at most `R`, whence the sum of its radii is small
  have hpow : ∀ j, j < n → ∑ i ∈ SL j, (ρ i)^d ≤ R := fun j hj =>
    sum_pow_le_of_Fenl_disjoint c ρ hρ B R hR0.le (SL j) (h.sub_parent j hj) (h.discFenl j hj)
  have hlev : ∀ j, j < n → ∑ i ∈ SL j, ρ i ≤ R / (2^40 * L) := fun j hj =>
    level_sum_le_one (d := d) hd0 hd1 c ρ hρ B R hR0 hR1 L hL (SL j) (h.pos j hj)
      (h.le_thrC j hj) (hpow j hj)
  have hsum : ∑ i ∈ s, ρ i ≤ R / 2^40 := by
    rw [hs, usedIdx]
    rw [Finset.sum_biUnion (fun j hj j' hj' hjj =>
      h.discIdx j j' (Finset.mem_range.mp hj) (Finset.mem_range.mp hj') hjj)]
    have h1 : ∑ j ∈ Finset.range n, ∑ i ∈ SL j, ρ i
        ≤ ∑ _j ∈ Finset.range n, R / ((2:ℝ)^40 * (L:ℝ)) :=
      Finset.sum_le_sum (fun j hj => hlev j (Finset.mem_range.mp hj))
    have h2 : ∑ _j ∈ Finset.range n, R / ((2:ℝ)^40 * (L:ℝ))
        = (n:ℝ) * (R / ((2:ℝ)^40 * (L:ℝ))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h3 : (n:ℝ) * (R / ((2:ℝ)^40 * (L:ℝ))) ≤ R / (2:ℝ)^40 := by
      rw [← mul_div_assoc, div_le_div_iff₀ hRLpos (by norm_num : (0:ℝ) < (2:ℝ)^40)]
      nlinarith [hR0.le]
    linarith
  have hεδ : ε ^ d ≤ delta R s / 2 := by rw [hs]; exact h.eps_arith
  have hδpos : 0 < delta R s := delta_pos hR0 s
  have hδ16 : 16 * delta R s ≤ R := delta_sixteen hR0 s
  have hcard : 2 * delta R s * s.card ≤ R / 16 := delta_card hR0 s
  have hUbound : MeasureTheory.Measure.hausdorffMeasure 1
      (Metric.thickening (delta R s) (⋃ i ∈ (s : Set ℕ), Iv (c i) (4 * ρ i)) ∩ Iv B R)
      ≤ ENNReal.ofReal (R / 4) :=
    thickening_measure_bound hρ s B R (delta R s) hδpos.le hR0 hsum hcard
  obtain ⟨S, hS1, hS2, hS3, hS4, hS5⟩ :=
    Work.MassTransferenceAlt.Kgb.exists_kgb d hd0 c ρ hρ hρfin hfull B R hR0 hB0 hB1
      (⋃ i ∈ (s : Set ℕ), Iv (c i) (4 * ρ i)) (delta R s) hδpos hδ16 hUbound
      (T ∪ s) ε h.eps_pos hεδ
  -- basic consequences of the covering lemma
  have hmemS : ∀ {i : ℕ}, i ∈ S → 0 < ρ i ∧ ρ i ≤ ε := fun {i} hi =>
    ⟨(hS1 i hi).2.1, (hS1 i hi).2.2⟩
  have hSnotT : ∀ {i : ℕ}, i ∈ S → i ∉ T := fun {i} hi hT =>
    (hS1 i hi).1 (Finset.mem_union.mpr (Or.inl hT))
  have hSnotS : ∀ {i : ℕ}, i ∈ S → i ∉ s := fun {i} hi hI =>
    (hS1 i hi).1 (Finset.mem_union.mpr (Or.inr hI))
  have hS_le_Rabs : ∀ i ∈ S, ρ i ≤ Rabs d := fun i hi =>
    le_trans (le_trans (hmemS hi).2 h.eps_le_thrC) (thrC_le_Rabs d R L)
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.sum_empty] at hS5
    have h1 : (0:ℝ) < R / 16 := by linarith
    linarith
  -- the smallest radius of the new sub-level and the new threshold
  obtain ⟨i₀, hi₀, hmin₀⟩ := Finset.exists_min_image S ρ hSne
  set M : ℝ := ρ i₀ with hMdef
  have hMpos : 0 < M := by rw [hMdef]; exact (hmemS hi₀).1
  have hMle : ∀ i ∈ S, M ≤ ρ i := by intro i hi; rw [hMdef]; exact hmin₀ i hi
  set δ' : ℝ := delta R (usedIdx (extendLevel SL n S) (n + 1)) with hδ'def
  have hδ'pos : 0 < δ' := by rw [hδ'def]; exact delta_pos hR0 _
  set ε' : ℝ := min (min (M / 2 / 2 ^ (1/d)) ((δ'/2) ^ (1/d))) (thrC d R L) with hε'def
  have hε'pos : 0 < ε' := by
    rw [hε'def]
    refine lt_min (lt_min ?_ ?_) (thrC_pos hR0 hd1 hL)
    · exact div_pos (div_pos hMpos (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)
    · exact div_two_rpow_pos (by linarith)
  have hε'δ : ε' ^ d ≤ δ' / 2 := by
    refine pow_le_div_two_of_le hδ'pos.le hε'pos.le hd0 ?_
    rw [hε'def]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hε'M : ε' ^ d ≤ (1/2) * M ^ d := by
    refine pow_le_half_mul_pow hMpos hε'pos.le hd0 ?_
    rw [hε'def]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hε'thrC : ε' ≤ thrC d R L := by rw [hε'def]; exact min_le_right _ _
  refine ⟨S, ε', ?_, ?_⟩
  · exact
      { empty_above := by
          intro j hj
          have h1 : ¬ j < n := by omega
          have h2 : ¬ j = n := by omega
          rw [extendLevel, if_neg h1, if_neg h2]
        pos := by
          intro j hj i hi
          rw [mem_extendLevel] at hi
          rcases hi with ⟨hjn, hi⟩ | ⟨-, hi⟩
          · exact h.pos j hjn i hi
          · exact (hmemS hi).1
        le_thrC := by
          intro j hj i hi
          rw [mem_extendLevel] at hi
          rcases hi with ⟨hjn, hi⟩ | ⟨-, hi⟩
          · exact h.le_thrC j hjn i hi
          · exact le_trans (hmemS hi).2 h.eps_le_thrC
        sub_parent := by
          intro j hj i hi
          rw [mem_extendLevel] at hi
          rcases hi with ⟨hjn, hi⟩ | ⟨-, hi⟩
          · exact h.sub_parent j hjn i hi
          · exact hS2 i hi
        discFenl := by
          intro j hj i hi i' hi' hne
          rw [mem_extendLevel] at hi hi'
          rcases hi with ⟨hjn, hi⟩ | ⟨hje, hi⟩
          · rcases hi' with ⟨-, hi'⟩ | ⟨hje', -⟩
            · exact h.discFenl j hjn i hi i' hi' hne
            · exact absurd hjn (by omega)
          · rcases hi' with ⟨hjn', -⟩ | ⟨-, hi'⟩
            · exact absurd hjn' (by omega)
            · exact hS4 i hi i' hi' hne
        disc3 := by
          intro j hj i hi j' hj' i' hi' hne
          rw [mem_extendLevel] at hi hi'
          rcases hi with ⟨hjn, hi⟩ | ⟨hje, hi⟩
          · rcases hi' with ⟨hj'n, hi'⟩ | ⟨hje', hi'⟩
            · exact h.disc3 j hjn i hi j' hj'n i' hi' hne
            · have hU : Iv (c i) (4 * ρ i) ⊆ ⋃ i ∈ (s : Set ℕ), Iv (c i) (4 * ρ i) :=
                fun z hz => Set.mem_iUnion₂.mpr
                  ⟨i, by rw [hs]; exact mem_usedIdx.mpr ⟨j, hjn, hi⟩, hz⟩
              have hdj : Disjoint (Fenl d c ρ i') (Iv (c i) (4 * ρ i)) :=
                (hS3 i' hi').mono_right hU
              have hd2 : Disjoint (Iv (c i') (3 * ρ i')) (Iv (c i) (4 * ρ i)) :=
                hdj.mono_left (Iv_three_subset_Fenl hd1 (hmemS hi').1 (hS_le_Rabs i' hi'))
              exact hd2.symm.mono_left (Iv_mono (by linarith [hρ i]))
          · rcases hi' with ⟨hj'n, hi'⟩ | ⟨hje', hi'⟩
            · have hU : Iv (c i') (4 * ρ i') ⊆ ⋃ i ∈ (s : Set ℕ), Iv (c i) (4 * ρ i) :=
                fun z hz => Set.mem_iUnion₂.mpr
                  ⟨i', by rw [hs]; exact mem_usedIdx.mpr ⟨j', hj'n, hi'⟩, hz⟩
              have hdj : Disjoint (Fenl d c ρ i) (Iv (c i') (4 * ρ i')) :=
                (hS3 i hi).mono_right hU
              have hd2 : Disjoint (Iv (c i) (3 * ρ i)) (Iv (c i') (4 * ρ i')) :=
                hdj.mono_left (Iv_three_subset_Fenl hd1 (hmemS hi).1 (hS_le_Rabs i hi))
              exact hd2.mono_right (Iv_mono (by linarith [hρ i']))
            · exact Disjoint.mono (Iv_three_subset_Fenl hd1 (hmemS hi).1 (hS_le_Rabs i hi))
                (Iv_three_subset_Fenl hd1 (hmemS hi').1 (hS_le_Rabs i' hi'))
                (hS4 i hi i' hi' hne)
        mass := by
          intro j hj
          by_cases hjn : j < n
          · rw [extendLevel_of_lt hjn]; exact h.mass j hjn
          · have hje : j = n := by omega
            rw [hje, extendLevel_self]; exact hS5
        decay := by
          intro j j' hj hj' hlt i hi i' hi'
          rw [mem_extendLevel] at hi hi'
          rcases hi with ⟨hjn, hi⟩ | ⟨hje, hi⟩
          · rcases hi' with ⟨hj'n, hi'⟩ | ⟨hje', hi'⟩
            · exact h.decay j j' hjn hj'n hlt i hi i' hi'
            · rw [hje']
              have hpd : (ρ i') ^ d ≤ ε ^ d := Real.rpow_le_rpow (hρ i') (hmemS hi').2 hd0.le
              by_cases hjn1 : j = n - 1
              · rw [hjn1] at hi ⊢
                rw [show n - (n - 1) = 1 by omega, pow_one]
                exact le_trans hpd (h.eps_decay (n - 1) (by omega) i hi)
              · have hjlt : j < n - 1 := by omega
                obtain ⟨i'', hi''⟩ := h.nonempty (n - 1) (by omega)
                have hε'' : ε ^ d ≤ (1/2) * (ρ i'') ^ d := h.eps_decay (n - 1) (by omega) i'' hi''
                have hdec'' : (ρ i'') ^ d ≤ (1/2)^((n - 1) - j) * (ρ i)^d :=
                  h.decay j (n - 1) hjn (by omega) hjlt i hi i'' hi''
                have hchain : (ρ i')^d ≤ (1/2) * ((1/2)^((n - 1) - j) * (ρ i)^d) := by
                  have h1 : (1/2) * (ρ i'')^d
                      ≤ (1/2) * ((1/2)^((n - 1) - j) * (ρ i)^d) :=
                    mul_le_mul_of_nonneg_left hdec'' (by norm_num)
                  exact le_trans hpd (le_trans hε'' h1)
                have hexp : (1/2:ℝ)^(n - j) = (1/2) * (1/2)^((n - 1) - j) := by
                  have h1 : n - j = (n - 1 - j) + 1 := by omega
                  rw [h1, pow_succ, mul_comm]
                rw [hexp]
                calc (ρ i')^d ≤ (1/2) * ((1/2)^((n - 1) - j) * (ρ i)^d) := hchain
                  _ = ((1/2) * (1/2)^((n - 1) - j)) * (ρ i)^d := by ring
          · exact absurd hlt (by omega)
        nonempty := by
          intro j hj
          by_cases hjn : j < n
          · rw [extendLevel_of_lt hjn]; exact h.nonempty j hjn
          · have hje : j = n := by omega
            rw [hje, extendLevel_self]; exact hSne
        discIdx := by
          intro j j' hj hj' hne
          by_cases hjn : j < n
          · by_cases hj'n : j' < n
            · rw [extendLevel_of_lt hjn, extendLevel_of_lt hj'n]
              exact h.discIdx j j' hjn hj'n hne
            · have hje' : j' = n := by omega
              rw [extendLevel_of_lt hjn, hje', extendLevel_self, Finset.disjoint_left]
              intro i hiSL hiS
              exact hSnotS hiS (mem_usedIdx.mpr ⟨j, hjn, hiSL⟩)
          · have hje : j = n := by omega
            rw [hje]
            by_cases hj'n : j' < n
            · rw [extendLevel_self, extendLevel_of_lt hj'n]
              rw [Finset.disjoint_left]
              intro i hiS hiSL
              exact hSnotS hiS (mem_usedIdx.mpr ⟨j', hj'n, hiSL⟩)
            · have hje' : j' = n := by omega
              exact absurd (hje' ▸ hje) hne
        fresh := by
          intro j hj i hi
          rw [mem_extendLevel] at hi
          rcases hi with ⟨hjn, hi⟩ | ⟨-, hi⟩
          · exact h.fresh j hjn i hi
          · exact hSnotT hi
        eps_pos := hε'pos
        eps_le_thrC := hε'thrC
        eps_arith := by rw [← hδ'def]; exact hε'δ
        eps_decay := by
          intro j hj i hi
          have hje : j = n := by omega
          rw [hje, extendLevel_self] at hi
          exact le_trans hε'M (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hMpos.le (hMle i hi) hd0.le) (by norm_num)) }
  · intro i hi
    exact hSnotT hi

/-- **The base of the induction.**  The empty partial level, with an initial threshold
below both `thrC d R L` and the arithmetic threshold of `exists_kgb`. -/
theorem partial_zero (d : ℝ) (c ρ : ℕ → ℝ) (B R : ℝ) (T : Finset ℕ) (L : ℕ)
    (hd0 : 0 < d) (hd1 : d < 1) (hR0 : 0 < R) (hL : 1 ≤ L) :
    ∃ (SL : ℕ → Finset ℕ) (ε : ℝ), Partial d c ρ B R T L 0 SL ε := by
  classical
  refine ⟨fun _ => ∅, min (thrC d R L) ((delta R ∅ / 2) ^ (1/d)), ?_⟩
  have hδ0 : 0 < delta R ∅ := delta_pos hR0 ∅
  have hTpos : 0 < thrC d R L := thrC_pos hR0 hd1 hL
  refine
    { empty_above := fun j _ => rfl
      pos := fun j hj i hi => absurd hj (Nat.not_lt_zero j)
      le_thrC := fun j hj i hi => absurd hj (Nat.not_lt_zero j)
      sub_parent := fun j hj i hi => absurd hj (Nat.not_lt_zero j)
      discFenl := fun j hj i hi => absurd hj (Nat.not_lt_zero j)
      disc3 := fun j hj i hi => absurd hj (Nat.not_lt_zero j)
      mass := fun j hj => absurd hj (Nat.not_lt_zero j)
      decay := fun j j' hj hj' => absurd hj (Nat.not_lt_zero j)
      nonempty := fun j hj => absurd hj (Nat.not_lt_zero j)
      discIdx := fun j j' hj hj' => absurd hj (Nat.not_lt_zero j)
      fresh := fun j hj => absurd hj (Nat.not_lt_zero j)
      eps_pos := lt_min hTpos (div_two_rpow_pos hδ0)
      eps_le_thrC := min_le_left _ _
      eps_arith := by
        rw [show usedIdx (fun _ => ∅) 0 = ∅ from usedIdx_zero _]
        exact pow_le_div_two_of_le hδ0.le (le_of_lt (lt_min hTpos (div_two_rpow_pos hδ0)))
          hd0 (min_le_right _ _)
      eps_decay := fun j hj i hi => absurd hj (by omega) }

/-- **The local level construction** (`R ≤ 1` version, applicable to the root `[0,1]`). -/
theorem existsLocal1 (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (hρfin : ∀ ε : ℝ, 0 < ε → {i : ℕ | ε ≤ ρ i}.Finite)
    (hfull : ∀ a b : ℝ, 0 ≤ a → b ≤ 1 →
      MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc a b ∩ Work.MassTransferenceAlt.LSenl d c ρ)
        = MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc a b))
    (B R : ℝ) (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hB0 : 0 ≤ B - R) (hB1 : B + R ≤ 1)
    (T : Finset ℕ) (L : ℕ) (hL : 1 ≤ L) :
    ∃ (F : Finset ℕ) (sub : ℕ → ℕ),
      (∀ i ∈ F, i ∉ T) ∧ Work.MassTransferenceAlt.IsLoc d c ρ B R F sub L := by
  classical
  -- the inductive construction of the sub-levels
  have main : ∀ n, n ≤ L → ∃ (SL : ℕ → Finset ℕ) (ε : ℝ), Partial d c ρ B R T L n SL ε := by
    intro n
    induction n with
    | zero => intro _; exact partial_zero d c ρ B R T L hd0 hd1 hR0 hL
    | succ n ih =>
      intro hnL
      have hn : n < L := by omega
      obtain ⟨SL, ε, hP⟩ := ih (le_of_lt hn)
      obtain ⟨S, ε', hP', -⟩ :=
        partial_succ hd0 hd1 hρ hρfin hfull hR0 hR1 hB0 hB1 hL hn hP
      exact ⟨extendLevel SL n S, ε', hP'⟩
  obtain ⟨SL, ε, hP⟩ := main L le_rfl
  -- the sub-level of an index of the full level
  let sub : ℕ → ℕ := fun i => if h : ∃ k < L, i ∈ SL k then Classical.choose h else 0
  have hsub_iff : ∀ i, i ∈ usedIdx SL L → ∀ k < L, (sub i = k ↔ i ∈ SL k) := by
    intro i hi k hk
    have hex : ∃ k, k < L ∧ i ∈ SL k := mem_usedIdx.mp hi
    have hch : sub i = Classical.choose hex := dif_pos hex
    have hspec := Classical.choose_spec hex
    constructor
    · intro h
      have h1 : Classical.choose hex = k := by rw [← hch]; exact h
      rw [← h1]; exact hspec.2
    · intro hik
      by_cases heq : Classical.choose hex = k
      · rw [hch, heq]
      · have hdisj := hP.discIdx k (Classical.choose hex) hk hspec.1 (fun h => heq h.symm)
        exact absurd hspec.2 (Finset.disjoint_left.mp hdisj hik)
  refine ⟨usedIdx SL L, sub, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- freshness
    intro i hi
    obtain ⟨k, hk, hik⟩ := mem_usedIdx.mp hi
    exact hP.fresh k hk i hik
  · -- positivity
    intro i hi
    obtain ⟨k, hk, hik⟩ := mem_usedIdx.mp hi
    exact hP.pos k hk i hik
  · -- the radius threshold
    intro i hi
    obtain ⟨k, hk, hik⟩ := mem_usedIdx.mp hi
    exact hP.le_thrC k hk i hik
  · -- the children lie in the parent
    intro i hi
    obtain ⟨k, hk, hik⟩ := mem_usedIdx.mp hi
    exact hP.sub_parent k hk i hik
  · -- disjointness of the enlarged intervals inside a sub-level
    intro i hi j hj hne heq
    obtain ⟨k, hk, hik⟩ := mem_usedIdx.mp hi
    have hjk : j ∈ SL k := (hsub_iff j hj k hk).mp (heq ▸ (hsub_iff i hi k hk).mpr hik)
    exact hP.discFenl k hk i hik j hjk hne
  · -- disjointness of the threefold dilations
    intro i hi j hj hne
    obtain ⟨k, hk, hik⟩ := mem_usedIdx.mp hi
    obtain ⟨l, hl, hjl⟩ := mem_usedIdx.mp hj
    have hik' : sub i = k := (hsub_iff i hi k hk).mpr hik
    have hjl' : sub j = l := (hsub_iff j hj l hl).mpr hjl
    rcases lt_trichotomy k l with hlt | heq | hgt
    · exact hP.disc3 k hk i hik l hl j hjl hne
    · rw [← heq] at hjl
      exact Disjoint.mono
        (Iv_three_subset_Fenl hd1 (hP.pos k hk i hik)
          (le_trans (hP.le_thrC k hk i hik) (thrC_le_Rabs d R L)))
        (Iv_three_subset_Fenl hd1 (hP.pos k hk j hjl)
          (le_trans (hP.le_thrC k hk j hjl) (thrC_le_Rabs d R L)))
        (hP.discFenl k hk i hik j hjl hne)
    · exact (hP.disc3 l hl j hjl k hk i hik hne.symm).symm
  · -- the sub-level index is below `L`
    intro i hi
    obtain ⟨k, hk, hik⟩ := mem_usedIdx.mp hi
    rw [(hsub_iff i hi k hk).mpr hik]
    exact hk
  · -- every sub-level is attained
    intro k hk
    obtain ⟨i, hi⟩ := hP.nonempty k hk
    exact ⟨i, mem_usedIdx.mpr ⟨k, hk, hi⟩, (hsub_iff i (mem_usedIdx.mpr ⟨k, hk, hi⟩) k hk).mpr hi⟩
  · -- the mass of every sub-level
    intro k hk
    have hfilter : (usedIdx SL L).filter (fun i => sub i = k) = SL k := by
      ext i
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hi, hsubk⟩
        exact (hsub_iff i hi k hk).mp hsubk
      · intro hik
        exact ⟨mem_usedIdx.mpr ⟨k, hk, hik⟩,
          (hsub_iff i (mem_usedIdx.mpr ⟨k, hk, hik⟩) k hk).mpr hik⟩
    rw [hfilter]
    exact hP.mass k hk
  · -- the geometric decay across sub-levels
    intro i hi j hj hlt
    obtain ⟨k, hk, hik⟩ := mem_usedIdx.mp hi
    obtain ⟨l, hl, hjl⟩ := mem_usedIdx.mp hj
    have hik' : sub i = k := (hsub_iff i hi k hk).mpr hik
    have hjl' : sub j = l := (hsub_iff j hj l hl).mpr hjl
    have hkl : k < l := by rw [← hik', ← hjl']; exact hlt
    have hdec := hP.decay k l hk hl hkl i hik j hjl
    rw [hjl', hik']
    exact hdec

end Work.MassTransferenceAlt.Tree
