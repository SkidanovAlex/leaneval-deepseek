import Mathlib
import Submission.Threshold
import Submission.Helpers

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-!
# Measurability of threshold sublevel sets

Tikhomirov 2020, proof of Theorem~A.  The fibre/conditional estimates of the
final layer condition on events of the form
`{x : Fin n → ℝ | threshold p x L ≤ S}` (threshold sublevel sets of the random
unit normal).  This module proves that every such set is measurable (indeed
closed in the Euclidean topology of `(Fin n → ℝ)`), which makes the
`H := {threshold ≤ S}` conditioning sets measurable for the fibre lemmas.

Route: the canonical Bernoulli(`p`) product measure is supported on the finite
set `{ω | ωᵢ = 0 ∨ ωᵢ = 1}` (`supportSet`), on which
`|Σᵢ ωᵢ(xᵢ − yᵢ)| ≤ Σᵢ |xᵢ − yᵢ|`.  Hence for vectors `y` close to `x`, the
slab mass `P{|Σωx − l| ≤ t}` is bounded by the slab mass of `y` at radius
`t + Σᵢ|xᵢ−yᵢ|`.  Combined with the slope bound
(`cfP_le_slope_of_threshold`) this shows that the sublevel sets
`{x | threshold p x L ≤ S}` are sequentially closed, hence measurable.
-/

namespace Submission.ThresholdMeas

open MeasureTheory ProbabilityTheory Measure Filter
open scoped ENNReal BigOperators Topology
open Submission.Threshold
open Submission.Helpers

/-- The support of the canonical Bernoulli(`p`) product measure: coordinate
functions with values in `{0,1}`. -/
def supportSet {n : ℕ} : Set (Fin n → ℝ) :=
  {ω | ∀ i : Fin n, ω i = 0 ∨ ω i = 1}

/-- The two-point set `{0,1}` is measurable. -/
lemma measurableSet_bool_pair : MeasurableSet ({0, 1} : Set ℝ) := by
  exact (IsClosed.union (isClosed_singleton : IsClosed ({0} : Set ℝ))
    (isClosed_singleton : IsClosed ({1} : Set ℝ))).measurableSet

/-- The support set is measurable (a finite intersection of cylinders). -/
lemma measurable_supportSet {n : ℕ} : MeasurableSet (supportSet : Set (Fin n → ℝ)) := by
  classical
  unfold supportSet
  have hEq : {ω : Fin n → ℝ | ∀ i : Fin n, ω i = 0 ∨ ω i = 1} =
      ⋂ i : Fin n, (fun ω : Fin n → ℝ => ω i) ⁻¹' ({0, 1} : Set ℝ) := by
    ext ω
    simp
  rw [hEq]
  exact MeasurableSet.iInter (fun i : Fin n => (measurable_pi_apply (δ := Fin n) (X := fun _ : Fin n => ℝ) i) measurableSet_bool_pair)

/-- Coordinate value `|ω i| ≤ 1` on the support. -/
lemma support_abs_le_one {n : ℕ} {ω : Fin n → ℝ} (hω : ω ∈ supportSet) (i : Fin n) :
    |ω i| ≤ 1 := by
  rcases hω i with h0 | h1
  · rw [h0]
    norm_num
  · rw [h1]
    norm_num

/-- On the support, `|Σᵢ ωᵢ·aᵢ| ≤ Σᵢ |aᵢ|`. -/
lemma abs_weighted_sum_le_sum_abs {n : ℕ} {ω : Fin n → ℝ} (hω : ω ∈ supportSet) (a : Fin n → ℝ) :
    |∑ i : Fin n, ω i * a i| ≤ ∑ i : Fin n, |a i| := by
  calc
    |∑ i : Fin n, ω i * a i| ≤ ∑ i : Fin n, |ω i * a i| := by
        simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin n => ω i * a i) (Finset.univ))
    _ = ∑ i : Fin n, |ω i| * |a i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul]
    _ ≤ ∑ i : Fin n, |a i| := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_of_le_one_left (abs_nonneg _) (support_abs_le_one hω i)

/-- The complement of the support has measure zero under `berP p`. -/
lemma support_compl_measure_zero {n : ℕ} (p : unitInterval) :
    berP (n := n) p (supportSetᶜ) = 0 := by
  classical
  have hEq : supportSetᶜ = ⋃ i : Fin n, {ω : Fin n → ℝ | ¬(ω i = 0 ∨ ω i = 1)} := by
    ext ω
    simp [supportSet]
  rw [hEq]
  apply le_antisymm
  · calc
      berP (n := n) p (⋃ i : Fin n, {ω : Fin n → ℝ | ¬(ω i = 0 ∨ ω i = 1)})
          ≤ ∑ i : Fin n, berP (n := n) p {ω : Fin n → ℝ | ¬(ω i = 0 ∨ ω i = 1)} := by
              simpa using (MeasureTheory.measure_iUnion_fintype_le (berP (n := n) p)
                (fun i : Fin n => {ω : Fin n → ℝ | ¬(ω i = 0 ∨ ω i = 1)}))
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hzero : (bernoulliMeasure 1 0 p) ({x : ℝ | x = 0 ∨ x = 1}ᶜ) = 0 := by
            have hmeas : MeasurableSet ({x : ℝ | x = 0 ∨ x = 1}ᶜ) :=
              measurableSet_bool_pair.compl
            have hmem0 : (0 : ℝ) ∉ ({x : ℝ | x = 0 ∨ x = 1}ᶜ) := by simp
            have hmem1 : (1 : ℝ) ∉ ({x : ℝ | x = 0 ∨ x = 1}ᶜ) := by simp
            simpa using (bernoulliMeasure_apply_of_notMem_of_notMem p hmeas hmem1 hmem0)
          -- cylinder {ω | ω i ∉ {0,1}} has the coordinate mass
          have hcyl : berP (n := n) p {ω : Fin n → ℝ | ¬(ω i = 0 ∨ ω i = 1)} =
              (bernoulliMeasure 1 0 p) ({x : ℝ | x = 0 ∨ x = 1}ᶜ) := by
            let f : (Fin n → ℝ) → ℝ := fun ω : Fin n → ℝ => ω i
            let s : Set ℝ := {x : ℝ | x = 0 ∨ x = 1}ᶜ
            have hpre : f ⁻¹' s = {ω : Fin n → ℝ | ¬(ω i = 0 ∨ ω i = 1)} := by
              ext ω
              simp [f, s]
            rw [← hpre]
            have hmeas_f : Measurable f := by
              dsimp [f]
              exact measurable_pi_apply (δ := Fin n) (X := fun _ : Fin n => ℝ) i
            have hmap : (berP (n := n) p).map f = bernoulliMeasure 1 0 p := by
              have hfun : f = Function.eval (α := Fin n) (β := fun _ : Fin n => ℝ) i := by
                funext ω
                rfl
              rw [hfun]
              exact marginal_proj p i
            calc
              berP (n := n) p (f ⁻¹' s) = (berP (n := n) p).map f s := by
                  rw [← Measure.map_apply hmeas_f (show MeasurableSet s by
                    dsimp [s]
                    exact measurableSet_bool_pair.compl)]
              _ = (bernoulliMeasure 1 0 p) s := by rw [hmap]
              _ = (bernoulliMeasure 1 0 p) ({x : ℝ | x = 0 ∨ x = 1}ᶜ) := by rfl
          rw [hcyl, hzero]
  · exact bot_le

/-- Any slab-type measurable set loses nothing by intersecting with the
support. -/
lemma measure_slab_eq_inter_support {n : ℕ} (p : unitInterval) {E : Set (Fin n → ℝ)}
    (hE : MeasurableSet E) : berP (n := n) p E = berP (n := n) p (E ∩ supportSet) := by
  classical
  apply le_antisymm
  · have hsub : E ⊆ (E ∩ supportSet) ∪ supportSetᶜ := by
      intro x hx
      by_cases h : x ∈ supportSet
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    have hm1 : MeasurableSet (E ∩ supportSet) := hE.inter (measurable_supportSet (n := n))
    have hm2 : MeasurableSet (supportSetᶜ : Set (Fin n → ℝ)) := (measurable_supportSet (n := n)).compl
    calc
      berP (n := n) p E ≤ berP (n := n) p ((E ∩ supportSet) ∪ supportSetᶜ) :=
          measure_mono hsub
      _ ≤ berP (n := n) p (E ∩ supportSet) + berP (n := n) p supportSetᶜ :=
          measure_union_le (E ∩ supportSet) supportSetᶜ
      _ = berP (n := n) p (E ∩ supportSet) := by
          rw [support_compl_measure_zero p]
          simp
  · exact measure_mono (by intro x hx; exact hx.1)

/-- The slab event `{|Σᵢ ωᵢvᵢ − l| ≤ t}` on the canonical space. -/
def slabEvent {n : ℕ} (v : Fin n → ℝ) (l t : ℝ) : Set (Fin n → ℝ) :=
  {ω : Fin n → ℝ | |∑ i : Fin n, ω i * v i - l| ≤ t}

/-- Slab events are measurable. -/
lemma measurable_slabEvent {n : ℕ} (v : Fin n → ℝ) (l t : ℝ) :
    MeasurableSet (slabEvent v l t : Set (Fin n → ℝ)) := by
  have hG : Measurable (fun ω : Fin n → ℝ => |∑ i : Fin n, ω i * v i - l|) := by
    fun_prop
  change MeasurableSet ((fun ω : Fin n → ℝ => |∑ i : Fin n, ω i * v i - l|) ⁻¹' (Set.Iic t))
  exact hG (isClosed_Iic.measurableSet)

/-- On the support, membership in the `x`-slab forces membership in the
`xm`-slab at radius `t + Σ|x − xm|`. -/
lemma slab_support_subset {n : ℕ} {x xm : Fin n → ℝ} {l t : ℝ} :
    (slabEvent x l t) ∩ supportSet ⊆ slabEvent xm l (t + ∑ i : Fin n, |x i - xm i|) := by
  intro ω hω
  have hmem : |∑ i : Fin n, ω i * x i - l| ≤ t := hω.1
  have hsupp : ω ∈ supportSet := hω.2
  dsimp [slabEvent] at *
  have hb' : |∑ i : Fin n, ω i * (xm i - x i)| ≤ ∑ i : Fin n, |x i - xm i| := by
    simpa [abs_sub_comm] using (abs_weighted_sum_le_sum_abs hsupp (fun i : Fin n => xm i - x i))
  have hsplit : (∑ i : Fin n, ω i * xm i - l) =
      (∑ i : Fin n, ω i * (xm i - x i)) + (∑ i : Fin n, ω i * x i - l) := by
    have h1 : (∑ i : Fin n, ω i * (xm i - x i)) =
        (∑ i : Fin n, ω i * xm i) - (∑ i : Fin n, ω i * x i) := by
      calc
        (∑ i : Fin n, ω i * (xm i - x i))
            = ∑ i : Fin n, (ω i * xm i - ω i * x i) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = (∑ i : Fin n, ω i * xm i) - (∑ i : Fin n, ω i * x i) := by
                rw [← Finset.sum_sub_distrib]
    calc
      (∑ i : Fin n, ω i * xm i - l)
          = ((∑ i : Fin n, ω i * xm i) - (∑ i : Fin n, ω i * x i)) + ((∑ i : Fin n, ω i * x i) - l) := by ring
      _ = (∑ i : Fin n, ω i * (xm i - x i)) + (∑ i : Fin n, ω i * x i - l) := by
              rw [← h1]
  calc
    |∑ i : Fin n, ω i * xm i - l| ≤ |∑ i : Fin n, ω i * (xm i - x i)| + |∑ i : Fin n, ω i * x i - l| := by
        rw [hsplit]
        exact abs_add_le _ _
    _ ≤ (∑ i : Fin n, |x i - xm i|) + t := by
        exact add_le_add hb' hmem
    _ = t + ∑ i : Fin n, |x i - xm i| := by rw [add_comm]



/-- Slab measure comparison: the `x`-slab has at most the mass of the `xm`-slab
at radius `t + Σ|x − xm|` (the support has full measure). -/
lemma measure_slab_le_of_close {n : ℕ} (p : unitInterval) {x xm : Fin n → ℝ} {l t : ℝ} :
    berP (n := n) p (slabEvent x l t) ≤
      berP (n := n) p (slabEvent xm l (t + ∑ i : Fin n, |x i - xm i|)) := by
  have hE1 : MeasurableSet (slabEvent x l t : Set (Fin n → ℝ)) := measurable_slabEvent x l t
  rw [measure_slab_eq_inter_support p hE1]
  exact measure_mono (slab_support_subset (x := x) (xm := xm) (l := l) (t := t))

/-- A probability bound on a single slab: if `xm` has threshold below
`t + Σ|x − xm|`, then the `x`-slab at radius `t` has real mass at most
`L·(t + Σ|x − xm|)`. -/
lemma real_slab_le_of_close_threshold {n : ℕ} (p : unitInterval) {x xm : Fin n → ℝ}
    {l : ℝ} {t : ℝ} (ht0 : 0 < t) {L : ℝ} (hL : 1 ≤ L)
    (hthr : threshold p xm L < t + ∑ i : Fin n, |x i - xm i|) :
    (berP (n := n) p (slabEvent x l t)).toReal ≤ L * (t + ∑ i : Fin n, |x i - xm i|) := by
  let δ : ℝ := ∑ i : Fin n, |x i - xm i|
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact Finset.sum_nonneg (fun i hi => abs_nonneg _)
  have hc1 : berP (n := n) p (slabEvent x l t) ≤ berP (n := n) p (slabEvent xm l (t + δ)) := by
    simpa [δ] using (measure_slab_le_of_close p (x := x) (xm := xm) (l := l) (t := t))
  have hc2 : berP (n := n) p (slabEvent xm l (t + δ)) ≤
      cfP (n := n) p xm (t + δ) := by
    dsimp [cfP, slabEvent]
    exact le_levyConcentration (berP (n := n) p)
      (fun ω : Fin n → ℝ => ∑ i : Fin n, ω i * xm i) (t + δ) l
  have hpos : 0 < t + δ := by linarith
  have hc3 : cfP (n := n) p xm (t + δ) ≤ ENNReal.ofReal (L * (t + δ)) := by
    simpa [δ] using (cfP_le_slope_of_threshold (n := n) (p := p) (x := xm) (L := L) hL hpos hthr)
  have hchain : berP (n := n) p (slabEvent x l t) ≤ ENNReal.ofReal (L * (t + δ)) :=
    le_trans hc1 (le_trans hc2 hc3)
  have hle1 : berP (n := n) p (slabEvent x l t) ≤ (1 : ℝ≥0∞) := by
    exact le_trans (measure_mono (Set.subset_univ _))
      (le_of_eq (by simp [MeasureTheory.IsProbabilityMeasure.measure_univ] :
        (berP (n := n) p) Set.univ = (1 : ℝ≥0∞)))
  have hEfinite : berP (n := n) p (slabEvent x l t) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle1
  have htoReal : (berP (n := n) p (slabEvent x l t)).toReal ≤ L * (t + δ) := by
    have h' : (berP (n := n) p (slabEvent x l t)).toReal ≤
        (ENNReal.ofReal (L * (t + δ))).toReal :=
      (ENNReal.toReal_le_toReal hEfinite ENNReal.ofReal_ne_top).2 hchain
    have hnonneg : 0 ≤ L * (t + δ) := by
      have hL0 : 0 ≤ L := by linarith
      exact mul_nonneg hL0 (by linarith)
    simpa [ENNReal.toReal_ofReal hnonneg] using h'
  simpa [δ] using htoReal

/-- `Σᵢ |x i − xseq m i| → 0` whenever `xseq m → x`. -/
lemma tendsto_sum_abs_sub {n : ℕ} {xseq : ℕ → Fin n → ℝ} {x : Fin n → ℝ}
    (hconv : Tendsto xseq atTop (𝓝 x)) :
    Tendsto (fun m : ℕ => ∑ i : Fin n, |x i - xseq m i|) atTop (𝓝 0) := by
  have hcoord : ∀ i : Fin n, Tendsto (fun m : ℕ => |x i - xseq m i|) atTop (𝓝 0) := by
    intro i
    have hc : Tendsto (fun m : ℕ => xseq m i) atTop (𝓝 (x i)) := by
      exact ((continuous_apply i).tendsto x).comp hconv
    have hsub : Tendsto (fun m : ℕ => x i - xseq m i) atTop (𝓝 (x i - x i)) :=
      tendsto_const_nhds.sub hc
    have hz : x i - x i = 0 := by ring
    rw [hz] at hsub
    simpa using hsub.abs
  have hsum := tendsto_finsetSum (s := (Finset.univ : Finset (Fin n)))
    (f := fun i : Fin n => fun m : ℕ => |x i - xseq m i|)
    (x := atTop) (a := fun i : Fin n => 0)
  have hmain : Tendsto (fun b : ℕ => ∑ i ∈ (Finset.univ : Finset (Fin n)), |x i - xseq b i|)
      atTop (𝓝 (∑ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ))) := by
    exact hsum (by intro i hi; exact hcoord i)
  simpa using hmain

/-- `threshold p x L ≤ S` from slope bounds above `S`. -/
lemma threshold_le_of_cf_above {n : ℕ} (p : unitInterval) {x : Fin n → ℝ} {L S : ℝ}
    (hS : 0 < S) (hcf : ∀ t : ℝ, S < t → cfP (n := n) p x t ≤ ENNReal.ofReal (L * t)) :
    threshold p x L ≤ S := by
  unfold threshold
  apply Real.sSup_le
  · intro t ht
    by_contra hnot
    have htS : S < t := lt_of_not_ge hnot
    have hb := hcf t htS
    exact (not_lt_of_ge hb) ht.2.2
  · exact le_of_lt hS


/-- Slab masses of the probability measure never exceed one. -/
lemma measure_slab_le_one {n : ℕ} (p : unitInterval) (v : Fin n → ℝ) (l t : ℝ) :
    berP (n := n) p (slabEvent v l t) ≤ (1 : ℝ≥0∞) := by
  exact le_trans (measure_mono (Set.subset_univ _))
    (le_of_eq (by simp [MeasureTheory.IsProbabilityMeasure.measure_univ] :
      (berP (n := n) p) Set.univ = (1 : ℝ≥0∞)))

/-- Slab masses are finite. -/
lemma slab_ne_top {n : ℕ} (p : unitInterval) (v : Fin n → ℝ) (l t : ℝ) :
    berP (n := n) p (slabEvent v l t) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) (measure_slab_le_one p v l t)

/-- The threshold sublevel sets `{x | threshold p x L ≤ S}` are sequentially
closed (hence closed and measurable) for `1 ≤ L` and `S > 0`. -/
lemma isSeqClosed_threshold_sublevel {n : ℕ} (p : unitInterval) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 < S) :
    IsSeqClosed {x : Fin n → ℝ | Submission.Threshold.threshold p x L ≤ S} := by
  intro xseq x0 hmem hconv
  apply threshold_le_of_cf_above p hS
  intro t htS
  have ht0 : 0 < t := lt_trans hS htS
  -- cfP p x0 t ≤ ofReal(L·t): bound every member of the sup
  unfold cfP
  unfold Submission.Helpers.levyConcentration
  rw [sSup_le_iff]
  rintro a ⟨l, rfl⟩
  change (berP (n := n) p (slabEvent x0 l t)) ≤ ENNReal.ofReal (L * t)
  -- squeeze from the approximating sequence
  have hsqueeze' : ∀ m : ℕ,
      (berP (n := n) p (slabEvent x0 l t)).toReal ≤ L * (t + ∑ i : Fin n, |x0 i - xseq m i|) := by
    intro m
    refine real_slab_le_of_close_threshold p (x := x0) (xm := xseq m) (l := l) (t := t) ht0 hL ?_
    have hthrS : Submission.Threshold.threshold p (xseq m) L ≤ S := hmem m
    have hδ0 : 0 ≤ ∑ i : Fin n, |x0 i - xseq m i| := Finset.sum_nonneg (fun i hi => abs_nonneg _)
    have hlt : S < t + ∑ i : Fin n, |x0 i - xseq m i| := by linarith
    exact lt_of_le_of_lt hthrS hlt
  have hdelta : Tendsto (fun m : ℕ => ∑ i : Fin n, |x0 i - xseq m i|) atTop (𝓝 0) :=
    tendsto_sum_abs_sub hconv
  have hlim : Tendsto (fun m : ℕ => L * (t + ∑ i : Fin n, |x0 i - xseq m i|)) atTop (𝓝 (L * t)) := by
    have hadd : Tendsto (fun m : ℕ => t + ∑ i : Fin n, |x0 i - xseq m i|) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add hdelta
    have hz : t + 0 = t := by ring
    rw [hz] at hadd
    simpa using (Filter.Tendsto.const_mul L hadd)
  have hsqueeze : (berP (n := n) p (slabEvent x0 l t)).toReal ≤ L * t := by
    refine ge_of_tendsto hlim ?_
    exact Filter.Eventually.of_forall hsqueeze'
  have hnonneg : 0 ≤ L * t := by
    have hL0 : 0 ≤ L := by linarith
    exact mul_nonneg hL0 (by linarith)
  have htoReal : (berP (n := n) p (slabEvent x0 l t)).toReal ≤
      (ENNReal.ofReal (L * t)).toReal := by
    simpa [ENNReal.toReal_ofReal hnonneg] using hsqueeze
  exact (ENNReal.toReal_le_toReal (slab_ne_top p x0 l t) ENNReal.ofReal_ne_top).1 htoReal

/-- Threshold sublevel sets are closed in `(Fin n → ℝ)`. -/
lemma isClosed_threshold_sublevel {n : ℕ} (p : unitInterval) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 < S) :
    IsClosed {x : Fin n → ℝ | Submission.Threshold.threshold p x L ≤ S} := by
  exact ((isSeqClosed_iff_isClosed (X := Fin n → ℝ)
    (M := {x : Fin n → ℝ | Submission.Threshold.threshold p x L ≤ S})).mp
    (isSeqClosed_threshold_sublevel p hL hS))

/-- Threshold sublevel sets are measurable.  This is the fact that makes the
`H := {threshold ≤ S}` conditioning sets of the fibre estimates measurable. -/
theorem measurableSet_threshold_sublevel {n : ℕ} (p : unitInterval) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 < S) :
    MeasurableSet {x : Fin n → ℝ | Submission.Threshold.threshold p x L ≤ S} := by
  exact (isClosed_threshold_sublevel p hL hS).measurableSet

/-- Threshold annuli `{a < threshold p x L ≤ b}` are measurable (used for the
dyadic annulus decomposition of the random normal). -/
theorem measurableSet_threshold_annulus {n : ℕ} (p : unitInterval) {L : ℝ} (hL : 1 ≤ L)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MeasurableSet {x : Fin n → ℝ | a < Submission.Threshold.threshold p x L ∧
      Submission.Threshold.threshold p x L ≤ b} := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsub_b : MeasurableSet {x : Fin n → ℝ | Submission.Threshold.threshold p x L ≤ b} :=
    measurableSet_threshold_sublevel p hL hb
  have hsub_a : MeasurableSet {x : Fin n → ℝ | Submission.Threshold.threshold p x L ≤ a} :=
    measurableSet_threshold_sublevel p hL ha
  convert hsub_b.diff hsub_a using 1
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, fun hle => not_lt_of_ge hle hx.1⟩
  · intro hx
    exact ⟨lt_of_not_ge hx.2, hx.1⟩



/-- on the support, `ω` equals the indicator of its 1-set. -/
lemma indVec_support_eq {n : ℕ} {ω : Fin n → ℝ} (hω : ω ∈ supportSet) :
    ω = indVec ((Finset.univ : Finset (Fin n)).filter (fun i => ω i = 1)) := by
  funext i
  dsimp [indVec]
  rcases hω i with h0 | h1
  · have hnot : ¬ ω i = 1 := by linarith
    simp [hnot, h0]
  · simp [h1]

/-- the weighted sum on the support equals the sum over the 1-set. -/
lemma sum_weight_eq_indVec {n : ℕ} {ω : Fin n → ℝ} (hω : ω ∈ supportSet)
    (v : Fin n → ℝ) :
    (∑ i : Fin n, ω i * v i) =
      (∑ i ∈ ((Finset.univ : Finset (Fin n)).filter (fun i => ω i = 1)), v i) := by
  calc
    (∑ i : Fin n, ω i * v i)
        = ∑ i : Fin n, (if ω i = 1 then v i else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h1 : ω i = 1
          · rw [h1]
            simp
          · have h0 : ω i = 0 := by
              rcases hω i with h0 | h1'
              · exact h0
              · exact False.elim (h1 h1')
            rw [h0]
            simp
    _ = (∑ i ∈ ((Finset.univ : Finset (Fin n)).filter (fun i => ω i = 1)), v i) := by
          rw [← Finset.sum_filter]

end Submission.ThresholdMeas
