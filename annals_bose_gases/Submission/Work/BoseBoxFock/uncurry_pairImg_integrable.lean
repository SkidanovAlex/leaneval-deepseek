import Mathlib.Analysis.Convolution
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imagesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uncurry_pairImg_integrable`

Joint integrability of the two `χ`-cut-off pair kernels of the `Q M Q` dictionary
(`Work.BoseBoxFock.qmqDefs`):

* the `m = 0` part `(a,b) ↦ χ_ℓ(a)·W(a−b)·χ_ℓ(b)` of the periodised kernel, and
* the lattice-images part `(a,b) ↦ imgKernel ℓ W a b = χ_ℓ(a)·(Σ'_{m≠0}W(a−b+ℓm))·χ_ℓ(b)`,

for an integrable one-body kernel `W` supported in `‖u‖ < R`.  No relation between `R` and `ℓ` is
assumed: the images kernel is dominated by the *finite* lattice sum over the lattice vectors with
`‖ℓm‖ ≤ ℓ + R`, a box which may contain arbitrarily many lattice points.

## The proof

Write `B := closedBall 0 (ℓ/2)`, `F := 1_B`, and `C := chiSup = (∫χ²)^{-1/2}`, so that
`0 ≤ χ_ℓ ≤ C·F` pointwise (the bump vanishes outside `B`).

* *Conjunct 1.*  `‖χ_ℓ(a)W(a−b)χ_ℓ(b)‖ ≤ C²·(F a·|W(a−b)|·F b)`, and the majorant is integrable:
this is the elementary convolution bound for `1_B` in one variable against `|W|` in the other
(`MeasureTheory.Integrable.convolution_integrand` with `L = mul`), the extra factor `F a` being
bounded by `1` (`Integrable.bdd_mul`).
* *Conjunct 2.*  `|imgKernel| ≤ C²·Σ_{m∈M}|W(a−b+ℓm)|` for any finset `M` containing the lattice
vectors with `‖ℓm‖ ≤ ℓ + R`: on `χ_ℓ(a)χ_ℓ(b) ≠ 0` one has `‖a−b‖ < ℓ`, so every term outside `M`
vanishes by the support hypothesis and `tsum_eq_sum` collapses the series; each summand is then
integrable by the same convolution bound applied to the translate `z ↦ W(z + ℓm)`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the scaled bump -/

/-- Nonvanishing of `χ_ℓ` forces its argument into the ball of radius `ℓ/2`. -/
private lemma chiScale_ne_zero_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : Submission.BoseGases.chiScale ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  by_contra hcon
  push Not at hcon
  apply hx
  rw [Submission.BoseGases.chiScale]
  apply Submission.BoseGases.chi_eq_zero_of_half_le_norm
  have h3 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by
    rw [show ℓ⁻¹ * (ℓ / 2) = (ℓ * ℓ⁻¹) / 2 by ring, mul_inv_cancel₀ (ne_of_gt hℓ), one_div]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), ← h3]
  exact mul_le_mul_of_nonneg_left hcon (inv_pos.mpr hℓ).le

/-- The scaled bump is dominated by `chiSup` times the indicator of the closed ball of radius
`ℓ/2`. -/
private lemma chiScale_le_chiSup_indicator {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) :
    Submission.BoseGases.chiScale ℓ x ≤ Submission.BoseGases.chiSup *
      (Metric.closedBall (0 : E3) (ℓ / 2)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Metric.closedBall (0 : E3) (ℓ / 2)
  · rw [Set.indicator_of_mem hx, mul_one]
    exact le_trans (le_abs_self _) (Submission.BoseGases.abs_chiScale_le_chiSup ℓ x)
  · rw [Set.indicator_of_notMem hx, mul_zero]
    have hlt : ℓ / 2 < ‖x‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact lt_of_not_ge hx
    rw [show Submission.BoseGases.chiScale ℓ x = 0 from by
      by_contra hne
      exact absurd (chiScale_ne_zero_norm_lt hℓ hne) (not_lt.mpr hlt.le)]

/-! ## The lattice box, and the pointwise images bound -/

/-- The lattice vectors with `‖ℓ • m‖ ≤ ℓ + R` are contained in an explicit finite box. -/
private lemma exists_finset_latVec_le' {ℓ R : ℝ} (hℓ : 0 < ℓ) :
    ∃ M : Finset (Fin 3 → ℤ), ∀ m : Fin 3 → ℤ, ‖ℓ • latVec m‖ ≤ ℓ + R → m ∈ M := by
  refine ⟨Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(⌈1 + R / ℓ⌉)) (⌈1 + R / ℓ⌉)),
    fun m hm => ?_⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hnorm : ‖latVec m‖ ≤ 1 + R / ℓ := by
    have h1 : ℓ * ‖latVec m‖ ≤ ℓ + R := by
      have h2 := hm
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at h2
    have h3 : 1 + R / ℓ = (ℓ + R) / ℓ := by field_simp
    rw [h3, le_div_iff₀ hℓ]
    linarith
  have hcoord : |((m i : ℤ) : ℝ)| ≤ 1 + R / ℓ := by
    have h := PiLp.norm_apply_le (latVec m) i
    rw [latVec_apply, Real.norm_eq_abs] at h
    exact le_trans h hnorm
  constructor
  · have h1 : -((⌈1 + R / ℓ⌉ : ℤ) : ℝ) ≤ ((m i : ℤ) : ℝ) := by
      have h2 := (abs_le.mp hcoord).1
      have h3 : ((⌈1 + R / ℓ⌉ : ℤ) : ℝ) ≥ 1 + R / ℓ := Int.le_ceil _
      linarith
    exact_mod_cast h1
  · have h1 : ((m i : ℤ) : ℝ) ≤ ((⌈1 + R / ℓ⌉ : ℤ) : ℝ) := by
      have h2 := (abs_le.mp hcoord).2
      have h3 : ((⌈1 + R / ℓ⌉ : ℤ) : ℝ) ≥ 1 + R / ℓ := Int.le_ceil _
      linarith
    exact_mod_cast h1

/-- **Pointwise finite-lattice bound for the images kernel.**  For any finset `M` containing all
lattice vectors with `‖ℓ • m‖ ≤ ℓ + R`, the images kernel is bounded by `chiSup²` times the finite
lattice sum over `M`. -/
private lemma imgKernel_abs_le_finset_sum' {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : ∀ u : E3, R ≤ ‖u‖ → W u = 0)
    {M : Finset (Fin 3 → ℤ)}
    (hM : ∀ m : Fin 3 → ℤ, ‖ℓ • latVec m‖ ≤ ℓ + R → m ∈ M) (a b : E3) :
    |imgKernel ℓ W a b| ≤ Submission.BoseGases.chiSup ^ 2 *
      ∑ m ∈ M, |W (a - b + ℓ • latVec m)| := by
  have hc0 : 0 ≤ Submission.BoseGases.chiSup := Submission.BoseGases.chiSup_pos.le
  by_cases hne : Submission.BoseGases.chiScale ℓ a = 0 ∨ Submission.BoseGases.chiScale ℓ b = 0
  · have hz : imgKernel ℓ W a b = 0 := by
      rw [imgKernel]
      rcases hne with h | h <;> simp [h]
    rw [hz, abs_zero]
    exact mul_nonneg (pow_nonneg hc0 2) (Finset.sum_nonneg (fun m _ => abs_nonneg _))
  · push Not at hne
    have ha : ‖a‖ < ℓ / 2 := chiScale_ne_zero_norm_lt hℓ hne.1
    have hb : ‖b‖ < ℓ / 2 := chiScale_ne_zero_norm_lt hℓ hne.2
    have hab : ‖a - b‖ < ℓ := by
      calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
        _ < ℓ / 2 + ℓ / 2 := by linarith
        _ = ℓ := by ring
    have hvan : ∀ m : Fin 3 → ℤ, m ∉ M →
        (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m)) = 0 := by
      intro m hm
      by_cases hm0 : m = 0
      · simp [hm0]
      · simp only [hm0, if_false]
        apply hWs
        by_contra hcon
        push Not at hcon
        have hMm : ‖ℓ • latVec m‖ ≤ ℓ + R := by
          have h1 : ‖ℓ • latVec m‖ ≤ ‖a - b + ℓ • latVec m‖ + ‖a - b‖ := by
            have h2 := norm_sub_le (a - b + ℓ • latVec m) (a - b)
            have heq : (a - b + ℓ • latVec m) - (a - b) = ℓ • latVec m := by abel
            rwa [heq] at h2
          linarith
        exact hm (hM m hMm)
    have htsum : (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m)))
        = ∑ m ∈ M, (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m)) := by
      rw [tsum_eq_sum hvan]
    have hImg : |imgKernel ℓ W a b| = Submission.BoseGases.chiScale ℓ a *
        |∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m))| *
        Submission.BoseGases.chiScale ℓ b := by
      rw [imgKernel, abs_mul, abs_mul,
        abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ a),
        abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ b)]
    have hχa : Submission.BoseGases.chiScale ℓ a ≤ Submission.BoseGases.chiSup :=
      le_trans (le_abs_self _) (Submission.BoseGases.abs_chiScale_le_chiSup ℓ a)
    have hχb : Submission.BoseGases.chiScale ℓ b ≤ Submission.BoseGases.chiSup :=
      le_trans (le_abs_self _) (Submission.BoseGases.abs_chiScale_le_chiSup ℓ b)
    have hterm : ∀ m ∈ M, |if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m)|
        ≤ |W (a - b + ℓ • latVec m)| := by
      intro m _
      by_cases hm0 : m = 0
      · simp [hm0]
      · simp [hm0]
    have hsum_abs : |∑ m ∈ M, (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m))|
        ≤ ∑ m ∈ M, |W (a - b + ℓ • latVec m)| :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
    have hsum_nn : 0 ≤ ∑ m ∈ M, |W (a - b + ℓ • latVec m)| :=
      Finset.sum_nonneg (fun m _ => abs_nonneg _)
    have hleft : Submission.BoseGases.chiScale ℓ a
          * |∑ m ∈ M, (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m))|
        ≤ Submission.BoseGases.chiSup * (∑ m ∈ M, |W (a - b + ℓ • latVec m)|) := by
      calc Submission.BoseGases.chiScale ℓ a
            * |∑ m ∈ M, (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m))|
          ≤ Submission.BoseGases.chiSup
            * |∑ m ∈ M, (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m))| :=
            mul_le_mul_of_nonneg_right hχa (abs_nonneg _)
        _ ≤ Submission.BoseGases.chiSup * (∑ m ∈ M, |W (a - b + ℓ • latVec m)|) :=
            mul_le_mul_of_nonneg_left hsum_abs hc0
    rw [hImg, htsum]
    calc Submission.BoseGases.chiScale ℓ a
          * |∑ m ∈ M, (if m = 0 then (0 : ℝ) else W (a - b + ℓ • latVec m))|
          * Submission.BoseGases.chiScale ℓ b
        ≤ (Submission.BoseGases.chiSup * (∑ m ∈ M, |W (a - b + ℓ • latVec m)|))
          * Submission.BoseGases.chiSup :=
          mul_le_mul hleft hχb (Submission.BoseGases.chiScale_nonneg ℓ b)
            (mul_nonneg hc0 hsum_nn)
      _ = Submission.BoseGases.chiSup ^ 2 * ∑ m ∈ M, |W (a - b + ℓ • latVec m)| := by ring

/-! ## The convolution-type `L¹` bound -/

/-- **The elementary `χ·W·χ` `L¹` bound**: for a measurable set `B` of finite measure and an
integrable `f`, the two-variable function `(a,b) ↦ 1_B(a)·|f(a−b)|·1_B(b)` is integrable.
(The proof is the convolution bound `Integrable.convolution_integrand` for `L = mul` in the second
variable, times the bounded factor `1_B` in the first.) -/
private lemma integrable_indicator_abs_sub_indicator' {B : Set E3} (hB : MeasurableSet B)
    (hBfin : (volume : Measure E3) B < ⊤) {f : E3 → ℝ} (hf : Integrable f) :
    Integrable (fun p : E3 × E3 =>
      (B.indicator (fun _ => (1 : ℝ))) p.1 * |f (p.1 - p.2)|
        * (B.indicator (fun _ => (1 : ℝ))) p.2)
      ((volume : Measure E3).prod (volume : Measure E3)) := by
  have hFint : Integrable (fun x : E3 => B.indicator (fun _ => (1 : ℝ)) x)
      (volume : Measure E3) := by
    rw [integrable_indicator_iff hB, integrableOn_const_iff]
    exact Or.inr hBfin
  have hFm : Measurable (fun x : E3 => B.indicator (fun _ => (1 : ℝ)) x) :=
    (measurable_const : Measurable (fun _ : E3 => (1 : ℝ))).indicator hB
  have hg : Integrable (fun z : E3 => |f z|) (volume : Measure E3) := by
    simpa only [Real.norm_eq_abs] using hf.abs
  have hbase : Integrable (fun p : E3 × E3 =>
      (B.indicator (fun _ => (1 : ℝ))) p.2 * |f (p.1 - p.2)|)
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    have h := Integrable.convolution_integrand (μ := (volume : Measure E3))
      (ν := (volume : Measure E3)) (L := ContinuousLinearMap.mul ℝ ℝ)
      (f := fun x : E3 => B.indicator (fun _ => (1 : ℝ)) x) (g := fun z : E3 => |f z|)
      hFint hg
    simpa using h
  have hstep : Integrable (fun p : E3 × E3 =>
      (B.indicator (fun _ => (1 : ℝ))) p.1 *
        ((B.indicator (fun _ => (1 : ℝ))) p.2 * |f (p.1 - p.2)|))
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    refine hbase.bdd_mul (f := fun p : E3 × E3 => (B.indicator (fun _ => (1 : ℝ))) p.1)
      (c := 1) ?_ ?_
    · exact (hFm.comp measurable_fst).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) p.1)]
      by_cases hp : p.1 ∈ B
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]
        norm_num
  refine hstep.congr (Filter.Eventually.of_forall fun p => ?_)
  ring

/-! ## The target -/

theorem uncurry_pairImg_integrable {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWi : MeasureTheory.Integrable W) (hWs : ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ → W u = 0) :
    MeasureTheory.Integrable
        (Function.uncurry (fun a b : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ a * W (a - b) * Submission.BoseGases.chiScale ℓ b))
        (MeasureTheory.volume.prod MeasureTheory.volume)
      ∧ MeasureTheory.Integrable
        (Function.uncurry (fun a b : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseBoxFock.imgKernel ℓ W a b))
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  set B : Set E3 := Metric.closedBall (0 : E3) (ℓ / 2) with hBdef
  set F : E3 → ℝ := B.indicator (fun _ => (1 : ℝ)) with hFdef
  have hB : MeasurableSet B := by
    rw [hBdef]
    exact Metric.isClosed_closedBall.measurableSet
  have hBfin : (volume : Measure E3) B < ⊤ := by
    rw [hBdef]
    exact (isCompact_closedBall (0 : E3) (ℓ / 2)).measure_lt_top
  have hFm : Measurable F := by
    rw [hFdef]
    exact (measurable_const : Measurable (fun _ : E3 => (1 : ℝ))).indicator hB
  have hFint : Integrable F (volume : Measure E3) := by
    rw [hFdef, integrable_indicator_iff hB, integrableOn_const_iff]
    exact Or.inr hBfin
  have hFnn : ∀ x : E3, 0 ≤ F x := by
    intro x
    rw [hFdef]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hFle : ∀ x : E3, F x ≤ 1 := by
    intro x
    rw [hFdef]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      norm_num
  have hqmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      ((volume : Measure E3).prod (volume : Measure E3)) (volume : Measure E3) :=
    quasiMeasurePreserving_sub_of_right_invariant _ _
  have hchi1AESM : AEStronglyMeasurable (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.1)
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_fst).aestronglyMeasurable
  have hchi2AESM : AEStronglyMeasurable (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.2)
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd).aestronglyMeasurable
  have hWAESM : AEStronglyMeasurable (fun p : E3 × E3 => W (p.1 - p.2))
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    hWi.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  constructor
  · -- the `m = 0` part
    have hmaj : Integrable (fun p : E3 × E3 =>
        Submission.BoseGases.chiSup ^ 2 * (F p.1 * |W (p.1 - p.2)| * F p.2))
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      (integrable_indicator_abs_sub_indicator' hB hBfin hWi).const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · show AEStronglyMeasurable (fun p : E3 × E3 =>
          Submission.BoseGases.chiScale ℓ p.1 * W (p.1 - p.2) * Submission.BoseGases.chiScale ℓ p.2)
          ((volume : Measure E3).prod (volume : Measure E3))
      exact (hchi1AESM.mul hWAESM).mul hchi2AESM
    · filter_upwards with p
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ p.1),
        abs_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ p.2)]
      have h1 := chiScale_le_chiSup_indicator hℓ p.1
      have h2 := chiScale_le_chiSup_indicator hℓ p.2
      have hWnn : 0 ≤ |W (p.1 - p.2)| := abs_nonneg _
      have hA : Submission.BoseGases.chiScale ℓ p.1 * |W (p.1 - p.2)|
          ≤ (Submission.BoseGases.chiSup * F p.1) * |W (p.1 - p.2)| :=
        mul_le_mul_of_nonneg_right h1 hWnn
      have hB2 : (Submission.BoseGases.chiScale ℓ p.1 * |W (p.1 - p.2)|)
            * Submission.BoseGases.chiScale ℓ p.2
          ≤ ((Submission.BoseGases.chiSup * F p.1) * |W (p.1 - p.2)|)
            * (Submission.BoseGases.chiSup * F p.2) :=
        mul_le_mul hA h2 (Submission.BoseGases.chiScale_nonneg ℓ p.2)
          (mul_nonneg (mul_nonneg (le_of_lt Submission.BoseGases.chiSup_pos) (hFnn p.1)) hWnn)
      calc Submission.BoseGases.chiScale ℓ p.1 * |W (p.1 - p.2)|
            * Submission.BoseGases.chiScale ℓ p.2
          ≤ ((Submission.BoseGases.chiSup * F p.1) * |W (p.1 - p.2)|)
            * (Submission.BoseGases.chiSup * F p.2) := hB2
        _ = Submission.BoseGases.chiSup ^ 2 * (F p.1 * |W (p.1 - p.2)| * F p.2) := by ring
  · -- the lattice-images part
    obtain ⟨M, hM⟩ := exists_finset_latVec_le' (R := R) hℓ
    have hTermInt : ∀ m : Fin 3 → ℤ, Integrable (fun p : E3 × E3 =>
        F p.1 * |W (p.1 - p.2 + ℓ • latVec m)| * F p.2)
        ((volume : Measure E3).prod (volume : Measure E3)) := by
      intro m
      have hgm : Integrable (fun z : E3 => |W (z + ℓ • latVec m)|) (volume : Measure E3) := by
        simpa only [Real.norm_eq_abs] using (hWi.comp_add_right (ℓ • latVec m)).abs
      have hbase : Integrable (fun p : E3 × E3 =>
          F p.2 * |W ((p.1 - p.2) + ℓ • latVec m)|)
          ((volume : Measure E3).prod (volume : Measure E3)) := by
        have h := Integrable.convolution_integrand (μ := (volume : Measure E3))
          (ν := (volume : Measure E3)) (L := ContinuousLinearMap.mul ℝ ℝ)
          (f := F) (g := fun z : E3 => |W (z + ℓ • latVec m)|) hFint hgm
        simpa using h
      have hstep : Integrable (fun p : E3 × E3 =>
          F p.1 * (F p.2 * |W (p.1 - p.2 + ℓ • latVec m)|))
          ((volume : Measure E3).prod (volume : Measure E3)) := by
        refine hbase.bdd_mul (f := fun p : E3 × E3 => F p.1) (c := 1)
          (hFm.comp measurable_fst).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall fun p => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnn p.1)]
        exact hFle p.1
      refine hstep.congr (Filter.Eventually.of_forall fun p => ?_)
      ring
    have hmaj : Integrable (fun p : E3 × E3 => Submission.BoseGases.chiSup ^ 2 *
        ∑ m ∈ M, (F p.1 * |W (p.1 - p.2 + ℓ • latVec m)| * F p.2))
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      (integrable_finsetSum M (fun m _ => hTermInt m)).const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · have htsum : AEMeasurable (fun p : E3 × E3 =>
          ∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else W (p.1 - p.2 + ℓ • latVec m)))
          ((volume : Measure E3).prod (volume : Measure E3)) := by
        apply AEMeasurable.tsum
        intro m
        by_cases hm : m = 0
        · simp only [hm, ↓reduceIte]
          exact aemeasurable_const
        · simp only [hm, ↓reduceIte]
          have hWm : AEStronglyMeasurable (fun z : E3 => W (z + ℓ • latVec m))
              (volume : Measure E3) :=
            hWi.aestronglyMeasurable.comp_quasiMeasurePreserving
              (measurePreserving_add_right (volume : Measure E3) (ℓ • latVec m)).quasiMeasurePreserving
          exact (hWm.comp_quasiMeasurePreserving hqmp).aemeasurable
      show AEStronglyMeasurable (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.1 *
          (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℝ) else W (p.1 - p.2 + ℓ • latVec m))) *
          Submission.BoseGases.chiScale ℓ p.2)
          ((volume : Measure E3).prod (volume : Measure E3))
      exact (hchi1AESM.mul htsum.aestronglyMeasurable).mul hchi2AESM
    · filter_upwards with p
      have h1 := imgKernel_abs_le_finset_sum' hℓ hWs hM p.1 p.2
      by_cases hne : Submission.BoseGases.chiScale ℓ p.1 = 0
          ∨ Submission.BoseGases.chiScale ℓ p.2 = 0
      · have hz : imgKernel ℓ W p.1 p.2 = 0 := by
          rw [imgKernel]
          rcases hne with h | h <;> simp [h]
        have hR : 0 ≤ Submission.BoseGases.chiSup ^ 2 *
            ∑ m ∈ M, (F p.1 * |W (p.1 - p.2 + ℓ • latVec m)| * F p.2) :=
          mul_nonneg (pow_nonneg (le_of_lt Submission.BoseGases.chiSup_pos) 2)
            (Finset.sum_nonneg (fun m _ =>
              mul_nonneg (mul_nonneg (hFnn p.1) (abs_nonneg _)) (hFnn p.2)))
        simp only [Function.uncurry]
        rw [hz, norm_zero]
        exact hR
      · push Not at hne
        have hp1 : p.1 ∈ B := by
          rw [hBdef, Metric.mem_closedBall, dist_zero_right]
          exact (chiScale_ne_zero_norm_lt hℓ hne.1).le
        have hp2 : p.2 ∈ B := by
          rw [hBdef, Metric.mem_closedBall, dist_zero_right]
          exact (chiScale_ne_zero_norm_lt hℓ hne.2).le
        have hF1 : F p.1 = 1 := by rw [hFdef]; exact Set.indicator_of_mem hp1 _
        have hF2 : F p.2 = 1 := by rw [hFdef]; exact Set.indicator_of_mem hp2 _
        simp only [Function.uncurry]
        rw [hF1, hF2]
        refine le_trans h1 (le_of_eq ?_)
        simp only [one_mul, mul_one]

end Work.BoseBoxFock
