import Mathlib
import Submission.AntiderivConv
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization_box
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization_orthant
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization_orthant_thin
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization_orthant_thin_marg
import Submission.Commons.Analysis.TensorApprox.exists_tensor_localization_orthant_thin_marg_explicit
import Submission.Rescale
import Submission.Commons.Analysis.Calculus.exists_contDiff_step
import Submission.Commons.Analysis.Calculus.contDiff_integral_Ioi
import Submission.Commons.Analysis.Integral.abs_integral_sq_sub_sq_le
import Submission.Commons.MeasureTheory.Integral.marginal_set_error_le

/-!
# Convergence of the tensor-data coefficients to the variational functionals

Given a continuous compactly supported `F` on `Fin k → ℝ` supported in the orthant and in
`{∑ i, t i ≤ R}`, the localisation theorem produces a tensor sum `t ↦ ∑ j, c j ∏ i, Gt j i (t i)`
uniformly close to `F`, whose one-variable components are smooth and compactly supported.  The
antiderivative family `f j i = anti ψ (Gt j) i` then has

  `tpAlpha c f = ∫_{[0,∞)^k} (∑ j, c j ∏ i, Gt j i (t i))²`,

and hence `tpAlpha c f → IFuncOrth k F` as the localisation error tends to `0`.
-/

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

set_option maxHeartbeats 2000000

/-- The strict orthant of `Fin k → ℝ`. -/
def orthantSet (k : ℕ) : Set (Fin k → ℝ) := Set.univ.pi fun _ : Fin k => Set.Ici (0:ℝ)

lemma measurableSet_orthantSet (k : ℕ) : MeasurableSet (orthantSet k) :=
  MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_Ici

lemma mem_orthantSet {k : ℕ} {t : Fin k → ℝ} : t ∈ orthantSet k ↔ ∀ i, 0 ≤ t i := by
  simp [orthantSet, Pi.le_def]

lemma orthInd_eq_indicator (k : ℕ) (t : Fin k → ℝ) :
    orthInd t = (orthantSet k).indicator (fun _ => (1:ℝ)) t := by
  rw [orthInd]
  by_cases h : t ∈ orthantSet k
  · rw [Set.indicator_of_mem h]
    refine Finset.prod_eq_one fun i _ => ?_
    exact Set.indicator_of_mem (Set.mem_Ici.mpr ((mem_orthantSet.mp h) i)) _
  · have hi : ∃ i, t i ∉ Set.Ici (0:ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact h (mem_orthantSet.mpr hcon)
    obtain ⟨i, hi⟩ := hi
    rw [Set.indicator_of_notMem h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- The box `∏ i [0, B]`. -/
def halfBox (k : ℕ) (B : ℝ) : Set (Fin k → ℝ) := Set.univ.pi fun _ : Fin k => Set.Icc (0:ℝ) B

lemma measurableSet_halfBox (k : ℕ) (B : ℝ) : MeasurableSet (halfBox k B) :=
  MeasurableSet.pi Set.countable_univ fun i _ => measurableSet_Icc

/-- A function vanishing outside the box `{∑ i, t i ≤ B}` on the orthant integrates the same
against the orthant indicator as over the box. -/
lemma setIntegral_orthant_eq_halfBox {k : ℕ} {h : (Fin k → ℝ) → ℝ} {B : ℝ}
    (hvan : ∀ t, (∀ i, 0 ≤ t i) → (∃ i, B < t i) → h t = 0) :
    (∫ t in orthantSet k, h t) = ∫ t in halfBox k B, h t := by
  rw [← MeasureTheory.integral_indicator (measurableSet_orthantSet k),
    ← MeasureTheory.integral_indicator (measurableSet_halfBox k B)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ halfBox k B
  · have hto : t ∈ orthantSet k := by
      rw [mem_orthantSet]
      intro i
      exact (Set.mem_Icc.mp (Set.mem_univ_pi.mp ht i)).1
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem hto]
  · rw [Set.indicator_of_notMem ht]
    by_cases hto : t ∈ orthantSet k
    · rw [Set.indicator_of_mem hto]
      refine hvan t (mem_orthantSet.mp hto) ?_
      by_contra hcon
      push_neg at hcon
      exact ht (Set.mem_univ_pi.mpr fun i =>
        Set.mem_Icc.mpr ⟨(mem_orthantSet.mp hto) i, hcon i⟩)
    · rw [Set.indicator_of_notMem hto]

/-- **Convergence of the `α`-coefficient.**  Every continuous compactly supported `F`
supported in the orthant and in `{∑ i, t i ≤ R}` admits tensor data `(c, Gt, β)` with
`∑ i, β j i ≤ R + 6 k η`, whose antiderivative coefficients approximate `IFuncOrth k F`
arbitrarily well. -/
theorem exists_tensorAlpha_near {k : ℕ} {F : (Fin k → ℝ) → ℝ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1) (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ (J : ℕ) (β : Fin J → Fin k → ℝ) (Gt : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ),
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (Gt j i)) ∧
      (∀ j i, HasCompactSupport (Gt j i)) ∧
      (∀ j i u, β j i < u → Gt j i u = 0) ∧
      (∀ j, ∑ i, β j i ≤ R + 6 * (k : ℝ) * η) ∧
      |tpAlpha c (fun j i => anti ψ (Gt j) i) - IFuncOrth k F| < δ := by
  classical
  have hbnd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Fin k → ℝ, |F t| ≤ C := by
    obtain ⟨C, hC⟩ := hFcs.isCompact.exists_bound_of_continuousOn hFc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
    by_cases ht : t ∈ tsupport F
    · exact le_trans ((Real.norm_eq_abs (F t)).symm ▸ hC t ht) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp
  obtain ⟨CF, hCF0, hCF⟩ := hbnd
  set Bg : ℝ := R + 6 * (k : ℝ) * η with hBg
  have h6 : (0:ℝ) ≤ 6 * (k : ℝ) * η := by positivity
  have hBg0 : 0 ≤ Bg := by rw [hBg]; linarith
  have hRB : R ≤ Bg := by rw [hBg]; linarith
  set Vb : ℝ := Bg ^ k with hVb
  have hVb0 : 0 ≤ Vb := by rw [hVb]; positivity
  set A : ℝ := 2 * (CF * Vb) + Vb + 1 with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [mul_nonneg hCF0 hVb0, hVb0]
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  set el : ℝ := min 1 (δ / (8 * A)) with hel
  have hel0 : 0 < el := by
    rw [hel]; exact lt_min one_pos (div_pos hδ (by positivity))
  have hel1 : el ≤ 1 := by rw [hel]; exact min_le_left _ _
  have helA : el * A ≤ δ / 8 := by
    have h : el ≤ δ / (8 * A) := by rw [hel]; exact min_le_right _ _
    calc el * A ≤ (δ / (8 * A)) * A := mul_le_mul_of_nonneg_right h hA0.le
      _ = δ / 8 := by field_simp
  obtain ⟨ι, hι, c, β, Gt, hGtsm, hGtcs, hGtvan, hβsum, happrox⟩ :=
    Commons.Analysis.TensorApprox.exists_tensor_localization hFc hFcs
      (fun t ht => (hR t ht).2) hη hel0
  have happrox' : ∀ t, |(∑ j : ι, c j * ∏ i, Gt j i (t i)) - F t| < el := by
    intro t
    rw [abs_sub_comm]
    exact happrox t
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j i => β (e.symm j) i, fun j i => Gt (e.symm j) i,
    fun j => c (e.symm j), fun j i => hGtsm (e.symm j) i, fun j i => hGtcs (e.symm j) i,
    fun j i u hu => hGtvan (e.symm j) i u hu, fun j => hβsum (e.symm j), ?_⟩
  have hGc : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), Continuous (Gt (e.symm j) i) :=
    fun j i => (hGtsm (e.symm j) i).continuous
  have hGcs' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), HasCompactSupport (Gt (e.symm j) i) :=
    fun j i => hGtcs (e.symm j) i
  have hGi' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), Integrable (Gt (e.symm j) i) :=
    fun j i => (hGc j i).integrable_of_hasCompactSupport (hGcs' j i)
  have hGv' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k),
      ∃ R : ℝ, ∀ x : ℝ, R ≤ x → Gt (e.symm j) i x = 0 :=
    fun j i => ⟨β (e.symm j) i + 1,
      fun x hx => hGtvan (e.symm j) i x (lt_of_lt_of_le (lt_add_one _) hx)⟩
  rw [tpAlpha_anti hψ1 (G := fun j i => Gt (e.symm j) i) hGc hGcs' hGi' hGv'
    (c := fun j => c (e.symm j))]
  have hkey : ∀ t : Fin k → ℝ,
      (∑ j : Fin (Fintype.card ι), c (e.symm j) * ∏ i, Gt (e.symm j) i (t i))
        = ∑ j : ι, c j * ∏ i, Gt j i (t i) := by
    intro t
    exact (Fintype.sum_equiv e (fun j : ι => c j * ∏ i, Gt j i (t i))
      (fun j : Fin (Fintype.card ι) => c (e.symm j) * ∏ i, Gt (e.symm j) i (t i))
      (fun x => by simp)).symm
  simp only [hkey]
  set Gtf : (Fin k → ℝ) → ℝ := fun t => ∑ j : ι, c j * ∏ i, Gt j i (t i) with hGtf
  have hGtfc : Continuous Gtf := by
    rw [hGtf]
    refine continuous_finsetSum _ fun j _ => Continuous.const_mul ?_ _
    exact continuous_finsetProd _ fun i _ => (hGtsm j i).continuous.comp (continuous_apply i)
  have hvanGtf : ∀ t, (∀ i, 0 ≤ t i) → (∃ i, Bg < t i) → Gtf t = 0 := by
    intro t hpos hex
    rw [hGtf]
    refine Finset.sum_eq_zero fun j _ => ?_
    obtain ⟨i₀, hi₀⟩ := hex
    by_contra hne
    have hprod : (∏ i, Gt j i (t i)) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hle : ∀ i, t i ≤ β j i := by
      intro i
      by_contra hcon
      push_neg at hcon
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) (hGtvan j i (t i) hcon))
    have h1 : t i₀ ≤ ∑ i, t i := Finset.single_le_sum (fun i _ => hpos i) (Finset.mem_univ i₀)
    have h2 : (∑ i, β j i) ≤ Bg := by rw [hBg]; exact hβsum j
    have h3 : (∑ i, t i) ≤ Bg := le_trans (Finset.sum_le_sum fun i _ => hle i) h2
    linarith
  have hvanF : ∀ t, (∀ i, 0 ≤ t i) → (∃ i, Bg < t i) → F t = 0 := by
    intro t hpos hex
    by_contra hne
    obtain ⟨hnn, hle⟩ := hR t hne
    obtain ⟨i₀, hi₀⟩ := hex
    have : t i₀ ≤ ∑ i, t i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i₀)
    linarith
  have hAlph : (∫ t : Fin k → ℝ, Gtf t ^ 2 * orthInd t) = ∫ t in orthantSet k, Gtf t ^ 2 := by
    rw [← MeasureTheory.integral_indicator (measurableSet_orthantSet k)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [orthInd_eq_indicator]
    by_cases ht : t ∈ orthantSet k
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_one]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
  have hboxG : (∫ t in orthantSet k, Gtf t ^ 2) = ∫ t in halfBox k Bg, Gtf t ^ 2 :=
    setIntegral_orthant_eq_halfBox fun t h1 h2 => by rw [hvanGtf t h1 h2]; ring
  have hboxF : (∫ t in orthantSet k, F t ^ 2) = ∫ t in halfBox k Bg, F t ^ 2 :=
    setIntegral_orthant_eq_halfBox fun t h1 h2 => by rw [hvanF t h1 h2]; ring
  have hIF : IFuncOrth k F = ∫ t in halfBox k Bg, F t ^ 2 := by
    rw [IFuncOrth, ← hboxF, ← MeasureTheory.integral_indicator (measurableSet_orthantSet k)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    by_cases ht : t ∈ orthantSet k
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      have hF0 : F t = 0 := by
        by_contra hne
        exact ht (mem_orthantSet.mpr (hR t hne).1)
      rw [hF0]; ring
  have hvolENN : (volume : Measure (Fin k → ℝ)) (halfBox k Bg) = ENNReal.ofReal Vb := by
    rw [halfBox, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
    have h1 : (∏ i : Fin k, (volume : Measure ℝ) (Set.Icc (0:ℝ) Bg))
        = ∏ _i : Fin k, ENNReal.ofReal Bg :=
      Finset.prod_congr rfl fun i _ => by rw [Real.volume_Icc]; congr 1; ring
    rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hVb]
    exact (ENNReal.ofReal_pow hBg0 k).symm
  have hvol : (volume (halfBox k Bg)).toReal = Vb := by
    rw [hvolENN, ENNReal.toReal_ofReal hVb0]
  have hvol_ne : (volume (halfBox k Bg)) ≠ ⊤ := by
    rw [hvolENN]; exact ENNReal.ofReal_ne_top
  have hbound := Commons.Analysis.Integral.abs_integral_sq_sub_sq_le
    (s := halfBox k Bg) (measurableSet_halfBox k Bg)
    hvol_ne (hGtfc.measurable.aestronglyMeasurable)
    hFc.measurable.aestronglyMeasurable (B := CF + el) (ε := el)
    (by linarith)
    (fun x _ => by
      have h1 : |Gtf x| ≤ |F x| + |Gtf x - F x| := by
        calc |Gtf x| = |F x + (Gtf x - F x)| := by ring_nf
          _ ≤ |F x| + |Gtf x - F x| := abs_add_le _ _
      linarith [hCF x, happrox' x])
    (fun x _ => le_trans (hCF x) (le_add_of_nonneg_right hel0.le)) (le_of_lt hel0)
    (fun x _ => le_of_lt (happrox' x))
  calc |(∫ t : Fin k → ℝ, Gtf t ^ 2 * orthInd t) - IFuncOrth k F|
      = |(∫ t in halfBox k Bg, Gtf t ^ 2) - (∫ t in halfBox k Bg, F t ^ 2)| := by
        rw [hAlph, hboxG, hIF]
    _ ≤ 2 * (CF + el) * el * (volume (halfBox k Bg)).toReal := hbound
    _ = 2 * (CF + el) * el * Vb := by rw [hvol]
    _ < δ := by
        have h1 : 2 * (CF + el) * el * Vb = el * (2 * (CF * Vb) + 2 * (el * Vb)) := by ring
        rw [h1]
        have h2 : 2 * (CF * Vb) + 2 * (el * Vb) ≤ 2 * A := by
          rw [hA]
          nlinarith [mul_nonneg hCF0 hVb0, mul_nonneg hel0.le hVb0,
            mul_le_mul_of_nonneg_right hel1 hVb0]
        calc el * (2 * (CF * Vb) + 2 * (el * Vb)) ≤ el * (2 * A) :=
              mul_le_mul_of_nonneg_left h2 hel0.le
          _ = 2 * (el * A) := by ring
          _ ≤ 2 * (δ / 8) := by linarith [helA]
          _ < δ := by linarith

/-- The halfline integral of a real function vanishing beyond `B` equals its integral over
`(0, B]`. -/
lemma setIntegral_Ioi_eq_Ioc {g : ℝ → ℝ} {B : ℝ} (hg : ∀ x : ℝ, B < x → g x = 0) :
    (∫ x in Set.Ioi (0:ℝ), g x) = ∫ x in Set.Ioc (0:ℝ) B, g x := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Set.Ioi (0:ℝ)
  · rw [Set.indicator_of_mem hx]
    by_cases hxB : x ∈ Set.Ioc (0:ℝ) B
    · rw [Set.indicator_of_mem hxB]
    · rw [Set.indicator_of_notMem hxB]
      have hlt : B < x := by
        rw [Set.mem_Ioc, not_and_or] at hxB
        rcases hxB with h | h
        · exact absurd hx h
        · exact lt_of_not_ge h
      exact hg x hlt
  · rw [Set.indicator_of_notMem hx]
    have hx' : x ∉ Set.Ioc (0:ℝ) B :=
      fun h => hx (Set.mem_Ioi.mpr (Set.mem_Ioc.mp h).1)
    rw [Set.indicator_of_notMem hx']

lemma card_subtype_ne {k : ℕ} (i : Fin k) :
    Fintype.card {l : Fin k // l ≠ i} = k - 1 := by
  have h1 : Fintype.card {l : Fin k // ¬ (l ≠ i)}
      = Fintype.card (Fin k) - Fintype.card {l : Fin k // l ≠ i} :=
    Fintype.card_subtype_compl (fun l : Fin k => l ≠ i)
  rw [Fintype.card_fin] at h1
  have h2 : Fintype.card {l : Fin k // ¬ (l ≠ i)} = 1 := by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun l : Fin k => not_ne_iff))]
    exact Fintype.card_subtype_eq i
  omega

/-- The marginal functional `∫_{[0,∞)^{k-1}} (∫_{x > 0} F(·, x))²` of the `θ`-side. -/
noncomputable def margInt {k : ℕ} (i : Fin k) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t : {l : Fin k // l ≠ i} → ℝ,
    (∫ x in Set.Ioi (0:ℝ), F (extendAt i x t)) ^ 2 * orthInd t

/-- The marginal box `∏_{l ≠ i} [0, B]`. -/
def margBox {k : ℕ} (i : Fin k) (B : ℝ) : Set ({l : Fin k // l ≠ i} → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0:ℝ) B

lemma measurableSet_margBox {k : ℕ} (i : Fin k) (B : ℝ) : MeasurableSet (margBox i B) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc

lemma measurable_orthInd {k : ℕ} (i : Fin k) :
    Measurable (fun t : {l : Fin k // l ≠ i} → ℝ => orthInd t) :=
  Finset.measurable_prod _ fun l _ =>
    (measurable_const.indicator measurableSet_Ici).comp (measurable_pi_apply l)

lemma volume_margBox {k : ℕ} (i : Fin k) {B : ℝ} (hB : 0 ≤ B) :
    (volume : Measure ({l : Fin k // l ≠ i} → ℝ)) (margBox i B)
      = ENNReal.ofReal (B ^ (k - 1)) := by
  rw [margBox, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  have h1 : (∏ l : {l : Fin k // l ≠ i}, (volume : Measure ℝ) (Set.Icc (0:ℝ) B))
      = ∏ _l : {l : Fin k // l ≠ i}, ENNReal.ofReal B :=
    Finset.prod_congr rfl fun l _ => by rw [Real.volume_Icc]; congr 1; ring
  rw [h1, Finset.prod_const, Finset.card_univ, card_subtype_ne]
  exact (ENNReal.ofReal_pow hB (k - 1)).symm

lemma continuous_extendAt_pair {k : ℕ} (i₀ : Fin k) :
    Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ => extendAt i₀ p.2 p.1) := by
  refine continuous_pi fun l => ?_
  by_cases hl : l = i₀
  · have h : Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ => p.2) := continuous_snd
    simpa only [extendAt, dif_pos hl] using h
  · have h : Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ => p.1 ⟨l, hl⟩) :=
      (continuous_apply (⟨l, hl⟩ : {l : Fin k // l ≠ i₀})).comp continuous_fst
    simpa only [extendAt, dif_neg hl] using h

/-- **Convergence of the marginal (`β`) coefficient.** -/
lemma margInt_error_le {k : ℕ} {F Gtf : (Fin k → ℝ) → ℝ} {CF R Bg el : ℝ}
    (hCF0 : 0 ≤ CF) (hCF : ∀ s : Fin k → ℝ, |F s| ≤ CF)
    (hBg0 : 0 ≤ Bg) (hRB : R ≤ Bg) (hel : 0 ≤ el)
    (hFcoord : ∀ s : Fin k → ℝ, (∃ i, R < s i) → F s = 0)
    (hGcoord : ∀ s : Fin k → ℝ, (∃ i, Bg < s i) → Gtf s = 0)
    (happrox : ∀ s : Fin k → ℝ, |Gtf s - F s| ≤ el)
    (hGtfc : Continuous Gtf) (hFc : Continuous F) (i₀ : Fin k) :
    |(∫ t : {l : Fin k // l ≠ i₀} → ℝ,
        (∫ x in Set.Ioi (0:ℝ), Gtf (extendAt i₀ x t)) ^ 2 * orthInd t)
      - margInt i₀ F| ≤ el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1) := by
  classical
  have hcontG : Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ =>
      Gtf (extendAt i₀ p.2 p.1)) := hGtfc.comp (continuous_extendAt_pair i₀)
  have hcontF : Continuous (fun p : ({l : Fin k // l ≠ i₀} → ℝ) × ℝ =>
      F (extendAt i₀ p.2 p.1)) := hFc.comp (continuous_extendAt_pair i₀)
  have hIoc : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∫ x in Set.Ioi (0:ℝ), Gtf (extendAt i₀ x t))
        = ∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t) := by
    intro t
    refine setIntegral_Ioi_eq_Ioc fun x hx => ?_
    exact hGcoord _ ⟨i₀, by simpa [extendAt] using hx⟩
  have hIocF : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∫ x in Set.Ioi (0:ℝ), F (extendAt i₀ x t))
        = ∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t) := by
    intro t
    refine setIntegral_Ioi_eq_Ioc fun x hx => ?_
    exact hFcoord _ ⟨i₀, by simpa [extendAt] using lt_of_le_of_lt hRB hx⟩
  have hvolIoc : volume (Set.Ioc (0:ℝ) Bg) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hcI : ∀ c : ℝ, 0 ≤ c → IntegrableOn (fun _ : ℝ => c) (Set.Ioc (0:ℝ) Bg) volume :=
    fun c hc => IntegrableOn.of_bound hvolIoc aestronglyMeasurable_const c
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg hc])
  have hb : ∀ (t : {l : Fin k // l ≠ i₀} → ℝ) (x : ℝ),
      |Gtf (extendAt i₀ x t)| ≤ CF + el := by
    intro t x
    calc |Gtf (extendAt i₀ x t)|
        ≤ |F (extendAt i₀ x t)| + |Gtf (extendAt i₀ x t) - F (extendAt i₀ x t)| := by
          calc |Gtf (extendAt i₀ x t)|
              = |F (extendAt i₀ x t) + (Gtf (extendAt i₀ x t) - F (extendAt i₀ x t))| := by
                ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ CF + el := add_le_add (hCF _) (happrox _)
  have hbdG : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      |∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)| ≤ (CF + el) * Bg := by
    intro t
    have hb' : ∀ x ∈ Set.Ioc (0:ℝ) Bg, |Gtf (extendAt i₀ x t)| ≤ CF + el :=
      fun x _ => hb t x
    calc |∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)|
        ≤ ∫ x in Set.Ioc (0:ℝ) Bg, |Gtf (extendAt i₀ x t)| := abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (0:ℝ) Bg, (CF + el) :=
          setIntegral_mono_of_nonneg (fun x _ => abs_nonneg _) hb'
            (hcI _ (by linarith))
      _ = (CF + el) * Bg := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          show (volume (Set.Ioc (0:ℝ) Bg)).toReal * (CF + el) = (CF + el) * Bg
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ Bg - 0)]
          ring
  have hbdF : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      |∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)| ≤ CF * Bg := by
    intro t
    calc |∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)|
        ≤ ∫ x in Set.Ioc (0:ℝ) Bg, |F (extendAt i₀ x t)| := abs_integral_le_integral_abs
      _ ≤ ∫ x in Set.Ioc (0:ℝ) Bg, CF :=
          setIntegral_mono_of_nonneg (fun x _ => abs_nonneg _) (fun x _ => hCF _)
            (hcI _ hCF0)
      _ = CF * Bg := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          show (volume (Set.Ioc (0:ℝ) Bg)).toReal * CF = CF * Bg
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ Bg - 0)]
          ring
  have hdiff : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      |(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2
        - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2|
        ≤ el * Bg * (2 * CF * Bg + el * Bg) := by
    intro t
    have hGi : IntegrableOn (fun x : ℝ => Gtf (extendAt i₀ x t)) (Set.Ioc (0:ℝ) Bg) volume :=
      IntegrableOn.of_bound hvolIoc
        ((hcontG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        (CF + el) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hb t x)
    have hFi : IntegrableOn (fun x : ℝ => F (extendAt i₀ x t)) (Set.Ioc (0:ℝ) Bg) volume :=
      IntegrableOn.of_bound hvolIoc
        ((hcontF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        CF (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hCF _)
    have hPQ : |(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t))
        - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t))| ≤ el * Bg := by
      have heq : (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t))
          - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t))
          = ∫ x in Set.Ioc (0:ℝ) Bg, (Gtf (extendAt i₀ x t) - F (extendAt i₀ x t)) :=
        (MeasureTheory.integral_sub hGi hFi).symm
      rw [heq]
      calc |∫ x in Set.Ioc (0:ℝ) Bg, (Gtf (extendAt i₀ x t) - F (extendAt i₀ x t))|
          ≤ ∫ x in Set.Ioc (0:ℝ) Bg, |Gtf (extendAt i₀ x t) - F (extendAt i₀ x t)| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ x in Set.Ioc (0:ℝ) Bg, el :=
            setIntegral_mono_of_nonneg (fun x _ => abs_nonneg _) (fun x _ => happrox _)
              (hcI _ hel)
        _ = el * Bg := by
            rw [MeasureTheory.setIntegral_const, smul_eq_mul]
            show (volume (Set.Ioc (0:ℝ) Bg)).toReal * el = el * Bg
            rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ Bg - 0)]
            ring
    have hPQs : |(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t))
        + (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t))|
        ≤ 2 * CF * Bg + el * Bg := by
      have h3 : (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t))
          + (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t))
          = ((∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t))
              - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)))
            + 2 * (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) := by ring
      rw [h3]
      refine le_trans (abs_add_le _ _) ?_
      have h4 : |2 * (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t))| ≤ 2 * (CF * Bg) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left (hbdF t) (by norm_num)
      linarith [hPQ, h4]
    have hsq : |(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2
        - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2|
        = |(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t))
            - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t))|
          * |(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t))
            + (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t))| := by
      rw [← abs_mul]; ring_nf
    rw [hsq]
    refine le_trans (mul_le_mul hPQ hPQs (abs_nonneg _) (mul_nonneg hel hBg0)) (le_of_eq ?_)
    ring
  have hkillG : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∃ l : {l : Fin k // l ≠ i₀}, Bg < t l) →
      (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) = 0 := by
    intro t hl
    obtain ⟨l, hl⟩ := hl
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    refine hGcoord _ ⟨l.1, ?_⟩
    rw [show extendAt i₀ x t l.1 = t l from by simp only [extendAt, dif_neg l.2]]
    exact hl
  have hkillF : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∃ l : {l : Fin k // l ≠ i₀}, Bg < t l) →
      (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) = 0 := by
    intro t hl
    obtain ⟨l, hl⟩ := hl
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    refine hFcoord _ ⟨l.1, ?_⟩
    rw [show extendAt i₀ x t l.1 = t l from by simp only [extendAt, dif_neg l.2]]
    exact lt_of_le_of_lt hRB hl
  have hkillI : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∃ l : {l : Fin k // l ≠ i₀}, t l < 0) → orthInd t = 0 := by
    intro t hl
    obtain ⟨l, hl⟩ := hl
    rw [orthInd]
    exact Finset.prod_eq_zero (Finset.mem_univ l)
      (Set.indicator_of_notMem (by rw [Set.mem_Ici]; exact not_le.mpr hl) _)
  have hptfg : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      ‖(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * orthInd t
        - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * orthInd t‖
        ≤ (el * Bg * (2 * CF * Bg + el * Bg)) *
            (margBox i₀ Bg).indicator (fun _ => (1:ℝ)) t := by
    intro t
    by_cases ht : t ∈ margBox i₀ Bg
    · rw [Set.indicator_of_mem ht, mul_one]
      have h1 : (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * orthInd t
          - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * orthInd t
          = ((∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2
              - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2) * orthInd t := by ring
      rw [h1, Real.norm_eq_abs, abs_mul, abs_of_nonneg (orthInd_nonneg t)]
      refine le_trans (mul_le_mul_of_nonneg_right (hdiff t) (orthInd_nonneg t)) ?_
      have hK : (0:ℝ) ≤ el * Bg * (2 * CF * Bg + el * Bg) := by
        have : (0:ℝ) ≤ 2 * CF * Bg + el * Bg := by
          have : (0:ℝ) ≤ CF + el := by linarith
          positivity
        positivity
      simpa using mul_le_mul_of_nonneg_left (orthInd_le_one t) hK
    · rw [Set.indicator_of_notMem ht, mul_zero]
      have hx : ∃ l : {l : Fin k // l ≠ i₀}, t l < 0 ∨ Bg < t l := by
        by_contra hc
        push_neg at hc
        exact ht (Set.mem_univ_pi.mpr fun l =>
          Set.mem_Icc.mpr ⟨hc l |>.1, hc l |>.2⟩)
      obtain ⟨l, hl⟩ := hx
      rcases hl with hl | hl
      · rw [hkillI t ⟨l, hl⟩]
        rw [show (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * 0
              - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * 0 = 0 from by ring]
        rw [norm_zero]
      · rw [hkillG t ⟨l, hl⟩, hkillF t ⟨l, hl⟩]
        rw [show (0:ℝ) ^ 2 * orthInd t - (0:ℝ) ^ 2 * orthInd t = 0 from by ring]
        rw [norm_zero]
  have hvolM : volume (margBox i₀ Bg) ≠ ⊤ := by
    rw [volume_margBox i₀ hBg0]; exact ENNReal.ofReal_ne_top
  have hIind : Integrable ((margBox i₀ Bg).indicator (fun _ => (1:ℝ))) := by
    rw [MeasureTheory.integrable_indicator_iff (measurableSet_margBox i₀ Bg)]
    refine IntegrableOn.of_bound (by rw [lt_top_iff_ne_top]; exact hvolM)
      aestronglyMeasurable_const 1 (Filter.Eventually.of_forall fun x => by simp)
  have hA'cont : Continuous (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
      ∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) := by
    rw [show (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
          ∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t))
        = fun t => ∫ x in (0:ℝ)..Bg, Gtf (extendAt i₀ x t) from by
          funext t; exact (intervalIntegral.integral_of_le hBg0).symm]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcontG 0 Bg
  have hAcont : Continuous (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
      ∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) := by
    rw [show (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
          ∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t))
        = fun t => ∫ x in (0:ℝ)..Bg, F (extendAt i₀ x t) from by
          funext t; exact (intervalIntegral.integral_of_le hBg0).symm]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcontF 0 Bg
  have hCptG : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      ‖(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * orthInd t‖
        ≤ max 1 (((CF + el) * Bg) ^ 2) * (margBox i₀ Bg).indicator (fun _ => (1:ℝ)) t := by
    intro t
    by_cases ht : t ∈ margBox i₀ Bg
    · rw [Set.indicator_of_mem ht, mul_one, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg _), abs_of_nonneg (orthInd_nonneg t)]
      have h3 : (0:ℝ) ≤ (CF + el) * Bg := by
        have h3' : (0:ℝ) ≤ CF + el := by linarith
        positivity
      have h2 : (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2
          ≤ ((CF + el) * Bg) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbdG t) 2
      refine le_trans (mul_le_mul_of_nonneg_right h2 (orthInd_nonneg t)) ?_
      refine le_trans (mul_le_mul_of_nonneg_left (orthInd_le_one t) (pow_nonneg h3 2)) ?_
      rw [mul_one]
      rcases le_total (((CF + el) * Bg) ^ 2) 1 with h | h
      · exact le_trans h (le_max_left _ _)
      · exact le_max_right _ _
    · rw [Set.indicator_of_notMem ht, mul_zero]
      have hx : ∃ l : {l : Fin k // l ≠ i₀}, t l < 0 ∨ Bg < t l := by
        by_contra hc
        push_neg at hc
        exact ht (Set.mem_univ_pi.mpr fun l =>
          Set.mem_Icc.mpr ⟨hc l |>.1, hc l |>.2⟩)
      obtain ⟨l, hl⟩ := hx
      rcases hl with hl | hl
      · rw [hkillI t ⟨l, hl⟩]
        rw [show (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * 0 = 0 from by ring]
        rw [norm_zero]
      · rw [hkillG t ⟨l, hl⟩]
        rw [show (0:ℝ) ^ 2 * orthInd t = 0 from by ring]
        rw [norm_zero]
  have hCptF : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      ‖(∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * orthInd t‖
        ≤ max 1 ((CF * Bg) ^ 2) * (margBox i₀ Bg).indicator (fun _ => (1:ℝ)) t := by
    intro t
    by_cases ht : t ∈ margBox i₀ Bg
    · rw [Set.indicator_of_mem ht, mul_one, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg _), abs_of_nonneg (orthInd_nonneg t)]
      have h3 : (0:ℝ) ≤ CF * Bg := by positivity
      have h2 : (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2
          ≤ (CF * Bg) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbdF t) 2
      refine le_trans (mul_le_mul_of_nonneg_right h2 (orthInd_nonneg t)) ?_
      refine le_trans (mul_le_mul_of_nonneg_left (orthInd_le_one t) (pow_nonneg h3 2)) ?_
      rw [mul_one]
      rcases le_total ((CF * Bg) ^ 2) 1 with h | h
      · exact le_trans h (le_max_left _ _)
      · exact le_max_right _ _
    · rw [Set.indicator_of_notMem ht, mul_zero]
      have hx : ∃ l : {l : Fin k // l ≠ i₀}, t l < 0 ∨ Bg < t l := by
        by_contra hc
        push_neg at hc
        exact ht (Set.mem_univ_pi.mpr fun l =>
          Set.mem_Icc.mpr ⟨hc l |>.1, hc l |>.2⟩)
      obtain ⟨l, hl⟩ := hx
      rcases hl with hl | hl
      · rw [hkillI t ⟨l, hl⟩]
        rw [show (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * 0 = 0 from by ring]
        rw [norm_zero]
      · rw [hkillF t ⟨l, hl⟩]
        rw [show (0:ℝ) ^ 2 * orthInd t = 0 from by ring]
        rw [norm_zero]
  have hIf : Integrable (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
      (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * orthInd t) :=
    Integrable.mono' (hIind.const_mul (max 1 (((CF + el) * Bg) ^ 2)))
      ((hA'cont.aestronglyMeasurable.pow 2).mul (measurable_orthInd i₀).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hCptG t)
  have hIg : Integrable (fun t : {l : Fin k // l ≠ i₀} → ℝ =>
      (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * orthInd t) :=
    Integrable.mono' (hIind.const_mul (max 1 ((CF * Bg) ^ 2)))
      ((hAcont.aestronglyMeasurable.pow 2).mul (measurable_orthInd i₀).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hCptF t)
  have hbeta : (∫ t : {l : Fin k // l ≠ i₀} → ℝ,
        (∫ x in Set.Ioi (0:ℝ), Gtf (extendAt i₀ x t)) ^ 2 * orthInd t)
      = ∫ t : {l : Fin k // l ≠ i₀} → ℝ,
          (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * orthInd t := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [hIoc t]
  have hmarg : margInt i₀ F = ∫ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * orthInd t := by
    rw [margInt]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [hIocF t]
  have hfinal : |(∫ t : {l : Fin k // l ≠ i₀} → ℝ,
        (∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * orthInd t)
      - (∫ t : {l : Fin k // l ≠ i₀} → ℝ,
        (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * orthInd t)|
      ≤ el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1) := by
    rw [← MeasureTheory.integral_sub hIf hIg]
    refine le_trans abs_integral_le_integral_abs ?_
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (f := fun t : {l : Fin k // l ≠ i₀} → ℝ =>
        ‖(∫ x in Set.Ioc (0:ℝ) Bg, Gtf (extendAt i₀ x t)) ^ 2 * orthInd t
          - (∫ x in Set.Ioc (0:ℝ) Bg, F (extendAt i₀ x t)) ^ 2 * orthInd t‖)
      (g := fun t : {l : Fin k // l ≠ i₀} → ℝ =>
        (el * Bg * (2 * CF * Bg + el * Bg)) *
          (margBox i₀ Bg).indicator (fun _ => (1:ℝ)) t)
      (Filter.Eventually.of_forall fun t => norm_nonneg _)
      (hIind.const_mul _)
      (Filter.Eventually.of_forall fun t => hptfg t)) ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator
        (measurableSet_margBox i₀ Bg), MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    show (el * Bg * (2 * CF * Bg + el * Bg)) * (volume (margBox i₀ Bg)).toReal
        ≤ el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1)
    rw [volume_margBox i₀ hBg0, ENNReal.toReal_ofReal (pow_nonneg hBg0 _)]
  rw [hbeta, hmarg]
  exact hfinal

/-- **Joint convergence of the tensor-data coefficients.**  Every continuous compactly
supported `F` supported in the orthant and in `{∑ i, t i ≤ R}` admits tensor data `(c, Gt, β)`
with each `β j i ≤ R + 12 k η` and `∑ i, β j i ≤ R + 12 k η`, whose antiderivative
coefficients approximate both `IFuncOrth k F` and every marginal functional `margInt i F`
arbitrarily well. -/
theorem exists_tensorData_near {k : ℕ} {F : (Fin k → ℝ) → ℝ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1) (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    {η δ M : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hM : ∀ t : Fin k → ℝ, |F t| ≤ M) :
    ∃ (J : ℕ) (β : Fin J → Fin k → ℝ) (Gt : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ),
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (Gt j i)) ∧
      (∀ j i, HasCompactSupport (Gt j i)) ∧
      (∀ j i u, β j i < u → Gt j i u = 0) ∧
      (∀ j i, 0 ≤ β j i) ∧
      (∀ j i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ j, ∑ i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ j i u, 0 ≤ u → Gt j i u ≠ 0 → β j i - 6 * η < u ∧ u < β j i) ∧
      (∃ B : ℝ, 0 ≤ B ∧ (∀ j i u, |Gt j i u| ≤ B) ∧
        (∀ t : Fin k → ℝ, ∑ j, |c j| * ∏ i, |Gt j i (t i)| ≤ B)) ∧
      (∃ (Gtf : (Fin k → ℝ) → ℝ) (Bg el CF : ℝ),
        (∀ s : Fin k → ℝ, Gtf s = ∑ j : Fin J, c j * ∏ l, Gt j l (s l)) ∧
        Bg = R + 12 * (k : ℝ) * η ∧
        0 ≤ el ∧ 0 ≤ CF ∧
        (∀ s : Fin k → ℝ, |F s| ≤ CF) ∧
        (∀ s : Fin k → ℝ, (∃ i, Bg < s i) → Gtf s = 0) ∧
        (∀ s : Fin k → ℝ, |Gtf s - F s| ≤ el) ∧
        (∀ t : Fin k → ℝ, ∑ j, |c j| * ∏ i, |Gt j i (t i)| ≤ M) ∧
        (∀ (i₀ : Fin k) (t : {l : Fin k // l ≠ i₀} → ℝ),
          ∑ j, |c j| * ∏ l : {l : Fin k // l ≠ i₀}, |Gt j (l : Fin k) (t l)| ≤ M) ∧
        el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1) ≤ δ / 2) ∧
      |tpAlpha c (fun j i => anti ψ (Gt j) i) - IFuncOrth k F| < δ ∧
      (∀ i₀, |tpBeta c (fun j i => anti ψ (Gt j) i) i₀ - margInt i₀ F| < δ) ∧
      (∃ Bm : ℝ, 0 ≤ Bm ∧ ∀ (i₀ : Fin k) (t : {l : Fin k // l ≠ i₀} → ℝ),
        ∑ j, |c j| * ∏ l : {l : Fin k // l ≠ i₀}, |Gt j (l : Fin k) (t l)| ≤ Bm) := by
  classical
  have hbnd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Fin k → ℝ, |F t| ≤ C := by
    obtain ⟨C, hC⟩ := hFcs.isCompact.exists_bound_of_continuousOn hFc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
    by_cases ht : t ∈ tsupport F
    · exact le_trans ((Real.norm_eq_abs (F t)).symm ▸ hC t ht) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp
  obtain ⟨CF, hCF0, hCF⟩ := hbnd
  set Bg : ℝ := R + 12 * (k : ℝ) * η with hBg
  have h12 : (0:ℝ) ≤ 12 * (k : ℝ) * η := by positivity
  have hBg0 : 0 ≤ Bg := by rw [hBg]; linarith
  have hRB : R ≤ Bg := by rw [hBg]; linarith
  set Vb : ℝ := Bg ^ k with hVb
  have hVb0 : 0 ≤ Vb := by rw [hVb]; positivity
  set A : ℝ := 2 * (2 * (CF * Vb) + Vb + 1) + 2 * ((2 * CF + 1) * Bg ^ 2 * (Vb + 1)) + 1 with hA
  have hA1 : 1 ≤ A := by
    rw [hA]
    nlinarith [mul_nonneg hCF0 hVb0, hVb0, mul_nonneg hBg0 hBg0,
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * CF + 1) (sq_nonneg Bg))
        (by positivity : (0:ℝ) ≤ Vb + 1)]
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  set el : ℝ := min 1 (δ / (8 * A)) with hel
  have hel0 : 0 < el := by
    rw [hel]; exact lt_min one_pos (div_pos hδ (by positivity))
  have hel1 : el ≤ 1 := by rw [hel]; exact min_le_left _ _
  have helA : el * A ≤ δ / 8 := by
    have h : el ≤ δ / (8 * A) := by rw [hel]; exact min_le_right _ _
    calc el * A ≤ (δ / (8 * A)) * A := mul_le_mul_of_nonneg_right h hA0.le
      _ = δ / 8 := by field_simp
  obtain ⟨ι, hι, c, β, Gt, hGtsm, hGtcs, hβnn, hβind, hβsum, hthin,
      ⟨Bun, hBun0, hBunbd, hBunsum⟩, hfullM0, hmargM0, happrox⟩ :=
    Commons.Analysis.TensorApprox.exists_tensor_localization_orthant_thin_marg_explicit
      hFc hFcs hR hM hη hel0
  have hBmarg0 : (0:ℝ) ≤ M := le_trans (abs_nonneg (F (fun _ => 0))) (hM (fun _ => 0))
  have hBmarg : ∀ (i : Fin k) (t : {l : Fin k // l ≠ i} → ℝ),
      ∑ j, |c j| * ∏ l : {l : Fin k // l ≠ i}, |Gt j l.1 (t l)| ≤ M := hmargM0
  have hGtvan : ∀ j i u, β j i < u → Gt j i u = 0 := by
    intro j i u hlt
    by_contra hne
    exact absurd (hthin j i u (le_of_lt (lt_of_le_of_lt (hβnn j i) hlt)) hne).2
      (not_lt.mpr (le_of_lt hlt))
  have happrox' : ∀ t, |(∑ j : ι, c j * ∏ i, Gt j i (t i)) - F t| < el := by
    intro t
    rw [abs_sub_comm]
    exact happrox t
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j i => β (e.symm j) i, fun j i => Gt (e.symm j) i,
    fun j => c (e.symm j), fun j i => hGtsm (e.symm j) i, fun j i => hGtcs (e.symm j) i,
    fun j i u hu => hGtvan (e.symm j) i u hu, fun j i => hβnn (e.symm j) i,
    fun j i => hβind (e.symm j) i,
    fun j => hβsum (e.symm j),
    (fun j i u hu hne => hthin (e.symm j) i u hu hne),
    ⟨Bun, hBun0, (fun j i u => hBunbd (e.symm j) i u), (fun t => by
      rw [← Fintype.sum_equiv e (fun j : ι => |c j| * ∏ i, |Gt j i (t i)|)
        (fun j : Fin (Fintype.card ι) => |c (e.symm j)| * ∏ i, |Gt (e.symm j) i (t i)|)
        (fun y => by simp)]
      exact hBunsum t)⟩, ?_, ?_, ?_, ?_⟩
  · -- the marginal-restricted approximation
    set Gtf : (Fin k → ℝ) → ℝ :=
      fun s => ∑ j : Fin (Fintype.card ι), c (e.symm j) * ∏ i, Gt (e.symm j) i (s i) with hGtf
    have hGtfc : Continuous Gtf := by
      rw [hGtf]
      refine continuous_finsetSum _ fun j _ => Continuous.const_mul ?_ _
      exact continuous_finsetProd _ fun i _ =>
        (hGtsm (e.symm j) i).continuous.comp (continuous_apply i)
    have hGcoord : ∀ s : Fin k → ℝ, (∃ i, Bg < s i) → Gtf s = 0 := by
      intro s hs
      rw [hGtf]
      dsimp only
      refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨i₀', hi₀'⟩ := hs
      have hbndj : β (e.symm j) i₀' ≤ Bg := by
        rw [hBg]; exact hβind (e.symm j) i₀'
      by_contra hne
      have hprod : (∏ i, Gt (e.symm j) i (s i)) ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hle : s i₀' ≤ β (e.symm j) i₀' := by
        by_contra hcon
        push_neg at hcon
        exact hprod (Finset.prod_eq_zero (Finset.mem_univ i₀')
          (hGtvan (e.symm j) i₀' (s i₀') hcon))
      linarith
    have hFcoord : ∀ s : Fin k → ℝ, (∃ i, R < s i) → F s = 0 := by
      intro s hs
      by_contra hne
      obtain ⟨hnn, hle⟩ := hR s hne
      obtain ⟨i, hi⟩ := hs
      have : s i ≤ ∑ i, s i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i)
      linarith
    have happ : ∀ s : Fin k → ℝ, |Gtf s - F s| ≤ el := by
      intro s
      have hre : (∑ j : Fin (Fintype.card ι), c (e.symm j) * ∏ i, Gt (e.symm j) i (s i))
          = ∑ j : ι, c j * ∏ i, Gt j i (s i) :=
        (Fintype.sum_equiv e (fun j : ι => c j * ∏ i, Gt j i (s i))
          (fun j : Fin (Fintype.card ι) => c (e.symm j) * ∏ i, Gt (e.symm j) i (s i))
          (fun y => by simp)).symm
      rw [hGtf]
      dsimp only
      rw [hre]
      exact le_of_lt (happrox' s)
    have hpow : Bg ^ (k - 1) ≤ Vb + 1 := by
      rw [hVb]
      rcases le_total 1 Bg with h | h
      · calc Bg ^ (k - 1) ≤ Bg ^ k := pow_le_pow_right₀ h (Nat.sub_le k 1)
          _ ≤ Bg ^ k + 1 := by linarith
      · calc Bg ^ (k - 1) ≤ 1 ^ (k - 1) := pow_le_pow_left₀ hBg0 h _
          _ = 1 := one_pow _
          _ ≤ Bg ^ k + 1 := by linarith [pow_nonneg hBg0 k]
    have h14 : el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1)
        ≤ el * ((2 * CF + 1) * Bg ^ 2 * (Vb + 1)) := by
      have hb2 : (0:ℝ) ≤ 2 * CF * Bg + el * Bg := by
        have h1 : (0:ℝ) ≤ CF * Bg := mul_nonneg hCF0 hBg0
        have h2 : (0:ℝ) ≤ el * Bg := mul_nonneg hel0.le hBg0
        linarith
      have hb3 : 2 * CF * Bg + el * Bg ≤ 2 * CF * Bg + Bg := by
        have h6 : el * Bg ≤ 1 * Bg := mul_le_mul_of_nonneg_right hel1 hBg0
        linarith
      have h4 : el * Bg * (2 * CF * Bg + el * Bg) ≤ el * Bg * (2 * CF * Bg + Bg) :=
        mul_le_mul_of_nonneg_left hb3 (by nlinarith [hel0, hBg0])
      have h5 : el * Bg * (2 * CF * Bg + Bg) * Bg ^ (k - 1)
          ≤ el * Bg * (2 * CF * Bg + Bg) * (Vb + 1) :=
        mul_le_mul_of_nonneg_left hpow (by
          have h1 : (0:ℝ) ≤ CF * Bg := mul_nonneg hCF0 hBg0
          have h2 : (0:ℝ) ≤ el * Bg := mul_nonneg hel0.le hBg0
          have h3 : (0:ℝ) ≤ 2 * CF * Bg + Bg := by linarith
          exact mul_nonneg h2 h3)
      refine le_trans (le_trans (mul_le_mul_of_nonneg_right h4 (pow_nonneg hBg0 _)) h5) (le_of_eq ?_)
      ring
    have h3 : ((2 * CF + 1) * Bg ^ 2 * (Vb + 1)) ≤ A := by
      rw [hA]
      nlinarith [mul_nonneg hCF0 hVb0, hVb0, sq_nonneg Bg,
        mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * CF + 1) (sq_nonneg Bg))
          (by linarith [hVb0] : (0:ℝ) ≤ Vb + 1)]
    have hfullM : ∀ t : Fin k → ℝ,
        ∑ j : Fin (Fintype.card ι), |c (e.symm j)| * ∏ i, |Gt (e.symm j) i (t i)| ≤ M := by
      intro t
      rw [← Fintype.sum_equiv e (fun j : ι => |c j| * ∏ i, |Gt j i (t i)|)
        (fun j : Fin (Fintype.card ι) => |c (e.symm j)| * ∏ i, |Gt (e.symm j) i (t i)|)
        (fun y => by simp)]
      exact hfullM0 t
    have hmargM : ∀ (i₀ : Fin k) (t : {l : Fin k // l ≠ i₀} → ℝ),
        ∑ j : Fin (Fintype.card ι), |c (e.symm j)| *
          ∏ l : {l : Fin k // l ≠ i₀}, |Gt (e.symm j) (l : Fin k) (t l)| ≤ M := by
      intro i₀ t
      rw [← Fintype.sum_equiv e
        (fun j : ι => |c j| * ∏ l : {l : Fin k // l ≠ i₀}, |Gt j (l : Fin k) (t l)|)
        (fun j : Fin (Fintype.card ι) => |c (e.symm j)| *
          ∏ l : {l : Fin k // l ≠ i₀}, |Gt (e.symm j) (l : Fin k) (t l)|)
        (fun y => by simp)]
      exact hmargM0 i₀ t
    refine ⟨Gtf, Bg, el, CF, (fun s => by rw [hGtf]), rfl, hel0.le, hCF0, hCF, hGcoord,
      happ, hfullM, hmargM, ?_⟩
    calc el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1)
        ≤ el * ((2 * CF + 1) * Bg ^ 2 * (Vb + 1)) := h14
      _ ≤ el * A := mul_le_mul_of_nonneg_left h3 hel0.le
      _ ≤ δ / 8 := helA
      _ ≤ δ / 2 := by linarith
  · -- the `α` bound
    have hGc : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), Continuous (Gt (e.symm j) i) :=
      fun j i => (hGtsm (e.symm j) i).continuous
    have hGcs' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), HasCompactSupport (Gt (e.symm j) i) :=
      fun j i => hGtcs (e.symm j) i
    have hGi' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), Integrable (Gt (e.symm j) i) :=
      fun j i => (hGc j i).integrable_of_hasCompactSupport (hGcs' j i)
    have hGv' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k),
        ∃ R : ℝ, ∀ x : ℝ, R ≤ x → Gt (e.symm j) i x = 0 :=
      fun j i => ⟨β (e.symm j) i + 1,
        fun x hx => hGtvan (e.symm j) i x (lt_of_lt_of_le (lt_add_one _) hx)⟩
    rw [tpAlpha_anti hψ1 (G := fun j i => Gt (e.symm j) i) hGc hGcs' hGi' hGv'
      (c := fun j => c (e.symm j))]
    have hkey : ∀ t : Fin k → ℝ,
        (∑ j : Fin (Fintype.card ι), c (e.symm j) * ∏ i, Gt (e.symm j) i (t i))
          = ∑ j : ι, c j * ∏ i, Gt j i (t i) := by
      intro t
      exact (Fintype.sum_equiv e (fun j : ι => c j * ∏ i, Gt j i (t i))
        (fun j : Fin (Fintype.card ι) => c (e.symm j) * ∏ i, Gt (e.symm j) i (t i))
        (fun x => by simp)).symm
    simp only [hkey]
    set Gtf : (Fin k → ℝ) → ℝ := fun t => ∑ j : ι, c j * ∏ i, Gt j i (t i) with hGtf
    have hGtfc : Continuous Gtf := by
      rw [hGtf]
      refine continuous_finsetSum _ fun j _ => Continuous.const_mul ?_ _
      exact continuous_finsetProd _ fun i _ => (hGtsm j i).continuous.comp (continuous_apply i)
    have hvanGtf : ∀ t, (∀ i, 0 ≤ t i) → (∃ i, Bg < t i) → Gtf t = 0 := by
      intro t hpos hex
      rw [hGtf]
      refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨i₀', hi₀'⟩ := hex
      have hbndj : β j i₀' ≤ Bg := by
        rw [hBg]; exact hβind j i₀'
      by_contra hne
      have hprod : (∏ i, Gt j i (t i)) ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hle : t i₀' ≤ β j i₀' := by
        by_contra hcon
        push_neg at hcon
        exact hprod (Finset.prod_eq_zero (Finset.mem_univ i₀') (hGtvan j i₀' (t i₀') hcon))
      linarith
    have hvanF : ∀ t, (∀ i, 0 ≤ t i) → (∃ i, Bg < t i) → F t = 0 := by
      intro t hpos hex
      by_contra hne
      obtain ⟨hnn, hle⟩ := hR t hne
      obtain ⟨i₀', hi₀'⟩ := hex
      have : t i₀' ≤ ∑ i, t i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i₀')
      linarith
    have hAlph : (∫ t : Fin k → ℝ, Gtf t ^ 2 * orthInd t) = ∫ t in orthantSet k, Gtf t ^ 2 := by
      rw [← MeasureTheory.integral_indicator (measurableSet_orthantSet k)]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      rw [orthInd_eq_indicator]
      by_cases ht : t ∈ orthantSet k
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, mul_one]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
    have hboxG : (∫ t in orthantSet k, Gtf t ^ 2) = ∫ t in halfBox k Bg, Gtf t ^ 2 :=
      setIntegral_orthant_eq_halfBox fun t h1 h2 => by rw [hvanGtf t h1 h2]; ring
    have hboxF : (∫ t in orthantSet k, F t ^ 2) = ∫ t in halfBox k Bg, F t ^ 2 :=
      setIntegral_orthant_eq_halfBox fun t h1 h2 => by rw [hvanF t h1 h2]; ring
    have hIF : IFuncOrth k F = ∫ t in halfBox k Bg, F t ^ 2 := by
      rw [IFuncOrth, ← hboxF, ← MeasureTheory.integral_indicator (measurableSet_orthantSet k)]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      by_cases ht : t ∈ orthantSet k
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht]
        have hF0 : F t = 0 := by
          by_contra hne
          exact ht (mem_orthantSet.mpr (hR t hne).1)
        rw [hF0]; ring
    have hvolENN : (volume : Measure (Fin k → ℝ)) (halfBox k Bg) = ENNReal.ofReal Vb := by
      rw [halfBox, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
      have h1 : (∏ i : Fin k, (volume : Measure ℝ) (Set.Icc (0:ℝ) Bg))
          = ∏ _i : Fin k, ENNReal.ofReal Bg :=
        Finset.prod_congr rfl fun i _ => by rw [Real.volume_Icc]; congr 1; ring
      rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hVb]
      exact (ENNReal.ofReal_pow hBg0 k).symm
    have hvol : (volume (halfBox k Bg)).toReal = Vb := by
      rw [hvolENN, ENNReal.toReal_ofReal hVb0]
    have hvol_ne : (volume (halfBox k Bg)) ≠ ⊤ := by
      rw [hvolENN]; exact ENNReal.ofReal_ne_top
    have hbound := Commons.Analysis.Integral.abs_integral_sq_sub_sq_le
      (s := halfBox k Bg) (measurableSet_halfBox k Bg)
      hvol_ne (hGtfc.measurable.aestronglyMeasurable)
      hFc.measurable.aestronglyMeasurable (B := CF + el) (ε := el)
      (by linarith)
      (fun x _ => by
        have h1 : |Gtf x| ≤ |F x| + |Gtf x - F x| := by
          calc |Gtf x| = |F x + (Gtf x - F x)| := by ring_nf
            _ ≤ |F x| + |Gtf x - F x| := abs_add_le _ _
        linarith [hCF x, happrox' x])
      (fun x _ => le_trans (hCF x) (le_add_of_nonneg_right hel0.le)) (le_of_lt hel0)
      (fun x _ => le_of_lt (happrox' x))
    calc |(∫ t : Fin k → ℝ, Gtf t ^ 2 * orthInd t) - IFuncOrth k F|
        = |(∫ t in halfBox k Bg, Gtf t ^ 2) - (∫ t in halfBox k Bg, F t ^ 2)| := by
          rw [hAlph, hboxG, hIF]
      _ ≤ 2 * (CF + el) * el * (volume (halfBox k Bg)).toReal := hbound
      _ = 2 * (CF + el) * el * Vb := by rw [hvol]
      _ < δ := by
          have h1 : 2 * (CF + el) * el * Vb = el * (2 * (CF * Vb) + 2 * (el * Vb)) := by ring
          rw [h1]
          have h2 : 2 * (CF * Vb) + 2 * (el * Vb) ≤ A := by
            rw [hA]
            nlinarith [mul_nonneg hCF0 hVb0, mul_nonneg hel0.le hVb0,
              mul_le_mul_of_nonneg_right hel1 hVb0, hVb0, sq_nonneg Bg,
              mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * CF + 1) (sq_nonneg Bg))
                (by positivity : (0:ℝ) ≤ Vb + 1)]
          calc el * (2 * (CF * Vb) + 2 * (el * Vb)) ≤ el * A :=
                mul_le_mul_of_nonneg_left h2 hel0.le
            _ ≤ δ / 8 := helA
            _ < δ := by linarith
  · -- the `β` bound
    intro i₀
    have hGc : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), Continuous (Gt (e.symm j) i) :=
      fun j i => (hGtsm (e.symm j) i).continuous
    have hGcs' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), HasCompactSupport (Gt (e.symm j) i) :=
      fun j i => hGtcs (e.symm j) i
    have hGi' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k), Integrable (Gt (e.symm j) i) :=
      fun j i => (hGc j i).integrable_of_hasCompactSupport (hGcs' j i)
    have hGv' : ∀ (j : Fin (Fintype.card ι)) (i : Fin k),
        ∃ R : ℝ, ∀ x : ℝ, R ≤ x → Gt (e.symm j) i x = 0 :=
      fun j i => ⟨β (e.symm j) i + 1,
        fun x hx => hGtvan (e.symm j) i x (lt_of_lt_of_le (lt_add_one _) hx)⟩
    rw [tpBeta_anti hψ0 hψ1 (G := fun j i => Gt (e.symm j) i) hGc hGcs' hGi' hGv'
      (c := fun j => c (e.symm j)) i₀]
    have hkeyB : ∀ (x : ℝ) (t : {l : Fin k // l ≠ i₀} → ℝ),
        (∑ j : Fin (Fintype.card ι), c (e.symm j) * ∏ l, Gt (e.symm j) l (extendAt i₀ x t l))
          = ∑ j : ι, c j * ∏ l, Gt j l (extendAt i₀ x t l) := by
      intro x t
      exact (Fintype.sum_equiv e
        (fun j : ι => c j * ∏ l, Gt j l (extendAt i₀ x t l))
        (fun j : Fin (Fintype.card ι) => c (e.symm j) * ∏ l, Gt (e.symm j) l (extendAt i₀ x t l))
        (fun y => by simp)).symm
    simp only [hkeyB]
    set Gtf : (Fin k → ℝ) → ℝ := fun t => ∑ j : ι, c j * ∏ i, Gt j i (t i) with hGtf
    have hGtfc : Continuous Gtf := by
      rw [hGtf]
      refine continuous_finsetSum _ fun j _ => Continuous.const_mul ?_ _
      exact continuous_finsetProd _ fun i _ => (hGtsm j i).continuous.comp (continuous_apply i)
    have hGcoord : ∀ s : Fin k → ℝ, (∃ i, Bg < s i) → Gtf s = 0 := by
      intro s hs
      rw [hGtf]
      refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨i₀', hi₀'⟩ := hs
      have hbndj : β j i₀' ≤ Bg := by
        rw [hBg]; exact hβind j i₀'
      by_contra hne
      have hprod : (∏ i, Gt j i (s i)) ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hle : s i₀' ≤ β j i₀' := by
        by_contra hcon
        push_neg at hcon
        exact hprod (Finset.prod_eq_zero (Finset.mem_univ i₀') (hGtvan j i₀' (s i₀') hcon))
      linarith
    have hFcoord : ∀ s : Fin k → ℝ, (∃ i, R < s i) → F s = 0 := by
      intro s hs
      by_contra hne
      obtain ⟨hnn, hle⟩ := hR s hne
      obtain ⟨i, hi⟩ := hs
      have : s i ≤ ∑ i, s i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i)
      linarith
    have happ : ∀ s : Fin k → ℝ, |Gtf s - F s| ≤ el := by
      intro s
      rw [hGtf]
      exact le_of_lt (happrox' s)
    have hpow : Bg ^ (k - 1) ≤ Vb + 1 := by
      rw [hVb]
      rcases le_total 1 Bg with h | h
      · calc Bg ^ (k - 1) ≤ Bg ^ k := pow_le_pow_right₀ h (Nat.sub_le k 1)
          _ ≤ Bg ^ k + 1 := by linarith
      · calc Bg ^ (k - 1) ≤ 1 ^ (k - 1) := pow_le_pow_left₀ hBg0 h _
          _ = 1 := one_pow _
          _ ≤ Bg ^ k + 1 := by linarith [pow_nonneg hBg0 k]
    have hmain := margInt_error_le (F := F) (Gtf := Gtf) (CF := CF) (R := R) (Bg := Bg) (el := el)
      hCF0 hCF hBg0 hRB hel0.le hFcoord hGcoord happ hGtfc hFc i₀
    have h14 : el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1)
        ≤ el * ((2 * CF + 1) * Bg ^ 2 * (Vb + 1)) := by
      have hb2 : (0:ℝ) ≤ 2 * CF * Bg + el * Bg := by
        have h1 : (0:ℝ) ≤ CF * Bg := mul_nonneg hCF0 hBg0
        have h2 : (0:ℝ) ≤ el * Bg := mul_nonneg hel0.le hBg0
        linarith
      have hb3 : 2 * CF * Bg + el * Bg ≤ 2 * CF * Bg + Bg := by
        have h6 : el * Bg ≤ 1 * Bg := mul_le_mul_of_nonneg_right hel1 hBg0
        linarith
      have h4 : el * Bg * (2 * CF * Bg + el * Bg) ≤ el * Bg * (2 * CF * Bg + Bg) :=
        mul_le_mul_of_nonneg_left hb3 (by nlinarith [hel0, hBg0])
      have h5 : el * Bg * (2 * CF * Bg + Bg) * Bg ^ (k - 1)
          ≤ el * Bg * (2 * CF * Bg + Bg) * (Vb + 1) :=
        mul_le_mul_of_nonneg_left hpow (by
          have h1 : (0:ℝ) ≤ CF * Bg := mul_nonneg hCF0 hBg0
          have h2 : (0:ℝ) ≤ el * Bg := mul_nonneg hel0.le hBg0
          have h3 : (0:ℝ) ≤ 2 * CF * Bg + Bg := by linarith
          exact mul_nonneg h2 h3)
      refine le_trans (le_trans (mul_le_mul_of_nonneg_right h4 (pow_nonneg hBg0 _)) h5) (le_of_eq ?_)
      ring
    have h3 : ((2 * CF + 1) * Bg ^ 2 * (Vb + 1)) ≤ A := by
      rw [hA]
      nlinarith [mul_nonneg hCF0 hVb0, hVb0, sq_nonneg Bg,
        mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * CF + 1) (sq_nonneg Bg))
          (by linarith [hVb0] : (0:ℝ) ≤ Vb + 1)]
    calc |(∫ t : {l : Fin k // l ≠ i₀} → ℝ,
          (∫ x in Set.Ioi (0:ℝ), ∑ j : ι, c j * ∏ l, Gt j l (extendAt i₀ x t l)) ^ 2 * orthInd t)
        - margInt i₀ F|
        ≤ el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1) := hmain
      _ ≤ el * ((2 * CF + 1) * Bg ^ 2 * (Vb + 1)) := h14
      _ ≤ el * A := mul_le_mul_of_nonneg_left h3 hel0.le
      _ ≤ δ / 8 := helA
      _ < δ := by linarith
  · -- the marginal bound
    refine ⟨M, hBmarg0, fun i₀ t => ?_⟩
    rw [← Fintype.sum_equiv e
      (fun j : ι => |c j| * ∏ l : {l : Fin k // l ≠ i₀}, |Gt j (l : Fin k) (t l)|)
      (fun j : Fin (Fintype.card ι) =>
        |c (e.symm j)| * ∏ l : {l : Fin k // l ≠ i₀}, |Gt (e.symm j) (l : Fin k) (t l)|)
      (fun y => by simp)]
    exact hmargM0 i₀ t


/-- **The marginal functional is `JFunc`.**  For `F` supported in the closed orthant and in
`{∑ i, t i ≤ R}` and `c ≥ R`, the orthant marginal integral `margInt i F` coincides with the
`J`-functional `JFunc k i c F` of the Maynard--Polymath variational problem. -/
theorem margInt_eq_JFunc {k : ℕ} {F : (Fin k → ℝ) → ℝ} {R : ℝ}
    (hR : ∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R) {c : ℝ} (hc : R ≤ c) (i : Fin k) :
    margInt i F = JFunc k i c F := by
  have hstep : ∀ t : {j : Fin k // j ≠ i} → ℝ,
      (∫ x : ℝ, F (extendAt i x t)) = ∫ x in Set.Ioi (0:ℝ), F (extendAt i x t) := by
    intro t
    have hzero : ∀ x ∈ Set.Iio (0:ℝ), F (extendAt i x t) = 0 := by
      intro x hx
      by_contra hne
      have h1 := (hR _ hne).1 i
      have h2 : (extendAt i x t) i = x := by simp [extendAt]
      rw [h2] at h1
      exact absurd h1 (not_le.mpr hx)
    have h1 : (∫ x : ℝ, F (extendAt i x t))
        = ∫ x, (Set.Ici (0:ℝ)).indicator (fun x => F (extendAt i x t)) x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ Set.Ici (0:ℝ)
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact hzero x (by rw [Set.mem_Iio]; exact lt_of_not_ge hx)
    rw [h1, MeasureTheory.integral_indicator measurableSet_Ici]
    exact (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici).symm
  rw [margInt, JFunc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [hstep t]
  by_cases ht : (∀ l, 0 ≤ t l)
  · by_cases hc' : (∑ l : {l : Fin k // l ≠ i}, t l) ≤ c
    · have hmem : t ∈ marginalSet k i c := by
        rw [marginalSet]; exact ⟨ht, hc'⟩
      rw [if_pos hmem]
      congr 1
      refine Finset.prod_eq_one fun l _ => ?_
      exact Set.indicator_of_mem (Set.mem_Ici.mpr (ht l)) _
    · have hmem : t ∉ marginalSet k i c := fun h => hc' h.2
      rw [if_neg hmem]
      have hz : (∫ x in Set.Ioi (0:ℝ), F (extendAt i x t)) = 0 := by
        refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
        by_contra hne
        obtain ⟨hnn, hle⟩ := hR _ hne
        have hsum := sum_extendAt i x t
        have hx0 : (0:ℝ) < x := hx
        have hlt : c < ∑ l : {l : Fin k // l ≠ i}, t l := lt_of_not_ge hc'
        linarith
      rw [hz]; ring
  · obtain ⟨l, hl⟩ := not_forall.mp ht
    have hz : orthInd t = 0 := by
      rw [orthInd]
      exact Finset.prod_eq_zero (Finset.mem_univ l)
        (Set.indicator_of_notMem (by rw [Set.mem_Ici]; exact hl) _)
    have hz2 : (∫ x in Set.Ioi (0:ℝ), F (extendAt i x t)) = 0 := by
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      by_contra hne
      have h1 := (hR _ hne).1 l
      have h2 : extendAt i x t l = t l := by simp only [extendAt, dif_neg l.2]
      rw [h2] at h1
      exact absurd h1 hl
    rw [hz, hz2]; ring

/-- **From a variational test function to the criterion's tensor data.**  Every continuous
compactly supported `F` supported in the closed orthant and in `{∑ i, t i ≤ R}` produces
`(J, c, f, M)` with `f` smooth and compactly supported, `M ≥ 0`, `M j i < |t| → f j i t = 0`,
`Σ_i M j i ≤ R + 24 k η`, `1 ≤ t → f j i t = 0` (when `R + 24 k η ≤ 1`), and the two
approximation properties for `tpAlpha` and `tpBeta`. -/
theorem exists_tensorData_JFunc {k : ℕ} {F : (Fin k → ℝ) → ℝ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    (hk : 1 ≤ k) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (h1 : R + 24 * (k : ℝ) * η ≤ 1) :
    ∃ (J : ℕ) (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ) (M : Fin J → Fin k → ℝ),
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i)) ∧
      (∀ j i, HasCompactSupport (f j i)) ∧
      (∀ j i, 0 ≤ M j i) ∧
      (∀ j i t, M j i < |t| → f j i t = 0) ∧
      (∀ j i, M j i ≤ R + 24 * (k : ℝ) * η) ∧
      (∀ j, ∑ i, M j i ≤ R + 24 * (k : ℝ) * η) ∧
      (∀ j i t, 1 ≤ t → f j i t = 0) ∧
      |tpAlpha c f - IFuncOrth k F| < δ ∧
      (∀ i₀, |tpBeta c f i₀ - JFunc k i₀ R F| < δ) := by
  classical
  obtain ⟨ψ, hψsm, hψ0', hψ1', hψ01⟩ :=
    Commons.Analysis.Calculus.exists_contDiff_step (-(12 * η)) 0 (by linarith)
  have hψ0 : ψ 0 = 1 := hψ1' 0 le_rfl
  have hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1 := fun u hu => hψ1' u hu
  obtain ⟨C₀, hC₀⟩ := hFcs.isCompact.exists_bound_of_continuousOn hFc.continuousOn
  have hMbd : ∀ t : Fin k → ℝ, |F t| ≤ max C₀ 0 := by
    intro t
    by_cases ht : t ∈ tsupport F
    · exact le_trans ((Real.norm_eq_abs (F t)).symm ▸ hC₀ t ht) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp
  obtain ⟨J, β, Gt, c, hGtsm, hGtcs, hGtvan, hβnn, hβind, hβsum, hthin, hB, hJnear, hαnear,
      hβnear, hBmarg⟩ :=
    exists_tensorData_near hFc hFcs hR0 hR hψ0 hψ1 hη hδ hMbd
  have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h12η : (0:ℝ) ≤ 12 * η := by positivity
  refine ⟨J, c, fun j i => anti ψ (Gt j) i, fun j i => max (12 * η) (β j i),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hαnear, ?_⟩
  · intro j i
    show ContDiff ℝ (↑(⊤ : ℕ∞)) (anti ψ (Gt j) i)
    have h2 : anti ψ (Gt j) i = fun u : ℝ => ψ u * ∫ s in Set.Ioi u, Gt j i s := rfl
    rw [h2]
    exact hψsm.mul (Commons.Analysis.Calculus.contDiff_integral_Ioi (Gt j i) (hGtcs j i) (hGtsm j i))
  · intro j i
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(12 * η)) (β j i))
      isCompact_Icc ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hcon
    rw [Set.mem_Icc, not_and_or] at hcon
    apply hu
    rcases hcon with h | h
    · have hz : ψ u = 0 := hψ0' u (by linarith [not_le.mp h])
      simp [anti, hz]
    · have hz : (∫ s in Set.Ioi u, Gt j i s) = 0 :=
        MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun s hs =>
          hGtvan j i s (lt_trans (not_le.mp h) hs)
      simp [anti, hz]
  · intro j i
    exact le_trans (le_of_lt (by positivity : (0:ℝ) < 12 * η)) (le_max_left _ _)
  · intro j i t ht
    have hβ : β j i < |t| := lt_of_le_of_lt (le_max_right _ _) ht
    have h12 : 12 * η < |t| := lt_of_le_of_lt (le_max_left _ _) ht
    by_cases ht0 : 0 ≤ t
    · have hz : (∫ s in Set.Ioi t, Gt j i s) = 0 := by
        refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
        rw [abs_of_nonneg ht0] at hβ
        exact hGtvan j i s (lt_trans hβ hs)
      simp [anti, hz]
    · have hz : ψ t = 0 := by
        refine hψ0' t ?_
        have habs : |t| = -t := abs_of_neg (lt_of_not_ge ht0)
        linarith
      simp [anti, hz]
  · intro j i
    have h2 := hβind j i
    have h3 : 12 * η ≤ 12 * (k : ℝ) * η := by nlinarith [hη, hk1]
    have h4 : max (12 * η) (β j i) ≤ 12 * η + β j i :=
      max_le (le_add_of_nonneg_right (hβnn j i)) (le_add_of_nonneg_left h12η)
    have h5 : 12 * (k : ℝ) * η ≤ R + 24 * (k : ℝ) * η := by linarith [hR0]
    linarith
  · intro j
    have hstep : ∀ i : Fin k, max (12 * η) (β j i) ≤ 12 * η + β j i := fun i =>
      max_le (le_add_of_nonneg_right (hβnn j i)) (le_add_of_nonneg_left h12η)
    calc ∑ i, max (12 * η) (β j i) ≤ ∑ i : Fin k, (12 * η + β j i) :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = (k : ℝ) * (12 * η) + ∑ i, β j i := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ ≤ (k : ℝ) * (12 * η) + (R + 12 * (k : ℝ) * η) := by linarith [hβsum j]
      _ = R + 24 * (k : ℝ) * η := by ring
  · intro j i t ht
    show anti ψ (Gt j) i t = 0
    have hz : (∫ s in Set.Ioi t, Gt j i s) = 0 := by
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hs' : t < s := hs
      exact hGtvan j i s (by nlinarith [hβind j i, h1, ht, hs', hk0, hη])
    simp [anti, hz]
  · intro i₀
    have h := hβnear i₀
    rw [margInt_eq_JFunc hR le_rfl i₀] at h
    exact h

/-- **The criterion's data.**  The tensor data of `exists_tensorData_JFunc`, together with the
automatic pairwise support conditions (87)/(90) of Polymath8a §5.3: for every `ϑ > 2 B` (where
`B = R + 24 k η`) and `4 B < 1` the bounds `hM1`/`hM2` of
`translate_two_primes_of_tpWeight_split_family` hold for every choice of the `J₁`-sets `Sf`. -/
theorem exists_criterion_tensorData {k : ℕ} {F : (Fin k → ℝ) → ℝ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    (hk : 1 ≤ k) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (h1 : R + 24 * (k : ℝ) * η ≤ 1) {ϑ : ℝ}
    (h4 : 4 * (R + 24 * (k : ℝ) * η) < 1) (hsmall : 2 * (R + 24 * (k : ℝ) * η) < ϑ) :
    ∃ (J : ℕ) (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ) (M : Fin J → Fin k → ℝ),
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i)) ∧
      (∀ j i, HasCompactSupport (f j i)) ∧
      (∀ j i, 0 ≤ M j i) ∧
      (∀ j i t, M j i < |t| → f j i t = 0) ∧
      (∀ j i t, 1 ≤ t → f j i t = 0) ∧
      (∀ j j', 2 * (∑ i, max (M j i) (M j' i)) < 1) ∧
      (∀ (Sf : Fin k → Finset (Fin J)) (j j' : Fin J) (i₀ : Fin k), j' ∈ Sf i₀ →
        ∑ i ∈ Finset.univ.erase i₀, (M j i + M j' i) < ϑ) ∧
      |tpAlpha c f - IFuncOrth k F| < δ ∧
      (∀ i₀, |tpBeta c f i₀ - JFunc k i₀ R F| < δ) := by
  obtain ⟨J, c, f, M, hsm, hcs, hMnn, hsupp, hMb, hMsum, hfb, hα, hβ⟩ :=
    exists_tensorData_JFunc hFc hFcs hR0 hR hk hη hδ h1
  refine ⟨J, c, f, M, hsm, hcs, hMnn, hsupp, hfb, ?_, ?_, hα, hβ⟩
  · intro j j'
    have hA : (∑ i, max (M j i) (M j' i)) ≤ ∑ i : Fin k, (M j i + M j' i) :=
      Finset.sum_le_sum fun i _ =>
        max_le (le_add_of_nonneg_right (hMnn j' i)) (le_add_of_nonneg_left (hMnn j i))
    have hB : (∑ i : Fin k, (M j i + M j' i))
        ≤ (R + 24 * (k : ℝ) * η) + (R + 24 * (k : ℝ) * η) := by
      rw [Finset.sum_add_distrib]
      linarith [hMsum j, hMsum j']
    nlinarith [hA, hB, h4]
  · intro Sf j j' i₀ hj'
    have hA : (∑ i ∈ Finset.univ.erase i₀, (M j i + M j' i)) ≤ ∑ i : Fin k, (M j i + M j' i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun i _ _ => by linarith [hMnn j i, hMnn j' i])
    have hB : (∑ i : Fin k, (M j i + M j' i))
        ≤ (R + 24 * (k : ℝ) * η) + (R + 24 * (k : ℝ) * η) := by
      rw [Finset.sum_add_distrib]
      linarith [hMsum j, hMsum j']
    linarith [hA, hB, hsmall]

end

end Commons.NumberTheory.MaynardSieve
