import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Commons.MeasureTheory

/-- For a measure `ν` all of whose atoms are bounded by `ε`, the product measure of the
diagonal is bounded by `ε * ν univ`. -/
private lemma prod_diagonal_le {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    (ν : Measure α) [SFinite ν] {ε : ENNReal} (h : ∀ y, ν {y} ≤ ε) :
    (ν.prod ν) {p : α × α | p.1 = p.2} ≤ ε * ν Set.univ := by
  have hs : MeasurableSet {p : α × α | p.1 = p.2} := by
    simpa [Set.diagonal] using measurableSet_diagonal (α := α)
  rw [Measure.prod_apply hs]
  have hcomp : ∀ w : α, ν (Prod.mk w ⁻¹' {p : α × α | p.1 = p.2}) ≤ ε := by
    intro w
    have hpre : Prod.mk w ⁻¹' {p : α × α | p.1 = p.2} = {w} := by
      ext z; simp [eq_comm]
    rw [hpre]; exact h w
  calc ∫⁻ w, ν (Prod.mk w ⁻¹' {p : α × α | p.1 = p.2}) ∂ν
      ≤ ∫⁻ w, ε ∂ν := lintegral_mono hcomp
    _ = ε * ν Set.univ := lintegral_const ε

/-- Energy lower bound: if all atoms of the probability measure `ν` are at most `ε`, then the
logarithmic energy of `ν` dominates `log (D / (2 t)) * ((ν (ball x t))² - ε)`. -/
private lemma key_bound {K : Set ℂ} {D : ℝ} (hD : 0 < D)
    (hDiam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (ν : MeasureTheory.ProbabilityMeasure K) {ε : ENNReal}
    (hε : ∀ y : K, (ν : Measure K) {y} ≤ ε)
    {x : K} {t : ℝ} (ht : 0 < t) (h2tD : 2 * t ≤ D) :
    ENNReal.ofReal (Real.log (D / (2 * t))) *
        (((ν : Measure K) {y : K | ‖((y : K) : ℂ) - ((x : K) : ℂ)‖ < t}) ^ 2 - ε)
      ≤ MeasureTheory.lintegral (ν.prod ν)
        (fun z : K × K => ENNReal.ofReal
          (Real.log (D / ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖))) := by
  set U : Set K := {y : K | ‖((y : K) : ℂ) - ((x : K) : ℂ)‖ < t} with hU
  set L : ENNReal := ENNReal.ofReal (Real.log (D / (2 * t))) with hL
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const))
      continuous_const
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hdiag : MeasurableSet {z : K × K | z.1 = z.2} := by
    simpa [Set.diagonal] using measurableSet_diagonal (α := K)
  have hPoint : ∀ z : K × K,
      (U ×ˢ U \ {z : K × K | z.1 = z.2}).indicator (fun _ => L) z
        ≤ ENNReal.ofReal (Real.log (D / ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖)) := by
    intro z
    rw [Set.indicator_apply]
    by_cases hz : z ∈ U ×ˢ U \ {z : K × K | z.1 = z.2}
    · rw [if_pos hz, hL]
      have hzS : z ∈ U ×ˢ U := hz.1
      have hzd : z.1 ≠ z.2 := by
        intro h; exact hz.2 (by simp [h])
      rw [Set.mem_prod, hU] at hzS
      obtain ⟨hz1, hz2⟩ := hzS
      simp only [Set.mem_setOf_eq] at hz1 hz2
      have hgpos : 0 < ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖ := by
        rw [norm_pos_iff]
        intro h; exact hzd (Subtype.ext (sub_eq_zero.mp h))
      have hglt : ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖ < 2 * t := by
        calc ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖
            = ‖(((z.1 : K) : ℂ) - ((x : K) : ℂ)) + (((x : K) : ℂ) - ((z.2 : K) : ℂ))‖ := by
              congr 1; ring
          _ ≤ ‖((z.1 : K) : ℂ) - ((x : K) : ℂ)‖ + ‖((x : K) : ℂ) - ((z.2 : K) : ℂ)‖ :=
              norm_add_le _ _
          _ = ‖((z.1 : K) : ℂ) - ((x : K) : ℂ)‖ + ‖((z.2 : K) : ℂ) - ((x : K) : ℂ)‖ := by
              rw [norm_sub_rev ((x : K) : ℂ) ((z.2 : K) : ℂ)]
          _ < t + t := add_lt_add hz1 hz2
          _ = 2 * t := by ring
      apply ENNReal.ofReal_le_ofReal
      apply Real.log_le_log
      · positivity
      · rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ hD.le
        simpa [one_div] using one_div_le_one_div_of_le hgpos hglt.le
    · rw [if_neg hz]; exact zero_le
  have hSmeas : MeasurableSet (U ×ˢ U \ {z : K × K | z.1 = z.2}) :=
    (hUmeas.prod hUmeas).diff hdiag
  have step1 : L * ((ν.prod ν : Measure (K × K)) (U ×ˢ U \ {z : K × K | z.1 = z.2}))
      ≤ MeasureTheory.lintegral (ν.prod ν)
        (fun z : K × K => ENNReal.ofReal
          (Real.log (D / ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖))) := by
    have h := lintegral_mono (μ := (ν.prod ν : Measure (K × K))) hPoint
    rw [lintegral_indicator_const hSmeas L] at h
    exact h
  have hdiagbound : (ν.prod ν : Measure (K × K))
        ((U ×ˢ U) ∩ {z : K × K | z.1 = z.2}) ≤ ε := by
    have h1 := prod_diagonal_le (ν : Measure K) (ε := ε) hε
    calc (ν.prod ν : Measure (K × K)) ((U ×ˢ U) ∩ {z : K × K | z.1 = z.2})
        ≤ (ν.prod ν : Measure (K × K)) {z : K × K | z.1 = z.2} :=
          measure_mono Set.inter_subset_right
      _ ≤ ε * (ν : Measure K) Set.univ := h1
      _ = ε := by rw [measure_univ, mul_one]
  have hSdiff : (ν.prod ν : Measure (K × K)) (U ×ˢ U \ {z : K × K | z.1 = z.2})
      = (ν.prod ν : Measure (K × K)) (U ×ˢ U)
        - (ν.prod ν : Measure (K × K)) ((U ×ˢ U) ∩ {z : K × K | z.1 = z.2}) := by
    have hset : U ×ˢ U \ {z : K × K | z.1 = z.2}
        = (U ×ˢ U) \ ((U ×ˢ U) ∩ {z : K × K | z.1 = z.2}) := by
      ext z; simp only [Set.mem_diff, Set.mem_inter_iff]; tauto
    rw [hset]
    exact measure_sdiff Set.inter_subset_left
      ((hUmeas.prod hUmeas).inter hdiag).nullMeasurableSet (measure_ne_top _ _)
  have hSU : (ν.prod ν : Measure (K × K)) (U ×ˢ U) = ((ν : Measure K) U) ^ 2 := by
    rw [ProbabilityMeasure.toMeasure_prod, Measure.prod_prod, sq]
  have hstep2 : L * (((ν : Measure K) U) ^ 2 - ε)
      ≤ L * (ν.prod ν : Measure (K × K)) (U ×ˢ U \ {z : K × K | z.1 = z.2}) := by
    apply mul_le_mul_of_nonneg_left _ (zero_le : (0 : ENNReal) ≤ L)
    rw [hSdiff, hSU]
    exact tsub_le_tsub_left hdiagbound _
  exact le_trans hstep2 step1

theorem atomless_of_tendsto_lintegral_le {K : Set ℂ} (hK : IsCompact K) {D c : ℝ} (hD : 0 < D)
    (hDiam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (μ : MeasureTheory.ProbabilityMeasure K) (νn : ℕ → MeasureTheory.ProbabilityMeasure K)
    (hconv : Filter.Tendsto νn Filter.atTop (nhds μ))
    (hsmall : ∀ n (x : K), (νn n) {x} ≤ ((n : ENNReal) + 1)⁻¹)
    (hc : ∀ n, MeasureTheory.lintegral ((νn n).prod (νn n))
        (fun z : K × K => ENNReal.ofReal
          (Real.log (D / ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖))) ≤ ENNReal.ofReal c) :
    ∀ x : K, μ {x} = 0 := by
  intro x
  by_contra hxne
  have hxne' : (μ : Measure K) {x} ≠ 0 := fun h =>
    hxne ((MeasureTheory.ProbabilityMeasure.null_iff_toMeasure_null μ {x}).mpr h)
  set A : ℝ := ((μ : Measure K) {x}).toReal with hA
  have hApos : 0 < A := by
    rw [hA]; exact ENNReal.toReal_pos hxne' (measure_ne_top _ _)
  have hAeq : ENNReal.ofReal A = (μ : Measure K) {x} :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  set B : ℝ := A / 2 with hBdef
  have hBpos : 0 < B := by rw [hBdef]; linarith
  set Q : ℝ := 8 * c / A ^ 2 with hQdef
  set t : ℝ := D / (2 * (Real.exp Q + 1)) with htdef
  have hAne : A ≠ 0 := ne_of_gt hApos
  have htpos : 0 < t := by rw [htdef]; positivity
  have h2teq : 2 * t = D / (Real.exp Q + 1) := by rw [htdef]; field_simp
  have hD2teq : D / (2 * t) = Real.exp Q + 1 := by rw [h2teq]; field_simp
  have h2tD : 2 * t ≤ D := by
    rw [h2teq]; exact div_le_self hD.le (by linarith [Real.exp_pos Q])
  have hlogeq : Real.log (D / (2 * t)) = Real.log (Real.exp Q + 1) := by rw [hD2teq]
  have hlogpos : 0 < Real.log (D / (2 * t)) := by
    rw [hlogeq]; exact Real.log_pos (by linarith [Real.exp_pos Q])
  have hA2pos : 0 < A ^ 2 / 8 := by positivity
  have hlog_gt_Q : Q < Real.log (D / (2 * t)) := by
    rw [hlogeq]
    calc Q = Real.log (Real.exp Q) := (Real.log_exp Q).symm
      _ < Real.log (Real.exp Q + 1) :=
          Real.log_lt_log (Real.exp_pos Q) (by linarith [Real.exp_pos Q])
  have hQA : Q * (A ^ 2 / 8) = c := by rw [hQdef]; field_simp
  have hkey : c < Real.log (D / (2 * t)) * (A ^ 2 / 8) := by
    rw [← hQA]; exact mul_lt_mul_of_pos_right hlog_gt_Q hA2pos
  -- portmanteau
  have hA_le_U : ENNReal.ofReal A
      ≤ (μ : Measure K) {y : K | ‖((y : K) : ℂ) - ((x : K) : ℂ)‖ < t} := by
    rw [hAeq]
    apply measure_mono
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simp only [Set.mem_setOf_eq, sub_self, norm_zero]
    exact htpos
  have hUopen : IsOpen {y : K | ‖((y : K) : ℂ) - ((x : K) : ℂ)‖ < t} :=
    isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const
  have hport := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hUopen
  have hliminf : ENNReal.ofReal A
      ≤ Filter.liminf (fun n => (νn n : Measure K)
          {y : K | ‖((y : K) : ℂ) - ((x : K) : ℂ)‖ < t}) Filter.atTop :=
    le_trans hA_le_U hport
  have heventuallyA : ∀ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal B
      ≤ (νn n : Measure K) {y : K | ‖((y : K) : ℂ) - ((x : K) : ℂ)‖ < t} := by
    have hlt : ENNReal.ofReal B < ENNReal.ofReal A := by
      rw [ENNReal.ofReal_lt_ofReal_iff hApos]; rw [hBdef]; linarith
    exact ((Filter.le_liminf_iff (f := Filter.atTop)).mp hliminf (ENNReal.ofReal B) hlt).mono
      (fun n h => h.le)
  have heventuallyEps : ∀ᶠ n : ℕ in Filter.atTop,
      ((n : ENNReal) + 1)⁻¹ ≤ ENNReal.ofReal (B ^ 2 / 2) := by
    have hd : 0 < ENNReal.ofReal (B ^ 2 / 2) := ENNReal.ofReal_pos.mpr (by positivity)
    have htend : Filter.Tendsto (fun n : ℕ => ((n : ENNReal) + 1)⁻¹) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ENNReal)⁻¹) Filter.atTop (nhds 0) :=
        ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Nat.cast_add, Nat.cast_one] using h1
    exact (htend.eventually (isOpen_Iio.mem_nhds hd)).mono (fun n h => h.le)
  obtain ⟨n, hnA, hnE⟩ := (heventuallyA.and heventuallyEps).exists
  -- apply the key bound
  have hε : ∀ y : K, (νn n : Measure K) {y} ≤ ((n : ENNReal) + 1)⁻¹ := by
    intro y
    rw [← MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact hsmall n y
  have hkb := key_bound (x := x) hD hDiam (νn n) hε htpos h2tD
  have hX2 : ENNReal.ofReal (B ^ 2)
      ≤ ((νn n : Measure K) {y : K | ‖((y : K) : ℂ) - ((x : K) : ℂ)‖ < t}) ^ 2 := by
    have h := pow_le_pow_left₀ (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal B) hnA 2
    rw [← ENNReal.ofReal_pow hBpos.le] at h
    exact h
  have hsub : ENNReal.ofReal (B ^ 2 / 2)
      ≤ ((νn n : Measure K) {y : K | ‖((y : K) : ℂ) - ((x : K) : ℂ)‖ < t}) ^ 2
        - ((n : ENNReal) + 1)⁻¹ := by
    have hof : ENNReal.ofReal (B ^ 2) - ENNReal.ofReal (B ^ 2 / 2)
        = ENNReal.ofReal (B ^ 2 / 2) := by
      rw [← ENNReal.ofReal_sub (B ^ 2) (by positivity : (0 : ℝ) ≤ B ^ 2 / 2)]
      congr 1; ring
    have h2 := tsub_le_tsub hX2 hnE
    rwa [hof] at h2
  have hLnn : (0 : ENNReal) ≤ ENNReal.ofReal (Real.log (D / (2 * t))) := zero_le
  have hfinal : ENNReal.ofReal (Real.log (D / (2 * t))) * ENNReal.ofReal (B ^ 2 / 2)
      ≤ MeasureTheory.lintegral ((νn n).prod (νn n))
          (fun z : K × K => ENNReal.ofReal
            (Real.log (D / ‖((z.1 : K) : ℂ) - ((z.2 : K) : ℂ)‖))) :=
    le_trans (mul_le_mul_of_nonneg_left hsub hLnn) hkb
  have hofL : ENNReal.ofReal (Real.log (D / (2 * t))) * ENNReal.ofReal (B ^ 2 / 2)
      = ENNReal.ofReal (Real.log (D / (2 * t)) * (B ^ 2 / 2)) :=
    (ENNReal.ofReal_mul hlogpos.le).symm
  have hle_final : ENNReal.ofReal (Real.log (D / (2 * t)) * (A ^ 2 / 8)) ≤ ENNReal.ofReal c := by
    have hB2 : B ^ 2 / 2 = A ^ 2 / 8 := by rw [hBdef]; ring
    rw [← hB2, ← hofL]
    exact hfinal.trans (hc n)
  have hypos : 0 < Real.log (D / (2 * t)) * (A ^ 2 / 8) := mul_pos hlogpos hA2pos
  have hlt : ENNReal.ofReal c
      < ENNReal.ofReal (Real.log (D / (2 * t)) * (A ^ 2 / 8)) :=
    (ENNReal.ofReal_lt_ofReal_iff hypos).mpr hkey
  exact absurd (hlt.trans_le hle_final) (lt_irrefl _)

end Commons.MeasureTheory