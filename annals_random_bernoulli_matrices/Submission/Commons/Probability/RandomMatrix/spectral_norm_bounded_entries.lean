import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas
import Submission.Commons.Topology.MetricSpace.sphere_net_cardinality

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal

namespace Commons.Probability.RandomMatrix

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma abs_inner_le_of_opNorm (T : H →L[ℝ] H) (x y : H) :
    |inner ℝ (T x) y| ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  have h1 : |inner ℝ (T x) y| ≤ ‖T x‖ * ‖y‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (T x) y
  calc
    |inner ℝ (T x) y| ≤ ‖T x‖ * ‖y‖ := h1
    _ ≤ (‖T‖ * ‖x‖) * ‖y‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm T x
    _ = ‖T‖ * ‖x‖ * ‖y‖ := by ring

lemma norm_le_of_forall_unit_inner_le (v : H) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ y : H, ‖y‖ = 1 → |inner ℝ v y| ≤ B) : ‖v‖ ≤ B := by
  by_cases hv : v = 0
  · simpa [hv] using hB
  · let y : H := (‖v‖)⁻¹ • v
    have hnorm0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hy : ‖y‖ = 1 := by
      dsimp [y]
      rw [norm_smul]
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
      exact inv_mul_cancel₀ hnorm0
    have hin : inner ℝ v y = ‖v‖ := by
      dsimp [y]
      rw [real_inner_smul_right]
      rw [real_inner_self_eq_norm_sq]
      field_simp [hnorm0]
    have habs : |inner ℝ v y| = ‖v‖ := by
      rw [hin]
      exact abs_of_nonneg (norm_nonneg v)
    linarith [h y hy]

lemma opNorm_le_of_forall_unit_inner_le (T : H →L[ℝ] H) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ ⦃x y : H⦄, ‖x‖ = 1 → ‖y‖ = 1 → |inner ℝ (T x) y| ≤ B) : ‖T‖ ≤ B := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (f := T) hB ?_
  intro x hx
  exact norm_le_of_forall_unit_inner_le (T x) hB (fun y hy => h hx hy)

end Hilbert


variable {n : ℕ}
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

noncomputable def Kp (K : ℝ) : ℝ≥0 := (‖(K - (-K) : ℝ)‖₊ / 2) ^ 2

lemma Kp_coe (K : ℝ) (hK : 0 ≤ K) : ((Kp K) : ℝ) = K ^ 2 := by
  unfold Kp
  rw [NNReal.coe_pow, NNReal.coe_div]
  have hn : ((‖(K - (-K) : ℝ)‖₊ : ℝ≥0) : ℝ) = 2 * K := by
    have hc : ((‖(K - (-K) : ℝ)‖₊ : ℝ≥0) : ℝ) = ‖(K - (-K) : ℝ)‖ := by simp
    rw [hc, Real.norm_eq_abs]
    have hring : (K - (-K) : ℝ) = 2 * K := by ring
    rw [hring, abs_of_nonneg (mul_nonneg two_pos.le hK)]
  rw [hn]
  norm_num

/-! ### coordinates -/
lemma clm_apply_ofLp (A : M n) (x : E n) :
    (((A.toEuclideanLin).toContinuousLinearMap) x).ofLp = A *ᵥ x.ofLp := by
  change (A.toEuclideanLin x).ofLp = A *ᵥ x.ofLp
  rw [Matrix.toEuclideanLin_apply]

lemma inner_clm_apply (A : M n) (u v : E n) :
    inner ℝ ((((A.toEuclideanLin).toContinuousLinearMap) u)) v
      = ∑ i : Fin n, (∑ j : Fin n, A i j * u.ofLp j) * v.ofLp i := by
  rw [PiLp.inner_apply]
  simp only [clm_apply_ofLp, Matrix.mulVec_apply_eq_sum]
  congr 1
  ext i
  simp [inner, mul_comm, mul_left_comm, mul_assoc]

lemma sq_norm_ofLp (u : E n) : ‖u‖ ^ 2 = ∑ i : Fin n, (u.ofLp i) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [sq]

lemma sum_sq_of_norm_eq_one {u : E n} (hu : ‖u‖ = 1) : ∑ i : Fin n, (u.ofLp i) ^ 2 = 1 := by
  nlinarith [sq_norm_ofLp u]

lemma pair_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ) :
    (∑ p : ι × κ, f p.1 p.2) = ∑ i : ι, ∑ j : κ, f i j := by
  classical
  rw [show (Finset.univ : Finset (ι × κ)) = (Finset.univ : Finset ι).product (Finset.univ : Finset κ) by simp]
  simpa using (Finset.sum_product (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset κ))
    (f := fun p : ι × κ => f p.1 p.2))

lemma sq_mul_sum_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (u : κ → ℝ) (v : ι → ℝ) :
    (∑ p : ι × κ, ((u p.2) * (v p.1)) ^ 2) = (∑ j : κ, (u j) ^ 2) * (∑ i : ι, (v i) ^ 2) := by
  classical
  calc
    (∑ p : ι × κ, ((u p.2) * (v p.1)) ^ 2)
        = ∑ p : ι × κ, (u p.2) ^ 2 * (v p.1) ^ 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = ∑ i : ι, ∑ j : κ, (u j) ^ 2 * (v i) ^ 2 := by
          rw [pair_sum (f := fun i j => (u j) ^ 2 * (v i) ^ 2)]
    _ = ∑ i : ι, ((∑ j : κ, (u j) ^ 2) * (v i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_mul]
    _ = (∑ j : κ, (u j) ^ 2) * ∑ i : ι, (v i) ^ 2 := by
          rw [← Finset.mul_sum]

/-! ### two-sided Hoeffding for independent subgaussians -/
lemma abs_sum_tail {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (c : ι → ℝ≥0) (h_subG : ∀ i, ProbabilityTheory.HasSubgaussianMGF (X i) (c i) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i, X i ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * (((∑ i, c i) : ℝ≥0) : ℝ))) := by
  classical
  let e : ℝ := Real.exp (-ε ^ 2 / (2 * (((∑ i, c i) : ℝ≥0) : ℝ)))
  have h1 : μ.real {ω | ε ≤ ∑ i, X i ω} ≤ e := by
    simpa [e] using (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep
      (s := Finset.univ) (fun i hi => h_subG i) hε)
  let Xn : ι → Ω → ℝ := fun i ω => -X i ω
  have h_indep_n : ProbabilityTheory.iIndepFun Xn μ := by
    refine h_indep.comp (fun i => fun x : ℝ => -x) (fun i => ?_)
    fun_prop
  have h_subG_n : ∀ i, ProbabilityTheory.HasSubgaussianMGF (Xn i) (c i) μ := fun i => (h_subG i).neg
  have h2 : μ.real {ω | ε ≤ ∑ i, Xn i ω} ≤ e := by
    simpa [e, Xn] using (ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep_n
      (s := Finset.univ) (fun i hi => h_subG_n i) hε)
  calc
    μ.real {ω | ε ≤ |∑ i, X i ω|}
        ≤ μ.real ({ω | ε ≤ ∑ i, X i ω} ∪ {ω | ε ≤ ∑ i, Xn i ω}) := by
          refine MeasureTheory.measureReal_mono ?_
          intro ω hω
          simp only [Set.mem_union, Set.mem_setOf_eq]
          by_cases hS : 0 ≤ ∑ i, X i ω
          · left
            exact hω.trans_eq (abs_of_nonneg hS)
          · right
            have hSneg : (∑ i, X i ω) < 0 := lt_of_not_ge hS
            have h2' : ε ≤ -∑ i, X i ω := by
              simpa [abs_of_neg hSneg] using hω
            simpa [Xn] using h2'
    _ ≤ μ.real {ω | ε ≤ ∑ i, X i ω} + μ.real {ω | ε ≤ ∑ i, Xn i ω} := by
          exact MeasureTheory.measureReal_union_le _ _
    _ ≤ e + e := add_le_add h1 h2
    _ = 2 * e := by ring

/-! ### Hoeffding per entry -/
lemma entry_subG {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ ω, |X ω| ≤ K) (hc : ∫ ω, X ω ∂P = 0) :
    ProbabilityTheory.HasSubgaussianMGF X (Kp K) P := by
  apply ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (a := -K) (b := K)
  · exact hX.aemeasurable
  · filter_upwards with ω
    simpa [Set.mem_Icc] using (abs_le.mp (hb ω))
  · exact hc

/-! ### Bilinear-form tail for a random matrix with bounded independent centered entries -/
lemma bilin_tail (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : Ω → M n)
    (hmeas : ∀ i j : Fin n, Measurable (fun ω => A ω i j))
    (hind : ProbabilityTheory.iIndepFun (fun ij : Fin n × Fin n => (A · ij.1 ij.2)) P)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ i j ω, |A ω i j| ≤ K)
    (hmean : ∀ i j : Fin n, ∫ ω, A ω i j ∂P = 0)
    (u v : E n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    P.real {ω | θ < |inner ℝ (((A ω).toEuclideanLin).toContinuousLinearMap u) v|}
      ≤ 2 * Real.exp (-θ ^ 2 / (2 * K ^ 2)) := by
  classical
  let r : Fin n × Fin n → ℝ := fun p => u.ofLp p.2 * v.ofLp p.1
  let Y : Fin n × Fin n → Ω → ℝ := fun p ω => r p * A ω p.1 p.2
  let c : Fin n × Fin n → ℝ≥0 := fun p => Kp (K * |r p|)
  have hYind : ProbabilityTheory.iIndepFun Y P := by
    refine hind.comp (fun p => fun x : ℝ => r p * x) (fun p => ?_)
    fun_prop
  have hsubY : ∀ p : Fin n × Fin n, ProbabilityTheory.HasSubgaussianMGF (Y p) (c p) P := by
    intro p
    dsimp [Y, c]
    exact entry_subG P (fun ω => r p * A ω p.1 p.2)
      (by fun_prop)
      (K * |r p|) (mul_nonneg hK (abs_nonneg (r p)))
      (by intro ω; simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left (hb p.1 p.2 ω) (abs_nonneg (r p)))
      (by rw [integral_const_mul, hmean p.1 p.2]; ring)
  have hsum_sq : (∑ p : Fin n × Fin n, (r p) ^ 2) = 1 := by
    calc
      (∑ p : Fin n × Fin n, (r p) ^ 2)
          = (∑ j : Fin n, (u.ofLp j) ^ 2) * (∑ i : Fin n, (v.ofLp i) ^ 2) := by
            simpa [r] using sq_mul_sum_eq (ι := Fin n) (κ := Fin n) (u := u.ofLp) (v := v.ofLp)
      _ = 1 := by rw [sum_sq_of_norm_eq_one hu, sum_sq_of_norm_eq_one hv]; ring
  have hcoe : (((∑ p : Fin n × Fin n, c p) : ℝ≥0) : ℝ) = K ^ 2 := by
    calc
      (((∑ p : Fin n × Fin n, c p) : ℝ≥0) : ℝ)
          = ∑ p : Fin n × Fin n, (c p : ℝ) := by
            rw [NNReal.coe_sum]
      _ = ∑ p : Fin n × Fin n, (K * |r p|) ^ 2 := by
            apply Finset.sum_congr rfl
            intro p hp
            simp only [c]
            exact Kp_coe (K * |r p|) (mul_nonneg hK (abs_nonneg (r p)))
      _ = K ^ 2 * ∑ p : Fin n × Fin n, (r p) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            rw [mul_pow]
            congr 1
            exact sq_abs (r p)
      _ = K ^ 2 := by rw [hsum_sq]; ring
  have htail' : P.real {ω | θ ≤ |∑ p : Fin n × Fin n, Y p ω|}
      ≤ 2 * Real.exp (-θ ^ 2 / (2 * K ^ 2)) := by
    have ht := abs_sum_tail P Y hYind c hsubY hθ
    have harg : (2 * ((((∑ p : Fin n × Fin n, c p) : ℝ≥0) : ℝ))) = 2 * K ^ 2 := by
      rw [hcoe]
    calc
      P.real {ω | θ ≤ |∑ p : Fin n × Fin n, Y p ω|}
          ≤ 2 * Real.exp (-θ ^ 2 / (2 * ((((∑ p : Fin n × Fin n, c p) : ℝ≥0) : ℝ)))) := ht
      _ = 2 * Real.exp (-θ ^ 2 / (2 * K ^ 2)) := by rw [harg]
  have hmem : {ω | θ < |inner ℝ (((A ω).toEuclideanLin).toContinuousLinearMap u) v|}
      ⊆ {ω | θ ≤ |∑ p : Fin n × Fin n, Y p ω|} := by
    intro ω hω
    dsimp at hω ⊢
    have hL : inner ℝ (((A ω).toEuclideanLin).toContinuousLinearMap u) v
        = ∑ i : Fin n, ∑ j : Fin n, (A ω i j * u.ofLp j) * v.ofLp i := by
      rw [inner_clm_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
    have hR : (∑ p : Fin n × Fin n, Y p ω)
        = ∑ i : Fin n, ∑ j : Fin n, (u.ofLp j * v.ofLp i) * A ω i j := by
      simp only [Y, r]
      rw [pair_sum (f := fun i j : Fin n => (u.ofLp j * v.ofLp i) * A ω i j)]
    have heq : inner ℝ (((A ω).toEuclideanLin).toContinuousLinearMap u) v = ∑ p : Fin n × Fin n, Y p ω := by
      calc
        inner ℝ (((A ω).toEuclideanLin).toContinuousLinearMap u) v
            = ∑ i : Fin n, ∑ j : Fin n, (A ω i j * u.ofLp j) * v.ofLp i := hL
        _ = ∑ i : Fin n, ∑ j : Fin n, (u.ofLp j * v.ofLp i) * A ω i j := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = ∑ p : Fin n × Fin n, Y p ω := hR.symm
    exact le_of_lt (by rw [← heq]; exact hω)
  exact (MeasureTheory.measureReal_mono hmem).trans htail'

/-! ### Net argument: spectral norm bounded by max over a finite δ-net of bilinear values -/
lemma opNorm_le_of_net (n : ℕ) {δ θ : ℝ} (hδ0 : 0 ≤ δ) (h2δ : 2 * δ < 1) (hθ : 0 ≤ θ)
    (S : Finset (E n)) (hSunit : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : E n, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ δ)
    (T : E n →L[ℝ] E n)
    (hnet : ∀ p ∈ S.product S, |inner ℝ (T p.1) p.2| ≤ (1 - 2 * δ) * θ) :
    ‖T‖ ≤ θ := by
  classical
  have hγpos : 0 < 1 - 2 * δ := by linarith
  have hpair : ∀ ⦃x y : E n⦄, ‖x‖ = 1 → ‖y‖ = 1 →
      |inner ℝ (T x) y| ≤ (1 - 2 * δ) * θ + 2 * δ * ‖T‖ := by
    intro x y hx hy
    rcases hcover x hx with ⟨x0, hxS, hxx0⟩
    rcases hcover y hy with ⟨y0, hyS, hyy0⟩
    have hx0y0 : |inner ℝ (T x0) y0| ≤ (1 - 2 * δ) * θ := by
      exact hnet (x0, y0) (by simp [hxS, hyS])
    have hcx : |inner ℝ (T x0) (y - y0)| ≤ ‖T‖ * δ := by
      have h := abs_inner_le_of_opNorm T x0 (y - y0)
      have hx01 : ‖x0‖ = 1 := hSunit x0 hxS
      have hb : ‖T‖ * ‖x0‖ * ‖y - y0‖ ≤ ‖T‖ * 1 * δ := by
        rw [hx01]
        nlinarith [mul_le_mul_of_nonneg_left hyy0 (norm_nonneg T)]
      nlinarith [h.trans hb]
    have hdy : |inner ℝ (T (x - x0)) y| ≤ ‖T‖ * δ := by
      have h := abs_inner_le_of_opNorm T (x - x0) y
      have hb : ‖T‖ * ‖x - x0‖ * ‖y‖ ≤ ‖T‖ * δ * 1 := by
        rw [hy]
        nlinarith [mul_le_mul_of_nonneg_left hxx0 (norm_nonneg T)]
      nlinarith [h.trans hb]
    have hident : inner ℝ (T x) y
        = inner ℝ (T x0) y0 + inner ℝ (T x0) (y - y0) + inner ℝ (T (x - x0)) y := by
      calc
        inner ℝ (T x) y = inner ℝ (T (x0 + (x - x0))) y := by rw [show x0 + (x - x0) = x by abel]
        _ = inner ℝ (T x0 + T (x - x0)) y := by rw [map_add]
        _ = inner ℝ (T x0) y + inner ℝ (T (x - x0)) y := by rw [inner_add_left]
        _ = inner ℝ (T x0) (y0 + (y - y0)) + inner ℝ (T (x - x0)) y := by
              rw [show y0 + (y - y0) = y by abel]
        _ = (inner ℝ (T x0) y0 + inner ℝ (T x0) (y - y0)) + inner ℝ (T (x - x0)) y := by
              rw [inner_add_right]
        _ = inner ℝ (T x0) y0 + inner ℝ (T x0) (y - y0) + inner ℝ (T (x - x0)) y := by ring
    have htri : |inner ℝ (T x) y| ≤ |inner ℝ (T x0) y0| + |inner ℝ (T x0) (y - y0)|
        + |inner ℝ (T (x - x0)) y| := by
      rw [hident]
      calc
        |(inner ℝ (T x0) y0 + inner ℝ (T x0) (y - y0)) + inner ℝ (T (x - x0)) y|
            ≤ |inner ℝ (T x0) y0 + inner ℝ (T x0) (y - y0)| + |inner ℝ (T (x - x0)) y| :=
              abs_add_le (inner ℝ (T x0) y0 + inner ℝ (T x0) (y - y0)) (inner ℝ (T (x - x0)) y)
        _ ≤ (|inner ℝ (T x0) y0| + |inner ℝ (T x0) (y - y0)|) + |inner ℝ (T (x - x0)) y| := by
              exact add_le_add (abs_add_le (inner ℝ (T x0) y0) (inner ℝ (T x0) (y - y0))) le_rfl
        _ = |inner ℝ (T x0) y0| + |inner ℝ (T x0) (y - y0)| + |inner ℝ (T (x - x0)) y| := by ring
    calc
      |inner ℝ (T x) y| ≤ |inner ℝ (T x0) y0| + |inner ℝ (T x0) (y - y0)|
          + |inner ℝ (T (x - x0)) y| := htri
      _ ≤ (1 - 2 * δ) * θ + ‖T‖ * δ + ‖T‖ * δ := by
            exact add_le_add (add_le_add hx0y0 hcx) hdy
      _ = (1 - 2 * δ) * θ + 2 * δ * ‖T‖ := by ring
  have hB : 0 ≤ (1 - 2 * δ) * θ + 2 * δ * ‖T‖ := by
    positivity
  have hdu := opNorm_le_of_forall_unit_inner_le (T) hB (fun ⦃x y⦄ hx hy => hpair hx hy)
  nlinarith

lemma net_event_subset (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    {δ θ : ℝ} (hδ0 : 0 ≤ δ) (h2δ : 2 * δ < 1) (hθ : 0 ≤ θ)
    (S : Finset (E n)) (hSunit : ∀ x ∈ S, ‖x‖ = 1)
    (hcover : ∀ y : E n, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ δ)
    (T : Ω → E n →L[ℝ] E n) :
    {ω : Ω | ‖T ω‖ > θ} ⊆
      ⋃ p ∈ S.product S, {ω : Ω | |inner ℝ (T ω p.1) p.2| > (1 - 2 * δ) * θ} := by
  classical
  intro ω hω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hω ⊢
  by_contra hn
  push_neg at hn
  have hle : ‖T ω‖ ≤ θ := by
    apply opNorm_le_of_net n hδ0 h2δ hθ S hSunit hcover (T ω)
    exact fun p hp => hn p hp
  exact hle.not_gt hω

/-! ### Measure-level net tail (finite net) -/
lemma measure_norm_tail (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : Ω → M n)
    (hmeas : ∀ i j : Fin n, Measurable (fun ω => A ω i j))
    (hind : ProbabilityTheory.iIndepFun (fun ij : Fin n × Fin n => (A · ij.1 ij.2)) P)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ i j ω, |A ω i j| ≤ K)
    (hmean : ∀ i j : Fin n, ∫ ω, A ω i j ∂P = 0)
    {δ θ : ℝ} (hδ0 : 0 < δ) (h2δ : 2 * δ < 1) (hθ : 0 ≤ θ)
    (S : Set (E n)) (hSfin : S.Finite) (hSun : ∀ x ∈ S, ‖x‖ = 1)
    (hScover : ∀ y : E n, ‖y‖ = 1 → ∃ x ∈ S, ‖y - x‖ ≤ δ) :
    P.real {ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > θ}
      ≤ (S.ncard : ℝ) ^ 2 * (2 * Real.exp (-((1 - 2 * δ) ^ 2 * θ ^ 2) / (2 * K ^ 2))) := by
  classical
  let T : Ω → E n →L[ℝ] E n := fun ω => ((A ω).toEuclideanLin).toContinuousLinearMap
  let Sf : Finset (E n) := hSfin.toFinset
  let G : E n × E n → Set Ω := fun p => {ω | (1 - 2 * δ) * θ < |inner ℝ (T ω p.1) p.2|}
  have hSfunit : ∀ x ∈ Sf, ‖x‖ = 1 := by
    intro x hx
    exact hSun x (by simpa [Sf] using hx)
  have hSfcover : ∀ y : E n, ‖y‖ = 1 → ∃ x ∈ Sf, ‖y - x‖ ≤ δ := by
    intro y hy
    rcases hScover y hy with ⟨x, hxS, hxy⟩
    refine ⟨x, ?_, hxy⟩
    simpa [Sf] using hxS
  have hinc : {ω | ‖T ω‖ > θ} ⊆ ⋃ p ∈ Sf.product Sf, G p :=
    net_event_subset n hδ0.le h2δ hθ Sf hSfunit hSfcover T
  have hbig : P.real {ω | ‖T ω‖ > θ} ≤ P.real (⋃ p ∈ Sf.product Sf, G p) := by
    exact MeasureTheory.measureReal_mono hinc (measure_ne_top P _)
  let e : ℝ := Real.exp (-((1 - 2 * δ) ^ 2 * θ ^ 2) / (2 * K ^ 2))
  have hpair : ∀ p ∈ Sf.product Sf, P.real (G p) ≤ 2 * e := by
    intro p hp
    have hp1 : ‖p.1‖ = 1 := hSfunit p.1 ((Finset.mem_product.mp hp).1)
    have hp2 : ‖p.2‖ = 1 := hSfunit p.2 ((Finset.mem_product.mp hp).2)
    have hθγ : 0 ≤ (1 - 2 * δ) * θ := mul_nonneg (sub_nonneg.mpr (le_of_lt h2δ)) hθ
    have ht := bilin_tail n P A hmeas hind hK hb hmean p.1 p.2 hp1 hp2 hθγ
    have hpow : ((1 - 2 * δ) * θ) ^ 2 = (1 - 2 * δ) ^ 2 * θ ^ 2 := by ring
    simpa [e, G, T, hpow] using ht
  calc
    P.real {ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > θ}
        ≤ P.real {ω | ‖T ω‖ > θ} := by simpa [T]
    _ ≤ P.real (⋃ p ∈ Sf.product Sf, G p) := hbig
    _ ≤ ∑ p ∈ Sf.product Sf, P.real (G p) := MeasureTheory.measureReal_biUnion_finset_le _ _
    _ ≤ ∑ p ∈ Sf.product Sf, (2 * e) := Finset.sum_le_sum hpair
    _ = ((Sf.product Sf).card : ℝ) * (2 * e) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (S.ncard : ℝ) ^ 2 * (2 * e) := by
          have hc : ((Sf.product Sf).card : ℝ) = (S.ncard : ℝ) ^ 2 := by
            simp [Sf, Finset.card_product]
            rw [← Set.ncard_eq_toFinset_card S hSfin]
            ring
          rw [hc]
    _ = (S.ncard : ℝ) ^ 2 * (2 * Real.exp (-((1 - 2 * δ) ^ 2 * θ ^ 2) / (2 * K ^ 2))) := by rfl

/-! ### Exponential bound helper -/
lemma exp_bound_final {a r L t : ℝ} (ha1 : 1 ≤ a) (ht : 1 ≤ t)
    (hmain : L + 2 * Real.log a + Real.log 2 ≤ r) :
    2 * Real.exp (2 * t * Real.log a) * Real.exp (-r * t) ≤ Real.exp (-L * t) := by
  have hlog2 : 0 ≤ Real.log 2 := by positivity
  have hineq : Real.log 2 + 2 * t * Real.log a - r * t ≤ -L * t := by
    nlinarith [mul_le_mul_of_nonneg_right hmain (by positivity : 0 ≤ t),
      mul_le_mul_of_nonneg_left ht hlog2]
  have h2e : ∀ X : ℝ, 2 * Real.exp X = Real.exp (Real.log 2 + X) := by
    intro X
    calc
      2 * Real.exp X = Real.exp (Real.log 2) * Real.exp X := by
            conv_lhs => rw [← Real.exp_log (by norm_num : 0 < (2 : ℝ))]
      _ = Real.exp (Real.log 2 + X) := by rw [← Real.exp_add]
  calc
    2 * Real.exp (2 * t * Real.log a) * Real.exp (-r * t)
        = 2 * Real.exp (2 * t * Real.log a + -r * t) := by
            rw [mul_assoc, ← Real.exp_add]
    _ = Real.exp (Real.log 2 + (2 * t * Real.log a + -r * t)) := by
            rw [h2e]
    _ ≤ Real.exp (-L * t) := by
          exact Real.exp_le_exp.mpr (by nlinarith [hineq])

/-! ### Final theorem -/
theorem spectral_norm_bounded_entries :
    ∀ (L : ℝ), 1 ≤ L → ∀ (K : ℝ), 1 ≤ K →
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (A : Ω → Matrix (Fin n) (Fin n) ℝ),
          (∀ i j : Fin n, Measurable (fun ω => A ω i j)) →
          (ProbabilityTheory.iIndepFun (fun ij : Fin n × Fin n => (A · ij.1 ij.2)) P) →
          (∀ (i j : Fin n) (ω : Ω), |A ω i j| ≤ K) →
          (∀ i j : Fin n, ∫ ω, A ω i j ∂P = 0) →
          P.real {ω : Ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > C * K * Real.sqrt (n : ℝ)} ≤
            Real.exp (-L * (n : ℝ)) := by
  classical
  intro L hL1 K hK1
  obtain ⟨C1, hC1ge1, hnet⟩ := Commons.Topology.MetricSpace.sphere_net_cardinality
  let a : ℝ := 8 * C1
  let base : ℝ := L + 2 * Real.log a + Real.log 2
  let C2 : ℝ := Real.sqrt (max 1 ((32 / 9) * base))
  let r : ℝ := (9 / 32) * C2 ^ 2
  have hK0 : 0 ≤ K := by linarith
  have hapos : 0 < a := by dsimp [a]; nlinarith
  have ha1 : 1 ≤ a := by dsimp [a]; nlinarith
  have hmax0 : 0 ≤ max 1 ((32 / 9) * base) := le_trans zero_le_one (le_max_left _ _)
  have hC2sq : C2 ^ 2 = max 1 ((32 / 9) * base) := by
    dsimp [C2]
    rw [Real.sq_sqrt hmax0]
  have hC2ge1 : 1 ≤ C2 := by
    have hC2nn : 0 ≤ C2 := by dsimp [C2]; positivity
    have hsq1 : 1 ≤ C2 ^ 2 := by
      rw [hC2sq]
      exact le_max_left _ _
    nlinarith
  have hbase_r : base ≤ r := by
    have hstep : (9 / 32) * ((32 / 9) * base) = base := by ring
    calc
      base = (9 / 32) * ((32 / 9) * base) := by rw [hstep]
      _ ≤ (9 / 32) * max 1 ((32 / 9) * base) := by
            exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
      _ = r := by
            dsimp [r]
            rw [hC2sq]
  have hKne : K ≠ 0 := by linarith
  refine ⟨C2, hC2ge1, ?_⟩
  intro n Ω _ P _ A hmeas hind hb hmean
  by_cases hn0 : n = 0
  · subst n
    have huniv : P.real Set.univ = 1 := by simp [Measure.real]
    have hz : Real.exp (-L * ((0 : ℕ) : ℝ)) = 1 := by simp
    calc
      P.real {ω : Ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > C2 * K * Real.sqrt ((0 : ℕ) : ℝ)}
          ≤ P.real Set.univ := by
            exact MeasureTheory.measureReal_mono
              (s₁ := {ω : Ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > C2 * K * Real.sqrt ((0 : ℕ) : ℝ)})
              (s₂ := Set.univ) (by intro ω hω; trivial)
      _ = 1 := huniv
      _ = Real.exp (-L * ((0 : ℕ) : ℝ)) := hz.symm
  · have hn1 : 1 ≤ n := by omega
    let t : ℝ := (n : ℝ)
    have ht1 : 1 ≤ t := by
      dsimp [t]
      exact_mod_cast hn1
    let θ : ℝ := C2 * K * Real.sqrt (n : ℝ)
    have hθ0 : 0 ≤ θ := by
      dsimp [θ]
      positivity
    obtain ⟨S, hSfin, hSun, hScover, hSbound⟩ := hnet n (1 / 8) (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
    have htail := measure_norm_tail n P A hmeas hind hK0 hb hmean (δ := (1 / 8)) (θ := θ)
      (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (2 : ℝ) * (1 / 8) < 1) hθ0
      S hSfin hSun hScover
    have hδnet : C1 / (1 / 8) = a := by
      dsimp [a]
      field_simp
    have hS1 : (S.ncard : ℝ) ≤ a ^ n := by
      calc
        (S.ncard : ℝ) ≤ (C1 / (1 / 8)) ^ n := hSbound
        _ = a ^ n := by rw [hδnet]
    have hSsq : (S.ncard : ℝ) ^ 2 ≤ a ^ (2 * n) := by
      have hSnn : 0 ≤ (S.ncard : ℝ) := by exact_mod_cast Nat.zero_le _
      have hapow0 : 0 ≤ a ^ n := pow_nonneg (le_of_lt hapos) n
      have h2 := mul_le_mul hS1 hS1 hSnn hapow0
      have hpow : (a ^ n) ^ 2 = a ^ (2 * n) := by
        rw [← pow_mul]
        congr 1
        omega
      calc
        (S.ncard : ℝ) ^ 2 ≤ a ^ n * a ^ n := by simpa [pow_two] using h2
        _ = a ^ (2 * n) := by simpa [pow_two] using hpow
    have h2e : 0 ≤ 2 * Real.exp (-((1 - 2 * (1 / 8)) ^ 2 * θ ^ 2) / (2 * K ^ 2)) := by
      positivity
    have htail2 : P.real {ω : Ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > θ}
        ≤ a ^ (2 * n) * (2 * Real.exp (-((1 - 2 * (1 / 8)) ^ 2 * θ ^ 2) / (2 * K ^ 2))) := by
      exact htail.trans (mul_le_mul_of_nonneg_right hSsq h2e)
    have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
      exact Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))
    have hexp : -((1 - 2 * (1 / 8)) ^ 2 * θ ^ 2) / (2 * K ^ 2) = -r * t := by
      dsimp [θ, r, t]
      rw [show (C2 * K * Real.sqrt (n : ℝ)) ^ 2 = C2 ^ 2 * K ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 by ring]
      rw [hsqrt]
      field_simp [hKne]
      ring
    have hpow_exp : a ^ (2 * n) = Real.exp (2 * t * Real.log a) := by
      rw [← Real.exp_log (pow_pos hapos (2 * n))]
      congr 1
      have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by
        rw [Nat.cast_mul]
        norm_num
      dsimp [t]
      rw [Real.log_pow, hcast]
    have hmain2 : P.real {ω : Ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > θ}
        ≤ Real.exp (-L * (n : ℝ)) := by
      calc
        P.real {ω : Ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > θ}
            ≤ a ^ (2 * n) * (2 * Real.exp (-((1 - 2 * (1 / 8)) ^ 2 * θ ^ 2) / (2 * K ^ 2))) := htail2
        _ = a ^ (2 * n) * (2 * Real.exp (-r * t)) := by rw [hexp]
        _ = 2 * Real.exp (2 * t * Real.log a) * Real.exp (-r * t) := by
              calc
                a ^ (2 * n) * (2 * Real.exp (-r * t)) = 2 * (a ^ (2 * n) * Real.exp (-r * t)) := by ring
                _ = 2 * Real.exp (2 * t * Real.log a) * Real.exp (-r * t) := by
                      rw [hpow_exp]
                      ring
        _ ≤ Real.exp (-L * t) := exp_bound_final (a := a) (r := r) (L := L) (t := t) ha1 ht1 hbase_r
        _ = Real.exp (-L * (n : ℝ)) := by dsimp [t]
    have hev : {ω : Ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > C2 * K * Real.sqrt (n : ℝ)}
        = {ω : Ω | ‖((A ω).toEuclideanLin).toContinuousLinearMap‖ > θ} := by
      simpa [θ]
    rw [hev]
    exact hmain2

end Commons.Probability.RandomMatrix