-- ⚠ IMPORT-CLASH WORKAROUND (session 123): verbatim copy of Submission.Commons.Analysis.GaussianMeasure.memLp_gauge_hermite_sum
-- with the import chain redirected so that the duplicate constant `toLp_norm_sq` of
-- `…bobkov_strong_nD` is not pulled into the same environment as
-- `…brascamp_lieb_truncated`.  Do not import both this file and the commons original.
import Mathlib
import Submission.HermiteProductMemLp

namespace Commons.Analysis.GaussianMeasure

open scoped BigOperators
open _root_.MeasureTheory

/-- A convex, balanced and absorbent subset of a finite-dimensional real normed space is a
neighbourhood of the origin: it contains a ball around `0`. -/
lemma exists_ball_subset_of_convex_absorbent_balanced {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {K : Set V} (hcvx : Convex ℝ K)
    (h0 : (0 : V) ∈ K) (habs : Absorbent ℝ K) (hbal : Balanced ℝ K) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball 0 δ ⊆ K := by
  -- Absorbency forces the affine span of `K` to be everything.
  have hspan : affineSpan ℝ K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, hrpos, hr⟩ := (habs x).exists_pos
    obtain ⟨y, hyK, hyx⟩ := Set.mem_smul_set.mp (hr r (le_abs_self r) rfl)
    have h1 : (0 : V) ∈ affineSpan ℝ K := mem_affineSpan ℝ h0
    have h2 : y ∈ affineSpan ℝ K := mem_affineSpan ℝ hyK
    have h := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ K) r h2 h1 h1
    rw [show r • (y -ᵥ (0 : V)) +ᵥ (0 : V) = x by rw [← hyx]; simp] at h
    exact h
  -- Hence (finite dimension) the interior is nonempty, and contains a ball.
  obtain ⟨x0, hx0⟩ := (Convex.interior_nonempty_iff_affineSpan_eq_top hcvx).mpr hspan
  rw [mem_interior_iff_mem_nhds] at hx0
  obtain ⟨δ1, hδ1, hball1⟩ := Metric.mem_nhds_iff.mp hx0
  -- Balancedness reflects this ball through the origin, and convexity centres it at `0`.
  have hball2 : Metric.ball (-x0) δ1 ⊆ K := by
    intro z hz
    have hz' : -z ∈ Metric.ball x0 δ1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] at hz
      rw [Metric.mem_ball, dist_eq_norm, show -z - x0 = -(z + x0) by abel, norm_neg]
      exact hz
    exact (hbal.neg_mem_iff (x := z)).mp (hball1 hz')
  refine ⟨δ1, hδ1, fun z hz => ?_⟩
  have hzmem : ‖z‖ < δ1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have h1 : x0 + z ∈ K := by
    apply hball1
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hzmem
  have h2 : -x0 + z ∈ K := by
    apply hball2
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hzmem
  have h3 : (1 / 2 : ℝ) • (x0 + z) + (1 / 2 : ℝ) • (-x0 + z) ∈ K :=
    hcvx h1 h2 (by norm_num) (by norm_num) (by norm_num)
  have he : (1 / 2 : ℝ) • (x0 + z) + (1 / 2 : ℝ) • (-x0 + z) = z := by module
  rwa [he] at h3

/-- For a convex, balanced and absorbent set in finite dimension the gauge is continuous and is
bounded by a multiple of the norm. -/
lemma exists_gauge_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {K : Set V} (hcvx : Convex ℝ K) (h0 : (0 : V) ∈ K)
    (habs : Absorbent ℝ K) (hbal : Balanced ℝ K) :
    ∃ M : ℝ, 0 < M ∧ Continuous (gauge K) ∧ ∀ y : V, gauge K y ≤ M * ‖y‖ := by
  obtain ⟨δ, hδ, hball⟩ := exists_ball_subset_of_convex_absorbent_balanced hcvx h0 habs hbal
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hnhds : K ∈ nhds (0 : V) := Metric.mem_nhds_iff.mpr ⟨δ, hδ, hball⟩
  refine ⟨2 / δ, by positivity, continuous_gauge hcvx hnhds, fun y => ?_⟩
  have hmono : gauge K y ≤ gauge (Metric.ball (0 : V) (δ / 2)) y :=
    gauge_mono (absorbent_ball_zero hδ2)
      (fun z hz => hball (Metric.ball_subset_ball (by linarith) hz)) y
  rw [gauge_ball hδ2.le] at hmono
  calc gauge K y ≤ ‖y‖ / (δ / 2) := hmono
    _ = (2 / δ) * ‖y‖ := by ring

/-- A bounded absorbent set has gauge dominating the norm. -/
lemma exists_norm_le_gauge {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {K : Set V}
    (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : V, c * ‖y‖ ≤ gauge K y := by
  obtain ⟨r, hr⟩ := (NormedSpace.isVonNBounded_iff' ℝ).mp hbdd
  refine ⟨1 / max r 1, by positivity, fun y => ?_⟩
  have hmax : 0 < max r 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : K ⊆ Metric.closedBall (0 : V) (max r 1) := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hr x hx).trans (le_max_left _ _)
  have h := le_gauge_of_subset_closedBall habs hmax.le hsub (x := y)
  calc (1 / max r 1) * ‖y‖ = ‖y‖ / max r 1 := by ring
    _ ≤ gauge K y := h

/-- For a convex, balanced, absorbent and bounded set in finite dimension, the gauge is
comparable to the ambient norm. -/
lemma exists_gauge_comparable_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {K : Set V} (hcvx : Convex ℝ K) (h0 : (0 : V) ∈ K)
    (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ y : V, c * ‖y‖ ≤ gauge K y ∧ gauge K y ≤ C * ‖y‖ := by
  obtain ⟨C, hC, _, hle⟩ := exists_gauge_bound hcvx h0 habs hbal
  obtain ⟨c, hc, hge⟩ := exists_norm_le_gauge habs hbdd
  exact ⟨c, C, hc, hC, fun y => ⟨hge y, hle y⟩⟩

theorem memLp_gauge_hermite_sum {n N : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcvx : Convex ℝ K) (hK0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) (hKabs : Absorbent ℝ K)
    (hKbdd : Bornology.IsVonNBounded ℝ K) (hKbal : Balanced ℝ K)
    (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.MemLp
      (fun x : EuclideanSpace ℝ (Fin N) =>
        gauge K (∑ α ∈ s, ((∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) • C α)))
      2 (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) := by
  classical
  -- von Neumann boundedness is not needed for this statement
  have _hbdd : Bornology.IsVonNBounded ℝ K := hKbdd
  -- the gauge is dominated by a multiple of the norm (and is continuous)
  obtain ⟨M, hMpos, hgauge_cont, hgauge_bound⟩ :=
    exists_gauge_bound hKcvx hK0 hKabs hKbal
  -- each Hermite monomial is in `L²` of the Gaussian measure
  have hφmem : ∀ α : Fin N → ℕ,
      MemLp (fun x : EuclideanSpace ℝ (Fin N) =>
        ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) 2
      (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) :=
    fun α => memLp_hermite_product α
  -- hence so is the finitely supported majorant
  have hG : MemLp (fun x : EuclideanSpace ℝ (Fin N) =>
      M * ∑ α ∈ s, ‖C α‖ * ‖(∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i)))‖) 2
      (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) := by
    refine (memLp_finsetSum (f := fun (α : Fin N → ℕ) (x : EuclideanSpace ℝ (Fin N)) =>
      ‖C α‖ * ‖(∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i)))‖) s ?_).const_mul M
    intro α _
    exact ((hφmem α).norm).const_mul ‖C α‖
  -- the vector-valued sum is continuous, hence the gauge applied to it is strongly measurable
  have hcontφ : ∀ α : Fin N → ℕ, Continuous (fun x : EuclideanSpace ℝ (Fin N) =>
      ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) := by
    intro α
    exact continuous_finsetProd Finset.univ (fun i _ =>
      (Polynomial.continuous_aeval (Polynomial.hermite (α i))).comp
        ((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin N => ℝ))))
  have hScont : Continuous (fun x : EuclideanSpace ℝ (Fin N) =>
      ∑ α ∈ s, (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) • C α) := by
    refine continuous_finsetSum s (fun α _ => ?_)
    exact (hcontφ α).smul continuous_const
  have hmeas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin N) =>
      gauge K (∑ α ∈ s, (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) • C α))
      (MeasureTheory.volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) :=
    (hgauge_cont.comp hScont).aestronglyMeasurable
  -- it remains to compare pointwise with the majorant
  refine MemLp.of_le hG hmeas (Filter.Eventually.of_forall fun x => ?_)
  have hSbound : ‖∑ α ∈ s, (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) • C α‖
      ≤ ∑ α ∈ s, ‖C α‖ * ‖(∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i)))‖ := by
    refine (norm_sum_le s _).trans ?_
    apply Finset.sum_le_sum
    intro α _
    rw [norm_smul]
    exact le_of_eq (mul_comm _ _)
  rw [Real.norm_of_nonneg (gauge_nonneg _), Real.norm_of_nonneg (by positivity)]
  calc gauge K (∑ α ∈ s, (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) • C α)
      ≤ M * ‖∑ α ∈ s, (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) • C α‖ :=
        hgauge_bound _
    _ ≤ M * ∑ α ∈ s, ‖C α‖ * ‖(∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i)))‖ := by
        gcongr

end Commons.Analysis.GaussianMeasure
