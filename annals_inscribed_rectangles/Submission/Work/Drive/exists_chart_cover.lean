import Mathlib
import Submission.Work.Drive.ChartData
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.exists_local_normalForm
import Submission.Work.Drive.exists_face_index
import Submission.Work.Drive.flowField_on_box
import Submission.Work.Drive.interior_unitBox
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.cofactorVec_apply_ne_zero
import Submission.Work.Drive.ker_eq_span_cofactorVec
import Submission.Work.Drive.contDiff_cofactorVectorF

/-!
# The zero set of `F` is covered by finitely many chart regions

`Work.Drive.exists_chart_cover`: a smooth `F : ℝ^{m+1} → ℝ^m` whose zeros on the unit box are
regular (`hreg`) has its zero set in the box covered by finitely many `ChartData` regions.

The proof has two halves.

* **Pointwise.**  Given a zero `p` of `F` in the box, `exists_face_index` picks a coordinate `i`
  such that `fderiv ℝ F p` is still surjective on the hyperplane `{v | v i = 0}`; the implicit
  function theorem in the form `exists_local_normalForm` then writes the zero set near `p` as a
  graph `u ↦ u • eᵢ + η u`.  The `i`-th cofactor of `fderiv ℝ F p` is then nonzero
  (`cofactorVec_apply_ne_zero`), so by continuity of `cofactorVectorF F` the `i`-th component of
  `flowField F` is bounded below by a positive constant `c` on a ball around `p`
  (`exists_flowField_lower_bound`); shrinking `δ` and `ρ` so that the chart region sits inside that
  ball produces a `ChartData F p` whose region contains `p`.
* **Compactness.**  The regions are open and cover the zero set pointwise, and `zeroSet F` is
  compact, so finitely many of them suffice.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-- A point of the unit box has norm at most `√(m+1)`. -/
theorem norm_le_sqrt_of_mem_unitBox {m : ℕ} {x : Amb m}
    (hx : x ∈ Submission.Drive.unitBox m) : ‖x‖ ≤ Real.sqrt ((m : ℝ) + 1) := by
  have hnorm2 : ‖x‖ ^ 2 ≤ ((m : ℝ) + 1) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i : Fin (m + 1), x i ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 := (hx i).1
          have h2 := (hx i).2
          nlinarith
      _ = ((m : ℝ) + 1) := by simp
  calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_le_sqrt hnorm2

/-- The bump `boxBump m` is still `1` at every point within distance `1/2` of the unit box. -/
theorem boxBump_eq_one_of_near_unitBox {m : ℕ} {p x : Amb m}
    (hp : p ∈ Submission.Drive.unitBox m) (hpx : ‖x - p‖ < 1 / 2) : boxBump m x = 1 := by
  have hp' := norm_le_sqrt_of_mem_unitBox hp
  have hxn : ‖x‖ ≤ Real.sqrt ((m : ℝ) + 1) + 1 := by
    have h1 : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by
      calc ‖x‖ = ‖(x - p) + p‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - p‖ + ‖p‖ := norm_add_le _ _
    linarith
  have hbump : (⟨Real.sqrt (m + 1) + 1, Real.sqrt (m + 1) + 2, by positivity,
      by linarith⟩ : ContDiffBump (0 : Amb m)) x = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  simpa [boxBump] using hbump

/-- **A positive lower bound for the `i`-th component of the flow field near a regular zero.**
If the `i`-th cofactor of `fderiv ℝ F p` does not vanish at a point `p` of the unit box, then
`|flowField F x i|` is bounded below by a positive constant on a ball around `p`.

Indeed `flowField F x i` is `boxBump m x` times a positive multiple of
`cofactorVectorF F x i`; near `p` the bump is `1` (because `p` is in the box, so a `1/2`-ball around
`p` lies well inside the inner radius of the bump) and `cofactorVectorF F x i` stays away from `0`
by continuity. -/
theorem exists_flowField_lower_bound {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F)
    {p : Amb m} (hp : p ∈ Submission.Drive.unitBox m) {i : Fin (m + 1)}
    (hcof : cofactorVectorF F p i ≠ 0) :
    ∃ c > 0, ∃ r > 0, ∀ x : Amb m, ‖x - p‖ < r → c ≤ |flowField F x i| := by
  have hcont : Continuous (cofactorVectorF F) := (contDiff_cofactorVectorF hF).continuous
  have ha_pos : 0 < |cofactorVectorF F p i| := abs_pos.mpr hcof
  have htend : Tendsto (cofactorVectorF F) (𝓝 p) (𝓝 (cofactorVectorF F p)) := hcont.continuousAt
  have hball : Metric.ball (cofactorVectorF F p) (|cofactorVectorF F p i| / 2) ∈
      𝓝 (cofactorVectorF F p) :=
    Metric.ball_mem_nhds _ (by linarith)
  obtain ⟨r₁, hr₁, hsub⟩ := Metric.mem_nhds_iff.mp (htend.eventually hball)
  refine ⟨(Real.sqrt (1 + (‖cofactorVectorF F p‖ + |cofactorVectorF F p i| / 2 + 1) ^ 2))⁻¹ *
      (|cofactorVectorF F p i| / 2), by positivity, min r₁ (1/2), lt_min hr₁ (by norm_num), ?_⟩
  intro x hx
  have hx₁ : ‖x - p‖ < r₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxh : ‖x - p‖ < 1/2 := lt_of_lt_of_le hx (min_le_right _ _)
  have hclose : ‖cofactorVectorF F x - cofactorVectorF F p‖ < |cofactorVectorF F p i| / 2 := by
    have h1 : cofactorVectorF F x ∈
        Metric.ball (cofactorVectorF F p) (|cofactorVectorF F p i| / 2) :=
      hsub (by rw [Metric.mem_ball, dist_eq_norm]; exact hx₁)
    rwa [Metric.mem_ball, dist_eq_norm] at h1
  have hcof_i : |cofactorVectorF F p i| / 2 ≤ |cofactorVectorF F x i| := by
    have h1 : |cofactorVectorF F x i - cofactorVectorF F p i| ≤
        ‖cofactorVectorF F x - cofactorVectorF F p‖ := by
      have h2 := PiLp.norm_apply_le (cofactorVectorF F x - cofactorVectorF F p) i
      rw [Real.norm_eq_abs] at h2
      simpa using h2
    have h2 : |cofactorVectorF F p i| ≤
        |cofactorVectorF F x i| + |cofactorVectorF F x i - cofactorVectorF F p i| := by
      have h3 := abs_sub_le (cofactorVectorF F x i) 0
        (cofactorVectorF F x i - cofactorVectorF F p i)
      rw [sub_zero, zero_sub, abs_neg] at h3
      calc |cofactorVectorF F p i| =
            |cofactorVectorF F x i - (cofactorVectorF F x i - cofactorVectorF F p i)| := by
            rw [sub_sub_cancel]
        _ ≤ |cofactorVectorF F x i| + |cofactorVectorF F x i - cofactorVectorF F p i| := h3
    linarith
  have hcof_norm : ‖cofactorVectorF F x‖ ≤
      ‖cofactorVectorF F p‖ + |cofactorVectorF F p i| / 2 := by
    have h1 : ‖cofactorVectorF F x‖ ≤ ‖cofactorVectorF F p‖ +
        ‖cofactorVectorF F x - cofactorVectorF F p‖ := by
      calc ‖cofactorVectorF F x‖ =
            ‖cofactorVectorF F p + (cofactorVectorF F x - cofactorVectorF F p)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  have hbump : boxBump m x = 1 := boxBump_eq_one_of_near_unitBox hp hxh
  have hflow : flowField F x i =
      (Real.sqrt (1 + ‖cofactorVectorF F x‖ ^ 2))⁻¹ * cofactorVectorF F x i := by
    rw [flowField, hbump, one_smul]
    simp only [PiLp.smul_apply, smul_eq_mul]
  rw [hflow, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt (1 + ‖cofactorVectorF F x‖ ^ 2))⁻¹)]
  have hsqrt_le : Real.sqrt (1 + ‖cofactorVectorF F x‖ ^ 2) ≤
      Real.sqrt (1 + (‖cofactorVectorF F p‖ + |cofactorVectorF F p i| / 2 + 1) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [norm_nonneg (cofactorVectorF F p), norm_nonneg (cofactorVectorF F x), ha_pos,
      hcof_norm]
  have hinv : (Real.sqrt (1 + (‖cofactorVectorF F p‖ + |cofactorVectorF F p i| / 2 + 1) ^ 2))⁻¹ ≤
      (Real.sqrt (1 + ‖cofactorVectorF F x‖ ^ 2))⁻¹ :=
    inv_anti₀ (by positivity) hsqrt_le
  exact mul_le_mul hinv hcof_i (by positivity) (by positivity)

/-- **The pointwise chart.**  Every zero of `F` in the unit box lies in the region of some
`ChartData F p`. -/
theorem exists_chart_at {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F)
    (hreg : ∀ x ∈ Submission.Drive.unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {p : Amb m} (hpbox : p ∈ Submission.Drive.unitBox m) (hpF : F p = 0) :
    ∃ C : ChartData F p, p ∈ C.region := by
  obtain ⟨i, hi⟩ := exists_face_index (hreg p hpbox hpF)
  obtain ⟨δ₀, ρ₀, η, hδ₀, hρ₀, hηcd, hηi, hηp, _hnorm, hchar⟩ :=
    exists_local_normalForm hF hpF i hi
  have hcof : cofactorVectorF F p i ≠ 0 := by
    have h := cofactorVec_apply_ne_zero (fderiv ℝ F p) i hi
    simpa [cofactorVectorF] using h
  obtain ⟨c, hc, r₁, hr₁, hvel⟩ := exists_flowField_lower_bound hF hpbox hcof
  set r : ℝ := min r₁ (1 / 2) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact lt_min hr₁ (by norm_num)
  have hrr₁ : r ≤ r₁ := by rw [hrdef]; exact min_le_left _ _
  have hηcont : Continuous η := hηcd.continuous
  obtain ⟨δ₁, hδ₁, hnear⟩ : ∃ δ₁ > 0, ∀ u, |u - p i| < δ₁ → ‖η u - η (p i)‖ < r / 3 := by
    have htend : Tendsto η (𝓝 (p i)) (𝓝 (η (p i))) := hηcont.continuousAt
    have hball : Metric.ball (η (p i)) (r / 3) ∈ 𝓝 (η (p i)) :=
      Metric.ball_mem_nhds _ (by positivity)
    obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.mem_nhds_iff.mp (htend.eventually hball)
    exact ⟨δ₁, hδ₁, fun u hu => hsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hu)⟩
  set δ : ℝ := min δ₀ (min δ₁ (r / 3)) with hδdef
  set ρ : ℝ := min ρ₀ (r / 3) with hρdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hδ₀ (lt_min hδ₁ (by positivity))
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hρ₀ (by positivity)
  have hδδ₀ : δ ≤ δ₀ := by rw [hδdef]; exact min_le_left _ _
  have hδδ₁ : δ ≤ δ₁ := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδr : δ ≤ r / 3 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hρρ₀ : ρ ≤ ρ₀ := by rw [hρdef]; exact min_le_left _ _
  have hρr : ρ ≤ r / 3 := by rw [hρdef]; exact min_le_right _ _
  have hgraph : ∀ x : Amb m, |x i - p i| < δ →
      ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ → F x = 0 →
      x = (x i) • EuclideanSpace.single i (1 : ℝ) + η (x i) := by
    intro x hx1 hx2 hxF
    exact (hchar x (lt_of_lt_of_le hx1 hδδ₀) (lt_of_lt_of_le hx2 hρρ₀)).mp hxF
  have hvelb : ∀ x : Amb m, |x i - p i| < δ →
      ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ →
      c ≤ |flowField F x i| := by
    intro x hx1 hx2
    have hxd : ‖x - p‖ < r := by
      have hp_eq : (p i) • EuclideanSpace.single i (1 : ℝ) + η (p i) = p := by
        rw [hηp]; abel
      have hxsum : (x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)) +
          ((x i - p i) • EuclideanSpace.single i (1 : ℝ)) + (η (x i) - η (p i)) = x - p := by
        have h1 : x - ((p i) • EuclideanSpace.single i (1 : ℝ) + η (p i)) = x - p :=
          congrArg (fun y => x - y) hp_eq
        rw [← h1]
        module
      have hbnorm : ‖(x i - p i) • EuclideanSpace.single i (1 : ℝ)‖ = |x i - p i| := by
        rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single]
        simp
      have hle : ‖x - p‖ ≤ ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ +
          |x i - p i| + ‖η (x i) - η (p i)‖ := by
        rw [← hxsum]
        have h1 := norm_add_le ((x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)) +
          ((x i - p i) • EuclideanSpace.single i (1 : ℝ))) (η (x i) - η (p i))
        have h2 := norm_add_le (x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i))
          ((x i - p i) • EuclideanSpace.single i (1 : ℝ))
        rw [hbnorm] at h2
        linarith
      have hxρ : ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < r / 3 :=
        lt_of_lt_of_le hx2 hρr
      have hxδ : |x i - p i| < r / 3 := lt_of_lt_of_le hx1 hδr
      have hxη : ‖η (x i) - η (p i)‖ < r / 3 := hnear (x i) (lt_of_lt_of_le hx1 hδδ₁)
      linarith
    exact hvel x (lt_of_lt_of_le hxd hrr₁)
  have hpmem : p ∈ (⟨i, δ, ρ, c, η, hδpos, hρpos, hc, hηcont, hηi, hgraph, hvelb⟩ :
      ChartData F p).region := by
    rw [ChartData.mem_region]
    refine ⟨?_, ?_⟩
    · rw [sub_self, abs_zero]; exact hδpos
    · have hzero : p - (p i) • EuclideanSpace.single i (1 : ℝ) - η (p i) = 0 := by
        rw [hηp, sub_self]
      rw [hzero, norm_zero]; exact hρpos
  exact ⟨_, hpmem⟩

theorem exists_chart_cover {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hreg : ∀ x ∈ Submission.Drive.unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x)) :
    ∃ (N : ℕ) (p : Fin N → Work.Drive.Amb m)
      (C : (j : Fin N) → Work.Drive.ChartData F (p j)),
      Work.Drive.zeroSet F ⊆ ⋃ j, (C j).region := by
  classical
  have hpt : ∀ q : zeroSet F, ∃ C : ChartData F q.1, q.1 ∈ C.region :=
    fun q => exists_chart_at hF hreg q.2.1 q.2.2
  choose C hC using hpt
  have hcov : zeroSet F ⊆ ⋃ q : zeroSet F, (C q).region := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hC ⟨x, hx⟩⟩
  obtain ⟨t, ht⟩ := (isCompact_zeroSet hF.continuous).elim_finite_subcover
    (fun q : zeroSet F => (C q).region) (fun q => (C q).isOpen_region) hcov
  refine ⟨t.card, fun j => (t.equivFin.symm j).1.1, fun j => C (t.equivFin.symm j).1, ?_⟩
  intro x hx
  obtain ⟨q, hqt, hxq⟩ := mem_iUnion₂.mp (ht hx)
  refine mem_iUnion.mpr ⟨t.equivFin ⟨q, hqt⟩, ?_⟩
  change x ∈ (C ((t.equivFin.symm (t.equivFin ⟨q, hqt⟩)).1)).region
  have hsub : (t.equivFin.symm (t.equivFin ⟨q, hqt⟩)).1 = q := by
    rw [Equiv.symm_apply_apply]
  rw [hsub]
  exact hxq

end

end Work.Drive
