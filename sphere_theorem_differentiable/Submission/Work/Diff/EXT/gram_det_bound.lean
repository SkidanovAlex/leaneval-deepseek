import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.cGram_eq_sum_gramInv
import Submission.Work.Diff.EXT.det_ge_pow_of_quadForm_ge
import Submission.Work.Diff.EXT.chartData_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform lower bound for the determinant of the chart Gram matrix along a Ricci flow

`gram_det_bound` is the input to the continuation/Shi step (`EXT`) of the Brendle–Schoen proof:
along a flow `G` of metrics whose time-`t` metric is comparable to the initial one on `[0,T)`,

  `⟨u,u⟩_{G t} ≤ e^{2 n C t} ⟨u,u⟩_{G 0}`  and  `⟨u,u⟩_{G 0} ≤ e^{2 n C t} ⟨u,u⟩_{G t}`
  (`n = finrank ℝ E`),

the determinant of the matrix of `G t` in the coordinate frame of the chart at `x₀`,
`GramM G x₀ t (pt x₀ y)`, is bounded below by a positive constant `c`, uniformly over
`t ∈ [T/2, T)` and `y` in a compact subset `K` of the chart target.

## Method

Fix coefficients `v` and write `Q_t(v) = ∑ᵢⱼ vᵢvⱼ (GramM G x₀ t p)ᵢⱼ` for the quadratic form of
the coordinate matrix of `G t` at `p = pt x₀ y`.

* `gdb_qform_GramM`: `Q_t(v)` is the `G t`-square of the combination `∑ᵢ vᵢ σᵢ` of coordinate frame
  vectors (pure bilinearity of the continuous bilinear form `(G t).inner p`).
* `gdb_posDef_point`: at a point of the chart (where the coordinate frame is a basis and the frame
  vector map is injective), `Q_0` is positive definite, by positive definiteness of the metric.
* `gdb_uniform_pd`: minimising `Q_0` over `K × {v : ‖v‖ = 1}` (compact) and using the homogeneity
  `Q_0(c v) = c² Q_0(v)` together with `∑ᵢ vᵢ² ≤ n ‖v‖²` gives `c₀ > 0` with
  `c₀ ∑ᵢ vᵢ² ≤ Q_0(v)` for all `y ∈ K` and all `v`.
* The comparison hypothesis gives `e^{-A₀t} Q_0(v) ≤ Q_t(v)` with `A₀ = 2nC ≥ 0`; since `t < T` and
  `Q_0 ≥ 0`, this yields `Q_t(v) ≥ ε ∑ᵢ vᵢ²` with `ε = e^{-A₀T} c₀ > 0`.
* `det_ge_pow_of_quadForm_ge` (from the quadratic form bound for a symmetric matrix) gives
  `ε^n ≤ det (GramM G x₀ t (pt x₀ y))`, so `c = ε^n` works.

The degenerate cases (`K = ∅`, `n = 0`) are handled separately/vacuously.
-/



set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Bilinearity of a continuous bilinear form -/

/-- The quadratic form of a continuous bilinear form on a finite combination is the double sum of
the pairings of the coefficients. -/
private lemma gdb_clm_qform {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] (B : F →L[ℝ] F →L[ℝ] ℝ) (σ : ι → F) (c : ι → ℝ) :
    B (∑ i, c i • σ i) (∑ j, c j • σ j) = ∑ i, ∑ j, c i * c j * B (σ i) (σ j) := by
  have h1 : B (∑ i, c i • σ i) = ∑ i, c i • B (σ i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul B (c i) (σ i)
  rw [h1]
  have h2 : ∀ j, (∑ i, c i • B (σ i)) (σ j) = ∑ i, c i * B (σ i) (σ j) := by
    intro j
    rw [sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_apply, smul_eq_mul]
  have h3 : ∀ j, (∑ i, c i • B (σ i)) (c j • σ j) = c j * (∑ i, c i * B (σ i) (σ j)) := by
    intro j
    rw [map_smul, h2 j, smul_eq_mul, Finset.mul_sum]
  have h4 : (∑ i, c i • B (σ i)) (∑ j, c j • σ j)
      = ∑ j, c j * (∑ i, c i * B (σ i) (σ j)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => h3 j
  rw [h4, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The inner product of a Riemannian metric is nonnegative on the diagonal. -/
private lemma gdb_inner_self_nonneg (g : Submission.Diff.SMet I M) (x : M)
    (u : TangentSpace I x) : 0 ≤ g.inner x u u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · exact (g.pos x u hu).le

/-- Pulling a scalar out of the quadratic form of a matrix. -/
private lemma gdb_qform_smul_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (v : Fin n → ℝ) :
    (∑ i, ∑ j, (c * v i) * (c * v j) * A i j) = c ^ 2 * ∑ i, ∑ j, v i * v j * A i j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The quadratic form of the Gram matrix is the metric of the combination of frame vectors.** -/
private lemma gdb_qform_GramM (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (y : E)
    (v : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j)
      = (G t).inner (pt (I := I) x₀ y)
          (∑ i, v i • Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y))
          (∑ i, v i • Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  simp only [Work.Diff.GE.GramM, Work.Diff.GE.mComp]
  rw [← gdb_clm_qform ((G t).inner (pt (I := I) x₀ y))
    (fun i => Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y)) v]

/-! ## Positive definiteness of the matrix of coefficients -/

/-- At a point of the chart target, the matrix of metric coefficients (in the coordinate frame) is
positive definite as a quadratic form. -/
private lemma gdb_posDef_point [T2Space M] (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v : Fin (Module.finrank ℝ E) → ℝ) (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y) i j := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G 0).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  rw [gdb_qform_GramM]
  have hp : pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    have h1 : pt (I := I) x₀ y ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have ha : (∑ i, v i • Work.Diff.GE.cBasis (E := E) i) ≠ 0 := by
    intro h0
    apply hv
    have h2 : (Work.Diff.GE.cBasis (E := E)).equivFun
        (∑ i, v i • Work.Diff.GE.cBasis (E := E) i) = v := by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    rw [h0] at h2
    simpa using h2.symm
  have hsum : (∑ i, v i • Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y))
      = Submission.Geodesic.frameVector (I := I) x₀ (pt (I := I) x₀ y)
          (∑ i, v i • Work.Diff.GE.cBasis (E := E) i) := by
    rw [Submission.Geodesic.frameVector_sum (I := I) Finset.univ x₀ (pt (I := I) x₀ y)
      v (Work.Diff.GE.cBasis (E := E))]
    exact Finset.sum_congr rfl fun i _ => by rw [Work.Diff.GE.cFrame_apply]
  rw [hsum]
  exact Work.Diff.GE.CGramInv.cGram_self_pos (G := G) x₀ hp 0 ha

/-! ## Uniform positive definiteness on a compact subset of the chart -/

/-- On the unit sphere of the coefficient space, `∑ i, (v i)^2 ≤ n * ‖v‖^2`. -/
private lemma gdb_sum_sq_le_norm_sq {n : ℕ} (v : Fin n → ℝ) :
    ∑ i, (v i) ^ 2 ≤ (n : ℝ) * ‖v‖ ^ 2 := by
  calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := Finset.sum_le_sum (fun i _ => by
        have h : ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
        have h' : |v i| ≤ ‖v‖ := by simpa using h
        nlinarith [abs_nonneg (v i), norm_nonneg v, sq_abs (v i)])
    _ = (n : ℝ) * ‖v‖ ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **Uniform positive definiteness of the matrix of `G 0` on a compact subset of the chart.** -/
private lemma gdb_uniform_pd [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K : Set E) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x₀).target) (hKne : K.Nonempty) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ y ∈ K, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      c₀ * ∑ i, (v i) ^ 2
        ≤ ∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y) i j := by
  classical
  by_cases hn : Module.finrank ℝ E = 0
  · refine ⟨1, one_pos, fun y _ v => ?_⟩
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [hn]; exact Fin.isEmpty
    simp
  · have hnpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hn
    have hnR : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hnpos
    set S : Set (Fin (Module.finrank ℝ E) → ℝ) := Metric.sphere 0 1 with hSdef
    have hSne : S.Nonempty := by
      obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp hnpos
      exact ⟨Pi.single i₀ (1 : ℝ), by
        rw [hSdef, Metric.mem_sphere, dist_eq_norm, sub_zero, Pi.norm_single]
        norm_num⟩
    have hScomp : IsCompact S := isCompact_sphere 0 1
    set Ψ : E × (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
      fun q => ∑ i, ∑ j, q.2 i * q.2 j * Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ q.1) i j
      with hΨdef
    have hentry : ∀ i j : Fin (Module.finrank ℝ E),
        ContinuousOn (fun y' : E => Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y') i j) K :=
      fun i j => ((chartData_contDiffOn (I := I) (M := M) G x₀ K hKt).2.2 0 i j).continuousOn
    have hcont : ContinuousOn Ψ (K ×ˢ S) := by
      rw [hΨdef]
      refine continuousOn_finsetSum Finset.univ (fun i _ => ?_)
      refine continuousOn_finsetSum Finset.univ (fun j _ => ?_)
      have hi : ContinuousOn (fun q : E × (Fin (Module.finrank ℝ E) → ℝ) => q.2 i)
          (K ×ˢ S) := ((continuous_apply i).comp continuous_snd).continuousOn
      have hj : ContinuousOn (fun q : E × (Fin (Module.finrank ℝ E) → ℝ) => q.2 j)
          (K ×ˢ S) := ((continuous_apply j).comp continuous_snd).continuousOn
      have hM : ContinuousOn (fun q : E × (Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ q.1) i j) (K ×ˢ S) :=
        (hentry i j).comp continuousOn_fst (fun q hq => hq.1)
      exact (hi.mul hj).mul hM
    obtain ⟨qm, hqm, hmin⟩ := (hK.prod hScomp).exists_isMinOn (hKne.prod hSne) hcont
    have hpos_min : 0 < Ψ qm := by
      have hvne : qm.2 ≠ 0 := by
        intro h0
        have h1 := hqm.2
        rw [hSdef, Metric.mem_sphere, dist_eq_norm, sub_zero, h0, norm_zero] at h1
        norm_num at h1
      have h := gdb_posDef_point G x₀ (hKt hqm.1) qm.2 hvne
      simpa only [hΨdef] using h
    refine ⟨Ψ qm / (Module.finrank ℝ E : ℝ), div_pos hpos_min hnR, fun y hy v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hsphere : (‖v‖⁻¹ • v) ∈ S := by
        rw [hSdef, Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv,
          Real.norm_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hvnorm]
      have hmin' : Ψ qm ≤ Ψ (y, ‖v‖⁻¹ • v) := hmin ⟨hy, hsphere⟩
      have hscale : Ψ (y, v) = ‖v‖ ^ 2 * Ψ (y, ‖v‖⁻¹ • v) := by
        have h := gdb_qform_smul_matrix (Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y))
          ‖v‖ (‖v‖⁻¹ • v)
        simp only [hΨdef, Pi.smul_apply, smul_eq_mul] at h ⊢
        refine Eq.trans ?_ h
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have h1 : ‖v‖ * (‖v‖⁻¹ * v i) = v i := by
          rw [← mul_assoc, mul_inv_cancel₀ hvnorm, one_mul]
        have h2 : ‖v‖ * (‖v‖⁻¹ * v j) = v j := by
          rw [← mul_assoc, mul_inv_cancel₀ hvnorm, one_mul]
        rw [h1, h2]
      have hsq : ∑ i, (v i) ^ 2 ≤ (Module.finrank ℝ E : ℝ) * ‖v‖ ^ 2 :=
        gdb_sum_sq_le_norm_sq v
      calc (Ψ qm / (Module.finrank ℝ E : ℝ)) * ∑ i, (v i) ^ 2
          ≤ (Ψ qm / (Module.finrank ℝ E : ℝ)) * ((Module.finrank ℝ E : ℝ) * ‖v‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (div_nonneg hpos_min.le hnR.le)
        _ = Ψ qm * ‖v‖ ^ 2 := by
            field_simp
        _ ≤ ‖v‖ ^ 2 * Ψ (y, ‖v‖⁻¹ • v) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left hmin' (sq_nonneg _)
        _ = Ψ (y, v) := hscale.symm

theorem gram_det_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (x₀ : M) (K : Set E) (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x₀).target) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      c ≤ (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).det := by
  classical
  by_cases hKne : K.Nonempty
  · obtain ⟨c₀, hc₀pos, hc₀⟩ := gdb_uniform_pd G x₀ K hK hKt hKne
    set A0 : ℝ := 2 * ((Module.finrank ℝ E : ℝ) * C) with hA0
    have hA0nonneg : 0 ≤ A0 := by
      rw [hA0]
      have : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      nlinarith [hC]
    have hεpos : 0 < Real.exp (-(A0 * T)) * c₀ := mul_pos (Real.exp_pos _) hc₀pos
    refine ⟨(Real.exp (-(A0 * T)) * c₀) ^ Module.finrank ℝ E, pow_pos hεpos _, ?_⟩
    intro t ht y hy
    have ht0 : t ∈ Set.Ico 0 T := ⟨by linarith [ht.1, hT], ht.2⟩
    have hquad : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        (Real.exp (-(A0 * T)) * c₀) * ∑ i, (v i) ^ 2
          ≤ ∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j := by
      intro v
      obtain ⟨_, h2⟩ := hmet t ht0 (pt (I := I) x₀ y)
        (∑ i, v i • Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y))
      have hlow0 : (∑ i, ∑ j, v i * v j *
            Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y) i j)
          ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) *
            (∑ i, ∑ j, v i * v j *
              Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j) := by
        rw [gdb_qform_GramM G x₀ 0 y v, gdb_qform_GramM G x₀ t y v]
        exact h2
      have hQ0nonneg : 0 ≤ ∑ i, ∑ j, v i * v j *
          Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y) i j := by
        rw [gdb_qform_GramM]
        exact gdb_inner_self_nonneg (G 0) _ _
      have hexple : Real.exp (-(A0 * t)) *
          (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) *
            (∑ i, ∑ j, v i * v j *
              Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j))
          = ∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j := by
        rw [← mul_assoc, ← Real.exp_add]
        have hsum0 : -(A0 * t) + 2 * ((Module.finrank ℝ E : ℝ) * C) * t = 0 := by
          rw [hA0]; ring
        rw [hsum0, Real.exp_zero, one_mul]
      have hlow : Real.exp (-(A0 * t)) *
          (∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y) i j)
          ≤ ∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j := by
        calc Real.exp (-(A0 * t)) *
              (∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y) i j)
            ≤ Real.exp (-(A0 * t)) *
              (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) *
                (∑ i, ∑ j, v i * v j *
                  Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j)) :=
              mul_le_mul_of_nonneg_left hlow0 (Real.exp_pos _).le
          _ = ∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j :=
              hexple
      have hexpmono : Real.exp (-(A0 * T)) ≤ Real.exp (-(A0 * t)) := by
        rw [Real.exp_le_exp]
        have hmul : A0 * t ≤ A0 * T := mul_le_mul_of_nonneg_left (le_of_lt ht.2) hA0nonneg
        linarith
      calc (Real.exp (-(A0 * T)) * c₀) * ∑ i, (v i) ^ 2
          = Real.exp (-(A0 * T)) * (c₀ * ∑ i, (v i) ^ 2) := by ring
        _ ≤ Real.exp (-(A0 * t)) *
              (∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ 0 (pt (I := I) x₀ y) i j) :=
            mul_le_mul hexpmono (hc₀ y hy v)
              (mul_nonneg hc₀pos.le (Finset.sum_nonneg fun i _ => sq_nonneg _))
              (Real.exp_pos _).le
        _ ≤ ∑ i, ∑ j, v i * v j * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j := hlow
    exact det_ge_pow_of_quadForm_ge (n := Module.finrank ℝ E)
      (M := Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y))
      (fun i j => (G t).symm (pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ i (pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ j (pt (I := I) x₀ y))) hεpos hquad
  · exact ⟨1, one_pos, fun _ _ _ hy => (hKne ⟨_, hy⟩).elim⟩

end Work.Diff.EXT
