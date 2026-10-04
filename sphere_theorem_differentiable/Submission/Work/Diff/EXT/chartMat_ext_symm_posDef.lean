import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Set Metric Filter

namespace Work.Diff.EXT

/-! ## The quadratic form of a matrix

We collect here the elementary facts about the quadratic form `v ↦ ∑ᵢ∑ⱼ vᵢ vⱼ Aᵢⱼ` of a matrix
`A : Fin n → Fin n → ℝ` that are needed to pass a uniform positive-definiteness bound across a seam
and to convert it into a strict positivity statement on a two-sided tube. -/

namespace SymPosDef

variable {n : ℕ}

/-- The quadratic form `v ↦ ∑ᵢ∑ⱼ vᵢ vⱼ Aᵢⱼ` of a matrix. -/
noncomputable def qf (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ := ∑ i, ∑ j, v i * v j * A i j

/-- The quadratic form is homogeneous of degree two. -/
lemma qf_smul (A : Fin n → Fin n → ℝ) (c : ℝ) (v : Fin n → ℝ) :
    qf A (c • v) = c ^ 2 * qf A v := by
  simp only [qf, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- A nonzero vector has strictly positive Euclidean square-sum. -/
lemma sum_sq_pos {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < ∑ i, (v i) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun i => not_not.mp (not_exists.mp h i))
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
    (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

/-- The quadratic form is (jointly) continuous. -/
lemma continuous_qf :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → ℝ) => qf p.1 p.2 := by
  have h : ∀ i j : Fin n, Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → ℝ) =>
      p.2 i * p.2 j * p.1 i j := by
    intro i j
    exact (((continuous_apply i).comp continuous_snd).mul
      ((continuous_apply j).comp continuous_snd)).mul
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
  simpa only [qf] using
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => h i j))

/-- Positivity of the quadratic form on the unit sphere gives strict positivity everywhere. -/
lemma qf_pos_of_sphere {A : Fin n → Fin n → ℝ}
    (h : ∀ w : Fin n → ℝ, w ∈ Metric.sphere (0 : Fin n → ℝ) 1 → 0 < qf A w) :
    ∀ v : Fin n → ℝ, v ≠ 0 → 0 < qf A v := by
  intro v hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwmem : (‖v‖⁻¹) • v ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hvpos, inv_mul_cancel₀ (ne_of_gt hvpos)]
  have hw := h _ hwmem
  rw [qf_smul] at hw
  exact pos_of_mul_pos_right hw (le_of_lt (pow_pos (inv_pos.mpr hvpos) 2))

end SymPosDef

open SymPosDef

/-- **The quadratic-form lower bound passes to the seam.**  With `n = finrank ℝ E`, if
`W : ℝ × E → (Fin n → Fin n → ℝ)` is continuous on the open slab `(T-a, T+a) × U` and its quadratic
form `v ↦ ∑ᵢ∑ⱼ vᵢ vⱼ W (t,y)ᵢⱼ` is bounded below by `ε ∑ᵢ (vᵢ)²` on the left half `(T-a,T) × U`,
then the same bound holds at the seam `t = T`: for fixed `y ∈ U` and `v`, the function
`t ↦ ∑ᵢ∑ⱼ vᵢvⱼ W (t,y)ᵢⱼ` is continuous at `T` (as `(T,y)` lies in the open slab and `t ↦ (t,y)`
maps the left half into the slab), and `ge_of_tendsto` along `𝓝[Ioo (T-a) T] T` gives the claim. -/
theorem qf_le_at_seam_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {T a ε : ℝ} (ha : 0 < a)
    {W : ℝ × E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ} {U : Set E}
    (hWc : ContinuousOn W (Set.Ioo (T - a) (T + a) ×ˢ U))
    (hu : ∀ t ∈ Set.Ioo (T - a) T, ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ qf (W (t, y)) v) :
    ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ qf (W (T, y)) v := by
  intro y hy v
  have hmem : (T, y) ∈ Set.Ioo (T - a) (T + a) ×ˢ U := by
    have ht1 : T - a < T := by linarith
    have ht2 : T < T + a := by linarith
    exact ⟨⟨ht1, ht2⟩, hy⟩
  have hφ : ContinuousWithinAt (fun t : ℝ => (t, y)) (Set.Ioo (T - a) T) T :=
    (continuous_id.prodMk continuous_const).continuousWithinAt
  have hmap : MapsTo (fun t : ℝ => (t, y)) (Set.Ioo (T - a) T)
      (Set.Ioo (T - a) (T + a) ×ˢ U) := by
    intro t ht
    have ht1 : T - a < t := ht.1
    have ht2 : t < T + a := by linarith [ht.2]
    exact ⟨⟨ht1, ht2⟩, hy⟩
  have hW : ContinuousWithinAt (fun t : ℝ => W (t, y)) (Set.Ioo (T - a) T) T :=
    (hWc.continuousWithinAt hmem).comp (f := fun t : ℝ => (t, y)) (x := T) hφ hmap
  have hqv : Continuous fun A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
      qf A v :=
    continuous_qf.comp (continuous_id.prodMk continuous_const)
  have hqv_u : ContinuousWithinAt (fun A : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ => qf A v) Set.univ (W (T, y)) :=
    hqv.continuousAt.continuousWithinAt
  have hfinal : ContinuousWithinAt (fun t : ℝ => qf (W (t, y)) v) (Set.Ioo (T - a) T) T :=
    hqv_u.comp (f := fun t : ℝ => W (t, y)) (t := Set.univ) (x := T) hW (fun t _ => trivial)
  haveI : NeBot (𝓝[Set.Ioo (T - a) T] T) := right_nhdsWithin_Ioo_neBot (by linarith)
  exact ge_of_tendsto hfinal
    (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => hu t ht y hy v))

/-- **A positive-definite tube across a seam.**  Let `W : ℝ × E → (Fin n → Fin n → ℝ)`
(`n = finrank ℝ E`) be continuous on the open slab `(T-a, T+a) × U` (`a > 0`, `U` open,
`y₀ ∈ U`), and suppose its quadratic form is bounded below by `ε ∑ᵢ (vᵢ)²` at time `T` for every
`y ∈ U` and every `v`, with `ε > 0`.  Then around `{T} × {y₀}` there is a full two-sided tube
`(T-δ', T+δ') × U'`, with `δ' ≤ a` and `U' ⊆ U` an open neighbourhood of `y₀`, on which the
quadratic form is strictly positive at every nonzero vector. -/
theorem exists_posDef_tube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {T a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    {W : ℝ × E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    {U : Set E} (hU : IsOpen U) {y₀ : E} (hy₀ : y₀ ∈ U)
    (hWc : ContinuousOn W (Set.Ioo (T - a) (T + a) ×ˢ U))
    (hT : ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ qf (W (T, y)) v) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ a ∧ ∃ U' : Set E, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧
      ∀ t ∈ Set.Ioo (T - δ') (T + δ'), ∀ y ∈ U', ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        v ≠ 0 → 0 < qf (W (t, y)) v := by
  -- a closed ball around `y₀` inside `U`
  obtain ⟨r, hrpos, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall y₀ r ⊆ U := by
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
    exact ⟨ρ / 2, by linarith,
      fun z hz => hρsub (Metric.closedBall_subset_ball (by linarith) hz)⟩
  -- the compact set `{T} × closedBall y₀ r × sphere 0 1`
  have hs : IsCompact (({T} ×ˢ Metric.closedBall y₀ r) ×ˢ
      Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1) :=
    (isCompact_singleton.prod (isCompact_closedBall y₀ r)).prod (isCompact_sphere 0 1)
  -- `W` is continuous on the open slab, hence at every point of the open set `A ×ˢ univ`
  have hA : IsOpen (Set.Ioo (T - a) (T + a) ×ˢ U) := isOpen_Ioo.prod hU
  have hZc : ContinuousOn (fun p : (ℝ × E) × (Fin (Module.finrank ℝ E) → ℝ) =>
      qf (W p.1) p.2) ((Set.Ioo (T - a) (T + a) ×ˢ U) ×ˢ Set.univ) := by
    rw [(hA.prod isOpen_univ).continuousOn_iff]
    intro p hp
    exact continuous_qf.continuousAt.comp₂
      ((hWc.continuousAt (hA.mem_nhds hp.1)).comp continuous_fst.continuousAt)
      continuousAt_snd
  have htarget : IsOpen (((Set.Ioo (T - a) (T + a) ×ˢ U) ×ˢ Set.univ) ∩
      (fun p : (ℝ × E) × (Fin (Module.finrank ℝ E) → ℝ) =>
        qf (W p.1) p.2) ⁻¹' (Set.Ioi 0)) :=
    hZc.isOpen_inter_preimage (hA.prod isOpen_univ) isOpen_Ioi
  have hssub : (({T} ×ˢ Metric.closedBall y₀ r) ×ˢ
        Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1) ⊆
      ((Set.Ioo (T - a) (T + a) ×ˢ U) ×ˢ Set.univ) ∩
        (fun p : (ℝ × E) × (Fin (Module.finrank ℝ E) → ℝ) =>
          qf (W p.1) p.2) ⁻¹' (Set.Ioi 0) := by
    rintro ⟨⟨t, y⟩, v⟩ ⟨⟨ht, hy⟩, hv⟩
    simp only [Set.mem_singleton_iff] at ht
    rw [ht]
    have htI : T ∈ Set.Ioo (T - a) (T + a) := ⟨by linarith, by linarith⟩
    have hmemA : (T, y) ∈ Set.Ioo (T - a) (T + a) ×ˢ U := ⟨⟨htI.1, htI.2⟩, hrsub hy⟩
    have hZm : qf (W (T, y)) v ∈ Set.Ioi 0 := by
      have hvne : v ≠ 0 := by
        intro h0
        rw [h0, Metric.mem_sphere, dist_self] at hv
        exact one_ne_zero hv.symm
      exact lt_of_lt_of_le (mul_pos hε (sum_sq_pos hvne)) (hT y (hrsub hy) v)
    exact ⟨⟨hmemA, trivial⟩, hZm⟩
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := hs.exists_cthickening_subset_open htarget hssub
  refine ⟨min a δ₀, lt_min ha hδ₀pos, min_le_left _ _, Metric.ball y₀ r, isOpen_ball,
    by simpa using hrpos, Metric.ball_subset_closedBall.trans hrsub, ?_⟩
  intro t ht y hy v hv
  have hyK : y ∈ Metric.closedBall y₀ r := Metric.ball_subset_closedBall hy
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwQ : (‖v‖⁻¹) • v ∈ Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hvpos, inv_mul_cancel₀ (ne_of_gt hvpos)]
  have hdist : dist ((t, y), (‖v‖⁻¹) • v) ((T, y), (‖v‖⁻¹) • v) ≤ δ₀ := by
    have ht1 : T - min a δ₀ < t := ht.1
    have ht2 : t < T + min a δ₀ := ht.2
    have h1 : |t - T| < min a δ₀ := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    have h2 : |t - T| ≤ δ₀ := le_of_lt (lt_of_lt_of_le h1 (min_le_right _ _))
    rw [show dist ((t, y), (‖v‖⁻¹) • v) ((T, y), (‖v‖⁻¹) • v) = |t - T| by
      simp [Prod.dist_eq, Real.dist_eq]]
    exact h2
  have hmem : ((t, y), (‖v‖⁻¹) • v) ∈ Metric.cthickening δ₀
      (({T} ×ˢ Metric.closedBall y₀ r) ×ˢ
        Metric.sphere (0 : Fin (Module.finrank ℝ E) → ℝ) 1) :=
    Metric.mem_cthickening_of_dist_le _ ((T, y), (‖v‖⁻¹) • v) δ₀ _
      ⟨⟨Set.mem_singleton T, hyK⟩, hwQ⟩ hdist
  have hZpos : 0 < qf (W (t, y)) ((‖v‖⁻¹) • v) := (hδ₀sub hmem).2
  have hmain : qf (W (t, y)) v = ‖v‖ ^ 2 * qf (W (t, y)) ((‖v‖⁻¹) • v) := by
    have hsm : ‖v‖ • ((‖v‖⁻¹) • v) = v := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
    conv_lhs => rw [← hsm]
    exact qf_smul _ _ _
  rw [hmain]
  exact mul_pos (pow_pos hvpos 2) hZpos

/-- **Symmetrising and shrinking a smooth extension of the chart matrix.**  Given a smooth `V` on
`(Ioo (T-δ) (T+δ)) ×ˢ U` which agrees with the chart matrix `chartMat G x₀` on the left slab
`(Ico (T-δ) T) ×ˢ U`, and given that the chart matrix is *uniformly* positive definite on that
slab, one can shrink `δ` and `U` and replace `V` by its symmetric part, obtaining `W` smooth on
`(Ioo (T-δ') (T+δ')) ×ˢ U'` which still agrees with the chart matrix on `(Ico (T-δ') T) ×ˢ U'` and
is symmetric and positive definite on the whole two-sided slab.

This is what turns any smooth extension of the chart matrix (e.g. the one produced by a Whitney
extension with bounded jets) into a legitimate local piece of a metric family, ready to be glued by
`Work.Diff.EXT.glue_local_metric_families`.  `chartMat G x₀ t y` is the matrix of `(G t).inner` in
the coordinate frame of the chart at `x₀`; it is symmetric because the metric form is, so the
symmetric part of `V` still agrees with it on the left slab.  `U` bounded (relatively compact in
the finite-dimensional `E`) is what makes the positivity survive on the right of `T`:
`hell` at `t → T⁻` gives a positive definite limit, and continuity on the compact set
`[T-δ', T+δ'] × closure U'` preserves it. -/
theorem chartMat_ext_symm_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (T δ : ℝ) (hδ : 0 < δ)
    (V : ℝ × E → Work.Diff.EXT.MatE (E := E))
    (U : Set E) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V ((Set.Ioo (T - δ) (T + δ)) ×ˢ U))
    (hVeq : ∀ t ∈ Set.Ico (T - δ) T, ∀ y ∈ U,
        V (t, y) = Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (T - δ) T, ∀ y ∈ U,
        ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j *
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j) :
    ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ ∃ U' : Set E, IsOpen U' ∧ U' ⊆ U ∧
      ∃ W : ℝ × E → Work.Diff.EXT.MatE (E := E),
        ContDiffOn ℝ (⊤ : ℕ∞) W ((Set.Ioo (T - δ') (T + δ')) ×ˢ U') ∧
        (∀ t ∈ Set.Ico (T - δ') T, ∀ y ∈ U',
          W (t, y) = Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y) ∧
        (∀ t ∈ Set.Ioo (T - δ') (T + δ'), ∀ y ∈ U',
          (∀ i j, W (t, y) i j = W (t, y) j i) ∧
          ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
            0 < ∑ i, ∑ j, v i * v j * W (t, y) i j) := by
  obtain ⟨ε, hεpos, hεbnd⟩ := hell
  -- the chart matrix is symmetric, being the matrix of a symmetric bilinear form
  have hsymm : ∀ (t : ℝ) (y : E) (i j : Fin (Module.finrank ℝ E)),
      chartMat (I := I) (M := M) G x₀ t y i j = chartMat (I := I) (M := M) G x₀ t y j i :=
    fun t y i j => (G t).symm _ _ _
  by_cases hUne : U.Nonempty
  · obtain ⟨y₀, hy₀⟩ := hUne
    -- the symmetric part of the extension
    set W : ℝ × E → MatE (E := E) := fun p i j => (V p i j + V p j i) / 2 with hWdef
    have hWsm : ContDiffOn ℝ (⊤ : ℕ∞) W (Set.Ioo (T - δ) (T + δ) ×ˢ U) := by
      simp only [hWdef]
      refine contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j => ?_))
      exact (((contDiffOn_pi.mp ((contDiffOn_pi.mp hV) i)) j).add
        ((contDiffOn_pi.mp ((contDiffOn_pi.mp hV) j)) i)).div_const 2
    have hWc : ContinuousOn W (Set.Ioo (T - δ) (T + δ) ×ˢ U) := hWsm.continuousOn
    -- `W` agrees with the chart matrix on the left slab
    have hWeq : ∀ t ∈ Set.Ico (T - δ) T, ∀ y ∈ U, W (t, y) = chartMat G x₀ t y := by
      intro t ht y hy
      have h1 : V (t, y) = chartMat G x₀ t y := hVeq t ht y hy
      funext i j
      simp only [hWdef]
      rw [show V (t, y) i j = chartMat G x₀ t y i j by rw [h1],
        show V (t, y) j i = chartMat G x₀ t y j i by rw [h1], hsymm t y j i]
      ring
    -- the uniform lower bound for `W` on the left half
    have hleft : ∀ t ∈ Set.Ioo (T - δ) T, ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ qf (W (t, y)) v := by
      intro t ht y hy v
      have ht' : t ∈ Set.Ico (T - δ) T := ⟨le_of_lt ht.1, ht.2⟩
      rw [hWeq t ht' y hy]
      exact hεbnd t ht' y hy v
    -- the bound passes to the seam
    have hTb : ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ qf (W (T, y)) v := qf_le_at_seam_gen hδ hWc hleft
    -- the two-sided positivity tube
    obtain ⟨δ', hδ'pos, hδ'δ, U', hU'o, hy₀U', hU'sub, htube⟩ :=
      exists_posDef_tube hδ hεpos hU hy₀ hWc hTb
    refine ⟨δ', hδ'pos, hδ'δ, U', hU'o, hU'sub, W, ?_, ?_, ?_⟩
    · -- smoothness on the shrunk slab
      refine hWsm.mono ?_
      exact Set.prod_mono (Set.Ioo_subset_Ioo (by linarith) (by linarith)) hU'sub
    · -- agreement with the chart matrix on the shrunk left slab
      intro t ht y hy
      exact hWeq t ⟨by linarith [ht.1, hδ'δ], ht.2⟩ y (hU'sub hy)
    · -- symmetry and strict positive definiteness
      intro t ht y hy
      refine ⟨fun i j => ?_, fun v hv => ?_⟩
      · simp only [hWdef]
        ring
      · show 0 < qf (W (t, y)) v
        by_cases htT : t < T
        · -- left half: the hypothesis on the chart matrix
          have ht' : t ∈ Set.Ico (T - δ) T := ⟨by linarith [ht.1, hδ'δ], htT⟩
          have hWeqt : W (t, y) = chartMat G x₀ t y := hWeq t ht' y (hU'sub hy)
          rw [hWeqt]
          show 0 < ∑ i, ∑ j, v i * v j * chartMat (I := I) (M := M) G x₀ t y i j
          have h1 : ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j *
              chartMat (I := I) (M := M) G x₀ t y i j := hεbnd t ht' y (hU'sub hy) v
          have h2 : 0 < ε * ∑ i, (v i) ^ 2 := mul_pos hεpos (sum_sq_pos hv)
          linarith
        · -- right half (including the seam): the tube
          exact htube t ht y hy v hv
  · -- `U = ∅`: everything is vacuous, take `W = V`, `U' = ∅`
    refine ⟨δ, hδ, le_rfl, ∅, isOpen_empty, Set.empty_subset U, V, ?_, ?_, ?_⟩
    · exact hV.mono (Set.prod_mono (Subset.refl _) (Set.empty_subset U))
    · intro t ht y hy
      exact absurd hy (by simp)
    · intro t ht y hy
      exact ⟨fun i j => absurd hy (by simp), fun v hv => absurd hy (by simp)⟩

end Work.Diff.EXT
