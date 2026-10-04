import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aCovArr_bound_of_jets
import Submission.Work.Diff.EXT.ConnCov.jets_bound_of_contDiffAt_compact
import Submission.Work.Diff.EXT.local_ext_of_chart_bounds_v2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Boundedness of the chart recursion `aCovArr` on a compact slab of a smooth family

`Work.Diff.EXT.aCovArr G x₀ t k v i j l` is the chart recursion for the `k`-th covariant derivative
(with respect to the background connection of `G 0`) of the lowered connection difference
`g_t(∇^{g_t} − ∇^{g_0})`.

The companion file `ConnCov/aCovArr_bound_of_jets.lean` proves that these components are uniformly
bounded on `K` for `t ∈ Ico (T'/2) T'` as soon as

* the *spatial* jets of the chart matrix `chartMat G x₀ t` are uniformly bounded on the slab,
* the chart matrix is uniformly elliptic there,
* and it is pointwise `C^∞` there.

In this file we discharge these three hypotheses from the single assumption that the family `G` is
**jointly smooth** on `[0, T)` — no Ricci-flow equation, no curvature bound and no a priori estimate
is used.  All three properties are consequences of the joint `C^∞`-ness of
`(t, y) ↦ chartMat G x₀ t y` on the *open* set `(Ioo 0 T) ×ˢ (extChartAt I x₀).target` together with
compactness of the closed slab `Icc a (2a) ×ˢ K` (which contains the half-open slab `Ico a (2a) ×ˢ K`
on which the conclusion is required — note that `Ico a (2a)` is *not* compact):

* smoothness in `y` at every point of the slab is `ContDiffAt.comp` with `y' ↦ (t, y')`;
* uniform bounds on the spatial jets follow from the pointwise inequality
  `‖D^k_y (chartMat G x₀ t) y‖ ≤ ‖D^k u (t,y)‖` for the joint function `u` (the slice jet is the joint
  jet composed with `inr`) and the uniform joint jet bound on the compact slab
  (`jets_bound_of_contDiffAt_compact`);
* uniform ellipticity is the compact-set form `uniform_posDef_of_compact` of
  `uniform_posDef_of_continuous_v2`: a continuous family of quadratic forms that is positive definite
  at every point of a compact set dominates `δ · 1` there with `δ > 0`.

The target then follows by instantiating `aCovArr_bound_of_jets` with `T' = 2a`
(so that `Ico (T'/2) T' = Ico a (2a)`).
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set Filter

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]

/-! ## The norm of the slice jet is bounded by the norm of the joint jet -/

/-- **The iterated derivative of a slice, in norm.**  For `Φ : ℝ × E → W` that is `C^∞` at `z`, the
`k`-th iterated derivative of the slice `y' ↦ Φ (z.1, y')` at `z.2` is the `k`-th iterated derivative
of `Φ` at `z` post-composed, in every argument, with the (norm-one) inclusion
`inr : E →L[ℝ] ℝ × E`.  Hence its norm is at most the norm of the joint jet. -/
theorem norm_iteratedFDeriv_slice_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : ℝ × E → W} {k : ℕ} {z : ℝ × E} (h : ContDiffAt ℝ (⊤ : ℕ∞) Φ z) :
    ‖iteratedFDeriv ℝ k (fun y' : E => Φ (z.1, y')) z.2‖ ≤ ‖iteratedFDeriv ℝ k Φ z‖ := by
  rw [Work.Diff.EXT.iteratedFDeriv_slice_eq (h := h.of_le (by simp))]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hprod : ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ ℝ E‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ ℝ E)
  calc ‖iteratedFDeriv ℝ k Φ z‖ * ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ ℝ E‖
      ≤ ‖iteratedFDeriv ℝ k Φ z‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k Φ z‖ := mul_one _

/-! ## Uniform positive definiteness on a compact set -/

/-- **Uniform positive definiteness of a continuous family of quadratic forms on a compact set.**
If the entries of `A : X → Fin n → Fin n → ℝ` are continuous at every point of a compact set `C` and
the quadratic form of `A x` is positive definite for every `x ∈ C`, then there is `δ > 0` with
`δ * ∑ vᵢ² ≤ ∑ vᵢ vⱼ (A x)ᵢⱼ` for all `x ∈ C` and all `v`.

This is the compact version of `Work.Diff.EXT.uniform_posDef_of_continuous_v2`: on the compact set
`C ×ˢ {v | ∑ vᵢ² = 1}` the quadratic form is continuous and strictly positive, hence attains a
positive minimum `δ`; homogeneity then gives the bound for arbitrary `v`. -/
theorem uniform_posDef_of_compact
    {n : ℕ} {X : Type*} [TopologicalSpace X] {A : X → Fin n → Fin n → ℝ} {C : Set X}
    (hC : IsCompact C)
    (hcont : ∀ x ∈ C, ∀ i j, ContinuousAt (fun y => A y i j) x)
    (hpos : ∀ x ∈ C, ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * A x i j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, ∀ v : Fin n → ℝ,
      δ * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * A x i j := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun x _ v => by simp⟩
  rcases C.eq_empty_or_nonempty with hC0 | hCne
  · subst hC0
    exact ⟨1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
  set S : Set (Fin n → ℝ) := {v | ∑ i, (v i) ^ 2 = 1} with hS
  have hSclosed : IsClosed S := by
    rw [hS]
    exact isClosed_eq (by fun_prop) continuous_const
  have hSbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have h2 : (v i) ^ 2 ≤ 1 := by
      rw [hS] at hv
      rw [hv] at h1
      exact h1
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hScomp : IsCompact S := (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hSclosed, hSbdd⟩
  have hSne : S.Nonempty := by
    refine ⟨fun _ : Fin n => Real.sqrt (1 / (n : ℝ)), ?_⟩
    rw [hS]
    simp only [Set.mem_setOf_eq]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hFcont : ContinuousOn
      (fun p : X × (Fin n → ℝ) => ∑ i, ∑ j, p.2 i * p.2 j * A p.1 i j)
      (C ×ˢ S) := by
    refine continuousOn_finsetSum Finset.univ fun i _ =>
      continuousOn_finsetSum Finset.univ fun j _ => ?_
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact ((continuous_apply i).comp continuous_snd).continuousOn
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
    · intro p hp
      exact ((hcont p.1 hp.1 i j).comp continuousAt_fst).continuousWithinAt
  obtain ⟨p₀, hp₀, hmin⟩ := (hC.prod hScomp).exists_isMinOn (hCne.prod hSne) hFcont
  have hp₀S : p₀.2 ∈ S := hp₀.2
  have hne : p₀.2 ≠ 0 := by
    intro h0
    have h1 : (∑ i, (p₀.2 i) ^ 2) = 0 := by
      rw [h0]
      simp
    have h2 : (∑ i, (p₀.2 i) ^ 2) = 1 := by
      simpa only [hS, Set.mem_setOf_eq] using hp₀S
    rw [h1] at h2
    norm_num at h2
  have hδpos : 0 < ∑ i, ∑ j, p₀.2 i * p₀.2 j * A p₀.1 i j := hpos p₀.1 hp₀.1 p₀.2 hne
  -- the minimum is a lower bound for the quadratic form on `C`
  have hmin' : ∀ b ∈ C ×ˢ S, (∑ i, ∑ j, p₀.2 i * p₀.2 j * A p₀.1 i j)
      ≤ ∑ i, ∑ j, b.2 i * b.2 j * A b.1 i j := fun b hb => hmin hb
  refine ⟨_, hδpos, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · rw [hv]
    simp
  · have hs_pos : 0 < ∑ i, (v i) ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv (funext h)
      exact Finset.sum_pos' (fun j _ => sq_nonneg (v j))
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    set c : ℝ := Real.sqrt (∑ i, (v i) ^ 2) with hc
    have hcpos : 0 < c := Real.sqrt_pos.mpr hs_pos
    have hc2 : c ^ 2 = ∑ i, (v i) ^ 2 := Real.sq_sqrt hs_pos.le
    set w : Fin n → ℝ := fun i => v i / c with hwdef
    have hwS : w ∈ S := by
      rw [hS]
      simp only [Set.mem_setOf_eq, hwdef]
      have h1 : ∀ i, (v i / c) ^ 2 = (1 / c ^ 2) * (v i) ^ 2 := by
        intro i
        field_simp
      simp only [h1]
      rw [← Finset.mul_sum, hc2]
      field_simp
    have hscale : ∑ i, ∑ j, v i * v j * A x i j
        = c ^ 2 * ∑ i, ∑ j, w i * w j * A x i j := by
      simp only [hwdef]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    have hminw : (∑ i, ∑ j, p₀.2 i * p₀.2 j * A p₀.1 i j)
        ≤ ∑ i, ∑ j, w i * w j * A x i j := by
      refine hmin' (x, w) ⟨hx, hwS⟩
    rw [hscale, hc2]
    calc (∑ i, ∑ j, p₀.2 i * p₀.2 j * A p₀.1 i j) * ∑ i, (v i) ^ 2
        = (∑ i, (v i) ^ 2) * (∑ i, ∑ j, p₀.2 i * p₀.2 j * A p₀.1 i j) := by ring
      _ ≤ (∑ i, (v i) ^ 2) * (∑ i, ∑ j, w i * w j * A x i j) :=
          mul_le_mul_of_nonneg_left hminw (by positivity)

/-! ## The target -/

theorem aCovArr_bound_piece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) {T : ℝ} (hT : 0 < T)
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T))
    (x₀ : M) (K : Set E) (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x₀).target)
    {a : ℝ} (ha : 0 < a) (h2a : 2 * a < T) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Ico a (2 * a), ∀ y ∈ K,
      ∀ (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.aCovArr G x₀ s k v i j l y| ≤ C := by
  classical
  -- ## The chart matrix is jointly `C^∞` at every point of the open slab
  have hjoint : ∀ p ∈ (Set.Ioo 0 T) ×ˢ (extChartAt I x₀).target,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) p := by
    rintro ⟨t, y⟩ hp
    have hwi := Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth_gen (I := I) (M := M)
      hG ⟨le_of_lt hp.1.1, hp.1.2⟩ x₀ hp.2
    refine hwi.contDiffAt ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hp.1) Set.Ioo_subset_Ico_self)
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hp.2)
  -- ## The closed slab is compact and sits inside that open set
  have hKslab : IsCompact (Set.Icc a (2 * a) ×ˢ K) :=
    (isCompact_Icc (a := a) (b := 2 * a)).prod hK
  have hsub : Set.Icc a (2 * a) ×ˢ K ⊆ (Set.Ioo 0 T) ×ˢ (extChartAt I x₀).target := by
    rintro ⟨t, y⟩ hp
    exact ⟨⟨lt_of_lt_of_le ha hp.1.1, lt_of_le_of_lt hp.1.2 h2a⟩, hKt hp.2⟩
  -- ## Uniform jet bounds for the chart matrix
  have hjets : ∀ kk : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico a (2 * a), ∀ y ∈ K,
      ‖iteratedFDeriv ℝ kk (fun y' : E => Work.Diff.EXT.chartMat G x₀ t y') y‖ ≤ C := by
    intro kk
    obtain ⟨C, hC0, hC⟩ := jets_bound_of_contDiffAt_compact
      (E := ℝ × E) (F := MatE (E := E))
      (f := fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      (O := (Set.Ioo 0 T) ×ˢ (extChartAt I x₀).target)
      (K := Set.Icc a (2 * a) ×ˢ K) hKslab hsub hjoint kk
    refine ⟨C, hC0, fun t ht y hy => ?_⟩
    have hmem : (t, y) ∈ Set.Icc a (2 * a) ×ˢ K := ⟨⟨ht.1, le_of_lt ht.2⟩, hy⟩
    exact le_trans (norm_iteratedFDeriv_slice_le (k := kk) (h := hjoint (t, y) (hsub hmem)))
      (hC (t, y) hmem)
  -- ## Uniform ellipticity of the chart matrix
  have hell : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ico a (2 * a), ∀ y ∈ K,
      ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        δ * ∑ i, (v i) ^ 2
          ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMat G x₀ t y i j := by
    obtain ⟨δ, hδ, hδb⟩ := uniform_posDef_of_compact
      (A := fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      (C := Set.Icc a (2 * a) ×ˢ K) hKslab
      (fun p hp i j => (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp
        (hjoint p (hsub hp)).continuousAt))
      (fun p hp v hv => Work.Diff.EXT.chartMatFun_posDef_target (G p.1) x₀ (hKt hp.2) hv)
    exact ⟨δ, hδ, fun t ht y hy v =>
      hδb (t, y) ⟨⟨ht.1, le_of_lt ht.2⟩, hy⟩ v⟩
  -- ## Pointwise smoothness of the spatial slices
  have hsm : ∀ t ∈ Set.Ico a (2 * a), ∀ y ∈ K, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.EXT.chartMat G x₀ t y') y := by
    intro t ht y hy
    exact (hjoint (t, y) (hsub ⟨⟨ht.1, le_of_lt ht.2⟩, hy⟩)).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  -- ## Assembly: `aCovArr_bound_of_jets` with `T' = 2a`
  have hdiv : 2 * a / 2 = a := by ring
  obtain ⟨C, hC0, hC⟩ := aCovArr_bound_of_jets (I := I) (M := M) G (2 * a) x₀ K hK hKt
    (by simpa only [hdiv] using hjets)
    (by simpa only [hdiv] using hell)
    (by simpa only [hdiv] using hsm) k
  refine ⟨C, hC0, fun s hs y hy v i j l => hC s ?_ y hy v i j l⟩
  exact ⟨by rw [hdiv]; exact hs.1, hs.2⟩

end Work.Diff.EXT.ConnCov
