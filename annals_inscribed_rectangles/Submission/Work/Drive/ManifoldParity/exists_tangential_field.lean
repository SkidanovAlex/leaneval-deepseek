import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ManifoldParity.exists_local_graph
import Submission.Work.Drive.ManifoldParity.exists_curve_data
import Submission.Work.ManifoldParity.exists_continuous_tangent_field_of_local_data
import Submission.Work.ManifoldParity.exists_parallel_smooth_field
import Submission.Work.Drive.ManifoldParity.InterSetDefs
import Submission.Work.Drive.ManifoldParity.TangentialDefs
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.cofactorVec_mem_ker
import Submission.Work.Drive.cofactorVec_ne_zero_of_surjective
import Submission.Work.Drive.flowField_basic
import Submission.Work.Drive.flowField_on_box

/-!
# A nowhere-zero tangential vector field along the intersection set

`Work.Drive.ManifoldParity.exists_tangential_field`: for a smooth `4`-manifold `M` and two smooth maps
`D : ℝ² → M`, `N : ℝ³ → M` whose derivatives together span the tangent space at every point of the
intersection set `K = {x ∈ [0,1]⁵ | D (sqPart x) = N (cbPart x)}`, there is a smooth compactly
supported vector field `V : ℝ⁵ → ℝ⁵` which is non-zero on `K` and tangential to `K` (i.e. killed by
the derivative of every charted difference map `chartDiff p D N`).

## The route (see `EXISTS_TANGENTIAL_FIELD_PLAN.md` for the full record)

The tangency condition is *chart independent*: at a meeting point `x` of `chartRegion p D N`,
`fderiv (chartDiff p D N) x = tangentCoordChange … ∘ Lfun D N x` with an invertible change of
coordinates (`fderiv_chartDiff_eq`), so on `K` the condition is exactly
`Lfun D N x (V x) = 0`, where `Lfun D N x = (mfderiv D) ∘ sqPartCLM - (mfderiv N) ∘ cbPartCLM`
is the difference of the two *manifold* derivatives (`TangentialDefs.lean`).  By
`Lfun_surjective` this is a one-dimensional kernel — the tangent line of the intersection
`1`-manifold.  So the task is: a smooth, compactly supported, nowhere-zero section of that line
bundle.

The assembly (this file, section "Statement of the remaining step") is

1. `exists_curve_data` (delegated): at every `x ∈ K` the zero set
   `Z = {y | D (sqPart y) = N (cbPart y)}` is *locally a graph* over some coordinate `i`
   (`exists_local_graph` because `fderiv (chartDiff p D N) x` is surjective and some coordinate
   hyperplane still maps onto the target), with graph curve `γ`, so that on a neighbourhood
   `R ∋ x` of the chart region, `y ∈ Z ↔ y = γ (y i)`; moreover the frame `fderiv γ (· i) 1` is
   tangent along `Z`: `Lfun D N y (fderiv γ (y i) 1) = 0` on meeting points (chain rule plus
   `fderiv_chartDiff_eq`).
2. `Work.ManifoldParity.exists_continuous_tangent_field_of_local_data` (delegated): the *hard* step —
   the tangent line bundle of the compact `1`-manifold with boundary `K` (presented by the local
   graph data of step 1) is trivializable, i.e. there is a *continuous* non-vanishing `U` on `K`
   parallel to every local frame.  (`interSet` is *not* locally a graph at points of `∂[0,1]⁵` —
   there it is a one-sided arc — so `Work.ManifoldParity.graph_tangent_field` cannot be applied
   directly; the sign/monodromy of the line bundle is the content.)
3. `Work.ManifoldParity.exists_parallel_smooth_field` (delegated): smoothing — from a continuous
   non-vanishing `U` and local smooth frames parallel to it, build a *smooth* compactly supported
   `V` with `V x = c • U x` (`c ≠ 0`) on `K`.
4. Combining: `V x = c • U x` for `x ∈ K`, and `Lfun D N x (U x) = 0` by step 1, whence
   `fderiv (chartDiff p D N) x (V x) = tangentCoordChange … (Lfun D N x (V x)) = 0` for every `p`.

The lemmas of the old gauge-corrected route above are kept because they are proved and harmless;
note that the "route (A)" smoothness of a fixed chart's derivative (`contMDiffOn_mfderiv_chartAt`)
is *false* for a general `ChartedSpace` (`wild_charts_counterexample.lean`) and has been removed.
-/

namespace Work.Drive.ManifoldParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## Elementary generalities -/

/-- A smooth function on an open set which is multiplied by a function whose topological support is
contained in that open set is smooth everywhere. -/
theorem contDiff_smul_of_tsupport_subset {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {ψ : E → ℝ} {U : Set E}
    (hψ : ContDiff ℝ Ctop ψ) (hU : IsOpen U) (hg : ContDiffOn ℝ Ctop g U)
    (hsupp : tsupport ψ ⊆ U) : ContDiff ℝ Ctop (fun x => ψ x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hψ.contDiffAt.smul ((hg.contDiffAt (hU.mem_nhds hx))))
  · have hx' : x ∉ tsupport ψ := fun h => hx (hsupp h)
    have hev : ψ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]

/-- The topological support of a finite sum of functions is contained in the union of the
topological supports. -/
theorem tsupport_finset_sum_subset {E ι : Type*} [TopologicalSpace E] (t : Finset ι)
    (β : ι → E → ℝ) :
    tsupport (fun z => ∑ y ∈ t, β y z) ⊆ ⋃ y ∈ t, tsupport (β y) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h1 : (fun z : E => ∑ y ∈ insert a s, β y z) = fun z => β a z + ∑ y ∈ s, β y z := by
      funext z; rw [Finset.sum_insert ha]
    rw [h1]
    refine (tsupport_add _ _).trans ?_
    rw [Finset.set_biUnion_insert]
    exact Set.union_subset_union (subset_refl _) ih

/-- The topological support of a bump function is contained in the closed ball of radius `rOut`. -/
theorem tsupport_bump_subset_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] {c : E} (f : ContDiffBump c) :
    tsupport f ⊆ Metric.closedBall c f.rOut := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  by_contra hmem
  exact hx (f.zero_of_le_dist (le_of_lt (not_le.mp (fun h => hmem (Metric.mem_closedBall.mpr h)))))

/-- **A bump which is positive on a compact set, supported in an open set and vanishing on a closed
set disjoint from it.** -/
theorem bump_positive_of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] {K L U : Set E} (hK : IsCompact K) (hL : IsClosed L) (hU : IsOpen U)
    (hKU : K ⊆ U) (hKL : Disjoint K L) :
    ∃ ψ : E → ℝ, ContDiff ℝ Ctop ψ ∧ (∀ x ∈ K, 0 < ψ x) ∧
      tsupport ψ ⊆ U ∧ Disjoint (tsupport ψ) L := by
  classical
  have hpoint : ∀ x : E, x ∈ K → ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U ∩ Lᶜ := by
    intro x hx
    obtain ⟨r₁, hr₁, h₁⟩ := Metric.isOpen_iff.mp hU x (hKU hx)
    have hxL : x ∉ L := fun h => (hKL.le_bot ⟨hx, h⟩)
    obtain ⟨r₂, hr₂, h₂⟩ := Metric.isOpen_iff.mp hL.isOpen_compl x hxL
    exact ⟨min r₁ r₂, lt_min hr₁ hr₂, fun y hy => ⟨
      h₁ (Metric.ball_subset_ball (min_le_left _ _) hy),
      h₂ (Metric.ball_subset_ball (min_le_right _ _) hy)⟩⟩
  let r : E → ℝ := fun x => if h : x ∈ K then (hpoint x h).choose else 1
  have hrpos : ∀ x ∈ K, 0 < r x := fun x hx => by
    have := (hpoint x hx).choose_spec.1
    simpa only [r, dif_pos hx] using this
  have hrsub : ∀ x ∈ K, Metric.ball x (r x) ⊆ U ∩ Lᶜ := fun x hx => by
    have := (hpoint x hx).choose_spec.2
    simpa only [r, dif_pos hx] using this
  have hcov : K ⊆ ⋃ y : K, Metric.ball (y : E) (r (y : E) / 4) := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    have := hrpos x hx
    linarith
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => Metric.ball (y : E) (r (y : E) / 4))
    (fun y => Metric.isOpen_ball) hcov
  refine ⟨fun z => ∑ y ∈ t, (⟨r (y : E) / 4, r (y : E) / 2, by have := hrpos (y : E) y.2; linarith,
      by have := hrpos (y : E) y.2; linarith⟩ : ContDiffBump (y : E)) z, ?_, ?_, ?_, ?_⟩
  · exact ContDiff.sum fun y _ => ContDiffBump.contDiff _
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
    have hb : (⟨r (y : E) / 4, r (y : E) / 2, by have := hrpos (y : E) y.2; linarith,
        by have := hrpos (y : E) y.2; linarith⟩ : ContDiffBump (y : E)) x = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall]
      have h2 := Metric.mem_ball.mp hxy
      have h3 : r (y : E) / 4 ≤ r (y : E) / 2 := by have := hrpos (y : E) y.2; linarith
      linarith [dist_comm x (y : E)]
    have hnonneg : ∀ y' ∈ t, 0 ≤ (⟨r (y' : E) / 4, r (y' : E) / 2, by
        have := hrpos (y' : E) y'.2; linarith,
        by have := hrpos (y' : E) y'.2; linarith⟩ : ContDiffBump (y' : E)) x :=
      fun y' _ => ContDiffBump.nonneg _
    have : (1 : ℝ) ≤ ∑ y' ∈ t, (⟨r (y' : E) / 4, r (y' : E) / 2, by
        have := hrpos (y' : E) y'.2; linarith,
        by have := hrpos (y' : E) y'.2; linarith⟩ : ContDiffBump (y' : E)) x := by
      refine le_trans (le_of_eq hb.symm) ?_
      exact Finset.single_le_sum hnonneg hyt
    linarith
  · refine (tsupport_finset_sum_subset t _).trans ?_
    refine iUnion₂_subset fun y hy => ?_
    refine (tsupport_bump_subset_closedBall _).trans ?_
    refine (Metric.closedBall_subset_ball ?_).trans
      ((hrsub (y : E) y.2).trans (inter_subset_left ..))
    have := hrpos (y : E) y.2
    linarith
  · refine (disjoint_compl_left : Disjoint (Lᶜ) L).mono_left ?_
    refine (tsupport_finset_sum_subset t _).trans ?_
    refine iUnion₂_subset fun y hy => ?_
    refine (tsupport_bump_subset_closedBall _).trans ?_
    refine (Metric.closedBall_subset_ball ?_).trans
      ((hrsub (y : E) y.2).trans (inter_subset_right ..))
    have := hrpos (y : E) y.2
    linarith


/-- At a point of the intersection set, the chart at the common image point contains both images. -/
theorem mem_chartRegion_self (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    {x : Amb 4} (heq : D (sqPart x) = N (cbPart x)) :
    x ∈ chartRegion (D (sqPart x)) D N := by
  rw [mem_chartRegion]
  have hmem : ∀ y : M, y ∈ (chr y).source := fun y => by
    rw [chr, ← extChartAt_source (I := 𝓡 4) y]
    exact mem_extChartAt_source _
  exact ⟨hmem _, by rw [heq]; exact hmem _⟩

/-- **The cut-off family.**  There is a finite family of smooth nonnegative cut-off functions on
`ℝ⁵` whose topological supports are contained in chart regions of `M` and which is strictly positive
on the intersection set. -/
theorem exists_cutoff_family (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N) :
    ∃ (n : ℕ) (p : Fin n → M) (χ : Fin n → Amb 4 → ℝ),
      (∀ i, ContDiff ℝ Ctop (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ i, tsupport (χ i) ⊆ chartRegion (p i) D N) ∧
      (∀ x ∈ interSet D N, ∃ i, 0 < χ i x) := by
  classical
  have hK : IsCompact (interSet D N) := isCompact_interSet D N hD.continuous hN.continuous
  have hpt : ∀ x : Amb 4, x ∈ interSet D N →
      ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ chartRegion (D (sqPart x)) D N := by
    intro x hx
    exact Metric.isOpen_iff.mp (isOpen_chartRegion _ D N hD.continuous hN.continuous) x
      (mem_chartRegion_self D N (mem_interSet.mp hx).2)
  let r : Amb 4 → ℝ := fun x => if h : x ∈ interSet D N then (hpt x h).choose else 1
  have hrpos : ∀ x ∈ interSet D N, 0 < r x := fun x hx => by
    have := (hpt x hx).choose_spec.1
    simpa only [r, dif_pos hx] using this
  have hrsub : ∀ x ∈ interSet D N, Metric.ball x (r x) ⊆ chartRegion (D (sqPart x)) D N :=
    fun x hx => by
      have := (hpt x hx).choose_spec.2
      simpa only [r, dif_pos hx] using this
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun y : ↥(interSet D N) => Metric.ball (y : Amb 4) (r (y : Amb 4) / 4))
    (fun _ => Metric.isOpen_ball)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, by
      rw [Metric.mem_ball, dist_self]
      have := hrpos y hy
      linarith⟩)
  let c : Fin t.card → Amb 4 := fun i => (t.equivFin.symm i).1.1
  have hcK : ∀ i, c i ∈ interSet D N := fun i => (t.equivFin.symm i).1.2
  have hrp : ∀ i, 0 < r (c i) := fun i => hrpos _ (hcK i)
  have hrc : ∀ i, Metric.ball (c i) (r (c i)) ⊆ chartRegion (D (sqPart (c i))) D N :=
    fun i => hrsub _ (hcK i)
  let b : (i : Fin t.card) → ContDiffBump (c i) := fun i =>
    ⟨r (c i) / 4, r (c i) / 2, by have := hrp i; linarith, by have := hrp i; linarith⟩
  refine ⟨t.card, fun i => D (sqPart (c i)), fun i => b i, ?_, ?_, ?_, ?_⟩
  · exact fun i => ContDiffBump.contDiff (b i)
  · exact fun i x => ContDiffBump.nonneg (b i)
  · intro i
    refine (tsupport_bump_subset_closedBall (b i)).trans ?_
    refine (Metric.closedBall_subset_ball ?_).trans (hrc i)
    change r (c i) / 2 < r (c i)
    have := hrp i; linarith
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
    have hcent : c (t.equivFin ⟨y, hyt⟩) = (y : Amb 4) := by
      simp only [c, Equiv.symm_apply_apply]
    refine ⟨t.equivFin ⟨y, hyt⟩, ?_⟩
    have hb1 : b (t.equivFin ⟨y, hyt⟩) x = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall]
      change dist x (c (t.equivFin ⟨y, hyt⟩)) ≤ r (c (t.equivFin ⟨y, hyt⟩)) / 4
      rw [hcent]
      have h2 : dist x (y : Amb 4) < r (y : Amb 4) / 4 := Metric.mem_ball.mp hxy
      linarith
    change 0 < b (t.equivFin ⟨y, hyt⟩) x
    rw [hb1]
    norm_num


/-! ## The chart-independent difference of the derivatives -/

open scoped Bundle

/-- **`Lfun` is surjective at a meeting point in the box.**  This is the transversality hypothesis
`htrans` transported to the chart-independent difference of the two manifold derivatives. -/
theorem Lfun_surjective (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap = ⊤)
    {x : Amb 4} (hx : x ∈ Submission.Drive.unitBox 4)
    (heq : D (sqPart x) = N (cbPart x)) :
    Function.Surjective (Lfun D N x) := by
  intro w
  have hmem : w ∈ LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap := by
    rw [htrans x hx heq]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨σ, hσ⟩ := LinearMap.mem_range.mp ha
  obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp hb
  have hA : mdD D x σ = a := hσ
  have hB : mdN N x τ = b := hτ
  refine ⟨mkPart σ (-τ), ?_⟩
  rw [Lfun_mkPart, map_neg, hA, hB, sub_neg_eq_add, hab]

/-- **The derivative of the charted difference map through `Lfun`.**  At a meeting point the two
change-of-coordinates maps of `fderiv_chartDiff_apply` coincide, so the derivative is the (fixed,
invertible) change of coordinates applied to `Lfun`. -/
theorem fderiv_chartDiff_eq (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x))
    (v : Amb 4) :
    fderiv ℝ (chartDiff p D N) x v =
      tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x)) (Lfun D N x v) := by
  rw [fderiv_chartDiff_apply p D N hD hN hx]
  have htc : tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x)) =
      tangentCoordChange (𝓡 4) (N (cbPart x)) p (N (cbPart x)) := by rw [← heq]
  rw [htc, ← map_sub, ← Lfun_apply]


/-- `B_p (b x)` is the inverse of the change-of-coordinates `tangentCoordChange` from the chart at
the point itself to the chart at `p`. -/
theorem symmLField_tangentCoordChange (D : EuclideanSpace ℝ (Fin 2) → M) {p : M} {x : Amb 4}
    (hx : D (sqPart x) ∈ (chr p).source) (w : Tgt 4) :
    symmLField D p x
      (tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x)) w) = w := by
  have hb : D (sqPart x) ∈ (triv p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  have hclm : (triv p).continuousLinearMapAt ℝ (D (sqPart x)) =
      tangentCoordChange (𝓡 4) (D (sqPart x)) p (D (sqPart x)) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := 𝓡 4) hx,
      ← mfderiv_chartAt_eq_tangentCoordChange (I := 𝓡 4)
        (H := EuclideanSpace ℝ (Fin 4)) hx]
    have hfun : (extChartAt (𝓡 4) p : M → EuclideanSpace ℝ (Fin 4)) = chr p := by
      funext z
      simp [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_def, chr]
    rw [hfun]
    rfl
  rw [← hclm]
  exact Bundle.Trivialization.symmL_continuousLinearMapAt (triv p) hb w

/-- **The derivative of the gauge-corrected local difference map.**  At a meeting point the value of
`gcorr` vanishes, so the derivative is `B_p (b x)` applied to the derivative of `chartDiff`, which is
`Lfun` by `symmLField_tangentCoordChange`. -/
theorem fderiv_gcorr (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N) (p : M)
    (hB : ContDiffOn ℝ Ctop (symmLField D p) {x : Amb 4 | D (sqPart x) ∈ (chr p).source})
    {x : Amb 4} (hx : x ∈ chartRegion p D N) (heq : D (sqPart x) = N (cbPart x))
    (v : Amb 4) :
    fderiv ℝ (gcorr D N p) x v = Lfun D N x v := by
  have hopen : {x : Amb 4 | D (sqPart x) ∈ (chr p).source} ∈ 𝓝 x := by
    have hcont : Continuous fun x : Amb 4 => D (sqPart x) :=
      hD.continuous.comp (by unfold sqPart; fun_prop)
    exact (hcont.isOpen_preimage _ (chr p).open_source).mem_nhds hx.1
  have hcd : ContDiffOn ℝ Ctop (chartDiff p D N) (chartRegion p D N) :=
    contDiffOn_chartDiff p D N hD hN
  have hc : DifferentiableAt ℝ (symmLField D p) x :=
    (hB.contDiffAt hopen).differentiableAt (by simp)
  have hu : DifferentiableAt ℝ (chartDiff p D N) x :=
    ((hcd.contDiffAt ((isOpen_chartRegion p D N hD.continuous hN.continuous).mem_nhds hx)).differentiableAt
      (by simp))
  change fderiv ℝ (fun y => symmLField D p y ((chartDiff p D N) y)) x v = Lfun D N x v
  rw [fderiv_clm_apply hc hu, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have hzero : (chartDiff p D N) x = 0 := (chartDiff_eq_zero_iff hx).mpr heq
  rw [hzero, map_zero, add_zero, fderiv_chartDiff_eq p D N hD hN hx heq]
  exact symmLField_tangentCoordChange D hx.1 (Lfun D N x v)

/-- **The gauge-corrected local pieces glue to a globally smooth map.** -/
theorem contDiff_sum_gcorr (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    {n : ℕ} (p : Fin n → M) (χ : Fin n → Amb 4 → ℝ)
    (hχ : ∀ i, ContDiff ℝ Ctop (χ i))
    (hsupp : ∀ i, tsupport (χ i) ⊆ chartRegion (p i) D N)
    (hg : ∀ i, ContDiffOn ℝ Ctop (gcorr D N (p i)) (chartRegion (p i) D N)) :
    ContDiff ℝ Ctop (fun x => ∑ i, χ i x • gcorr D N (p i) x) := by
  refine ContDiff.sum fun i _ => ?_
  exact contDiff_smul_of_tsupport_subset (hχ i)
    (isOpen_chartRegion (p i) D N hD.continuous hN.continuous) (hg i) (hsupp i)

/-! ## Smoothness of the derivative of a fixed chart (route A) -/

/-- **Route (A), step 2**: the *raw* second component of the bundled tangent map of a fixed chart is
smooth.  The extraction is `S`-free because the codomain is the tangent bundle of the model space
(`contMDiff_snd_tangentBundle_modelSpace`). -/
theorem contMDiffOn_tangentMapWithin_snd (q : M) :
    ContMDiffOn ((𝓡 4).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 4))) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) Ctop
      (fun z : TangentBundle (𝓡 4) M =>
        (tangentMapWithin (𝓡 4) (𝓡 4) (chr q) (chr q).source z).2)
      ((π (EuclideanSpace ℝ (Fin 4)) (TangentSpace (𝓡 4))) ⁻¹' (chr q).source) := by
  have hf : ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr q) (chr q).source := by
    simpa [chr] using contMDiffOn_extChartAt (I := 𝓡 4) (x := q) (n := Ctop)
  have ht := hf.contMDiffOn_tangentMapWithin (m := Ctop) (by simp)
    (fun x hx => (chr q).open_source.uniqueMDiffWithinAt hx)
  have hsnd : ContMDiff (𝓡 4).tangent 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) Ctop
      (fun p : TangentBundle (𝓡 4) (EuclideanSpace ℝ (Fin 4)) => p.2) :=
    contMDiff_snd_tangentBundle_modelSpace (EuclideanSpace ℝ (Fin 4)) (𝓡 4)
  intro z hz
  exact (hsnd.contMDiffAt).comp_contMDiffWithinAt _ (ht z hz)

/-! ## Auxiliary lemmas for the assembly

The final assembly uses

* `finrank_ker_Lfun`: the kernel of `Lfun` at a meeting point in the box is one dimensional
  (rank-nullity plus `Lfun_surjective`), so "being in the kernel" is the same as "being parallel";
* `contDiff_frame`: the frame `y ↦ fderiv ℝ γ (y i) 1` of a graph curve is smooth;
* `exists_smul_of_finrank_eq_one`: two nonzero vectors of a one-dimensional subspace are
  proportional.
-/

/-- The kernel of `Lfun` at a meeting point in the box is one dimensional. -/
theorem finrank_ker_Lfun (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap = ⊤)
    {x : Amb 4} (hx : x ∈ interSet D N) :
    Module.finrank ℝ (LinearMap.ker (Lfun D N x : Amb 4 →ₗ[ℝ] Tgt 4)) = 1 := by
  have hsurj : Function.Surjective (Lfun D N x) :=
    Lfun_surjective D N htrans hx.1 hx.2
  have hrange : LinearMap.range (Lfun D N x : Amb 4 →ₗ[ℝ] Tgt 4) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have h := LinearMap.finrank_range_add_finrank_ker (Lfun D N x : Amb 4 →ₗ[ℝ] Tgt 4)
  rw [hrange, finrank_top, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at h
  omega

/-- The frame of a graph curve is smooth. -/
theorem contDiff_frame {γ : ℝ → Amb 4} (hγ : ContDiff ℝ Ctop γ) (i : Fin 5) :
    ContDiff ℝ Ctop (fun y : Amb 4 => fderiv ℝ γ (y i) 1) := by
  have hfd : ContDiff ℝ Ctop (fun p : ℝ => fderiv ℝ γ p) := hγ.fderiv_right (by simp)
  have hproj : ContDiff ℝ Ctop (fun y : Amb 4 => y i) := by
    simpa using (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i).contDiff
  exact (hfd.comp hproj).clm_apply contDiff_const

/-- Two nonzero vectors of a one-dimensional subspace are proportional. -/
theorem exists_smul_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {K : Submodule ℝ V} (hK : Module.finrank ℝ K = 1) {u v : V}
    (hu : u ∈ K) (hv : v ∈ K) (hu0 : u ≠ 0) (hv0 : v ≠ 0) : ∃ c : ℝ, c ≠ 0 ∧ v = c • u := by
  have hspan_le : (ℝ ∙ u : Submodule ℝ V) ≤ K := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact K.smul_mem a hu
  have hfin : Module.finrank ℝ (ℝ ∙ u : Submodule ℝ V) = 1 := finrank_span_singleton hu0
  have heq : (ℝ ∙ u : Submodule ℝ V) = K :=
    Submodule.eq_of_le_of_finrank_le hspan_le (by rw [hfin, hK])
  have hv' : v ∈ (ℝ ∙ u : Submodule ℝ V) := by rw [heq]; exact hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv'
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [zero_smul] at hc
  exact hv0 hc.symm

/-! ## Statement of the remaining step -/


open scoped Manifold ContDiff in
theorem exists_tangential_field {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (htrans : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x)).toLinearMap = ⊤) :
    ∃ V : Work.Drive.Amb 4 → Work.Drive.Amb 4,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ HasCompactSupport V ∧
      (∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
        D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → V x ≠ 0) ∧
      (∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
        D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → ∀ p : M,
        x ∈ Work.Drive.chartRegion p D N →
        fderiv ℝ (Work.Drive.chartDiff p D N) x (V x) = 0) := by
  classical
  set Z : Set (Amb 4) := {y | D (sqPart y) = N (cbPart y)} with hZdef
  have hZcl : IsClosed Z := by
    rw [hZdef]
    exact isClosed_eq (hD.continuous.comp (by unfold sqPart; fun_prop))
      (hN.continuous.comp (by unfold cbPart; fun_prop))
  have hKcomp : IsCompact (interSet D N) :=
    isCompact_interSet D N hD.continuous hN.continuous
  have hKZ : interSet D N ⊆ Z := fun y hy => hy.2
  have hdata : ∀ x ∈ interSet D N, ∃ (i : Fin 5) (γ : ℝ → Amb 4) (R : Set (Amb 4)),
      IsOpen R ∧ x ∈ R ∧ ContDiff ℝ Ctop γ ∧ (∀ t, (γ t) i = t) ∧ γ (x i) = x ∧
      (∀ y ∈ R, (D (sqPart y) = N (cbPart y) ↔ y = γ (y i))) ∧
      (∀ y ∈ R, D (sqPart y) = N (cbPart y) → Lfun D N y (fderiv ℝ γ (y i) 1) = 0) :=
    fun x hx => Work.Drive.ManifoldParity.exists_curve_data D N hD hN htrans hx
  have hdataZ : ∀ x ∈ interSet D N, ∃ (i : Fin 5) (γ : ℝ → Amb 4) (R : Set (Amb 4)),
      IsOpen R ∧ x ∈ R ∧ ContDiff ℝ Ctop γ ∧ (∀ t, (γ t) i = t) ∧ γ (x i) = x ∧
      (∀ y ∈ R, y ∈ Z ↔ y = γ (y i)) := by
    intro x hx
    obtain ⟨i, γ, R, h1, h2, h3, h4, h5, h6, -⟩ := hdata x hx
    exact ⟨i, γ, R, h1, h2, h3, h4, h5, fun y hy => by rw [hZdef]; exact h6 y hy⟩
  obtain ⟨U, hUcont, hUne, hUpar⟩ :=
    Work.ManifoldParity.exists_continuous_tangent_field_of_local_data (m := 4)
      (interSet D N) Z hKcomp hZcl hKZ hdataZ
  have hUtan : ∀ x ∈ interSet D N, Lfun D N x (U x) = 0 := by
    intro x hx
    obtain ⟨i, γ, R, hRopen, hxR, hγ, hi, hxi, hsym, htang⟩ := hdata x hx
    obtain ⟨c, hc, hcU⟩ := hUpar x hx i γ R hRopen hxR hγ hi hxi
      (fun y hy => by rw [hZdef]; exact hsym y hy)
    rw [hcU, map_smul, htang x hxR hx.2, smul_zero]
  have hloc : ∀ x ∈ interSet D N, ∃ (W : Amb 4 → Amb 4) (UU : Set (Amb 4)),
      IsOpen UU ∧ x ∈ UU ∧ ContDiff ℝ Ctop W ∧
      ∀ y ∈ interSet D N ∩ UU, ∃ c : ℝ, c ≠ 0 ∧ W y = c • U y := by
    intro x hx
    obtain ⟨i, γ, R, hRopen, hxR, hγ, hi, hxi, hsym, htang⟩ := hdata x hx
    refine ⟨fun y => fderiv ℝ γ (y i) 1, R, hRopen, hxR, contDiff_frame hγ i, ?_⟩
    intro y hy
    obtain ⟨hyK, hyR⟩ := hy
    have hWy : Lfun D N y (fderiv ℝ γ (y i) 1) = 0 := htang y hyR hyK.2
    have hUy : Lfun D N y (U y) = 0 := hUtan y hyK
    have hWne : fderiv ℝ γ (y i) 1 ≠ 0 := by
      intro h0
      have hcoord : (fderiv ℝ γ (y i) 1) i = 1 := by
        set ℓ : ℝ → ℝ := fun t => (γ t) i with hℓ
        have hproj_eq : (fun v : Amb 4 => v i)
            = ⇑(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i) := by
          funext v; rw [PiLp.proj_apply]
        have h2 : fderiv ℝ ℓ (y i)
            = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i).comp (fderiv ℝ γ (y i)) := by
          rw [hℓ, show (fun t : ℝ => (γ t) i) = (fun v : Amb 4 => v i) ∘ γ from rfl, hproj_eq]
          exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i).hasFDerivAt.comp (y i)
            (hγ.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
        have h3 : fderiv ℝ ℓ (y i) 1 = deriv ℓ (y i) :=
          (fderiv_apply_one_eq_deriv (f := ℓ) (x := y i)).symm
        have hℓid : ℓ = fun t : ℝ => t := by
          funext t; exact hi t
        have h4 : deriv ℓ (y i) = 1 := by rw [hℓid]; simp
        have h5 : (fderiv ℝ γ (y i) 1) i = fderiv ℝ ℓ (y i) 1 := by
          rw [h2, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
        rw [h5, h3, h4]
      rw [h0] at hcoord
      simp at hcoord
    have hUne' : U y ≠ 0 := hUne y hyK
    have hdim := finrank_ker_Lfun D N htrans hyK
    exact exists_smul_of_finrank_eq_one hdim hUy hWy hUne' hWne
  obtain ⟨V, hVsmooth, hVsupp, hVne, hVpar⟩ :=
    Work.ManifoldParity.exists_parallel_smooth_field (n := 5) (interSet D N) hKcomp U hUcont hUne hloc
  refine ⟨V, hVsmooth, hVsupp, ?_, ?_⟩
  · intro x hxbox heq
    exact hVne x ⟨hxbox, heq⟩
  · intro x hxbox heq p hxreg
    obtain ⟨c, hc, hcV⟩ := hVpar x ⟨hxbox, heq⟩
    rw [hcV, map_smul, fderiv_chartDiff_eq p D N hD hN hxreg heq, hUtan x ⟨hxbox, heq⟩,
      map_zero, smul_zero]

end

end Work.Drive.ManifoldParity
