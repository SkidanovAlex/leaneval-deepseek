import Mathlib
import Submission.Work.HP.Q44Child.LatticeCountDefs

/-!
# Counting lattice points in a ball

If every point of `E` is within `μ` of a `ℤ`-lattice `L ⊆ E`, then the closed Voronoi cell
`V = {x | ∀ u : L, ‖x‖ ≤ ‖x - u‖}` is an additive fundamental domain of `L`, contained in
`closedBall 0 μ`.  The translates `u +ᵥ V` by lattice points `u` of norm `≤ T` are a.e. disjoint
and all lie in `closedBall 0 (T + μ)`, hence
`#{u : L | ‖u‖ ≤ T} * vol V ≤ vol (closedBall 0 (T + μ))`, and `vol V = covolume L`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Metric Set
open scoped ENNReal Pointwise RealInnerProductSpace

namespace Work.HP.Q44Child

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The lattice points of norm at most `T`. -/
def latBall (L : Submodule ℤ E) (T : ℝ) : Set ↥L := {u | ‖(u : E)‖ ≤ T}

@[simp] lemma mem_latBall {L : Submodule ℤ E} {T : ℝ} {u : ↥L} :
    u ∈ latBall L T ↔ ‖(u : E)‖ ≤ T := Iff.rfl

/-- Translating a set does not change its volume. -/
lemma volume_vadd_set (S : Set E) (z : E) : volume (z +ᵥ S) = volume S := by
  have hset : z +ᵥ S = (fun x : E => x + (-z)) ⁻¹' S := by
    ext x
    rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
    rw [show (-z +ᵥ x) = x + (-z) from by rw [vadd_eq_add]; exact add_comm (-z) x]
  rw [hset]
  exact MeasureTheory.measure_preimage_add_right volume (-z) S

/-- The set `{x | ⟪x, g⟫ = c}` has measure zero for `g ≠ 0`. -/
lemma volume_inner_eq_zero (g : E) (hg : g ≠ 0) (c : ℝ) :
    volume {x : E | inner ℝ (x) (g) = c} = 0 := by
  have hgn : (0 : ℝ) < ‖g‖ := norm_pos_iff.mpr hg
  set K : Submodule ℝ E := LinearMap.ker (innerSL ℝ g).toLinearMap with hK
  have hmem : ∀ x : E, x ∈ K ↔ inner ℝ (x) (g) = 0 := by
    intro x
    rw [hK, LinearMap.mem_ker]
    show (innerSL ℝ g) x = 0 ↔ inner ℝ (x) (g) = 0
    rw [innerSL_apply_apply]
    show inner ℝ (g) (x) = 0 ↔ inner ℝ (x) (g) = 0
    exact ⟨fun h => by rw [real_inner_comm x g] at h; exact h,
      fun h => by rw [← real_inner_comm x g] at h; exact h⟩
  have hKtop : K ≠ ⊤ := by
    intro h
    have hgK : g ∈ K := by rw [h]; trivial
    rw [hmem] at hgK
    have h2 : ‖g‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact hgK
    exact (ne_of_gt (pow_pos hgn 2)) h2
  have hgp : inner ℝ (-((c / ‖g‖ ^ 2) • g)) (g) = -c := by
    rw [inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ c (ne_of_gt (pow_pos hgn 2))]
  have hset : {x : E | inner ℝ (x) (g) = c} = ((c / ‖g‖ ^ 2) • g) +ᵥ (K : Set E) := by
    ext x
    show (inner ℝ (x) (g) = c) ↔ x ∈ ((c / ‖g‖ ^ 2) • g) +ᵥ (K : Set E)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, SetLike.mem_coe]
    rw [show (-((c / ‖g‖ ^ 2) • g) +ᵥ x) = x + (-((c / ‖g‖ ^ 2) • g)) from by
      rw [vadd_eq_add]; exact add_comm _ _]
    rw [show (x + -((c / ‖g‖ ^ 2) • g)) ∈ K ↔ inner ℝ (x + -((c / ‖g‖ ^ 2) • g)) (g) = 0
      from hmem _]
    rw [inner_add_left, hgp]
    constructor <;> intro h <;> linarith
  rw [hset, volume_vadd_set]
  exact MeasureTheory.Measure.addHaar_submodule volume K hKtop

/-- For a discrete lattice, every point has a nearest lattice point. -/
lemma exists_nearestPoint (L : Submodule ℤ E) [DiscreteTopology ↥L] (x : E) :
    ∃ u : L, ∀ v : L, ‖x - (u : E)‖ ≤ ‖x - (v : E)‖ := by
  have hclosed : IsClosed (L : Set E) :=
    AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)
  have hcpt : IsCompact (Metric.closedBall x ‖x‖ ∩ (L : Set E)) :=
    (ProperSpace.isCompact_closedBall x ‖x‖).inter_right hclosed
  have hne : (Metric.closedBall x ‖x‖ ∩ (L : Set E)).Nonempty := by
    refine ⟨(0 : E), ?_, Submodule.zero_mem L⟩
    simp [Metric.mem_closedBall, dist_eq_norm]
  obtain ⟨y, hy, hmin⟩ := hcpt.exists_isMinOn (f := fun z : E => ‖x - z‖) hne
    ((continuous_const.sub continuous_id).norm.continuousOn)
  refine ⟨⟨y, hy.2⟩, fun v => ?_⟩
  by_cases hv : ‖x - (v : E)‖ ≤ ‖x‖
  · refine hmin ⟨?_, v.2⟩
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hv
  · push_neg at hv
    have hyb : ‖x - y‖ ≤ ‖x‖ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hy.1
    exact le_trans hyb hv.le

/-- The closed Voronoi cell is an additive fundamental domain for a discrete lattice. -/
lemma isAddFundamentalDomain_voronoi (L : Submodule ℤ E) [DiscreteTopology ↥L] :
    IsAddFundamentalDomain ↥L (voronoiCell L) volume := by
  refine MeasureTheory.IsAddFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact (voronoiCell_isClosed L).measurableSet.nullMeasurableSet
  · refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨u, hu⟩ := exists_nearestPoint L x
    refine ⟨-u, ?_⟩
    have hcoe : ((-u : ↥L) : E) = -(u : E) := Submodule.coe_neg L u
    have hyx : ((-u : ↥L) +ᵥ x) = x - (u : E) := by
      rw [show ((-u : ↥L) +ᵥ x) = (((-u : ↥L) : E) + x) from rfl, hcoe]
      abel
    rw [hyx]
    intro v
    have h := hu (v + u)
    rw [Submodule.coe_add] at h
    have h2 : x - ((v : E) + (u : E)) = x - (u : E) - (v : E) := by abel
    rwa [h2] at h
  · intro g hg
    refine measure_mono_null ?_ (volume_inner_eq_zero (g : E) (by simpa using hg) (‖(g : E)‖ ^ 2 / 2))
    rintro x ⟨hx1, hx2⟩
    show inner ℝ (x) ((g : E)) = ‖(g : E)‖ ^ 2 / 2
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx1
    have hcoe : ((-g : ↥L) : E) = -(g : E) := Submodule.coe_neg L g
    have hyx : ((-g : ↥L) +ᵥ x) = x - (g : E) := by
      rw [show ((-g : ↥L) +ᵥ x) = (((-g : ↥L) : E) + x) from rfl, hcoe]
      abel
    have h1 : ‖x‖ ≤ ‖x - (g : E)‖ := hx2 g
    have h2 : ‖x - (g : E)‖ ≤ ‖x‖ := by
      have h := hx1 (-g)
      rw [hyx, hcoe] at h
      have h3 : x - (g : E) - (-(g : E)) = x := by abel
      rwa [h3] at h
    have heq : ‖x - (g : E)‖ = ‖x‖ := le_antisymm h2 h1
    have hsq : ‖x - (g : E)‖ ^ 2 = ‖x‖ ^ 2 := by rw [heq]
    rw [norm_sub_sq_real] at hsq
    linarith
  · intro g
    have hfun : (fun x : E => (g : ↥L) +ᵥ x) = (fun x : E => (g : E) + x) := rfl
    rw [hfun]
    exact (MeasureTheory.measurePreserving_add_left volume (g : E)).quasiMeasurePreserving

/-- Counting lattice points in a ball, given a covering radius. -/
theorem lattice_count_le (L : Submodule ℤ E) [DiscreteTopology ↥L] [IsZLattice ℝ L]
    {μ T : ℝ} (hcov : ∀ x : E, ∃ u : L, ‖x - (u : E)‖ ≤ μ) :
    ((latBall L T).ncard : ℝ) ≤
      (volume (Metric.closedBall (0 : E) (T + μ))).toReal / ZLattice.covolume L := by
  classical
  have hF : IsAddFundamentalDomain ↥L (voronoiCell L) volume := isAddFundamentalDomain_voronoi L
  have hcovol : ZLattice.covolume L = (volume (voronoiCell L)).toReal :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hF
  have hVsub : voronoiCell L ⊆ Metric.closedBall (0 : E) μ :=
    voronoiCell_subset_closedBall L hcov
  have hVfin : volume (voronoiCell L) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hVsub) Metric.isBounded_closedBall.measure_lt_top)
  have hIfin : (latBall L T).Finite := by
    refine Set.Finite.of_finite_image ?_ (Subtype.coe_injective.injOn)
    refine (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (Metric.isBounded_closedBall (x := (0 : E)) (r := T))
      (AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup))).subset ?_
    rintro y ⟨u, hu, rfl⟩
    exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hu, u.2⟩
  have hIbal : ∀ u : ↥L, ‖(u : E)‖ ≤ T →
      (u : ↥L) +ᵥ voronoiCell L ⊆ Metric.closedBall (0 : E) (T + μ) := by
    intro u hu y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    have hcoe : ((-u : ↥L) : E) = -(u : E) := Submodule.coe_neg L u
    have hyx : ((-u : ↥L) +ᵥ y) = y - (u : E) := by
      rw [show ((-u : ↥L) +ᵥ y) = (((-u : ↥L) : E) + y) from rfl, hcoe]
      abel
    have hyμ : ‖y - (u : E)‖ ≤ μ := by
      have h := hVsub hy
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero, hyx] at h
    calc ‖y‖ = ‖(y - (u : E)) + (u : E)‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - (u : E)‖ + ‖(u : E)‖ := norm_add_le _ _
      _ ≤ μ + T := add_le_add hyμ hu
      _ = T + μ := add_comm _ _
  have hdisj : ((hIfin.toFinset : Finset ↥L) : Set ↥L).Pairwise
      (fun u v => AEDisjoint volume ((u : ↥L) +ᵥ voronoiCell L)
        ((v : ↥L) +ᵥ voronoiCell L)) :=
    fun a _ b _ hab => hF.aedisjoint hab
  have hnm : ∀ u ∈ hIfin.toFinset,
      NullMeasurableSet ((u : ↥L) +ᵥ voronoiCell L) volume := by
    intro u _
    have h : ((u : ↥L) +ᵥ voronoiCell L)
        = (fun x : E => x - (u : E)) ⁻¹' voronoiCell L := by
      ext x
      rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [show ((-u : ↥L) +ᵥ x) = x - (u : E) from by
        rw [show ((-u : ↥L) +ᵥ x) = (((-u : ↥L) : E) + x) from rfl, Submodule.coe_neg L u]
        abel]
    rw [h]
    exact ((voronoiCell_isClosed L).preimage
      (continuous_id.sub continuous_const)).measurableSet.nullMeasurableSet
  have hunion : (⋃ u ∈ hIfin.toFinset, (u : ↥L) +ᵥ voronoiCell L)
      ⊆ Metric.closedBall (0 : E) (T + μ) := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨u, hu, hy⟩ := hy
    exact hIbal u ((Set.Finite.mem_toFinset hIfin).mp hu) hy
  have hmeas := MeasureTheory.measure_biUnion_finset₀
    (μ := volume) (s := hIfin.toFinset)
    (f := fun u : ↥L => (u : ↥L) +ᵥ voronoiCell L) hdisj hnm
  have hcard : hIfin.toFinset.card = (latBall L T).ncard :=
    (Set.ncard_eq_toFinset_card (latBall L T) hIfin).symm
  have hkey : ((latBall L T).ncard : ℝ≥0∞) * volume (voronoiCell L)
      ≤ volume (Metric.closedBall (0 : E) (T + μ)) := by
    have hsum : ∑ p ∈ hIfin.toFinset, volume ((p : ↥L) +ᵥ voronoiCell L)
        = ∑ p ∈ hIfin.toFinset, volume (voronoiCell L) :=
      Finset.sum_congr rfl (fun p _ => volume_vadd_set (voronoiCell L) (p : E))
    have h1 : ((latBall L T).ncard : ℝ≥0∞) * volume (voronoiCell L)
        = ∑ p ∈ hIfin.toFinset, volume ((p : ↥L) +ᵥ voronoiCell L) := by
      rw [← hcard, hsum, Finset.sum_const, nsmul_eq_mul]
    rw [h1, ← hmeas]
    exact measure_mono hunion
  rw [hcovol]
  have hpos : 0 < (volume (voronoiCell L)).toReal := by
    rw [← hcovol]
    exact ZLattice.covolume_pos L volume
  have hBfin : volume (Metric.closedBall (0 : E) (T + μ)) ≠ ⊤ :=
    ne_of_lt Metric.isBounded_closedBall.measure_lt_top
  have hreal := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hVfin) hBfin).mpr hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  rw [le_div_iff₀ hpos]
  exact hreal

end

end Work.HP.Q44Child
