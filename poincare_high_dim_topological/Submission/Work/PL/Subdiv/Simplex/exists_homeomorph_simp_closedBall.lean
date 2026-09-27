import Mathlib
import Submission.Work.PL.Subdiv.Defs
import Submission.Work.PL.Subdiv.Simplex.sum_smul_unique
import Submission.Work.PL.Subdiv.Simplex.mem_convexHull_range_iff_exists_weights
import Submission.Work.PL.Subdiv.Simplex.sum_smul_mem_convexHull_compl_iff

/-!
# A simplex is homeomorphic to a closed ball (blueprint A2 item 8)

For a finite affinely independent vertex set `s ⊆ E N` the convex hull `PL.simp s` is
homeomorphic to the closed unit ball of `E (s.card - 1)`, and the homeomorphism carries the
union of the facets `PL.simp (s.erase v)` onto the unit sphere.

The homeomorphism is built in three steps:

* barycentric coordinates identify `PL.simp s` with the *coordinate simplex*
  `stdSimplexSet κ = {u : E κ | u ≥ 0, ∑ u ≤ 1}` (a simplex with a vertex at the origin),
* the gauge-rescale homeomorphism `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`
  (Mathlib, `Analysis/Convex/GaugeRescale.lean`) identifies that simplex with the closed ball
  and its frontier with the sphere,
* on the coordinate simplex the frontier is exactly "some coordinate vanishes".
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Simplex

noncomputable section

/-! ## The coordinate simplex -/

/-- The coordinate simplex `{u : ℝ^κ | u ≥ 0, ∑ u ≤ 1}`: the convex hull of the origin and the
standard basis vectors of `E κ`.  It has `κ + 1` vertices and is the target simplex in which the
gauge-rescale homeomorphism to the ball is computed. -/
def stdSimplexSet (κ : ℕ) : Set (PL.E κ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}

lemma mem_stdSimplexSet {κ : ℕ} {u : PL.E κ} :
    u ∈ stdSimplexSet κ ↔ (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 := Iff.rfl

/-! ## Elementary lemmas about `Fin (n+1)` -/

private lemma fin_exists_eq_zero_iff {n : ℕ} {f : Fin (n + 1) → ℝ} :
    (∃ i, f i = 0) ↔ (∃ i : Fin n, f i.castSucc = 0) ∨ f (Fin.last n) = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr hi
    | cast j => exact Or.inl ⟨j, hi⟩
  · rintro (⟨j, hj⟩ | h)
    · exact ⟨j.castSucc, hj⟩
    · exact ⟨Fin.last n, h⟩

private lemma sum_castSucc_eq_one_sub_last {n : ℕ} {f : Fin (n + 1) → ℝ}
    (h : ∑ i, f i = 1) : ∑ i : Fin n, f i.castSucc = 1 - f (Fin.last n) := by
  have h' := Fin.sum_univ_castSucc f
  linarith

/-! ## Point-set facts about the coordinate simplex

The coordinate simplex `stdSimplexSet κ` is the convex hull of the origin and the standard
basis vectors of `E κ`, hence compact with nonempty interior; its interior is the *open*
coordinate simplex and its frontier is exactly the set of points with a vanishing coordinate
or total mass `1`.  -/

private lemma interior_proj_nonneg' (κ : ℕ) (i : Fin κ) :
    interior {v : PL.E κ | (0 : ℝ) ≤ v i} = {v : PL.E κ | (0 : ℝ) < v i} := by
  have hpre : {v : PL.E κ | (0 : ℝ) ≤ v i} = (EuclideanSpace.proj i) ⁻¹' (Ici 0) := by
    ext v; simp
  have hsurj : Function.Surjective (EuclideanSpace.proj i : PL.E κ →L[ℝ] ℝ) := by
    intro r; exact ⟨EuclideanSpace.single i r, by simp⟩
  rw [hpre, ContinuousLinearMap.interior_preimage _ hsurj, interior_Ici]
  ext v; simp

private lemma interior_sum_le' (κ : ℕ) :
    interior {v : PL.E κ | (∑ i, v i) ≤ (1 : ℝ)} = {v : PL.E κ | (∑ i, v i) < 1} := by
  rcases κ with _ | k
  · ext v; simp
  · have hpre : {v : PL.E (k + 1) | (∑ i, v i) ≤ (1 : ℝ)} =
        ⇑(∑ i, EuclideanSpace.proj i) ⁻¹' (Iic (1 : ℝ)) := by
      ext v; simp
    have hsurj : Function.Surjective ⇑((∑ i, EuclideanSpace.proj i) : PL.E (k + 1) →L[ℝ] ℝ) := by
      intro r
      refine ⟨EuclideanSpace.single ⟨0, Nat.succ_pos k⟩ r, ?_⟩
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hEq := ContinuousLinearMap.interior_preimage
      ((∑ i, EuclideanSpace.proj i) : PL.E (k + 1) →L[ℝ] ℝ) hsurj (Iic (1 : ℝ))
    apply Subset.antisymm
    · intro u hu
      rw [hpre, hEq, interior_Iic] at hu
      simpa using hu
    · apply interior_maximal
      · intro v hv
        have hv' : ∑ i, v i < 1 := hv
        exact le_of_lt hv'
      · exact isOpen_lt (by fun_prop) continuous_const

private lemma isOpen_interiorSet' (κ : ℕ) :
    IsOpen {u : PL.E κ | (∀ i, 0 < u i) ∧ ∑ i, u i < 1} := by
  have hA : IsOpen {u : PL.E κ | ∀ i, 0 < u i} := by
    rw [show {u : PL.E κ | ∀ i, 0 < u i} = ⋂ i, {u : PL.E κ | (0 : ℝ) < u i} from by
      ext u; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
  have hB : IsOpen {u : PL.E κ | ∑ i, u i < 1} := isOpen_lt (by fun_prop) continuous_const
  exact hA.inter hB

private lemma interiorSet_subset' (κ : ℕ) :
    {u : PL.E κ | (∀ i, 0 < u i) ∧ ∑ i, u i < 1} ⊆ stdSimplexSet κ := by
  intro u hu
  exact ⟨fun i => le_of_lt (hu.1 i), le_of_lt hu.2⟩

private lemma isClosed_coordSimplex (κ : ℕ) : IsClosed (stdSimplexSet κ) := by
  have h1 : IsClosed {u : PL.E κ | ∀ i, (0 : ℝ) ≤ u i} := by
    rw [show {u : PL.E κ | ∀ i, (0 : ℝ) ≤ u i} = ⋂ i, {u : PL.E κ | (0 : ℝ) ≤ u i} from by
      ext u; simp]
    exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {u : PL.E κ | (∑ i, u i) ≤ 1} := isClosed_le (by fun_prop) continuous_const
  have hset : stdSimplexSet κ =
      {u : PL.E κ | ∀ i, (0 : ℝ) ≤ u i} ∩ {u : PL.E κ | ∑ i, u i ≤ 1} := rfl
  rw [hset]
  exact h1.inter h2

private lemma apply_add_smul' {κ : ℕ} (x y : PL.E κ) (a b : ℝ) (i : Fin κ) :
    (a • x + b • y) i = a * x i + b * y i := by
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private lemma sum_apply_add_smul' {κ : ℕ} (x y : PL.E κ) (a b : ℝ) :
    (∑ i, (a • x + b • y) i) = a * (∑ i, x i) + b * (∑ i, y i) := by
  rw [Finset.sum_congr rfl (fun i _ => apply_add_smul' x y a b i), Finset.sum_add_distrib,
    Finset.mul_sum, Finset.mul_sum]

private lemma convex_coordSimplex (κ : ℕ) : Convex ℝ (stdSimplexSet κ) := by
  intro x hx y hy a b ha hb _
  refine ⟨fun i => ?_, ?_⟩
  · rw [apply_add_smul']
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · rw [sum_apply_add_smul']
    nlinarith [hx.2, hy.2, ha, hb,
      add_le_add (mul_le_of_le_one_right ha hx.2) (mul_le_of_le_one_right hb hy.2)]

private lemma isBounded_coordSimplex (κ : ℕ) : Bornology.IsBounded (stdSimplexSet κ) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, fun u hu => ?_⟩
  have h0 : ∀ i, 0 ≤ u i := hu.1
  have hsum : ∑ i, u i ≤ 1 := hu.2
  have hnorm : ‖u‖ = Real.sqrt (∑ i, (u i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    exact Finset.sum_congr rfl
      (fun i _ => by simp [Real.norm_eq_abs, abs_of_nonneg (h0 i)])
  rw [hnorm, Real.sqrt_le_one]
  calc ∑ i, (u i) ^ 2 ≤ ∑ i, u i := Finset.sum_le_sum (fun i _ => by
        have hi : u i ≤ 1 :=
          (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)).trans hsum
        nlinarith [h0 i, hi])
    _ ≤ 1 := hsum

private lemma interior_coordSimplex (κ : ℕ) :
    interior (stdSimplexSet κ) = {u : PL.E κ | (∀ i, 0 < u i) ∧ ∑ i, u i < 1} := by
  apply Subset.antisymm
  · intro u hu
    refine ⟨fun i => ?_, ?_⟩
    · have h1 : u ∈ interior {v : PL.E κ | (0 : ℝ) ≤ v i} :=
        interior_mono (fun v hv => hv.1 i) hu
      rwa [interior_proj_nonneg'] at h1
    · have h1 : u ∈ interior {v : PL.E κ | (∑ i, v i) ≤ (1 : ℝ)} :=
        interior_mono (fun v hv => hv.2) hu
      rwa [interior_sum_le'] at h1
  · exact interior_maximal (interiorSet_subset' κ) (isOpen_interiorSet' κ)

private lemma nonempty_interior_coordSimplex (κ : ℕ) :
    (interior (stdSimplexSet κ)).Nonempty := by
  set u : PL.E κ := WithLp.toLp 2 (fun _ : Fin κ => ((κ : ℝ) + 2)⁻¹) with hu
  refine ⟨u, ?_⟩
  rw [interior_coordSimplex]
  have hsum : (∑ i : Fin κ, u i) = (κ : ℝ) * ((κ : ℝ) + 2)⁻¹ := by
    simp [hu, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  refine ⟨fun i => ?_, ?_⟩
  · rw [show u i = ((κ : ℝ) + 2)⁻¹ from by simp [hu]]
    positivity
  · rw [hsum, ← div_eq_mul_inv, div_lt_one (by positivity)]
    linarith

private lemma mem_frontier_coordSimplex (κ : ℕ) (u : PL.E κ) :
    u ∈ frontier (stdSimplexSet κ) ↔
      (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1 ∧ ((∃ i, u i = 0) ∨ ∑ i, u i = 1) := by
  have hclosed : closure (stdSimplexSet κ) = stdSimplexSet κ :=
    (isClosed_coordSimplex κ).closure_eq
  have hfront : u ∈ frontier (stdSimplexSet κ) ↔
      u ∈ stdSimplexSet κ ∧ u ∉ interior (stdSimplexSet κ) := by
    constructor
    · intro hu
      have hs : u ∈ stdSimplexSet κ := by rw [← hclosed]; exact frontier_subset_closure hu
      exact ⟨hs, (mem_frontier_iff_notMem_interior hs).mp hu⟩
    · rintro ⟨hs, hi⟩
      exact (mem_frontier_iff_notMem_interior hs).mpr hi
  rw [hfront, interior_coordSimplex, mem_stdSimplexSet]
  constructor
  · rintro ⟨⟨h0, h1⟩, hU⟩
    refine ⟨h0, h1, ?_⟩
    have hU' : ¬((∀ i, 0 < u i) ∧ ∑ i, u i < 1) := hU
    rw [not_and_or] at hU'
    rcases hU' with hA | hB
    · left
      simp only [not_forall, not_lt] at hA
      obtain ⟨i, hi⟩ := hA
      exact ⟨i, le_antisymm hi (h0 i)⟩
    · right
      rw [not_lt] at hB
      exact le_antisymm h1 hB
  · rintro ⟨h0, h1, hR⟩
    refine ⟨⟨h0, h1⟩, ?_⟩
    have hU' : ¬((∀ i, 0 < u i) ∧ ∑ i, u i < 1) := by
      rintro ⟨hA, hB⟩
      rcases hR with ⟨i, hi⟩ | h
      · have := hA i
        rw [hi] at this
        exact absurd this (lt_irrefl 0)
      · rw [h] at hB
        exact absurd hB (lt_irrefl 1)
    exact hU'

/-- The coordinate simplex is homeomorphic to the closed ball, frontier going to the sphere. -/
private lemma exists_homeo_coordSimplex_sphere (κ : ℕ) :
    ∃ e : (stdSimplexSet κ) ≃ₜ Metric.closedBall (0 : PL.E κ) 1,
      ∀ u : stdSimplexSet κ, (e u : PL.E κ) ∈ Metric.sphere (0 : PL.E κ) 1 ↔
        (∃ i, (u : PL.E κ) i = 0) ∨ ∑ i, (u : PL.E κ) i = 1 := by
  obtain ⟨h, -, hclos, hfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall (E := PL.E κ)
      (convex_coordSimplex κ) (nonempty_interior_coordSimplex κ) (isBounded_coordSimplex κ)
  have hset : h '' (stdSimplexSet κ) = Metric.closedBall (0 : PL.E κ) 1 := by
    rw [← hclos, (isClosed_coordSimplex κ).closure_eq]
  refine ⟨(h.image (stdSimplexSet κ)).trans (Homeomorph.setCongr hset), ?_⟩
  intro u
  have hcoe : ((h.image (stdSimplexSet κ)).trans (Homeomorph.setCongr hset) u : PL.E κ)
      = h (u : PL.E κ) := rfl
  have hmem : h (u : PL.E κ) ∈ Metric.sphere (0 : PL.E κ) 1 ↔
      (u : PL.E κ) ∈ frontier (stdSimplexSet κ) := by
    rw [← hfront]
    exact ⟨fun ⟨y, hy, hyu⟩ => h.injective hyu ▸ hy, fun hu => ⟨(u : PL.E κ), hu, rfl⟩⟩
  rw [hcoe, hmem, mem_frontier_coordSimplex κ (u : PL.E κ)]
  exact ⟨fun h => h.2.2, fun h => ⟨u.2.1, u.2.2, h⟩⟩

/-! ## The main construction -/

/-- **A simplex is homeomorphic to a closed ball.**  For a finite affinely independent vertex set
`s` of cardinality `κ + 1` there is a homeomorphism from `PL.simp s` to the closed unit ball of
`E κ`, and a point of `PL.simp s` is mapped to the unit sphere exactly when it lies in one of the
facets `PL.simp (s.erase v)`. -/
theorem exists_homeomorph_simp_closedBall_aux {N κ : ℕ} (s : Finset (PL.E N))
    (hcard : s.card = κ + 1) (hind : AffineIndependent ℝ ((↑) : s → PL.E N)) :
    ∃ e : (PL.simp s) ≃ₜ Metric.closedBall (0 : PL.E κ) 1,
      ∀ x : (PL.simp s), ((e x : PL.E κ)) ∈ Metric.sphere (0 : PL.E κ) 1 ↔
        (x : PL.E N) ∈ ⋃ v ∈ s, PL.simp (s.erase v) := by
  classical
  -- ## Step 0: an enumeration of the vertex set `s` by `Fin (κ+1)`
  set es : ↥s ≃ Fin (κ + 1) := (Finset.equivFin s).trans (finCongr hcard) with hes
  set v : Fin (κ + 1) → PL.E N := fun i => (es.symm i : PL.E N) with hv
  have hv_mem : ∀ i, v i ∈ s := fun i => (es.symm i).2
  have hv_es : ∀ i, es ⟨v i, hv_mem i⟩ = i := fun i => es.apply_symm_apply i
  have hv_val : ∀ (x : PL.E N) (hx : x ∈ s), v (es ⟨x, hx⟩) = x := by
    intro x hx
    change ((es.symm (es ⟨x, hx⟩)) : PL.E N) = x
    rw [Equiv.symm_apply_apply]
  have hv_range : Set.range v = (s : Set (PL.E N)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact hv_mem i
    · intro hx
      exact ⟨es ⟨x, hx⟩, hv_val x hx⟩
  have hv_ai : AffineIndependent ℝ v := by
    have h := hind.comp_embedding es.symm.toEmbedding
    change AffineIndependent ℝ (Subtype.val ∘ ⇑es.symm)
    exact h
  have hv_erase : ∀ i : Fin (κ + 1), (↑(s.erase (v i)) : Set (PL.E N)) = v '' {i}ᶜ := by
    intro i
    ext x
    constructor
    · intro hx
      rw [Finset.mem_coe, Finset.mem_erase] at hx
      obtain ⟨hne, hxs⟩ := hx
      refine ⟨es ⟨x, hxs⟩, ?_, hv_val x hxs⟩
      rintro rfl
      exact hne (hv_val x hxs).symm
    · rintro ⟨j, hj, rfl⟩
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, hv_mem j⟩
      intro hcon
      have h2 : (⟨v j, hv_mem j⟩ : ↥s) = ⟨v i, hv_mem i⟩ := Subtype.ext hcon
      have : j = i := by rw [← hv_es j, ← hv_es i, h2]
      exact hj this
  -- ## Step 1: the barycentric coordinate map
  have hF_cont : Continuous fun t : Fin (κ + 1) → ℝ => ∑ i, t i • v i := by
    refine continuous_finset_sum Finset.univ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const
  have hF_mem : ∀ t : Fin (κ + 1) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i = 1 →
      (∑ i, t i • v i) ∈ PL.simp s := by
    intro t ht0 ht1
    have h1 : (∑ i, t i • v i) ∈ convexHull ℝ (Set.range v) := by
      refine (convex_convexHull ℝ (Set.range v)).sum_mem (t := Finset.univ) ?_ ?_ ?_
      · intro i _
        exact ht0 i
      · simpa using ht1
      · intro i _
        exact subset_convexHull ℝ (Set.range v) (Set.mem_range_self i)
    rw [hv_range] at h1
    simpa only [PL.simp] using h1
  have hF_inj : ∀ t t' : Fin (κ + 1) → ℝ, (∀ i, 0 ≤ t i) → ∑ i, t i = 1 →
      (∀ i, 0 ≤ t' i) → ∑ i, t' i = 1 → ∑ i, t i • v i = ∑ i, t' i • v i → t = t' :=
    fun t t' _ ht1 _ ht1' h => sum_smul_unique hv_ai ht1 ht1' h
  have hF_surj : ∀ x ∈ PL.simp s, ∃ t : Fin (κ + 1) → ℝ,
      (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧ ∑ i, t i • v i = x := by
    intro x hx
    have hx' : x ∈ convexHull ℝ (Set.range v) := by
      rw [hv_range]
      simpa only [PL.simp] using hx
    exact (mem_convexHull_range_iff_exists_weights v x).1 hx'
  have hsimp_compact : IsCompact (PL.simp s) := by
    simpa only [PL.simp] using (s.finite_toSet).isCompact_convexHull ℝ
  haveI : CompactSpace ↥(PL.simp s) := isCompact_iff_compactSpace.mp hsimp_compact
  -- the standard simplex of coefficient vectors
  have hstd_mem : ∀ t : Fin (κ + 1) → ℝ, t ∈ stdSimplex ℝ (Fin (κ + 1)) ↔
      (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 := by
    intro t
    simp [stdSimplex_eq_inter]
  have hstd_pair : ∀ t : Fin (κ + 1) → ℝ, t ∈ stdSimplex ℝ (Fin (κ + 1)) →
      (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 := fun t ht => (hstd_mem t).1 ht
  haveI : CompactSpace ↥(stdSimplex ℝ (Fin (κ + 1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (κ + 1)))
  set Φ₁ : ↥(stdSimplex ℝ (Fin (κ + 1))) → ↥(PL.simp s) :=
    fun t => ⟨∑ i, (t : Fin (κ + 1) → ℝ) i • v i,
      hF_mem _ (hstd_pair _ t.2).1 (hstd_pair _ t.2).2⟩ with hΦ₁
  have hΦ₁_val : ∀ t : ↥(stdSimplex ℝ (Fin (κ + 1))), (Φ₁ t : PL.E N) =
      ∑ i, (t : Fin (κ + 1) → ℝ) i • v i := fun t => rfl
  have hΦ₁_cont : Continuous Φ₁ :=
    Continuous.subtype_mk (hF_cont.comp continuous_subtype_val)
      (fun t => hF_mem _ (hstd_pair _ t.2).1 (hstd_pair _ t.2).2)
  have hΦ₁_bij : Function.Bijective Φ₁ := by
    constructor
    · intro t t' h
      refine Subtype.ext (hF_inj _ _ (hstd_pair _ t.2).1 (hstd_pair _ t.2).2
        (hstd_pair _ t'.2).1 (hstd_pair _ t'.2).2 ?_)
      exact congrArg (fun y : ↥(PL.simp s) => (y : PL.E N)) h
    · rintro ⟨x, hx⟩
      obtain ⟨t, ht0, ht1, hFt⟩ := hF_surj x hx
      exact ⟨⟨t, (hstd_mem t).2 ⟨ht0, ht1⟩⟩, Subtype.ext hFt⟩
  set e1 : ↥(stdSimplex ℝ (Fin (κ + 1))) ≃ₜ ↥(PL.simp s) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective Φ₁ hΦ₁_bij) hΦ₁_cont with he1
  -- ## Step 2: the barycentric coordinates of a point of the simplex
  set coord : ↥(PL.simp s) → (Fin (κ + 1) → ℝ) := fun x => (e1.symm x : Fin (κ + 1) → ℝ)
    with hcoord
  have hcoord_cont : Continuous coord := continuous_subtype_val.comp e1.symm.continuous
  have hcoord_pair : ∀ x, (∀ i, 0 ≤ coord x i) ∧ ∑ i, coord x i = 1 :=
    fun x => hstd_pair _ (e1.symm x).2
  have hcoord_spec : ∀ x : ↥(PL.simp s), ∑ i, coord x i • v i = (x : PL.E N) := by
    intro x
    exact congrArg (fun y : ↥(PL.simp s) => (y : PL.E N)) (e1.apply_symm_apply x)
  have hcoord_unique : ∀ (x : ↥(PL.simp s)) (t : Fin (κ + 1) → ℝ), (∀ i, 0 ≤ t i) →
      ∑ i, t i = 1 → ∑ i, t i • v i = (x : PL.E N) → t = coord x := by
    intro x t ht0 ht1 hFt
    have h1 : (⟨t, (hstd_mem t).2 ⟨ht0, ht1⟩⟩ : ↥(stdSimplex ℝ (Fin (κ + 1)))) = e1.symm x := by
      refine e1.injective ?_
      rw [e1.apply_symm_apply]
      exact Subtype.ext hFt
    exact congrArg (fun y : ↥(stdSimplex ℝ (Fin (κ + 1))) => (y : Fin (κ + 1) → ℝ)) h1
  -- ## Step 3: the map to the coordinate simplex
  set Φ : ↥(PL.simp s) → PL.E κ :=
    fun x => WithLp.toLp 2 (fun i : Fin κ => coord x i.castSucc) with hΦ
  have hΦ_apply : ∀ (x : ↥(PL.simp s)) (i : Fin κ), Φ x i = coord x i.castSucc := by
    intro x i
    simp [hΦ, WithLp.ofLp_toLp]
  have hΦ_cont : Continuous Φ := by
    simp only [hΦ]
    fun_prop
  have hΦ_mem : ∀ x, Φ x ∈ stdSimplexSet κ := by
    intro x
    refine ⟨fun i => (hcoord_pair x).1 i.castSucc, ?_⟩
    have hsum := sum_castSucc_eq_one_sub_last (hcoord_pair x).2
    have hlast := (hcoord_pair x).1 (Fin.last κ)
    linarith
  have hΦ_fun_inj : Function.Injective (fun x : ↥(PL.simp s) =>
      (⟨Φ x, hΦ_mem x⟩ : ↥(stdSimplexSet κ))) := by
    intro x x' h
    have hcast : ∀ i : Fin κ, coord x i.castSucc = coord x' i.castSucc := by
      intro i
      have h2 := congrArg (fun u : ↥(stdSimplexSet κ) => (u : PL.E κ) i) h
      simpa only [hΦ] using h2
    have hlast : coord x (Fin.last κ) = coord x' (Fin.last κ) := by
      have h1 : (∑ i : Fin κ, coord x i.castSucc) = ∑ i : Fin κ, coord x' i.castSucc :=
        Finset.sum_congr rfl fun i _ => hcast i
      have h2 := sum_castSucc_eq_one_sub_last (hcoord_pair x).2
      have h3 := sum_castSucc_eq_one_sub_last (hcoord_pair x').2
      linarith
    have hcoord_eq : coord x = coord x' := by
      funext i
      exact Fin.lastCases hlast (fun j => hcast j) i
    refine Subtype.ext ?_
    rw [← hcoord_spec x, ← hcoord_spec x', hcoord_eq]
  have hΦ_fun_surj : Function.Surjective (fun x : ↥(PL.simp s) =>
      (⟨Φ x, hΦ_mem x⟩ : ↥(stdSimplexSet κ))) := by
    rintro ⟨u, hu⟩
    have hu' : (∀ i, 0 ≤ u i) ∧ ∑ i : Fin κ, u i ≤ 1 := hu
    set t : Fin (κ + 1) → ℝ := Fin.snoc (fun i : Fin κ => u i) (1 - ∑ i : Fin κ, u i) with ht
    have ht_cast : ∀ i : Fin κ, t i.castSucc = u i := by
      intro i
      rw [ht, Fin.snoc_castSucc]
    have ht_last : t (Fin.last κ) = 1 - ∑ i : Fin κ, u i := by
      rw [ht, Fin.snoc_last]
    have ht_nonneg : ∀ i, 0 ≤ t i := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [ht_last]
        linarith [hu'.2]
      · rw [ht_cast j]
        exact hu'.1 j
    have ht_sum : ∑ i, t i = 1 := by
      rw [Fin.sum_univ_castSucc, Finset.sum_congr rfl (fun i _ => ht_cast i), ht_last]
      ring
    refine ⟨⟨∑ i, t i • v i, hF_mem t ht_nonneg ht_sum⟩, ?_⟩
    have hcoord_t : coord ⟨∑ i, t i • v i, hF_mem t ht_nonneg ht_sum⟩ = t :=
      (hcoord_unique _ t ht_nonneg ht_sum rfl).symm
    refine Subtype.ext ?_
    apply PiLp.ext
    intro i
    have h2 : coord ⟨∑ i, t i • v i, hF_mem t ht_nonneg ht_sum⟩ i.castSucc = u i := by
      rw [hcoord_t, ht_cast i]
    simpa only [hΦ, WithLp.ofLp_toLp] using h2
  set Φh : ↥(PL.simp s) ≃ₜ ↥(stdSimplexSet κ) :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ ⟨hΦ_fun_inj, hΦ_fun_surj⟩)
      (Continuous.subtype_mk hΦ_cont hΦ_mem) with hΦh
  have hΦh_apply : ∀ (x : ↥(PL.simp s)) (i : Fin κ), (Φh x : PL.E κ) i = coord x i.castSucc :=
    fun x i => rfl
  -- ## Step 4: the barycentric coordinate of `v i` vanishes exactly on the opposite facet
  have hfacet : ∀ (x : ↥(PL.simp s)) (i : Fin (κ + 1)),
      coord x i = 0 ↔ (x : PL.E N) ∈ PL.simp (s.erase (v i)) := by
    intro x i
    change coord x i = 0 ↔ (x : PL.E N) ∈ convexHull ℝ (↑(s.erase (v i)) : Set (PL.E N))
    rw [hv_erase i, ← hcoord_spec x]
    exact (sum_smul_mem_convexHull_compl_iff hv_ai (hcoord_pair x).1 (hcoord_pair x).2 i).symm
  -- ## Step 5: the two descriptions of the boundary of the simplex agree
  have hunion : ∀ x : ↥(PL.simp s),
      ((∃ i : Fin κ, (Φh x : PL.E κ) i = 0) ∨ ∑ i : Fin κ, (Φh x : PL.E κ) i = 1) ↔
        (x : PL.E N) ∈ ⋃ v ∈ s, PL.simp (s.erase v) := by
    intro x
    have h1 : (∃ i : Fin κ, (Φh x : PL.E κ) i = 0) ↔ ∃ i : Fin κ, coord x i.castSucc = 0 := by
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, by rwa [hΦh_apply] at hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, by rwa [hΦh_apply]⟩
    have h2 : (∑ i : Fin κ, (Φh x : PL.E κ) i = 1) ↔ coord x (Fin.last κ) = 0 := by
      have hsum : (∑ i : Fin κ, (Φh x : PL.E κ) i) = ∑ i : Fin κ, coord x i.castSucc :=
        Finset.sum_congr rfl fun i _ => by rw [hΦh_apply]
      have hrel := sum_castSucc_eq_one_sub_last (hcoord_pair x).2
      rw [hsum, hrel]
      constructor <;> intro h <;> linarith
    have h3 : (x : PL.E N) ∈ ⋃ v ∈ s, PL.simp (s.erase v) ↔
        ∃ i : Fin (κ + 1), coord x i = 0 := by
      rw [Set.mem_iUnion₂]
      constructor
      · rintro ⟨w, hw, hxw⟩
        have hxw' : (x : PL.E N) ∈ PL.simp (s.erase (v (es ⟨w, hw⟩))) := by
          rw [hv_val w hw]
          exact hxw
        exact ⟨es ⟨w, hw⟩, (hfacet x _).2 hxw'⟩
      · rintro ⟨i, hi⟩
        exact ⟨v i, hv_mem i, (hfacet x i).1 hi⟩
    rw [h1, h2, h3]
    exact (fin_exists_eq_zero_iff (f := coord x)).symm
  -- ## Step 6: assemble the homeomorphism with the gauge-rescale homeomorphism of the ball
  obtain ⟨e2, he2⟩ := exists_homeo_coordSimplex_sphere κ
  exact ⟨Φh.trans e2, fun x => by rw [Homeomorph.trans_apply, he2 (Φh x)]; exact hunion x⟩

theorem exists_homeomorph_simp_closedBall {N : ℕ} (s : Finset (PL.E N)) (hs : s.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : s → PL.E N)) :
    ∃ e : (PL.simp s) ≃ₜ Metric.closedBall (0 : PL.E (s.card - 1)) 1,
      ∀ x : (PL.simp s), ((e x : PL.E (s.card - 1))) ∈ Metric.sphere (0 : PL.E (s.card - 1)) 1 ↔
        (x : PL.E N) ∈ ⋃ v ∈ s, PL.simp (s.erase v) := by
  have h1 : 1 ≤ s.card := Finset.card_pos.mpr hs
  exact exists_homeomorph_simp_closedBall_aux s (Nat.sub_add_cancel h1).symm hind

end

end Work.PL.Subdiv.Simplex
