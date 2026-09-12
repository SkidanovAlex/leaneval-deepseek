import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

namespace Commons.Geometry.Convex.Hadwiger

open Metric
open scoped Pointwise Classical

noncomputable section

/-- The affine span of a set containing an affine simplex with base point `p0` and
vertices `p0 + (ρ/2) • b i` (for an orthonormal basis `b`) is the whole space. -/
private lemma affineSpan_eq_top_of_simplex (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (p0 : EuclideanSpace ℝ (Fin m)) (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS0 : p0 ∈ S)
    (hSi : ∀ i : Fin m,
      p0 + (ρ / 2 : ℝ) • (EuclideanSpace.basisFun (Fin m) ℝ i) ∈ S) :
    affineSpan ℝ S = ⊤ := by
  classical
  let V := EuclideanSpace ℝ (Fin m)
  let b : Fin m → V := EuclideanSpace.basisFun (Fin m) ℝ
  have hSne : S.Nonempty := ⟨p0, hS0⟩
  have hvsub : ∀ i : Fin m, (ρ / 2 : ℝ) • b i ∈ vectorSpan ℝ S := by
    intro i
    have hv := vsub_mem_vectorSpan ℝ (hSi i) hS0
    simpa [b, add_sub_cancel_left] using hv
  have hb_mem : ∀ i : Fin m, b i ∈ vectorSpan ℝ S := by
    intro i
    have hw := hvsub i
    have hscaled : ((2 / ρ : ℝ) • ((ρ / 2 : ℝ) • b i)) ∈ vectorSpan ℝ S :=
      (vectorSpan ℝ S).smul_mem (2 / ρ) hw
    have heq : ((2 / ρ : ℝ) • ((ρ / 2 : ℝ) • b i)) = b i := by
      rw [smul_smul]
      have hmul : (2 / ρ) * (ρ / 2) = 1 := by field_simp [hρ.ne']
      simp [hmul]
    simpa [heq] using hscaled
  have hrange : Set.range b ⊆ (vectorSpan ℝ S : Set V) := by
    rintro x ⟨i, rfl⟩
    exact hb_mem i
  have hspan_le : Submodule.span ℝ (Set.range b) ≤ vectorSpan ℝ S := Submodule.span_le.mpr hrange
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
    simpa [b] using (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.span_eq
  have htop_le : (⊤ : Submodule ℝ V) ≤ vectorSpan ℝ S := by
    simpa [hspan] using hspan_le
  have hvs : vectorSpan ℝ S = ⊤ := le_antisymm le_top htop_le
  exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ V V hSne).mpr hvs

/-- Every convex body in `ℝᵐ` is arbitrarily close (in Hausdorff distance) to a
full-dimensional polytope, i.e. a convex body which is the convex hull of finitely
many points and has nonempty interior. -/
theorem exists_fullDim_polytope_close (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : ConvexBody (EuclideanSpace ℝ (Fin m)),
      ∃ u : Finset (EuclideanSpace ℝ (Fin m)),
        (P : Set (EuclideanSpace ℝ (Fin m))) = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m))) ∧
        (interior (P : Set (EuclideanSpace ℝ (Fin m)))).Nonempty ∧
        dist P K < δ := by
  classical
  let V := EuclideanSpace ℝ (Fin m)
  let ρ : ℝ := δ / 3
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρδ : ρ < δ := by
    dsimp [ρ]
    linarith
  -- A finite ρ-net of K (centres of a finite subcover of K by ρ-balls).
  let c : {x : V // x ∈ (K : Set V)} → Set V := fun i => ball (i : V) ρ
  have hcov : (K : Set V) ⊆ ⋃ i : {x : V // x ∈ (K : Set V)}, c i := by
    intro x hx
    rw [Set.mem_iUnion]
    exact ⟨⟨x, hx⟩, Metric.mem_ball_self hρ⟩
  rcases (K.isCompact.elim_finite_subcover c (fun i => Metric.isOpen_ball) hcov) with ⟨t, ht⟩
  let e : {x : V // x ∈ (K : Set V)} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let net : Finset V := t.map e
  have hnet : ∀ y ∈ (K : Set V), ∃ z ∈ net, dist y z < ρ := by
    intro y hy
    have hx' : y ∈ ⋃ i ∈ t, ball (i : V) ρ := by
      simpa [c] using ht hy
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨i, hi⟩
    rw [Set.mem_iUnion] at hi
    rcases hi with ⟨hit, hix⟩
    refine ⟨(i : V), ?_, ?_⟩
    · dsimp [net]
      exact Finset.mem_map.mpr ⟨i, Finset.mem_coe.mp hit, rfl⟩
    · exact Metric.mem_ball.mp hix
  have hnetK : (net : Set V) ⊆ (K : Set V) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    dsimp [net] at hx
    rcases (Finset.mem_map.mp hx) with ⟨a, ha, rfl⟩
    exact a.2
  obtain ⟨p0, hp0⟩ := K.nonempty
  -- Add the vertices of a tiny simplex of full dimension.
  let simpVerts : Finset V :=
    Finset.univ.image (fun i : Fin m => p0 + ((ρ / 2 : ℝ) • EuclideanSpace.basisFun (Fin m) ℝ i))
  let simpAll : Finset V := insert p0 simpVerts
  let u : Finset V := simpAll ∪ net
  have hp0u : p0 ∈ u := by
    dsimp [u, simpAll]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert.mpr (Or.inl rfl)))
  have hVerts : ∀ i : Fin m,
      p0 + ((ρ / 2 : ℝ) • EuclideanSpace.basisFun (Fin m) ℝ i) ∈ u := by
    intro i
    dsimp [u, simpAll, simpVerts]
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))))
  -- The polytope P = convexHull u, a convex body.
  have hu_ne : (u : Set V).Nonempty := ⟨p0, by simpa using hp0u⟩
  let P : ConvexBody V :=
    ⟨convexHull ℝ (u : Set V), convex_convexHull ℝ (u : Set V),
     Set.Finite.isCompact_convexHull ℝ (Finset.finite_toSet u),
     convexHull_nonempty_iff.mpr hu_ne⟩
  -- L := K + ρ-ball is convex and contains all vertices of u.
  let L : Set V := (K : Set V) + Metric.closedBall (0 : V) ρ
  have hLconv : Convex ℝ L := K.convex.add (convex_closedBall (0 : V) ρ)
  have h0ball : (0 : V) ∈ Metric.closedBall (0 : V) ρ := by
    rw [Metric.mem_closedBall]
    simpa using (le_of_lt hρ)
  have hKsubL : (K : Set V) ⊆ L := by
    intro x hx
    change x ∈ (K : Set V) + Metric.closedBall (0 : V) ρ
    simpa using (Set.add_mem_add hx h0ball)
  have hw_ball : ∀ i : Fin m,
      ((ρ / 2 : ℝ) • EuclideanSpace.basisFun (Fin m) ℝ i) ∈ Metric.closedBall (0 : V) ρ := by
    intro i
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm]
    simp only [sub_zero]
    rw [norm_smul]
    rw [OrthonormalBasis.norm_eq_one]
    have hρ2 : 0 ≤ ρ / 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hρ2]
    norm_num
    linarith
  have hsvL : (simpVerts : Set V) ⊆ L := by
    intro x hx
    change x ∈ (K : Set V) + Metric.closedBall (0 : V) ρ
    rw [Finset.mem_coe] at hx
    dsimp [simpVerts] at hx
    rcases (Finset.mem_image.mp hx) with ⟨i, hi, rfl⟩
    exact Set.add_mem_add hp0 (hw_ball i)
  have hsAL : (simpAll : Set V) ⊆ L := by
    intro x hx
    rw [Finset.mem_coe] at hx
    rcases (Finset.mem_insert.mp hx) with rfl | hx
    · exact hKsubL hp0
    · exact hsvL (by simpa using hx)
  have huL : (u : Set V) ⊆ L := by
    intro x hx
    rw [Finset.mem_coe] at hx
    rcases (Finset.mem_union.mp hx) with hx | hx
    · exact hsAL (by simpa using hx)
    · exact hKsubL (hnetK (by simpa using hx))
  have hPsubL : (P : Set V) ⊆ L := by
    change convexHull ℝ (u : Set V) ⊆ L
    exact convexHull_min huL hLconv
  -- Hausdorff distance bound.
  have hdist_le : Metric.hausdorffDist (P : Set V) (K : Set V) ≤ ρ := by
    refine Metric.hausdorffDist_le_of_mem_dist (le_of_lt hρ) ?_ ?_
    · intro x hx
      have hxL : x ∈ L := hPsubL hx
      change x ∈ (K : Set V) + Metric.closedBall (0 : V) ρ at hxL
      rw [Set.mem_add] at hxL
      rcases hxL with ⟨k, hk, w, hw, rfl⟩
      refine ⟨k, hk, ?_⟩
      rw [dist_eq_norm, add_sub_cancel_left]
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hw)
    · intro y hy
      rcases hnet y hy with ⟨z, hz, hzy⟩
      refine ⟨z, ?_, le_of_lt hzy⟩
      change z ∈ convexHull ℝ (u : Set V)
      have hzu : z ∈ u := by
        dsimp [u]
        exact Finset.mem_union.mpr (Or.inr hz)
      exact subset_convexHull ℝ (u : Set V) (by simpa using hzu)
  refine ⟨P, u, ?_, ?_, ?_⟩
  · change (convexHull ℝ (u : Set V)) = convexHull ℝ (u : Set V)
    rfl
  · have hspan : affineSpan ℝ (u : Set V) = ⊤ :=
      affineSpan_eq_top_of_simplex m hρ p0 (u : Set V) (by simpa using hp0u) (by simpa using hVerts)
    have hInt : (interior (convexHull ℝ (u : Set V))).Nonempty :=
      (interior_convexHull_nonempty_iff_affineSpan_eq_top (s := (u : Set V))).mpr hspan
    change (interior (convexHull ℝ (u : Set V))).Nonempty
    exact hInt
  · have hd : Metric.hausdorffDist (P : Set V) (K : Set V) < δ := lt_of_le_of_lt hdist_le hρδ
    simpa [ConvexBody.hausdorffDist_coe] using hd

end

end Commons.Geometry.Convex.Hadwiger