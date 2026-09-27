/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The mesh of the iterated barycentric subdivision of `Δⁿ`

This file proves that the `N`-fold barycentric subdivision `SdPiecesPow N n` of the standard
simplex has mesh tending to zero (`SdPiecesPow_diam_lt`).

The proof goes through the explicit description of the pieces of the barycentric subdivision
`SdPieces n`: every piece in the support of `SdPieces n` has as its vertices the centroids of a
(decreasing) chain of nonempty faces of `Δⁿ` (`exists_faceChain_mem_support_SdPieces`, proved
here).  Two such centroids lie within `n/(n+1)` of the diameter of the vertex set of any ambient
simplex (`mesh_step`), so one subdivision step shrinks every piece's mesh by `n/(n+1)`
(`meshV_subdividePiece_le`), and iterating gives the result (`meshV_SdPiecesPow_le`).
-/
import Mathlib
import Submission.Work.Cohomology.SubdivisionChain
import Submission.Work.Subdivision.mesh_step
import Submission.Work.Subdivision.diam_convexHull_centroid_le

open CategoryTheory Simplicial Opposite

namespace Work.Subdivision

open Submission.Cohomology

noncomputable section

/-! ## The ambient geometry of a piece -/

/-- The vertices of a piece, as a subset of the ambient space `Fin (n+1) → ℝ`. -/
def vtxSet {n m : ℕ} (q : Piece n m) : Set (Fin (n+1) → ℝ) :=
  Set.range fun i => (q i : Fin (n+1) → ℝ)

/-- The realisation of a piece, as a subset of the ambient space `Fin (n+1) → ℝ`. -/
def geoSet {n m : ℕ} (q : Piece n m) : Set (Fin (n+1) → ℝ) :=
  Set.range fun t : TSimplex m => ((affineSimplex q t : TSimplex n) : Fin (n+1) → ℝ)

/-- The vertices of a piece are contained in its realisation. -/
lemma vtxSet_subset_geoSet {n m : ℕ} (q : Piece n m) : vtxSet q ⊆ geoSet q := by
  rintro x ⟨i, rfl⟩
  exact ⟨vert i, by simp [affineSimplex_vert]⟩

/-- The ambient coordinates of the affine simplex with vertices `q` at the barycentric coordinate
`t` are the center of mass of the vertices with weights `t`. -/
lemma affineSimplex_amb_eq_centerMass {n m : ℕ} (q : Piece n m) (t : TSimplex m) :
    ((affineSimplex q t : TSimplex n) : Fin (n+1) → ℝ)
      = Finset.univ.centerMass (fun i => (t : Fin (m+1) → ℝ) i)
          (fun i => (q i : Fin (n+1) → ℝ)) := by
  funext j
  rw [affineSimplex_apply, affineSimplexFun, Finset.centerMass, stdSimplex.sum_eq_one t,
    inv_one, one_smul]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The realisation of a piece is contained in the convex hull of its vertices. -/
lemma geoSet_subset_convexHull {n m : ℕ} (q : Piece n m) :
    geoSet q ⊆ convexHull ℝ (vtxSet q) := by
  rintro x ⟨t, rfl⟩
  change ((affineSimplex q t : TSimplex n) : Fin (n+1) → ℝ) ∈ convexHull ℝ _
  rw [affineSimplex_amb_eq_centerMass]
  refine Finset.centerMass_mem_convexHull (s := vtxSet q) Finset.univ
    (fun i _ => t.2.1 i) ?_ (fun i _ => Set.mem_range_self i)
  have h : ∑ i ∈ (Finset.univ : Finset (Fin (m+1))), Subtype.val t i = 1 :=
    stdSimplex.sum_eq_one t
  rw [h]; norm_num

lemma isBounded_vtxSet {n m : ℕ} (q : Piece n m) : Bornology.IsBounded (vtxSet q) :=
  (Set.finite_range _).isBounded

/-- A piece and its vertex set have the same diameter. -/
lemma diam_geoSet_eq_diam_vtxSet {n m : ℕ} (q : Piece n m) :
    Metric.diam (geoSet q) = Metric.diam (vtxSet q) := by
  have hb : Bornology.IsBounded (convexHull ℝ (vtxSet q)) :=
    isBounded_convexHull.mpr (isBounded_vtxSet q)
  refine le_antisymm ?_ ?_
  · calc Metric.diam (geoSet q) ≤ Metric.diam (convexHull ℝ (vtxSet q)) :=
        Metric.diam_mono (geoSet_subset_convexHull q) hb
      _ = Metric.diam (vtxSet q) := convexHull_diam _
  · exact Metric.diam_mono (vtxSet_subset_geoSet q)
      (hb.subset (geoSet_subset_convexHull q))

/-- The diameter of the singular simplex `affineSimplex q` (computed in `TSimplex n`) equals the
diameter of its vertex set (computed in the ambient space). -/
lemma diam_range_affineSimplex_eq_diam_vtxSet {n m : ℕ} (q : Piece n m) :
    Metric.diam (Set.range fun t => (affineSimplex q t : TSimplex n))
      = Metric.diam (vtxSet q) := by
  have h1 : Subtype.val '' (Set.range fun t => (affineSimplex q t : TSimplex n))
      = geoSet q := by
    apply Set.Subset.antisymm
    · rintro x ⟨a, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨affineSimplex q t, ⟨t, rfl⟩, rfl⟩
  rw [← diam_geoSet_eq_diam_vtxSet q, ← h1]
  exact ((isometry_subtype_coe (s := stdSimplex ℝ (Fin (n+1)))).diam_image
    (Set.range fun t => (affineSimplex q t : TSimplex n))).symm

/-! ## The centroids of faces -/

/-- The `j`-th coordinate of the sum of the vertices over `S` is the indicator of `S` at `j`. -/
lemma sum_vert_apply {n : ℕ} (S : Finset (Fin (n+1))) (j : Fin (n+1)) :
    (∑ a ∈ S, (vert a : Fin (n+1) → ℝ)) j = if j ∈ S then 1 else 0 := by
  rw [Finset.sum_apply]
  simp only [vert_apply]
  exact Finset.sum_ite_eq' S j (fun _ => (1:ℝ))

/-- A weighted sum of the indicator function of a finset. -/
lemma sum_weighted_indicator {n : ℕ} (S : Finset (Fin (n+1))) (c : ℝ)
    (f : Fin (n+1) → ℝ) :
    (∑ i, c * (∑ a ∈ S, (vert a : Fin (n+1) → ℝ) i) * f i) = c * ∑ i ∈ S, f i := by
  have h1 : ∀ i : Fin (n+1), (∑ a ∈ S, (vert a : Fin (n+1) → ℝ) i)
      = if i ∈ S then (1:ℝ) else 0 := by
    intro i
    rw [← Finset.sum_apply]
    exact sum_vert_apply S i
  simp only [h1]
  have h2 : ∀ x, (c * (if x ∈ S then (1:ℝ) else 0)) * f x
      = if x ∈ S then c * f x else 0 := by
    intro x; by_cases hx : x ∈ S <;> simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => h2 x)]
  rw [← Finset.sum_filter, Finset.filter_univ_mem]
  rw [Finset.mul_sum]

/-- If `x` is the centroid of `S` in `Δⁿ`, then `affineSimplex Q x` is the centroid of `Q` over
`S`. -/
lemma affineSimplex_centroid_coe {n m : ℕ} {Q : Piece m n} {S : Finset (Fin (n+1))}
    {x : TSimplex n} {c : ℝ}
    (hx : (x : Fin (n+1) → ℝ) = c • ∑ a ∈ S, (vert a : Fin (n+1) → ℝ)) :
    ((affineSimplex Q x : TSimplex m) : Fin (m+1) → ℝ)
      = c • ∑ a ∈ S, (Q a : Fin (m+1) → ℝ) := by
  ext j
  rw [affineSimplex_apply, affineSimplexFun, hx]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_weighted_indicator S c (fun i => ((Q i : TSimplex m) : Fin (m+1) → ℝ) j)

/-- The barycentre of `Δⁿ` is the centroid of the full vertex set. -/
lemma bary_centroid {n : ℕ} :
    (bary n : Fin (n+1) → ℝ)
      = ((Finset.univ : Finset (Fin (n+1))).card : ℝ)⁻¹ •
          ∑ a ∈ Finset.univ, (vert a : Fin (n+1) → ℝ) := by
  funext j
  have hbary : (bary n : Fin (n+1) → ℝ) j = ((Fintype.card (Fin (n+1)) : ℝ))⁻¹ := rfl
  rw [hbary, Pi.smul_apply, smul_eq_mul, sum_vert_apply]
  simp [Finset.card_univ, Fintype.card_fin]

/-- The face inclusion sends the centroid of `S` to the centroid of the image of `S`. -/
lemma faceIncl_centroid {k : ℕ} (i : Fin (k+2)) {x : TSimplex k}
    {S : Finset (Fin (k+1))} {c : ℝ}
    (hx : (x : Fin (k+1) → ℝ) = c • ∑ a ∈ S, (vert a : Fin (k+1) → ℝ)) :
    (faceIncl i x : Fin (k+2) → ℝ)
      = c • ∑ a ∈ S.image (Fin.succAbove i), (vert a : Fin (k+2) → ℝ) := by
  rw [faceIncl_coe, hx, map_smul, map_sum]
  congr 1
  rw [Finset.sum_image (fun a _ b _ hab => Fin.succAbove_right_injective hab)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← stdSimplex.map_coe]
  simp only [vert, stdSimplex.map_vertex]

/-! ## Supports of the basic operations -/

lemma support_mapDomain_subset_image {α β M : Type*} [AddCommMonoid M]
    (f : α → β) (x : α →₀ M) :
    ∀ b, b ∈ (Finsupp.mapDomain f x).support → b ∈ f '' (x.support : Set α) := by
  intro b hb
  by_contra h
  exact (Finsupp.mem_support_iff.mp hb) (Finsupp.mapDomain_of_not_mem_image_support h)

lemma mem_support_conePieces {n m : ℕ} {b : TSimplex n} {X : Piece n m →₀ ℚ}
    {p : Piece n (m+1)} (hp : p ∈ (conePieces b m X).support) :
    ∃ q ∈ X.support, conePiece b q = p := by
  rw [conePieces, Finsupp.lmapDomain_apply] at hp
  rcases support_mapDomain_subset_image (conePiece b) X p hp with ⟨q, hq, hqp⟩
  exact ⟨q, hq, hqp⟩

lemma mem_support_pushPieces {n n' m : ℕ} {f : TSimplex n → TSimplex n'}
    {X : Piece n m →₀ ℚ} {p : Piece n' m} (hp : p ∈ (pushPieces f m X).support) :
    ∃ q ∈ X.support, pushPiece f q = p := by
  rw [pushPieces, Finsupp.lmapDomain_apply] at hp
  rcases support_mapDomain_subset_image (pushPiece f) X p hp with ⟨q, hq, hqp⟩
  exact ⟨q, hq, hqp⟩

/-! ## The face-chain structure of the subdivision pieces -/

/-- Every piece in the support of `SdPieces n` has as its vertices the centroids of a decreasing
chain of nonempty faces of `Δⁿ`. -/
theorem exists_faceChain_mem_support_SdPieces :
    ∀ (n : ℕ) {p : Piece n n}, p ∈ (SdPieces n).support →
      ∃ F : Fin (n+1) → Finset (Fin (n+1)),
        (∀ i, (F i).Nonempty) ∧ Antitone F ∧
        ∀ i, (p i : Fin (n+1) → ℝ)
          = ((F i).card : ℝ)⁻¹ • ∑ a ∈ F i, (vert a : Fin (n+1) → ℝ) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have hsupp : (SdPieces 0).support = {idPiece 0} := by
      rw [show SdPieces 0 = Finsupp.single (idPiece 0) 1 from rfl]
      simp
    rw [hsupp, Finset.mem_singleton] at hp
    subst hp
    refine ⟨fun _ => Finset.univ, fun i => Finset.univ_nonempty, fun i j hij => le_rfl, ?_⟩
    intro i
    funext j
    have hij : i = j := by omega
    subst hij
    simp [idPiece]
  | succ k ih =>
    intro p hp
    rw [show SdPieces (k+1) =
        ∑ i : Fin (k+2), (-1 : ℚ) ^ (i : ℕ) •
          conePieces (bary (k+1)) k (pushPieces (faceIncl i) k (SdPieces k)) from rfl] at hp
    have hp2 := Finsupp.support_finsetSum hp
    rw [Finset.mem_biUnion] at hp2
    obtain ⟨i, -, hi⟩ := hp2
    have hi' : p ∈ (conePieces (bary (k+1)) k
        (pushPieces (faceIncl i) k (SdPieces k))).support := Finsupp.support_smul hi
    obtain ⟨q₁, hq₁, rfl⟩ := mem_support_conePieces hi'
    obtain ⟨q₀, hq₀, rfl⟩ := mem_support_pushPieces hq₁
    obtain ⟨F₀, hne₀, hanti₀, hcmp₀⟩ := ih hq₀
    set G : Fin (k+2) → Finset (Fin (k+2)) :=
      Fin.cases Finset.univ (fun j => (F₀ j).image (Fin.succAbove i)) with hG
    refine ⟨G, ?_, ?_, ?_⟩
    · intro m
      rw [hG]
      simp only []
      rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨j, rfl⟩
      · rw [Fin.cases_zero]; exact Finset.univ_nonempty
      · rw [Fin.cases_succ]; exact (hne₀ j).image (Fin.succAbove i)
    · intro a b hab
      rw [hG]
      simp only []
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
      · intro x _
        rw [Fin.cases_zero]
        exact Finset.mem_univ x
      · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
        · exact absurd (Fin.le_iff_val_le_val.mp hab) (Nat.not_succ_le_zero a'.val)
        · rw [Fin.cases_succ, Fin.cases_succ]
          exact Finset.image_subset_image (hanti₀ (Fin.succ_le_succ_iff.mp hab))
    · intro m
      rw [hG]
      simp only []
      rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨j, rfl⟩
      · rw [Fin.cases_zero, conePiece_zero]
        exact bary_centroid
      · rw [Fin.cases_succ, conePiece_succ]
        change (faceIncl i (q₀ j) : Fin (k+2) → ℝ) = _
        rw [faceIncl_centroid i (hcmp₀ j)]
        rw [Finset.card_image_of_injective _ (Fin.succAbove_right_injective)]

/-! ## One subdivision step shrinks the mesh -/

/-- Pushing one barycentric subdivision step onto an arbitrary simplex shrinks the mesh of every
piece by the factor `n/(n+1)`. -/
theorem meshV_subdividePiece_le {n : ℕ} (Q : Piece n n) (p : Piece n n)
    (hp : p ∈ (SdPieces n).support) :
    Metric.diam (vtxSet (fun i => affineSimplex Q (p i)))
      ≤ ((n : ℝ) / (n + 1)) * Metric.diam (vtxSet Q) := by
  obtain ⟨F, hne, hanti, hcmp⟩ := exists_faceChain_mem_support_SdPieces n hp
  have hset : vtxSet (fun i => affineSimplex Q (p i))
      = Set.range fun i => ((F i).card : ℝ)⁻¹ •
          ∑ a ∈ F i, (Q a : Fin (n+1) → ℝ) := by
    ext x; constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (affineSimplex_centroid_coe (Q := Q) (hcmp i)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, affineSimplex_centroid_coe (Q := Q) (hcmp i)⟩
  rw [hset]
  have hcoef : ((Fintype.card (Fin (n+1)) : ℝ) - 1) / (Fintype.card (Fin (n+1)))
      = (n : ℝ) / (n + 1) := by
    rw [Fintype.card_fin]; push_cast; ring
  have hC : 0 ≤ ((n : ℝ) / (n + 1)) * Metric.diam (vtxSet Q) :=
    mul_nonneg (by positivity) Metric.diam_nonneg
  refine Metric.diam_le_of_forall_dist_le hC ?_
  rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
  rcases le_total i j with hij | hij
  · have hsub : F j ⊆ F i := hanti hij
    have hb := mesh_step (fun a : Fin (n+1) => (Q a : Fin (n+1) → ℝ)) (F j) (F i) (hne j) hsub
    rw [hcoef] at hb
    rw [dist_eq_norm, norm_sub_rev]
    rw [show Set.range (fun a : Fin (n+1) => (Q a : Fin (n+1) → ℝ)) = vtxSet Q from rfl] at hb
    exact hb
  · have hsub : F i ⊆ F j := hanti hij
    have hb := mesh_step (fun a : Fin (n+1) => (Q a : Fin (n+1) → ℝ)) (F i) (F j) (hne i) hsub
    rw [hcoef] at hb
    rw [dist_eq_norm]
    rw [show Set.range (fun a : Fin (n+1) => (Q a : Fin (n+1) → ℝ)) = vtxSet Q from rfl] at hb
    exact hb

/-! ## Iterating -/

/-- The mesh of the `N`-fold barycentric subdivision of `Δⁿ` decays geometrically. -/
theorem meshV_SdPiecesPow_le (n : ℕ) (N : ℕ) (q : Piece n n)
    (hq : q ∈ (SdPiecesPow N n).support) :
    Metric.diam (vtxSet q)
      ≤ ((n : ℝ) / (n + 1)) ^ N * Metric.diam (vtxSet (idPiece n)) := by
  induction N generalizing q with
  | zero =>
    have hsupp : (SdPiecesPow 0 n).support = {idPiece n} := by
      rw [show SdPiecesPow 0 n = Finsupp.single (idPiece n) 1 from rfl]
      simp
    rw [hsupp, Finset.mem_singleton] at hq
    subst hq
    rw [pow_zero, one_mul]
  | succ K ih =>
    rw [SdPiecesPow_succ] at hq
    have hq2 := Finsupp.support_sum hq
    rw [Finset.mem_biUnion] at hq2
    obtain ⟨Q, hQ, hqQ⟩ := hq2
    have hq' : q ∈ (subdividePiece Q).support := Finsupp.support_smul hqQ
    rw [subdividePiece] at hq'
    obtain ⟨p, hp, hpq⟩ := mem_support_pushPieces hq'
    rw [← hpq]
    calc Metric.diam (vtxSet (pushPiece (fun x => affineSimplex Q x) p))
        = Metric.diam (vtxSet (fun i => affineSimplex Q (p i))) := rfl
      _ ≤ ((n : ℝ) / (n + 1)) * Metric.diam (vtxSet Q) := meshV_subdividePiece_le Q p hp
      _ ≤ ((n : ℝ) / (n + 1)) *
            (((n : ℝ) / (n + 1)) ^ K * Metric.diam (vtxSet (idPiece n))) :=
          mul_le_mul_of_nonneg_left (ih Q hQ) (by positivity)
      _ = ((n : ℝ) / (n + 1)) ^ (K + 1) * Metric.diam (vtxSet (idPiece n)) := by
          rw [pow_succ]; ring

/-! ## The mesh of the iterated subdivision tends to zero -/

/-- The `N`-fold barycentric subdivision of `Δⁿ` has mesh tending to zero: for every `ε > 0`
there is `N` such that every piece in the support of `SdPiecesPow N n` has diameter `< ε`.
Each piece of the subdivision is the convex hull of the centroids of a chain of nonempty subsets of
the vertex set `Fin (n+1)`, so `Work.Subdivision.diam_convexHull_centroid_le` (a one-step bound by
`n/(n+1)` times the diameter) iterates. -/
theorem SdPiecesPow_diam_lt (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ q : Submission.Cohomology.Piece n n,
      q ∈ (Submission.Cohomology.SdPiecesPow N n).support →
      Metric.diam (Set.range fun t => (Submission.Cohomology.affineSimplex q t :
        Submission.Cohomology.TSimplex n)) < ε := by
  set D0 : ℝ := Metric.diam (vtxSet (idPiece n)) with hD0
  have hD0nonneg : 0 ≤ D0 := by rw [hD0]; exact Metric.diam_nonneg
  have hr0 : 0 ≤ (n : ℝ) / (n + 1) := by positivity
  have hr1 : (n : ℝ) / (n + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have htend : Filter.Tendsto (fun N : ℕ => ((n : ℝ) / (n + 1)) ^ N * D0)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const D0
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend) ε hε
  refine ⟨N, fun q hq => ?_⟩
  rw [diam_range_affineSimplex_eq_diam_vtxSet q]
  have hle := meshV_SdPiecesPow_le n N q hq
  rw [← hD0] at hle
  have hNN := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hNN
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hr0 N) hD0nonneg)] at hNN
  exact lt_of_le_of_lt hle hNN

end

end Work.Subdivision
