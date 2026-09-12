import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_mem_intrinsicInterior_exposedFace
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_disjoint_intrinsicInterior_faces
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_parallelBody_cellDecomposition
import Submission.Commons.Geometry.Convex.Hadwiger.finite_exposedFaces_convexHull
import Submission.Commons.Geometry.Convex.Hadwiger.frontier_mem_facet
import Submission.Commons.Geometry.Convex.Hadwiger.facet_containing_proper_face
import Submission.Commons.Geometry.Convex.Hadwiger.cone_int_mem
import Submission.Commons.Geometry.Convex.Hadwiger.exists_frontier_on_segment_of_mem_interior
universe u

open Set Filter
open scoped BigOperators Topology Pointwise Convex

noncomputable section

namespace Commons.Geometry.Convex.Hadwiger

set_option linter.unusedVariables false

/-! # Triangulation of the convex hull of a finite point set

`convexHull_triangulation_rel`: if `S : Finset V` is nonempty and `d` is the
dimension of the affine hull of `S`, then `convexHull S` is the finite union
of `d`-simplices with pairwise disjoint (relative) interiors.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- differences of two points of an affine subspace lie in its direction -/
lemma vsub_mem_direction_of_mem {A : AffineSubspace ℝ V} {a b : V} (ha : a ∈ A) (hb : b ∈ A) :
    a - b ∈ A.direction := by
  rw [← vsub_eq_sub]
  exact (AffineSubspace.vsub_right_mem_direction_iff_mem (s := A) (p := b) hb a).mpr ha

/-- if `s0 ∈ S`, every other point of `S` differs from `s0` by an element of the direction -/
lemma mem_direction_sub_of_mem_finset (S : Finset V) (s0 : V) (hs0 : s0 ∈ S) {s : V}
    (hs : s ∈ S) : s - s0 ∈ (affineSpan ℝ (S : Set V)).direction := by
  apply vsub_mem_direction_of_mem
  · exact subset_affineSpan ℝ (S : Set V) (by simpa using hs)
  · exact subset_affineSpan ℝ (S : Set V) (by simpa using hs0)

/-- if the direction has dimension 0 and S is nonempty, all points of S are equal -/
lemma eq_of_finrank_direction_zero {S : Finset V} (hS : S.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ (S : Set V)).direction = 0) :
    ∀ s ∈ S, ∀ t ∈ S, s = t := by
  classical
  rcases hS with ⟨s0, hs0⟩
  have hdir : (affineSpan ℝ (S : Set V)).direction = ⊥ :=
    (Submodule.finrank_eq_zero (S := (affineSpan ℝ (S : Set V)).direction)).mp hdim
  intro s hs t ht
  have hsub : s - s0 = 0 := by
    have : s - s0 ∈ (affineSpan ℝ (S : Set V)).direction :=
      mem_direction_sub_of_mem_finset S s0 hs0 hs
    have hbot : s - s0 ∈ (⊥ : Submodule ℝ V) := by simpa [hdir] using this
    exact (Submodule.mem_bot ℝ).mp hbot
  have htsub : t - s0 = 0 := by
    have : t - s0 ∈ (affineSpan ℝ (S : Set V)).direction :=
      mem_direction_sub_of_mem_finset S s0 hs0 ht
    have hbot : t - s0 ∈ (⊥ : Submodule ℝ V) := by simpa [hdir] using this
    exact (Submodule.mem_bot ℝ).mp hbot
  calc
    s = s0 := sub_eq_zero.mp hsub
    _ = t := (sub_eq_zero.mp htsub).symm

/-! ## The main local structure: what a triangulation is -/

/-- data of a triangulation of a point set by `d`-simplices -/
def HasTriang (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (d : ℕ) (S : Finset V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι), ∃ A : ι → Set V, ∃ w : ι → Fin (d + 1) → V,
    (⋃ i : ι, A i = convexHull ℝ (S : Set V)) ∧
    (∀ i : ι, A i = convexHull ℝ (Set.range (w i))) ∧
    (∀ i : ι, AffineIndependent ℝ (w i)) ∧
    (∀ i j : ι, i ≠ j →
      Disjoint (intrinsicInterior ℝ (A i)) (intrinsicInterior ℝ (A j)))

/-- The claim of `convexHull_triangulation_rel` -/
def RelClaim (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Finset V) : Prop :=
  HasTriang V (Module.finrank ℝ (affineSpan ℝ (S : Set V)).direction) S

/-- full-dimensional version: `u` spans all of `V`, ambient dimension `n` -/
def FullClaim (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (n : ℕ) (u : Finset V) : Prop :=
  HasTriang V n u


/-! ## Appending an apex point to a `Fin n`-indexed family -/

/-- append `O` to the family `v : Fin n → V` at the last position (typed function) -/
abbrev snocLC (n : ℕ) (v : Fin n → V) (O : V) : Fin (n + 1) → V :=
  fun i => Fin.lastCases O (fun k : Fin n => v k) i

@[simp] lemma snocLC_castSucc {n : ℕ} (v : Fin n → V) (O : V) (k : Fin n) :
    snocLC n v O k.castSucc = v k := by
  simp [snocLC]

@[simp] lemma snocLC_last {n : ℕ} (v : Fin n → V) (O : V) :
    snocLC n v O (Fin.last n) = O := by
  simp [snocLC]

/-- value of the appended family away from the last index is the corresponding `v` -/
lemma snocLC_eq_v_of_ne_last {n : ℕ} (v : Fin n → V) (O : V) {i : Fin (n + 1)}
    (hi : i ≠ Fin.last n) : snocLC n v O i = v (Fin.castPred i hi) := by
  rcases (Fin.eq_castSucc_of_ne_last hi) with ⟨k, rfl⟩
  rw [snocLC_castSucc]
  have hck : Fin.castPred k.castSucc hi = k := by
    apply Fin.ext
    simp
  rw [hck]

/-- the range of the appended family is the base range together with `O` -/
lemma range_snocLC {n : ℕ} (v : Fin n → V) (O : V) :
    Set.range (snocLC n v O) = insert O (Set.range v) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last => simp
    | cast k => simp
  · intro hz
    rcases hz with rfl | ⟨k, rfl⟩
    · exact ⟨Fin.last n, by simp⟩
    · exact ⟨k.castSucc, by simp⟩

/-- appending a point outside the affine hull preserves affine independence -/
lemma affineIndependent_snocLC {n : ℕ} (v : Fin n → V) (hv : AffineIndependent ℝ v) (O : V)
    (hO : O ∉ affineSpan ℝ (Set.range v)) : AffineIndependent ℝ (snocLC n v O) := by
  classical
  have h1 : AffineIndependent ℝ (fun x : {y : Fin (n + 1) // y ≠ Fin.last n} =>
      snocLC n v O x.1) := by
    let e : {y : Fin (n + 1) // y ≠ Fin.last n} ≃ Fin n := {
      toFun := fun x => Fin.castPred x.1 x.2
      invFun := fun k => ⟨k.castSucc, (Fin.castSucc_lt_last k).ne⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact (Fin.castSucc_castPred x.1 x.2).symm
      right_inv := by
        intro k
        apply Fin.ext
        simp }
    have hc : (fun x : {y : Fin (n + 1) // y ≠ Fin.last n} => snocLC n v O x.1)
        = v ∘ e := by
      funext x
      exact snocLC_eq_v_of_ne_last v O x.2
    rw [hc]
    exact (affineIndependent_equiv (e := e) (p := v)).mpr hv
  have h2 : snocLC n v O (Fin.last n) ∉ affineSpan ℝ
      ((fun x : Fin (n + 1) => snocLC n v O x) '' {x : Fin (n + 1) | x ≠ Fin.last n}) := by
    have hset : ((fun x : Fin (n + 1) => snocLC n v O x) ''
        {x : Fin (n + 1) | x ≠ Fin.last n}) = Set.range v := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxne : x ≠ Fin.last n := by simpa using hx
        refine ⟨Fin.castPred x hxne, ?_⟩
        exact (snocLC_eq_v_of_ne_last v O hxne).symm
      · rintro ⟨k, rfl⟩
        refine ⟨k.castSucc, (Fin.castSucc_lt_last k).ne, ?_⟩
        simp
    rw [hset]
    simp
    exact hO
  exact AffineIndependent.affineIndependent_of_notMem_span (p := (snocLC n v O))
    (i := Fin.last n) h1 h2

/-! ## transport along an injective affine map that preserves everything -/

/-- A transport lemma: a triangulation is preserved by a linear isometry
embedding composed with a translation (an affine isometry). -/
private lemma tri_transport {V₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [FiniteDimensional ℝ V₂] [DecidableEq V] (φ : V₂ →ᵃⁱ[ℝ] V) (d : ℕ) (u : Finset V₂) :
    HasTriang V₂ d u → HasTriang V d (u.image fun x : V₂ => φ x) := by
  classical
  rintro ⟨ι, hι, A, w, hunion, hAs, hwind, hdisj⟩
  refine ⟨ι, hι, (fun i => φ '' A i), (fun i k => φ (w i k)), ?_, ?_, ?_, ?_⟩
  · calc
      (⋃ i : ι, (φ '' A i)) = φ '' (⋃ i : ι, A i) := by
        rw [← Set.image_iUnion]
      _ = φ '' convexHull ℝ (u : Set V₂) := by rw [hunion]
      _ = convexHull ℝ (φ '' (u : Set V₂)) := by
        exact AffineMap.image_convexHull φ.toAffineMap (u : Set V₂)
      _ = convexHull ℝ ((u.image fun x : V₂ => φ x) : Set V) := by
        rw [Finset.coe_image]
  · intro i
    calc
      φ '' A i = φ '' convexHull ℝ (Set.range (w i)) := by rw [hAs i]
      _ = convexHull ℝ (φ '' Set.range (w i)) := by
        exact AffineMap.image_convexHull φ.toAffineMap (Set.range (w i))
      _ = convexHull ℝ (Set.range (fun k : Fin (d + 1) => φ (w i k))) := by
        congr 1
        ext y
        simp
  · intro i
    have hf : Function.Injective (⇑φ.toAffineMap) := by
      simpa using φ.injective
    exact (AffineMap.affineIndependent_iff (f := φ.toAffineMap) (p := w i) hf).mpr (hwind i)
  · intro i j hij
    have hA : intrinsicInterior ℝ (φ '' A i) = φ '' intrinsicInterior ℝ (A i) :=
      AffineIsometry.intrinsicInterior_image φ (A i)
    have hB : intrinsicInterior ℝ (φ '' A j) = φ '' intrinsicInterior ℝ (A j) :=
      AffineIsometry.intrinsicInterior_image φ (A j)
    rw [hA, hB]
    rw [disjoint_left]
    intro z hz₁ hz₂
    rcases hz₁ with ⟨a, ha₁, rfl⟩
    rcases hz₂ with ⟨b, hb₂, hφ⟩
    have hb₂' : a ∈ intrinsicInterior ℝ (A j) := by
      have : a = b := φ.injective hφ.symm
      simpa [this] using hb₂
    exact (disjoint_left.mp (hdisj i j hij)) ha₁ hb₂'

/-! ## relative interior inside a full-dimensional simplex -/

/-- a set whose affine span is everything has intrinsic interior equal to its interior -/
private lemma intrinsicInterior_eq_interior_of_affineSpan_top {s : Set V}
    (hspan : affineSpan ℝ s = ⊤) : intrinsicInterior ℝ s = interior s := by
  ext x
  constructor
  · intro hx
    rcases (mem_intrinsicInterior.mp hx) with ⟨y, hy, rfl⟩
    have hys : ((↑) ⁻¹' s : Set (affineSpan ℝ s)) ∈ 𝓝 y := by
      exact mem_interior_iff_mem_nhds.mp hy
    let p : V → Prop := fun z : V => z ∈ (affineSpan ℝ s)
    have hyP : p (y : V) := y.2
    have hcont : ∀ᶠ x in 𝓝 (y : V), p x := by
      apply Filter.Eventually.of_forall
      intro x
      have hxset : x ∈ (affineSpan ℝ s : Set V) := by
        rw [hspan]
        trivial
      exact (AffineSubspace.mem_coe x (affineSpan ℝ s)).mp hxset
    have hmap := map_nhds_subtype_coe_eq_nhds (p := p) (x := (y : V)) hyP hcont
    have hmem : s ∈ map (fun z : (affineSpan ℝ s) => (z : V)) (𝓝 y) := by
      exact Filter.mem_map.mpr hys
    rw [hmap] at hmem
    exact mem_interior_iff_mem_nhds.mpr hmem
  · intro hx
    exact interior_subset_intrinsicInterior hx

/-! ## faces (facets) of a full-dimensional polytope -/

/-- the set of facets (codimension-one exposed faces) of the polytope `P` -/
private noncomputable def facetFinset (u : Finset V) (P : Set V) : Finset (Set V) := by
  classical
  exact ((u.powerset.image (fun T : Finset V => convexHull ℝ (T : Set V))).filter
    (fun F : Set V => F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P ∧
      Module.finrank ℝ (affineSpan ℝ (F : Set V)).direction = Module.finrank ℝ V - 1))

/-- a boundary point of a full-dimensional polytope belongs to a facet -/
private lemma facet_of_frontier (u : Finset V) (P : Set V) (hP : P = convexHull ℝ (u : Set V))
    (hint : (interior P).Nonempty) {x : V} (hxP : x ∈ P) (hxint : x ∉ interior P) :
    ∃ F : Set V, F ∈ facetFinset u P ∧ x ∈ F := by
  classical
  rcases Commons.Geometry.Convex.Hadwiger.frontier_mem_facet u P hP hint hxP hxint with
    ⟨F, hFne, hFexp, hFneP, hdim, hxF⟩
  refine ⟨F, ?_, hxF⟩
  -- F ∈ facetFinset u P: F = convexHull of a subset of u and satisfies the facet predicate
  have hFcv : F = convexHull ℝ (F ∩ (u : Set V)) :=
    exposedFace_conv_vertices_generic u P hP hFexp hFne
  let T : Finset V := u.filter (fun y : V => y ∈ F)
  have hT : (T : Set V) = F ∩ (u : Set V) := by
    ext y
    simp [T]
    constructor <;> intro hy <;> exact ⟨hy.2, hy.1⟩
  have hmemimg : F ∈ (u.powerset.image (fun T' : Finset V => convexHull ℝ (T' : Set V))) := by
    apply Finset.mem_image.mpr
    refine ⟨T, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr (Finset.filter_subset (fun y : V => y ∈ F) u)
    · calc
        convexHull ℝ (T : Set V) = convexHull ℝ (F ∩ (u : Set V)) := by rw [hT]
        _ = F := hFcv.symm
  rw [facetFinset]
  rw [Finset.mem_filter]
  exact ⟨hmemimg, hFne, hFexp, hFneP, hdim⟩

/-- a facet is the convex hull of the generators it contains -/
private lemma facet_eq_convexHull (u : Finset V) (P : Set V) (hP : P = convexHull ℝ (u : Set V))
    {F : Set V} (hF : F ∈ facetFinset u P) : F = convexHull ℝ (F ∩ (u : Set V)) := by
  classical
  have hFp := (Finset.mem_filter.mp hF).2
  rcases hFp with ⟨hFne, hFexp, hFneP, hdim⟩
  exact exposedFace_conv_vertices_generic u P hP hFexp hFne



private def levelSetAffSub (l : V →L[ℝ] ℝ) (c : ℝ) : AffineSubspace ℝ V :=
  { carrier := {y : V | l y = c},
    smul_vsub_vadd_mem' := by
      intro a p1 p2 p3 hp1 hp2 hp3
      change l (a • (p1 - p2) + p3) = c
      rw [map_add, map_smul, map_sub]
      have hp1' : l p1 = c := hp1
      have hp2' : l p2 = c := hp2
      have hp3' : l p3 = c := hp3
      simp [hp1', hp2', hp3', smul_eq_mul] }
private lemma exposed_not_interior {P F : Set V} (hF : IsExposed ℝ P F) (hFne : F.Nonempty)
    (hFproper : F ≠ P) {x : V} (hxF : x ∈ F) : x ∉ interior P := by
  classical
  rcases hF hFne with ⟨l₀, hFeq⟩
  have hPmax : ∀ y ∈ P, l₀ y ≤ l₀ x := by
    rw [hFeq] at hxF
    exact hxF.2
  have hxP : x ∈ P := by
    rw [hFeq] at hxF
    exact hxF.1
  have hl₀ne : l₀ ≠ 0 := by
    intro h0
    apply hFproper
    rw [hFeq]
    ext z
    constructor
    · intro hz; exact hz.1
    · intro hzP
      exact ⟨hzP, fun y hy => by simpa [h0] using hPmax y hy⟩
  have hne : ∃ v : V, l₀ v ≠ 0 := by
    by_contra h
    apply hl₀ne
    ext v
    exact by_contra (fun hv => h ⟨v, hv⟩)
  rcases hne with ⟨v, hv⟩
  have hvpos : 0 < l₀ v ∨ l₀ v < 0 := lt_or_gt_of_ne hv.symm
  let w : V := if h : 0 < l₀ v then v else -v
  have hwpos : 0 < l₀ w := by
    by_cases hp : 0 < l₀ v
    · simp [w, hp]
    · have hn : l₀ v < 0 := lt_of_le_of_ne (le_of_not_gt hp) hv
      simp [w, hp]
      linarith
  intro hxint
  rcases mem_interior.mp hxint with ⟨t, htP, ht, hxt⟩
  rcases (Metric.isOpen_iff.mp ht) x hxt with ⟨r, hr0, hball⟩
  let m : ℝ := ‖w‖ + 1
  have hm : 0 < m := by
    dsimp [m]
    linarith [norm_nonneg w]
  let δ : ℝ := r / (2 * m)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    positivity
  have hδm : δ * m = r / 2 := by
    dsimp [δ]
    field_simp [hm.ne']
  have hδw : δ * ‖w‖ ≤ r / 2 := by
    have hle : δ * ‖w‖ ≤ δ * m :=
      mul_le_mul_of_nonneg_left (by dsimp [m]; linarith) (le_of_lt hδ0)
    rwa [hδm] at hle
  have hδwlt : δ * ‖w‖ < r := by linarith
  have hin_ball : x + δ • w ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    calc
      ‖x - (x + δ • w)‖ = ‖δ • w‖ := by
        rw [show x - (x + δ • w) = -(δ • w) by abel]
        simp
      _ = δ * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ0]
      _ < r := hδwlt
  have hxδP : x + δ • w ∈ P := htP (hball hin_ball)
  have hval : l₀ (x + δ • w) = l₀ x + δ * l₀ w := by
    rw [map_add, map_smul]
    simp [smul_eq_mul]
  have hlt : l₀ x < l₀ (x + δ • w) := by
    rw [hval]
    nlinarith [mul_pos hδ0 hwpos]
  have hle := hPmax (x + δ • w) hxδP
  exact (not_lt_of_ge hle) hlt


private lemma int_not_mem_affineSpan_facet_of_exposed (P : Set V)
    {F : Set V} (hFexp : IsExposed ℝ P F) (hFne : F.Nonempty) (hFproper : F ≠ P)
    {O : V} (hO : O ∈ interior P) :
    O ∉ (affineSpan ℝ (F : Set V) : Set V) := by
  classical
  rcases hFne with ⟨w, hwF⟩
  let l₀ : V →L[ℝ] ℝ := Classical.choose (hFexp ⟨w, hwF⟩)
  have hFmax : F = {y : V | y ∈ P ∧ ∀ z ∈ P, l₀ z ≤ l₀ y} :=
    Classical.choose_spec (hFexp ⟨w, hwF⟩)
  have hwF' : w ∈ {y : V | y ∈ P ∧ ∀ z ∈ P, l₀ z ≤ l₀ y} := by simpa [hFmax] using hwF
  have hPmax : ∀ z ∈ P, l₀ z ≤ l₀ w := hwF'.2
  have hFconst : ∀ y ∈ F, l₀ y = l₀ w := by
    intro y hy
    have hy' : y ∈ {x : V | x ∈ P ∧ ∀ z ∈ P, l₀ z ≤ l₀ x} := by simpa [hFmax] using hy
    apply le_antisymm
    · exact hPmax y hy'.1
    · exact hy'.2 w hwF'.1
  intro hOspan
  have hspan_le_A : ((affineSpan ℝ (F : Set V)) : Set V) ⊆ {y : V | l₀ y = l₀ w} := by
    have hFle : (F : Set V) ⊆ {y : V | l₀ y = l₀ w} := by
      intro y hy
      exact hFconst y hy
    -- affinespan(F) ⊆ level set because the level set is an affine subspace containing F
    have hAeq : ((levelSetAffSub l₀ (l₀ w)) : Set V) = {y : V | l₀ y = l₀ w} := rfl
    rw [← hAeq]
    exact (affineSpan_le.mpr hFle : affineSpan ℝ (F : Set V) ≤ levelSetAffSub l₀ (l₀ w))
  have hOlevel : l₀ O = l₀ w := hspan_le_A hOspan
  have hOF : O ∈ F := by
    rw [hFmax]
    refine ⟨interior_subset hO, ?_⟩
    intro z hz
    calc
      l₀ z ≤ l₀ w := hPmax z hz
      _ = l₀ O := hOlevel.symm
  exact (exposed_not_interior hFexp ⟨w, hwF⟩ hFproper hOF) hO


/-- an interior point of a full-dimensional polytope does not lie in the affine span of a facet -/
private lemma int_not_mem_affineSpan_facet (u : Finset V) (P : Set V)
    {F : Set V} (hF : F ∈ facetFinset u P) {O : V} (hO : O ∈ interior P) :
    O ∉ (affineSpan ℝ (F : Set V) : Set V) := by
  classical
  rcases (Finset.mem_filter.mp hF).2 with ⟨hFne, hFexp, hFneP, hdim⟩
  exact int_not_mem_affineSpan_facet_of_exposed P hFexp hFne hFneP hO


/-- the vertex set of a facet spans a codimension-one affine subspace -/
private lemma finrank_direction_facet (u : Finset V) (P : Set V) (hP : P = convexHull ℝ (u : Set V))
    {F : Set V} (hF : F ∈ facetFinset u P) :
    Module.finrank ℝ (affineSpan ℝ (F ∩ (u : Set V))).direction = Module.finrank ℝ V - 1 := by
  classical
  rcases (Finset.mem_filter.mp hF).2 with ⟨hFne, hFexp, hFneP, hdim⟩
  have hsp : affineSpan ℝ (F : Set V) = affineSpan ℝ (F ∩ (u : Set V)) := by
    calc
      affineSpan ℝ (F : Set V) = affineSpan ℝ (convexHull ℝ (F ∩ (u : Set V))) := by
        congr 1
        exact facet_eq_convexHull u P hP (hF := hF)
      _ = affineSpan ℝ (F ∩ (u : Set V)) := affineSpan_convexHull (𝕜 := ℝ) (s := F ∩ (u : Set V))
  rwa [hsp] at hdim

/-! ## more lemmas for the fan (coning) construction -/

/-- the intrinsic interior is monotone under subsets that do not change the affine span -/
private lemma intrinsicInterior_mono_of_affineSpan_eq {s t : Set V} (hst : s ⊆ t)
    (hsp : affineSpan ℝ s = affineSpan ℝ t) :
    intrinsicInterior ℝ s ⊆ intrinsicInterior ℝ t := by
  rw [intrinsicInterior, intrinsicInterior]
  rw [hsp]
  exact image_mono (interior_mono (by intro x hx; exact hst hx))

/-- all conditions satisfied by a member of `facetFinset` -/
private lemma facet_props (u : Finset V) (P : Set V) {F : Set V} (hF : F ∈ facetFinset u P) :
    F.Nonempty ∧ IsExposed ℝ P F ∧ F ≠ P ∧
      Module.finrank ℝ (affineSpan ℝ (F : Set V)).direction = Module.finrank ℝ V - 1 := by
  classical
  rw [facetFinset] at hF
  exact (Finset.mem_filter.mp hF).2

/-- the affine span of an affinely independent `n`-tuple lying inside a facet is the whole
affine span of that facet -/
private lemma affineSpan_range_eq_affineSpan_facet {n : ℕ} (hnpos : 0 < n)
    (u : Finset V) (P : Set V) {F : Set V} (hF : F ∈ facetFinset u P)
    (hfin : Module.finrank ℝ V = n) {w : Fin n → V} (hw : AffineIndependent ℝ w)
    (hwF : ∀ j : Fin n, w j ∈ F) :
    affineSpan ℝ (Set.range w) = affineSpan ℝ F := by
  have hle : affineSpan ℝ (Set.range w) ≤ affineSpan ℝ F := by
    exact affineSpan_mono ℝ (by rintro z ⟨j, rfl⟩; exact hwF j)
  have hdimF : Module.finrank ℝ (affineSpan ℝ (F : Set V)).direction = n - 1 := by
    have h := (facet_props u P hF).2.2.2
    simpa [hfin] using h
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (affineSpan ℝ F).direction + 1 := by
    rw [hdimF]
    simp only [Fintype.card_fin]
    omega
  exact AffineIndependent.affineSpan_eq_of_le_of_card_eq_finrank_add_one hw hle hcard

/-- coning lemma: a point of the relative interior of the cone from `O` over the simplex
spanned by `v` lies on an open segment `(1-t)O + t z` with `z` in the relative interior of
the base simplex -/
private lemma cone_int_decomp {m : ℕ} (hm : 0 < m) (v : Fin m → V) (O : V)
    (hAff : AffineIndependent ℝ (snocLC m v O))
    (hspan : affineSpan ℝ (Set.range (snocLC m v O)) = ⊤)
    {p : V} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range (snocLC m v O)))) :
    ∃ t : ℝ, t ∈ Set.Ioo 0 1 ∧ ∃ z : V,
      z ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range v)) ∧
      p = (1 - t) • O + t • z := by
  rcases Commons.Geometry.Convex.Hadwiger.cone_int_mem (V := V) hm (snocLC m v O) hAff hspan hp
    with ⟨t, ht, z, hz, hEq⟩
  refine ⟨t, ht, z, ?_, ?_⟩
  · have hcast : (fun k : Fin m => snocLC m v O k.castSucc) = v := by
      funext k
      simp
    simpa [hcast] using hz
  · simpa using hEq

/-- applying a linear functional to points of a convex hull of a family on which it is constant -/
private lemma linear_eq_on_convexHull_range {m : ℕ} (l : V →L[ℝ] ℝ) {c : ℝ} {v : Fin m → V}
    (h : ∀ j : Fin m, l (v j) = c) {z : V} (hz : z ∈ convexHull ℝ (Set.range v)) :
    l z = c := by
  have hlin : l z ∈ l '' convexHull ℝ (Set.range v) := ⟨z, hz, rfl⟩
  have hsub : l '' convexHull ℝ (Set.range v) ⊆ ({c} : Set ℝ) := by
    calc
      l '' convexHull ℝ (Set.range v) = convexHull ℝ (l '' Set.range v) := by
        exact (AffineMap.image_convexHull l.toLinearMap.toAffineMap (Set.range v))
      _ ⊆ convexHull ℝ ({c} : Set ℝ) := by
        exact convexHull_mono (by
          rintro x ⟨z, ⟨j, rfl⟩, rfl⟩
          simpa [h j])
      _ = ({c} : Set ℝ) := by simp
  simpa using hsub hlin

/-- the open segment from an interior point of a convex set to any of its points stays interior -/
private lemma openSegment_interior_subset {P : Set V} (hPcvx : Convex ℝ P)
    {O z : V} (hO : O ∈ interior P) (hz : z ∈ P) :
    openSegment ℝ O z ⊆ interior P := by
  rw [openSegment_subset_iff]
  intro a b ha hb hab
  exact hPcvx.combo_interior_self_mem_interior hO hz ha hb.le hab

/-- an interior point cannot lie on a nonempty proper exposed face -/
private lemma not_mem_interior_of_exposed {P F : Set V} (hFexp : IsExposed ℝ P F)
    (hFne : F.Nonempty) (hFproper : F ≠ P) {x : V} (hxF : x ∈ F) : x ∉ interior P :=
  exposed_not_interior hFexp hFne hFproper hxF

/-! ## data extraction from a `HasTriang` witness -/

private noncomputable def tri_ι {d : ℕ} {S : Finset V} (h : HasTriang V d S) : Type :=
  Classical.choose h

private noncomputable def tri_fintype {d : ℕ} {S : Finset V} (h : HasTriang V d S) :
    Fintype (tri_ι h) :=
  Classical.choose (Classical.choose_spec h)

private noncomputable def tri_A {d : ℕ} {S : Finset V} (h : HasTriang V d S) : tri_ι h → Set V :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec h))

private noncomputable def tri_w {d : ℕ} {S : Finset V} (h : HasTriang V d S) :
    tri_ι h → Fin (d + 1) → V :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))

private lemma tri_props {d : ℕ} {S : Finset V} (h : HasTriang V d S) :
    (⋃ i : tri_ι h, tri_A h i = convexHull ℝ (S : Set V)) ∧
    (∀ i : tri_ι h, tri_A h i = convexHull ℝ (Set.range (tri_w h i))) ∧
    (∀ i : tri_ι h, AffineIndependent ℝ (tri_w h i)) ∧
    (∀ i j : tri_ι h, i ≠ j →
      Disjoint (intrinsicInterior ℝ (tri_A h i)) (intrinsicInterior ℝ (tri_A h j))) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))

/-- a piece of a triangulation is contained in the set it triangulates -/
private lemma tri_union {d : ℕ} {S : Finset V} (h : HasTriang V d S) :
    (⋃ i : tri_ι h, tri_A h i = convexHull ℝ (S : Set V)) := (tri_props h).1

private lemma tri_piece {d : ℕ} {S : Finset V} (h : HasTriang V d S) :
    ∀ i : tri_ι h, tri_A h i = convexHull ℝ (Set.range (tri_w h i)) := (tri_props h).2.1

private lemma tri_aff {d : ℕ} {S : Finset V} (h : HasTriang V d S) :
    ∀ i : tri_ι h, AffineIndependent ℝ (tri_w h i) := (tri_props h).2.2.1

private lemma tri_disj {d : ℕ} {S : Finset V} (h : HasTriang V d S) :
    ∀ i j : tri_ι h, i ≠ j →
      Disjoint (intrinsicInterior ℝ (tri_A h i)) (intrinsicInterior ℝ (tri_A h j)) :=
  (tri_props h).2.2.2

private lemma piece_subset_conv {d : ℕ} {T : Finset V} (hTri : HasTriang V d T)
    (i : tri_ι hTri) : tri_A hTri i ⊆ convexHull ℝ (T : Set V) := by
  intro z hz
  rw [← (tri_props hTri).1]
  exact Set.mem_iUnion.mpr ⟨i, hz⟩

private lemma affineIndependent_comp_equiv {m n : ℕ} (e : Fin m ≃ Fin n) {v : Fin n → V}
    (hv : AffineIndependent ℝ v) : AffineIndependent ℝ (v ∘ e) := by
  exact AffineIndependent.comp_embedding (f := e.toEmbedding) (p := v) hv

private lemma range_comp_equiv {α β : Type*} (e : α ≃ β) (f : β → V) :
    Set.range (f ∘ e) = Set.range f :=
  Function.Surjective.range_comp e.surjective f

/-- the functional exhibiting an exposed face is constant on that face -/
private lemma exposed_func_const_on {P F : Set V} (hFexp : IsExposed ℝ P F) {x x0 : V}
    (hxF : x ∈ F) (hx0F : x0 ∈ F) :
    Classical.choose (hFexp ⟨x0, hx0F⟩) x = Classical.choose (hFexp ⟨x0, hx0F⟩) x0 := by
  let l : V →L[ℝ] ℝ := Classical.choose (hFexp ⟨x0, hx0F⟩)
  have hFeq : F = {x : V | x ∈ P ∧ ∀ y ∈ P, l y ≤ l x} :=
    Classical.choose_spec (hFexp ⟨x0, hx0F⟩)
  have hxF' : x ∈ {x : V | x ∈ P ∧ ∀ y ∈ P, l y ≤ l x} := by simpa [hFeq] using hxF
  have hx0F' : x0 ∈ {x : V | x ∈ P ∧ ∀ y ∈ P, l y ≤ l x} := by simpa [hFeq] using hx0F
  apply le_antisymm
  · exact hx0F'.2 x hxF'.1
  · exact hxF'.2 x0 hx0F'.1

/-- an interior point of `P` cannot satisfy the level equality of a proper exposed face -/
private lemma interior_point_not_on_exposed_level {P F : Set V} (hFexp : IsExposed ℝ P F)
    (hFne : F.Nonempty) (hFproper : F ≠ P) {O x0 : V} (hOint : O ∈ interior P) (hx0F : x0 ∈ F) :
    Classical.choose (hFexp hFne) O ≠ Classical.choose (hFexp hFne) x0 := by
  intro hEq
  let l : V →L[ℝ] ℝ := Classical.choose (hFexp hFne)
  have hFeq : F = {x : V | x ∈ P ∧ ∀ y ∈ P, l y ≤ l x} := Classical.choose_spec (hFexp hFne)
  have hx0F' : x0 ∈ {x : V | x ∈ P ∧ ∀ y ∈ P, l y ≤ l x} := by simpa [hFeq] using hx0F
  have hx0P : x0 ∈ P := hx0F'.1
  have hmax : ∀ y ∈ P, l y ≤ l x0 := hx0F'.2
  have hOinF : O ∈ F := by
    rw [hFeq]
    refine ⟨interior_subset hOint, ?_⟩
    intro y hy
    calc
      l y ≤ l x0 := hmax y hy
      _ = l O := hEq.symm
  exact (not_mem_interior_of_exposed hFexp hFne hFproper hOinF) hOint

/-- if `z₁ - O = s • (z₂ - O)` for `s ∈ (0,1)`, then `z₁` is in the open segment `(O,z₂)` -/
private lemma mem_openSegment_of_sub_smul {O z₁ z₂ : V} {s : ℝ} (hs : s ∈ Set.Ioo 0 1)
    (h : z₁ - O = s • (z₂ - O)) : z₁ ∈ openSegment ℝ O z₂ := by
  rw [openSegment_eq_image_lineMap]
  refine ⟨s, hs, ?_⟩
  calc
    AffineMap.lineMap O z₂ s = s • (z₂ - O) + O := by rw [AffineMap.lineMap_apply_module']
    _ = (z₁ - O) + O := by rw [h]
    _ = z₁ := by abel

/-- scaling identity `t₁ (z₁-O) = t₂ (z₂-O)` implies `z₁-O = (t₂/t₁)(z₂-O)` -/
private lemma smul_sub_eq_smul_sub_iff_div {O z₁ z₂ : V} {t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0)
    (hvec : t₁ • (z₁ - O) = t₂ • (z₂ - O)) :
    z₁ - O = (t₂ / t₁) • (z₂ - O) := by
  calc
    z₁ - O = (1 : ℝ) • (z₁ - O) := by simp
    _ = (t₁⁻¹ * t₁) • (z₁ - O) := by rw [inv_mul_cancel₀ ht₁]
    _ = t₁⁻¹ • (t₁ • (z₁ - O)) := by rw [smul_smul]
    _ = t₁⁻¹ • (t₂ • (z₂ - O)) := by rw [hvec]
    _ = (t₁⁻¹ * t₂) • (z₂ - O) := by rw [smul_smul]
    _ = (t₂ / t₁) • (z₂ - O) := by
      congr 1
      ring

/-- two points of the cones from `O` over `z₁` and `z₂` with the same direction force one of
`z₁,z₂` to lie in the open segment from `O` to the other (unless they are equal) -/
private lemma mem_openSegment_or_of_smul_eq {O z₁ z₂ : V} {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Set.Ioo 0 1) (ht₂ : t₂ ∈ Set.Ioo 0 1)
    (hvec : t₁ • (z₁ - O) = t₂ • (z₂ - O)) (hne : z₁ ≠ z₂) :
    z₁ ∈ openSegment ℝ O z₂ ∨ z₂ ∈ openSegment ℝ O z₁ := by
  have ht₁p : 0 < t₁ := ht₁.1
  have ht₂p : 0 < t₂ := ht₂.1
  by_cases h : t₁ ≤ t₂
  · right
    -- z₂ - O = (t₁/t₂) • (z₁ - O); s = t₁/t₂ ∈ (0,1)
    have hdiv : z₂ - O = (t₁ / t₂) • (z₁ - O) :=
      smul_sub_eq_smul_sub_iff_div (ne_of_gt ht₂p) hvec.symm
    have hs0 : 0 < t₁ / t₂ := div_pos ht₁p ht₂p
    have hs1 : t₁ / t₂ < 1 := by
      apply (div_lt_one₀ ht₂p).mpr
      exact lt_of_le_of_ne h (by
        intro heq
        apply hne
        have hz : z₁ - O = z₂ - O := by
          calc
            z₁ - O = (t₂ / t₁) • (z₂ - O) := smul_sub_eq_smul_sub_iff_div (ne_of_gt ht₁p) hvec
            _ = (t₁ / t₁) • (z₂ - O) := by rw [heq]
            _ = z₂ - O := by rw [div_self (ne_of_gt ht₁p), one_smul]
        have hsub : z₁ - z₂ = 0 := by
          calc
            z₁ - z₂ = (z₁ - O) - (z₂ - O) := by abel
            _ = 0 := by
              rw [hz]
              abel
        exact sub_eq_zero.mp hsub)
    exact mem_openSegment_of_sub_smul ⟨hs0, hs1⟩ hdiv
  · left
    have hlt : t₂ < t₁ := lt_of_not_ge h
    have hdiv : z₁ - O = (t₂ / t₁) • (z₂ - O) := smul_sub_eq_smul_sub_iff_div (ne_of_gt ht₁p) hvec
    have hs0 : 0 < t₂ / t₁ := div_pos ht₂p ht₁p
    have hs1 : t₂ / t₁ < 1 := (div_lt_one₀ ht₁p).mpr hlt
    exact mem_openSegment_of_sub_smul ⟨hs0, hs1⟩ hdiv

/-- cones over pieces of the same facet have disjoint relative interiors -/
private lemma cone_disj_same {n : ℕ} (hnpos : 0 < n) (O : V) {P F : Set V}
    (hFexp : IsExposed ℝ P F) (hFne : F.Nonempty) (hFprop : F ≠ P)
    (hOint : O ∈ interior P)
    {v₁ v₂ : Fin n → V}
    (hSub₁ : convexHull ℝ (Set.range v₁) ⊆ F) (hSub₂ : convexHull ℝ (Set.range v₂) ⊆ F)
    (hAff₁ : AffineIndependent ℝ (snocLC n v₁ O))
    (hAff₂ : AffineIndependent ℝ (snocLC n v₂ O))
    (hSpan₁ : affineSpan ℝ (Set.range (snocLC n v₁ O)) = ⊤)
    (hSpan₂ : affineSpan ℝ (Set.range (snocLC n v₂ O)) = ⊤)
    (hRel : Disjoint (intrinsicInterior ℝ (convexHull ℝ (Set.range v₁)))
                     (intrinsicInterior ℝ (convexHull ℝ (Set.range v₂)))) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ (Set.range (snocLC n v₁ O))))
             (intrinsicInterior ℝ (convexHull ℝ (Set.range (snocLC n v₂ O)))) := by
  classical
  let x0 : V := Classical.choose hFne
  have hx0F : x0 ∈ F := Classical.choose_spec hFne
  have hOne : Classical.choose (hFexp hFne) O ≠ Classical.choose (hFexp hFne) x0 := by
    exact interior_point_not_on_exposed_level (P := P) hFexp hFne hFprop hOint hx0F
  let l : V →L[ℝ] ℝ := Classical.choose (hFexp hFne)
  rw [disjoint_left]
  intro p hp₁ hp₂
  rcases cone_int_decomp (m := n) hnpos v₁ O hAff₁ hSpan₁ hp₁ with ⟨t₁, ht₁, z₁, hz₁, heq₁⟩
  rcases cone_int_decomp (m := n) hnpos v₂ O hAff₂ hSpan₂ hp₂ with ⟨t₂, ht₂, z₂, hz₂, heq₂⟩
  have hz1F : z₁ ∈ F := hSub₁ (intrinsicInterior_subset hz₁)
  have hz2F : z₂ ∈ F := hSub₂ (intrinsicInterior_subset hz₂)
  have hc₁ : l z₁ = l x0 := exposed_func_const_on (P := P) hFexp hz1F hx0F
  have hc₂ : l z₂ = l x0 := exposed_func_const_on (P := P) hFexp hz2F hx0F
  have hv₁ : p - O = t₁ • (z₁ - O) := by rw [heq₁]; module
  have hv₂ : p - O = t₂ • (z₂ - O) := by rw [heq₂]; module
  have hvec : t₁ • (z₁ - O) = t₂ • (z₂ - O) := hv₁.symm.trans hv₂
  have hl₁ : l (p - O) = t₁ * (l z₁ - l O) := by
    calc
      l (p - O) = l (t₁ • (z₁ - O)) := by rw [hv₁]
      _ = t₁ * (l z₁ - l O) := by
        rw [map_smul]
        simp [sub_eq_add_neg]
  have hl₂ : l (p - O) = t₂ * (l z₂ - l O) := by
    calc
      l (p - O) = l (t₂ • (z₂ - O)) := by rw [hv₂]
      _ = t₂ * (l z₂ - l O) := by
        rw [map_smul]
        simp [sub_eq_add_neg]
  have hlin : t₁ * (l z₁ - l O) = t₂ * (l z₂ - l O) := hl₁.symm.trans hl₂
  have hcl : l z₁ - l O = l z₂ - l O := by rw [hc₁, hc₂]
  have ht12 : t₁ = t₂ := by
    have hd0 : l z₁ - l O ≠ 0 := by
      rw [hc₁]
      exact sub_ne_zero.mpr hOne.symm
    exact mul_left_cancel₀ hd0 (by simpa [mul_comm, hcl.symm] using hlin)
  have hzz : z₁ = z₂ := by
    have hzvec : t₁ • (z₁ - O) = t₁ • (z₂ - O) := by
      simpa [ht12] using hvec
    have ht1nz : t₁ ≠ 0 := ne_of_gt ht₁.1
    have hsmul : t₁ • ((z₁ - O) - (z₂ - O)) = 0 := by
      rw [smul_sub, hzvec, sub_self]
    have hxy : (z₁ - O) - (z₂ - O) = 0 := (smul_eq_zero.mp hsmul).resolve_left ht1nz
    have hzsub : z₁ - z₂ = 0 := by
      calc
        z₁ - z₂ = (z₁ - O) - (z₂ - O) := by abel
        _ = 0 := hxy
    exact sub_eq_zero.mp hzsub
  have hz2₁ : z₂ ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range v₁)) := by
    simpa [hzz] using hz₁
  exact (disjoint_left.mp hRel) hz2₁ hz₂

/-- cones over pieces of two different facets have disjoint relative interiors -/
private lemma cone_disj_cross {n : ℕ} (hnpos : 0 < n) {P : Set V} (hPcvx : Convex ℝ P)
    (O : V) (hOint : O ∈ interior P)
    {F₁ F₂ : Set V} (hF₁exp : IsExposed ℝ P F₁) (hF₂exp : IsExposed ℝ P F₂)
    (hF₁ne : F₁.Nonempty) (hF₂ne : F₂.Nonempty) (hF₁prop : F₁ ≠ P) (hF₂prop : F₂ ≠ P)
    (hF12 : F₁ ≠ F₂)
    {v₁ v₂ : Fin n → V}
    (hSub₁ : convexHull ℝ (Set.range v₁) ⊆ F₁) (hSub₂ : convexHull ℝ (Set.range v₂) ⊆ F₂)
    (hAff₁ : AffineIndependent ℝ (snocLC n v₁ O))
    (hAff₂ : AffineIndependent ℝ (snocLC n v₂ O))
    (hSpan₁ : affineSpan ℝ (Set.range (snocLC n v₁ O)) = ⊤)
    (hSpan₂ : affineSpan ℝ (Set.range (snocLC n v₂ O)) = ⊤)
    (hSpanBase₁ : affineSpan ℝ (Set.range v₁) = affineSpan ℝ F₁)
    (hSpanBase₂ : affineSpan ℝ (Set.range v₂) = affineSpan ℝ F₂) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ (Set.range (snocLC n v₁ O))))
             (intrinsicInterior ℝ (convexHull ℝ (Set.range (snocLC n v₂ O)))) := by
  classical
  rw [disjoint_left]
  intro p hp₁ hp₂
  rcases cone_int_decomp (m := n) hnpos v₁ O hAff₁ hSpan₁ hp₁ with ⟨t₁, ht₁, z₁, hz₁, heq₁⟩
  rcases cone_int_decomp (m := n) hnpos v₂ O hAff₂ hSpan₂ hp₂ with ⟨t₂, ht₂, z₂, hz₂, heq₂⟩
  have hz1F1 : z₁ ∈ F₁ := hSub₁ (intrinsicInterior_subset hz₁)
  have hz2F2 : z₂ ∈ F₂ := hSub₂ (intrinsicInterior_subset hz₂)
  have hz1P : z₁ ∈ P := hF₁exp.subset hz1F1
  have hz2P : z₂ ∈ P := hF₂exp.subset hz2F2
  have hv₁ : p - O = t₁ • (z₁ - O) := by rw [heq₁]; module
  have hv₂ : p - O = t₂ • (z₂ - O) := by rw [heq₂]; module
  have hvec : t₁ • (z₁ - O) = t₂ • (z₂ - O) := hv₁.symm.trans hv₂
  by_cases hzz : z₁ = z₂
  · subst z₂
    have hz1F2 : z₁ ∈ intrinsicInterior ℝ F₂ := by
      have hsub' : intrinsicInterior ℝ (convexHull ℝ (Set.range v₂)) ⊆ intrinsicInterior ℝ F₂ :=
        intrinsicInterior_mono_of_affineSpan_eq hSub₂ (by
          rw [affineSpan_convexHull (𝕜 := ℝ) (Set.range v₂)]
          exact hSpanBase₂)
      exact hsub' hz₂
    have hz1F1' : z₁ ∈ intrinsicInterior ℝ F₁ := by
      have hsub' : intrinsicInterior ℝ (convexHull ℝ (Set.range v₁)) ⊆ intrinsicInterior ℝ F₁ :=
        intrinsicInterior_mono_of_affineSpan_eq hSub₁ (by
          rw [affineSpan_convexHull (𝕜 := ℝ) (Set.range v₁)]
          exact hSpanBase₁)
      exact hsub' hz₁
    have hdisj := Commons.Geometry.Convex.Hadwiger.intrinsicInterior_disjoint_of_exposed
      (P := P) hF₁exp hF₂exp hF12
    exact (disjoint_left.mp hdisj) hz1F1' hz1F2
  · rcases mem_openSegment_or_of_smul_eq (O := O) (z₁ := z₁) (z₂ := z₂) ht₁ ht₂ hvec hzz with
      hseg₁ | hseg₂
    · have hint : z₁ ∈ interior P :=
        openSegment_interior_subset hPcvx hOint hz2P hseg₁
      exact (not_mem_interior_of_exposed hF₁exp hF₁ne hF₁prop hz1F1) hint
    · have hint : z₂ ∈ interior P :=
        openSegment_interior_subset hPcvx hOint hz1P hseg₂
      exact (not_mem_interior_of_exposed hF₂exp hF₂ne hF₂prop hz2F2) hint

/-- If every facet of a full-dimensional polytope `P` is triangulated into
`(n-1)`-simplices, then `P` itself is triangulated into `n`-simplices by
coning from an interior point. -/
private lemma fan_triangulate {n : ℕ} (hnpos : 0 < n) (u : Finset V) (P : Set V)
    (hP : P = convexHull ℝ (u : Set V)) (hint : (interior P).Nonempty)
    (hn : Module.finrank ℝ V = n)
    (facetsTri : ∀ F : Set V, F ∈ facetFinset u P →
      ∃ T : Finset V, (T : Set V) ⊆ u ∧ F = convexHull ℝ (T : Set V) ∧
        HasTriang V (n - 1) T) :
    FullClaim V n u := by
  classical
  let O : V := Classical.choose hint
  have hOint : O ∈ interior P := Classical.choose_spec hint
  let facetIdx := {F : Set V // F ∈ facetFinset u P}
  letI : Fintype facetIdx := (facetFinset u P).finite_toSet.fintype
  let mF : ℕ := Fintype.card facetIdx
  let eF : facetIdx ≃ Fin mF := Fintype.equivFin facetIdx
  let fac : Fin mF → facetIdx := eF.symm
  let facSet : Fin mF → Set V := fun a => (fac a).1
  have hfacMem : ∀ a : Fin mF, facSet a ∈ facetFinset u P := fun a => (fac a).2
  let facetT : Fin mF → Finset V := fun a => Classical.choose (facetsTri (facSet a) (hfacMem a))
  have hTriF : ∀ a : Fin mF, HasTriang V (n - 1) (facetT a) := fun a =>
    (Classical.choose_spec (facetsTri (facSet a) (hfacMem a))).2.2
  have hFcv : ∀ a : Fin mF, facSet a = convexHull ℝ ((facetT a : Finset V) : Set V) := fun a =>
    (Classical.choose_spec (facetsTri (facSet a) (hfacMem a))).2.1
  have hFexp : ∀ a : Fin mF, IsExposed ℝ P (facSet a) := fun a =>
    (facet_props u P (hfacMem a)).2.1
  have hFne : ∀ a : Fin mF, (facSet a).Nonempty := fun a =>
    (facet_props u P (hfacMem a)).1
  have hFproper : ∀ a : Fin mF, facSet a ≠ P := fun a =>
    (facet_props u P (hfacMem a)).2.2.1
  have hEq : (n - 1) + 1 = n := by omega
  let reidx : Fin ((n - 1) + 1) ≃ Fin n := Equiv.cast (congrArg Fin hEq)
  let base : (a : Fin mF) → tri_ι (hTriF a) → Fin n → V :=
    fun a j => (tri_w (hTriF a) j) ∘ reidx.symm
  let cone : (a : Fin mF) → tri_ι (hTriF a) → Fin (n + 1) → V :=
    fun a j => snocLC n (base a j) O
  let idx := Σ a : Fin mF, tri_ι (hTriF a)
  have hpiece : ∀ (a : Fin mF) (j : tri_ι (hTriF a)), tri_A (hTriF a) j ⊆ facSet a := by
    intro a j z hz
    have hz' : z ∈ convexHull ℝ ((facetT a : Finset V) : Set V) :=
      piece_subset_conv (hTriF a) j hz
    simpa [hFcv a] using hz'
  have hbase_range : ∀ (a : Fin mF) (j : tri_ι (hTriF a)),
      Set.range (base a j) = Set.range (tri_w (hTriF a) j) := by
    intro a j
    dsimp [base]
    exact range_comp_equiv reidx.symm (tri_w (hTriF a) j)
  have hσ : ∀ (a : Fin mF) (j : tri_ι (hTriF a)),
      tri_A (hTriF a) j = convexHull ℝ (Set.range (tri_w (hTriF a) j)) := fun a j =>
    (tri_props (hTriF a)).2.1 j
  have hconv_base : ∀ (a : Fin mF) (j : tri_ι (hTriF a)),
      convexHull ℝ (Set.range (base a j)) = tri_A (hTriF a) j := by
    intro a j
    rw [hbase_range a j, hσ a j]
  have hbase_aff : ∀ (a : Fin mF) (j : tri_ι (hTriF a)),
      AffineIndependent ℝ (base a j) := by
    intro a j
    dsimp [base]
    exact affineIndependent_comp_equiv reidx.symm (tri_aff (hTriF a) j)
  have hbase_memF : ∀ (a : Fin mF) (j : tri_ι (hTriF a)) (k : Fin n),
      base a j k ∈ facSet a := by
    intro a j k
    have hr : base a j k ∈ Set.range (tri_w (hTriF a) j) := by
      dsimp [base]
      exact ⟨reidx.symm k, rfl⟩
    have hc : base a j k ∈ tri_A (hTriF a) j := by
      rw [hσ a j]
      exact subset_convexHull ℝ (Set.range (tri_w (hTriF a) j)) hr
    exact hpiece a j hc
  have hOspanF : ∀ a : Fin mF, O ∉ (affineSpan ℝ (facSet a : Set V) : Set V) := by
    intro a
    exact int_not_mem_affineSpan_facet u P (hfacMem a) hOint
  have hOspan : ∀ (a : Fin mF) (j : tri_ι (hTriF a)),
      O ∉ affineSpan ℝ (Set.range (base a j)) := by
    intro a j hmem
    have hle : affineSpan ℝ (Set.range (base a j)) ≤ affineSpan ℝ (facSet a : Set V) :=
      affineSpan_mono ℝ (by rintro z ⟨k, rfl⟩; exact hbase_memF a j k)
    exact (hOspanF a) (hle hmem)
  have hcone_aff : ∀ (a : Fin mF) (j : tri_ι (hTriF a)),
      AffineIndependent ℝ (cone a j) := by
    intro a j
    dsimp [cone]
    exact affineIndependent_snocLC (base a j) (hbase_aff a j) O (hOspan a j)
  have hcone_span : ∀ (a : Fin mF) (j : tri_ι (hTriF a)),
      affineSpan ℝ (Set.range (cone a j)) = ⊤ := by
    intro a j
    exact (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one (k := ℝ)
      (p := cone a j) (hcone_aff a j)).mpr (by simp [hn])
  have hPcl : IsClosed P := by
    rw [hP]
    exact (u.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hPcvx : Convex ℝ P := by simpa [hP] using convex_convexHull ℝ (u : Set V)
  have hcone_subset_P : ∀ (a : Fin mF) (j : tri_ι (hTriF a)),
      convexHull ℝ (Set.range (cone a j)) ⊆ P := by
    intro a j
    refine convexHull_min ?_ (by simpa [hP] using convex_convexHull ℝ (u : Set V))
    rintro q ⟨k, rfl⟩
    dsimp [cone]
    cases k using Fin.lastCases with
    | last =>
        simpa using (interior_subset hOint : O ∈ P)
    | cast k0 =>
        have : base a j k0 ∈ P := by
          have hb : base a j k0 ∈ facSet a := hbase_memF a j k0
          exact (hFexp a).subset hb
        simpa using this
  have hcone_cover : P ⊆ ⋃ i : idx, convexHull ℝ (Set.range (cone i.1 i.2)) := by
    intro x hx
    have hfront : ∃ y : V, y ∈ frontier P ∧ x ∈ segment ℝ O y :=
      Commons.Geometry.Convex.Hadwiger.exists_frontier_on_segment_of_mem_interior (V := V)
        (by simpa [hn] using hnpos) hPcvx
        (by rw [hP]; exact (u.finite_toSet.isCompact_convexHull ℝ)) (hO := hOint) (hx := hx)
    rcases hfront with ⟨y, hyfront, hxseg⟩
    have hyfront' : y ∈ P \ interior P := by rwa [IsClosed.frontier_eq hPcl] at hyfront
    rcases facet_of_frontier u P hP hint (hxP := hyfront'.1) (hxint := hyfront'.2) with
      ⟨F0, hF0mem, hyF0⟩
    let a0 : Fin mF := eF ⟨F0, hF0mem⟩
    have hfac0 : facSet a0 = F0 := by
      dsimp [facSet, fac, a0]
      simpa using (Equiv.symm_apply_apply eF ⟨F0, hF0mem⟩)
    have hyF0' : y ∈ facSet a0 := by simpa [hfac0] using hyF0
    have hu : (⋃ j : tri_ι (hTriF a0), tri_A (hTriF a0) j) = facSet a0 := by
      calc
        (⋃ j : tri_ι (hTriF a0), tri_A (hTriF a0) j) =
            convexHull ℝ ((facetT a0 : Finset V) : Set V) := (tri_props (hTriF a0)).1
        _ = facSet a0 := (hFcv a0).symm
    have hyunion : y ∈ ⋃ j : tri_ι (hTriF a0), tri_A (hTriF a0) j := by
      simpa [hu] using hyF0'
    rcases Set.mem_iUnion.mp hyunion with ⟨j0, hyj0⟩
    have hybase : y ∈ convexHull ℝ (Set.range (base a0 j0)) := by
      have hyj0' : y ∈ convexHull ℝ (Set.range (tri_w (hTriF a0) j0)) := by
        rw [hσ a0 j0] at hyj0
        exact hyj0
      rwa [← hbase_range a0 j0] at hyj0'
    have hycone : y ∈ convexHull ℝ (Set.range (cone a0 j0)) := by
      have hrngcone : Set.range (cone a0 j0) = insert O (Set.range (base a0 j0)) := by
        dsimp [cone]
        exact range_snocLC (base a0 j0) O
      have hrng : Set.range (base a0 j0) ⊆ Set.range (cone a0 j0) := by
        rw [hrngcone]
        exact Set.subset_insert O (Set.range (base a0 j0))
      exact (convexHull_mono hrng) hybase
    have hoc : O ∈ convexHull ℝ (Set.range (cone a0 j0)) := by
      apply subset_convexHull ℝ (Set.range (cone a0 j0))
      dsimp [cone]
      exact ⟨Fin.last n, by simp⟩
    have hxcone : x ∈ convexHull ℝ (Set.range (cone a0 j0)) := by
      have hseg : segment ℝ O y ⊆ convexHull ℝ (Set.range (cone a0 j0)) :=
        Convex.segment_subset (convex_convexHull ℝ (Set.range (cone a0 j0))) hoc hycone
      exact hseg hxseg
    exact Set.mem_iUnion.mpr ⟨⟨a0, j0⟩, hxcone⟩
  have hall_subset : (⋃ i : idx, convexHull ℝ (Set.range (cone i.1 i.2))) ⊆ P := by
    exact Set.iUnion_subset (fun i => hcone_subset_P i.1 i.2)
  have hunion : (⋃ i : idx, convexHull ℝ (Set.range (cone i.1 i.2))) = P :=
    Set.Subset.antisymm hall_subset hcone_cover
  have hdisj : ∀ i j : idx, i ≠ j →
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (Set.range (cone i.1 i.2))))
        (intrinsicInterior ℝ (convexHull ℝ (Set.range (cone j.1 j.2)))) := by
    rintro ⟨a1, j1⟩ ⟨a2, j2⟩ hij
    by_cases ha : a1 = a2
    · subst a2
      have hj : j1 ≠ j2 := by
        intro hjj
        apply hij
        rw [hjj]
      have hSub₁ : convexHull ℝ (Set.range (base a1 j1)) ⊆ facSet a1 := by
        intro z hz
        rw [hconv_base a1 j1] at hz
        exact hpiece a1 j1 hz
      have hSub₂ : convexHull ℝ (Set.range (base a1 j2)) ⊆ facSet a1 := by
        intro z hz
        rw [hconv_base a1 j2] at hz
        exact hpiece a1 j2 hz
      have hRel : Disjoint (intrinsicInterior ℝ (convexHull ℝ (Set.range (base a1 j1))))
          (intrinsicInterior ℝ (convexHull ℝ (Set.range (base a1 j2)))) := by
        simpa [hconv_base a1 j1, hconv_base a1 j2] using (tri_disj (hTriF a1) j1 j2 hj)
      simpa [cone] using
        (cone_disj_same (n := n) hnpos O (hFexp a1) (hFne a1) (hFproper a1) hOint
          hSub₁ hSub₂ (hcone_aff a1 j1) (hcone_aff a1 j2)
          (by simpa [cone] using hcone_span a1 j1) (by simpa [cone] using hcone_span a1 j2)
          hRel)
    · have hFacNe : facSet a1 ≠ facSet a2 := by
        intro hEq
        apply ha
        have h₁ : (eF.symm a1).1 = (eF.symm a2).1 := by simpa [facSet, fac] using hEq
        have h₂ : eF.symm a1 = eF.symm a2 := Subtype.ext h₁
        exact (Equiv.injective (eF.symm)) h₂
      have hSub₁ : convexHull ℝ (Set.range (base a1 j1)) ⊆ facSet a1 := by
        intro z hz
        rw [hconv_base a1 j1] at hz
        exact hpiece a1 j1 hz
      have hSub₂ : convexHull ℝ (Set.range (base a2 j2)) ⊆ facSet a2 := by
        intro z hz
        rw [hconv_base a2 j2] at hz
        exact hpiece a2 j2 hz
      have hSpanBase₁ : affineSpan ℝ (Set.range (base a1 j1)) =
          affineSpan ℝ (facSet a1 : Set V) := by
        exact affineSpan_range_eq_affineSpan_facet hnpos u P (hfacMem a1) hn (hbase_aff a1 j1)
          (by intro k; exact hbase_memF a1 j1 k)
      have hSpanBase₂ : affineSpan ℝ (Set.range (base a2 j2)) =
          affineSpan ℝ (facSet a2 : Set V) := by
        exact affineSpan_range_eq_affineSpan_facet hnpos u P (hfacMem a2) hn (hbase_aff a2 j2)
          (by intro k; exact hbase_memF a2 j2 k)
      simpa [cone] using
        (cone_disj_cross (n := n) hnpos hPcvx O hOint
          (hFexp a1) (hFexp a2) (hFne a1) (hFne a2) (hFproper a1) (hFproper a2) hFacNe
          hSub₁ hSub₂ (hcone_aff a1 j1) (hcone_aff a2 j2)
          (by simpa [cone] using hcone_span a1 j1) (by simpa [cone] using hcone_span a2 j2)
          hSpanBase₁ hSpanBase₂)
  change HasTriang V n u
  refine ⟨idx, ?_, (fun i => convexHull ℝ (Set.range (cone i.1 i.2))), (fun i => cone i.1 i.2), ?_, ?_, ?_, ?_⟩
  · haveI : ∀ a : Fin mF, Fintype (tri_ι (hTriF a)) := fun a => tri_fintype (hTriF a)
    infer_instance
  · simpa [hP] using hunion
  · intro i
    rfl
  · intro i
    exact hcone_aff i.1 i.2
  · exact hdisj


/-! ## the full-dimensional triangulation theorem -/

/-- in dimension zero the only polytope is a point -/
private lemma full_dim_zero (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (hfin : Module.finrank ℝ V = 0) (uu : Finset V) (hu : uu.Nonempty)
    (hspan : affineSpan ℝ (uu : Set V) = ⊤) : FullClaim V 0 uu := by
  classical
  rcases hu with ⟨p0, hp0⟩
  have hu' : uu.Nonempty := ⟨p0, hp0⟩
  have hdim0 : Module.finrank ℝ (affineSpan ℝ (uu : Set V)).direction = 0 := by
    rw [hspan]
    rw [AffineSubspace.direction_top]
    rw [finrank_top]
    exact hfin
  have hall_eq : ∀ s ∈ uu, ∀ t ∈ uu, s = t := eq_of_finrank_direction_zero (S := uu) hu' hdim0
  have hset : (uu : Set V) = {p0} := by
    ext x
    constructor
    · intro hx
      have : x = p0 := hall_eq x hx p0 hp0
      simpa [this]
    · intro hx
      rw [show x = p0 by simpa using hx]
      exact hp0
  let w : PUnit → Fin (0 + 1) → V := fun _ _ => p0
  let A : PUnit → Set V := fun _ => ({p0} : Set V)
  change HasTriang V 0 uu
  refine ⟨PUnit, inferInstance, A, w, ?_, ?_, ?_, ?_⟩
  · calc
      (⋃ _ : PUnit, A ()) = ({p0} : Set V) := by simp [A]
      _ = convexHull ℝ (uu : Set V) := by rw [hset]; simp
  · intro i
    calc
      A i = ({p0} : Set V) := by simp [A]
      _ = convexHull ℝ (Set.range (w i)) := by
        have hr : Set.range (w i) = ({p0} : Set V) := by
          ext y
          constructor
          · rintro ⟨k, rfl⟩
            simp [w]
          · intro hy
            subst y
            exact ⟨Fin.last 0, by simp [w]⟩
        rw [hr]
        simp
  · intro i
    haveI : Subsingleton (Fin (0 + 1)) := ⟨by intro a b; apply Fin.ext; simp⟩
    exact affineIndependent_of_subsingleton (k := ℝ) (p := w i)
  · intro i j hij
    exfalso
    exact hij (Subsingleton.elim i j)

/-- membership in an affine subspace is equivalent to the difference with a base point
lying in its direction -/
private lemma mem_affineSpan_iff_vsub_mem_direction {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {A : AffineSubspace ℝ V} {p0 z : V} (hp0 : p0 ∈ A) :
    z ∈ A ↔ z - p0 ∈ A.direction := by
  rw [← vsub_eq_sub]
  exact (AffineSubspace.vsub_right_mem_direction_iff_mem hp0 z).symm

/-- relative triangulation from the full-dimensional theorem: move the affine hull to a
linear subspace and translate back -/
private lemma rel_from_full {n : ℕ} {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (hfull : ∀ (V' : Type u) [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
        [FiniteDimensional ℝ V'], Module.finrank ℝ V' = n → ∀ uu : Finset V', uu.Nonempty →
        (affineSpan ℝ (uu : Set V') = ⊤) → HasTriang V' n uu)
    (S : Finset V) (hS : S.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ (S : Set V)).direction = n) : HasTriang V n S := by
  classical
  rcases hS with ⟨p0, hp0S⟩
  let W : Submodule ℝ V := (affineSpan ℝ (S : Set V)).direction
  let fS : {x : V // x ∈ S} → W := fun x =>
    ⟨(x : V) - p0, mem_direction_sub_of_mem_finset S p0 hp0S x.2⟩
  let S' : Finset W := S.attach.image fS
  have hS'ne : S'.Nonempty := by
    refine ⟨fS ⟨p0, hp0S⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨p0, hp0S⟩, by simp, rfl⟩
  have hdimW : Module.finrank ℝ W = n := by
    simpa [W] using hdim
  let φ : W →ᵃⁱ[ℝ] V :=
    (AffineIsometryEquiv.constVAdd (𝕜 := ℝ) (P := V) p0).toAffineIsometry.comp
      W.subtypeₗᵢ.toAffineIsometry
  have hφinj : Function.Injective (⇑φ.toAffineMap) := by
    simpa using φ.injective
  have hφ_apply : ∀ w : W, φ w = (w : V) + p0 := by
    intro w
    have h : p0 + (w : V) = (w : V) + p0 := by abel
    simpa [φ, AffineIsometryEquiv.coe_constVAdd, AffineIsometryEquiv.coe_toAffineIsometry,
      LinearIsometry.coe_toAffineIsometry] using h
  have hφ_fS : ∀ x : {x : V // x ∈ S}, φ (fS x) = (x : V) := by
    intro x
    have h : p0 + ((x : V) - p0) = (x : V) := by abel
    simpa [φ, fS, AffineIsometryEquiv.coe_constVAdd,
      AffineIsometryEquiv.coe_toAffineIsometry, LinearIsometry.coe_toAffineIsometry] using h
  have himg_set : φ '' (S' : Set W) = (S : Set V) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwS : w ∈ S' := by simpa using hw
      rw [Finset.mem_image] at hwS
      rcases hwS with ⟨x, hx, hfxw⟩
      have hφx : φ w = (x : V) := by
        rw [← hfxw]
        exact hφ_fS x
      rw [hφx]
      exact x.2
    · intro hz
      have hdir : z - p0 ∈ W := mem_direction_sub_of_mem_finset S p0 hp0S hz
      refine ⟨(fS ⟨z, hz⟩ : W), ?_, ?_⟩
      · change fS ⟨z, hz⟩ ∈ S'
        rw [Finset.mem_image]
        refine ⟨⟨z, hz⟩, ?_, rfl⟩
        simp
      · exact hφ_fS ⟨z, hz⟩
  have hspanW : affineSpan ℝ (S' : Set W) = ⊤ := by
    let A : AffineSubspace ℝ V := affineSpan ℝ (S : Set V)
    have hA0 : p0 ∈ A := subset_affineSpan ℝ (S : Set V) hp0S
    have hmap1 : (affineSpan ℝ (S' : Set W)).map φ.toAffineMap = A := by
      calc
        (affineSpan ℝ (S' : Set W)).map φ.toAffineMap = affineSpan ℝ (φ '' (S' : Set W)) := by
          exact AffineSubspace.map_span φ.toAffineMap (S' : Set W)
        _ = affineSpan ℝ (S : Set V) := by rw [himg_set]
    have hmap2 : (⊤ : AffineSubspace ℝ W).map φ.toAffineMap = A := by
      apply AffineSubspace.ext
      intro z
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hzdir : (φ w) - p0 ∈ W := by
          rw [hφ_apply]
          change (w : V) + p0 - p0 ∈ W
          simpa using (show (w : V) ∈ W from w.2)
        exact (mem_affineSpan_iff_vsub_mem_direction (A := A) hA0).mpr (by simpa [W] using hzdir)
      · intro hz
        have hdir : z - p0 ∈ A.direction :=
          (mem_affineSpan_iff_vsub_mem_direction (A := A) hA0).mp hz
        let w0 : W := ⟨z - p0, (by simpa [W] using hdir)⟩
        refine ⟨w0, ?_, ?_⟩
        · trivial
        · rw [AffineIsometry.coe_toAffineMap]
          rw [hφ_apply]
          simp [w0]
    have heq : (affineSpan ℝ (S' : Set W)).map φ.toAffineMap =
        (⊤ : AffineSubspace ℝ W).map φ.toAffineMap := by
      rw [hmap1, hmap2]
    calc
      affineSpan ℝ (S' : Set W) = ((affineSpan ℝ (S' : Set W)).map φ.toAffineMap).comap φ.toAffineMap := by
        exact (AffineSubspace.comap_map_eq_of_injective hφinj _).symm
      _ = ((⊤ : AffineSubspace ℝ W).map φ.toAffineMap).comap φ.toAffineMap := by rw [heq]
      _ = ⊤ := AffineSubspace.comap_map_eq_of_injective hφinj ⊤
  have htri' : HasTriang W n S' := hfull (V' := W) hdimW S' hS'ne hspanW
  have htri'' : HasTriang V n (S'.image fun x : W => φ x) := by
    exact tri_transport (V₂ := W) (V := V) φ n S' htri'
  have himg : (S'.image fun x : W => φ x) = S := by
    apply Finset.ext
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwS : w ∈ S' := by simpa using hw
      have hφw : φ w ∈ (S : Set V) := by
        rw [← himg_set]
        exact ⟨w, hwS, rfl⟩
      simpa using hφw
    · intro hy
      have hmem : (fS ⟨y, hy⟩ : W) ∈ S' := by
        rw [Finset.mem_image]
        refine ⟨⟨y, hy⟩, ?_, rfl⟩
        simp
      refine ⟨(fS ⟨y, hy⟩ : W), hmem, ?_⟩
      exact hφ_fS ⟨y, hy⟩
  simpa [himg] using htri''

/-- full-dimensional triangulation from the relative statement one dimension lower -/
private lemma full_dim_of_rel {n : ℕ} {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (hrel : ∀ (V' : Type u) [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
        [FiniteDimensional ℝ V'], ∀ S : Finset V', S.Nonempty →
        Module.finrank ℝ (affineSpan ℝ (S : Set V')).direction = n → HasTriang V' n S)
    (hfin : Module.finrank ℝ V = n + 1) (uu : Finset V) (hu : uu.Nonempty)
    (hspan : affineSpan ℝ (uu : Set V) = ⊤) : FullClaim V (n + 1) uu := by
  classical
  let P : Set V := convexHull ℝ (uu : Set V)
  have hspanP : affineSpan ℝ (P : Set V) = ⊤ := by
    dsimp [P]
    rw [affineSpan_convexHull (𝕜 := ℝ) (uu : Set V)]
    exact hspan
  have hint : (interior P).Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top (convex_convexHull ℝ (uu : Set V))).mpr hspanP
  have hfacetsTri : ∀ F : Set V, F ∈ facetFinset uu P →
      ∃ T : Finset V, (T : Set V) ⊆ uu ∧ F = convexHull ℝ (T : Set V) ∧
        HasTriang V ((n + 1) - 1) T := by
    intro F hFmem
    let T : Finset V := uu.filter (fun y : V => y ∈ F)
    have hT : (T : Set V) = F ∩ (uu : Set V) := by
      ext y
      simp [T]
      constructor <;> intro hy <;> exact ⟨hy.2, hy.1⟩
    refine ⟨T, ?_, ?_, ?_⟩
    · exact Finset.filter_subset (fun y : V => y ∈ F) uu
    · calc
        F = convexHull ℝ (F ∩ (uu : Set V)) := by
          exact facet_eq_convexHull uu P (by dsimp [P]) (hF := hFmem)
        _ = convexHull ℝ (T : Set V) := by rw [hT]
    · have hFcv : F = convexHull ℝ (T : Set V) := by
        calc
          F = convexHull ℝ (F ∩ (uu : Set V)) := by
            exact facet_eq_convexHull uu P (by dsimp [P]) (hF := hFmem)
          _ = convexHull ℝ (T : Set V) := by rw [hT]
      have hTne : T.Nonempty := by
        have hFne : F.Nonempty := (facet_props uu P hFmem).1
        by_contra hTempty
        have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTempty
        have hFempty : F = (∅ : Set V) := by
          calc
            F = convexHull ℝ (T : Set V) := hFcv
            _ = (∅ : Set V) := by rw [hTe]; simp
        exact (by simpa [hFempty] : ¬ F.Nonempty) hFne
      have hdimT : Module.finrank ℝ (affineSpan ℝ (T : Set V)).direction = n := by
        have hd := finrank_direction_facet uu P (by dsimp [P]) (hF := hFmem)
        have hd' : Module.finrank ℝ (affineSpan ℝ (F ∩ (uu : Set V))).direction = n := by
          simpa [hfin] using hd
        rwa [← hT] at hd'
      exact hrel (V' := V) T hTne hdimT
  exact fan_triangulate (n := n + 1) (by omega) uu P (by dsimp [P]) hint hfin hfacetsTri

/-- mutual recursion: the full-dimensional statement and the relative statement -/
private theorem full_and_rel : ∀ n : ℕ,
    (∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
      Module.finrank ℝ V = n → ∀ uu : Finset V, uu.Nonempty →
        (affineSpan ℝ (uu : Set V) = ⊤) → FullClaim V n uu) ∧
    (∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
      ∀ S : Finset V, S.Nonempty →
        Module.finrank ℝ (affineSpan ℝ (S : Set V)).direction = n → HasTriang V n S) := by
  classical
  intro n
  induction n with
  | zero =>
      constructor
      · intro V _ _ _ hfin uu hu hspan
        exact full_dim_zero V hfin uu hu hspan
      · intro V _ _ _ S hS hdim
        exact rel_from_full (V := V)
          (fun V' _ _ _ hfin' uu' hu' hspan' => full_dim_zero V' hfin' uu' hu' hspan') S hS hdim
  | succ n ih =>
      have hP1 : ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
          [FiniteDimensional ℝ V], Module.finrank ℝ V = n + 1 → ∀ uu : Finset V, uu.Nonempty →
          (affineSpan ℝ (uu : Set V) = ⊤) → FullClaim V (n + 1) uu := by
        intro V _ _ _ hfin uu hu hspan
        exact full_dim_of_rel (n := n) (V := V) ih.2 hfin uu hu hspan
      constructor
      · intro V _ _ _ hfin uu hu hspan
        exact hP1 V hfin uu hu hspan
      · intro V _ _ _ S hS hdim
        exact rel_from_full (n := n + 1) (V := V) hP1 S hS hdim

/-! ## the relative (requested) statement -/

theorem convexHull_triangulation_rel_v2 {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Finset V) (hS : S.Nonempty) :
    let d : ℕ := Module.finrank ℝ (affineSpan ℝ (S : Set V)).direction
    ∃ (ι : Type) (_ : Fintype ι), ∃ A : ι → Set V,
      ∃ w : ι → Fin (d + 1) → V,
        (⋃ i : ι, A i = convexHull ℝ (S : Set V)) ∧
        (∀ i : ι, A i = convexHull ℝ (Set.range (w i))) ∧
        (∀ i : ι, AffineIndependent ℝ (w i)) ∧
        (∀ i j : ι, i ≠ j →
          Disjoint (intrinsicInterior ℝ (A i)) (intrinsicInterior ℝ (A j))) := by
  classical
  let d : ℕ := Module.finrank ℝ (affineSpan ℝ (S : Set V)).direction
  change HasTriang V d S
  exact (full_and_rel d).2 V S hS rfl

end Commons.Geometry.Convex.Hadwiger
