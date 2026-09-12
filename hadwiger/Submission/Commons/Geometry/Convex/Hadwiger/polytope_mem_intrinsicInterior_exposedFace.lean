import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

open scoped BigOperators
open Set

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V]

/-- The exposed face of `P` in the direction `n`: the set of maximizers of `⟪n, ·⟫` over `P`. -/
def topFace (n : V) (P : Set V) : Set V :=
  {x ∈ P | ∀ y ∈ P, inner ℝ n y ≤ inner ℝ n x}

lemma mem_topFace_iff {n : V} {P : Set V} {x : V} :
    x ∈ topFace n P ↔ x ∈ P ∧ ∀ y ∈ P, inner ℝ n y ≤ inner ℝ n x := Iff.rfl

lemma mem_topFace_of_forall_le {n : V} {P : Set V} {x : V} (hxP : x ∈ P)
    (h : ∀ y ∈ P, inner ℝ n y ≤ inner ℝ n x) : x ∈ topFace n P := ⟨hxP, h⟩

lemma topFace_subset {n : V} {P : Set V} : topFace n P ⊆ P := fun x hx => hx.1

lemma topFace_le_of_mem {n : V} {P : Set V} {x y : V} (hx : x ∈ topFace n P) (hy : y ∈ P) :
    inner ℝ n y ≤ inner ℝ n x := hx.2 y hy

-- if q ∈ P maximizes ⟪n,·⟫ then the top face in direction n is the level set
lemma topFace_eq_level {n q : V} {P : Set V} (hqP : q ∈ P)
    (hmax : ∀ y ∈ P, inner ℝ n y ≤ inner ℝ n q) :
    topFace n P = {x ∈ P | inner ℝ n x = inner ℝ n q} := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    apply le_antisymm
    · exact hmax x hx.1
    · exact hx.2 q hqP
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro y hy
    calc
      inner ℝ n y ≤ inner ℝ n q := hmax y hy
      _ = inner ℝ n x := hx.2.symm

-- the level hyperplane {x | ⟪n,x⟫ = c} has empty interior for n ≠ 0
lemma interior_level_empty_of_ne_zero {n q : V} (hn : n ≠ 0) :
    interior {x : V | inner ℝ n x = inner ℝ n q} = ∅ := by
  let f : V →L[ℝ] ℝ := InnerProductSpace.toDual ℝ V n
  have hneq : f ≠ 0 := by
    intro hz
    apply hn
    have h := congrArg (InnerProductSpace.toDual ℝ V).symm hz
    simpa [f] using h
  have hsurj : Function.Surjective f := by
    intro t
    have hne : ∃ x, f x ≠ 0 := by
      by_contra hc
      apply hneq
      ext x
      by_contra hx
      exact hc ⟨x, hx⟩
    rcases hne with ⟨x0, hx0⟩
    refine ⟨(t / f x0) • x0, ?_⟩
    calc
      f ((t / f x0) • x0) = (t / f x0) • f x0 := by simp
      _ = (t / f x0) * f x0 := rfl
      _ = t := by field_simp [hx0]
  have hpre : {x : V | inner ℝ n x = inner ℝ n q} = f ⁻¹' ({inner ℝ n q} : Set ℝ) := by
    ext x
    simp [f, InnerProductSpace.toDual_apply_apply]
  rw [hpre]
  rw [ContinuousLinearMap.interior_preimage f hsurj ({inner ℝ n q} : Set ℝ)]
  simp

lemma isExposed_topFace (n : V) (P : Set V) : IsExposed ℝ P (topFace n P) := by
  classical
  let l : StrongDual ℝ V := InnerProductSpace.toDual ℝ V n
  have hset : ContinuousLinearMap.toExposed l P = topFace n P := by
    ext x
    constructor
    · rintro ⟨hxP, hx⟩
      refine ⟨hxP, ?_⟩
      intro y hy
      have hly : l y = inner ℝ n y := by
        simpa [l] using (InnerProductSpace.toDual_apply_apply (𝕜 := ℝ) (E := V) (x := n) (y := y))
      have hlx : l x = inner ℝ n x := by
        simpa [l] using (InnerProductSpace.toDual_apply_apply (𝕜 := ℝ) (E := V) (x := n) (y := x))
      simpa [hly, hlx] using hx y hy
    · rintro ⟨hxP, hx⟩
      refine ⟨hxP, ?_⟩
      intro y hy
      have hly : l y = inner ℝ n y := by
        simpa [l] using (InnerProductSpace.toDual_apply_apply (𝕜 := ℝ) (E := V) (x := n) (y := y))
      have hlx : l x = inner ℝ n x := by
        simpa [l] using (InnerProductSpace.toDual_apply_apply (𝕜 := ℝ) (E := V) (x := n) (y := x))
      simpa [hly, hlx] using hx y hy
  rw [← hset]
  exact ContinuousLinearMap.toExposed.isExposed


lemma topFace_convex {n : V} {P : Set V} (hP : Convex ℝ P) : Convex ℝ (topFace n P) := by
  exact (isExposed_topFace n P).convex hP

/-- A nonempty exposed face of the convex hull of a finite set is the convex hull of the
generators it contains (generic version of `polytope_exposedFace_conv_vertices`). -/
theorem exposedFace_conv_vertices_generic
    (u : Finset V) (P : Set V) (hP : P = convexHull ℝ (u : Set V)) {F : Set V}
    (hF : IsExposed ℝ P F) (hFne : F.Nonempty) :
    F = convexHull ℝ (F ∩ (u : Set V)) := by
  classical
  obtain ⟨l, hl⟩ := hF hFne
  have hPconv : Convex ℝ P := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set V)
  have hFconv : Convex ℝ F := hF.convex hPconv
  have huP : (u : Set V) ⊆ P := by
    rw [hP]
    exact subset_convexHull ℝ (u : Set V)
  apply Set.Subset.antisymm
  · intro x hxF
    have hxF' : x ∈ {x' ∈ P | ∀ y ∈ P, l y ≤ l x'} := by
      rw [hl] at hxF
      exact hxF
    have hxmax : ∀ y ∈ P, l y ≤ l x := hxF'.2
    have hxCH : x ∈ convexHull ℝ (u : Set V) := by
      simpa [hP] using hxF'.1
    rw [Finset.mem_convexHull'] at hxCH
    rcases hxCH with ⟨w, hw0, hw1, hwx⟩
    have hle : ∀ z ∈ u, l z ≤ l x := by
      intro z hz
      exact hxmax z (huP hz)
    have hsecond : (∑ z ∈ u, w z * l z) = l x := by
      calc
        (∑ z ∈ u, w z * l z) = (∑ z ∈ u, w z • l z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          simp
        _ = l (∑ z ∈ u, w z • z) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro z hz
          exact (map_smul l (w z) z).symm
        _ = l x := by rw [hwx]
    have hsum : (∑ z ∈ u, w z * (l x - l z)) = 0 := by
      calc
        (∑ z ∈ u, w z * (l x - l z)) = (∑ z ∈ u, (w z * l x - w z * l z)) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          ring
        _ = (∑ z ∈ u, w z * l x) - (∑ z ∈ u, w z * l z) := by
          rw [Finset.sum_sub_distrib]
        _ = l x - (∑ z ∈ u, w z * l z) := by
          rw [← Finset.sum_mul]
          rw [hw1]
          ring
        _ = l x - l x := by rw [hsecond]
        _ = 0 := by ring
    have hterm_nonneg : ∀ z ∈ u, 0 ≤ w z * (l x - l z) := by
      intro z hz
      exact mul_nonneg (hw0 z hz) (sub_nonneg.mpr (hle z hz))
    have hterm : ∀ z ∈ u, w z * (l x - l z) = 0 := by
      intro z hz
      exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hsum z hz
    have hmax_eq : ∀ z ∈ u, w z ≠ 0 → l z = l x := by
      intro z hz hwz
      have h : l x - l z = 0 := (mul_eq_zero.mp (hterm z hz)).resolve_left hwz
      exact (sub_eq_zero.mp h).symm
    have hw_of_out : ∀ z ∈ u, z ∉ F → w z = 0 := by
      intro z hz hzF
      by_contra hwz
      apply hzF
      rw [hl]
      have hlz : l z = l x := hmax_eq z hz hwz
      have hzP : z ∈ P := huP hz
      exact ⟨hzP, fun y hy => by simpa [hlz] using hxmax y hy⟩
    let v : Finset V := u.filter (fun z => z ∈ F)
    have hvsub : v ⊆ u := Finset.filter_subset _ u
    have hw0v : ∀ z ∈ v, 0 ≤ w z := by
      intro z hz
      exact hw0 z (hvsub hz)
    have hw_out_v : ∀ z ∈ u, z ∉ v → w z = 0 := by
      intro z hz hzv
      exact hw_of_out z hz (by
        intro hzF
        apply hzv
        simpa [v] using ⟨hz, hzF⟩)
    have hsumv : (∑ z ∈ v, w z) = 1 := by
      calc
        (∑ z ∈ v, w z) = (∑ z ∈ u, w z) := Finset.sum_subset hvsub hw_out_v
        _ = 1 := hw1
    have hsumx : (∑ z ∈ v, w z • z) = x := by
      calc
        (∑ z ∈ v, w z • z) = (∑ z ∈ u, w z • z) := by
          refine Finset.sum_subset hvsub ?_
          intro z hz hzv
          simp [hw_out_v z hz hzv]
        _ = x := hwx
    have hxCHv : x ∈ convexHull ℝ (v : Set V) := by
      exact (Finset.mem_convexHull' (s := v) (x := x)).2 ⟨w, hw0v, hsumv, hsumx⟩
    have hv_eq : (v : Set V) = F ∩ (u : Set V) := by
      ext z
      simp [v]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hv_eq] at hxCHv
    exact hxCHv
  · exact convexHull_min (inter_subset_left : F ∩ (u : Set V) ⊆ F) hFconv

/-- generic supporting-functional theorem at a non-interior point of a convex set in a
finite-dimensional Euclidean space -/
theorem exists_supporting_functional_at_frontier_generic
    {P : Set V} (hPconv : Convex ℝ P)
    (hPint : (interior P).Nonempty) {q : V}
    (hqP : q ∈ P) (hqnot : q ∉ interior P) :
    ∃ n : V, n ≠ 0 ∧
      ∀ x ∈ P, inner ℝ n x ≤ inner ℝ n q := by
  classical
  rcases geometric_hahn_banach_of_nonempty_interior_point (E := V) hPconv hqnot hPint with
    ⟨f, hfne, hfmax⟩
  let n : V := (InnerProductSpace.toDual ℝ V).symm f
  have hn_ne : n ≠ 0 := by
    intro hn0
    apply hfne
    have h := congrArg (InnerProductSpace.toDual ℝ V) hn0
    simpa [n] using h
  refine ⟨n, hn_ne, ?_⟩
  intro x hx
  have hx1 : inner ℝ n x = f x := by
    change inner ℝ ((InnerProductSpace.toDual ℝ V).symm f) x = f x
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := x) (y := f)
  have hq1 : inner ℝ n q = f q := by
    change inner ℝ ((InnerProductSpace.toDual ℝ V).symm f) q = f q
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := q) (y := f)
  rw [hx1, hq1]
  exact hfmax x hx

/-- A point of the intrinsic interior of a full-dimensional convex set is an interior point. -/
lemma mem_interior_of_mem_intrinsicInterior {P : Set V} (hPcvx : Convex ℝ P)
    (hPint : (interior P).Nonempty)
    {q : V} (hq : q ∈ intrinsicInterior ℝ P) : q ∈ interior P := by
  classical
  have hspan : affineSpan ℝ P = ⊤ := (Convex.interior_nonempty_iff_affineSpan_eq_top hPcvx).mp hPint
  let s := affineSpan ℝ P
  haveI : Nonempty s := by
    rcases hPint with ⟨p, hp⟩
    have hpP : p ∈ P := interior_subset hp
    exact ⟨⟨p, subset_affineSpan ℝ P hpP⟩⟩
  rcases mem_intrinsicInterior.mp hq with ⟨y, hy, hyq⟩
  let sA : Set s := ((↑) : s → V) ⁻¹' P
  have hy' : y ∈ interior sA := by simpa [sA] using hy
  let φ : s →ᵃ[ℝ] V := s.subtype
  have hcar : ((affineSpan ℝ P : AffineSubspace ℝ V) : Set V) = univ := by
    rw [hspan]
    simp
  have hφsurj : Function.Surjective φ := by
    intro v
    have hv : v ∈ (s : Set V) := by
      change v ∈ ((affineSpan ℝ P : AffineSubspace ℝ V) : Set V)
      rw [hcar]
      trivial
    refine ⟨⟨v, hv⟩, rfl⟩
  have hφcont : Continuous φ := by
    change Continuous (fun z : s => (z : V))
    continuity
  have hopen : IsOpenMap φ := AffineMap.isOpenMap φ hφcont hφsurj
  have hφopen : IsOpen (φ '' interior sA) := hopen (interior sA) isOpen_interior
  have hmem : q ∈ φ '' interior sA := by
    refine ⟨y, hy', ?_⟩
    exact hyq
  refine mem_interior.mpr ⟨φ '' interior sA, ?_, hφopen, hmem⟩
  intro z hz
  rcases hz with ⟨z', hz', rfl⟩
  have hzP : (z' : V) ∈ P := by
    simpa [sA] using (interior_subset hz')
  exact hzP


/-- Supporting functional at an intrinsic-frontier point of a convex set, proper. -/
lemma exists_proper_support_at_intrinsicFrontier {P : Set V} (hPcvx : Convex ℝ P)
    {q : V} (hqP : q ∈ P) (hqnot : q ∉ intrinsicInterior ℝ P) :
    ∃ n : V, n ≠ 0 ∧ (∀ y ∈ P, inner ℝ n y ≤ inner ℝ n q) ∧ ∃ y ∈ P, inner ℝ n y < inner ℝ n q := by
  classical
  let S0 : Set V := {x | x + q ∈ P}
  let W : Submodule ℝ V := Submodule.span ℝ S0
  let P' : Set W := ((↑) : W → V) ⁻¹' S0
  let φ : W →ᵃⁱ[ℝ] V := {
    toAffineMap := {
      toFun := fun w : W => q + (w : V)
      linear := W.subtype
      map_vadd' := by
        intro x v
        simp [add_assoc, add_comm, add_left_comm]
    }
    norm_map := by
      intro x
      simp
  }
  have hS0cvx : Convex ℝ S0 := by
    let f : V →ᵃ[ℝ] V := {
      toFun := fun x : V => x + q
      linear := LinearMap.id
      map_vadd' := by
        intro x v
        simp [add_assoc, add_comm, add_left_comm]
    }
    have hpre : f ⁻¹' P = S0 := by
      ext x
      rfl
    rw [← hpre]
    exact hPcvx.affine_preimage f
  have hqS0 : (0 : V) ∈ S0 := by
    dsimp [S0]
    simpa using hqP
  have hS0W : S0 ⊆ (W : Set V) := by
    exact Submodule.subset_span (R := ℝ) (s := S0)
  have hP'cvx : Convex ℝ P' := by
    -- P' = (↑) ⁻¹' S0, preimage of a convex set under a linear map
    exact hS0cvx.affine_preimage (W.subtype.toAffineMap)
  have hzeroP' : (0 : W) ∈ P' := by
    dsimp [P']
    exact hqS0
  have hφP' : φ '' P' = P := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwS : (w : V) ∈ S0 := by simpa [P'] using hw
      dsimp [S0] at hwS
      change q + (w : V) ∈ P
      simpa [add_comm] using hwS
    · intro hz
      refine ⟨⟨z - q, hS0W ?_⟩, ?_, ?_⟩
      · dsimp [S0]
        have hcalc : (z - q) + q = z := by abel
        simpa [hcalc] using hz
      · dsimp [P']
        dsimp [S0]
        have hcalc : (z - q) + q = z := by abel
        simpa [hcalc] using hz
      · change q + (z - q) = z
        abel
  have hzero_not_intII : (0 : W) ∉ intrinsicInterior ℝ P' := by
    intro hz
    apply hqnot
    have hII : intrinsicInterior ℝ (φ '' P') = φ '' intrinsicInterior ℝ P' := by
      exact AffineIsometry.intrinsicInterior_image φ P'
    have hqII : q ∈ intrinsicInterior ℝ (φ '' P') := by
      rw [hII]
      refine ⟨(0 : W), hz, ?_⟩
      change (fun w : W => q + (w : V)) 0 = q
      simp
    simpa [hφP'] using hqII
  have hzero_not_int : (0 : W) ∉ interior P' := by
    intro hz
    exact hzero_not_intII (interior_subset_intrinsicInterior hz)
  -- P' is full-dimensional in W, so its interior in W is nonempty
  have hP'int : (interior P').Nonempty := by
    have himg : (↑) '' P' = S0 := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hx
        refine ⟨⟨x, hS0W hx⟩, ?_, rfl⟩
        simpa [P'] using hx
    have hmap : Submodule.map W.subtype (Submodule.span ℝ (P' : Set W)) = W := by
      rw [Submodule.map_span]
      change Submodule.span ℝ (Subtype.val '' P') = W
      rw [himg]
    have hspanP' : Submodule.span ℝ (P' : Set W) = ⊤ := by
      have h2 : Submodule.map W.subtype (⊤ : Submodule ℝ W) = W := by
        rw [Submodule.map_top, Submodule.range_subtype]
      have hinj : Function.Injective W.subtype := by
        intro x y hxy
        exact Subtype.ext hxy
      exact (Submodule.map_injective_of_injective hinj) (by simpa [h2, hmap])
    have haff : affineSpan ℝ (P' : Set W) = ⊤ := by
      have h0 : (0 : W) ∈ P' := hzeroP'
      have hcar : (affineSpan ℝ (P' : Set W) : Set W) = univ := by
        have hins : insert (0 : W) (P' : Set W) = P' := by
          ext x
          simp [h0]
        rw [← hins]
        rw [affineSpan_insert_zero]
        rw [hspanP']
        simp
      ext x
      change x ∈ (affineSpan ℝ (P' : Set W) : Set W) ↔
        x ∈ ((⊤ : AffineSubspace ℝ W) : Set W)
      rw [hcar]
      simp
    exact (Convex.interior_nonempty_iff_affineSpan_eq_top hP'cvx).mpr haff
  -- supporting functional inside W
  letI : FiniteDimensional ℝ W := by infer_instance
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  rcases (exists_supporting_functional_at_frontier_generic (V := W) hP'cvx hP'int hzeroP' hzero_not_int) with ⟨n₁, hn₁ne, hn₁max⟩
  have hn₁max0 : ∀ x ∈ P', inner ℝ n₁ x ≤ 0 := by
    intro x hx
    simpa using hn₁max x hx
  have hproperW : ∃ x ∈ P', inner ℝ n₁ x < 0 := by
    by_contra hc
    have hz : ∀ x ∈ P', inner ℝ n₁ x = 0 := by
      intro x hx
      apply le_antisymm
      · exact hn₁max0 x hx
      · by_contra hpos
        exact hc ⟨x, hx, lt_of_not_ge hpos⟩
    have hsubset : P' ⊆ {x : W | inner ℝ n₁ x = inner ℝ n₁ 0} := by
      intro x hx
      simpa using hz x hx
    rcases hP'int with ⟨p', hp'⟩
    have hp'2 : p' ∈ interior {x : W | inner ℝ n₁ x = inner ℝ n₁ 0} := interior_mono hsubset hp'
    have hlevel : interior {x : W | inner ℝ n₁ x = inner ℝ n₁ 0} = ∅ :=
      interior_level_empty_of_ne_zero (V := W) hn₁ne
    rw [hlevel] at hp'2
    exact hp'2
  let n : V := (n₁ : V)
  have hn_ne : n ≠ 0 := by
    intro hn0
    exact hn₁ne (Subtype.ext hn0)
  refine ⟨n, hn_ne, ?_, ?_⟩
  · intro y hy
    -- y = q + (y - q); (y - q) ∈ P'
    have hwS : y - q ∈ S0 := by
      dsimp [S0]
      have hcalc : (y - q) + q = y := by abel
      simpa [hcalc] using hy
    have hwW : y - q ∈ (W : Set V) := hS0W hwS
    let w' : W := ⟨y - q, hwW⟩
    have hw'P : w' ∈ P' := by
      dsimp [P']
      exact hwS
    have hval : inner ℝ n₁ w' ≤ 0 := hn₁max0 w' hw'P
    -- inner n y = inner n q + inner n₁ w'
    have hdecomp : inner ℝ n y = inner ℝ n q + inner ℝ n (y - q) := by
      calc
        inner ℝ n y = inner ℝ n (q + (y - q)) := by congr 1; abel
        _ = inner ℝ n q + inner ℝ n (y - q) := by rw [inner_add_right]
    have hwy : inner ℝ n (y - q) = inner ℝ n₁ w' := by
      dsimp [n, w']
    calc
      inner ℝ n y = inner ℝ n q + inner ℝ n (y - q) := hdecomp
      _ = inner ℝ n q + inner ℝ n₁ w' := by rw [hwy]
      _ ≤ inner ℝ n q := by linarith
  · rcases hproperW with ⟨x₀, hx₀P, hx₀neg⟩
    refine ⟨q + (x₀ : V), ?_, ?_⟩
    · have hx₀S : (x₀ : V) ∈ S0 := by simpa [P'] using hx₀P
      dsimp [S0] at hx₀S
      simpa [add_comm] using hx₀S
    · have hdecomp : inner ℝ n (q + (x₀ : V)) = inner ℝ n q + inner ℝ n (x₀ : V) := by
        dsimp [n]
        rw [inner_add_right]
      have hwx : inner ℝ n (x₀ : V) = inner ℝ n₁ x₀ := by
        dsimp [n]
      calc
        inner ℝ n (q + (x₀ : V)) = inner ℝ n q + inner ℝ n (x₀ : V) := hdecomp
        _ = inner ℝ n q + inner ℝ n₁ x₀ := by rw [hwx]
        _ < inner ℝ n q := by linarith

lemma topFace_eq_of_mem {n : V} {P : Set V} {x y : V} (hx : x ∈ topFace n P)
    (hy : y ∈ topFace n P) : inner ℝ n x = inner ℝ n y := by
  apply le_antisymm
  · exact topFace_le_of_mem hy (topFace_subset hx)
  · exact topFace_le_of_mem hx (topFace_subset hy)

lemma lt_inner_of_not_mem_topFace {n : V} {P : Set V} {x q : V} (hq : q ∈ topFace n P)
    (hxP : x ∈ P) (hx : x ∉ topFace n P) : inner ℝ n x < inner ℝ n q := by
  have hle : inner ℝ n x ≤ inner ℝ n q := topFace_le_of_mem hq hxP
  have hne : inner ℝ n x ≠ inner ℝ n q := by
    intro heq
    apply hx
    refine ⟨hxP, fun y hy => ?_⟩
    calc
      inner ℝ n y ≤ inner ℝ n q := topFace_le_of_mem hq hy
      _ = inner ℝ n x := heq.symm
  exact lt_of_le_of_ne hle hne

/-- If `q` lies in the exposed face `F₀ = topFace a P` and in the exposed face of `F₀`
`F₁ = topFace b F₀`, then for a small `ε > 0` the face in direction `a + ε • b` of `P`
equals `F₁`. -/
lemma exists_eps_topFace_lift {u : Finset V} {P : Set V} (hP : P = convexHull ℝ (u : Set V))
    {q : V} (hqP : q ∈ P) (a b : V)
    (hqFa : q ∈ topFace a P)
    (hqFb : q ∈ topFace b (topFace a P)) :
    ∃ ε : ℝ, 0 < ε ∧ topFace (a + ε • b) P = topFace b (topFace a P) := by
  classical
  let F₀ : Set V := topFace a P
  let F₁ : Set V := topFace b F₀
  have hqF₀ : q ∈ F₀ := hqFa
  have hqF₁ : q ∈ F₁ := hqFb
  have hF₀P : F₀ ⊆ P := by intro x hx; exact topFace_subset hx
  have hF₁F₀ : F₁ ⊆ F₀ := by intro x hx; exact topFace_subset hx
  have huP : (u : Set V) ⊆ P := by rw [hP]; exact subset_convexHull ℝ (u : Set V)
  have hPcvx : Convex ℝ P := by rw [hP]; exact convex_convexHull ℝ (u : Set V)
  have hF₀cvx : Convex ℝ F₀ := topFace_convex hPcvx
  have hF₁cvx : Convex ℝ F₁ := topFace_convex hF₀cvx
  -- the 'bad' vertices (outside F₀ where b strictly increases)
  let bad : Finset V := u.filter (fun v => v ∉ F₀ ∧ inner ℝ b q < inner ℝ b v)
  have hbN : ∀ v ∈ bad, 0 < inner ℝ a q - inner ℝ a v := by
    intro v hv
    have hvmem : v ∈ u := (Finset.mem_filter.mp hv).1
    have hvF : v ∉ F₀ := (Finset.mem_filter.mp hv).2.1
    have hle : inner ℝ a v ≤ inner ℝ a q := topFace_le_of_mem hqF₀ (huP hvmem)
    have hne : inner ℝ a v ≠ inner ℝ a q := by
      intro heq
      apply hvF
      have hlev : F₀ = {x ∈ P | inner ℝ a x = inner ℝ a q} := by
        dsimp [F₀]
        exact topFace_eq_level hqP (fun y hy => topFace_le_of_mem hqF₀ hy)
      rw [hlev]
      exact ⟨huP hvmem, heq⟩
    have hlt : inner ℝ a v < inner ℝ a q := lt_of_le_of_ne hle hne
    linarith
  have hb_nonneg : ∀ v ∈ bad,
      0 ≤ (inner ℝ b v - inner ℝ b q) / (inner ℝ a q - inner ℝ a v) := by
    intro v hv
    have hD : 0 < inner ℝ b v - inner ℝ b q := sub_pos.mpr (Finset.mem_filter.mp hv).2.2
    exact div_nonneg hD.le (hbN v hv).le
  let S : ℝ := ∑ v ∈ bad, (inner ℝ b v - inner ℝ b q) / (inner ℝ a q - inner ℝ a v)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg hb_nonneg
  let ε : ℝ := (1 + S)⁻¹
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact inv_pos.mpr (by linarith)
  have hε_small : ∀ v ∈ bad, ε * (inner ℝ b v - inner ℝ b q) < inner ℝ a q - inner ℝ a v := by
    intro v hv
    let D : ℝ := inner ℝ b v - inner ℝ b q
    let N : ℝ := inner ℝ a q - inner ℝ a v
    have hD0 : 0 < D := by dsimp [D]; exact sub_pos.mpr (Finset.mem_filter.mp hv).2.2
    have hN0 : 0 < N := hbN v hv
    have hSge : D / N ≤ S := by
      dsimp [D, N, S]
      exact Finset.single_le_sum hb_nonneg hv
    have hDle : D ≤ N * S := by
      have h1 := mul_le_mul_of_nonneg_left hSge hN0.le
      field_simp [ne_of_gt hN0] at h1
      linarith
    have hND : D < N * (1 + S) := by nlinarith
    have h1p : 0 < 1 + S := by linarith
    have h' : D / (1 + S) < N := (div_lt_iff₀ h1p).mpr hND
    have h'2 : (1 + S)⁻¹ * D < N := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact h'
    simpa [ε, D, N] using h'2
  -- functional f := inner (a+εb) · , and val := f
  let f : V →ₗ[ℝ] ℝ := InnerProductSpace.toDual ℝ V (a + ε • b)
  have hfval : ∀ z : V, f z = inner ℝ (a + ε • b) z := by
    intro z
    exact (InnerProductSpace.toDual_apply_apply (𝕜 := ℝ) (E := V) (x := a + ε • b) (y := z))
  have hval_decomp : ∀ z : V, f z = inner ℝ a z + ε * inner ℝ b z := by
    intro z
    rw [hfval, inner_add_left, inner_smul_left]
    simp
  have hf_linear : ∀ (t : Finset V) (w : V → ℝ),
      f (∑ v ∈ t, w v • v) = ∑ v ∈ t, w v * f v := by
    intro t w
    calc
      f (∑ v ∈ t, w v • v) = ∑ v ∈ t, w v • f v := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro v hv
        exact (map_smul f (w v) v)
      _ = ∑ v ∈ t, w v * f v := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        simp
  -- vertex-wise bound
  have hvert_le : ∀ v ∈ u, f v ≤ f q := by
    intro v hv
    rw [hval_decomp v, hval_decomp q]
    by_cases hvF : v ∈ F₀
    · by_cases hvF₁ : v ∈ F₁
      · have haeq : inner ℝ a v = inner ℝ a q := topFace_eq_of_mem (n := a) hvF hqF₀
        have hbeq : inner ℝ b v = inner ℝ b q := topFace_eq_of_mem (n := b) hvF₁ hqF₁
        nlinarith
      · have haeq : inner ℝ a v = inner ℝ a q := topFace_eq_of_mem (n := a) hvF hqF₀
        have hb_lt : inner ℝ b v < inner ℝ b q := lt_inner_of_not_mem_topFace (n := b) hqF₁ hvF hvF₁
        have hε0' : 0 ≤ ε := le_of_lt hε0
        nlinarith
    · have ha_lt : inner ℝ a v < inner ℝ a q :=
        lt_inner_of_not_mem_topFace (n := a) hqF₀ (huP hv) hvF
      by_cases hble : inner ℝ b v ≤ inner ℝ b q
      · have hε0' : 0 ≤ ε := le_of_lt hε0
        nlinarith
      · have hvbad : v ∈ bad := by
          simp [bad, hv, hvF]
          exact lt_of_not_ge hble
        have hεs := hε_small v hvbad
        have hε0' : 0 ≤ ε := le_of_lt hε0
        nlinarith
  have hvert_eq_of : ∀ v ∈ u, v ∈ F₁ → f v = f q := by
    intro v hv hvF₁
    have hvF₀ : v ∈ F₀ := hF₁F₀ hvF₁
    have haeq : inner ℝ a v = inner ℝ a q := topFace_eq_of_mem (n := a) hvF₀ hqF₀
    have hbeq : inner ℝ b v = inner ℝ b q := topFace_eq_of_mem (n := b) hvF₁ hqF₁
    rw [hval_decomp v, hval_decomp q]
    nlinarith
  have hvert_eq_only : ∀ v ∈ u, f v = f q → v ∈ F₁ := by
    intro v hv hveq
    by_contra hvF₁
    have hvF₀ : v ∈ F₀ := by
      by_contra hvF₀
      have ha_lt : inner ℝ a v < inner ℝ a q :=
        lt_inner_of_not_mem_topFace (n := a) hqF₀ (huP hv) hvF₀
      have hle0 : f v ≤ f q := hvert_le v hv
      by_cases hble : inner ℝ b v ≤ inner ℝ b q
      · have hlt : f v < f q := by
          rw [hval_decomp v, hval_decomp q]
          nlinarith [hε0]
        linarith
      · have hvbad : v ∈ bad := by
          simp [bad, hv, hvF₀]
          exact lt_of_not_ge hble
        have hεs := hε_small v hvbad
        have hlt : f v < f q := by
          rw [hval_decomp v, hval_decomp q]
          nlinarith [hε0]
        linarith
    -- v ∈ F₀∖F₁
    have haeq : inner ℝ a v = inner ℝ a q := topFace_eq_of_mem (n := a) hvF₀ hqF₀
    have hb_lt : inner ℝ b v < inner ℝ b q := lt_inner_of_not_mem_topFace (n := b) hqF₁ hvF₀ hvF₁
    have hlt : f v < f q := by
      rw [hval_decomp v, hval_decomp q]
      nlinarith [hε0]
    linarith
  -- x ∈ topFace(a+εb) P implies x ∈ F₁
  have h1 : topFace (a + ε • b) P ⊆ F₁ := by
    intro x hx
    have hxP : x ∈ P := topFace_subset hx
    rcases (Finset.mem_convexHull' (s := u) (x := x)).1 (by simpa [hP] using hxP) with ⟨w, hw0, hw1, hwx⟩
    have hfq_le_fx : f q ≤ f x := by
      -- q ∈ P, and x ∈ topFace
      have hxmax : ∀ y ∈ P, f y ≤ f x := by
        intro y hy
        rw [hfval y, hfval x]
        exact hx.2 y hy
      exact hxmax q hqP
    have hfx_le_fq : f x ≤ f q := by
      calc
        f x = f (∑ v ∈ u, w v • v) := by rw [← hwx]
        _ = ∑ v ∈ u, w v * f v := hf_linear u w
        _ ≤ ∑ v ∈ u, w v * f q := by
          refine Finset.sum_le_sum ?_
          intro v hv
          exact mul_le_mul_of_nonneg_left (hvert_le v hv) (hw0 v hv)
        _ = f q := by
          rw [← Finset.sum_mul]
          rw [hw1]
          simp
    have hfeq : f x = f q := le_antisymm hfx_le_fq hfq_le_fx
    have hsupport : ∀ v ∈ u, w v ≠ 0 → v ∈ F₁ := by
      intro v hv hwv
      have hsum : (∑ v' ∈ u, w v' * (f q - f v')) = 0 := by
        calc
          (∑ v' ∈ u, w v' * (f q - f v')) = (∑ v' ∈ u, (w v' * f q - w v' * f v')) := by
            refine Finset.sum_congr rfl ?_
            intro v' hv'
            ring
          _ = (∑ v' ∈ u, w v' * f q) - (∑ v' ∈ u, w v' * f v') := by
            rw [Finset.sum_sub_distrib]
          _ = f q - f x := by
            rw [← Finset.sum_mul, hw1]
            have hright : (∑ v' ∈ u, w v' * f v') = f x := by
              rw [← hf_linear u w]
              rw [hwx]
            rw [hright]
            ring
          _ = 0 := by rw [hfeq]; ring
      have hterm_nonneg : ∀ v' ∈ u, 0 ≤ w v' * (f q - f v') := by
        intro v' hv'
        exact mul_nonneg (hw0 v' hv') (sub_nonneg.mpr (hvert_le v' hv'))
      have hterm : ∀ v' ∈ u, w v' * (f q - f v') = 0 := by
        intro v' hv'
        exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hsum v' hv'
      have hwq : w v * (f q - f v) = 0 := hterm v hv
      have hfv : f v = f q := by
        have hq : f q - f v = 0 := (mul_eq_zero.mp hwq).resolve_left hwv
        linarith
      exact hvert_eq_only v hv hfv
    -- x ∈ conv of the vertices in F₁
    let v₁ : Finset V := u.filter (fun z => z ∈ F₁)
    have hv₁sub : v₁ ⊆ u := Finset.filter_subset _ u
    have hw_out : ∀ z ∈ u, z ∉ v₁ → w z = 0 := by
      intro z hz hzv₁
      have hzF₁ : z ∉ F₁ := by
        intro hzF₁
        exact hzv₁ (by simp [v₁, hz, hzF₁])
      by_contra hwz
      exact hzF₁ (hsupport z hz hwz)
    have hsum₁ : (∑ z ∈ v₁, w z) = 1 := by
      calc
        (∑ z ∈ v₁, w z) = (∑ z ∈ u, w z) := Finset.sum_subset hv₁sub hw_out
        _ = 1 := hw1
    have hsumx₁ : (∑ z ∈ v₁, w z • z) = x := by
      calc
        (∑ z ∈ v₁, w z • z) = (∑ z ∈ u, w z • z) := by
          refine Finset.sum_subset hv₁sub ?_
          intro z hz hzv₁
          simp [hw_out z hz hzv₁]
        _ = x := hwx
    have hxconv : x ∈ convexHull ℝ (v₁ : Set V) := by
      refine (Finset.mem_convexHull' (s := v₁) (x := x)).2 ⟨w, ?_, hsum₁, hsumx₁⟩
      intro z hz
      exact hw0 z (hv₁sub hz)
    have hv₁eq : (v₁ : Set V) = F₁ ∩ (u : Set V) := by
      ext z
      simp [v₁]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hv₁eq] at hxconv
    exact (convexHull_min (inter_subset_left : F₁ ∩ (u : Set V) ⊆ F₁) hF₁cvx) hxconv
  -- conversely
  have h2 : F₁ ⊆ topFace (a + ε • b) P := by
    intro x hxF₁
    refine ⟨hF₀P (hF₁F₀ hxF₁), fun y hy => ?_⟩
    have hyval : f y ≤ f q := by
      rcases (Finset.mem_convexHull' (s := u) (x := y)).1 (by simpa [hP] using hy) with ⟨w, hw0, hw1, hwy⟩
      calc
        f y = f (∑ v ∈ u, w v • v) := by rw [← hwy]
        _ = ∑ v ∈ u, w v * f v := hf_linear u w
        _ ≤ ∑ v ∈ u, w v * f q := by
          refine Finset.sum_le_sum ?_
          intro v hv
          exact mul_le_mul_of_nonneg_left (hvert_le v hv) (hw0 v hv)
        _ = f q := by
          rw [← Finset.sum_mul]
          rw [hw1]
          simp
    have hxval : f q = f x := by
      have hxF₀ : x ∈ F₀ := hF₁F₀ hxF₁
      have haeq : inner ℝ a x = inner ℝ a q := topFace_eq_of_mem (n := a) hxF₀ hqF₀
      have hbeq : inner ℝ b x = inner ℝ b q := topFace_eq_of_mem (n := b) hxF₁ hqF₁
      rw [hval_decomp q, hval_decomp x]
      nlinarith
    calc
      f y ≤ f q := hyval
      _ = f x := hxval
  refine ⟨ε, hε0, ?_⟩
  dsimp [F₁] at h1 h2 ⊢
  exact Set.Subset.antisymm h1 h2

/-- The main recursive polytope statement: every point of the convex hull of a finite set lies
either in its intrinsic interior or in the intrinsic interior of a top face in some nonzero
direction.  Proved by induction on the number of vertices; the face of maximizers is a proper
face whose vertex set is strictly smaller. -/
theorem aux_polytope_card : ∀ N : ℕ, ∀ (u : Finset V), u.card = N →
    ∀ (P : Set V), P = convexHull ℝ (u : Set V) → ∀ q : V, q ∈ P →
      q ∈ intrinsicInterior ℝ P ∨ ∃ n : V, n ≠ 0 ∧ q ∈ intrinsicInterior ℝ (topFace n P) := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro u hu P hP q hqP
    by_cases hqint : q ∈ intrinsicInterior ℝ P
    · exact Or.inl hqint
    · right
      have hPcvx : Convex ℝ P := by rw [hP]; exact convex_convexHull ℝ (u : Set V)
      have hqnot : q ∉ intrinsicInterior ℝ P := hqint
      rcases exists_proper_support_at_intrinsicFrontier hPcvx hqP hqnot with
        ⟨n₀, hn₀ne, hn₀max, hn₀proper⟩
      let F₀ : Set V := topFace n₀ P
      have hqF₀ : q ∈ F₀ := by
        dsimp [F₀]
        exact mem_topFace_of_forall_le hqP hn₀max
      have hF₀exp : IsExposed ℝ P F₀ := by
        dsimp [F₀]
        exact isExposed_topFace n₀ P
      let u₀ : Finset V := u.filter (fun x => x ∈ F₀)
      have hF₀conv : F₀ = convexHull ℝ (F₀ ∩ (u : Set V)) :=
        exposedFace_conv_vertices_generic u P hP hF₀exp ⟨q, hqF₀⟩
      have hu₀set : (u₀ : Set V) = F₀ ∩ (u : Set V) := by
        ext x
        simp [u₀]
        exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      have hF₀rep : F₀ = convexHull ℝ (u₀ : Set V) := by
        rw [hF₀conv, hu₀set]
      -- u₀ is strictly smaller than u (proper face)
      have hF₀propre : F₀ ≠ P := by
        rcases hn₀proper with ⟨y, hyP, hylt⟩
        intro hEq
        have hyF : y ∈ F₀ := by rw [hEq]; exact hyP
        have hle : inner ℝ n₀ q ≤ inner ℝ n₀ y := by
          dsimp [F₀] at hyF
          exact topFace_le_of_mem hyF hqP
        linarith
      have hF₀Psub : F₀ ⊆ P := by
        intro x hxF
        dsimp [F₀] at hxF
        exact topFace_subset hxF
      have hu₀ne : u₀ ≠ u := by
        intro hEq
        apply hF₀propre
        have huF₀ : (u : Set V) ⊆ F₀ := by
          intro x hx
          have hxu₀ : x ∈ u₀ := by rw [hEq]; exact hx
          exact (Finset.mem_filter.mp hxu₀).2
        apply Set.Subset.antisymm
        · exact hF₀Psub
        · rw [hP]
          exact convexHull_min huF₀ (topFace_convex hPcvx)
      have hcard_lt : u₀.card < N := by
        have hsub₀ : u₀ ⊆ u := Finset.filter_subset _ u
        have hlt : u₀.card < u.card := by
          exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub₀, hu₀ne⟩)
        omega
      have hsub := ih u₀.card hcard_lt u₀ rfl F₀ hF₀rep q hqF₀
      rcases hsub with hqrelF₀ | ⟨n₁, hn₁ne, hqrel₁⟩
      · -- q is in the intrinsic interior of F₀ itself
        refine ⟨n₀, hn₀ne, ?_⟩
        dsimp [F₀] at hqrelF₀ ⊢
        exact hqrelF₀
      · -- q in intrinsic interior of a face of F₀: lift with ε
        have hqFb : q ∈ topFace n₁ F₀ := by
          dsimp [F₀]
          exact intrinsicInterior_subset hqrel₁
        have hqFa : q ∈ topFace n₀ P := by
          dsimp [F₀] at hqF₀ ⊢
          exact hqF₀
        rcases exists_eps_topFace_lift (u := u) (P := P) hP hqP n₀ n₁ hqFa hqFb with
          ⟨ε, hε0, hlift⟩
        refine ⟨n₀ + ε • n₁, ?_, ?_⟩
        · -- the direction is nonzero because its face is a proper subset of P
          intro hzero
          have htop0 : topFace (n₀ + ε • n₁) P = P := by
            simp [hzero, topFace]
          have hPleF₀ : P ⊆ topFace n₀ P := by
            calc
              P = topFace (n₀ + ε • n₁) P := htop0.symm
              _ = topFace n₁ (topFace n₀ P) := hlift
              _ ⊆ topFace n₀ P := fun x hx => topFace_subset hx
          apply hF₀propre
          dsimp [F₀]
          exact Set.Subset.antisymm (fun x hx => topFace_subset hx) hPleF₀
        · dsimp [F₀] at hqrel₁ ⊢
          rw [hlift]
          exact hqrel₁

/-- The requested statement, instantiated at `EuclideanSpace ℝ (Fin m)`. -/
theorem polytope_mem_intrinsicInterior_exposedFace (m : ℕ)
    (P : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (u : Finset (EuclideanSpace ℝ (Fin m)))
    (hP : (P : Set (EuclideanSpace ℝ (Fin m))) = convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin m))))
    (hint : (interior (P : Set (EuclideanSpace ℝ (Fin m)))).Nonempty)
    {q : EuclideanSpace ℝ (Fin m)} (hqP : q ∈ (P : Set (EuclideanSpace ℝ (Fin m)))) :
    q ∈ interior (P : Set (EuclideanSpace ℝ (Fin m))) ∨
      ∃ n : EuclideanSpace ℝ (Fin m), n ≠ 0 ∧
        q ∈ intrinsicInterior ℝ {x ∈ (P : Set (EuclideanSpace ℝ (Fin m))) |
          ∀ y ∈ (P : Set (EuclideanSpace ℝ (Fin m))), inner ℝ n y ≤ inner ℝ n x} := by
  classical
  let E : Type _ := EuclideanSpace ℝ (Fin m)
  have hPcvx : Convex ℝ (P : Set E) := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set E)
  have hmain := aux_polytope_card (V := E) u.card u rfl (P : Set E) hP q hqP
  rcases hmain with hqint | ⟨n, hnne, hqrel⟩
  · left
    exact mem_interior_of_mem_intrinsicInterior hPcvx hint hqint
  · right
    refine ⟨n, hnne, ?_⟩
    simpa [topFace] using hqrel