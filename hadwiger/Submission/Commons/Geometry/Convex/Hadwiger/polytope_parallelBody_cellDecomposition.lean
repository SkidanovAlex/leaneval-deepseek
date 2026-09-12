import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_mem_intrinsicInterior_exposedFace
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_disjoint_intrinsicInterior_faces

open Set
open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V]

/-! # The polytope parallel-body cell decomposition

For a full-dimensional polytope `P = convexHull u`, its (nonempty) exposed faces form a finite
family whose intrinsic interiors partition `P`, and for every `t ≥ 0` the parallel body
`P + closedBall 0 t` is the disjoint union, over the faces `F`, of
`intrinsicInterior F + (normalCone F ∩ closedBall 0 t)`.

We prove this for an arbitrary finite-dimensional real inner-product space `V`.
-/

/-- The outward normal cone of a subset `F` of `P`. -/
def normalCone (P F : Set V) : Set V :=
  {z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y}

lemma normalCone_iff {P F : Set V} {z : V} :
    z ∈ normalCone P F ↔ ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y := Iff.rfl

/-- `x ∈ F` and `z ∈ normalCone P F` implies `⟨x - w, z⟩ ≥ 0` for `w ∈ P`. -/
lemma inner_sub_nonneg_of_normalCone {P F : Set V} {x z : V} (hxF : x ∈ F)
    (hz : z ∈ normalCone P F) {w : V} (hwP : w ∈ P) : 0 ≤ inner ℝ (x - w) z := by
  have hle : inner ℝ z w ≤ inner ℝ z x := hz w hwP x hxF
  calc
    0 ≤ inner ℝ z x - inner ℝ z w := sub_nonneg.mpr hle
    _ = inner ℝ z (x - w) := by rw [inner_sub_right]
    _ = inner ℝ (x - w) z := by rw [real_inner_comm]

/-- If `⟨a, z⟩ ≥ 0` then `‖a + z‖ ≥ ‖z‖`. -/
lemma norm_add_ge_of_inner_nonneg {a z : V} (h : 0 ≤ inner ℝ a z) :
    ‖a + z‖ ^ 2 ≥ ‖z‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℝ)]
  simp
  nlinarith [sq_nonneg ‖a‖]

/-- If additionally equality holds then `a = 0`. -/
lemma eq_of_norm_add_sq_eq {a z : V} (h : 0 ≤ inner ℝ a z)
    (heq : ‖a + z‖ ^ 2 = ‖z‖ ^ 2) : a = 0 := by
  rw [norm_add_sq (𝕜 := ℝ)] at heq
  simp at heq
  have ha0 : ‖a‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a‖]
  have ha : ‖a‖ = 0 := sq_eq_zero_iff.mp ha0
  exact norm_eq_zero.mp ha

/-- A point written as `x + z` with `x ∈ F`, `z ∈ normalCone P F` is the unique point of `P`
closest to `x + z`: every other point of `P` is strictly farther away. -/
lemma unique_nearest_of_normalCone {P F : Set V} {x z : V} (hFP : F ⊆ P) (hxF : x ∈ F)
    (hz : z ∈ normalCone P F) {w : V} (hwP : w ∈ P) :
    ‖(x + z) - w‖ ^ 2 ≥ ‖z‖ ^ 2 ∧ (‖(x + z) - w‖ ^ 2 = ‖z‖ ^ 2 → w = x) := by
  have hveq : (x + z) - w = (x - w) + z := by abel
  have hin : 0 ≤ inner ℝ (x - w) z := inner_sub_nonneg_of_normalCone hxF hz hwP
  constructor
  · rw [hveq]
    exact norm_add_ge_of_inner_nonneg hin
  · intro heq
    rw [hveq] at heq
    have ha0 : x - w = 0 := eq_of_norm_add_sq_eq hin heq
    exact (sub_eq_zero.mp ha0).symm

/-- Square expansion: `‖a - t • b‖² = ‖a‖² - 2t⟨a,b⟩ + t²‖b‖²`. -/
lemma norm_sub_smul_sub_sq (a b : V) (t : ℝ) :
    ‖a - t • b‖ ^ 2 = ‖a‖ ^ 2 - 2 * t * inner ℝ a b + t ^ 2 * ‖b‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℝ)]
  rw [inner_smul_right]
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  simp [RCLike.re]
  ring

/-- Nearest point of a compact convex set with the normal-cone inequality. -/
lemma exists_nearest_normalCone {P : Set V} (hPc : IsCompact P) (hPcvx : Convex ℝ P)
    (hPn : P.Nonempty) (x : V) :
    ∃ q ∈ P, (∀ y ∈ P, ‖x - q‖ ≤ ‖x - y‖) ∧
      ∀ y ∈ P, inner ℝ (x - q) (y - q) ≤ 0 := by
  classical
  let f : V → ℝ := fun y => ‖x - y‖
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  obtain ⟨q, hq, hqmin⟩ := hPc.exists_isMinOn hPn hfcont.continuousOn
  refine ⟨q, hq, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ {z | f q ≤ f z} := hqmin hy
    simpa [f] using hy'
  · intro y hy
    by_contra hgt
    let s : ℝ := inner ℝ (x - q) (y - q)
    have hs : 0 < s := lt_of_not_ge hgt
    have hsq : ‖y - q‖ ^ 2 = 0 → False := by
      intro h0
      have hyq : y = q := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h0))
      subst y
      simp [s] at hs
    have hbound : ∀ t : ℝ, 0 < t → t ≤ 1 → 2 * s ≤ t * ‖y - q‖ ^ 2 := by
      intro t ht0 ht1
      have hzt : q + t • (y - q) ∈ P := by
        have hm : q + t • (y - q) = (1 - t) • q + t • y := by
          simp [smul_sub, sub_smul]
          abel
        rw [hm]
        exact hPcvx hq hy (by linarith) (le_of_lt ht0) (by ring)
      have hle : ‖x - q‖ ≤ ‖x - (q + t • (y - q))‖ := by
        have hy' : q + t • (y - q) ∈ {z | f q ≤ f z} := hqmin hzt
        simpa [f] using hy'
      have hnorm : ‖x - q‖ ^ 2 ≤ ‖x - (q + t • (y - q))‖ ^ 2 := by
        nlinarith [sq_nonneg (‖x - q‖ - ‖x - (q + t • (y - q))‖),
          norm_nonneg (x - q), norm_nonneg (x - (q + t • (y - q)))]
      have hdiff : x - (q + t • (y - q)) = (x - q) - t • (y - q) := by
        abel
      have hcalc := norm_sub_smul_sub_sq (x - q) (y - q) t
      rw [hdiff] at hnorm
      rw [hcalc] at hnorm
      have hsdef : inner ℝ (x - q) (y - q) = s := rfl
      rw [hsdef] at hnorm
      have hnorm' : 2 * t * s ≤ t ^ 2 * ‖y - q‖ ^ 2 := by
        nlinarith
      have htne : t ≠ 0 := ne_of_gt ht0
      have hmul := mul_le_mul_of_nonneg_left hnorm' (inv_nonneg.mpr (le_of_lt ht0))
      have hL : t⁻¹ * (2 * t * s) = 2 * s := by
        field_simp [htne]
      have hR : t⁻¹ * (t ^ 2 * ‖y - q‖ ^ 2) = t * ‖y - q‖ ^ 2 := by
        field_simp [htne]
      nlinarith
    by_cases hbig : ‖y - q‖ ^ 2 < s
    · have h1 := hbound 1 (by norm_num) (by norm_num)
      linarith
    · have hsqnz : ‖y - q‖ ^ 2 ≠ 0 := by
        intro h0
        exact hsq h0
      have hynz : ‖y - q‖ ≠ 0 := by
        intro hn
        apply hsqnz
        rw [hn]
        norm_num
      let t : ℝ := s / ‖y - q‖ ^ 2
      have ht0 : 0 < t := by
        dsimp [t]
        exact div_pos hs (sq_pos_of_ne_zero hynz)
      have ht1 : t ≤ 1 := by
        dsimp [t]
        exact div_le_one_of_le₀ (le_of_not_gt hbig) (sq_nonneg _)
      have h1 := hbound t ht0 ht1
      have hcalc : t * ‖y - q‖ ^ 2 = s := by
        dsimp [t]
        field_simp [hsqnz]
      linarith

/-- Two distinct exposed faces of a set have disjoint intrinsic interiors. -/
lemma intrinsicInterior_disjoint_of_exposed {P F G : Set V} (hF : IsExposed ℝ P F)
    (hG : IsExposed ℝ P G) (hFG : F ≠ G) :
    Disjoint (intrinsicInterior ℝ F) (intrinsicInterior ℝ G) := by
  classical
  rw [Set.disjoint_left]
  intro x hxF hxG
  have hxFmem : x ∈ F := intrinsicInterior_subset hxF
  have hxGmem : x ∈ G := intrinsicInterior_subset hxG
  have hG_le_F : G ⊆ F :=
    subset_of_mem_intrinsicInterior_of_isExtreme (C := P) (F := F) (G := G)
      hG.subset hF.isExtreme hxFmem hxG
  have hF_le_G : F ⊆ G :=
    subset_of_mem_intrinsicInterior_of_isExtreme (C := P) (F := G) (G := F)
      hF.subset hG.isExtreme hxGmem hxF
  exact hFG (Set.Subset.antisymm hF_le_G hG_le_F)

/-- The face decomposition of a polytope: the (nonempty) exposed faces of the convex hull of a
finite vertex set form a finite family whose intrinsic interiors partition the polytope. -/
theorem polytope_faceDecomposition (u : Finset V) (P : Set V)
    (hP : P = convexHull ℝ (u : Set V)) (hint : (interior P).Nonempty) :
    ∃ faces : Finset (Set V),
      (∀ F ∈ faces, F.Nonempty ∧ IsExposed ℝ P F) ∧
      (∀ F ∈ faces, ∃ S : Finset V, ↑S ⊆ u ∧ F = convexHull ℝ (↑S : Set V)) ∧
      (∀ p ∈ P, ∃! F : Set V, F ∈ faces ∧ p ∈ intrinsicInterior ℝ F) := by
  classical
  let facesSet : Set (Set V) := {F : Set V | (intrinsicInterior ℝ F).Nonempty ∧ IsExposed ℝ P F}
  have hfacesSet_fin : facesSet.Finite := by
    dsimp [facesSet]
    let S : Finset (Set V) := u.powerset.image (fun T : Finset V => convexHull ℝ (T : Set V))
    apply (S.finite_toSet : ((S : Finset (Set V)) : Set (Set V)).Finite).subset
    intro F hF
    rcases hF with ⟨hrel, hFexp⟩
    rcases hrel with ⟨p, hp⟩
    have hFne : F.Nonempty := ⟨p, intrinsicInterior_subset hp⟩
    have hFcv : F = convexHull ℝ (F ∩ (u : Set V)) := exposedFace_conv_vertices_generic u P hP hFexp hFne
    let T : Finset V := u.filter (fun x => x ∈ F)
    have hTsub : T ⊆ u := Finset.filter_subset (fun x : V => x ∈ F) u
    have hTeq : (T : Set V) = F ∩ (u : Set V) := by
      ext x
      simp [T]
      constructor <;> intro hx <;> exact ⟨hx.2, hx.1⟩
    refine Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr hTsub, ?_⟩
    calc
      convexHull ℝ (T : Set V) = convexHull ℝ (F ∩ (u : Set V)) := by rw [hTeq]
      _ = F := hFcv.symm
  let faces : Finset (Set V) := hfacesSet_fin.toFinset
  have hfaces_mem : ∀ F : Set V, F ∈ faces ↔ F ∈ facesSet := by
    intro F
    exact hfacesSet_fin.mem_toFinset
  have h1 : ∀ F ∈ faces, F.Nonempty ∧ IsExposed ℝ P F := by
    intro F hF
    have hFs := (hfaces_mem F).1 hF
    rcases hFs with ⟨hrel, hFexp⟩
    rcases hrel with ⟨x, hx⟩
    exact ⟨⟨x, intrinsicInterior_subset hx⟩, hFexp⟩
  have h2 : ∀ F ∈ faces, ∃ S : Finset V, ↑S ⊆ u ∧ F = convexHull ℝ (↑S : Set V) := by
    intro F hF
    have hFs := (hfaces_mem F).1 hF
    rcases hFs with ⟨hrel, hFexp⟩
    rcases hrel with ⟨x, hx⟩
    have hFne : F.Nonempty := ⟨x, intrinsicInterior_subset hx⟩
    have hFcv : F = convexHull ℝ (F ∩ (u : Set V)) := exposedFace_conv_vertices_generic u P hP hFexp hFne
    let S : Finset V := u.filter (fun x => x ∈ F)
    refine ⟨S, Finset.filter_subset (fun x : V => x ∈ F) u, ?_⟩
    have hS : (S : Set V) = F ∩ (u : Set V) := by
      ext x
      simp [S]
      constructor <;> intro hx <;> exact ⟨hx.2, hx.1⟩
    rw [hS]
    exact hFcv
  have h3 : ∀ p ∈ P, ∃! F : Set V, F ∈ faces ∧ p ∈ intrinsicInterior ℝ F := by
    intro p hpP
    have haux := aux_polytope_card u.card u rfl P hP p hpP
    rcases haux with hpint | ⟨n, hn, hprel⟩
    · refine ⟨P, ⟨(hfaces_mem P).2 ⟨⟨p, hpint⟩, IsExposed.refl P⟩, hpint⟩, ?_⟩
      intro F hF
      rcases hF with ⟨hFmem, hFp⟩
      by_contra hFP
      have hdisj : Disjoint (intrinsicInterior ℝ F) (intrinsicInterior ℝ P) :=
        intrinsicInterior_disjoint_of_exposed (P := P) (F := F) (G := P) (h1 F hFmem).2
          (IsExposed.refl P) hFP
      exact (Set.disjoint_left.mp hdisj) hFp hpint
    · let F₀ : Set V := topFace n P
      have hF₀rel : p ∈ intrinsicInterior ℝ F₀ := by
        simpa [F₀] using hprel
      have hF₀mem : F₀ ∈ faces := (hfaces_mem F₀).2 ⟨⟨p, hF₀rel⟩,
        by simpa [F₀] using isExposed_topFace n P⟩
      refine ⟨F₀, ⟨hF₀mem, hF₀rel⟩, ?_⟩
      intro F hF
      rcases hF with ⟨hFmem, hFp⟩
      by_contra hFF₀
      have hdisj : Disjoint (intrinsicInterior ℝ F) (intrinsicInterior ℝ F₀) :=
        intrinsicInterior_disjoint_of_exposed (P := P) (F := F) (G := F₀) (h1 F hFmem).2
          (by simpa [F₀] using isExposed_topFace n P) hFF₀
      exact (Set.disjoint_left.mp hdisj) hFp hF₀rel
  exact ⟨faces, h1, h2, h3⟩

theorem polytope_parallelBody_cellDecomposition
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V]
    (u : Finset V) (P : Set V)
    (hP : P = convexHull ℝ (u : Set V)) (hint : (interior P).Nonempty) :
    ∃ faces : Finset (Set V),
      (∀ F ∈ faces, F.Nonempty ∧ IsExposed ℝ P F) ∧
      (∀ F ∈ faces, ∃ S : Finset V, ↑S ⊆ u ∧ F = convexHull ℝ (↑S : Set V)) ∧
      (∀ p ∈ P, ∃! F : Set V, F ∈ faces ∧ p ∈ intrinsicInterior ℝ F) ∧
      (∀ t : ℝ, 0 ≤ t →
        (∀ F ∈ faces,
          Set.image2 (fun (x y : V) => x + y) (intrinsicInterior ℝ F)
              ({z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y} ∩
                Metric.closedBall (0 : V) t) ⊆
            Set.image2 (fun (x y : V) => x + y) P (Metric.closedBall (0 : V) t)) ∧
        (Set.image2 (fun (x y : V) => x + y) P (Metric.closedBall (0 : V) t) ⊆
          ⋃ F ∈ faces,
            Set.image2 (fun (x y : V) => x + y) (intrinsicInterior ℝ F)
              ({z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y} ∩
                Metric.closedBall (0 : V) t)) ∧
        (∀ F ∈ faces, ∀ G ∈ faces, F ≠ G →
          Disjoint
            (Set.image2 (fun (x y : V) => x + y) (intrinsicInterior ℝ F)
              ({z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y} ∩
                Metric.closedBall (0 : V) t))
            (Set.image2 (fun (x y : V) => x + y) (intrinsicInterior ℝ G)
              ({z : V | ∀ x ∈ P, ∀ y ∈ G, inner ℝ z x ≤ inner ℝ z y} ∩
                Metric.closedBall (0 : V) t)))) := by
  classical
  rcases polytope_faceDecomposition u P hP hint with ⟨faces, h1, h2, h3⟩
  refine ⟨faces, h1, h2, h3, ?_⟩
  intro t ht
  let NC : Set V → Set V := fun F => {z : V | ∀ x ∈ P, ∀ y ∈ F, inner ℝ z x ≤ inner ℝ z y}
  let Bt : Set V := Metric.closedBall (0 : V) t
  let PB : Set V := Set.image2 (fun (x y : V) => x + y) P Bt
  let cell : Set V → Set V := fun F =>
    Set.image2 (fun (x y : V) => x + y) (intrinsicInterior ℝ F) (NC F ∩ Bt)
  have hPcvx : Convex ℝ P := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set V)
  have hPcpt : IsCompact P := by
    rw [hP]
    exact u.finite_toSet.isCompact_convexHull ℝ
  have hPn : P.Nonempty := by
    rcases hint with ⟨p, hp⟩
    exact ⟨p, interior_subset hp⟩
  constructor
  · -- (a) each cell lies in the parallel body
    intro F hF
    dsimp [cell, PB]
    apply Set.image2_subset
    · intro x hx
      exact (IsExposed.subset (h1 F hF).2) (intrinsicInterior_subset hx)
    · intro z hz
      exact hz.2
  constructor
  · -- (b) the parallel body is covered by the cells
    intro q hq
    dsimp [PB] at hq
    rw [Set.mem_add] at hq
    rcases hq with ⟨p₀, hp₀P, b₀, hb₀B, hq_eq⟩
    have hb₀norm : ‖b₀‖ ≤ t := by
      have hb : b₀ ∈ Metric.closedBall (0 : V) t := by
        simpa [Bt] using hb₀B
      have hb' : dist b₀ 0 ≤ t := (Metric.mem_closedBall).1 hb
      simpa [dist_eq_norm] using hb'
    rcases exists_nearest_normalCone hPcpt hPcvx hPn q with ⟨ph, hphP, hmin, hnc⟩
    let z : V := q - ph
    have hzball : z ∈ Bt := by
      dsimp [z, Bt]
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have hz : ‖q - ph‖ ≤ t := by
        calc
          ‖q - ph‖ ≤ ‖q - p₀‖ := hmin p₀ hp₀P
          _ = ‖b₀‖ := by
            congr 1
            rw [← hq_eq]
            abel
          _ ≤ t := hb₀norm
      exact hz
    have hphtop : ph ∈ topFace z P := by
      apply mem_topFace_of_forall_le (x := ph) hphP
      intro y hy
      have hineq := hnc y hy
      have hsub : inner ℝ z y - inner ℝ z ph ≤ 0 := by
        have h1 : inner ℝ z y - inner ℝ z ph = inner ℝ z (y - ph) := by
          rw [inner_sub_right]
        rw [h1]
        dsimp [z]
        exact hineq
      linarith
    rcases h3 ph hphP with ⟨F, hFm, hFun⟩
    have hFmem : F ∈ faces := hFm.1
    have hprel : ph ∈ intrinsicInterior ℝ F := hFm.2
    have hFtop : F ⊆ topFace z P := by
      exact subset_of_mem_intrinsicInterior_of_isExtreme (C := P) (F := topFace z P) (G := F)
        (IsExposed.subset (h1 F hFmem).2) ((isExposed_topFace z P).isExtreme) hphtop hprel
    have hzNC : z ∈ NC F := by
      dsimp [NC]
      intro x hxP y hyF
      exact (hFtop hyF).2 x hxP
    refine Set.mem_iUnion₂.mpr ⟨F, hFmem, ?_⟩
    dsimp [cell]
    change q ∈ intrinsicInterior ℝ F + (NC F ∩ Bt)
    rw [Set.mem_add]
    refine ⟨ph, hprel, z, ⟨hzNC, hzball⟩, ?_⟩
    dsimp [z]
    abel
  · -- (c) cells over distinct faces are disjoint
    intro F hF G hG hFG
    rw [Set.disjoint_left]
    intro q hqF hqG
    dsimp [cell] at hqF hqG
    rw [Set.mem_add] at hqF hqG
    rcases hqF with ⟨x, hxFrel, z, hzmem, hqz⟩
    rcases hqG with ⟨x', hx'Grel, z', hz'mem, hqz'⟩
    have hzNC : z ∈ NC F := hzmem.1
    have hz'NC : z' ∈ NC G := hz'mem.1
    have hxF : x ∈ F := intrinsicInterior_subset hxFrel
    have hx'G : x' ∈ G := intrinsicInterior_subset hx'Grel
    have hxP : x ∈ P := (IsExposed.subset (h1 F hF).2) hxF
    have hx'P : x' ∈ P := (IsExposed.subset (h1 G hG).2) hx'G
    have hzq : q - x = z := by
      rw [← hqz]
      abel
    have hz'q : q - x' = z' := by
      rw [← hqz']
      abel
    have huniqx : ∀ w ∈ P,
        ‖q - w‖ ^ 2 ≥ ‖q - x‖ ^ 2 ∧ (‖q - w‖ ^ 2 = ‖q - x‖ ^ 2 → w = x) := by
      intro w hw
      have hw0 := unique_nearest_of_normalCone (P := P) (F := F) (x := x) (z := z)
        (IsExposed.subset (h1 F hF).2) hxF hzNC hw
      rw [hqz, ← hzq] at hw0
      exact hw0
    have huniqx' : ∀ w ∈ P,
        ‖q - w‖ ^ 2 ≥ ‖q - x'‖ ^ 2 ∧ (‖q - w‖ ^ 2 = ‖q - x'‖ ^ 2 → w = x') := by
      intro w hw
      have hw0 := unique_nearest_of_normalCone (P := P) (F := G) (x := x') (z := z')
        (IsExposed.subset (h1 G hG).2) hx'G hz'NC hw
      rw [hqz', ← hz'q] at hw0
      exact hw0
    have hle1 : ‖q - x'‖ ^ 2 ≥ ‖q - x‖ ^ 2 := (huniqx x' hx'P).1
    have hle2 : ‖q - x‖ ^ 2 ≥ ‖q - x'‖ ^ 2 := (huniqx' x hxP).1
    have heqsq : ‖q - x'‖ ^ 2 = ‖q - x‖ ^ 2 := le_antisymm hle2 hle1
    have hx'eqx : x' = x := (huniqx x' hx'P).2 heqsq
    have hxrelG : x ∈ intrinsicInterior ℝ G := by
      simpa [hx'eqx] using hx'Grel
    have hxuniq := h3 x hxP
    rcases hxuniq with ⟨F₀, hF₀m, hF₀u⟩
    have hF₀eqF : F₀ = F := (hF₀u F ⟨hF, hxFrel⟩).symm
    have hF₀eqG : F₀ = G := (hF₀u G ⟨hG, hxrelG⟩).symm
    exact hFG (hF₀eqF.symm.trans hF₀eqG)

end

end Commons.Geometry.Convex.Hadwiger