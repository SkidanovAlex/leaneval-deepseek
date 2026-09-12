import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_mem_intrinsicInterior_exposedFace

open Set Filter Finset
open scoped BigOperators Topology Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Any `y` whose barycentric coordinates (w.r.t. an affine basis of `V`) are nonnegative and whose
coordinate at the last basis point vanishes lies in the convex hull of the face spanned by the
first `n` basis points. -/
lemma mem_convexHull_range_face_of_coord_nonneg_of_last_zero {n : ℕ}
    (b : AffineBasis (Fin (n + 1)) ℝ V) {y : V}
    (hcoord : ∀ i : Fin (n + 1), 0 ≤ b.coord i y)
    (hlast : b.coord (Fin.last n) y = 0) :
    y ∈ convexHull ℝ (Set.range (fun k : Fin n => b (Fin.castSucc k))) := by
  classical
  let c : Fin n → ℝ := fun k => b.coord (Fin.castSucc k) y
  have hsum1 : (∑ k : Fin n, c k) = 1 := by
    have hsplit := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => b.coord i y)
    have hsumall : (∑ i : Fin (n + 1), b.coord i y) = 1 := b.sum_coord_apply_eq_one y
    rw [hsplit, hlast] at hsumall
    simpa [c] using hsumall
  have hsumx : y = (∑ k : Fin n, c k • b (Fin.castSucc k)) := by
    calc
      y = ∑ i : Fin (n + 1), b.coord i y • b i := (b.linear_combination_coord_eq_self y).symm
      _ = (∑ k : Fin n, (b.coord (Fin.castSucc k) y) • b (Fin.castSucc k)) := by
        rw [Fin.sum_univ_castSucc]
        rw [hlast]
        simp
      _ = ∑ k : Fin n, c k • b (Fin.castSucc k) := by simp [c]
  have hnonneg : ∀ k : Fin n, 0 ≤ c k := by
    intro k
    exact hcoord (Fin.castSucc k)
  have hmem : (Finset.univ.affineCombination ℝ (fun k : Fin n => b (Fin.castSucc k)) c) ∈
      convexHull ℝ (Set.range (fun k : Fin n => b (Fin.castSucc k))) := by
    exact affineCombination_mem_convexHull (s := (Finset.univ : Finset (Fin n)))
      (v := fun k : Fin n => b (Fin.castSucc k)) (w := c) (by intro k hk; exact hnonneg k) (by simpa using hsum1)
  have hyaff : y = Finset.univ.affineCombination ℝ (fun k : Fin n => b (Fin.castSucc k)) c := by
    calc
      y = ∑ k : Fin n, c k • b (Fin.castSucc k) := hsumx
      _ = Finset.univ.affineCombination ℝ (fun k : Fin n => b (Fin.castSucc k)) c := by
        rw [Finset.affineCombination_eq_linear_combination (s := (Finset.univ : Finset (Fin n)))
          (p := fun k : Fin n => b (Fin.castSucc k)) (w := c) (by simpa using hsum1)]
  simpa [hyaff] using hmem

/-- If an affine function vanishes at a family of points then it vanishes on their affine span. -/
lemma eq_zero_on_affineSpan_of_eq_zero {ι : Type*} [Fintype ι] {n : ℕ}
    (b : AffineBasis (Fin (n + 1)) ℝ V) (i : Fin (n + 1)) (p : ι → V)
    (hp : ∀ j, b.coord i (p j) = 0) :
    ∀ z ∈ affineSpan ℝ (Set.range p), b.coord i z = 0 := by
  intro z hz
  rcases eq_affineCombination_of_mem_affineSpan_of_fintype hz with ⟨w, hw, rfl⟩
  rw [Finset.map_affineCombination (s := (Finset.univ : Finset ι)) (p := p) (w := w)
    (by simpa using hw) (f := b.coord i)]
  change (Finset.univ.affineCombination ℝ (fun j : ι => (b.coord i) (p j))) w = 0
  rw [funext hp]
  exact Finset.affineCombination_apply_const (s := (Finset.univ : Finset ι)) (w := w) (p := (0 : ℝ))
    (by simpa using hw)

/-- There is a neighbourhood of `y` on which all facet barycentric coordinates are positive. -/
lemma exists_ball_pos_coords {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ V) {y : V}
    (hpos : ∀ k : Fin n, 0 < b.coord (Fin.castSucc k) y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : V, dist z y < δ → ∀ k : Fin n, 0 < b.coord (Fin.castSucc k) z := by
  classical
  have hnbd : ∀ k : Fin n, {z : V | 0 < b.coord (Fin.castSucc k) z} ∈ 𝓝 y := by
    intro k
    have hc : Continuous (fun z : V => b.coord (Fin.castSucc k) z) :=
      continuous_barycentric_coord b (Fin.castSucc k)
    exact hc.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (hpos k))
  have hall : ∀ᶠ z in 𝓝 y, ∀ k : Fin n, 0 < b.coord (Fin.castSucc k) z :=
    Filter.eventually_all.mpr hnbd
  exact Metric.eventually_nhds_iff.mp hall

/-- A point of the affine span of the facet whose facet barycentric coordinates are strictly
positive lies in the intrinsic interior of the convex hull of the facet. -/
lemma mem_intrinsicInterior_facet {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ V) {y : V}
    (hpos : ∀ k : Fin n, 0 < b.coord (Fin.castSucc k) y)
    (hlast : b.coord (Fin.last n) y = 0) :
    y ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range (fun k : Fin n => b (Fin.castSucc k)))) := by
  classical
  let p : Fin n → V := fun k => b (Fin.castSucc k)
  let F : Set V := convexHull ℝ (Set.range p)
  let A : AffineSubspace ℝ V := affineSpan ℝ (Set.range p)
  let A' : AffineSubspace ℝ V := affineSpan ℝ F
  have hAeq : A' = A := by
    dsimp [A, A', F]
    rw [affineSpan_convexHull]
  have hyF : y ∈ F := by
    dsimp [F]
    refine mem_convexHull_range_face_of_coord_nonneg_of_last_zero b ?_ hlast
    intro i
    by_cases hi : i = Fin.last n
    · rw [hi, hlast]
    · have hlt : i.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) (by intro hv; apply hi; apply Fin.ext; simpa using hv)
      let k : Fin n := ⟨i.val, hlt⟩
      have hik : i = Fin.castSucc k := by apply Fin.ext; rfl
      rw [hik]
      exact (hpos k).le
  have hyA : y ∈ (A : Set V) := (convexHull_subset_affineSpan (s := (Set.range p))) hyF
  have hyA' : y ∈ (A' : Set V) := by simpa [hAeq] using hyA
  let yA : A' := ⟨y, hyA'⟩
  have hcoef_last : ∀ z : A, b.coord (Fin.last n) (z : V) = 0 := by
    intro z
    exact eq_zero_on_affineSpan_of_eq_zero b (Fin.last n) p (fun k => by
      dsimp [p]
      exact b.coord_apply_ne (Fin.castSucc_ne_last k).symm) (z : V) z.2
  have hyAint : yA ∈ interior ((↑) ⁻¹' F : Set A') := by
    rw [mem_interior_iff_mem_nhds]
    rw [Metric.mem_nhds_iff]
    rcases exists_ball_pos_coords b hpos with ⟨δ, hδ0, hδpos⟩
    refine ⟨δ, hδ0, ?_⟩
    intro z hzball
    change (z : V) ∈ F
    have hzA : (z : V) ∈ (A : Set V) := by simpa [hAeq] using z.2
    dsimp [F]
    refine mem_convexHull_range_face_of_coord_nonneg_of_last_zero b ?_ ?_
    · intro i
      by_cases hi : i = Fin.last n
      · rw [hi]
        exact le_of_eq ((hcoef_last ⟨(z : V), hzA⟩).symm)
      · have hlt : i.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) (by intro hv; apply hi; apply Fin.ext; simpa using hv)
        let k : Fin n := ⟨i.val, hlt⟩
        have hik : i = Fin.castSucc k := by apply Fin.ext; rfl
        rw [hik]
        exact (hδpos (z : V) (by simpa [Subtype.dist_eq, yA] using hzball) k).le
    · exact hcoef_last ⟨(z : V), hzA⟩
  exact mem_intrinsicInterior.mpr ⟨yA, hyAint, rfl⟩

/-- The requested lemma: an interior point of a simplex lies on the open segment from the last
vertex to an interior point of the opposite face. -/
theorem cone_int_mem {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (hn : 0 < n) (w : Fin (n + 1) → V)
    (hw : AffineIndependent ℝ w) (hspan : affineSpan ℝ (Set.range w) = ⊤) {x : V}
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range w))) :
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ y : V, y ∈ intrinsicInterior ℝ
        (convexHull ℝ (Set.range (fun k : Fin n => w k.castSucc))) ∧
        x = (1 - t) • w (Fin.last n) + t • y := by
  classical
  let b : AffineBasis (Fin (n + 1)) ℝ V := ⟨w, hw, hspan⟩
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  haveI : CompleteSpace V := FiniteDimensional.complete ℝ V
  have hcoef : (⇑b : Fin (n + 1) → V) = w := by rfl
  let lam : Fin (n + 1) → ℝ := fun i => b.coord i x
  -- 1. all barycentric coordinates are strictly positive
  have hpos : ∀ i : Fin (n + 1), 0 < lam i := by
    intro i
    have hCvx : Convex ℝ (convexHull ℝ (Set.range w)) := convex_convexHull ℝ (Set.range w)
    have hInt : (interior (convexHull ℝ (Set.range w))).Nonempty :=
      (interior_convexHull_nonempty_iff_affineSpan_eq_top (s := (Set.range w))).mpr hspan
    have hint : x ∈ interior (convexHull ℝ (Set.range w)) :=
      mem_interior_of_mem_intrinsicInterior hCvx hInt hx
    have hbint : x ∈ interior (convexHull ℝ (Set.range ⇑b)) := by
      rw [hcoef]
      exact hint
    have hmem' : ∀ j : Fin (n + 1), 0 < b.coord j x := by
      rw [b.interior_convexHull] at hbint
      simpa using hbint
    simpa [lam] using hmem' i
  -- 2. the mass t on the face
  let t : ℝ := ∑ k : Fin n, lam (Fin.castSucc k)
  have hsum1 : (∑ i : Fin (n + 1), lam i) = 1 := by
    dsimp [lam]
    exact b.sum_coord_apply_eq_one x
  have hsplit : (∑ i : Fin (n + 1), lam i) =
      (∑ k : Fin n, lam (Fin.castSucc k)) + lam (Fin.last n) :=
    Fin.sum_univ_castSucc (fun i : Fin (n + 1) => lam i)
  have hsplit1 : (∑ k : Fin n, lam (Fin.castSucc k)) + lam (Fin.last n) = 1 := by
    simpa [hsplit] using hsum1
  have ht_eq : t = 1 - lam (Fin.last n) := by
    dsimp [t]
    linarith
  have ht0 : 0 < t := by
    dsimp [t]
    refine Finset.sum_pos ?_ ?_
    · intro k hk
      exact hpos (Fin.castSucc k)
    · refine ⟨0, ?_⟩
      simp
  have ht1 : t < 1 := by linarith [ht_eq, hpos (Fin.last n)]
  have ht_ne : t ≠ 0 := ne_of_gt ht0
  -- 3. weights of y
  let γ : Fin (n + 1) → ℝ := fun i => if i = Fin.last n then 0 else lam i / t
  let y : V := ∑ i : Fin (n + 1), γ i • b i
  have hγlast : γ (Fin.last n) = 0 := by simp [γ]
  have hγk (k : Fin n) : γ (Fin.castSucc k) = lam (Fin.castSucc k) / t := by
    dsimp [γ]
    simp [Fin.castSucc_ne_last k]
  have hsum_div : (∑ k : Fin n, lam (Fin.castSucc k) / t) = t / t := by
    calc
      (∑ k : Fin n, lam (Fin.castSucc k) / t) = (∑ k : Fin n, lam (Fin.castSucc k)) / t := by
        rw [Finset.sum_div]
      _ = t / t := by simp [t]
  have hγsum : (∑ i : Fin (n + 1), γ i) = 1 := by
    calc
      (∑ i : Fin (n + 1), γ i) = (∑ k : Fin n, γ (Fin.castSucc k)) + γ (Fin.last n) :=
        Fin.sum_univ_castSucc (fun i : Fin (n + 1) => γ i)
      _ = (∑ k : Fin n, lam (Fin.castSucc k) / t) + 0 := by simp [hγk, hγlast]
      _ = (∑ k : Fin n, lam (Fin.castSucc k) / t) := by simp
      _ = 1 := by rw [hsum_div, div_self ht_ne]
  -- 4. coordinates of y
  have hyaff : y = Finset.univ.affineCombination ℝ b γ := by
    rw [Finset.affineCombination_eq_linear_combination (s := (Finset.univ : Finset (Fin (n+1))))
      (p := b) (w := γ) (by simpa using hγsum)]
  have hcoord (j : Fin (n + 1)) : b.coord j y = γ j := by
    rw [hyaff]
    exact b.coord_apply_combination_of_mem (Finset.mem_univ j) (by simpa using hγsum)
  -- 5. y lies in the intrinsic interior of the facet
  have hyF : y ∈ intrinsicInterior ℝ
      (convexHull ℝ (Set.range (fun k : Fin n => b (Fin.castSucc k)))) := by
    refine mem_intrinsicInterior_facet b ?_ ?_
    · intro k
      rw [hcoord (Fin.castSucc k), hγk k]
      exact div_pos (hpos (Fin.castSucc k)) ht0
    · rw [hcoord (Fin.last n), hγlast]
  -- 6. the decomposition identity
  have hxsplit : x = (∑ k : Fin n, lam (Fin.castSucc k) • b (Fin.castSucc k)) +
      lam (Fin.last n) • b (Fin.last n) := by
    calc
      x = ∑ i : Fin (n + 1), lam i • b i := by
        simpa [lam] using (b.linear_combination_coord_eq_self x).symm
      _ = (∑ k : Fin n, lam (Fin.castSucc k) • b (Fin.castSucc k)) +
          lam (Fin.last n) • b (Fin.last n) :=
        Fin.sum_univ_castSucc (fun i : Fin (n + 1) => lam i • b i)
  have hty : t • y = (∑ k : Fin n, lam (Fin.castSucc k) • b (Fin.castSucc k)) := by
    calc
      t • y = t • (∑ i : Fin (n + 1), γ i • b i) := by simp [y]
      _ = ∑ i : Fin (n + 1), t • (γ i • b i) := by rw [Finset.smul_sum]
      _ = (∑ k : Fin n, t • (γ (Fin.castSucc k) • b (Fin.castSucc k))) := by
        rw [Fin.sum_univ_castSucc]
        rw [hγlast]
        simp
      _ = ∑ k : Fin n, lam (Fin.castSucc k) • b (Fin.castSucc k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [smul_smul]
        rw [hγk k]
        congr 1
        field_simp [ht_ne]
  have hxeq : x = (1 - t) • b (Fin.last n) + t • y := by
    calc
      x = (∑ k : Fin n, lam (Fin.castSucc k) • b (Fin.castSucc k)) +
          lam (Fin.last n) • b (Fin.last n) := hxsplit
      _ = t • y + lam (Fin.last n) • b (Fin.last n) := by rw [← hty]
      _ = (1 - t) • b (Fin.last n) + t • y := by
        have hl : lam (Fin.last n) = 1 - t := by linarith
        rw [hl, add_comm]
  -- 7. assemble
  refine ⟨t, Set.mem_Ioo.mpr ⟨ht0, ht1⟩, ?_⟩
  refine ⟨y, ?_, ?_⟩
  · have hyFw : y ∈ intrinsicInterior ℝ
        (convexHull ℝ (Set.range (fun k : Fin n => w k.castSucc))) := by
      have he : (fun k : Fin n => b (Fin.castSucc k)) = (fun k : Fin n => w (Fin.castSucc k)) := by
        ext k
        rfl
      rw [he] at hyF
      exact hyF
    exact hyFw
  · have hxeqw : x = (1 - t) • w (Fin.last n) + t • y := by
      rw [hcoef] at hxeq
      exact hxeq
    exact hxeqw
