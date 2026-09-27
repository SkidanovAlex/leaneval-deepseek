import Mathlib
import Submission.Work.Mostow.cuspHoro.voronoiDefs

/-!
# The Dirichlet cell of a properly discontinuous isometric action

For a group `G` acting on the Euclidean space `E m = EuclideanSpace ℝ (Fin m)` through a
homomorphism `ρ : G →* (E m ≃ᵢ E m)` which is properly discontinuous and acts with a point
`x₀` of trivial stabiliser, we prove the three properties of the Dirichlet cell
`cell ρ x₀ = {y | ∀ g, dist y x₀ ≤ dist y (ρ g x₀)}`:

* it is convex (it is an intersection of closed half spaces);
* the translates `ρ g '' cell ρ x₀` cover the whole space;
* two points of the `ε`-inner parallel body are at distance at least `2ε` from each other
  after being moved apart by a non-trivial group element.

The last statement is the key "thickening" property used to build fundamental domains for
cusps: if `y, y'` both have distance `> ε` from the boundary of the cell then
`dist y (ρ g y') ≥ 2 ε` for every `g ≠ 1`.
-/

namespace Work.Mostow.cuspHoro

open Metric

/-- Moving `p` a small amount in the direction `b - a`, when `p` lies on the perpendicular
bisector of `a` and `b` and `b ≠ a`, strictly decreases the distance to `b`. -/
theorem voronoi_shift_lt_dist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b p : E} (hba : b ≠ a) (h : dist p a = dist p b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : E, dist w p < δ ∧ dist w b < dist w a := by
  have hv : b - a ≠ 0 := sub_ne_zero.mpr hba
  have hpos : 0 < ‖b - a‖ := norm_pos_iff.mpr hv
  set s : ℝ := δ / (2 * ‖b - a‖) with hsdef
  have hs : 0 < s := by rw [hsdef]; positivity
  refine ⟨p + s • (b - a), ?_, ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    rw [hsdef, div_mul_eq_mul_div, mul_div_mul_right]
    · linarith
    · positivity
  · have hId : ∀ x : E,
        dist x b ^ 2 = dist x a ^ 2 - 2 * inner ℝ (x - a) (b - a) + ‖b - a‖ ^ 2 := by
      intro x
      rw [dist_eq_norm, dist_eq_norm, ← norm_sub_sq_real (x - a) (b - a)]
      rw [show x - b = (x - a) - (b - a) from by abel]
    have hkey : 2 * inner ℝ (p - a) (b - a) = ‖b - a‖ ^ 2 := by
      have h1 := hId p
      have h2 : dist p b ^ 2 = dist p a ^ 2 := by rw [h]
      linarith
    have hx : (p + s • (b - a)) - a = (p - a) + s • (b - a) := by abel
    have h1 := hId (p + s • (b - a))
    rw [hx, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
    have hinner : inner ℝ (p - a) (b - a) = ‖b - a‖ ^ 2 / 2 := by linarith [hkey]
    rw [hinner] at h1
    have hsh : 0 < s * ‖b - a‖ ^ 2 := mul_pos hs (pow_pos hpos 2)
    have hsq : dist (p + s • (b - a)) b ^ 2 < dist (p + s • (b - a)) a ^ 2 := by
      nlinarith [h1, hsh]
    exact (sq_lt_sq₀ dist_nonneg dist_nonneg).mp hsq

/-- The set of points at least as close to `a` as to `b` is a closed half space, hence
convex. -/
theorem voronoi_convex_dist_halfspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a b : E) : Convex ℝ {y : E | dist y a ≤ dist y b} := by
  have hiff : ∀ y : E, (dist y a ≤ dist y b) ↔
      inner ℝ y (b - a) ≤ (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2 := by
    intro y
    have h1 : dist y a ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ y a + ‖a‖ ^ 2 := by
      rw [dist_eq_norm, norm_sub_sq_real]
    have h2 : dist y b ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ y b + ‖b‖ ^ 2 := by
      rw [dist_eq_norm, norm_sub_sq_real]
    rw [← sq_le_sq₀ (dist_nonneg : (0 : ℝ) ≤ dist y a) (dist_nonneg : (0 : ℝ) ≤ dist y b)]
    rw [h1, h2, inner_sub_right]
    constructor <;> intro h <;> linarith
  have hset : {y : E | dist y a ≤ dist y b} =
      {y : E | inner ℝ y (b - a) ≤ (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2} := by
    ext y
    exact hiff y
  rw [hset]
  exact convex_halfSpace_le (IsLinearMap.mk (fun x y => by rw [inner_add_left])
    (fun c x => by rw [real_inner_smul_left]; rfl)) _

/-- The Dirichlet cell of `x₀` is convex. -/
theorem voronoi_cell_convex {m : ℕ} {G : Type*} [Group G]
    (ρ : G →* (EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin m)) : Convex ℝ (cell ρ x₀) := by
  have h : cell ρ x₀ =
      ⋂ g : G, {y : EuclideanSpace ℝ (Fin m) | dist y x₀ ≤ dist y (ρ g x₀)} := by
    ext y
    simp [cell]
  rw [h]
  exact convex_iInter fun g => voronoi_convex_dist_halfspace x₀ (ρ g x₀)

/-- The translates of the Dirichlet cell of `x₀` cover the whole space, for a properly
discontinuous action. -/
theorem voronoi_cell_covers {m : ℕ} {G : Type*} [Group G]
    (ρ : G →* (EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)))
    (hproper : ∀ K : Set (EuclideanSpace ℝ (Fin m)), IsCompact K →
      {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite)
    (x₀ : EuclideanSpace ℝ (Fin m)) :
    ∀ y : EuclideanSpace ℝ (Fin m), ∃ g : G, ρ g y ∈ cell ρ x₀ := by
  intro y
  classical
  have hSfin : ({g : G | dist y (ρ g x₀) ≤ dist y x₀}).Finite := by
    refine (hproper (Metric.closedBall y (dist y x₀)) (isCompact_closedBall _ _)).subset ?_
    intro g hg
    have hgk : ρ g x₀ ∈ Metric.closedBall y (dist y x₀) := by
      rw [Metric.mem_closedBall, dist_comm]
      exact hg
    have hx0k : x₀ ∈ Metric.closedBall y (dist y x₀) := by
      rw [Metric.mem_closedBall, dist_comm]
    exact ⟨ρ g x₀, ⟨Set.mem_image_of_mem _ hx0k, hgk⟩⟩
  have hSne : ({g : G | dist y (ρ g x₀) ≤ dist y x₀}).Nonempty := ⟨1, by simp⟩
  obtain ⟨k, hkS, hkmin⟩ := hSfin.toFinset.exists_min_image (fun g => dist y (ρ g x₀))
    ⟨hSne.choose, by simpa using hSne.choose_spec⟩
  have hkS' : dist y (ρ k x₀) ≤ dist y x₀ := by simpa using hkS
  have hkmin' : ∀ h : G, dist y (ρ k x₀) ≤ dist y (ρ h x₀) := by
    intro h
    by_cases hh : dist y (ρ h x₀) ≤ dist y x₀
    · exact hkmin h (by simpa using hh)
    · have hh' : dist y x₀ < dist y (ρ h x₀) := not_le.mp hh
      linarith
  refine ⟨k⁻¹, ?_⟩
  intro h
  have h1 : dist (ρ (k⁻¹) y) x₀ = dist y (ρ k x₀) := by
    rw [map_inv, ← IsometryEquiv.dist_eq (ρ k) ((ρ k)⁻¹ y) x₀]
    simp
  have h2 : dist (ρ (k⁻¹) y) (ρ h x₀) = dist y (ρ (k * h) x₀) := by
    rw [map_inv, ← IsometryEquiv.dist_eq (ρ k) ((ρ k)⁻¹ y) (ρ h x₀), map_mul]
    simp
  rw [h1, h2]
  exact hkmin' (k * h)

/-- If both `p` and `ρ h p` lie in the Dirichlet cell, then `p` is equidistant from `x₀`
and `ρ h⁻¹ x₀`. -/
theorem voronoi_dist_eq_of_mem_cell {m : ℕ} {G : Type*} [Group G]
    (ρ : G →* (EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin m)) {h : G} {p : EuclideanSpace ℝ (Fin m)}
    (hp : p ∈ cell ρ x₀) (hp' : ρ h p ∈ cell ρ x₀) :
    dist p x₀ = dist p (ρ h⁻¹ x₀) := by
  refine le_antisymm (hp h⁻¹) ?_
  have h2 : dist (ρ h p) x₀ ≤ dist (ρ h p) (ρ h x₀) := hp' h
  have h3 : dist ((ρ h⁻¹) ((ρ h) p)) ((ρ h⁻¹) x₀) ≤
      dist ((ρ h⁻¹) ((ρ h) p)) ((ρ h⁻¹) ((ρ h) x₀)) := by
    rw [IsometryEquiv.dist_eq (ρ h⁻¹) (ρ h p) x₀,
        IsometryEquiv.dist_eq (ρ h⁻¹) (ρ h p) (ρ h x₀)]
    exact h2
  simpa using h3

/-- If `p` and `ρ h p` both lie in the Dirichlet cell with `h ≠ 1` (and `x₀` has trivial
stabiliser), then `p` is not an interior point of the cell: points arbitrarily close to `p`
lie outside the cell. -/
theorem voronoi_exists_notMem_cell_near {m : ℕ} {G : Type*} [Group G]
    (ρ : G →* (EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)))
    (x₀ : EuclideanSpace ℝ (Fin m)) (hx₀ : ∀ g : G, g ≠ 1 → ρ g x₀ ≠ x₀)
    {h : G} (hh : h ≠ 1) {p : EuclideanSpace ℝ (Fin m)}
    (hp : p ∈ cell ρ x₀) (hp' : ρ h p ∈ cell ρ x₀) :
    ∀ δ : ℝ, 0 < δ → ∃ w : EuclideanSpace ℝ (Fin m), dist w p < δ ∧ w ∉ cell ρ x₀ := by
  intro δ hδ
  have heq : dist p x₀ = dist p (ρ h⁻¹ x₀) := voronoi_dist_eq_of_mem_cell ρ x₀ hp hp'
  have hne : ρ h⁻¹ x₀ ≠ x₀ := hx₀ h⁻¹ (inv_ne_one.mpr hh)
  obtain ⟨w, hw1, hw2⟩ := voronoi_shift_lt_dist hne heq hδ
  refine ⟨w, hw1, ?_⟩
  intro hwc
  have := hwc h⁻¹
  linarith

theorem voronoiData {m : ℕ} {G : Type*} [Group G]
    (ρ : G →* (EuclideanSpace ℝ (Fin m) ≃ᵢ EuclideanSpace ℝ (Fin m)))
    (hproper : ∀ K : Set (EuclideanSpace ℝ (Fin m)), IsCompact K →
      {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite)
    (x₀ : EuclideanSpace ℝ (Fin m)) (hx₀ : ∀ g : G, g ≠ 1 → ρ g x₀ ≠ x₀) :
    Convex ℝ (Work.Mostow.cuspHoro.cell ρ x₀) ∧
      (∀ y : EuclideanSpace ℝ (Fin m), ∃ g : G, ρ g y ∈ Work.Mostow.cuspHoro.cell ρ x₀) ∧
      (∀ {ε : ℝ}, 0 < ε → ∀ {g : G}, g ≠ 1 → ∀ {y y' : EuclideanSpace ℝ (Fin m)},
        y ∈ Work.Mostow.cuspHoro.innerBody ε (Work.Mostow.cuspHoro.cell ρ x₀) →
        y' ∈ Work.Mostow.cuspHoro.innerBody ε (Work.Mostow.cuspHoro.cell ρ x₀) →
          2 * ε ≤ dist y (ρ g y')) := by
  refine ⟨voronoi_cell_convex ρ x₀, voronoi_cell_covers ρ hproper x₀, ?_⟩
  intro ε hε g hg y y' hy hy'
  by_contra hbad
  have hbad' : dist y (ρ g y') < 2 * ε := not_le.mp hbad
  set m : EuclideanSpace ℝ (Fin m) := midpoint ℝ y (ρ g y') with hmdef
  have hmy : dist m y = dist y (ρ g y') / 2 := by
    rw [hmdef, dist_midpoint_left]
    norm_num
    ring
  have hmy' : dist m (ρ g y') = dist y (ρ g y') / 2 := by
    rw [hmdef, dist_midpoint_right]
    norm_num
    ring
  have hym : dist y m = dist y (ρ g y') / 2 := by rw [dist_comm, hmy]
  have hm_cell : m ∈ cell ρ x₀ := hy m (by rw [hym]; linarith)
  have hdist_inv : dist (ρ (g⁻¹) m) y' = dist m (ρ g y') := by
    rw [map_inv, ← IsometryEquiv.dist_eq (ρ g) ((ρ g)⁻¹ m) y']
    simp
  have hinv_cell : ρ (g⁻¹) m ∈ cell ρ x₀ := by
    apply hy'
    rw [dist_comm, hdist_inv, hmy']
    linarith
  have heqdist : dist m x₀ = dist m (ρ g x₀) := by
    have h2 := voronoi_dist_eq_of_mem_cell ρ x₀ hm_cell hinv_cell
    simpa only [inv_inv] using h2
  have hne : ρ g x₀ ≠ x₀ := hx₀ g hg
  have hδ : 0 < ε - dist y (ρ g y') / 2 := by linarith
  obtain ⟨w, hw1, hw2⟩ := voronoi_shift_lt_dist hne heqdist hδ
  have hwy : dist y w < ε := by
    have h1 : dist y w ≤ dist y m + dist m w := dist_triangle y m w
    rw [hym] at h1
    have h3 : dist m w < ε - dist y (ρ g y') / 2 := by rw [dist_comm]; exact hw1
    linarith
  have hwcell : w ∈ cell ρ x₀ := hy w hwy
  have hcontra := hwcell g
  linarith

end Work.Mostow.cuspHoro
