import Mathlib

/-!
# Foundations for "two balls glued along their boundary form a sphere"

This file sets up the explicit geometry used to prove `Work.Morse.two_balls`:
the decomposition of the unit sphere `Sⁿ ⊆ ℝ^{n+1}` into an upper and a lower
hemisphere, each homeomorphic to the closed unit ball `Dⁿ ⊆ ℝⁿ` via the graph
parametrisation `y ↦ (y, ±√(1 - ‖y‖²))`.

Concretely we define, on `EuclideanSpace ℝ (Fin n) = PiLp 2 (Fin n → ℝ)`,

* `snocLp y t` — append the coordinate `t` to `y`, giving an element of `ℝⁿ⁺¹`;
* `strip z` — drop the last coordinate of `z`;
* `upMap y` (resp. `downMap y`) — the graph of `√(1 - ‖y‖²)` (resp. `-√(1 - ‖y‖²)`),
  landing on the unit sphere of `ℝⁿ⁺¹`;
* `upperHemi` / `lowerHemi` — the two hemispheres.

The two parametrisations agree on the unit sphere `Sⁿ⁻¹ ⊆ Dⁿ`.
-/

open scoped Manifold ContDiff Topology
open Metric

namespace Work.Morse

variable {n : ℕ}

/-! ## Appending and stripping a coordinate -/

/-- Append the coordinate `t` to `y : ℝⁿ`, viewed as an element of `EuclideanSpace ℝ (Fin (n+1))`. -/
noncomputable def snocLp (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (fun i => y.ofLp i) t)

@[simp] lemma snocLp_ofLp_castSucc (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) (i : Fin n) :
    (snocLp y t).ofLp i.castSucc = y.ofLp i := by simp [snocLp]

@[simp] lemma snocLp_ofLp_last (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (snocLp y t).ofLp (Fin.last n) = t := by simp [snocLp]

lemma snocLp_norm_sq (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖snocLp y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_castSucc]
  simp only [snocLp, WithLp.ofLp_toLp, Fin.snoc_castSucc, Fin.snoc_last]
  rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ), Real.norm_eq_abs, sq_abs]

lemma snocLp_injective (t : ℝ) :
    Function.Injective (fun y : EuclideanSpace ℝ (Fin n) => snocLp y t) := by
  intro y y' h
  apply PiLp.ext
  intro i
  have := congrArg (fun z => z.ofLp i.castSucc) h
  simpa using this

/-- Drop the last coordinate. -/
noncomputable def strip (z : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => z.ofLp i.castSucc)

@[simp] lemma strip_ofLp (z : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    (strip z).ofLp i = z.ofLp i.castSucc := by simp [strip]

lemma snocLp_strip (z : EuclideanSpace ℝ (Fin (n + 1))) :
    snocLp (strip z) (z.ofLp (Fin.last n)) = z := by
  apply PiLp.ext
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

@[fun_prop]
lemma continuous_snocLp :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => snocLp p.1 p.2) := by
  unfold snocLp; fun_prop

/-! ## The upper and lower hemisphere parametrisations -/

lemma norm_le_one_of_mem_closedBall {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) : ‖y‖ ≤ 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
  exact hy

lemma norm_eq_one_of_mem_sphere {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ‖z‖ = 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
  exact hz

/-- The upper graph parametrisation of the unit sphere: `y ↦ (y, √(1 - ‖y‖²))`. -/
noncomputable def upMap (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨snocLp (y : EuclideanSpace ℝ (Fin n)) (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)),
    by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      have hy : ‖(y:EuclideanSpace ℝ (Fin n))‖ ≤ 1 := norm_le_one_of_mem_closedBall y.2
      have hs : 0 ≤ 1 - ‖(y:EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
        nlinarith [norm_nonneg (y:EuclideanSpace ℝ (Fin n))]
      have h2 : ‖snocLp (y:EuclideanSpace ℝ (Fin n))
          (Real.sqrt (1 - ‖(y:EuclideanSpace ℝ (Fin n))‖ ^ 2))‖ ^ 2 = 1 := by
        rw [snocLp_norm_sq, Real.sq_sqrt hs]; ring
      rcases sq_eq_one_iff.mp h2 with h | h
      · exact h
      · exfalso
        linarith [norm_nonneg (snocLp (y:EuclideanSpace ℝ (Fin n))
          (Real.sqrt (1 - ‖(y:EuclideanSpace ℝ (Fin n))‖ ^ 2)))]⟩

/-- The lower graph parametrisation of the unit sphere: `y ↦ (y, -√(1 - ‖y‖²))`. -/
noncomputable def downMap (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨snocLp (y : EuclideanSpace ℝ (Fin n)) (-Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)),
    by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      have hs : 0 ≤ 1 - ‖(y:EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
        nlinarith [norm_nonneg (y:EuclideanSpace ℝ (Fin n)), norm_le_one_of_mem_closedBall y.2]
      have h2 : ‖snocLp (y:EuclideanSpace ℝ (Fin n))
          (-Real.sqrt (1 - ‖(y:EuclideanSpace ℝ (Fin n))‖ ^ 2))‖ ^ 2 = 1 := by
        rw [snocLp_norm_sq, neg_sq, Real.sq_sqrt hs]; ring
      rcases sq_eq_one_iff.mp h2 with h | h
      · exact h
      · exfalso
        linarith [norm_nonneg (snocLp (y:EuclideanSpace ℝ (Fin n))
          (-Real.sqrt (1 - ‖(y:EuclideanSpace ℝ (Fin n))‖ ^ 2)))]⟩

@[simp] lemma upMap_apply (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (upMap y : EuclideanSpace ℝ (Fin (n+1))) =
      snocLp (y : EuclideanSpace ℝ (Fin n)) (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)) :=
  rfl

@[simp] lemma downMap_apply (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (downMap y : EuclideanSpace ℝ (Fin (n+1))) =
      snocLp (y : EuclideanSpace ℝ (Fin n)) (-Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2)) :=
  rfl

@[simp] lemma upMap_ofLp_castSucc (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (i : Fin n) :
    ((upMap y : EuclideanSpace ℝ (Fin (n+1)))).ofLp i.castSucc =
      (y : EuclideanSpace ℝ (Fin n)).ofLp i := by
  rw [upMap_apply, snocLp_ofLp_castSucc]

@[simp] lemma downMap_ofLp_castSucc (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (i : Fin n) :
    ((downMap y : EuclideanSpace ℝ (Fin (n+1)))).ofLp i.castSucc =
      (y : EuclideanSpace ℝ (Fin n)).ofLp i := by
  rw [downMap_apply, snocLp_ofLp_castSucc]

@[simp] lemma upMap_ofLp_last (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ((upMap y : EuclideanSpace ℝ (Fin (n+1)))).ofLp (Fin.last n) =
      Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
  rw [upMap_apply, snocLp_ofLp_last]

@[simp] lemma downMap_ofLp_last (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ((downMap y : EuclideanSpace ℝ (Fin (n+1)))).ofLp (Fin.last n) =
      -Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
  rw [downMap_apply, snocLp_ofLp_last]

lemma continuous_upMap : Continuous (upMap (n := n)) := by
  apply Continuous.subtype_mk
  unfold snocLp; fun_prop

lemma continuous_downMap : Continuous (downMap (n := n)) := by
  apply Continuous.subtype_mk
  unfold snocLp; fun_prop

lemma upMap_injective : Function.Injective (upMap (n := n)) := by
  intro y y' h
  apply Subtype.ext
  apply PiLp.ext
  intro i
  have := congrArg (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))).ofLp i.castSucc) h
  simpa using this

lemma downMap_injective : Function.Injective (downMap (n := n)) := by
  intro y y' h
  apply Subtype.ext
  apply PiLp.ext
  intro i
  have := congrArg (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))).ofLp i.castSucc) h
  simpa using this

/-! ## The hemispheres -/

/-- The equator of the unit sphere of `ℝⁿ⁺¹`. -/
def equator (n : ℕ) : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
  {z | (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n) = 0}

/-- The upper hemisphere of the unit sphere of `ℝⁿ⁺¹`. -/
def upperHemi (n : ℕ) : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
  {z | 0 ≤ (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)}

/-- The lower hemisphere of the unit sphere of `ℝⁿ⁺¹`. -/
def lowerHemi (n : ℕ) : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
  {z | (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n) ≤ 0}

/-! ## Relating the sphere inside the closed ball to the ambient sphere -/

lemma mem_sphere_closedBall_iff (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    y ∈ Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 1 ↔
      (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [Metric.mem_sphere, Metric.mem_sphere, Subtype.dist_eq]
  rfl

lemma norm_eq_one_of_mem_sphere_closedBall
    (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hy : y ∈ Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 1) :
    ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 :=
  norm_eq_one_of_mem_sphere ((mem_sphere_closedBall_iff y).mp hy)

lemma mem_sphere_closedBall_of_norm_eq_one
    (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1) :
    y ∈ Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 1 :=
  (mem_sphere_closedBall_iff y).mpr (by rwa [Metric.mem_sphere, dist_eq_norm, sub_zero])

/-- The last coordinate of a point of the unit sphere of `ℝⁿ⁺¹`. -/
def lastCoord (n : ℕ) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : ℝ :=
  (z : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n)

@[simp] lemma lastCoord_apply (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    lastCoord n z = (z : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n) := rfl

lemma upperHemi_eq : upperHemi n = {z | 0 ≤ lastCoord n z} := rfl
lemma lowerHemi_eq : lowerHemi n = {z | lastCoord n z ≤ 0} := rfl

@[simp] lemma lastCoord_upMap (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    lastCoord n (upMap y) = Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2) :=
  upMap_ofLp_last y

@[simp] lemma lastCoord_downMap (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    lastCoord n (downMap y) = -Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2) :=
  downMap_ofLp_last y

lemma upMap_mem_upperHemi (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    upMap y ∈ upperHemi n := by
  show 0 ≤ (upMap y : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)
  rw [upMap_ofLp_last]
  exact Real.sqrt_nonneg _

lemma downMap_mem_lowerHemi (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    downMap y ∈ lowerHemi n := by
  show (downMap y : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n) ≤ 0
  rw [downMap_ofLp_last]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

lemma mem_range_upMap {z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1}
    (hz : z ∈ upperHemi n) : z ∈ Set.range (upMap (n := n)) := by
  have hzt : 0 ≤ (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n) := hz
  have hz1 : ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := norm_eq_one_of_mem_sphere z.2
  have hnorm : ‖strip (z : EuclideanSpace ℝ (Fin (n+1)))‖ ^ 2
      = 1 - ((z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)) ^ 2 := by
    have h := snocLp_norm_sq (strip (z : EuclideanSpace ℝ (Fin (n+1))))
      ((z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n))
    rw [snocLp_strip, hz1] at h
    linarith [h]
  have hmem : strip (z : EuclideanSpace ℝ (Fin (n+1)))
      ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    nlinarith [norm_nonneg (strip (z : EuclideanSpace ℝ (Fin (n+1))))]
  refine ⟨⟨strip (z : EuclideanSpace ℝ (Fin (n+1))), hmem⟩, ?_⟩
  apply Subtype.ext
  rw [upMap_apply]
  have hsqrt : Real.sqrt (1 - ‖strip (z : EuclideanSpace ℝ (Fin (n+1)))‖ ^ 2)
      = (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n) := by
    rw [show 1 - ‖strip (z : EuclideanSpace ℝ (Fin (n+1)))‖ ^ 2
          = ((z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)) ^ 2 by linarith [hnorm]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hzt]
  rw [hsqrt, snocLp_strip]

lemma mem_range_downMap {z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1}
    (hz : z ∈ lowerHemi n) : z ∈ Set.range (downMap (n := n)) := by
  have hzt : (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n) ≤ 0 := hz
  have hz1 : ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := norm_eq_one_of_mem_sphere z.2
  have hnorm : ‖strip (z : EuclideanSpace ℝ (Fin (n+1)))‖ ^ 2
      = 1 - ((z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)) ^ 2 := by
    have h := snocLp_norm_sq (strip (z : EuclideanSpace ℝ (Fin (n+1))))
      ((z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n))
    rw [snocLp_strip, hz1] at h
    linarith [h]
  have hmem : strip (z : EuclideanSpace ℝ (Fin (n+1)))
      ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    nlinarith [norm_nonneg (strip (z : EuclideanSpace ℝ (Fin (n+1))))]
  refine ⟨⟨strip (z : EuclideanSpace ℝ (Fin (n+1))), hmem⟩, ?_⟩
  apply Subtype.ext
  rw [downMap_apply]
  have hsqrt : -Real.sqrt (1 - ‖strip (z : EuclideanSpace ℝ (Fin (n+1)))‖ ^ 2)
      = (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n) := by
    rw [show 1 - ‖strip (z : EuclideanSpace ℝ (Fin (n+1)))‖ ^ 2
          = ((z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)) ^ 2 by linarith [hnorm]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonpos hzt, neg_neg]
  rw [hsqrt, snocLp_strip]

lemma range_upMap : Set.range (upMap (n := n)) = upperHemi n := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩; exact upMap_mem_upperHemi y
  · intro hz; exact mem_range_upMap hz

lemma range_downMap : Set.range (downMap (n := n)) = lowerHemi n := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩; exact downMap_mem_lowerHemi y
  · intro hz; exact mem_range_downMap hz

lemma isClosed_upperHemi : IsClosed (upperHemi n) := by
  rw [show upperHemi n = {z | (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)) z ∈ Set.Ici 0} from rfl]
  exact isClosed_Ici.preimage (by fun_prop)

lemma isClosed_lowerHemi : IsClosed (lowerHemi n) := by
  rw [show lowerHemi n = {z | (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)) z ∈ Set.Iic 0} from rfl]
  exact isClosed_Iic.preimage (by fun_prop)

lemma upperHemi_union_lowerHemi : upperHemi n ∪ lowerHemi n = Set.univ := by
  rw [Set.eq_univ_iff_forall]; intro z
  rcases le_total ((z : EuclideanSpace ℝ (Fin (n+1))).ofLp (Fin.last n)) 0 with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma upperHemi_inter_lowerHemi : upperHemi n ∩ lowerHemi n = equator n := by
  ext z
  simp only [Set.mem_inter_iff, equator, upperHemi, lowerHemi, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨le_of_eq h.symm, le_of_eq h⟩

/-- On the boundary sphere the two graph parametrisations agree. -/
lemma upMap_eq_downMap_of_norm_eq_one {y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1}
    (hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1) :
    upMap y = downMap y := by
  apply Subtype.ext
  rw [upMap_apply, downMap_apply, hy]
  norm_num

/-- A closed-ball element of norm one, seen as a sphere element, has the same graph
parametrisation on the two hemispheres. -/
lemma upMap_sphere_eq_downMap (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    upMap ⟨(u : EuclideanSpace ℝ (Fin n)), Metric.sphere_subset_closedBall u.2⟩ =
      downMap ⟨(u : EuclideanSpace ℝ (Fin n)), Metric.sphere_subset_closedBall u.2⟩ := by
  refine upMap_eq_downMap_of_norm_eq_one ?_
  simpa using norm_eq_one_of_mem_sphere u.2

end Work.Morse
