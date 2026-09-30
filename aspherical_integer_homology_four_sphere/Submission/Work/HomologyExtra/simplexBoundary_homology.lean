import Mathlib
import Submission.Work.HomologyExtra.SimplexClass
import Submission.Work.HomologyExtra.simplexBand_homology_iso_equator
import Submission.Work.HomologyExtra.simplexNorthCap_contractible
import Submission.Work.HomologyExtra.simplexSouthCap_contractible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The homology of the boundary of the standard simplex

The boundary `∂Δⁿ⁺¹` of the standard `(n+1)`-simplex is the topological `n`-sphere.  This file
constructs the homeomorphism explicitly, by **radial projection from the barycentre** of the
simplex, and then reads off the homology of `∂Δⁿ⁺¹` from the (already known) homology of `Sⁿ`.

Concretely, `Δⁿ⁺¹` is the standard simplex on the `n+2` vertices `Fin (n+2)`, with barycentric
coordinates `wᵢ` and centre `c = (1/(n+2), …, 1/(n+2))`.  A point `x` of the boundary has a
vanishing coordinate, so `x - c ≠ 0`; dropping the last coordinate of `x - c` (which is
redundant, since the coordinates of `x - c` sum to zero) identifies the affine span of the
simplex with `ℝⁿ⁺¹`, and the map

* `toSph n x = (x - c) / ‖x - c‖`

is a continuous bijection `∂Δⁿ⁺¹ → Sⁿ` (its inverse is the point where the ray from `c` through
`x` leaves the simplex, `c + t·(x - c)` with `t` chosen so that the smallest barycentric
coordinate becomes `0`).  As `∂Δⁿ⁺¹` is compact and `Sⁿ` Hausdorff, this is a homeomorphism
(`exists_homeo_boundarySpace_sphere`).

* `simplexBoundary_homology` — `H_k(∂Δⁿ⁺¹; ℤ) ≅ ℤ` for `k = 0, n` and `= 0` otherwise
  (`n ≥ 1`), the statement needed for the aspherical homology 4-sphere.

The auxiliary material is `private`: it is an implementation detail of
`exists_homeo_boundarySpace_sphere`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-! ## Barycentric set-up -/

/-- The barycentric coordinate of the centre of `Δⁿ⁺¹`: `1/(n+2)`. -/
private def cw (n : ℕ) : ℝ := ((n + 2 : ℕ) : ℝ)⁻¹

private lemma cw_pos (n : ℕ) : 0 < cw n := by rw [cw]; positivity

private lemma cw_ne (n : ℕ) : cw n ≠ 0 := ne_of_gt (cw_pos n)

private lemma cw_card (n : ℕ) : ((n + 2 : ℕ) : ℝ) * cw n = 1 := by
  rw [cw, mul_inv_cancel₀ (by positivity)]

private lemma sum_const_fin {m : ℕ} (a : ℝ) : (∑ _ : Fin m, a) = (m : ℝ) * a := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The barycentric weights of a point of `∂Δⁿ⁺¹`. -/
private abbrev wt (n : ℕ) (x : ↥(boundarySpace (n + 1))) : Fin (n + 2) → ℝ :=
  fun i => (x : simplex (n + 1)).weights i

private lemma wt_nonneg (n : ℕ) (x : ↥(boundarySpace (n + 1))) (i : Fin (n + 2)) :
    0 ≤ wt n x i := Convexity.StdSimplex.weights_nonneg i

private lemma wt_sum (n : ℕ) (x : ↥(boundarySpace (n + 1))) : ∑ i, wt n x i = 1 :=
  Convexity.StdSimplex.total_of_fintype _

/-- The vector `x - c` of barycentric coordinates, in the ambient `ℝⁿ⁺²`. -/
private def rfull (n : ℕ) (x : ↥(boundarySpace (n + 1))) : Fin (n + 2) → ℝ :=
  fun i => wt n x i - cw n

/-- The first `n+1` coordinates of `x - c`: the last one is redundant.  This is the vector whose
direction is the radial projection of `x`. -/
private def rvec (n : ℕ) (x : ↥(boundarySpace (n + 1))) : Fin (n + 1) → ℝ :=
  fun i => rfull n x i.castSucc

private lemma rvec_eq (n : ℕ) (x : ↥(boundarySpace (n + 1))) (i : Fin (n + 1)) :
    rvec n x i = wt n x i.castSucc - cw n := rfl

private lemma rfull_sum (n : ℕ) (x : ↥(boundarySpace (n + 1))) : ∑ i, rfull n x i = 0 := by
  have h : ∑ i : Fin (n + 2), rfull n x i = ∑ i, wt n x i - ∑ _i : Fin (n + 2), cw n := by
    simp only [rfull]; rw [Finset.sum_sub_distrib]
  rw [h, wt_sum, sum_const_fin, cw_card]; ring

/-- A boundary point has a vanishing coordinate, hence `min (x - c) = -1/(n+2)`. -/
private lemma rfull_min (n : ℕ) (x : ↥(boundarySpace (n + 1))) :
    ∃ i, rfull n x i = -cw n := by
  obtain ⟨j, hj⟩ := x.2
  have hj' : wt n x j = 0 := hj
  exact ⟨j, by rw [rfull, hj']; ring⟩

private lemma rfull_ge (n : ℕ) (x : ↥(boundarySpace (n + 1))) (i : Fin (n + 2)) :
    -cw n ≤ rfull n x i := by
  rw [rfull]; linarith [wt_nonneg n x i]

private lemma rfull_min_eq (n : ℕ) (x : ↥(boundarySpace (n + 1))) :
    (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (rfull n x) = -cw n := by
  refine le_antisymm ?_ ?_
  · obtain ⟨j, hj⟩ := rfull_min n x
    rw [← hj]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  · exact Finset.le_inf' _ _ (fun i _ => rfull_ge n x i)

/-- The last coordinate of `x - c` is minus the sum of the first `n+1`. -/
private lemma rfull_last (n : ℕ) (x : ↥(boundarySpace (n + 1))) :
    rfull n x (Fin.last (n + 1)) = -∑ i : Fin (n + 1), rvec n x i := by
  have h := rfull_sum n x
  rw [Fin.sum_univ_castSucc (fun i => rfull n x i)] at h
  have h' : (∑ i : Fin (n + 1), rvec n x i) = ∑ i : Fin (n + 1), rfull n x i.castSucc := by
    simp only [rvec]
  rw [h']; linarith

/-- `x - c ≠ 0` for a boundary point: all barycentric coordinates of `x - c` would have to
vanish, so all barycentric coordinates of `x` would be `1/(n+2)` none of which is zero. -/
private lemma rvec_ne_zero (n : ℕ) (x : ↥(boundarySpace (n + 1))) : rvec n x ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := x.2
  have hj' : wt n x j = 0 := hj
  have hcast : ∀ i : Fin (n + 1), wt n x i.castSucc = cw n := by
    intro i
    have h1 := congrFun h i
    rw [rvec_eq n x i, Pi.zero_apply] at h1
    linarith
  have hsum : (∑ i : Fin (n + 1), rfull n x i.castSucc) + rfull n x (Fin.last (n + 1)) = 0 := by
    rw [← Fin.sum_univ_castSucc (fun i => rfull n x i)]
    exact rfull_sum n x
  have h1 : ∑ i : Fin (n + 1), rfull n x i.castSucc = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [rfull]
    linarith [hcast i]
  have hlast0 : rfull n x (Fin.last (n + 1)) = 0 := by linarith
  have hlast : wt n x (Fin.last (n + 1)) = cw n := by
    rw [rfull] at hlast0
    linarith
  rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | hjl
  · rw [hcast k] at hj'
    exact cw_ne n hj'
  · rw [hjl, hlast] at hj'
    exact cw_ne n hj'

/-! ## The radial projection as a map to the sphere -/

/-- The vector `x - c` restricted to the first `n+1` coordinates, as an element of `ℝⁿ⁺¹`. -/
private def uvec (n : ℕ) (x : ↥(boundarySpace (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (rvec n x)

private lemma uvec_ne_zero (n : ℕ) (x : ↥(boundarySpace (n + 1))) : uvec n x ≠ 0 := by
  intro h
  refine rvec_ne_zero n x ?_
  have h1 := congrArg WithLp.ofLp h
  simpa [uvec] using h1

/-- **The radial projection of the simplex boundary**, as a map to the unit sphere of `ℝⁿ⁺¹`. -/
private def toSph (n : ℕ) (x : ↥(boundarySpace (n + 1))) :
    ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨(‖uvec n x‖)⁻¹ • uvec n x, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact norm_smul_inv_norm (uvec_ne_zero n x)⟩

private lemma continuous_uvec (n : ℕ) :
    Continuous (fun x : ↥(boundarySpace (n + 1)) => uvec n x) := by
  have h : Continuous (fun x : ↥(boundarySpace (n + 1)) => rvec n x) :=
    continuous_pi (fun i => by
      have hw : Continuous (fun x : ↥(boundarySpace (n + 1)) => wt n x i.castSucc) :=
        (Convexity.StdSimplex.continuous_weights_apply ℝ i.castSucc).comp continuous_subtype_val
      exact hw.sub continuous_const)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp h

private lemma continuous_toSph (n : ℕ) : Continuous (toSph n) := by
  apply Continuous.subtype_mk
  have hf := continuous_uvec n
  exact (hf.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (uvec_ne_zero n x))).smul hf

/-! ## The inverse: the point where the ray leaves the simplex -/

/-- Reading the coordinates of a point of the sphere `Sⁿ ⊆ ℝⁿ⁺¹` as a function. -/
private abbrev yf (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Fin (n + 1) → ℝ := (y : EuclideanSpace ℝ (Fin (n + 1))).ofLp

private lemma y_norm (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
  have h := Metric.mem_sphere.mp y.2
  rwa [dist_eq_norm, sub_zero] at h

/-- The direction of a point of the sphere, written in the `n+2` barycentric coordinates: the
last coordinate is chosen so that the sum is zero. -/
private def hVec (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Fin (n + 2) → ℝ :=
  Fin.lastCases (-∑ i : Fin (n + 1), yf n y i) (fun i => yf n y i)

private lemma hVec_castSucc (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (i : Fin (n + 1)) : hVec n y i.castSucc = yf n y i := by simp [hVec]

private lemma hVec_last (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    hVec n y (Fin.last (n + 1)) = -∑ i : Fin (n + 1), yf n y i := by simp [hVec]

private lemma hVec_sum (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ∑ i : Fin (n + 2), hVec n y i = 0 := by
  rw [Fin.sum_univ_castSucc (fun i => hVec n y i), hVec_last]
  simp only [hVec_castSucc]
  ring

private lemma hVec_ne_zero (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    hVec n y ≠ 0 := by
  intro h
  have hyf : (y : EuclideanSpace ℝ (Fin (n + 1))).ofLp = 0 := by
    funext i
    have h1 := congrFun h i.castSucc
    rw [hVec_castSucc, Pi.zero_apply] at h1
    exact h1
  have hy0 : (y : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
    rw [← WithLp.toLp_ofLp 2 (y : EuclideanSpace ℝ (Fin (n + 1))), hyf, WithLp.toLp_zero]
  have hnorm := y_norm n y
  rw [hy0, norm_zero] at hnorm
  norm_num at hnorm

/-- The parameter `t` of the exit point `c + t·h` of the ray from the centre in direction `h`. -/
private def tOf (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) : ℝ :=
  -cw n / (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (hVec n y)

private lemma inf'neg_lt_zero (n : ℕ)
    (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (hVec n y) < 0 := by
  obtain ⟨i, hi⟩ : ∃ i, hVec n y i < 0 := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin (n + 2))), hVec n y i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun i _ => hcon i)).mp
        (hVec_sum n y)
    exact hVec_ne_zero n y (funext (fun i => hzero i (Finset.mem_univ i)))
  calc (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (hVec n y)
      ≤ hVec n y i := Finset.inf'_le _ (Finset.mem_univ i)
    _ < 0 := hi

private lemma tOf_mul (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    tOf n y * (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (hVec n y)
      = -cw n := by
  rw [tOf, div_mul_cancel₀ _ (ne_of_lt (inf'neg_lt_zero n y))]

private lemma tOf_pos (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    0 < tOf n y := by
  rw [tOf]
  exact div_pos_of_neg_of_neg (neg_lt_zero.mpr (cw_pos n)) (inf'neg_lt_zero n y)

/-- The barycentric coordinates of the exit point of the ray from the centre through `y`. -/
private def wtOf (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    Fin (n + 2) → ℝ :=
  fun i => cw n + tOf n y * hVec n y i

private lemma wtOf_nonneg (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (i : Fin (n + 2)) : 0 ≤ wtOf n y i := by
  have h1 : (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (hVec n y)
      ≤ hVec n y i := Finset.inf'_le _ (Finset.mem_univ i)
  have h2 := tOf_mul n y
  have h3 := tOf_pos n y
  have h4 : tOf n y * (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (hVec n y)
      ≤ tOf n y * hVec n y i := mul_le_mul_of_nonneg_left h1 (le_of_lt h3)
  rw [wtOf]
  linarith

private lemma wtOf_sum (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ∑ i : Fin (n + 2), wtOf n y i = 1 := by
  have h : ∀ i : Fin (n + 2), wtOf n y i = cw n + tOf n y * hVec n y i := fun i => rfl
  rw [show (∑ i : Fin (n + 2), wtOf n y i) =
      ∑ i : Fin (n + 2), (cw n + tOf n y * hVec n y i) from
        Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hVec_sum, mul_zero, add_zero, sum_const_fin,
    cw_card]

private lemma wtOf_zero (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ∃ i, wtOf n y i = 0 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin (n + 2))))
    Finset.univ_nonempty (hVec n y)
  refine ⟨i, ?_⟩
  rw [wtOf, ← hi, tOf_mul, add_neg_cancel]

/-- A standard simplex element with prescribed barycentric coordinates. -/
private def simplexOfWts (n : ℕ) (g : Fin (n + 2) → ℝ) (h1 : ∀ i, 0 ≤ g i)
    (h2 : ∑ i, g i = 1) : Convexity.StdSimplex ℝ (Fin (n + 2)) :=
  ⟨Finsupp.equivFunOnFinite.symm g, fun i => by simpa using h1 i,
    by simpa [Finsupp.sum_fintype] using h2⟩

private lemma simplexOfWts_weights (n : ℕ) (g : Fin (n + 2) → ℝ) (h1 : ∀ i, 0 ≤ g i)
    (h2 : ∑ i, g i = 1) (i : Fin (n + 2)) : (simplexOfWts n g h1 h2).weights i = g i := by
  simp [simplexOfWts]

/-- **The inverse of the radial projection**: the point of `∂Δⁿ⁺¹` where the ray from the
centre in the direction of `y` leaves the simplex. -/
private def toBd (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    ↥(boundarySpace (n + 1)) :=
  ⟨simplexOfWts n (wtOf n y) (wtOf_nonneg n y) (wtOf_sum n y),
    by obtain ⟨i, hi⟩ := wtOf_zero n y
       exact ⟨i, by rw [simplexOfWts_weights]; exact hi⟩⟩

private lemma wt_toBd (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (i : Fin (n + 2)) : wt n (toBd n y) i = wtOf n y i :=
  simplexOfWts_weights n (wtOf n y) (wtOf_nonneg n y) (wtOf_sum n y) i

private lemma rvec_toBd (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    rvec n (toBd n y) = tOf n y • yf n y := by
  funext i
  rw [rvec_eq, wt_toBd, wtOf, hVec_castSucc, Pi.smul_apply]
  ring

private lemma uvec_toBd (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    uvec n (toBd n y) = tOf n y • (y : EuclideanSpace ℝ (Fin (n + 1))) := by
  rw [uvec, rvec_toBd, WithLp.toLp_smul, WithLp.toLp_ofLp]

private lemma toSph_toBd (n : ℕ) (y : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    toSph n (toBd n y) = y := by
  apply Subtype.ext
  have hnorm : ‖uvec n (toBd n y)‖ = tOf n y := by
    rw [uvec_toBd, norm_smul, y_norm n y, mul_one, Real.norm_of_nonneg (le_of_lt (tOf_pos n y))]
  show (‖uvec n (toBd n y)‖)⁻¹ • uvec n (toBd n y) = (y : EuclideanSpace ℝ (Fin (n + 1)))
  rw [hnorm, uvec_toBd, inv_smul_smul₀ (ne_of_gt (tOf_pos n y))]

/-! ## The radial projection is injective -/

/-- Scaling a finite infimum. -/
private lemma inf'_mul_const {m : ℕ} (a : ℝ) (ha : 0 ≤ a) (f : Fin (m + 1) → ℝ) :
    (Finset.univ : Finset (Fin (m + 1))).inf' Finset.univ_nonempty (fun i => a * f i) =
      a * (Finset.univ : Finset (Fin (m + 1))).inf' Finset.univ_nonempty f := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin (m + 1))))
      Finset.univ_nonempty f
    rw [hi]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  · exact Finset.le_inf' _ _
      (fun i _ => mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ i)) ha)

private lemma toSph_injective (n : ℕ) : Function.Injective (toSph n) := by
  intro x x' h
  have hv : (‖uvec n x‖)⁻¹ • uvec n x = (‖uvec n x'‖)⁻¹ • uvec n x' := by
    have h1 := congrArg Subtype.val h
    simpa [toSph] using h1
  have hfun : ∀ i : Fin (n + 1),
      (‖uvec n x‖)⁻¹ * rvec n x i = (‖uvec n x'‖)⁻¹ * rvec n x' i := by
    intro i
    have h1 := congrFun (congrArg WithLp.ofLp hv) i
    simpa [uvec] using h1
  have hx_ne : ‖uvec n x‖ ≠ 0 := norm_ne_zero_iff.mpr (uvec_ne_zero n x)
  have hx'_ne : ‖uvec n x'‖ ≠ 0 := norm_ne_zero_iff.mpr (uvec_ne_zero n x')
  set lam : ℝ := ‖uvec n x‖ / ‖uvec n x'‖ with hlam
  have hpos : 0 < lam := div_pos (norm_pos_iff.mpr (uvec_ne_zero n x))
    (norm_pos_iff.mpr (uvec_ne_zero n x'))
  have hr : ∀ i : Fin (n + 1), rvec n x i = lam * rvec n x' i := by
    intro i
    have h1 := hfun i
    calc rvec n x i
        = (‖uvec n x‖) * ((‖uvec n x‖)⁻¹ * rvec n x i) :=
          (mul_inv_cancel_left₀ hx_ne (rvec n x i)).symm
      _ = (‖uvec n x‖) * ((‖uvec n x'‖)⁻¹ * rvec n x' i) := by rw [h1]
      _ = lam * rvec n x' i := by rw [hlam]; field_simp
  have hfull : ∀ i : Fin (n + 2), rfull n x i = lam * rfull n x' i := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 := hr j
      simpa [rvec] using h1
    · rw [rfull_last n x, rfull_last n x']
      have hs : (∑ j : Fin (n + 1), rvec n x j) = lam * ∑ j : Fin (n + 1), rvec n x' j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => hr j)
      rw [hs]; ring
  have hmin : lam = 1 := by
    have h1 : (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (rfull n x) =
        lam * (Finset.univ : Finset (Fin (n + 2))).inf' Finset.univ_nonempty (rfull n x') := by
      rw [show rfull n x = (fun i => lam * rfull n x' i) from funext hfull]
      exact inf'_mul_const lam (le_of_lt hpos) (rfull n x')
    rw [rfull_min_eq n x, rfull_min_eq n x'] at h1
    have h2 : cw n * lam = cw n * 1 := by linarith [h1]
    exact mul_left_cancel₀ (cw_ne n) h2
  have hr1 : ∀ i : Fin (n + 1), rvec n x i = rvec n x' i := by
    intro i; rw [hr i, hmin, one_mul]
  have hfull1 : rfull n x = rfull n x' := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 := hr1 j
      simpa [rvec] using h1
    · rw [rfull_last n x, rfull_last n x']
      exact congrArg Neg.neg (Finset.sum_congr rfl (fun j _ => hr1 j))
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  ext i
  have h1 := congrFun hfull1 i
  simp only [rfull] at h1
  show wt n x i = wt n x' i
  linarith

/-! ## The homeomorphism and the homology of the boundary -/

/-- **The boundary of the standard `(n+1)`-simplex is homeomorphic to the `n`-sphere.** -/
theorem exists_homeo_boundarySpace_sphere (n : ℕ) :
    Nonempty (↥(boundarySpace (n + 1)) ≃ₜ ↥(Work.Homology.Sph n)) := by
  haveI : CompactSpace ↥(boundarySpace (n + 1)) :=
    isCompact_iff_compactSpace.mp (isClosed_simplexBoundary (n + 1)).isCompact
  have hbij : Function.Bijective (toSph n) :=
    ⟨toSph_injective n, fun y => ⟨toBd n y, toSph_toBd n y⟩⟩
  have hh : IsHomeomorph (toSph n) :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨continuous_toSph n, hbij⟩
  exact ⟨IsHomeomorph.homeomorph (toSph n) hh⟩

/-- **The homology of `∂Δⁿ⁺¹` is the homology of `Sⁿ`**: `ℤ` in degrees `0` and `n`, and `0`
otherwise (`n ≥ 1`). -/
theorem simplexBoundary_homology (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod k
        (Work.HomologyExtra.boundarySpace (n + 1)) ≅
      (if k = 0 ∨ k = n then Work.Homology.ZMod else ModuleCat.of ℤ PUnit)) := by
  obtain ⟨e⟩ := exists_homeo_boundarySpace_sphere n
  obtain ⟨i₁⟩ := Work.Homology.SingHomologyHomeomorph (X := boundarySpace (n + 1))
    (Y := Work.Homology.Sph n) Work.Homology.ZMod k e
  obtain ⟨i₂⟩ := Work.Homology.singHomology_sphere n k hn
  exact ⟨i₁ ≪≫ i₂⟩

/-- The same homeomorphism in the `∂Δⁿ = Sⁿ⁻¹` indexing (`n ≥ 1`). -/
theorem exists_homeo_boundarySpace_sphere' (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (↥(boundarySpace n) ≃ₜ ↥(Work.Homology.Sph (n - 1))) := by
  have h := exists_homeo_boundarySpace_sphere (n - 1)
  exact (Nat.sub_add_cancel hn) ▸ h

/-- **The homology of `∂Δⁿ ≅ Sⁿ⁻¹`** (`n ≥ 2`): `ℤ` in degrees `0` and `n-1`, zero otherwise.
This is the form in which the statement is used in a Mayer–Vietoris induction on `n`. -/
theorem boundarySpace_homology (n k : ℕ) (hn : 2 ≤ n) :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod k (boundarySpace n) ≅
      (if k = 0 ∨ k = n - 1 then Work.Homology.ZMod else ModuleCat.of ℤ PUnit)) := by
  have h := simplexBoundary_homology (n - 1) k (by omega)
  exact (Nat.sub_add_cancel (by omega : 1 ≤ n)) ▸ h

end

end Work.HomologyExtra
