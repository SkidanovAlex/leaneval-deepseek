import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.ThomBordism.Grassmann.Clamp.LpcCriterion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Coning a free null-homotopy of a sphere map

`Work.Serre.CWModel.sphereExtend`: a continuous map `φ : Sⁿ → X` which is *freely* null-homotopic
(the homotopy `H` from `φ` to the constant map at `x` is given as data) extends over the model
cell `Dⁿ⁺¹`.

The construction is the classical "cone" one.  Write `S` for the model sphere
`Work.RatHurewicz.cellSphere n = S^{n+1} ⊆ ℝ^{n+2}` and `D` for the model cell
`Work.RatHurewicz.cellDisk n = D^{n+2}`, so that the boundary inclusion is
`Work.RatHurewicz.cellSphereToDisk n`.  The map

  `q : I × S → D`,   `q (t, z) = (1 - t) • z`

exhibits `D` as the cone on `S`: it is continuous and surjective, and since `I × S` is compact and
`D` is Hausdorff it is a closed map, hence a **quotient map** (`cellConeMap_isQuotientMap`).

A homotopy `H` from `φ` to the constant map at `x` is *constant on the fibres* of `q`
(`cellConeMap_factorsThrough`): the fibre of `q` over a point of the interior is a single point,
while the fibre over the centre `0` is the top slice `{1} × S`, on which `H` is constantly `x` by
hypothesis.  Hence `H` descends along the quotient map to a continuous `G : D → X`
(`Topology.IsQuotientMap.lift`), and

  `G (cellSphereToDisk n z) = G (q (0, z)) = H (0, z) = φ z`,

which is the required extension.

This is the step that converts "null-homotopic" into "extends" in the CW models
(`Submission/Work/Drive/SERRE_BLUEPRINT.md`); it needs no hypothesis on `X` beyond the homotopy
itself.  The same construction (with the index shifted by one) is used in
`Work.RatHurewicz.freeNull_implies_basedNull`.
-/

open scoped unitInterval Topology

namespace Work.Serre.CWModel

noncomputable section

open Work.RatHurewicz

variable {n : ℕ}

/-- A point of the model sphere `S^{n+1} ⊆ ℝ^{n+2}` has norm `1`. -/
theorem norm_coe_cellSphere (z : cellSphere n) : ‖(z : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := by
  have h := Metric.mem_sphere.mp z.2
  rwa [dist_eq_norm, sub_zero] at h

/-- **The cone parametrisation of the model cell** `Dⁿ⁺¹`: the continuous map
`q (t, z) = (1 - t) • z` from `I × Sⁿ` onto `cellDisk n`.  It exhibits the model cell as the cone
on its boundary sphere. -/
def cellConeMap (n : ℕ) : C(unitInterval × cellSphere n, cellDisk n) where
  toFun z := ⟨(1 - (z.1 : ℝ)) • (z.2 : EuclideanSpace ℝ (Fin (n + 2))), by
    have hz : ‖(z.2 : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := norm_coe_cellSphere z.2
    have h1t : ‖((1 : ℝ) - (z.1 : ℝ))‖ = 1 - (z.1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [z.1.2.1, z.1.2.2])]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, h1t, hz, mul_one]
    linarith [z.1.2.1, z.1.2.2]⟩
  continuous_toFun := by fun_prop

@[simp] theorem cellConeMap_apply (n : ℕ) (t : unitInterval) (z : cellSphere n) :
    ((cellConeMap n (t, z) : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2))) =
      (1 - (t : ℝ)) • (z : EuclideanSpace ℝ (Fin (n + 2))) := rfl

/-- On the bottom slice `t = 0` the cone parametrisation is the boundary inclusion. -/
theorem cellConeMap_zero (n : ℕ) (z : cellSphere n) :
    cellConeMap n (0, z) = cellSphereToDisk n z := by
  apply Subtype.ext
  show ((cellConeMap n (0, z) : cellDisk n) : EuclideanSpace ℝ (Fin (n + 2))) =
    (z : EuclideanSpace ℝ (Fin (n + 2)))
  rw [cellConeMap_apply]
  simp

/-- The cone parametrisation is surjective: every point of the closed ball of radius `1` is
`(1 - t) • z` for some `t : I` and some `z` of norm `1`. -/
theorem cellConeMap_surjective (n : ℕ) : Function.Surjective (cellConeMap n) := by
  classical
  have hScomp : CompactSpace (cellSphere n) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
  let pt : cellSphere n := ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    simp⟩
  rintro ⟨u, hu⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hu
  by_cases hu0 : u = 0
  · refine ⟨((1 : unitInterval), pt), ?_⟩
    apply Subtype.ext
    show (1 - ((1 : unitInterval) : ℝ)) • (pt : EuclideanSpace ℝ (Fin (n + 2))) = u
    rw [hu0]; norm_num
  · have hnormu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    let ω : cellSphere n := ⟨‖u‖⁻¹ • u, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg u), inv_mul_cancel₀ hnormu]⟩
    have htmem : (0 : ℝ) ≤ 1 - ‖u‖ ∧ 1 - ‖u‖ ≤ 1 :=
      ⟨by linarith [norm_nonneg u, hu], by linarith [norm_nonneg u, hu]⟩
    let t : unitInterval := ⟨1 - ‖u‖, htmem⟩
    refine ⟨(t, ω), ?_⟩
    apply Subtype.ext
    have ht : (t : ℝ) = 1 - ‖u‖ := rfl
    show (1 - (t : ℝ)) • (ω : EuclideanSpace ℝ (Fin (n + 2))) = u
    have hs : (1 : ℝ) - (1 - ‖u‖) = ‖u‖ := by ring
    rw [ht, hs]
    show ‖u‖ • (‖u‖⁻¹ • u) = u
    rw [smul_inv_smul₀ hnormu u]

/-- The cone parametrisation is a closed map (compact source, Hausdorff target). -/
theorem cellConeMap_isClosedMap (n : ℕ) : IsClosedMap (cellConeMap n) := by
  have hScomp : CompactSpace (cellSphere n) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
  exact fun s hs => (hs.isCompact.image (cellConeMap n).continuous).isClosed

/-- **The cone parametrisation is a quotient map.** -/
theorem cellConeMap_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (⇑(cellConeMap n)) :=
  (cellConeMap_isClosedMap n).isQuotientMap (cellConeMap n).continuous
    (cellConeMap_surjective n)

/-- **A free null-homotopy is constant on the fibres of the cone parametrisation.**  The fibres of
`cellConeMap n` over the interior of the cell are singletons, and the fibre over the centre is the
top slice `{1} × S`, on which `H` is constantly `x`. -/
theorem cellConeMap_factorsThrough {X : Type} [TopologicalSpace X]
    (H : C(unitInterval × cellSphere n, X)) (x : X) (h1 : ∀ z, H (1, z) = x) :
    Function.FactorsThrough H (⇑(cellConeMap n)) := by
  intro a b hab
  have hval : (1 - (a.1 : ℝ)) • (a.2 : EuclideanSpace ℝ (Fin (n + 2)))
      = (1 - (b.1 : ℝ)) • (b.2 : EuclideanSpace ℝ (Fin (n + 2))) := by
    have h := congrArg (fun q : cellDisk n => (q : EuclideanSpace ℝ (Fin (n + 2)))) hab
    simpa [cellConeMap] using h
  have hta : ‖(a.2 : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := norm_coe_cellSphere a.2
  have htb : ‖(b.2 : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 := norm_coe_cellSphere b.2
  -- the radial parameter `1 - t` is determined by the image
  have ht_eq : (a.1 : ℝ) = (b.1 : ℝ) := by
    have h := congrArg norm hval
    rw [norm_smul, norm_smul, hta, htb, mul_one, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [a.1.2.1, a.1.2.2]),
      abs_of_nonneg (by linarith [b.1.2.1, b.1.2.2])] at h
    linarith
  have ht : a.1 = b.1 := Subtype.ext ht_eq
  by_cases ha1 : a.1 = 1
  · -- both parameters lie on the top slice, where the homotopy is constant
    have hb1 : b.1 = 1 := by rw [← ht]; exact ha1
    have ha' : H a = x := by
      change H (a.1, a.2) = x
      rw [ha1]; exact h1 a.2
    have hb' : H b = x := by
      change H (b.1, b.2) = x
      rw [hb1]; exact h1 b.2
    rw [ha', hb']
  · -- otherwise the sphere coordinate is determined as well
    have ha1ne : (a.1 : ℝ) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hne : (1 : ℝ) - (a.1 : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1ne)
    have hscale : (1 : ℝ) - (b.1 : ℝ) = 1 - (a.1 : ℝ) := by rw [ht_eq]
    rw [hscale] at hval
    have hs_eq : (a.2 : cellSphere n) = b.2 := by
      apply Subtype.ext
      have h2 := congrArg (fun w => ((1 - (a.1 : ℝ))⁻¹) • w) hval
      simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using h2
    exact congrArg H (Prod.ext ht hs_eq)

/-- **Null-homotopic maps of the model sphere extend over the model cell.**

Given `φ : Sⁿ → X` and a homotopy `H` from `φ` to the constant map at `x`, the map
`φ` extends over the model cell `Dⁿ⁺¹`; the extension is the descent of `H` along the cone
parametrisation. -/
theorem sphereExtend {n : ℕ} {X : Type} [TopologicalSpace X]
    (φ : C(Work.RatHurewicz.cellSphere n, X))
    (H : C(unitInterval × Work.RatHurewicz.cellSphere n, X)) (x : X)
    (h0 : ∀ z, H (0, z) = φ z) (h1 : ∀ z, H (1, z) = x) :
    ∃ G : C(Work.RatHurewicz.cellDisk n, X),
      G.comp (Work.RatHurewicz.cellSphereToDisk n) = φ := by
  refine ⟨(cellConeMap_isQuotientMap n).lift H (cellConeMap_factorsThrough H x h1), ?_⟩
  have hcomp := Topology.IsQuotientMap.lift_comp (cellConeMap_isQuotientMap n) H
    (cellConeMap_factorsThrough H x h1)
  ext z
  show (cellConeMap_isQuotientMap n).lift H (cellConeMap_factorsThrough H x h1)
      (Work.RatHurewicz.cellSphereToDisk n z) = φ z
  calc (cellConeMap_isQuotientMap n).lift H (cellConeMap_factorsThrough H x h1)
        (Work.RatHurewicz.cellSphereToDisk n z)
      = (cellConeMap_isQuotientMap n).lift H (cellConeMap_factorsThrough H x h1)
        (cellConeMap n (0, z)) := by rw [cellConeMap_zero]
    _ = ((cellConeMap_isQuotientMap n).lift H (cellConeMap_factorsThrough H x h1)).comp
        (cellConeMap n) (0, z) := rfl
    _ = H (0, z) := by rw [hcomp]
    _ = φ z := h0 z

end

end Work.Serre.CWModel
