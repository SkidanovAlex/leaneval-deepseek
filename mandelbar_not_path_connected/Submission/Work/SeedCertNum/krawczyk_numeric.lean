/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Krawczyk's criterion, numerical form

This is the numerical (Krawczyk) certification step of the `SeedCertNum` contract: from an
explicit enclosure of the Jacobian of `f` on the closed ball `B(u₀,r)` (by a fixed matrix `Ac`
with error `ε`), an approximate inverse `M` of `Ac` (`‖1 - M∘Ac‖ ≤ α`, `‖M‖ ≤ β`) and the
defect `‖M (f u₀)‖ ≤ η`, the ball contains exactly one zero of `f`, provided
`(α + β ε) r + η < r`.

The proof is Krawczyk's: the Newton-type map `G u = u - M (f u)` maps the ball strictly into
itself and is a contraction there with constant `α + β ε < 1`; by Banach's fixed point theorem
it has a unique fixed point in the ball, and (using that `M` is injective, which follows from
`‖1 - M∘Ac‖ < 1` and finite-dimensionality of `ℝ³`) the fixed points of `G` in the ball are
exactly the zeros of `f`.

The analytic input is the mean value inequality
`Convex.norm_image_sub_le_of_norm_fderiv_le'` applied to `f` with `φ = Ac`.
-/
import Mathlib
import Submission.Work.SeedCertNum.Jet1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

local notation "E3" => Work.SeedCert.E3

open Metric

theorem krawczyk_numeric {f : Work.SeedCert.E3 → Work.SeedCert.E3} {u₀ : Work.SeedCert.E3}
    {r ε η α β : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hdiff : ∀ u ∈ Metric.closedBall u₀ r, DifferentiableAt ℝ f u)
    {Ac M : Work.SeedCert.E3 →L[ℝ] Work.SeedCert.E3}
    (hJac : ∀ u ∈ Metric.closedBall u₀ r, ‖fderiv ℝ f u - Ac‖ ≤ ε)
    (hA : ‖(1 : Work.SeedCert.E3 →L[ℝ] Work.SeedCert.E3) - M.comp Ac‖ ≤ α)
    (hB : ‖M‖ ≤ β) (hEta : ‖M (f u₀)‖ ≤ η)
    (hball : (α + β * ε) * r + η < r) :
    ∃! u ∈ Metric.closedBall u₀ r, f u = 0 := by
  have hr0 : 0 ≤ r := le_of_lt hr
  have hκ0 : 0 ≤ α + β * ε := add_nonneg hα (mul_nonneg hβ hε)
  have hκlt : α + β * ε < 1 := by
    have h1 : (α + β * ε) * r < r := by linarith
    nlinarith [h1, hr, hκ0]
  have hαlt : α < 1 :=
    lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg hβ hε)) hκlt
  -- ### `M` is injective
  --
  -- `M ∘ Ac = 1 - T` with `‖T‖ ≤ α < 1` is injective; in finite dimension it is then
  -- surjective, hence `M` is surjective and (again by finite dimension) injective.
  have hinjM : Function.Injective M := by
    have hker : ∀ v : E3, M (Ac v) = 0 → v = 0 := by
      intro v hv
      have h1 : ((1 : E3 →L[ℝ] E3) - M.comp Ac) v = v := by
        simp only [sub_apply, ContinuousLinearMap.comp_apply,
          one_apply_eq_self, hv, sub_zero]
      have h2 : ‖v‖ ≤ α * ‖v‖ := by
        calc ‖v‖ = ‖((1 : E3 →L[ℝ] E3) - M.comp Ac) v‖ := by rw [h1]
          _ ≤ ‖(1 : E3 →L[ℝ] E3) - M.comp Ac‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ α * ‖v‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg v)
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
    have hinj_comp : Function.Injective (M.comp Ac) := by
      intro v w hvw
      have hvw' : M (Ac v) = M (Ac w) := by
        simpa only [ContinuousLinearMap.comp_apply] using hvw
      have hv : M (Ac (v - w)) = 0 := by
        rw [ContinuousLinearMap.map_sub Ac v w, ContinuousLinearMap.map_sub M (Ac v) (Ac w),
          hvw', sub_self]
      exact sub_eq_zero.mp (hker (v - w) hv)
    have hsurj : Function.Surjective (M.comp Ac) :=
      (LinearMap.injective_iff_surjective (f := (M.comp Ac : E3 →ₗ[ℝ] E3))).mp hinj_comp
    have hsurjM : Function.Surjective M := by
      intro y
      obtain ⟨w, hw⟩ := hsurj y
      exact ⟨Ac w, hw⟩
    exact (LinearMap.injective_iff_surjective (f := (M : E3 →ₗ[ℝ] E3))).mpr hsurjM
  -- ### The Krawczyk map
  let G : E3 → E3 := fun u => u - M (f u)
  have hGid : ∀ x y : E3, G x - G y = ((1 : E3 →L[ℝ] E3) - M.comp Ac) (x - y)
      - M (f x - f y - Ac (x - y)) := by
    intro x y
    have h1 : G x - G y = (x - y) - M (f x - f y) := by
      simp only [G]
      rw [ContinuousLinearMap.map_sub]
      abel
    rw [h1]
    have h2 : M (f x - f y) = M (Ac (x - y)) + M (f x - f y - Ac (x - y)) := by
      nth_rewrite 1 [show f x - f y = Ac (x - y) + (f x - f y - Ac (x - y)) from by abel]
      rw [map_add]
    rw [h2]
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      one_apply_eq_self]
    abel
  -- ### Mean value inequality
  have hmv : ∀ x ∈ Metric.closedBall u₀ r, ∀ y ∈ Metric.closedBall u₀ r,
      ‖f y - f x - Ac (y - x)‖ ≤ ε * ‖y - x‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := f) (φ := Ac) (C := ε)
      (s := Metric.closedBall u₀ r) (x := x) (y := y) hdiff hJac (convex_closedBall u₀ r) hx hy
  -- ### `G` is a contraction with constant `α + β ε`
  have hcontra : ∀ x ∈ Metric.closedBall u₀ r, ∀ y ∈ Metric.closedBall u₀ r,
      ‖G x - G y‖ ≤ (α + β * ε) * ‖x - y‖ := by
    intro x hx y hy
    have hm := hmv y hy x hx
    have hb1 : ‖((1 : E3 →L[ℝ] E3) - M.comp Ac) (x - y)‖ ≤ α * ‖x - y‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    have hb2 : ‖M (f x - f y - Ac (x - y))‖ ≤ β * (ε * ‖x - y‖) :=
      calc ‖M (f x - f y - Ac (x - y))‖ ≤ ‖M‖ * ‖f x - f y - Ac (x - y)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ β * ‖f x - f y - Ac (x - y)‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
        _ ≤ β * (ε * ‖x - y‖) := mul_le_mul_of_nonneg_left hm hβ
    calc ‖G x - G y‖
        = ‖((1 : E3 →L[ℝ] E3) - M.comp Ac) (x - y) - M (f x - f y - Ac (x - y))‖ := by
          rw [hGid x y]
      _ ≤ ‖((1 : E3 →L[ℝ] E3) - M.comp Ac) (x - y)‖ + ‖M (f x - f y - Ac (x - y))‖ :=
          norm_sub_le _ _
      _ ≤ α * ‖x - y‖ + β * (ε * ‖x - y‖) := add_le_add hb1 hb2
      _ = (α + β * ε) * ‖x - y‖ := by ring
  have hlip : ∀ x ∈ Metric.closedBall u₀ r, ∀ y ∈ Metric.closedBall u₀ r,
      dist (G x) (G y) ≤ (α + β * ε) * dist x y := by
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    exact hcontra x hx y hy
  -- ### `G` maps the ball strictly into itself
  have hGball : ∀ u ∈ Metric.closedBall u₀ r, G u ∈ Metric.closedBall u₀ r := by
    intro u hu
    have hu₀ : u₀ ∈ Metric.closedBall u₀ r := Metric.mem_closedBall_self hr0
    have hdu : ‖u - u₀‖ ≤ r := by
      have h := hu
      rwa [Metric.mem_closedBall, dist_eq_norm] at h
    have h1 : ‖G u - G u₀‖ ≤ (α + β * ε) * r :=
      (hcontra u hu u₀ hu₀).trans (mul_le_mul_of_nonneg_left hdu hκ0)
    have h2 : ‖G u₀ - u₀‖ ≤ η := by
      have h3 : G u₀ - u₀ = -M (f u₀) := by simp only [G]; abel
      rw [h3, norm_neg]
      exact hEta
    have hsplit : (G u - G u₀) + (G u₀ - u₀) = G u - u₀ := by abel
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt (calc ‖G u - u₀‖ = ‖(G u - G u₀) + (G u₀ - u₀)‖ := by rw [hsplit]
      _ ≤ ‖G u - G u₀‖ + ‖G u₀ - u₀‖ := norm_add_le _ _
      _ ≤ (α + β * ε) * r + η := add_le_add h1 h2
      _ < r := hball)
  -- ### Fixed points of `G` in the ball are zeros of `f`
  have hiff : ∀ x ∈ Metric.closedBall u₀ r, (G x = x ↔ f x = 0) := by
    intro x _
    constructor
    · intro h
      have hx1 : x - M (f x) = x := h
      have hM0 : M (f x) = 0 := sub_eq_self.mp hx1
      exact hinjM (by rw [hM0, ContinuousLinearMap.map_zero])
    · intro h
      simp only [G]
      rw [h]
      simp
  -- ### Banach's fixed point theorem on the closed ball
  let s : Set E3 := Metric.closedBall u₀ r
  have hx₀ : u₀ ∈ s := Metric.mem_closedBall_self hr0
  have hsf : Set.MapsTo G s s := fun x hx => hGball x hx
  have hcomp : IsComplete s := Metric.isClosed_closedBall.isComplete
  let K : NNReal := ⟨α + β * ε, hκ0⟩
  have hKcoe : (K : ℝ) = α + β * ε := rfl
  have hKlt : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe]
    exact hκlt
  have hLip : LipschitzWith K (hsf.restrict G s s) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simp only [Set.MapsTo.restrict]
    rw [hKcoe]
    exact hlip x x.2 y y.2
  have hcontr : ContractingWith K (hsf.restrict G s s) := ⟨hKlt, hLip⟩
  obtain ⟨y, hys, hyfix, -⟩ :=
    ContractingWith.exists_fixedPoint' hcomp hsf hcontr hx₀ (edist_ne_top u₀ (G u₀))
  refine ⟨y, ⟨hys, (hiff y hys).1 hyfix⟩, ?_⟩
  intro z hz
  obtain ⟨hzs, hzf⟩ := hz
  have hzfix : G z = z := (hiff z hzs).2 hzf
  have h1 : dist (G z) (G y) ≤ (α + β * ε) * dist z y := hlip z hzs y hys
  rw [hzfix, hyfix] at h1
  have h2 : dist z y = 0 := by
    have hpos : 0 < 1 - (α + β * ε) := by linarith
    nlinarith [dist_nonneg (x := z) (y := y)]
  exact dist_eq_zero.mp h2

end Work.SeedCertNum
