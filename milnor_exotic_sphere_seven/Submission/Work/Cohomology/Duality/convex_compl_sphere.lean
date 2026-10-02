import Mathlib
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The complement of a compact convex set is homotopy equivalent to a sphere

For a nonempty convex set `K ⊆ E` in a real inner product space and a ball `Metric.ball p R ⊇ K`
with `p ∈ K`, the complement `E ∖ K` deformation retracts onto the sphere `Metric.sphere p R`
(radial projection from `p`).  Convexity is what keeps the intermediate points outside `K`: for
`x ∉ K` and `p ∈ K` the ray `p + s (x - p)`, `s ≥ 1`, is disjoint from `K`.

This is the geometric input for the local homology `H_n(ℝⁿ, ℝⁿ ∖ K) ≅ ℤ` for compact convex `K`,
the base case of the "fundamental class" lemma (Hatcher 3.27) used in Poincaré duality.
-/

open scoped unitInterval
open Set

namespace Work.Cohomology.Duality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Elementary facts -/

/-- **On the ray beyond a point one stays outside a convex set.**  If `K` is convex, `p ∈ K` and
`x ∉ K`, then `p + s (x - p) ∉ K` for every `s ≥ 1`. -/
lemma convex_ray_notMem (K : Set E) (hconv : Convex ℝ K) (p : E) (hp : p ∈ K)
    (x : {x : E // x ∉ K}) (s : ℝ) (hs : 1 ≤ s) :
    p + s • ((x : E) - p) ∉ K := by
  intro hmem
  have hsne : s ≠ 0 := by linarith
  have hpos : 0 < s⁻¹ := inv_pos.mpr (by linarith)
  have hle : s⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hs
  apply x.2
  have hrepr : (x : E) = (1 - s⁻¹) • p + s⁻¹ • (p + s • ((x : E) - p)) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hsne, one_smul, ← add_assoc, ← add_smul]
    have h1 : (1 - s⁻¹) + s⁻¹ = 1 := by rw [sub_add_cancel]
    rw [h1, one_smul]
    abel
  rw [hrepr]
  have h3 : (1 - s⁻¹) + s⁻¹ = 1 := by rw [sub_add_cancel]
  exact hconv hp hmem (by linarith) (le_of_lt hpos) h3

/-- **The sphere of radius `R` about `p` is homotopy equivalent to the unit sphere**, via the
similarity `y ↦ R⁻¹ • (y - p)`. -/
noncomputable def sphereHomotopyEquiv (p : E) (R : ℝ) (hR : 0 < R) :
    ContinuousMap.HomotopyEquiv (Metric.sphere p R) (Metric.sphere (0 : E) 1) := by
  have hmem1 : ∀ y : Metric.sphere p R, R⁻¹ • ((y : E) - p) ∈ Metric.sphere (0 : E) 1 := by
    intro y
    rw [Metric.mem_sphere, dist_zero_right]
    have hy : ‖(y : E) - p‖ = R := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp y.2
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, hy, inv_mul_cancel₀ (ne_of_gt hR)]
  have hmem2 : ∀ x : Metric.sphere (0 : E) 1, p + R • (x : E) ∈ Metric.sphere p R := by
    intro x
    rw [Metric.mem_sphere, dist_eq_norm]
    have hx : ‖(x : E)‖ = 1 := by
      have h := Metric.mem_sphere.mp x.2
      rwa [dist_zero_right] at h
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR, hx, mul_one]
  let φ : C(Metric.sphere p R, Metric.sphere (0 : E) 1) :=
    ⟨fun y => ⟨R⁻¹ • ((y : E) - p), hmem1 y⟩,
      Continuous.subtype_mk (continuous_const.smul (continuous_subtype_val.sub continuous_const))
        hmem1⟩
  let ψ : C(Metric.sphere (0 : E) 1, Metric.sphere p R) :=
    ⟨fun x => ⟨p + R • (x : E), hmem2 x⟩,
      Continuous.subtype_mk (continuous_const.add (continuous_const.smul continuous_subtype_val))
        hmem2⟩
  have h1 : ψ.comp φ = ContinuousMap.id _ := by
    ext y
    show p + R • (R⁻¹ • ((y : E) - p)) = (y : E)
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul, add_sub_cancel]
  have h2 : φ.comp ψ = ContinuousMap.id _ := by
    ext x
    show R⁻¹ • (p + R • (x : E) - p) = (x : E)
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul]
  exact { toFun := φ, invFun := ψ, left_inv := by rw [h1], right_inv := by rw [h2] }

/-! ## The main homotopy equivalence -/

/-- **The complement of a convex set containing `p` retracts onto the sphere of radius `R` about
`p`**, whenever `K ⊆ Metric.ball p R`. -/
theorem convex_compl_homotopyEquiv_sphereOf (K : Set E) (hconv : Convex ℝ K) (p : E) (hp : p ∈ K)
    (R : ℝ) (hR : 0 < R) (hsub : K ⊆ Metric.ball p R) :
    Nonempty (ContinuousMap.HomotopyEquiv {x : E // x ∉ K} (Metric.sphere p R)) := by
  have hnorm_pos : ∀ x : {x : E // x ∉ K}, 0 < ‖(x : E) - p‖ := by
    intro x
    refine norm_pos_iff.mpr ?_
    intro h0
    exact x.2 (by rw [sub_eq_zero.mp h0]; exact hp)
  -- the radial projection
  let proj : {x : E // x ∉ K} → Metric.sphere p R := fun x =>
    ⟨p + (R / ‖(x : E) - p‖) • ((x : E) - p), by
      rw [Metric.mem_sphere, dist_eq_norm]
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (le_of_lt hR) (le_of_lt (hnorm_pos x))),
        div_mul_cancel₀ _ (ne_of_gt (hnorm_pos x))]⟩
  have hproj : Continuous proj := by
    apply Continuous.subtype_mk
    have hx : Continuous fun x : {x : E // x ∉ K} => (x : E) := continuous_subtype_val
    have hn : Continuous fun x : {x : E // x ∉ K} => ‖(x : E) - p‖ :=
      (hx.sub continuous_const).norm
    have hd : Continuous fun x : {x : E // x ∉ K} => R / ‖(x : E) - p‖ :=
      continuous_const.div hn (fun x => ne_of_gt (hnorm_pos x))
    exact continuous_const.add (hd.smul (hx.sub continuous_const))
  -- the inclusion of the sphere
  let incl : Metric.sphere p R → {x : E // x ∉ K} := fun y =>
    ⟨y, by
      intro hyK
      have h1 : dist (y : E) p < R := hsub hyK
      rw [Metric.mem_sphere.mp y.2] at h1
      exact lt_irrefl R h1⟩
  have hincl : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  -- `proj ∘ incl = id`
  have hproj_incl : (⟨proj, hproj⟩ : C({x : E // x ∉ K}, Metric.sphere p R)).comp
      (⟨incl, hincl⟩ : C(Metric.sphere p R, {x : E // x ∉ K})) = ContinuousMap.id _ := by
    ext y
    have hy : ‖(y : E) - p‖ = R := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp y.2
    show p + (R / ‖(y : E) - p‖) • ((y : E) - p) = (y : E)
    rw [hy, div_self (ne_of_gt hR), one_smul]
    abel
  -- the homotopy: push the radius inward from `x` to the sphere
  have hkey : ∀ (x : {x : E // x ∉ K}) (t : ℝ), 0 ≤ t → t ≤ 1 →
      p + ((1 - t) * (R / ‖(x : E) - p‖) + t) • ((x : E) - p) ∉ K := by
    intro x t ht0 ht1
    have hx0 := hnorm_pos x
    have hc : 0 < R / ‖(x : E) - p‖ := div_pos hR hx0
    set s : ℝ := (1 - t) * (R / ‖(x : E) - p‖) + t with hs
    have hs1 : 0 < s := by
      rcases eq_or_lt_of_le ht0 with h | h
      · subst h
        rw [hs, sub_zero, one_mul, add_zero]
        exact hc
      · have h2 : 0 ≤ (1 - t) * (R / ‖(x : E) - p‖) :=
          mul_nonneg (by linarith) (le_of_lt hc)
        rw [hs]
        linarith
    by_cases hcase : ‖(x : E) - p‖ ≤ R
    · -- then `s ≥ 1` and we are on the ray beyond `x`
      have hle : 1 ≤ R / ‖(x : E) - p‖ := (one_le_div hx0).mpr hcase
      have hsge : 1 ≤ s := by
        have h2 : 0 ≤ 1 - t := by linarith
        have h3 : (1 - t) * 1 ≤ (1 - t) * (R / ‖(x : E) - p‖) :=
          mul_le_mul_of_nonneg_left hle h2
        rw [hs]
        linarith
      exact convex_ray_notMem K hconv p hp x s hsge
    · -- then the point is at distance at least `R` from `p`
      have hcase' : R ≤ ‖(x : E) - p‖ := le_of_lt (not_le.mp hcase)
      have hle : R / ‖(x : E) - p‖ ≤ 1 := (div_le_one hx0).mpr hcase'
      have hsge : R / ‖(x : E) - p‖ ≤ s := by
        have h4 : t * (R / ‖(x : E) - p‖) ≤ t * 1 := mul_le_mul_of_nonneg_left hle ht0
        rw [hs]
        linarith
      have hsR : R ≤ s * ‖(x : E) - p‖ := by
        have h4 := mul_le_mul_of_nonneg_right hsge (le_of_lt hx0)
        have h5 : (R / ‖(x : E) - p‖) * ‖(x : E) - p‖ = R :=
          div_mul_cancel₀ _ (ne_of_gt hx0)
        rw [h5] at h4
        exact h4
      intro hmem
      have hb := hsub hmem
      rw [Metric.mem_ball, dist_eq_norm] at hb
      have hdist : ‖p + s • ((x : E) - p) - p‖ = s * ‖(x : E) - p‖ := by
        rw [show p + s • ((x : E) - p) - p = s • ((x : E) - p) by rw [add_sub_cancel_left],
          norm_smul, Real.norm_eq_abs, abs_of_pos hs1]
      rw [hdist] at hb
      linarith
  let H : I × {x : E // x ∉ K} → {x : E // x ∉ K} := fun q =>
    ⟨p + ((1 - (q.1 : ℝ)) * (R / ‖(q.2 : E) - p‖) + (q.1 : ℝ)) • ((q.2 : E) - p),
      hkey q.2 (q.1 : ℝ) q.1.2.1 q.1.2.2⟩
  have hH : Continuous H := by
    apply Continuous.subtype_mk
    have ht : Continuous fun q : I × {x : E // x ∉ K} => (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous fun q : I × {x : E // x ∉ K} => (q.2 : E) :=
      continuous_subtype_val.comp continuous_snd
    have hn : Continuous fun q : I × {x : E // x ∉ K} => ‖(q.2 : E) - p‖ :=
      (hx.sub continuous_const).norm
    have hnne : ∀ q : I × {x : E // x ∉ K}, ‖(q.2 : E) - p‖ ≠ 0 :=
      fun q => ne_of_gt (hnorm_pos q.2)
    have hd : Continuous fun q : I × {x : E // x ∉ K} => R / ‖(q.2 : E) - p‖ :=
      continuous_const.div hn hnne
    exact continuous_const.add ((((continuous_const.sub ht).mul hd).add ht).smul
      (hx.sub continuous_const))
  refine ⟨{ toFun := ⟨proj, hproj⟩
            invFun := ⟨incl, hincl⟩
            left_inv := ⟨ContinuousMap.Homotopy.mk ⟨H, hH⟩ ?_ ?_⟩
            right_inv := by rw [hproj_incl] }⟩
  · intro x
    apply Subtype.ext
    show p + ((1 - (0:ℝ)) * (R / ‖(x : E) - p‖) + (0:ℝ)) • ((x : E) - p)
      = p + (R / ‖(x : E) - p‖) • ((x : E) - p)
    norm_num
  · intro x
    apply Subtype.ext
    show p + ((1 - (1:ℝ)) * (R / ‖(x : E) - p‖) + (1:ℝ)) • ((x : E) - p) = (x : E)
    have hs1 : ((1:ℝ) - 1) * (R / ‖(x : E) - p‖) + 1 = 1 := by norm_num
    rw [hs1, one_smul]
    abel

/-- **The complement of a nonempty compact convex set is homotopy equivalent to the unit sphere.** -/
theorem convex_compl_homotopyEquiv_sphere (K : Set E) (hKc : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) :
    Nonempty (ContinuousMap.HomotopyEquiv {x : E // x ∉ K} (Metric.sphere (0 : E) 1)) := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨R, hR, hsub⟩ := hKc.isBounded.subset_ball_lt 0 p
  obtain ⟨e⟩ := convex_compl_homotopyEquiv_sphereOf K hconv p hp R hR hsub
  exact ⟨e.trans (sphereHomotopyEquiv p R hR)⟩

end Work.Cohomology.Duality
