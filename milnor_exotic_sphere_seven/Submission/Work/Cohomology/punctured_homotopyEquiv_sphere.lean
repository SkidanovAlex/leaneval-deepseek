import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The punctured space deformation retracts onto the unit sphere

For a real inner product space `E`, the complement of the origin `{v : E // v ≠ 0}`
is homotopy equivalent to the unit sphere `Metric.sphere (0 : E) 1`.

The homotopy equivalence is realized by radial normalization `v ↦ ‖v‖⁻¹ • v` from the
punctured space to the sphere, together with the inclusion of the sphere into the
punctured space.  The composite `normalize ∘ incl` is literally the identity of the
sphere (every point of the sphere has norm `1`), while `incl ∘ normalize` is homotopic
to the identity of the punctured space through the straight line homotopy
`(t, v) ↦ ((1 - t)‖v‖⁻¹ + t) • v`, which never vanishes because it is a convex
combination of the two positive scalars `‖v‖⁻¹` and `1`.
-/

open scoped unitInterval

namespace Work.Cohomology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex combination of `a` and `1` with weights `1 - t` and `t`, for `t ∈ [0,1]`,
is strictly positive when `a > 0`. -/
private lemma pos_conv (t a : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 < a) :
    0 < (1 - t) * a + t := by
  rcases eq_or_lt_of_le ht1 with h | h
  · subst h; norm_num
  · have h1 : 0 < 1 - t := by linarith
    have h2 : 0 < (1 - t) * a := mul_pos h1 ha
    linarith

omit [InnerProductSpace ℝ E] in
private lemma sphere_norm_eq_one (x : Metric.sphere (0 : E) 1) : ‖(x : E)‖ = 1 := by
  have h := Metric.mem_sphere.mp x.2
  rwa [dist_zero_right] at h

omit [InnerProductSpace ℝ E] in
private lemma sphere_ne_zero (x : Metric.sphere (0 : E) 1) : (x : E) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [sphere_norm_eq_one x]; norm_num)

private lemma norm_inv_smul_mem (v : {v : E // v ≠ 0}) :
    (‖(v : E)‖ : ℝ)⁻¹ • (v : E) ∈ Metric.sphere (0 : E) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
    Real.norm_of_nonneg (norm_nonneg (v : E)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr v.2)]

private lemma continuous_norm_inv_smul :
    Continuous fun v : {v : E // v ≠ 0} => (‖(v : E)‖ : ℝ)⁻¹ • (v : E) :=
  (continuous_subtype_val.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.2)).smul
    continuous_subtype_val

/-- Radial normalization from the punctured space to the unit sphere. -/
private noncomputable def toSphere : C({v : E // v ≠ 0}, Metric.sphere (0 : E) 1) :=
  ⟨fun v => ⟨(‖(v : E)‖ : ℝ)⁻¹ • (v : E), norm_inv_smul_mem v⟩,
   Continuous.subtype_mk continuous_norm_inv_smul (fun v => norm_inv_smul_mem v)⟩

/-- The inclusion of the unit sphere into the punctured space. -/
private noncomputable def incl : C(Metric.sphere (0 : E) 1, {v : E // v ≠ 0}) :=
  ⟨fun x => ⟨(x : E), sphere_ne_zero x⟩,
   Continuous.subtype_mk continuous_subtype_val (fun x => sphere_ne_zero x)⟩

private lemma toSphere_comp_incl :
    toSphere.comp incl = ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  ext x
  simp [toSphere, incl, ContinuousMap.comp_apply, sphere_norm_eq_one x]

/-- Underlying `E`-valued formula for the straight line homotopy between the identity and
the radial normalization. -/
private noncomputable def hval (p : I × {v : E // v ≠ 0}) : E :=
  ((1 - (p.1 : ℝ)) * (‖(p.2 : E)‖ : ℝ)⁻¹ + (p.1 : ℝ)) • (p.2 : E)

private lemma hval_ne_zero (p : I × {v : E // v ≠ 0}) : hval p ≠ 0 := by
  have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
  have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  have ha : 0 < (‖(p.2 : E)‖ : ℝ)⁻¹ := inv_pos.mpr (norm_pos_iff.mpr p.2.2)
  have hs : (1 - (p.1 : ℝ)) * (‖(p.2 : E)‖ : ℝ)⁻¹ + (p.1 : ℝ) ≠ 0 :=
    ne_of_gt (pos_conv _ _ ht0 ht1 ha)
  rw [hval]
  exact smul_ne_zero hs p.2.2

private lemma continuous_hval : Continuous fun p : I × {v : E // v ≠ 0} => hval p := by
  have ht : Continuous fun p : I × {v : E // v ≠ 0} => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun p : I × {v : E // v ≠ 0} => (p.2 : E) :=
    continuous_subtype_val.comp continuous_snd
  have hn : Continuous fun p : I × {v : E // v ≠ 0} => (‖(p.2 : E)‖ : ℝ)⁻¹ :=
    hx.norm.inv₀ (fun p => norm_ne_zero_iff.mpr p.2.2)
  have h : Continuous fun p : I × {v : E // v ≠ 0} =>
      ((1 - (p.1 : ℝ)) * (‖(p.2 : E)‖ : ℝ)⁻¹ + (p.1 : ℝ)) • (p.2 : E) :=
    (((continuous_const.sub ht).mul hn).add ht).smul hx
  simpa only [hval] using h

private noncomputable def hcm : C(I × {v : E // v ≠ 0}, {v : E // v ≠ 0}) :=
  ⟨fun p => ⟨hval p, hval_ne_zero p⟩,
   Continuous.subtype_mk continuous_hval hval_ne_zero⟩

/-- The straight line homotopy from the normalization composed with the inclusion to the
identity of the punctured space. -/
private noncomputable def homotopy : ContinuousMap.Homotopy
    (incl.comp toSphere) (ContinuousMap.id {v : E // v ≠ 0}) :=
  ContinuousMap.Homotopy.mk hcm (fun x => by
    apply Subtype.ext
    change hval (0, x) = (‖(x : E)‖ : ℝ)⁻¹ • (x : E)
    simp [hval]) (fun x => by
    apply Subtype.ext
    change hval (1, x) = (x : E)
    simp [hval])

/-- The punctured space `{v : E // v ≠ 0}` is homotopy equivalent to the unit sphere
`Metric.sphere (0 : E) 1`. -/
theorem punctured_homotopyEquiv_sphere (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Nonempty (ContinuousMap.HomotopyEquiv {v : E // v ≠ 0} (Metric.sphere (0 : E) 1)) :=
  ⟨{ toFun := toSphere
     invFun := incl
     left_inv := ⟨homotopy⟩
     right_inv := by rw [toSphere_comp_incl] }⟩

end Work.Cohomology
