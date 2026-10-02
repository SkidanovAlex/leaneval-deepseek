import Submission.Work.Tubular.BundleDisc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The radial collapse of a Euclidean bundle onto its Thom space

The **space-level Pontryagin–Thom collapse** of a real bundle `Z`: the total space is retracted
radially onto the closed unit disc bundle, each fibre being scaled by `min 1 ‖v‖⁻¹`; all vectors of
norm `≥ 1` are pushed onto the sphere bundle and hence onto the basepoint of the Thom space
`Th(Z) = D(Z)/S(Z)`.  Passing to the one-point compactification `Z.TotalSpace ∪ {∞}` (which, for a
rank-`k` bundle over a compact `8`-manifold, is the sphere `S^{k+8}`) gives the collapse
`Z.TotalSpace ∪ {∞} → Th(Z)`.

This file contains the **pointwise** content: the radial scaling factor
(`Work.Tubular.radialScale`), its effect on the fibrewise norm
(`Work.Tubular.fibreNorm_discRetract_le`, `..._eq_one`), and the induced map
(`Work.Tubular.bundleCollapse`) with the three value lemmas that make it the collapse
(identity on the disc bundle, basepoint on the sphere bundle and on the complement of the disc
bundle).  It is the space-level half of the Pontryagin–Thom construction, and it is the map that the
Thom class is evaluated against.

The continuity of `bundleCollapse` is proved in the setting this chapter is about — the normal bundle
of an embedded manifold, modelled as a subspace of `V.pt × ℝ^N` — by
`Work.Tubular.continuous_tubeCollapse`, which uses the tubular neighbourhood.  For an abstract
gluing-data bundle the continuity of the radial retraction is checked in the local trivialisations;
that argument is not carried out here (see the chapter's `README.md`).
-/

open scoped Topology
open Set Bundle

open Work.TangentClasses

open Work.Thom

namespace Work.Tubular

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*}

/-- The **radial scaling factor**: `1` on vectors of norm at most `1`, and `‖v‖⁻¹` beyond — so that
multiplying a fibre by it retracts the fibre onto its closed unit disc and pushes the complement onto
the unit sphere. -/
def radialScale (t : ℝ) : ℝ := if t ≤ 1 then 1 else t⁻¹

@[simp] theorem radialScale_apply (t : ℝ) : radialScale t = if t ≤ 1 then 1 else t⁻¹ := rfl

theorem radialScale_nonneg (t : ℝ) : 0 ≤ radialScale t := by
  rw [radialScale]
  split
  · exact zero_le_one
  · rename_i h
    exact inv_nonneg.mpr (le_trans zero_le_one (le_of_not_ge h))

theorem radialScale_le_one (t : ℝ) : radialScale t ≤ 1 := by
  rw [radialScale]
  split
  · exact le_rfl
  · rename_i h
    exact le_of_lt (inv_lt_one_of_one_lt₀ (lt_of_not_ge h))

theorem radialScale_eq_one (t : ℝ) (ht : t ≤ 1) : radialScale t = 1 := by
  rw [radialScale, if_pos ht]

theorem radialScale_mul_self_le_one (t : ℝ) (ht : 0 ≤ t) : radialScale t * t ≤ 1 := by
  rw [radialScale]
  split
  · rename_i h; rw [one_mul]; exact h
  · rename_i h
    exact le_of_eq (inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_of_not_ge h))))

theorem radialScale_mul_self_eq_one (t : ℝ) (ht : 1 < t) : radialScale t * t = 1 := by
  rw [radialScale, if_neg (not_le.mpr ht)]
  exact inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one ht))

/-! ## The radial retraction -/

/-- **The radial retraction of the total space onto the closed unit disc bundle**: each fibre is
scaled by `radialScale` applied to the fibrewise norm. -/
def discRetract (Z : RealBundle B F ι) (p : Z.TotalSpace) : Z.TotalSpace :=
  ⟨p.proj, radialScale (fibreNorm Z p) • p.2⟩

@[simp] theorem discRetract_proj (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    (discRetract Z p).proj = p.proj := rfl

theorem discRetract_mk (Z : RealBundle B F ι) (x : B) (v : Z.Fiber x) :
    discRetract Z (⟨x, v⟩ : Z.TotalSpace) =
      ⟨x, radialScale (fibreNorm Z (⟨x, v⟩ : Z.TotalSpace)) • v⟩ := rfl

/-- The fibrewise norm is non-negative. -/
theorem fibreNorm_nonneg (Z : RealBundle B F ι) (p : Z.TotalSpace) : 0 ≤ fibreNorm Z p :=
  norm_nonneg (show F from p.2)

/-- The radial retraction lands in the closed unit disc bundle. -/
theorem fibreNorm_discRetract_le (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    fibreNorm Z (discRetract Z p) ≤ 1 := by
  obtain ⟨x, v⟩ := p
  show ‖radialScale (fibreNorm Z (⟨x, v⟩ : Z.TotalSpace)) • (show F from v)‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (radialScale_nonneg _)]
  exact radialScale_mul_self_le_one _ (fibreNorm_nonneg Z _)

/-- The radial retraction sends the complement of the disc bundle onto the sphere bundle. -/
theorem fibreNorm_discRetract_eq_one (Z : RealBundle B F ι) {p : Z.TotalSpace}
    (hp : 1 < fibreNorm Z p) : fibreNorm Z (discRetract Z p) = 1 := by
  obtain ⟨x, v⟩ := p
  show ‖radialScale (fibreNorm Z (⟨x, v⟩ : Z.TotalSpace)) • (show F from v)‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (radialScale_nonneg _)]
  exact radialScale_mul_self_eq_one _ hp

/-- The radial retraction fixes the closed unit disc bundle. -/
theorem discRetract_eq_self (Z : RealBundle B F ι) {p : Z.TotalSpace} (hp : fibreNorm Z p ≤ 1) :
    discRetract Z p = p := by
  obtain ⟨x, v⟩ := p
  show (⟨x, radialScale (fibreNorm Z (⟨x, v⟩ : Z.TotalSpace)) • v⟩ : Z.TotalSpace) = ⟨x, v⟩
  rw [radialScale_eq_one _ hp, one_smul]

theorem discRetract_mem_sphere (Z : RealBundle B F ι) {p : Z.TotalSpace} (hp : p ∈ sphereSet Z) :
    discRetract Z p ∈ sphereSet Z := by
  obtain ⟨x, v⟩ := p
  show fibreNorm Z (⟨x, radialScale (fibreNorm Z (⟨x, v⟩ : Z.TotalSpace)) • v⟩ :
    Z.TotalSpace) = 1
  rw [radialScale_eq_one _ (le_of_eq hp), one_smul]
  exact hp

/-! ## The collapse -/

/-- **The Pontryagin–Thom collapse** of a real bundle, as a map of the one-point compactification:
the total space is retracted onto the disc bundle and the sphere bundle (and `∞`) is collapsed to
the basepoint of the Thom space. -/
def bundleCollapse (Z : RealBundle B F ι) (q : SphSub Z) :
    OnePoint Z.TotalSpace → ThomSpace Z :=
  fun x => Option.elim x (thomMk Z ⟨q.1, le_of_eq q.2⟩)
    (fun p => thomMk Z ⟨discRetract Z p, fibreNorm_discRetract_le Z p⟩)

@[simp] theorem bundleCollapse_coe (Z : RealBundle B F ι) (q : SphSub Z) (p : Z.TotalSpace) :
    bundleCollapse Z q p = thomMk Z ⟨discRetract Z p, fibreNorm_discRetract_le Z p⟩ := rfl

@[simp] theorem bundleCollapse_infty (Z : RealBundle B F ι) (q : SphSub Z) :
    bundleCollapse Z q OnePoint.infty = thomMk Z ⟨q.1, le_of_eq q.2⟩ := rfl

/-- **The collapse is the identity on the disc bundle** (after the identification
`D(Z) ⊆ Z.TotalSpace`). -/
theorem bundleCollapse_eq_thomMk (Z : RealBundle B F ι) (q : SphSub Z) {p : Z.TotalSpace}
    (hp : fibreNorm Z p ≤ 1) :
    bundleCollapse Z q p = thomMk Z ⟨p, hp⟩ := by
  have hsub : (⟨discRetract Z p, fibreNorm_discRetract_le Z p⟩ : DiscSub Z) = ⟨p, hp⟩ :=
    Subtype.ext (discRetract_eq_self Z hp)
  rw [bundleCollapse_coe, hsub]

/-- **The collapse sends the sphere bundle to the basepoint.** -/
theorem bundleCollapse_of_mem_sphere (Z : RealBundle B F ι) (q : SphSub Z) {p : Z.TotalSpace}
    (hp : p ∈ sphereSet Z) :
    bundleCollapse Z q p = thomMk Z ⟨q.1, le_of_eq q.2⟩ := by
  rw [bundleCollapse_coe]
  exact thomMk_eq_of_mem_sphereInDisc (discRetract_mem_sphere Z hp) q.2

/-- **The collapse sends the complement of the disc bundle to the basepoint.** -/
theorem bundleCollapse_of_one_lt (Z : RealBundle B F ι) (q : SphSub Z) {p : Z.TotalSpace}
    (hp : 1 < fibreNorm Z p) :
    bundleCollapse Z q p = thomMk Z ⟨q.1, le_of_eq q.2⟩ := by
  rw [bundleCollapse_coe]
  exact thomMk_eq_of_mem_sphereInDisc (fibreNorm_discRetract_eq_one Z hp) q.2

end

end Work.Tubular
