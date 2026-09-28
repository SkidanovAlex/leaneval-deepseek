import Mathlib
import Submission.Work.Thom.DiscSphereTopology
import Submission.Work.Thom.Continuous
import Submission.Work.Thom.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The sphere bundle is a deformation retract of the complement of the zero section

For a Euclidean real bundle `Z` over `B`, the inclusion `S(E) ↪ E ∖ 0` of the unit sphere bundle
into the complement of the zero section is a homotopy equivalence.  The homotopy inverse is the
radial projection `p ↦ ⟨p.1, (fibreNorm Z p)⁻¹ • p.2⟩` and the homotopy is the linear interpolation
of the radial scaling, `(t,p) ↦ ⟨p.1, ((1-t) + t·(fibreNorm Z p)⁻¹) • p.2⟩`; the scaling
coefficient is strictly positive on `E ∖ 0`, so the deformation stays inside `E ∖ 0`.

The main result is `Work.Thom.sphereInDisc_homotopyEquiv`.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle Filter

open scoped Topology

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*}

/-! The helper lemmas below are collected in the namespace `Work.Thom.SphereInDisc`, so that they
cannot clash with the names other modules of the chapter introduce in `Work.Thom`. -/

namespace SphereInDisc

/-! ## A universe-general version of the continuity of a fibrewise rescaling

`Work.Thom.continuous_smul_section` is stated for test spaces living in the smallest universe,
which makes it unusable on `I × (E ∖ 0)` when `E` lives in a larger one; the two lemmas below are
the same statements without that restriction (their proofs are the ones in
`Submission/Work/Thom/Continuous.lean`). -/

theorem continuousAt_localTrivAt_snd' {X : Type*} [TopologicalSpace X] (Z : RealBundle B F ι)
    (σ : C(X, Z.TotalSpace)) (x₀ : X) :
    ContinuousAt (fun x => ((Z.localTrivAt (σ x₀).1) (σ x)).2) x₀ := by
  have h := ((FiberBundle.continuousAt_totalSpace F σ (x₀ := x₀)).1
    σ.continuous.continuousAt).2
  simpa only [VectorBundleCore.trivializationAt, VectorBundleCore.proj] using h

theorem continuous_smul_section' {X : Type*} [TopologicalSpace X] (Z : RealBundle B F ι)
    (σ : C(X, Z.TotalSpace)) (c : C(X, ℝ)) :
    Continuous (fun x => (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set i := Z.indexAt (σ x₀).1 with hi
  have hx0 : (σ x₀).1 ∈ Z.baseSet i := by rw [hi]; exact Z.mem_baseSet_at (σ x₀).1
  have hσ : ContinuousAt (fun x => ((Z.localTriv i) (σ x)).2) x₀ :=
    continuousAt_localTrivAt_snd' Z σ x₀
  have hpair : ContinuousAt (fun x => ((σ x).1, c x • ((Z.localTriv i) (σ x)).2)) x₀ :=
    (Z.continuous_proj.continuousAt.comp σ.continuous.continuousAt).prodMk
      (c.continuous.continuousAt.smul hσ)
  have heq : (fun x => (Z.localTriv i) (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) =
      fun x => ((σ x).1, c x • ((Z.localTriv i) (σ x)).2) := by
    funext x
    rw [VectorBundleCore.localTriv_apply, ContinuousLinearMap.map_smul,
      VectorBundleCore.localTriv_apply]
  refine (Z.localTriv i).continuousAt_of_comp_left ?_ hx0 ?_
  · show ContinuousAt (fun x => Z.proj (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) x₀
    rw [show (fun x => Z.proj (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) = fun x => (σ x).1
      from by funext x; rfl]
    exact Z.continuous_proj.continuousAt.comp σ.continuous.continuousAt
  · show ContinuousAt (fun x => (Z.localTriv i) (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) x₀
    rw [heq]
    exact hpair

/-! ## The fibrewise norm and the radial rescaling -/

theorem fibreNorm_eq_norm (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    fibreNorm Z p = ‖(show F from p.2)‖ := rfl

theorem mem_zeroComplement_iff_fibreNorm_ne_zero (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    p ∈ zeroComplement Z ↔ fibreNorm Z p ≠ 0 := by
  rw [mem_zeroComplement, fibreNorm_eq_norm, norm_ne_zero_iff]

theorem fibreNorm_pos_iff (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    0 < fibreNorm Z p ↔ p ∈ zeroComplement Z := by
  rw [fibreNorm_eq_norm, norm_pos_iff, mem_zeroComplement]

theorem fibreNorm_smul_eq (Z : RealBundle B F ι) (p : Z.TotalSpace) (c : ℝ) :
    fibreNorm Z (⟨p.1, c • p.2⟩ : Z.TotalSpace) = |c| * fibreNorm Z p := by
  rw [fibreNorm_smul]

/-- The fibrewise rescaling of `p` by `(fibreNorm Z p)⁻¹`: pointwise, the radial projection of the
fibre onto its unit sphere. -/
def radialRescale (Z : RealBundle B F ι) (p : Z.TotalSpace) : Z.TotalSpace :=
  ⟨p.1, (fibreNorm Z p)⁻¹ • p.2⟩

theorem fibreNorm_radialRescale {Z : RealBundle B F ι} {p : Z.TotalSpace}
    (hp : p ∈ zeroComplement Z) : fibreNorm Z (radialRescale Z p) = 1 := by
  have hn : 0 < fibreNorm Z p := (fibreNorm_pos_iff Z p).2 hp
  rw [radialRescale, fibreNorm_smul_eq, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']

theorem radialRescale_mem_sphereSet {Z : RealBundle B F ι} {p : Z.TotalSpace}
    (hp : p ∈ zeroComplement Z) : radialRescale Z p ∈ sphereSet Z := by
  rw [mem_sphereSet, fibreNorm_radialRescale hp]

theorem zeroComplement_of_mem_sphereSet {Z : RealBundle B F ι} {p : Z.TotalSpace}
    (hp : p ∈ sphereSet Z) : p ∈ zeroComplement Z := by
  rw [mem_zeroComplement_iff_fibreNorm_ne_zero, mem_sphereSet] at *
  rw [hp]
  norm_num

theorem zeroComplement_of_smul {Z : RealBundle B F ι} {p : Z.TotalSpace}
    (hp : p ∈ zeroComplement Z) {c : ℝ} (hc : c ≠ 0) :
    (⟨p.1, c • p.2⟩ : Z.TotalSpace) ∈ zeroComplement Z := by
  rw [mem_zeroComplement_iff_fibreNorm_ne_zero, fibreNorm_smul_eq]
  exact mul_ne_zero (abs_ne_zero.mpr hc) ((mem_zeroComplement_iff_fibreNorm_ne_zero Z p).1 hp)

/-! ## The inclusion `S(E) ↪ E ∖ 0` and the radial projection -/

/-- The inclusion of the sphere bundle into the complement of the zero section. -/
def sphereToZeroComplement (Z : RealBundle B F ι) : C(sphereInDisc Z, zeroComplement Z) :=
  ⟨fun q => ⟨((q : DiscSub Z) : Z.TotalSpace), zeroComplement_of_mem_sphereSet q.2⟩,
    Continuous.subtype_mk
      ((continuous_subtype_val : Continuous (Subtype.val : DiscSub Z → Z.TotalSpace)).comp
        (continuous_subtype_val : Continuous (Subtype.val : sphereInDisc Z → DiscSub Z)))
      (fun q => zeroComplement_of_mem_sphereSet q.2)⟩

@[simp] theorem sphereToZeroComplement_coe (Z : RealBundle B F ι) (q : sphereInDisc Z) :
    ((sphereToZeroComplement Z q : zeroComplement Z) : Z.TotalSpace) =
      ((q : DiscSub Z) : Z.TotalSpace) := rfl

/-- The radial projection of `E ∖ 0` onto the sphere bundle. -/
def radialProjection (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    C(zeroComplement Z, sphereInDisc Z) :=
  ⟨fun p => ⟨⟨radialRescale Z p,
        sphereSet_subset_closedDiscSet Z (radialRescale_mem_sphereSet p.2)⟩,
      radialRescale_mem_sphereSet p.2⟩,
    Continuous.subtype_mk
      (Continuous.subtype_mk
        (continuous_smul_section' Z
          ⟨fun p : zeroComplement Z => (p : Z.TotalSpace), continuous_subtype_val⟩
          ⟨fun p : zeroComplement Z => (fibreNorm Z (p : Z.TotalSpace))⁻¹,
            (((continuous_fibreNorm hZ).comp continuous_subtype_val)).inv₀
              (fun p => ne_of_gt ((fibreNorm_pos_iff Z _).2 p.2))⟩)
        (fun p => sphereSet_subset_closedDiscSet Z (radialRescale_mem_sphereSet p.2)))
      (fun p => radialRescale_mem_sphereSet p.2)⟩

@[simp] theorem radialProjection_coe (Z : RealBundle B F ι) (hZ : IsEuclidean Z)
    (p : zeroComplement Z) :
    (((radialProjection Z hZ p : sphereInDisc Z) : DiscSub Z) : Z.TotalSpace) =
      radialRescale Z (p : Z.TotalSpace) := rfl

/-- The radial projection fixes the sphere bundle pointwise. -/
theorem radialProjection_comp_sphereToZeroComplement (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    (radialProjection Z hZ).comp (sphereToZeroComplement Z) =
      ContinuousMap.id (sphereInDisc Z) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  apply Subtype.ext
  show radialRescale Z ((q : DiscSub Z) : Z.TotalSpace) = ((q : DiscSub Z) : Z.TotalSpace)
  have h1 : fibreNorm Z ((q : DiscSub Z) : Z.TotalSpace) = 1 := q.2
  rw [radialRescale, h1, inv_one, one_smul]

/-! ## The radial deformation -/

/-- The scaling coefficient of the radial deformation at time `t` and point `p`. -/
def deformCoeff (Z : RealBundle B F ι) (x : unitInterval × zeroComplement Z) : ℝ :=
  (1 - (x.1 : ℝ)) + (x.1 : ℝ) * (fibreNorm Z (x.2 : Z.TotalSpace))⁻¹

theorem pos_deformCoeff_aux {t n : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (hn : 0 < n) :
    0 < (1 - t) + t * n⁻¹ := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h, sub_self, zero_add, one_mul]
    exact inv_pos.mpr hn
  · have : 0 ≤ t * n⁻¹ := mul_nonneg h0 (le_of_lt (inv_pos.mpr hn))
    linarith

/-- The scaling coefficient of the radial deformation is strictly positive on `E ∖ 0`. -/
theorem pos_deformCoeff (Z : RealBundle B F ι) (x : unitInterval × zeroComplement Z) :
    0 < deformCoeff Z x := by
  rw [deformCoeff]
  exact pos_deformCoeff_aux x.1.2.1 x.1.2.2 ((fibreNorm_pos_iff Z _).2 x.2.2)

/-- The point map of the radial deformation. -/
def deformPoint (Z : RealBundle B F ι) (x : unitInterval × zeroComplement Z) : Z.TotalSpace :=
  ⟨(x.2 : Z.TotalSpace).1, deformCoeff Z x • (x.2 : Z.TotalSpace).2⟩

theorem continuous_deformCoeff {Z : RealBundle B F ι} (hZ : IsEuclidean Z) :
    Continuous (deformCoeff Z) := by
  have hfib : Continuous (fun x : unitInterval × zeroComplement Z =>
      (fibreNorm Z (x.2 : Z.TotalSpace))⁻¹) :=
    (((continuous_fibreNorm hZ).comp continuous_subtype_val).comp continuous_snd).inv₀
      (fun x => ne_of_gt ((fibreNorm_pos_iff Z _).2 x.2.2))
  have ht : Continuous (fun x : unitInterval × zeroComplement Z => (x.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  exact (continuous_const.sub ht).add (ht.mul hfib)

theorem continuous_deformPoint {Z : RealBundle B F ι} (hZ : IsEuclidean Z) :
    Continuous (deformPoint Z) :=
  continuous_smul_section' Z
    ⟨fun x : unitInterval × zeroComplement Z => (x.2 : Z.TotalSpace),
      continuous_subtype_val.comp continuous_snd⟩
    ⟨deformCoeff Z, continuous_deformCoeff hZ⟩

/-- The radial deformation as a continuous map, landing in the complement of the zero section. -/
def deformMap (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    C(unitInterval × zeroComplement Z, zeroComplement Z) :=
  ⟨fun x => ⟨deformPoint Z x,
      zeroComplement_of_smul (p := (x.2 : Z.TotalSpace)) x.2.2
        (c := deformCoeff Z x) (ne_of_gt (pos_deformCoeff Z x))⟩,
    Continuous.subtype_mk (continuous_deformPoint hZ)
      (fun x => zeroComplement_of_smul (p := (x.2 : Z.TotalSpace)) x.2.2
        (c := deformCoeff Z x) (ne_of_gt (pos_deformCoeff Z x)))⟩

@[simp] theorem deformMap_coe (Z : RealBundle B F ι) (hZ : IsEuclidean Z)
    (x : unitInterval × zeroComplement Z) :
    ((deformMap Z hZ x : zeroComplement Z) : Z.TotalSpace) = deformPoint Z x := rfl

/-- **The radial deformation is a homotopy from the identity of `E ∖ 0` to the composite of the
radial projection with the inclusion.** -/
theorem homotopic_id_radialProjection (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    ContinuousMap.Homotopic (ContinuousMap.id (zeroComplement Z))
      ((sphereToZeroComplement Z).comp (radialProjection Z hZ)) := by
  refine ⟨ContinuousMap.Homotopy.mk (deformMap Z hZ) ?_ ?_⟩
  · intro x
    apply Subtype.ext
    show deformPoint Z (0, x) = (x : Z.TotalSpace)
    rw [deformPoint, deformCoeff]
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, zero_mul, add_zero, one_smul]
  · intro x
    apply Subtype.ext
    show deformPoint Z (1, x) =
      (((radialProjection Z hZ x : sphereInDisc Z) : DiscSub Z) : Z.TotalSpace)
    rw [deformPoint, deformCoeff]
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_add, one_mul]
    rfl

end SphereInDisc

open SphereInDisc

/-- The inclusion of the unit sphere bundle `S(E)` into the complement `E∖0` of the zero section,
for a Euclidean real bundle `Z`, is a homotopy equivalence.  The homotopy inverse is the radial
projection `p ↦ ⟨p.1, (fibreNorm Z p)⁻¹ • p.2⟩` onto the sphere bundle, and the homotopy is the
linear interpolation of the radial scaling; the map stays inside `E∖0` because the scaling
coefficient `(1-t) + t·(fibreNorm Z p)⁻¹` is strictly positive on `E∖0`. -/
theorem sphereInDisc_homotopyEquiv {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} (Z : Work.TangentClasses.RealBundle B F ι)
    (hZ : Work.Thom.IsEuclidean Z) :
    ∃ e : ContinuousMap.HomotopyEquiv (Work.Thom.sphereInDisc Z) (Work.Thom.zeroComplement Z),
      ∀ q, (e.toFun q : Z.TotalSpace) = ((q : Work.Thom.DiscSub Z) : Z.TotalSpace) := by
  refine ⟨{ toFun := sphereToZeroComplement Z
            invFun := radialProjection Z hZ
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · rw [radialProjection_comp_sphereToZeroComplement Z hZ]
  · exact (homotopic_id_radialProjection Z hZ).symm
  · intro q
    rfl

end

end Work.Thom
