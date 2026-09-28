import Mathlib
import Submission.Work.Thom.DiscSphereTopology
import Submission.Work.Thom.Continuous
import Submission.Work.Thom.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The closed disc bundle `D(E)` is a deformation retract of the total space `E`

For a Euclidean real bundle `Z` (`Work.Thom.IsEuclidean`, so that the fibrewise norm is continuous,
`Work.Thom.continuous_fibreNorm`) the map

`r : E ⟶ D(E),   r p = ⟨p.1, (max 1 ‖p‖)⁻¹ • p.2⟩`

is the **radial retraction** of the total space onto the closed unit disc bundle, and the inclusion
`D(E) ↪ E` is a homotopy equivalence with homotopy inverse `r`.  The homotopy is the linear
interpolation of the radial scaling,

`(t,p) ↦ ⟨p.1, (c p + t (1 - c p)) • p.2⟩`,  `c p = (max 1 ‖p‖)⁻¹`,

which at `t = 0` is `r` and at `t = 1` is the identity of `E`.  The composite `r ∘ i` is *equal* to
the identity of `D(E)` (not only homotopic to it), because `c p = 1` on the closed disc.

Note that `(max 1 n)⁻¹` is the same map of the total space as the coefficient
`min 1 n⁻¹` of the classical formula: the two differ only for `n = 0`, where `min 1 0 = 0` but the
fibre vector is `0` and both scalings agree.  The advantage of the `max` form is that
`p ↦ (max 1 (fibreNorm Z p))⁻¹` is *continuous* (it is `1` near the zero section and `n⁻¹` away
from it), whereas `p ↦ min 1 (fibreNorm Z p)⁻¹` is not — although the rescaled *vector* is still
continuous, being `p` on the disc.

The two continuity lemmas `continuousAt_localTrivAt_snd_univ` and `continuous_smul_section_univ`
are the universe-general versions of `Work.Thom.continuousAt_localTrivAt_snd` and
`Work.Thom.continuous_smul_section` of `Submission/Work/Thom/Continuous.lean` (those are stated for
`X : Type`, i.e. for a space in `Type 0`, while the total space `Z.TotalSpace` lives in
`Type (max u v)`; the proofs are the same).

## Main result

* `Work.Thom.discSub_homotopyEquiv` — the inclusion `D(E) → E` is a homotopy equivalence, with
  homotopy inverse the radial retraction.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*}

/-! ## The universe-general continuity lemmas for fibrewise rescalings -/

/-- The coordinate of a continuous map into the total space of a bundle, read in the preferred
trivialisation at its base point `σ x₀`, is continuous at `x₀`.  This is the universe-general
version of `Work.Thom.continuousAt_localTrivAt_snd` (there `X : Type`): it is
`FiberBundle.continuousAt_totalSpace` with the identification
`trivializationAt F Z.Fiber b = Z.localTrivAt b`. -/
theorem continuousAt_localTrivAt_snd_univ {X : Type*} [TopologicalSpace X] (Z : RealBundle B F ι)
    (σ : C(X, Z.TotalSpace)) (x₀ : X) :
    ContinuousAt (fun x => ((Z.localTrivAt (σ x₀).1) (σ x)).2) x₀ := by
  have h := ((FiberBundle.continuousAt_totalSpace F σ (x₀ := x₀)).1
    σ.continuous.continuousAt).2
  simpa only [VectorBundleCore.trivializationAt, VectorBundleCore.proj] using h

/-- **Fibrewise rescaling of a continuous map into the total space**, for a space `X` in any
universe: if `σ : X → E` is continuous and `c : X → ℝ` is continuous, then
`x ↦ ⟨(σ x).1, c x • (σ x).2⟩` is continuous.  Universe-general version of
`Work.Thom.continuous_smul_section`. -/
theorem continuous_smul_section_univ {X : Type*} [TopologicalSpace X] (Z : RealBundle B F ι)
    (σ : C(X, Z.TotalSpace)) (c : C(X, ℝ)) :
    Continuous (fun x => (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set i := Z.indexAt (σ x₀).1 with hi
  have hx0 : (σ x₀).1 ∈ Z.baseSet i := by rw [hi]; exact Z.mem_baseSet_at (σ x₀).1
  have hσ : ContinuousAt (fun x => ((Z.localTriv i) (σ x)).2) x₀ :=
    continuousAt_localTrivAt_snd_univ Z σ x₀
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

/-! ## The radial coefficient and the radial retraction -/

/-- The **radial coefficient** of a point of the total space: `(max 1 ‖p‖)⁻¹`, where `‖p‖` is the
fibrewise norm (`Work.Thom.fibreNorm`).  This is the amount by which the fibre vector of `p` has to
be scaled down to land in the closed unit disc; it is `1` on the closed disc and `‖p‖⁻¹` outside
it.  (As a map of the total space, `p ↦ (max 1 ‖p‖)⁻¹ • p.2` coincides with the classical
`p ↦ (min 1 ‖p‖⁻¹) • p.2`, see the module docstring; the present form is the continuous one.) -/
def radialCoeff (Z : RealBundle B F ι) (p : Z.TotalSpace) : ℝ := (max 1 (fibreNorm Z p))⁻¹

theorem radialCoeff_nonneg (Z : RealBundle B F ι) (p : Z.TotalSpace) : 0 ≤ radialCoeff Z p := by
  rw [radialCoeff]
  exact inv_nonneg.mpr (le_trans zero_le_one (le_max_left _ _))

theorem radialCoeff_le_one (Z : RealBundle B F ι) (p : Z.TotalSpace) : radialCoeff Z p ≤ 1 := by
  rw [radialCoeff]
  exact inv_le_one_of_one_le₀ (le_max_left _ _)

/-- The radial coefficient does not increase the fibrewise norm beyond `1`. -/
theorem radialCoeff_mul_fibreNorm_le_one (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    radialCoeff Z p * fibreNorm Z p ≤ 1 := by
  rcases le_total (fibreNorm Z p) 1 with h | h
  · calc radialCoeff Z p * fibreNorm Z p ≤ 1 * 1 :=
          mul_le_mul (radialCoeff_le_one Z p) h (norm_nonneg _) zero_le_one
       _ = 1 := by norm_num
  · have hn : (0:ℝ) < fibreNorm Z p := lt_of_lt_of_le zero_lt_one h
    have hmax : max 1 (fibreNorm Z p) = fibreNorm Z p := max_eq_right h
    rw [radialCoeff, hmax, inv_mul_cancel₀ hn.ne']

/-- On the closed unit disc the radial coefficient is `1`. -/
theorem radialCoeff_eq_one_of_fibreNorm_le (Z : RealBundle B F ι) (p : Z.TotalSpace)
    (h : fibreNorm Z p ≤ 1) : radialCoeff Z p = 1 := by
  rw [radialCoeff, max_eq_left h, inv_one]

/-- The radial coefficient is continuous (for a Euclidean bundle, so that `fibreNorm` is). -/
theorem continuous_radialCoeff {Z : RealBundle B F ι} (hZ : IsEuclidean Z) :
    Continuous (radialCoeff Z) :=
  (continuous_const.max (continuous_fibreNorm hZ)).inv₀ fun _ =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- The fibrewise rescaling by the radial coefficient lands in the closed unit disc. -/
theorem fibreNorm_radialCoeff_smul_le_one (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    fibreNorm Z (⟨p.1, radialCoeff Z p • p.2⟩ : Z.TotalSpace) ≤ 1 := by
  rw [fibreNorm_smul]
  rw [abs_of_nonneg (radialCoeff_nonneg Z p)]
  exact radialCoeff_mul_fibreNorm_le_one Z p

/-- **The radial retraction** of the total space onto the closed disc bundle, as a map. -/
def radialRetract (Z : RealBundle B F ι) (p : Z.TotalSpace) : DiscSub Z :=
  ⟨⟨p.1, radialCoeff Z p • p.2⟩, fibreNorm_radialCoeff_smul_le_one Z p⟩

@[simp] theorem radialRetract_coe (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    ((radialRetract Z p : DiscSub Z) : Z.TotalSpace) = ⟨p.1, radialCoeff Z p • p.2⟩ := rfl

/-- The radial retraction is continuous. -/
theorem continuous_radialRetract (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    Continuous (radialRetract Z) := by
  have h : Continuous (fun p : Z.TotalSpace => (⟨p.1, radialCoeff Z p • p.2⟩ : Z.TotalSpace)) :=
    continuous_smul_section_univ Z (ContinuousMap.id Z.TotalSpace)
      ⟨radialCoeff Z, continuous_radialCoeff hZ⟩
  exact h.subtype_mk fun p => fibreNorm_radialCoeff_smul_le_one Z p

/-! ## The inclusion and the retraction as continuous maps -/

/-- The inclusion `D(E) → E` of the closed disc bundle in the total space. -/
def discInclusion (Z : RealBundle B F ι) : C(DiscSub Z, Z.TotalSpace) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The radial retraction `E → D(E)` as a continuous map. -/
def discRetraction (Z : RealBundle B F ι) (hZ : IsEuclidean Z) : C(Z.TotalSpace, DiscSub Z) :=
  ⟨radialRetract Z, continuous_radialRetract Z hZ⟩

@[simp] theorem discRetraction_apply (Z : RealBundle B F ι) (hZ : IsEuclidean Z)
    (p : Z.TotalSpace) :
    (discRetraction Z hZ p : Z.TotalSpace) = ⟨p.1, radialCoeff Z p • p.2⟩ := rfl

/-- The composite `r ∘ i` of the radial retraction with the inclusion is the identity of the closed
disc bundle (the radial coefficient is `1` there). -/
theorem discRetraction_comp_inclusion (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    (discRetraction Z hZ).comp (discInclusion Z) = ContinuousMap.id (DiscSub Z) := by
  apply ContinuousMap.ext
  intro q
  change (radialRetract Z (q : Z.TotalSpace) : DiscSub Z) = q
  apply Subtype.ext
  rw [radialRetract_coe]
  have h : (q : Z.TotalSpace) ∈ closedDiscSet Z := q.2
  rw [mem_closedDiscSet] at h
  rw [radialCoeff_eq_one_of_fibreNorm_le Z (q : Z.TotalSpace) h, one_smul]

/-- **The inclusion followed by the radial retraction is homotopic to the identity of `E`**, by
linear interpolation of the radial scaling. -/
theorem homotopic_inclusion_comp_retraction (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    ContinuousMap.Homotopic ((discInclusion Z).comp (discRetraction Z hZ))
      (ContinuousMap.id Z.TotalSpace) := by
  have hκ : Continuous (fun q : unitInterval × Z.TotalSpace =>
      radialCoeff Z q.2 + ((q.1 : unitInterval) : ℝ) * (1 - radialCoeff Z q.2)) :=
    ((continuous_radialCoeff hZ).comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_const.sub ((continuous_radialCoeff hZ).comp continuous_snd)))
  have hcont : Continuous (fun q : unitInterval × Z.TotalSpace =>
      (⟨q.2.1, (radialCoeff Z q.2 + ((q.1 : unitInterval) : ℝ) * (1 - radialCoeff Z q.2)) •
        q.2.2⟩ : Z.TotalSpace)) :=
    continuous_smul_section_univ Z
      ((ContinuousMap.id Z.TotalSpace).comp
        (⟨fun q : unitInterval × Z.TotalSpace => q.2, continuous_snd⟩ :
          C(unitInterval × Z.TotalSpace, Z.TotalSpace)))
      ⟨fun q : unitInterval × Z.TotalSpace =>
        radialCoeff Z q.2 + ((q.1 : unitInterval) : ℝ) * (1 - radialCoeff Z q.2), hκ⟩
  refine ⟨ContinuousMap.Homotopy.mk ⟨_, hcont⟩ ?_ ?_⟩
  · intro p
    show (⟨p.1, (radialCoeff Z p + ((0 : unitInterval) : ℝ) * (1 - radialCoeff Z p)) • p.2⟩ :
      Z.TotalSpace) = _
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero]
    rfl
  · intro p
    show (⟨p.1, (radialCoeff Z p + ((1 : unitInterval) : ℝ) * (1 - radialCoeff Z p)) • p.2⟩ :
      Z.TotalSpace) = p
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    rw [show radialCoeff Z p + 1 * (1 - radialCoeff Z p) = 1 by ring, one_smul]

/-! ## The homotopy equivalence -/

/-- The inclusion of the closed unit disc bundle `D(E)` of a Euclidean real bundle `Z` into the
total space `E` is a homotopy equivalence.  The homotopy inverse is the radial retraction
`p ↦ ⟨p.1, min 1 (fibreNorm Z p)⁻¹ • p.2⟩`, which retracts `E` onto `D(E)` along the linear
interpolation of the radial scaling; `IsEuclidean Z` is needed so that the fibrewise norm
`Work.Thom.fibreNorm` is continuous (`Work.Thom.continuous_fibreNorm`), and the fibrewise rescaling
is continuous by `Work.Thom.continuous_smul_section`. -/
theorem discSub_homotopyEquiv {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} (Z : Work.TangentClasses.RealBundle B F ι)
    (hZ : Work.Thom.IsEuclidean Z) :
    ∃ e : ContinuousMap.HomotopyEquiv (Work.Thom.DiscSub Z) Z.TotalSpace,
      ⇑e.toFun = (Subtype.val : Work.Thom.DiscSub Z → Z.TotalSpace) := by
  refine ⟨⟨discInclusion Z, discRetraction Z hZ, ?_, ?_⟩, rfl⟩
  · have h : (discRetraction Z hZ).comp (discInclusion Z) = ContinuousMap.id (DiscSub Z) :=
      discRetraction_comp_inclusion Z hZ
    simpa only [h] using ContinuousMap.Homotopic.refl (ContinuousMap.id (DiscSub Z))
  · exact homotopic_inclusion_comp_retraction Z hZ

end

end Work.Thom
