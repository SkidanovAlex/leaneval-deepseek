import Mathlib
import Submission.Work.Isotopy.contDiffOn_symm_of_contDiffOn

namespace Work.Drive.N2

open ContinuousLinearMap Set Metric Filter Function
open scoped NNReal Topology

/-- In a topological ring of continuous linear endomorphisms, being a unit of the ring is the same
as being (the underlying map of) a continuous linear equivalence.  This lets us use the openness of
the units (`Units.isOpen`) to see that invertibility of a continuous linear endomorphism is an open
condition. -/
lemma isInvertible_iff_isUnit_clm {M : Type*} [AddCommMonoid M] [Module ℝ M] [TopologicalSpace M]
    (f : M →L[ℝ] M) : f.IsInvertible ↔ IsUnit f := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ((ContinuousLinearEquiv.unitsEquiv ℝ M).symm A).isUnit
  · rintro ⟨u, rfl⟩
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ M u, rfl⟩

/- Route: restrict to a small ball B ⊆ U around x₀ on which `fderiv ℝ F` is invertible everywhere
(the invertible continuous linear maps form an open set: `Units.isOpen` together with
`ContinuousLinearMap.isUnit_iff_bijective`; use `ContDiffOn.continuousOn_fderiv_of_isOpen` and
`Filter.Tendsto.eventually` to find a ball), small enough that `ApproximatesLinearOn F L B c` holds with
`c < ‖L.symm‖₊⁻¹` (get `HasStrictFDerivAt F (L : _ →L[ℝ] _) x₀` from `hF` and `hL` via
`ContDiffAt.hasStrictFDerivAt'`, then `HasStrictFDerivAt.approximates_deriv_on_open_nhds` and
`ApproximatesLinearOn.mono_set`).  Then `ApproximatesLinearOn.toOpenPartialHomeomorph` gives a partial
homeomorphism whose source is exactly B and whose underlying map is F; smoothness of the inverse at every
point of the target follows from `OpenPartialHomeomorph.contDiffAt_symm` (the derivative of F at the
relevant point is invertible by the choice of B, and F is smooth there because B ⊆ U), and pointwise
`ContDiffAt` gives `ContDiffOn` via `ContDiffAt.contDiffWithinAt`. -/
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_local_diffeomorph (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (U : Set (EuclideanSpace ℝ (Fin 2))) (x₀ : EuclideanSpace ℝ (Fin 2))
    (hUo : IsOpen U) (hxU : x₀ ∈ U) (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (hL : HasFDerivAt F (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) x₀) :
    ∃ φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)),
      x₀ ∈ φ.source ∧ φ.source ⊆ U ∧
      (∀ x ∈ φ.source, φ x = F x) ∧
      (∀ x ∈ φ.source, ContinuousLinearMap.IsInvertible (fderiv ℝ F x)) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) φ.source ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ.symm φ.target := by
  -- `F` is `C^∞`, hence strictly differentiable, at `x₀`.
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hFAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F x₀ := hF.contDiffAt (hUo.mem_nhds hxU)
  have hstrict : HasStrictFDerivAt F
      (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) x₀ :=
    hFAt.hasStrictFDerivAt' hL hn
  -- An open neighbourhood `s ∋ x₀` on which `F` approximates `L`.
  obtain ⟨s, hsx, hsopen, hsapp⟩ := hstrict.approximates_deriv_on_open_nhds (f' := L)
  -- A neighbourhood of `x₀` on which `fderiv ℝ F` is invertible: the units of the ring of
  -- continuous linear endomorphisms form an open set, and `fderiv ℝ F` is continuous at `x₀`.
  have hcont : ContinuousAt (fderiv ℝ F) x₀ := hFAt.continuousAt_fderiv hn
  have hunit : IsUnit (fderiv ℝ F x₀) := by
    rw [hL.fderiv]
    exact (isInvertible_iff_isUnit_clm
      (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))).mp isInvertible_equiv
  have hnhds : (fderiv ℝ F) ⁻¹'
      {f : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) | IsUnit f} ∈ 𝓝 x₀ :=
    hcont.preimage_mem_nhds (Units.isOpen.mem_nhds hunit)
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hnhds
  -- The ball on which we build the local inverse.
  let B : Set (EuclideanSpace ℝ (Fin 2)) := U ∩ s ∩ ball x₀ r
  have hBopen : IsOpen B := (hUo.inter hsopen).inter isOpen_ball
  have hx₀B : x₀ ∈ B := ⟨⟨hxU, hsx⟩, mem_ball_self hrpos⟩
  have hBU : B ⊆ U := fun x hx => hx.1.1
  have hBs : B ⊆ s := fun x hx => hx.1.2
  have hBr : B ⊆ ball x₀ r := fun x hx => hx.2
  have hBapp : ApproximatesLinearOn F
      (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) B
      (‖(L.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))‖₊⁻¹ / 2) :=
    hsapp.mono_set hBs
  have hc : Subsingleton (EuclideanSpace ℝ (Fin 2)) ∨
      (‖(L.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))‖₊⁻¹ / 2 : ℝ≥0) <
        ‖(L.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))‖₊⁻¹ :=
    L.subsingleton_or_nnnorm_symm_pos.imp id
      (fun h => NNReal.half_lt_self (ne_of_gt (inv_pos.2 h)))
  have hinvB : ∀ x ∈ B, (fderiv ℝ F x).IsInvertible := by
    intro x hx
    exact (isInvertible_iff_isUnit_clm (fderiv ℝ F x)).mpr (hrsub hx.2)
  have hFsmoothB : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F B := hF.mono hBU
  -- The local inverse, as a partial homeomorphism with source exactly `B` and underlying map `F`.
  let φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
    ApproximatesLinearOn.toOpenPartialHomeomorph F B hBapp hc hBopen
  have hφsrc : φ.source = B := rfl
  have hφcoe : (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) = F := rfl
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφsrc]; exact hx₀B
  · rw [hφsrc]; exact hBU
  · intro x hx; rw [hφcoe]
  · intro x hx; rw [hφsrc] at hx; exact hinvB x hx
  · rw [hφsrc, hφcoe]; exact hFsmoothB
  · exact Work.Isotopy.contDiffOn_symm_of_contDiffOn F B hBopen hFsmoothB hinvB φ hφcoe
      (by rw [hφsrc])

end Work.Drive.N2
