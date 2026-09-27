import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.starShapedRadial
import Submission.Work.Drive.N2Lead.starShapedComponents
import Submission.Work.Drive.N2Lead.radFlatKernel
import Submission.Work.Drive.N2Lead.starRegionsCore

set_option maxHeartbeats 1000000

/-!
# The star-regions certificate: the rows of the radial push

The two rows of the piecewise radial push `pushMap` of `starRegionsCore` that are consumed by
`isLevelIsotopy_ambient_local`:

* `pushMap_eq_imp`: if two points of the level picture have the same pushed image, then they lie in
  the same region and their planar projections differ by a positive multiple (about the centre) —
  the injectivity row;
* `pushMap_fderiv_eq_zero`: if the derivative of the push kills a tangent vector at a picture point,
  then the planar projection of that vector is a real multiple of the radius vector — the
  immersivity row (the kernel of the flattening radial map, `radFlatKernel`).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

variable {K : ℕ} {Ω : Fin K → Set ℂ} {o : Fin K → ℂ} {ρ : Fin K → ℝ}

/-- **The planar projection of the push, from a region.** -/
theorem proj2_pushMap_eq (hdisj : Pairwise fun k l : Fin K => Disjoint (Ω k) (Ω l))
    {s : ℝ} {v : E3} {k : Fin K} (hk : proj2 v ∈ Ω k) (hne : proj2 v ≠ o k) :
    proj2 (pushMap Ω o ρ s v) = o k + radCoeff (ρ k) s (v - pl (o k)) • (proj2 v - o k) := by
  rw [pushMap_of_mem hdisj s v k hk hne]
  have h1 : radFlat (pl (o k)) (ρ k) s v
      = (radFlat (pl (o k)) (ρ k) s v - pl (o k)) + pl (o k) := by abel
  rw [h1, proj2_add, proj2_radFlat_sub, proj2_sub, proj2_pl]
  abel

/-- **The push identifies two picture points only on a common ray** (in the same region). -/
theorem pushMap_eq_imp (hdisj : Pairwise fun k l : Fin K => Disjoint (Ω k) (Ω l))
    (hρ : ∀ k : Fin K, 0 < ρ k)
    (hconv : ∀ k : Fin K, Convex ℝ (Ω k))
    (hball : ∀ k : Fin K, Metric.closedBall (o k) (ρ k) ⊆ Ω k)
    {s : ℝ} {v₁ v₂ : E3} {k₁ k₂ : Fin K}
    (h₁ : proj2 v₁ ∈ Ω k₁) (h₁' : proj2 v₁ ≠ o k₁)
    (h₂ : proj2 v₂ ∈ Ω k₂) (h₂' : proj2 v₂ ≠ o k₂)
    (h : pushMap Ω o ρ s v₁ = pushMap Ω o ρ s v₂) :
    k₁ = k₂ ∧ ∃ t : ℝ, 0 < t ∧ proj2 v₂ - o k₂ = t • (proj2 v₁ - o k₂) := by
  have hmem₁ : proj2 (pushMap Ω o ρ s v₁) ∈ Ω k₁ :=
    proj2_pushMap_mem hdisj hρ hconv hball (s := s) (v := v₁) (k := k₁) h₁ h₁'
  have hmem₂ : proj2 (pushMap Ω o ρ s v₂) ∈ Ω k₂ :=
    proj2_pushMap_mem hdisj hρ hconv hball (s := s) (v := v₂) (k := k₂) h₂ h₂'
  have hproj : proj2 (pushMap Ω o ρ s v₁) = proj2 (pushMap Ω o ρ s v₂) := by rw [h]
  have hk : k₁ = k₂ := by
    by_contra hne'
    refine (Set.disjoint_left.mp (hdisj hne') hmem₁) ?_
    rw [hproj]
    exact hmem₂
  refine ⟨hk, ?_⟩
  have h₁₂ : proj2 v₁ ∈ Ω k₂ := hk ▸ h₁
  have h₁'' : proj2 v₁ ≠ o k₂ := hk ▸ h₁'
  have hv₁ : proj2 (pushMap Ω o ρ s v₁)
      = o k₂ + radCoeff (ρ k₂) s (v₁ - pl (o k₂)) • (proj2 v₁ - o k₂) :=
    proj2_pushMap_eq hdisj (s := s) (v := v₁) (k := k₂) h₁₂ h₁''
  have hv₂ : proj2 (pushMap Ω o ρ s v₂)
      = o k₂ + radCoeff (ρ k₂) s (v₂ - pl (o k₂)) • (proj2 v₂ - o k₂) :=
    proj2_pushMap_eq hdisj (s := s) (v := v₂) (k := k₂) h₂ h₂'
  have hc₁ : 0 < radCoeff (ρ k₂) s (v₁ - pl (o k₂)) :=
    radCoeff_pos (hρ k₂) s (by rw [proj2_sub, proj2_pl]; exact sub_ne_zero.mpr h₁'')
  have hc₂ : 0 < radCoeff (ρ k₂) s (v₂ - pl (o k₂)) :=
    radCoeff_pos (hρ k₂) s (by rw [proj2_sub, proj2_pl]; exact sub_ne_zero.mpr h₂')
  have hkey : radCoeff (ρ k₂) s (v₁ - pl (o k₂)) • (proj2 v₁ - o k₂)
      = radCoeff (ρ k₂) s (v₂ - pl (o k₂)) • (proj2 v₂ - o k₂) := by
    have h2 : o k₂ + radCoeff (ρ k₂) s (v₁ - pl (o k₂)) • (proj2 v₁ - o k₂)
        = o k₂ + radCoeff (ρ k₂) s (v₂ - pl (o k₂)) • (proj2 v₂ - o k₂) := by
      rw [← hv₁, ← hv₂]
      exact hproj
    exact add_left_cancel h2
  have h' : (radCoeff (ρ k₂) s (v₂ - pl (o k₂)))⁻¹
        • (radCoeff (ρ k₂) s (v₁ - pl (o k₂)) • (proj2 v₁ - o k₂))
      = proj2 v₂ - o k₂ := by
    rw [hkey, smul_smul, inv_mul_cancel₀ hc₂.ne', one_smul]
  refine ⟨radCoeff (ρ k₂) s (v₁ - pl (o k₂)) / radCoeff (ρ k₂) s (v₂ - pl (o k₂)),
    div_pos hc₁ hc₂, ?_⟩
  calc proj2 v₂ - o k₂
      = (radCoeff (ρ k₂) s (v₂ - pl (o k₂)))⁻¹
          • (radCoeff (ρ k₂) s (v₁ - pl (o k₂)) • (proj2 v₁ - o k₂)) := h'.symm
    _ = ((radCoeff (ρ k₂) s (v₂ - pl (o k₂)))⁻¹
          * radCoeff (ρ k₂) s (v₁ - pl (o k₂))) • (proj2 v₁ - o k₂) := by rw [smul_smul]
    _ = (radCoeff (ρ k₂) s (v₁ - pl (o k₂)) / radCoeff (ρ k₂) s (v₂ - pl (o k₂)))
          • (proj2 v₁ - o k₂) := by rw [div_eq_inv_mul]

/-- **The kernel of the push, in the planar projection.** -/
theorem pushMap_fderiv_eq_zero (hΩ : ∀ k : Fin K, IsOpen (Ω k))
    (hdisj : Pairwise fun k l : Fin K => Disjoint (Ω k) (Ω l))
    (hρ : ∀ k : Fin K, 0 < ρ k)
    {s : ℝ} {v w : E3} {k : Fin K} (hk : proj2 v ∈ Ω k) (hne : proj2 v ≠ o k)
    (h : fderiv ℝ (pushMap Ω o ρ s) v w = 0) :
    ∃ t : ℝ, proj2 w = t • (proj2 v - o k) := by
  have hne' : proj2 (v - pl (o k)) ≠ 0 := by
    rwa [proj2_sub, proj2_pl, sub_ne_zero]
  have h₁ : {v' : E3 | proj2 v' ∈ Ω k ∧ proj2 v' ≠ o k} ∈ 𝓝 v :=
    Filter.inter_mem (((hΩ k).preimage proj2CLM.continuous).mem_nhds hk)
      ((isOpen_ne.preimage proj2CLM.continuous).mem_nhds hne)
  have heq : pushMap Ω o ρ s =ᶠ[𝓝 v] radFlat (pl (o k)) (ρ k) s := by
    filter_upwards [h₁] with v' hv'
    exact pushMap_of_mem hdisj s v' k hv'.1 hv'.2
  rw [heq.fderiv_eq] at h
  exact radFlatKernel (hρ k) hne' h

end

end Work.Drive.N2Lead
