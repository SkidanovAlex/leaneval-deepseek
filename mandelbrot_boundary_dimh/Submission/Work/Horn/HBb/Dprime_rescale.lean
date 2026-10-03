import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts

namespace Work.Horn.HBb

open MandelDim Set Metric Filter Topology

theorem Dprime_rescale {D D' : Set ℂ} {s : ℂ} (hs : s ≠ 0)
    (h1 : IsOpen D') (h2 : (0 : ℂ) ∈ D') (h3 : D' ⊆ D) (h4 : Bornology.IsBounded D')
    (h5 : ∀ C : Set ℂ, IsPreconnected C → C ⊆ D \ {0} → (C ∩ D').Nonempty → C ⊆ D') :
    IsOpen ((fun ζ : ℂ => s * ζ) '' D') ∧
    (0 : ℂ) ∈ (fun ζ : ℂ => s * ζ) '' D' ∧
    (fun ζ : ℂ => s * ζ) '' D' ⊆ (fun ζ : ℂ => s * ζ) '' D ∧
    Bornology.IsBounded ((fun ζ : ℂ => s * ζ) '' D') ∧
    (∀ C : Set ℂ, IsPreconnected C →
      C ⊆ (fun ζ : ℂ => s * ζ) '' D \ {0} →
      (C ∩ (fun ζ : ℂ => s * ζ) '' D').Nonempty → C ⊆ (fun ζ : ℂ => s * ζ) '' D') := by
  -- `ζ ↦ s * ζ` and `ζ ↦ s⁻¹ * ζ` are mutually inverse for `s ≠ 0`
  have key1 : ∀ z : ℂ, (fun ζ : ℂ => s⁻¹ * ζ) ((fun ζ : ℂ => s * ζ) z) = z := by
    intro z; show s⁻¹ * (s * z) = z; rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have key2 : ∀ z : ℂ, (fun ζ : ℂ => s * ζ) ((fun ζ : ℂ => s⁻¹ * ζ) z) = z := by
    intro z; show s * (s⁻¹ * z) = z; rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the rescaling is an open map
    simpa only [smul_eq_mul] using (isOpenMap_smul₀ (G₀ := ℂ) (α := ℂ) hs) D' h1
  · -- `0` is the image of `0`
    exact ⟨0, h2, by simp⟩
  · -- monotonicity of the image
    exact Set.image_mono h3
  · -- boundedness is preserved by the rescaling
    have h := Bornology.IsBounded.smul₀ h4 s
    rw [← Set.image_smul] at h
    simpa only [smul_eq_mul] using h
  · -- the connectivity clause is transported by pulling back along `ζ ↦ s⁻¹ * ζ`
    intro C hCpre hCsub hCint
    have hCpre' : IsPreconnected ((fun ζ : ℂ => s⁻¹ * ζ) '' C) :=
      hCpre.image _ (continuous_const.mul continuous_id).continuousOn
    have hCsub' : (fun ζ : ℂ => s⁻¹ * ζ) '' C ⊆ D \ {0} := by
      rintro y ⟨c, hc, rfl⟩
      obtain ⟨hcD, hcne⟩ := hCsub hc
      obtain ⟨d, hd, hdc⟩ := hcD
      have hd_ne : d ≠ 0 := by
        intro hd0
        exact hcne (by rw [← hdc, hd0]; simp)
      refine ⟨?_, ?_⟩
      · rw [← hdc, key1 d]; exact hd
      · rw [← hdc, key1 d]; exact hd_ne
    have hCint' : ((fun ζ : ℂ => s⁻¹ * ζ) '' C ∩ D').Nonempty := by
      obtain ⟨c, hcC, hcD'⟩ := hCint
      obtain ⟨d', hd', hd'c⟩ := hcD'
      refine ⟨d', ⟨?_, hd'⟩⟩
      exact ⟨c, hcC, by rw [← hd'c, key1 d']⟩
    have hC'sub : (fun ζ : ℂ => s⁻¹ * ζ) '' C ⊆ D' := h5 _ hCpre' hCsub' hCint'
    intro c hc
    exact ⟨s⁻¹ * c, hC'sub ⟨c, hc, rfl⟩, key2 c⟩

end Work.Horn.HBb
