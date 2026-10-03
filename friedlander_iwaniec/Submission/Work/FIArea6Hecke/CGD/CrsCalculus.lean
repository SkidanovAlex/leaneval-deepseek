import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs

namespace Work.FIArea6Hecke.CGD

open scoped BigOperators

noncomputable section

/-- The (unique) element of a complete residue system `S` mod `M` congruent to `z` mod `M`. -/
def crsRep (M : GaussianInt) (S : Finset GaussianInt)
    (hS : Work.FIArea6Hecke.R.IsCRS M S) (z : GaussianInt) : GaussianInt :=
  Classical.choose (hS z).exists

lemma crsRep_mem (M : GaussianInt) (S : Finset GaussianInt)
    (hS : Work.FIArea6Hecke.R.IsCRS M S) (z : GaussianInt) : crsRep M S hS z ∈ S :=
  (Classical.choose_spec (hS z).exists).1

lemma crsRep_dvd (M : GaussianInt) (S : Finset GaussianInt)
    (hS : Work.FIArea6Hecke.R.IsCRS M S) (z : GaussianInt) :
    M ∣ z - crsRep M S hS z :=
  (Classical.choose_spec (hS z).exists).2

lemma crsRep_unique (M : GaussianInt) (S : Finset GaussianInt)
    (hS : Work.FIArea6Hecke.R.IsCRS M S) {z s : GaussianInt} (hs : s ∈ S)
    (h : M ∣ z - s) : s = crsRep M S hS z :=
  ExistsUnique.unique (hS z) ⟨hs, h⟩ (Classical.choose_spec (hS z).exists)

/-- A complete residue system mod `M` has pairwise distinct residues: two of its elements
congruent mod `M` are equal. -/
lemma eq_of_mem_of_dvd (M : GaussianInt) (S : Finset GaussianInt)
    (hS : Work.FIArea6Hecke.R.IsCRS M S) {s₁ s₂ : GaussianInt} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S)
    (h : M ∣ s₁ - s₂) : s₁ = s₂ :=
  ExistsUnique.unique (hS s₁) ⟨h₁, by rw [sub_self]; exact dvd_zero M⟩ ⟨h₂, h⟩

theorem CrsCalculus (M : GaussianInt) (S T : Finset GaussianInt)
    (hS : Work.FIArea6Hecke.R.IsCRS M S) (hT : Work.FIArea6Hecke.R.IsCRS M T)
    (f : GaussianInt → ℂ) (hf : ∀ z w : GaussianInt, M ∣ (z - w) → f z = f w) :
    (Finset.sum S f = Finset.sum T f) ∧
    (∀ w : GaussianInt, Work.FIArea6Hecke.R.IsCRS M (S.image (fun s => s + w))) ∧
    (∀ δ : GaussianInt, Work.FIArea6Hecke.R.IsUnitMod M δ → δ ≠ 0 →
      Work.FIArea6Hecke.R.IsCRS M (S.image (fun s => s * δ))) ∧
    (∀ w : GaussianInt, Finset.sum (S.image (fun s => s + w)) f =
      Finset.sum S (fun s => f (s + w))) ∧
    (∀ δ : GaussianInt, δ ≠ 0 → Finset.sum (S.image (fun s => s * δ)) f =
      Finset.sum S (fun s => f (s * δ))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the two CRS have the same sum
    refine Finset.sum_bij (fun s _ => crsRep M T hT s) ?_ ?_ ?_ ?_
    · intro s _
      exact crsRep_mem M T hT s
    · intro s₁ hs₁ s₂ hs₂ heq
      have h₁ : M ∣ s₁ - crsRep M T hT s₁ := crsRep_dvd M T hT s₁
      have h₂ : M ∣ crsRep M T hT s₂ - s₂ := by
        simpa using dvd_neg.mpr (crsRep_dvd M T hT s₂)
      rw [heq] at h₁
      refine eq_of_mem_of_dvd M S hS hs₁ hs₂ ?_
      convert dvd_add h₁ h₂ using 1
      ring
    · intro b hb
      refine ⟨crsRep M S hS b, crsRep_mem M S hS b, ?_⟩
      refine (crsRep_unique M T hT hb ?_).symm
      simpa using dvd_neg.mpr (crsRep_dvd M S hS b)
    · intro s _
      exact hf s (crsRep M T hT s) (crsRep_dvd M T hT s)
  · -- translation of a CRS is a CRS
    intro w z
    refine ⟨crsRep M S hS (z - w) + w, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨crsRep M S hS (z - w), crsRep_mem M S hS (z - w), rfl⟩
    · have h := crsRep_dvd M S hS (z - w)
      convert h using 1
      ring
    · rintro y ⟨hy_mem, hy_dvd⟩
      obtain ⟨s₁, hs₁, rfl⟩ := Finset.mem_image.mp hy_mem
      have h : M ∣ (z - w) - s₁ := by
        convert hy_dvd using 1
        ring
      rw [crsRep_unique M S hS hs₁ h]
  · -- multiplication by a unit mod `M` is a CRS
    rintro δ ⟨w, hw⟩ _ z
    refine ⟨crsRep M S hS (z * w) * δ, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨crsRep M S hS (z * w), crsRep_mem M S hS (z * w), rfl⟩
    · obtain ⟨k, hk⟩ := hw
      have h1 : M ∣ (z * w - crsRep M S hS (z * w)) * δ :=
        dvd_mul_of_dvd_left (crsRep_dvd M S hS (z * w)) δ
      have h2 : M ∣ z * (w * δ - 1) := by
        rw [show w * δ - 1 = M * k from by rw [mul_comm w δ]; exact hk]
        exact ⟨z * k, by ring⟩
      convert h1.sub h2 using 1
      ring
    · rintro y ⟨hy_mem, hy_dvd⟩
      obtain ⟨s₁, hs₁, rfl⟩ := Finset.mem_image.mp hy_mem
      obtain ⟨k, hk⟩ := hw
      have h1 : M ∣ (z - s₁ * δ) * w := dvd_mul_of_dvd_left hy_dvd w
      have h2 : M ∣ s₁ * δ * w - s₁ := by
        have heq : s₁ * δ * w - s₁ = s₁ * (δ * w - 1) := by ring
        rw [heq, hk]
        exact ⟨s₁ * k, by ring⟩
      have hmain : M ∣ z * w - s₁ := by
        convert dvd_add h1 h2 using 1
        ring
      rw [crsRep_unique M S hS hs₁ hmain]
  · -- sums over a translate
    intro w
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact add_right_cancel hxy
  · -- sums over a dilation
    intro δ hδ0
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact mul_right_cancel₀ hδ0 hxy

end

end Work.FIArea6Hecke.CGD
