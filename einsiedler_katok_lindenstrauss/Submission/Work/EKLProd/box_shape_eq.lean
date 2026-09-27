import Mathlib
import Submission.Work.EKLProd.BoxFlowerDefs

namespace Work.EKLProd

open Work.EKLContract

theorem box_shape_eq {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    {R : ℝ} {C : Set Work.EKLContract.X3} {W : ℕ → Set Work.EKLContract.X3}
    (hfreeH : ∀ c ∈ C, ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ • c = h₂ • c → h₁ = h₂)
    {c : Work.EKLContract.X3} (hc : c ∈ C)
    {g₀ : Work.EKLContract.SL3} (hg₀ : g₀ ∈ Work.EKLProd.prodBox T U R)
    {x : Work.EKLContract.X3} (hx : g₀ • c = x)
    (hatom : Work.EKLContract.atom (Work.EKLProd.boxSigma T U R C W) x =
      Work.EKLProd.boxCollar T U R {c}) :
    Work.EKLContract.shape (Work.EKLProd.boxSigma T U R C W) H x =
      {g : Work.EKLContract.SL3 | g ∈ H ∧ g * g₀ ∈ Work.EKLProd.prodBox T U R} := by
  have hg₀H : g₀ ∈ (H : Set Work.EKLContract.SL3) := prodBox_subset_H hTH hUH hg₀
  have key : ∀ g ∈ H, (g * g₀) • c ∈ Work.EKLProd.boxCollar T U R {c}
      ↔ g * g₀ ∈ Work.EKLProd.prodBox T U R := by
    intro g hg
    rw [Work.EKLProd.boxCollar_eq T U R {c}]
    constructor
    · rintro ⟨k, hk, c', hc', hkc'⟩
      have hc'c : c' = c := by simpa using hc'
      rw [hc'c] at hkc'
      have hk_eq : k = g * g₀ :=
        hfreeH c hc k (prodBox_subset_H hTH hUH hk) (g * g₀) (H.mul_mem hg hg₀H) hkc'
      rw [hk_eq] at hk
      exact hk
    · rintro hk
      exact ⟨g * g₀, hk, c, rfl, rfl⟩
  rw [Work.EKLContract.shape, hatom]
  ext g
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hgH, hgx⟩
    refine ⟨hgH, ?_⟩
    rw [← hx, ← mul_smul] at hgx
    exact (key g hgH).mp hgx
  · rintro ⟨hgH, hgg⟩
    refine ⟨hgH, ?_⟩
    rw [← hx, ← mul_smul]
    exact (key g hgH).mpr hgg

end Work.EKLProd
