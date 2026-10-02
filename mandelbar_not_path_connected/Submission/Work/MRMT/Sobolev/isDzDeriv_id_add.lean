import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.isDzDeriv_moll_gen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Sobolev

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

open Work.MRMT

/-- The weak (distributional) `∂`-derivative is additive: the weak `∂`-derivative of a sum is
the sum of the weak `∂`-derivatives. -/
theorem isDzDeriv_add {f₁ g₁ f₂ g₂ : ℂ → ℂ} (h₁ : IsDzDeriv f₁ g₁) (h₂ : IsDzDeriv f₂ g₂) :
    IsDzDeriv (fun z => f₁ z + f₂ z) (fun z => g₁ z + g₂ z) := by
  obtain ⟨hf₁, hg₁, hr₁⟩ := h₁
  obtain ⟨hf₂, hg₂, hr₂⟩ := h₂
  refine ⟨hf₁.add hf₂, hg₁.add hg₂, ?_⟩
  intro φ
  obtain ⟨hI₁, hJ₁, hE₁⟩ := hr₁ φ
  obtain ⟨hI₂, hJ₂, hE₂⟩ := hr₂ φ
  refine ⟨?_, ?_, ?_⟩
  · refine (hI₁.add hI₂).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  · refine (hJ₁.add hJ₂).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  · have hL : (∫ z, (f₁ z + f₂ z) * dz (φ : ℂ → ℂ) z)
        = (∫ z, f₁ z * dz (φ : ℂ → ℂ) z) + (∫ z, f₂ z * dz (φ : ℂ → ℂ) z) := by
      rw [← integral_add hI₁ hI₂]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    have hR : (∫ z, (g₁ z + g₂ z) * (φ : ℂ → ℂ) z)
        = (∫ z, g₁ z * (φ : ℂ → ℂ) z) + (∫ z, g₂ z * (φ : ℂ → ℂ) z) := by
      rw [← integral_add hJ₁ hJ₂]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    calc (∫ z, (f₁ z + f₂ z) * dz (φ : ℂ → ℂ) z)
        = (∫ z, f₁ z * dz (φ : ℂ → ℂ) z) + (∫ z, f₂ z * dz (φ : ℂ → ℂ) z) := hL
      _ = (-∫ z, g₁ z * (φ : ℂ → ℂ) z) + (-∫ z, g₂ z * (φ : ℂ → ℂ) z) := by
            rw [hE₁, hE₂]
      _ = -((∫ z, g₁ z * (φ : ℂ → ℂ) z) + (∫ z, g₂ z * (φ : ℂ → ℂ) z)) := by ring
      _ = -(∫ z, (g₁ z + g₂ z) * (φ : ℂ → ℂ) z) := by rw [← hR]

/-- The identity function has weak `∂`-derivative the constant `1`. -/
theorem isDzDeriv_id : IsDzDeriv (fun z : ℂ => z) (fun _ : ℂ => (1 : ℂ)) := by
  have h : IsDzDeriv (fun z : ℂ => z) (dz (fun z : ℂ => z)) :=
    Work.MRMT.Weyl.isDzDeriv_dz (u := fun z : ℂ => z)
      (n := (⊤ : WithTop ℕ∞)) contDiff_id (by simp)
  exact Work.MRMT.Weyl.isDzDeriv_congr h (fun z => Work.MRMT.dz_id z)

theorem isDzDeriv_id_add {F g : ℂ → ℂ} (h : Work.MRMT.IsDzDeriv F g) :
    Work.MRMT.IsDzDeriv (fun z : ℂ => z + F z) (fun z : ℂ => 1 + g z) := by
  have h' := isDzDeriv_add isDzDeriv_id h
  simpa using h'

end Work.MRMT.Sobolev
