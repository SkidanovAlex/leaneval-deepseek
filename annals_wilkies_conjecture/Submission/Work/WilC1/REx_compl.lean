import Mathlib
import Submission.Work.WilC1.Defs
import Submission.Work.WilC1.REx_preimage

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC1

theorem REx_compl
    (hconv : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), REx (Fin n) X ↔ WilkiesDesign.RExpExist X)
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X →
      WilkiesDesign.RExpExist Xᶜ)
    {ι : Type} [Fintype ι] (X : Set (ι → ℝ)) (hX : REx ι X) : REx ι Xᶜ := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  -- Transport `X` to `Fin (card ι)` and complement there.
  have hY : REx (Fin (Fintype.card ι)) {w : Fin (Fintype.card ι) → ℝ | w ∘ e ∈ X} :=
    REx_preimage (e : ι → Fin (Fintype.card ι)) hX
  have hExpY : WilkiesDesign.RExpExist {w : Fin (Fintype.card ι) → ℝ | w ∘ e ∈ X} :=
    (hconv _ _).mp hY
  have hExpYc :
      WilkiesDesign.RExpExist ({w : Fin (Fintype.card ι) → ℝ | w ∘ e ∈ X})ᶜ :=
    hR _ _ hExpY
  have hYc :
      REx (Fin (Fintype.card ι)) ({w : Fin (Fintype.card ι) → ℝ | w ∘ e ∈ X})ᶜ :=
    (hconv _ _).mpr hExpYc
  -- The complement is the transported copy of `Xᶜ`.
  have hset : ({w : Fin (Fintype.card ι) → ℝ | w ∘ e ∈ X})ᶜ
      = {w : Fin (Fintype.card ι) → ℝ | w ∘ e ∈ Xᶜ} := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  rw [hset] at hYc
  -- Transport back along `e.symm`; the composite reindexing is the identity.
  refine REx.congr ?_ (REx_preimage (e.symm : Fin (Fintype.card ι) → ι) hYc)
  ext w
  have hcomp : ((w ∘ e.symm) ∘ e) = w := by
    funext x
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, hcomp]

end Work.WilC1
