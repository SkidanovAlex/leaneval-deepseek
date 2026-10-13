/-
  Area C0: `RExpExistI` is closed under complement, given the frozen hypothesis `hR`
  (Gabrielov's theorem of the complement for `ℝ_rexp`, as stated in the C0 hole).
-/
import Submission.Work.WilC0.Bridge

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace Work.WilC0

open WilkiesDesign (rexp RExpExist)

/-- `RExpExistI` is closed under complement, given the hypothesis `hR` on `Fin n`-indexed sets. -/
theorem RExpExistI.compl {κ : Type} [Fintype κ] {X : Set (κ → ℝ)}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hX : RExpExistI X) : RExpExistI Xᶜ := by
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hY : RExpExistI {z : Fin (Fintype.card κ) → ℝ | z ∘ ⇑e ∈ X} := hX.pullback (⇑e)
  have hYc : RExpExist ({z : Fin (Fintype.card κ) → ℝ | z ∘ ⇑e ∈ X}ᶜ) :=
    hR _ _ ((rexExistI_iff_rexExist _).mp hY)
  have hYci : RExpExistI ({z : Fin (Fintype.card κ) → ℝ | z ∘ ⇑e ∈ X}ᶜ) :=
    (rexExistI_iff_rexExist _).mpr hYc
  have hcomp : ∀ z : κ → ℝ, (z ∘ ⇑e.symm) ∘ ⇑e = z := by
    intro z
    funext a
    simp
  refine (hYci.pullback (⇑e.symm)).of_eq ?_
  ext z
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  rw [hcomp z]

end Work.WilC0
