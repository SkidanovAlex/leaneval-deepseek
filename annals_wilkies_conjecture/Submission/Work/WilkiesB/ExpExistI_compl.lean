import Mathlib
import Submission.Work.WilkiesB.Defs
import Submission.Work.WilkiesB.ExpExistI_pullback

noncomputable section

open Classical

namespace Work.WilkiesB

/-- `ExpExistI` is closed under complement, given the hypothesis `hW` (Gabrielov's theorem of the
complement for `ℝ_exp`, stated for `Fin n`-indexed sets as in the frozen `WilkiesDesign`).

The ambient index type `κ` is first identified with `Fin (Fintype.card κ)`; the frozen hypothesis
`hW` then applies to the corresponding `Fin`-indexed set, and the result is pulled back along
`e.symm`. -/
theorem ExpExistI_compl {κ : Type*} [Fintype κ] {X : Set (κ → ℝ)}
    (hW : ∀ (n : ℕ) (Y : Set (Fin n → ℝ)), WilkiesDesign.ExpExist Y → WilkiesDesign.ExpExist Yᶜ)
    (hX : ExpExistI X) : ExpExistI Xᶜ := by
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hY : ExpExistI {z : Fin (Fintype.card κ) → ℝ | z ∘ ⇑e ∈ X} :=
    ExpExistI_pullback (⇑e) hX
  have hYc : WilkiesDesign.ExpExist ({z : Fin (Fintype.card κ) → ℝ | z ∘ ⇑e ∈ X}ᶜ) :=
    hW (Fintype.card κ) _ ((expExist_iff_expExistI _).mpr hY)
  have hYci : ExpExistI ({z : Fin (Fintype.card κ) → ℝ | z ∘ ⇑e ∈ X}ᶜ) :=
    (expExist_iff_expExistI _).mp hYc
  have hcomp : ∀ z : κ → ℝ, (z ∘ ⇑e.symm) ∘ ⇑e = z := by
    intro z
    funext a
    simp
  refine (ExpExistI_pullback (⇑e.symm) hYci).of_eq ?_
  ext z
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  rw [hcomp z]

end Work.WilkiesB
