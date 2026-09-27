import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Compactify

theorem antitone_compl_image_coe {X : Type*} [TopologicalSpace X] {U : ℕ → Set X} (hmono : Monotone U) : Antitone fun k => (((↑) '' U k : Set (OnePoint X))ᶜ) := by
  intro a b hab x hx hxa
  exact hx (Set.image_mono (hmono hab) hxa)

end Work.Brown.Compactify
