import Mathlib
import Submission.Work.ORDunwoody.Basic

namespace Work.ORDunwoody.Lemmas

/-- The image of a finitely generated subgroup under a group homomorphism is
finitely generated. -/
theorem fg_map {G H : Type*} [Group G] [Group H] (f : G →* H) {K : Subgroup G}
    (hK : K.FG) : (K.map f).FG := by
  rw [Subgroup.fg_iff] at hK ⊢
  rcases hK with ⟨S, hS, hSfin⟩
  exact ⟨f '' S, by rw [← MonoidHom.map_closure f S, hS], hSfin.image f⟩

end Work.ORDunwoody.Lemmas
