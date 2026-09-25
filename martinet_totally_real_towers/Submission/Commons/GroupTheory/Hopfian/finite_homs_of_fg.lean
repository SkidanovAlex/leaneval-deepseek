import Mathlib.GroupTheory.Finiteness

set_option linter.style.haveILetI false

namespace Commons.GroupTheory.Hopfian

universe u v

/-- There are finitely many homomorphisms from a finitely generated group into a fixed
finite group: a homomorphism is determined by the images of a finite generating set. -/
theorem finite_homs_of_fg {G : Type u} [Group G] [Group.FG G] (F : Type v) [Group F] [Finite F] :
    Finite (G →* F) := by
  rcases Group.fg_iff.mp ‹Group.FG G› with ⟨s, hs1, hs2⟩
  -- `s` is a finite generating set: `Subgroup.closure (s : Set G) = ⊤`
  letI : Fintype s := hs2.fintype
  refine Finite.of_injective (fun φ : G →* F => fun x : s => φ (x : G)) ?_
  intro φ₁ φ₂ h
  apply MonoidHom.ext
  intro x
  have hsub : Set.EqOn φ₁ φ₂ (Subgroup.closure (s : Set G)) := by
    exact MonoidHom.eqOn_closure (fun x hx => congrFun h ⟨x, hx⟩)
  have hx : x ∈ (Subgroup.closure (s : Set G)) := by
    rw [hs1]
    trivial
  exact hsub hx

end Commons.GroupTheory.Hopfian