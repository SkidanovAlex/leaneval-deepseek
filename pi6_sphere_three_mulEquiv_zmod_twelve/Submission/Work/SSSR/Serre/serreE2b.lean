import Mathlib
import Submission.Work.SSSR.Serre.Engine
import Submission.Work.SSSR.Serre.simpHomExists
import Submission.Work.SSSR.Serre.simpHomVanishing
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval
namespace Work.SSSR.Serre

/-- The swap of a homotopy `I × Z → X` into a map `Z × I → X`. -/
def swapHom {X : Type} [TopologicalSpace X] {Z : Type} [TopologicalSpace Z]
    (G : C(unitInterval × Z, X)) : C(Z × unitInterval, X) :=
  ⟨fun p => G (p.2, p.1), G.continuous.comp (continuous_snd.prodMk continuous_fst)⟩

@[simp]
theorem swapHom_apply {X : Type} [TopologicalSpace X] {Z : Type} [TopologicalSpace Z]
    (G : C(unitInterval × Z, X)) (z : Z) (t : unitInterval) :
    swapHom G (z, t) = G (t, z) := rfl

/-- The hypothesis of `SerreE2b` is the compression property in the form used by the cone
construction: a homotopy relative to the boundary, with time first, is the same data. -/
theorem compressHyp_of_serreHyp {X : Type} [TopologicalSpace X] (A : Set X) (N : ℕ)
    (h : ∀ (n : ℕ), n ≤ N → ∀ f : C(Work.SSSR.Stems.Cubical.IC n, X),
        (∀ t, t ∈ Cube.boundary (Fin n) → f t ∈ A) →
        ∃ g : C(Work.SSSR.Stems.Cubical.IC n, X), (∀ t, g t ∈ A) ∧
          ContinuousMap.HomotopicRel f g (Cube.boundary (Fin n))) :
    CompressHyp X A N := by
  intro m hm f hf
  obtain ⟨g, hg, hH⟩ := h m hm f hf
  obtain ⟨F⟩ := hH
  refine ⟨swapHom (F.toHomotopy.toContinuousMap), ?_, ?_, ?_⟩
  · intro x
    simp only [swapHom_apply]
    exact (show F.toHomotopy (0, x) = f x from F.toHomotopy.apply_zero x)
  · intro x hx t
    simp only [swapHom_apply]
    exact F.prop t x hx
  · intro x
    simp only [swapHom_apply]
    exact (show F.toHomotopy (1, x) = g x from F.toHomotopy.apply_one x).symm ▸ hg x

theorem serreE2b : Work.SSSR.Serre.SerreE2b (R := R) := by
  intro X _ A N h n hn
  have hc := compressHyp_of_serreHyp A N h
  obtain ⟨H⟩ := simpHom_of_compress N hc
  exact simpHomVanishing H n hn

end Work.SSSR.Serre
