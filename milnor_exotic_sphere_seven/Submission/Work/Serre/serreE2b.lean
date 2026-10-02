import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.simpHomExists
import Submission.Work.Serre.simpHomVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# E2(b): compression implies the vanishing of relative homology

`Work.Serre.SerreE2b` states that if every map of pairs `(Iⁿ,∂Iⁿ) → (X,A)` with `n ≤ N` is homotopic
into `A` relative to the boundary, then `Hₙ(X,A;ℤ) = 0` for `n ≤ N`.  The proof has three parts:

* `compressHyp_of_serreHyp` converts the hypothesis into the compression property
  `Work.Serre.CompressHyp` in the form `Work.RatHurewicz.CompressRel` used by the cone construction;
* `Work.Serre.simpHom_of_compress` turns it into a coherent family of homotopies of singular
  simplices (`Work.Serre.SimpHom`);
* `Work.Serre.simpHomVanishing` shows that such a family contracts the relative chain complex
  `C_*(X,A)` in degrees `≤ N`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

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
    (h : ∀ (n : ℕ), n ≤ N → ∀ f : C(Work.Stems.Cubical.IC n, X),
        (∀ t, t ∈ Cube.boundary (Fin n) → f t ∈ A) →
        ∃ g : C(Work.Stems.Cubical.IC n, X), (∀ t, g t ∈ A) ∧
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

theorem serreE2b : Work.Serre.SerreE2b := by
  intro X _ A N h n hn
  have hc := compressHyp_of_serreHyp A N h
  obtain ⟨H⟩ := simpHom_of_compress N hc
  exact simpHomVanishing H n hn

end Work.Serre
