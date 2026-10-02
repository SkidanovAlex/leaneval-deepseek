import Mathlib
import Submission.Work.ThomBordism.TwoSet.CompressBasic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Transport of the compression property along a homeomorphism of the cube

`compresses_homeo`: if the pair `(Y, A)` has the compression property in dimension `d`, then for
any space `W` homeomorphic to `I^d`, via `e : I^d ≃ₜ W`, every map `f : W → Y` whose values on the
transported boundary `eB = e '' ∂I^d` lie in `A` is homotopic to a map into `A`, relative to `eB`.

This is the form in which the hypotheses `Compress ↥V {v | ↑v ∈ U} d` and
`Compress ↥U {u | ↑u ∈ V} d` are applied to the cells of the grid in the proof of
`Work.ThomBordism.TwoSet.compressRel_twoSet`.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

theorem compresses_homeo {Y : Type*} [TopologicalSpace Y] {A : Set Y} {d : ℕ}
    {W : Type*} [TopologicalSpace W] (h : Compress Y A d) (e : IC d ≃ₜ W)
    (eB : Set W) (he : e '' Cube.boundary (Fin d) = eB)
    (f : C(W, Y)) (hf : ∀ x, x ∈ eB → f x ∈ A) :
    ∃ G : C(W × unitInterval, Y),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x (hx : x ∈ eB) t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ A) := by
  let eC : C(IC d, W) := ⟨e, e.continuous⟩
  let esC : C(W, IC d) := ⟨e.symm, e.symm.continuous⟩
  have hbd : ∀ u : IC d, u ∈ Cube.boundary (Fin d) → (f.comp eC) u ∈ A := by
    intro u hu
    exact hf (e u) (by rw [← he]; exact ⟨u, hu, rfl⟩)
  obtain ⟨G, hG0, hGbd, hG1⟩ := h (f.comp eC) hbd
  refine ⟨G.comp (esC.prodMap (ContinuousMap.id unitInterval)), ?_, ?_, ?_⟩
  · intro x
    show G (esC x, (0 : unitInterval)) = f x
    rw [hG0]
    show f (eC (esC x)) = f x
    simp [eC, esC]
  · intro x hx t
    have hx' : esC x ∈ Cube.boundary (Fin d) := by
      rw [← he] at hx
      obtain ⟨u, hu, hueq⟩ := hx
      have : esC x = u := by
        show e.symm x = u
        rw [← hueq]
        exact e.symm_apply_apply u
      rw [this]; exact hu
    show G (esC x, t) = f x
    rw [hGbd (esC x) hx' t]
    show f (eC (esC x)) = f x
    simp [eC, esC]
  · intro x
    show G (esC x, (1 : unitInterval)) ∈ A
    exact hG1 (esC x)

end Work.ThomBordism.TwoSet
