/-
# Transporting a chart of `M̄` avoiding the cusped boundary to a chart of `M̂`

The assembled space `M̂ = (M̄ ⊔ ⊔_v [-1,1]²×T_v)/~₃` of the Ratcliffe--Tschantz construction
contains the hyperbolic piece `M̄` as the closed subspace `range a.incMbar`.  A chart of `M̄`
whose source avoids the cusped boundary `a.Tset` does not meet any of the filling pieces, so it is
also a chart of `M̂` with the same target:

* `Work.RTInstance.exists_chartOfMbar` — for every open partial homeomorphism
  `Φ : OpenPartialHomeomorph a.Mbar E4` with `Φ.source ⊆ a.Tsetᶜ` there is
  `Ψ : OpenPartialHomeomorph a.Mhat E4` with
  `Ψ.source = a.incMbar '' Φ.source`, `Ψ.target = Φ.target`, `Ψ (a.incMbar x) = Φ x` on the
  source, and `Ψ.symm q = a.incMbar (Φ.symm q)` on the target.

The mathematical content is the single observation that `incMbar` is an **open** embedding when
restricted to an open set meeting `Tsetᶜ`: an open `W ⊆ Φ.source` has open image in `M̂` because its
preimage under `incMbar` is `W` and its preimage under `incY` is empty (a point of `M̄` is glued to a
point of the filling pieces only on `Tset`).  The rest of the proof is the bookkeeping of
`OpenPartialHomeomorph.lift_openEmbedding`, the `X` being the subtype `Φ.source` (an open subset of
`M̄`) and the map `X → M̂` being `incMbar`.  The degenerate case `Φ.source = ∅` is vacuous and is
handled separately, since `OpenPartialHomeomorph.subtypeRestr` needs the domain to be nonempty.
-/
import Mathlib
import Submission.Work.Space.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTInstance

theorem exists_chartOfMbar (a : Work.Space.Assembly) (Φ : OpenPartialHomeomorph a.Mbar Work.Space.E4)
    (hΦ : Φ.source ⊆ a.Tsetᶜ) :
    ∃ Ψ : OpenPartialHomeomorph a.Mhat Work.Space.E4,
      Ψ.source = a.incMbar '' Φ.source ∧ Ψ.target = Φ.target ∧
      (∀ x ∈ Φ.source, Ψ (a.incMbar x) = Φ x) ∧
      (∀ q ∈ Ψ.target, Ψ.symm q = a.incMbar (Φ.symm q)) := by
  by_cases hne : Φ.source.Nonempty
  · -- The non-degenerate case: `Φ.source` is a nonempty open set, so we may restrict `Φ` to the
    -- subtype `s := Φ.source` and lift it along the open embedding `incMbar : s → M̂`.
    let s : TopologicalSpace.Opens a.Mbar := ⟨Φ.source, Φ.open_source⟩
    have hsn : Nonempty s := hne.to_subtype
    -- The image in `M̂` of an open subset of `Φ.source` is open: the only identifications of the
    -- quotient are between a point of `Tset` and a point of the filling pieces, and `Φ.source`
    -- misses `Tset`.
    have key : ∀ W : Set a.Mbar, IsOpen W → W ⊆ Φ.source → IsOpen (a.incMbar '' W) := by
      intro W hW hWsub
      rw [a.isOpen_iff_sum]
      refine ⟨?_, ?_⟩
      · have h : {x : a.Mbar | a.incMbar x ∈ a.incMbar '' W} = W :=
          Set.preimage_image_eq W a.incMbar_injective
        rw [h]; exact hW
      · have h : {y : a.Y | a.incY y ∈ a.incMbar '' W} = ∅ := by
          ext y
          constructor
          · intro hy
            obtain ⟨x, hxW, hxy⟩ := hy
            exact (hΦ (hWsub hxW)) (a.incMbar_eq_incY_iff.mp hxy).choose
          · intro hy; exact absurd hy (by simp)
        rw [h]; exact isOpen_empty
    -- `incMbar`, viewed as a map out of the subtype `s`, is an open embedding.
    let f : s → a.Mhat := fun x => a.incMbar x
    have hf : Topology.IsOpenEmbedding f := by
      refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
      · exact a.continuous_incMbar.comp continuous_subtype_val
      · intro x y hxy
        exact Subtype.ext (a.incMbar_injective hxy)
      · intro W hW
        have hWm : IsOpen ((Subtype.val '' W) : Set a.Mbar) :=
          (Φ.open_source.isOpenEmbedding_subtypeVal).isOpen_iff_image_isOpen.mp hW
        have hsub : (Subtype.val '' W) ⊆ Φ.source := by
          rintro x ⟨y, -, rfl⟩
          exact y.2
        have hkey := key _ hWm hsub
        rwa [show f '' W = a.incMbar '' (Subtype.val '' W) from by
          rw [← Set.image_comp]; rfl]
    -- The chart `Φ` restricted to the subtype `s`, and its lift to `M̂`.
    let e : OpenPartialHomeomorph s Work.Space.E4 := Φ.subtypeRestr hsn
    let Ψ : OpenPartialHomeomorph a.Mhat Work.Space.E4 := e.lift_openEmbedding hf
    have hecoe : (↑e : s → Work.Space.E4) = Φ ∘ Subtype.val := by
      ext x
      simp [e, OpenPartialHomeomorph.subtypeRestr_coe]
    have hesrc : e.source = univ := by
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      ext x; exact iff_of_true x.2 trivial
    have hetgt : e.target = Φ.target := by
      have h : e.target = ↑Φ '' Φ.source := by
        rw [← OpenPartialHomeomorph.image_source_eq_target e, hesrc, Set.image_univ, hecoe,
          Set.range_comp, Subtype.range_val]
        rw [show (↑s : Set a.Mbar) = Φ.source from rfl]
      rw [h, Φ.image_source_eq_target]
    refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
    · calc Ψ.source = f '' e.source := OpenPartialHomeomorph.lift_openEmbedding_source e hf
        _ = f '' univ := by rw [hesrc]
        _ = range f := Set.image_univ
        _ = a.incMbar '' Φ.source := by
            ext z
            constructor
            · rintro ⟨x, rfl⟩
              exact ⟨(x : a.Mbar), x.2, rfl⟩
            · rintro ⟨x, hx, rfl⟩
              exact ⟨⟨x, hx⟩, rfl⟩
    · rw [OpenPartialHomeomorph.lift_openEmbedding_target e hf, hetgt]
    · intro x hx
      have h := OpenPartialHomeomorph.lift_openEmbedding_apply (e := e) hf (x := (⟨x, hx⟩ : s))
      simpa [Ψ, f, e, OpenPartialHomeomorph.subtypeRestr_coe] using h
    · intro q hq
      have hqT : q ∈ e.target := by
        rw [← OpenPartialHomeomorph.lift_openEmbedding_target e hf]; exact hq
      have h1 : (((e.symm q) : s) : a.Mbar) = Φ.symm q :=
        OpenPartialHomeomorph.subtypeRestr_symm_apply Φ hsn hqT
      have hsymm : Ψ.symm q = f (e.symm q) := by
        simp only [Ψ, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply]
      rw [hsymm, ← h1]
  · -- The degenerate case `Φ.source = ∅`: then also `Φ.target = ∅` and every condition is
    -- vacuous.
    have h0 : Φ.source = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hT0 : Φ.target = ∅ := by rw [← Φ.image_source_eq_target, h0]; simp
    let Ψ : OpenPartialHomeomorph a.Mhat Work.Space.E4 :=
      { toFun := fun _ => (0 : Work.Space.E4)
        invFun := fun _ => Classical.arbitrary a.Mhat
        source := ∅
        target := ∅
        map_source' := by intro x hx; exact absurd hx (by simp)
        map_target' := by intro q hq; exact absurd hq (by simp)
        left_inv' := by intro x hx; exact absurd hx (by simp)
        right_inv' := by intro q hq; exact absurd hq (by simp)
        open_source := isOpen_empty
        open_target := isOpen_empty
        continuousOn_toFun := by simp
        continuousOn_invFun := by simp }
    refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
    · simp [Ψ, h0]
    · simp [Ψ, hT0]
    · intro x hx
      exact absurd (h0 ▸ hx) (by simp)
    · intro q hq
      exact absurd hq (by simp [Ψ])

end Work.RTInstance
