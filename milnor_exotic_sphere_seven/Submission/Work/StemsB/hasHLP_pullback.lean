import Mathlib
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The homotopy lifting property is stable under base change

Mathlib has no fibrations at all, so the basic closure properties of the homotopy lifting property
have to be built here.  This file proves that the property `Work.StemsB.HasHLP` is preserved by
pullback (base change): if `p : E → B` has the HLP with respect to `Z`, then so does its base
change `pullbackSnd p q : E ×_B E' → E'` along any `q : E' → B`.

The proof is the classical two-step construction: lift the `E'`-coordinate of the homotopy (that is
the given homotopy itself, read in `E'`), use the homotopy lifting property of `p` on the composite
of that lift with `q : E' → B` to produce the `E`-coordinate, and pair the two.  At every time
`t` the pair lands in the fibre product by construction.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-- **Base change (pullback) of a map with the homotopy lifting property.**  If `p : E → B` has the
HLP with respect to `Z`, then so does the projection `pullbackSnd p q : E ×_B E' → E'` of the
fibre product of `p` with any `q : E' → B`. -/
theorem hasHLP_pullback {E B E' Z : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace Z] (p : C(E, B)) (q : C(E', B))
    (h : Work.StemsB.HasHLP p Z) : Work.StemsB.HasHLP (Work.StemsB.pullbackSnd p q) Z := by
  intro f b H
  -- the compatibility of `f` with the two projections
  have hbase : ∀ z : Z, p (pullbackFst p q (f z)) = q (pullbackSnd p q (f z)) :=
    fun z => (f z).2
  -- the two ends of the given homotopy, read through the projections
  have hH0 : ∀ z : Z, H.toContinuousMap (0, z) = pullbackSnd p q (f z) :=
    fun z => H.map_zero_left z
  have hH1 : ∀ z : Z, H.toContinuousMap (1, z) = b z :=
    fun z => H.map_one_left z
  -- step 1: the composite of `q` with the homotopy is a homotopy in `B` out of `p ∘ (fst ∘ f)`
  have hK0 : ∀ z : Z, (q.comp H.toContinuousMap) (0, z)
      = (p.comp ((pullbackFst p q).comp f)) z := by
    intro z
    show q (H.toContinuousMap (0, z)) = p (pullbackFst p q (f z))
    rw [hH0 z, hbase z]
  have hK1 : ∀ z : Z, (q.comp H.toContinuousMap) (1, z) = (q.comp b) z := by
    intro z
    show q (H.toContinuousMap (1, z)) = q (b z)
    rw [hH1 z]
  let KH : (p.comp ((pullbackFst p q).comp f)).Homotopy (q.comp b) :=
    ContinuousMap.Homotopy.mk (q.comp H.toContinuousMap) hK0 hK1
  -- step 2: lift it using the HLP of `p`, giving the `E`-coordinate of the lifted homotopy
  obtain ⟨G, HG, hHG⟩ := h ((pullbackFst p q).comp f) (q.comp b) KH
  have hHG' : ∀ w : ↑I × Z, p (HG.toContinuousMap w) = q (H.toContinuousMap w) := by
    intro w
    have hw := congrArg (fun u : C(↑I × Z, B) => u w) hHG
    simp only [ContinuousMap.comp_apply] at hw
    exact hw
  -- the endpoint of the lifted homotopy lies in the fibre product over `b`
  have hgb : ∀ z : Z, p (G z) = q (b z) := by
    intro z
    have h1 : HG.toContinuousMap (1, z) = G z := HG.map_one_left z
    have h2 : H.toContinuousMap (1, z) = b z := H.map_one_left z
    have h3 : p (HG.toContinuousMap (1, z)) = q (H.toContinuousMap (1, z)) := hHG' (1, z)
    rw [h1, h2] at h3
    exact h3
  -- the lifted homotopy itself, valued in the fibre product
  have hGgcont : Continuous fun w : ↑I × Z =>
      (⟨(HG.toContinuousMap w, H.toContinuousMap w), hHG' w⟩ : Pullback p q) := by
    refine Continuous.subtype_mk ?_ hHG'
    exact HG.toContinuousMap.continuous_toFun.prodMk H.toContinuousMap.continuous_toFun
  let Gg : C(↑I × Z, Pullback p q) :=
    ⟨fun w => ⟨(HG.toContinuousMap w, H.toContinuousMap w), hHG' w⟩, hGgcont⟩
  -- its value at time `1`, as a map `Z → E ×_B E'`
  have hgcont : Continuous fun z : Z => (⟨(G z, b z), hgb z⟩ : Pullback p q) := by
    refine Continuous.subtype_mk ?_ hgb
    exact G.continuous_toFun.prodMk b.continuous_toFun
  let g : C(Z, Pullback p q) := ⟨fun z => ⟨(G z, b z), hgb z⟩, hgcont⟩
  have hm0 : ∀ z : Z, Gg (0, z) = f z := by
    intro z
    have hp1 : HG.toContinuousMap (0, z) = pullbackFst p q (f z) := HG.map_zero_left z
    have hp2 : H.toContinuousMap (0, z) = pullbackSnd p q (f z) := H.map_zero_left z
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · exact hp1
    · exact hp2
  have hm1 : ∀ z : Z, Gg (1, z) = g z := by
    intro z
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · exact HG.map_one_left z
    · exact H.map_one_left z
  let H' : f.Homotopy g := ContinuousMap.Homotopy.mk Gg hm0 hm1
  refine ⟨g, H', ?_⟩
  show (pullbackSnd p q).comp Gg = H.toContinuousMap
  ext w
  rfl

end

end Work.StemsB
