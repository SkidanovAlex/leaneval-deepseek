import Mathlib
import Submission.Work.Stems.WedgePinch
import Submission.Work.Stems.wedgeFst_pinchMap_homotopic
import Submission.Work.Stems.wedgeSnd_pinchMap_homotopic
import Submission.Work.Stems.wedgeFstSnd_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Additivity of the Hurewicz chain map along `GenLoop.transAt`

The target is the additivity of `Work.Stems.hurewiczChain` with respect to the cube concatenation
`GenLoop.transAt`: the Hurewicz map `πₙ(X,x₀) → Hₙ(X)` is a group homomorphism.

The mathematical content is the *pinch computation*: a cube concatenation, transported to the
sphere by the collapse `Iⁿ → Sⁿ`, becomes the composition of the pinch map `Sⁿ → Sⁿ ∨ Sⁿ` with the
two halves of the cube (`Work.Stems.cubeLift_transAt_eq`).  The additivity then follows from the
standard fact (`Work.Stems.pinchMap_hurewiczClass`) that the pinch map sends the fundamental class
to the sum of the two summands; this in turn is deduced from the fact that the two folds
`Sⁿ ∨ Sⁿ → Sⁿ` are homotopic to the identity when composed with the pinch
(`Work.Stems.wedgeFst_pinchMap_homotopic`, `Work.Stems.wedgeSnd_pinchMap_homotopic`) together with
their joint injectivity on homology (`Work.Stems.wedgeFstSnd_injective`).
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- Homotopic maps induce the same map on homology. -/
theorem hm_congr (n : ℕ) {A B : Type} [TopologicalSpace A] [TopologicalSpace B] {f g : C(A, B)}
    (h : ContinuousMap.Homotopic f g) : hm f n = hm g n := by
  have hh : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := h.some
  have hcongr := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor hh
    (ModuleCat.of ℤ ℤ) n
  simp only [hm]
  rw [hcongr]

/-- Evaluation of a composite on homology. -/
theorem hm_apply_comp (n : ℕ) {A B D : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace D] (f : C(B, D)) (g : C(A, B))
    (x : (chains (TopCat.of A)).homology n) :
    (hm f n) ((hm g n) x) = hm (f.comp g) n x := by
  rw [hm_comp]
  rfl

/-- **The pinch computation.**  The pinch `Sⁿ → Sⁿ ∨ Sⁿ` sends the fundamental class of `Sⁿ` to
the sum of the fundamental classes of the two summands. -/
theorem pinchMap_hurewiczClass (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    hm (pinchMap n hn i) n (sphereGenerator n hn) =
      hm (wedgeInl (sphBase n hn)) n (sphereGenerator n hn)
        + hm (wedgeInr (sphBase n hn)) n (sphereGenerator n hn) := by
  apply wedgeFstSnd_injective n hn
  have hfst_p : (hm (wedgeFst (sphBase n hn)) n)
      ((hm (pinchMap n hn i) n) (sphereGenerator n hn)) = sphereGenerator n hn := by
    rw [hm_apply_comp n (wedgeFst (sphBase n hn)) (pinchMap n hn i),
      hm_congr n (wedgeFst_pinchMap_homotopic n hn i), hm_id, LinearMap.id_apply]
  have hsnd_p : (hm (wedgeSnd (sphBase n hn)) n)
      ((hm (pinchMap n hn i) n) (sphereGenerator n hn)) = sphereGenerator n hn := by
    rw [hm_apply_comp n (wedgeSnd (sphBase n hn)) (pinchMap n hn i),
      hm_congr n (wedgeSnd_pinchMap_homotopic n hn i), hm_id, LinearMap.id_apply]
  have hfst_i1 : (hm (wedgeFst (sphBase n hn)) n)
      ((hm (wedgeInl (sphBase n hn)) n) (sphereGenerator n hn)) = sphereGenerator n hn := by
    rw [hm_apply_comp n (wedgeFst (sphBase n hn)) (wedgeInl (sphBase n hn)),
      wedgeFst_inl, hm_id, LinearMap.id_apply]
  have hfst_i2 : (hm (wedgeFst (sphBase n hn)) n)
      ((hm (wedgeInr (sphBase n hn)) n) (sphereGenerator n hn)) = 0 := by
    rw [hm_apply_comp n (wedgeFst (sphBase n hn)) (wedgeInr (sphBase n hn)),
      wedgeFst_inr, hm_const n (sphBase n hn) hn, LinearMap.zero_apply]
  have hsnd_i1 : (hm (wedgeSnd (sphBase n hn)) n)
      ((hm (wedgeInl (sphBase n hn)) n) (sphereGenerator n hn)) = 0 := by
    rw [hm_apply_comp n (wedgeSnd (sphBase n hn)) (wedgeInl (sphBase n hn)),
      wedgeSnd_inl, hm_const n (sphBase n hn) hn, LinearMap.zero_apply]
  have hsnd_i2 : (hm (wedgeSnd (sphBase n hn)) n)
      ((hm (wedgeInr (sphBase n hn)) n) (sphereGenerator n hn)) = sphereGenerator n hn := by
    rw [hm_apply_comp n (wedgeSnd (sphBase n hn)) (wedgeInr (sphBase n hn)),
      wedgeSnd_inr, hm_id, LinearMap.id_apply]
  simp only [map_add, hfst_p, hsnd_p, hfst_i1, hfst_i2, hsnd_i1, hsnd_i2, add_zero, zero_add]

/-- **Additivity of the Hurewicz chain map.** -/
theorem hurewiczChain_transAt (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X}
    (i : Fin n) (p q : GenLoop (Fin n) X x₀) :
    hurewiczChain n hn x₀ (GenLoop.transAt i q p) =
      hurewiczChain n hn x₀ p + hurewiczChain n hn x₀ q := by
  have hb : cubeLift n hn q (sphBase n hn) = cubeLift n hn p (sphBase n hn) :=
    (cubeLift_sphBase n hn q).trans (cubeLift_sphBase n hn p).symm
  have hg : cubeLift n hn (GenLoop.transAt i q p)
      = (wedgeMap (sphBase n hn) (cubeLift n hn q) (cubeLift n hn p) hb).comp
          (pinchMap n hn i) :=
    cubeLift_transAt_eq n hn i p q hb
  simp only [hurewiczChain, hurewiczClass_eq_hm]
  rw [hg, hm_comp, LinearMap.comp_apply, pinchMap_hurewiczClass, map_add]
  rw [show (hm (wedgeMap (sphBase n hn) (cubeLift n hn q) (cubeLift n hn p) hb) n)
        ((hm (wedgeInl (sphBase n hn)) n) (sphereGenerator n hn))
      = hm ((wedgeMap (sphBase n hn) (cubeLift n hn q) (cubeLift n hn p) hb).comp
          (wedgeInl (sphBase n hn))) n (sphereGenerator n hn) from by
    rw [hm_comp]; rfl]
  rw [show (hm (wedgeMap (sphBase n hn) (cubeLift n hn q) (cubeLift n hn p) hb) n)
        ((hm (wedgeInr (sphBase n hn)) n) (sphereGenerator n hn))
      = hm ((wedgeMap (sphBase n hn) (cubeLift n hn q) (cubeLift n hn p) hb).comp
          (wedgeInr (sphBase n hn))) n (sphereGenerator n hn) from by
    rw [hm_comp]; rfl]
  rw [wedgeMap_comp_inl, wedgeMap_comp_inr, add_comm]

end

end Work.Stems
