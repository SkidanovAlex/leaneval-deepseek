import Mathlib
import Submission.Work.Stems.Hurewicz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Well-definedness of the Hurewicz chain of a cube on homotopy classes

`Work.Stems.hurewiczChain n hn x₀ p` is the Hurewicz class of the sphere map obtained by
descending the cube map `p : Ω^ (Fin n) X x₀` along the collapse `φ : Iⁿ → Sⁿ`
(`Work.Stems.cubeLift`).  Here we prove that it only depends on the homotopy class of `p`
relative to the boundary of the cube.

The proof is the standard one: a homotopy `H : I × Iⁿ → X` from `p` to `q` which is constant on
`∂Iⁿ` is constant on the fibres of `φ` in the cube variable, so — after currying — it descends
along the quotient map `φ` to a map `Sⁿ → C(I, X)`, which uncurries to a homotopy
`I × Sⁿ → X` between `cubeLift p` and `cubeLift q`.  Homotopy invariance of singular homology
(`Work.Stems.hurewiczClass_eq_of_homotopic`) then gives the result.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- Descending to `Sⁿ` along the collapse commutes with homotopies rel boundary of cube maps:
homotopic cube maps give homotopic sphere maps. -/
theorem cubeLift_homotopic_of_homotopicRel (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    {x₀ : X} {p q : GenLoop (Fin n) X x₀}
    (H : p.1.HomotopicRel q.1 (Cube.boundary (Fin n))) :
    (cubeLift n hn p).Homotopic (cubeLift n hn q) := by
  classical
  -- the homotopy, as a continuous map `I × Iⁿ → X`
  let Hf : C(I × (Fin n → I), X) := H.some.toHomotopy.toContinuousMap
  have hHf : ∀ (t : I) (y : Fin n → I), Hf (t, y) = H.some (t, y) := fun _ _ => rfl
  -- its curried form `Iⁿ → C(I, X)`
  let Hc : C((Fin n → I), C(I, X)) := (Hf.comp (Homeomorph.prodComm (Fin n → I) I)).curry
  have hHc : ∀ (y : Fin n → I) (t : I), Hc y t = Hf (t, y) := by
    intro y t
    simp [Hc, ContinuousMap.curry_apply, ContinuousMap.comp_apply]
  -- the curried homotopy is constant on the boundary of the cube
  have hbound : ∀ y ∈ Cube.boundary (Fin n), Hc y = ContinuousMap.const I x₀ := by
    intro y hy
    ext t
    rw [hHc y t, hHf t y, H.some.eq_fst t hy]
    exact p.2 y hy
  -- hence it is constant on the fibres of the collapse, so it descends to `Sⁿ`
  have hfac : Function.FactorsThrough Hc (collapseMap n hn) := by
    intro y y' h
    rcases collapseMap_fiber n hn h with h' | ⟨hy, hy'⟩
    · rw [h']
    · rw [hbound y hy, hbound y' hy']
  let F : C(sphere n, C(I, X)) := (collapseMap_isQuotientMap n hn).lift Hc hfac
  have hFcomp : F.comp (collapseMap n hn) = Hc :=
    Topology.IsQuotientMap.lift_comp (collapseMap_isQuotientMap n hn) Hc hfac
  have hF : ∀ y, F (collapseMap n hn y) = Hc y := fun y =>
    congrFun (congrArg (fun (g : C((Fin n → I), C(I, X))) => (⇑g)) hFcomp) y
  -- uncurrying gives the homotopy on the sphere
  refine ⟨⟨(ContinuousMap.uncurry F).comp (Homeomorph.prodComm I (sphere n)), ?_, ?_⟩⟩
  · intro z
    obtain ⟨y, rfl⟩ := (collapseMap_isQuotientMap n hn).surjective z
    show F (collapseMap n hn y) 0 = cubeLift n hn p (collapseMap n hn y)
    rw [hF y]
    have hb : Hc y 0 = p.1 y := by rw [hHc y 0, hHf 0 y, H.some.apply_zero]
    have h2 : cubeLift n hn p (collapseMap n hn y) = p.1 y := by
      have h3 := congrArg (fun (g : C(CubeI n, X)) => g y) (cubeLift_comp n hn p)
      simpa using h3
    rw [hb, h2]
  · intro z
    obtain ⟨y, rfl⟩ := (collapseMap_isQuotientMap n hn).surjective z
    show F (collapseMap n hn y) 1 = cubeLift n hn q (collapseMap n hn y)
    rw [hF y]
    have hb : Hc y 1 = q.1 y := by rw [hHc y 1, hHf 1 y, H.some.apply_one]
    have h2 : cubeLift n hn q (collapseMap n hn y) = q.1 y := by
      have h3 := congrArg (fun (g : C(CubeI n, X)) => g y) (cubeLift_comp n hn q)
      simpa using h3
    rw [hb, h2]

/-- `hurewiczChain` is well defined on homotopy classes rel boundary: the Hurewicz chain of a
cube depends only on the homotopy class of the cube in `πₙ(X,x₀)`. -/
theorem hurewiczChain_eq_of_homotopic (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    {x₀ : X} {p q : GenLoop (Fin n) X x₀} (h : GenLoop.Homotopic p q) :
    hurewiczChain n hn x₀ p = hurewiczChain n hn x₀ q := by
  show hurewiczClass n hn (cubeLift n hn p) = hurewiczClass n hn (cubeLift n hn q)
  exact hurewiczClass_eq_of_homotopic n hn (cubeLift_homotopic_of_homotopicRel n hn h)

end

end Work.Stems
