import Mathlib
import Submission.Work.SSS.edgeTransport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The boundary of the spread, applied to a cycle

`Work.SSS.LiftFam.spread_boundary` computes the boundary of the spread of a simplex `τ` of the
fibre as the difference of the two ends of the lift minus the spread of the boundary of `τ`.  For
the degree bookkeeping of the first differential of the Serre spectral sequence one needs the same
identity with `τ` a *cycle* (so that the last term vanishes) and with the indices shifted by one.
This file records that statement (`Work.SSS.spread_boundary_apply`).

The statement is the `t`-th case of `spread_boundary` for `t ≥ 1`; the case `t = 0` is the
degenerate case of the prism identity, where the simplex `Δ^0` has no faces, and is proved directly
(`Work.SSS.prismChainBoundary_zero`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial

namespace Work.SSS

noncomputable section

/-- **The boundary of the prism chain in degree one.**  For a homotopy `G : Δ^0 × I → X` of a
`0`-simplex, the boundary of its prism chain (a `1`-chain) is the difference of its bottom and top
chains: there are no faces to correct by. -/
theorem prismChainBoundary_zero {X : Type} [TopologicalSpace X]
    (G : C(↥(stdSimplex ℝ (Fin 1)) × unitInterval, X)) :
    (ModuleCat.Hom.hom ((Work.Stems.hChain X).d 1 0))
        (Work.Stems.PerSimplex.prismChain (X := X) 0 G)
      = Work.Stems.simplexChain (X := X) 0
          (Work.RatHurewicz.Bridge.simplexOf 0 (G.comp (Work.Serre.botIncl 0)))
        - Work.Stems.simplexChain (X := X) 0
            (Work.RatHurewicz.Bridge.simplexOf 0 (G.comp (Work.Serre.topIncl 0))) := by
  have hbot : (G.comp (Work.Serre.pp 0 (0 : Fin 1))).comp
        (Work.RatHurewicz.Bridge.coface 0 (1 : Fin 2)) = G.comp (Work.Serre.botIncl 0) := by
    rw [ContinuousMap.comp_assoc]
    rw [show (0 : Fin 1) = Fin.last 0 from Fin.ext rfl]
    rw [show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl]
    rw [Work.Serre.pp_coface_last_last 0]
  have htop : (G.comp (Work.Serre.pp 0 (0 : Fin 1))).comp
        (Work.RatHurewicz.Bridge.coface 0 (0 : Fin 2)) = G.comp (Work.Serre.topIncl 0) := by
    rw [ContinuousMap.comp_assoc]
    rw [Work.Serre.pp_coface_zero_zero 0]
  rw [Work.Stems.PerSimplex.prismChain_def, Fin.sum_univ_one, map_zsmul,
    Work.RatHurewicz.Bridge.d_ιChainComplex_one, Fin.sum_univ_two]
  rw [Work.Stems.PerSimplex.delta_simplexOf, Work.Stems.PerSimplex.delta_simplexOf]
  rw [hbot, htop]
  simp only [Work.Stems.simplexChain]
  simp only [Fin.val_zero, Fin.val_one, zero_add, pow_one, pow_zero, one_smul]
  simp only [neg_zsmul, one_zsmul, neg_add_rev, neg_neg, sub_eq_add_neg]

theorem spread_boundary_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} {b₀ b₁ : B} {γ : Path b₀ b₁} (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp t, Work.StemsB.fibre p b₀))
    (hτ : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d t
        ((ComplexShape.down ℕ).next t)))
        (Work.Stems.simplexChain (X := Work.StemsB.fibre p b₀) t
          (Work.RatHurewicz.Bridge.simplexOf t τ)) = 0) :
    (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
        (t + 1) t)) (Φ.spread t τ)
      = (ModuleCat.Hom.hom ((sourceChainMap p γ).f t))
          (Work.Stems.simplexChain (X := Work.StemsB.fibre p b₀) t
            (Work.RatHurewicz.Bridge.simplexOf t τ))
        - (ModuleCat.Hom.hom ((targetChainMap p γ).f t)) (Φ.topChain t τ) := by
  rcases t with _ | t
  · rw [LiftFam.spread, prismChainBoundary_zero (Φ.graph 0 τ), LiftFam.botChain_eq Φ 0 τ,
      LiftFam.topChain_eq Φ 0 τ]
  · have hnext : (ComplexShape.down ℕ).next (t + 1) = t := ChainComplex.next_nat_succ t
    have hτ' : (ModuleCat.Hom.hom
        ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d (t + 1) t))
        (Work.Stems.simplexChain (X := Work.StemsB.fibre p b₀) (t + 1)
          (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ)) = 0 := by
      rw [hnext] at hτ
      exact hτ
    rw [LiftFam.spread_boundary Φ t τ, hτ', map_zero, sub_zero]

end

end Work.SSS
