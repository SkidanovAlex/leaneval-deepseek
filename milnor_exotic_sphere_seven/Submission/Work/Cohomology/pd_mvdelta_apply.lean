import Mathlib
import Submission.Work.Cohomology.MVSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The elementwise description of the Mayer–Vietoris connecting homomorphism

For subsets `U V ⊆ X` and `n : ℕ`, the connecting homomorphism of the Mayer–Vietoris long exact
sequence

`mvδ U V n : Hₙ₊₁(C^{U,V}_*(X)) ⟶ Hₙ(U ∩ V)`

is computed by the usual snake-lemma description.  Given a cycle `z` of the small chains in degree
`n+1`, a chain `z₂` of `C_*(U) ⊞ C_*(V)` in degree `n+1` lifting it (`mvRight z₂ = iCycles z`),
and a cycle `w` of `C_*(U ∩ V)` in degree `n` whose image under `mvLeft` is the boundary `d z₂`,
then

`mvδ U V n [z] = [w]`.

This is `Work.Cohomology.pd_mvdelta_apply`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- **The elementwise description of the Mayer–Vietoris connecting homomorphism.**  If `z` is a
cycle of the small chains in degree `n+1`, `z₂` is a lift of `z` in `C_*(U) ⊞ C_*(V)`
(`mvRight z₂ = iCycles z`), and `w` is a cycle of `C_*(U ∩ V)` in degree `n` whose image under
`mvLeft` is `d z₂`, then `mvδ [z] = [w]`. -/
theorem pd_mvdelta_apply {X : TopCat} {U V : Set X} {n : ℕ}
    (z : (smallChains U V).cycles (n + 1))
    (z₂ : (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).X (n + 1))
    (hz₂ : (mvRight U V).f (n + 1) z₂ = (smallChains U V).iCycles (n + 1) z)
    (w : (singularChains ℤ (TopCat.of ↥(U ∩ V))).cycles n)
    (hw : (mvLeft U V).f n ((singularChains ℤ (TopCat.of ↥(U ∩ V))).iCycles n w)
      = (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).d (n + 1) n z₂) :
    mvδ U V n ((smallChains U V).homologyπ (n + 1) z)
      = (singularChains ℤ (TopCat.of ↥(U ∩ V))).homologyπ n w := by
  -- Snake-lemma description of the connecting map `ShortExact.δ_apply'`, with the intermediate
  -- element `pOpcycles z₂` of the opcycles of the middle term.
  refine CategoryTheory.ShortComplex.ShortExact.δ_apply' (mv_shortExact U V) (n + 1) n
      (by simp [ComplexShape.down])
      ((smallChains U V).homologyπ (n + 1) z)
      (ConcreteCategory.hom
        ((singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).pOpcycles (n + 1)) z₂)
      w ?_ ?_
  · -- `opcyclesMap (mvRight) (pOpcycles z₂) = homologyι (homologyπ z)`, both sides being
    -- `pOpcycles (iCycles z)`.
    change (ConcreteCategory.hom (HomologicalComplex.opcyclesMap (mvRight U V) (n + 1)))
        ((ConcreteCategory.hom
          (HomologicalComplex.pOpcycles (singularChains ℤ (TopCat.of U) ⊞
            singularChains ℤ (TopCat.of V)) (n + 1))) z₂)
      = (ConcreteCategory.hom ((smallChains U V).homologyι (n + 1)))
        ((ConcreteCategory.hom (HomologicalComplex.homologyπ (smallChains U V) (n + 1))) z)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      HomologicalComplex.p_opcyclesMap (mvRight U V) (n + 1),
      HomologicalComplex.homology_π_ι (K := smallChains U V) (n + 1)]
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hz₂]
  · -- `cyclesMap (mvLeft) n w = opcyclesToCycles (n+1) n (pOpcycles z₂)`:  the right-hand side is
    -- `toCycles z₂ = iCycles⁻¹ (d z₂)`, and the left-hand side is `iCycles⁻¹ (mvLeft (iCycles w))`,
    -- which is `iCycles⁻¹ (d z₂)` by `hw`.
    change (ConcreteCategory.hom (HomologicalComplex.cyclesMap (mvLeft U V) n)) w
      = (ConcreteCategory.hom
          (HomologicalComplex.opcyclesToCycles (singularChains ℤ (TopCat.of U) ⊞
            singularChains ℤ (TopCat.of V)) (n + 1) n))
        ((ConcreteCategory.hom
          (HomologicalComplex.pOpcycles (singularChains ℤ (TopCat.of U) ⊞
            singularChains ℤ (TopCat.of V)) (n + 1))) z₂)
    rw [← ConcreteCategory.comp_apply,
      HomologicalComplex.pOpcycles_opcyclesToCycles
        (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)) (n + 1) n]
    apply (Preadditive.mono_iff_injective (HomologicalComplex.iCycles
      (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)) n)).1 inferInstance
    change (ConcreteCategory.hom (HomologicalComplex.iCycles
          (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)) n))
        ((ConcreteCategory.hom (HomologicalComplex.cyclesMap (mvLeft U V) n)) w)
      = (ConcreteCategory.hom (HomologicalComplex.iCycles
          (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)) n))
        ((ConcreteCategory.hom (HomologicalComplex.toCycles
          (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)) (n + 1) n)) z₂)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      HomologicalComplex.cyclesMap_i (mvLeft U V) n,
      HomologicalComplex.toCycles_i
        (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)) (n + 1) n]
    rw [ConcreteCategory.comp_apply]
    exact hw

end

end Work.Cohomology
