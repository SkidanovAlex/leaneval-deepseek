import Mathlib
import Submission.Work.SSSR.iotaF_chainMap
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory in
/-- The chain-map property of the abstract σ-piece map `iotaFGen`, at an ARBITRARY first degree
`P`.  `Work.SSSR.iotaFGen_chainMap` supplies this only after being handed the boundary formula for
`ezGen P (q+1)` as a hypothesis `Hbd`; this discharges that hypothesis in the two cases `P = 0`
(`ezGen_boundary_zero`) and `P = P'+1` (`ezGen_boundary_succ` + `xChain_piecePi_eq_zero`), so the
chain-map property holds unconditionally for every `P : ℕ`. -/
theorem iotaFGen_chainMap_anyP {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F) ⟶ Work.SSSR.pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _) :
    Work.SSSR.iotaFGen f P (q + 1) σ ez ≫ (Work.SSSR.pieceAlong R f σ).d (P + (q + 1)) (P + q)
      = (-1 : ℤ) ^ P • (((Work.SSSR.sCC R F).d (q + 1) q) ≫ Work.SSSR.iotaFGen f P q σ ez) := by
  rcases P with _ | n
  · -- ## the degenerate case `P = 0`: the shuffle chain of the vertex
    refine iotaFGen_chainMap f 0 σ ez q (fun _ => 0) ?_ ?_
    · intro τ
      have hcm := congrArg (fun (g : (sCC R ((SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) ⊗ F)).X
            (0 + (q+1)) ⟶ (sCC R (pullAlong f σ)).X (0 + q)) =>
          g.hom (Work.SSSR.Cohomology.Crux33.ezGen 0 (q+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) F (stdIdSimplex 0) τ))
        ((sCCMap R ez).comm (0 + (q+1)) (0 + q))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcm
      rw [hcm, ezGen_boundary_zero q
        (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) F (stdIdSimplex 0) τ]
      rw [show ((-1:ℤ)^0) = (1:ℤ) from pow_zero (-1), one_zsmul]
      exact (zero_add _).symm
    · intro τ
      exact map_zero _
  · -- ## the main case `P = n+1`
    refine iotaFGen_chainMap f (n+1) σ ez q
      (fun τ => ((sCCMap R ez).f ((n+1)+q)).hom
        (xChain n q (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
          F (stdIdSimplex (n+1)) τ)) ?_ ?_
    · intro τ
      have hcm := congrArg (fun (g : (sCC R ((SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⊗ F)).X
            ((n+1)+(q+1)) ⟶ (sCC R (pullAlong f σ)).X ((n+1)+q)) =>
          g.hom (Work.SSSR.Cohomology.Crux33.ezGen (n+1) (q+1)
            (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) F (stdIdSimplex (n+1)) τ))
        ((sCCMap R ez).comm ((n+1)+(q+1)) ((n+1)+q))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcm
      rw [hcm]
      rw [show ((sCC R ((SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) ⊗ F)).d
            ((n+1)+(q+1)) ((n+1)+q)).hom
            (Work.SSSR.Cohomology.Crux33.ezGen (n+1) (q+1)
              (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0}) F (stdIdSimplex (n+1)) τ)
          = xChain n q (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
              F (stdIdSimplex (n+1)) τ
            + ((-1:ℤ)^(n+1)) • yChain (n+1) q
              (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
              F (stdIdSimplex (n+1)) τ from
        ezGen_boundary_succ n q (SSet.stdSimplex.obj (SimplexCategory.mk (n+1)) : SSet.{0})
          F (stdIdSimplex (n+1)) τ]
      rw [map_add, map_zsmul]
      congr 1
    · intro τ
      exact IotaAux.xChain_piecePi_eq_zero f n q σ ez hez τ

end

end Work.SSSR
