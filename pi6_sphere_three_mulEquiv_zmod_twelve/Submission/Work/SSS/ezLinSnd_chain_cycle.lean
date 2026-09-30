import Mathlib
import Submission.Work.SSS.iotaF_isCycle
import Submission.Work.SSS.hornCok_d_faceLift_chain
import Submission.Work.SSS.ezLinSnd_boundary
import Submission.Work.SSS.ezSimplexZero_aux
import Submission.Work.SSS.iotaFGen_chainMap_anyP
import Submission.Work.SSS.iotaFGen_zero_cycle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

/-! ## The linearised Eilenberg–Zilber shuffle chain and `iotaFGen`

`Work.SSS.ezLinSnd P q X F (stdIdSimplex P)` is the linear extension, in the second variable, of the
Eilenberg–Zilber shuffle chain `ezGen P q X F (stdIdSimplex P)`.  It is exactly the `Sigma.desc`-map
that underlies `Work.SSS.iotaFGen`; composing it with the chain map `sCCMap ez` induced by a lift
`ez : Δ[P] ⊗ F ⟶ T_σ` and with the projection `pieceπOf f σ` to the σ-piece therefore recovers
`iotaFGen f P q σ ez`.  This identification is what lets the chain-map properties of `iotaFGen` be
applied to the chain-level shuffle chain. -/

/-- **The chain-level shuffle chain, pushed into the σ-piece, is `iotaFGen`.**  For an abstract lift
`ez : Δ[P] ⊗ F ⟶ T_σ` of `pr₁ ≫ σ` and every degree `q`, the composite
`ezLinSnd P q Δ[P] F (stdIdSimplex P) ≫ sCCMap ez ≫ pieceπOf f σ` equals `iotaFGen f P q σ ez`:
both are the `Sigma.desc` of the shuffle chains of the fundamental `P`-simplex, pushed along `ez` and
projected. -/
lemma ezLinSnd_sCCMap_pieceπOf_eq_iotaFGen {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ) :
    ezLinSnd P q (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) F (stdIdSimplex P)
      ≫ (sCCMap ez).f (P+q) ≫ (pieceπOf f σ).f (P+q)
      = iotaFGen f P q σ ez := by
  apply SSet.chainComplex_hom_ext (X := F) (n := q)
  intro τ
  rw [← Category.assoc, ezLinSnd_ι_eltHom, eltHom_comp, iotaFGen_gen]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]

/-- For a lift `ez : Δ[P] ⊗ Sing (p⁻¹b) ⟶ T_σ` of `pr₁ ≫ σ` (`hez`) and an arbitrary CHAIN
`z ∈ C_t(Sing (p⁻¹b))` with `∂z = 0`, the shuffle chain `ezLinSnd P t Δ[P] F (stdIdSimplex P) z`
pushed into `T_σ` along `ez` and projected to the σ-piece `C(T_σ)/C(∂T_σ)` is a cycle.  This is the
CHAIN-level (non-vacuous) form of the PROVED simplex-level `Work.SSS.sCCMap_ezGen_chain_cycle`,
whose hypothesis is a cycle SIMPLEX and hence says nothing in even fibre degrees.
Route: `iotaFGen`-route (use the PROVED `Work.SSS.iotaFGen_gen_apply`, `ezLinSnd_apply`,
`Work.KunnethEZ.chain_eq_sum_gen` for linearity, then `Work.SSS.iotaFGen_chainMap` with `Hbd` from
`Work.SSS.ezGen_boundary_succ`/`ezGen_boundary_zero` and `HXT` from
`Work.SSS.IotaAux.xChain_piecePi_eq_zero`; fibre degree 0 separately by linearity and the PROVED
`Work.SSS.IotaAux.iotaFGen_zero_d`), or the direct route via `Work.SSS.ezLinSnd_boundary` +
`Work.SSS.pieceAlong_d_pieceπOf_sCCMap` + `Work.SSS.sCCMap_pieceπOf_genP_bdry`. -/
theorem ezLinSnd_chain_cycle {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (P t : ℕ) (b : B) (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})) ⟶ Work.SSS.sSing B) (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⊗ Work.SSS.sSing (Work.StemsB.fibre p b)) ⟶ Work.SSS.pullAlong (Work.SSS.sSingP p) σ) (hez : ez ≫ pullback.fst σ (Work.SSS.sSingP p) = SemiCartesianMonoidalCategory.fst _ _) (z : (Work.SSS.fibreCC p b).X t) (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0) : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (P+t) ((ComplexShape.down ℕ).next (P+t)))) ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (P+t))) ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (P+t))) (Work.SSS.ezLinSnd P t (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P) z))) = 0 := by
  -- Identify the pushed/projected shuffle chain with `iotaFGen` applied to the chain.
  have hid := ezLinSnd_sCCMap_pieceπOf_eq_iotaFGen (Work.SSS.sSingP p) P t σ ez
  have h1 : (ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p) σ).f (P+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap ez).f (P+t)))
        (ModuleCat.Hom.hom (Work.SSS.ezLinSnd P t
          (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex P)) z))
      = ModuleCat.Hom.hom (Work.SSS.iotaFGen (Work.SSS.sSingP p) P t σ ez) z := by
    have h := congrArg (fun (g : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).X t ⟶
        (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).X (P+t)) => g.hom z) hid
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  rw [h1]
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · -- ## fibre degree `0`: the image of an arbitrary `0`-chain under `iotaFGen` is a cycle
    subst ht0
    simpa using iotaFGen_zero_cycle (Work.SSS.sSingP p) P σ ez hez z
  · -- ## fibre degree `q + 1`: the chain-map property `∂(ι_σ z) = (-1)^P ι_σ(∂z)` of `iotaFGen`
    obtain ⟨q, rfl⟩ : ∃ q, t = q + 1 := ⟨t - 1, by omega⟩
    have hz' : (ModuleCat.Hom.hom
        ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).d (q+1) q)) z = 0 := by
      have h := hz
      rw [show (ComplexShape.down ℕ).next (q+1) = q from by rw [down_next_eq]; omega] at h
      exact h
    have hnext : (ComplexShape.down ℕ).next (P + (q+1)) = P + q := by
      rw [down_next_eq]; omega
    rw [hnext]
    have hcm := iotaFGen_chainMap_anyP (Work.SSS.sSingP p) P q σ ez hez
    have h2 : (ModuleCat.Hom.hom
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (P + (q+1)) (P + q)))
        (ModuleCat.Hom.hom (Work.SSS.iotaFGen (Work.SSS.sSingP p) P (q+1) σ ez) z)
        = (-1 : ℤ)^P • (ModuleCat.Hom.hom (Work.SSS.iotaFGen (Work.SSS.sSingP p) P q σ ez)
            ((ModuleCat.Hom.hom
              ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).d (q+1) q)) z)) := by
      have h := congrArg (fun (g : (Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p b))).X (q+1) ⟶
          (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).X (P+q)) => g.hom z) hcm
      simpa using h
    rw [h2, hz', map_zero]
    exact zsmul_zero _

end Work.SSS
