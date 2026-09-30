import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.SSSR.SSetChain
import Submission.Work.SSSR.pieceContraction
import Submission.Work.SSSR.cokernelAcyclicOfHomotopy
import Submission.Work.StemsB.Fibrations
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/-- **Every cycle of `T_σ` is homologous to a cycle in the horn.**  For a Serre fibration `p`, a
simplex `σ` of the base and a cycle `z` of the singular chains of the pullback `T_σ`, the class of
`z` is represented by a chain `z'` coming from the horn `Λ = pieceHorn (sSingP p) σ`.

This is the `Work.SSSR`-spelling of the statement (all occurrences of the objects are written in
the `Work.SSSR` mirror of `Work.SSS`). -/
private theorem pieceHorn_lift_aux {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (q : ℕ)
    (z : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X q)
    (hz : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d q (q - 1) z = 0) :
    ∃ (z' : (Work.SSSR.sChains 𝕜 ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).toSSet)).X q)
      (c : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (q + 1)),
      z = (Work.SSSR.sChainMap 𝕜 (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f q z'
          + ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (q + 1) q) c := by
  classical
  -- the combinatorial contraction of the pair `(T_σ, Λ)`
  obtain ⟨g, H, hg, hH⟩ := Work.SSSR.pieceContraction p hfib (le_refl 1) σ
  have hle : SSet.Subcomplex.range g ≤ Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ := by
    rw [Subfunctor.le_def]
    intro U x hx
    rw [Subfunctor.range_obj] at hx
    obtain ⟨y, rfl⟩ := hx
    exact hg U.unop.len y
  let g' : Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ ⟶
      (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).toSSet := SSet.Subcomplex.lift g hle
  have hg' : g' ≫ (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι = g :=
    SSet.Subcomplex.lift_ι g hle
  -- the induced chain homotopy between the identity and the push-forward of `g`
  have hid : SSet.chainComplexMap (𝟙 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
        (ModuleCat.of 𝕜 𝕜)
      = 𝟙 (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) := by
    rw [show SSet.chainComplexMap (𝟙 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ))
          (ModuleCat.of 𝕜 𝕜) =
        ((SSet.chainComplexFunctor (ModuleCat 𝕜)).obj (ModuleCat.of 𝕜 𝕜)).map
          (𝟙 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) from rfl,
      CategoryTheory.Functor.map_id]
  let K : Homotopy (𝟙 (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)))
      (Work.SSSR.sChainMap 𝕜 g) :=
    (Homotopy.ofEq hid.symm).trans (H.sSetChainComplexMap (ModuleCat.of 𝕜 𝕜))
  -- the homotopy identity `z = s(∂z) + ∂(sz) + g z`
  have hcomm := K.comm q
  rw [HomologicalComplex.id_f, dNext_nat, Work.SSSR.prevD_chain_nat] at hcomm
  have hh := congrArg (fun (φ : (Work.SSSR.sChains 𝕜
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X q ⟶
      (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X q) => φ.hom z) hcomm
  have hz0 : ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d q (q - 1)).hom z
      = 0 := hz
  simp only [ModuleCat.hom_id, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.comp_apply, hz0, map_zero, zero_add] at hh
  -- `g` is `ι` after `g'`, so the last term is a chain of the horn
  have hzg : ((Work.SSSR.sChainMap 𝕜 ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι).f q).hom
        (((Work.SSSR.sChainMap 𝕜 g').f q).hom z)
      = ((Work.SSSR.sChainMap 𝕜 g).f q).hom z := by
    have h1 : Work.SSSR.sChainMap 𝕜 g' ≫
          Work.SSSR.sChainMap 𝕜 (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι
        = Work.SSSR.sChainMap 𝕜 g := by
      rw [Work.SSSR.sChainMap_comp, hg']
    have h2 := congrArg (fun (φ : Work.SSSR.sChains 𝕜
          (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) ⟶
        Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)) =>
          (φ.f q).hom z) h1
    simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  refine ⟨(Work.SSSR.sChainMap 𝕜 g').f q z, (K.hom q (q + 1)).hom z, ?_⟩
  change z = ((Work.SSSR.sChainMap 𝕜 ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι).f q).hom
        (((Work.SSSR.sChainMap 𝕜 g').f q).hom z)
      + ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (q + 1) q).hom
          ((K.hom q (q + 1)).hom z)
  rw [hzg]
  exact hh.trans (add_comm _ _)

theorem pieceHorn_lift {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (q : ℕ)
    (z : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).X q)
    (hz : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).d q (q - 1) z = 0) :
    ∃ (z' : (Work.SSSR.sChains 𝕜 ((Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).toSSet)).X q)
      (c : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).X (q + 1)),
      z = (Work.SSSR.sChainMap 𝕜 (Work.SSSR.pieceHorn (Work.SSS.sSingP p) σ).ι).f q z'
          + ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSS.sSingP p) σ)).d (q + 1) q) c := by
  exact pieceHorn_lift_aux p hfib σ q z hz

end

end Work.Pi6.MSS
