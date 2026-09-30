import Mathlib
import Submission.Work.Pi6.MSS.E2cfkDefs
import Submission.Work.SSSR.pieceContraction
import Submission.Work.SSSR.cokernelAcyclicOfHomotopy
import Submission.Work.SSSR.SSetChain
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The horn lifting with a cycle in the horn

`Work.Pi6.MSS.pieceHorn_lift_cycle` is `Work.Pi6.MSS.pieceHorn_lift` with the extra information
that the chain of the horn may be taken to be a cycle when the chain we start from is one; it is
the input of the transport `Work.Pi6.MSS.transport_chain`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Pi6.MSS
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
variable (q : ℕ) (hfib : Work.StemsB.IsSerreFibration p)

/-- Functoriality of the singular chain complex on morphisms of simplicial sets. -/
theorem ccMap_comp {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.chainComplexMap (f ≫ g) (ModuleCat.of 𝕜 𝕜)
      = SSet.chainComplexMap f (ModuleCat.of 𝕜 𝕜) ≫
        SSet.chainComplexMap g (ModuleCat.of 𝕜 𝕜) := by
  rw [show SSet.chainComplexMap (f ≫ g) (ModuleCat.of 𝕜 𝕜)
        = ((SSet.chainComplexFunctor (ModuleCat 𝕜)).obj (ModuleCat.of 𝕜 𝕜)).map (f ≫ g)
        from rfl,
    CategoryTheory.Functor.map_comp]

/-- **The horn lifting in the form used for the transport**: the chain of the horn may be taken to
be a cycle whenever the chain we start from is one.  (This is the same argument as
`Work.Pi6.MSS.pieceHorn_lift`, with the explicit description of the horn chain as the image under
the contraction `g'` of the cycle.) -/
theorem pieceHorn_lift_cycle (hfib : Work.StemsB.IsSerreFibration p) (q : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (z : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X q)
    (hz : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d q (q - 1) z = 0) :
    ∃ (z' : (Work.SSSR.sChains 𝕜
          ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).toSSet)).X q)
      (c : (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (q + 1)),
      (Work.SSSR.sChains 𝕜
          ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).toSSet)).d q (q - 1) z' = 0 ∧
      z = (Work.SSSR.sChainMap 𝕜 (Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).ι).f q z'
          + ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (q + 1) q) c := by
  classical
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
  have hcomm := K.comm q
  rw [HomologicalComplex.id_f, dNext_nat, Work.SSSR.prevD_chain_nat] at hcomm
  have hh := congrArg (fun (φ : (Work.SSSR.sChains 𝕜
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X q ⟶
      (Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X q) => φ.hom z) hcomm
  have hz0 : ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d q (q - 1)).hom z
      = 0 := hz
  simp only [ModuleCat.hom_id, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.comp_apply, hz0, map_zero, zero_add] at hh
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
  have hcyc : ModuleCat.Hom.hom ((Work.SSSR.sChains 𝕜
        ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).toSSet)).d q (q - 1))
        (ModuleCat.Hom.hom ((Work.SSSR.sChainMap 𝕜 g').f q) z) = 0 := by
    have hcm := HomologicalComplex.Hom.comm (Work.SSSR.sChainMap 𝕜 g') q (q - 1)
    have h2 := congrArg (fun (φ : (Work.SSSR.sChains 𝕜
          (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X q ⟶
        (Work.SSSR.sChains 𝕜
          ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ).toSSet)).X (q - 1)) =>
            φ.hom z) hcm
    have hz' : ModuleCat.Hom.hom ((Work.SSSR.sChains 𝕜
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d q (q - 1)) z = 0 := hz
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz', map_zero] at h2
    exact h2
  refine ⟨(Work.SSSR.sChainMap 𝕜 g').f q z, (K.hom q (q + 1)).hom z, hcyc, ?_⟩
  change z = ((Work.SSSR.sChainMap 𝕜 ((Work.SSSR.pieceHorn (Work.SSSR.sSingP p) σ)).ι).f q).hom
        (((Work.SSSR.sChainMap 𝕜 g').f q).hom z)
      + ((Work.SSSR.sChains 𝕜 (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d (q + 1) q).hom
          ((K.hom q (q + 1)).hom z)
  rw [hzg]
  exact hh.trans (add_comm _ _)


end

end Work.Pi6.MSS
