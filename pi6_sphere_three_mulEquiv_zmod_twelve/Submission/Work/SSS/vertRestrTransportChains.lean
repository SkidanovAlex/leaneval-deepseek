import Mathlib
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.transport_eq_topEnd
import Submission.Work.SSS.vertRestrPath
import Submission.Work.SSS.vertRestrReduction
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.vertPathExists
import Submission.Work.SSS.iotaTBdryHorn
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.KunnethEZ.ezChain_isCycle
import Submission.Work.SSS.vertRestrEZDefs
import Submission.Work.SSS.singPullbackIso_exists
import Submission.Work.SSS.transportIsoPathChain
import Submission.Work.SSS.sCCMap_ezChain_zero_last
import Submission.Work.SSS.vertZvtx_vtx0

/-!
# The `v₁`-vertex restriction of a coherent lift realises the fibre transport, for chains

This file proves `Work.SSS.vertRestrTransportChains`: for a Serre fibration `p : E → B`, a simplex
`σ : Δ[s+1] ⟶ Sing B` with `sigmaVert σ = b`, and `v : Sing (p⁻¹b) ⟶ Sing (p⁻¹b')` the vertex-`1`
restriction of the chosen coherent lift family (characterised by
`v ≫ sSingP (fibreIncl p b') = vertIncl p b s ≫ (δ₀ ⊗ 𝟙) ≫ liftFam p hfib (s+1) b σ h`), the image
of the homology class of a cycle chain `z` of the fibre over `b` under `v` is the parallel transport
of the class of `z` along the edge `σ|_{[v₀,v₁]}`.

The proof is the chain-level Eilenberg–Zilber construction of `Submission/Work/SSS/vertRestrEZDefs.lean`:

* `γ : Path b b'` is the edge path of `Work.SSS.vertPathExists`, whose edge simplex is
  `vertEdgeSimplex s σ`;
* `V = vertZ' p hfib s b σ h γ hγ e : Δ[1] ⊗ Sing F_b → Sing (Pullback p γ)` is the prism map of the
  vertex restriction (the factors are interchanged so that the EZ chain
  `ezChain t 0 (Sing F_b) Δ[1] z (genC Δ[1] ν)` of a `t`-chain and a *vertex* sits in degree
  `t + 0 = t`), and `W = (sCCMap V).f (t+1) (ezChain t 1 (Sing F_b) Δ[1] z [id])` is the associated
  EZ prism chain of degree `t + 1`;
* the Eilenberg–Zilber derivation identity (`Work.KunnethEZ.ezChain_derivation` for `t ≥ 1`,
  `Work.KunnethEZ.ezChain_d_left0` for `t = 0`) computes the boundary of `W` as the two vertex
  insertions `vtx0S1`, `vtx1S1`; these are evaluated by
  `Work.SSS.sCCMap_ezChain_zero_last` together with the vertex restrictions
  `Work.SSS.vertZvtx_vtx0` (= `sSingP (inclSource p γ)`) and `vertZvtx_vtx1_aux`
  (= `v ≫ sSingP (inclTarget p γ)`), giving
  `∂ W = ± ((targetChainMap p γ) (v_* z) - (sourceChainMap p γ) z)`;
* the chain-level transport criterion `Work.SSS.transportIsoPathChain` concludes.
-/

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

/-- The chain-map property of `sCCMap`, on an element. -/
lemma sCCMap_d_applyA {X Y : SSet.{0}} (φ : X ⟶ Y) (i j : ℕ) (x : (sCC X).X i) :
    (sCC Y).d i j ((sCCMap φ).f i x) = (sCCMap φ).f j ((sCC X).d i j x) := by
  have h := congrArg (fun (g : (sCC X).X i ⟶ (sCC Y).X j) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.Hom.comm (sCCMap φ) i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- **The vertex restriction of the prism map at the vertex `1` of `Δ[1]`** is the `v₁`-vertex
restriction `v` of the coherent lift followed by the target inclusion of the fibre. -/
private theorem vertZvtx_vtx1_aux {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ sSing B)
    (h : sigmaVert σ = b)
    (γ : Path b (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
    (hγ : (sSingP γ.toContinuousMap).app (op ⦋1⦌) lambda1 = vertEdgeSimplex s σ)
    (v : sSing (Work.StemsB.fibre p b) ⟶
      sSing (Work.StemsB.fibre p (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))
    (hv : v ≫ sSingP (Work.StemsB.fibreIncl p (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
      = vertIncl p b s ≫ (SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (sSing (Work.StemsB.fibre p b)))
          ≫ liftFam p hfib (s+1) b σ h)
    (e : sSing (Work.StemsB.Pullback p γ.toContinuousMap) ≅
      pullback (sSingP p) (sSingP γ.toContinuousMap))
    (he₁ : e.hom ≫ pullback.fst (sSingP p) (sSingP γ.toContinuousMap)
      = sSingP (Work.StemsB.pullbackFst p γ.toContinuousMap))
    (he₂ : e.hom ≫ pullback.snd (sSingP p) (sSingP γ.toContinuousMap)
      = sSingP (Work.StemsB.pullbackSnd p γ.toContinuousMap)) :
    vertZvtx p hfib s b σ h γ hγ e vtx1S1 = v ≫ sSingP (inclTarget p γ) := by
  -- The `E`-component of the vertex-`1` restriction is the restriction `v` of the coherent lift.
  have hfst : vertInclS1 p b vtx1S1 ≫ vertZE p hfib s b σ h
      = v ≫ sSingP (Work.StemsB.fibreIncl p (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))) := by
    rw [vertInclS1, vertZE, ← Category.assoc, CartesianMonoidalCategory.lift_map]
    rw [SSet.const_comp]
    rw [vertEdge_vtx1]
    simp only [Category.id_comp]
    rw [hv]
    rw [show vertIncl p b s ≫ (SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (sSing (Work.StemsB.fibre p b)))
            ≫ liftFam p hfib (s+1) b σ h
          = CartesianMonoidalCategory.lift
              (SSet.const ((SSet.stdSimplex.δ (n := s) 0).app (op ⦋0⦌) (ssetVertex s)))
              (𝟙 (sSing (Work.StemsB.fibre p b))) ≫ liftFam p hfib (s+1) b σ h from by
      rw [← Category.assoc, vertIncl, CartesianMonoidalCategory.lift_map, SSet.const_comp,
        Category.id_comp]]
  -- The `I`-component of the vertex-`1` restriction is the constant map at the point `1`.
  have hsnd : vertInclS1 p b vtx1S1 ≫ vertZI p b
      = SSet.const (vertLiftI.app (op ⦋0⦌) vtx1S1) := by
    rw [vertZI, vertInclS1, ← Category.assoc, CartesianMonoidalCategory.lift_fst, SSet.const_comp]
  -- The same two components for the target inclusion of the pullback.
  have h1 : v ≫ sSingP (inclTarget p γ) ≫ e.hom
        ≫ pullback.fst (sSingP p) (sSingP γ.toContinuousMap)
      = v ≫ sSingP (Work.StemsB.fibreIncl p (sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))) := by
    rw [he₁]
    simp only [sSingP]
    rw [← Functor.map_comp, inclTarget_comp_pullbackFst]
  have h2 : v ≫ sSingP (inclTarget p γ) ≫ e.hom
        ≫ pullback.snd (sSingP p) (sSingP γ.toContinuousMap)
      = SSet.const (vertLiftI.app (op ⦋0⦌) vtx1S1) := by
    rw [he₂]
    simp only [sSingP]
    rw [← Functor.map_comp, inclTarget_comp_pullbackSnd, TopCat.toSSet_map_const]
    rw [show TopCat.toSSetObj₀Equiv.symm (1 : unitInterval)
        = vertLiftI.app (op ⦋0⦌) vtx1S1 from by
      rw [← toSSetObj₀Equiv_vertLiftI_vtx1, Equiv.symm_apply_apply]]
    exact SSet.comp_const _ _
  -- Both sides become the same map into the pullback after composing with `e.hom`.
  have key : vertInclS1 p b vtx1S1
      ≫ pullback.lift (vertZE p hfib s b σ h) (vertZI p b)
          (vertZcompat p hfib s b σ h γ hγ)
      = v ≫ sSingP (inclTarget p γ) ≫ e.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [hfst, h1]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [hsnd, h2]
  show vertInclS1 p b vtx1S1
      ≫ (pullback.lift (vertZE p hfib s b σ h) (vertZI p b)
          (vertZcompat p hfib s b σ h γ hγ) ≫ e.inv) = v ≫ sSingP (inclTarget p γ)
  rw [← Category.assoc, key]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem vertRestrTransportChains {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (s t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (v : Work.SSS.sSing (Work.StemsB.fibre p b) ⟶
      Work.SSS.sSing (Work.StemsB.fibre p
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))
    (hv : v ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p
          (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
      = Work.SSS.vertIncl p b s
          ≫ (SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
          ≫ Work.SSS.liftFam p hfib (s+1) b σ h)
    (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
    (hz' : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p
              (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).d t
              ((ComplexShape.down ℕ).next t))) ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t)) z) = 0) :
    ∃ γ : Path b (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)),
      (Work.SSS.transportIsoPath p hfib γ t).hom
          ((Work.SSS.fibreCC p b).homologyπ t
            ((Work.SSS.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz))
        = (Work.SSS.fibreCC p (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).homologyπ t
            ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).cyclesMk
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap v).f t)) z)
              ((ComplexShape.down ℕ).next t) rfl hz') := by
  obtain ⟨γ, hγ⟩ := Work.SSS.vertPathExists s b σ h
  obtain ⟨e, he₁, he₂⟩ := Work.SSS.singPullbackIso_exists p γ.toContinuousMap
  refine ⟨γ, ?_⟩
  have hsrc : Work.SSS.sourceChainMap p γ = sCCMap (Work.SSS.sSingP (Work.SSS.inclSource p γ)) := rfl
  have htgt : Work.SSS.targetChainMap p γ = sCCMap (Work.SSS.sSingP (Work.SSS.inclTarget p γ)) := rfl
  cases t with
  | zero =>
    let V : (sSing (Work.StemsB.fibre p b) ⊗ stdS1) ⟶
        sSing (Work.StemsB.Pullback p γ.toContinuousMap) :=
      Work.SSS.vertZ' p hfib s b σ h γ hγ e
    let EZ : (sCC (sSing (Work.StemsB.fibre p b) ⊗ stdS1)).X 1 :=
      Work.KunnethEZ.ezChain 0 1 (sSing (Work.StemsB.fibre p b)) stdS1 z
        (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1))
    let W : (Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).X 1 :=
      (sCCMap V).f 1 EZ
    have heval : ∀ (ν : (stdS1) _⦋0⦌),
        (sCCMap V).f 0 (Work.KunnethEZ.ezChain 0 0 (sSing (Work.StemsB.fibre p b)) stdS1 z
            (Work.KunnethEZ.genC stdS1 ν))
          = (sCCMap (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
              (SSet.const ν) ≫ V)).f 0 z :=
      fun ν => Work.SSS.sCCMap_ezChain_zero_last V 0 ν z
    have hvt0 : (sCCMap (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
            (SSet.const Work.SSS.vtx0S1) ≫ V)).f 0 z
        = (Work.SSS.sourceChainMap p γ).f 0 z := by
      rw [show (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
            (SSet.const Work.SSS.vtx0S1) ≫ V)
          = Work.SSS.vertZvtx p hfib s b σ h γ hγ e Work.SSS.vtx0S1 from
        Work.SSS.vertZvtx_eq_braiding p hfib s b σ h γ hγ e Work.SSS.vtx0S1]
      rw [Work.SSS.vertZvtx_vtx0 p hfib s b σ h γ hγ e he₁ he₂, hsrc]
    have hvt1 : (sCCMap (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
            (SSet.const Work.SSS.vtx1S1) ≫ V)).f 0 z
        = (Work.SSS.targetChainMap p γ).f 0 ((sCCMap v).f 0 z) := by
      rw [show (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
            (SSet.const Work.SSS.vtx1S1) ≫ V)
          = Work.SSS.vertZvtx p hfib s b σ h γ hγ e Work.SSS.vtx1S1 from
        Work.SSS.vertZvtx_eq_braiding p hfib s b σ h γ hγ e Work.SSS.vtx1S1]
      rw [vertZvtx_vtx1_aux p hfib s b σ h γ hγ v hv e he₁ he₂, htgt]
      rw [← sCCMap_comp_apply]
    have hbd : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
          (0+1) (0+0))) W
        = (Work.SSS.targetChainMap p γ).f 0 ((sCCMap v).f 0 z)
          - (Work.SSS.sourceChainMap p γ).f 0 z := by
      have h1 : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
            (0+1) (0+0))) W
          = (sCCMap V).f 0 ((ModuleCat.Hom.hom
              ((sCC (sSing (Work.StemsB.fibre p b) ⊗ stdS1)).d (0+1) (0+0))) EZ) :=
        sCCMap_d_applyA V (0+1) (0+0) EZ
      rw [h1]
      have h2 : (ModuleCat.Hom.hom ((sCC (sSing (Work.StemsB.fibre p b) ⊗ stdS1)).d
            (0+1) (0+0))) EZ
          = Work.KunnethEZ.ezChain 0 0 (sSing (Work.StemsB.fibre p b)) stdS1 z
              ((ModuleCat.Hom.hom ((sCC stdS1).d (0+1) 0))
                (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1))) :=
        Work.KunnethEZ.ezChain_d_left0 0 (sSing (Work.StemsB.fibre p b)) stdS1 z
          (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1))
      rw [h2, Work.KunnethEZ.d_genC 0 stdS1 (Work.SSS.stdIdSimplex 1)]
      rw [Work.KunnethEZ.ezChain_sum_right 0 0 (sSing (Work.StemsB.fibre p b)) stdS1 Finset.univ
        (fun i : Fin 2 => (-1:ℤ)^(i:ℕ))
        (fun i : Fin 2 => Work.KunnethEZ.genC stdS1 ((stdS1).δ i (Work.SSS.stdIdSimplex 1)))
        z]
      rw [map_sum]
      simp only [map_zsmul]
      have h0 : (sCCMap V).f 0 (Work.KunnethEZ.ezChain 0 0 (sSing (Work.StemsB.fibre p b)) stdS1 z
            (Work.KunnethEZ.genC stdS1 ((stdS1).δ 0 (Work.SSS.stdIdSimplex 1))))
          = (Work.SSS.targetChainMap p γ).f 0 ((sCCMap v).f 0 z) := by
        rw [show (stdS1).δ 0 (Work.SSS.stdIdSimplex 1) = Work.SSS.vtx1S1 from rfl]
        rw [heval Work.SSS.vtx1S1, hvt1]
      have h0' : (sCCMap V).f 0 (Work.KunnethEZ.ezChain 0 0 (sSing (Work.StemsB.fibre p b)) stdS1 z
            (Work.KunnethEZ.genC stdS1 ((stdS1).δ 1 (Work.SSS.stdIdSimplex 1))))
          = (Work.SSS.sourceChainMap p γ).f 0 z := by
        rw [show (stdS1).δ 1 (Work.SSS.stdIdSimplex 1) = Work.SSS.vtx0S1 from rfl]
        rw [heval Work.SSS.vtx0S1, hvt0]
      rw [Fin.sum_univ_two, h0, h0']
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one]
      abel
    have hWfin : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
          (0+1) 0)) (-W)
        = (Work.SSS.sourceChainMap p γ).f 0 z
          - (Work.SSS.targetChainMap p γ).f 0 ((sCCMap v).f 0 z) := by
      rw [map_neg, hbd]
      abel
    exact Work.SSS.transportIsoPathChain p hfib γ 0 z hz ((sCCMap v).f 0 z) hz' (-W) hWfin
  | succ t' =>
    let V : (sSing (Work.StemsB.fibre p b) ⊗ stdS1) ⟶
        sSing (Work.StemsB.Pullback p γ.toContinuousMap) :=
      Work.SSS.vertZ' p hfib s b σ h γ hγ e
    let EZ : (sCC (sSing (Work.StemsB.fibre p b) ⊗ stdS1)).X (Nat.succ t' + 1) :=
      Work.KunnethEZ.ezChain (Nat.succ t') 1 (sSing (Work.StemsB.fibre p b)) stdS1 z
        (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1))
    let W : (Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).X (Nat.succ t' + 1) :=
      (sCCMap V).f (Nat.succ t' + 1) EZ
    have hz_t : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d (Nat.succ t') t')) z = 0 := by
      have hn : (ComplexShape.down ℕ).next (Nat.succ t') = t' := ChainComplex.next_nat_succ t'
      have h := hz
      rwa [hn] at h
    have heval : ∀ (ν : (stdS1) _⦋0⦌),
        (sCCMap V).f (Nat.succ t') (Work.KunnethEZ.ezChain (Nat.succ t') 0
            (sSing (Work.StemsB.fibre p b)) stdS1 z (Work.KunnethEZ.genC stdS1 ν))
          = (sCCMap (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
              (SSet.const ν) ≫ V)).f (Nat.succ t') z :=
      fun ν => Work.SSS.sCCMap_ezChain_zero_last V (Nat.succ t') ν z
    have hrawY : ∀ (w : (sCC stdS1).X 0),
        Work.KunnethEZ.rawY t' 0 (sSing (Work.StemsB.fibre p b)) stdS1 z w
          = Work.KunnethEZ.ezChain (Nat.succ t') 0 (sSing (Work.StemsB.fibre p b)) stdS1 z w := by
      intro w
      rw [Work.KunnethEZ.rawY_eq_ezChain t' 0 (sSing (Work.StemsB.fibre p b)) stdS1 rfl z w]
      simp
    have hvt0 : (sCCMap (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
            (SSet.const Work.SSS.vtx0S1) ≫ V)).f (Nat.succ t') z
        = (Work.SSS.sourceChainMap p γ).f (Nat.succ t') z := by
      rw [show (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
            (SSet.const Work.SSS.vtx0S1) ≫ V)
          = Work.SSS.vertZvtx p hfib s b σ h γ hγ e Work.SSS.vtx0S1 from
        Work.SSS.vertZvtx_eq_braiding p hfib s b σ h γ hγ e Work.SSS.vtx0S1]
      rw [Work.SSS.vertZvtx_vtx0 p hfib s b σ h γ hγ e he₁ he₂, hsrc]
    have hvt1 : (sCCMap (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
            (SSet.const Work.SSS.vtx1S1) ≫ V)).f (Nat.succ t') z
        = (Work.SSS.targetChainMap p γ).f (Nat.succ t') ((sCCMap v).f (Nat.succ t') z) := by
      rw [show (CartesianMonoidalCategory.lift (𝟙 (sSing (Work.StemsB.fibre p b)))
            (SSet.const Work.SSS.vtx1S1) ≫ V)
          = Work.SSS.vertZvtx p hfib s b σ h γ hγ e Work.SSS.vtx1S1 from
        Work.SSS.vertZvtx_eq_braiding p hfib s b σ h γ hγ e Work.SSS.vtx1S1]
      rw [vertZvtx_vtx1_aux p hfib s b σ h γ hγ v hv e he₁ he₂, htgt]
      rw [← sCCMap_comp_apply]
    have h0 : (sCCMap V).f (Nat.succ t') (Work.KunnethEZ.ezChain (Nat.succ t') 0
            (sSing (Work.StemsB.fibre p b)) stdS1 z
            (Work.KunnethEZ.genC stdS1 ((stdS1).δ 0 (Work.SSS.stdIdSimplex 1))))
        = (Work.SSS.targetChainMap p γ).f (Nat.succ t') ((sCCMap v).f (Nat.succ t') z) := by
      rw [show (stdS1).δ 0 (Work.SSS.stdIdSimplex 1) = Work.SSS.vtx1S1 from rfl]
      rw [heval Work.SSS.vtx1S1, hvt1]
    have h0' : (sCCMap V).f (Nat.succ t') (Work.KunnethEZ.ezChain (Nat.succ t') 0
            (sSing (Work.StemsB.fibre p b)) stdS1 z
            (Work.KunnethEZ.genC stdS1 ((stdS1).δ 1 (Work.SSS.stdIdSimplex 1))))
        = (Work.SSS.sourceChainMap p γ).f (Nat.succ t') z := by
      rw [show (stdS1).δ 1 (Work.SSS.stdIdSimplex 1) = Work.SSS.vtx0S1 from rfl]
      rw [heval Work.SSS.vtx0S1, hvt0]
    have hbd : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
          (Nat.succ t' + 1) (Nat.succ t'))) W
        = ((-1:ℤ)^(Nat.succ t')) •
            ((Work.SSS.targetChainMap p γ).f (Nat.succ t') ((sCCMap v).f (Nat.succ t') z)
              - (Work.SSS.sourceChainMap p γ).f (Nat.succ t') z) := by
      have h1 : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
            (Nat.succ t' + 1) (Nat.succ t'))) W
          = (sCCMap V).f (Nat.succ t') ((ModuleCat.Hom.hom
              ((sCC (sSing (Work.StemsB.fibre p b) ⊗ stdS1)).d (Nat.succ t' + 1) (Nat.succ t'))) EZ) :=
        sCCMap_d_applyA V (Nat.succ t' + 1) (Nat.succ t') EZ
      rw [h1]
      have h2 : (ModuleCat.Hom.hom ((sCC (sSing (Work.StemsB.fibre p b) ⊗ stdS1)).d
            (Nat.succ t' + 1) (Nat.succ t'))) EZ
          = Work.KunnethEZ.rawX t' 0 (sSing (Work.StemsB.fibre p b)) stdS1
              ((ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d (Nat.succ t') t')) z)
              (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1))
            + ((-1:ℤ)^(Nat.succ t')) •
              Work.KunnethEZ.rawY t' 0 (sSing (Work.StemsB.fibre p b)) stdS1 z
                ((ModuleCat.Hom.hom ((sCC stdS1).d (0+1) 0))
                  (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1))) :=
        Work.KunnethEZ.ezChain_derivation t' 0 (sSing (Work.StemsB.fibre p b)) stdS1 z
          (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1))
      rw [h2]
      rw [hrawY ((ModuleCat.Hom.hom ((sCC stdS1).d (0+1) 0))
            (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1)))]
      rw [hz_t]
      rw [show Work.KunnethEZ.rawX t' 0 (sSing (Work.StemsB.fibre p b)) stdS1 0
            (Work.KunnethEZ.genC stdS1 (Work.SSS.stdIdSimplex 1)) = 0 from by
        rw [Work.KunnethEZ.rawX]
        simp only [map_zero, LinearMap.zero_apply]]
      rw [zero_add]
      rw [Work.KunnethEZ.d_genC 0 stdS1 (Work.SSS.stdIdSimplex 1)]
      rw [Work.KunnethEZ.ezChain_sum_right (Nat.succ t') 0 (sSing (Work.StemsB.fibre p b)) stdS1
        Finset.univ (fun i : Fin 2 => (-1:ℤ)^(i:ℕ))
        (fun i : Fin 2 => Work.KunnethEZ.genC stdS1 ((stdS1).δ i (Work.SSS.stdIdSimplex 1)))
        z]
      rw [map_zsmul, map_sum]
      simp only [map_zsmul]
      rw [Fin.sum_univ_two, h0, h0']
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one]
      abel
    have hcc : ((-1:ℤ)^(Nat.succ t')) * ((-1:ℤ)^(Nat.succ t')) = 1 := by
      rw [← pow_add, show (Nat.succ t') + (Nat.succ t') = 2 * (Nat.succ t') from by ring, pow_mul]
      norm_num
    have hWfin : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
          (Nat.succ t' + 1) (Nat.succ t'))) (-(((-1:ℤ)^(Nat.succ t')) • W))
        = (Work.SSS.sourceChainMap p γ).f (Nat.succ t') z
          - (Work.SSS.targetChainMap p γ).f (Nat.succ t') ((sCCMap v).f (Nat.succ t') z) := by
      rw [map_neg, map_zsmul, hbd, smul_smul, hcc, one_smul]
      abel
    exact Work.SSS.transportIsoPathChain p hfib γ (Nat.succ t') z hz ((sCCMap v).f (Nat.succ t') z)
      hz' (-(((-1:ℤ)^(Nat.succ t')) • W)) hWfin


end Work.SSS
