import Mathlib
import Submission.Work.SSS.serreE1CruxD1
import Submission.Work.SSS.faceB_grFi_nondeg
import Submission.Work.SSS.faceB_grFi_degenerate
import Submission.Work.SSS.faceB_grFi_zero
import Submission.Work.SSS.iotaF_pieceCastElem
import Submission.Work.SSS.ezSimplexZero_chain_class
import Submission.Work.SSS.jF_eq_grFi
import Submission.Work.SSS.faceD_iota
import Submission.Work.SSS.nIndexSigma_face
import Submission.Work.SSS.exists_cycleMk
import Submission.Work.SSS.cyclesMk_sum
import Submission.Work.SSS.d_sndToR_iotaTLin
import Submission.Work.SSS.homologyMap_cyclesMk
import Submission.Work.SSS.chainCondAux
import Submission.Work.SSS.kF_psiCoef_gen
import Submission.Work.SSS.faceB_class_nondeg
import Submission.Work.SSS.faceB_class_zero

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable


/-- `homologyπ` of a cycle class only depends on the underlying element. -/
lemma homologyπ_cyclesMk_eq {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) {x x' : K.X i} (hxx : x = x')
    (hx : (ModuleCat.Hom.hom (K.d i j)) x = 0)
    (hx' : (ModuleCat.Hom.hom (K.d i j)) x' = 0) :
    K.homologyπ i (K.cyclesMk x j hj hx) = K.homologyπ i (K.cyclesMk x' j hj hx') := by
  subst hxx
  rfl

/-- Pulling an integer scalar out of a finite sum, for the canonical (`zsmul`) action on an
abelian group.  Stated with `zsmul` rather than `DistribSMul` so that it applies to module objects
such as `ModuleCat ℤ`. -/
lemma zsmul_finset_sum {N : Type} [AddCommGroup N] {ι : Type} (s : Finset ι) (a : ℤ)
    (f : ι → N) : (∑ i ∈ s, a • f i) = a • ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, zsmul_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, zsmul_add]

/-- **The generator-level computation of `d¹`._**  For the comparison map `PsiSig` of the first page,
the canonical Serre filtration `xiCan p`, a nondegenerate `(s+1)`-simplex `σ` of the base and a
cycle `z` of the fibre over the first vertex of `σ`, the two sides of the chain condition agree on
the generator `(triv_b) (homologyπ z)` of `H_t(F_b)`.

NOTE: the module `Submission.Work.SSS.mapPhiY_iotaF_gen` (lemma `Work.SSS.mapPhiY_iotaF_gen`, being
written in parallel) is also needed; add its import when it exists.  Do NOT import
`Submission.Work.SSS.serreE1Main`: it contains a duplicate declaration of this statement (with
`sorry`), which will be removed once this one is proved.

Route (all steps use PROVED lemmas of this workspace): `Sigma_ι_comp_PsiSig` and `d1 = kF ≫ jF`;
`(PsiCoef σ).hom (T zh) = c(s+1) • [ι_σ z]` by `PieceInv` (`pieceInv_of_pieceAlpha`) at `(s+1)`;
`H(mapPhiY σ) [ι_σ z] = [grFι f (s+1) w]`, `w := (sCCMap (sndToR σ)) (iotaTLin σ z)`, by
`mapPhiY_iotaF_gen` and `homologyMap_cyclesMk`; `kF (xiCan p) s t` of that class is the class of
`faceSum` by `kF_eq_of_lift` (`hw` is `rfl` by `grFι_succ`, `hv` is `d_sndToR_iotaTLin`, `hvcyc`
from `hv` via `d_comp_d` and injectivity of `incF (Fc p) s`); then `jF_eq_grFi`,
`homologyMap_cyclesMk`, `dsimp only [faceSum]` with `map_sum`/`map_zsmul`, `cyclesMk_sum` in the
complex `grF (Fc p) s`, and additivity of `homologyπ` give the alternating sum of the classes
`[grFι f s (faceB ... i)]`; each is identified with `H(mapPhiY ρ_i)([ιF ρ_i z])` by
`faceB_grFi_nondeg` (`ρ_i := nIndexEquiv (sSing B) s ⟨δ i (nIndexBase (sSing B) σ), hnd⟩`,
`hρi := (nIndexSigma_face σ i hnd).symm`), with `0` by `faceB_grFi_degenerate`, and with
`H(mapPhiY ρ_0)([ιF ρ_0 z'])` by `faceB_grFi_zero` + `ezSimplexZero_chain_class` +
`iotaF_pieceCastElem`, where `z'` comes from `exists_cycleMk` applied to
`(triv_{σ_0(v_0)}).inv (T_b zh)`.
On the other side `faceD_iota` + `Preadditive.sum_comp` + `Sigma_ι_comp_PsiSig` + `PieceInv` at `s`
give `(c(s+1)*c s) • Σ_i (-1)^i (if hnd then c s • H(mapPhiY ρ_i)([ιF ρ_i z_i]) else 0)`, and
`c(s+1) • X = (c(s+1)*c s) • (c s • X)` since `c s * c s = 1` (from `hc1`). -/

theorem chainCondition_gen (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSS.PieceAlpha p hfib c)
    (s : ℕ) (σ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1))
    (z : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
        Work.SSS.coefM p e₀ t) σ ≫
        Work.SSS.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSS.d1 (Work.SSS.xiCan p) s t))
      ((Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
        ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
          ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz)))
    = (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
        Work.SSS.coefM p e₀ t) σ ≫
        ((c (s+1) * c s) • (Work.SSS.faceD' (Work.SSS.sSing B) (Work.SSS.coefM p e₀ t) s ≫
          Work.SSS.PsiSig p e₀ hfib hc t s))))
      ((Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
        ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
          ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz))) := by
  set M0 := (Work.SSS.triv p e₀ hfib hc t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).hom
      ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).homologyπ t
        ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (Work.SSS.sigHat σ))).cyclesMk z
          ((ComplexShape.down ℕ).next t) rfl hz)) with hM0
  have hv : (ModuleCat.Hom.hom (((Work.SSS.Fc p).obj (s+1)).d ((s+1)+t) (s+t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
        (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z))
      = (ModuleCat.Hom.hom ((Work.SSS.incF (Work.SSS.Fc p) s).f (s+t)))
        (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z) :=
    Work.SSS.d_sndToR_iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) σ rfl z hz
  have hvcyc : (ModuleCat.Hom.hom (((Work.SSS.Fc p).obj s).d (s+t) ((ComplexShape.down ℕ).next (s+t))))
      (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z) = 0 := by
    haveI : Mono (Work.SSS.incF (Work.SSS.Fc p) s) := (Work.SSS.xiCan p).mono s
    refine (ModuleCat.mono_iff_injective ((Work.SSS.incF (Work.SSS.Fc p) s).f
      ((ComplexShape.down ℕ).next (s+t)))).mp inferInstance ?_
    rw [map_zero]
    rw [← Work.SSS.chainMap_comm_apply_elem (Work.SSS.incF (Work.SSS.Fc p) s)
      (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)]
    rw [← hv]
    have h2 := congrArg (fun (g : ((Work.SSS.Fc p).obj (s+1)).X ((s+1)+t) ⟶
        ((Work.SSS.Fc p).obj (s+1)).X ((ComplexShape.down ℕ).next (s+t)))
      => (ModuleCat.Hom.hom g)
          ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.sndToR (Work.SSS.sSingP p) σ)).f ((s+1)+t)))
            (Work.SSS.iotaTLin p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)))
      (HomologicalComplex.d_comp_d ((Work.SSS.Fc p).obj (s+1)) ((s+1)+t) (s+t) ((ComplexShape.down ℕ).next (s+t)))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h2
  have hkF := Work.SSS.kF_psiCoef_gen p e₀ hfib hc t c hc1 hal s σ z hz hvcyc
  have hL1 : (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
        Work.SSS.coefM p e₀ t) σ ≫
        Work.SSS.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSS.kF (Work.SSS.xiCan p) s t)) M0
      = c (s+1) • ((Work.SSS.Fc p).obj s).homologyπ (s+t)
          (((Work.SSS.Fc p).obj s).cyclesMk
            (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)
            ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc) := by
    rw [← Category.assoc, Work.SSS.Sigma_ι_comp_PsiSig, Category.assoc]
    exact hkF
  have hL2 : (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
        Work.SSS.coefM p e₀ t) σ ≫
        Work.SSS.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSS.d1 (Work.SSS.xiCan p) s t)) M0
      = c (s+1) • (ModuleCat.Hom.hom (Work.SSS.jF (Work.SSS.xiCan p) s t))
          (((Work.SSS.Fc p).obj s).homologyπ (s+t)
            (((Work.SSS.Fc p).obj s).cyclesMk
              (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)
              ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc)) := by
    have hcomp : (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
          Work.SSS.coefM p e₀ t) σ ≫
          Work.SSS.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSS.d1 (Work.SSS.xiCan p) s t)
        = (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
            Work.SSS.coefM p e₀ t) σ ≫
            Work.SSS.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSS.kF (Work.SSS.xiCan p) s t)
          ≫ Work.SSS.jF (Work.SSS.xiCan p) s t := by
      rw [Work.SSS.d1]
      simp only [Category.assoc]
    rw [hcomp, ModuleCat.hom_comp, LinearMap.comp_apply, hL1, map_zsmul]

  have hjF : (CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.homologyMap (Work.SSS.grFι (Work.SSS.sSingP p) s) (s+t)))
      (((Work.SSS.Fc p).obj s).homologyπ (s+t)
        (((Work.SSS.Fc p).obj s).cyclesMk
          (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ)) (Work.SSS.sigHat σ) rfl z)
          ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc))
      = ∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
           then c s • (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t))
                ((Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom M0)
           else 0) := by
    have hx' : ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
        (((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t))
          (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
            (Work.SSS.sigHat σ) rfl z)) = 0 := by
      rw [Work.SSS.chainMap_comm_apply_elem (Work.SSS.grFι (Work.SSS.sSingP p) s)
        (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z), hvcyc]
      exact map_zero _
    let xfun : Fin (s+2) → (Work.SSS.grF (Work.SSS.Fc p) s).X (s+t) :=
      fun i => ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t))
        (Work.SSS.faceB p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z i)
    have hcyc0 : ∀ i : Fin (s+2), ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t)
        ((ComplexShape.down ℕ).next (s+t))) (xfun i) = 0 :=
      fun i => by
        dsimp only [xfun]
        simp only [Work.SSS.ccHom, Work.SSS.ccHomF]
        exact Work.SSS.grFι_faceB_cycle p hfib s t σ z hz i
    have hsum : ((Work.SSS.grFι (Work.SSS.sSingP p) s).f (s+t))
        (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
          (Work.SSS.sigHat σ) rfl z)
        = ∑ i : Fin (s+2), (-1:ℤ)^(i:ℕ) • xfun i := by
      rw [Work.SSS.faceSum]
      simp only [map_sum, map_zsmul]
      congr 1
    have hx''0 : ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
        (∑ i : Fin (s+2), (-1:ℤ)^(i:ℕ) • xfun i) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_zsmul, hcyc0 i]
      exact zsmul_zero _
    have hbridge := (Work.SSS.homologyMap_cyclesMk (K := (Work.SSS.Fc p).obj s)
      (L := Work.SSS.grF (Work.SSS.Fc p) s) (Work.SSS.grFι (Work.SSS.sSingP p) s) (hj := rfl)
      (Work.SSS.faceSum p hfib s t (Work.SSS.sigmaVert (Work.SSS.sigHat σ))
        (Work.SSS.sigHat σ) rfl z) hvcyc hx').symm
    refine hbridge.trans ?_
    rw [Work.SSS.homologyπ_cyclesMk_eq (hj := rfl) hsum hx' hx''0]
    have hcycF : ∀ i : Fin (s+2),
        (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map
          ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
          (xfun i) = 0 :=
      fun i => by
        show ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
          (xfun i) = 0
        exact hcyc0 i
    have hx''F : (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map
          ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
        (∑ i : Fin (s+2), (-1:ℤ)^(i:ℕ) • xfun i) = 0 := by
      show ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
        (∑ i : Fin (s+2), (-1:ℤ)^(i:ℕ) • xfun i) = 0
      exact hx''0
    have key : ∀ (x : Fin (s+2) → (Work.SSS.grF (Work.SSS.Fc p) s).X (s+t))
        (hx : ∀ j, (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map
          ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
          (x j) = 0)
        (h : (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map
          ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
          (∑ j : Fin (s+2), (-1:ℤ)^(j:ℕ) • x j) = 0),
        (Work.SSS.grF (Work.SSS.Fc p) s).cyclesMk (∑ j : Fin (s+2), (-1:ℤ)^(j:ℕ) • x j)
            ((ComplexShape.down ℕ).next (s+t)) rfl h
          = ∑ j : Fin (s+2), (-1:ℤ)^(j:ℕ) • (Work.SSS.grF (Work.SSS.Fc p) s).cyclesMk (x j)
              ((ComplexShape.down ℕ).next (s+t)) rfl (hx j) := by
      intro x hx h
      apply (Preadditive.mono_iff_injective ((Work.SSS.grF (Work.SSS.Fc p) s).iCycles (s+t))).1 inferInstance
      simp only [map_sum, map_zsmul, HomologicalComplex.i_cyclesMk]
    have hcs := key xfun hcycF hx''F
    refine (congrArg (fun z => (CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.homologyπ (Work.SSS.grF (Work.SSS.Fc p) s) (s+t))) z) hcs).trans ?_
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    congr 1
    by_cases hnd : SimplicialObject.δ (Work.SSS.sSing B) i
        (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
    · rw [dif_pos hnd]
      by_cases hi : i = 0
      · subst hi
        exact Work.SSS.faceB_class_zero p e₀ hfib hc t c hc1 hal s σ z hz hnd
      · exact Work.SSS.faceB_class_nondeg p e₀ hfib hc t c hc1 hal s σ z hz i hi hnd
    · rw [dif_neg hnd]
      have hzero : xfun i = 0 := by
        dsimp only [xfun]
        simp only [Work.SSS.ccHom]
        cases s with
        | zero =>
          rw [SSet.nondegenerate_zero] at hnd
          exact absurd (Set.mem_univ _) hnd
        | succ k =>
          rw [Work.SSS.faceB_grFi_degenerate p hfib k t σ z i hnd]
      have hz0 : (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat ℤ) Ab).map
          ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
          (0 : (Work.SSS.grF (Work.SSS.Fc p) s).X (s+t)) = 0 := by
        show ((Work.SSS.grF (Work.SSS.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
          (0 : (Work.SSS.grF (Work.SSS.Fc p) s).X (s+t)) = 0
        rw [← hzero]
        exact hcyc0 i
      refine (Work.SSS.homologyπ_cyclesMk_eq (hj := rfl) hzero (hcycF i) hz0).trans ?_
      rw [Work.SSS.cyclesMk_zero]
      exact map_zero _
  have hLHS : (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
        Work.SSS.coefM p e₀ t) σ ≫
        Work.SSS.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSS.d1 (Work.SSS.xiCan p) s t)) M0
      = c (s+1) • (∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
           then c s • (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t))
                ((Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom M0)
           else 0)) := by
    rw [hL2]
    congr 1
    rw [Work.SSS.jF_eq_grFi]
    exact hjF
  have hRHS : (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSS.nIndex (Work.SSS.sSing B) (s+1) =>
        Work.SSS.coefM p e₀ t) σ ≫
        ((c (s+1) * c s) • (Work.SSS.faceD' (Work.SSS.sSing B) (Work.SSS.coefM p e₀ t) s ≫
          Work.SSS.PsiSig p e₀ hfib hc t s)))) M0
      = (c (s+1) * c s) • (∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t))
                ((Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom M0)
           else 0)) := by
    rw [CategoryTheory.Preadditive.comp_zsmul]
    rw [ModuleCat.hom_zsmul, Work.SSS.zsmul_hom_apply]
    congr 1
    exact Work.SSS.faceD_PsiSig_gen p e₀ hfib hc t s σ M0
  have hstep1 : (∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
           then c s • (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t))
                ((Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom M0)
           else 0))
      = ∑ i : Fin (s+2), c s • ((-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t))
                ((Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom M0)
           else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : SimplicialObject.δ (Work.SSS.sSing B) i
        (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
    · rw [dif_pos h, dif_pos h, smul_comm]
    · rw [dif_neg h, dif_neg h]
      simp only [zsmul_zero]
  have hstep2 : (∑ i : Fin (s+2), c s • ((-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t))
                ((Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom M0)
           else 0)))
      = c s • (∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSS.sSing B) i
                (Work.SSS.nIndexBase (Work.SSS.sSing B) σ) ∈ (Work.SSS.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSS.mapPhiY (Work.SSS.sSingP p) s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)) (s+t))
                ((Work.SSS.PsiCoef p e₀ hfib hc t s
                  (Work.SSS.nIndexEquiv (Work.SSS.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSS.sSing B) i
                      (Work.SSS.nIndexBase (Work.SSS.sSing B) σ), h⟩)).hom M0)
           else 0)) := by
    exact zsmul_finset_sum Finset.univ (c s) _
  rw [hLHS, hRHS, hstep1, hstep2, smul_smul]

end Work.SSS
