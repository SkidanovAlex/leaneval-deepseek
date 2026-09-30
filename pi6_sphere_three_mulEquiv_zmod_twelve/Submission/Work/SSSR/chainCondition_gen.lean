import Mathlib
import Submission.Work.SSSR.serreE1CruxD1
import Submission.Work.SSSR.faceB_grFi_nondeg
import Submission.Work.SSSR.faceB_grFi_degenerate
import Submission.Work.SSSR.faceB_grFi_zero
import Submission.Work.SSSR.iotaF_pieceCastElem
import Submission.Work.SSSR.ezSimplexZero_chain_class
import Submission.Work.SSSR.jF_eq_grFi
import Submission.Work.SSSR.faceD_iota
import Submission.Work.SSSR.nIndexSigma_face
import Submission.Work.SSSR.exists_cycleMk
import Submission.Work.SSSR.cyclesMk_sum
import Submission.Work.SSSR.d_sndToR_iotaTLin
import Submission.Work.SSSR.homologyMap_cyclesMk
import Submission.Work.SSSR.chainCondAux
import Submission.Work.SSSR.kF_psiCoef_gen
import Submission.Work.SSSR.faceB_class_nondeg
import Submission.Work.SSSR.faceB_class_zero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
open HomologicalComplex
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable


/-- `homologyπ` of a cycle class only depends on the underlying element. -/
lemma homologyπ_cyclesMk_eq {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ}
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

NOTE: the module `Submission.Work.SSSR.mapPhiY_iotaF_gen` (lemma `Work.SSSR.mapPhiY_iotaF_gen`, being
written in parallel) is also needed; add its import when it exists.  Do NOT import
`Submission.Work.SSSR.serreE1Main`: it contains a duplicate declaration of this statement (with
`sorry`), which will be removed once this one is proved.

Route (all steps use PROVED lemmas of this workspace): `Sigma_ι_comp_PsiSig` and `d1 = kF ≫ jF`;
`(PsiCoef σ).hom (T zh) = c(s+1) • [ι_σ z]` by `PieceInv` (`pieceInv_of_pieceAlpha`) at `(s+1)`;
`H(mapPhiY R σ) [ι_σ z] = [grFι R f (s+1) w]`, `w := (sCCMap R (sndToR σ)) (iotaTLin σ z)`, by
`mapPhiY_iotaF_gen` and `homologyMap_cyclesMk`; `kF (xiCan p) s t` of that class is the class of
`faceSum` by `kF_eq_of_lift` (`hw` is `rfl` by `grFι_succ`, `hv` is `d_sndToR_iotaTLin`, `hvcyc`
from `hv` via `d_comp_d` and injectivity of `incF (Fc p) s`); then `jF_eq_grFi`,
`homologyMap_cyclesMk`, `dsimp only [faceSum]` with `map_sum`/`map_zsmul`, `cyclesMk_sum` in the
complex `grF (Fc p) s`, and additivity of `homologyπ` give the alternating sum of the classes
`[grFι R f s (faceB ... i)]`; each is identified with `H(mapPhiY R ρ_i)([ιF ρ_i z])` by
`faceB_grFi_nondeg` (`ρ_i := nIndexEquiv (sSing B) s ⟨δ i (nIndexBase (sSing B) σ), hnd⟩`,
`hρi := (nIndexSigma_face σ i hnd).symm`), with `0` by `faceB_grFi_degenerate`, and with
`H(mapPhiY R ρ_0)([ιF ρ_0 z'])` by `faceB_grFi_zero` + `ezSimplexZero_chain_class` +
`iotaF_pieceCastElem`, where `z'` comes from `exists_cycleMk` applied to
`(triv_{σ_0(v_0)}).inv (T_b zh)`.
On the other side `faceD_iota` + `Preadditive.sum_comp` + `Sigma_ι_comp_PsiSig` + `PieceInv` at `s`
give `(c(s+1)*c s) • Σ_i (-1)^i (if hnd then c s • H(mapPhiY R ρ_i)([ιF ρ_i z_i]) else 0)`, and
`c(s+1) • X = (c(s+1)*c s) • (c s • X)` since `c s * c s = 1` (from `hc1`). -/

theorem chainCondition_gen (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) (c : ℕ → ℤ)
    (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1) (hal : Work.SSSR.PieceAlpha (R := R) p hfib c)
    (s : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1))
    (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).d t
        ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
        Work.SSSR.coefM p e₀ t) σ ≫
        Work.SSSR.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSSR.d1 (Work.SSSR.xiCan (R := R) p) s t))
      ((Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
        ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
          ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz)))
    = (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
        Work.SSSR.coefM p e₀ t) σ ≫
        ((c (s+1) * c s) • (Work.SSSR.faceD' (Work.SSSR.sSing B) (Work.SSSR.coefM p e₀ t) s ≫
          Work.SSSR.PsiSig p e₀ hfib hc t s))))
      ((Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
        ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
          ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz))) := by
  set M0 := (Work.SSSR.triv p e₀ hfib hc t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom
      ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ t
        ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
          ((ComplexShape.down ℕ).next t) rfl hz)) with hM0
  have hv : (ModuleCat.Hom.hom (((Work.SSSR.Fc p).obj (s+1)).d ((s+1)+t) (s+t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
        (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z))
      = (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.Fc p) s).f (s+t)))
        (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z) :=
    Work.SSSR.d_sndToR_iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) σ rfl z hz
  have hvcyc : (ModuleCat.Hom.hom (((Work.SSSR.Fc p).obj s).d (s+t) ((ComplexShape.down ℕ).next (s+t))))
      (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z) = 0 := by
    haveI : Mono (Work.SSSR.incF (Work.SSSR.Fc (R := R) p) s) := (Work.SSSR.xiCan p).mono s
    refine (ModuleCat.mono_iff_injective ((Work.SSSR.incF (Work.SSSR.Fc p) s).f
      ((ComplexShape.down ℕ).next (s+t)))).mp inferInstance ?_
    rw [map_zero]
    rw [← Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.incF (Work.SSSR.Fc p) s)
      (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)]
    rw [← hv]
    have h2 := congrArg (fun (g : ((Work.SSSR.Fc p).obj (s+1)).X ((s+1)+t) ⟶
        ((Work.SSSR.Fc p).obj (s+1)).X ((ComplexShape.down ℕ).next (s+t)))
      => (ModuleCat.Hom.hom g)
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f ((s+1)+t)))
            (Work.SSSR.iotaTLin p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)))
      (HomologicalComplex.d_comp_d ((Work.SSSR.Fc p).obj (s+1)) ((s+1)+t) (s+t) ((ComplexShape.down ℕ).next (s+t)))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h2
  have hkF := Work.SSSR.kF_psiCoef_gen p e₀ hfib hc t c hc1 hal s σ z hz hvcyc
  have hL1 : (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
        Work.SSSR.coefM p e₀ t) σ ≫
        Work.SSSR.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSSR.kF (Work.SSSR.xiCan p) s t)) M0
      = c (s+1) • ((Work.SSSR.Fc p).obj s).homologyπ (s+t)
          (((Work.SSSR.Fc p).obj s).cyclesMk
            (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)
            ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc) := by
    rw [← Category.assoc, Work.SSSR.Sigma_ι_comp_PsiSig, Category.assoc]
    exact hkF
  have hL2 : (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
        Work.SSSR.coefM p e₀ t) σ ≫
        Work.SSSR.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSSR.d1 (Work.SSSR.xiCan p) s t)) M0
      = c (s+1) • (ModuleCat.Hom.hom (Work.SSSR.jF (Work.SSSR.xiCan p) s t))
          (((Work.SSSR.Fc p).obj s).homologyπ (s+t)
            (((Work.SSSR.Fc p).obj s).cyclesMk
              (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)
              ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc)) := by
    have hcomp : (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
          Work.SSSR.coefM p e₀ t) σ ≫
          Work.SSSR.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSSR.d1 (Work.SSSR.xiCan (R := R) p) s t)
        = (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
            Work.SSSR.coefM p e₀ t) σ ≫
            Work.SSSR.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSSR.kF (Work.SSSR.xiCan p) s t)
          ≫ Work.SSSR.jF (Work.SSSR.xiCan p) s t := by
      rw [Work.SSSR.d1]
      simp only [Category.assoc]
    rw [hcomp, ModuleCat.hom_comp, LinearMap.comp_apply, hL1, map_zsmul]

  have hjF : (CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.homologyMap (Work.SSSR.grFι R (Work.SSSR.sSingP p) s) (s+t)))
      (((Work.SSSR.Fc p).obj s).homologyπ (s+t)
        (((Work.SSSR.Fc p).obj s).cyclesMk
          (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ)) (Work.SSSR.sigHat σ) rfl z)
          ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc))
      = ∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
           then c s • (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t))
                ((Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom M0)
           else 0) := by
    have hx' : ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
        (((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t))
          (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
            (Work.SSSR.sigHat σ) rfl z)) = 0 := by
      rw [Work.SSSR.chainMap_comm_apply_elem (Work.SSSR.grFι R (Work.SSSR.sSingP p) s)
        (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z), hvcyc]
      exact map_zero _
    let xfun : Fin (s+2) → (Work.SSSR.grF (Work.SSSR.Fc p) s).X (s+t) :=
      fun i => ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t))
        (Work.SSSR.faceB p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z i)
    have hcyc0 : ∀ i : Fin (s+2), ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t)
        ((ComplexShape.down ℕ).next (s+t))) (xfun i) = 0 :=
      fun i => by
        dsimp only [xfun]
        simp only [Work.SSSR.ccHom, Work.SSSR.ccHomF]
        exact Work.SSSR.grFι_faceB_cycle p hfib s t σ z hz i
    have hsum : ((Work.SSSR.grFι R (Work.SSSR.sSingP p) s).f (s+t))
        (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
          (Work.SSSR.sigHat σ) rfl z)
        = ∑ i : Fin (s+2), (-1:ℤ)^(i:ℕ) • xfun i := by
      rw [Work.SSSR.faceSum]
      simp only [map_sum, map_zsmul]
      congr 1
    have hx''0 : ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
        (∑ i : Fin (s+2), (-1:ℤ)^(i:ℕ) • xfun i) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_zsmul, hcyc0 i]
      exact zsmul_zero _
    have hbridge := (Work.SSSR.homologyMap_cyclesMk (K := (Work.SSSR.Fc p).obj s)
      (L := Work.SSSR.grF (Work.SSSR.Fc p) s) (Work.SSSR.grFι R (Work.SSSR.sSingP p) s) (hj := rfl)
      (Work.SSSR.faceSum p hfib s t (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))
        (Work.SSSR.sigHat σ) rfl z) hvcyc hx').symm
    refine hbridge.trans ?_
    rw [Work.SSSR.homologyπ_cyclesMk_eq (hj := rfl) hsum hx' hx''0]
    have hcycF : ∀ i : Fin (s+2),
        (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat R) Ab).map
          ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
          (xfun i) = 0 :=
      fun i => by
        show ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
          (xfun i) = 0
        exact hcyc0 i
    have hx''F : (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat R) Ab).map
          ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
        (∑ i : Fin (s+2), (-1:ℤ)^(i:ℕ) • xfun i) = 0 := by
      show ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
        (∑ i : Fin (s+2), (-1:ℤ)^(i:ℕ) • xfun i) = 0
      exact hx''0
    have key : ∀ (x : Fin (s+2) → (Work.SSSR.grF (Work.SSSR.Fc p) s).X (s+t))
        (hx : ∀ j, (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat R) Ab).map
          ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
          (x j) = 0)
        (h : (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat R) Ab).map
          ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
          (∑ j : Fin (s+2), (-1:ℤ)^(j:ℕ) • x j) = 0),
        (Work.SSSR.grF (Work.SSSR.Fc p) s).cyclesMk (∑ j : Fin (s+2), (-1:ℤ)^(j:ℕ) • x j)
            ((ComplexShape.down ℕ).next (s+t)) rfl h
          = ∑ j : Fin (s+2), (-1:ℤ)^(j:ℕ) • (Work.SSSR.grF (Work.SSSR.Fc p) s).cyclesMk (x j)
              ((ComplexShape.down ℕ).next (s+t)) rfl (hx j) := by
      intro x hx h
      apply (Preadditive.mono_iff_injective ((Work.SSSR.grF (Work.SSSR.Fc p) s).iCycles (s+t))).1 inferInstance
      simp only [map_sum, map_zsmul, HomologicalComplex.i_cyclesMk]
    have hcs := key xfun hcycF hx''F
    refine (congrArg (fun z => (CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.homologyπ (Work.SSSR.grF (Work.SSSR.Fc p) s) (s+t))) z) hcs).trans ?_
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    congr 1
    by_cases hnd : SimplicialObject.δ (Work.SSSR.sSing B) i
        (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
    · rw [dif_pos hnd]
      by_cases hi : i = 0
      · subst hi
        exact Work.SSSR.faceB_class_zero p e₀ hfib hc t c hc1 hal s σ z hz hnd
      · exact Work.SSSR.faceB_class_nondeg p e₀ hfib hc t c hc1 hal s σ z hz i hi hnd
    · rw [dif_neg hnd]
      have hzero : xfun i = 0 := by
        dsimp only [xfun]
        simp only [Work.SSSR.ccHom]
        cases s with
        | zero =>
          rw [SSet.nondegenerate_zero] at hnd
          exact absurd (Set.mem_univ _) hnd
        | succ k =>
          rw [Work.SSSR.faceB_grFi_degenerate p hfib k t σ z i hnd]
      have hz0 : (CategoryTheory.ConcreteCategory.hom ((forget₂ (ModuleCat R) Ab).map
          ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))))
          (0 : (Work.SSSR.grF (Work.SSSR.Fc p) s).X (s+t)) = 0 := by
        show ((Work.SSSR.grF (Work.SSSR.Fc p) s).d (s+t) ((ComplexShape.down ℕ).next (s+t)))
          (0 : (Work.SSSR.grF (Work.SSSR.Fc p) s).X (s+t)) = 0
        rw [← hzero]
        exact hcyc0 i
      refine (Work.SSSR.homologyπ_cyclesMk_eq (hj := rfl) hzero (hcycF i) hz0).trans ?_
      rw [Work.SSSR.cyclesMk_zero]
      exact map_zero _
  have hLHS : (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
        Work.SSSR.coefM p e₀ t) σ ≫
        Work.SSSR.PsiSig p e₀ hfib hc t (s+1) ≫ Work.SSSR.d1 (Work.SSSR.xiCan p) s t)) M0
      = c (s+1) • (∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
           then c s • (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t))
                ((Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom M0)
           else 0)) := by
    rw [hL2]
    congr 1
    rw [Work.SSSR.jF_eq_grFi]
    exact hjF
  have hRHS : (ModuleCat.Hom.hom (Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1) =>
        Work.SSSR.coefM p e₀ t) σ ≫
        ((c (s+1) * c s) • (Work.SSSR.faceD' (Work.SSSR.sSing B) (Work.SSSR.coefM p e₀ t) s ≫
          Work.SSSR.PsiSig p e₀ hfib hc t s)))) M0
      = (c (s+1) * c s) • (∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t))
                ((Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom M0)
           else 0)) := by
    rw [CategoryTheory.Preadditive.comp_zsmul]
    rw [ModuleCat.hom_zsmul, Work.SSSR.zsmul_hom_apply]
    congr 1
    exact Work.SSSR.faceD_PsiSig_gen p e₀ hfib hc t s σ M0
  have hstep1 : (∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
           then c s • (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t))
                ((Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom M0)
           else 0))
      = ∑ i : Fin (s+2), c s • ((-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t))
                ((Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom M0)
           else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : SimplicialObject.δ (Work.SSSR.sSing B) i
        (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
    · rw [dif_pos h, dif_pos h, smul_comm]
    · rw [dif_neg h, dif_neg h]
      simp only [zsmul_zero]
  have hstep2 : (∑ i : Fin (s+2), c s • ((-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t))
                ((Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom M0)
           else 0)))
      = c s • (∑ i : Fin (s+2), (-1 : ℤ)^(i:ℕ) •
          (if h : SimplicialObject.δ (Work.SSSR.sSing B) i
                (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ) ∈ (Work.SSSR.sSing B).nonDegenerate s
           then (HomologicalComplex.homologyMap (Work.SSSR.mapPhiY R (Work.SSSR.sSingP p) s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)) (s+t))
                ((Work.SSSR.PsiCoef p e₀ hfib hc t s
                  (Work.SSSR.nIndexEquiv (Work.SSSR.sSing B) s
                    ⟨SimplicialObject.δ (Work.SSSR.sSing B) i
                      (Work.SSSR.nIndexBase (Work.SSSR.sSing B) σ), h⟩)).hom M0)
           else 0)) := by
    exact zsmul_finset_sum Finset.univ (c s) _
  rw [hLHS, hRHS, hstep1, hstep2, smul_smul]

end Work.SSSR
