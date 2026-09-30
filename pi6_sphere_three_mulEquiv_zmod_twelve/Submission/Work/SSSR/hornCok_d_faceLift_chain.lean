import Mathlib
import Submission.Work.SSSR.ezGen_snd_sum_zero
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.iotaF_chainMap
import Submission.Work.SSSR.ezLinSnd_boundary_succ
import Submission.Work.SSSR.ezLinSnd_map_fst
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.iotaTBdryHorn
import Submission.Work.SSSR.lastFaceDefs
import Submission.Work.SSSR.serreE1PieceDefs
import Submission.Work.SSSR.piszDefs
import Submission.Work.SSSR.hornCok_d_faceLift
import Submission.Work.SSSR.serreE1StepAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000


/-- The standard simplex `Δ[n]`, as a simplicial set in `SSet.{0}`. -/
abbrev hcdflStd (n : ℕ) : SSet.{0} := SSet.stdSimplex.obj (SimplexCategory.mk n)

/-- The two degree transports along mutually inverse equalities cancel. -/
lemma hcdfl_castElem_symm {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j) (x : K.X i) :
    castElem K h.symm (castElem K h x) = x := by
  subst h
  simp [castElem]

/-- **The differential at a propositionally equal target degree.** -/
lemma hcdfl_d_eq_castElem (K : ChainComplex (ModuleCat R) ℕ) {i j j' : ℕ} (h : j' = j)
    (x : K.X i) : K.d i j x = castElem K h (K.d i j' x) := by
  subst h
  simp [castElem]

/-- `castElem_eqToHom_apply` with the `congrArg` argument spelled as a lambda. -/
lemma hcdfl_eqToHom_apply {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j) (x : K.X i) :
    (eqToHom (congrArg (fun k => K.X k) h)).hom x = castElem K h x :=
  castElem_eqToHom_apply h x

/-- `castElem` cancellation for two independent proofs of mutually inverse equalities. -/
lemma hcdfl_castElem_cancel {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ} (h : i = j) (h' : j = i)
    (x : K.X i) : castElem K h' (castElem K h x) = x := by
  rw [show h' = h.symm from Subsingleton.elim _ _]
  exact hcdfl_castElem_symm h x

/-! ## The linearised shuffle chain on an arbitrary chain -/

/-- The value of the linearised Eilenberg–Zilber shuffle chain on an arbitrary chain, expanded in
the generators of the chain complex of the second variable. -/
lemma ezLinSnd_chain_eq_sum (n q : ℕ) (X Y : SSet.{0}) (σ : X _⦋n⦌)
    (z : (Y.chainComplex (ezR R)).X q) :
    (ezLinSnd n q X Y σ).hom z
      = ∑ τ ∈ (Work.SSSR.Cohomology.Crux33.coords Y q z).support,
          (Work.SSSR.Cohomology.Crux33.coords Y q z τ) •
            Work.SSSR.Cohomology.Crux33.ezGen n q X Y σ τ := by
  conv_lhs => rw [Work.SSSR.KunnethEZ.chain_eq_sum_gen Y q z]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [map_smul, ezLinSnd_apply]

/-! ## The boundary of the linearised shuffle chain at the degrees used by the main theorem -/

/-- **The boundary formula in fibre degree `0`**, as a morphism out of the `0`-chains. -/
lemma hcdfl_bd_zero_mor (P : ℕ) (X Y : SSet.{0}) (σ : X _⦋P+1⦌) :
    ezLinSnd (P+1) 0 X Y σ ≫ ((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+0) (P+0)
      = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • ezLinSnd P 0 X Y (X.δ i σ) := by
  apply SSet.chainComplex_hom_ext (X := Y) (R := (ezR R)) (n := 0)
  intro τ
  have hL : Y.ιChainComplex (R := (ezR R)) τ ≫
        (ezLinSnd (P+1) 0 X Y σ ≫ ((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+0) (P+0))
      = eltHom ((((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+0) (P+0)).hom
          (Work.SSSR.Cohomology.Crux33.ezGen (P+1) 0 X Y σ τ)) := by
    rw [← Category.assoc, ezLinSnd_ι_eltHomS, eltHom_comp]
  have hR : Y.ιChainComplex (R := (ezR R)) τ ≫
        (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • ezLinSnd P 0 X Y (X.δ i σ))
      = eltHom ((((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+0) (P+0)).hom
          (Work.SSSR.Cohomology.Crux33.ezGen (P+1) 0 X Y σ τ)) := by
    rw [Preadditive.comp_sum]
    have h1 : (∑ i : Fin (P+2), Y.ιChainComplex (R := (ezR R)) τ ≫
          ((-1:ℤ)^(i:ℕ) • ezLinSnd P 0 X Y (X.δ i σ)))
        = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
            eltHom (Work.SSSR.Cohomology.Crux33.ezGen P 0 X Y (X.δ i σ) τ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Preadditive.comp_zsmul, ezLinSnd_ι_eltHomS]
    rw [h1, eltHom_sum, ← ezGen_bdry_faces_zero P σ τ]
  rw [hL, hR]

/-- **The boundary formula in fibre degree `0`**, elementwise. -/
lemma hcdfl_bd_zero (P : ℕ) (X Y : SSet.{0}) (σ : X _⦋P+1⦌)
    (z : (Y.chainComplex (ezR R)).X 0) :
    (((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+0) (P+0)).hom ((ezLinSnd (P+1) 0 X Y σ).hom z)
      = ∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • ((ezLinSnd P 0 X Y (X.δ i σ)).hom z) := by
  have h := congrArg (fun (g : (Y.chainComplex (ezR R)).X 0 ⟶
      ((X ⊗ Y).chainComplex (ezR R)).X (P+0)) => g.hom z) (hcdfl_bd_zero_mor P X Y σ)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply] at h
  exact h

/-- **The boundary formula in fibre degree `q+1`**, elementwise and at the degree
`P+(q+1)` of the main theorem. -/
lemma hcdfl_bd_succ (P q : ℕ) (X Y : SSet.{0}) (σ : X _⦋P+1⦌)
    (z : (Y.chainComplex (ezR R)).X (q+1)) :
    (((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+(q+1)) (P+(q+1))).hom
        ((ezLinSnd (P+1) (q+1) X Y σ).hom z)
      = (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) • ((ezLinSnd P (q+1) X Y (X.δ i σ)).hom z))
        + (-1:ℤ)^(P+1) •
            ((eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (ezR R)).X k)
              (by omega : (P+1)+q = P+(q+1)))).hom
                ((ezLinSnd (P+1) q X Y σ).hom
                  (((Y.chainComplex (ezR R)).d (q+1) q).hom z))) := by
  have h2 : P + (q+1) = (P+1) + q := by omega
  have hh : (P+1) + q = P + (q+1) := h2.symm
  have hbd : (((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+(q+1)) ((P+1)+q)).hom
        ((ezLinSnd (P+1) (q+1) X Y σ).hom z)
      = (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
            ((eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (ezR R)).X k)
              (by omega : P+(q+1) = (P+1)+q))).hom
                ((ezLinSnd P (q+1) X Y (X.δ i σ)).hom z)))
        + (-1:ℤ)^(P+1) •
            ((ezLinSnd (P+1) q X Y σ).hom (((Y.chainComplex (ezR R)).d (q+1) q).hom z)) := by
    have h := congrArg (fun (g : (Y.chainComplex (ezR R)).X (q+1) ⟶
        ((X ⊗ Y).chainComplex (ezR R)).X ((P+1)+q)) => g.hom z) (ezLinSnd_boundary_succ P q X Y σ)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply] at h
    exact h
  have hd : (((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+(q+1)) (P+(q+1))).hom
        ((ezLinSnd (P+1) (q+1) X Y σ).hom z)
      = ((eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (ezR R)).X k) hh)).hom
          ((((X ⊗ Y).chainComplex (ezR R)).d ((P+1)+(q+1)) ((P+1)+q)).hom
            ((ezLinSnd (P+1) (q+1) X Y σ).hom z))) := by
    rw [hcdfl_d_eq_castElem ((X ⊗ Y).chainComplex (ezR R)) (i := (P+1)+(q+1)) hh]
    rw [castElem_eqToHom_apply]
  have hkey : ∀ v : ((X ⊗ Y).chainComplex (ezR R)).X (P+(q+1)),
      (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (ezR R)).X k)
          (by omega : (P+1)+q = P+(q+1)))).hom
        ((eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (ezR R)).X k)
          (by omega : P+(q+1) = (P+1)+q))).hom v) = v := by
    intro v
    rw [hcdfl_eqToHom_apply h2 v]
    rw [hcdfl_eqToHom_apply hh (castElem ((X ⊗ Y).chainComplex (ezR R)) h2 v)]
    rw [hcdfl_castElem_cancel h2 hh v]
  rw [hd, hbd]
  simp only [map_add, map_sum, map_zsmul]
  have hsum : (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
        (eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (ezR R)).X k)
          (by omega : (P+1)+q = P+(q+1)))).hom
          ((eqToHom (congrArg (fun k => ((X ⊗ Y).chainComplex (ezR R)).X k)
            (by omega : P+(q+1) = (P+1)+q))).hom
              ((ezLinSnd P (q+1) X Y (X.δ i σ)).hom z)))
      = (∑ i : Fin (P+2), (-1:ℤ)^(i:ℕ) •
          ((ezLinSnd P (q+1) X Y (X.δ i σ)).hom z)) :=
    Finset.sum_congr rfl (fun i _ => by rw [hkey])
  rw [hsum]

/-! ## The horn quotient of the individual face terms, for an arbitrary chain -/

/-- **Every non-last face term of the Eilenberg–Zilber boundary dies in the horn quotient**, for an
arbitrary chain `z` of the fibre. -/
lemma hcdfl_face {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (P t : ℕ) (b : B)
    (σ : hcdflStd (P+1) ⟶ sSing B)
    (ez : (hcdflStd (P+1) ⊗ sSing (Work.SSSR.StemsB.fibre p b)) ⟶ pullAlong (sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (z : (fibreCC p b).X t) (i : Fin (P+2)) (hi : i ≠ Fin.last (P+1)) :
    (hornCokπ (sSingP p) σ).f (P+t) ((sCCMap R ez).f (P+t)
      ((ezLinSnd P t (hcdflStd (P+1)) (sSing (Work.SSSR.StemsB.fibre p b))
        ((hcdflStd (P+1)).δ i (stdIdSimplex (P+1)))).hom z)) = 0 := by
  rw [ezLinSnd_chain_eq_sum P t (hcdflStd (P+1)) (sSing (Work.SSSR.StemsB.fibre p b))
    ((hcdflStd (P+1)).δ i (stdIdSimplex (P+1))) z]
  simp only [map_sum, map_smul]
  refine Finset.sum_eq_zero (fun τ _ => ?_)
  rw [hornCokpi_ezGen_face p P t b σ ez hez τ i hi, smul_zero]

/-- **The last face term of the Eilenberg–Zilber boundary is the push-forward along the last-face
pasting map**, for an arbitrary chain `z` of the fibre. -/
lemma hcdfl_last {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (P t : ℕ) (b : B)
    (σ : hcdflStd (P+1) ⟶ sSing B)
    (ez : (hcdflStd (P+1) ⊗ sSing (Work.SSSR.StemsB.fibre p b)) ⟶ pullAlong (sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (z : (fibreCC p b).X t) :
    (hornCokπ (sSingP p) σ).f (P+t) ((sCCMap R ez).f (P+t)
        ((ezLinSnd P t (hcdflStd (P+1)) (sSing (Work.SSSR.StemsB.fibre p b))
          ((hcdflStd (P+1)).δ (Fin.last (P+1)) (stdIdSimplex (P+1)))).hom z))
      = (hornCokπ (sSingP p) σ).f (P+t) ((TIncl (sSingP p) σ).f (P+t)
          ((lastFaceChain (sSingP p) P σ).f (P+t)
            ((sCCMap R (faceLift (sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)
              ((ezLinSnd P t (hcdflStd P) (sSing (Work.SSSR.StemsB.fibre p b))
                (stdIdSimplex P)).hom z)))) := by
  have hcomp : ((SSet.stdSimplex.δ (n := P) (Fin.last (P+1))) ⊗ₘ
        𝟙 (sSing (Work.SSSR.StemsB.fibre p b))) ≫ ez
      = faceLift (sSingP p) σ ez hez (Fin.last (P+1)) ≫
        pullFaceIncl (sSingP p) σ (Fin.last (P+1)) :=
    (faceLift_pullFaceIncl (sSingP p) σ ez hez (Fin.last (P+1))).symm
  have hgen : (sCCMap R ((SSet.stdSimplex.δ (n := P) (Fin.last (P+1))) ⊗ₘ
        𝟙 (sSing (Work.SSSR.StemsB.fibre p b)))).f (P+t)
        ((ezLinSnd P t (hcdflStd P) (sSing (Work.SSSR.StemsB.fibre p b))
          (stdIdSimplex P)).hom z)
      = (ezLinSnd P t (hcdflStd (P+1)) (sSing (Work.SSSR.StemsB.fibre p b))
          ((hcdflStd (P+1)).δ (Fin.last (P+1)) (stdIdSimplex (P+1)))).hom z := by
    have h := ezLinSnd_map_fst P t (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)))
      (stdIdSimplex P) z
    rw [← delta_stdIdSimplex_eq P (Fin.last (P+1))] at h
    exact h
  have hchain : (sCCMap R (faceLift (sSingP p) σ ez hez (Fin.last (P+1)) ≫
        pullFaceIncl (sSingP p) σ (Fin.last (P+1)))).f (P+t)
        ((ezLinSnd P t (hcdflStd P) (sSing (Work.SSSR.StemsB.fibre p b))
          (stdIdSimplex P)).hom z)
      = (TIncl (sSingP p) σ).f (P+t) ((lastFaceChain (sSingP p) P σ).f (P+t)
          ((sCCMap R (faceLift (sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)
            ((ezLinSnd P t (hcdflStd P) (sSing (Work.SSSR.StemsB.fibre p b))
              (stdIdSimplex P)).hom z))) := by
    have h1 : sCCMap R (pullFaceIncl (sSingP p) σ (Fin.last (P+1)))
        = lastFaceChain (sSingP p) P σ ≫ TIncl (sSingP p) σ :=
      (lastFaceChain_comp_TIncl (sSingP p) P σ).symm
    rw [sCCMap_comp', h1]
    rw [← chainMap_comp_apply (sCCMap R (faceLift (sSingP p) σ ez hez (Fin.last (P+1))))
      (lastFaceChain (sSingP p) P σ ≫ TIncl (sSingP p) σ)]
    rw [← chainMap_comp_apply (lastFaceChain (sSingP p) P σ) (TIncl (sSingP p) σ)]
  rw [← hgen, sCCMap_comp_apply, hcomp, hchain]

/-- **The boundary of a lifted Eilenberg–Zilber chain modulo the horn, for an arbitrary CHAIN.**

For a Serre fibration `p`, a simplex `σ : Δ[P+1] ⟶ Sing B`, a lift
`ez : Δ[P+1] ⊗ F ⟶ T_σ` of `pr₁ ≫ σ` and a CYCLE chain `z` of the fibre `F = Sing (p⁻¹b)`, the class
in `C(T_σ)/C(Λ)` (Λ = `pieceHorn`) of `∂(ez_*(EZ(P+1,t,[id],z)))` is `(-1)^(P+1)` times the class of
the push-forward along `TIncl ≫ lastFaceChain` of the EZ chain `EZ(P,t,[id],z)` pushed along the
*face restriction* `faceLift` of `ez`.

Route (all pieces already proved, except the last rewriting step of `ez_* ∘ (δ ⊗ 𝟙)_*`):
1. `ez_* ∘ ∂ = ∂ ∘ ez_*` (naturality of the chain map `sCCMap R ez`), so it suffices to expand
   `∂(ezLinSnd (P+1) t Δ[P+1] F (stdIdSimplex (P+1)) z)` by
   `Work.SSSR.ezLinSnd_boundary_succ` (PROVED, module `Submission.Work.SSSR.ezLinSnd_boundary_succ`);
   its `(-1)^(P+1) • (d_F ≫ ezLinSnd (P+1) (t-1) ...)` term vanishes on `z` by `hz`
   (for `t = 0` use `Work.SSSR.ezLinSnd_boundary_zero` instead, where there is no such term).
2. For `i ≠ Fin.last (P+1)`: the `i`-th face term
   `(sCCMap R ez).f ((P+1)+t) (ezLinSnd P t Δ[P+1] F (δ i (stdIdSimplex (P+1))) z)` has, for each of
   its `genP R`-summands, first projection `Δ[P+1].map a (δ i (stdIdSimplex (P+1)))`, which factors
   through `δ i` and hence lies in `hornSimp (P+1)`; so the term lies in `C(Λ)` and dies under
   `cokernel.π (sCCMap R (pieceHorn).ι)` (use `Work.SSSR.sCCMap_pieceHorn_ι_eq` and
   `CategoryTheory.Limits.cokernel.condition`, as in `Work.SSSR.hornCokπ_rawX_eq_zero` of
   `iotaTBdryHorn.lean`).
3. For `i = Fin.last (P+1)`: rewrite the face term as the push-forward of the `P`-dim chain along
   the face inclusion using `delta_stdIdSimplex_eq` (in `piszEZ.lean`) and the naturality of
   `ezLinSnd` in its first variable, `Work.SSSR.ezLinSnd_map_fst` (PROVED, module
   `Submission.Work.SSSR.ezLinSnd_map_fst`), and then use `Work.SSSR.faceLift_pullFaceIncl` together
   with `Work.SSSR.lastFaceChain_comp_TIncl`. -/
theorem hornCok_d_faceLift_chain {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (P t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (ez : (((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) ⟶ Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
    (hez : ez ≫ pullback.fst σ (Work.SSSR.sSingP p) = SemiCartesianMonoidalCategory.fst _ _)
    (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t
        ((ComplexShape.down ℕ).next t))) z = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f (P+t)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).d
            ((P+1)+t) (P+t)))
          ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R ez).f ((P+1)+t)))
            (Work.SSSR.ezLinSnd (P+1) t
              (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0})
              (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex (P+1)) z)))
      = (-1 : ℤ)^(P+1) •
          (ModuleCat.Hom.hom ((Work.SSSR.hornCokπ (Work.SSSR.sSingP p) σ).f (P+t)))
            ((ModuleCat.Hom.hom ((Work.SSSR.TIncl (Work.SSSR.sSingP p) σ).f (P+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.lastFaceChain (Work.SSSR.sSingP p) P σ).f (P+t)))
                ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R
                    (Work.SSSR.faceLift (Work.SSSR.sSingP p) σ ez hez (Fin.last (P+1)))).f (P+t)))
                  (Work.SSSR.ezLinSnd P t
                    (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0})
                    (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex P) z)))) := by
  rw [chainMap_comm_apply_elem (sCCMap R ez)]
  rcases t with _ | q
  · -- ## fibre degree `0`
    rw [hcdfl_bd_zero P (hcdflStd (P+1)) (sSing (Work.SSSR.StemsB.fibre p b))
      (stdIdSimplex (P+1)) z]
    simp only [map_sum, map_zsmul]
    rw [Finset.sum_eq_single (Fin.last (P+1))]
    · rw [Fin.val_last]
      congr 1
      exact hcdfl_last p P 0 b σ ez hez z
    · intro i _ hi
      rw [hcdfl_face p P 0 b σ ez hez z i hi, zsmul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · -- ## fibre degree `q+1`
    have hzq : (((sSing (Work.SSSR.StemsB.fibre p b)).chainComplex (ezR R)).d (q+1) q).hom z = 0 := by
      have h := hz
      rw [ChainComplex.next_nat_succ] at h
      exact h
    rw [hcdfl_bd_succ P q (hcdflStd (P+1)) (sSing (Work.SSSR.StemsB.fibre p b))
      (stdIdSimplex (P+1)) z]
    have hY : ((eqToHom (congrArg (fun k =>
          ((hcdflStd (P+1) ⊗ sSing (Work.SSSR.StemsB.fibre p b)).chainComplex (ezR R)).X k)
          (by omega : (P+1)+q = P+(q+1)))).hom
        ((ezLinSnd (P+1) q (hcdflStd (P+1)) (sSing (Work.SSSR.StemsB.fibre p b))
          (stdIdSimplex (P+1))).hom
          ((((sSing (Work.SSSR.StemsB.fibre p b)).chainComplex (ezR R)).d (q+1) q).hom z))) = 0 := by
      rw [hzq]
      simp
    rw [hY, zsmul_zero, add_zero]
    simp only [map_sum, map_zsmul]
    rw [Finset.sum_eq_single (Fin.last (P+1))]
    · rw [Fin.val_last]
      congr 1
      exact hcdfl_last p P (q+1) b σ ez hez z
    · intro i _ hi
      rw [hcdfl_face p P (q+1) b σ ez hez z i hi, zsmul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem



end Work.SSSR
