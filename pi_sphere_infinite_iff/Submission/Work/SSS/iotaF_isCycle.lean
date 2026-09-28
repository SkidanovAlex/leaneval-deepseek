import Mathlib
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.iotaF_chainMap
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSS.ez_pair_mem_bdryAlong_of

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

/-! ## The degenerate right degree `q = 0`

The Eilenberg–Zilber shuffle chain of the fundamental `(P+1)`-simplex of `Δ[P+1]` and a *vertex* of
`F` is the single shuffle chain `genP` of the pair
`((Δ[P+1]).map (aHom (zSh0)) (stdIdSimplex), F.map (bHom (zSh0)) τ)`; every `X`-component of its
boundary is a face `(Δ[P+1]).δ j _`, i.e. a `P`-simplex of `Δ[P+1]`, and *every* `P`-simplex of
`Δ[P+1]` lies in the boundary `∂Δ[P+1]` (`SSet.boundary_obj_eq_univ`).  Consequently each summand of
the boundary is carried by `∂T_σ` and is killed by the projection to the σ-piece. -/

/-- **The projection to the σ-piece kills the shuffle chain of a boundary simplex.**
For a `P`-simplex `x` of `Δ[P+1]` lying in `∂Δ[P+1]` and a `P`-simplex `y` of `F`, the class of
`genP x y ∈ C_{P}(Δ[P+1] ⊗ F)` in the σ-piece `C(T_σ)/C(∂T_σ)` is zero: the simplex `(x,y)` maps
into `∂T_σ`. -/
theorem IotaAux.sCCMap_ez_genP_eq_zero {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (x : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) _⦋P⦌)
    (hx : x ∈ (SSet.boundary (P+1)).obj (Opposite.op (SimplexCategory.mk P)))
    (y : F _⦋P⦌) :
    (ConcreteCategory.hom ((pieceπOf f σ).f P))
      ((ConcreteCategory.hom ((sCCMap ez).f P)) (Work.KunnethEZ.genP x y)) = 0 := by
  refine IotaAux.sCCMap_piecepiOf_elt_eq_zero f σ ez (x, y) ?_
  exact ez_pair_mem_bdryAlong_of f P σ ez hez x hx y

/-- **The boundary of the Eilenberg–Zilber shuffle chain dies in the σ-piece** in the degenerate
right degree `q = 0`: for a simplex `σ : Δ[P+1] ⟶ Yf`, a lift `ez` of `pr₁` and a vertex `τ` of `F`,
the boundary of `ezGen (P+1) 0 Δ[P+1] F (stdIdSimplex (P+1)) τ` (pushed into `T_σ` by `ez`) is
killed by the projection `C(T_σ) ⟶ C(T_σ)/C(∂T_σ)`. -/
theorem IotaAux.pieceπOf_sCCMap_d_ezGen_zero {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (τ : F _⦋0⦌) :
    (ConcreteCategory.hom ((pieceπOf f σ).f P))
      ((ConcreteCategory.hom ((sCCMap ez).f P))
        ((ConcreteCategory.hom
            ((((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⊗ F).chainComplex
              Work.KunnethEZ.eZR).d (P+1) P))
          (Work.Cohomology.Crux33.ezGen (P+1) 0
            (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F
            (Work.SSS.stdIdSimplex (P+1)) τ))) = 0 := by
  rw [Work.KunnethEZ.ezGen_zero_single_right]
  rw [Work.KunnethEZ.d_genP (n := P)]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have hx : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).δ j
      ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}).map
        (Quiver.Hom.op (Work.Cohomology.Crux33.aHom (p := P+1) (q := 0)
          (Work.KunnethEZ.zSh0 (P+1)).1 (Work.KunnethEZ.zSh0 (P+1)).2))
        (Work.SSS.stdIdSimplex (P+1))))
      ∈ (SSet.boundary (P+1)).obj (Opposite.op (SimplexCategory.mk P)) := by
    rw [SSet.boundary_obj_eq_univ P (P+1) (by omega)]
    exact Set.mem_univ _
  rw [IotaAux.sCCMap_ez_genP_eq_zero f P σ ez hez _ hx _, zsmul_zero]

/-- **The `q = 0` case of the chain-map property.**  For the abstract σ-piece chain map
`iotaFGen f (P+1) 0 σ ez` (the Eilenberg–Zilber shuffle chain of the fundamental `(P+1)`-simplex and
a vertex, pushed into `T_σ` and projected), the image of the generator of a vertex of `F` is a cycle
of the σ-piece. -/
theorem IotaAux.iotaFGen_zero_d {Xf Yf F : SSet.{0}} (f : Xf ⟶ Yf) (P : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ Yf)
    (ez : ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⊗ F) ⟶ pullAlong f σ)
    (hez : ez ≫ pullback.fst σ f = SemiCartesianMonoidalCategory.fst _ _)
    (τ : F _⦋0⦌) :
    (ConcreteCategory.hom ((pieceAlong f σ).d (P+1) P))
      ((ConcreteCategory.hom (iotaFGen f (P+1) 0 σ ez))
        ((ConcreteCategory.hom (F.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ)) 1)) = 0 := by
  rw [show (ConcreteCategory.hom (iotaFGen f (P+1) 0 σ ez))
        ((ConcreteCategory.hom (F.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ)) 1)
      = (ConcreteCategory.hom ((pieceπOf f σ).f (P+1)))
        ((ConcreteCategory.hom ((sCCMap ez).f (P+1)))
          (Work.Cohomology.Crux33.ezGen (P+1) 0
            (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F
            (Work.SSS.stdIdSimplex (P+1)) τ)) from
    iotaFGen_gen_apply f (P+1) 0 σ ez τ]
  show (ConcreteCategory.hom ((pieceπOf f σ).f (P+1) ≫ (pieceAlong f σ).d (P+1) P))
      ((ConcreteCategory.hom ((sCCMap ez).f (P+1)))
        (Work.Cohomology.Crux33.ezGen (P+1) 0
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F
          (Work.SSS.stdIdSimplex (P+1)) τ)) = 0
  rw [HomologicalComplex.Hom.comm (pieceπOf f σ) (P+1) P]
  show (ConcreteCategory.hom ((pieceπOf f σ).f P))
      ((ConcreteCategory.hom ((sCC (pullAlong f σ)).d (P+1) P))
        ((ConcreteCategory.hom ((sCCMap ez).f (P+1)))
          (Work.Cohomology.Crux33.ezGen (P+1) 0
            (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F
            (Work.SSS.stdIdSimplex (P+1)) τ))) = 0
  show (ConcreteCategory.hom ((pieceπOf f σ).f P))
      ((ConcreteCategory.hom ((sCCMap ez).f (P+1) ≫ (sCC (pullAlong f σ)).d (P+1) P))
        (Work.Cohomology.Crux33.ezGen (P+1) 0
          (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F
          (Work.SSS.stdIdSimplex (P+1)) τ)) = 0
  rw [HomologicalComplex.Hom.comm (sCCMap ez) (P+1) P]
  show (ConcreteCategory.hom ((pieceπOf f σ).f P))
      ((ConcreteCategory.hom ((sCCMap ez).f P))
        ((ConcreteCategory.hom
            ((sCC ((SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⊗ F)).d (P+1) P))
          (Work.Cohomology.Crux33.ezGen (P+1) 0
            (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) F
            (Work.SSS.stdIdSimplex (P+1)) τ))) = 0
  exact IotaAux.pieceπOf_sCCMap_d_ezGen_zero f P σ ez hez τ

end

/-- **`ι_σ τ` is a cycle when `τ` is.**  The Eilenberg–Zilber chain map
`Work.SSS.iotaF p (liftFam p hfib) (liftFam_proj p hfib) P b σ h q` of degree `P`, evaluated on the
generator of a simplex `τ` of the fibre `F_b` (`b` a base point with `sigmaVert σ = b`), is a cycle
of the σ-piece `C(T_σ)/C(∂T_σ)` as soon as `τ` is a cycle of `C(F_b)`.

This is the `∂τ = 0` half of the chain map property `∂ (ι_σ τ) = (-1)^P ι_σ (∂τ)` of `ι_σ`; it is
needed because the induction of `Work.SSS.serreE1PieceIso_iota` applies its induction hypothesis to
the last face `d_lastσ`, which requires the cycle condition there.

Proof route: for `q ≥ 1` this is an immediate corollary of the sorry-free
`Work.SSS.iotaF_chainMap` (apply it with `q-1`, giving `∂(ι_σ τ) = (-1)^P ι_σ(∂τ)`).  For `q = 0`
(and `P ≥ 1`) `ezGen P 0 [id] τ` is the single shuffle chain `genP ([id]) (…)`
(`Work.KunnethEZ.ezGen_zero_single_right`) whose boundary
`Σ_j (-1)^j genP ((Δ[P]).δ_j [id]) (…)` (`Work.KunnethEZ.d_genP`) has every `Δ[P]`-component a face
of `Δ[P]`, hence in `∂Δ[P]`, so each summand is killed by the projection to the σ-piece
(`Work.SSS.IotaAux.sCCMap_piecepiOf_elt_eq_zero`), and `d 0 (next 0) = 0` handles `P = q = 0`. -/
theorem iotaF_isCycle {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.StemsB.IsSerreFibration p) (P : ℕ) (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b) (q : ℕ)
    (τ : Work.SSS.sSing (Work.StemsB.fibre p b) _⦋q⦌)
    (hτ : (Work.SSS.fibreCC p b).d q ((ComplexShape.down ℕ).next q)
        (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) τ).hom 1) = 0) :
    (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).d (P+q)
        ((ComplexShape.down ℕ).next (P+q))
        ((Work.SSS.iotaF p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) P b σ h q)
          (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1)) = 0 := by
  rcases Nat.eq_zero_or_pos q with hq0 | _hqpos
  · -- `q = 0`: all `0`-chains of the fibre are cycles, and we argue by cases on `P`
    subst hq0
    rcases Nat.eq_zero_or_pos P with hP0 | _hPpos
    · -- `P = q = 0`: the differential `d 0 (next 0) = d 0 0` of the σ-piece vanishes
      subst hP0
      simp only [Nat.add_zero]
      rw [show (ComplexShape.down ℕ).next (0 : ℕ) = 0 from ChainComplex.next_nat_zero]
      rw [HomologicalComplex.shape _ 0 0 (by rw [ComplexShape.down_Rel]; omega)]
      simp
    · -- `P = P' + 1`, `q = 0`: the boundary of the shuffle chain of the fundamental simplex and a
      -- vertex is carried by `∂T_σ`
      obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
      rw [show (ComplexShape.down ℕ).next (P' + 1 + 0) = P' from by
        rw [show (P' + 1 + 0 : ℕ) = P' + 1 from rfl]
        exact ChainComplex.next_nat_succ P']
      exact IotaAux.iotaFGen_zero_d (Work.SSS.sSingP p) P' σ
        (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (P'+1) b σ h)
        (Work.SSS.ezSimplex_fst (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) (P'+1) b σ h)
        τ
  · -- `q = q' + 1`: `∂ (ι_σ τ) = (-1)^P ι_σ (∂τ) = 0` by the chain-map property of `ι_σ`
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hchain := Work.SSS.iotaF_chainMap p (Work.SSS.liftFam p hfib)
      (Work.SSS.liftFam_proj p hfib) P b σ h q'
    have h1 := congrArg (fun (g : (Work.SSS.fibreCC p b).X (q'+1) ⟶
        (Work.SSS.pieceAlong (Work.SSS.sSingP p) σ).X (P + q')) =>
          g.hom (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) τ).hom 1)) hchain
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul] at h1
    rw [ChainComplex.next_nat_succ] at hτ
    rw [show (ComplexShape.down ℕ).next (P + (q' + 1)) = P + q' from
      ChainComplex.next_nat_succ (P + q')]
    rw [h1]
    show ((-1 : ℤ) ^ P) • ((ConcreteCategory.hom (Work.SSS.iotaF p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) P b σ h q'))
          ((ConcreteCategory.hom ((Work.SSS.fibreCC p b).d (q'+1) q'))
            (((Work.SSS.sSing (Work.StemsB.fibre p b)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) τ).hom 1))) = 0
    rw [hτ]
    rw [map_zero, zsmul_zero]

end Work.SSS
