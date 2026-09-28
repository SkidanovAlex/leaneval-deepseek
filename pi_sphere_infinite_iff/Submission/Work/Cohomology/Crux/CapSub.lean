import Mathlib
import Submission.Work.Cohomology.CapProduct
import Submission.Work.Cohomology.cap_natural
import Submission.Work.Cohomology.cap_d
import Submission.Work.Cohomology.coprod_shortExact
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Cohomology.RelMVDefs

/-!
# The cap product on the chains of a simplicial subcomplex

For a simplicial set `Y`, a subfunctor `S : Y.Subcomplex` and a cochain `α` on `Y` of degree `n`,
the map `σ ↦ α(σ_front) • σ_back` sends a simplex of `S` to a chain of `S`: the back face of a
simplex of `S` is again a simplex of `S` (subfunctors are closed under all simplicial
operations).  Hence the cap product restricts to the chains of `S`, giving a linear map

  `capSub S n m α : C_{n+m}(S) ⟶ C_m(S)`,

compatible with the inclusion `C_*(S) ⟶ C_*(Y)` (`capSub_comp_incl`) and satisfying the boundary
formula of `Work.Cohomology.cap_d` when `α` is a cocycle (`capSub_comm_d`, `capSub_boundary`).

This is the raw material for the "cap product with a relative cocycle" on the Mayer–Vietoris
complexes of `Submission/Work/Cohomology/RelMVDefs.lean`: the small chains of `(U,V)` lying in a
set `B` are the chains of the subfunctor `smallInSubcomplex U V B`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {Y : SSet}

/-- The inclusion of the chains of a subcomplex into the ambient chains is a monomorphism. -/
theorem mono_subfunctor_incl_chainComplex (S : Y.Subcomplex) :
    Mono (SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono (coprodMap (R := ℤ) (fun σ : S _⦋n⦌ =>
    S.ι.app (Opposite.op ⦋n⦌) σ))
  refine mono_coprodMap _ (fun a b hab => ?_)
  exact Subtype.ext hab

/-- The chain complex of a subcomplex, as an abbreviation. -/
abbrev subChains (S : Y.Subcomplex) : ChainComplex (ModuleCat ℤ) ℕ :=
  (S : SSet).chainComplex (ModuleCat.of ℤ ℤ)

/-- The inclusion of the chains of a subcomplex into the ambient chains. -/
abbrev incChain (S : Y.Subcomplex) :
    subChains S ⟶ (Y.chainComplex (ModuleCat.of ℤ ℤ)) :=
  SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)

/-- The degreewise component of the inclusion of the chains of a subcomplex is a monomorphism. -/
theorem mono_subfunctor_incl_chainComplex_f (S : Y.Subcomplex) (n : ℕ) :
    Mono ((SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)).f n) := by
  change Mono (coprodMap (R := ℤ) (fun σ : S _⦋n⦌ =>
    S.ι.app (Opposite.op ⦋n⦌) σ))
  exact mono_coprodMap _ (fun a b hab => Subtype.ext hab)

/-- **The cap product on the chains of a subcomplex.**  On a generator `σ` of the `(n+m)`-chains
of `S` it is `α(σ_front) • σ_back`, the back face being taken inside `S`. -/
def capSub (S : Y.Subcomplex) (n m : ℕ) (α : Cochain ℤ Y n) :
    ((S : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X (n + m) ⟶
      ((S : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X m :=
  (S : SSet).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) (n + m) |>.desc
    (Cofan.mk (((S : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X m)
      (fun σ : S _⦋n + m⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
          (genEval ℤ Y α (frontFace Y n (n + m) (Nat.le_add_right n m)
            (S.ι.app (Opposite.op ⦋n + m⦌) σ)))) ≫
        (S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) (backFace (S : SSet) n m σ)))

/-- The value of `capSub` on a generator. -/
theorem ιChainComplex_capSub (S : Y.Subcomplex) (n m : ℕ) (α : Cochain ℤ Y n)
    (σ : S _⦋n + m⦌) :
    (S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ capSub S n m α =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
        (genEval ℤ Y α (frontFace Y n (n + m) (Nat.le_add_right n m)
          (S.ι.app (Opposite.op ⦋n + m⦌) σ)))) ≫
      (S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) (backFace (S : SSet) n m σ) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `capSub` on a generator, as an element. -/
theorem capSub_apply_gen (S : Y.Subcomplex) (n m : ℕ) (α : Cochain ℤ Y n)
    (σ : S _⦋n + m⦌) :
    (capSub S n m α).hom (((S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) =
      genEval ℤ Y α (frontFace Y n (n + m) (Nat.le_add_right n m)
        (S.ι.app (Opposite.op ⦋n + m⦌) σ)) •
        (((S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (backFace (S : SSet) n m σ)).hom 1) := by
  have h2 := congrArg
    (fun (g : ModuleCat.of ℤ ℤ ⟶ ((S : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X m) =>
      g.hom 1)
    (ιChainComplex_capSub S n m α σ)
  have h4 : (ModuleCat.Hom.hom ((S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (backFace (S : SSet) n m σ)))
        ((ModuleCat.Hom.hom (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
          (genEval ℤ Y α (frontFace Y n (n + m) (Nat.le_add_right n m)
            (S.ι.app (Opposite.op ⦋n + m⦌) σ)))))) 1) =
      genEval ℤ Y α (frontFace Y n (n + m) (Nat.le_add_right n m)
        (S.ι.app (Opposite.op ⦋n + m⦌) σ)) •
        (ModuleCat.Hom.hom ((S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (backFace (S : SSet) n m σ))) 1 := by
    rw [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
    nth_rewrite 1 [show (genEval ℤ Y α (frontFace Y n (n + m) (Nat.le_add_right n m)
        (S.ι.app (Opposite.op ⦋n + m⦌) σ)) : ℤ)
        = genEval ℤ Y α (frontFace Y n (n + m) (Nat.le_add_right n m)
        (S.ι.app (Opposite.op ⦋n + m⦌) σ)) • (1 : ℤ) from by simp]
    exact map_zsmul (((S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (backFace (S : SSet) n m σ)).hom)
      (genEval ℤ Y α (frontFace Y n (n + m) (Nat.le_add_right n m)
        (S.ι.app (Opposite.op ⦋n + m⦌) σ))) 1
  simpa only [capSub, ModuleCat.hom_comp, LinearMap.comp_apply, h4] using h2

/-- The back face of a simplex of a subcomplex, as a simplex of the subcomplex. -/
theorem backFace_ι_apply (S : Y.Subcomplex) (n m : ℕ) (σ : S _⦋n + m⦌) :
    S.ι.app (Opposite.op ⦋m⦌) (backFace (S : SSet) n m σ) =
      backFace Y n m (S.ι.app (Opposite.op ⦋n + m⦌) σ) :=
  NatTrans.naturality_apply S.ι ((backIncl n m).op) σ

/-- **The cap product on a subcomplex is compatible with the inclusion into the ambient chains.**
-/
theorem capSub_comp_incl (S : Y.Subcomplex) (n m : ℕ) (α : Cochain ℤ Y n) :
    capSub S n m α ≫ (SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)).f m =
      (SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)).f (n + m) ≫ capHom ℤ Y α m := by
  apply SSet.chainComplex_hom_ext (C := ModuleCat ℤ)
  intro σ
  rw [← Category.assoc, ιChainComplex_capSub]
  rw [Category.assoc]
  rw [show ((S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) (backFace (S : SSet) n m σ)) ≫
      (SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)).f m =
      Y.ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (S.ι.app (Opposite.op ⦋m⦌) (backFace (S : SSet) n m σ)) from
    SSet.ι_chainComplexMap_f (X := (S : SSet)) (Y := Y) S.ι (ModuleCat.of ℤ ℤ) _]
  rw [backFace_ι_apply]
  rw [← Category.assoc]
  rw [show ((S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ) ≫
      (SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)).f (n + m) =
      Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) (S.ι.app (Opposite.op ⦋n + m⦌) σ) from
    SSet.ι_chainComplexMap_f (X := (S : SSet)) (Y := Y) S.ι (ModuleCat.of ℤ ℤ) _]
  rw [ιChainComplex_capHom]

/-- The boundary formula of `Work.Cohomology.cap_d` for a cocycle, in the sign-free case
(`n` even). -/
theorem capHom_comp_d_of_cocycle_even {n m : ℕ} (hn : Even n) (α : Cochain ℤ Y n)
    (hα : cochainDiff ℤ Y α = 0) :
    capHom ℤ Y α (m + 1) ≫ (Y.chainComplex (ModuleCat.of ℤ ℤ)).d (m + 1) m =
      (Y.chainComplex (ModuleCat.of ℤ ℤ)).d (n + (m + 1)) (n + m) ≫ capHom ℤ Y α m := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← cap, ← cap]
  rw [cap_d ℤ Y α c, hα, cap_zero, LinearMap.zero_apply, sub_zero, Even.neg_one_pow hn,
    one_smul]

/-- **The boundary formula for the cap product on a subcomplex**, in the sign-free case
(`n` even, so that `(-1)^n = 1`): the cap product with a cocycle of even degree is a chain map. -/
theorem capSub_comm_d_of_even (S : Y.Subcomplex) (n m : ℕ) (hn : Even n)
    (α : Cochain ℤ Y n) (hα : cochainDiff ℤ Y α = 0) :
    capSub S n (m + 1) α ≫ (subChains S).d (m + 1) m =
      (subChains S).d (n + (m + 1)) (n + m) ≫ capSub S n m α := by
  have hamb := capHom_comp_d_of_cocycle_even (Y := Y) (n := n) (m := m) hn α hα
  have hcomm1 : (subChains S).d (m + 1) m ≫ (incChain S).f m =
      (incChain S).f (m + 1) ≫ (Y.chainComplex (ModuleCat.of ℤ ℤ)).d (m + 1) m :=
    (HomologicalComplex.Hom.comm (incChain S) (m + 1) m).symm
  have hcomm2 : (subChains S).d (n + (m + 1)) (n + m) ≫ (incChain S).f (n + m) =
      (incChain S).f (n + (m + 1)) ≫ (Y.chainComplex (ModuleCat.of ℤ ℤ)).d (n + (m + 1)) (n + m) :=
    (HomologicalComplex.Hom.comm (incChain S) (n + (m + 1)) (n + m)).symm
  have hP : capSub S n (m + 1) α ≫ (incChain S).f (m + 1) =
      (incChain S).f (n + (m + 1)) ≫ capHom ℤ Y α (m + 1) := capSub_comp_incl S n (m + 1) α
  have hQ : capSub S n m α ≫ (incChain S).f m =
      (incChain S).f (n + m) ≫ capHom ℤ Y α m := capSub_comp_incl S n m α
  haveI := mono_subfunctor_incl_chainComplex_f S m
  rw [← cancel_mono ((incChain S).f m)]
  conv_lhs => rw [Category.assoc, hcomm1, ← Category.assoc, hP, Category.assoc]
  conv_rhs => rw [Category.assoc, hQ, ← Category.assoc, hcomm2, Category.assoc]
  rw [hamb]
end

end Work.Cohomology
