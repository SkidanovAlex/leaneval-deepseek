-- PORTED COPY (neutral island) of `Submission/Work/Serre/Surj/baseChangeEzShufChain.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
/-
# Base change `ℤ → ℚ` commutes with the Eilenberg–Zilber shuffle

`Work.Serre.ezShufChain W P m q u vt` is the Eilenberg–Zilber shuffle of the integral chains
`u ∈ C_m(W;ℤ)` and `vt ∈ C_q(P;ℤ)`, computed through the shuffle chain map
`Work.Kunneth.ezMapT` (and the tensor product `tpC` of the two integral chain complexes);
`Work.Serre.shufRat W P m q` is the rational Eilenberg–Zilber shuffle, built from the bilinear
shuffle `Work.Serre.ezBilR ℚ`.

The statement proved here is the compatibility of the two constructions with the coefficient change
`ℤ → ℚ`, expressed through the comparison isomorphism

`Φ_X : C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)`

of `Work.StemsB.RatBC`: for all integral chains `u`, `vt`,

`Φ_{W×P} (1 ⊗ EZ(u, vt)) = EZ_ℚ (Φ_W (1 ⊗ u), Φ_P (1 ⊗ vt))`.

The proof uses the computation rule `Φ_X (1 ⊗ x) = bcCast x` of `Work.Serre` (the coefficient
change is the identity on the generators `Work.KunnethEZ.genC`), the fact that `bcCast` is natural
for the chain maps induced by maps of simplicial sets, and the fact that `bcCast` commutes with the
bilinear shuffle `ezBilR` (both statements being reduced to generators).
-/

import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.ezMap_ezBilR
import Submission.Work.StemsB.RatBaseNaturality
import Submission.Work.Serre.Neu.BaseChangeAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology Simplicial
open scoped Simplicial TensorProduct MonoidalCategory

namespace Work.Serre.Surj

noncomputable section

/-! ## Extensionality on the generators of the simplicial chains -/

/-- A morphism out of the coefficient `ℤ` is determined by its value at `1`. -/
lemma zcZ_hom_ext {M : ModuleCat ℤ} (f g : Work.Serre.zcZ ⟶ M)
    (h : f.hom (1 : ℤ) = g.hom (1 : ℤ)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

/-- A `ℤ`-linear map out of the integral simplicial chains is determined by its values on the
generators. -/
lemma zLinearMap_ext_gen {X : SSet} {p : ℕ} {T : Type} [AddCommGroup T] [Module ℤ T]
    {f g : (X.chainComplex Work.Serre.zcZ).X p →ₗ[ℤ] T}
    (h : ∀ σ : X _⦋p⦌, f ((X.ιChainComplex (R := Work.Serre.zcZ) σ).hom 1)
        = g ((X.ιChainComplex (R := Work.Serre.zcZ) σ).hom 1)) : f = g := by
  have h' : (ModuleCat.ofHom f : (X.chainComplex Work.Serre.zcZ).X p ⟶ ModuleCat.of ℤ T)
      = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext (X := X) (R := Work.Serre.zcZ) (n := p)
    intro σ
    apply zcZ_hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    exact h σ
  have h'' := congrArg ModuleCat.Hom.hom h'
  simpa using h''

/-- A `ℚ`-linear map out of the rational simplicial chains is determined by its values on the
generators. -/
lemma qLinearMap_ext_gen {X : SSet} {p : ℕ} {T : Type} [AddCommGroup T] [Module ℚ T]
    {f g : (X.chainComplex Work.Serre.zcQ).X p →ₗ[ℚ] T}
    (h : ∀ σ : X _⦋p⦌, f ((X.ιChainComplex (R := Work.Serre.zcQ) σ).hom 1)
        = g ((X.ιChainComplex (R := Work.Serre.zcQ) σ).hom 1)) : f = g := by
  have h' : (ModuleCat.ofHom f : (X.chainComplex Work.Serre.zcQ).X p ⟶ ModuleCat.of ℚ T)
      = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext (X := X) (R := Work.Serre.zcQ) (n := p)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    exact h σ
  have h'' := congrArg ModuleCat.Hom.hom h'
  simpa using h''

/-! ## The coefficient change of the shuffle chain of a pair of simplices -/

/-- The shuffle chain of a pair of simplices commutes with the coefficient change `ℤ → ℚ`. -/
lemma bcCast_ezGenR (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    (Work.Serre.bcCast (X ⊗ Y) (p + q)).hom (Work.Serre.ezGenR ℤ p q X Y σ τ)
      = Work.Serre.ezGenR ℚ p q X Y σ τ := by
  rw [Work.Serre.ezGenR, Work.Serre.ezGenR, map_sum]
  exact Finset.sum_congr rfl (fun S _ => by
    rw [map_zsmul]
    congr 1
    exact Work.Serre.bcCast_ι (X ⊗ Y) (p + q) (Work.Serre.ezCellGenR p q X Y σ τ S))

/-! ## The coefficient change commutes with the bilinear shuffle -/

/-- The value of `ezShufR` on a generator of the second variable. -/
lemma ezShufR_genElt (R : Type) [CommRing R] (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌)
    (τ : Y _⦋q⦌) :
    (Work.Serre.ezShufR R p q X Y σ).hom
        ((Y.ιChainComplex (R := ModuleCat.of R R) τ).hom 1)
      = Work.Serre.ezGenR R p q X Y σ τ := by
  have h := congrArg (fun (f : ModuleCat.of R R ⟶
      ModuleCat.of R (↥(((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q)))) =>
        f.hom (1 : R)) (Work.Serre.ezShufR_ι R p q X Y σ τ)
  simpa using h

/-- The base change of the shuffle chain of a pair of generators. -/
lemma bcCast_ezBilR_gen (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    (Work.Serre.bcCast (X ⊗ Y) (p + q)).hom
        ((Work.Serre.ezBilR ℤ p q X Y).hom
          ((X.ιChainComplex (R := Work.Serre.zcZ) σ).hom 1)
          ((Y.ιChainComplex (R := Work.Serre.zcZ) τ).hom 1))
      = (Work.Serre.ezBilR ℚ p q X Y).hom
          ((Work.Serre.bcCast X p).hom ((X.ιChainComplex (R := Work.Serre.zcZ) σ).hom 1))
          ((Work.Serre.bcCast Y q).hom ((Y.ιChainComplex (R := Work.Serre.zcZ) τ).hom 1)) := by
  rw [Work.Serre.bcCast_ι X p σ, Work.Serre.bcCast_ι Y q τ,
    Work.Serre.ezBilR_gen ℤ p q X Y σ τ, Work.Serre.ezBilR_gen ℚ p q X Y σ τ]
  exact bcCast_ezGenR p q X Y σ τ

/-- The base change of a shuffle chain, in the second variable. -/
lemma bcCast_ezShufR (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌)
    (v : ↥((Y.chainComplex Work.Serre.zcZ).X q)) :
    (Work.Serre.bcCast (X ⊗ Y) (p + q)).hom ((Work.Serre.ezShufR ℤ p q X Y σ).hom v)
      = (Work.Serre.ezShufR ℚ p q X Y σ).hom ((Work.Serre.bcCast Y q).hom v) := by
  have key : ((Work.Serre.bcCast (X ⊗ Y) (p + q)).hom.comp
        ((Work.Serre.ezShufR ℤ p q X Y σ).hom))
      = (((Work.Serre.ezShufR ℚ p q X Y σ).hom).restrictScalars ℤ).comp
          ((Work.Serre.bcCast Y q).hom) := by
    apply zLinearMap_ext_gen (X := Y) (p := q)
    intro τ
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [Work.Serre.bcCast_ι Y q τ, ezShufR_genElt ℤ p q X Y σ τ,
      ezShufR_genElt ℚ p q X Y σ τ]
    exact bcCast_ezGenR p q X Y σ τ
  exact congrArg (fun (f : ↥((Y.chainComplex Work.Serre.zcZ).X q) →ₗ[ℤ]
      ↥(((X ⊗ Y).chainComplex Work.Serre.zcQ).X (p + q))) => f v) key

/-- Evaluating the integral shuffle in its first variable at `1` gives `ezShufR`. -/
lemma ezBilR_ι_apply_one (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) :
    (Work.Serre.ezBilR ℤ p q X Y).hom ((X.ιChainComplex (R := Work.Serre.zcZ) σ).hom 1)
      = (Work.Serre.ezShufR ℤ p q X Y σ).hom := by
  apply zLinearMap_ext_gen (X := Y) (p := q)
  intro τ
  rw [Work.Serre.ezBilR_gen ℤ p q X Y σ τ, ezShufR_genElt ℤ p q X Y σ τ]

/-- The rational analogue of `ezBilR_ι_apply_one`. -/
lemma ezBilR_ι_apply_one_rat (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) :
    (Work.Serre.ezBilR ℚ p q X Y).hom ((X.ιChainComplex (R := Work.Serre.zcQ) σ).hom 1)
      = (Work.Serre.ezShufR ℚ p q X Y σ).hom := by
  apply qLinearMap_ext_gen (X := Y) (p := q)
  intro τ
  rw [Work.Serre.ezBilR_gen ℚ p q X Y σ τ, ezShufR_genElt ℚ p q X Y σ τ]

/-- The base change of a shuffle chain, in the first variable. -/
lemma bcCast_ezBilR_right (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌)
    (v : ↥((Y.chainComplex Work.Serre.zcZ).X q)) :
    (Work.Serre.bcCast (X ⊗ Y) (p + q)).hom
        ((Work.Serre.ezBilR ℤ p q X Y).hom ((X.ιChainComplex (R := Work.Serre.zcZ) σ).hom 1) v)
      = (Work.Serre.ezBilR ℚ p q X Y).hom
          ((Work.Serre.bcCast X p).hom ((X.ιChainComplex (R := Work.Serre.zcZ) σ).hom 1))
          ((Work.Serre.bcCast Y q).hom v) := by
  rw [Work.Serre.bcCast_ι X p σ, ezBilR_ι_apply_one p q X Y σ,
    ezBilR_ι_apply_one_rat p q X Y σ]
  exact bcCast_ezShufR p q X Y σ v

/-! ## The two `ℤ`-linear models, with one variable evaluated -/

/-- The integral shuffle with the second variable evaluated, as a `ℤ`-linear map in the first
variable. -/
def ezBilZLeft (p q : ℕ) (X Y : SSet) (v : ↥((Y.chainComplex Work.Serre.zcZ).X q)) :
    ModuleCat.of ℤ (↥((X.chainComplex Work.Serre.zcZ).X p)) ⟶
      ModuleCat.of ℤ (↥(((X ⊗ Y).chainComplex Work.Serre.zcZ).X (p + q))) :=
  ModuleCat.ofHom (show (↥((X.chainComplex Work.Serre.zcZ).X p)) →ₗ[ℤ]
      ↥(((X ⊗ Y).chainComplex Work.Serre.zcZ).X (p + q)) from
    (LinearMap.applyₗ v).comp (Work.Serre.ezBilR ℤ p q X Y).hom)

/-- The rational shuffle with the second variable evaluated, as a `ℤ`-linear map in the first
variable. -/
def ezBilQLeft (p q : ℕ) (X Y : SSet) (v : ↥((Y.chainComplex Work.Serre.zcQ).X q)) :
    ModuleCat.of ℤ (↥((X.chainComplex Work.Serre.zcQ).X p)) ⟶
      ModuleCat.of ℤ (↥(((X ⊗ Y).chainComplex Work.Serre.zcQ).X (p + q))) :=
  ModuleCat.ofHom (show (↥((X.chainComplex Work.Serre.zcQ).X p)) →ₗ[ℤ]
      ↥(((X ⊗ Y).chainComplex Work.Serre.zcQ).X (p + q)) from
    ((LinearMap.applyₗ v).comp (Work.Serre.ezBilR ℚ p q X Y).hom).restrictScalars ℤ)

/-- **The coefficient change commutes with the bilinear shuffle.** -/
theorem bcCast_ezBilR (p q : ℕ) (X Y : SSet)
    (u : ↥((X.chainComplex Work.Serre.zcZ).X p))
    (v : ↥((Y.chainComplex Work.Serre.zcZ).X q)) :
    (Work.Serre.bcCast (X ⊗ Y) (p + q)).hom ((Work.Serre.ezBilR ℤ p q X Y).hom u v)
      = (Work.Serre.ezBilR ℚ p q X Y).hom ((Work.Serre.bcCast X p).hom u)
          ((Work.Serre.bcCast Y q).hom v) := by
  have key : ezBilZLeft p q X Y v ≫ Work.Serre.bcCast (X ⊗ Y) (p + q)
      = Work.Serre.bcCast X p ≫ ezBilQLeft p q X Y ((Work.Serre.bcCast Y q).hom v) := by
    apply ModuleCat.hom_ext
    apply zLinearMap_ext_gen (X := X) (p := p)
    intro σ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ezBilZLeft, ezBilQLeft,
      ModuleCat.hom_ofHom, LinearMap.restrictScalars_apply, LinearMap.applyₗ_apply_apply]
    exact bcCast_ezBilR_right p q X Y σ v
  exact congrArg (fun (f : (X.chainComplex Work.Serre.zcZ).X p →ₗ[ℤ]
      ↥(ModuleCat.of ℤ (↥(((X ⊗ Y).chainComplex Work.Serre.zcQ).X (p + q))))) => f u)
    (congrArg ModuleCat.Hom.hom key)

/-! ## Naturality of the coefficient change -/

/-- The coefficient change commutes with the chain maps induced by maps of simplicial sets. -/
lemma bcCast_chainComplexMap_mor {X Y : SSet} (f : X ⟶ Y) (n : ℕ) :
    (SSet.chainComplexMap f Work.Serre.zcZ).f n ≫ Work.Serre.bcCast Y n
      = Work.Serre.bcCast X n ≫ ModuleCat.ofHom
          (((SSet.chainComplexMap f Work.Serre.zcQ).f n).hom.restrictScalars ℤ) := by
  apply SSet.chainComplex_hom_ext (X := X) (R := Work.Serre.zcZ) (n := n)
  intro x
  rw [SSet.ι_chainComplexMap_f_assoc, Work.Serre.bcCast_ι_mor, ← Category.assoc,
    Work.Serre.bcCast_ι_mor]
  apply zcZ_hom_ext
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, LinearMap.restrictScalars_apply, one_smul]
  have hnat := congrArg (fun (g : Work.Serre.zcQ ⟶ (Y.chainComplex Work.Serre.zcQ).X n) =>
      g.hom (1 : ℚ)) (SSet.ι_chainComplexMap_f (X := X) (Y := Y) f Work.Serre.zcQ (n := n) x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hnat
  exact hnat.symm

/-- The elementwise form of `bcCast_chainComplexMap_mor`. -/
lemma bcCast_chainComplexMap {X Y : SSet} (f : X ⟶ Y) (n : ℕ)
    (z : ↥((X.chainComplex Work.Serre.zcZ).X n)) :
    (Work.Serre.bcCast Y n).hom (((SSet.chainComplexMap f Work.Serre.zcZ).f n).hom z)
      = ((SSet.chainComplexMap f Work.Serre.zcQ).f n).hom
          ((Work.Serre.bcCast X n).hom z) := by
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (bcCast_chainComplexMap_mor f n)) z
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simpa only [ModuleCat.hom_ofHom, LinearMap.restrictScalars_apply] using h

/-! ## The comparison isomorphism on a pure tensor -/

/-- **The comparison `Φ` on a pure tensor**: `Φ_X (1 ⊗ x) = bcCast x`. -/
lemma Phi_tmul (X : SSet) (n : ℕ) (x : ↥((X.chainComplex Work.Serre.zcZ).X n)) :
    (HomologicalComplex.Hom.f (Work.StemsB.RatBC.Phi X).hom n).hom
        (TensorProduct.tmul ℤ (1 : ℚ) x)
      = (Work.Serre.bcCast X n).hom x := by
  have h := Work.Serre.Phi_unit_bcCast X n x
  simpa only [Work.Serre.PhiN] using h

/-! ## The main theorem -/

/-- **Base change `ℤ → ℚ` commutes with the Eilenberg–Zilber shuffle on a product.** -/
theorem baseChangeEzShufChain (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (m q : ℕ) (u : (Work.Cohomology.singularChains ℤ (TopCat.of W)).X m)
    (vt : (Work.Cohomology.singularChains ℤ (TopCat.of P)).X q) :
    (((Work.StemsB.RatBC.Phi (Work.Serre.singSSetN (W × P))).hom).f (m + q)).hom
        (TensorProduct.tmul ℤ (1 : ℚ) (Work.Serre.ezShufChain W P m q u vt))
      = Work.Serre.shufRat W P m q
          ((((Work.StemsB.RatBC.Phi (Work.Serre.singSSetN W)).hom).f m).hom
            (TensorProduct.tmul ℤ (1 : ℚ) u))
          ((((Work.StemsB.RatBC.Phi (Work.Serre.singSSetN P)).hom).f q).hom
            (TensorProduct.tmul ℤ (1 : ℚ) vt)) := by
  have hU : Work.Serre.ezShufChain W P m q u vt
      = ((SSet.chainComplexMap (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv
            Work.Kunneth.zz).f (m + q)).hom
          ((Work.Serre.ezBilR ℤ m q (Work.Serre.singSSetN W) (Work.Serre.singSSetN P)).hom
            u vt) := by
    rw [Work.Serre.ezShufChain, Work.Kunneth.ezMapT, HomologicalComplex.comp_f,
      CategoryTheory.comp_apply, Work.Serre.ezMap_ezBilR]
  have hD : (Work.Serre.bcCast (Work.Serre.singSSetN (W × P)) (m + q)).hom
        (((SSet.chainComplexMap (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv
            Work.Kunneth.zz).f (m + q)).hom
          ((Work.Serre.ezBilR ℤ m q (Work.Serre.singSSetN W) (Work.Serre.singSSetN P)).hom u vt))
      = ((SSet.chainComplexMap (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv
            Work.Serre.zcQ).f (m + q)).hom
          ((Work.Serre.bcCast ((Work.Serre.singSSetN W) ⊗ (Work.Serre.singSSetN P)) (m + q)).hom
            ((Work.Serre.ezBilR ℤ m q (Work.Serre.singSSetN W) (Work.Serre.singSSetN P)).hom u vt)) :=
    bcCast_chainComplexMap (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv (m + q) _
  have hC : (Work.Serre.bcCast ((Work.Serre.singSSetN W) ⊗ (Work.Serre.singSSetN P)) (m + q)).hom
        ((Work.Serre.ezBilR ℤ m q (Work.Serre.singSSetN W) (Work.Serre.singSSetN P)).hom u vt)
      = (Work.Serre.ezBilR ℚ m q (Work.Serre.singSSetN W) (Work.Serre.singSSetN P)).hom
          ((Work.Serre.bcCast (Work.Serre.singSSetN W) m).hom u)
          ((Work.Serre.bcCast (Work.Serre.singSSetN P) q).hom vt) :=
    bcCast_ezBilR m q (Work.Serre.singSSetN W) (Work.Serre.singSSetN P) u vt
  rw [Phi_tmul, hU, hD, hC, Phi_tmul, Phi_tmul, Work.Serre.shufRat]
  rfl

end

end Work.Serre.Surj
