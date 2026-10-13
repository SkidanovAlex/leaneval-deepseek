import Mathlib
import Submission.Work.DSSEC.Defs
import Submission.Work.DSSEC.Defs2

namespace Work.DSSEC

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped ZeroObject
open DSMap DSMap.Mix2

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

universe u

section Coaug

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {N : ℕ}
  {i : X ⟶ DSMap.PSpace A N} {W : Type u} [CommRing W] {ψ : A →+* W} {t : Idx.{(u)} N → W}

/-- The comparison map sends `1` to `1`. -/
lemma cmpMap_one (D : SecData A X f N i W ψ t) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) :
    (cmpMap D n y).hom (1 : Γ(X, ROpen i n y)) = (1 : chartRing t (SIdx N n y)) := by
  have h1 : ((DSMap.cechPresheaf A X f).map
      (eqToHom (congrArg op (ROpen_eq_IOpen i n y)))).hom (1 : Γ(X, ROpen i n y)) =
      (1 : Γ(X, IOpen i n y)) := by
    show (X.presheaf.map (eqToHom (congrArg op (ROpen_eq_IOpen i n y)))).hom 1 = 1
    exact map_one _
  rw [cmpMap]
  show (D.toFun (SIdx N n y) (SIdx_nonempty N n y))
      (((DSMap.cechPresheaf A X f).map
        (eqToHom (congrArg op (ROpen_eq_IOpen i n y)))).hom (1 : Γ(X, ROpen i n y))) = 1
  rw [h1, map_one]

/-- The degree-`0` coaugmentation of the `ℕ`-complex comparison map. -/
lemma coaug_chiZero (D : SecData A X f N i W ψ t) :
    DSMap.coaug0 A X f (DSMap.Mix2.chartCover i) ≫ (chiZero D).f 0 =
      DSMap.Mix2.chartCoaugA ψ t := by
  refine Fan.IsLimit.hom_ext
    (Limits.isLimitOfHasProductOfPreservesLimit (ModuleCat.restrictScalars ψ) (chartTerm t 0))
    _ _ (fun y => ?_)
  show DSMap.coaug0 A X f (DSMap.Mix2.chartCover i) ≫ (chiZero D).f 0 ≫
        (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t 0) y) =
      DSMap.Mix2.chartCoaugA ψ t ≫
        (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t 0) y)
  rw [show (chiZero D).f 0 = chiZeroComp D 0 from rfl]
  rw [chiZeroComp_fac]
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  show (cmpMap D 0 y).hom (((DSMap.coaug0 A X f (DSMap.Mix2.chartCover i) ≫
      Pi.π (coverTerm A X f i 0) y).hom a)) =
    ((DSMap.Mix2.chartCoaugA ψ t ≫ (ModuleCat.restrictScalars ψ).map
      (Pi.π (chartTerm t 0) y)).hom) a
  have h1 : ((DSMap.coaug0 A X f (DSMap.Mix2.chartCover i) ≫
      Pi.π (coverTerm A X f i 0) y).hom a) = DSMap.phiU A X f (ROpen i 0 y) a := by
    rw [show DSMap.coaug0 A X f (DSMap.Mix2.chartCover i) ≫
          Pi.π (coverTerm A X f i 0) y =
        DSMap.unitTop A X f ≫ (DSMap.cechPresheaf A X f).map
          (homOfLE (le_top : ROpen i 0 y ≤ ⊤)).op from Pi.lift_comp_π _ _]
    show (X.presheaf.map (homOfLE (le_top : ROpen i 0 y ≤ ⊤)).op).hom
      ((DSMap.unitTop A X f).hom a) = DSMap.phiU A X f (ROpen i 0 y) a
    rw [show (DSMap.unitTop A X f).hom a = DSMap.phiU A X f ⊤ a from
      congrArg (fun g : A →+* Γ(X, ⊤) => g a)
        (RingHom.algebraMap_toAlgebra (DSMap.phiU A X f ⊤))]
    exact DSMap.phiU_res A X f (homOfLE (le_top : ROpen i 0 y ≤ ⊤)) a
  have h2 : (cmpMap D 0 y).hom (DSMap.phiU A X f (ROpen i 0 y) a) =
      algebraMap W (chartRing t (SIdx N 0 y)) (ψ a) := by
    rw [cmpMap]
    show (D.toFun (SIdx N 0 y) (SIdx_nonempty N 0 y))
      (((DSMap.cechPresheaf A X f).map
        (eqToHom (congrArg op (ROpen_eq_IOpen i 0 y)))).hom
          (DSMap.phiU A X f (ROpen i 0 y) a)) = _
    rw [show ((DSMap.cechPresheaf A X f).map
          (eqToHom (congrArg op (ROpen_eq_IOpen i 0 y)))).hom
          (DSMap.phiU A X f (ROpen i 0 y) a) =
        DSMap.phiU A X f (IOpen i 0 y) a from by
      show (X.presheaf.map (eqToHom (congrArg op (ROpen_eq_IOpen i 0 y)))).hom
          (DSMap.phiU A X f (ROpen i 0 y) a) = DSMap.phiU A X f (IOpen i 0 y) a
      rw [show (eqToHom (congrArg op (ROpen_eq_IOpen i 0 y))) =
          (homOfLE (le_of_eq (ROpen_eq_IOpen i 0 y).symm)).op from Subsingleton.elim _ _]
      exact DSMap.phiU_res A X f
        (homOfLE (le_of_eq (ROpen_eq_IOpen i 0 y).symm)) a]
    exact RingHom.congr_fun (D.comm_A (SIdx N 0 y) (SIdx_nonempty N 0 y)) a
  have h3 : (((DSMap.Mix2.chartCoaugA ψ t ≫ (ModuleCat.restrictScalars ψ).map
      (Pi.π (chartTerm t 0) y)).hom) a) = algebraMap W (chartRing t (SIdx N 0 y)) (ψ a) := by
    rw [show (DSMap.Mix2.chartCoaugA ψ t) = DSMap.Mix2.unitA ψ ≫
        (ModuleCat.restrictScalars ψ).map (DSMap.Mix2.chartCoaugW t) from rfl,
      Category.assoc, ← Functor.map_comp]
    rw [show DSMap.Mix2.chartCoaugW t ≫ Pi.π (chartTerm t 0) y =
        ModuleCat.ofHom (Algebra.linearMap W (chartRing t (SIdx N 0 y))) from
      Pi.lift_comp_π _ _]
    show (Algebra.linearMap W (chartRing t (SIdx N 0 y)))
      ((DSMap.Mix2.unitA ψ).hom a) = algebraMap W (chartRing t (SIdx N 0 y)) (ψ a)
    rw [show (DSMap.Mix2.unitA ψ).hom a = ψ a from rfl, Algebra.linearMap_apply]
  rw [h1, h3, h2]

end Coaug
/-- **The combinatorial half of node `SEC`**: a chart comparison on nonempty index sets
(`Work.DSSEC.SecData`, i.e. maps `Γ(X, U_S) → W[J/t_S]`, `x_k/x_i ↦ t_k/t_i`, compatible with
restrictions and with `A → W`) produces the chain map of the frozen node
`DSMap.Mix2.area_SEC`, compatibly with the coaugmentations.

Plan: in degree `n` both complexes are products over `x : Fin (n+1) → Idx N`; identify the index
objects — `∏ᶜ_a chartIdx (x a) = op (Finset.univ.image x)` (products in `(Finset ι)ᵒᵖ` are unions,
`finite_coproduct_eq_finset_sup`) and `∏ᶜ_a chartCover i (x a) = ⨅ m ∈ univ.image x, chartCover i m`
(products in `X.Opens` are infima) — and set `χ.f n := Pi.lift (fun x => Pi.π _ x ≫ φ n x)` with
`φ n x` the comparison map at the index set `Finset.univ.image x`.  The chain condition is then
componentwise: use `Work.DSF1.Cech.cechComplexFunctor_d_π` and `D.natural` for the inclusion
`image (x ∘ δ_a) ⊆ image x`; the coaugmentation condition reduces to `D.comm_A` for singletons.
Pass to `ℤ`-degrees with `HomologicalComplex.extendMap`. -/
theorem exists_cechMap_of_secData (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) (N : ℕ) (i : X ⟶ DSMap.PSpace A N) (W : Type u) [CommRing W]
    (ψ : A →+* W) (t : Work.DSSEC.Idx N → W) (D : Work.DSSEC.SecData A X f N i W ψ t) :
    ∃ χ : DSMap.cechZ A X f (DSMap.Mix2.chartCover i) ⟶ DSMap.Mix2.chartCechA ψ t,
      DSMap.coaug0 A X f (DSMap.Mix2.chartCover i) ≫
        ((DSMap.cech A X f (DSMap.Mix2.chartCover i)).extendXIso
            ComplexShape.embeddingUpNat (i := 0) rfl).inv ≫
          χ.f 0 ≫ (ModuleCat.restrictScalars ψ).map
            ((DSMap.Mix2.chartCech t).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        DSMap.Mix2.chartCoaugA ψ t := by
  refine ⟨chi D, ?_⟩
  rw [chi_comp_iso D]
  exact coaug_chiZero D

end Work.DSSEC
