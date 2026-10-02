import Mathlib
import Submission.Work.Cohomology.Pullback
import Submission.Work.RatHurewicz.Excision
import Submission.Work.Cohomology.CompactSupport

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Every singular chain is carried by a compact set

For a topological space `X`, a singular `j`-chain with coefficients in `ℚ`,
`c ∈ C_j(X;ℚ)`, is a finite sum `∑ a_σ • σ` of generators (simplices), hence has compact
support: there is a compact `K ⊆ X` and a chain `w` on `K` whose image under the chain map of
the inclusion `K ↪ X` is `c`.

The two ingredients are
* `coordsQ`/`mkQ` (with `mkQ_comp_coordsQ`, `chain_eq_sum_genQ`): the identification of the
  singular chain module `C_n(X;ℚ)` with the free module on the `n`-simplices, giving the
  expansion of a chain into its generators (the `ℚ` analogue of
  `Work.Cohomology.Crux33.coords`/`mk`, which is stated for `ℤ`);
* `liftSimplex`/`map_liftSimplex`: a simplex whose image lies in `K` lifts to a simplex of `K`,
  and the lift is taken to it by the map induced by the inclusion.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.StemsB

noncomputable section

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

/-! ## 1. Chains with coefficients in `ℚ` as finite sums of simplices -/

/-- The coordinate function of an `n`-chain of a simplicial set: the `ℚ`-linear map sending the
generator attached to a simplex `x` to `Finsupp.single x 1`. -/
def coordsQ (X : SSet) (n : ℕ) :
    (X.chainComplex (ModuleCat.of ℚ ℚ)).X n →ₗ[ℚ] (X _⦋n⦌ →₀ ℚ) :=
  ModuleCat.Hom.hom (Cofan.IsColimit.desc (X.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n)
    (fun x => ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℚ _ (Finsupp.single x (1 : ℚ)))))

/-- The coordinate function of the generator attached to a simplex. -/
@[simp]
theorem coordsQ_ι (X : SSet) (n : ℕ) (x : X _⦋n⦌) :
    coordsQ X n ((X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom 1)
      = Finsupp.single x (1 : ℚ) := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n)
    (fun y => ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℚ _ (Finsupp.single y (1 : ℚ)))) x
  have h2 := congrArg (fun (g : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ((X _⦋n⦌) →₀ ℚ)) =>
    g.hom (1 : ℚ)) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : (LinearMap.toSpanSingleton ℚ ((X _⦋n⦌) →₀ ℚ)
      (Finsupp.single x (1 : ℚ))) (1 : ℚ) = Finsupp.single x (1 : ℚ) := by
    rw [LinearMap.toSpanSingleton_apply]
    exact one_smul _ _
  rw [ModuleCat.hom_ofHom, h3] at h2
  exact h2

/-- The `ℚ`-linear map from the free module on the `n`-simplices of `X` back to the `n`-chains. -/
def mkQ (X : SSet) (n : ℕ) :
    (X _⦋n⦌ →₀ ℚ) →ₗ[ℚ] (X.chainComplex (ModuleCat.of ℚ ℚ)).X n :=
  (Finsupp.lsum ℚ) (fun x => (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom)

/-- The value of `mkQ` on a generator. -/
theorem mkQ_single (X : SSet) (n : ℕ) (x : X _⦋n⦌) (b : ℚ) :
    mkQ X n (Finsupp.single x b) = ((X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x)).hom b := by
  show ((Finsupp.lsum ℚ) (fun x => (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom))
      (Finsupp.single x b) = _
  rw [Finsupp.lsum_single]

/-- `mkQ` expands a finitely supported function into a sum of generators. -/
theorem mkQ_eq_sum_gen (X : SSet) (n : ℕ) (c : X _⦋n⦌ →₀ ℚ) :
    mkQ X n c = ∑ x ∈ c.support, (c x) • (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom 1 := by
  change ((Finsupp.lsum ℚ) (fun x => (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom)) c = _
  rw [Finsupp.lsum_apply]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [← map_smul, smul_eq_mul, mul_one]

/-- `mkQ` is a left inverse of `coordsQ`. -/
theorem mkQ_comp_coordsQ (X : SSet) (n : ℕ) :
    (mkQ X n).comp (coordsQ X n) = LinearMap.id := by
  have h : ModuleCat.ofHom ((mkQ X n).comp (coordsQ X n))
      = ModuleCat.ofHom (LinearMap.id :
          (X.chainComplex (ModuleCat.of ℚ ℚ)).X n →ₗ[ℚ]
            (X.chainComplex (ModuleCat.of ℚ ℚ)).X n) := by
    apply SSet.chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show mkQ X n (coordsQ X n ((X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom 1))
      = (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom 1
    rw [coordsQ_ι, mkQ_single]
  exact congrArg ModuleCat.Hom.hom h

/-- **A chain with coefficients in `ℚ` is the sum of its generators.** -/
theorem chain_eq_sum_genQ (X : SSet) (n : ℕ) (u : (X.chainComplex (ModuleCat.of ℚ ℚ)).X n) :
    u = ∑ x ∈ (coordsQ X n u).support,
        (coordsQ X n u x) • (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x).hom 1 := by
  rw [← mkQ_eq_sum_gen X n (coordsQ X n u)]
  exact (LinearMap.congr_fun (mkQ_comp_coordsQ X n) u).symm

/-! ## 2. Lifting a simplex whose image lies in a subset -/

/-- The canonical equivalence between the `n`-simplices of the singular simplicial set and the
continuous maps from the standard `n`-simplex is natural in the space. -/
theorem toSSetObjEquiv_map' {X Y : TopCat.{0}} (g : X ⟶ Y) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk n)))
        ((TopCat.toSSet.map g).app (Opposite.op (SimplexCategory.mk n)) x)
      = g.hom.comp (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) x) := by
  ext z
  rw [show (TopCat.toSSet.map g).app _ x = ULift.up (x.down ≫ g) from rfl]
  show (TopCat.toSSetObjEquiv Y _ (ULift.up (x.down ≫ g))) z
      = (g.hom.comp (TopCat.toSSetObjEquiv X _ x)) z
  have hL : (TopCat.toSSetObjEquiv Y _ (ULift.up (x.down ≫ g))) z
      = TopCat.Hom.hom (x.down ≫ g) (ULift.up z) := rfl
  have hR : (TopCat.toSSetObjEquiv X _ x) z = TopCat.Hom.hom x.down (ULift.up z) := rfl
  rw [hL]
  simp only [ContinuousMap.comp_apply]
  rw [hR]
  rfl

/-- The lift of a singular `j`-simplex `σ` of `X` to a subset `K` containing its image. -/
def liftSimplex {X : Type} [TopologicalSpace X] (K : Set X) {j : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋j⦌)
    (h : Set.range ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋j⦌)) σ) ⊆ K) :
    (TopCat.toSSet.obj (TopCat.of ↥K)) _⦋j⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of ↥K) (Opposite.op ⦋j⦌)).symm
    { toFun := fun z => ⟨(TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋j⦌) σ) z, h ⟨z, rfl⟩⟩
      continuous_toFun := Continuous.subtype_mk
        (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋j⦌) σ).continuous _ }

/-- **The inclusion `K ↪ X` takes the lift of `σ` to `σ`.** -/
theorem map_liftSimplex {X : Type} [TopologicalSpace X] (K : Set X) {j : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋j⦌)
    (h : Set.range ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋j⦌)) σ) ⊆ K) :
    (TopCat.toSSet.map (TopCat.ofHom (Work.RatHurewicz.setIncl K))).app (Opposite.op ⦋j⦌)
      (liftSimplex K σ h) = σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋j⦌)).injective
  rw [toSSetObjEquiv_map']
  have h1 : (TopCat.toSSetObjEquiv (TopCat.of ↥K) (Opposite.op ⦋j⦌)) (liftSimplex K σ h)
      = (⟨fun z => ⟨(TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋j⦌) σ) z, h ⟨z, rfl⟩⟩,
          Continuous.subtype_mk (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋j⦌) σ).continuous _⟩ :
        C(Convexity.StdSimplex ℝ (Fin (j+1)), TopCat.of ↥K)) :=
    Equiv.apply_symm_apply _ _
  rw [h1]
  ext z
  rfl

/-- The chain map induced by an inclusion carries the generator of a lift to the generator. -/
theorem genElt_chainComplexMapQ {A B : SSet.{0}} (F : A ⟶ B) (n : ℕ) (σ : A _⦋n⦌) :
    (SSet.chainComplexMap F (ModuleCat.of ℚ ℚ)).f n (Work.Cohomology.genElt ℚ A σ)
      = Work.Cohomology.genElt ℚ B (F.app (Opposite.op (SimplexCategory.mk n)) σ) := by
  have h := congrArg (fun (g : ModuleCat.of ℚ ℚ ⟶ (B.chainComplex (ModuleCat.of ℚ ℚ)).X n) =>
      ModuleCat.Hom.hom g (1 : ℚ))
    (SSet.ι_chainComplexMap_f (X := A) (Y := B) (f := F) (R := ModuleCat.of ℚ ℚ) σ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, Work.Cohomology.genElt] using h

/-! ## 3. The main statement -/

theorem compactSupportChain {X : Type} [TopologicalSpace X] (j : ℕ)
    (c : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X j) :
    ∃ (K : Set X) (_ : IsCompact K)
      (w : (Work.Cohomology.singularChains ℚ (TopCat.of ↥K)).X j),
      (Work.Cohomology.chainMap ℚ (TopCat.of ↥K) (TopCat.of X)
        (TopCat.ofHom (Work.RatHurewicz.setIncl K))).f j w = c := by
  classical
  have hsum : c = ∑ σ ∈ (coordsQ (TopCat.toSSet.obj (TopCat.of X)) j c).support,
      (coordsQ (TopCat.toSSet.obj (TopCat.of X)) j c σ) •
        Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of X)) σ :=
    chain_eq_sum_genQ (TopCat.toSSet.obj (TopCat.of X)) j c
  set S : Finset (TopCat.toSSet.obj (TopCat.of X) _⦋j⦌) :=
    (coordsQ (TopCat.toSSet.obj (TopCat.of X)) j c).support with hSdef
  set K : Set X := ⋃ σ ∈ (S : Set (TopCat.toSSet.obj (TopCat.of X) _⦋j⦌)),
    Work.Cohomology.simplexRange (TopCat.of X) σ with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    exact Set.Finite.isCompact_biUnion S.finite_toSet
      (fun σ _ => Work.Cohomology.isCompact_simplexRange (TopCat.of X) σ)
  have hsub : ∀ σ ∈ S, Set.range ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋j⦌)) σ) ⊆ K := by
    intro σ hσ
    rw [hKdef]
    exact Set.subset_biUnion_of_mem (s := (S : Set (TopCat.toSSet.obj (TopCat.of X) _⦋j⦌)))
      (u := fun σ => Work.Cohomology.simplexRange (TopCat.of X) σ) hσ
  let w : (Work.Cohomology.singularChains ℚ (TopCat.of ↥K)).X j :=
    ∑ x ∈ S.attach, (coordsQ (TopCat.toSSet.obj (TopCat.of X)) j c x.1) •
      Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of ↥K))
        (liftSimplex K x.1 (hsub x.1 x.2))
  refine ⟨K, hKc, w, ?_⟩
  have hA : (Work.Cohomology.chainMap ℚ (TopCat.of ↥K) (TopCat.of X)
      (TopCat.ofHom (Work.RatHurewicz.setIncl K))).f j w
      = ∑ x ∈ S.attach, (coordsQ (TopCat.toSSet.obj (TopCat.of X)) j c x.1) •
          Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of X)) x.1 := by
    rw [show w = ∑ x ∈ S.attach, (coordsQ (TopCat.toSSet.obj (TopCat.of X)) j c x.1) •
      Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of ↥K))
        (liftSimplex K x.1 (hsub x.1 x.2)) from rfl]
    rw [show Work.Cohomology.chainMap ℚ (TopCat.of ↥K) (TopCat.of X)
        (TopCat.ofHom (Work.RatHurewicz.setIncl K))
        = SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (Work.RatHurewicz.setIncl K)))
            (ModuleCat.of ℚ ℚ) from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [map_smul]
    congr 1
    refine (genElt_chainComplexMapQ (TopCat.toSSet.map (TopCat.ofHom (Work.RatHurewicz.setIncl K))) j
      (liftSimplex K x.1 (hsub x.1 x.2))).trans ?_
    rw [map_liftSimplex]
  rw [hA, Finset.sum_attach S (fun σ => (coordsQ (TopCat.toSSet.obj (TopCat.of X)) j c σ) •
      Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of X)) σ)]
  exact hsum.symm

end

end Work.StemsB
