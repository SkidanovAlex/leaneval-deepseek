import Mathlib
import Submission.Work.Cohomology.CapProduct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Naturality of the cap product

The cap product `⌢` is natural with respect to maps of simplicial sets: for `f : X ⟶ Y`,
a cochain `α` of degree `n` on `Y` and a chain `c` of degree `n + m` on `X`,

  `f_*(c ⌢ f*α) = (f_* c) ⌢ α`,

where `f_*` denotes the map induced by `f` on singular chains (`(chainComplexMap f R).f _`)
and `f*α = α ∘ (chainComplexMap f R).f n` the pullback of the cochain `α`.

The proof is by the usual computation on generators: on a singular simplex `σ` the identity
reads `α(f σ_front) • f_* σ_back = α((f σ)_front) • (f σ)_back`, which is `genEval` naturality
together with the commutation of the front/back faces with `f` (`app_frontFace`, `app_backFace`).
The auxiliary lemma `capNatChainExt` records that a linear map on `n`-chains is determined by
its values on the generators `ιChainComplex σ` (which jointly present the chains as a coproduct).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- A linear map on the `N`-chains of a simplicial set `X` (with values in the `m`-chains of a
simplicial set `Y`) is determined by its values on the generators `ιChainComplex σ`, i.e. on
`1` in each summand of the coproduct presentation of the chains. -/
lemma capNatChainExt (R : Type) [CommRing R] {X Y : SSet} {N m : ℕ}
    {f g : (↑((X.chainComplex (ModuleCat.of R R)).X N)) →ₗ[R]
      (↑((Y.chainComplex (ModuleCat.of R R)).X m))}
    (h : ∀ σ : X _⦋N⦌, f ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
      = g ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) : f = g := by
  have key : (ModuleCat.ofHom f : (X.chainComplex (ModuleCat.of R R)).X N
        ⟶ (Y.chainComplex (ModuleCat.of R R)).X m)
      = (ModuleCat.ofHom g : (X.chainComplex (ModuleCat.of R R)).X N
        ⟶ (Y.chainComplex (ModuleCat.of R R)).X m) := by
    apply SSet.chainComplex_hom_ext (C := ModuleCat R)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    have hr : (X.ιChainComplex (R := ModuleCat.of R R) σ).hom r
        = r • (X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1 := by
      simpa using LinearMap.map_smul (X.ιChainComplex (R := ModuleCat.of R R) σ).hom r (1 : R)
    rw [hr, map_smul, map_smul]
    exact congrArg (fun z => r • z) (h σ)
  simpa only [ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom key

/-- The chain map induced by `f : X ⟶ Y` sends the generator of a simplex `τ` to the generator
of its image `f τ`. -/
lemma chainComplexMap_ιChainComplex_apply (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y)
    {k : ℕ} (τ : X _⦋k⦌) :
    ((SSet.chainComplexMap f (ModuleCat.of R R)).f k).hom
        ((X.ιChainComplex (R := ModuleCat.of R R) τ).hom 1)
      = (Y.ιChainComplex (R := ModuleCat.of R R) (f.app _ τ)).hom 1 := by
  have h := congrArg (fun (g : ModuleCat.of R R ⟶ (Y.chainComplex (ModuleCat.of R R)).X k) =>
      g.hom 1) (SSet.ι_chainComplexMap_f (X := X) (Y := Y) f (ModuleCat.of R R) τ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The cap product is natural with respect to maps of simplicial sets:
`f_*(c ⌢ f*α) = (f_* c) ⌢ α`. -/
theorem cap_natural (R : Type) [CommRing R] {X Y : SSet} (f : X ⟶ Y) {n m : ℕ}
    (α : Work.Cohomology.Cochain R Y n) (c : (X.chainComplex (ModuleCat.of R R)).X (n + m)) :
    ((SSet.chainComplexMap f (ModuleCat.of R R)).f m).hom
        (Work.Cohomology.cap R X (α.comp ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom) m c) =
      Work.Cohomology.cap R Y α m (((SSet.chainComplexMap f (ModuleCat.of R R)).f (n + m)).hom c) := by
  -- the identity on a generator
  have key : ∀ σ : X _⦋n + m⦌,
      ((SSet.chainComplexMap f (ModuleCat.of R R)).f m).hom
          (Work.Cohomology.cap R X (α.comp ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom) m
            (((X.ιChainComplex (R := ModuleCat.of R R)) σ).hom 1)) =
      Work.Cohomology.cap R Y α m
        (((SSet.chainComplexMap f (ModuleCat.of R R)).f (n + m)).hom
          (((X.ιChainComplex (R := ModuleCat.of R R)) σ).hom 1)) := by
    intro σ
    have hfgen : ∀ {k : ℕ} (τ : X _⦋k⦌),
        ((SSet.chainComplexMap f (ModuleCat.of R R)).f k).hom
            ((X.ιChainComplex (R := ModuleCat.of R R) τ).hom 1)
          = (Y.ιChainComplex (R := ModuleCat.of R R) (f.app _ τ)).hom 1 :=
      fun τ => chainComplexMap_ιChainComplex_apply R f τ
    have hgen : ∀ (τ : X _⦋n⦌),
        genEval R X (α.comp ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom) τ
          = genEval R Y α (f.app _ τ) := by
      intro τ
      rw [show α.comp ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom
          = ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap α from rfl]
      exact genEval_dualMap R f α τ
    rw [cap_apply R X (α.comp ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom) σ,
      map_smul, hfgen, hgen, app_frontFace f, app_backFace f, hfgen]
    rw [cap_apply R Y α (f.app _ σ)]
  -- lift to all chains by the coproduct universal property
  have hmap : ((SSet.chainComplexMap f (ModuleCat.of R R)).f m).hom.comp
        (Work.Cohomology.cap R X (α.comp ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom) m)
      = (Work.Cohomology.cap R Y α m).comp
        ((SSet.chainComplexMap f (ModuleCat.of R R)).f (n + m)).hom := by
    apply capNatChainExt R
    intro σ
    exact key σ
  exact LinearMap.congr_fun hmap c

end

end Work.Cohomology
