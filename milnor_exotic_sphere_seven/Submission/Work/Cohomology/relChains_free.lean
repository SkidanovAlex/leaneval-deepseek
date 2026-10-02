import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.relChainsProjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative singular chains are degreewise free

For a topological space `X`, a subset `A ⊆ X` and `n : ℕ`, the relative singular `n`-chains
`C_n(X,A)` — the cokernel of the inclusion `C_n(A) ⟶ C_n(X)` of chain complexes — form a **free**
`ℤ`-module (`relChains_free`).

The proof identifies `C_n(X,A)` with the free module on the `n`-simplices of `X` which do **not**
come from `A`.  Writing `s_n : Simplex (TopCat.of A) n → Simplex X n` for the map induced by the
inclusion `A ⊆ X` on `n`-simplices and

`OutSimplex X A n = {y : Simplex X n // y ∉ range s_n}`

for the complementary simplices, the statement is that

`C_n(X,A) ≅ ⨁_{y ∈ OutSimplex} ℤ`.

The two maps realising this are

* `relCoeff : C_n(X) ⟶ ⨁_{OutSimplex} ℤ`, which on the generator of a simplex `y` returns the
  basis vector of `y` if `y` comes from `A`... more precisely returns `0` if `y` comes from `A`
  and the basis vector of `y` otherwise (so that it descends to the cokernel), and
* `relPsiCoker : ⨁_{OutSimplex} ℤ ⟶ C_n(X,A)`, which sends the basis vector of `y` to the class
  of the generator of `y`,

and they are mutually inverse.  The only two inputs about singular chains are

* a morphism out of `C_n(X)` is determined by its values on the generators `gen X n y`
  (`genLift`, `genLift_gen`), and
* a submodule containing all generators is everything (`Work.Cohomology.mem_of_gen`).

## Main results

* `relCoeff`, `relPhiCoker`, `relPsiCoker` — the two comparison maps and their composites.
* `relIso` — the isomorphism `C_n(X,A) ≅ ⨁_{OutSimplex X A n} ℤ`.
* `relChains_free` — `C_n(X,A)` is a free `ℤ`-module.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial
open Classical

namespace Work.Cohomology

noncomputable section

/-! ## Prescribing morphisms out of the singular chains on generators -/

/-- A morphism out of the singular `n`-chains of `X` into `M`, prescribed on the generators of
simplices: `genLift X n v` sends the generator of a simplex `σ` to `v σ`. -/
def genLift (X : TopCat) (n : ℕ) {M : ModuleCat ℤ} (v : Simplex X n → M) :
    (singularChains ℤ X).X n ⟶ M :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (v σ)))

lemma genLift_gen (X : TopCat) (n : ℕ) {M : ModuleCat ℤ} (v : Simplex X n → M)
    (σ : Simplex X n) : (genLift X n v).hom (gen X n σ) = v σ := by
  have h := Cofan.IsColimit.fac
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (v σ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ M) => g.hom (1 : ℤ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  rw [genLift, gen]
  exact h2

/-! ## The chain map on generators and the complementary simplices -/

/-- The map induced by `A ⊆ X` on singular `n`-simplices. -/
def simplexMap (X : TopCat) (A : Set X) (n : ℕ) : Simplex (TopCat.of A) n → Simplex X n :=
  (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op (SimplexCategory.mk n))

/-- The singular `n`-simplices of `X` which do not come from `A`. -/
abbrev OutSimplex (X : TopCat) (A : Set X) (n : ℕ) :=
  {y : Simplex X n // y ∉ Set.range (simplexMap X A n)}

/-- The inclusion `C_n(A) ⟶ C_n(X)` on generators of simplices. -/
lemma inclChains_gen (X : TopCat) (A : Set X) (n : ℕ) (σ : Simplex (TopCat.of A) n) :
    (((inclChains X A).f n).hom) (gen (TopCat.of A) n σ) = gen X n (simplexMap X A n σ) := by
  have h2 := congrArg ModuleCat.Hom.hom (SSet.ι_chainComplexMap_f
    (TopCat.toSSet.obj (TopCat.of A)) (TopCat.toSSet.obj X) (TopCat.toSSet.map (subtypeIncl X A))
    (ModuleCat.of ℤ ℤ) σ)
  rw [ModuleCat.hom_comp] at h2
  simp only [inclChains, chainMap_f_eq, gen]
  exact LinearMap.congr_fun h2 1

/-- The class in `C_n(X,A)` of a chain coming from `A` vanishes. -/
lemma coker_π_f_apply (X : TopCat) (A : Set X) (n : ℕ)
    (w : (singularChains ℤ (TopCat.of A)).X n) :
    (cokernel.π ((inclChains X A).f n)).hom ((((inclChains X A).f n).hom) w) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (cokernel.condition ((inclChains X A).f n))
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact LinearMap.congr_fun h w

/-! ## The two comparison maps -/

/-- The projection of the `n`-chains of `X` onto the simplices which do not come from `A`. -/
def relCoeff (X : TopCat) (A : Set X) (n : ℕ) :
    (singularChains ℤ X).X n ⟶ ModuleCat.of ℤ (OutSimplex X A n →₀ ℤ) :=
  genLift X n (fun y : Simplex X n =>
    if h : y ∉ Set.range (simplexMap X A n) then
      (Finsupp.single ⟨y, h⟩ (1 : ℤ) : OutSimplex X A n →₀ ℤ) else 0)

lemma relCoeff_gen (X : TopCat) (A : Set X) (n : ℕ) (y : Simplex X n) :
    (relCoeff X A n).hom (gen X n y)
      = if h : y ∉ Set.range (simplexMap X A n) then
          (Finsupp.single ⟨y, h⟩ (1 : ℤ) : OutSimplex X A n →₀ ℤ) else 0 :=
  genLift_gen X n _ y

/-- The projection kills the chains coming from `A`. -/
lemma relCoeff_inclChains (X : TopCat) (A : Set X) (n : ℕ) :
    (inclChains X A).f n ≫ relCoeff X A n = 0 := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  rw [← LinearMap.ker_eq_top]
  apply mem_of_gen (TopCat.of A) n
  intro σ
  rw [LinearMap.mem_ker]
  change (relCoeff X A n).hom ((((inclChains X A).f n).hom) (gen (TopCat.of A) n σ)) = 0
  rw [inclChains_gen X A n σ, relCoeff_gen X A n (simplexMap X A n σ),
    dif_neg (by simp : ¬ (simplexMap X A n σ ∉ Set.range (simplexMap X A n)))]

/-- The comparison map `C_n(X,A) ⟶ ⨁_{OutSimplex} ℤ`. -/
def relPhiCoker (X : TopCat) (A : Set X) (n : ℕ) :
    cokernel ((inclChains X A).f n) ⟶ ModuleCat.of ℤ (OutSimplex X A n →₀ ℤ) :=
  cokernel.desc ((inclChains X A).f n) (relCoeff X A n) (relCoeff_inclChains X A n)

lemma relPhiCoker_π (X : TopCat) (A : Set X) (n : ℕ) :
    cokernel.π ((inclChains X A).f n) ≫ relPhiCoker X A n = relCoeff X A n :=
  cokernel.π_desc _ _ _

lemma relPhiCoker_gen (X : TopCat) (A : Set X) (n : ℕ) (y : Simplex X n) :
    (relPhiCoker X A n).hom ((cokernel.π ((inclChains X A).f n)).hom (gen X n y))
      = if h : y ∉ Set.range (simplexMap X A n) then
          (Finsupp.single ⟨y, h⟩ (1 : ℤ) : OutSimplex X A n →₀ ℤ) else 0 := by
  have h := congrArg ModuleCat.Hom.hom (relPhiCoker_π X A n)
  rw [ModuleCat.hom_comp] at h
  have h2 : (relPhiCoker X A n).hom ((cokernel.π ((inclChains X A).f n)).hom (gen X n y))
      = (relCoeff X A n).hom (gen X n y) := LinearMap.congr_fun h (gen X n y)
  rw [h2, relCoeff_gen X A n y]

/-- The inverse comparison map `⨁_{OutSimplex} ℤ ⟶ C_n(X,A)`. -/
def relPsiCoker (X : TopCat) (A : Set X) (n : ℕ) :
    ModuleCat.of ℤ (OutSimplex X A n →₀ ℤ) ⟶ cokernel ((inclChains X A).f n) :=
  ModuleCat.ofHom (Finsupp.linearCombination ℤ (fun y : OutSimplex X A n =>
    (cokernel.π ((inclChains X A).f n)).hom (gen X n y.1)))

lemma relPsiCoker_single (X : TopCat) (A : Set X) (n : ℕ) (y : OutSimplex X A n) (b : ℤ) :
    (relPsiCoker X A n).hom (Finsupp.single y b)
      = (LinearMap.toSpanSingleton ℤ _ ((cokernel.π ((inclChains X A).f n)).hom
          (gen X n y.1))) b := by
  rw [relPsiCoker]
  change (Finsupp.linearCombination ℤ (fun y : OutSimplex X A n =>
      (cokernel.π ((inclChains X A).f n)).hom (gen X n y.1))) (Finsupp.single y b)
    = (LinearMap.toSpanSingleton ℤ _ ((cokernel.π ((inclChains X A).f n)).hom (gen X n y.1))) b
  rw [Finsupp.linearCombination_single, LinearMap.toSpanSingleton_apply]

lemma relPsiCoker_single_one (X : TopCat) (A : Set X) (n : ℕ) (y : OutSimplex X A n) :
    (relPsiCoker X A n).hom (Finsupp.single y 1)
      = (cokernel.π ((inclChains X A).f n)).hom (gen X n y.1) := by
  rw [relPsiCoker_single, LinearMap.toSpanSingleton_apply_one]

lemma relPhiCoker_toSpanSingleton (X : TopCat) (A : Set X) (n : ℕ)
    (w : ↥(cokernel ((inclChains X A).f n))) :
    (relPhiCoker X A n).hom.comp (LinearMap.toSpanSingleton ℤ _ w)
      = LinearMap.toSpanSingleton ℤ _ ((relPhiCoker X A n).hom w) := by
  refine LinearMap.ext_ring ?_
  change (relPhiCoker X A n).hom ((LinearMap.toSpanSingleton ℤ _ w) 1)
    = (LinearMap.toSpanSingleton ℤ _ ((relPhiCoker X A n).hom w)) 1
  rw [LinearMap.toSpanSingleton_apply_one, LinearMap.toSpanSingleton_apply_one]

lemma relPhiCoker_toSpanSingleton_apply (X : TopCat) (A : Set X) (n : ℕ)
    (w : ↥(cokernel ((inclChains X A).f n))) (b : ℤ) :
    (relPhiCoker X A n).hom ((LinearMap.toSpanSingleton ℤ _ w) b)
      = (LinearMap.toSpanSingleton ℤ _ ((relPhiCoker X A n).hom w)) b :=
  congrFun (congrArg DFunLike.coe (relPhiCoker_toSpanSingleton X A n w)) b

/-! ## The two comparison maps are mutually inverse -/

lemma relPsiCoker_relPhiCoker_id (X : TopCat) (A : Set X) (n : ℕ) :
    relPsiCoker X A n ≫ relPhiCoker X A n = 𝟙 (ModuleCat.of ℤ (OutSimplex X A n →₀ ℤ)) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_id]
  refine Finsupp.lhom_ext (fun y b => ?_)
  change (relPhiCoker X A n).hom ((relPsiCoker X A n).hom (Finsupp.single y b))
    = Finsupp.single y b
  rw [relPsiCoker_single, relPhiCoker_toSpanSingleton_apply, relPhiCoker_gen, dif_pos y.2]
  change (LinearMap.toSpanSingleton ℤ _ (Finsupp.single y (1 : ℤ) : OutSimplex X A n →₀ ℤ)) b
    = Finsupp.single y b
  rw [LinearMap.toSpanSingleton_apply, Finsupp.smul_single, smul_eq_mul, mul_one]

lemma relPhiCoker_relPsiCoker_id (X : TopCat) (A : Set X) (n : ℕ) :
    relPhiCoker X A n ≫ relPsiCoker X A n = 𝟙 (cokernel ((inclChains X A).f n)) := by
  rw [← cancel_epi (cokernel.π ((inclChains X A).f n))]
  rw [Category.comp_id, ← Category.assoc, relPhiCoker_π]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp]
  have htop : LinearMap.ker (((relPsiCoker X A n).hom.comp (relCoeff X A n).hom) -
      (cokernel.π ((inclChains X A).f n)).hom) = ⊤ := by
    apply mem_of_gen X n
    intro σ
    rw [LinearMap.mem_ker]
    change (relPsiCoker X A n).hom ((relCoeff X A n).hom (gen X n σ))
      - (cokernel.π ((inclChains X A).f n)).hom (gen X n σ) = 0
    rw [relCoeff_gen X A n σ]
    by_cases h : σ ∉ Set.range (simplexMap X A n)
    · rw [dif_pos h, relPsiCoker_single_one, sub_self]
    · rw [dif_neg h, map_zero, zero_sub, neg_eq_zero]
      rw [not_not] at h
      obtain ⟨x, hx⟩ := h
      rw [← hx, ← inclChains_gen X A n x, coker_π_f_apply]
  have h0 : ((relPsiCoker X A n).hom.comp (relCoeff X A n).hom) -
      (cokernel.π ((inclChains X A).f n)).hom = 0 := by
    apply LinearMap.ext
    intro z
    have hz := Submodule.eq_top_iff'.mp htop z
    simpa [LinearMap.mem_ker] using hz
  exact sub_eq_zero.mp h0

/-! ## Freeness -/

/-- **The relative `n`-chains are free**: `C_n(X,A)` is isomorphic to the direct sum of one copy
of `ℤ` for each `n`-simplex of `X` which does not come from `A`. -/
def relIso (X : TopCat) (A : Set X) (n : ℕ) :
    (relChains X A).X n ≅ ModuleCat.of ℤ (OutSimplex X A n →₀ ℤ) :=
  relChains_cokernelIso X A n ≪≫
    Iso.mk (relPhiCoker X A n) (relPsiCoker X A n)
      (relPhiCoker_relPsiCoker_id X A n) (relPsiCoker_relPhiCoker_id X A n)

theorem relChains_free (X : TopCat) (A : Set X) (n : ℕ) :
    Module.Free ℤ ↥((Work.Cohomology.relChains X A).X n) :=
  Module.Free.of_equiv' (Module.Free.finsupp ℤ ℤ (OutSimplex X A n))
    (relIso X A n).toLinearEquiv.symm

end

end Work.Cohomology
