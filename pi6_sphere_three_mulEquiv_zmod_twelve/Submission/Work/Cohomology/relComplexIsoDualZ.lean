import Mathlib
import Submission.Work.Cohomology.dualZ
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.linSimplex_boundary

/-!
# The relative cochain complex with coefficients in `R` is the `ℤ`-dual of the relative chain
complex

For a topological space `X` and a subset `A ⊆ X` the relative singular cochains with coefficients
in a commutative ring `R` are the kernel of the restriction `C^*(X;R) ⟶ C^*(A;R)`, while the
relative singular chains `C_*(X,A;ℤ)` are the cokernel of the inclusion `C_*(A;ℤ) ⟶ C_*(X;ℤ)`.
Since `Hom_ℤ(-, R)` carries cokernels of `ℤ`-modules to kernels, the two complexes agree:

`C^*(X,A;R) ≅ Hom_ℤ(C_*(X,A;ℤ), R) = dualZ R (relChains X A)`.

The proof has two layers.

* **Coefficient comparison.**  The singular `n`-chains are the coproduct of one copy of the
  coefficient ring per singular `n`-simplex (`SSet.isColimitChainComplexXCofan`), so a `ℤ`-linear
  functional on `C_n(X;ℤ)` is the same thing as an `R`-linear functional on `C_n(X;R)`: both are
  determined by their values on the generators `1 • σ`.  This is `cochCoeffEquiv`, and it is
  compatible both with the differentials (`cochCoeffEquiv_comm_d`) and with continuous maps
  (`cochCoeffEquiv_natural`).
* **Left exactness of `Hom`.**  The quotient map `p_n : C_n(X;ℤ) ⟶ C_n(X,A;ℤ)` is surjective with
  kernel the (split) image of `C_n(A;ℤ)`, so `Hom_ℤ(C_n(X,A), R) ≅ ker (p_n)^T`, which under the
  coefficient comparison is exactly `C^n(X,A;R)`.

## Main result

* `Work.Cohomology.relComplexIsoDualZ` — `C^*(X,A;R) ≅ dualZ R (C_*(X,A;ℤ))`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-! ## Generators of the singular chains

The singular `n`-chains of `X` with coefficients in a ring are the coproduct of one copy of the
coefficient ring for each singular `n`-simplex (`SSet.isColimitChainComplexXCofan`), so the chains
`1 • σ` generate.  We record the generators, the functionals with prescribed values on them, and
the resulting extensionality principle. -/

/-- The generator `1 • σ` of the `ℤ`-chains of `X`. -/
def genZ (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) : (singularChains ℤ X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ (1 : ℤ)

/-- The generator `1 • σ` of the `R`-chains of `X`. -/
def genR (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) : (singularChains R X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ (1 : R)

/-- The `R`-linear functional on the `R`-chains of `X` with prescribed values on the generators. -/
def mkDualR (X : TopCat) (n : ℕ) (v : (TopCat.toSSet.obj X) _⦋n⦌ → R) :
    (singularChains R X).X n →ₗ[R] R :=
  ModuleCat.Hom.hom
    (Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of R R) n)
      (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton R R (v σ))))

/-- The `ℤ`-linear functional on the `ℤ`-chains of `X` with prescribed values on the
generators. -/
def mkDualZ (X : TopCat) (n : ℕ) (v : (TopCat.toSSet.obj X) _⦋n⦌ → R) :
    (singularChains ℤ X).X n →ₗ[ℤ] R :=
  ModuleCat.Hom.hom
    (Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
      (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ R (v σ))))

lemma mkDualR_gen (X : TopCat) (n : ℕ) (v : (TopCat.toSSet.obj X) _⦋n⦌ → R)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    mkDualR R X n v (genR R X n σ) = v σ := by
  have h := Cofan.IsColimit.fac
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton R R (v σ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom (1 : R)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] at h2
  exact h2

lemma mkDualZ_gen (X : TopCat) (n : ℕ) (v : (TopCat.toSSet.obj X) _⦋n⦌ → R)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    mkDualZ R X n v (genZ X n σ) = v σ := by
  have h := Cofan.IsColimit.fac
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ R (v σ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ R) => g.hom (1 : ℤ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] at h2
  exact h2

/-- The `R`-linear functionals on the `R`-chains are determined by their values on the
generators. -/
lemma singularFunc_ext_R (X : TopCat) (n : ℕ) {f g : (singularChains R X).X n →ₗ[R] R}
    (h : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌, f (genR R X n σ) = g (genR R X n σ)) : f = g := by
  have h' : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact h σ
  have h2 := congrArg ModuleCat.Hom.hom h'
  simpa only [ModuleCat.hom_ofHom] using h2

/-- The `ℤ`-linear functionals on the `ℤ`-chains with values in `R` are determined by their values
on the generators. -/
lemma singularFunc_ext_Z (X : TopCat) (n : ℕ)
    {f g : (singularChains ℤ X).X n →ₗ[ℤ] R}
    (h : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌, f (genZ X n σ) = g (genZ X n σ)) : f = g := by
  have h' : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact h σ
  have h2 := congrArg ModuleCat.Hom.hom h'
  simpa only [ModuleCat.hom_ofHom] using h2

/-! ## The comparison of coefficients

A `ℤ`-linear functional on the `ℤ`-chains with values in `R` is the same thing as an `R`-linear
functional on the `R`-chains: both are given by an arbitrary function on the set of simplices. -/

/-- **The comparison of coefficients**: functionals on the `ℤ`-chains with values in `R` are
functionals on the `R`-chains. -/
def cochCoeffEquiv (X : TopCat) (n : ℕ) :
    ((singularChains ℤ X).X n →ₗ[ℤ] R) ≃ₗ[R] ((singularChains R X).X n →ₗ[R] R) where
  toFun φ := mkDualR R X n (fun σ => φ (genZ X n σ))
  invFun ψ := mkDualZ R X n (fun σ => ψ (genR R X n σ))
  left_inv φ := by
    apply singularFunc_ext_Z
    intro σ
    rw [mkDualZ_gen, mkDualR_gen]
  right_inv ψ := by
    apply singularFunc_ext_R
    intro σ
    rw [mkDualR_gen, mkDualZ_gen]
  map_add' φ ψ := by
    apply singularFunc_ext_R
    intro σ
    simp only [LinearMap.add_apply, mkDualR_gen]
  map_smul' r φ := by
    apply singularFunc_ext_R
    intro σ
    simp [LinearMap.smul_apply, mkDualR_gen]

/-- The value of `cochCoeffEquiv` on the generators of the `R`-chains. -/
lemma cochCoeffEquiv_apply_gen (X : TopCat) (n : ℕ) (φ : (singularChains ℤ X).X n →ₗ[ℤ] R)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    cochCoeffEquiv R X n φ (genR R X n σ) = φ (genZ X n σ) :=
  mkDualR_gen R X n _ σ

/-- The value of the inverse of `cochCoeffEquiv` on the generators of the `ℤ`-chains. -/
lemma cochCoeffEquiv_symm_apply_gen (X : TopCat) (n : ℕ)
    (ψ : (singularChains R X).X n →ₗ[R] R) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (cochCoeffEquiv R X n).symm ψ (genZ X n σ) = ψ (genR R X n σ) :=
  mkDualZ_gen R X n _ σ

/-! ### Compatibility with the differentials and with continuous maps -/

/-- The boundary of the generator `1 • σ` of the `ℤ`-chains. -/
lemma d_genZ (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    (singularChains ℤ X).d (n+1) n (genZ X (n+1) σ)
      = ∑ i : Fin (n+2), ((-1 : ℤ) ^ (i : ℕ)) • genZ X n ((TopCat.toSSet.obj X).δ i σ) :=
  chainComplex_d_ι_apply ℤ (X := TopCat.toSSet.obj X) (n := n) σ

/-- The boundary of the generator `1 • σ` of the `R`-chains. -/
lemma d_genR (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    (singularChains R X).d (n+1) n (genR R X (n+1) σ)
      = ∑ i : Fin (n+2), ((-1 : ℤ) ^ (i : ℕ)) • genR R X n ((TopCat.toSSet.obj X).δ i σ) :=
  chainComplex_d_ι_apply R (X := TopCat.toSSet.obj X) (n := n) σ

/-- The chain map induced by a continuous map on a generator of the `ℤ`-chains. -/
lemma genZ_chainMap {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (chainMap ℤ X Y f).f n (genZ X n σ)
      = genZ Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) σ) := by
  have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (singularChains ℤ Y).X n) => g.hom (1 : ℤ))
    (SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map f) (R := ModuleCat.of ℤ ℤ) (x := σ))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, genZ] at h ⊢
  exact h

/-- The chain map induced by a continuous map on a generator of the `R`-chains. -/
lemma genR_chainMap {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (chainMap R X Y f).f n (genR R X n σ)
      = genR R Y n ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) σ) := by
  have h := congrArg (fun (g : ModuleCat.of R R ⟶ (singularChains R Y).X n) => g.hom (1 : R))
    (SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map f) (R := ModuleCat.of R R) (x := σ))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, genR] at h ⊢
  exact h

/-- **The comparison of coefficients commutes with the differentials.** -/
lemma cochCoeffEquiv_comm_d (X : TopCat) (n : ℕ)
    (φ : (singularChains ℤ X).X n →ₗ[ℤ] R) :
    cochCoeffEquiv R X (n+1) (φ.comp ((singularChains ℤ X).d (n+1) n).hom)
      = (cochCoeffEquiv R X n φ).comp ((singularChains R X).d (n+1) n).hom := by
  apply singularFunc_ext_R
  intro σ
  rw [LinearMap.comp_apply, cochCoeffEquiv_apply_gen, LinearMap.comp_apply]
  rw [d_genZ, d_genR]
  simp only [map_sum, map_zsmul, cochCoeffEquiv_apply_gen]

/-- **The comparison of coefficients is natural** with respect to continuous maps. -/
lemma cochCoeffEquiv_natural {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (ψ : (singularChains ℤ Y).X n →ₗ[ℤ] R) :
    cochCoeffEquiv R X n (ψ.comp ((chainMap ℤ X Y f).f n).hom)
      = (cochCoeffEquiv R Y n ψ).comp ((chainMap R X Y f).f n).hom := by
  apply singularFunc_ext_R
  intro σ
  rw [LinearMap.comp_apply, cochCoeffEquiv_apply_gen, LinearMap.comp_apply,
    genZ_chainMap f n σ, genR_chainMap R f n σ, cochCoeffEquiv_apply_gen]

/-! ## The relative cochain complex is the dual of the relative chain complex -/

section rel

variable (X : TopCat) (A : Set X)

/-- An element of the cochain module of `X`, viewed as a functional on chains. -/
def cochainLM (n : ℕ) (φ : ↥((singularCochainComplex R X).X n)) :
    (singularChains R X).X n →ₗ[R] R := φ

/-- The composite `C_n(A;ℤ) ⟶ C_n(X;ℤ) ⟶ C_n(X,A;ℤ)` vanishes. -/
lemma relDualProj_comp_incl (n : ℕ) :
    (relDualProj X A n).hom.comp ((inclChains X A).f n).hom = 0 := by
  apply LinearMap.ext
  intro y
  simpa using relDualProj_incl_apply X A n y

/-- The restriction map on relative cochains, evaluated: it is composition with the chain map
induced by the inclusion `A ⊆ X`. -/
lemma restr_f_apply (n : ℕ) (Θ : (singularCochainComplex R X).X n) :
    ((restr R X A).f n).hom Θ
      = Θ.comp ((chainMap R (TopCat.of A) X (subtypeIncl X A)).f n).hom := rfl

/-- The differential of the relative cochains, evaluated on a chain. -/
lemma relDiff_apply (n : ℕ) (Θ : ↥(relKern R X A n))
    (x : (singularChains R X).X (n+1)) :
    cochainLM R X (n+1) (relDiff R X A n Θ).1 x
      = cochainLM R X n Θ.1 (((singularChains R X).d (n+1) n).hom x) := by
  rw [show (relDiff R X A n Θ).1 = (relDiffLM R X A n Θ).1 from rfl, relDiffLM_coe]
  rw [show (singularCochainComplex R X).d n (n+1) = dualDifferential R X n from
    CochainComplex.of_d (dualChains R X) (dualDifferential R X) n]
  rfl

/-- The differential of the relative cochains, as composition with the differential of the
chains. -/
lemma relDiff_coe (n : ℕ) (Θ : ↥(relKern R X A n)) :
    cochainLM R X (n+1) (relDiff R X A n Θ).1
      = (cochainLM R X n Θ.1).comp ((singularChains R X).d (n+1) n).hom :=
  LinearMap.ext fun x => relDiff_apply R X A n Θ x

/-- **The degreewise map** from `Hom_ℤ(C_n(X,A), R)` to `C^n(X,A;R)`: precomposition with the
quotient map `p_n : C_n(X;ℤ) ⟶ C_n(X,A;ℤ)`, transported across the coefficient comparison. -/
def relZLM (n : ℕ) : ((relChains X A).X n →ₗ[ℤ] R) →ₗ[R] ↥(relKern R X A n) :=
  (((cochCoeffEquiv R X n).toLinearMap).comp
      (LinearMap.lcomp R R (relDualProj X A n).hom)).codRestrict (relKern R X A n) (by
    intro φ
    rw [relKern, LinearMap.mem_ker]
    show ((restr R X A).f n).hom
      (cochCoeffEquiv R X n (LinearMap.lcomp R R (relDualProj X A n).hom φ)) = 0
    rw [restr_f_apply R X A n]
    rw [← cochCoeffEquiv_natural R (subtypeIncl X A) n
      (LinearMap.lcomp R R (relDualProj X A n).hom φ)]
    have hz : (LinearMap.lcomp R R (relDualProj X A n).hom φ).comp
        ((chainMap ℤ (TopCat.of A) X (subtypeIncl X A)).f n).hom = 0 := by
      rw [LinearMap.lcomp_apply', LinearMap.comp_assoc, relDualProj_comp_incl,
        LinearMap.comp_zero]
    rw [hz, map_zero])

/-- The value of `relZLM`: it is the coefficient comparison of `φ ∘ p_n`. -/
lemma relZLM_apply (n : ℕ) (φ : (relChains X A).X n →ₗ[ℤ] R) :
    (relZLM R X A n φ).1
      = cochCoeffEquiv R X n (φ.comp (relDualProj X A n).hom) := rfl

/-- `relZLM` is injective, since `p_n` is surjective. -/
lemma relZLM_injective (n : ℕ) : Function.Injective (relZLM R X A n) := by
  intro φ ψ h
  have h2 : cochCoeffEquiv R X n (φ.comp (relDualProj X A n).hom)
      = cochCoeffEquiv R X n (ψ.comp (relDualProj X A n).hom) := by
    have hh := congrArg Subtype.val h
    rwa [relZLM_apply, relZLM_apply] at hh
  have h3 : LinearMap.lcomp R R (relDualProj X A n).hom φ
      = LinearMap.lcomp R R (relDualProj X A n).hom ψ := by
    rw [LinearMap.lcomp_apply', LinearMap.lcomp_apply']
    exact (cochCoeffEquiv R X n).injective h2
  exact LinearMap.lcomp_injective_of_surjective (S := R) (N := R) (relDualProj X A n).hom
    (relDualProj_surjective X A n) h3

/-- `relZLM` is surjective: a relative cochain vanishes on the chains of `A`, so it factors
through the quotient map.  This is the left exactness of `Hom_ℤ(-, R)`. -/
lemma relZLM_surjective (n : ℕ) : Function.Surjective (relZLM R X A n) := by
  intro Θ
  have hΘ : ((restr R X A).f n).hom (Θ : (singularCochainComplex R X).X n) = 0 := by
    simpa only [relKern, LinearMap.mem_ker] using Θ.2
  set ψ : (singularChains ℤ X).X n →ₗ[ℤ] R := (cochCoeffEquiv R X n).symm Θ.1
  have hΦψ : cochCoeffEquiv R X n ψ = Θ.1 := (cochCoeffEquiv R X n).apply_symm_apply Θ.1
  have hzero : ψ.comp ((chainMap ℤ (TopCat.of A) X (subtypeIncl X A)).f n).hom = 0 := by
    apply (cochCoeffEquiv R (TopCat.of A) n).injective
    rw [(cochCoeffEquiv R (TopCat.of A) n).map_zero]
    rw [cochCoeffEquiv_natural R (subtypeIncl X A) n ψ, hΦψ,
      ← restr_f_apply R X A n Θ.1, hΘ]
  have hmem : ψ ∈ Set.range (⇑(LinearMap.lcomp ℤ R (relDualProj X A n).hom)) :=
    (LinearMap.exact_lcomp_of_exact_of_surjective (N := R) (relDualProj_exact X A n)
      (relDualProj_surjective X A n) ψ).1 (by
        rw [LinearMap.lcomp_apply']
        exact hzero)
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨φ, ?_⟩
  apply Subtype.ext
  rw [relZLM_apply,
    ← LinearMap.lcomp_apply' (S := ℤ) (N := R) (relDualProj X A n).hom φ, hφ, hΦψ]

/-- **The degreewise isomorphism** `Hom_ℤ(C_n(X,A), R) ≃ C^n(X,A;R)`. -/
def relZEquiv (n : ℕ) : ((relChains X A).X n →ₗ[ℤ] R) ≃ₗ[R] ↥(relKern R X A n) :=
  LinearEquiv.ofBijective (relZLM R X A n)
    ⟨relZLM_injective R X A n, relZLM_surjective R X A n⟩

/-- The underlying linear map of `relZEquiv` is `relZLM`. -/
lemma relZEquiv_apply (n : ℕ) (φ : (relChains X A).X n →ₗ[ℤ] R) :
    (relZEquiv R X A n φ : ↥(relKern R X A n)) = relZLM R X A n φ :=
  LinearEquiv.ofBijective_apply _ φ

/-- The value of `relZEquiv`. -/
lemma relZEquiv_apply_coe (n : ℕ) (φ : (relChains X A).X n →ₗ[ℤ] R) :
    (relZEquiv R X A n φ).1
      = cochCoeffEquiv R X n (φ.comp (relDualProj X A n).hom) := by
  rw [relZEquiv_apply, relZLM_apply]

/-- **The differentials of the relative cochains and of the dual of the relative chains
correspond** under `relZEquiv`. -/
lemma relZEquiv_comm_apply (n : ℕ) (φ : (relChains X A).X n →ₗ[ℤ] R) :
    relZEquiv R X A (n+1) ((dualZDiff R (relChains X A) n) φ)
      = (relDiff R X A n) (relZEquiv R X A n φ) := by
  apply Subtype.ext
  show cochainLM R X (n+1) ((relZEquiv R X A (n+1) ((dualZDiff R (relChains X A) n) φ)).1)
      = cochainLM R X (n+1) ((relDiff R X A n (relZEquiv R X A n φ)).1)
  apply singularFunc_ext_R
  intro σ
  have hL : cochainLM R X (n+1)
        ((relZEquiv R X A (n+1) ((dualZDiff R (relChains X A) n) φ)).1)
        (genR R X (n+1) σ)
      = φ (((relChains X A).d (n+1) n).hom
          ((relDualProj X A (n+1)).hom (genZ X (n+1) σ))) := by
    simp only [cochainLM, relZEquiv_apply_coe, cochCoeffEquiv_apply_gen, LinearMap.comp_apply]
    exact dualZDiff_apply R (relChains X A) n φ
      ((relDualProj X A (n+1)).hom (genZ X (n+1) σ))
  have hR : cochainLM R X (n+1) ((relDiff R X A n (relZEquiv R X A n φ)).1)
        (genR R X (n+1) σ)
      = φ (((relChains X A).d (n+1) n).hom
          ((relDualProj X A (n+1)).hom (genZ X (n+1) σ))) := by
    have hkey : ((relChains X A).d (n+1) n).hom ((relDualProj X A (n+1)).hom (genZ X (n+1) σ))
        = (relDualProj X A n).hom
          (((singularChains ℤ X).d (n+1) n).hom (genZ X (n+1) σ)) :=
      LinearMap.congr_fun (relDualProj_comm_lm X A n) (genZ X (n+1) σ)
    rw [relDiff_apply, relZEquiv_apply_coe]
    simp only [cochainLM]
    rw [← LinearMap.comp_apply,
      ← cochCoeffEquiv_comm_d R X n (φ.comp (relDualProj X A n).hom),
      cochCoeffEquiv_apply_gen, LinearMap.comp_apply, LinearMap.comp_apply, ← hkey]
  rw [hL, hR]

end rel

section iso

variable (X : TopCat) (A : Set X)

/-- The degreewise isomorphism `Hom_ℤ(C_n(X,A), R) ≅ C^n(X,A;R)`, as an isomorphism of
cochain complexes. -/
def relZIso (n : ℕ) :
    (dualZ R (relChains X A)).X n ≅ (relComplex R X A).X n :=
  LinearEquiv.toModuleIso (relZEquiv R X A n)

/-- The forward map of `relZIso` is `relZEquiv`. -/
@[simp]
lemma relZIso_hom (n : ℕ) :
    (relZIso R X A n).hom = ModuleCat.ofHom ((relZEquiv R X A n) :
      ((relChains X A).X n →ₗ[ℤ] R) →ₗ[R] ↥(relKern R X A n)) := rfl

/-- **The degreewise isomorphisms commute with the differentials.** -/
lemma relZIso_comm (n : ℕ) :
    (relZIso R X A n).hom ≫ (relComplex R X A).d n (n+1)
      = (dualZ R (relChains X A)).d n (n+1) ≫ (relZIso R X A (n+1)).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, relZIso_hom, ModuleCat.hom_ofHom,
    relComplex_d, dualZ_d]
  exact (relZEquiv_comm_apply R X A n φ).symm

/-- **The relative cochain complex with coefficients in `R` is the `ℤ`-dual of the relative chain
complex.** -/
theorem relComplexIsoDualZ (R : Type) [CommRing R] (X : TopCat) (A : Set X) :
    Nonempty (Work.Cohomology.relComplex R X A ≅
      Work.Cohomology.dualZ R (Work.Cohomology.relChains X A)) :=
  ⟨(HomologicalComplex.Hom.isoOfComponents (fun n => relZIso R X A n)
    (fun i j hij => by
      rw [← hij]
      exact relZIso_comm R X A i)).symm⟩

end iso

end

end Work.Cohomology
