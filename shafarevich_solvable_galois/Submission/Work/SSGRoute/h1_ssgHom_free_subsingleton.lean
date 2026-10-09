import Mathlib
import Submission.Work.SSGRoute.SSGDescentDefs
import Submission.Work.SSGRoute.homCoind_H1_free_conj_v2
import Submission.Work.SSGRoute.subsingleton_H1_pi_inf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹_cont(Gal(Ω/k), Hom_ℤ(infl R, Ωˣ)) = 0` for `R` free on an arbitrary index set

This file proves `Work.SSGRoute.h1_ssgHom_free_subsingleton`, the vanishing of the continuous
first cohomology of `Γ = Gal(Ω/k)` with coefficients `Hom_ℤ(infl R, Ωˣ)`, where `R` is the
inflation `Rep.res (ssgResHom k Ω K) (Rep.free Coeff Gal(K/k) ι)` of a free `Coeff[Gal(K/k)]`-module
on an *arbitrary* (possibly infinite) index type `ι`, and `infl Ωˣ` is `Ωˣ` with the Galois action.

The strategy is the one described in the target's docstring:

* `linAddEquiv` bridges the two spellings of the coefficient module: for `Coeff = ULift ℤ` a
  `Coeff`-linear map is the same thing as an additive map (`AddMonoidHom.map_zsmul` together with
  `Int.cast_smul_eq_zsmul`), and it is equivariant for the conjugation actions.
* `H¹(Γ, Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)) = 0` (conjugation action) reduces, via the product
  decomposition `freeHomEquiv` (equivariant for the conjugation action,
  `freeHomEquiv_conjSmul_v2`) to `H¹` of the product `∏_{i ∈ ι} Maps(Gal(K/k), Ωˣ)`, which
  vanishes because each factor does (`coindU_H1_subsingleton_v2`, Shapiro + Hilbert 90) and `H¹`
  of an *arbitrary* product of coefficient modules is a subsingleton as soon as each factor is
  (`subsingleton_H1_pi_inf` — the infinite-index form of `subsingleton_H1_pi`).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt

noncomputable section

/-! ## The two spellings of `Hom_ℤ(-, Ωˣ)`: `Coeff`-linear versus additive -/

section Bridge

variable {Γ : Type} [Group Γ]

/-- For `Coeff = ULift ℤ`, a `Coeff`-linear map is exactly an additive map: the `ULift ℤ`-action
on an additive commutative group is its `ℤ`-action (`ulift_up_int_smul_eq`), so additivity already
implies linearity (`AddMonoidHom.map_zsmul`). -/
def linAddEquiv (V W : Type) [AddCommGroup V] [AddCommGroup W] [Module Coeff V] [Module Coeff W] :
    (V →ₗ[Coeff] W) ≃+ (V →+ W) where
  toFun f := f.toAddMonoidHom
  invFun f :=
    { toFun := f
      map_add' := fun x y => f.map_add x y
      map_smul' := fun c x => by
        obtain ⟨z⟩ := c
        simp only [RingHom.id_apply]
        rw [show (ULift.up z : Coeff) = ((z : ℤ) : Coeff) from rfl]
        rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact AddMonoidHom.map_zsmul f z x }
  left_inv f := LinearMap.ext fun x => rfl
  right_inv f := AddMonoidHom.ext fun x => rfl
  map_add' f g := AddMonoidHom.ext fun x => rfl

@[simp] lemma linAddEquiv_apply (V W : Type) [AddCommGroup V] [AddCommGroup W]
    [Module Coeff V] [Module Coeff W] (f : V →ₗ[Coeff] W) (x : V) :
    linAddEquiv V W f x = f x := rfl

/-- The conjugation action `(σ · f) x = σ · f (σ⁻¹ · x)` on additive maps, written out explicitly
(so that its statement involves no type class instance). -/
def homAddConj (R N : Rep.{0} Coeff Γ) (σ : Γ) (f : R.V →+ N.V) : R.V →+ N.V where
  toFun x := N.ρ σ (f ((R.ρ (σ⁻¹)) x))
  map_zero' := by simp
  map_add' x y := by simp [map_add]

/-- `linAddEquiv` intertwines the conjugation actions. -/
theorem linAddEquiv_homSMul (R N : Rep.{0} Coeff Γ) (σ : Γ) (f : R.V →ₗ[Coeff] N.V) :
    linAddEquiv R.V N.V (homSMul R N σ f) = homAddConj R N σ (linAddEquiv R.V N.V f) := by
  ext x
  rfl

end Bridge


section ProductDecomp

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-! ## The product decomposition `freeHomEquiv` without the finiteness hypothesis

The corresponding lemmas in `Submission/Work/SSGRoute/homCoind_H1_free{,_conj_v2}.lean`
(`freeHomEquiv_apply`, `freeHomEquiv_conjSmul_v2`) carry a spurious `[Finite ι]` argument (their
statements do not mention it; it is dragged in from the section variable).  Since the target
statement is about an arbitrary index type, the two statements are repeated here. -/

/-- `freeHomEquiv` evaluated at a basis element. -/
theorem freeHomEquiv_apply_inf {ι : Type}
    (φ : Work.SSGRoute.homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) ι)) (i : ι)
    (g : K ≃ₐ[k] K) :
    Work.SSGRoute.freeHomEquiv (k := k) (Ω := Ω) (K := K) φ i g
      = φ (Finsupp.single i (MonoidAlgebra.single g 1)) := by
  simp only [Work.SSGRoute.freeHomEquiv, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply,
    AddEquiv.addMonoidHomCongrLeft_apply, AddMonoidHom.comp_apply,
    Finsupp.liftAddHom_symm_apply, MonoidAlgebra.coeffAddEquiv_symm_apply,
    MonoidAlgebra.ofCoeff_single, Finsupp.singleAddHom_apply,
    Work.SSGRoute.coeffHomEquiv_apply]
  rfl

/-- `freeHomEquiv` is equivariant for the conjugation action on `Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)` and the
coinduced (componentwise) action on the product `∏_{i ∈ ι} Maps(Gal(K/k), Ωˣ)`. -/
theorem freeHomEquiv_conjSmul_inf {ι : Type} (σ : Ω ≃ₐ[k] Ω)
    (φ : Work.SSGRoute.homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) ι)) :
    Work.SSGRoute.freeHomEquiv (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.conjSmul_v2 (Rep.free Coeff (K ≃ₐ[k] K) ι) σ φ)
      = fun i => Work.SSGRoute.coindAct_v2 (K := K) σ
          (Work.SSGRoute.freeHomEquiv (k := k) (Ω := Ω) (K := K) φ i) := by
  funext i g
  rw [freeHomEquiv_apply_inf (k := k) (Ω := Ω) (K := K)]
  rw [show (Work.SSGRoute.coindAct_v2 (K := K) σ
        (Work.SSGRoute.freeHomEquiv (k := k) (Ω := Ω) (K := K) φ i)) g
      = σ • ((Work.SSGRoute.freeHomEquiv (k := k) (Ω := Ω) (K := K) φ) i
          ((SSGRoute.res k K σ)⁻¹ * g)) from rfl]
  rw [freeHomEquiv_apply_inf (k := k) (Ω := Ω) (K := K)]
  rw [show Work.SSGRoute.conjSmul_v2 (Rep.free Coeff (K ≃ₐ[k] K) ι) σ φ
        (Finsupp.single i (MonoidAlgebra.single g 1))
      = σ • (φ ((Rep.free Coeff (K ≃ₐ[k] K) ι).ρ ((SSGRoute.res k K σ)⁻¹)
          (Finsupp.single i (MonoidAlgebra.single g 1)))) from rfl]
  rw [Representation.free_single_single]

end ProductDecomp

/-! ## The vanishing for the `→+` spelling (conjugation action) -/

/-- `homAddConj` for `R = infl ℤ[Gal(K/k)]^ι`, `N = infl Ωˣ` agrees with `conjSmul_v2`, the
explicit form of the coinduced conjugation action of `coindU_H1_subsingleton_v2`: the two differ
only by rewriting `(r σ)⁻¹` to `r (σ⁻¹)` (`map_inv`). -/
theorem homAddConj_eq_conjSmul {k : Type} [Field k] [CharZero k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] {ι : Type} (σ : Ω ≃ₐ[k] Ω)
    (g : Work.SSGRoute.homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) ι)) :
    homAddConj (Rep.res (SSGDescent.ssgResHom k Ω K) (Rep.free Coeff (K ≃ₐ[k] K) ι))
        (SSGDescent.ssgCoeffM k Ω) σ g
      = Work.SSGRoute.conjSmul_v2 (Rep.free Coeff (K ≃ₐ[k] K) ι) σ g := by
  refine AddMonoidHom.ext fun x => ?_
  show (SSGDescent.ssgCoeffM k Ω).ρ σ
      (g ((Rep.res (SSGDescent.ssgResHom k Ω K) (Rep.free Coeff (K ≃ₐ[k] K) ι)).ρ
        (σ⁻¹) x))
    = (Work.SSGRoute.homCoind.smulHom σ)
        (g ((Rep.free Coeff (K ≃ₐ[k] K) ι).ρ ((SSGDescent.ssgResHom k Ω K σ)⁻¹) x))
  rw [show (Rep.res (SSGDescent.ssgResHom k Ω K) (Rep.free Coeff (K ≃ₐ[k] K) ι)).ρ (σ⁻¹) x
      = (Rep.free Coeff (K ≃ₐ[k] K) ι).ρ ((SSGDescent.ssgResHom k Ω K σ)⁻¹) x from by
    rw [Rep.coe_res_obj_ρ', map_inv]]
  rfl

/-- **`H¹(Γ, Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)) = 0` for the conjugation action and an arbitrary index
type.**  This is `homCoind_H1_free_conj_v2` with the hypothesis `[Finite ι]` removed: the product
over `ι` of the coinduced modules `Maps(Gal(K/k), Ωˣ)` is no longer finite, but `H¹` of a product
vanishes as soon as every factor's does (`subsingleton_H1_pi_inf`), so no finiteness is needed. -/
theorem homCoind_H1_free_conj_inf {k : Type} [Field k] [CharZero k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] (ι : Type) :
    @Subsingleton (@Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) ι)) _ _
      (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free Coeff (K ≃ₐ[k] K) ι))
      (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Rep.free Coeff (K ≃ₐ[k] K) ι))) := by
  have hprod : @Subsingleton (@Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      ((i : ι) → Work.SSGRoute.CoindU k Ω K) _ _ (Pi.addCommGroup)
      (Pi.distribMulAction (Ω ≃ₐ[k] Ω))) :=
    @subsingleton_H1_pi_inf (Ω ≃ₐ[k] Ω) _ _ ι (fun _ => Work.SSGRoute.CoindU k Ω K)
      (fun _ => inferInstance) (fun _ => Work.SSGRoute.CoindU.instDistribMulAction)
      (fun _ => Work.SSGRoute.coindU_H1_subsingleton_v2 (k := k) (Ω := Ω) (K := K))
  refine @subsingleton_H1_of_addEquiv (Ω ≃ₐ[k] Ω) _ _
    (Work.SSGRoute.homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) ι))
    ((i : ι) → Work.SSGRoute.CoindU k Ω K)
    (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free Coeff (K ≃ₐ[k] K) ι))
    (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Rep.free Coeff (K ≃ₐ[k] K) ι))
    (Pi.addCommGroup) (Pi.distribMulAction (Ω ≃ₐ[k] Ω))
    (Work.SSGRoute.freeHomEquiv (k := k) (Ω := Ω) (K := K) (ι := ι)) ?_ hprod
  intro σ φ
  exact freeHomEquiv_conjSmul_inf (k := k) (Ω := Ω) (K := K) σ φ

/-! ## The target statement -/

/-- **`H¹_cont(Gal(Ω/k), Hom_ℤ(infl R, Ωˣ)) = 0` for `R` the free module on an arbitrary index set.**

`k` of characteristic `0`, `Ω` an algebraic closure of `k`, `K ⊆ Ω` a finite Galois intermediate
field, and `R` the inflation of the free `Coeff[Gal(K/k)]`-module on an arbitrary index type `ι`.
With `N` the inflation of `Ωˣ` (so that `R.V →ₗ[Coeff] N.V` is `Hom_ℤ(infl R, Ωˣ)` carrying the
conjugation action of `homRep`), the continuous `H¹` of `Gal(Ω/k)` with these coefficients vanishes.

The statement is written in the *variables-with-equality-hypotheses* shape (the one used by
`Work.SSGRoute.hilbert90_hom_subsingleton_prover`) so that instance search finds the conjugation
action `homRepDistribMulAction` on the unfolded `homRep` type.  Proof route: as an abelian group
the coefficient module is the product `∏_{i ∈ ι} Map(Gal(K/k), Ωˣ)` and the conjugation action is
componentwise (it does not permute `ι`); a locally constant cocycle thus has locally constant
components, each of which is a coboundary by Shapiro's lemma + Hilbert 90
(`Work.SSGRoute.coindU_H1_subsingleton_v2`), and coboundaries are componentwise, so the assembled
family of primitives is a primitive.  Note `Work.SSGRoute.subsingleton_H1_pi` needs `[Fintype ι]`,
so the infinite-index case must go through the componentwise argument; the `homCoind` (`→+`)
spelling (`Work.SSGRoute.homCoind_H1_free_conj_v2`, with its instances passed explicitly) and the
`→ₗ`-spelling have to be bridged, and `Work.SSGRoute.ulift_up_int_smul_eq` shows that
`Coeff = ULift ℤ`-linearity is additivity. -/
theorem h1_ssgHom_free_subsingleton {k : Type} [Field k] [CharZero k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] (ι : Type)
    (R : Rep.{0} SSGRoute.PTExt.Coeff (Ω ≃ₐ[k] Ω))
    (hR : R = Rep.res (Work.SSGRoute.SSGDescent.ssgResHom k Ω K)
      (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ι))
    (N : Rep.{0} SSGRoute.PTExt.Coeff (Ω ≃ₐ[k] Ω))
    (hN : N = Work.SSGRoute.SSGDescent.ssgCoeffM k Ω) :
    Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (R.V →ₗ[SSGRoute.PTExt.Coeff] N.V)) := by
  subst hR
  subst hN
  -- Step A: `H¹` of the `→+` spelling (conjugation action) vanishes
  have hfree := homCoind_H1_free_conj_inf (k := k) (Ω := Ω) (K := K) ι
  -- Step B: transfer along `linAddEquiv`
  refine @subsingleton_H1_of_addEquiv (Ω ≃ₐ[k] Ω) _ _
    ((Rep.res (SSGDescent.ssgResHom k Ω K) (Rep.free Coeff (K ≃ₐ[k] K) ι)).V →ₗ[Coeff]
      (SSGDescent.ssgCoeffM k Ω).V)
    (Work.SSGRoute.homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) ι)) _
    (homRepDistribMulAction (Rep.res (SSGDescent.ssgResHom k Ω K)
        (Rep.free Coeff (K ≃ₐ[k] K) ι)) (SSGDescent.ssgCoeffM k Ω))
    (Work.SSGRoute.homCoind.instAddCommGroup (Rep.free Coeff (K ≃ₐ[k] K) ι))
    (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (Rep.free Coeff (K ≃ₐ[k] K) ι))
    (linAddEquiv _ _) ?_ hfree
  intro σ f
  change linAddEquiv ((Rep.res (SSGDescent.ssgResHom k Ω K)
        (Rep.free Coeff (K ≃ₐ[k] K) ι)).V) ((SSGDescent.ssgCoeffM k Ω).V)
      (homSMul (Rep.res (SSGDescent.ssgResHom k Ω K) (Rep.free Coeff (K ≃ₐ[k] K) ι))
        (SSGDescent.ssgCoeffM k Ω) σ f)
    = Work.SSGRoute.conjSmul_v2 (Rep.free Coeff (K ≃ₐ[k] K) ι) σ
      (linAddEquiv ((Rep.res (SSGDescent.ssgResHom k Ω K) (Rep.free Coeff (K ≃ₐ[k] K) ι)).V)
        ((SSGDescent.ssgCoeffM k Ω).V) f)
  rw [linAddEquiv_homSMul]
  exact homAddConj_eq_conjSmul (k := k) (Ω := Ω) (K := K) σ _

end

end Work.SSGRoute
