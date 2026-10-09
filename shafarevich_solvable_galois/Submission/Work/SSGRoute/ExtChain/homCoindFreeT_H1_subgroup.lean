import Mathlib
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.homCoind_H1_free_conj_v2
import Submission.Work.SSGRoute.PT.br_pTorsion_openSubgroup
import Submission.Work.SSGRoute.PT.shapiro_H1_coind
import Submission.Work.SSGRoute.PT.alphaTwo_trivAction_units_openSubgroup
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.PT.akH2Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(D, Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)) = 0` for a closed subgroup `D ≤ Gal(Ω/k)`

The "subgroup Hilbert 90" input of the E1a localisation comparison: the vanishing of `H¹` of the
free coinduced coefficient at a *closed subgroup* `D` of the absolute Galois group
`Γ = Gal(Ω/k)`.  It is what makes the connecting map of the canonical dualised resolution
injective over a place (see `Work.SSGRoute.PT.NOTE_e1a_square_session10` §2 input 1 and
`Work.SSGRoute.E1aClean.NOTE_levelChangeRoute` §2g (P2)).

## Proof

The `Γ`-module `M = Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)` is the product of `|ι| · |Gal(K/k)|` copies of `Ωˣ`
with the conjugation action; under the coordinate equivalence `freeHomEquiv` it is the product
`∏_{i ∈ ι} CoindU k Ω K`.  Restricting to `↥D` (acting through `p = res k K ∘ D.subtype`):

* `CoindU k Ω K = Maps(Gal(K/k), Ωˣ)` with the coinduced action is, D-equivariantly, the product
  over the cosets `H \ Gal(K/k)` (`H = p.range`) of `Maps(H, Ωˣ)`;
* `Maps(H, Ωˣ)` with the coinduced action is isomorphic to the right-coinduced module
  `Coind ↥D p.ker (Ωˣ)`, whose `H¹` is `H¹(↥(p.ker), Ωˣ)` by Shapiro
  (`PT.shapiro_H1_coind`), and that vanishes since `p.ker = D ⊓ Gal(Ω/K)` is closed
  (`PT.bropenHilbert90ClosedSubgroup`).

The instance arguments are written with `@`-application throughout, because instance synthesis on
the unfolded type `M.V →+ Additive Ωˣ` prefers Mathlib's pointwise action over the conjugation
action of `homCoindDefs` (the same care as in `homCoind_H1_free_conj_v2`).
-/

namespace Work.SSGRoute.ExtChain

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Left cosets of a subgroup, and the product decomposition `G ≃ H × H \ G` -/

section Cosets

variable {G₀ : Type*} [Group G₀]

/-- The setoid of the right cosets `Hg` of a subgroup, written by left multiplication. -/
def lcSetoid (H : Subgroup G₀) : Setoid G₀ where
  r a b := a * b⁻¹ ∈ H
  iseqv := by
    refine ⟨fun a => by simp, fun {a b} hab => ?_, fun {a b c} hab hbc => ?_⟩
    · simpa [mul_inv_rev, inv_inv] using H.inv_mem hab
    · have h : a * b⁻¹ * (b * c⁻¹) ∈ H := H.mul_mem hab hbc
      simpa [mul_assoc] using h

/-- The set of right cosets `H \ G`, presented as a quotient by left multiplication. -/
abbrev LCosets (H : Subgroup G₀) : Type _ := Quotient (lcSetoid H)

/-- The quotient map onto the coset space. -/
abbrev lcMk (H : Subgroup G₀) (g : G₀) : LCosets H := Quotient.mk (lcSetoid H) g

theorem lcMk_eq_iff {H : Subgroup G₀} {a b : G₀} :
    lcMk H a = lcMk H b ↔ a * b⁻¹ ∈ H :=
  Quotient.eq

theorem lcMk_mul (H : Subgroup G₀) (h : H) (g : G₀) :
    lcMk H ((h : G₀) * g) = lcMk H g :=
  lcMk_eq_iff.mpr (by simpa [mul_assoc] using h.2)

theorem lcMk_out (H : Subgroup G₀) (q : LCosets H) : lcMk H (Quotient.out q) = q := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep q
  rw [← ha, lcMk_eq_iff]
  exact Quotient.mk_out (s := lcSetoid H) a

/-- **A group is the product of a subgroup and its coset space**, by left multiplication:
`g = h · (a lift of its coset)`. -/
noncomputable def selfProd (H : Subgroup G₀) : G₀ ≃ H × LCosets H where
  toFun g := (⟨g * (Quotient.out (lcMk H g))⁻¹, by
      have h := Quotient.mk_out (s := lcSetoid H) g
      simpa [mul_inv_rev, inv_inv] using H.inv_mem h⟩, lcMk H g)
  invFun x := (x.1 : G₀) * Quotient.out x.2
  left_inv := by
    intro g
    show (g * (Quotient.out (lcMk H g))⁻¹) * Quotient.out (lcMk H g) = g
    group
  right_inv := by
    rintro ⟨⟨h, hh⟩, q⟩
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      have h1 : lcMk H ((h : G₀) * Quotient.out q) = q := by
        rw [lcMk_mul (H := H) ⟨h, hh⟩ (Quotient.out q)]
        exact lcMk_out H q
      show ((h : G₀) * Quotient.out q)
        * (Quotient.out (lcMk H ((h : G₀) * Quotient.out q)))⁻¹ = h
      rw [h1]
      group
    · show lcMk H ((h : G₀) * Quotient.out q) = q
      rw [lcMk_mul (H := H) ⟨h, hh⟩ (Quotient.out q)]
      exact lcMk_out H q

/-- The product decomposition is `H`-equivariant for left multiplication. -/
theorem selfProd_mul (H : Subgroup G₀) (h : H) (g : G₀) :
    selfProd H ((h : G₀) * g) = (h * (selfProd H g).1, (selfProd H g).2) := by
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    have h1 : lcMk H ((h : G₀) * g) = lcMk H g := lcMk_mul H h g
    show ((h : G₀) * g) * (Quotient.out (lcMk H ((h : G₀) * g)))⁻¹
      = (h : G₀) * (g * (Quotient.out (lcMk H g))⁻¹)
    rw [h1]
    group
  · show lcMk H ((h : G₀) * g) = lcMk H g
    exact lcMk_mul H h g

theorem selfProd_symm_apply (H : Subgroup G₀) (g : G₀) :
    ((selfProd H g).1 : G₀) * Quotient.out ((selfProd H g).2) = g :=
  (selfProd H).symm_apply_apply g

theorem selfProd_out (H : Subgroup G₀) (q : LCosets H) :
    (selfProd H (Quotient.out q)).1 = 1 := by
  refine Subtype.ext ?_
  show Quotient.out q * (Quotient.out (lcMk H (Quotient.out q)))⁻¹ = 1
  rw [lcMk_out H q]
  group

end Cosets

/-! ## 2. The product decomposition of the function space -/

section Decomp

variable {G₀ : Type*} [Group G₀] {A : Type*} [AddCommGroup A]

/-- **The product decomposition of `Maps(G, A)` along a subgroup**: `f ↦ (x, h) ↦ f (h · out x)`. -/
noncomputable def selfProdFuncAddEquiv (H : Subgroup G₀) :
    (G₀ → A) ≃+ (LCosets H → H → A) where
  toFun f x h := f ((h : G₀) * Quotient.out x)
  invFun g q := g (selfProd H q).2 (selfProd H q).1
  left_inv f := by
    funext g
    show f (((selfProd H g).1 : G₀) * Quotient.out ((selfProd H g).2)) = f g
    rw [selfProd_symm_apply]
  right_inv g := by
    funext x h
    show g (selfProd H ((h : G₀) * Quotient.out x)).2
        (selfProd H ((h : G₀) * Quotient.out x)).1 = g x h
    rw [selfProd_mul, selfProd_out]
    show g (lcMk H (Quotient.out x)) (h * 1) = g x h
    rw [lcMk_out]
    congr 1
    exact Subtype.ext (mul_one _)
  map_add' f f' := rfl

theorem selfProdFuncAddEquiv_apply (H : Subgroup G₀) (f : G₀ → A) (x : LCosets H) (h : H) :
    selfProdFuncAddEquiv H f x h = f ((h : G₀) * Quotient.out x) := rfl

end Decomp

/-! ## 3. The two module structures -/

section Structures

variable {Γ : Type*} [Group Γ] (D : Subgroup Γ) (A : Type*) [AddCommGroup A]
variable [DistribMulAction Γ A]

/-- The `↥D`-action on `A` obtained by restricting the `Γ`-action. -/
@[reducible] def resAction : DistribMulAction ↥D A := DistribMulAction.compHom A D.subtype

variable {G₀ : Type*} [Group G₀] (p : ↥D →* G₀)

/-- The coinduced `↥D`-action on `G₀ → A` along `p`: `(δ · f) g = δ • f ((p δ)⁻¹ * g)`. -/
def coinducedAction : DistribMulAction ↥D (G₀ → A) where
  smul δ f := fun g => δ • f ((p δ)⁻¹ * g)
  one_smul f := by
    funext g
    show (1 : ↥D) • f ((p 1)⁻¹ * g) = f g
    rw [map_one, inv_one, one_mul, one_smul]
  mul_smul δ ε f := by
    funext g
    show (δ * ε) • f ((p (δ * ε))⁻¹ * g)
      = δ • (ε • f ((p ε)⁻¹ * ((p δ)⁻¹ * g)))
    rw [map_mul, mul_inv_rev, mul_assoc]
    exact mul_smul δ ε (f ((p ε)⁻¹ * ((p δ)⁻¹ * g)))
  smul_zero δ := by
    funext g
    show δ • (0 : G₀ → A) ((p δ)⁻¹ * g) = 0
    simp
  smul_add δ f f' := by
    funext g
    show δ • (f + f') ((p δ)⁻¹ * g)
      = δ • f ((p δ)⁻¹ * g) + δ • f' ((p δ)⁻¹ * g)
    simp [smul_add]

/-- **Equivariance of the product decomposition**: the coinduced action becomes the pointwise
action on the coset space together with the coinduced action on `H → A`. -/
theorem selfProdFuncAddEquiv_smul (δ : ↥D) (f : G₀ → A) :
    (selfProdFuncAddEquiv (A := A) p.range (fun g => δ • f ((p δ)⁻¹ * g)))
      = fun x h =>
        δ • (selfProdFuncAddEquiv (A := A) p.range f x (((p.rangeRestrict δ)⁻¹) * h)) := by
  funext x h
  rw [selfProdFuncAddEquiv_apply]
  show δ • f ((p δ)⁻¹ * ((h : G₀) * Quotient.out x))
      = δ • f ((((p.rangeRestrict δ)⁻¹ * h : p.range) : G₀) * Quotient.out x)
  congr 1
  congr 1
  rw [show (((p.rangeRestrict δ)⁻¹ * h : p.range) : G₀)
      = (p.rangeRestrict δ : G₀)⁻¹ * (h : G₀) from rfl]
  rw [show (p.rangeRestrict δ : G₀) = p δ from MonoidHom.coe_rangeRestrict p δ]
  group

end Structures

/-! ## 4. `Maps(H, Ωˣ)` with the coinduced action is the right-coinduced module `Coind D p.ker` -/

section CoindIso

variable {Γ : Type*} [Group Γ] (D : Subgroup Γ) (A : Type*) [AddCommGroup A]
variable [DistribMulAction Γ A]
variable {G₀ : Type*} [Group G₀] (p : ↥D →* G₀)

/-- A chosen lift of an element of `p.range` to `↥D`. -/
noncomputable def liftRange (h : p.range) : ↥D :=
  Classical.choose (MonoidHom.mem_range.mp h.2)

theorem rangeRestrict_liftRange (h : p.range) : p.rangeRestrict (liftRange D p h) = h :=
  Subtype.ext (Classical.choose_spec (MonoidHom.mem_range.mp h.2))

/-- **The coinduced module `p.range → A` is the right-coinduced module `Coind ↥D p.ker A`**,
the isomorphism being `f ↦ (δ ↦ δ⁻¹ • f (p.rangeRestrict δ))`. -/
noncomputable def coindArrowEquiv :
    (p.range → A) ≃+ Work.SSGRoute.PT.Coind ↥D p.ker A where
  toFun f := ⟨fun δ => (δ : ↥D)⁻¹ • f (p.rangeRestrict δ), by
    rintro δ u
    have hu : p (u : ↥D) = 1 := u.2
    have h1 : p.rangeRestrict (δ * (u : ↥D)) = p.rangeRestrict δ := by
      ext
      show p (δ * (u : ↥D)) = p δ
      rw [map_mul, hu, mul_one]
    show (δ * (u : ↥D) : ↥D)⁻¹ • f (p.rangeRestrict (δ * (u : ↥D)))
      = (u : ↥D)⁻¹ • ((δ : ↥D)⁻¹ • f (p.rangeRestrict δ))
    rw [h1, mul_inv_rev, mul_smul]⟩
  invFun F := fun h => liftRange D p h • (F : ↥D → A) (liftRange D p h)
  left_inv f := by
    funext h
    show liftRange D p h • ((liftRange D p h : ↥D)⁻¹ • f (p.rangeRestrict (liftRange D p h)))
      = f h
    rw [smul_smul, mul_inv_cancel, one_smul, rangeRestrict_liftRange]
  right_inv F := by
    refine Subtype.ext (funext fun δ => ?_)
    show (δ : ↥D)⁻¹ • (liftRange D p (p.rangeRestrict δ) •
        (F : ↥D → A) (liftRange D p (p.rangeRestrict δ))) = (F : ↥D → A) δ
    set u : ↥D := liftRange D p (p.rangeRestrict δ) with hu
    have hpu : p u = p δ := congrArg Subtype.val (rangeRestrict_liftRange D p (p.rangeRestrict δ))
    have hmem : u⁻¹ * δ ∈ p.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpu, inv_mul_cancel]
    have hF := (F : Work.SSGRoute.PT.Coind ↥D p.ker A).2 u ⟨u⁻¹ * δ, hmem⟩
    rw [show u * (u⁻¹ * δ) = δ from by group] at hF
    rw [hF, smul_smul]
    congr 1
    show δ⁻¹ * u = (u⁻¹ * δ)⁻¹
    group
  map_add' f f' := by
    refine Subtype.ext (funext fun δ => ?_)
    show (δ : ↥D)⁻¹ • (f + f') (p.rangeRestrict δ)
      = ((δ : ↥D)⁻¹ • f (p.rangeRestrict δ)) + ((δ : ↥D)⁻¹ • f' (p.rangeRestrict δ))
    simp

theorem coindArrowEquiv_apply (f : p.range → A) (δ : ↥D) :
    (coindArrowEquiv D A p f : ↥D → A) δ = (δ : ↥D)⁻¹ • f (p.rangeRestrict δ) := rfl

/-- Equivariance of `coindArrowEquiv` for the coinduced action on `p.range → A`. -/
theorem coindArrowEquiv_smul (δ : ↥D) (f : p.range → A) :
    coindArrowEquiv D A p (fun h => δ • f ((p.rangeRestrict δ)⁻¹ * h))
      = δ • coindArrowEquiv D A p f := by
  refine Subtype.ext (funext fun δ' => ?_)
  rw [Work.SSGRoute.PT.Coind.smul_apply, coindArrowEquiv_apply, coindArrowEquiv_apply,
    smul_smul, map_mul, map_inv, mul_inv_rev, inv_inv]

end CoindIso

/-! ## 5. The vanishing -/

section Final

theorem homCoindFreeT_H1_subgroup {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] {ι : Type} [Finite ι] (D : Subgroup (Ω ≃ₐ[k] Ω))
    (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω))) :
    Subsingleton (@Work.AbsoluteKummer.H1 ↥D
      (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) _ _
      (Work.SSGRoute.ExtChain.instAddCommGroupHomCoindFreeT k Ω K ι)
      (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) _ _
        (Work.SSGRoute.ExtChain.instDistribMulActionHomCoindFreeT k Ω K ι) D)) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  let p : ↥D →* (K ≃ₐ[k] K) := (SSGRoute.res k K).comp D.subtype
  have hkereq : ∀ x : ↥D, x ∈ p.ker ↔ ((x : Ω ≃ₐ[k] Ω)) ∈ D ⊓ K.fixingSubgroup := by
    intro x
    constructor
    · intro hx
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      have h2 : (x : Ω ≃ₐ[k] Ω) ∈ (AlgEquiv.restrictNormalHom ↥K).ker := MonoidHom.mem_ker.mpr hx
      rw [IntermediateField.restrictNormalHom_ker K] at h2
      exact h2
    · intro hx
      show p x = 1
      have h2 : (x : Ω ≃ₐ[k] Ω) ∈ (AlgEquiv.restrictNormalHom ↥K).ker := by
        rw [IntermediateField.restrictNormalHom_ker K]
        exact hx.2
      exact MonoidHom.mem_ker.mp h2
  have hΦto : ∀ x : ↥(p.ker), ((x.1 : Ω ≃ₐ[k] Ω)) ∈ D ⊓ K.fixingSubgroup :=
    fun x => (hkereq x.1).mp x.2
  have hΦinv : ∀ y : ↥(D ⊓ K.fixingSubgroup),
      (⟨(y.1 : Ω ≃ₐ[k] Ω), y.2.1⟩ : ↥D) ∈ p.ker :=
    fun y => (hkereq ⟨(y.1 : Ω ≃ₐ[k] Ω), y.2.1⟩).mpr y.2
  let Φ : ↥(p.ker) ≃* ↥(D ⊓ K.fixingSubgroup) :=
    { toFun := fun x => Subtype.mk (x.1 : Ω ≃ₐ[k] Ω) (hΦto x)
      invFun := fun y => Subtype.mk (Subtype.mk (y.1 : Ω ≃ₐ[k] Ω) y.2.1) (hΦinv y)
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  have hΦcont : Continuous (Φ.symm : ↥(D ⊓ K.fixingSubgroup) → ↥(p.ker)) := by
    refine Continuous.subtype_mk ?_ (fun y => hΦinv y)
    refine Continuous.subtype_mk ?_ (fun y => y.2.1)
    exact continuous_subtype_val
  have hΦcont' : Continuous (Φ : ↥(p.ker) → ↥(D ⊓ K.fixingSubgroup)) := by
    refine Continuous.subtype_mk ?_ (fun x => hΦto x)
    exact continuous_subtype_val.comp continuous_subtype_val
  haveI h90big : Subsingleton (Work.AbsoluteKummer.H1 ↥(D ⊓ K.fixingSubgroup)
      (Additive Ωˣ)) :=
    Work.SSGRoute.PT.bropenHilbert90ClosedSubgroup (D ⊓ K.fixingSubgroup)
      (hD.inter (IntermediateField.fixingSubgroup_isClosed K))
  haveI h90 : Subsingleton (Work.AbsoluteKummer.H1 ↥(p.ker) (Additive Ωˣ)) := by
    have hli := Work.SSGRoute.PT.h1TransferAddHom_leftInverse Φ hΦcont hΦcont'
      (AddEquiv.refl (Additive Ωˣ)) (fun g' m' => rfl)
    refine ⟨fun a b => ?_⟩
    rw [← hli a, ← hli b]
    congr 1
    exact Subsingleton.elim _ _
  haveI hfin : p.ker.FiniteIndex := by
    haveI : Finite p.range :=
      Finite.of_injective (fun x : p.range => (x : K ≃ₐ[k] K)) Subtype.coe_injective
    infer_instance
  have hclosed : IsClosed ((p.ker : Subgroup ↥D) : Set ↥D) := by
    have hset : ((p.ker : Subgroup ↥D) : Set ↥D)
        = (fun x : ↥D => (x : Ω ≃ₐ[k] Ω)) ⁻¹'
            ((D ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
      ext x
      exact hkereq x
    rw [hset]
    exact (hD.inter (IntermediateField.fixingSubgroup_isClosed K)).preimage continuous_subtype_val
  have hopen : IsOpen ((p.ker : Subgroup ↥D) : Set ↥D) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex p.ker hclosed
  have hdis : Work.AbsoluteKummer.IsDiscreteModule ↥(p.ker) (Additive Ωˣ) :=
    Work.SSGRoute.PT.H2Fin.isDiscreteModule_subgroup (Γ := ↥D) p.ker
      (Work.SSGRoute.PT.H2Fin.isDiscreteModule_subgroup (Γ := Ω ≃ₐ[k] Ω) D
        (Work.SSGRoute.isDiscreteModule_addUnitsΩ (k := k) (Ω := Ω)))
  haveI hC : Subsingleton (Work.AbsoluteKummer.H1 ↥D
      (Work.SSGRoute.PT.Coind ↥D p.ker (Additive Ωˣ))) :=
    (Work.SSGRoute.PT.shapiro_H1_coind (G := ↥D) p.ker hopen hdis).elim
      (fun e => ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩)
  -- (1) the coefficient `p.range → Ωˣ` with the coinduced action
  have hArr : Subsingleton (@Work.AbsoluteKummer.H1 ↥D (p.range → Additive Ωˣ) _ _
      _ (coinducedAction D (Additive Ωˣ) p.rangeRestrict)) :=
    @subsingleton_H1_of_addEquiv ↥D _ _ (p.range → Additive Ωˣ)
      (Work.SSGRoute.PT.Coind ↥D p.ker (Additive Ωˣ)) _
      (coinducedAction D (Additive Ωˣ) p.rangeRestrict) _ _
      (coindArrowEquiv D (Additive Ωˣ) p)
      (fun δ f => coindArrowEquiv_smul D (Additive Ωˣ) p δ f) hC
  -- (2) the product over the cosets
  haveI hCosF : Fintype (LCosets p.range) := Fintype.ofFinite _
  have hProd : Subsingleton (@Work.AbsoluteKummer.H1 ↥D
      (LCosets p.range → p.range → Additive Ωˣ) _ _
      _ (@Pi.distribMulAction (LCosets p.range)
        (fun _ => p.range → Additive Ωˣ) ↥D _ _
        (fun _ => coinducedAction D (Additive Ωˣ) p.rangeRestrict))) :=
    @subsingleton_H1_pi ↥D _ _ (LCosets p.range) _ (fun _ => p.range → Additive Ωˣ) _
      (fun _ => coinducedAction D (Additive Ωˣ) p.rangeRestrict) (fun _ => hArr)
  -- (3) the module `Gal(K/k) → Ωˣ` with the coinduced action
  have hCoindU : Subsingleton (@Work.AbsoluteKummer.H1 ↥D ((K ≃ₐ[k] K) → Additive Ωˣ) _ _
      _ (coinducedAction D (Additive Ωˣ) p)) :=
    @subsingleton_H1_of_addEquiv ↥D _ _ ((K ≃ₐ[k] K) → Additive Ωˣ)
      (LCosets p.range → p.range → Additive Ωˣ) _
      (coinducedAction D (Additive Ωˣ) p) _
      (@Pi.distribMulAction (LCosets p.range)
        (fun _ => p.range → Additive Ωˣ) ↥D _ _
        (fun _ => coinducedAction D (Additive Ωˣ) p.rangeRestrict))
      (selfProdFuncAddEquiv (A := Additive Ωˣ) p.range)
      (fun δ f => selfProdFuncAddEquiv_smul D (Additive Ωˣ) p δ f) hProd
  -- (4) the product over `ι`
  have hι : Subsingleton (@Work.AbsoluteKummer.H1 ↥D
      (ι → (K ≃ₐ[k] K) → Additive Ωˣ) _ _
      _ (@Pi.distribMulAction ι (fun _ => (K ≃ₐ[k] K) → Additive Ωˣ) ↥D _ _
        (fun _ => coinducedAction D (Additive Ωˣ) p))) :=
    @subsingleton_H1_pi ↥D _ _ ι _ (fun _ => (K ≃ₐ[k] K) → Additive Ωˣ) _
      (fun _ => coinducedAction D (Additive Ωˣ) p) (fun _ => hCoindU)
  -- (5) transport along `freeHomEquiv`
  refine @subsingleton_H1_of_addEquiv ↥D _ _
    (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι)
    (ι → (K ≃ₐ[k] K) → Additive Ωˣ) _
    (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) _ _
      (Work.SSGRoute.ExtChain.instDistribMulActionHomCoindFreeT k Ω K ι) D) _
    (@Pi.distribMulAction ι (fun _ => (K ≃ₐ[k] K) → Additive Ωˣ) ↥D _ _
      (fun _ => coinducedAction D (Additive Ωˣ) p))
    (freeHomEquiv (k := k) (Ω := Ω) (K := K) (ι := ι)) ?_ hι
  intro δ φ
  rw [Subgroup.smul_def]
  exact freeHomEquiv_conjSmul_v2 (k := k) (Ω := Ω) (K := K) (ι := ι)
    (δ : Ω ≃ₐ[k] Ω) φ

end Final

end Work.SSGRoute.ExtChain
