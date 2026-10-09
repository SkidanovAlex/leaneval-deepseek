import Mathlib
import Submission.Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup
import Submission.Work.SSGRoute.h1_ssgHom_free_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Subgroup Hilbert 90 for `Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ)` at an *arbitrary* index type

`Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup` proves the vanishing of
`H¹(D, Hom_ℤ(ℤ[Gal(K/k)]^ι, Ωˣ))` for a *closed* subgroup `D ≤ Gal(Ω/k)` of the absolute Galois
group `Ω ≃ₐ[k] Ω`, under the extra hypothesis `[Finite ι]`.  That finiteness enters the proof at a
single place: the coefficient module is, under `freeHomEquiv`, the product
`∏_{i ∈ ι} Maps(Gal(K/k), Ωˣ)`, and the finite proof invokes `subsingleton_H1_pi`, which needs
`[Fintype ι]`.

The hypothesis is spurious.  `H¹` of an *arbitrary* product of coefficient modules vanishes as soon
as each factor's does (`Work.SSGRoute.subsingleton_H1_pi_inf`): a locally constant crossed
homomorphism into a product has locally constant components, each of which is a coboundary because
its `H¹` vanishes, and the componentwise family of primitives is a primitive for the original
cocycle.  The only remaining finiteness input of the argument,
`FiniteIndex (D ⊓ Gal(Ω/K))` (equivalently the finiteness of `Gal(K/k)`), is independent of `ι`.

This file records exactly that: it repeats the proof of `homCoindFreeT_H1_subgroup` with

* `subsingleton_H1_pi` replaced by its infinite-index form `subsingleton_H1_pi_inf` (for both the
  product over the cosets `p.range \ Gal(K/k)` and the product over `ι`), and
* `freeHomEquiv_conjSmul_v2` replaced by `freeHomEquiv_conjSmul_inf`, the `[Finite ι]`-free form of
  the equivariance of `freeHomEquiv`.

The instance arguments are again written with `@`-application throughout, because instance search
on the unfolded types prefers Mathlib's pointwise action over the conjugation resp. coinduced
action (cf. the remarks in `homCoind_H1_free_conj_v2` and `ExtChain.homCoindFreeT_H1_subgroup`).
-/

namespace Work.SSGRoute.HomCoindSubgroup

open Work.SSGRoute.ExtChain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem homCoindFreeT_H1_subgroup_inf {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (ι : Type) (D : Subgroup (Ω ≃ₐ[k] Ω))
    (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω))) :
    Subsingleton (@Work.AbsoluteKummer.H1 ↥D
      (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) _ _
      (Work.SSGRoute.ExtChain.instAddCommGroupHomCoindFreeT k Ω K ι)
      (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.ExtChain.homCoindFreeT k Ω K ι) _ _
        (Work.SSGRoute.ExtChain.instDistribMulActionHomCoindFreeT k Ω K ι) D)) := by
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
  -- (2) the product over the cosets — *no* finiteness on the coset space is needed
  have hProd : Subsingleton (@Work.AbsoluteKummer.H1 ↥D
      (LCosets p.range → p.range → Additive Ωˣ) _ _
      _ (@Pi.distribMulAction (LCosets p.range)
        (fun _ => p.range → Additive Ωˣ) ↥D _ _
        (fun _ => coinducedAction D (Additive Ωˣ) p.rangeRestrict))) :=
    @subsingleton_H1_pi_inf ↥D _ _ (LCosets p.range)
      (fun _ => p.range → Additive Ωˣ)
      (fun _ => inferInstance)
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
  -- (4) the product over `ι` — here the infinite-index product lemma is used
  have hι : Subsingleton (@Work.AbsoluteKummer.H1 ↥D
      (ι → (K ≃ₐ[k] K) → Additive Ωˣ) _ _
      _ (@Pi.distribMulAction ι (fun _ => (K ≃ₐ[k] K) → Additive Ωˣ) ↥D _ _
        (fun _ => coinducedAction D (Additive Ωˣ) p))) :=
    @subsingleton_H1_pi_inf ↥D _ _ ι (fun _ => (K ≃ₐ[k] K) → Additive Ωˣ)
      (fun _ => inferInstance)
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
  exact freeHomEquiv_conjSmul_inf (k := k) (Ω := Ω) (K := K)
    (δ : Ω ≃ₐ[k] Ω) φ

end Work.SSGRoute.HomCoindSubgroup
