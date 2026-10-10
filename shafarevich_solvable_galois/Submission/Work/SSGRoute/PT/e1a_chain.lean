import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.ext_one_homCoind_iso
import Submission.Work.SSGRoute.PT.finite_dualMod_tensor
import Submission.Work.SSGRoute.PT.h2_equiv_of_equiv
import Submission.Work.SSGRoute.PT.homCoind_SES
import Submission.Work.SSGRoute.PT.sha2_to_H2AK
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.sha2_coeff.mapH2_injective_of_addEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a, the `Ext`-side chain for a finite free cover of `E'` (shared helper module)

This module contains the pieces of node `E1a` (`Work.SSGRoute.PT.e1a_ext_sha2_bridge`) that are
needed *below* the target file, so that the modules proving the remaining clauses (and the
Shapiro computation of the crux) can import them without creating an import cycle with the target
file:

* `homCoindFree` and its two instances -- the `@[reducible]` wrapper for the middle coefficient
  `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)` of the dualised resolution, needed because instance search for the
  cohomology quotients of the plain `Rep.free`-based coefficient diverges;
* `e1a_ext2_homCoind` -- `Ext²_G(N,Kˣ) ≅ H¹(Γ, Hom_ℤ(R,Ωˣ))` (syzygy shift + the E1c dictionary);
* `e1a_deltaH2` -- the injective connecting map `δ` of the dualised resolution, with
  `δ.range = ker (mapH2 S.iota)`;
* `e1a_h2_coeff_iso` -- `H²(Γ,E) ≅ H²(Γ, Hom_ℤ(E',Ωˣ))`;
* `e1aCoeffMap` -- a chosen realisation of that coefficient map as an additive map, and
  `e1aCoeffMap_injective`.

The target theorem `Work.SSGRoute.PT.e1a_ext_sha2_bridge` and the assembled map `β` live in the
modules `Submission.Work.SSGRoute.PT.e1a_beta` and `Submission.Work.SSGRoute.PT.e1a_ext_sha2_bridge`.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section


/-! ## Step 2 of the route: the `Ext`-side chain for a finite free cover of `E'`

The three lemmas below realise, as named maps, the chain
`Ext²_G(E',Kˣ) ≅ Ext¹_G(R,Kˣ) ≅ H¹(Γ, Hom_ℤ(R,Ωˣ)) --δ--> H²(Γ, Hom_ℤ(E',Ωˣ)) ≅ H²(Γ, E)`
of the route (steps 1–2), for `0 → R → F → E' → 0` a finite free cover of `E'` over `G = Gal(K/k)`
and `Γ = Gal(Ω/k)`.

*Type class friction.*  The coefficient `Hom_ℤ(ℤ[G]^n, Ωˣ)` is `Rep.free`-based, and instance
search for `AddCommGroup`/`DistribMulAction` on the quotient types `H¹`/`H²` of that coefficient
diverges (the `Finsupp` unfolding of the free module), so that `H²(Γ,Hom_ℤ(F,Ωˣ))` cannot even be
*formed* as a type class instance.  The wrapper `homCoindFree` below is a plain `def` (not an
`abbrev`), with its two instances registered by hand; instance search then grounds out immediately
on the head symbol `homCoindFree`, while the defeq `homCoindFree k Ω K n = homCoind k Ω K (free n)`
still lets every existing lemma about the free coefficient be used. -/

/-- `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)` with the conjugation action of `Γ = Gal(Ω/k)`, wrapped in a
`@[reducible] def` so that instance search for the cohomology quotients `H¹`, `H²` of this
coefficient terminates on the head symbol `homCoindFree` (see the module note) while remaining
definitionally equal to `homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) (Fin n))` at `instances`
transparency, so that every lemma about the free coefficient applies. -/
@[reducible] def homCoindFree (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (n : ℕ) : Type :=
  Work.SSGRoute.homCoind k Ω K (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n))

noncomputable instance instAddCommGroupHomCoindFree (k : Type) [Field k] [CharZero k]
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (n : ℕ) : AddCommGroup (homCoindFree k Ω K n) :=
  Work.SSGRoute.homCoind.instAddCommGroup _

noncomputable instance instDistribMulActionHomCoindFree' (k : Type) [Field k] [CharZero k]
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (n : ℕ) :
    DistribMulAction (Ω ≃ₐ[k] Ω) (homCoindFree k Ω K n) :=
  Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv _

/-- **E1a, step 2 (syzygy shift plus the `E1c` dictionary).**  For a finitely generated
`Gal(K/k)`-module `N` and a finite free cover `pic : ℤ[Gal(K/k)]^n ↠ N` with kernel `R`,
`Ext²_{Gal(K/k)}(N, Kˣ) ≅ H¹(Γ, Hom_ℤ(R, Ωˣ))` — the composite of the syzygy shift
`Ext²(N,Kˣ) ≅ Ext¹(R,Kˣ)` (`ext_shift_of_projective_presentation`, with `F` projective) and the
`E1c`-pattern dictionary `Ext¹(R,Kˣ) ≅ H¹(Γ,Hom_ℤ(R,Ωˣ))` (`ext_one_homCoind_iso`). -/
theorem e1a_ext2_homCoind (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ N.V]
    (n : ℕ) (pic : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n) ⟶ N) (hpic : Epi pic) :
    Nonempty (Abelian.Ext N (unitsK k K) 2 ≃+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic))) := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  let S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :=
    ShortComplex.mk (CategoryTheory.Limits.kernel.ι pic) pic
      (CategoryTheory.Limits.kernel.condition pic)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel pic) inferInstance hpic
  obtain ⟨e1⟩ :=
    ext_shift_of_projective_presentation (K ≃ₐ[k] K) S hS (unitsK k K) 1 (by norm_num)
  haveI : Module.Finite ℤ (CategoryTheory.Limits.kernel pic).V := repFG_kernel N pic
  obtain ⟨e2⟩ := ext_one_homCoind_iso k Ω K (CategoryTheory.Limits.kernel pic)
  exact ⟨e1.symm.trans e2⟩

/-- **E1a, step 2, the connecting map `δ`.**  For a surjection `pic : ℤ[Gal(K/k)]^n ↠ N` with
kernel `R`, the dualised resolution `0 → Hom_ℤ(N,Ωˣ) → Hom_ℤ(F,Ωˣ) → Hom_ℤ(R,Ωˣ) → 0` (exact
because `Ωˣ` is divisible) produces an injective connecting map
`δ : H¹(Γ, Hom_ℤ(R,Ωˣ)) ↪ H²(Γ, Hom_ℤ(N,Ωˣ))` whose image is the kernel of
`H²(Γ,Hom_ℤ(N,Ωˣ)) → H²(Γ,Hom_ℤ(F,Ωˣ))`.  Injectivity is `H¹(Γ, Hom_ℤ(F,Ωˣ)) = 0` (Shapiro +
Hilbert 90, `homCoind_H1_free_conj_v2`). -/
theorem e1a_deltaH2 (k : Type) [Field k] [CharZero k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (n : ℕ)
    (pic : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n) ⟶ N)
    (hf : Function.Surjective (Rep.Hom.hom pic)) :
    ∃ (S : Work.AbsoluteKummer.ShortExactSeq (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K N)
        (homCoindFree k Ω K n)
        (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic)))
      (δ : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic)) →+
          Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K N)),
      S.iota = Work.SSGRoute.precompAddHom (Rep.Hom.hom pic).toAddMonoidHom ∧
      Function.Injective δ ∧
      δ.range = (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker := by
  classical
  obtain ⟨S, hS, -⟩ := homCoind_SES (k := k) (Ω := Ω) (K := K) pic hf
  obtain ⟨δ, hker, hrange⟩ :=
    Work.AbsoluteKummer.SES.exists_connecting_exact_H2 S
  haveI : Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (homCoindFree k Ω K n)) :=
    homCoind_H1_free_conj_v2 (k := k) (Ω := Ω) (K := K) (ι := Fin n)
  refine ⟨S, δ, hS, ?_, hrange⟩
  intro x y hxy
  have hmem : x - y ∈ δ.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
  rw [← hker] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz0 : z = 0 := Subsingleton.elim z 0
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- **E1a, step 2, the coefficient change `H²(Γ,E) ≅ H²(Γ, Hom_ℤ(E',Ωˣ))`.**  The equivariant
additive isomorphism `E ≅ Hom_ℤ(E',Ωˣ)` (`dualPairingEquiv_homCoind`, equivalent to
`Hom_ℤ(E',Kˣ) ≅ E` of `hom_dualMod_units_equiv`) induces an isomorphism of the continuous second
cohomology groups (`h2_equiv_of_equiv`). -/
theorem e1a_h2_coeff_iso (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Nonempty (@Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) ≃+
      @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K
          (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) _ _
        (Work.SSGRoute.homCoind.instAddCommGroup
          (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv
          (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  obtain ⟨Φ, hΦ⟩ := dualPairingEquiv_homCoind p k Ω K ζ hζ hζK T hT E
  exact h2_equiv_of_equiv Φ hΦ


/-- **The chosen coefficient identification on `H²`**, `H²(Γ,E) → H²(Γ, Hom_ℤ(E',Ωˣ))`.

`dualPairingEquiv_homCoind` supplies an equivariant additive isomorphism
`Ψ : E ≃+ Hom_ℤ(E',Ωˣ)` (equivalently `Hom_ℤ(E',Kˣ) ≅ E`, `hom_dualMod_units_equiv`); the induced
map `mapH2 Ψ hΨ` on continuous second cohomology is *chosen once and for all* here, so that the
statements further up may refer to a single fixed map instead of re-quantifying over `Ψ` and its
equivariance (which forces the `DistribMulAction (Ω ≃ₐ[k] Ω) E` instance `DistribMulAction.compHom`
into every statement). -/
noncomputable def e1aCoeffMap (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) →+
      Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K
          (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  exact Work.AbsoluteKummer.mapH2
    (Classical.choose (dualPairingEquiv_homCoind p k Ω K ζ hζ hζK T hT E)).toAddMonoidHom
    (fun σ e => Classical.choose_spec (dualPairingEquiv_homCoind p k Ω K ζ hζ hζK T hT E) σ e)


/-- `e1aCoeffMap` is injective: it is `mapH2` of the equivariant additive *equivalence*
`E ≃+ Hom_ℤ(E',Ωˣ)`, and `mapH2` of an equivariant additive equivalence is injective
(`Work.SSGRoute.sha2_coeff.mapH2_injective_of_addEquiv`). -/
theorem e1aCoeffMap_injective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Function.Injective (e1aCoeffMap p k Ω K ζ hζ hζK T hT E) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  let Ψ : E ≃+ Work.SSGRoute.homCoind k Ω K
      (modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) :=
    Classical.choose (dualPairingEquiv_homCoind p k Ω K ζ hζ hζK T hT E)
  have hΨ : ∀ (σ : Ω ≃ₐ[k] Ω) (e : E), Ψ ((SSGRoute.res k K σ) • e) = σ • Ψ e :=
    Classical.choose_spec (dualPairingEquiv_homCoind p k Ω K ζ hζ hζK T hT E)
  have hΨsymm : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Ψ.symm.toAddMonoidHom := by
    intro σ n
    apply Ψ.injective
    calc Ψ (Ψ.symm (σ • n)) = σ • n := Ψ.apply_symm_apply (σ • n)
      _ = σ • Ψ (Ψ.symm n) := by rw [Ψ.apply_symm_apply]
      _ = Ψ (σ • Ψ.symm n) := (hΨ σ (Ψ.symm n)).symm
  exact Work.SSGRoute.sha2_coeff.mapH2_injective_of_addEquiv Ψ (fun σ e => hΨ σ e) hΨsymm


/-! ## The assembled map `β : Ш²(k,E) → Ext²_G(E',Kˣ)`

The route (steps 1–3 of the module note): `Sha2 p k Ω K E --φ--> H²(Γ,E) --e1aCoeffMap-->
H²(Γ,Hom_ℤ(E',Ωˣ)) --δ⁻¹--> H¹(Γ,Hom_ℤ(R,Ωˣ)) --(chain iso)⁻¹--> Ext²_G(E',Kˣ)`, where
`0 → R → F → E' → 0` is a chosen finite free cover of `E' = DualMod p (E ⊗ T)` over `G = Gal(K/k)`.
The well-definedness of `δ⁻¹` on the image is exactly the crux `e1a_sha2_mem_deltaRange`; every
factor is an additive injection, so `β` is an additive injection.  The two remaining clauses of the
target theorem -- that the image of `β` is `ker extToIdeles`, and its naturality in `E` -- are
*separate* statements about this same map (see the module note). -/

end

end Work.SSGRoute.PT
