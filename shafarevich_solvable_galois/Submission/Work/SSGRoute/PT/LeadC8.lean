import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Module.StablyFree.Basic
import Submission.Work.SSGRoute.EulerSymm.eulerChar_decomp_clean
import Submission.Work.SSGRoute.LTD02Proved.local_tate_duality_02_proved
import Submission.Work.SSGRoute.PT.g1FinHalf_hreal_unr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Lead design ssg_c8_0400, proved part, copied to `PT/LeadC8.lean` by the hub lane.
Copied from `Submission/_lead_design/ssg_c8_0400.lean` (the lead's clause-(8) design) with the two
open obligations `finrank_H0loc_le_unrClasses` (C1a) and `hreal_unr_of_unrCount` (R1) removed (they
are dispatched as separate lemmas) and the `#typeTaint` / `#print axioms` checks dropped.
Namespace `Work.SSGRoute.LeadC8`; everything here is `sorry`-free and `sorryAx`-free. -/

/-! Lead design ssg_c8_0400 (clause (8) of `PT.canonical_localPairing_reciprocity_converse`).

Abstract interface only: no TYPE below mentions `g1FinHalf`, `finZB`, `finZBg`, `archβc`,
`archPairLocal` or `localDictionary_natural_family(_arch)`; see `#typeTaint` at the end.
Proved here: `LeadC8.ann_le_of_finrank` (the linear algebra), `LeadC8.inertia_of_dictionary_eq`
(removes `hβg_unr` from v7), `LeadC8.unrCount_goodPlace_of_C1a` (the count from C1a + two
PROVED arithmetic theorems).  Open (`sorry`, to dispatch): `C1a`, `R1`. -/

set_option synthInstance.maxHeartbeats 400000

namespace Work.SSGRoute.LeadC8

open scoped TensorProduct

/-! ## 0. The linear algebra (PROVED) -/

/-- Perfect-on-the-right pairing, `U ⊥ U'`, `dim V ≤ dim U + dim U'`  ⟹  `ann(U') ⊆ U`. -/
theorem ann_le_of_finrank {F V W : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (P : V →ₗ[F] W →ₗ[F] F) (hr : ∀ w, (∀ v, P v w = 0) → w = 0)
    (U : Submodule F V) (U' : Submodule F W) (horth : ∀ u ∈ U, ∀ u' ∈ U', P u u' = 0)
    (hcount : Module.finrank F V ≤ Module.finrank F U + Module.finrank F U') :
    ∀ v, (∀ u' ∈ U', P v u' = 0) → v ∈ U := by
  classical
  -- Φ : V → Dual U'
  let Φ : V →ₗ[F] Module.Dual F U' := (LinearMap.lcomp F F U'.subtype).comp P
  have hΦ : ∀ v (u' : U'), Φ v u' = P v u' := fun v u' => rfl
  -- Ψ : U' → Dual V, injective
  let Ψ : U' →ₗ[F] Module.Dual F V := P.flip.comp U'.subtype
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u' hu'
    have : (u' : W) = 0 := hr u' (fun v => by
      have := LinearMap.congr_fun hu' v
      simpa [Ψ] using this)
    exact Subtype.ext this
  -- Ψ = Φ.dualMap ∘ eval
  have hΨ : Ψ = Φ.dualMap.comp (Module.evalEquiv F U').toLinearMap := by
    ext u' v
    simp [Ψ, Φ, LinearMap.dualMap_apply, Module.evalEquiv]
  have hrk : Module.finrank F (LinearMap.range Φ) = Module.finrank F U' := by
    rw [← LinearMap.finrank_range_dualMap_eq_finrank_range]
    have h1 : LinearMap.range Ψ = LinearMap.range Φ.dualMap := by
      rw [hΨ, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    rw [← h1, LinearMap.finrank_range_of_inj hΨinj]
  have hker : Module.finrank F (LinearMap.ker Φ) ≤ Module.finrank F U := by
    have := LinearMap.finrank_range_add_finrank_ker Φ
    omega
  have hle : U ≤ LinearMap.ker Φ := by
    intro u hu
    rw [LinearMap.mem_ker]
    ext u'
    rw [hΦ]
    exact horth u hu u' u'.2
  have heq : U = LinearMap.ker Φ := Submodule.eq_of_le_of_finrank_le hle hker
  intro v hv
  rw [heq, LinearMap.mem_ker]
  ext u'
  rw [hΦ]
  exact hv u' u'.2

/-! ## 1. `hβg_unr` is not needed by v7 (PROVED helper for `finiteS_converse_canonical_v8`) -/

/-- At a place unramified in `K/k`: if a dictionary with kernel = coboundaries takes the same value
on `ε` and on an inertia-vanishing `a`, then `ε` vanishes on the inertia. -/
theorem inertia_of_dictionary_eq (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    {M : Type} [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M] {E : Type} [AddCommGroup E]
    (A : ValuationSubring Ω) (hram : ¬ SSGRoute.IsRamifiedIn k K A)
    (βl : ((Ω ≃ₐ[k] Ω) → M) → E)
    (hβl_add : ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' → βl (b + b') = βl b + βl b')
    (hβl_ker : ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (ε a : (Ω ≃ₐ[k] Ω) → M)
    (hεc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) ε)
    (hεl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) ε)
    (hac : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hal : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (haI : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0)
    (heq : βl ε = βl a) :
    ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → ε σ = 0 := by
  have hcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (ε - a) :=
    Work.SSGRoute.IsCocycleOn.sub hεc hac
  have hlc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (ε - a) :=
    Work.SSGRoute.IsLocConstOn.sub hεl hal
  have hadd := hβl_add (ε - a) a hcoc hlc hac hal
  rw [sub_add_cancel, heq] at hadd
  have hz : βl (ε - a) = 0 := by
    have h2 : βl (ε - a) + βl a = 0 + βl a := by rw [zero_add]; exact hadd.symm
    exact add_right_cancel h2
  exact Work.SSGRoute.PT.eq_zero_of_isInertia_of_sub_isCoboundary k Ω K A hram haI
    ((hβl_ker _ hcoc hlc).mp hz)

/-! ## 2. The unramified classes and the count -/

/-- The unramified classes of `H¹_loc(D_A, X)`: classes of locally constant cocycles vanishing on
the inertia of `A`. -/
noncomputable def unrClasses (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (A : ValuationSubring Ω) :
    Submodule (ZMod p) (Work.SSGRoute.H1loc p k Ω K X (SSGRoute.decomp k A)) :=
  Submodule.span (ZMod p) {y | ∃ f : (Ω ≃ₐ[k] Ω) → X,
    f ∈ Work.SSGRoute.lcCocycles p k Ω K X (SSGRoute.decomp k A) ∧
    (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → f σ = 0) ∧
    Work.SSGRoute.toClass p k Ω K X (SSGRoute.decomp k A) f = y}


/-- **C1 (PROVED from C1a here)**: `dim H¹(D_A,M) ≤ dim U(M) + dim U(M^∨(1))`, from the PROVED
Euler characteristic `EulerSymm.eulerChar_decomp_notResidueChar` and the PROVED degree-0/2 duality
`LTD02Proved.local_tate_duality_02_proved`. -/
theorem unrCount_goodPlace_of_C1a (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hC1a : ∀ (X : Type) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] [Finite X]
      (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation ((p : ℚ) : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K X (SSGRoute.decomp k A)) ≤
        Module.finrank (ZMod p) ↥(unrClasses p k Ω K X A))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hp : ¬ A.valuation ((p : ℚ) : Ω) < 1) (hram : ¬ SSGRoute.IsRamifiedIn k K A) :
    Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) ≤
      Module.finrank (ZMod p) ↥(unrClasses p k Ω K M A) +
      Module.finrank (ZMod p) ↥(unrClasses p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A) := by
  haveI hMTfin : Finite (TensorProduct (ZMod p) M T) := by
    haveI : Module.Free (ZMod p) T := inferInstance
    have hfr : Module.finrank (ZMod p) T = 1 := hT.1
    haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
    have h2 : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
      rw [hfr, Module.finrank_self]
    have e : TensorProduct (ZMod p) M T ≃ₗ[ZMod p] TensorProduct (ZMod p) M (ZMod p) :=
      TensorProduct.congr (LinearEquiv.refl (ZMod p) M)
        (LinearEquiv.ofFinrankEq T (ZMod p) h2 : T ≃ₗ[ZMod p] ZMod p)
    have e₂ : TensorProduct (ZMod p) M (ZMod p) ≃ₗ[ZMod p] M := TensorProduct.rid (ZMod p) M
    exact Finite.of_injective
      ((e.trans e₂ : TensorProduct (ZMod p) M T ≃ₗ[ZMod p] M) : TensorProduct (ZMod p) M T → M)
      (LinearEquiv.injective _)
  haveI : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    Finite.of_injective (fun f => (f : TensorProduct (ZMod p) M T → ZMod p))
      (fun f g hfg => LinearMap.ext (fun x => congrFun hfg x))
  have hE := (Work.SSGRoute.EulerSymm.eulerChar_decomp_notResidueChar p k Ω K A hA hp M).2
  have h02 := (Work.SSGRoute.LTD02Proved.local_tate_duality_02_proved p k Ω K ζ hζ hζK T hT
    A hA M).1
  have h1 := hC1a M A hA hp hram
  have h2 := hC1a (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A hA hp hram
  omega


/-- **Assembly (PROVED from R1 + C1a)**: the `hreal_unr` hypothesis of `finiteS_converse_canonical_v7`
(verbatim shape, all good places) for an abstract `pair` with the hub's clauses (2)–(4),(6). -/
theorem hreal_unr_assembly (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hC1a : ∀ (X : Type) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] [Finite X]
      (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation ((p : ℚ) : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K X (SSGRoute.decomp k A)) ≤
        Module.finrank (ZMod p) ↥(unrClasses p k Ω K X A))
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hcl : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
      (Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) ≤
        Module.finrank (ZMod p) ↥(unrClasses p k Ω K M A) +
        Module.finrank (ZMod p) ↥(unrClasses p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A)) →
      (∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
        lam (b + b') = lam b + lam b') →
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) →
      (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) → lam b = 0) →
      ∃ a : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) ∧
        ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          pair (SSGRoute.decomp k A) a b = lam b) :
    ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
        (∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          lam (b + b') = lam b + lam b') →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) → lam b = 0) →
        ∃ a : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) ∧
          ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            pair (SSGRoute.decomp k A) a b = lam b := by
  intro A hA hp hram lam h1 h2 h3
  have hp' : ¬ A.valuation ((p : ℚ) : Ω) < 1 := by rwa [Rat.cast_natCast]
  exact hcl A hA hp hram lam
    (unrCount_goodPlace_of_C1a p k Ω K ζ hζ hζK T hT hC1a M A hA hp' hram) h1 h2 h3

end Work.SSGRoute.LeadC8
