import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.LeadC8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# C1a: `dim H⁰(D_A,X) ≤ dim unrClasses`

At a finite place `A` of `Ω` unramified in `K/k` with `p` a unit of `A`, the unramified classes of
the local `H¹` — the `𝔽_p`-span of the classes of the locally constant `1`-cocycles of
`D_A = decomp k A` vanishing on the inertia `I_A` — have dimension at least `dim X^{D_A}`.

The proof has three ingredients, all already on disk:

* `Work.SSGRoute.finrank_H0loc_decomp` (degree-zero row of the two-row decomposition):
  `dim H⁰(D_A,X) = dim ker (conj₀ - 1)`, where `conj₀` is the conjugation action of a Frobenius
  lift `σ` on `H⁰(I_A,X) = X^{I_A}`;
* `Work.SSGRoute.HSTwoRow.ker_res1_finrank_eq_ker_conj0_loc`:
  `dim ker (res1 : H¹(D_A,X) → H¹(I_A,X)) = dim ker (conj₀ - 1)`;
* the elementary description of the kernel of the restriction: a class killed by `res1` is
  represented by a locally constant cocycle on `D_A` vanishing on `I_A`.  In fact
  `unrClasses p k Ω K X A = ker (res1)` on the nose (`unrClasses_eq_ker_res1` below).

Since `ker (res1) ≤ unrClasses`, monotonicity of the dimension gives the claim.  The arithmetic
structure of the place (`I_A` closed in `D_A`, normal there, `D_A = I_A ⊔ closure ⟨σ⟩` with
`I_A ⊓ closure ⟨σ⟩ = ⊥`, and `closure ⟨σ⟩` procyclic in the sense that it surjects onto every
`ZMod n`) is supplied by `exists_frobenius_complement`, `inertiaSub_le_decomp`,
`inertiaSub_isClosed_zhat`, `inertiaSub_normal` and `zhat_surjection_of_level`.

Only that group-theoretic input is used: the present inequality needs neither the vanishing of
`H²(I_A,–)` nor the finiteness of `H¹(I_A,–)`, and hence neither of the hypotheses `hp` (`p` a unit
of `A`) and `hram` (unramifiedness) beyond the fact that `A` is a finite place; they are kept in the
statement because the caller's interface carries them.

Note that `HSTwoRow/finrank_ker_res1_eq_ker_conj0.lean` (which carries the closely related
`finrank_ker_res1_eq_ker_conj0`, together with the `toClass` additivity helpers `cob_mem`,
`toClassSub`, `toClassSmul`) does not build, because its import
`Submission.Work.SSGRoute.HSTwoRow.extension_of_lcCocycle` is missing from the tree; it is listed in
`Submission/Work/SSGRoute/MISSING_MODULES_STATUS.md`.  Nothing here depends on it: the same
statement is available as `ker_res1_finrank_eq_ker_conj0_loc` in the buildable
`HSTwoRow/finrank_H1loc_decomp.lean`, and the few `toClass` manipulations needed below are done
directly from `LTDDefs/Basic.lean`.
-/

open Classical

namespace Work.SSGRoute.PT.LeadC8

set_option maxHeartbeats 1000000

/-! ## The kernel of the restriction to the inertia -/

/-- The unramified classes lie in the kernel of `res1`: a locally constant `1`-cocycle of `D_A`
vanishing on `I_A` restricts to the zero cocycle of `I_A`, which is a coboundary. -/
theorem unrClasses_le_ker_res1 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (A : ValuationSubring Ω) :
    Work.SSGRoute.LeadC8.unrClasses p k Ω K X A ≤
      LinearMap.ker (Work.SSGRoute.res1 p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)) := by
  classical
  rw [Work.SSGRoute.LeadC8.unrClasses, Submodule.span_le]
  rintro y ⟨f, hf, hvan, rfl⟩
  change Work.SSGRoute.res1 p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
    (Work.SSGRoute.inertiaSub_le_decomp k Ω A)
    (Work.SSGRoute.toClass p k Ω K X (SSGRoute.decomp k A) f) = 0
  rw [Work.SSGRoute.res1_toClass p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
    (Work.SSGRoute.inertiaSub_le_decomp k Ω A) f hf]
  have hfI : f ∈ Work.SSGRoute.lcCocycles p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) :=
    (Work.SSGRoute.restrictCocycle1 p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
      (Work.SSGRoute.inertiaSub_le_decomp k Ω A) ⟨f, hf⟩).2
  rw [Work.SSGRoute.toClass_eq_zero_iff p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) hfI]
  exact ⟨0, fun i hi => by rw [hvan i hi]; simp⟩

/-- A class killed by the restriction `res1 : H¹(D_A,X) → H¹(I_A,X)` is the class of a locally
constant `1`-cocycle on `D_A` vanishing on the inertia. -/
theorem ker_res1_le_unrClasses (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (A : ValuationSubring Ω) :
    LinearMap.ker (Work.SSGRoute.res1 p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)) ≤
      Work.SSGRoute.LeadC8.unrClasses p k Ω K X A := by
  classical
  intro y hy
  rw [LinearMap.mem_ker] at hy
  -- a locally constant cocycle on `D_A` representing `y`
  obtain ⟨f, hf, hfy⟩ :=
    Work.SSGRoute.toClass_surjective p k Ω K X (SSGRoute.decomp k A) y
  -- the restriction of `y` to the inertia is zero
  have hfI : f ∈ Work.SSGRoute.lcCocycles p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) :=
    (Work.SSGRoute.restrictCocycle1 p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
      (Work.SSGRoute.inertiaSub_le_decomp k Ω A) ⟨f, hf⟩).2
  have hzero : Work.SSGRoute.toClass p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) f = 0 := by
    rw [← Work.SSGRoute.res1_toClass p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
      (Work.SSGRoute.inertiaSub_le_decomp k Ω A) f hf, hfy]
    exact hy
  -- so `f` restricted to the inertia is a coboundary there
  obtain ⟨m, hm⟩ :=
    (Work.SSGRoute.toClass_eq_zero_iff p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) hfI).mp hzero
  -- subtract that coboundary: it is a locally constant cocycle on `D_A`
  set cob : (Ω ≃ₐ[k] Ω) → X := fun x => SSGRoute.res k K x • m - m with hcob
  have hcobmem : cob ∈ Work.SSGRoute.coboundaries p k Ω K X (SSGRoute.decomp k A) :=
    ⟨m, fun g _ => rfl⟩
  have hcoblc : cob ∈ Work.SSGRoute.lcCocycles p k Ω K X (SSGRoute.decomp k A) :=
    Work.SSGRoute.coboundaries_le_lcCocycles p k Ω K X (SSGRoute.decomp k A) hcobmem
  have hmem : f - cob ∈ Work.SSGRoute.lcCocycles p k Ω K X (SSGRoute.decomp k A) :=
    Submodule.sub_mem _ hf hcoblc
  have hvan : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → (f - cob) σ = 0 := by
    intro σ hσ
    have h := hm σ hσ
    rw [Pi.sub_apply, hcob, h, sub_self]
  have hclass : Work.SSGRoute.toClass p k Ω K X (SSGRoute.decomp k A) (f - cob) = y := by
    have hcob0 : Work.SSGRoute.toClass p k Ω K X (SSGRoute.decomp k A) cob = 0 :=
      (Work.SSGRoute.toClass_eq_zero_iff p k Ω K X (SSGRoute.decomp k A) hcoblc).mpr hcobmem
    have hadd := Work.SSGRoute.toClass_add p k Ω K X (SSGRoute.decomp k A) hmem hcoblc
    rw [show (f - cob) + cob = f from by ext x; simp, hcob0, add_zero] at hadd
    rw [← hfy]
    exact hadd.symm
  exact Submodule.subset_span ⟨f - cob, hmem, hvan, hclass⟩

/-- **The unramified classes are the kernel of the restriction to the inertia.** -/
theorem unrClasses_eq_ker_res1 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X]
    (A : ValuationSubring Ω) :
    Work.SSGRoute.LeadC8.unrClasses p k Ω K X A =
      LinearMap.ker (Work.SSGRoute.res1 p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)) :=
  le_antisymm (unrClasses_le_ker_res1 p k Ω K X A) (ker_res1_le_unrClasses p k Ω K X A)

/-! ## C1a -/

/-- **C1a.**  At a place unramified in `K/k` with `p` a unit, the unramified classes of `H¹_loc`
have dimension at least `dim X^{D_A}` (one inequality of the degree-0 part of local Tate duality).
`Work.SSGRoute.LeadC8.unrClasses p k Ω K X A` (defined in `Submission/Work/SSGRoute/PT/LeadC8.lean`)
is the span of the classes of the locally constant `1`-cocycles of `D_A = decomp k A` that vanish on
the inertia. -/
theorem finrank_H0loc_le_unrClasses (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] [Finite X]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hp : ¬ A.valuation ((p : ℚ) : Ω) < 1) (hram : ¬ SSGRoute.IsRamifiedIn k K A) :
    Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K X (SSGRoute.decomp k A)) ≤
      Module.finrank (ZMod p) ↥(Work.SSGRoute.LeadC8.unrClasses p k Ω K X A) := by
  classical
  -- the hypotheses `hp` and `hram` belong to the interface of the caller; this inequality only
  -- uses that `A` is a finite place (see the module docstring)
  have _hp := hp
  have _hram := hram
  -- the inertia structure of the finite place: `I_A` is closed in `D_A`, normal there, and has a
  -- procyclic complement `closure ⟨σ⟩` with `I_A ⊓ closure ⟨σ⟩ = ⊥` and `D_A ≤ I_A ⊔ closure ⟨σ⟩`
  obtain ⟨σ, hσD, hsup, hinf⟩ := Work.SSGRoute.exists_frobenius_complement k Ω A hA
  have hI : Work.SSGRoute.inertiaSub k Ω A ≤ SSGRoute.decomp k A :=
    Work.SSGRoute.inertiaSub_le_decomp k Ω A
  have hIclosed : IsClosed (Work.SSGRoute.inertiaSub k Ω A : Set (Ω ≃ₐ[k] Ω)) :=
    Work.SSGRoute.inertiaSub_isClosed_zhat k Ω A
  have hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ Work.SSGRoute.inertiaSub k Ω A,
      δ * u * δ⁻¹ ∈ Work.SSGRoute.inertiaSub k Ω A :=
    Work.SSGRoute.inertiaSub_normal k Ω A
  have hnorm2 : ∀ n ∈ Work.SSGRoute.inertiaSub k Ω A,
      σ⁻¹ * n * σ ∈ Work.SSGRoute.inertiaSub k Ω A :=
    fun n hn => hnorm σ⁻¹ ((SSGRoute.decomp k A).inv_mem hσD) n hn
  have hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
      Multiplicative (ZMod n), Function.Surjective f :=
    fun n hn => Work.SSGRoute.zhat_surjection_of_level p k Ω A hA σ hσD hsup n hn
  -- degree zero: `dim H⁰(D_A,X) = dim ker (conj₀ - 1)`
  have h0 := Work.SSGRoute.finrank_H0loc_decomp p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) σ A
    hI hσD hsup hnorm2
  -- degree one: `dim ker (res1) = dim ker (conj₀ - 1)`
  have hker := (Work.SSGRoute.HSTwoRow.ker_res1_finrank_eq_ker_conj0_loc p k Ω K A
    (Work.SSGRoute.inertiaSub k Ω A) σ hI hIclosed hnorm hσD hsup hinf hZ X hnorm2).2
  -- the kernel of the restriction consists of unramified classes
  have hsub : LinearMap.ker (Work.SSGRoute.res1 p k Ω K X (Work.SSGRoute.inertiaSub k Ω A) A
        (Work.SSGRoute.inertiaSub_le_decomp k Ω A)) ≤
      Work.SSGRoute.LeadC8.unrClasses p k Ω K X A :=
    (unrClasses_eq_ker_res1 p k Ω K X A).ge
  have hFinD : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K X (SSGRoute.decomp k A)) :=
    Work.SSGRoute.h1loc_decomp_finite p k Ω K A hA X
  calc Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K X (SSGRoute.decomp k A))
      = Module.finrank (ZMod p) ↥(LinearMap.ker (Work.SSGRoute.res1 p k Ω K X
          (Work.SSGRoute.inertiaSub k Ω A) A hI)) := h0.trans hker.symm
    _ ≤ Module.finrank (ZMod p) ↥(Work.SSGRoute.LeadC8.unrClasses p k Ω K X A) :=
        Submodule.finrank_mono hsub

end Work.SSGRoute.PT.LeadC8
