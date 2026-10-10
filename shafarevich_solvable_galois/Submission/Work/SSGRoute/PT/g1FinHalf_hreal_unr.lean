import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.NodeShim.g1FinHalfPairClauses
import Submission.Work.SSGRoute.PT.exists_finite_spanning_locCocycles
import Submission.Work.SSGRoute.PT.localPairing_surjective_dual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-! ## Inertia bookkeeping for `g1FinHalf_hreal_unr`

At a finite place `A` that is unramified in `K/k` the inertia `I_A` lies in `Gal(Ω/K)`, hence is
killed by `res k K`; therefore every coboundary on `decomp k A` (whose coefficient module carries
the `Gal(K/k)`-action through `res k K`) vanishes on `I_A`.  Consequently the property "vanishes on
the inertia" is a property of the *cohomology class* `b`, not only of the cocycle `b`: a cocycle
cohomologous to an inertia-vanishing one is itself inertia-vanishing.  This is the step of the
`hreal_unr` assembly which upgrades the realiser produced by the surjectivity of the local pairing
to an inertia-vanishing one. -/

/-- The inertia of a place unramified in `K/k` lies in `Gal(Ω/K)`. -/
theorem res_eq_one_of_isInertia_of_not_ramified (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (A : ValuationSubring Ω) [FiniteDimensional k K] [IsGalois k K]
    (hram : ¬ SSGRoute.IsRamifiedIn k K A)
    {σ : Ω ≃ₐ[k] Ω} (hσ : SSGRoute.IsInertia k A σ) :
    SSGRoute.res k K σ = 1 := by
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  rw [← MonoidHom.mem_ker, hker]
  by_contra h
  exact hram ⟨σ, hσ, h⟩

/-- A coboundary on `decomp k A` vanishes at the inertia of a place `A` unramified in `K/k`. -/
theorem isCoboundaryOn_apply_eq_zero_of_isInertia (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    {M : Type} [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]
    (A : ValuationSubring Ω) [FiniteDimensional k K] [IsGalois k K]
    (hram : ¬ SSGRoute.IsRamifiedIn k K A)
    {b : (Ω ≃ₐ[k] Ω) → M}
    (hb : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    {σ : Ω ≃ₐ[k] Ω} (hσ : SSGRoute.IsInertia k A σ) : b σ = 0 := by
  obtain ⟨m, hm⟩ := hb
  rw [hm σ hσ.1, res_eq_one_of_isInertia_of_not_ramified k Ω K A hram hσ, one_smul, sub_self]

/-- A cocycle cohomologous to an inertia-vanishing cocycle is itself inertia-vanishing (at a place
`A` unramified in `K/k`). -/
theorem eq_zero_of_isInertia_of_sub_isCoboundary (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    {M : Type} [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]
    (A : ValuationSubring Ω) [FiniteDimensional k K] [IsGalois k K]
    (hram : ¬ SSGRoute.IsRamifiedIn k K A)
    {b c : (Ω ≃ₐ[k] Ω) → M}
    (hc : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → c σ = 0)
    (hz : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) (b - c)) :
    ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0 := by
  intro σ hσ
  have h1 : (b - c) σ = 0 :=
    isCoboundaryOn_apply_eq_zero_of_isInertia k Ω K A hram hz hσ
  have h2 : b σ - c σ = 0 := by simpa using h1
  rw [hc σ hσ] at h2
  simpa using h2

/-! ## The `hreal_unr` node of `G1⁺`: route, and the two open inputs it consumes

**Goal** (`g1FinHalf_hreal_unr`).  At a *good* finite place `A` of `Ω` (`p` not in the maximal
ideal, `A` unramified in `K/k`), every functional `lam` on the locally constant
`M^∨(1) = DualMod p (M ⊗ T)`-cocycles of `decomp k A` which is additive on cocycles, kills the
coboundaries, and kills the cocycles vanishing on the inertia `I_A`, is represented through the
local pairing `G1pOwn.g1FinHalf` by a locally constant `M`-cocycle `a` that *vanishes on `I_A`*.

**Route** (all on-disk pieces are named):

1. `G1plusOwn.g1FinHalf_pairClauses` (`NodeShim/g1FinHalfPairClauses.lean`, proved) gives the
   clause bundle of `pair := g1FinHalf … M (decomp k A)`: additivity in each variable (needs
   `hχadd`, `hχcompat`), vanishing on a coboundary (needs `hχadd`), and **perfectness in each
   variable** (from `G1pOwn.g1FinHalf_perfect_left/_right`, whose `βl`/`pair` inputs are
   instantiated with `PT.finZB`/`g1FinHalf` and whose value formula is `g1FinHalf_hpair`).
2. `PT.exists_finite_spanning_locCocycles` (proved) at `M` and at `DualMod p (M ⊗ T)` supplies the
   finiteness of the two local `H¹`s.
3. `PT.localPairing_surjective_dual` (proved) then produces `a₀ : G_k → M`, a locally constant
   cocycle of `decomp k A` realising `lam`: `pair (decomp k A) a₀ b = lam b` for every locally
   constant cocycle `b`.
4. **The missing step**: `a₀` must be shown to *vanish on `I_A`*.  By
   `isCoboundaryOn_apply_eq_zero_of_isInertia` below, "vanishes on `I_A`" is a property of the
   cohomology class of `a₀` (coboundaries vanish on `I_A` because `hram` forces `res k K σ = 1`
   there), so this is the arithmetic statement that the class of `a₀` is *unramified* —
   equivalently, that the annihilator of the inertia-vanishing classes in the second variable is
   contained in the inertia-vanishing classes of the first: the "unramified subgroups are exact
   annihilators" half of local Tate duality (Milne, ADT I.2).  It does **not** follow from the
   clause bundle of step 1 (the clauses are invariant under scaling the pairing), and the lane's
   own verdict notes record the split into two open inputs:
   * **(unramified detection)** `E7cOmega.isUnramifiedExt_of_levelPair_unramified` (still `sorry`;
     its proved reduction `E7cΩ.isUnramifiedExt_of_detector` leaves a global unramified detector,
     `E7cOmega/unramifiedDetector_dwQuotientTransfer.lean`): it turns "`finZB(A) a₀` pairs to zero
     with every unramified class at every level" — which is the third hypothesis on `lam`,
     transported through the value formula `g1FinHalf_hpair` and the injectivity of `χ ∘ ι` on
     `p`-torsion (`hχinj`) — into `IsUnramifiedExt (finQ K A hA) (finZB … a₀)`;
   * **(converse of the dictionary's unramified clause)** `E1aClean.natFam_unramified_converse`
     (still `sorry`), the twin of `finZB_unramified`: with `finZB`'s kernel and surjectivity
     clauses it is equivalent to the cardinality statement
     `Nat.card {unramified classes of H¹_loc(D_A, M)} = Nat.card {unramified Ext¹-classes}`
     recommended as a standalone node in
     `E1aClean/NOTE_natFam_unramified_converse_verdict.md`.  Given it, unramifiedness of
     `finZB(A) a₀` yields `a₀ σ = 0` for `σ ∈ I_A`, i.e. the conclusion.
5. With `a₀` inertia-vanishing, the pairing identity of step 3 *is* the conclusion.

**Certification status (measured, 2026-10).**  The *type* of `g1FinHalf_hreal_unr` mentions
`Work.SSGRoute.PT.G1pOwn.g1FinHalf`, whose body reaches `finAtValue → finZZ → PT.finZB =
Classical.choose (E1aClean.localDictionary_natural_family_arch …)`, and that theorem is still
`by sorry` (line 337 of `E1aClean/localDictionary_natural_family.lean`).  Since `#print axioms`
traverses the type, *any* declaration whose type mentions `g1FinHalf` reports `sorryAx` (measured:
`#print axioms Work.SSGRoute.PT.G1pOwn.g1FinHalf_add_left = [propext, sorryAx, Classical.choice,
Quot.sound]`; likewise a two-line probe whose type is `(g1FinHalf … = g1FinHalf …) → True` and whose
proof is `fun _ => trivial`).  As the permitted axioms are `{propext, Quot.sound, Classical.choice}`,
no proof of this statement can pass the finishing check while that node is open — the defect the
lead's own design note rules about ("NEVER mention `finZB` / `g1FinHalf` in any statement you
dispatch", `_lead_design/v4_0215/NOTE.md`).  So the statement should be re-filed over the abstract
`pair`/dictionary interface, or kept as a hypothesis (as `finiteS_converse_canonical_v5/v7`
already do), with the two inputs of step 4 as explicit hypotheses. -/
/-- **The formal part of `g1FinHalf_hreal_unr`**, with the one missing arithmetic input isolated as
an explicit hypothesis `hann`.

`hann` is the unramified annihilator half of local Tate duality *in the language of the local
pairing itself*: a locally constant cocycle `a` of `decomp k A` which pairs to zero with every
locally constant cocycle vanishing on the inertia `I_A`, vanishes on `I_A`.  Equivalently (by the
perfectness clauses and the vanishing of the pairing of two inertia-vanishing cocycles) it is the
inclusion `ann(unr W) ⊆ unr V`, i.e. the "unramified subgroups are exact annihilators" half of
Milne, ADT I.2; it is *not* a consequence of the clause bundle of the pairing, and it is what the
open nodes `E7cOmega.isUnramifiedExt_of_levelPair_unramified` and
`E1aClean.natFam_unramified_converse` (and their on-disk verdict notes) supply.

Everything else is proved here: the clause bundle (`G1plusOwn.g1FinHalf_pairClauses`), the finite
spanning of the two local `H¹`'s (`PT.exists_finite_spanning_locCocycles`), the realisation of
`lam` (`PT.localPairing_surjective_dual`), and the transport of the third hypothesis `h3` on `lam`
to the annihilator hypothesis (pure rewrite through the realisation). -/
theorem g1FinHalf_hreal_unr_of_annihilator (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L hKL u = 0 → u = 0)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hann : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ a : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
          Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M
            (SSGRoute.decomp k A) a b = 0) →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
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
            Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M
              (SSGRoute.decomp k A) a b = lam b := by
  classical
  intro A hA hp hram lam h1 h2 h3
  -- the clause bundle of the finite half at `decomp k A`
  have hpc := Work.SSGRoute.PT.G1plusOwn.g1FinHalf_pairClauses p k Ω K ζ hζ hζK T hT χ
    hχadd hχinj hχcompat M A hA
  obtain ⟨hadd_l, hadd_r, hcob, hperf_l, hperf_r⟩ := hpc
  -- finiteness of the two local `H¹`s
  haveI hXfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    Work.SSGRoute.PT.G1plusOwn.g1l_finite_dualMod_tensor p k Ω K ζ hζ hζK T hT M
  obtain ⟨nA, φA, hφA⟩ := Work.SSGRoute.PT.exists_finite_spanning_locCocycles p k Ω K M A hA
  obtain ⟨nB, ψB, hψB⟩ :=
    Work.SSGRoute.PT.exists_finite_spanning_locCocycles p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A hA
  -- the realiser of `lam` through the local pairing
  obtain ⟨a, hac, hal, haeq⟩ := Work.SSGRoute.PT.localPairing_surjective_dual p k Ω K T M A hA
    (fun H a b => Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b)
    (fun a a' b ha hla ha' hla' hb hlb =>
      hadd_l a a' b ⟨ha, hla⟩ ⟨ha', hla'⟩ ⟨hb, hlb⟩)
    (fun a b b' ha hla hb hlb hb' hlb' =>
      hadd_r a b b' ⟨ha, hla⟩ ⟨hb, hlb⟩ ⟨hb', hlb'⟩)
    (fun a b ha hla hb hlb hk => hcob a b ⟨ha, hla⟩ ⟨hb, hlb⟩ hk)
    (fun a ha hla hzero => hperf_l a ⟨ha, hla⟩ (fun b hb => hzero b hb.1 hb.2))
    (fun b hb hlb hzero => hperf_r b ⟨hb, hlb⟩ (fun a ha => hzero a ha.1 ha.2))
    ⟨nA, φA, hφA⟩ ⟨nB, ψB, hψB⟩ lam h1 h2
  refine ⟨a, hac, hal, ?_, fun b hbc hbl => haeq b hbc hbl⟩
  -- the third hypothesis on `lam` is exactly the annihilator hypothesis for `a`
  refine hann A hA hp hram a hac hal ?_
  intro b hbc hbl hbin
  rw [haeq b hbc hbl]
  exact h3 b hbc hbl hbin

theorem g1FinHalf_hreal_unr (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L hKL u = 0 → u = 0)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
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
            Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M
              (SSGRoute.decomp k A) a b = lam b := by sorry

end Work.SSGRoute.PT
