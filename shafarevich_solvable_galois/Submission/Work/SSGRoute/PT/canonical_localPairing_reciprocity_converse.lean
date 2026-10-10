import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.NodeShim.coherentPTorsionKx
import Submission.Work.SSGRoute.PT.LeadC8.finrank_H0loc_le_unrClasses
import Submission.Work.SSGRoute.PT.LeadC8.hreal_unr_of_unrCount
import Submission.Work.SSGRoute.PT.archFamilyClauses
import Submission.Work.SSGRoute.PT.finiteS_converse_canonical_v8
import Submission.Work.SSGRoute.PT.glueOfTwoHalves
import Submission.Work.SSGRoute.PT.hrecJoint_archFamily
import Submission.Work.SSGRoute.PT.localLevelExistence
import Submission.Work.SSGRoute.PT.relaxed_converse_of_finiteS_v3

/-! Guidance from the project lead (the requester):

Lead guidance. The design is in the workspace at _lead_design/ssg_pt_design_1002/DESIGN.md. Read the section for your statement FIRST (§2 C6 via the induced module from the normal closure of inertia; §3 CRUX-a 3-step; §4 G1+COUNT via the canonical class-formation pairing). It gives the proof route as numbered steps and the proved workspace names to reuse (local_duality_ext_in, detectsAt_of_coeff_surjection, grunwald_over_K_general, countingIdentity_of_reciprocity_and_converse, ...). Do not re-derive what is proved.
Memory: Lean only through the harness; no sleep loops around lake.
-/

namespace Work.SSGRoute.PT

open scoped TensorProduct
open CategoryTheory

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

/-- The canonical local pairing with reciprocity (`G1`) together with the converse that makes the
counting identity (`COUNT`) hold: one family `pair`, clauses (1)–(7) verbatim from
`Work.SSGRoute.canonical_localPairing_with_reciprocity`, plus clause (8): local data `(α, β)` at
`S ∪ C` whose product-form sum vanishes against every relaxed dual Selmer class (coboundary at the
places split in `N` off `S`, unramified at the others) is realized by a global cocycle unramified
outside `S ∪ cs(N)` (`PT.IsRealizableClass`).  So `G1` is the first two conjuncts, and `COUNT`
follows from `PT.countingIdentity_of_reciprocity_and_converse` with `hconv` read off clause (8)
(`PT.productFormFun_primalClassOf` translates classes to representatives).

Route (DESIGN.md §B; no local invariant map, no cup products, no Euler characteristic).
Define `pair M H a b` at a finite place `H = decomp k A` by choosing a finite Galois level
`L ≤ Ω` where `a|_H`, `b|_H` factor, and setting
`pair = χ_L (ι_{w'} (levelPair (βl a) [b]))`, where `βl` is the local dictionary of
`ext_h1_localGlobal_dictionary`, `[b] ∈ H¹(D_{w'}, M')`, `ι_{w'}` places a class of
`H²(D_{w'}, L_{w'}ˣ)` at the orbit of `w'` in `H²(Gal(L/k), 𝕀_L)` and maps it to `C_L`, and
`χ` is `pt_coherent_pTorsion_invariant`.  At an involution use the same recipe at the real place
(for odd `p` every value is `0`).  Then: (1)–(3),(5) are Yoneda linearity and naturality; (4) is
`Work.SSGRoute.local_duality_ext_in` (both clauses, proved) plus injectivity of `ι` on `p`-torsion
(`pt_orbitIdele_H2_eq_zero`) and of `χ`; (6) is the vanishing of the Yoneda product of two
unramified classes (`ValuationSES`); (7) is the class formation: the sum of the local values of a
global pair is `χ_L` of the image of a class of `H²(Gal(L/k), Lˣ)` in `C_L`, which is `0`
(uses the square (c) of `ext_h1_localGlobal_dictionary` and `PT.extLoc_yonedaPair`); (8) is the
middle exactness: lift the data to `X ∈ Ext¹(M', 𝕀_K)` (`ext_idele_shapiro`), relax at `cs(N)`, then
the value formula `χ_L (phiAt (extToClasses X) h) = Σ_v pair_v` (definitional, plus
`e9_glue_phiAt`) and orthogonality give `PhiOneVanishesIn`, so `extToClasses X = 0` by
`phi1_mono_sylow_in`, and `PT.pt_extSegment_exact` (i) with the square (c) produces `ε`. -/
theorem canonical_localPairing_reciprocity_converse
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∃ pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
          [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (∀ H : Subgroup (Ω ≃ₐ[k] Ω),
          ((∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) ∨
            (∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ H = Subgroup.zpowers c)) →
          -- (1)+(2) additive in each variable on locally constant cocycles
          (∀ (a a' : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            pair M H (a + a') b = pair M H a b + pair M H a' b) ∧
          (∀ (a : (Ω ≃ₐ[k] Ω) → M)
              (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
            pair M H a (b + b') = pair M H a b + pair M H a b') ∧
          -- (3) zero on a coboundary
          (∀ (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
              SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
            pair M H a b = 0) ∧
          -- (4) perfect in each variable
          (∀ a : (Ω ≃ₐ[k] Ω) → M,
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
              (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
              pair M H a b = 0) →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a) ∧
          (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (∀ a : (Ω ≃ₐ[k] Ω) → M,
              (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
              pair M H a b = 0) →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) ∧
          -- (5) naturality in the coefficient module (transpose of `f ⊗ id_T`)
          (∀ (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
              [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
              (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
              (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
                Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
              (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
                f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
              (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            pair M₂ H (fun σ => f (a σ)) b = pair M H a (fun σ => f' (b σ))) ∧
          -- (6) orthogonality on unramified classes at good places
          (∀ (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
            SSGRoute.IsFinPlace k A → ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
            (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) →
            pair M (SSGRoute.decomp k A) a b = 0))) ∧
      -- (7) reciprocity
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
          [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
          (a : (Ω ≃ₐ[k] Ω) → M)
          (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
          ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
        ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
        (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
        (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
        ∑ A ∈ S', pair M (SSGRoute.decomp k A) a b +
          ∑ c ∈ C', pair M (Subgroup.zpowers c) a b = 0) ∧
      -- (8) the converse: local data orthogonal to the relaxed dual Selmer classes is realizable
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
          [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
          (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N], K ≤ N →
        ∀ (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
          ∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ (C : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C, c ^ 2 = 1) →
        (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
        (∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
        ∀ (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M),
        (∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A)) →
        (∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c)) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) →
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0) →
          ∑ A ∈ S, pair M (SSGRoute.decomp k A) (α A) b +
            ∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b = 0) →
        ∃ ε : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
          (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun σ => ε σ - α A σ)) ∧
          (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
            (fun σ => ε σ - β c σ)) ∧
          ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0) := by
  classical
  -- ## The coherent `p`-torsion invariant `χ` (S1, proved).
  obtain ⟨χ, hχadd, hχinj, hχcompat⟩ :=
    Work.SSGRoute.PT.coherent_pTorsion_chi_k_of_KΩ (p := p) (k := k) (Ω := Ω) (K := K)
  -- ## The coefficient module `T` is finite (`IsCyclotomicDual` says `finrank = 1`); the archimedean
  -- half `PT.archFamily` needs it as an instance.
  haveI hTfin : Finite T := by
    haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
    exact Module.finite_of_finite (ZMod p)
  -- ## The seam embeddings of the involutions (`ArchPlace.exists_conjEmbedding`: every nontrivial
  -- involution of `G_k` is complex conjugation for some embedding of `Ω` in `ℂ`).
  let φc : (c : Ω ≃ₐ[k] Ω) → c ^ 2 = 1 → c ≠ 1 → Ω →+* ℂ :=
    fun c hc2 hc1 => Classical.choose (Work.SSGRoute.ArchPlace.exists_conjEmbedding k Ω c hc2 hc1)
  have hφc : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
      φc c hc2 hc1 (c x) = starRingEnd ℂ (φc c hc2 hc1 x) :=
    fun c hc2 hc1 =>
      Classical.choose_spec (Work.SSGRoute.ArchPlace.exists_conjEmbedding k Ω c hc2 hc1)
  -- ## The involution half `arch` of the glued family: the class-formation pairing `PT.archFamily`,
  -- which is `PT.archPairLocal` at the canonical generator of an involution group and `0` at `⊥`
  -- (`PT/PING_s18_arch_zero_at_bot.md`).
  let arch : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p :=
    fun M _ _ _ _ _ => archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M
  -- its clauses (1)-(4) and its clause (5), in the shapes `glueOfTwoHalves` consumes
  have harch_clauses : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (c : Ω ≃ₐ[k] Ω), c ^ 2 = 1 →
      H1Pair.PairClauses p K T M (fun a b => arch M (Subgroup.zpowers c) a b)
        (Subgroup.zpowers c) :=
    fun M _ _ _ _ _ c hc => archFamily_clauses p k Ω K ζ hζ hζK T hT χ hχadd hχinj φc hφc M c hc
  have harch_nat : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
      [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
      (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
      (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
        Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
        f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
      (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
      (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a ∧
        SSGRoute.IsLocConstOn (Subgroup.zpowers c) a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
        SSGRoute.IsLocConstOn (Subgroup.zpowers c) b) →
      arch M₂ (Subgroup.zpowers c) (fun σ => f (a σ)) b =
        arch M (Subgroup.zpowers c) a (fun σ => f' (b σ)) :=
    fun M _ _ _ _ _ M₂ _ _ _ _ _ f hf f' hff' c hc a b ha hb =>
      archFamily_natural p k Ω K ζ hζ hζK T hT χ hχcompat φc hφc M M₂ f hf f' hff' c hc a b
        ha hb
  -- ## The finite-place half `fin` (node `PT.finAtValue`, complete).
  let fin : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p :=
    fun M _ _ _ _ _ H a b =>
      G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M H a b
  -- ## The *guarded* finite-place half `finG`: it agrees with `fin` on cocycles and is `0` off them.
  --
  -- The extra guard on the *first* variable is what makes clause (8) reachable: the interfaces of
  -- `finiteS_converse_canonical_v4` / `_v7` contain the hypothesis `hpair_unr` (at a good place, a
  -- pair of inertia-vanishing cocycles pairs to `0`) stated **without** any cocycle hypothesis, which
  -- `fin` (= the guarded `g1FinHalf`, whose *value formula* `hpair` is only available on cocycles)
  -- cannot satisfy.  `finG` satisfies `hpair_unr` (off cocycles it is `0`), while the *weakened* value
  -- formula it satisfies — with `βl := βlG` below, `0` off cocycles — is exactly what v4/v7 use.
  -- All clauses (1)-(7) hold for `finG`: their hypotheses always include `IsCocycleOn` of the first
  -- variable, so `finG = fin` there.
  let finG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p :=
    fun M _ _ _ _ _ H a b =>
      if _hcocycle : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a then fin M H a b else 0
  have finG_eq : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) H a → finG M H a b = fin M H a b :=
    fun M _ _ _ _ _ H a b ha => dif_pos ha
  have hclauses : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      H1Pair.PairClauses p K T M (fun a b => fin M (SSGRoute.decomp k A) a b)
        (SSGRoute.decomp k A) := by
    intro M _ _ _ _ _ A hA
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- clause (1): additivity in the first variable
      intro a a' b ha ha' hb
      have hla := ha.2
      have hla' := ha'.2
      have hlb := hb.2
      exact G1pOwn.g1FinHalf_add_left p k Ω K ζ hζ hζK T hT χ hχadd M A hA a a' b
        hla hla' hlb (SSGRoute.IsLocConstOn.add hla hla') ha.1 ha'.1
    · -- clause (2): additivity in the second variable
      intro a b b' ha hb hb'
      exact G1pOwn.g1FinHalf_add_right p k Ω K ζ hζ hζK T hT χ hχcompat hχadd M A hA a b b'
        ha.2 hb.2 hb'.2 (SSGRoute.IsLocConstOn.add hb.2 hb'.2) hb.1 hb'.1
    · -- clause (3): vanishing when one argument is a coboundary
      intro a b ha hb hcob
      exact G1pOwn.g1FinHalf_coboundary p k Ω K ζ hζ hζK T hT χ hχadd M A hA a b
        ha.2 hb.2 ha.1 hb.1 hcob
    · -- clause (4), left: perfectness in the first variable.
      -- `G1plusOwn.g1FinHalf_perfect_left` (the lane's restatement of the proved perfectness
      -- clause over the abstract `βl`/`pair`/`hpair` interface; 0 `sorry`s) with the value
      -- the binder-instance form is unsatisfiable for `pair := g1FinHalf`, whose type is
      -- instance-free), at the natural dictionary `finZB` (its clauses from `PT.finZB_spec`),
      -- the pairing `fin` and the value formula `G1plusOwn.g1FinHalf_hpair`.
      intro a ha h
      exact G1plusOwn.g1FinHalf_perfect_left p k Ω K ζ hζ hζK T hT χ hχadd hχinj hχcompat M
        (fun A' hA' => finZB p K ζ hζ hζK T hT M A' hA')
        (fun A' hA' b b' hb hlb hb' hlb' =>
          finZB_add p k Ω K ζ hζ hζK T hT M A' hA' b b' hb hlb hb' hlb')
        (fun A' hA' b hb hlb => finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A' hA' b hb hlb)
        (fun A' hA' y => finZB_surjective p k Ω K ζ hζ hζK T hT M A' hA' y)
        (fun A' hA' hpA' hramA' b hb hlb hiner =>
          finZB_unramified p k Ω K ζ hζ hζK T hT M A' hA' hpA' hramA' b hb hlb hiner)
        (fun H a b => fin M H a b)
        (fun A' hA' a b hla hlb hb L _ _ _ hKL _ _ _ b₀ hb₀ =>
          G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A' hA' a b hla hlb hb
            L hKL b₀ hb₀)
        A hA a ha.1 ha.2 (fun b hb => h b hb)
    · -- clause (4), right: perfectness in the second variable
      -- (`G1plusOwn.g1FinHalf_perfect_right`, the same restatement in the second variable).
      intro b hb h
      exact G1plusOwn.g1FinHalf_perfect_right p k Ω K ζ hζ hζK T hT χ hχadd hχinj hχcompat M
        (fun A' hA' => finZB p K ζ hζ hζK T hT M A' hA')
        (fun A' hA' b b' hb hlb hb' hlb' =>
          finZB_add p k Ω K ζ hζ hζK T hT M A' hA' b b' hb hlb hb' hlb')
        (fun A' hA' b hb hlb => finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A' hA' b hb hlb)
        (fun A' hA' y => finZB_surjective p k Ω K ζ hζ hζK T hT M A' hA' y)
        (fun A' hA' hpA' hramA' b hb hlb hiner =>
          finZB_unramified p k Ω K ζ hζ hζK T hT M A' hA' hpA' hramA' b hb hlb hiner)
        (fun H a b => fin M H a b)
        (fun A' hA' a b hla hlb hb L _ _ _ hKL _ _ _ b₀ hb₀ =>
          G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A' hA' a b hla hlb hb
            L hKL b₀ hb₀)
        A hA b hb.1 hb.2 (fun a ha => h a ha)
  have hnat : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
      [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
      (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
      (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
        Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
        f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
      (H : Subgroup (Ω ≃ₐ[k] Ω))
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      fin M₂ H (fun σ => f (a σ)) b = fin M H a (fun σ => f' (b σ)) := by
    intro M _ _ _ _ _ M₂ _ _ _ _ _ f hf f' hff' H a b ha hb
    by_cases h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A
    · obtain ⟨A, hA, rfl⟩ := h
      exact G1pOwn.g1FinHalf_natural p k Ω K T ζ hζ hζK hT χ hχcompat M M₂ f hf f' hff'
        A hA a b ha hb
    · rw [show fin M₂ H (fun σ => f (a σ)) b = 0 from
            G1pOwn.g1FinHalf_eq_zero_of_not p k Ω K ζ hζ hζK T hT χ M₂ H
              (fun σ => f (a σ)) b h,
          show fin M H a (fun σ => f' (b σ)) = 0 from
            G1pOwn.g1FinHalf_eq_zero_of_not p k Ω K ζ hζ hζK T hT χ M H
              a (fun σ => f' (b σ)) h]
  have horth : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
      (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
      (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0),
      fin M (SSGRoute.decomp k A) a b = 0 := by
    -- Clause (6), proved directly from the *proved* level-existence
    -- `PT.exists_unramified_level_factors_clean` (this file's clean replacement for the lane's
    -- `G1plusOwn.exists_unramified_level_factors`): the level that both factors `b` and is
    -- unramified at `A`, the unramified dictionary class (`finZB_unramified`) and the value formula
    -- (`G1plusOwn.g1FinHalf_hpair`).
    intro M _ _ _ _ _ A hA hpA hramA a b ha hb hiner
    obtain ⟨L, hLnf, hLfd, hLgal, hKL, hunr, b₀, hb₀⟩ :=
      exists_unramified_level_factors_clean (p := p) (K := K) (T := T) (M := M) (A := A)
        hA hramA b hb.1 hb.2 (fun σ hσ => (hiner σ hσ).2)
    haveI : NumberField ↥L := hLnf
    haveI : FiniteDimensional k L := hLfd
    haveI : IsGalois k L := hLgal
    letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
    haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    -- the value formula at the level `L`
    show Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M
      (SSGRoute.decomp k A) a b = 0
    rw [G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A hA a b ha.2 hb.2 hb.1
      L hKL b₀ hb₀]
    -- the level pairing vanishes: the dictionary class is unramified and so is the level at `A`
    have hz : SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
        (Work.SSGRoute.PT.finZI hKL A hA)
        (Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M A hA a)
        (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb.1 b₀ hb₀) = 0 := by
      have hw' : NK.GlobalCFT.Place.LiesOver
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) :=
        (Work.SSGRoute.PT.place_glue_level k Ω K L hKL A hA (Work.SSGRoute.PT.finQ K A hA)
          (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
          (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)).1
      refine Work.SSGRoute.PT.levelPair_unramified_eq_zero (k := k) (K := ↥K)
        (M := SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
        (w := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (L := ↥L)
        (q' := Work.SSGRoute.PT.finQW L A hA) (hw' := hw') (hunr := hunr)
        (f := Work.SSGRoute.PT.finZF hKL A hA) (hf := Work.SSGRoute.PT.finZF_spec hKL A hA)
        (ι := Work.SSGRoute.PT.finZI hKL A hA) ?_
        (y := Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M A hA a)
        (hy := finZB_unramified p k Ω K ζ hζ hζK T hT M A hA hpA hramA a ha.1 ha.2
          (fun σ hσ => (hiner σ hσ).1))
        (h := Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb.1 b₀ hb₀)
      intro u
      simp only [Work.SSGRoute.PT.finZI]
      exact Work.SSGRoute.PT.localUnitsMapAt_spec k ↥K ↥L
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) hw'
        (Work.SSGRoute.PT.finZF hKL A hA) (Work.SSGRoute.PT.finZF_spec hKL A hA) u
    rw [hz, Work.SSGRoute.PT.iota_zero]
    -- `χ 0 = 0`
    have hχ0 : χ L hKL (0 : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) = 0 := by
      have h := hχadd L hKL 0 0 (by simp) (by simp)
      rw [add_zero] at h
      have h2 : χ L hKL 0 + χ L hKL 0 = χ L hKL 0 + 0 := by rw [h.symm, add_zero]
      exact add_left_cancel h2
    exact hχ0
  have hrecJoint : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
      (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
        ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
          ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
      ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
      (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
      (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
      ∑ A ∈ S', fin M (SSGRoute.decomp k A) a b +
        ∑ c ∈ C', arch M (Subgroup.zpowers c) a b = 0 := by
    intro M _ _ _ _ _ a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hS'unram C' hC'inv hC'rep hC'disj
    -- Clause (7) for **all** `p`: the class-formation reciprocity of the two halves,
    -- `PT.hrecJoint_archFamily` (the finite half `G1pOwn.g1FinHalf` plus the involution half
    -- `PT.archFamily`), which subsumes the `p ≠ 2`-only `G1plusOwn.reciprocityFiniteClause`.
    exact hrecJoint_archFamily p k Ω K ζ hζ hζK T hT χ hχadd hχcompat φc hφc M a b
      ha1 ha2 hb1 hb2 S' hS'fin hS'disj hS'unram C' hC'inv hC'rep hC'disj
  -- ## The clause bundles for the *guarded* half `finG`: every hypothesis below carries
  -- `IsCocycleOn _` of the first variable, so `finG` may be replaced by `fin` there.
  have hclausesGG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      H1Pair.PairClauses p K T M (fun a b => finG M (SSGRoute.decomp k A) a b)
        (SSGRoute.decomp k A) := by
    intro M _ _ _ _ _ A hA
    obtain ⟨c1, c2, c3, c4, c5⟩ := hclauses M A hA
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a a' b ha ha' hb
      show finG M (SSGRoute.decomp k A) (a + a') b
        = finG M (SSGRoute.decomp k A) a b + finG M (SSGRoute.decomp k A) a' b
      rw [finG_eq M (SSGRoute.decomp k A) (a + a') b (SSGRoute.IsCocycleOn.add ha.1 ha'.1),
        finG_eq M (SSGRoute.decomp k A) a b ha.1,
        finG_eq M (SSGRoute.decomp k A) a' b ha'.1]
      exact c1 a a' b ha ha' hb
    · intro a b b' ha hb hb'
      show finG M (SSGRoute.decomp k A) a (b + b')
        = finG M (SSGRoute.decomp k A) a b + finG M (SSGRoute.decomp k A) a b'
      rw [finG_eq M (SSGRoute.decomp k A) a (b + b') ha.1,
        finG_eq M (SSGRoute.decomp k A) a b ha.1,
        finG_eq M (SSGRoute.decomp k A) a b' ha.1]
      exact c2 a b b' ha hb hb'
    · intro a b ha hb hcob
      show finG M (SSGRoute.decomp k A) a b = 0
      rcases hcob with hcob | hcob
      · rw [finG_eq M (SSGRoute.decomp k A) a b
          (SSGRoute.isCocycleOn_of_isCoboundaryOn (act := SSGRoute.res k K) hcob)]
        exact c3 a b ha hb (Or.inl hcob)
      · rw [finG_eq M (SSGRoute.decomp k A) a b ha.1]
        exact c3 a b ha hb (Or.inr hcob)
    · intro a ha h
      refine c4 a ha (fun b hb => ?_)
      show fin M (SSGRoute.decomp k A) a b = 0
      rw [← finG_eq M (SSGRoute.decomp k A) a b ha.1]
      exact h b hb
    · intro b hb h
      refine c5 b hb (fun a ha => ?_)
      show fin M (SSGRoute.decomp k A) a b = 0
      rw [← finG_eq M (SSGRoute.decomp k A) a b ha.1]
      exact h a ha
  have hnatGG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
      [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
      (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
      (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
        Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
        f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
      (H : Subgroup (Ω ≃ₐ[k] Ω))
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      finG M₂ H (fun σ => f (a σ)) b = finG M H a (fun σ => f' (b σ)) := by
    intro M _ _ _ _ _ M₂ _ _ _ _ _ f hf f' hff' H a b ha hb
    have hcocf : SSGRoute.IsCocycleOn (SSGRoute.res k K) H (fun σ => f (a σ)) := by
      intro g hg h hh
      show f (a (g * h)) = f (a g) + SSGRoute.res k K g • f (a h)
      rw [ha.1 g hg h hh, map_add, hf]
    rw [finG_eq M₂ H (fun σ => f (a σ)) b hcocf,
      finG_eq M H a (fun σ => f' (b σ)) ha.1]
    exact hnat M M₂ f hf f' hff' H a b ha hb
  have horthGG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
      (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
      (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0),
      finG M (SSGRoute.decomp k A) a b = 0 := by
    intro M _ _ _ _ _ A hA hpA hramA a b ha hb hiner
    rw [finG_eq M (SSGRoute.decomp k A) a b ha.1]
    exact horth M A hA hpA hramA a b ha hb hiner
  have hrecJointGG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
      (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
        ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
          ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
      ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
      (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
      (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
      ∑ A ∈ S', finG M (SSGRoute.decomp k A) a b +
        ∑ c ∈ C', arch M (Subgroup.zpowers c) a b = 0 := by
    intro M _ _ _ _ _ a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hS'unram C' hC'inv hC'rep hC'disj
    have hsum : (∑ A ∈ S', finG M (SSGRoute.decomp k A) a b)
        = ∑ A ∈ S', fin M (SSGRoute.decomp k A) a b :=
      Finset.sum_congr rfl (fun A _ =>
        finG_eq M (SSGRoute.decomp k A) a b
          (SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top ha1))
    rw [hsum]
    exact hrecJoint M a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hS'unram C' hC'inv hC'rep hC'disj
  -- ## The glued family (clauses (1)-(7)).
  --
  -- It is introduced as an explicit `let` (rather than as the `obtain`ed witness of
  -- `glueOfTwoHalves`) so that clause (8) can rewrite `pair` at a decomposition group by
  -- `pairGlueArch_decomp`; the four clauses are the four components of `glueOfTwoHalves`.
  let pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p :=
    fun M _ _ _ _ _ => pairGlueArch p k Ω K ζ hζ hζK T hT finG arch M
  have hpc : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (H : Subgroup (Ω ≃ₐ[k] Ω)), H1Pair.IsLocalGroup k Ω H →
      H1Pair.PairClauses p K T M (fun a b => pair M H a b) H :=
    fun M _ _ _ _ _ => pairGlueArch_pairClauses p k Ω K ζ hζ hζK T hT finG arch hclausesGG
      harch_clauses (E7Arch.localGroupDisjoint k Ω) M
  have hnatG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
      [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
      (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
      (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
        Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
        f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
      (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H1Pair.IsLocalGroup k Ω H)
      (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      pair M₂ H (fun σ => f (a σ)) b = pair M H a (fun σ => f' (b σ)) :=
    pairGlueArch_naturality p k Ω K ζ hζ hζK T hT finG arch hnatGG harch_nat
      (E7Arch.localGroupDisjoint k Ω)
  have horthG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
      (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
      (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
      (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0),
      pair M (SSGRoute.decomp k A) a b = 0 :=
    pairGlueArch_orth p k Ω K ζ hζ hζK T hT finG arch horthGG (E7Arch.localGroupDisjoint k Ω)
  have hrecG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      H1Pair.PairReciprocity p K T M (fun H a b => pair M H a b) :=
    fun M _ _ _ _ _ => pairGlueArch_reciprocity p k Ω K ζ hζ hζK T hT finG arch hrecJointGG
      (E7Arch.localGroupDisjoint k Ω) M
  refine ⟨pair, ?_, ?_, ?_⟩
  · intro M _ _ _ _ _ H hH
    obtain ⟨pc1, pc2, pc3, pc4, pc5⟩ := hpc M H hH
    refine ⟨pc1, pc2, pc3, pc4, pc5, ?_, ?_⟩
    · intro M₂ _ _ _ _ _ f hf f' hff' a b ha hb
      exact hnatG M M₂ f hf f' hff' H hH a b ha hb
    · intro A a b hA hp hram ha hb hiner
      exact horthG M A hA hp hram a b ha hb hiner
  · intro M _ _ _ _ _ a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hS'unram C' hC'inv hC'rep hC'disj
    exact hrecG M a b ha1 ha2 hb1 hb2 S' hS'fin hS'disj hS'unram C' hC'inv hC'rep hC'disj
  · -- ## Clause (8): the relaxed converse, via `relaxed_converse_of_finiteS_v3`
    -- with `finiteS_converse_canonical_v8` as its `hfinS`, the guarded dictionary `βlG`,
    -- the value formula `hpairG`, the cocycle-free orthogonality `hpairUnrG`, `hreal` from
    -- `PT.localPairing_surjective_dual` + `PT.exists_finite_spanning_locCocycles`, and
    -- `hreal_unr` from `LeadC8.hreal_unr_assembly` (C1a + R1).
    intro M _ _ _ _ _ N _ _ hKN S hSfin hSdisj hSram C hCinv hC hCdisj α β hα hβ horth8
    -- ### a plain ring hom `Ω →+* ℂ`, used only to fill the values of the *total* seam embedding
    -- away from the involutions
    haveI : CharZero Ω :=
      charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k Ω)
    haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
    let φdefault : Ω →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := Ω) (M := ℂ)).toRingHom
    let φcTot : (c : Ω ≃ₐ[k] Ω) → Ω →+* ℂ := fun c =>
      if h : c ^ 2 = 1 ∧ c ≠ 1 then φc c h.1 h.2 else φdefault
    have hφcTot : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1),
        φcTot c = φc c hc2 hc1 := by
      intro c hc2 hc1
      show (if h : c ^ 2 = 1 ∧ c ≠ 1 then φc c h.1 h.2 else φdefault) = φc c hc2 hc1
      rw [dif_pos ⟨hc2, hc1⟩]
    have hφcTot_seam : ∀ (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (x : Ω),
        φcTot c (c x) = starRingEnd ℂ (φcTot c x) := by
      intro c hc2 hc1 x
      rw [hφcTot c hc2 hc1]
      exact hφc c hc2 hc1 x
    -- ### the guarded local dictionary `βlG`
    let βlG := fun (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (a : (Ω ≃ₐ[k] Ω) → M) =>
      if _hguard : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a
        then finZB p K ζ hζ hζK T hT M A hA a else 0
    have hβlG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (a : (Ω ≃ₐ[k] Ω) → M),
        βlG M A hA a = (if _hguard : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a
          then finZB p K ζ hζ hζK T hT M A hA a else 0) := fun M _ _ _ _ _ A hA a => rfl
    have hβlG_add : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (b b' : (Ω ≃ₐ[k] Ω) → M),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
        βlG M A hA (b + b') = βlG M A hA b + βlG M A hA b' := by
      intro M _ _ _ _ _ A hA b b' hb hlb hb' hlb'
      rw [hβlG M A hA (b + b'), hβlG M A hA b, hβlG M A hA b',
        dif_pos (show SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (b + b') ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (b + b') from
          ⟨SSGRoute.IsCocycleOn.add hb hb', SSGRoute.IsLocConstOn.add hlb hlb'⟩),
        dif_pos (show SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b from ⟨hb, hlb⟩),
        dif_pos (show SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' from ⟨hb', hlb'⟩)]
      exact finZB_add p k Ω K ζ hζ hζK T hT M A hA b b' hb hlb hb' hlb'
    have hβlG_ker : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (b : (Ω ≃ₐ[k] Ω) → M),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (βlG M A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) := by
      intro M _ _ _ _ _ A hA b hb hlb
      rw [hβlG M A hA b, dif_pos (show SSGRoute.IsCocycleOn (SSGRoute.res k K)
          (SSGRoute.decomp k A) b ∧ SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b from ⟨hb, hlb⟩)]
      exact finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A hA b hb hlb
    have hβlG_onto : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (y : CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1),
        ∃ b : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βlG M A hA b = y := by
      intro M _ _ _ _ _ A hA y
      obtain ⟨b, hb, hlb, hby⟩ := finZB_surjective p k Ω K ζ hζ hζK T hT M A hA y
      exact ⟨b, hb, hlb, by
        rw [hβlG M A hA b, dif_pos (show SSGRoute.IsCocycleOn (SSGRoute.res k K)
          (SSGRoute.decomp k A) b ∧ SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b from ⟨hb, hlb⟩),
          hby]⟩
    have hβlG_unr : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
        ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
        ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βlG M A hA b) := by
      intro M _ _ _ _ _ A hA hpA hramA b hb hlb hiner
      rw [hβlG M A hA b, dif_pos (show SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A) b ∧ SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b from ⟨hb, hlb⟩)]
      exact finZB_unramified p k Ω K ζ hζ hζK T hT M A hA hpA hramA b hb hlb hiner
    -- ### the value formula for the guarded finite half
    have hpairG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
          (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
          (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair M (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βlG M A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))) := by
      intro M _ _ _ _ _ A hA a b hla hlb hb L hN hFD hGal hKL hAlg hS1 hS2 b₀ hb₀
      letI : FiniteDimensional k ↥L := hFD
      letI : IsGalois k ↥L := hGal
      letI : Algebra ↥K ↥L := hAlg
      letI : IsScalarTower k ↥K ↥L := hS1
      letI : IsScalarTower ↥K ↥L Ω := hS2
      rw [show pair M (SSGRoute.decomp k A) a b
            = pairGlueArch p k Ω K ζ hζ hζK T hT finG arch M (SSGRoute.decomp k A) a b from rfl,
        pairGlueArch_decomp p k Ω K ζ hζ hζK T hT finG arch (E7Arch.localGroupDisjoint k Ω)
          M A hA a b]
      by_cases hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a
      · rw [finG_eq M (SSGRoute.decomp k A) a b hca, hβlG M A hA a,
          dif_pos (show SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a from ⟨hca, hla⟩)]
        exact G1plusOwn.g1FinHalf_hpair p k Ω K ζ hζ hζK T hT χ hχcompat M A hA a b hla hlb hb
          L hKL b₀ hb₀
      · rw [show finG M (SSGRoute.decomp k A) a b = 0 from dif_neg hca,
          hβlG M A hA a, dif_neg (fun hc => hca hc.1),
          Work.SSGRoute.levelPair_zero, Work.SSGRoute.PT.iota_zero]
        have h0 : χ L hKL (0 : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) = 0 := by
          have h := hχadd L hKL 0 0 (by simp) (by simp)
          rw [add_zero] at h
          have h2 : χ L hKL 0 + χ L hKL 0 = χ L hKL 0 + 0 := by rw [h.symm, add_zero]
          exact add_left_cancel h2
        exact h0.symm
    -- ### orthogonality at a good place, without cocycle hypotheses
    have hfinG_zero_not_coc : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        ¬ SSGRoute.IsCocycleOn (SSGRoute.res k K) H a → finG M H a b = 0 :=
      fun M _ _ _ _ _ H a b h => dif_neg h
    have hfinG_zero_not_loc : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        ¬ (SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
        finG M (SSGRoute.decomp k A) a b = 0 := by
      intro M _ _ _ _ _ A hA a b h
      by_cases hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a
      · rw [finG_eq M (SSGRoute.decomp k A) a b hca]
        exact G1pOwn.g1FinHalf_eq_zero_of_not_locConst p k Ω K ζ hζ hζK T hT χ M
          (SSGRoute.decomp k A) a b ⟨A, hA, rfl⟩ h
      · exact hfinG_zero_not_coc M (SSGRoute.decomp k A) a b hca
    have hfinG_zero_not_coc_b : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
        ¬ SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        finG M (SSGRoute.decomp k A) a b = 0 := by
      intro M _ _ _ _ _ A hA a b hla h
      by_cases hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a
      · rw [finG_eq M (SSGRoute.decomp k A) a b hca]
        show Work.SSGRoute.PT.G1pOwn.g1FinHalf p k Ω K ζ hζ hζK T hT χ M
          (SSGRoute.decomp k A) a b = 0
        simp only [Work.SSGRoute.PT.G1pOwn.g1FinHalf]
        split
        · rename_i hP
          split
          · simp only [Work.SSGRoute.PT.finAtValue]
            split
            · split
              · rename_i hbc
                exact absurd (hP.choose_spec.2.symm ▸ hbc) h
              · rfl
            · rfl
          · rfl
        · rfl
      · exact hfinG_zero_not_coc M (SSGRoute.decomp k A) a b hca
    have hpairUnrG : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
        ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
        ∀ (a : (Ω ≃ₐ[k] Ω) → M)
          (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) →
          (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
          pair M (SSGRoute.decomp k A) a b = 0 := by
      intro M _ _ _ _ _ A hA hpA hramA a b hina hinb
      rw [show pair M (SSGRoute.decomp k A) a b
            = pairGlueArch p k Ω K ζ hζ hζK T hT finG arch M (SSGRoute.decomp k A) a b from rfl,
        pairGlueArch_decomp p k Ω K ζ hζ hζK T hT finG arch (E7Arch.localGroupDisjoint k Ω)
          M A hA a b]
      by_cases hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a
      · by_cases hloc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b
        · by_cases hcb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b
          · rw [finG_eq M (SSGRoute.decomp k A) a b hca]
            exact horth M A hA hpA hramA a b ⟨hca, hloc.1⟩ ⟨hcb, hloc.2⟩
              (fun σ hσ => ⟨hina σ hσ, hinb σ hσ⟩)
          · exact hfinG_zero_not_coc_b M A hA a b hloc.1 hcb
        · exact hfinG_zero_not_loc M A hA a b hloc
      · exact hfinG_zero_not_coc M (SSGRoute.decomp k A) a b hca
    -- ### `hreal`: the local realiser, from the surjectivity half of local duality
    have hreal : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
        ∀ lam : ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p,
          (∀ b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
            lam (b + b') = lam b + lam b') →
          (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b → lam b = 0) →
          ∃ a : (Ω ≃ₐ[k] Ω) → M,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a ∧
            ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
              SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
              pair M (SSGRoute.decomp k A) a b = lam b := by
      intro M _ _ _ _ _ A hA lam h1 h2
      haveI : Finite (TensorProduct (ZMod p) M T) := by
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
      obtain ⟨pc1, pc2, pc3, pc4, pc5⟩ := hpc M (SSGRoute.decomp k A) (Or.inl ⟨A, hA, rfl⟩)
      exact localPairing_surjective_dual p k Ω K T M A hA (pair M)
        (fun a a' b hca hla hca' hla' hb hlb =>
          pc1 a a' b ⟨hca, hla⟩ ⟨hca', hla'⟩ ⟨hb, hlb⟩)
        (fun a b b' hca hla hb hlb hb' hlb' =>
          pc2 a b b' ⟨hca, hla⟩ ⟨hb, hlb⟩ ⟨hb', hlb'⟩)
        (fun a b hca hla hb hlb hcob => pc3 a b ⟨hca, hla⟩ ⟨hb, hlb⟩ hcob)
        (fun a hca hla h => pc4 a ⟨hca, hla⟩ (fun b hb => h b hb.1 hb.2))
        (fun b hcb hlb h => pc5 b ⟨hcb, hlb⟩ (fun a ha => h a ha.1 ha.2))
        (exists_finite_spanning_locCocycles p k Ω K M A hA)
        (exists_finite_spanning_locCocycles p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A hA)
        lam h1 h2
    -- ### the two `hadd` inputs of v3
    have hadd : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
        ∀ (a : (Ω ≃ₐ[k] Ω) → M)
          (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
          pair M (SSGRoute.decomp k A) a (b + b') =
            pair M (SSGRoute.decomp k A) a b + pair M (SSGRoute.decomp k A) a b' := by
      intro M _ _ _ _ _ A hA a b b' hca hla hb hlb hb' hlb'
      exact (hpc M (SSGRoute.decomp k A) (Or.inl ⟨A, hA, rfl⟩)).2.1 a b b'
        ⟨hca, hla⟩ ⟨hb, hlb⟩ ⟨hb', hlb'⟩
    have haddArch : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (c : Ω ≃ₐ[k] Ω), c ^ 2 = 1 →
        ∀ (a : (Ω ≃ₐ[k] Ω) → M)
          (b b' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
          pair M (Subgroup.zpowers c) a (b + b') =
            pair M (Subgroup.zpowers c) a b + pair M (Subgroup.zpowers c) a b' := by
      intro M _ _ _ _ _ c hc a b b' hb hb'
      rw [show pair M (Subgroup.zpowers c) a (b + b')
            = arch M (Subgroup.zpowers c) a (b + b') from
            pairGlueArch_arch p k Ω K ζ hζ hζK T hT finG arch M hc rfl a (b + b'),
          show pair M (Subgroup.zpowers c) a b = arch M (Subgroup.zpowers c) a b from
            pairGlueArch_arch p k Ω K ζ hζ hζK T hT finG arch M hc rfl a b,
          show pair M (Subgroup.zpowers c) a b' = arch M (Subgroup.zpowers c) a b' from
            pairGlueArch_arch p k Ω K ζ hζ hζK T hT finG arch M hc rfl a b',
          show arch M (Subgroup.zpowers c) a (b + b')
            = archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a (b + b') from rfl,
          show arch M (Subgroup.zpowers c) a b
            = archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b from rfl,
          show arch M (Subgroup.zpowers c) a b'
            = archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b' from rfl]
      by_cases hc1 : c = 1
      · subst hc1
        rw [Subgroup.zpowers_one_eq_bot]
        show archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M ⊥ a (b + b')
            = archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M ⊥ a b
              + archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M ⊥ a b'
        simp only [archFamily_bot, add_zero]
      · rw [archFamily_zpowers p k Ω K ζ hζ hζK T hT χ φc hφc M c hc hc1 a (b + b'),
          archFamily_zpowers p k Ω K ζ hζ hζK T hT χ φc hφc M c hc hc1 a b,
          archFamily_zpowers p k Ω K ζ hζ hζK T hT χ φc hφc M c hc hc1 a b']
        exact archPairLocal_add_right p k Ω K ζ hζ hζK T hT χ hχadd M c hc hc1
          (φc c hc hc1) (hφc c hc hc1) a b b' hb hb'
    -- ### `hreal_unr`, from the count (C1a + R1)
    have hreal_unr : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
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
              pair M (SSGRoute.decomp k A) a b = lam b :=
      fun M _ _ _ _ _ =>
        Work.SSGRoute.LeadC8.hreal_unr_assembly p k Ω K ζ hζ hζK T hT
          (fun X _ _ _ _ _ A hA hpA hramA =>
            Work.SSGRoute.PT.LeadC8.finrank_H0loc_le_unrClasses p k Ω K X A hA hpA hramA)
          M (pair M)
          (fun A hA hpA hramA lam hcount h1 h2 h3 =>
          Work.SSGRoute.PT.LeadC8.hreal_unr_of_unrCount p k Ω K T M A hA hpA hramA (pair M)
            (fun a a' b hca hla hca' hla' hb hlb =>
              (hpc M (SSGRoute.decomp k A) (Or.inl ⟨A, hA, rfl⟩)).1 a a' b
                ⟨hca, hla⟩ ⟨hca', hla'⟩ ⟨hb, hlb⟩)
            (fun a b b' hca hla hb hlb hb' hlb' =>
              (hpc M (SSGRoute.decomp k A) (Or.inl ⟨A, hA, rfl⟩)).2.1 a b b'
                ⟨hca, hla⟩ ⟨hb, hlb⟩ ⟨hb', hlb'⟩)
            (fun a b hca hla hb hlb hcob =>
              (hpc M (SSGRoute.decomp k A) (Or.inl ⟨A, hA, rfl⟩)).2.2.1 a b
                ⟨hca, hla⟩ ⟨hb, hlb⟩ hcob)
            (fun a hca hla h =>
              (hpc M (SSGRoute.decomp k A) (Or.inl ⟨A, hA, rfl⟩)).2.2.2.1 a ⟨hca, hla⟩
                (fun b hb => h b hb.1 hb.2))
            (fun b hcb hlb h =>
              (hpc M (SSGRoute.decomp k A) (Or.inl ⟨A, hA, rfl⟩)).2.2.2.2 b ⟨hcb, hlb⟩
                (fun a ha => h a ha.1 ha.2))
            (fun a b ha hb hiner => horthG M A hA hpA hramA a b ha hb hiner)
            hcount lam h1 h2 h3)
    -- ### the *global* clauses of the arch-based dictionary `finZBg` (its per-`E` bundle)
    have hβg_ker : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (b : (Ω ≃ₐ[k] Ω) → M),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        (finZBg p K ζ hζ hζK T hT M b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b) :=
      fun M _ _ _ _ _ b hb hl =>
        (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
          (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT)))
          M).2.2.1 b hb hl
    have hβg_onto : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (y : CategoryTheory.Abelian.Ext
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
          (SSGRoute.PTExt.unitsK k ↥K) 1),
        ∃ b : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧ SSGRoute.IsLocConstOn ⊤ b ∧
            finZBg p K ζ hζ hζK T hT M b = y :=
      fun M _ _ _ _ _ y =>
        (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
          (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT)))
          M).2.2.2.1 y
    -- ### `hfinS`: `finiteS_converse_canonical_v8`, with `1` dropped from `C`
    have hfinS : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (S₁ : Finset (ValuationSubring Ω)), (∀ A ∈ S₁, SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S₁, ∀ B ∈ S₁, SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (SSGRoute.IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) →
          ∃ A ∈ S₁, SSGRoute.IsConjPlace k A B) →
        ∀ (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
        (hC : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
          ∃ c₀ ∈ C, ∃ σ : (Ω ≃ₐ[k] Ω), c = σ * c₀ * σ⁻¹)
        (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : (Ω ≃ₐ[k] Ω), c' = σ * c * σ⁻¹) → c = c')
        (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
        (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M),
        (∀ A ∈ S₁, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A)) →
        (∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c)) →
        (∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
            ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
          ∑ A ∈ S₁, pair M (SSGRoute.decomp k A) (α A) b +
            ∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b = 0) →
        ∃ ε : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
          (∀ A ∈ S₁, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun σ => ε σ - α A σ)) ∧
          (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
            (fun σ => ε σ - β c σ)) ∧
          ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
            ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → ε σ = 0 := by
      intro M _ _ _ _ _ S₁ hS₁fin hS₁disj hS₁ram C hCinv hC hCdisj α β hα hβ horth
      let C' : Finset (Ω ≃ₐ[k] Ω) := C.filter (fun c => c ≠ 1)
      have hC'1 : ∀ c ∈ C', c ≠ 1 := fun c hc => (Finset.mem_filter.mp hc).2
      have hC'inv : ∀ c ∈ C', c ^ 2 = 1 := fun c hc => hCinv c (Finset.mem_filter.mp hc).1
      have hC'rep : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
          ∃ c₀ ∈ C', ∃ σ : (Ω ≃ₐ[k] Ω), c = σ * c₀ * σ⁻¹ := by
        intro c hc2 hc1
        obtain ⟨c₀, hc₀, σ, hσ⟩ := hC c hc2 hc1
        refine ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, ?_⟩, σ, hσ⟩
        intro h; subst h
        rw [mul_one, mul_inv_cancel] at hσ
        exact hc1 hσ
      have hC'disj : ∀ c ∈ C', ∀ c' ∈ C', (∃ σ : (Ω ≃ₐ[k] Ω), c' = σ * c * σ⁻¹) → c = c' :=
        fun c hc c' hc' h => hCdisj c (Finset.mem_filter.mp hc).1 c' (Finset.mem_filter.mp hc').1 h
      have hsumC : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          (∑ c ∈ C', pair M (Subgroup.zpowers c) (β c) b) =
            ∑ c ∈ C, pair M (Subgroup.zpowers c) (β c) b := by
        intro b
        rw [← Finset.sum_filter_add_sum_filter_not C (fun c => c ≠ 1)
          (fun c => pair M (Subgroup.zpowers c) (β c) b)]
        have hz : ∑ c ∈ C.filter (fun c => ¬ (c ≠ 1)),
            pair M (Subgroup.zpowers c) (β c) b = 0 := by
          apply Finset.sum_eq_zero
          intro c hc
          rw [Finset.mem_filter] at hc
          rw [not_not] at hc
          obtain rfl : c = 1 := hc.2
          rw [show pair M (Subgroup.zpowers 1) (β 1) b
                = pairGlueArch p k Ω K ζ hζ hζK T hT finG arch M
                    (Subgroup.zpowers 1) (β 1) b from rfl,
            pairGlueArch_arch p k Ω K ζ hζ hζK T hT finG arch M
              (by simp : (1 : Ω ≃ₐ[k] Ω) ^ 2 = 1) rfl (β 1) b,
            Subgroup.zpowers_one_eq_bot]
          exact archFamily_bot p k Ω K ζ hζ hζK T hT χ φc hφc M (β 1) b
        rw [show C.filter (fun c => c ≠ 1) = C' from rfl, hz, add_zero]
      have horth' : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
            (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
            ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
          ∑ A ∈ S₁, pair M (SSGRoute.decomp k A) (α A) b +
            ∑ c ∈ C', pair M (Subgroup.zpowers c) (β c) b = 0 := by
        intro b hbc hbl hin
        rw [hsumC b]
        exact horth b hbc hbl hin
      obtain ⟨ε, hεcoc, hεlc, hεS, hεC', hεunr⟩ :=
        finiteS_converse_canonical_v8 (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
          (hζK := hζK) (T := T) (hT := hT) (χ := χ) (hχadd := hχadd) (hχinj := hχinj)
          (hχcompat := hχcompat) (M := M)
          (βl := βlG M) (hβl_add := hβlG_add M) (hβl_ker := hβlG_ker M)
          (hβl_onto := hβlG_onto M) (hβl_unr := hβlG_unr M)
          (pair := pair M) (hpair := hpairG M) (hpair_unr := hpairUnrG M)
          (hreal_unr := hreal_unr M)
          (βg := finZBg p K ζ hζ hζK T hT M)
          (hβg_add := finZBg_add p k Ω K ζ hζ hζK T hT M)
          (hβg_ker := hβg_ker M)
          (hβg_onto := hβg_onto M)
          (hsq := fun b hb hl A hA => by
            rw [hβlG M A hA b, dif_pos (show SSGRoute.IsCocycleOn (SSGRoute.res k K)
                (SSGRoute.decomp k A) b ∧ SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b from
              ⟨SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hb,
                SSGRoute.isLocConstOn_mono le_top hl⟩)]
            exact finZB_square p k Ω K ζ hζ hζK T hT M A hA b hb hl)
          (wc := fun c => archW k Ω K (φcTot c))
          (βc := fun c b => archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K (φcTot c)) b)
          (hwc := fun c hc2 hc1 => ⟨fun q => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ q,
            (decompK_linked k Ω K c hc2 hc1 (φcTot c) (hφcTot_seam c hc2 hc1)).symm⟩)
          (φc := φcTot)
          (hseam := fun c hc2 hc1 => ⟨hφcTot_seam c hc2 hc1, rfl⟩)
          (hβc_add := fun c hc2 hc1 b b' hb hb' =>
            archβc_add p k Ω K ζ hζ hζK T hT M c hc2 hc1 (φcTot c)
              (hφcTot_seam c hc2 hc1) b b' hb hb')
          (hβc_ker := fun c hc2 hc1 b hb =>
            archβc_eq_zero_iff p k Ω K ζ hζ hζK T hT M c hc2 hc1 (φcTot c)
              (hφcTot_seam c hc2 hc1) b hb)
          (hβc_onto := fun c hc2 hc1 y =>
            archβc_surjective p k Ω K ζ hζ hζK T hT M c hc2 hc1 (φcTot c)
              (hφcTot_seam c hc2 hc1) y)
          (hβc_sq := fun c hc2 hc1 b hb hl =>
            archβc_square p k Ω K ζ hζ hζK T hT M c hc2 hc1 (φcTot c)
              (hφcTot_seam c hc2 hc1) b hb hl)
          (hpairArch := fun c hc2 hc1 a b ha L hN hFD hGal hKL hAlg hS1 hS2 u hu hus ψ hψ hres => by
            letI : FiniteDimensional k ↥L := hFD
            letI : IsGalois k ↥L := hGal
            letI : Algebra ↥K ↥L := hAlg
            letI : IsScalarTower k ↥K ↥L := hS1
            letI : IsScalarTower ↥K ↥L Ω := hS2
            have hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
              intro g hg h hh
              have hcompat : SSGRoute.PTExt.galRes k (↥K) (↥L) (SSGRoute.res k L g)
                  = SSGRoute.res k K g :=
                (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply ↥K ↥L (F := k)
                  (K₃ := Ω) g).symm
              rw [hres (g * h) (Subgroup.mul_mem _ hg hh), hres g hg, hres h hh, map_mul,
                hψ (SSGRoute.res k L g) (SSGRoute.res k L h), hcompat]
              exact add_comm _ _
            rw [show pair M (Subgroup.zpowers c) a b
                = arch M (Subgroup.zpowers c) a b from
                pairGlueArch_arch p k Ω K ζ hζ hζK T hT finG arch M hc2 rfl a b,
              show arch M (Subgroup.zpowers c) a b
                = archFamily p k Ω K ζ hζ hζK T hT χ φc hφc M (Subgroup.zpowers c) a b from rfl,
              archFamily_zpowers p k Ω K ζ hζ hζK T hT χ φc hφc M c hc2 hc1 a b]
            exact (archPairLocal_congr_arg p k Ω K ζ hζ hζK T hT χ M (g := c) (c := c) rfl
                (φg := φc c hc2 hc1) (φ := φcTot c) (hφg := (hφcTot c hc2 hc1).symm)
                hc2 hc2 hc1 hc1 (hφc c hc2 hc1) (hφcTot_seam c hc2 hc1) a b).trans
              (archPairLocal_hpairArch p k Ω K ζ hζ hζK T hT χ hχadd hχcompat M c hc2 hc1 a b ha hb
                (φcTot c) (hφcTot_seam c hc2 hc1) L hKL u hu hus ψ hψ hres))
          (S₁ := S₁) (hS₁fin := hS₁fin) (hS₁disj := hS₁disj) (hS₁ram := hS₁ram)
          (α := α) (hα := hα) (C := C') (hCinv := hC'inv) (hC := hC'rep) (hCdisj := hC'disj)
          (hC1 := hC'1) (β := β)
          (hβ := fun c hc => hβ c (Finset.mem_filter.mp hc).1) (horth := horth')
      refine ⟨ε, hεcoc, hεlc, hεS, ?_, hεunr⟩
      intro c hc
      by_cases hc1 : c = 1
      · subst hc1
        rw [Subgroup.zpowers_one_eq_bot]
        refine isCoboundaryOn_bot_of_isCocycleOn (SSGRoute.res k K) _ ?_
        refine SSGRoute.IsCocycleOn.sub
          (SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hεcoc) ?_
        simpa [Subgroup.zpowers_one_eq_bot] using (hβ 1 hc)
      · exact hεC' c (Finset.mem_filter.mpr ⟨hc, hc1⟩)
    -- ### the conclusion: v3 with the four inputs built above
    exact relaxed_converse_of_finiteS_v3 (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (hζK := hζK) (T := T) (hT := hT) (pair := pair) (hadd := hadd)
      (haddArch := haddArch) (hreal := hreal) (hfinS := hfinS) (M := M) (N := N) (hKN := hKN)
      (S := S) (hSfin := hSfin) (hSdisj := hSdisj) (hSram := hSram) (C := C) (hCinv := hCinv)
      (hC := hC) (hCdisj := hCdisj) (α := α) (hα := hα) (β := β) (hβ := hβ) (horth := horth8)

end Work.SSGRoute.PT
