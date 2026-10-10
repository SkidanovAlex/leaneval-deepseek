import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.LeadC8
import Submission.Work.SSGRoute.PT.glue_realiser_arch_v4
import Submission.Work.SSGRoute.PT.valueFormula_arch_own_v2
import Submission.Work.SSGRoute.phi1_mono_sylow_in
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option maxHeartbeats 1000000

/-! Guidance from the project lead (the requester):

Lead design (Claude) 10-05 23:05 (_lead_design/flags_2305/flags_2305.md): the target is v7, the
`hus` (seam-place) restatement of v6.  The assembly below is `glue_realiser_arch_v3` +
`valueFormula_arch_own` + E6Ω (`phi1_mono_sylow_in`) + the exact segment (`pt_extSegment_exact`);
the `C`-clause uses `hβc_sq` + `hβc_ker`.
-/

namespace Work.SSGRoute.PT

/-- **The place of `↥K` under a conjugate place of `Ω` is the conjugate place.**
(Copied from `PT/finiteS_converse_canonical_v4.lean`, where it is proved; the standalone module
`PT/exists_finQ_smul_of_isConjPlace` carries the same statement, still `sorry`.) -/
theorem exists_finQ_smul_of_isConjPlace_v8 {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (A B : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hB : SSGRoute.IsFinPlace k B)
    (h : SSGRoute.IsConjPlace k A B) :
    ∃ σ : ↥K ≃ₐ[k] ↥K,
      σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA) =
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K B hB) := by
  classical
  obtain ⟨τ, hτ⟩ := h
  refine ⟨AlgEquiv.restrictNormalHom K τ, ?_⟩
  have hcoe : ∀ y : NumberField.RingOfIntegers ↥K,
      (((NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormalHom K τ) y : ↥K)) : Ω)
        = τ • (((y : ↥K) : Ω)) := by
    intro y
    rw [NK.GlobalCFT.Place.ringOfIntegersEquiv_apply, AlgEquiv.restrictNormalHom_apply,
      AlgEquiv.smul_def]
  have hq : NK.GlobalCFT.Place.smulHeightOneSpectrum (AlgEquiv.restrictNormalHom K τ)
      (Work.SSGRoute.PT.finQ K A hA) = Work.SSGRoute.PT.finQ K B hB := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    apply Ideal.ext
    intro x
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal,
      Ideal.mem_map_iff_of_surjective
        (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormalHom K τ))
        (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormalHom K τ)).surjective,
      Work.SSGRoute.PT.finQ_spec K B hB x]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyv : A.valuation (((y : ↥K) : Ω)) < 1 := (Work.SSGRoute.PT.finQ_spec K A hA y).mp hy
      have hyA : (((y : ↥K) : Ω)) ∈ A :=
        ValuationSubring.mem_of_valuation_le_one A _ (le_of_lt hyv)
      rw [← hyx, hcoe y, ← hτ]
      exact (Work.SSGRoute.smul_valuation_lt_one τ A (((y : ↥K) : Ω)) hyA).mpr hyv
    · intro hx
      set y : NumberField.RingOfIntegers ↥K :=
        (NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormalHom K τ)).symm x with hydef
      have hyx : NK.GlobalCFT.Place.ringOfIntegersEquiv (AlgEquiv.restrictNormalHom K τ) y = x := by
        rw [hydef]; simp
      refine ⟨y, ?_, hyx⟩
      rw [Work.SSGRoute.PT.finQ_spec K A hA]
      have hBval : B.valuation (τ • (((y : ↥K) : Ω))) < 1 := by rw [← hcoe y, hyx]; exact hx
      have h3 : (τ • A).valuation (τ • (((y : ↥K) : Ω))) < 1 := by rw [hτ]; exact hBval
      have hwA : (((y : ↥K) : Ω)) ∈ A := by
        have h1 : τ • (((y : ↥K) : Ω)) ∈ τ • A :=
          ValuationSubring.mem_of_valuation_le_one (τ • A) _ (le_of_lt h3)
        have h2 := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := τ) (S := A)
          (x := τ • (((y : ↥K) : Ω)))).mp h1
        simpa using h2
      exact (Work.SSGRoute.smul_valuation_lt_one τ A (((y : ↥K) : Ω)) hwA).mp h3
  rw [NK.GlobalCFT.Place.smul_ofFinite, hq]

/-- SEAM-PLACE RESTATEMENT (flags_2305).  Identical to `finiteS_converse_canonical_v6` except that `hpairArch` is required only
at the seam place `u = mk (φc c |_L)` of each level `L` (binder `hus`), instead of at every
`u | wc c` with `D_u = ⟨res_L c⟩`.  The hypothesis is weaker, so any proof that applies
`hpairArch` only at `u_c = mk (φc c |_L)` goes through with `hus := rfl` in place of
`decompK_linked`.  The G1⁺ hub can supply it without a `τ`-invariance argument (flags_2305.md).

The finite-`S` converse for every prime `p`, version 6 (flags_1730).  This is v5 with three
corrections, all forced by counterexamples to v5 (see flags_1730.md).

* `hC1 : 1 ∉ C`.  In v5, `1 ∈ C` was allowed, and `pair ⊥` is pinned by nothing, so `horth` could be
  met with any `α`.
* The seam `φc`/`hseam`: `wc c` is the place `mk (φc c |_K)` of an embedding with
  `φc c ∘ c = conj ∘ φc c`.  In v5 `wc c` was tied to `c` only through `D_{wc c} = ⟨res c⟩`, so two
  non-conjugate involutions could share one place and the glue could not give both components.  With
  the seam the `wc c` (`c ∈ C`) are in distinct orbits (`wc_orbit_injective` + `hCdisj`), and every
  level `L` has a place over `wc c` with `D = ⟨res_L c⟩` (`liesOver_linked`, `decompK_linked`).
* `hpairArch` holds at EVERY level `L ≥ K`, exactly like `hpair`: for `u | wc c` with
  `D_u = ⟨res_L c⟩` and a level-`L` cocycle `ψ` representing `b` on `⟨c⟩`,
  `pair ⟨c⟩ a b = χ_L (iota u (levelPair (D_u → D_w) (K_wˣ → L_uˣ) (βc c a) (h_ψ|_{D_u})))`.  The
  level-`K` form of v5 is wrong at real `wc c` (`res c = 1`, `D_w = ⊥`).  There it forces `pair = 0`,
  but the real-place pairing `H¹(ℝ, M) × H¹(ℝ, M') → ℤ/2` is perfect.  Counterexample to v5:
  `k = K = ℚ`, `p = 2`, `M = ℤ/2`, `S₁ = {2}`, `α = [2]`, `β c` nontrivial; `horth` holds, but no
  `ε ∈ ⟨−1, 2⟩` is `≡ 2` in `ℚ₂ˣ/ℚ₂ˣ²` and negative.  In the all-level form a level where
  `res_L c = 1` admits only `b` with `b c = 0`, so nothing false is forced.

Route.  As in v5, with the value formula at level `L` (`valueFormula_arch_v2`): the term at the place
`u_c = mk (φc c |_L)` is `yonedaPair (extLoc u_c Z) (h|_{D_{u_c}})`, which is DEFINITIONALLY
`levelPair (decompKRestrict) (localUnitsMap) (extLoc (wc c) X) (h|_{D_{u_c}})` once
`E7cOmega.extLoc_push_ideleMap` (place-generic) rewrites `extLoc u_c Z`.  The glue
(`glue_realiser_arch_v2`) gives `extLoc (wc c) X = βc c (β c)`, and `hpairArch` at level `L` then
gives `pair ⟨c⟩ (β c) b`. -/
theorem finiteS_converse_canonical_v8 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
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
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hβl_onto : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) y,
      ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl A hA b = y)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (hpair_unr : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0) →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        pair (SSGRoute.decomp k A) a b = 0)
    (hreal_unr : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
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
            pair (SSGRoute.decomp k A) a b = lam b)
    (βg : ((Ω ≃ₐ[k] Ω) → M) →
      CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
        (SSGRoute.PTExt.unitsK k ↥K) 1)
    (hβg_add : ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
      βg (b + b') = βg b + βg b')
    (hβg_ker : ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (βg b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b))
    (hβg_onto : ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
      SSGRoute.IsLocConstOn ⊤ b ∧ βg b = y)
    (hsq : ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
        SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
            (SSGRoute.PTExt.extToIdeles (k := k) (βg b)) = βl A hA b)
    (wc : (Ω ≃ₐ[k] Ω) → NK.GlobalCFT.Place ↥K)
    (βc : ∀ c : (Ω ≃ₐ[k] Ω), ((Ω ≃ₐ[k] Ω) → M) →
      CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (wc c)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (wc c)) 1)
    (hwc : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
        wc c ≠ NK.GlobalCFT.Place.ofFinite q) ∧
      (Subgroup.zpowers c).map (SSGRoute.res k K) = SSGRoute.PTExt.decompK (k := k) (wc c))
    (φc : (Ω ≃ₐ[k] Ω) → (Ω →+* ℂ))
    (hseam : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      (∀ x : Ω, φc c (c x) = starRingEnd ℂ (φc c x)) ∧
      wc c = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥K) Ω))))
    (hβc_add : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
      βc c (b + b') = βc c b + βc c b')
    (hβc_ker : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      (βc c b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (hβc_onto : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc c b = y)
    (hβc_sq : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.PTExt.extLoc (k := k) (wc c)
        (SSGRoute.PTExt.extToIdeles (k := k) (βg b)) = βc c b)
    (hpairArch : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
        ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
          (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (wc c))
          (hus : u = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥L) Ω))))
          (ψ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
          (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L, ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g),
          (∀ σ ∈ Subgroup.zpowers c, b σ = ψ (SSGRoute.res k L σ)) →
          pair (Subgroup.zpowers c) a b =
            χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L) u
              (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (wc c) u hu)
                (Work.SSGRoute.localUnitsMap k ↥K ↥L (wc c) u hu) (βc c a)
                (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
                  (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)))))
    (S₁ : Finset (ValuationSubring Ω)) (hS₁fin : ∀ A ∈ S₁, SSGRoute.IsFinPlace k A)
    (hS₁disj : ∀ A ∈ S₁, ∀ B ∈ S₁, SSGRoute.IsConjPlace k A B → A = B)
    (hS₁ram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S₁, SSGRoute.IsConjPlace k A B)
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → M)
    (hα : ∀ A ∈ S₁, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (α A))
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : (Ω ≃ₐ[k] Ω), c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : (Ω ≃ₐ[k] Ω), c' = σ * c * σ⁻¹) → c = c')
    (hC1 : ∀ c ∈ C, c ≠ 1)
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (β c))
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ S₁, pair (SSGRoute.decomp k A) (α A) b +
        ∑ c ∈ C, pair (Subgroup.zpowers c) (β c) b = 0) :
    ∃ ε : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧ SSGRoute.IsLocConstOn ⊤ ε ∧
      (∀ A ∈ S₁, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => ε σ - α A σ)) ∧
      (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => ε σ - β c σ)) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → ε σ = 0 := by
  classical
  -- ## The coefficient module `M' = DualMod p (M ⊗ T)` is finite and `p`-torsion.
  haveI hTfin : Finite T := by
    haveI : Module.Free (ZMod p) T := inferInstance
    have hfr : Module.finrank (ZMod p) T = 1 := hT.1
    haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by omega)
    have h2 : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
      rw [hfr, Module.finrank_self]
    exact Finite.of_injective
      (LinearEquiv.ofFinrankEq T (ZMod p) h2 : T ≃ₗ[ZMod p] ZMod p) (LinearEquiv.injective _)
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
  haveI hDfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    Finite.of_injective (fun f => (f : TensorProduct (ZMod p) M T → ZMod p))
      (fun f g hfg => LinearMap.ext (fun x => congrFun hfg x))
  haveI hModD : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    inferInstance
  haveI hDfinRep : Finite (↑(SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))) := hDfin
  haveI hModDRep : Module (ZMod p) (↑(SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))) := hModD
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- ## Step 1: the gluing and the realisers of the local data at `S₁` (piece G⁺).
  obtain ⟨R, hRfin, hS₁R, hRdisj, hRcov, αe, hαeS₁, hαecl, hαeunr, hsum, X, hXfin, hXarch, hXzero⟩ :=
    glue_realiser_arch_v4 p k Ω K ζ hζ hζK T hT χ hχadd hχinj hχcompat M βl hβl_add hβl_ker
      hβl_onto hβl_unr pair hpair hpair_unr hreal_unr βg hβg_add hβg_ker hβg_onto hsq wc βc hwc
      φc hseam hβc_add hβc_ker hβc_onto hβc_sq hpairArch S₁ hS₁fin hS₁disj hS₁ram α hα C hCinv hC
      hCdisj hC1 β hβ horth
  -- ## Step 2: the value formula (piece V⁺) turns the vanishing of the glued sum into `φ¹` vanishing.
  have hαunr : {v : ValuationSubring Ω | v ∈ R ∧
      ¬ ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k v σ → αe v σ = 0}.Finite := by
    refine Set.Finite.subset (S₁.finite_toSet) ?_
    rintro v ⟨hvR, hv⟩
    by_contra hvS
    exact hv (hαeunr v hvR (by simpa using hvS))
  have hphi : SSGRoute.PTExt.PhiOneVanishesIn Ω (SSGRoute.PTExt.extToClasses (k := k) X) := by
    intro L _ _ _ h
    obtain ⟨b, hbc, hbl, hkey⟩ :=
      valueFormula_arch_own_v2 p k Ω K ζ hζ hζK T hT χ hχadd hχinj hχcompat M βl hβl_add hβl_ker
        hβl_onto hβl_unr pair hpair hpair_unr hreal_unr βg hβg_add hβg_ker hβg_onto hsq wc βc
        hwc φc hseam hβc_add hβc_ker hβc_onto hβc_sq hpairArch S₁ hS₁fin hS₁disj hS₁ram α hα C hCinv hC
        hCdisj hC1 β hβ horth R hRfin hRdisj hRcov αe hαecl hαunr X ⟨hXfin, hXarch, hXzero⟩ L h
    exact hkey (hsum b hbc hbl)
  -- ## Step 3: `φ¹` injectivity (E6Ω) kills the class of `X`.
  have hX0 : SSGRoute.PTExt.extToClasses (k := k) X = 0 :=
    Work.SSGRoute.phi1_mono_sylow_in p k ↥K Ω (⟨ζ, hζK⟩ : ↥K)
      (IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
        (algebraMap ↥K Ω).injective)
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
      (fun m => by rw [← Nat.cast_smul_eq_nsmul (ZMod p) p m, ZMod.natCast_self, zero_smul])
      (SSGRoute.PTExt.extToClasses (k := k) X) hphi
  -- ## Step 4: the global lift of the class to a global cocycle `ε`.
  obtain ⟨ε, hεcoc, hεlc, hεeq⟩ :=
    ((pt_extSegment_exact p k Ω K ζ hζ hζK T hT M βg hβg_add hβg_ker hβg_onto).1 X).mp hX0
  refine ⟨ε, hεcoc, hεlc, ?_, ?_, ?_⟩
  · -- the local data at `S₁` is cohomologous to `ε`
    intro A hA
    have hAfin : SSGRoute.IsFinPlace k A := hS₁fin A hA
    have hαA := hα A hA
    have hβleq : βl A hAfin ε = βl A hAfin (α A) := by
      have h1 : SSGRoute.PTExt.extLoc (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hAfin)) X =
          βl A hAfin ε := by
        rw [← hεeq]
        exact hsq ε hεcoc hεlc A hAfin
      have h2 : SSGRoute.PTExt.extLoc (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hAfin)) X =
          βl A hAfin (α A) := by
        rw [← hαeS₁ A hA]
        exact hXfin A (hS₁R A hA)
      exact h1.symm.trans h2
    have hcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => ε σ - α A σ) :=
      Work.SSGRoute.IsCocycleOn.sub
        (Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hεcoc) hαA.1
    have hlc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (fun σ => ε σ - α A σ) :=
      Work.SSGRoute.IsLocConstOn.sub (Work.SSGRoute.isLocConstOn_mono le_top hεlc) hαA.2
    have hzero : βl A hAfin (fun σ => ε σ - α A σ) = 0 := by
      have hadd := hβl_add A hAfin (fun σ => ε σ - α A σ) (α A) hcoc hlc hαA.1 hαA.2
      have hone : (fun σ => ε σ - α A σ) + α A = ε := by
        funext σ
        simp
      rw [hone, hβleq] at hadd
      have hcancel : βl A hAfin (fun σ => ε σ - α A σ) + βl A hAfin (α A) =
          0 + βl A hAfin (α A) := by
        rw [zero_add]
        exact hadd.symm
      exact add_right_cancel hcancel
    exact (hβl_ker A hAfin (fun σ => ε σ - α A σ) hcoc hlc).mp hzero
  · -- the `C`-clause: `hβc_sq` + `hβc_ker` (all `p`, including `p = 2` and real places)
    intro c hc
    have hc2 : c ^ 2 = 1 := hCinv c hc
    have hcne : c ≠ 1 := hC1 c hc
    have hx : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => ε σ - β c σ) :=
      Work.SSGRoute.IsCocycleOn.sub
        (Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hεcoc) (hβ c hc)
    -- the archimedean square: `βc c ε = extLoc (wc c) X = βc c (β c)`
    have hβceq : βc c ε = βc c (β c) := by
      have h1 : SSGRoute.PTExt.extLoc (k := k) (wc c)
          (SSGRoute.PTExt.extToIdeles (k := k) (βg ε)) = βc c ε :=
        hβc_sq c hc2 hcne ε hεcoc hεlc
      rw [hεeq] at h1
      exact h1.symm.trans (hXarch c hc)
    have hxβ : (fun σ => ε σ - β c σ) + β c = ε := by
      funext σ
      simp
    have hadd := hβc_add c hc2 hcne (fun σ => ε σ - β c σ) (β c) hx (hβ c hc)
    rw [hxβ, hβceq] at hadd
    have hzero : βc c (fun σ => ε σ - β c σ) = 0 := by
      have h2 : βc c (fun σ => ε σ - β c σ) + βc c (β c) = 0 + βc c (β c) := by
        rw [zero_add]
        exact hadd.symm
      exact add_right_cancel h2
    exact (hβc_ker c hc2 hcne (fun σ => ε σ - β c σ) hx).mp hzero
  · -- the inertia clause: `ε` vanishes on the inertia at `B`.  (This is the v8 replacement for
    -- the `hβg_unr` step: the comparison of the dictionary values is made at the transversal
    -- representative `v` of the conjugacy class of `B`, by `LeadC8.inertia_of_dictionary_eq`,
    -- and the vanishing is then transported from `v` to `B` by `PT.inertiaVanishing_conj`.)
    intro B hB hBnotconj σ hσ
    obtain ⟨hBunr, hBval⟩ :=
      Work.SSGRoute.not_isRamifiedIn_and_not_val_p_lt_one_of_forall_not_conj K p S₁ hS₁ram B hB
        hBnotconj
    obtain ⟨v, hvR, τ, hτv⟩ := hRcov B hB
    have hvfin : SSGRoute.IsFinPlace k v := hRfin v hvR
    have hvnotconj : ∀ A ∈ S₁, ¬ SSGRoute.IsConjPlace k A v := by
      intro A hA hc
      exact hBnotconj A hA (Work.SSGRoute.isConjPlace_trans hc ⟨τ, hτv⟩)
    obtain ⟨hvunr, hvval⟩ :=
      Work.SSGRoute.not_isRamifiedIn_and_not_val_p_lt_one_of_forall_not_conj K p S₁ hS₁ram v
        hvfin hvnotconj
    have hvS : v ∉ S₁ := fun hvS => hBnotconj v hvS ⟨τ, hτv⟩
    have heq : βl v hvfin ε = βl v hvfin (αe v) := by
      have h1 : SSGRoute.PTExt.extLoc (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v hvfin)) X =
          βl v hvfin ε := by
        rw [← hεeq]
        exact hsq ε hεcoc hεlc v hvfin
      have h2 : SSGRoute.PTExt.extLoc (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v hvfin)) X =
          βl v hvfin (αe v) := hXfin v hvR
      exact h1.symm.trans h2
    have hIv : ∀ τ' : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v τ' → ε τ' = 0 :=
      LeadC8.inertia_of_dictionary_eq k Ω K v hvunr (βl v hvfin) (hβl_add v hvfin)
        (hβl_ker v hvfin) ε (αe v)
        (Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hεcoc)
        (Work.SSGRoute.isLocConstOn_mono le_top hεlc) (hαecl v hvR).1 (hαecl v hvR).2
        (hαeunr v hvR hvS) heq
    exact (Work.SSGRoute.PT.inertiaVanishing_conj p k Ω K M ε hεcoc hvunr hBunr hτv).mp hIv σ hσ

end Work.SSGRoute.PT
