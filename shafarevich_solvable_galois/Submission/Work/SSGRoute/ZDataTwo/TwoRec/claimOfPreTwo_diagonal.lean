import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.evenCountAtNonEscapePrime
import Submission.Work.SSGRoute.NodeS37.oPairAt_smul_conj
import Submission.Work.SSGRoute.NodeS37.pinnedZeroImpLocalGroup
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_dictionary
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_localNormalise
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_squareAtSBlock
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.killsInertia_of_unit_notTwo
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.preTwoExists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `TwoRec.claimOfPreTwo_diagonal` — the p. 16 diagonal case

This is the `m = l` case of Schmidt–Wingberg's Claim for the corrected `p = 2` §4 recursion: for a
history `s` with `PreTwo` at every prefix, the Kummer cochain of `b_m` kills the local group of the
`σ`-sibling of its *own* escape prime `Q_m`.  The value there is prescribed neither by the rule (4)
nor by the confinement clause of `PreTwo`, and must come from the arithmetic of `b_m` itself
(Schmidt–Wingberg, p. 16).

The file is organised as

* `preTwo_finPlace_diag` — the finiteness of the escape primes;
* `pinnedValue_diagonal` — **the arithmetic core**: the pinned value of `χ_{b_m}` at the sibling
  vanishes (the p.16 computation, via the product formula with the anti-invariant representative
  `X = z - ρz`);
* `claimOfPreTwo_diagonal` — the assembly (passage from the pinned value to the whole local group,
  `NodeS37.pinnedZeroImpLocalGroup`, plus the `gesKConj`-transport of the local group of `σ • Q_m`
  to the sibling).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-- Every escape prime of a history satisfying the prefix invariant at all stages is a finite
place.  (A local copy of `NodeS37.preTwo_finPlace`, which cannot be imported here: the node's file
imports this one.) -/
theorem preTwo_finPlace_diag {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω]
    {Λ : IntermediateField k Ω} [FiniteDimensional k Λ] [IsGalois k Λ]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) (n : ℕ) :
    SSGRoute.IsFinPlace k ((s.f n).1) :=
  (hs (n + 1)).1 n (Nat.lt_succ_self n)

/-- **The p. 16 arithmetic core.**  For a history satisfying the prefix invariant at every stage,
the pinned value of `χ_{b_m}` at the `ρ`-sibling of the escape prime `Q_m` (`ρ = res k K σ` an
involution `≠ 1`) vanishes.

Route (Schmidt–Wingberg, p. 16).  Pick the representative `z = b_m x²` with `v_{ρ𝔮}(z) = 0`
(`claimOfPreTwo_localNormalise`), put `X := z - ρz`, and let `T'` be the set of `K`-class
representatives of the sibling together with the primes dividing `2X`.  The multi-place product
formula for the pair `(ρz, X)` reads

  `oPairAt(sibling)(χ_{ρz}, χ_X) + Σ_{A ∈ Σ} oPairAt(A)(χ_{ρz}, χ_X) = 0`,

and

* the sibling term is the pinned value `V` (dictionary at the sibling: `X = z·u` with `u` a `1`-unit
  there, so `χ_X` and `χ_b` agree on the local group, and `χ_b` kills the inertia there);
* at a dyadic place the second cochain `χ_{ρz} = χ_{ρb}` kills the whole local group
  (`claimOfPreTwo_squareAtSBlock` + conjugation), so the term vanishes;
* at a prime in `Σ` the term is `count_A(X) • χ_{ρz}(ψ_A)`: in the split case the two places of the
  `K`-class pair cancel by Galois covariance, in the inert case (`ρA = A`) either `count_A(X)` is
  even or `ρz ∈ K_A^{×2}` (`ρz ≡ a mod A` with `a ∈ L`). -/
theorem pinnedValue_diagonal {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (m : ℕ) (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1) :
    Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 ρ = 0 := by
  sorry

/-- **A `1`-unit at a place where `2` is a unit is a local square** (template check). -/
theorem killsLocalGroup_of_one_unit_tmp {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (y : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hunit : A.valuation (algebraMap ↥K Ω (y : ↥K)) = 1)
    (ht : A.valuation (algebraMap ↥K Ω ((y : ↥K) - 1)) < 1) :
    ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ y u = 0 := by
  sorry

/-- **An invariant element of even valuation at a `ρ`-fixed unramified place is a local square**
(template check). -/
theorem killsLocalGroup_of_rho_fixed_tmp {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (a : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hfixA : Work.SSGRoute.ZDataMup.galLift K ρ • A = A)
    (hunram : ¬ SSGRoute.IsRamifiedIn k K A)
    (hafix : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a)
    (heven : ∃ d : (↥K)ˣ, A.valuation (algebraMap ↥K Ω (a : ↥K))
      = A.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2) :
    ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a u = 0 := by
  sorry

/-- **The p. 16 Claim** (Schmidt–Wingberg, the `m = l` case of the recursion's Claim):  for a
history satisfying `PreTwo` at every prefix, and every involution `res k K σ` of `Gal(K|k)`, the
Kummer cochain of `b_m` kills the local group of the `σ`-sibling of its own escape prime `Q_m`. -/
theorem claimOfPreTwo_diagonal {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (k := k) (Ω := Ω) (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s) :
    ∀ m : ℕ, ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f m).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
  intro m σ hσK hσ2 u hu
  obtain ⟨hfin, hsplit, hdisjG, hdisjC, hexcl, hreal, hinv, hconf9, hnorm⟩ := hs (m + 1)
  have hm : m < m + 1 := Nat.lt_succ_self m
  set t : K ≃ₐ[k] K := SSGRoute.res k K σ with ht
  have ht1 : t ≠ 1 := by
    intro h1
    have hmem : σ ∈ (SSGRoute.res k K).ker := by
      rw [MonoidHom.mem_ker, ← ht]
      exact h1
    exact hσK (by rwa [IntermediateField.restrictNormalHom_ker K] at hmem)
  have ht2 : t ^ 2 = 1 := by
    rw [ht]
    exact hσ2
  -- the strong confinement of the recursion's classes outside their own escape prime
  have hconf : ∀ j : ℕ, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K ((s.f j).1) B) →
      ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f j).2 τ = 0 :=
    Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ) hKΛ
      ζ hζ hζK S y hy hyT s hs
  -- the sibling of `Q_m` at `res σ`, and the `K`-conjugacy `σ • Q_m ∼ sibling`
  have hAtt : Work.SSGRoute.gesKConj K (σ • (s.f m).1)
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) := by
    refine ⟨Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹, ?_, ?_⟩
    · rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_inv,
        Work.SSGRoute.ZDataMup.galLift_spec, ht, mul_inv_cancel]
    · show (Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹) • (σ • (s.f m).1)
        = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1
      rw [mul_smul, inv_smul_smul, Work.SSGRoute.ZDataMup.siblingPlace]
  have hQfin : SSGRoute.IsFinPlace k ((s.f m).1) := hfin m hm
  have hAfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) :=
    (SSGRoute.isFinPlace_smul_iff (s.f m).1 (Work.SSGRoute.ZDataMup.galLift K t)).mpr hQfin
  have hQsplit : SSGRoute.IsSplitIn k K ((s.f m).1) :=
    Work.SSGRoute.NodeS35.isSplitIn_of_le (K := K) (N := Λ) hKΛ (hsplit m hm)
  have hsep : ¬ Work.SSGRoute.gesKConj K ((s.f m).1)
      (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1) :=
    Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K ht1 hQsplit
  have hkillA : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.galLift K t • (s.f m).1) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 τ = 0 :=
    fun τ hτK hτI => hconf m _ hAfin hsep τ hτK hτI
  -- the Kummer-pinned Frobenius at the sibling
  haveI : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  haveI : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  haveI : NumberField
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) (s.f m).2) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (s.f m).2
  obtain ⟨⟨ψ, hψ⟩, hpin⟩ := Work.SSGRoute.NodeS35.exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => ((s.f m).1, (s.f m).2)) 0
    (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) hAfin hkillA
  have hpinv : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ
      = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
          (fun _ => ((s.f m).1, (s.f m).2))
          (fun _ => preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 t :=
    Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 t ht1 ψ hψ hpin
  have hpinVal : Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK
      (fun _ => ((s.f m).1, (s.f m).2))
      (fun _ => preTwo_finPlace_diag (K := K) ζ hζ hζK S y s hs m) 0 t = 0 :=
    pinnedValue_diagonal (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin hSdisj hSram
      y hy hyc hyS hyT hy0 hyinf s hs m t ht1 ht2
  have h0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 ψ = 0 := by
    rw [hpinv, hpinVal]
  -- the whole local group at the sibling vanishes
  have hmain := Work.SSGRoute.NodeS37.pinnedZeroImpLocalGroup (K := K) ζ hζ hζK (s.f m).2
    (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) hAfin hkillA ψ hψ hpin h0
  -- transport the local group of `σ • Q_m` to the sibling
  obtain ⟨w, hwK, hwA⟩ := hAtt
  have huK : u ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hu).2
  have huD : u ∈ SSGRoute.decomp k (σ • (s.f m).1) := (Subgroup.mem_inf.mp hu).1
  have hu'K : w * u * w⁻¹ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hwK huK) (K.fixingSubgroup.inv_mem hwK)
  have hu'D : w * u * w⁻¹ ∈ SSGRoute.decomp k
      (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1) := by
    show (w * u * w⁻¹) • (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1)
      = Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1
    rw [mul_smul, mul_smul, show w⁻¹ • (Work.SSGRoute.ZDataMup.siblingPlace K t (s.f m).1)
        = σ • (s.f m).1 from by rw [← hwA, inv_smul_smul],
      show u • (σ • (s.f m).1) = σ • (s.f m).1 from MulAction.mem_stabilizer_iff.mp huD,
      ← hwA]
  have hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 (w * u * w⁻¹)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u :=
    Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK (s.f m).2 hwK u
  have hfinal : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (s.f m).2 u = 0 := by
    rw [← hval]
    exact hmain _ (Subgroup.mem_inf.mpr ⟨hu'D, hu'K⟩)
  rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK
    (s.f m).2 u]
  exact hfinal

end Work.SSGRoute.ZDataTwo.TwoRec
