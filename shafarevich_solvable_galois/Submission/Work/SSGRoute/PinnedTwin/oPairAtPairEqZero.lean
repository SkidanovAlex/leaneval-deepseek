import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.henselUnitSquare
import Submission.Work.SSGRoute.P2Nat.oPairAt_smul_conj
import Submission.Work.SSGRoute.SSG8Escape.ChebotarevDensityInput
import Submission.Work.SSGRoute.ZConstruction.LevelKHilbert
import Submission.Work.SSGRoute.ZConstruction.hilbertSymbolNegOneGlobal
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_dictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two-place cancellation of the level-`K` Kummer pairing at `p = 2`

For an involution `ρ ≠ 1` of `K|k`, a unit `a ∈ Kˣ` fixed by `ρ`, a unit `X ∈ Kˣ` with
`ρ(X) = -X`, and a finite place `B` of `Ω` at which `2` and `a` are units, the local Kummer
pairings of the Kummer cochains of `a` and `X` at `B` and at its `ρ`-conjugate `ρ • B` cancel:

  `⟨χ_a, χ_X⟩_B + ⟨χ_a, χ_X⟩_{ρB} = 0`.

This is the `p = 2` "two-place cancellation" of Schmidt--Wingberg's corrected proof (the line
`(2bρ, a)_P · (2bρ, a)_{ρP} = (-1, a)_P = 1` of the p. 16 computation), in the language of the
local Kummer pairing `oPairAt`.

## Proof

Let `g := galLift K ρ`, so that `g • B` is the second place.

* **Galois invariance** (`oPairAt_smul_conj`, the pairing is unchanged when both the place and the
  two units are transported): with `conjUnit g a = a` and `conjUnit g X = -X`,
  `⟨χ_a, χ_{-X}⟩_{gB} = ⟨χ_a, χ_X⟩_B`, and likewise `⟨χ_a, χ_{-1}⟩_{gB} = ⟨χ_a, χ_{-1}⟩_B`.
* **Bilinearity in the second variable** (`oPairAt_add_right`): `χ_{-X} = χ_{-1} + χ_X`.
* **Vanishing** (`oPairAt_chi_neg_one_eq_zero`): `⟨χ_a, χ_{-1}⟩_B = 0` because `a` is a unit at the
  odd place `B`, i.e. the local Hilbert symbol `(-1, a)_B = 1` (`hilbertSymbolNegOneGlobal`).

Hence the sum equals `⟨χ_a, χ_{-X}⟩_{gB} + ⟨χ_a, χ_X⟩_{gB} = ⟨χ_a, χ_{-1}⟩_{gB} = ⟨χ_a, χ_{-1}⟩_B
= 0`.
-/

namespace Work.SSGRoute.PinnedTwin

/-- **Additivity of `oPairAt` in its second variable.**  For two locally constant `1`-cocycles
`v`, `w` on the level-`K` local group of `A` (in particular for the Kummer cochains of two global
units), the pairing against `v + w` is the sum of the pairings. -/
private lemma oPairAt_add_right {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : _root_.SSGRoute.IsFinPlace k A)
    (u v w : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hv : v ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup))
    (hw : w ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA u (v + w)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA u v
        + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA
            u w := by
  simp only [Work.SSGRoute.ZDataMup.OddForm.oPairAt]
  rw [Work.SSGRoute.toClass_add p k Ω K (ZMod p)
    (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) hv hw]
  exact map_add (Work.SSGRoute.ZDataMup.OddForm.oPairForm (K := K) (p := p) (k := k) (Ω := Ω)
    ζ hζ hA
    (Work.SSGRoute.toClass p k Ω K (ZMod p)
      (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) u)) _ _

/-- **The pairing of a unit with `-1` vanishes at a place where `2` is a unit.**  For a finite place
`B` with `B ∤ 2` and a global unit `a` which is a `B`-adic unit,
`⟨χ_a, χ_{-1}⟩_B = ⟨a, -1⟩_B = 0` (equivalently `(-1, a)_B = 1`). -/
private lemma oPairAt_chi_neg_one_eq_zero {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (a : (↥K)ˣ)
    (B : ValuationSubring Ω) (hB : _root_.SSGRoute.IsFinPlace k B)
    (hB2 : ¬ B.valuation (2 : Ω) < 1)
    (hvala : B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        B hB (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1)) = 0 := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  rw [Work.SSGRoute.P2Nat.oPairAt_eq_oPairGlob_aux (K := K) ζ hζ hζK a (-1) B hB]
  by_cases ha2 : a ∈ NK.LocalAnabelian.powSubgroup 2 ↥K
  · exact Work.SSGRoute.H9.oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) hζ' a (-1) B hB ha2
  · rw [Work.SSGRoute.ZConstruction.oPairGlob_eq_finPair (K := K) (k := k) (Ω := Ω) ζ hζ hζK
      B hB a (-1) ha2]
    rw [Work.SSGRoute.ZDataTwo.finPair_comm ↥K
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB) a (-1)]
    rw [Work.SSGRoute.ZDataTwo.finPair]
    simp only [Work.SSGRoute.ZDataTwo.localImage]
    have h𝔭 : B.comap (algebraMap ↥K Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
          (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB) :=
      Submission.NeukirchUchida.primeOf_spec (K₁ := ↥K) (K₁' := Ω) B
        (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := B) hB)
    have h2 : ¬ (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB).valuation ↥K
        (2 : ↥K) < 1 := by
      intro h
      refine hB2 ?_
      have h' := (Work.SSGRoute.ZConstruction.place_valuation_lt_one_iff_base (K := ↥K) (Ω := Ω) B
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB) h𝔭 (2 : ↥K)).mpr h
      rwa [map_ofNat (algebraMap ↥K Ω) 2] at h'
    have h2unit : IsUnit (2 : (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B
        hB).adicCompletionIntegers ↥K) :=
      Work.SSGRoute.ZDataTwo.TwoRec.isUnit_two_adicCompletionIntegers_of_not_lt_one
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB) h2
    have ha_unit : (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB).valuation ↥K
        (a : ↥K) = 1 :=
      (Work.SSGRoute.ZConstruction.place_valuation_eq_one_iff_base (K := ↥K) (Ω := Ω) B
        (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB) h𝔭 (a : ↥K)).mp hvala
    rw [Work.SSGRoute.ZConstruction.hilbertSymbolNegOneGlobal
      (Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB) h2unit a ha_unit]
    simp

theorem oPairAtPairEqZero {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (a X : (↥K)ˣ)
    (ha : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a)
    (hX : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) X = -X)
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hB2 : ¬ B.valuation (2 : Ω) < 1)
    (hvala : B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        B hB (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B)
        ((SSGRoute.isFinPlace_smul_iff (k := k) B (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hB)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) = 0 := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  haveI hfd₁ : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' a
  haveI hgal₁ : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' a
  haveI hnf₁ : NumberField
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' a
  haveI hfd₂ : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a)) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a)
  haveI hgal₂ : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a)) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a)
  haveI hnf₂ : NumberField
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2)
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a)) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a)
  have hB' : _root_.SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K ρ • B) :=
    (Work.SSGRoute.isFinPlace_smul_iff (k := k) B (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hB
  -- Galois invariance of the pairing, with the anti-invariant unit `X` transported to `-X`
  have hI : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-X))
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        B hB (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) := by
    have h := Work.SSGRoute.P2Nat.oPairAt_smul_conj k Ω K ζ hζ hζK a X ρ B hB hB'
    rwa [ha, hX] at h
  have hneg1 : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) (-1 : (↥K)ˣ)
      = -1 := by
    rw [Work.SSGRoute.H9.conjUnit, Work.SSGRoute.ZDataMup.galLift_spec]
    ext
    simp
  -- Galois invariance of the pairing against `-1`
  have hII : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1))
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        B hB (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1)) := by
    have h := Work.SSGRoute.P2Nat.oPairAt_smul_conj k Ω K ζ hζ hζK a (-1) ρ B hB hB'
    rwa [ha, hneg1] at h
  -- the cochain of `-X` is the sum of the cochains of `-1` and of `X`
  have hχ : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-X)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1 : (↥K)ˣ)
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X := by
    have h := Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK (-1 : (↥K)ˣ) X
    rw [show (-1 : (↥K)ˣ) * X = -X from by simp] at h
    exact h
  have hv : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1 : (↥K)ˣ)
      ∈ Work.SSGRoute.lcCocycles 2 k Ω K (ZMod 2)
        (_root_.SSGRoute.decomp k (Work.SSGRoute.ZDataMup.galLift K ρ • B) ⊓ K.fixingSubgroup) :=
    ⟨Work.SSGRoute.isCocycleOn_mono (_root_.SSGRoute.res k K) inf_le_right
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ (-1)),
      Work.SSGRoute.isLocConstOn_mono inf_le_right
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ (-1))⟩
  have hw : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X
      ∈ Work.SSGRoute.lcCocycles 2 k Ω K (ZMod 2)
        (_root_.SSGRoute.decomp k (Work.SSGRoute.ZDataMup.galLift K ρ • B) ⊓ K.fixingSubgroup) :=
    ⟨Work.SSGRoute.isCocycleOn_mono (_root_.SSGRoute.res k K) inf_le_right
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ X),
      Work.SSGRoute.isLocConstOn_mono inf_le_right
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ X)⟩
  have hadd := oPairAt_add_right (K := K) (k := k) (Ω := Ω) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ'
    (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1))
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) hv hw
  have hzero := oPairAt_chi_neg_one_eq_zero ζ hζ hζK a B hB hB2 hvala
  calc Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        B hB (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-X))
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) := by rw [hI]
    _ = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1)
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) := by rw [hχ]
    _ = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1))
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) := by rw [hadd]
    _ = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        B hB (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (-1)) := by
        rw [add_assoc,
          show Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
              (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
              (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
              (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
              (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
            + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
              (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
              (Work.SSGRoute.ZDataMup.galLift K ρ • B) hB'
              (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
              (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) = 0 from by
            rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul],
          add_zero, hII]
    _ = 0 := hzero

end Work.SSGRoute.PinnedTwin
