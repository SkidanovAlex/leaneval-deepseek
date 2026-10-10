import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.AuxChase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open scoped Pointwise BigOperators

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- **Isotropy of the relaxed level-`K` localisation image**: a global level-`K` cocycle `z` which
is unramified outside the level-`K` classes of `T` except at the places splitting in `Λ`, paired
with a relaxed dual class `b` (unramified outside those classes, locally trivial at the `Λ`-split
places), sums to zero over `T`.

This is the relaxed analogue of `Work.SSGRoute.ZDataMup.sum_pair_selmer_eq_zero`, and the proof is
the one of `Work.SSGRoute.auxDatum_orthogonal_of_productFormula`
(`ZConstruction/AuxChase.lean`), verbatim, with the prescribed datum `auxDatum K S y₁` replaced by
`z`, its `ZHyp.hyS` clause replaced by `hzunr`, and the last step (the comparison with the datum)
deleted. -/
theorem relaxedSum_pair_eq_zero
    {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hprod : Work.SSGRoute.ZDataMup.IsProductFormula p k Ω K pair)
    (hunr : Work.SSGRoute.IsUnramifiedOrthogonal (p := p) K pair)
    {T : Finset (ValuationSubring Ω)} (hTfin : ∀ A ∈ T, IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.KConj K A B → A = B)
    {z b : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hz : IsCocycleOn (res k K) K.fixingSubgroup z)
    (hzl : IsLocConstOn K.fixingSubgroup z)
    (hzunr : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.KConj K A B) → ¬ IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → z σ = 0)
    (hb : Work.SSGRoute.IsRelaxedDual (p := p) K Λ T b) :
    ∑ A ∈ T, pair (decomp k A ⊓ K.fixingSubgroup) z b = 0 := by
  classical
  obtain ⟨hboc, hbloc, hbunr, hbtriv⟩ := hb
  -- (0) additivity of `z` on `G_K` (the restriction is trivial on `G_K`)
  have hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
    intro g hg h hh
    rw [hz g hg h hh, ZDataMup.res_eq_one_of_mem_fixingSubgroup hg, one_smul]
  -- (1) the level at which `z` vanishes
  obtain ⟨N, _hKN, hNfin, hNgal, hNv⟩ :=
    exists_level_vanishing_finite (K := K) hzadd hzl
  haveI : FiniteDimensional k N := hNfin
  haveI : IsGalois k N := hNgal
  -- (2) the `G_k`-conjugacy cover of the places ramified in `N|k`
  obtain ⟨S', hS'fin, hS'disj, _hS'sub, hS'ram⟩ :=
    ZConstruction.exists_finset_ramifiedPlaces p (Fact.out : p.Prime) k Ω N ∅ (by simp) (by simp)
  -- (3) the level-`K` cover, glued to `T`
  obtain ⟨T'', hT''fin, hT''disj, hT''sub, _hT''cov⟩ :=
    ZConstruction.exists_finset_KConj_cover p k Ω K T S'
      hTfin hTdisj hS'fin hS'disj
  -- (4) the zero extensions
  have hcocZ : IsCocycleOn (res k K) K.fixingSubgroup (zeroOff K z) :=
    isCocycleOn_zeroOff hz
  have hlocZ : IsLocConstOn K.fixingSubgroup (zeroOff K z) :=
    isLocConstOn_zeroOff hzl
  have hcocB : IsCocycleOn (res k K) K.fixingSubgroup (zeroOff K b) :=
    isCocycleOn_zeroOff hboc
  have hlocB : IsLocConstOn K.fixingSubgroup (zeroOff K b) :=
    isLocConstOn_zeroOff hbloc
  -- (5) the unramifiedness outside `T''`, at level `k`
  have hunram : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ T'', ¬ ∃ τ ∈ K.fixingSubgroup,
        ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ →
        zeroOff K z σ = 0 ∧ zeroOff K b σ = 0 := by
    intro B hB hnot σ hσI
    have hnotK : ∀ A ∈ T'', ¬ KConj K A B := by
      intro A hA hc
      exact hnot A hA (kConj_forall_mem_of_kConj hc)
    by_cases hσK : σ ∈ K.fixingSubgroup
    · rw [zeroOff_eq_of_mem hσK, zeroOff_eq_of_mem hσK]
      refine ⟨?_, ?_⟩
      · by_contra hne
        have hσN : σ ∈ N.fixingSubgroup := by
          by_contra hσN
          have hram : IsRamifiedIn k N B := ⟨σ, hσI, hσN⟩
          obtain ⟨A, hA, hconj⟩ := hS'ram B hB (Or.inl hram)
          obtain ⟨A', hA', hc⟩ := _hT''cov B hB ⟨A, hA, hconj⟩
          exact hnotK A' hA' hc
        exact hne (hNv σ hσN)
      · exact hbunr B hB (fun A₀ hA₀ hc => hnotK A₀ (hT''sub A₀ hA₀) hc) σ hσK hσI
    · rw [zeroOff_eq_zero_of_not_mem hσK, zeroOff_eq_zero_of_not_mem hσK]
      exact ⟨rfl, rfl⟩
  -- (6) Hilbert reciprocity over `T''`
  have hsumZ : ∑ A ∈ T'', pair (decomp k A ⊓ K.fixingSubgroup) (zeroOff K z)
      (zeroOff K b) = 0 :=
    hprod (zeroOff K z) (zeroOff K b) hcocZ hlocZ hcocB hlocB T'' hT''fin
      (fun A hA B hB' h => hT''disj A hA B hB' (kConj_of_forall_mem h)) hunram
  -- (7) replace the zero extensions by the original cochains
  have hsumY : ∑ A ∈ T'', pair (decomp k A ⊓ K.fixingSubgroup) z b = 0 := by
    rw [← hsumZ]
    refine Finset.sum_congr rfl fun A hA => ?_
    have hAfin : IsFinPlace k A := hT''fin A hA
    have hH : ∃ A' : ValuationSubring Ω, IsFinPlace k A' ∧
        (decomp k A ⊓ K.fixingSubgroup) = (decomp k A' ⊓ K.fixingSubgroup) :=
      ⟨A, hAfin, rfl⟩
    have hle : decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
    have hcZ : IsCocycleOn (res k K)
        (decomp k A ⊓ K.fixingSubgroup) z :=
      ZDataMup.isCocycleOn_of_le hle hz
    have hlZ : IsLocConstOn (decomp k A ⊓ K.fixingSubgroup) z :=
      ZDataMup.isLocConstOn_of_le hle hzl
    have hcZ' : IsCocycleOn (res k K)
        (decomp k A ⊓ K.fixingSubgroup) (zeroOff K z) :=
      ZDataMup.isCocycleOn_of_le hle hcocZ
    have hlZ' : IsLocConstOn (decomp k A ⊓ K.fixingSubgroup) (zeroOff K z) :=
      ZDataMup.isLocConstOn_of_le hle hlocZ
    have hcB' : IsCocycleOn (res k K)
        (decomp k A ⊓ K.fixingSubgroup) b :=
      ZDataMup.isCocycleOn_of_le hle hboc
    have hlB' : IsLocConstOn (decomp k A ⊓ K.fixingSubgroup) b :=
      ZDataMup.isLocConstOn_of_le hle hbloc
    have hcB'' : IsCocycleOn (res k K)
        (decomp k A ⊓ K.fixingSubgroup) (zeroOff K b) :=
      ZDataMup.isCocycleOn_of_le hle hcocB
    have hlB'' : IsLocConstOn (decomp k A ⊓ K.fixingSubgroup) (zeroOff K b) :=
      ZDataMup.isLocConstOn_of_le hle hlocB
    have hstep1 : pair (decomp k A ⊓ K.fixingSubgroup) z b
        = pair (decomp k A ⊓ K.fixingSubgroup) z (zeroOff K b) :=
      ZDataMup.pair_congr_of_eqOn_right hpair hH ⟨hcZ, hlZ⟩ ⟨hcB', hlB'⟩ ⟨hcB'', hlB''⟩
        (fun g hg => (zeroOff_eq_of_mem (f := b) (hle hg)).symm)
    have hstep2 : pair (decomp k A ⊓ K.fixingSubgroup) z (zeroOff K b)
        = pair (decomp k A ⊓ K.fixingSubgroup) (zeroOff K z) (zeroOff K b) :=
      ZDataMup.pair_congr_of_eqOn_left hpair hH ⟨hcZ, hlZ⟩ ⟨hcZ', hlZ'⟩ ⟨hcB'', hlB''⟩
        (fun g hg => (zeroOff_eq_of_mem (f := z) (hle hg)).symm)
    rw [hstep1, hstep2]
  -- (8) the terms at the new places `T'' ∖ T` vanish
  have hRvan : ∀ A ∈ T'' \ T,
      pair (decomp k A ⊓ K.fixingSubgroup) z b = 0 := by
    intro A hA
    obtain ⟨hAT'', hAnT⟩ := Finset.mem_sdiff.mp hA
    have hAfin : IsFinPlace k A := hT''fin A hAT''
    have hnotT : ∀ A₀ ∈ T, ¬ KConj K A₀ A := by
      intro A₀ hA₀ hc
      have hA₀T'' : A₀ ∈ T'' := hT''sub A₀ hA₀
      have hEq : A = A₀ := hT''disj A hAT'' A₀ hA₀T'' (ZConstruction.kConj_symm hc)
      exact hAnT (hEq ▸ hA₀)
    have hH : ∃ A' : ValuationSubring Ω, IsFinPlace k A' ∧
        (decomp k A ⊓ K.fixingSubgroup) = (decomp k A' ⊓ K.fixingSubgroup) :=
      ⟨A, hAfin, rfl⟩
    have hle : decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
    have hcZ : IsCocycleOn (res k K)
        (decomp k A ⊓ K.fixingSubgroup) z :=
      ZDataMup.isCocycleOn_of_le hle hz
    have hlZ : IsLocConstOn (decomp k A ⊓ K.fixingSubgroup) z :=
      ZDataMup.isLocConstOn_of_le hle hzl
    have hcB' : IsCocycleOn (res k K)
        (decomp k A ⊓ K.fixingSubgroup) b :=
      ZDataMup.isCocycleOn_of_le hle hboc
    have hlB' : IsLocConstOn (decomp k A ⊓ K.fixingSubgroup) b :=
      ZDataMup.isLocConstOn_of_le hle hbloc
    by_cases hsplit : IsSplitIn k Λ A
    · -- `b` is locally trivial at the `Λ`-split place `A`
      have hbcob : IsCoboundaryOn (res k K)
          (decomp k A ⊓ K.fixingSubgroup) b := by
        refine ⟨0, fun g hg => ?_⟩
        rw [hbtriv A hAfin hnotT hsplit g (Subgroup.mem_inf.mp hg).2 (Subgroup.mem_inf.mp hg).1]
        simp
      exact hpair.vanishes_coboundary _ hH z b ⟨hcZ, hlZ⟩ ⟨hcB', hlB'⟩ (Or.inr hbcob)
    · -- otherwise both classes are unramified at `A`
      exact hunr A hAfin z b ⟨hcZ, hlZ⟩ ⟨hcB', hlB'⟩
        (fun σ hσ hσI => hzunr A hAfin hnotT hsplit σ hσ hσI)
        (fun σ hσ hσI => hbunr A hAfin hnotT σ hσ hσI)
  -- (9) split the sum
  have hunion : T ∪ (T'' \ T) = T'' := Finset.union_sdiff_of_subset (fun a ha => hT''sub a ha)
  have hdisj : Disjoint T (T'' \ T) := Finset.disjoint_sdiff
  have hsplitSum : ∑ A ∈ T'', pair (decomp k A ⊓ K.fixingSubgroup) z b
      = ∑ A ∈ T, pair (decomp k A ⊓ K.fixingSubgroup) z b
        + ∑ A ∈ T'' \ T, pair (decomp k A ⊓ K.fixingSubgroup) z b := by
    conv_lhs => rw [← hunion]
    rw [Finset.sum_union hdisj]
  have hTsum : ∑ A ∈ T, pair (decomp k A ⊓ K.fixingSubgroup) z b = 0 := by
    have h2 : (∑ A ∈ T, pair (decomp k A ⊓ K.fixingSubgroup) z b)
        + (∑ A ∈ T'' \ T, pair (decomp k A ⊓ K.fixingSubgroup) z b) = 0 := by
      rw [← hsplitSum]
      exact hsumY
    simpa [Finset.sum_eq_zero hRvan] using h2
  exact hTsum

end Work.SSGRoute.ZConstruction
