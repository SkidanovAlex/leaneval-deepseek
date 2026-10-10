import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Valuation

open WithZero

set_option linter.style.haveILetI false

/-- In `ℤᵐ⁰`, an element `α` with `0 < α < 1` has arbitrarily small positive powers. -/
private lemma exists_pow_le_of_lt_one (α β : ℤᵐ⁰) (hα : α < 1) (hα0 : α ≠ 0) (hβ0 : β ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ α ^ n ≤ β := by
  have hlog : WithZero.log α ≤ -1 := by
    have h : WithZero.log α < 0 := by
      rw [← WithZero.log_one, WithZero.log_lt_log hα0 one_ne_zero]
      exact hα
    omega
  have hαexp : α ≤ WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log hα0]
    exact WithZero.exp_le_exp.mpr hlog
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hβ0
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  calc α ^ (k + 1) ≤ (WithZero.exp (-1 : ℤ)) ^ (k + 1) :=
        pow_le_pow_left₀ (bot_le : (0 : ℤᵐ⁰) ≤ α) hαexp _
    _ = WithZero.exp (-(k + 1 : ℤ)) := by
        rw [← WithZero.exp_nsmul]; congr 1; ring
    _ ≤ WithZero.exp (-(k : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
    _ ≤ β := le_of_lt hk

/-- **The Archimedean divisibility property of the valuation rings of `F` over a number
field `K`.**  If `C` is a valuation subring of `F` whose restriction to `K` is proper (so that
`F/K` carries a genuine valuation), then for `a ∈ C` nonzero and `b` in the maximal ideal of
`C`, some positive power of `b` is divisible by `a` in `C`. -/
private theorem exists_pow_mul_eq_of_mem_maximalIdeal
    {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F] [Algebra.IsAlgebraic K F]
    (C : ValuationSubring F) (hKC : C.comap (algebraMap K F) ≠ ⊤)
    {a b : C} (ha : a ≠ 0) (hb : b ∈ IsLocalRing.maximalIdeal C) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : C, a * c = b ^ n := by
  classical
  rcases eq_or_ne b 0 with hb0 | hb0
  · exact ⟨1, one_pos, 0, by rw [hb0]; simp⟩
  -- The finite subextension `M = K(a, b)` of `F`: a number field.
  set M : IntermediateField K F := IntermediateField.adjoin K ({(a : F), (b : F)} : Set F) with hM
  have hx : IsIntegral K (a : F) := Algebra.IsIntegral.isIntegral (a : F)
  have hy : IsIntegral K (b : F) := Algebra.IsIntegral.isIntegral (b : F)
  haveI hMfin : FiniteDimensional K M := by
    rw [hM]; exact IntermediateField.finiteDimensional_adjoin_pair hx hy
  haveI hMN : NumberField ↥M := NumberField.of_module_finite K ↥M
  have haM : (a : F) ∈ (M : Set F) := by
    rw [hM]; exact IntermediateField.subset_adjoin K _ (by simp)
  have hbM : (b : F) ∈ (M : Set F) := by
    rw [hM]; exact IntermediateField.subset_adjoin K _ (by simp)
  let aM : ↥M := ⟨(a : F), haM⟩
  let bM : ↥M := ⟨(b : F), hbM⟩
  have ha0 : aM ≠ 0 := fun h =>
    ha (Subtype.ext (by simpa [aM] using congrArg Subtype.val h))
  have hb0' : bM ≠ 0 := fun h =>
    hb0 (Subtype.ext (by simpa [bM] using congrArg Subtype.val h))
  -- The valuation ring `B = C ∩ M` of the number field `M`.
  let B : ValuationSubring ↥M := C.comap (algebraMap ↥M F)
  have hBne : B ≠ ⊤ := by
    intro hB
    refine hKC ?_
    apply le_antisymm le_top
    intro x _
    rw [ValuationSubring.mem_comap]
    have hxB : algebraMap K ↥M x ∈ B := by rw [hB]; trivial
    have hxC : algebraMap ↥M F (algebraMap K ↥M x) ∈ C := ValuationSubring.mem_comap.mp hxB
    rwa [IsScalarTower.algebraMap_apply K ↥M F]
  have hR : ∀ x : NumberField.RingOfIntegers ↥M,
      algebraMap (NumberField.RingOfIntegers ↥M) ↥M x ∈ B :=
    Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring B
  obtain ⟨w, hw⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime B hBne hR
  let wv : Valuation ↥M ℤᵐ⁰ := IsDedekindDomain.HeightOneSpectrum.valuation ↥M w
  have hB_eq : B = wv.valuationSubring := by
    rw [hw, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  -- `bM` lies in the valuation ring but is not a unit.
  have hbB : bM ∈ wv.valuationSubring := by
    rw [← hB_eq, ValuationSubring.mem_comap]
    exact b.2
  have hα : wv bM < 1 := by
    refine lt_of_le_of_ne ?_ ?_
    · exact (Valuation.mem_valuationSubring_iff wv bM).mp hbB
    · intro hone
      have hbM' : bM⁻¹ ∈ wv.valuationSubring := by
        rw [Valuation.mem_valuationSubring_iff, map_inv₀, hone, inv_one]
      have hcinv : algebraMap ↥M F bM⁻¹ ∈ C := by
        have := (ValuationSubring.mem_comap (A := C) (f := algebraMap ↥M F)).mp
          (hB_eq ▸ hbM')
        simpa using this
      have hnu : ¬ IsUnit b :=
        mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal b).mp hb)
      refine hnu (IsUnit.of_mul_eq_one (⟨algebraMap ↥M F bM⁻¹, hcinv⟩ : C) ?_)
      apply Subtype.ext
      show (b : F) * algebraMap ↥M F bM⁻¹ = ((1 : C) : F)
      rw [map_inv₀]
      simp only [Subring.coe_one]
      change (b : F) * (b : F)⁻¹ = 1
      exact mul_inv_cancel₀ (by simpa using hb0)
  have hβ0 : wv aM ≠ 0 := (Valuation.ne_zero_iff wv).mpr ha0
  have hβpos : 0 < wv aM := (Valuation.pos_iff wv).mpr ha0
  have hα0 : wv bM ≠ 0 := (Valuation.ne_zero_iff wv).mpr hb0'
  obtain ⟨n, hn, hpow⟩ := exists_pow_le_of_lt_one (wv bM) (wv aM) hα hα0 hβ0
  -- The element `c = b ^ n / a` of `M` has valuation `≤ 1`, hence lies in `C`.
  let cM : ↥M := bM ^ n * aM⁻¹
  have hcB : cM ∈ wv.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]
    show wv (bM ^ n * aM⁻¹) ≤ 1
    rw [map_mul, map_inv₀, Valuation.map_pow]
    calc (wv bM) ^ n * (wv aM)⁻¹ ≤ (wv aM) * (wv aM)⁻¹ :=
          mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (le_of_lt hβpos))
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hβpos)
  have hcC : algebraMap ↥M F cM ∈ C := by
    have hcB' : cM ∈ B := hB_eq ▸ hcB
    exact ValuationSubring.mem_comap.mp hcB'
  refine ⟨n, hn, ⟨⟨algebraMap ↥M F cM, hcC⟩, ?_⟩⟩
  apply Subtype.ext
  show (a : F) * algebraMap ↥M F cM = ((b ^ n : C) : F)
  have hmul : aM * cM = bM ^ n := by
    show aM * (bM ^ n * aM⁻¹) = bM ^ n
    rw [← mul_assoc, mul_comm aM (bM ^ n), mul_assoc, mul_inv_cancel₀ ha0, mul_one]
  simpa [aM, bM, map_mul, map_pow] using congrArg (algebraMap ↥M F) hmul

/-- **Krull dimension at most one for the valuation rings of an algebraic extension of a number
field that restrict properly to the base field.** -/
private theorem krdimle_one_of_comap_ne_top
    {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F] [Algebra.IsAlgebraic K F]
    (C : ValuationSubring F) (hKC : C.comap (algebraMap K F) ≠ ⊤) :
    Ring.KrullDimLE 1 C := by
  refine Ring.KrullDimLE.mk₁' fun I hIne hIprime => ?_
  have hle : I ≤ IsLocalRing.maximalIdeal C := IsLocalRing.le_maximalIdeal_of_isPrime I
  have hmle : IsLocalRing.maximalIdeal C ≤ I := by
    intro b hb
    obtain ⟨a, haI, ha0⟩ := (Submodule.ne_bot_iff I).mp hIne
    obtain ⟨n, hn, c, hc⟩ := exists_pow_mul_eq_of_mem_maximalIdeal C hKC ha0 hb
    have hbn : b ^ n ∈ I := by rw [← hc]; exact I.mul_mem_right c haI
    exact hIprime.mem_of_pow_mem n hbn
  have hIeq : I = IsLocalRing.maximalIdeal C := le_antisymm hle hmle
  rw [hIeq]
  exact inferInstance

theorem le_eq_top_of_comap_ne_top_of_ne {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (L : IntermediateField K K') (A₁ A₂ : ValuationSubring K')
    (h₁ : A₁.comap (algebraMap ↥L K') ≠ ⊤) (h₂ : A₂.comap (algebraMap ↥L K') ≠ ⊤)
    (hne : A₁.comap (algebraMap ↥L K') ≠ A₂.comap (algebraMap ↥L K')) :
    ∀ D : ValuationSubring ↥L, A₁.comap (algebraMap ↥L K') ≤ D →
      A₂.comap (algebraMap ↥L K') ≤ D → D = ⊤ := by
  haveI hsep : Algebra.IsSeparable K K' := IsSepClosure.separable
  haveI : Algebra.IsAlgebraic K K' := hsep.isAlgebraic
  haveI : Algebra.IsAlgebraic K ↥L := inferInstance
  haveI : Algebra.IsAlgebraic ↥L K' := inferInstance
  have hK₁ : (A₁.comap (algebraMap ↥L K')).comap (algebraMap K ↥L) ≠ ⊤ := by
    intro h
    exact h₁ (Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
      (A₁.comap (algebraMap ↥L K')) inferInstance h)
  have hK₂ : (A₂.comap (algebraMap ↥L K')).comap (algebraMap K ↥L) ≠ ⊤ := by
    intro h
    exact h₂ (Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
      (A₂.comap (algebraMap ↥L K')) inferInstance h)
  haveI h1K : Ring.KrullDimLE 1 (A₁.comap (algebraMap ↥L K')) :=
    krdimle_one_of_comap_ne_top _ hK₁
  haveI h2K : Ring.KrullDimLE 1 (A₂.comap (algebraMap ↥L K')) :=
    krdimle_one_of_comap_ne_top _ hK₂
  intro D hD₁ hD₂
  rcases ValuationSubring.eq_self_or_eq_top_of_le hD₁ with h | h
  · rcases ValuationSubring.eq_self_or_eq_top_of_le hD₂ with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · exact h'
  · exact h

end Commons.NumberTheory.NumberField.Valuation
