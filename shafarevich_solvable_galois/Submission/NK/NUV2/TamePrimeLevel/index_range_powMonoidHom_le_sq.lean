import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.NK.NUV2.TamePrimeLevel.natCard_quot_range_powMonoidHom_sup_inf
import Submission.NK.TameStructureDeep.Tame.Unconditional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.overlappingInstances false

open scoped ValuativeRel

namespace NK.NUV2.TamePrimeLevel

noncomputable section

/-! ## Generic group theory: the `ℓ`-elementary quotient

Two general lemmas about the cardinality of `G ⧸ G^ℓ`, where `G^ℓ = (powMonoidHom ℓ).range` is the
subgroup of `ℓ`-th powers: invariance under a multiplicative equivalence, and the value `ℓ` for an
infinite cyclic group. -/

section Generic

variable {G H : Type*}

/-- Transfer of the cardinality of `G ⧸ G^ℓ` along a multiplicative equivalence. -/
theorem natCard_quot_range_powMonoidHom_mulEquiv [CommGroup G] [CommGroup H]
    (e : G ≃* H) (ℓ : ℕ) :
    Nat.card (G ⧸ (powMonoidHom ℓ : G →* G).range) =
      Nat.card (H ⧸ (powMonoidHom ℓ : H →* H).range) := by
  have hcomap : ((powMonoidHom ℓ : H →* H).range).comap (e : G →* H) =
      (powMonoidHom ℓ : G →* G).range := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.mem_range]
    simp only [powMonoidHom_apply]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := e.surjective y
      refine ⟨z, ?_⟩
      apply e.injective
      rw [map_pow]
      exact hy
    · rintro ⟨z, rfl⟩
      exact ⟨e z, by rw [map_pow]; rfl⟩
  have h := Subgroup.index_comap_of_surjective ((powMonoidHom ℓ : H →* H).range)
    (f := (e : G →* H)) e.surjective
  rw [hcomap] at h
  rw [← Subgroup.index_eq_card ((powMonoidHom ℓ : G →* G).range),
    ← Subgroup.index_eq_card ((powMonoidHom ℓ : H →* H).range)]
  exact h

/-- The `ℓ`-elementary quotient of an infinite cyclic group has order `ℓ`. -/
theorem natCard_quot_range_powMonoidHom_zpowers_eq [CommGroup G] (g : G)
    (hg : orderOf g = 0) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Nat.card (↥(Subgroup.zpowers g) ⧸
      (powMonoidHom ℓ : ↥(Subgroup.zpowers g) →* ↥(Subgroup.zpowers g)).range) = ℓ := by
  set A : Subgroup G := Subgroup.zpowers g with hA
  have hKeq : (powMonoidHom ℓ : ↥A →* ↥A).range = (Subgroup.zpowers (g ^ ℓ)).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    simp only [powMonoidHom_apply]
    constructor
    · rintro ⟨y, hy⟩
      have hy' : ((y : G)) ^ ℓ = (x : G) := by
        have h2 := congrArg (fun z : ↥A => (z : G)) hy
        simpa using h2
      obtain ⟨j, hj⟩ := y.2
      refine ⟨j, ?_⟩
      rw [← hy', ← hj, ← zpow_natCast g ℓ, ← zpow_mul, ← zpow_natCast (g ^ j) ℓ, ← zpow_mul,
        mul_comm ((ℓ : ℤ)) j]
    · rintro ⟨j, hj⟩
      have hx : (x : G) = (g ^ j) ^ ℓ := by
        rw [← hj, ← zpow_natCast g ℓ, ← zpow_mul, ← zpow_natCast (g ^ j) ℓ, ← zpow_mul,
          mul_comm ((ℓ : ℤ)) j]
      refine ⟨⟨g ^ j, Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      show (((g ^ j : G)) ^ ℓ) = (x : G)
      rw [hx]
  rw [← Subgroup.index_eq_card ((powMonoidHom ℓ : ↥A →* ↥A).range), hKeq]
  exact NK.LocalReciprocityLubinTate.Units.relIndex_zpowers_pow_eq g hg hℓ

end Generic

/-! ## Hensel: the `ℓ`-elementary quotient of the units of a Henselian local ring

For a Henselian local ring `R` with finite residue field `k` and `ℓ` a prime which is a unit of
`R`, reduction mod the maximal ideal induces an isomorphism
`Rˣ ⧸ (Rˣ)^ℓ ≃ kˣ ⧸ (kˣ)^ℓ`: it is surjective because `R → k` is, and its kernel is exactly
`(Rˣ)^ℓ` because `ℓ`-th roots of units lift through a Henselian local ring.  Since `kˣ` is cyclic,
`kˣ ⧸ (kˣ)^ℓ ≅ ker(x ↦ x ^ ℓ)` has at most `ℓ` elements
(`IsCyclic.card_pow_eq_one_le`). -/

/-- The `ℓ`-elementary quotient of the units of a Henselian local ring with finite residue field
has order at most `ℓ`, for a prime `ℓ` which is a unit of the ring. -/
theorem natCard_units_quot_range_powMonoidHom_le {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hunit : IsUnit ((ℓ : ℕ) : R)) :
    Nat.card (Rˣ ⧸ (powMonoidHom ℓ : Rˣ →* Rˣ).range) ≤ ℓ := by
  classical
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  set k := IsLocalRing.ResidueField R with hk
  set KH : Subgroup kˣ := (powMonoidHom ℓ : kˣ →* kˣ).range with hKH
  let Φ : Rˣ →* kˣ ⧸ KH :=
    (QuotientGroup.mk' KH).comp (Units.map (IsLocalRing.residue R).toMonoidHom)
  have hΦ : ∀ u : Rˣ, Φ u =
      QuotientGroup.mk ((Units.map (IsLocalRing.residue R).toMonoidHom) u) :=
    fun u => QuotientGroup.mk'_apply _ _
  have hker : Φ.ker = (powMonoidHom ℓ : Rˣ →* Rˣ).range := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hu
      rw [hΦ] at hu
      exact Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow ℓ hunit u
        ((QuotientGroup.eq_one_iff _).mp hu)
    · rintro ⟨v, rfl⟩
      rw [hΦ]
      exact (QuotientGroup.eq_one_iff _).mpr
        (MonoidHom.mem_range.mpr ⟨(Units.map (IsLocalRing.residue R).toMonoidHom) v, rfl⟩)
  have hsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective KH y
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (w : k)
    have hrunit : IsUnit r := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hr]
      exact Units.ne_zero w
    have hw : (Units.map (IsLocalRing.residue R).toMonoidHom) hrunit.unit = w := by
      ext
      rw [Units.coe_map, IsUnit.unit_spec]
      exact hr
    refine ⟨hrunit.unit, ?_⟩
    rw [hΦ, hw, ← QuotientGroup.mk'_apply]
  haveI hfinQ : Finite (kˣ ⧸ KH) := Finite.of_surjective _ (QuotientGroup.mk'_surjective KH)
  have hmain : Nat.card (kˣ ⧸ KH) = Nat.card ↥(powMonoidHom ℓ : kˣ →* kˣ).ker := by
    set Kker := (powMonoidHom ℓ : kˣ →* kˣ).ker with hKker
    have hA : Nat.card ↥KH * KH.index = Nat.card kˣ := Subgroup.card_mul_index KH
    have hB : Nat.card ↥Kker * Kker.index = Nat.card kˣ := Subgroup.card_mul_index Kker
    have hC : Kker.index = Nat.card ↥KH := Subgroup.index_ker (powMonoidHom ℓ : kˣ →* kˣ)
    have hpos : 0 < Nat.card ↥KH := Nat.card_pos
    rw [hC] at hB
    have hAB : Nat.card ↥KH * KH.index = Nat.card ↥KH * Nat.card ↥Kker := by
      rw [hA, ← hB, mul_comm]
    have hcancel : KH.index = Nat.card ↥Kker := Nat.mul_left_cancel hpos hAB
    rw [← Subgroup.index_eq_card KH, hcancel]
  have hkerle : Nat.card ↥(powMonoidHom ℓ : kˣ →* kˣ).ker ≤ ℓ := by
    haveI : Fintype ↥(powMonoidHom ℓ : kˣ →* kˣ).ker := Fintype.ofFinite _
    have hce : Fintype.card ↥(powMonoidHom ℓ : kˣ →* kˣ).ker =
        Fintype.card {x : kˣ // x ^ ℓ = 1} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x => by
        simp [MonoidHom.mem_ker, powMonoidHom_apply])
    have hfs : Fintype.card {x : kˣ // x ^ ℓ = 1} =
        (Finset.univ.filter (fun x : kˣ => x ^ ℓ = 1)).card := by
      rw [Fintype.card_subtype]
    rw [Nat.card_eq_fintype_card, hce, hfs]
    exact IsCyclic.card_pow_eq_one_le (α := kˣ) hℓ.pos
  calc Nat.card (Rˣ ⧸ (powMonoidHom ℓ : Rˣ →* Rˣ).range)
      = Nat.card (Rˣ ⧸ Φ.ker) := by rw [hker]
    _ = Nat.card ↥Φ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
    _ ≤ Nat.card (kˣ ⧸ KH) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = Nat.card ↥(powMonoidHom ℓ : kˣ →* kˣ).ker := hmain
    _ ≤ ℓ := hkerle

/-! ## The local decomposition `Fˣ = ⟨π⟩ · 𝒪_Fˣ` -/

section Local

variable {K : Type} [Field K] [NumberField K]

/-- A uniformiser of the completion, i.e. an element of value `exp (-1)`, has infinite order in
`Fˣ`. -/
theorem orderOf_mk0_eq_zero
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {x : Q.adicCompletion K} (hxne : x ≠ 0)
    (hxval : Valued.v x = WithZero.exp (-1 : ℤ)) :
    orderOf (Units.mk0 x hxne) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn hpow
  have h1 : Valued.v ((Units.mk0 x hxne ^ n : (Q.adicCompletion K)ˣ) :
      Q.adicCompletion K) = 1 := by
    rw [hpow]
    exact map_one _
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hxval,
    ← WithZero.exp_nsmul] at h1
  have h2 : n • (-1 : ℤ) = 0 := WithZero.exp_eq_one.mp h1
  have h3 : (n : ℤ) = 0 := by simpa [zsmul_eq_mul] using h2
  omega

/-- For a uniformiser `x` of the completion, the units of the ring of integers and `⟨x⟩` generate
`Fˣ`: every unit of the completion is a power of `x` times a unit of `𝒪_F`. -/
theorem units_sup_zpowers_eq_top
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {x : Q.adicCompletion K} (hxne : x ≠ 0)
    (hxval : Valued.v x = WithZero.exp (-1 : ℤ)) :
    (Q.adicCompletionIntegers K).units ⊔ Subgroup.zpowers (Units.mk0 x hxne) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [Subgroup.mem_sup]
  have hyvne : Valued.v (y : Q.adicCompletion K) ≠ 0 := by
    intro h
    exact Units.ne_zero y ((Valuation.zero_iff Valued.v).mp h)
  set j : ℤ := (Valued.v (y : Q.adicCompletion K)).log with hj
  have hexp : WithZero.exp j = Valued.v (y : Q.adicCompletion K) := WithZero.exp_log hyvne
  refine ⟨y * (Units.mk0 x hxne) ^ j, ?_, (Units.mk0 x hxne) ^ (-j),
    Subgroup.mem_zpowers_iff.mpr ⟨-j, rfl⟩, ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, hxval,
      ← WithZero.exp_zsmul]
    rw [show j • (-1 : ℤ) = -j by simp, ← hexp]
    rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · group

/-- For a uniformiser `x` of the completion, the units of the ring of integers meet `⟨x⟩`
trivially. -/
theorem units_inf_zpowers_eq_bot
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {x : Q.adicCompletion K} (hxne : x ≠ 0)
    (hxval : Valued.v x = WithZero.exp (-1 : ℤ)) :
    (Q.adicCompletionIntegers K).units ⊓ Subgroup.zpowers (Units.mk0 x hxne) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_inf] at hy
  obtain ⟨hyV, hyA⟩ := hy
  rw [Subgroup.mem_zpowers_iff] at hyA
  obtain ⟨k, hk⟩ := hyA
  have h1 : Valued.v (y : Q.adicCompletion K) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mp hyV
  rw [← hk, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hxval,
    ← WithZero.exp_zsmul] at h1
  have h2 : k • (-1 : ℤ) = 0 := WithZero.exp_eq_one.mp h1
  have h3 : k = 0 := by simpa [zsmul_eq_mul] using h2
  rw [← hk, h3, zpow_zero]

/-- The `ℓ`-elementary quotient of `𝒪_Fˣ` has at most `ℓ` elements. -/
theorem units_quot_range_powMonoidHom_le
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hunit : IsUnit ((ℓ : ℕ) : Q.adicCompletionIntegers K)) :
    Nat.card (↥((Q.adicCompletionIntegers K).units) ⧸
        (powMonoidHom ℓ : ↥((Q.adicCompletionIntegers K).units) →*
          ↥((Q.adicCompletionIntegers K).units)).range) ≤ ℓ := by
  haveI : HenselianLocalRing (Q.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := NumberField.RingOfIntegers K) (K := K) Q
  haveI : Finite (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K Q
  rw [natCard_quot_range_powMonoidHom_mulEquiv
    (Submonoid.unitsEquivUnitsType (Q.adicCompletionIntegers K).toSubmonoid) ℓ]
  exact natCard_units_quot_range_powMonoidHom_le (R := Q.adicCompletionIntegers K) ℓ hℓ hunit

end Local

/-- **The `ℓ`-elementary quotient of `Fˣ` has order at most `ℓ²`** for `F = Q.adicCompletion K` and
a prime `ℓ` invertible in the ring of integers `𝒪_F` (i.e. `ℓ ≠ p`, the residue characteristic).

Concretely: the subgroup `(Fˣ)^ℓ = (powMonoidHom ℓ).range` of `ℓ`-th powers has index at most `ℓ²`
in `Fˣ`.  Ingredients: `Fˣ = ⟨π⟩ · U` with `⟨π⟩ ⊓ U = ⊥` (`NK.LocalReciprocityLubinTate.Units.
sup_zpowers_range`, `inf_zpowers_range`, `U = higherUnits F 0`), so `(Fˣ)^ℓ = ⟨π ^ ℓ⟩ · U ^ ℓ` and
`[Fˣ : (Fˣ)^ℓ] = ℓ · [U : U^ℓ]`; then `U¹ = higherUnits F 1 = 1+𝔪` is `ℓ`-divisible (Newton's method
`NK.LocalReciprocityLubinTate.Units.exists_pow_eq_of_mem_maximalIdeal_pow` plus Frobenius deepening
and Bézout), hence `U / U^ℓ` is a quotient of `U / (U¹ · μ_{q-1}^ℓ)` whose order is at most `ℓ`. -/
theorem index_range_powMonoidHom_le_sq
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hunit : IsUnit ((ℓ : ℕ) : Q.adicCompletionIntegers K)) :
    (((powMonoidHom ℓ : (Q.adicCompletion K)ˣ →* (Q.adicCompletion K)ˣ)).range).index ≤ ℓ ^ 2 := by
  classical
  obtain ⟨π, hπval, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one Q
  have hπne : (π : Q.adicCompletion K) ≠ 0 := by
    intro h
    have h' := hπval
    rw [h, map_zero] at h'
    exact WithZero.exp_ne_zero h'.symm
  rw [Subgroup.index_eq_card]
  have hinf : (Q.adicCompletionIntegers K).units ⊓
      Subgroup.zpowers (Units.mk0 (π : Q.adicCompletion K) hπne) = ⊥ :=
    units_inf_zpowers_eq_bot Q hπne hπval
  have hsup : (Q.adicCompletionIntegers K).units ⊔
      Subgroup.zpowers (Units.mk0 (π : Q.adicCompletion K) hπne) = ⊤ :=
    units_sup_zpowers_eq_top Q hπne hπval
  rw [natCard_quot_range_powMonoidHom_sup_inf _ _ hinf hsup ℓ]
  have hA : Nat.card (↥(Subgroup.zpowers (Units.mk0 (π : Q.adicCompletion K) hπne)) ⧸
      (powMonoidHom ℓ : ↥(Subgroup.zpowers (Units.mk0 (π : Q.adicCompletion K) hπne)) →*
        ↥(Subgroup.zpowers (Units.mk0 (π : Q.adicCompletion K) hπne))).range) = ℓ :=
    natCard_quot_range_powMonoidHom_zpowers_eq _ (orderOf_mk0_eq_zero Q hπne hπval) ℓ hℓ.one_le
  have hB : Nat.card (↥((Q.adicCompletionIntegers K).units) ⧸
      (powMonoidHom ℓ : ↥((Q.adicCompletionIntegers K).units) →*
        ↥((Q.adicCompletionIntegers K).units)).range) ≤ ℓ :=
    units_quot_range_powMonoidHom_le Q ℓ hℓ hunit
  calc Nat.card (↥((Q.adicCompletionIntegers K).units) ⧸
          (powMonoidHom ℓ : ↥((Q.adicCompletionIntegers K).units) →*
            ↥((Q.adicCompletionIntegers K).units)).range) *
        Nat.card (↥(Subgroup.zpowers (Units.mk0 (π : Q.adicCompletion K) hπne)) ⧸
          (powMonoidHom ℓ : ↥(Subgroup.zpowers (Units.mk0 (π : Q.adicCompletion K) hπne)) →*
            ↥(Subgroup.zpowers (Units.mk0 (π : Q.adicCompletion K) hπne))).range)
      = Nat.card (↥((Q.adicCompletionIntegers K).units) ⧸
          (powMonoidHom ℓ : ↥((Q.adicCompletionIntegers K).units) →*
            ↥((Q.adicCompletionIntegers K).units)).range) * ℓ := by rw [hA]
    _ ≤ ℓ * ℓ := Nat.mul_le_mul hB le_rfl
    _ = ℓ ^ 2 := by ring

end

end NK.NUV2.TamePrimeLevel
