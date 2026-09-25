/-
Auxiliary development for `NK.Mine.hasZl2Quotient_completionUnits_iff`.

For `κ = K_𝔭`, the `𝔭`-adic completion of a number field `K`, this file develops

* the decomposition of `κˣ` into the unit part in `𝒪_κˣ` and the valuation exponent,
* the homomorphism `κˣ →* Ẑ × (residue field)ˣ` with kernel the principal units `U¹ = 1+𝔪`.
-/
import Mathlib
import Submission.NK.LocalInputs.PowerQuotient.LamIndex
import Submission.NK.LocalInputs.CommGroupRank.numIndexSubgroups_profiniteCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
import Submission.Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalReciprocity.Invariants
import Submission.NK.Mine.pu_pow_surjective
import Submission.NK.Mine.zmodQuotient_of_card_quot_pow
import Submission.NK.Mine.exists_surjective_hom_of_subgroup_index_mul
import Submission.NK.Mine.index_powSub_cpl_eq
import Submission.NK.LocalInputs.PowerQuotient.natCard_pu_quot_pow

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero IsMulCommutative

namespace NK.Mine

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- Abbreviation: the ring of integers of the completion. -/
abbrev RO (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Type _ :=
  𝔭.adicCompletionIntegers K

/-- The zpow-valuation rule for the `𝔭`-adic valuation. -/
lemma map_zpow_val (x : 𝔭.adicCompletion K) (k : ℤ) :
    Valued.v (x ^ k) = Valued.v x ^ k := map_zpow₀ (Valued.v) x k

/-- The valuation exponent of a unit of `κ = K_𝔭`: the integer `n` with `v x = exp n`. -/
noncomputable def valExp (x : (𝔭.adicCompletion K)ˣ) : ℤ :=
  (Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K) x).toAdd

lemma valExp_eq_log (x : (𝔭.adicCompletion K)ˣ) :
    valExp 𝔭 x = (Valued.v (x : 𝔭.adicCompletion K)).log := by
  rw [valExp, Commons.NumberTheory.NumberField.Completion.unitsValLog_apply]
  rfl

lemma valExp_ofAdd (x : (𝔭.adicCompletion K)ˣ) :
    Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K) x
      = Multiplicative.ofAdd (valExp 𝔭 x) := rfl

lemma valExp_ne_zero (x : (𝔭.adicCompletion K)ˣ) :
    Valued.v (x : 𝔭.adicCompletion K) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (Units.ne_zero x)

lemma val_eq_exp_valExp (x : (𝔭.adicCompletion K)ˣ) :
    Valued.v (x : 𝔭.adicCompletion K) = WithZero.exp (valExp 𝔭 x) := by
  rw [valExp_eq_log]; exact (WithZero.exp_log (valExp_ne_zero 𝔭 x)).symm

lemma valExp_mul (x y : (𝔭.adicCompletion K)ˣ) :
    valExp 𝔭 (x * y) = valExp 𝔭 x + valExp 𝔭 y := by
  rw [valExp_eq_log, valExp_eq_log, valExp_eq_log, Units.val_mul, Valuation.map_mul,
    WithZero.log_mul (valExp_ne_zero 𝔭 x) (valExp_ne_zero 𝔭 y)]

lemma valExp_one : valExp 𝔭 (1 : (𝔭.adicCompletion K)ˣ) = 0 := by
  rw [valExp_eq_log, Units.val_one, map_one, WithZero.log_one]

lemma valExp_zpow (x : (𝔭.adicCompletion K)ˣ) (k : ℤ) :
    valExp 𝔭 (x ^ k) = k * valExp 𝔭 x := by
  have h : (Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K) (x ^ k))
      = (Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K) x) ^ k :=
    map_zpow _ x k
  have h2 : ((Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K) x) ^ k).toAdd
      = k • (Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K) x).toAdd := by
    have h3 : Multiplicative.ofAdd (((Commons.NumberTheory.NumberField.Completion.unitsValLog
        (𝔭.adicCompletion K) x) ^ k).toAdd)
        = Multiplicative.ofAdd (k • (Commons.NumberTheory.NumberField.Completion.unitsValLog
            (𝔭.adicCompletion K) x).toAdd) := by
      rw [ofAdd_toAdd, ofAdd_zsmul, ofAdd_toAdd]
    exact Multiplicative.ofAdd.injective h3
  unfold valExp
  rw [h, h2, zsmul_eq_mul, Int.cast_id]

lemma valExp_eq_neg_one (π : (𝔭.adicCompletion K)ˣ)
    (hπ : Valued.v (π : 𝔭.adicCompletion K) = WithZero.exp (-1)) : valExp 𝔭 π = -1 := by
  rw [valExp_eq_log, hπ, WithZero.log_exp]

/-- **The unit part** of a unit of `κ = K_𝔭`. -/
noncomputable def unitPart (π : (𝔭.adicCompletion K)ˣ) (x : (𝔭.adicCompletion K)ˣ) :
    (𝔭.adicCompletion K)ˣ :=
  x * π ^ (valExp 𝔭 x)

lemma unitPart_mul (π : (𝔭.adicCompletion K)ˣ) (x y : (𝔭.adicCompletion K)ˣ) :
    unitPart 𝔭 π (x * y) = unitPart 𝔭 π x * unitPart 𝔭 π y := by
  unfold unitPart
  rw [valExp_mul, zpow_add, mul_mul_mul_comm]

lemma valExp_unitPart (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (x : (𝔭.adicCompletion K)ˣ) : valExp 𝔭 (unitPart 𝔭 π x) = 0 := by
  rw [unitPart, valExp_mul, valExp_zpow, hπ]
  ring

lemma unitPart_zpow (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) (k : ℤ) :
    unitPart 𝔭 π (π ^ k) = 1 := by
  unfold unitPart
  rw [valExp_zpow, hπ, ← zpow_add]
  have : k + k * (-1) = 0 := by ring
  rw [this, zpow_zero]

lemma val_unitPart (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (x : (𝔭.adicCompletion K)ˣ) :
    Valued.v ((unitPart 𝔭 π x : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) = 1 := by
  have hval : Valued.v (π : 𝔭.adicCompletion K) = WithZero.exp (-1) := by
    rw [val_eq_exp_valExp (𝔭 := 𝔭) π, hπ]
  have hmap : Valued.v ((x * π ^ (valExp 𝔭 x) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K)
      = Valued.v (x : 𝔭.adicCompletion K) *
        Valued.v ((π ^ (valExp 𝔭 x) : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) := by
    rw [Units.val_mul, Valuation.map_mul]
  rw [unitPart, hmap, Units.val_zpow_eq_zpow_val, map_zpow_val (𝔭 := 𝔭),
    val_eq_exp_valExp, hval, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  have : valExp 𝔭 x + valExp 𝔭 x • (-1 : ℤ) = 0 := by
    rw [zsmul_eq_mul, Int.cast_id]; ring
  rw [this, WithZero.exp_zero]

lemma mem_unitPart_unitGroup (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (x : (𝔭.adicCompletion K)ˣ) :
    unitPart 𝔭 π x ∈ (𝔭.adicCompletionIntegers K).unitGroup := by
  rw [show (𝔭.adicCompletionIntegers K)
      = (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ))).valuationSubring
        from rfl, Valuation.mem_unitGroup_iff]
  exact val_unitPart 𝔭 π hπ x

/-- **The unit-part homomorphism** `κˣ →* 𝒪_κˣ`. -/
noncomputable def unitPartHom (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) :
    (𝔭.adicCompletion K)ˣ →* (𝔭.adicCompletionIntegers K)ˣ :=
  (ValuationSubring.unitGroupMulEquiv (𝔭.adicCompletionIntegers K)).toMonoidHom.comp
    { toFun := fun x => ⟨unitPart 𝔭 π x, mem_unitPart_unitGroup 𝔭 π hπ x⟩
      map_one' := by
        refine Subtype.ext ?_
        show unitPart 𝔭 π 1 = 1
        unfold unitPart
        rw [valExp_one, zpow_zero, mul_one]
      map_mul' := fun x y => Subtype.ext (unitPart_mul 𝔭 π x y) }

lemma unitPartHom_apply (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (x : (𝔭.adicCompletion K)ˣ) :
    ((unitPartHom 𝔭 π hπ x : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)
      = unitPart 𝔭 π x :=
  ValuationSubring.coe_unitGroupMulEquiv_apply _ _

/-- The inclusion `𝒪_κˣ →* κˣ`. -/
noncomputable def unitsCoeHom : (𝔭.adicCompletionIntegers K)ˣ →* (𝔭.adicCompletion K)ˣ :=
  Units.map (ValuationSubring.subtype (𝔭.adicCompletionIntegers K)).toMonoidHom

/-- The units of `𝒪_κ` regarded as units of `κ`. -/
noncomputable abbrev unitsCoe (u : (𝔭.adicCompletionIntegers K)ˣ) : (𝔭.adicCompletion K)ˣ :=
  unitsCoeHom 𝔭 u

lemma unitsCoe_val (u : (𝔭.adicCompletionIntegers K)ˣ) :
    ((unitsCoe 𝔭 u : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K)
      = (u : 𝔭.adicCompletionIntegers K) := by
  show ((Units.map (ValuationSubring.subtype (𝔭.adicCompletionIntegers K)).toMonoidHom u :
    (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) = (u : 𝔭.adicCompletionIntegers K)
  rw [Units.coe_map]
  rfl

lemma unitsCoe_unitPartHom (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (x : (𝔭.adicCompletion K)ˣ) :
    unitsCoe 𝔭 (unitPartHom 𝔭 π hπ x) = unitPart 𝔭 π x := by
  apply Units.ext
  rw [unitsCoe_val, unitPartHom_apply]

lemma unitsCoe_injective : Function.Injective (unitsCoe 𝔭) := by
  intro u v h
  have h2 : ((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)
      = ((v : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) := by
    have h3 := congrArg (fun w : (𝔭.adicCompletion K)ˣ => (w : 𝔭.adicCompletion K)) h
    rwa [unitsCoe_val, unitsCoe_val] at h3
  exact Units.ext (Subtype.ext h2)

lemma unitsCoe_mem_unitGroup (u : (𝔭.adicCompletionIntegers K)ˣ) :
    unitsCoe 𝔭 u ∈ (Valued.v : Valuation (𝔭.adicCompletion K)
      (WithZero (Multiplicative ℤ))).valuationSubring.unitGroup := by
  have hcoe : unitsCoe 𝔭 u
      = ((ValuationSubring.unitGroupMulEquiv (𝔭.adicCompletionIntegers K)).symm u :
          (𝔭.adicCompletion K)ˣ) := by
    apply Units.ext
    rw [unitsCoe_val, ValuationSubring.coe_unitGroupMulEquiv_symm_apply]
  rw [hcoe]
  exact (ValuationSubring.unitGroupMulEquiv (𝔭.adicCompletionIntegers K)).symm u |>.2

lemma val_unitsCoe (u : (𝔭.adicCompletionIntegers K)ˣ) :
    Valued.v ((unitsCoe 𝔭 u : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) = 1 := by
  have h := (ValuationSubring.mem_unitGroup_iff (𝔭.adicCompletionIntegers K)
    (unitsCoe 𝔭 u)).mp (unitsCoe_mem_unitGroup 𝔭 u)
  exact (Valuation.IsEquiv.eq_one_iff_eq_one
    (Valuation.isEquiv_valuation_valuationSubring (Valued.v))).mpr h

lemma valExp_unitsCoe (u : (𝔭.adicCompletionIntegers K)ˣ) : valExp 𝔭 (unitsCoe 𝔭 u) = 0 := by
  have hne : Valued.v ((unitsCoe 𝔭 u : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) ≠ 0 :=
    valExp_ne_zero 𝔭 (unitsCoe 𝔭 u)
  have hlog : (Valued.v ((unitsCoe 𝔭 u : (𝔭.adicCompletion K)ˣ) :
      𝔭.adicCompletion K)).log = 0 := by
    rw [val_unitsCoe 𝔭 u, WithZero.log_one]
  rw [valExp_eq_log, hlog]

lemma unitPart_unitsCoe (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (u : (𝔭.adicCompletionIntegers K)ˣ) : unitPart 𝔭 π (unitsCoe 𝔭 u) = unitsCoe 𝔭 u := by
  unfold unitPart
  rw [valExp_unitsCoe, zpow_zero, mul_one]

lemma unitPartHom_apply_unitsCoe (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (u : (𝔭.adicCompletionIntegers K)ˣ) :
    unitPartHom 𝔭 π hπ (unitsCoe 𝔭 u) = u := by
  apply unitsCoe_injective
  rw [unitsCoe_unitPartHom 𝔭 π hπ, unitPart_unitsCoe 𝔭 π hπ]

lemma unitPartHom_surjective (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) :
    Function.Surjective (unitPartHom 𝔭 π hπ) :=
  fun u => ⟨unitsCoe 𝔭 u, unitPartHom_apply_unitsCoe 𝔭 π hπ u⟩

/-- The principal units of `κ` regarded as a subgroup of `κˣ`. -/
noncomputable def puInK : Subgroup (𝔭.adicCompletion K)ˣ :=
  (NK.LocalInputs.PowerQuotient.pu 𝔭 1).map (unitsCoeHom 𝔭)

lemma mem_puInK (x : (𝔭.adicCompletion K)ˣ) :
    x ∈ puInK 𝔭 ↔ ∃ u ∈ NK.LocalInputs.PowerQuotient.pu 𝔭 1, unitsCoe 𝔭 u = x :=
  Subgroup.mem_map

/-- The residue-field-units part of the decomposition of `κˣ`. -/
noncomputable def residuePart (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) :
    (𝔭.adicCompletion K)ˣ →* (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ :=
  (Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom).comp
    (unitPartHom 𝔭 π hπ)

/-- **The decomposition homomorphism** `κˣ →* ℤ × (residue field)ˣ`, whose kernel is `U¹`. -/
noncomputable def PsiHom (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) :
    (𝔭.adicCompletion K)ˣ →*
      (Multiplicative ℤ × (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ) :=
  (Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K)).prod
    (residuePart 𝔭 π hπ)

lemma PsiHom_apply (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (x : (𝔭.adicCompletion K)ˣ) :
    PsiHom 𝔭 π hπ x
      = (Multiplicative.ofAdd (valExp 𝔭 x),
          Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom
            (unitPartHom 𝔭 π hπ x)) := rfl

lemma unitPartHom_zpow (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) (k : ℤ) :
    unitPartHom 𝔭 π hπ (π ^ k) = 1 := by
  apply unitsCoe_injective
  have h1 : unitsCoe 𝔭 (1 : (𝔭.adicCompletionIntegers K)ˣ) = 1 := map_one (unitsCoeHom 𝔭)
  rw [h1, unitsCoe_unitPartHom 𝔭 π hπ, unitPart_zpow 𝔭 π hπ k]

lemma unitPart_unitsCoe_mul (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1)
    (u : (𝔭.adicCompletionIntegers K)ˣ) (k : ℤ) :
    unitPart 𝔭 π (unitsCoe 𝔭 u * π ^ k) = unitsCoe 𝔭 u := by
  unfold unitPart
  rw [valExp_mul, valExp_unitsCoe, valExp_zpow, hπ, zero_add]
  rw [show k * (-1) = -k by ring, mul_assoc, ← zpow_add]
  rw [show k + -k = 0 by ring, zpow_zero, mul_one]

lemma PsiHom_surjective (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) :
    Function.Surjective (PsiHom 𝔭 π hπ) := by
  intro y
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Multiplicative.ofAdd k = y.1 :=
    ⟨y.1.toAdd, (ofAdd_toAdd y.1).symm⟩
  obtain ⟨u, hu⟩ := Commons.NumberTheory.NumberField.Completion.surjective_units_residue_adicCompletion
    (K := K) 𝔭 y.2
  refine ⟨unitsCoe 𝔭 u * π ^ (-k), ?_⟩
  rw [PsiHom_apply, Prod.mk.injEq]
  constructor
  · rw [valExp_mul, valExp_unitsCoe, zero_add, valExp_zpow, hπ]
    rw [show (-k) * (-1) = k by ring, hk]
  · show Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom
        (unitPartHom 𝔭 π hπ (unitsCoe 𝔭 u * π ^ (-k))) = y.2
    rw [map_mul, unitPartHom_apply_unitsCoe, unitPartHom_zpow, mul_one]
    exact hu

/-- The `ker` of the decomposition homomorphism is the group of principal units. -/
lemma ker_PsiHom (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) :
    (PsiHom 𝔭 π hπ).ker = puInK 𝔭 := by
  have hpu : NK.LocalInputs.PowerQuotient.pu 𝔭 1
      = (Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom).ker := by
    rw [NK.LocalInputs.PowerQuotient.pu_one]
    rfl
  have hpu' : ∀ u : (𝔭.adicCompletionIntegers K)ˣ,
      u ∈ NK.LocalInputs.PowerQuotient.pu 𝔭 1 ↔
        Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom u = 1 := by
    intro u
    rw [hpu, MonoidHom.mem_ker]
  ext x
  rw [MonoidHom.mem_ker, mem_puInK]
  constructor
  · intro hx
    have h1 : valExp 𝔭 x = 0 := by
      have h := congrArg Prod.fst hx
      rw [PsiHom_apply] at h
      exact ofAdd_eq_one.mp (by simpa using h)
    have h2 : Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom
        (unitPartHom 𝔭 π hπ x) = 1 := by
      have h := congrArg Prod.snd hx
      rw [PsiHom_apply] at h
      simpa using h
    exact ⟨unitPartHom 𝔭 π hπ x, (hpu' _).mpr h2, by
      rw [unitsCoe_unitPartHom 𝔭 π hπ, unitPart, h1, zpow_zero, mul_one]⟩
  · rintro ⟨u, hu, rfl⟩
    rw [PsiHom_apply, Prod.mk.injEq]
    exact ⟨by rw [valExp_unitsCoe]; rfl,
      by rw [unitPartHom_apply_unitsCoe]; exact (hpu' u).mp hu⟩



/-! ## Surjections onto `Multiplicative (ZMod (p ^ n))` -/

section Surjections

variable {p : ℕ}

lemma localDegree_pos : 0 < NK.LocalInputs.localDegree K 𝔭 := by
  rw [NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg]
  exact Nat.mul_pos (Ideal.ramificationIdx_pos 𝔭.asIdeal ℤ) (Ideal.inertiaDeg_pos 𝔭.asIdeal ℤ)

/-- **`U¹` has a surjection onto the cyclic group `ZMod (p ^ n)`.** -/
theorem exists_surjective_pu (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) (n : ℕ) :
    ∃ f : ↥(NK.LocalInputs.PowerQuotient.pu 𝔭 1) →* Multiplicative (ZMod (p ^ n)),
      Function.Surjective f := by
  obtain ⟨M, hM, ⟨D⟩⟩ := NK.LocalInputs.PowerQuotient.exists_logData 𝔭
  have hcard : Nat.card (Multiplicative ↥(NK.LocalInputs.PowerQuotient.Lam D hp hchar) ⧸
      Subgroup.closure (Set.range fun y :
        Multiplicative ↥(NK.LocalInputs.PowerQuotient.Lam D hp hchar) => y ^ p))
      = p ^ NK.LocalInputs.localDegree K 𝔭 := by
    rw [NK.Mine.closure_range_pow_eq_powMonoidHom_range]
    exact NK.LocalInputs.PowerQuotient.natCard_Lam_quot_pow D hp hchar
  obtain ⟨f, hf⟩ := NK.Mine.zmodQuotient_of_card_quot_pow
    (A := Multiplicative ↥(NK.LocalInputs.PowerQuotient.Lam D hp hchar)) hp
    (NK.LocalInputs.PowerQuotient.lamFunHom_pow_eq_one D hp hchar) hcard
    (localDegree_pos 𝔭) n
  exact ⟨f.comp (NK.LocalInputs.PowerQuotient.lamFunHom D hp hchar),
    hf.comp (NK.LocalInputs.PowerQuotient.lamFunHom_surjective D hp hchar)⟩

lemma natCard_residueField_eq_pow (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      = p ^ 𝔭.asIdeal.inertiaDeg ℤ :=
  NK.LocalInputs.PowerQuotient.natCard_residueField_eq_pow (𝔭 := 𝔭) hp hchar

/-- **`𝒪_κˣ` has a surjection onto `ZMod (p ^ n)`.** -/
theorem exists_surjective_adicUnits (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) (n : ℕ) :
    ∃ f : (𝔭.adicCompletionIntegers K)ˣ →* Multiplicative (ZMod (p ^ n)),
      Function.Surjective f := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_pu 𝔭 hp hchar n
  haveI hfin : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  haveI hne : Nonempty (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := ⟨0⟩
  set q : ℕ := Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) with hqdef
  have hq : q = p ^ 𝔭.asIdeal.inertiaDeg ℤ := natCard_residueField_eq_pow 𝔭 hp hchar
  have hqpos : 0 < q := Nat.card_pos
  have hpdvd : p ∣ q := by
    rw [hq]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp (Ideal.inertiaDeg_pos 𝔭.asIdeal ℤ))
  have hcop : (q - 1).Coprime (p ^ n) :=
    ((Nat.coprime_self_sub_left (by omega : 1 ≤ q)).mpr (Nat.coprime_one_left q)).coprime_dvd_right
      hpdvd |>.pow_right n
  have hpu : NK.LocalInputs.PowerQuotient.pu 𝔭 1
      = (Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom).ker := by
    rw [NK.LocalInputs.PowerQuotient.pu_one]
    rfl
  have hU : ∀ a : (𝔭.adicCompletionIntegers K)ˣ,
      a ^ (q - 1) ∈ NK.LocalInputs.PowerQuotient.pu 𝔭 1 := by
    intro a
    rw [hpu, MonoidHom.mem_ker, map_pow]
    have hcard : Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ = q - 1 :=
      Nat.card_units _
    rw [← hcard]
    exact pow_card_eq_one'
  have hH : ∀ y : Multiplicative (ZMod (p ^ n)), y ^ (p ^ n) = 1 := by
    intro y
    rw [← ofAdd_toAdd y, ← ofAdd_nsmul]
    have : (p ^ n) • y.toAdd = 0 := by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [this, ofAdd_zero]
  obtain ⟨e, he⟩ : ∃ e : ℕ, (q - 1) * e ≡ 1 [MOD p ^ n] := by
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
    have hunit : IsUnit ((q - 1 : ℕ) : ZMod (p ^ n)) :=
      (ZMod.isUnit_iff_coprime (q - 1) (p ^ n)).mpr hcop
    obtain ⟨v, hv⟩ := hunit
    refine ⟨(((v⁻¹ : (ZMod (p ^ n))ˣ)) : ZMod (p ^ n)).val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff ((q - 1) * _) 1 (p ^ n)]
    rw [Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val, ← hv]
    exact Units.mul_inv v
  obtain ⟨f, hf⟩ := NK.Mine.exists_surjective_hom_of_subgroup_index_mul
    (NK.LocalInputs.PowerQuotient.pu 𝔭 1) hU hH he ψ hψ
  exact ⟨f, hf⟩

/-- The valuation of `κˣ`, reduced modulo `p ^ n`. -/
noncomputable def valExpHom (p n : ℕ) :
    (𝔭.adicCompletion K)ˣ →* Multiplicative (ZMod (p ^ n)) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd ((valExp 𝔭 x : ℤ) : ZMod (p ^ n))) (by
    intro x y
    rw [valExp_mul, Int.cast_add, ofAdd_add])

lemma valExpHom_apply (p n : ℕ) (x : (𝔭.adicCompletion K)ˣ) :
    valExpHom 𝔭 p n x = Multiplicative.ofAdd ((valExp 𝔭 x : ℤ) : ZMod (p ^ n)) := rfl

lemma valExpHom_zpow (p n : ℕ) (π : (𝔭.adicCompletion K)ˣ) (k : ℤ) :
    valExpHom 𝔭 p n (π ^ k)
      = Multiplicative.ofAdd (((k * valExp 𝔭 π : ℤ)) : ZMod (p ^ n)) := by
  rw [valExpHom_apply, valExp_zpow]

lemma valExpHom_surjective (p n : ℕ) (π : (𝔭.adicCompletion K)ˣ) (hπ : valExp 𝔭 π = -1) :
    Function.Surjective (valExpHom 𝔭 p n) := by
  intro c
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective c.toAdd
  refine ⟨π ^ (-m), ?_⟩
  rw [valExpHom_zpow, hπ, show (-m) * (-1) = m by ring, hm, ofAdd_toAdd]

/-- The uniformizer of `𝒪_κ`, as a unit of `κ`. -/
noncomputable def uni : (𝔭.adicCompletion K)ˣ :=
  Units.mk0 ((Commons.RingTheory.Henselian.uniformizer
      (R := NumberField.RingOfIntegers K) (K := K) 𝔭 : 𝔭.adicCompletionIntegers K) :
        𝔭.adicCompletion K) (by
    intro h0
    have h := Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) 𝔭
    rw [h0, map_zero] at h
    exact WithZero.exp_ne_zero h.symm)

lemma valExp_uni : valExp 𝔭 (uni 𝔭) = -1 :=
  valExp_eq_neg_one 𝔭 (uni 𝔭)
    (Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) 𝔭)

/-- **`κˣ` has a surjection onto `(ZMod (p ^ n))²`.** -/
theorem exists_surjective_units_sq (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) (n : ℕ) :
    ∃ f : (𝔭.adicCompletion K)ˣ →*
        (Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))),
      Function.Surjective f := by
  obtain ⟨φ, hφ⟩ := exists_surjective_adicUnits 𝔭 hp hchar n
  refine ⟨(valExpHom 𝔭 p n).prod (φ.comp (unitPartHom 𝔭 (uni 𝔭) (valExp_uni 𝔭))), ?_⟩
  rintro ⟨a, b⟩
  obtain ⟨u, hu⟩ := hφ b
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (a * (valExpHom 𝔭 p n (unitsCoe 𝔭 u))⁻¹).toAdd
  refine ⟨unitsCoe 𝔭 u * uni 𝔭 ^ (-m), Prod.ext ?_ ?_⟩
  · change valExpHom 𝔭 p n (unitsCoe 𝔭 u * uni 𝔭 ^ (-m)) = a
    rw [map_mul]
    have hsecond : valExpHom 𝔭 p n (uni 𝔭 ^ (-m))
        = a * (valExpHom 𝔭 p n (unitsCoe 𝔭 u))⁻¹ := by
      rw [valExpHom_zpow, valExp_uni 𝔭, show (-m) * (-1) = m by ring]
      exact (congrArg Multiplicative.ofAdd hm).trans (ofAdd_toAdd _)
    rw [hsecond]
    generalize valExpHom 𝔭 p n (unitsCoe 𝔭 u) = X
    rw [← mul_assoc, mul_comm X a, mul_assoc, mul_inv_cancel, mul_one]
  · change φ (unitPartHom 𝔭 (uni 𝔭) (valExp_uni 𝔭) (unitsCoe 𝔭 u * uni 𝔭 ^ (-m))) = b
    rw [map_mul, unitPartHom_apply_unitsCoe, unitPartHom_zpow 𝔭 (uni 𝔭) (valExp_uni 𝔭), mul_one, hu]

/-- **`completionUnits κ` has a surjection onto `(ZMod (p ^ n))²`.**

This is the lift of the surjection of `κˣ` to the profinite completion, via the universal
property of the completion. -/
theorem exists_surjective_completionUnits (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) (n : ℕ) :
    ∃ f : NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K) →*
        (Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))),
      Function.Surjective f := by
  obtain ⟨q, hq⟩ := exists_surjective_units_sq 𝔭 hp hchar n
  haveI hne : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  let E : Type u := ULift.{u, 0} (Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n)))
  let q' : (𝔭.adicCompletion K)ˣ →* E :=
    (MulEquiv.ulift.symm : (Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))) ≃* E
      ).toMonoidHom.comp q
  let P : ProfiniteGrp := ProfiniteGrp.ofFiniteGrp (FiniteGrp.of E)
  let Φ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of ((𝔭.adicCompletion K)ˣ)) ⟶ P :=
    ProfiniteGrp.ProfiniteCompletion.lift (P := P)
      (GrpCat.ofHom (q' : (𝔭.adicCompletion K)ˣ →* ↑P.toProfinite.toTop))
  let F' : NK.LocalReciprocity.completionUnits (𝔭.adicCompletion K) →* E := Φ.hom.toMonoidHom
  have hF' : F'.comp (NK.LocalInputs.CommGroupRank.cplEta ((𝔭.adicCompletion K)ˣ)) = q' := by
    refine MonoidHom.ext (fun a => ?_)
    exact CategoryTheory.ConcreteCategory.congr_hom (ProfiniteGrp.ProfiniteCompletion.lift_eta
      (P := P) (f := GrpCat.ofHom (q' : (𝔭.adicCompletion K)ˣ →* ↑P.toProfinite.toTop))) a
  refine ⟨(MulEquiv.ulift : E ≃* (Multiplicative (ZMod (p ^ n)) ×
    Multiplicative (ZMod (p ^ n)))).toMonoidHom.comp F', ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hq y
  refine ⟨NK.LocalInputs.CommGroupRank.cplEta ((𝔭.adicCompletion K)ˣ) x, ?_⟩
  show (MulEquiv.ulift : E ≃* _) (F' (NK.LocalInputs.CommGroupRank.cplEta _ x)) = y
  rw [show F' (NK.LocalInputs.CommGroupRank.cplEta ((𝔭.adicCompletion K)ˣ) x) = q' x from
    congrArg (fun g : (𝔭.adicCompletion K)ˣ →* E => g x) hF']
  have hq'x : q' x = ULift.up (q x) := rfl
  rw [hq'x]
  exact hx

end Surjections





end

end NK.Mine
