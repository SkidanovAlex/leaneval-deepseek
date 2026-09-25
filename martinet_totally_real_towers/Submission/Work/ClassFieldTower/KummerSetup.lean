import Mathlib
import Submission.Work.ClassFieldTower.TwoDescentDefs
import Submission.Work.ClassFieldTower.degreeTwo_sqrt_gen
import Submission.Work.ClassFieldTower.rootsOfUnity_two_equiv_zmod_two
import Submission.Work.ClassFieldTower.hom_units_factor_two

/-!
# The Kummer pairing for exponent-`2` Galois extensions

For a finite Galois extension `L / K` (with `(2 : K) ≠ 0`) whose Galois group has exponent `2`
(i.e. `σ ^ 2 = 1` for all `σ`), we set up the Kummer pairing

`Gal(L/K) × W → μ₂ ⊆ Lˣ`,  `(σ, a) ↦ σ(√a)/√a`,

where `W = kummerSquareRoots K L ≤ Kˣ` is the subgroup of elements of `Kˣ` having a square root in
`L`, packaged as the subgroup `U = kummerU K L ≤ Kˣ/(Kˣ)²` of Kummer classes.

The main results of this file are

* `Work.ClassFieldTower.mem_kummerU_iff` -- the characterisation of `U` (so `U` is the subgroup
  required by the statement of `Work.ClassFieldTower.kummer_expTwo_iso`);
* `Work.ClassFieldTower.kummerThetaHom_ker` -- the kernel of the pairing is `(Kˣ)²`;
* `Work.ClassFieldTower.kummerThetaHom_surjective` -- the pairing realises every character
  `Gal(L/K) →* μ₂` (via the quadratic subextension `L ^ ker χ / K`).

Together these give `U ≃* (Gal(L/K) →* μ₂)`, which is the content of Kummer theory used in
`Work.ClassFieldTower.kummer_expTwo_iso`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped Classical IsMulCommutative

noncomputable section

namespace Work.ClassFieldTower

section Basic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The subgroup of `Kˣ` of elements having a square root in `L`. -/
def kummerSquareRoots (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Subgroup Kˣ where
  carrier := {a | ∃ b : L, b * b = algebraMap K L (a : K)}
  mul_mem' := by
    rintro a a' ⟨b, hb⟩ ⟨c, hc⟩
    refine ⟨b * c, ?_⟩
    rw [show (((a * a' : Kˣ)) : K) = (a : K) * (a' : K) from by simp, map_mul]
    calc (b * c) * (b * c) = (b * b) * (c * c) := by ring
      _ = algebraMap K L (a : K) * algebraMap K L (a' : K) := by rw [hb, hc]
  one_mem' := by
    refine ⟨1, ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      intro h
      have h1 : algebraMap K L (a : K) = 0 := by rw [← hb, h, mul_zero]
      exact Units.ne_zero a (FaithfulSMul.algebraMap_injective K L (by rw [h1, map_zero]))
    refine ⟨b⁻¹, ?_⟩
    rw [← mul_inv_rev, hb]
    simp [map_inv₀]

@[simp]
lemma mem_kummerSquareRoots {a : Kˣ} :
    a ∈ kummerSquareRoots K L ↔ ∃ b : L, b * b = algebraMap K L (a : K) := Iff.rfl

lemma mem_Sq_iff {a : Kˣ} : a ∈ Sq K ↔ ∃ c : Kˣ, c ^ 2 = a := by
  rw [Sq, Subgroup.mem_map]
  constructor
  · rintro ⟨c, -, hc⟩
    exact ⟨c, by simpa using hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, trivial, rfl⟩

lemma sq_le_kummerSquareRoots : Sq K ≤ kummerSquareRoots K L := by
  intro a ha
  rw [mem_Sq_iff] at ha
  obtain ⟨c, rfl⟩ := ha
  refine ⟨algebraMap K L (c : K), ?_⟩
  have h : ((c ^ 2 : Kˣ) : K) = (c : K) * (c : K) := by rw [pow_two, Units.val_mul]
  rw [h, ← map_mul]

/-- The Kummer subgroup `U ≤ Kˣ/(Kˣ)²`. -/
def kummerU (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Subgroup (Kˣ ⧸ Sq K) :=
  (kummerSquareRoots K L).map (QuotientGroup.mk' (Sq K))

lemma mem_kummerU_iff {a : Kˣ} :
    QuotientGroup.mk' (Sq K) a ∈ kummerU K L ↔
      ∃ b : L, b * b = algebraMap K L (a : K) := by
  rw [kummerU, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hw'⟩
    have hmem : w⁻¹ * a ∈ Sq K := by
      have h1 : QuotientGroup.mk' (Sq K) (w⁻¹ * a) = 1 := by
        rw [map_mul, map_inv, hw', inv_mul_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : w⁻¹ * a ∈ kummerSquareRoots K L := sq_le_kummerSquareRoots hmem
    have h3 : a = w * (w⁻¹ * a) := by group
    rw [h3]
    exact mul_mem hw h2
  · intro ha
    exact ⟨a, ha, rfl⟩

/-! ### The Kummer pairing -/

/-- A choice of square root of an element of `kummerSquareRoots K L`. -/
def kummerRoot (a : ↥(kummerSquareRoots K L)) : L := Classical.choose a.2

lemma kummerRoot_mul_self (a : ↥(kummerSquareRoots K L)) :
    kummerRoot a * kummerRoot a = algebraMap K L ((a : Kˣ) : K) := Classical.choose_spec a.2

lemma kummerRoot_ne_zero (a : ↥(kummerSquareRoots K L)) : kummerRoot a ≠ 0 := by
  intro h
  have h1 : algebraMap K L ((a : Kˣ) : K) = 0 := by rw [← kummerRoot_mul_self a, h, mul_zero]
  exact Units.ne_zero (a : Kˣ) (FaithfulSMul.algebraMap_injective K L (by rw [h1, map_zero]))

lemma eq_or_eq_neg_of_mul_self_eq {b c : L} (h : b * b = c * c) : b = c ∨ b = -c := by
  have hfac : (b - c) * (b + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left; exact sub_eq_zero.mp h1
  · right; exact add_eq_zero_iff_eq_neg.mp h1

lemma ratio_eq_ratio (σ : L ≃ₐ[K] L) {b c : L} (h : b * b = c * c) : σ b / b = σ c / c := by
  rcases eq_or_eq_neg_of_mul_self_eq h with h1 | h1
  · rw [h1]
  · rw [h1, map_neg, neg_div_neg_eq]

/-- The Kummer ratio `σ(√a)/√a ∈ L`. -/
def kummerRatio (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) : L :=
  σ (kummerRoot a) / kummerRoot a

lemma kummerRatio_any (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) {b : L}
    (hb : b * b = algebraMap K L ((a : Kˣ) : K)) : σ b / b = kummerRatio σ a :=
  ratio_eq_ratio σ (hb.trans (kummerRoot_mul_self a).symm)

lemma sqrt_sq_eq_sqrt_sq (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) :
    σ (kummerRoot a) * σ (kummerRoot a) = kummerRoot a * kummerRoot a := by
  rw [← map_mul, kummerRoot_mul_self, AlgEquiv.commutes]

lemma kummerRatio_sq (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) :
    kummerRatio σ a * kummerRatio σ a = 1 := by
  have hr : kummerRoot a ≠ 0 := kummerRoot_ne_zero a
  show σ (kummerRoot a) / kummerRoot a * (σ (kummerRoot a) / kummerRoot a) = 1
  rw [div_mul_div_comm, sqrt_sq_eq_sqrt_sq]
  exact div_self (mul_ne_zero hr hr)

lemma kummerRatio_ne_zero (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) :
    kummerRatio σ a ≠ 0 := by
  intro h
  have h1 := kummerRatio_sq σ a
  rw [h, mul_zero] at h1
  exact one_ne_zero h1.symm

lemma kummerRatio_one (a : ↥(kummerSquareRoots K L)) :
    kummerRatio (1 : L ≃ₐ[K] L) a = 1 := by
  rw [kummerRatio, AlgEquiv.one_apply, div_self (kummerRoot_ne_zero a)]

lemma kummerRatio_one_arg (σ : L ≃ₐ[K] L) : kummerRatio σ (1 : ↥(kummerSquareRoots K L)) = 1 := by
  have h := kummerRatio_any σ (1 : ↥(kummerSquareRoots K L)) (b := 1) (by simp)
  rw [← h]
  simp

/-- The Kummer symbol `σ ↦ σ(√a)/√a` as an element of `μ₂ = {±1}`. -/
def kummerSymbol (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) : rootsOfUnity 2 L :=
  ⟨Units.mk0 (kummerRatio σ a) (kummerRatio_ne_zero σ a), by
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0, pow_two]
    exact kummerRatio_sq σ a⟩

lemma coe_kummerSymbol (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) :
    (((kummerSymbol σ a : rootsOfUnity 2 L) : Lˣ) : L) = kummerRatio σ a := rfl

lemma kummerSymbol_eq_one_iff (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) :
    kummerSymbol σ a = 1 ↔ kummerRatio σ a = 1 := by
  rw [Subtype.ext_iff, Units.ext_iff, Subgroup.coe_one, Units.val_one, coe_kummerSymbol]

lemma kummerSymbol_mul_left (σ τ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) :
    kummerSymbol (σ * τ) a = kummerSymbol σ a * kummerSymbol τ a := by
  rw [Subtype.ext_iff, Units.ext_iff, Subgroup.coe_mul, Units.val_mul, coe_kummerSymbol,
    coe_kummerSymbol, coe_kummerSymbol]
  have hroot : (τ (kummerRoot a)) * (τ (kummerRoot a)) = algebraMap K L ((a : Kˣ) : K) := by
    rw [← map_mul, kummerRoot_mul_self, AlgEquiv.commutes]
  have h1 : σ (τ (kummerRoot a)) / (τ (kummerRoot a)) = kummerRatio σ a :=
    kummerRatio_any σ a hroot
  have h2 : τ (kummerRoot a) / kummerRoot a = kummerRatio τ a := rfl
  have hne : τ (kummerRoot a) ≠ 0 := fun h =>
    kummerRoot_ne_zero a (τ.injective (by rw [h, map_zero]))
  rw [kummerRatio, AlgEquiv.mul_apply, ← h1, ← h2, div_mul_div_comm,
    mul_comm (σ (τ (kummerRoot a)))]
  exact (mul_div_mul_left (σ (τ (kummerRoot a))) (kummerRoot a) hne).symm

lemma kummerSymbol_mul_right (σ : L ≃ₐ[K] L) (a a' : ↥(kummerSquareRoots K L)) :
    kummerSymbol σ (a * a') = kummerSymbol σ a * kummerSymbol σ a' := by
  rw [Subtype.ext_iff, Units.ext_iff, Subgroup.coe_mul, Units.val_mul, coe_kummerSymbol,
    coe_kummerSymbol, coe_kummerSymbol]
  have hroot : (kummerRoot a * kummerRoot a') * (kummerRoot a * kummerRoot a')
      = algebraMap K L (((a * a' : ↥(kummerSquareRoots K L)) : Kˣ) : K) := by
    rw [show (((a * a' : ↥(kummerSquareRoots K L)) : Kˣ) : K)
        = ((a : Kˣ) : K) * ((a' : Kˣ) : K) from by rw [Subgroup.coe_mul, Units.val_mul],
      map_mul]
    rw [← kummerRoot_mul_self a, ← kummerRoot_mul_self a']
    ring
  rw [← kummerRatio_any σ (a * a') hroot, map_mul, mul_div_mul_comm]
  rfl

/-- The Kummer character attached to `a ∈ W`. -/
def kummerThetaFun (a : ↥(kummerSquareRoots K L)) : (L ≃ₐ[K] L) →* rootsOfUnity 2 L where
  toFun := fun σ => kummerSymbol σ a
  map_one' := by
    rw [Subtype.ext_iff, Units.ext_iff, Subgroup.coe_one, Units.val_one, coe_kummerSymbol]
    exact kummerRatio_one a
  map_mul' := fun σ τ => kummerSymbol_mul_left σ τ a

/-- The Kummer pairing as a monoid homomorphism `W →* Hom(G, μ₂)`. -/
def kummerThetaHom : ↥(kummerSquareRoots K L) →* ((L ≃ₐ[K] L) →* rootsOfUnity 2 L) where
  toFun := kummerThetaFun
  map_one' := MonoidHom.ext (fun σ => by
    rw [MonoidHom.one_apply, Subtype.ext_iff, Units.ext_iff, Subgroup.coe_one, Units.val_one]
    exact kummerRatio_one_arg σ)
  map_mul' := fun a a' => MonoidHom.ext (fun σ => kummerSymbol_mul_right σ a a')

/-! ### The nontrivial element of `μ₂` -/

/-- The element `-1` of `μ₂`. -/
def negOne (L : Type*) [Field L] : rootsOfUnity 2 L :=
  ⟨-1, by
    rw [mem_rootsOfUnity, pow_two]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one]
    ring⟩

@[simp]
lemma coe_negOne (L : Type*) [Field L] :
    (((negOne L : rootsOfUnity 2 L) : Lˣ) : L) = -1 := rfl

lemma kummerSymbol_eq_negOne_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (a : ↥(kummerSquareRoots K L)) :
    kummerSymbol σ a = negOne L ↔ kummerRatio σ a = -1 := by
  constructor
  · intro h
    rw [← coe_kummerSymbol, h]
    rfl
  · intro h
    rw [Subtype.ext_iff, Units.ext_iff, coe_kummerSymbol, h]
    rfl


end Basic

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-! ### The kernel of the Kummer pairing -/

lemma kummerThetaHom_ker :
    (kummerThetaHom (K := K) (L := L)).ker =
      (Sq K).subgroupOf (kummerSquareRoots K L) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Sq_iff]
  constructor
  · intro h
    have hratio : ∀ σ : L ≃ₐ[K] L, kummerRatio σ a = 1 := fun σ => by
      have h1 : kummerSymbol σ a = 1 := by
        have := congrArg (fun f : (L ≃ₐ[K] L) →* rootsOfUnity 2 L => f σ) h
        simpa [kummerThetaHom, kummerThetaFun] using this
      exact (kummerSymbol_eq_one_iff σ a).mp h1
    have hfix : ∀ σ : L ≃ₐ[K] L, σ (kummerRoot a) = kummerRoot a := fun σ => by
      have h2 := hratio σ
      rw [kummerRatio] at h2
      exact (div_eq_one_iff_eq (kummerRoot_ne_zero a)).mp h2
    have hmem : kummerRoot a ∈ (⊥ : IntermediateField K L) :=
      (IsGalois.mem_bot_iff_fixed (F := K) (E := L) (kummerRoot a)).mpr hfix
    rw [IntermediateField.mem_bot] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc0 : c ≠ 0 := fun h0 => kummerRoot_ne_zero a (by rw [← hc, h0, map_zero])
    refine ⟨Units.mk0 c hc0, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two]
    apply FaithfulSMul.algebraMap_injective K L
    rw [map_mul, hc]
    exact kummerRoot_mul_self a
  · rintro ⟨c, hc⟩
    have hmem : c ^ 2 ∈ kummerSquareRoots K L :=
      sq_le_kummerSquareRoots (mem_Sq_iff.mpr ⟨c, rfl⟩)
    have ha : a = (⟨c ^ 2, hmem⟩ : ↥(kummerSquareRoots K L)) := Subtype.ext hc.symm
    rw [ha]
    refine MonoidHom.ext (fun σ => ?_)
    rw [MonoidHom.one_apply]
    show kummerSymbol σ (⟨c ^ 2, hmem⟩ : ↥(kummerSquareRoots K L)) = 1
    rw [kummerSymbol_eq_one_iff]
    have hbc : (algebraMap K L (c : K)) * (algebraMap K L (c : K))
        = algebraMap K L (((⟨c ^ 2, hmem⟩ : ↥(kummerSquareRoots K L)) : Kˣ) : K) := by
      have h1 : (((⟨c ^ 2, hmem⟩ : ↥(kummerSquareRoots K L)) : Kˣ) : K)
          = (c : K) * (c : K) := by
        rw [show (((⟨c ^ 2, hmem⟩ : ↥(kummerSquareRoots K L)) : Kˣ) : K) = ((c ^ 2 : Kˣ) : K)
          from rfl, pow_two, Units.val_mul]
      rw [h1, ← map_mul]
    rw [← kummerRatio_any σ (⟨c ^ 2, hmem⟩ : ↥(kummerSquareRoots K L)) hbc, AlgEquiv.commutes]
    exact div_self (fun h => Units.ne_zero c ((algebraMap K L).injective (by rw [h, map_zero])))

/-! ### Surjectivity of the Kummer pairing -/

section Surj

lemma two_ne_zero_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hchar : (2 : K) ≠ 0) : (2 : L) ≠ 0 := by
  have h : (2 : L) = algebraMap K L (2 : K) := (map_ofNat (algebraMap K L) 2).symm
  rw [h]
  exact fun h' => hchar ((algebraMap K L).injective (by rw [h', map_zero]))

lemma neg_one_ne_one_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hchar : (2 : K) ≠ 0) : (-1 : L) ≠ 1 := by
  intro h
  have hh : (2 : L) = 0 := by
    have h1 : (-1 : L) + 1 = 0 := by ring
    rw [h] at h1
    have h2 : (2 : L) = 1 + 1 := by ring
    rw [h2]
    exact h1
  exact two_ne_zero_algebraMap (K := K) hchar hh

lemma isPrimitiveRoot_neg_one_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hchar : (2 : K) ≠ 0) : IsPrimitiveRoot (-1 : L) 2 := by
  rw [IsPrimitiveRoot.iff (by norm_num : 0 < 2)]
  refine ⟨by ring, ?_⟩
  intro l hl hl2
  interval_cases l
  intro h
  rw [pow_one] at h
  exact neg_one_ne_one_algebraMap (K := K) hchar h

lemma eq_negOne_of_ne_one {L : Type*} [Field L] (hchar : (-1 : L) ≠ 1)
    {u : rootsOfUnity 2 L} (h : u ≠ 1) : u = negOne L := by
  have hu2 : (u : Lˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 (u : Lˣ)).mp u.2
  have hu2L : ((u : Lˣ) : L) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu2]
    rfl
  have hu1 : ((u : Lˣ) : L) ≠ 1 := fun h1 => h (by
    rw [Subtype.ext_iff, Units.ext_iff]
    exact h1)
  rcases sq_eq_one_iff.mp hu2L with h2 | h2
  · exact absurd h2 hu1
  · apply Subtype.ext
    apply Units.ext
    rw [h2, coe_negOne]

lemma eq_or_eq_neg_of_sq_eq_sq {b c : L} (h : b * b = c * c) : b = c ∨ b = -c :=
  eq_or_eq_neg_of_mul_self_eq h

lemma kummerThetaHom_surjective (hchar : (2 : K) ≠ 0) :
    Function.Surjective (kummerThetaHom (K := K) (L := L)) := by
  intro χ
  by_cases hχ : χ = 1
  · exact ⟨1, by rw [hχ, map_one]⟩
  · have hμcard : Nat.card (rootsOfUnity 2 L) = 2 := by
      obtain ⟨e⟩ := rootsOfUnity_two_equiv_zmod_two (R := L)
        (two_ne_zero_algebraMap (K := K) hchar)
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      simp
    have hindex : χ.ker.index = 2 := by
      rw [Subgroup.index_ker]
      have hdvd : Nat.card ↥χ.range ∣ 2 := by
        have h0 := Subgroup.card_subgroup_dvd_card χ.range
        rwa [hμcard] at h0
      have hne1 : Nat.card ↥χ.range ≠ 1 := by
        intro h1
        have hbot : χ.range = ⊥ := Subgroup.card_eq_one.mp h1
        refine hχ (MonoidHom.ext (fun σ => ?_))
        have hmem : χ σ ∈ (⊥ : Subgroup (rootsOfUnity 2 L)) :=
          hbot ▸ MonoidHom.mem_range.mpr ⟨σ, rfl⟩
        simpa using hmem
      have hpos : 0 < Nat.card ↥χ.range := Nat.card_pos
      have hle : Nat.card ↥χ.range ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    let M : IntermediateField K L := IntermediateField.fixedField χ.ker
    have hMfin : Module.finrank K ↥M = 2 := by
      have h := IntermediateField.finrank_eq_fixingSubgroup_index (F := K) L M
      rw [IntermediateField.fixingSubgroup_fixedField (F := K) (E := L) χ.ker] at h
      rw [h, hindex]
    obtain ⟨a, b, hbM, hbsq, hbgen⟩ :=
      degreeTwo_sqrt_gen (K := K) (L := L) hchar M hMfin
    have haW : a ∈ kummerSquareRoots K L := ⟨b, hbsq⟩
    have hb0 : b ≠ 0 := fun h0 => by
      apply Units.ne_zero a
      exact (algebraMap K L).injective (by rw [← hbsq, h0, mul_zero, map_zero])
    have hiff : ∀ σ : L ≃ₐ[K] L, σ b = b ↔ σ ∈ χ.ker := by
      intro σ
      constructor
      · intro hσb
        have hfix : ∀ x ∈ IntermediateField.adjoin K ({b} : Set L), σ x = x := by
          intro x hx
          induction hx using IntermediateField.adjoin_induction with
          | mem y hy =>
              rw [Set.mem_singleton_iff] at hy
              rw [hy]
              exact hσb
          | algebraMap y => exact AlgEquiv.commutes σ y
          | add y z hy hz ihy ihz => rw [map_add, ihy, ihz]
          | mul y z hy hz ihy ihz => rw [map_mul, ihy, ihz]
          | inv y hy ihy => rw [map_inv₀, ihy]
        have hmem : σ ∈ M.fixingSubgroup := by
          rw [IntermediateField.mem_fixingSubgroup_iff]
          intro x hx
          rw [← hbgen] at hx
          exact hfix x hx
        rwa [IntermediateField.fixingSubgroup_fixedField (F := K) (E := L) χ.ker] at hmem
      · intro hσ
        have hmem : σ ∈ M.fixingSubgroup := by
          rwa [IntermediateField.fixingSubgroup_fixedField (F := K) (E := L) χ.ker]
        rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
        exact hmem b hbM
    refine ⟨⟨a, haW⟩, ?_⟩
    refine MonoidHom.ext (fun σ => ?_)
    show kummerSymbol σ (⟨a, haW⟩ : ↥(kummerSquareRoots K L)) = χ σ
    by_cases hσ : σ ∈ χ.ker
    · have hb : σ b = b := (hiff σ).mpr hσ
      have hχσ : χ σ = 1 := MonoidHom.mem_ker.mp hσ
      rw [hχσ, kummerSymbol_eq_one_iff, ← kummerRatio_any σ (⟨a, haW⟩ : ↥(kummerSquareRoots K L)) hbsq,
        hb, div_self hb0]
    · have hb : σ b ≠ b := fun h => hσ ((hiff σ).mp h)
      have hne : χ σ ≠ 1 := fun h => hσ (MonoidHom.mem_ker.mpr h)
      have hχσ : χ σ = negOne L := by
        refine eq_negOne_of_ne_one (L := L) ?_ hne
        exact neg_one_ne_one_algebraMap (K := K) hchar
      have hσb : σ b = -b := by
        have hsq1 : σ (b * b) = algebraMap K L (a : K) := by
          rw [hbsq]
          exact AlgEquiv.commutes σ (a : K)
        have hsq' : σ b * σ b = b * b := by
          rw [← map_mul]
          exact hsq1.trans hbsq.symm
        rcases eq_or_eq_neg_of_sq_eq_sq hsq' with h | h
        · exact absurd h hb
        · exact h
      have hsymbol : kummerSymbol σ (⟨a, haW⟩ : ↥(kummerSquareRoots K L)) = negOne L := by
        rw [kummerSymbol_eq_negOne_iff,
          ← kummerRatio_any σ (⟨a, haW⟩ : ↥(kummerSquareRoots K L)) hbsq, hσb, neg_div,
          div_self hb0]
      rw [hχσ, hsymbol]

end Surj


end Galois
