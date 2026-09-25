import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.SquareRoot
import Submission.Work.ShafarevichKoch.FracIdealOfUnit
import Submission.Work.ShafarevichKoch.vClass_eq_one_iff
import Submission.Work.ShafarevichKoch.vClass_surjective_twoTorsion
import Submission.Work.ShafarevichKoch.vClass_mul
import Submission.Work.ShafarevichKoch.vClass_sq_eq_one
import Submission.Work.ShafarevichKoch.vClass_eq_mk
import Submission.Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le
import Submission.Work.QuadraticFields.RankTwo
import Submission.Work.QuadraticFields.sqClass_eq_zero_iff
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.unitTwoRank_eq_finrank_units_modSquares
import Submission.Work.ClassFieldTower.classGroupTwoRank_eq_finrank_modN
import Submission.Work.ClassFieldTower.card_quotient_squareSubgroup_eq_card_twoTorsion
import Submission.Work.ClassFieldTower.two_pow_classGroupTwoRank

/-!
# `Work.ShafarevichKoch.vTwo_rank_two_corrected`

**The Kummer two-descent dimension count.**

For a number field `F`, Koch's group
`V_∅ = VTwo F = {x ∈ Fˣ : (x) is a square fractional ideal}` fits into the exact sequence
`1 → O_F^×/(O_F^×)² → V_∅/Fˣ² → Cl(F)[2] → 1` (Koch, *Galois theory of `p`-extensions*, Ch. 11;
Hajir--Maire--Ramakrishna, arXiv:2103.09508 §1).  Hence

`dim_{F₂} (V_∅/Fˣ²) = d(O_F^×) + rank₂ Cl(F) = unitTwoRank F + classGroupTwoRank F`.

This file proves that statement in the form

`rankTwo (↥(VTwo F) ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) = unitTwoRank F + classGroupTwoRank F`

(the *corrected* form of `vTwo_rank_two`, which quotients `V_∅` by the squares of all of `Fˣ`; the
uncorrected form with `V_∅/V_∅²` is false, see `vTwo_rank_two_refutation.lean`).

## Structure of the proof

1. `vClassHom` is the Kummer two-descent `V_∅ → Cl(F)` as a monoid homomorphism.
2. `psi` is the induced map `V_∅/Fˣ² → Cl(F)`; it is *surjective onto* the `2`-torsion
   (`psi_range`, `vClassHom_range`) and its kernel is the image of `O_F^×`
   (`gHom_range`), with kernel of `gHom` exactly `(O_F^×)²` (`gHom_ker`, which uses that a unit of
   `F` that is a square is a square of a unit of `O_F`, i.e. that `O_F` is integrally closed in
   `F`).
3. Lagrange's theorem on `V_∅/Fˣ²` therefore gives `#(V_∅/Fˣ²) = 2^(unitTwoRank F) · 2^(classGroupTwoRank F)`.
4. The quotient `V_∅/Fˣ²` has exponent `2` (`quotient_exponent_two`), hence `V_∅/Fˣ² ≅ (V_∅/Fˣ²)²`
   and `rankTwo` of it is `log₂` of its cardinality, which finishes the count.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField
open Work.QuadraticFields

namespace Work.ShafarevichKoch

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-! ## 1. `vClass` as a monoid homomorphism -/

/-- The Kummer two-descent class of the trivial element is trivial. -/
lemma vClass_one : vClass F (1 : VTwo F) = 1 := by
  have h1 : (1 : IdealUnit F) * 1 = FracIdealOf F (((1 : VTwo F)) : Fˣ) := by
    rw [show (((1 : VTwo F)) : Fˣ) = 1 from Subgroup.coe_one _, FracIdealOf_one, mul_one]
  rw [vClass_eq_mk F (x := 1) (J := 1) h1]
  exact map_one (ClassGroup.mk F)

/-- **The Kummer two-descent `vClass` as a monoid homomorphism** `V_∅ →* Cl(F)`. -/
def vClassHom : VTwo F →* ClassGroup (𝓞 F) where
  toFun := vClass F
  map_one' := vClass_one F
  map_mul' := vClass_mul F

/-! ## 2. Squares and units lie in `V_∅` -/

/-- A square lies in Koch's group `V_∅`. -/
lemma sqMemVTwo (y : Fˣ) : y ^ 2 ∈ VTwo F :=
  ⟨FracIdealOf F y, by rw [pow_two, FracIdealOf_mul]⟩

/-- A unit of `𝓞 F` lies in Koch's group `V_∅`. -/
lemma unitEmbed_mem_VTwo (u : RingUnit F) : unitEmbed F u ∈ VTwo F :=
  ⟨1, by rw [fracIdealOf_unitEmbed F u, mul_one]⟩

/-- The Kummer two-descent of a square is trivial. -/
lemma vClass_sq (y : Fˣ) : vClass F ⟨y ^ 2, sqMemVTwo F y⟩ = 1 := by
  rw [vClass_eq_mk F (x := ⟨y ^ 2, sqMemVTwo F y⟩) (J := FracIdealOf F y)
    (by show FracIdealOf F y * FracIdealOf F y = FracIdealOf F (y ^ 2)
        rw [pow_two, FracIdealOf_mul]),
    classGroup_mk_fracIdealOf_eq_one F y]

/-- The squares of `Fˣ` lie in the kernel of the Kummer two-descent. -/
lemma squares_le_ker : (squareSubgroup Fˣ).subgroupOf (VTwo F) ≤ (vClassHom F).ker := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨y, hy⟩ := mem_squareSubgroup_iff.mp hx
  have hx_eq : x = ⟨y ^ 2, sqMemVTwo F y⟩ := Subtype.ext hy.symm
  rw [MonoidHom.mem_ker, hx_eq]
  show vClass F ⟨y ^ 2, sqMemVTwo F y⟩ = 1
  exact vClass_sq F y

/-! ## 3. The induced map `V_∅/Fˣ² → Cl(F)` -/

/-- **The Kummer two-descent, induced on `V_∅/Fˣ²`.** -/
def psi : (VTwo F ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) →* ClassGroup (𝓞 F) :=
  QuotientGroup.lift _ (vClassHom F) (squares_le_ker F)

lemma psi_mk (x : VTwo F) :
    psi F (QuotientGroup.mk' _ x) = vClass F x :=
  QuotientGroup.lift_mk' ((squareSubgroup Fˣ).subgroupOf (VTwo F)) (squares_le_ker F) x

/-- **`psi` is surjective onto the `2`-torsion of the class group**: its range is the range of
`vClass`, which is exactly the `2`-torsion (`vClassHom_range`). -/
lemma psi_range : (psi F).range = (vClassHom F).range := by
  ext c
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    exact ⟨x, by rw [psi_mk]; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨QuotientGroup.mk' _ x, by rw [psi_mk]; rfl⟩

/-- **The range of the Kummer two-descent is the `2`-torsion of the class group.** -/
lemma vClassHom_range :
    (vClassHom F).range = (powMonoidHom 2 : ClassGroup (𝓞 F) →* ClassGroup (𝓞 F)).ker := by
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact vClass_sq_eq_one F x
  · intro hc
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hc
    obtain ⟨x, hx⟩ := vClass_surjective_twoTorsion F c hc
    exact ⟨x, hx⟩

/-- **The units of `𝓞 F` as a homomorphism into `V_∅/Fˣ²`.** -/
def gHom : RingUnit F →* (VTwo F ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) :=
  (QuotientGroup.mk' _).comp
    { toFun := fun u => (⟨unitEmbed F u, unitEmbed_mem_VTwo F u⟩ : VTwo F)
      map_one' := rfl
      map_mul' := fun a b => rfl }

lemma gHom_apply (u : RingUnit F) :
    gHom F u = QuotientGroup.mk' _ (⟨unitEmbed F u, unitEmbed_mem_VTwo F u⟩ : VTwo F) := rfl

/-- **The range of `gHom` is the kernel of `psi`**: an element of `V_∅` has trivial descent class
exactly when its class modulo `Fˣ²` comes from a unit of `𝓞 F`. -/
lemma gHom_range : (gHom F).range = (psi F).ker := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    rw [MonoidHom.mem_ker, gHom_apply, psi_mk]
    show vClass F ⟨unitEmbed F u, unitEmbed_mem_VTwo F u⟩ = 1
    rw [vClass_eq_one_iff]
    exact ⟨u, 1, by rw [one_pow, mul_one]⟩
  · intro hz
    rw [MonoidHom.mem_ker] at hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hx : vClass F x = 1 := by
      have := hz
      rw [psi_mk] at this
      exact this
    obtain ⟨u, y, hy⟩ := (vClass_eq_one_iff F x).mp hx
    have hxeq : x = (⟨unitEmbed F u, unitEmbed_mem_VTwo F u⟩ : VTwo F) * ⟨y ^ 2, sqMemVTwo F y⟩ := by
      apply Subtype.ext
      show (x : Fˣ) = unitEmbed F u * y ^ 2
      exact hy
    refine ⟨u, ?_⟩
    change QuotientGroup.mk' ((squareSubgroup Fˣ).subgroupOf (VTwo F))
        (⟨unitEmbed F u, unitEmbed_mem_VTwo F u⟩ : VTwo F) = QuotientGroup.mk' _ x
    simp only [QuotientGroup.mk'_apply]
    rw [eq_comm, QuotientGroup.eq]
    have hkey : x⁻¹ * (⟨unitEmbed F u, unitEmbed_mem_VTwo F u⟩ : VTwo F)
        = (⟨y ^ 2, sqMemVTwo F y⟩ : VTwo F)⁻¹ := by
      rw [hxeq]
      group
    rw [hkey]
    exact Subgroup.inv_mem _
      ((Subgroup.mem_subgroupOf).mpr (mem_squareSubgroup_iff.mpr ⟨y, rfl⟩))

/-- **The kernel of `gHom` is `(O_F^×)²`.**  If `u ∈ O_F^×` and `unitEmbed u = y²` for some
`y ∈ Fˣ`, then `y` is integral over `𝓞 F` (it is a root of `T² - unitEmbed u`), hence a unit of
`𝓞 F` (its inverse in `F` is `y · (unitEmbed u)⁻¹ ∈ 𝓞 F`), and `u = y²` in `𝓞 F`. -/
lemma gHom_ker : (gHom F).ker = squareSubgroup (RingUnit F) := by
  ext u
  rw [MonoidHom.mem_ker, mem_squareSubgroup_iff]
  constructor
  · intro hu
    have hmem : (⟨unitEmbed F u, unitEmbed_mem_VTwo F u⟩ : VTwo F)
        ∈ (squareSubgroup Fˣ).subgroupOf (VTwo F) := by
      have h2 : (↑(⟨unitEmbed F u, unitEmbed_mem_VTwo F u⟩ : VTwo F)
          : (VTwo F ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) = 1 := hu
      exact (QuotientGroup.eq_one_iff _).mp h2
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨y, hy⟩ := mem_squareSubgroup_iff.mp hmem
    -- `hy : y ^ 2 = unitEmbed F u`
    have hyF : (y : F) * (y : F) = ((unitEmbed F u : Fˣ) : F) := by
      have h := congrArg (fun z : Fˣ => (z : F)) hy
      simpa [pow_two] using h
    -- `y` is integral over `ℤ`
    have hint : IsIntegral ℤ (y : F) := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      have hui : IsIntegral ℤ (((unitEmbed F u : Fˣ) : F)) := by
        rw [unitEmbed_coe]
        exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 F) (R := ℤ) (B := F)).mpr
          ⟨(u : 𝓞 F), rfl⟩
      rwa [show (y : F) ^ 2 = ((unitEmbed F u : Fˣ) : F) from by rw [pow_two]; exact hyF]
    obtain ⟨w, hw⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F) (R := ℤ) (B := F)).mp hint
    -- `hw : algebraMap (𝓞 F) F w = y`
    have hww : w * w = (u : 𝓞 F) := by
      apply IsIntegralClosure.algebraMap_injective (𝓞 F) ℤ F
      calc algebraMap (𝓞 F) F (w * w) = algebraMap (𝓞 F) F w * algebraMap (𝓞 F) F w :=
            map_mul _ _ _
        _ = (y : F) * (y : F) := by rw [hw]
        _ = ((unitEmbed F u : Fˣ) : F) := hyF
        _ = algebraMap (𝓞 F) F (u : 𝓞 F) := unitEmbed_coe F u
    -- `w` is a unit of `𝓞 F`, with inverse `w * (u⁻¹)`
    have hinv : w * (w * ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) = 1 := by
      rw [← mul_assoc, hww]
      show (u : 𝓞 F) * ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) = 1
      rw [Units.mul_inv]
    let v : RingUnit F := Units.mkOfMulEqOne w (w * ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) hinv
    refine ⟨v, ?_⟩
    apply Units.ext
    show ((v ^ 2 : RingUnit F) : 𝓞 F) = (u : 𝓞 F)
    rw [Units.val_pow_eq_pow_val, Units.val_mkOfMulEqOne, pow_two, hww]
  · rintro ⟨b, rfl⟩
    rw [gHom_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine mem_squareSubgroup_iff.mpr ⟨unitEmbed F b, ?_⟩
    show (unitEmbed F b) ^ 2 = ↑(⟨unitEmbed F (b ^ 2), unitEmbed_mem_VTwo F (b ^ 2)⟩ : VTwo F)
    show (unitEmbed F b) ^ 2 = unitEmbed F (b ^ 2)
    rw [pow_two, pow_two, unitEmbed_mul]

/-! ## 4. The cardinality of `V_∅/Fˣ²` -/

lemma card_ker_psi : Nat.card ↥((psi F).ker) = 2 ^ Work.ClassFieldTower.unitTwoRank F := by
  calc Nat.card ↥((psi F).ker) = Nat.card ↥((gHom F).range) := by rw [gHom_range F]
    _ = Nat.card (RingUnit F ⧸ (gHom F).ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange (gHom F)).toEquiv).symm
    _ = Nat.card (RingUnit F ⧸ squareSubgroup (RingUnit F)) := by rw [gHom_ker F]
    _ = Nat.card (ModN (Additive (RingUnit F)) 2) :=
        (Work.ClassFieldTower.natCard_modN_two_eq_natCard_sqQuotient (RingUnit F)).symm
    _ = 2 ^ Work.ClassFieldTower.unitTwoRank F := cuql_card_units F

lemma card_range_psi : Nat.card ↥((psi F).range)
    = 2 ^ Work.ClassFieldTower.classGroupTwoRank F := by
  calc Nat.card ↥((psi F).range) = Nat.card ↥((vClassHom F).range) := by rw [psi_range F]
    _ = Nat.card ↥((powMonoidHom 2 : ClassGroup (𝓞 F) →* ClassGroup (𝓞 F)).ker) := by
        rw [vClassHom_range F]
    _ = Nat.card {c : ClassGroup (𝓞 F) // c ^ 2 = 1} :=
        Nat.card_congr (Equiv.subtypeEquivRight
          (fun c => by rw [MonoidHom.mem_ker, powMonoidHom_apply]))
    _ = 2 ^ Work.ClassFieldTower.classGroupTwoRank F := cuql_card_classGroup_twoTorsion F

/-- **The cardinality of `V_∅/Fˣ²` is `2^(unitTwoRank F + classGroupTwoRank F)`.** -/
lemma card_quotient_VTwo :
    Nat.card (VTwo F ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))
      = 2 ^ (Work.ClassFieldTower.unitTwoRank F
          + Work.ClassFieldTower.classGroupTwoRank F) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((psi F).ker),
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (psi F)).toEquiv,
    card_range_psi F, card_ker_psi F, mul_comm, ← pow_add]

/-- **The quotient `V_∅/Fˣ²` has exponent `2`.** -/
lemma quotient_exponent_two (z : VTwo F ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) :
    z ^ 2 = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  rw [← map_pow]
  refine (QuotientGroup.eq_one_iff _).mpr ?_
  rw [Subgroup.mem_subgroupOf]
  exact mem_squareSubgroup_iff.mpr ⟨(x : Fˣ), rfl⟩

/-- The square subgroup of an exponent-`2` group is trivial. -/
lemma squareSubgroup_eq_bot_of_sq_eq_one {A : Type*} [CommGroup A]
    (h : ∀ a : A, a ^ 2 = 1) : squareSubgroup A = ⊥ := by
  rw [Work.QuadraticFields.squareSubgroup, Subgroup.closure_eq_bot_iff]
  rintro y ⟨a, rfl⟩
  simpa using h a

/-! ## 5. The dimension count -/


end

theorem vTwo_rank_two_corrected (F : Type*) [Field F] [NumberField F] :
    Work.QuadraticFields.rankTwo (↥(Work.ShafarevichKoch.VTwo F) ⧸
        (Work.QuadraticFields.squareSubgroup Fˣ).subgroupOf (Work.ShafarevichKoch.VTwo F))
      = Work.ClassFieldTower.unitTwoRank F + Work.ClassFieldTower.classGroupTwoRank F := by
  have hcard := card_quotient_VTwo F
  have hne : Nat.card (↥(VTwo F) ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) ≠ 0 := by
    rw [hcard]; positivity
  haveI : Finite (↥(VTwo F) ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) :=
    (Nat.card_ne_zero.mp hne).2
  haveI : Finite (ModN (Additive (↥(VTwo F)
      ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) 2) :=
    Finite.of_surjective (ModN.mkQ (G := Additive (↥(VTwo F)
      ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) 2) (Submodule.mkQ_surjective _)
  haveI : Module.Finite (ZMod 2) (ModN (Additive (↥(VTwo F)
      ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) 2) := Module.Finite.of_finite
  have hmodN : Nat.card (ModN (Additive (↥(VTwo F)
        ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) 2)
      = Nat.card (↥(VTwo F) ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) := by
    rw [Work.ClassFieldTower.natCard_modN_two_eq_natCard_sqQuotient,
      show Subgroup.closure (Set.range fun x : (↥(VTwo F)
          ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) => x ^ 2)
        = squareSubgroup (↥(VTwo F) ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) from rfl,
      squareSubgroup_eq_bot_of_sq_eq_one (A := ↥(VTwo F) ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F)) (quotient_exponent_two F)]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  have hOne : Nat.card (ModN (Additive (↥(VTwo F)
        ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) 2)
      = 2 ^ Module.finrank (ZMod 2) (ModN (Additive (↥(VTwo F)
        ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) 2) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  change Module.finrank (ZMod 2) (ModN (Additive (↥(VTwo F)
      ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) 2)
      = Work.ClassFieldTower.unitTwoRank F + Work.ClassFieldTower.classGroupTwoRank F
  refine Nat.pow_right_injective (a := 2) (by norm_num) ?_
  show 2 ^ Module.finrank (ZMod 2) (ModN (Additive (↥(VTwo F)
      ⧸ (squareSubgroup Fˣ).subgroupOf (VTwo F))) 2)
    = 2 ^ (Work.ClassFieldTower.unitTwoRank F + Work.ClassFieldTower.classGroupTwoRank F)
  rw [← hOne, hmodN, hcard]

end Work.ShafarevichKoch
