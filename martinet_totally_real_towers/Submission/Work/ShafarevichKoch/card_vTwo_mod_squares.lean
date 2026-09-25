import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.FracIdealOfUnit
import Submission.Work.ShafarevichKoch.vClass_eq_mk
import Submission.Work.ShafarevichKoch.vClass_eq_one_iff
import Submission.Work.ShafarevichKoch.vClass_mul
import Submission.Work.ShafarevichKoch.vClass_sq_eq_one
import Submission.Work.ShafarevichKoch.vClass_surjective_twoTorsion
import Submission.Work.ShafarevichKoch.vTwo_rank_two_refutation
import Submission.Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le

/-!
# `Work.ShafarevichKoch.card_vTwo_mod_squares`

**The cardinality of Koch's Kummer radical modulo the squares of `Fˣ`.**

The exact sequence of Koch's Kummer two-descent (see `Defs.lean`)

`1 → 𝓞_Fˣ/(𝓞_Fˣ)² → V_∅/Fˣ² → Cl(F)[2] → 1`

computes the cardinality of `V_∅/(Fˣ)²`, where `V_∅ = VTwo F` is Koch's group of those
`x ∈ Fˣ` whose principal fractional ideal is a square.  Since `(Fˣ)² ≤ V_∅` (a square
generates a square ideal), the quotient `V_∅/(Fˣ)²` is

`VTwo F ⧸ (VTwo F).subtype ⁻¹' (Fˣ)²`,

the subgroup `(Fˣ)²` being the image of the squaring endomorphism of `Fˣ` (i.e.
`Subgroup.map (powMonoidHom 2) ⊤`).  The main theorem of this file is

`Nat.card (V_∅/(Fˣ)²) = 2 ^ (unitTwoRank F + classGroupTwoRank F)`,

i.e. `#(V_∅/Fˣ²) = 2 ^ (d₂(𝓞_Fˣ) + rank₂ Cl(F))`, which is the numerical form of the
exact sequence above.

## Proof

Let `φ : V_∅ →* Cl(F)` be the Kummer two-descent `x ↦ [√(x)]` (`vClass`).  Pick an
intermediate subgroup `(Fˣ)² ≤ ker φ ≤ V_∅` and use the index multiplicativity
`[V_∅ : (Fˣ)²] = [ker φ : (Fˣ)²] · [V_∅ : ker φ]` (`Subgroup.relIndex_mul_index`).

* `[V_∅ : ker φ] = #Cl(F)[2] = 2 ^ classGroupTwoRank F`: the first isomorphism theorem
  identifies `V_∅/ker φ` with the range of `φ`, which is exactly the `2`-torsion of the
  class group (`vClass_sq_eq_one`, `vClass_surjective_twoTorsion`).
* `[ker φ : (Fˣ)²] = #(𝓞_Fˣ/(𝓞_Fˣ)²) = 2 ^ unitTwoRank F`: the map
  `𝓞_Fˣ → ker φ/(Fˣ)²`, `u ↦ unitEmbed u`, has kernel `(𝓞_Fˣ)²` — here one uses that a
  unit of `𝓞 F` which is a square in `F` is the square of a unit of `𝓞 F`
  (`exists_unit_sq_of_unitEmbed_eq_sq`, from `IsIntegral.of_pow` and the integral
  closedness of `𝓞 F` in `F`) — and it is surjective because `ker φ` consists of the
  elements `u · y²` with `u` a unit (`vClass_eq_one_iff`).  The cardinality of the
  target is `2 ^ unitTwoRank F` by `two_pow_unitTwoRank_eq_card_units_sqQuotient`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **A unit of `𝓞 F` which is a square in `F` is the square of a unit of `𝓞 F`.**

If `unitEmbed F u = y ^ 2` for some `y : Fˣ`, then `y` is a root of the monic polynomial
`X ^ 2 - u` with coefficients in `𝓞 F`, hence integral over `ℤ`; as `y ^ 2 = u` is a unit,
so is `y`.  This is the statement that `(𝓞 F)ˣ ∩ (Fˣ)² = ((𝓞 F)ˣ)²`, needed to identify
the kernel of the Kummer two-descent with the square classes of units. -/
theorem exists_unit_sq_of_unitEmbed_eq_sq (F : Type*) [Field F] [NumberField F]
    (u : (𝓞 F)ˣ) (y : Fˣ) (h : unitEmbed F u = y ^ 2) :
    ∃ v : (𝓞 F)ˣ, u = v ^ 2 := by
  have hF : algebraMap (𝓞 F) F (u : 𝓞 F) = ((y : Fˣ) : F) ^ 2 := by
    have hc := congrArg (fun w : Fˣ => (w : F)) h
    simpa only [unitEmbed_coe, Units.val_pow_eq_pow_val] using hc
  have hint : IsIntegral ℤ ((y : Fˣ) : F) := by
    apply IsIntegral.of_pow (by norm_num : 0 < 2)
    rw [← hF]
    exact (IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 F) (B := F)).mpr ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := (IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 F) (B := F)).mp hint
  have hvv : v * v = (u : 𝓞 F) := by
    apply RingOfIntegers.coe_injective (K := F)
    rw [map_mul, hv, hF, pow_two]
  have huval : (u : 𝓞 F) * ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hunit : IsUnit v := by
    rw [isUnit_iff_dvd_one]
    refine ⟨v * ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F), ?_⟩
    rw [← mul_assoc, hvv, huval]
  refine ⟨IsUnit.unit hunit, ?_⟩
  ext
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_two, hvv]

/-- **`2 ^ unitTwoRank F = #(𝓞_Fˣ/(𝓞_Fˣ)²)`.**

`unitTwoRank F = NumberField.Units.rank F + 1` is the `𝔽₂`-dimension of the group of
units modulo squares, so `2` raised to it is the cardinality of that group: the torsion
subgroup contributes one dimension (`NumberField.Units.even_torsionOrder`) and the free
part of rank `r` contributes `2 ^ r` (`NumberField.Units.finrank_modTorsion`). -/
theorem two_pow_unitTwoRank_eq_card_units_sqQuotient (F : Type*) [Field F] [NumberField F] :
    2 ^ Work.ClassFieldTower.unitTwoRank F =
      Nat.card ((𝓞 F)ˣ ⧸ Subgroup.closure (Set.range (fun x : (𝓞 F)ˣ => x ^ 2))) := by
  haveI : Finite (CommGroup.torsion (𝓞 F)ˣ) :=
    (inferInstance : Finite (NumberField.Units.torsion F))
  haveI : IsCyclic (CommGroup.torsion (𝓞 F)ˣ) :=
    (inferInstance : IsCyclic (NumberField.Units.torsion F))
  have hEven : Even (Nat.card (CommGroup.torsion (𝓞 F)ˣ)) := by
    simpa only [NumberField.Units.torsionOrder, NumberField.Units.torsion] using
      NumberField.Units.even_torsionOrder F
  have hcard : Nat.card (ModN (Additive (𝓞 F)ˣ) 2) = 2 ^ Work.ClassFieldTower.unitTwoRank F := by
    rw [Work.ClassFieldTower.natCard_modN_additive_torsion_eq_two_mul (𝓞 F)ˣ hEven]
    rw [show Nat.card (ModN (Additive ((𝓞 F)ˣ ⧸ CommGroup.torsion (𝓞 F)ˣ)) 2)
          = 2 ^ NumberField.Units.rank F from by
      rw [show ModN (Additive ((𝓞 F)ˣ ⧸ CommGroup.torsion (𝓞 F)ˣ)) 2
            = ModN (Additive ((𝓞 F)ˣ ⧸ NumberField.Units.torsion F)) 2 from rfl]
      rw [ModN.natCard_eq, NumberField.Units.finrank_modTorsion]]
    rw [Work.ClassFieldTower.unitTwoRank, pow_succ, mul_comm]
  rw [← hcard, Work.ClassFieldTower.natCard_modN_two_eq_natCard_sqQuotient]

/-- **The cardinality of the Kummer radical modulo the squares of `Fˣ`.**

`#(V_∅/Fˣ²) = 2 ^ (d₂(𝓞_Fˣ) + rank₂ Cl(F))`, the numerical form of Koch's exact
sequence `1 → 𝓞_Fˣ/(𝓞_Fˣ)² → V_∅/Fˣ² → Cl(F)[2] → 1`. -/
theorem card_vTwo_mod_squares (F : Type*) [Field F] [NumberField F] :
    Nat.card (Work.ShafarevichKoch.VTwo F ⧸
      (Subgroup.map (powMonoidHom (2 : ℕ) : Fˣ →* Fˣ) ⊤).comap
        (Work.ShafarevichKoch.VTwo F).subtype)
      = 2 ^ (Work.ClassFieldTower.unitTwoRank F + Work.ClassFieldTower.classGroupTwoRank F) := by
  classical
  -- the subgroup of `VTwo F` cut out by the squares of `Fˣ`
  set K : Subgroup ↥(Work.ShafarevichKoch.VTwo F) :=
    (Subgroup.map (powMonoidHom (2 : ℕ) : Fˣ →* Fˣ) ⊤).comap
      (Work.ShafarevichKoch.VTwo F).subtype with hK
  -- membership in `K`
  have memK_iff : ∀ x : ↥(Work.ShafarevichKoch.VTwo F),
      x ∈ K ↔ ∃ y : Fˣ, (x : Fˣ) = y ^ 2 := by
    intro x
    rw [hK, Subgroup.mem_comap, Subgroup.map_top, MonoidHom.mem_range]
    simp only [Subgroup.coe_subtype, powMonoidHom_apply]
    exact exists_congr (fun _ => eq_comm)
  -- the Kummer two-descent, as a group homomorphism
  have hvClass_one : vClass F (1 : ↥(VTwo F)) = 1 := by
    rw [vClass_eq_mk F (x := 1) (J := 1) (by simp [FracIdealOf_one])]
    exact map_one (ClassGroup.mk F :
      (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ →* ClassGroup (𝓞 F))
  let φ : ↥(VTwo F) →* ClassGroup (𝓞 F) :=
    { toFun := fun x => vClass F x
      map_one' := hvClass_one
      map_mul' := fun x y => vClass_mul F x y }
  -- the squares lie in the kernel of the descent
  have hKle : K ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change vClass F x = 1
    obtain ⟨y, hy⟩ := (memK_iff x).mp hx
    exact (vClass_eq_one_iff F x).mpr
      ⟨1, y, by rw [unitEmbed_one, one_mul]; exact hy⟩
  -- the units of `𝓞 F` as elements of `V_∅`
  have hmemU : ∀ u : (𝓞 F)ˣ, unitEmbed F u ∈ VTwo F :=
    fun u => ⟨1, by rw [fracIdealOf_unitEmbed, mul_one]⟩
  have hkerU : ∀ u : (𝓞 F)ˣ, φ ⟨unitEmbed F u, hmemU u⟩ = 1 := by
    intro u
    change vClass F ⟨unitEmbed F u, hmemU u⟩ = 1
    rw [vClass_eq_mk F (x := ⟨unitEmbed F u, hmemU u⟩) (J := 1)
      (by rw [mul_one, fracIdealOf_unitEmbed])]
    exact map_one (ClassGroup.mk F :
      (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ →* ClassGroup (𝓞 F))
  let Φ : (𝓞 F)ˣ →* ↥φ.ker :=
    { toFun := fun u => ⟨⟨unitEmbed F u, hmemU u⟩, hkerU u⟩
      map_one' := by ext <;> rfl
      map_mul' := by intro a b; ext <;> rfl }
  let Ψ : (𝓞 F)ˣ →* (↥φ.ker ⧸ K.subgroupOf φ.ker) :=
    (QuotientGroup.mk' (K.subgroupOf φ.ker)).comp Φ
  -- the kernel of `Ψ` is the square subgroup of the units
  have hkerPsi : Ψ.ker = Subgroup.closure (Set.range (fun x : (𝓞 F)ˣ => x ^ 2)) := by
    ext u
    rw [MonoidHom.mem_ker]
    dsimp only [Ψ, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change ((Φ u : ↥φ.ker) : ↥(VTwo F)) ∈ K ↔
      u ∈ Subgroup.closure (Set.range (fun x : (𝓞 F)ˣ => x ^ 2))
    rw [memK_iff]
    change (∃ y : Fˣ, unitEmbed F u = y ^ 2) ↔
      u ∈ Subgroup.closure (Set.range (fun x : (𝓞 F)ˣ => x ^ 2))
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨v, hv⟩ := exists_unit_sq_of_unitEmbed_eq_sq F u y hy
      rw [Work.ClassFieldTower.sqSubgroup_eq_range, MonoidHom.mem_range]
      exact ⟨v, by rw [powMonoidHom_apply]; exact hv.symm⟩
    · intro hu
      rw [Work.ClassFieldTower.sqSubgroup_eq_range, MonoidHom.mem_range] at hu
      obtain ⟨v, hv⟩ := hu
      rw [powMonoidHom_apply] at hv
      refine ⟨unitEmbed F v, ?_⟩
      rw [← hv]
      simp [pow_two]
  -- `Ψ` is surjective: the kernel of the descent consists of `unit · square`
  have hsurj : Function.Surjective Ψ := by
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf φ.ker) z
    obtain ⟨u, y, hy⟩ := (vClass_eq_one_iff F (w : ↥(VTwo F))).mp w.2
    refine ⟨u, ?_⟩
    dsimp only [Ψ, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine (memK_iff _).mpr ⟨y, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    change (unitEmbed F u)⁻¹ * ((w : ↥(VTwo F)) : Fˣ) = y ^ 2
    rw [hy]
    group
  -- `[ker φ : (Fˣ)²] = 2 ^ unitTwoRank F`
  have hcardD : Nat.card (↥φ.ker ⧸ K.subgroupOf φ.ker)
      = 2 ^ Work.ClassFieldTower.unitTwoRank F := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective Ψ hsurj).toEquiv]
    rw [hkerPsi, two_pow_unitTwoRank_eq_card_units_sqQuotient F]
  -- `[V_∅ : ker φ] = #Cl(F)[2] = 2 ^ classGroupTwoRank F`
  have hrange : ∀ c : ClassGroup (𝓞 F), c ∈ φ.range ↔ c ^ 2 = 1 := by
    intro c
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      change (vClass F x) ^ 2 = 1
      exact vClass_sq_eq_one F x
    · intro hc
      obtain ⟨x, hx⟩ := vClass_surjective_twoTorsion F c hc
      exact ⟨x, by change vClass F x = c; exact hx⟩
  have hcardRange : Nat.card ↥φ.range = Nat.card {c : ClassGroup (𝓞 F) // c ^ 2 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight hrange)
  have hcardKer : Nat.card (↥(VTwo F) ⧸ φ.ker)
      = 2 ^ Work.ClassFieldTower.classGroupTwoRank F := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hcardRange]
    exact (Work.ClassFieldTower.card_quotient_squareSubgroup_eq_card_twoTorsion
        (ClassGroup (𝓞 F))).symm.trans
      (Work.ClassFieldTower.two_pow_classGroupTwoRank F).symm
  -- index multiplicativity for `(Fˣ)² ≤ ker φ ≤ V_∅`
  have hmain : Nat.card (↥(VTwo F) ⧸ K)
      = Nat.card (↥φ.ker ⧸ K.subgroupOf φ.ker)
        * Nat.card (↥(VTwo F) ⧸ φ.ker) := by
    rw [← Subgroup.index_eq_card K, ← Subgroup.index_eq_card (K.subgroupOf φ.ker),
        ← Subgroup.index_eq_card φ.ker]
    rw [show (K.subgroupOf φ.ker).index = K.relIndex φ.ker from rfl,
        Subgroup.relIndex_mul_index hKle]
  rw [hmain, hcardD, hcardKer, ← pow_add]

end Work.ShafarevichKoch
