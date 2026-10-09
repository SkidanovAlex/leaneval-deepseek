import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The order of `(𝒪[F]/𝔪[F]^n)ˣ`

For a nonarchimedean local field `F` with residue cardinality `q = #𝓀[F]` and maximal ideal
`𝔪 = 𝔪[F]` of the ring of integers, the group of units of `𝒪[F]/𝔪^n` has order
`(q - 1) * q^(n - 1)` for `n ≥ 1`.  This is the classical statement `#(𝒪/𝔪^n)ˣ = (q - 1)q^{n-1}`
(Serre, *Local Fields*, Ch. IV §1); it is the source of the cardinality of the successive
quotients `U^n/U^{n+1} ≅ 𝓀` of the Lubin–Tate filtration of the unit group.

The proof is carried out for an arbitrary discrete valuation ring `R` with finite residue field:

* `Ideal.quotEquivPowQuotPowSuccEquiv` together with
  `Ideal.powQuotPowSuccEquivMapMkPowSuccPow` shows that each successive quotient `𝔪^n/𝔪^(n+1)` has
  the cardinality `q` of the residue field;
* the third isomorphism theorem for modules (`Submodule.card_quotient_mul_card_quotient`) then
  gives `#(R/𝔪^n) = q^n` and `#(𝔪/𝔪^n) = q^(n-1)` by induction on `n`;
* the units of the finite local ring `R/𝔪^n` are the complement of its maximal ideal `𝔪/𝔪^n`, so
  `#(R/𝔪^n)ˣ = q^n - q^(n-1) = (q - 1) q^(n-1)`.
-/

open scoped ValuativeRel

set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.Units

noncomputable section

/-! ## The image of an ideal in a quotient ring -/

/-- The image of an ideal `J` in the quotient `R ⧸ I` is the same set whether it is taken as the
ideal `Ideal.map (Ideal.Quotient.mk I) J` of the quotient ring or as the image of `J` under the
quotient map viewed as a linear map, `Submodule.map (Submodule.mkQ I) J`. -/
theorem coe_idealMap_eq_coe_submoduleMap_mkQ (R : Type*) [CommRing R] (I J : Ideal R) :
    (Ideal.map (Ideal.Quotient.mk I) J : Set (R ⧸ I)) =
      (Submodule.map (Submodule.mkQ I) (J : Submodule R R) : Set (R ⧸ I)) := by
  ext x
  simp only [SetLike.mem_coe]
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

/-- The cardinals of `Ideal.map (Ideal.Quotient.mk I) J` and of `Submodule.map (Submodule.mkQ I) J`
agree, since the two are the same subset of `R ⧸ I`. -/
theorem natCard_idealMap_eq_natCard_submoduleMap_mkQ (R : Type*) [CommRing R] (I J : Ideal R) :
    Nat.card ↥(Ideal.map (Ideal.Quotient.mk I) J) =
      Nat.card ↥(Submodule.map (Submodule.mkQ I) (J : Submodule R R)) :=
  Nat.card_congr (Set.equivOfEq (coe_idealMap_eq_coe_submoduleMap_mkQ R I J))

/-! ## Discrete valuation rings -/

section DVR

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In a discrete valuation ring the maximal ideal is principal. -/
theorem maximalIdeal_isPrincipal : (IsLocalRing.maximalIdeal R).IsPrincipal :=
  IsPrincipalIdealRing.principal _

/-- In a discrete valuation ring the maximal ideal is not zero. -/
theorem maximalIdeal_ne_bot : IsLocalRing.maximalIdeal R ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field R

/-- **Each successive quotient `𝔪^n / 𝔪^{n+1}` has the residue cardinality**: the maximal ideal of a
DVR is principal, so `R ⧸ 𝔪 ≃ 𝔪^n ⧸ 𝔪^{n+1}` via `Ideal.quotEquivPowQuotPowSuccEquiv`. -/
theorem natCard_pow_quot_pow_succ (n : ℕ) :
    Nat.card ↥(Submodule.map (Submodule.mkQ ((IsLocalRing.maximalIdeal R) ^ (n + 1)))
        (((IsLocalRing.maximalIdeal R) ^ n : Ideal R) : Submodule R R)) =
      Nat.card (IsLocalRing.ResidueField R) := by
  rw [← natCard_idealMap_eq_natCard_submoduleMap_mkQ]
  exact (Nat.card_congr
    ((Ideal.quotEquivPowQuotPowSuccEquiv (maximalIdeal_isPrincipal R)
        (maximalIdeal_ne_bot R) n).trans
      (Ideal.powQuotPowSuccEquivMapMkPowSuccPow (IsLocalRing.maximalIdeal R) n))).symm

/-- **The order of `R ⧸ 𝔪^n`** is the `n`-th power of the residue cardinality. -/
theorem natCard_quot_maximalIdeal_pow (n : ℕ) :
    Nat.card (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) =
      (Nat.card (IsLocalRing.ResidueField R)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Submodule.card_quotient_mul_card_quotient (R := R) (M := R)
      ((IsLocalRing.maximalIdeal R) ^ n : Ideal R)
      ((IsLocalRing.maximalIdeal R) ^ (n + 1) : Ideal R)
      (Ideal.pow_le_pow_right (Nat.le_succ n))
    rw [natCard_pow_quot_pow_succ R n, ih, ← pow_succ'] at h
    exact h.symm

/-- **The order of `𝔪 / 𝔪^n`** for `n ≥ 1` is `q^(n-1)`; this is the cardinality of the maximal
ideal of the finite local ring `R ⧸ 𝔪^n`. -/
theorem natCard_submoduleMap_mkQ_maximalIdeal (hfin : Finite (IsLocalRing.ResidueField R))
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(Submodule.map (Submodule.mkQ ((IsLocalRing.maximalIdeal R) ^ n))
        ((IsLocalRing.maximalIdeal R) : Submodule R R)) =
      (Nat.card (IsLocalRing.ResidueField R)) ^ (n - 1) := by
  have hq : Nat.card (IsLocalRing.ResidueField R) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  have h := Submodule.card_quotient_mul_card_quotient (R := R) (M := R)
    ((IsLocalRing.maximalIdeal R) : Ideal R)
    ((IsLocalRing.maximalIdeal R) ^ n : Ideal R)
    (Ideal.pow_le_self (by omega : n ≠ 0))
  rw [natCard_quot_maximalIdeal_pow R n] at h
  have hn' : n = (n - 1) + 1 := by omega
  have hkey : (Nat.card (IsLocalRing.ResidueField R)) ^ n =
      (Nat.card (IsLocalRing.ResidueField R)) ^ (n - 1) *
        Nat.card (IsLocalRing.ResidueField R) := by
    conv_lhs => rw [hn']
    rw [pow_succ]
  rw [hkey] at h
  exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hq) h

/-- The quotient of a DVR with finite residue field by a power of its maximal ideal is finite. -/
theorem finite_quot_maximalIdeal_pow (hfin : Finite (IsLocalRing.ResidueField R)) (n : ℕ) :
    Finite (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) := by
  have hcard : Nat.card (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) ≠ 0 := by
    rw [natCard_quot_maximalIdeal_pow R n]
    exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩)
  exact (Nat.card_ne_zero.mp hcard).2

end DVR

/-! ## The units of a finite local ring -/

section FiniteLocalRing

variable (A : Type*) [CommRing A] [IsLocalRing A] [Finite A]

/-- The units of a monoid, as the subtype of units. -/
def unitsEquivIsUnit : Aˣ ≃ {x : A // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := by ext; exact IsUnit.unit_spec u.isUnit
  right_inv x := Subtype.ext (IsUnit.unit_spec x.2)

/-- **The units of a finite local ring are the complement of its maximal ideal**, so
`#A = #Aˣ + #𝔪`. -/
theorem natCard_eq_natCard_units_add_natCard_maximalIdeal :
    Nat.card A = Nat.card Aˣ + Nat.card ↥(IsLocalRing.maximalIdeal A) := by
  classical
  have h1 : Nat.card Aˣ = Nat.card {x : A // IsUnit x} :=
    Nat.card_congr (unitsEquivIsUnit A)
  have h2 : Nat.card ↥(IsLocalRing.maximalIdeal A) = Nat.card {x : A // ¬IsUnit x} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
      constructor
      · intro hx hu
        exact (IsLocalRing.notMem_maximalIdeal (x := x)).mpr hu hx
      · intro hx
        by_contra hmem
        exact hx ((IsLocalRing.notMem_maximalIdeal (x := x)).mp hmem)))
  calc Nat.card A = Nat.card ({x : A // IsUnit x} ⊕ {x : A // ¬IsUnit x}) :=
        (Nat.card_congr (Equiv.sumCompl (fun x : A => IsUnit x))).symm
    _ = Nat.card {x : A // IsUnit x} + Nat.card {x : A // ¬IsUnit x} := Nat.card_sum
    _ = Nat.card Aˣ + Nat.card ↥(IsLocalRing.maximalIdeal A) := by rw [h1, ← h2]

end FiniteLocalRing

/-! ## The main computation -/

section DVRUnits

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The order of `(R ⧸ 𝔪^n)ˣ`**: for a discrete valuation ring `R` with finite residue field and
`n ≥ 1`, it is `(q - 1) q^(n-1)` where `q = #𝓀[R]`. -/
theorem natCard_units_quot_maximalIdeal_pow (hfin : Finite (IsLocalRing.ResidueField R))
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ((R ⧸ (IsLocalRing.maximalIdeal R) ^ n)ˣ) =
      (Nat.card (IsLocalRing.ResidueField R) - 1) *
        (Nat.card (IsLocalRing.ResidueField R)) ^ (n - 1) := by
  have hq : Nat.card (IsLocalRing.ResidueField R) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  have hfinq : Finite (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) :=
    finite_quot_maximalIdeal_pow R hfin n
  letI : Finite (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) := hfinq
  have hnt : Nontrivial (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    rw [Ideal.pow_eq_top_iff] at htop
    rcases htop with h | h
    · exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top h
    · omega
  letI : IsLocalRing (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmax : Nat.card ↥(IsLocalRing.maximalIdeal (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)) =
      (Nat.card (IsLocalRing.ResidueField R)) ^ (n - 1) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ n))
      Ideal.Quotient.mk_surjective]
    rw [natCard_idealMap_eq_natCard_submoduleMap_mkQ R ((IsLocalRing.maximalIdeal R) ^ n)
      (IsLocalRing.maximalIdeal R)]
    exact natCard_submoduleMap_mkQ_maximalIdeal R hfin n hn
  have hdecomp := natCard_eq_natCard_units_add_natCard_maximalIdeal
    (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)
  rw [natCard_quot_maximalIdeal_pow R n, hmax] at hdecomp
  have hn' : n = (n - 1) + 1 := by omega
  have hkey : (Nat.card (IsLocalRing.ResidueField R)) ^ n =
      (Nat.card (IsLocalRing.ResidueField R)) ^ (n - 1) *
        Nat.card (IsLocalRing.ResidueField R) := by
    conv_lhs => rw [hn']
    rw [pow_succ]
  have harith : (Nat.card (IsLocalRing.ResidueField R) - 1) *
        (Nat.card (IsLocalRing.ResidueField R)) ^ (n - 1) =
      (Nat.card (IsLocalRing.ResidueField R)) ^ n -
        (Nat.card (IsLocalRing.ResidueField R)) ^ (n - 1) := by
    rw [Nat.mul_sub_right_distrib, one_mul, mul_comm, ← hkey]
  exact (Nat.eq_sub_of_add_eq hdecomp.symm).trans harith.symm

end DVRUnits

/-! ## The local field statement -/

theorem natCard_units_quot_pow_maximalIdeal (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ((((ValuativeRel.valuation F).integer ⧸
        NK.LocalReciprocityLubinTate.maximalIdealOfIntegers F ^ n))ˣ) =
      (NK.LocalReciprocityLubinTate.residueCard F - 1) *
        NK.LocalReciprocityLubinTate.residueCard F ^ (n - 1) := by
  have h := natCard_units_quot_maximalIdeal_pow (ValuativeRel.valuation F).integer
    (inferInstance : Finite
      (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer)) n hn
  simpa [NK.LocalReciprocityLubinTate.residueCard,
    NK.LocalReciprocityLubinTate.maximalIdealOfIntegers] using h

end

end NK.LocalReciprocityLubinTate.Units
