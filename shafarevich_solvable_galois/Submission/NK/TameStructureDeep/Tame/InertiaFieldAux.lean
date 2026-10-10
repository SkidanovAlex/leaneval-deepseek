import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.Commons.RingTheory.Henselian.kummer_root_lift
import Submission.NK.Ramification.Defs
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.isPrimitiveRoot_residue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the inertia field computation

Three elementary facts:

* a root of unity of `E` lies in a valuation subring `A` of `E`;
* two `n`-th roots of unity of a local ring with the same residue are equal, provided `n` is a
  unit (the reduction map is injective on the roots of unity of order `n`);
* in a Henselian local ring with finite residue field `k`, the `(#k - 1)`-st roots of unity lift.
-/

open scoped Classical

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {κ E : Type*} [Field κ] [Field E] [Algebra κ E]

/-- **A root of unity of `E` lies in the valuation subring `A`.**  It is a root of the monic
polynomial `X ^ n - 1` with coefficients in `A`, hence integral over `A`; and a valuation subring
is maximal among the local subrings of its fraction field, so integrally closed. -/
theorem mem_valuationSubring_of_isPrimitiveRoot (A : ValuationSubring E) {n : ℕ} {ζ : E}
    (hζ : IsPrimitiveRoot ζ n) (hn0 : n ≠ 0) : ζ ∈ A :=
  (ValuationSubring.mem_toSubring A ζ).mp
    (LocalSubring.mem_of_isMax_of_isIntegral (ValuationSubring.isMax_toLocalSubring A)
      (IsIntegral.of_pow (Nat.pos_of_ne_zero hn0)
        (by rw [hζ.pow_eq_one]; exact isIntegral_one)))

/-- **Two `n`-th roots of unity of a local ring with equal residues and `(n : R)` a unit are
equal.** -/
theorem eq_of_residue_eq_of_pow_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : IsUnit (n : R)) {x y : R} (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hres : IsLocalRing.residue R x = IsLocalRing.residue R y) : x = y := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn.ne_zero (Nat.cast_zero)
  have hηpow : (x * y ^ (n - 1)) ^ n = 1 := by
    rw [mul_pow, hx, one_mul, ← pow_mul, mul_comm (n - 1) n, pow_mul, hy, one_pow]
  have hηres : IsLocalRing.residue R (x * y ^ (n - 1)) = 1 := by
    rw [map_mul, map_pow, hres, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0),
      ← map_pow, hy, map_one]
  have hηeq := eq_one_of_residue_eq_one hn hηpow hηres
  have h2 : x * y ^ (n - 1) * y = y := by rw [hηeq, one_mul]
  have h3 : x * y ^ (n - 1) * y = x := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), hy, mul_one]
  rw [← h3, h2]

/-- **The inertia subgroup fixes roots of unity whose order is a unit of `A`.**

If `τ` lies in `A.inertiaSubgroup κ` then `τ` acts trivially on the residue field of `A`; hence
`τ ζ` and `ζ` are two `n`-th roots of unity with the same residue in `A`, so they are equal by
`eq_of_residue_eq_of_pow_eq_one`. -/
theorem inertiaSubgroup_apply_isPrimitiveRoot (A : ValuationSubring E) [IsDiscreteValuationRing A]
    {n : ℕ} (hn : IsUnit (n : ↥A))
    (τ : ↥(A.inertiaSubgroup κ)) {ζ : E} (hζ : IsPrimitiveRoot ζ n) :
    ((τ : ↥(A.decompositionSubgroup κ)) : E ≃ₐ[κ] E) ζ = ζ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn.ne_zero (Nat.cast_zero)
  have hζA : ζ ∈ A := mem_valuationSubring_of_isPrimitiveRoot A hζ hn0
  let ζA : ↥A := ⟨ζ, hζA⟩
  let g : ↥(A.decompositionSubgroup κ) := τ.1
  have hζA_pow : ζA ^ n = 1 := by
    apply Subtype.ext
    change (A.subtype (ζA ^ n)) = A.subtype 1
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  have hy_pow : (g • ζA) ^ n = 1 := by
    have h := map_pow (MulSemiringAction.toRingHom ↥(A.decompositionSubgroup κ) ↥A g) ζA n
    rw [hζA_pow, map_one] at h
    rw [MulSemiringAction.toRingHom_apply] at h
    exact h.symm
  have hres : IsLocalRing.residue ↥A ζA = IsLocalRing.residue ↥A (g • ζA) := by
    rw [IsLocalRing.ResidueField.residue_smul, ← MulSemiringAction.toRingEquiv_apply]
    have hker : MulSemiringAction.toRingAut ↥(A.decompositionSubgroup κ)
        (IsLocalRing.ResidueField ↥A) g = 1 := MonoidHom.mem_ker.mp τ.2
    rw [← MulSemiringAction.toRingAut_apply, hker]
    rfl
  have heq : ζA = g • ζA := eq_of_residue_eq_of_pow_eq_one hn hζA_pow hy_pow hres
  rw [← NK.Ramification.coe_smul A g ζA, ← heq]

/-- **Teichmüller lift of the roots of unity of the residue field.**  A Henselian local ring with
finite residue field `k` contains a primitive `(#k - 1)`-st root of unity. -/
theorem exists_isPrimitiveRoot_residueField_card_sub_one (R : Type*) [CommRing R] [HenselianLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] :
    ∃ ζ : R, IsPrimitiveRoot ζ (Nat.card (IsLocalRing.ResidueField R) - 1) := by
  classical
  haveI : IsLocalRing R := ‹HenselianLocalRing R›.toIsLocalRing
  haveI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  set N : ℕ := Nat.card (IsLocalRing.ResidueField R) - 1 with hN
  obtain ⟨ω, hωgen⟩ := IsCyclic.exists_generator (α := (IsLocalRing.ResidueField R)ˣ)
  have hωord : orderOf (ω : IsLocalRing.ResidueField R) = N := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hωgen, Nat.card_units, hN]
  have hωprim : IsPrimitiveRoot (ω : IsLocalRing.ResidueField R) N :=
    IsPrimitiveRoot.iff_orderOf.mpr hωord
  have hcard : Nat.card (IsLocalRing.ResidueField R) = Fintype.card (IsLocalRing.ResidueField R) :=
    Nat.card_eq_fintype_card
  have h1k : 1 ≤ Nat.card (IsLocalRing.ResidueField R) := by
    rw [hcard]; exact le_of_lt Fintype.one_lt_card
  have hcard0 : (Nat.card (IsLocalRing.ResidueField R) : IsLocalRing.ResidueField R) = 0 := by
    rw [hcard]; exact FiniteField.cast_card_eq_zero _
  have hNunit : IsUnit (N : R) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hres' : (IsLocalRing.residue R) ((N : ℕ) : R) = -1 := by
      rw [map_natCast, hN, Nat.cast_sub h1k, hcard0, Nat.cast_one]
      simp
    rw [hres']
    exact neg_ne_zero.mpr one_ne_zero
  obtain ⟨ζ, hζpow, hζres⟩ :=
    Commons.RingTheory.Henselian.kummer_root_lift (R := R) N (u := 1) isUnit_one hNunit
      (ω : IsLocalRing.ResidueField R) (by rw [map_one]; exact hωprim.pow_eq_one)
  refine ⟨ζ, IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  refine Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr hζpow) ?_
  have hmap : orderOf (IsLocalRing.residue R ζ) ∣ orderOf ζ :=
    orderOf_map_dvd (IsLocalRing.residue R).toMonoidHom ζ
  rwa [hζres, hωord] at hmap

end

end NK.TameStructureDeep.Tame
