import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.int_coords_and_norm
import Submission.Work.ClassFieldTower.span_pair_sq
import Submission.Work.ClassFieldTower.card_quotient_sq_eq_card_twoTorsion
import Submission.Work.ClassFieldTower.card_twoTorsion_ge_of_independent
import Submission.Commons.NumberTheory.NumberField.not_isSquare_prod_primes

/-!
# The numerical genus-theory certificate `rank₂ Cl(F) ≥ 5`

For the imaginary quadratic field `F = ℚ(√-30030)` (`30030 = 2·3·5·7·11·13`) the ring of
integers is `ℤ[√-d]`, and for each of the five odd primes `p ∈ {3,5,7,11,13}` the ideal
`P_p = (p, √-d)` satisfies `P_p² = (p)`.  Hence the classes of the `P_p` are `2`-torsion, and all
`32` sub-products are pairwise distinct: if `∏_{p ∈ T} P_p` were principal, with generator
`a = x + y√-d`, then `∏_{p∈T} p = |N a| = |x² + d y²|`, which is impossible because the nonempty
product `∏_{p∈T} p` is strictly smaller than `d` and is not a square.

Consequently `Cl(𝓞 F)[2]` has at least `2 ^ 5 = 32` elements, and `#(Cl/Cl²) = #Cl[2]` gives
`classGroupTwoRank F = log₂ #(Cl/Cl²) ≥ 5`.
-/

open scoped Classical
open scoped NumberField
open scoped nonZeroDivisors
open NumberField

namespace Work.ClassFieldTower

noncomputable section

set_option maxHeartbeats 800000

/-! ## The ramified prime ideals -/

/-- `P_i = (p_i, √-d)`, the prime ideal of `𝓞 Kc` above the ramified prime `p_i = certPrime i`. -/
def Pideal (i : Fin 5) : Ideal (𝓞 Kc) :=
  Ideal.span ({(certPrime i : 𝓞 Kc), scR} : Set (𝓞 Kc))

lemma Pideal_ne_zero (i : Fin 5) : Pideal i ≠ 0 := by
  intro h
  have hle : Ideal.span ({(certPrime i : 𝓞 Kc)} : Set (𝓞 Kc)) ≤ Pideal i := by
    rw [Pideal, Ideal.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Ideal.subset_span (by simp)
  rw [h] at hle
  have h2 : (certPrime i : 𝓞 Kc) = 0 :=
    Ideal.span_singleton_eq_bot.mp (le_bot_iff.mp hle)
  exact Nat.cast_ne_zero.mpr (certPrime_prime i).ne_zero h2

lemma Pideal_mem (i : Fin 5) : Pideal i ∈ (Ideal (𝓞 Kc))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (Pideal_ne_zero i)

lemma Pideal_sq (i : Fin 5) : Pideal i ^ 2 = Ideal.span {(certPrime i : 𝓞 Kc)} :=
  span_pair_sq i

lemma finrank_ringOfIntegers : Module.finrank ℤ (𝓞 Kc) = 2 := by
  rw [NumberField.RingOfIntegers.rank, finrank_eq_two]

/-- The absolute norm of the ramified prime ideal `P_i` is `p_i`. -/
lemma absNorm_Pideal (i : Fin 5) : (Pideal i).absNorm = certPrime i := by
  have hsq : (Pideal i ^ 2).absNorm = certPrime i * certPrime i := by
    rw [Pideal_sq, Ideal.absNorm_span_natCast, finrank_ringOfIntegers, pow_two]
  have hmul : (Pideal i ^ 2).absNorm = (Pideal i).absNorm * (Pideal i).absNorm := by
    rw [pow_two]
    exact map_mul (Ideal.absNorm) (Pideal i) (Pideal i)
  rw [hmul] at hsq
  exact Nat.mul_self_inj.mp hsq

/-- The class of `P_i` is `2`-torsion. -/
lemma mk0_Pideal_sq (i : Fin 5) :
    (ClassGroup.mk0 ⟨Pideal i, Pideal_mem i⟩) ^ 2 = 1 := by
  have hmem : Ideal.span {(certPrime i : 𝓞 Kc)} ∈ (Ideal (𝓞 Kc))⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro hzero
    exact Nat.cast_ne_zero.mpr (certPrime_prime i).ne_zero
      (Ideal.span_singleton_eq_bot.mp (by simpa using hzero))
  have hsq : (⟨Pideal i, Pideal_mem i⟩ : (Ideal (𝓞 Kc))⁰) * ⟨Pideal i, Pideal_mem i⟩
      = ⟨Ideal.span {(certPrime i : 𝓞 Kc)}, hmem⟩ := by
    apply Subtype.ext
    show Pideal i * Pideal i = Ideal.span {(certPrime i : 𝓞 Kc)}
    rw [← pow_two]
    exact Pideal_sq i
  rw [pow_two, ← map_mul, hsq]
  refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
  exact (Submodule.isPrincipal_iff _).mpr ⟨certPrime i, rfl⟩

/-- **No nonempty sub-product of the ramified prime ideals is principal.** -/
lemma not_isPrincipal_prod (T : Finset (Fin 5)) (hT : T.Nonempty) :
    ¬ Submodule.IsPrincipal (∏ i ∈ T, Pideal i) := by
  intro hprin
  obtain ⟨a, ha⟩ := hprin.principal
  have hnorm1 : (∏ i ∈ T, Pideal i).absNorm = ∏ i ∈ T, certPrime i := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => absNorm_Pideal i)
  have hspan : Ideal.span {a} = ∏ i ∈ T, Pideal i := by
    rw [ha]
  have hnorm2 : (Algebra.norm ℤ a).natAbs = ∏ i ∈ T, certPrime i := by
    rw [← Ideal.absNorm_span_singleton a, hspan]
    exact hnorm1
  obtain ⟨x, y, _hxy, hnormxy⟩ := int_coords_and_norm a
  have hnonneg : (0 : ℤ) ≤ x ^ 2 + (dWit : ℤ) * y ^ 2 := by
    have h1 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
    have h2 : (0 : ℤ) ≤ (dWit : ℤ) * y ^ 2 := by positivity
    linarith
  have hkey : x ^ 2 + (dWit : ℤ) * y ^ 2 = (∏ i ∈ T, certPrime i : ℤ) := by
    have h3 : (x ^ 2 + (dWit : ℤ) * y ^ 2).natAbs = ∏ i ∈ T, certPrime i := by
      rw [← hnormxy]
      exact hnorm2
    have h4 : (((x ^ 2 + (dWit : ℤ) * y ^ 2).natAbs : ℕ) : ℤ)
        = x ^ 2 + (dWit : ℤ) * y ^ 2 := Int.natAbs_of_nonneg hnonneg
    have := congrArg (fun n : ℕ => (n : ℤ)) h3
    rw [h4] at this
    push_cast at this ⊢
    exact this
  have hlt : (∏ i ∈ T, certPrime i : ℤ) < 30030 := by
    have h := certPrime_finset_prod_lt T hT
    have : dWit = 30030 := rfl
    omega
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    have hx2 : x ^ 2 = (∏ i ∈ T, certPrime i : ℤ) := by simpa using hkey
    refine Commons.NumberTheory.NumberField.not_isSquare_prod_primes T certPrime
      (fun i _ => certPrime_prime i) (fun i _ j _ hij => certPrime_injective hij) hT (x : ℚ) ?_
    have hcast : ((x : ℚ)) ^ 2 = ((x ^ 2 : ℤ) : ℚ) := by push_cast; ring
    rw [hcast, hx2]
    push_cast
    ring
  · have hy1 : (1 : ℤ) ≤ y ^ 2 := by
      have hpos : (0 : ℤ) < y ^ 2 := sq_pos_of_ne_zero hy
      omega
    have hbig : (30030 : ℤ) ≤ (dWit : ℤ) * y ^ 2 := by
      have h1 : (30030 : ℤ) ≤ y ^ 2 * 30030 := by
        simpa using mul_le_mul_of_nonneg_right hy1 (show (0 : ℤ) ≤ 30030 by norm_num)
      have h2 : (dWit : ℤ) = 30030 := rfl
      rw [h2]
      linarith
    have hx0 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
    have : (30030 : ℤ) ≤ (∏ i ∈ T, certPrime i : ℤ) := by linarith
    omega

/-- No nonempty sub-product of the classes of the ramified primes is trivial. -/
lemma mk0_prod_ne_one (T : Finset (Fin 5)) (hT : T.Nonempty) :
    (∏ i ∈ T, ClassGroup.mk0 ⟨Pideal i, Pideal_mem i⟩) ≠ 1 := by
  intro h
  refine not_isPrincipal_prod T hT ?_
  have h2 : ClassGroup.mk0 (∏ i ∈ T, (⟨Pideal i, Pideal_mem i⟩ : (Ideal (𝓞 Kc))⁰)) = 1 := by
    rw [map_prod]
    exact h
  have h3 : (∏ i ∈ T, (⟨Pideal i, Pideal_mem i⟩ : (Ideal (𝓞 Kc))⁰))
      = ⟨∏ i ∈ T, Pideal i, mem_nonZeroDivisors_of_ne_zero
          (Finset.prod_ne_zero_iff.mpr (fun i _ => Pideal_ne_zero i))⟩ := by
    apply Subtype.ext
    rw [Submonoid.coe_finsetProd]
  rw [h3] at h2
  exact (ClassGroup.mk0_eq_one_iff _).mp h2

/-- **The numerical certificate.** -/
theorem five_le_classGroupTwoRank : 5 ≤ classGroupTwoRank Kc := by
  have h1 : 2 ^ 5 ≤ Nat.card {y : ClassGroup (𝓞 Kc) // y ^ 2 = 1} :=
    card_twoTorsion_ge_of_independent (ClassGroup (𝓞 Kc)) 5
      (fun i => ClassGroup.mk0 ⟨Pideal i, Pideal_mem i⟩)
      (fun i => mk0_Pideal_sq i)
      (fun T hT => mk0_prod_ne_one T hT)
  have h2 : Nat.card (ClassGroup (𝓞 Kc) ⧸ Subgroup.closure
        (Set.range (fun x : ClassGroup (𝓞 Kc) => x ^ 2)))
      = Nat.card {y : ClassGroup (𝓞 Kc) // y ^ 2 = 1} :=
    card_quotient_sq_eq_card_twoTorsion (ClassGroup (𝓞 Kc))
  have h3 : classGroupTwoRank Kc
      = Nat.log 2 (Nat.card (ClassGroup (𝓞 Kc) ⧸ Subgroup.closure
          (Set.range (fun x : ClassGroup (𝓞 Kc) => x ^ 2)))) := rfl
  rw [h3, h2]
  refine (Nat.le_log_iff_pow_le (by norm_num) ?_).mpr h1
  exact Nat.card_ne_zero.mpr ⟨⟨⟨1, by simp⟩⟩, inferInstance⟩

end

theorem exists_imaginaryQuadratic_classGroupTwoRank_ge_five :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyComplex F)
      (_ : Module.finrank ℚ F = 2), 5 ≤ classGroupTwoRank F := by
  refine ⟨Kc, ?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstance
  · exact inferInstance
  · exact isTotallyComplex
  · exact finrank_eq_two
  · exact five_le_classGroupTwoRank

end Work.ClassFieldTower
