import Mathlib
import Submission.Work.QuadraticFields.QuadField
import Submission.Work.QuadraticFields.quadField_finrank

/-!
# `Work.ClassFieldTower.WitnessField` -- the witness field `ℚ(√-30030)`

The numerical certificate `rank₂ Cl(F) ≥ 5` needed by the Golod--Shafarevich criterion is
implemented for the concrete imaginary quadratic field `F = ℚ(√-d)`, `d = 30030 = 2·3·5·7·11·13`.

The five odd primes `3, 5, 7, 11, 13` dividing `d` are ramified, and the ideals
`P_p = (p, √-d)` satisfy `P_p² = (p)`; hence their classes in `Cl(𝓞 F)` are `2`-torsion.
The proof that the `32` sub-products of these five classes are pairwise distinct goes through
the norm form: `𝓞 F = ℤ[√-d]`, so an element `a = x + y√-d` has `|N a| = x² + d y²`, and for a
nonempty set `S` of primes the ideal `∏_{p∈S} P_p` has norm `∏_{p∈S} p < d`, which is not
represented by the norm form (it is > 1 and squarefree).  Hence
`Cl(𝓞 F)[2]` has at least `2 ^ 5 = 32` elements and therefore `rank₂ Cl(F) = log₂ #(Cl/Cl²) ≥ 5`.

This file contains the basic setup of the field and the elementary facts about it; the
arithmetic lemmas are in the sibling modules.

## Main definitions

* `Work.ClassFieldTower.dWit`, `aWit`: `30030` and `-30030`.
* `Work.ClassFieldTower.Kc`: the field `ℚ(√-30030)` (inside `AlgebraicClosure ℚ`).
* `Work.ClassFieldTower.sc`: the generator `√-30030`.

## Main results

* `sc_sq`, `sc_sq_num`, `no_rat_sq`, `finrank_eq_two`, `sc_not_rat`, `isTotallyComplex`,
  `exists_coords`.
-/

open NumberField
open scoped NumberField

namespace Work.ClassFieldTower

noncomputable section

set_option maxHeartbeats 800000

/-- `d = 2 · 3 · 5 · 7 · 11 · 13 = 30030`, the radicand of the witness field. -/
abbrev dWit : ℕ := 30030

/-- `-d`, the argument of the square root defining the witness field. -/
abbrev aWit : ℚ := -(dWit : ℚ)

/-- The witness field `ℚ(√-30030)`, an imaginary quadratic field. -/
abbrev Kc : Type := ↥(Work.QuadraticFields.quadField aWit)

/-- The generator `√-30030` of the witness field. -/
def sc : Kc := ⟨Work.QuadraticFields.sqrtVal aWit,
  Work.QuadraticFields.sqrtVal_mem_quadField aWit⟩

theorem sc_sq : sc * sc = algebraMap ℚ Kc aWit := by
  apply Subtype.ext
  rw [IntermediateField.coe_mul, IntermediateField.coe_algebraMap_apply]
  simpa [sc, pow_two] using Work.QuadraticFields.sqrtVal_sq aWit

/-- The defining relation of the generator, in the `ℕ`-cast form used by the later arguments. -/
theorem sc_sq_num : sc * sc = -(30030 : Kc) := by
  rw [sc_sq]
  norm_num [aWit, dWit]

theorem no_rat_sq : ∀ r : ℚ, r ^ 2 ≠ aWit := by
  intro r hr
  have h1 : (0:ℚ) ≤ r^2 := sq_nonneg r
  have h2 : aWit < 0 := by norm_num [aWit, dWit]
  linarith

/-- The witness field is quadratic. -/
theorem finrank_eq_two : Module.finrank ℚ Kc = 2 :=
  Work.QuadraticFields.quadField_finrank aWit no_rat_sq

/-- The generator is not rational. -/
theorem sc_not_rat (q : ℚ) : sc ≠ algebraMap ℚ Kc q := by
  intro h
  have h2 : algebraMap ℚ Kc (q * q) = algebraMap ℚ Kc aWit := by
    rw [map_mul, ← h, sc_sq]
  have h3 : q * q = aWit := (algebraMap ℚ Kc).injective h2
  exact no_rat_sq q (by rw [sq]; exact h3)

/-- **The witness field is totally complex.**  Every embedding of `ℚ(√-d)` into `ℂ` sends the
generator to a square root of the negative rational number `-d`, hence is not real. -/
theorem isTotallyComplex : NumberField.IsTotallyComplex Kc := by
  refine ⟨fun w => ?_⟩
  refine ⟨w.embedding, ?_, NumberField.InfinitePlace.mk_embedding w⟩
  intro hreal
  have h1 : star (w.embedding sc) = w.embedding sc := by
    rw [← RingHom.star_apply, hreal]
  have hsq : w.embedding sc * w.embedding sc = -(30030 : ℂ) := by
    rw [← map_mul, sc_sq_num, map_neg, map_ofNat]
  have him : (w.embedding sc).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    simpa [Complex.star_def] using h1
  have hz : w.embedding sc = ((w.embedding sc).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have h3 : (((w.embedding sc).re : ℂ)) ^ 2 = ((-30030 : ℝ) : ℂ) := by
    rw [← hz, pow_two, hsq]
    norm_num
  have h4 : (w.embedding sc).re ^ 2 = -30030 := by
    rw [← Complex.ofReal_pow] at h3
    exact Complex.ofReal_injective h3
  have h5 : (0:ℝ) ≤ (w.embedding sc).re ^ 2 := sq_nonneg _
  linarith

/-- **The primitive element theorem for the witness field**: `ℚ[√-d] = Kc`. -/
theorem adjoin_sc_eq_top : Algebra.adjoin ℚ ({sc} : Set Kc) = ⊤ := by
  have hInt : IntermediateField.adjoin ℚ ({sc} : Set Kc) = ⊤ := by
    apply IntermediateField.lift_injective (Work.QuadraticFields.quadField aWit)
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have hset : (Subtype.val '' ({sc} : Set Kc) : Set (AlgebraicClosure ℚ))
        = {Work.QuadraticFields.sqrtVal aWit} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Set.mem_singleton _
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨sc, Set.mem_singleton _, rfl⟩
    rw [hset]
    rfl
  exact Algebra.adjoin_eq_top_of_primitive_element (Algebra.IsAlgebraic.isAlgebraic sc) hInt

/-- **Coordinates over `ℚ`.**  Every element of the witness field is `x + y√-d` with
`x y : ℚ`. -/
theorem exists_coords (z : Kc) :
    ∃ x y : ℚ, z = algebraMap ℚ Kc x + algebraMap ℚ Kc y * sc := by
  let T : Subalgebra ℚ Kc :=
    { carrier := {z | ∃ x y : ℚ, z = algebraMap ℚ Kc x + algebraMap ℚ Kc y * sc}
      add_mem' := by
        rintro a b ⟨x, y, rfl⟩ ⟨x', y', rfl⟩
        refine ⟨x + x', y + y', ?_⟩
        simp only [map_add]
        ring
      zero_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨x, y, rfl⟩ ⟨x', y', rfl⟩
        refine ⟨x * x' + aWit * (y * y'), x * y' + y * x', ?_⟩
        have key :
          (algebraMap ℚ Kc x + algebraMap ℚ Kc y * sc) *
              (algebraMap ℚ Kc x' + algebraMap ℚ Kc y' * sc)
            = algebraMap ℚ Kc (x * x') + algebraMap ℚ Kc (y * y') * (sc * sc)
              + (algebraMap ℚ Kc (x * y') + algebraMap ℚ Kc (y * x')) * sc := by
          simp only [map_add, map_mul]
          ring
        rw [key, sc_sq]
        simp only [map_add, map_mul]
        ring
      one_mem' := ⟨1, 0, by simp⟩
      algebraMap_mem' := by
        intro r
        exact ⟨r, 0, by simp⟩ }
  have hle : Algebra.adjoin ℚ ({sc} : Set Kc) ≤ T := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨0, 1, by simp⟩
  exact hle (by rw [adjoin_sc_eq_top]; trivial)

/-- **`√-d` is an algebraic integer.**  It is a root of the monic polynomial `X² + d`. -/
theorem isIntegral_sc : IsIntegral ℤ sc := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (dWit : ℤ), ?_, ?_⟩
  · monicity!
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [pow_two, sc_sq_num]
    norm_num

/-- The generator as an element of the ring of integers. -/
def scR : 𝓞 Kc := ⟨sc, isIntegral_sc⟩

@[simp] theorem scR_coe : ((scR : 𝓞 Kc) : Kc) = sc := rfl

/-- The five odd primes dividing `dWit = 30030 = 2·3·5·7·11·13` that are used as the
classes of order `2` in the class group of the witness field. -/
def certPrime : Fin 5 → ℕ := ![3, 5, 7, 11, 13]

theorem certPrime_prime (i : Fin 5) : (certPrime i).Prime := by
  fin_cases i <;> decide

theorem certPrime_dvd (i : Fin 5) : certPrime i ∣ dWit := by
  fin_cases i <;> decide

theorem certPrime_odd (i : Fin 5) : Odd (certPrime i) := by
  fin_cases i <;> decide

theorem certPrime_two_le (i : Fin 5) : 2 < certPrime i := by
  fin_cases i <;> decide

theorem certPrime_injective : Function.Injective certPrime := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [certPrime]

theorem certPrime_ne_two (i : Fin 5) : certPrime i ≠ 2 := by
  have := certPrime_two_le i; omega

/-- The product of all five certificate primes is `dWit / 2 = 15015`, in particular less than
`dWit`; this is what makes the norm form argument work for every nonempty subset. -/
theorem certPrime_prod_lt : (∏ i : Fin 5, certPrime i) < dWit := by
  decide

/-- Any nonempty product of certificate primes is at most `15015 < 30030`. -/
theorem certPrime_finset_prod_lt (T : Finset (Fin 5)) (hT : T.Nonempty) :
    (∏ i ∈ T, certPrime i) < dWit := by
  have h1 : (∏ i ∈ T, certPrime i) ≤ ∏ i : Fin 5, certPrime i := by
    refine Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ T) ?_
    intro i _ hi
    have := certPrime_two_le i
    omega
  exact lt_of_le_of_lt h1 certPrime_prod_lt

/-- The product of the primes in a nonempty subset is `> 1`. -/
theorem certPrime_finset_prod_gt_one (T : Finset (Fin 5)) (hT : T.Nonempty) :
    1 < (∏ i ∈ T, certPrime i) := by
  obtain ⟨i, hi⟩ := hT
  have h1 : certPrime i ≤ ∏ j ∈ T, certPrime j :=
    Finset.single_le_prod (fun j _ => (certPrime_prime j).one_le) hi
  have h2 : 2 < certPrime i := certPrime_two_le i
  omega

/-- `scR ^ 2 = -30030` in the ring of integers. -/
theorem scR_sq : scR * scR = -(30030 : 𝓞 Kc) := by
  apply Subtype.ext
  show ((scR : Kc) * (scR : Kc)) = ((-(30030 : 𝓞 Kc)) : Kc)
  rw [scR_coe, sc_sq_num]
  rfl

/-- `dWit = 2 · 3 · 5 · 7 · 11 · 13`. -/
theorem dWit_eq : dWit = 2 * 3 * 5 * 7 * 11 * 13 := rfl

/-- The product of the five certificate primes is `dWit / 2`. -/
theorem dWit_eq_two_mul_prod : dWit = 2 * ∏ i : Fin 5, certPrime i := by
  decide

end

end Work.ClassFieldTower
