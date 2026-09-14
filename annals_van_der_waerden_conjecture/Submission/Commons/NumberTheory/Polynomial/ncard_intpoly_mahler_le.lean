import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Int.Star

namespace Commons.NumberTheory.Polynomial

open Finset

/-- The coercion `ℤ → ℂ` is an isometry for the usual norms (`|·|` on `ℤ` and the
complex absolute value on `ℂ`). -/
theorem isometry_intCastRingHom_complex : Isometry (Int.castRingHom ℂ) :=
  (AddMonoidHomClass.isometry_iff_norm (Int.castRingHom ℂ)).mpr
    (fun n => by simp [Int.norm_eq_abs])

/-- **Coefficient bound from the Mahler measure.** Every coefficient of an integer polynomial `f`
is bounded by `2 ^ f.natDegree` times its Mahler measure. This is Mathlib's Mignotte-type bound
`Polynomial.norm_coeff_le_choose_mul_mapMahlerMeasure` combined with the estimate
`natDegree.choose i ≤ 2 ^ natDegree`. -/
theorem coeff_abs_le_two_pow_natDegree_mul_mapMahlerMeasure (f : Polynomial ℤ) (i : ℕ) :
    |((f.coeff i : ℤ) : ℝ)| ≤ 2 ^ f.natDegree * f.mapMahlerMeasure (Int.castRingHom ℂ) := by
  have h := Polynomial.norm_coeff_le_choose_mul_mapMahlerMeasure (Int.castRingHom ℂ)
    isometry_intCastRingHom_complex i f
  rw [Int.norm_eq_abs] at h
  refine h.trans ?_
  have hch : ((f.natDegree.choose i : ℕ) : ℝ) ≤ 2 ^ f.natDegree := by
    exact_mod_cast Nat.choose_le_two_pow f.natDegree i
  have hM : 0 ≤ f.mapMahlerMeasure (Int.castRingHom ℂ) :=
    Polynomial.mapMahlerMeasure_nonneg f _
  exact mul_le_mul_of_nonneg_right hch hM

/-- **Counting integer polynomials with bounded coefficients.** A set `s` of integer polynomials,
all of degree at most `m` and with all coefficients of index `≤ m` bounded in absolute value
by a nonnegative real number `B`, has at most `(2 * B + 1) ^ (m + 1)` elements.

Indeed a polynomial of degree at most `m` is determined by its coefficients in degrees
`0, …, m`, and each of these takes at most `2 * B + 1` values (at most `2 * ⌊B⌋ + 1`, which is
at most `2 * B + 1`, integers of absolute value at most `B`). -/
theorem ncard_intpoly_le_of_coeff_le {m : ℕ} {B : ℝ} (hB : 0 ≤ B) {s : Set (Polynomial ℤ)}
    (hdeg : ∀ f ∈ s, f.natDegree ≤ m)
    (hcoeff : ∀ f ∈ s, ∀ i ≤ m, |((f.coeff i : ℤ) : ℝ)| ≤ B) :
    ((s.ncard : ℕ) : ℝ) ≤ (2 * B + 1) ^ (m + 1) := by
  classical
  set C : Finset ℤ := Finset.Icc (-(⌊B⌋)) ⌊B⌋ with hC
  have hsub : ∀ f ∈ s, (fun i : Fin (m + 1) => f.coeff (i : ℕ)) ∈
      (↑(Fintype.piFinset (fun _ : Fin (m + 1) => C)) : Set (Fin (m + 1) → ℤ)) := by
    intro f hf
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [hC, Finset.mem_Icc]
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.isLt
    obtain ⟨h1, h2⟩ := abs_le.mp (hcoeff f hf (i : ℕ) hi)
    refine ⟨?_, Int.le_floor.mpr h2⟩
    have hthis : ((-(f.coeff (i : ℕ)) : ℤ) : ℝ) ≤ B := by
      have : -(f.coeff (i : ℕ) : ℝ) ≤ B := by linarith
      simpa using this
    have h3 := Int.le_floor.mpr hthis
    linarith
  have hinj : Set.InjOn (fun f : Polynomial ℤ => fun i : Fin (m + 1) => f.coeff (i : ℕ)) s := by
    intro f hf g hg heq
    ext k
    by_cases hk : k ≤ m
    · have := congrFun heq ⟨k, Nat.lt_succ_of_le hk⟩
      simpa using this
    · push Not at hk
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt
          (Nat.lt_of_le_of_lt (hdeg f hf) hk)).trans
        (Polynomial.coeff_eq_zero_of_natDegree_lt
          (Nat.lt_of_le_of_lt (hdeg g hg) hk)).symm
  have hle : s.ncard ≤ (Fintype.piFinset (fun _ : Fin (m + 1) => C)).card := by
    have := Set.ncard_le_ncard_of_injOn (s := s)
      (fun f : Polynomial ℤ => fun i : Fin (m + 1) => f.coeff (i : ℕ)) hsub hinj
    rwa [Set.ncard_coe_finset] at this
  have hcardC : ((C.card : ℕ) : ℝ) ≤ 2 * B + 1 := by
    have hK1 : -(⌊B⌋) ≤ ⌊B⌋ + 1 := by
      have := Int.floor_nonneg.mpr hB; omega
    have h1 : ((C.card : ℕ) : ℤ) = 2 * ⌊B⌋ + 1 := by
      rw [hC, Int.card_Icc_of_le (-(⌊B⌋)) (⌊B⌋) hK1]; ring
    have h2 : ((C.card : ℕ) : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by exact_mod_cast h1
    rw [h2]
    have hf : (⌊B⌋ : ℝ) ≤ B := Int.floor_le _
    linarith
  calc ((s.ncard : ℕ) : ℝ)
      ≤ ((Fintype.piFinset (fun _ : Fin (m + 1) => C)).card : ℝ) := by exact_mod_cast hle
    _ = ((C.card : ℕ) : ℝ) ^ (m + 1) := by
        rw [Fintype.card_piFinset]; push_cast
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (2 * B + 1) ^ (m + 1) := pow_le_pow_left₀ (by positivity) hcardC _

/-- The set of integer polynomials of degree exactly `m` whose Mahler measure (as a complex
polynomial, via `ℤ → ℂ`) is at most `S ≥ 1` has at most `(2 ^ (m + 1) * S + 1) ^ (m + 1)`
elements. -/
theorem ncard_intpoly_mahler_le (m : ℕ) (S : ℝ) (hS : 1 ≤ S) :
    (({f : Polynomial ℤ | f.natDegree = m ∧ Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ S} : Set (Polynomial ℤ)).ncard : ℝ)
      ≤ ((2 : ℝ) ^ (m + 1) * S + 1) ^ (m + 1) := by
  classical
  have hS0 : (0 : ℝ) ≤ S := le_trans zero_le_one hS
  have hB : (0 : ℝ) ≤ 2 ^ m * S := by positivity
  have hmain := ncard_intpoly_le_of_coeff_le (m := m) (B := 2 ^ m * S) hB
    (s := {f : Polynomial ℤ | f.natDegree = m ∧ Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ S})
    (fun f hf => le_of_eq hf.1)
    (fun f hf i _ => by
      have h := coeff_abs_le_two_pow_natDegree_mul_mapMahlerMeasure f i
      rw [hf.1] at h
      exact h.trans (mul_le_mul_of_nonneg_left hf.2 (by positivity)))
  refine hmain.trans (le_of_eq ?_)
  congr 1
  rw [pow_succ']
  ring

end Commons.NumberTheory.Polynomial