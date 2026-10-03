import Mathlib
import Submission.Work.FIArea4.pv_primitive
import Submission.Work.FIArea4.sum_coprime_mul_eq
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

set_option linter.style.haveILetI false

open Finset

noncomputable section

/-- **Pointwise reduction of an imprimitive character to its primitive character.**
For a Dirichlet character `χ` of level `N` and `n : ℕ`, the value `χ n` is `0` unless `(n,N) = 1`,
and in the coprime case it equals the value of the primitive character `χ.primitiveCharacter` of
level `χ.conductor` at `n`. -/
lemma eval_eq_primitiveCharacter {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) :
    χ (n : ZMod N)
      = if n.gcd N = 1 then χ.primitiveCharacter (n : ZMod χ.conductor) else 0 := by
  rw [show (n : ZMod N) = ((n : ℤ) : ZMod N) from (Int.cast_natCast n).symm,
    show (n : ZMod χ.conductor) = ((n : ℤ) : ZMod χ.conductor) from (Int.cast_natCast n).symm]
  by_cases h : n.gcd N = 1
  · rw [if_pos h]
    exact (DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ
      (Nat.isCoprime_iff_coprime.mpr h)).symm
  · rw [if_neg h]
    exact (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
      (by rwa [Nat.isCoprime_iff_coprime])

/-- The partial sum of an imprimitive character equals the partial sum of its primitive
character restricted to the integers coprime to the level. -/
lemma sum_chi_eq_sum_coprime_primitive {N X : ℕ} (χ : DirichletCharacter ℂ N) :
    ∑ n ∈ Finset.Icc 1 X, χ (n : ZMod N)
      = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n.gcd N = 1),
          χ.primitiveCharacter (n : ZMod χ.conductor) := by
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => eval_eq_primitiveCharacter χ n

/-- **Counting the squarefree divisors of `rad N` that are coprime to `d`** (`d ∣ N`).
Every such divisor `e` divides `N = d · (N/d)` and is coprime to `d`, hence divides `N/d`; so the
set is contained in `(N/d).divisors`. -/
lemma card_filter_divisors_coprime_le {N d : ℕ} (hN : N ≠ 0) (hdvd : d ∣ N) :
    ((∏ p ∈ N.primeFactors, p).divisors.filter (fun e => e.gcd d = 1)).card
      ≤ (N / d).divisors.card := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hNpos
  have hk : N / d ≠ 0 := by
    have : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hNpos hdvd) hdpos
    omega
  refine Finset.card_le_card ?_
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨heR, hecop⟩ := he
  rw [Nat.mem_divisors] at heR
  obtain ⟨heRdvd, -⟩ := heR
  refine Nat.mem_divisors.mpr ⟨?_, hk⟩
  have heN : e ∣ N := heRdvd.trans (Nat.prod_primeFactors_dvd N)
  have hNd : N = d * (N / d) := (Nat.mul_div_cancel' hdvd).symm
  exact Nat.Coprime.dvd_of_dvd_mul_left hecop (by rw [← hNd]; exact heN)

/-- **Pólya–Vinogradov for an arbitrary non-principal Dirichlet character.**  For a Dirichlet
character `χ` of level `N` whose conductor is `> 1` (i.e. `χ` is not the principal character),

  `‖Σ_{n ≤ X} χ(n)‖ ≤ C √N (log N + 1)`.

The intended proof: reduce to the primitive character `χ.primitiveCharacter` of level
`d = χ.conductor` (`DirichletCharacter.changeLevel_primitiveCharacter`), sieve the coprimality
condition `(n, N) = 1` by Möbius over the divisors of `rad N`
(`changeLevel_eq_cast_of_dvd'` gives `χ n = χ.primitiveCharacter n` for `(n,N)=1`), note that the
terms with `gcd(e, d) > 1` vanish (a non-unit of `ZMod d`), and bound the remaining
`≤ 2 ^ (N/d).primeFactors.card ≤ 2 * √(N/d)` sums with `pv_primitive`, which gives `≪ 4 √d log d`
for each.  Altogether `≪ 2√(N/d) · 4√d log d = 8√N log d ≤ 8√N log N`. -/
theorem pv_dirichlet :
    ∃ C : ℝ, 0 < C ∧ ∀ (N X : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < χ.conductor →
      ‖∑ n ∈ Finset.Icc 1 X, χ (n : ZMod N)‖ ≤ C * Real.sqrt N * (Real.log N + 1) := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1 / 2) (by norm_num)
  refine ⟨4 * C₀ + 1, by linarith, ?_⟩
  intro N X hN χ hcond
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hDvd : χ.conductor ∣ N := DirichletCharacter.conductor_dvd_level χ
  have hD2 : 2 ≤ χ.conductor := by omega
  have hDpos : (0 : ℝ) < (χ.conductor : ℝ) := by
    exact_mod_cast (show 0 < χ.conductor by omega)
  have hlogD : 0 ≤ Real.log (χ.conductor : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ χ.conductor by omega))
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hbd : ∀ a : ZMod χ.conductor, ‖χ.primitiveCharacter a‖ ≤ 1 :=
    fun a => DirichletCharacter.norm_le_one _ a
  have hpv : ∀ Y : ℕ,
      ‖∑ m ∈ Finset.Icc 1 Y, χ.primitiveCharacter (m : ZMod χ.conductor)‖
        ≤ 4 * Real.sqrt (χ.conductor : ℝ) * (Real.log (χ.conductor : ℝ) + 1) :=
    fun Y => pv_primitive χ.primitiveCharacter hprim hD2 hbd Y
  set B : ℝ := 4 * Real.sqrt (χ.conductor : ℝ) * (Real.log (χ.conductor : ℝ) + 1) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by linarith)
  -- Möbius sieve
  have hsieve : ∑ n ∈ Finset.Icc 1 X, χ (n : ZMod N)
      = ∑ e ∈ (∏ p ∈ N.primeFactors, p).divisors,
          (ArithmeticFunction.moebius e : ℂ) * χ.primitiveCharacter (e : ZMod χ.conductor)
            * ∑ m ∈ Finset.Icc 1 (X / e), χ.primitiveCharacter (m : ZMod χ.conductor) := by
    rw [sum_chi_eq_sum_coprime_primitive χ]
    exact sum_coprime_mul_eq (c := N) (N := X) (NeZero.ne N)
      (fun n => χ.primitiveCharacter (n : ZMod χ.conductor))
      (by simp)
      (fun a b => by rw [Nat.cast_mul, map_mul])
  -- per-term bound
  have hterm : ∀ e ∈ (∏ p ∈ N.primeFactors, p).divisors,
      ‖(ArithmeticFunction.moebius e : ℂ) * χ.primitiveCharacter (e : ZMod χ.conductor)
          * ∑ m ∈ Finset.Icc 1 (X / e), χ.primitiveCharacter (m : ZMod χ.conductor)‖
        ≤ (if e.gcd χ.conductor = 1 then B else 0) := by
    intro e _
    by_cases hc : e.gcd χ.conductor = 1
    · rw [if_pos hc]
      have h1 : ‖(ArithmeticFunction.moebius e : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        have := ArithmeticFunction.abs_moebius_le_one (n := e)
        exact_mod_cast this
      have h2 : ‖χ.primitiveCharacter (e : ZMod χ.conductor)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one _ _
      have h3 : ‖∑ m ∈ Finset.Icc 1 (X / e), χ.primitiveCharacter (m : ZMod χ.conductor)‖
          ≤ B := by rw [hBdef]; exact hpv (X / e)
      calc ‖(ArithmeticFunction.moebius e : ℂ) * χ.primitiveCharacter (e : ZMod χ.conductor)
            * ∑ m ∈ Finset.Icc 1 (X / e), χ.primitiveCharacter (m : ZMod χ.conductor)‖
          = ‖(ArithmeticFunction.moebius e : ℂ)‖ * ‖χ.primitiveCharacter (e : ZMod χ.conductor)‖
              * ‖∑ m ∈ Finset.Icc 1 (X / e), χ.primitiveCharacter (m : ZMod χ.conductor)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 * B :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _)
              (by norm_num)
        _ = B := by ring
    · rw [if_neg hc]
      have hψe : χ.primitiveCharacter (e : ZMod χ.conductor) = 0 := by
        rw [show (e : ZMod χ.conductor)
            = ((e : ℤ) : ZMod χ.conductor) from (Int.cast_natCast e).symm]
        exact (DirichletCharacter.apply_eq_zero_iff χ.primitiveCharacter (e : ℤ)).mpr
          (by rwa [Nat.isCoprime_iff_coprime])
      rw [hψe]
      simp
  -- cardinality of the surviving set of `e`
  have hcard : (((∏ p ∈ N.primeFactors, p).divisors.filter
      (fun e => e.gcd χ.conductor = 1)).card : ℝ)
      ≤ C₀ * Real.sqrt ((N / χ.conductor : ℕ) : ℝ) := by
    have h1 : ((∏ p ∈ N.primeFactors, p).divisors.filter
        (fun e => e.gcd χ.conductor = 1)).card ≤ (N / χ.conductor).divisors.card :=
      card_filter_divisors_coprime_le (NeZero.ne N) hDvd
    have h1' : (((∏ p ∈ N.primeFactors, p).divisors.filter
        (fun e => e.gcd χ.conductor = 1)).card : ℝ)
        ≤ ((N / χ.conductor).divisors.card : ℝ) := by exact_mod_cast h1
    have h2 := hC₀ (N / χ.conductor)
    rw [← Real.sqrt_eq_rpow] at h2
    exact le_trans h1' h2
  -- square-root identity `√(N/d)·√d = √N`
  have hsq : Real.sqrt ((N / χ.conductor : ℕ) : ℝ) * Real.sqrt (χ.conductor : ℝ)
      = Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    rw [← Nat.cast_mul, Nat.div_mul_cancel hDvd]
  have hlogle : Real.log (χ.conductor : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hDpos
      (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hDvd)
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by have := NeZero.ne N; omega))
  calc ‖∑ n ∈ Finset.Icc 1 X, χ (n : ZMod N)‖
      = ‖∑ e ∈ (∏ p ∈ N.primeFactors, p).divisors,
          (ArithmeticFunction.moebius e : ℂ) * χ.primitiveCharacter (e : ZMod χ.conductor)
            * ∑ m ∈ Finset.Icc 1 (X / e), χ.primitiveCharacter (m : ZMod χ.conductor)‖ := by
        rw [hsieve]
    _ ≤ ∑ e ∈ (∏ p ∈ N.primeFactors, p).divisors,
          ‖(ArithmeticFunction.moebius e : ℂ) * χ.primitiveCharacter (e : ZMod χ.conductor)
            * ∑ m ∈ Finset.Icc 1 (X / e), χ.primitiveCharacter (m : ZMod χ.conductor)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ e ∈ (∏ p ∈ N.primeFactors, p).divisors,
          (if e.gcd χ.conductor = 1 then B else 0) := Finset.sum_le_sum hterm
    _ = (((∏ p ∈ N.primeFactors, p).divisors.filter
          (fun e => e.gcd χ.conductor = 1)).card : ℝ) * B := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C₀ * Real.sqrt ((N / χ.conductor : ℕ) : ℝ)) * B :=
        mul_le_mul_of_nonneg_right hcard hBnn
    _ = 4 * C₀ * Real.sqrt N * (Real.log (χ.conductor : ℝ) + 1) := by
        rw [hBdef]
        calc (C₀ * Real.sqrt ((N / χ.conductor : ℕ) : ℝ))
              * (4 * Real.sqrt (χ.conductor : ℝ) * (Real.log (χ.conductor : ℝ) + 1))
            = 4 * C₀ * (Real.sqrt ((N / χ.conductor : ℕ) : ℝ) * Real.sqrt (χ.conductor : ℝ))
                * (Real.log (χ.conductor : ℝ) + 1) := by ring
          _ = 4 * C₀ * Real.sqrt (N : ℝ) * (Real.log (χ.conductor : ℝ) + 1) := by rw [hsq]
    _ ≤ 4 * C₀ * Real.sqrt N * (Real.log N + 1) := by
        have h4 : (0 : ℝ) ≤ 4 * C₀ * Real.sqrt N :=
          mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC₀pos)) (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (by linarith) h4
    _ ≤ (4 * C₀ + 1) * Real.sqrt N * (Real.log N + 1) := by
        have h1 : (0 : ℝ) ≤ Real.sqrt N * (Real.log N + 1) :=
          mul_nonneg (Real.sqrt_nonneg _) (by linarith)
        calc 4 * C₀ * Real.sqrt N * (Real.log N + 1)
            = (4 * C₀) * (Real.sqrt N * (Real.log N + 1)) := by ring
          _ ≤ (4 * C₀ + 1) * (Real.sqrt N * (Real.log N + 1)) :=
              mul_le_mul_of_nonneg_right (by linarith) h1
          _ = (4 * C₀ + 1) * Real.sqrt N * (Real.log N + 1) := by ring

end

end Work.FIArea4
