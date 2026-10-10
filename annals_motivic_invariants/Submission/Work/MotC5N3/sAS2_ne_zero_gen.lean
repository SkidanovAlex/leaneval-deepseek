import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.CensusAS2Aux
import Submission.Work.MotC5N3.sAS2_ne_zero
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Work.MotC5N3

open MvPolynomial
open Work.MotAS

/-!
# `Work.MotC5N3.sAS2_ne_zero_gen`

The source ruling quintic `sAS2 a b g` of the AS chart is nonzero for *arbitrary* coefficients
`a b g` of a field `K` of characteristic `5`, as soon as `a ^ 2 - a * b - b ^ 2 ≠ 0`.

This is the coefficient-generic form of `Submission/Work/MotC5N3/sAS2_ne_zero.lean`
(`Work.MotC5N3.sAS2_ne_zero`, where `a = aK K D`, `b = bK K D` and `g` is arbitrary): the engine
`Work.MotAS.censusAS_sAS_ne_zero` is a computation in the *coefficients* `a, b, g` only — the
`X ^ 10`-coefficient of the sparse evaluation is `(-(a ^ 10) + a ^ 5 * b ^ 5 + b ^ 10) * (Y0.coeff 2) ^ 5`,
independent of the datum `D` — so the whole argument ports verbatim with `aK K D ↦ a`,
`bK K D ↦ b` and hypothesis `aK_sq_sub_ne ↦ ha`.
-/

/-- **The source ruling quintic `sAS` is nonzero** for arbitrary coefficients `(a, b, g)` with
`a ^ 2 - a * b - b ^ 2 ≠ 0`, over any field `K` of characteristic `5`. -/
theorem sAS_gen_ne_zero_arb (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) : sAS a b g ≠ 0 := by
  intro h0
  have hd : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0 := ha
  -- the substitution `X₀ ↦ 0, X₁ ↦ X, X₂ ↦ 0`
  set Ψ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval
      (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial K) i)
    with hΨdef
  -- the image of the chart vector
  set Y0 : Polynomial K := Polynomial.C (288 : K) *
      (Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ)))) with hY0def
  set Y4 : Polynomial K := (576 : Polynomial K) *
      ((Polynomial.C (a)) ^(2:ℕ) - Polynomial.C (a) * Polynomial.C (b)
        - (Polynomial.C (b)) ^(2:ℕ)) with hY4def
  set Y2 : Polynomial K := Y4 * Polynomial.X with hY2def
  -- the values of `Ψ` on the chart data
  have hQΨ : Ψ (kleinQAS (MvPolynomial.C (a)) (MvPolynomial.C (b))
        (Work.MotK.chart3 K))
      = Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ))) := by
    have h1c : (Work.MotK.chart3 K) 0 = (0 : MvPolynomial (Fin 3) K) := rfl
    have h2c : (Work.MotK.chart3 K) 1 = MvPolynomial.X 0 := rfl
    have h3c : (Work.MotK.chart3 K) 2 = MvPolynomial.X 1 := rfl
    have h4c : (Work.MotK.chart3 K) 3 = MvPolynomial.X 2 := rfl
    have h5c : (Work.MotK.chart3 K) 4 = (1 : MvPolynomial (Fin 3) K) := rfl
    simp only [hΨdef, kleinQAS, h1c, h2c, h3c, h4c, h5c, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, map_zero, map_one, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      ← Polynomial.C_eq_algebraMap]
    simp
    first | refl_ring1 | ring
  have hBΨ : Ψ (kleinBilinAS (MvPolynomial.C (a)) (MvPolynomial.C (b))
        (pAS K) (Work.MotK.chart3 K))
      = -(576 : Polynomial K) * ((Polynomial.C (a)) ^(2:ℕ)
          - Polynomial.C (a) * Polynomial.C (b) - (Polynomial.C (b)) ^(2:ℕ)) := by
    rw [show kleinBilinAS (MvPolynomial.C (a)) (MvPolynomial.C (b)) (pAS K)
        (Work.MotK.chart3 K) = linAS (a) (b) from rfl, linAS_eq, hΨdef]
    simp only [map_mul, map_sub, map_pow, map_neg, map_ofNat, MvPolynomial.aeval_C,
      ← Polynomial.C_eq_algebraMap] <;> ring
  have hpASΨ : ∀ i : Fin 5, Ψ (pAS K i)
      = Polynomial.C (if i = 0 then (288 : K) else 0) := by
    intro i
    rw [hΨdef]
    simp only [pAS, MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
  have hchartΨ : ∀ i : Fin 5, Ψ (Work.MotK.chart3 K i)
      = ![0, 0, Polynomial.X, 0, 1] i := by
    intro i
    rw [hΨdef]
    fin_cases i <;> simp [Work.MotK.chart3, MvPolynomial.aeval_X]
  have hvec : (fun i => Ψ (kleinStereoAS (MvPolynomial.C (a)) (MvPolynomial.C (b))
        (pAS K) (Work.MotK.chart3 K) i)) = ![Y0, 0, Y2, 0, Y4] := by
    funext i
    fin_cases i <;>
      · simp only [kleinStereoAS, map_mul, map_sub, hpASΨ, hchartΨ, hQΨ, hBΨ, hY0def, hY2def,
          hY4def] <;> simp <;> ring
  -- the transport of `kleinSecAS` along `Ψ`
  have hΨ : Ψ (sAS (a) (b) g)
      = kleinSecAS (Polynomial.C (a)) (Polynomial.C (b)) (Polynomial.C g)
          (fun i => ![Y0, 0, Y2, 0, Y4] i) := by
    rw [show sAS (a) (b) g
        = kleinSecAS (MvPolynomial.C (a)) (MvPolynomial.C (b))
            (MvPolynomial.C g)
            (kleinStereoAS (MvPolynomial.C (a)) (MvPolynomial.C (b)) (pAS K)
              (Work.MotK.chart3 K)) from rfl]
    change (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K)
        (kleinSecAS (MvPolynomial.C (a)) (MvPolynomial.C (b))
          (MvPolynomial.C g)
          (kleinStereoAS (MvPolynomial.C (a)) (MvPolynomial.C (b)) (pAS K)
            (Work.MotK.chart3 K)))
      = kleinSecAS (Polynomial.C (a)) (Polynomial.C (b)) (Polynomial.C g)
          (fun i => ![Y0, 0, Y2, 0, Y4] i)
    rw [map_kleinSecAS (φ := (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K))]
    have hCa : (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K)
        (MvPolynomial.C (a)) = Polynomial.C (a) := by
      rw [hΨdef]
      show (MvPolynomial.aeval
          (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial K) i))
          (MvPolynomial.C (a)) = Polynomial.C (a)
      rw [MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
    have hCb : (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K)
        (MvPolynomial.C (b)) = Polynomial.C (b) := by
      rw [hΨdef]
      show (MvPolynomial.aeval
          (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial K) i))
          (MvPolynomial.C (b)) = Polynomial.C (b)
      rw [MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
    have hCg : (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K)
        (MvPolynomial.C g) = Polynomial.C g := by
      rw [hΨdef]
      show (MvPolynomial.aeval
          (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial K) i))
          (MvPolynomial.C g) = Polynomial.C g
      rw [MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
    rw [hCa, hCb, hCg]
    change kleinSecAS (Polynomial.C (a)) (Polynomial.C (b)) (Polynomial.C g)
        (fun i => Ψ (kleinStereoAS (MvPolynomial.C (a)) (MvPolynomial.C (b))
          (pAS K) (Work.MotK.chart3 K) i))
      = kleinSecAS (Polynomial.C (a)) (Polynomial.C (b)) (Polynomial.C g)
          (fun i => ![Y0, 0, Y2, 0, Y4] i)
    rw [hvec]
  have hzero : kleinSecAS (Polynomial.C (a)) (Polynomial.C (b)) (Polynomial.C g)
      (fun i => ![Y0, 0, Y2, 0, Y4] i) = 0 := by
    rw [← hΨ, h0, map_zero]
  -- degree bounds
  have hY0deg : Y0.natDegree ≤ 2 := by
    rw [hY0def]
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    have hA : (Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        ).natDegree ≤ 2 :=
      le_trans (Polynomial.natDegree_C_mul_le _ _) (by simpa using Polynomial.natDegree_X_pow_le 2)
    have hB : (Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X).natDegree ≤ 2 :=
      le_trans (le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le)
        (by norm_num)
    have hC : (Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ)))).natDegree ≤ 2 :=
      le_trans (le_of_eq (Polynomial.natDegree_C _)) (by norm_num)
    calc (Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
          + Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X
          + Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ)))).natDegree
        ≤ max (Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
            + Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X).natDegree
            (Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ)))).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ 2 := max_le (le_trans (Polynomial.natDegree_add_le _ _) (max_le hA hB)) hC
  have hY4deg : Y4.natDegree ≤ 0 := by
    rw [hY4def]
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [← Polynomial.C_mul, ← Polynomial.C_pow, ← Polynomial.C_add, ← Polynomial.C_sub,
      ← Polynomial.C_neg, ← Polynomial.C_ofNat, Polynomial.coeff_C]
    simp [hN.ne']
  have hY2deg : Y2.natDegree ≤ 1 := by
    rw [hY2def]
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 : Y4.natDegree ≤ 0 := hY4deg
    have h2 : (Polynomial.X : Polynomial K).natDegree ≤ 1 := Polynomial.natDegree_X_le
    omega
  -- the coefficient of `X^10`
  have hcoeff := coeff_ten_sparse (a) (b) g Y0 Y2 Y4 hY0deg hY2deg hY4deg
  have hthis : ((-(a ^(10:ℕ)) + (a) ^(5:ℕ) * (b) ^(5:ℕ) + (b) ^(10:ℕ)) * (Y0.coeff 2) ^(5:ℕ)
      : K) = 0 := by
    rw [← hcoeff, hzero, Polynomial.coeff_zero]
  have hY0c2 : Y0.coeff 2
      = (288 : K) * (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) := by
    rw [hY0def, Polynomial.coeff_C_mul]
    have hq : (Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ)))).coeff 2
        = -(a ^(2:ℕ) - a * b - b ^(2:ℕ)) := by
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    rw [hq]
  -- the final contradiction
  have h288 : (288 : K) ≠ 0 := by
    have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    have h3 : (288 : K) = 3 := by linear_combination (57 : K) * h5
    rw [h3]
    intro h
    have h53 : (5 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 5 3).mp h
    norm_num at h53
  have hfrob : (a) ^(10:ℕ) - (a) ^(5:ℕ) * (b) ^(5:ℕ) - (b) ^(10:ℕ)
      = (a ^(2:ℕ) - a * b - b ^(2:ℕ)) ^(5:ℕ) := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hA := sub_pow_char_pow (a ^(2:ℕ) - a * b) (b ^(2:ℕ)) 1
    have hB := sub_pow_char_pow (a ^(2:ℕ)) (a * b) 1
    simp only [pow_one] at hA hB
    rw [hA, hB]
    first | refl_ring1 | ring
  rw [hY0c2] at hthis
  have hneg : (-(a ^(10:ℕ)) + (a) ^(5:ℕ) * (b) ^(5:ℕ) + (b) ^(10:ℕ))
      = -((a) ^(10:ℕ) - (a) ^(5:ℕ) * (b) ^(5:ℕ) - (b) ^(10:ℕ)) := by ring
  have hval : (-(a ^(10:ℕ)) + (a) ^(5:ℕ) * (b) ^(5:ℕ) + (b) ^(10:ℕ))
      * ((288 : K) * (-(a ^(2:ℕ) - a * b - b ^(2:ℕ)))) ^(5:ℕ)
      = (288 : K) ^(5:ℕ) * (a ^(2:ℕ) - a * b - b ^(2:ℕ)) ^(10:ℕ) := by
    rw [hneg, hfrob]
    first | refl_ring1 | ring
  rw [hval] at hthis
  exact (mul_ne_zero (pow_ne_zero 5 h288) (pow_ne_zero 10 hd)) hthis

/-- **The source ruling quintic of the AS chart is a non-zero polynomial** for arbitrary
coefficients `a b g : K` (a field of characteristic `5`) with `a ^ 2 - a * b - b ^ 2 ≠ 0`.

It differs from `sAS` by the unit constant `288 ^ 5 = 3` (`Work.MotAS.sAS_eq_scale`). -/
theorem sAS2_ne_zero_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    Work.MotAS.sAS2 a b g ≠ 0 := by
  intro h0
  exact sAS_gen_ne_zero_arb K a b g ha
    (by rw [Work.MotAS.sAS_eq_scale, h0, mul_zero])

end Work.MotC5N3
