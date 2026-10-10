import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.CensusASGen
import Submission.Work.MotAS.censusAS_sAS_ne_zero
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
set_option maxHeartbeats 8000000

namespace Work.MotAS.ASRulV2M

open MvPolynomial
open Work.MotAS

/-!
# `Work.MotAS.ASRulV2M.aeval_sAS_eq_zero_imp`

The `(X₀, X₂) = 0` specialisation `Ψ` of the AS source ruling quintic `sAS a b g`
(`Ψ = MvPolynomial.aeval ![0, X, 0]`, the linear functional that extracts the coefficient of the
monomial `X₁ ^ 10`) can vanish only on the singular locus `a ^ 2 - a * b - b ^ 2 = 0` of the AS
quadric.  Equivalently: the `X ^ 10`-coefficient of `Ψ (sAS a b g)` is `288 ^ 5 (a²-ab-b²)^10` in
characteristic `5`.

The proof is the general-field version of the computation carried out in
`Submission/Work/MotAS/censusAS_sAS_ne_zero.lean` for the census data: the specialisation of the
stereographic vector is the sparse vector `![Y0, 0, Y2, 0, Y4]`, the `X ^ 10`-coefficient of the
sparse evaluation of `kleinSecAS` is `(-(a^10) + a^5 b^5 + b^10) * (Y0.coeff 2)^5`
(`Work.MotAS.coeff_ten_sparse`), and `Y0.coeff 2 = 288 · (-(a²-ab-b²))`; Frobenius in
characteristic `5` turns `a^10 - a^5 b^5 - b^10` into `(a²-ab-b²)^5`.
-/

theorem aeval_sAS_eq_zero_imp {K : Type*} [Field K] [CharP K 5] (a b g : K)
    (h : MvPolynomial.aeval (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial K) i)
      (Work.MotAS.sAS a b g) = 0) :
    a ^(2:ℕ) - a * b - b ^(2:ℕ) = 0 := by
  set Ψ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval
      (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial K) i) with hΨdef
  -- the image of the chart vector
  set Y0 : Polynomial K := Polynomial.C (288 : K) *
      (Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ)))) with hY0def
  set Y4 : Polynomial K := (576 : Polynomial K) *
      ((Polynomial.C a) ^(2:ℕ) - Polynomial.C a * Polynomial.C b - (Polynomial.C b) ^(2:ℕ))
      with hY4def
  set Y2 : Polynomial K := Y4 * Polynomial.X with hY2def
  -- the chart coordinates
  have h1c : (Work.MotK.chart3 K) 0 = (0 : MvPolynomial (Fin 3) K) := rfl
  have h2c : (Work.MotK.chart3 K) 1 = MvPolynomial.X 0 := rfl
  have h3c : (Work.MotK.chart3 K) 2 = MvPolynomial.X 1 := rfl
  have h4c : (Work.MotK.chart3 K) 3 = MvPolynomial.X 2 := rfl
  have h5c : (Work.MotK.chart3 K) 4 = (1 : MvPolynomial (Fin 3) K) := rfl
  -- the values of `Ψ` on the chart data
  have hQΨ : Ψ (kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotK.chart3 K))
      = Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ))) := by
    simp only [hΨdef, kleinQAS, h1c, h2c, h3c, h4c, h5c, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, map_zero, map_one, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      ← Polynomial.C_eq_algebraMap]
    simp
    first | refl_ring1 | ring
  have hBΨ : Ψ (kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS K)
        (Work.MotK.chart3 K))
      = -(576 : Polynomial K) * ((Polynomial.C a) ^(2:ℕ) - Polynomial.C a * Polynomial.C b
          - (Polynomial.C b) ^(2:ℕ)) := by
    rw [show kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS K) (Work.MotK.chart3 K)
        = linAS a b from rfl, linAS_eq, hΨdef]
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
  have hvec : (fun i => Ψ (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS K)
        (Work.MotK.chart3 K) i)) = ![Y0, 0, Y2, 0, Y4] := by
    funext i
    fin_cases i <;>
      · simp only [kleinStereoAS, map_mul, map_sub, hpASΨ, hchartΨ, hQΨ, hBΨ, hY0def, hY2def,
          hY4def] <;> simp <;> ring
  -- the transport of `kleinSecAS` along `Ψ`
  have hCΨ : ∀ x : K, Ψ (MvPolynomial.C x) = Polynomial.C x := by
    intro x
    rw [hΨdef, MvPolynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
  have hΨ : Ψ (Work.MotAS.sAS a b g)
      = kleinSecAS (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun i => ![Y0, 0, Y2, 0, Y4] i) := by
    rw [show Work.MotAS.sAS a b g
        = kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS K)
              (Work.MotK.chart3 K)) from rfl]
    change (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K)
        (kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS K)
            (Work.MotK.chart3 K)))
      = kleinSecAS (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun i => ![Y0, 0, Y2, 0, Y4] i)
    rw [map_kleinSecAS (φ := (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K))]
    have hCa : (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K) (MvPolynomial.C a)
        = Polynomial.C a := hCΨ a
    have hCb : (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K) (MvPolynomial.C b)
        = Polynomial.C b := hCΨ b
    have hCg : (Ψ : MvPolynomial (Fin 3) K →+* Polynomial K) (MvPolynomial.C g)
        = Polynomial.C g := hCΨ g
    rw [hCa, hCb, hCg]
    change kleinSecAS (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
        (fun i => Ψ (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS K)
          (Work.MotK.chart3 K) i))
      = kleinSecAS (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
          (fun i => ![Y0, 0, Y2, 0, Y4] i)
    rw [hvec]
  have hΨh : Ψ (Work.MotAS.sAS a b g) = 0 := by
    rw [hΨdef]
    exact h
  have hzero : kleinSecAS (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
      (fun i => ![Y0, 0, Y2, 0, Y4] i) = 0 := by
    rw [← hΨ, hΨh]
  -- degree bounds
  have hY0deg : Y0.natDegree ≤ 2 := by
    rw [hY0def]
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    have hA : (Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        ).natDegree ≤ 2 :=
      le_trans (Polynomial.natDegree_C_mul_le _ _)
        (by simpa using Polynomial.natDegree_X_pow_le 2)
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
    have h2 : (Polynomial.X : Polynomial K).natDegree ≤ 1 := Polynomial.natDegree_X_le
    omega
  -- the coefficient of `X^10`
  have hcoeff := coeff_ten_sparse a b g Y0 Y2 Y4 hY0deg hY2deg hY4deg
  have hthis : ((-(a ^(10:ℕ)) + a ^(5:ℕ) * b ^(5:ℕ) + b ^(10:ℕ)) * (Y0.coeff 2) ^(5:ℕ) : K) = 0 := by
    rw [← hcoeff, hzero, Polynomial.coeff_zero]
  have hY0c2 : Y0.coeff 2 = (288 : K) * (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) := by
    rw [hY0def, Polynomial.coeff_C_mul]
    have hq : (Polynomial.C (-(a ^(2:ℕ) - a * b - b ^(2:ℕ))) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-(2 * a ^(2:ℕ) + 2 * b ^(2:ℕ))) * Polynomial.X
        + Polynomial.C (-(2 * a ^(2:ℕ) - a * b - 2 * b ^(2:ℕ)))).coeff 2
        = -(a ^(2:ℕ) - a * b - b ^(2:ℕ)) := by
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    rw [hq]
  have h288 : (288 : K) ≠ 0 := by
    show ((288 : ℕ) : K) ≠ 0
    have h1 : ((288 : ℕ) : K) = ((3 : ℕ) : K) := by
      rw [show (288 : ℕ) = 5 * 57 + 3 from by norm_num, Nat.cast_add, Nat.cast_mul,
        CharP.cast_eq_zero K 5, zero_mul, zero_add]
    rw [h1]
    intro h3
    have hdiv : 5 ∣ 3 := (CharP.cast_eq_zero_iff K 5 3).mp h3
    norm_num at hdiv
  have hfrob : a ^(10:ℕ) - a ^(5:ℕ) * b ^(5:ℕ) - b ^(10:ℕ) = (a ^(2:ℕ) - a * b - b ^(2:ℕ)) ^(5:ℕ) := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hA := sub_pow_char_pow (a ^(2:ℕ) - a * b) (b ^(2:ℕ)) 1
    have hB := sub_pow_char_pow (a ^(2:ℕ)) (a * b) 1
    simp only [pow_one] at hA hB
    rw [hA, hB]
    first | refl_ring1 | ring
  have hneg : (-(a ^(10:ℕ)) + a ^(5:ℕ) * b ^(5:ℕ) + b ^(10:ℕ))
      = -((a ^(10:ℕ)) - a ^(5:ℕ) * b ^(5:ℕ) - b ^(10:ℕ)) := by ring
  have hval : (-(a ^(10:ℕ)) + a ^(5:ℕ) * b ^(5:ℕ) + b ^(10:ℕ))
      * ((288 : K) * (-(a ^(2:ℕ) - a * b - b ^(2:ℕ)))) ^(5:ℕ)
      = (288 : K) ^(5:ℕ) * (a ^(2:ℕ) - a * b - b ^(2:ℕ)) ^(10:ℕ) := by
    rw [hneg, hfrob]
    first | refl_ring1 | ring
  rw [hY0c2] at hthis
  rw [hval] at hthis
  rcases mul_eq_zero.mp hthis with h1 | h1
  · exact absurd h1 (pow_ne_zero 5 h288)
  · exact (pow_eq_zero_iff (by norm_num : (10 : ℕ) ≠ 0)).mp h1

end Work.MotAS.ASRulV2M
