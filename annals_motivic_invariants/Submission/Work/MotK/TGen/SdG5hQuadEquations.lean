import Mathlib
import Submission.Work.MotK.TGen.CruxAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.SdG5hQuadEquations` — a monic quadratic factor forces the six equations

Writing the monic homogeneous quadratic factor of `Gg` as `quadF p q r s t = x₀² + Bx₀ + C` with
`B = px₁+qx₂`, `C = rx₁²+sx₁x₂+tx₂²`, the synthetic division (`division_identity`)

`Gg - (R₁ x₀ + R₀) = quadF · Q`

combined with the *degree-in-`x₀`* argument (the substitution `psiV` keeps `x₀` and makes `x₁, x₂`
constants, so that `quadF` becomes monic of degree `2` while `R₁x₀+R₀` has degree `≤ 1`) gives
`R₁ = 0` and `R₀ = 0`.  Dehomogenising `(x₁,x₂) ↦ (X,1)` and reading off coefficients yields the
six equations consumed by `SdG5hQuadAlg`.
-/

set_option maxHeartbeats 8000000
set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- The substitution keeping `x₀` and turning `x₁`, `x₂` into constants. -/
noncomputable def psiV : MvPolynomial (Fin 3) K →ₐ[K] Polynomial (MvPolynomial (Fin 3) K) :=
  MvPolynomial.aeval (fun i : Fin 3 =>
    ![Polynomial.X, Polynomial.C (MvPolynomial.X 1), Polynomial.C (MvPolynomial.X 2)] i)

lemma psiV_X0 : psiV (K := K) (X 0) = Polynomial.X := by
  rw [psiV, MvPolynomial.aeval_X]; simp
lemma psiV_X1 : psiV (K := K) (X 1) = Polynomial.C (MvPolynomial.X 1) := by
  rw [psiV, MvPolynomial.aeval_X]; simp
lemma psiV_X2 : psiV (K := K) (X 2) = Polynomial.C (MvPolynomial.X 2) := by
  rw [psiV, MvPolynomial.aeval_X]; simp
lemma psiV_C (a : K) : psiV (K := K) (C a) = Polynomial.C (MvPolynomial.C a) := by
  rw [psiV, MvPolynomial.aeval_C]; simp

lemma psiV_quadF (p q r s t : K) :
    psiV (K := K) (quadF p q r s t)
      = Polynomial.X ^ 2 + Polynomial.C (BB p q) * Polynomial.X + Polynomial.C (CC r s t) := by
  rw [quadF, BB, CC]
  simp only [map_add, map_mul, map_pow, psiV_X0, psiV_X1, psiV_X2, psiV_C]

lemma psiV_RR1 (g1 g4 g5 p q r s t : K) :
    psiV (K := K) (RR1 g1 g4 g5 p q r s t)
      = Polynomial.C (RR1 g1 g4 g5 p q r s t) := by
  rw [RR1, BB, CC]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, psiV_X1, psiV_X2, psiV_C]

lemma psiV_RR0 (g1 g2 g3 g4 p q r s t : K) :
    psiV (K := K) (RR0 g1 g2 g3 g4 p q r s t)
      = Polynomial.C (RR0 g1 g2 g3 g4 p q r s t) := by
  rw [RR0, BB, CC]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, psiV_X1, psiV_X2, psiV_C]

/-- **The degree-in-`x₀` argument.**  A monic quadratic factor makes the remainder vanish. -/
theorem quadEquations (g1 g2 g3 g4 g5 p q r s t : K) (H : MvPolynomial (Fin 3) K)
    (hfac : quadF p q r s t * H = Gg g1 g2 g3 g4 g5) :
    RR1 g1 g4 g5 p q r s t = 0 ∧ RR0 g1 g2 g3 g4 p q r s t = 0 := by
  have hψ : psiV (K := K) (quadF p q r s t) * psiV (K := K) H
      = psiV (K := K) (Gg g1 g2 g3 g4 g5) := by
    rw [← map_mul, hfac]
  have hψdiv : psiV (K := K) (Gg g1 g2 g3 g4 g5)
      - (psiV (K := K) (RR1 g1 g4 g5 p q r s t) * Polynomial.X
          + psiV (K := K) (RR0 g1 g2 g3 g4 p q r s t))
      = psiV (K := K) (quadF p q r s t) * psiV (K := K) (QQ g1 g4 p q r s t) := by
    have h := congrArg (psiV (K := K)) (division_identity g1 g2 g3 g4 g5 p q r s t)
    simp only [map_sub, map_add, map_mul] at h
    rw [psiV_X0] at h
    exact h
  have hkey : psiV (K := K) (quadF p q r s t)
        * (psiV (K := K) H - psiV (K := K) (QQ g1 g4 p q r s t))
      = psiV (K := K) (RR1 g1 g4 g5 p q r s t) * Polynomial.X
          + psiV (K := K) (RR0 g1 g2 g3 g4 p q r s t) := by
    rw [mul_sub, hψ, ← hψdiv]
    first | refl_ring1 | ring
  have hdvd : psiV (K := K) (quadF p q r s t)
      ∣ (psiV (K := K) (RR1 g1 g4 g5 p q r s t) * Polynomial.X
          + psiV (K := K) (RR0 g1 g2 g3 g4 p q r s t)) :=
    ⟨psiV (K := K) H - psiV (K := K) (QQ g1 g4 p q r s t), hkey.symm⟩
  have hdegQ : (Polynomial.C (BB p q) * Polynomial.X
      + Polynomial.C (CC r s t) : Polynomial (MvPolynomial (Fin 3) K)).degree < (2 : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    rw [max_lt_iff]
    exact ⟨lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num),
      lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)⟩
  have hdeg : (psiV (K := K) (quadF p q r s t)).degree = (2 : WithBot ℕ) := by
    rw [psiV_quadF, add_assoc]
    rw [Polynomial.degree_add_eq_left_of_degree_lt]
    · exact Polynomial.degree_X_pow 2
    · rw [Polynomial.degree_X_pow]; exact hdegQ
  have hRR1deg : (psiV (K := K) (RR1 g1 g4 g5 p q r s t)).degree ≤ (0 : WithBot ℕ) := by
    rw [psiV_RR1]; exact Polynomial.degree_C_le
  have hRR0deg : (psiV (K := K) (RR0 g1 g2 g3 g4 p q r s t)).degree ≤ (0 : WithBot ℕ) := by
    rw [psiV_RR0]; exact Polynomial.degree_C_le
  have hdegR1 : (psiV (K := K) (RR1 g1 g4 g5 p q r s t) * Polynomial.X).degree
      < (2 : WithBot ℕ) := by
    calc (psiV (K := K) (RR1 g1 g4 g5 p q r s t) * Polynomial.X).degree
        ≤ (psiV (K := K) (RR1 g1 g4 g5 p q r s t)).degree + Polynomial.X.degree :=
          Polynomial.degree_mul_le _ _
      _ ≤ 0 + 1 := add_le_add hRR1deg Polynomial.degree_X.le
      _ = 1 := by norm_num
      _ < 2 := by norm_num
  have hdegR : (psiV (K := K) (RR1 g1 g4 g5 p q r s t) * Polynomial.X
      + psiV (K := K) (RR0 g1 g2 g3 g4 p q r s t)).degree < (2 : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    rw [max_lt_iff]
    exact ⟨hdegR1, lt_of_le_of_lt hRR0deg (by norm_num)⟩
  have hzero := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd (by rw [hdeg]; exact hdegR)
  have hC : (Polynomial.C (RR1 g1 g4 g5 p q r s t) * Polynomial.X
      + Polynomial.C (RR0 g1 g2 g3 g4 p q r s t) : Polynomial (MvPolynomial (Fin 3) K)) = 0 := by
    simpa only [psiV_RR1, psiV_RR0] using hzero
  constructor
  · have h1 := congrArg (fun f : Polynomial (MvPolynomial (Fin 3) K) => Polynomial.coeff f 1) hC
    simpa [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C] using h1
  · have h0 := congrArg (fun f : Polynomial (MvPolynomial (Fin 3) K) => Polynomial.coeff f 0) hC
    simpa [Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_C_zero] using h0

/-- The substitution collapsing `x₀` to `0` and `x₂` to `1` (dehomogenisation in `x₁`). -/
-- NAME DISAMBIGUATION (area owner, 2026-10-04): this `K`-algebra homomorphism was called `chiV`
-- and collided with the *different* `Work.MotK.TGen.chiV : Fin 5 → MvPolynomial (Fin 2) K` of
-- `TGen/FwVec4ParamClean.lean` (both modules lie in the closure of the census
-- `Work.MotK.TGenCensusWired`, so `lake` rejected the pair with "environment already contains
-- 'Work.MotK.TGen.chiV'").  It is therefore renamed `chiSdG5` here; no file outside this one
-- mentions it.
noncomputable def chiSdG5 : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval (fun i : Fin 3 => ![0, Polynomial.X, (1 : Polynomial K)] i)

lemma chiSdG5_X0 : chiSdG5 (K := K) (X 0) = 0 := by
  rw [chiSdG5, MvPolynomial.aeval_X]; simp
lemma chiSdG5_X1 : chiSdG5 (K := K) (X 1) = Polynomial.X := by
  rw [chiSdG5, MvPolynomial.aeval_X]; simp
lemma chiSdG5_X2 : chiSdG5 (K := K) (X 2) = 1 := by
  rw [chiSdG5, MvPolynomial.aeval_X]; simp
lemma chiSdG5_C (a : K) : chiSdG5 (K := K) (C a) = Polynomial.C a := by
  rw [chiSdG5, MvPolynomial.aeval_C]; simp

/-- Expansion of the dehomogenised `R₁` (coefficients of `x₁⁴, x₁³x₂, …, x₂⁴`). -/
lemma chiSdG5_RR1 (g1 g4 g5 p q r s t : K) :
    chiSdG5 (K := K) (RR1 g1 g4 g5 p q r s t)
      = Polynomial.C (g1 * (p ^ 4 - 3 * p ^ 2 * r + r ^ 2)) * Polynomial.X ^ 4
        + Polynomial.C (g1 * (4 * p ^ 3 * q - 3 * p ^ 2 * s - 6 * p * q * r + 2 * r * s) + g5)
            * Polynomial.X ^ 3
        + Polynomial.C (g1 * (6 * p ^ 2 * q ^ 2 - 3 * p ^ 2 * t - 6 * p * q * s - 3 * q ^ 2 * r
            + 2 * r * t + s ^ 2) - g4 * p) * Polynomial.X ^ 2
        + Polynomial.C (g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t) - g4 * q)
            * Polynomial.X
        + Polynomial.C (g1 * (q ^ 4 - 3 * q ^ 2 * t + t ^ 2)) := by
  rw [RR1, BB, CC]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, chiSdG5_X1, chiSdG5_X2, chiSdG5_C]
  ring_nf

/-- Expansion of the dehomogenised `R₀` (coefficients of `x₁⁵, x₁⁴x₂, …, x₂⁵`). -/
lemma chiSdG5_RR0 (g1 g2 g3 g4 p q r s t : K) :
    chiSdG5 (K := K) (RR0 g1 g2 g3 g4 p q r s t)
      = Polynomial.C (g1 * (p ^ 3 * r - 2 * p * r ^ 2) + g2) * Polynomial.X ^ 5
        + Polynomial.C (g1 * (p ^ 3 * s + 3 * p ^ 2 * q * r - 4 * p * r * s - 2 * q * r ^ 2))
            * Polynomial.X ^ 4
        + Polynomial.C (g1 * (p ^ 3 * t + 3 * p ^ 2 * q * s + 3 * p * q ^ 2 * r - 4 * p * r * t
            - 2 * p * s ^ 2 - 4 * q * r * s) - g4 * r) * Polynomial.X ^ 3
        + Polynomial.C (g1 * (3 * p ^ 2 * q * t + 3 * p * q ^ 2 * s - 4 * p * s * t + q ^ 3 * r
            - 4 * q * r * t - 2 * q * s ^ 2) - g4 * s) * Polynomial.X ^ 2
        + Polynomial.C (g1 * (3 * p * q ^ 2 * t + q ^ 3 * s - 2 * p * t ^ 2 - 4 * q * s * t) - g4 * t)
            * Polynomial.X
        + Polynomial.C (g1 * (q ^ 3 * t - 2 * q * t ^ 2) + g3) := by
  rw [RR0, BB, CC]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, chiSdG5_X1, chiSdG5_X2, chiSdG5_C]
  ring_nf

/-- **The six scalar equations** forced by a monic quadratic factor. -/
theorem quadEquationsScalar (g1 g2 g3 g4 g5 p q r s t : K) (H : MvPolynomial (Fin 3) K)
    (hfac : quadF p q r s t * H = Gg g1 g2 g3 g4 g5) :
    g1 * (p ^ 4 - 3 * p ^ 2 * r + r ^ 2) = 0
      ∧ g1 * (4 * p ^ 3 * q - 3 * p ^ 2 * s - 6 * p * q * r + 2 * r * s) + g5 = 0
      ∧ g1 * (4 * p * q ^ 3 - 6 * p * q * t - 3 * q ^ 2 * s + 2 * s * t) - g4 * q = 0
      ∧ g1 * (p ^ 3 * r - 2 * p * r ^ 2) + g2 = 0
      ∧ g1 * (p ^ 3 * s + 3 * p ^ 2 * q * r - 4 * p * r * s - 2 * q * r ^ 2) = 0
      ∧ g1 * (3 * p ^ 2 * q * t + 3 * p * q ^ 2 * s - 4 * p * s * t + q ^ 3 * r - 4 * q * r * t
          - 2 * q * s ^ 2) - g4 * s = 0
      ∧ g1 * (q ^ 3 * t - 2 * q * t ^ 2) + g3 = 0 := by
  obtain ⟨hR1, hR0⟩ := quadEquations g1 g2 g3 g4 g5 p q r s t H hfac
  have e1 : chiSdG5 (K := K) (RR1 g1 g4 g5 p q r s t) = 0 := by rw [hR1, map_zero]
  have e0 : chiSdG5 (K := K) (RR0 g1 g2 g3 g4 p q r s t) = 0 := by rw [hR0, map_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have c := congrArg (fun f : Polynomial K => Polynomial.coeff f 4) e1
    rw [chiSdG5_RR1] at c
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_zero] at c
    norm_num at c
    rcases c with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  · have c := congrArg (fun f : Polynomial K => Polynomial.coeff f 3) e1
    rw [chiSdG5_RR1] at c
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_zero] at c
    norm_num at c
    exact c
  · have c := congrArg (fun f : Polynomial K => Polynomial.coeff f 1) e1
    rw [chiSdG5_RR1] at c
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_zero] at c
    norm_num at c
    exact c
  · have c := congrArg (fun f : Polynomial K => Polynomial.coeff f 5) e0
    rw [chiSdG5_RR0] at c
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_zero] at c
    norm_num at c
    exact c
  · have c := congrArg (fun f : Polynomial K => Polynomial.coeff f 4) e0
    rw [chiSdG5_RR0] at c
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_zero] at c
    norm_num at c
    rcases c with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  · have c := congrArg (fun f : Polynomial K => Polynomial.coeff f 2) e0
    rw [chiSdG5_RR0] at c
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_zero] at c
    norm_num at c
    exact c
  · have c := congrArg (fun f : Polynomial K => Polynomial.coeff f 0) e0
    rw [chiSdG5_RR0] at c
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C, Polynomial.coeff_zero] at c
    norm_num at c
    exact c

end Work.MotK.TGen
