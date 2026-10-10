import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZTwistDivGeomCerts`

The explicit polynomial certificates for the chart picture of the `h`-twisted Crauder--Katz
link (node K6 of the T-twisted link).  Vocabulary (`zpgE`, `zpgE4`, `zpgW4`, `zpgC4`, `zpgQ`,
`zpgI4`, `zpgG3`) is in `Submission/Work/MotK/TGen/ZTwistDivGeomDefs.lean`; the meaning of the
five conjuncts is recalled in `NOTE_ZTwistDivGeomCerts.md`.

The content of the theorem is

1. the eliminant `ZElim2` of the twisted Klein curve, after the invertible diagonal substitution
   `X₀ ↦ (a/b)y₁`, `X₁ ↦ -(a/b)h·y₃`, equals `(a³/b⁴)·zpgE` (the plane model of the residual
   curve in the chart `y₀ = 1`);
2. `zpgE4 ∈ zpgI4`: the eliminant of the chart of the residual curve lies in the ideal of the
   chart of the twisted Klein curve — the only "Gröbner" input, proved by the explicit cofactor
   identity `zpgE4 = -∑_{k<5} zpgCert_k · zpgQ_k` (cofactors found by CAS);
3. `zpgG3 ∈ zpgI4`: the inverse chart relation `h²Wy₄ - c` lies in the chart ideal;
4. each chart quadric lies in `zpgI4` (trivial);
5. the third chart quadric resolves the chart coordinate `y₂` of the inverse chart map.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Work.MotK.TGen

open MvPolynomial

section

variable {K : Type} [Field K]

/-! ## The cofactors of the Gröbner certificate `zpgE4 = -∑ c_k · zpgQ_k` -/

/-- Cofactor of `zpgQ a b h 0` in the certificate `zpgE4 = -∑ c_k zpgQ_k`. -/
private noncomputable def zpgCert0 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (a^4*b^3*h^2) * (X 0)^2 * X 2 + C (a^5*b^2*h^2) * X 0 * (X 1)^2
    - C (a*b^6*h^2) * X 0 * X 3 - C (a^3*b^4*h^2) * X 1 * X 2
    + C (a^5*b^2*h^4) * (X 2)^2 * X 3 + C (a^2*b^5)

/-- Cofactor of `zpgQ a b h 1` in the certificate. -/
private noncomputable def zpgCert1 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (a^6*b*h^4) * X 0 * X 1 * X 2 + C (2*a^5*b^2*h^2) * X 0
    - C (2*a^4*b^3*h^4) * (X 2)^2 - C (a^5*b^2*h^6) * X 2 * (X 3)^2

/-- Cofactor of `zpgQ a b h 2` in the certificate. -/
private noncomputable def zpgCert2 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (b^7*h^2) * (X 0)^2 + C (2*a^4*b^3*h^2) * X 1 - C (a^6*b*h^4) * X 2 * X 3

/-- Cofactor of `zpgQ a b h 3` in the certificate. -/
private noncomputable def zpgCert3 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (a^2*b^5*h^2) * (X 0)^3 - C (a^4*b^3*h^4) * (X 1)^2 * X 3

/-- Cofactor of `zpgQ a b h 4` in the certificate. -/
private noncomputable def zpgCert4 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (a^4*b^3*h^2) * (X 1)^2 + C (a^7*h^4) * (X 2)^3 - C (2*a^5*b^2*h^2) * X 3

/-- **The Gröbner certificate** (computed with CAS over `ℚ(a,b,h)`):
`zpgE4 = -(zpgCert0·zpgQ₀ + zpgCert1·zpgQ₁ + … + zpgCert4·zpgQ₄)`. -/
private theorem zpgE4_cert (a b h : K) :
    zpgE4 a b h = -(zpgCert0 a b h * zpgQ a b h 0 + zpgCert1 a b h * zpgQ a b h 1
      + zpgCert2 a b h * zpgQ a b h 2 + zpgCert3 a b h * zpgQ a b h 3
      + zpgCert4 a b h * zpgQ a b h 4) := by
  rw [zpgE4, zpgQ, zpgCert0, zpgCert1, zpgCert2, zpgCert3, zpgCert4]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    map_mul, map_pow, map_sub, map_neg, map_ofNat]
  first | refl_ring1 | ring

/-- The chart relation `h²·W·y₄ - c` is `-(b²·zpgQ₀) - (a²h²·y₃·zpgQ₃)`. -/
private theorem zpgG3_eq (a b h : K) :
    zpgG3 a b h = -(C (b^2) * zpgQ a b h 0) - C (a^2*h^2) * X 2 * zpgQ a b h 3 := by
  rw [zpgG3, zpgC4, zpgW4, zpgQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    map_mul, map_pow, map_neg, map_add, map_sub]
  first | refl_ring1 | ring

/-- The third chart quadric solves for the chart coordinate `y₂` of the inverse chart map. -/
private theorem zpg_surj (a b h : K) :
    C (b^2) * X 1 = C (a^2*h^2) * X 2 * X 3 - C (a*b) * (X 0)^2 - zpgQ a b h 3 := by
  rw [zpgQ]
  simp only [Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

/-- The diagonal substitution `X₀ ↦ (a/b)y₁`, `X₁ ↦ -(a/b)h·y₃` turns the eliminant `ZElim2`
into `(a³/b⁴)·zpgE`: `b⁴·ZElim2((a/b)y₁, -(a/b)h y₃) = a³·zpgE(y₁,y₃)`. -/
private theorem zpgE_aeval_eq (a b h : K) :
    MvPolynomial.aeval (R := K) (S₁ := MvPolynomial (Fin 2) K) (σ := Fin 2)
          ![C a * X 0, C (-(a*h)) * X 1]
          (Work.MotK.TwCensus.ZElim2 a b h) * C (b ^ 4)
        = C (a ^ 3) * MvPolynomial.aeval (R := K)
            (S₁ := MvPolynomial (Fin 2) K) (σ := Fin 2)
            ![C b * X 0, C b * X 1]
            (zpgE a b h) := by
  rw [Work.MotK.TwCensus.ZElim2, zpgE]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  first | refl_ring1 | ring

end

theorem ZTwistDivGeomCerts (K : Type) [Field K] (a b h : K) :
    (MvPolynomial.aeval (R := K) (S₁ := MvPolynomial (Fin 2) K) (σ := Fin 2)
          ![MvPolynomial.C a * MvPolynomial.X 0, MvPolynomial.C (-(a*h)) * MvPolynomial.X 1]
          (Work.MotK.TwCensus.ZElim2 a b h) * MvPolynomial.C (b ^ 4)
        = MvPolynomial.C (a ^ 3) * MvPolynomial.aeval (R := K)
            (S₁ := MvPolynomial (Fin 2) K) (σ := Fin 2)
            ![MvPolynomial.C b * MvPolynomial.X 0, MvPolynomial.C b * MvPolynomial.X 1]
            (Work.MotK.TGen.zpgE a b h))
    ∧ (Work.MotK.TGen.zpgE4 a b h ∈ Work.MotK.TGen.zpgI4 a b h)
    ∧ (Work.MotK.TGen.zpgG3 a b h ∈ Work.MotK.TGen.zpgI4 a b h)
    ∧ (∀ k : Fin 5, Work.MotK.TGen.zpgQ a b h k ∈ Work.MotK.TGen.zpgI4 a b h)
    ∧ (MvPolynomial.C (b ^ 2) * MvPolynomial.X 1
        = MvPolynomial.C (a ^ 2 * h ^ 2) * MvPolynomial.X 2 * MvPolynomial.X 3
          - MvPolynomial.C (a * b) * (MvPolynomial.X 0) ^ 2 - Work.MotK.TGen.zpgQ a b h 3) := by
  refine ⟨zpgE_aeval_eq a b h, ?_, ?_, ?_, zpg_surj a b h⟩
  · rw [zpgE4_cert]
    refine neg_mem ?_
    have h0 : zpgQ a b h 0 ∈ zpgI4 a b h := Ideal.subset_span ⟨0, rfl⟩
    have h1 : zpgQ a b h 1 ∈ zpgI4 a b h := Ideal.subset_span ⟨1, rfl⟩
    have h2 : zpgQ a b h 2 ∈ zpgI4 a b h := Ideal.subset_span ⟨2, rfl⟩
    have h3 : zpgQ a b h 3 ∈ zpgI4 a b h := Ideal.subset_span ⟨3, rfl⟩
    have h4 : zpgQ a b h 4 ∈ zpgI4 a b h := Ideal.subset_span ⟨4, rfl⟩
    exact add_mem (add_mem (add_mem (add_mem (Ideal.mul_mem_left _ _ h0)
      (Ideal.mul_mem_left _ _ h1)) (Ideal.mul_mem_left _ _ h2))
      (Ideal.mul_mem_left _ _ h3)) (Ideal.mul_mem_left _ _ h4)
  · rw [zpgG3_eq]
    exact sub_mem
      ((Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨3, rfl⟩))
  · intro k
    exact Ideal.subset_span ⟨k, rfl⟩

end Work.MotK.TGen
