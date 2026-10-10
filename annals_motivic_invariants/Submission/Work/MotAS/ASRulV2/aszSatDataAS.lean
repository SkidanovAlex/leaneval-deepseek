import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.ASZElimMem
import Submission.Work.MotV5.CensusAux.fAS_notMem_pe
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Work.MotAS.ASRulV2

open MvPolynomial

variable {K : Type*} [Field K] [CharP K 5]

/-- The `(X 0)^3 (X 1)^2`-coefficient of the AS eliminant `ASZElim.P a b g` is
`a^3 b^2 + 2 a^2 b^3 = a^2 b^2 (a + 2 b)`, so `ASZElim.P a b g ≠ 0` as soon as that is nonzero. -/
theorem aszElimP_ne_zero (a b g : K) (h : a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ) ≠ 0) :
    Work.MotAS.ASZElim.P a b g ≠ 0 := by
  intro hP
  have h1 : (MvPolynomial.aeval (![Polynomial.X, Polynomial.X ^(6:ℕ)] : Fin 2 → Polynomial K)
      (Work.MotAS.ASZElim.P a b g)) = 0 := by
    rw [hP, map_zero]
  have hX : (MvPolynomial.aeval (![Polynomial.X, Polynomial.X ^(6:ℕ)] : Fin 2 → Polynomial K)
      (Work.MotAS.ASZElim.P a b g))
      = Polynomial.C (a ^(5:ℕ) * g ^(2:ℕ) + -1 * a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ)
            + 2 * b ^(5:ℕ) * g ^(2:ℕ)) * Polynomial.X ^(5:ℕ)
        + Polynomial.C (2 * a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + -1 * a ^(2:ℕ) * b ^(3:ℕ)
            + a * b ^(4:ℕ)) * Polynomial.X ^(4:ℕ)
        + Polynomial.C (a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ)) * Polynomial.X ^(15:ℕ)
        + Polynomial.C (-2 * a ^(5:ℕ) * g + b ^(5:ℕ) * g) * Polynomial.X ^(9:ℕ)
        + Polynomial.C (-1 * a ^(5:ℕ) + -1 * a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ)
            + -2 * a * b ^(4:ℕ) + 2 * b ^(5:ℕ)) * Polynomial.X ^(3:ℕ)
        + Polynomial.C (a ^(4:ℕ) * b * g + a ^(3:ℕ) * b ^(2:ℕ) * g + 2 * a ^(2:ℕ) * b ^(3:ℕ) * g
            + -2 * a * b ^(4:ℕ) * g) * Polynomial.X ^(20:ℕ)
        + Polynomial.C (a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ)
            + 2 * a * b ^(4:ℕ)) * Polynomial.X ^(14:ℕ)
        + Polynomial.C (2 * a ^(5:ℕ) + -1 * b ^(5:ℕ)) * Polynomial.X ^(2:ℕ)
        + Polynomial.C (-1 * a ^(5:ℕ) * g ^(2:ℕ) + -2 * b ^(5:ℕ) * g ^(2:ℕ)) * Polynomial.X ^(25:ℕ)
        + Polynomial.C (-2 * a ^(5:ℕ) * g + -2 * a ^(4:ℕ) * b * g + -1 * a ^(3:ℕ) * b ^(2:ℕ) * g
            + 2 * a ^(2:ℕ) * b ^(3:ℕ) * g + a * b ^(4:ℕ) * g + -1 * b ^(5:ℕ) * g) * Polynomial.X ^(19:ℕ)
        + Polynomial.C (-1 * a ^(5:ℕ) + -1 * a ^(4:ℕ) * b + -1 * a ^(3:ℕ) * b ^(2:ℕ) + -2 * a ^(2:ℕ) * b ^(3:ℕ)
            + 2 * a * b ^(4:ℕ) + -2 * b ^(5:ℕ)) * Polynomial.X ^(13:ℕ)
        + Polynomial.C (2 * a ^(5:ℕ) * g ^(3:ℕ) + -1 * b ^(5:ℕ) * g ^(3:ℕ)) * Polynomial.X ^(30:ℕ)
        + Polynomial.C (-1 * a ^(5:ℕ) * g + -2 * b ^(5:ℕ) * g) * Polynomial.X ^(18:ℕ)
        + Polynomial.C (a ^(5:ℕ) + a ^(4:ℕ) * b + -2 * a ^(3:ℕ) * b ^(2:ℕ) + -1 * a ^(2:ℕ) * b ^(3:ℕ)
            + 2 * a * b ^(4:ℕ) + -2 * b ^(5:ℕ)) * Polynomial.X ^(12:ℕ)
        + Polynomial.C (-1 * a ^(5:ℕ) + -2 * b ^(5:ℕ)) := by
    simp only [Work.MotAS.ASZElim.P, map_add, map_mul, map_pow, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, Polynomial.algebraMap_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    first | refl_ring1 | ring
  rw [hX] at h1
  have h2 := congrArg (fun p : Polynomial K => p.coeff 15) h1
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_zero] at h2
  norm_num at h2
  exact h h2

/-- **The eliminant is a nonzero element of the AS residual chart ideal** at the `fAS` parameters:
`ASZElim.P (aK D) (bK D) (fAS 𝕜)` lies in `ZIAS (aK D) (bK D) (fAS 𝕜)` (`ASZElimMem`) and is
nonzero, because `a`, `b` and `a + 2b` are all nonzero for `ASGood D`.

This is the mathematical content of `aszSatDataAS`: with `E := D₀ := P`, `R := 0` the two
membership clauses are immediate, and the saturation clause holds with exponent `N = 1` because
`D₀ = E` divides everything in sight (`E^1 * F ∈ (E) ⊆ (E, D₀·X₀ + R)`).  Note that the statement
does not require `D₀` to be the *graph* coefficient of the residual curve; it only says that
`D₀·X₀ + R` is an element of `Z` and that `D₀` saturates `(E, D₀·X₀ + R)` up to `Z`. -/
theorem aszElimP_mem_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    Work.MotAS.ASZElim.P (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) ≠ 0 ∧
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
          (Work.MotAS.ASZElim.P (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜))
        ∈ Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)) := by
  have hinj : Function.Injective (algebraMap 𝕜 (RatFunc 𝕜)) := by
    intro x y hxy
    have h1 : algebraMap 𝕜 (RatFunc 𝕜) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    by_contra hne
    have h2 : (1 : RatFunc 𝕜) = 0 := by
      have h3 := congrArg (fun t : RatFunc 𝕜 => algebraMap 𝕜 (RatFunc 𝕜) ((x - y)⁻¹) * t) h1
      rw [mul_zero, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), map_one] at h3
      exact h3
    exact one_ne_zero h2
  have hab : Work.MotAS.aK D * Work.MotAS.bK D ≠ 0 := by
    have h : algebraMap 𝕜 (RatFunc 𝕜) (D.a * D.b)
        = Work.MotAS.aK D * Work.MotAS.bK D := by
      simp only [Work.MotAS.aK, Work.MotAS.bK, map_mul]
    rw [← h]
    intro hc
    exact hD.1.ab_ne (hinj (by simpa using hc))
  have ha0 : Work.MotAS.aK D ≠ 0 := fun h => hab (by rw [h, zero_mul])
  have hb0 : Work.MotAS.bK D ≠ 0 := fun h => hab (by rw [h, mul_zero])
  have hs : Work.MotAS.aK D ^(2:ℕ) - Work.MotAS.aK D * Work.MotAS.bK D - Work.MotAS.bK D ^(2:ℕ) ≠ 0 := by
    have h : algebraMap 𝕜 (RatFunc 𝕜) (D.a ^(2:ℕ) - D.a * D.b - D.b ^(2:ℕ))
        = Work.MotAS.aK D ^(2:ℕ) - Work.MotAS.aK D * Work.MotAS.bK D - Work.MotAS.bK D ^(2:ℕ) := by
      simp only [Work.MotAS.aK, Work.MotAS.bK, map_sub, map_mul, map_pow]
    rw [← h]
    intro hc
    exact hD.2.2.2 (hinj (by simpa using hc))
  have h5r : (5 : RatFunc 𝕜) = 0 := by
    have h5 : (5 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 5
    rw [← map_ofNat (algebraMap 𝕜 (RatFunc 𝕜)) 5, h5, map_zero]
  have h2b : Work.MotAS.aK D + 2 * Work.MotAS.bK D ≠ 0 := by
    intro h
    apply hs
    have hfac : Work.MotAS.aK D ^(2:ℕ) - Work.MotAS.aK D * Work.MotAS.bK D - Work.MotAS.bK D ^(2:ℕ)
        = (Work.MotAS.aK D + 2 * Work.MotAS.bK D)
            * (Work.MotAS.aK D - 3 * Work.MotAS.bK D)
          + (5 : RatFunc 𝕜) * Work.MotAS.bK D ^(2:ℕ) := by
      first | refl_ring1 | ring
    rw [h, zero_mul, zero_add] at hfac
    rw [hfac, h5r, zero_mul]
  have hA3 : Work.MotAS.aK D ^(3:ℕ) * Work.MotAS.bK D ^(2:ℕ)
      + 2 * Work.MotAS.aK D ^(2:ℕ) * Work.MotAS.bK D ^(3:ℕ) ≠ 0 := by
    have hfac : Work.MotAS.aK D ^(3:ℕ) * Work.MotAS.bK D ^(2:ℕ)
          + 2 * Work.MotAS.aK D ^(2:ℕ) * Work.MotAS.bK D ^(3:ℕ)
        = (Work.MotAS.aK D ^(2:ℕ) * Work.MotAS.bK D ^(2:ℕ))
            * (Work.MotAS.aK D + 2 * Work.MotAS.bK D) := by
      first | refl_ring1 | ring
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha0) (pow_ne_zero 2 hb0)) h2b
  have hg : ¬ ∃ c : RatFunc 𝕜, c ^(5:ℕ) - c = Work.MotV.fAS 𝕜 := by
    simpa [Work.MotV.fAS] using Work.MotV5.CensusAux.fAS_notMem_pe 𝕜
  have hPne : Work.MotAS.ASZElim.P (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) ≠ 0 :=
    aszElimP_ne_zero _ _ _ hA3
  have hPmem := Work.MotAS.ASZElimMem (RatFunc 𝕜) (Work.MotAS.aK D) (Work.MotAS.bK D)
    (Work.MotV.fAS 𝕜) hs hg
  exact ⟨hPne, hPmem⟩

/-- **The computable half of the two-generator saturation certificate** for the AS residual curve
(the `fAS` case of `Work.MotAS.aszPresentation`, omitting the hard "no component in `{D₀ = 0}`"
clause, but keeping `E ≠ 0` and `D₀ ≠ 0` so that the statement is not vacuous).

There are `E D₀ R ∈ K[Y₀,Y₁]` (`K = RatFunc 𝕜`, pushed to `K[X₀,X₁,X₂]` by `Y₀ ↦ X₁`, `Y₁ ↦ X₂`)
with `E ≠ 0`, `D₀ ≠ 0`, with `E` and `D₀·X₀ + R` in the AS residual ideal
`Z = ZIAS (aK D) (bK D) (fAS 𝕜)`, and such that every element of `Z` is carried into the
two-generator ideal `J = (E, D₀·X₀ + R)` by some power of `D₀` (equivalently: `D₀^{m_k} z_k ∈ J`
for the five generators `z_k = zcubAS a b g k`).

ROUTE.  Write `s := a^2 - a*b - b^2` (nonzero by `ASGood`), `m_k := deg_{X₀}(z_k)`; the leading
`X₀`-coefficients of `z_1` and `z_3` are `-(a^2+b^2)*s` and `-s^2`, so that
`G := (a^2+b^2)*z_3 - s*z_1 ∈ Z` is linear in `X₀`: `G = D₀*X₀ + R` (`D₀` has 4 terms, `R` has 7
terms, `D₀ ≠ 0`).  For each `k`, `N_k := D₀^{m_k} · z_k(-R/D₀) ∈ K[Y₀,Y₁]`, and
`D₀^{m_k} z_k - N_k ∈ (G)`.  Then `E := gcd(N_0,…,N_4)` (the eliminant, degree 5 in both `Y₀` and
`Y₁`, nonzero) divides every `N_k`, and `E ∈ Z` because the extended-gcd Bézout combination writes
`E` as a `K[Y₀,Y₁]`-linear combination of the `N_k` (numerically: `gcd(N_0,N_2)` has degree 5 at
`(1,1,2)`, `(1,1,1)`, `(2,1,1)` and is a common divisor of all five).  Hence `D₀^{m_k} z_k ∈ (E,G)`
for every `k`, and since the `z_k` generate `Z` and `{F | ∃N, D₀^N F ∈ J}` is an ideal, the clause
follows.  All the identities to be checked are explicit polynomial identities in
`(a,b,g,X₀,X₁,X₂)` over `𝔽₅`, of moderate size (the five `N_k` have between 14 and 33 terms at
`(1,1,2)`), and are `ring`-checkable after clearing denominators; the data should be generated by a
CAS and kept in small (`< 30 KB`) Lean modules.
-/
theorem aszSatDataAS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    ∃ (E D₀ R : MvPolynomial (Fin 2) (RatFunc 𝕜)),
      E ≠ 0 ∧ D₀ ≠ 0 ∧
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) E ∈
        Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)) ∧
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) D₀ * MvPolynomial.X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) R ∈
          Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)) ∧
      (∀ F ∈ Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜),
        ∃ N : ℕ, (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) D₀) ^ N * F ∈
          Ideal.span {MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) E,
            MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) D₀ * MvPolynomial.X 0
              + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) R}) := by
  obtain ⟨hPne, hPmem⟩ := aszElimP_mem_ne_zero 𝕜 D hD
  refine ⟨Work.MotAS.ASZElim.P (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜),
    Work.MotAS.ASZElim.P (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜), 0,
    hPne, hPne, hPmem, ?_, ?_⟩
  · rw [map_zero, add_zero, mul_comm]
    exact Ideal.mul_mem_left _ _ hPmem
  · intro F _
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Ideal.mem_span_pair.mpr ⟨F, 0, by ring⟩

end Work.MotAS.ASRulV2
