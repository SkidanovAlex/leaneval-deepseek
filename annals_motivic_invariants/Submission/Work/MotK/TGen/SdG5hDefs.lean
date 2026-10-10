import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TwCensus.SdualTShape
import Submission.Work.MotK.TwCensus.SdualTOneIrreducible
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.sdG5h` — the degree-five part of the target ruling divisor `sdualT`

`Work.MotK.TGen.sdualT a b h = kleinTwSDualV a b h (chart3 K)` is the chart restriction
`z = (0, X₀, X₁, X₂, 1)` of the target-side dual secant quintic of the T-twisted Crauder–Katz
link.  Its twelve-term shape is `Work.MotK.TwCensus.sdualT_explicit`; grouping the terms by total
degree, the degree-five part is

```
sdG5h a b h = -a⁵b⁵h⁴ x₀⁵ - a⁵b⁵h³ x₁⁵ - a⁵b⁵h² x₂⁵
              + h³(3a⁴b⁶-a⁹b) x₀²x₁x₂² + h³(2a⁷b³-a²b⁸) x₀x₁³x₂
```

while the seven remaining terms (`sdG5hLower`) have total degree `≤ 4`.  Since the leading form
`sdG5h a b h` is homogeneous of degree five, the classical "top-degree" argument
(`Work.MotK.TwCensus.irreducible_of_isHomogeneous_add`) shows that `Irreducible (sdG5h a b h)`
implies `Irreducible (sdualT a b h)`; this file records exactly that bookkeeping, so that the
irreducibility of `sdG5h a b h` (isolated in `Work.MotK.TGen.SdG5hCrux`) yields the target.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- **The degree-five part of `sdualT a b h`.** -/
noncomputable def sdG5h (a b h : K) : MvPolynomial (Fin 3) K :=
    C (-(a ^(5:ℕ) * b ^(5:ℕ) * h ^(4:ℕ))) * (X 0) ^(5:ℕ)
  + C (-(a ^(5:ℕ) * b ^(5:ℕ) * h ^(3:ℕ))) * (X 1) ^(5:ℕ)
  + C (-(a ^(5:ℕ) * b ^(5:ℕ) * h ^(2:ℕ))) * (X 2) ^(5:ℕ)
  + C (h ^(3:ℕ) * (3 * a ^(4:ℕ) * b ^(6:ℕ) - a ^(9:ℕ) * b)) * ((X 0) ^(2:ℕ) * X 1 * (X 2) ^(2:ℕ))
  + C (h ^(3:ℕ) * (2 * a ^(7:ℕ) * b ^(3:ℕ) - a ^(2:ℕ) * b ^(8:ℕ))) * (X 0 * (X 1) ^(3:ℕ) * X 2)

/-- The seven monomials of `sdualT a b h` which are not of total degree five. -/
noncomputable def sdG5hLower (a b h : K) : MvPolynomial (Fin 3) K :=
    C (-(a ^(5:ℕ) * b ^(5:ℕ) * h))
  + C (h ^(3:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * ((X 0) ^(3:ℕ) * X 2)
  + C (h ^(2:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * (X 0 * X 1)
  - C (h ^(3:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * ((X 0) ^(2:ℕ) * (X 1) ^(2:ℕ))
  - C (h ^(2:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * (X 0 * (X 2) ^(2:ℕ))
  + C (h ^(2:ℕ) * (3 * a ^(4:ℕ) * b ^(6:ℕ) - a ^(9:ℕ) * b)) * ((X 1) ^(2:ℕ) * X 2)
  + C (h ^(2:ℕ) * (2 * a ^(7:ℕ) * b ^(3:ℕ) - a ^(2:ℕ) * b ^(8:ℕ))) * (X 1 * (X 2) ^(3:ℕ))

/-- **`sdualT a b h = sdG5h a b h + sdG5hLower a b h`.** -/
theorem sdualT_eq_sdG5h_add (a b h : K) :
    Work.MotK.TGen.sdualT a b h = sdG5h a b h + sdG5hLower a b h := by
  rw [Work.MotK.TwCensus.sdualT_explicit, sdG5h, sdG5hLower]
  simp only [map_neg, map_mul, map_pow, map_add, map_sub, map_ofNat, map_one]
  first | refl_ring1 | ring

/-- `sdG5h a b h` is homogeneous of degree `5`. -/
theorem sdG5h_isHomogeneous (a b h : K) : (sdG5h a b h).IsHomogeneous 5 := by
  have t1 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h ^(4:ℕ))) * (X (0 : Fin 3)) ^(5:ℕ) :
      MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (σ := Fin 3) _).mul (isHomogeneous_X_pow (R := K) 0 5)
  have t2 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h ^(3:ℕ))) * (X (1 : Fin 3)) ^(5:ℕ) :
      MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (σ := Fin 3) _).mul (isHomogeneous_X_pow (R := K) 1 5)
  have t3 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h ^(2:ℕ))) * (X (2 : Fin 3)) ^(5:ℕ) :
      MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (σ := Fin 3) _).mul (isHomogeneous_X_pow (R := K) 2 5)
  have t4 : (C (h ^(3:ℕ) * (3 * a ^(4:ℕ) * b ^(6:ℕ) - a ^(9:ℕ) * b)) *
      ((X (0 : Fin 3)) ^(2:ℕ) * X 1 * (X 2) ^(2:ℕ)) : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (σ := Fin 3) _).mul
      (((isHomogeneous_X_pow (R := K) 0 2).mul (isHomogeneous_X (R := K) 1)).mul
        (isHomogeneous_X_pow (R := K) 2 2))
  have t5 : (C (h ^(3:ℕ) * (2 * a ^(7:ℕ) * b ^(3:ℕ) - a ^(2:ℕ) * b ^(8:ℕ))) *
      (X (0 : Fin 3) * (X 1) ^(3:ℕ) * X 2) : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (σ := Fin 3) _).mul
      (((isHomogeneous_X (R := K) 0).mul (isHomogeneous_X_pow (R := K) 1 3)).mul
        (isHomogeneous_X (R := K) 2))
  rw [sdG5h]
  exact (((t1.add t2).add t3).add t4).add t5

/-- A polynomial which is homogeneous of degree `≤ 4` has total degree `≤ 4`. -/
private lemma td_of_hom {f : MvPolynomial (Fin 3) K} {n : ℕ} (h : f.IsHomogeneous n)
    (hn : n ≤ 4) : f.totalDegree ≤ 4 := h.totalDegree_le.trans hn

/-- The lower part `sdG5hLower a b h` has total degree `< 5`. -/
theorem sdG5hLower_totalDegree (a b h : K) : (sdG5hLower a b h).totalDegree < 5 := by
  have t1 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h)) : MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    td_of_hom (isHomogeneous_C (σ := Fin 3) _) (by norm_num)
  have t2 : (C (h ^(3:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * ((X (0 : Fin 3)) ^(3:ℕ) * X 2) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    td_of_hom ((isHomogeneous_C (σ := Fin 3) _).mul
      ((isHomogeneous_X_pow (R := K) 0 3).mul (isHomogeneous_X (R := K) 2))) (by norm_num)
  have t3 : (C (h ^(2:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * (X (0 : Fin 3) * X 1) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    td_of_hom ((isHomogeneous_C (σ := Fin 3) _).mul
      ((isHomogeneous_X (R := K) 0).mul (isHomogeneous_X (R := K) 1))) (by norm_num)
  have t4 : (C (h ^(3:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * ((X (0 : Fin 3)) ^(2:ℕ) * (X 1) ^(2:ℕ)) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    td_of_hom ((isHomogeneous_C (σ := Fin 3) _).mul
      ((isHomogeneous_X_pow (R := K) 0 2).mul (isHomogeneous_X_pow (R := K) 1 2)))
      (by norm_num)
  have t5 : (C (h ^(2:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * (X (0 : Fin 3) * (X 2) ^(2:ℕ)) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    td_of_hom ((isHomogeneous_C (σ := Fin 3) _).mul
      ((isHomogeneous_X (R := K) 0).mul (isHomogeneous_X_pow (R := K) 2 2)))
      (by norm_num)
  have t6 : (C (h ^(2:ℕ) * (3 * a ^(4:ℕ) * b ^(6:ℕ) - a ^(9:ℕ) * b)) * ((X (1 : Fin 3)) ^(2:ℕ) * X 2) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    td_of_hom ((isHomogeneous_C (σ := Fin 3) _).mul
      ((isHomogeneous_X_pow (R := K) 1 2).mul (isHomogeneous_X (R := K) 2))) (by norm_num)
  have t7 : (C (h ^(2:ℕ) * (2 * a ^(7:ℕ) * b ^(3:ℕ) - a ^(2:ℕ) * b ^(8:ℕ))) * (X (1 : Fin 3) * (X 2) ^(3:ℕ)) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    td_of_hom ((isHomogeneous_C (σ := Fin 3) _).mul
      ((isHomogeneous_X (R := K) 1).mul (isHomogeneous_X_pow (R := K) 2 3))) (by norm_num)
  rw [sdG5hLower]
  refine lt_of_le_of_lt ?_ (by norm_num : (4 : ℕ) < 5)
  have s12 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h))
      + C (h ^(3:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * ((X (0 : Fin 3)) ^(3:ℕ) * X 2) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    (totalDegree_add _ _).trans (max_le t1 t2)
  have s123 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h))
      + C (h ^(3:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * ((X (0 : Fin 3)) ^(3:ℕ) * X 2)
      + C (h ^(2:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * (X (0 : Fin 3) * X 1) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    (totalDegree_add _ _).trans (max_le s12 t3)
  have s1234 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h))
      + C (h ^(3:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * ((X (0 : Fin 3)) ^(3:ℕ) * X 2)
      + C (h ^(2:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * (X (0 : Fin 3) * X 1)
      - C (h ^(3:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * ((X (0 : Fin 3)) ^(2:ℕ) * (X 1) ^(2:ℕ)) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    (totalDegree_sub _ _).trans (max_le s123 t4)
  have s12345 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h))
      + C (h ^(3:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * ((X (0 : Fin 3)) ^(3:ℕ) * X 2)
      + C (h ^(2:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * (X (0 : Fin 3) * X 1)
      - C (h ^(3:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * ((X (0 : Fin 3)) ^(2:ℕ) * (X 1) ^(2:ℕ))
      - C (h ^(2:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * (X (0 : Fin 3) * (X 2) ^(2:ℕ)) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    (totalDegree_sub _ _).trans (max_le s1234 t5)
  have s123456 : (C (-(a ^(5:ℕ) * b ^(5:ℕ) * h))
      + C (h ^(3:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * ((X (0 : Fin 3)) ^(3:ℕ) * X 2)
      + C (h ^(2:ℕ) * (2 * a ^(3:ℕ) * b ^(7:ℕ) + a ^(8:ℕ) * b ^(2:ℕ))) * (X (0 : Fin 3) * X 1)
      - C (h ^(3:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * ((X (0 : Fin 3)) ^(2:ℕ) * (X 1) ^(2:ℕ))
      - C (h ^(2:ℕ) * (3 * a ^(6:ℕ) * b ^(4:ℕ) + a * b ^(9:ℕ))) * (X (0 : Fin 3) * (X 2) ^(2:ℕ))
      + C (h ^(2:ℕ) * (3 * a ^(4:ℕ) * b ^(6:ℕ) - a ^(9:ℕ) * b)) * ((X (1 : Fin 3)) ^(2:ℕ) * X 2) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 4 :=
    (totalDegree_add _ _).trans (max_le s12345 t6)
  exact (totalDegree_add _ _).trans (max_le s123456 t7)

end Work.MotK.TGen
