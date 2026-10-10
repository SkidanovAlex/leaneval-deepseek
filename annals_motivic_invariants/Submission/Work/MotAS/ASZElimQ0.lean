import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZElim.Q0` — the `X 1 = 0` slice of the AS eliminant

`Q0 a b g` is the univariate polynomial obtained from `Work.MotAS.ASZElim.P a b g` by setting the
second variable (`X 1`, the chart coordinate `X₂`) to `0`, i.e. it is the sum of the `X 1`-free
terms of the eliminant:

`Q0 a b g = c5 · X^5 + c4 · X^4 + C · X^3 + F · X^2 + M`

with (in characteristic `5`)

* `c5 = a^5 g^2 - a^3 b^2 + 2 a^2 b^3 + 2 b^5 g^2`,
* `c4 = 2 a^4 b + 2 a^3 b^2 - a^2 b^3 + a b^4`,
* `C  = -a^5 - a^4 b + 2 a^3 b^2 + a^2 b^3 - 2 a b^4 + 2 b^5`,
* `F  = 2 a^5 - b^5`,
* `M  = -a^5 - 2 b^5`.

## Why this slice matters

For a hypothetical factorisation `P a b g = A * B` in `K[X 0, X 1]` (with `A` of total degree
`≤ 2`, which always holds for one of the two factors), specialising `X 1 = 0` gives
`Q0 a b g = A(X 0, 0) * B(X 0, 0)`, so `A(X 0, 0)` — a polynomial of degree `≤ 2` — divides
`Q0 a b g`.  Hence: **if `Q0 a b g` has no factor of degree `1` or `2`, then `P a b g` is
irreducible**.  This is the reduction used in `Submission/Work/MotAS/aszPPrime.lean`.

## The key lemma (`Q0` has no small factor)

`Work.MotAS.Q0_no_dvd_of_degree_le_two` states that `Q0 a b g` has no factor of degree `1` or `2`
under the hypotheses `a ^ 2 - a * b - b ^ 2 ≠ 0` and `g ∉ ℘(K)`.  Route (verified numerically over
`𝔽₅` for all `80` admissible `(a, b, g)`, and described in `Submission/Work/MotAS/aszPPrime.lean`):
over `L := K(θ)`, `θ ^ 5 - θ = g` (a degree-`5` extension, since `g ∉ ℘(K)`), the slice **splits
completely**,

`Q0 a b g = c5 * ∏_{i ∈ 𝔽₅} (X + δ(θ + i))`

for an explicit polynomial `δ ∈ K[X]` of degree `≤ 4`; the roots are permuted in a `5`-cycle by
the `K`-automorphism `θ ↦ θ + 1` of `L`, are pairwise distinct, and the conjugacy argument
`Work.MotAS.ASZElimSigmaIrr` then gives irreducibility of `Q0 a b g` over `K`.
-/

set_option autoImplicit false

namespace Work.MotAS.ASZElim

open Polynomial

variable {K : Type*} [Field K]

/-- The `X 1 = 0` slice of the AS eliminant `Work.MotAS.ASZElim.P a b g`. -/
noncomputable def Q0 (a b g : K) : Polynomial K :=
  C (a ^(5:ℕ) * g ^(2:ℕ) - a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ) + 2 * b ^(5:ℕ) * g ^(2:ℕ)) * X ^(5:ℕ)
  + C (2 * a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) - a ^(2:ℕ) * b ^(3:ℕ) + a * b ^(4:ℕ)) * X ^(4:ℕ)
  + C (-a ^(5:ℕ) - a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) - 2 * a * b ^(4:ℕ) + 2 * b ^(5:ℕ)) * X ^(3:ℕ)
  + C (2 * a ^(5:ℕ) - b ^(5:ℕ)) * X ^(2:ℕ)
  + C (-a ^(5:ℕ) - 2 * b ^(5:ℕ))

end Work.MotAS.ASZElim

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K]

/-- The eliminant `Work.MotAS.ASZElim.P a b g`, regrouped by powers of `X 0`. -/
theorem aszP_eq (a b g : K) :
    ASZElim.P a b g
      = C (a ^(5:ℕ) * g ^(2:ℕ) - a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ) + 2 * b ^(5:ℕ) * g ^(2:ℕ)) * (X 0) ^(5:ℕ)
        + C (2 * a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) - a ^(2:ℕ) * b ^(3:ℕ) + a * b ^(4:ℕ)) * (X 0) ^(4:ℕ)
        + (C (a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ)) * (X 1) ^(2:ℕ)
            + C (-2 * a ^(5:ℕ) * g + b ^(5:ℕ) * g) * X 1
            + C (-a ^(5:ℕ) - a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) - 2 * a * b ^(4:ℕ) + 2 * b ^(5:ℕ)))
          * (X 0) ^(3:ℕ)
        + (C (a ^(4:ℕ) * b * g + a ^(3:ℕ) * b ^(2:ℕ) * g + 2 * a ^(2:ℕ) * b ^(3:ℕ) * g - 2 * a * b ^(4:ℕ) * g) * (X 1) ^(3:ℕ)
            + C (a ^(4:ℕ) * b + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) + 2 * a * b ^(4:ℕ)) * (X 1) ^(2:ℕ)
            + C (2 * a ^(5:ℕ) - b ^(5:ℕ))) * (X 0) ^(2:ℕ)
        + (C (-a ^(5:ℕ) * g ^(2:ℕ) - 2 * b ^(5:ℕ) * g ^(2:ℕ)) * (X 1) ^(4:ℕ)
            + C (-2 * a ^(5:ℕ) * g - 2 * a ^(4:ℕ) * b * g - a ^(3:ℕ) * b ^(2:ℕ) * g + 2 * a ^(2:ℕ) * b ^(3:ℕ) * g
                + a * b ^(4:ℕ) * g - b ^(5:ℕ) * g) * (X 1) ^(3:ℕ)
            + C (-a ^(5:ℕ) - a ^(4:ℕ) * b - a ^(3:ℕ) * b ^(2:ℕ) - 2 * a ^(2:ℕ) * b ^(3:ℕ) + 2 * a * b ^(4:ℕ) - 2 * b ^(5:ℕ))
              * (X 1) ^(2:ℕ)) * X 0
        + (C (2 * a ^(5:ℕ) * g ^(3:ℕ) - b ^(5:ℕ) * g ^(3:ℕ)) * (X 1) ^(5:ℕ)
            + C (-a ^(5:ℕ) * g - 2 * b ^(5:ℕ) * g) * (X 1) ^(3:ℕ)
            + C (a ^(5:ℕ) + a ^(4:ℕ) * b - 2 * a ^(3:ℕ) * b ^(2:ℕ) - a ^(2:ℕ) * b ^(3:ℕ) + 2 * a * b ^(4:ℕ) - 2 * b ^(5:ℕ))
              * (X 1) ^(2:ℕ)
            + C (-a ^(5:ℕ) - 2 * b ^(5:ℕ))) := by
  simp only [ASZElim.P]
  first | refl_ring1 | ring

variable (K) in
/-- The algebra map `K[X 0, X 1] → K[X]` sending `X 0 ↦ X` and `X 1 ↦ 0` (the slice `X 1 = 0`). -/
noncomputable def aszSlice :
    MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (Polynomial.X : Polynomial K) else 0)

variable (K) in
@[simp] lemma aszSlice_X0 :
    aszSlice K (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) = Polynomial.X := by
  simp [aszSlice]

variable (K) in
@[simp] lemma aszSlice_X1 :
    aszSlice K (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) = 0 := by
  simp [aszSlice]

variable (K) in
@[simp] lemma aszSlice_C (c : K) :
    aszSlice K (MvPolynomial.C c) = Polynomial.C c := by
  simp [aszSlice]

/-- The slice of the eliminant is `Work.MotAS.ASZElim.Q0`. -/
theorem aszSlice_aszP (a b g : K) :
    aszSlice K (ASZElim.P a b g) = ASZElim.Q0 a b g := by
  rw [aszP_eq]
  simp only [map_add, map_mul, map_pow, aszSlice_X0, aszSlice_X1, aszSlice_C, ASZElim.Q0]
  first | refl_ring1 | ring

end Work.MotAS
