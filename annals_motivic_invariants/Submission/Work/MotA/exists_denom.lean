import Mathlib
import Submission.Work.MotA.SpreadAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotA

open MvPolynomial

/-- **`S1`, denominator clearing for the spread localisation.**

Let `K = RatFunc 𝕜`, `A = K[x₁,…,xₙ]`, `B = 𝕜[t,x₁,…,xₙ]`, `f = spreadMap 𝕜 n : B →ₐ[𝕜] A` (so
that `f(B) = 𝕜[t][x₁,…,xₙ]`), `G ∈ A` and `G₀ ∈ B` with `f(G₀) = cG0 · G` for some nonzero
`cG0 ∈ 𝕜[t]`.  Then every element `y` of the localisation `S = A_{(G)}` becomes a `B`-element after
multiplication by a suitable power of `awayMap (G₀ · tPoly h)`, for `h` ranging over the multiples of
a fixed nonzero `d ∈ 𝕜[t]`.

Concretely, write `y = a / G^k` with `a ∈ A` (`IsLocalization.Away.surj`) and pick `0 ≠ d ∈ 𝕜[t]`
and `b₀ ∈ B` with `f(b₀) = d · a` (`exists_clearing`).  For `h = d·m` and `M = k+1` one has
`y · (awayMap (G₀ · tPoly h))^{k+1} = awayMap b` with `b = tPoly ((cG0·d·m)^k·m) · b₀ · G₀`: indeed
in `S`, using `awayMap (G₀·tPoly h) = (cG0 h)·[G]`, the `[G]^{k+1}` of the power cancels the
`[G]^{-k}` of `y` up to a single factor `[G]`, and the extra `h^k` clears the `t`-denominators of
`a`. -/
theorem exists_denom (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (G : MvPolynomial (Fin n) (RatFunc 𝕜)) (G₀ : MvPolynomial (Fin (n + 1)) 𝕜)
    (cG0 : Polynomial 𝕜) (hcG0 : cG0 ≠ 0)
    (hG₀ : Work.MotA.spreadMap 𝕜 n G₀ =
      MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cG0) * G)
    (y : Localization.Away G) :
    ∃ d : Polynomial 𝕜, d ≠ 0 ∧ ∀ h : Polynomial 𝕜, d ∣ h →
      ∃ (M : ℕ) (b : MvPolynomial (Fin (n + 1)) 𝕜),
        y * Work.MotA.awayMap 𝕜 n G (G₀ * Work.MotA.tPoly 𝕜 n h) ^ M =
          Work.MotA.awayMap 𝕜 n G b := by
  classical
  -- Write `y` over the common denominator `G ^ k`; `a` is its numerator in `A`.
  obtain ⟨k, a, hk⟩ := IsLocalization.Away.surj G y
  -- Clear the `t`-denominators of `a`: `f b₀ = d · a` for a nonzero `d ∈ 𝕜[t]`.
  obtain ⟨d, hd, b0, hb0⟩ := exists_clearing 𝕜 n a
  refine ⟨d, hd, ?_⟩
  intro h hdh
  obtain ⟨m, rfl⟩ := hdh
  -- `M = k + 1` (the extra factor of `[G]` is absorbed by the numerator).
  refine ⟨k + 1, tPoly 𝕜 n ((cG0 * (d * m)) ^ k * m) * b0 * G₀, ?_⟩
  -- The image of `G₀ · tPoly (d·m)` under `spreadMap` is `G · C (cG0·d·m)`.
  have hsp : spreadMap 𝕜 n (G₀ * tPoly 𝕜 n (d * m)) =
      G * MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))) := by
    rw [map_mul, hG₀, spreadMap_tPoly]
    rw [map_mul (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) cG0 (d * m)]
    rw [MvPolynomial.C_mul]
    first | refl_ring1 | ring
  -- Left-hand side.
  have hL : y * awayMap 𝕜 n G (G₀ * tPoly 𝕜 n (d * m)) ^ (k + 1)
      = (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
          (a * G *
            MvPolynomial.C ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))) ^ (k + 1))) := by
    rw [awayMap_apply, hsp]
    have hX : ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) G) ^ (k + 1)
        = ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) G) ^ k
          * (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) G :=
      pow_succ _ _
    have hY : ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
          (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) ^ (k + 1)
        = ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
            (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) ^ k
          * (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
            (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m)))) :=
      pow_succ _ _
    calc y * ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
            (G * MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) ^ (k + 1)
        = y * (((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) G) ^ (k + 1)
            * ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
              (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) ^ (k + 1)) := by
          rw [map_mul, mul_pow]
      _ = (y * ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) G) ^ k)
            * (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) G
            * (((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
              (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) ^ k
              * (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
              (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) := by
          rw [hX, hY]; ring
      _ = (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) a
            * (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) G
            * (((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
              (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) ^ k
              * (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
              (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) := by
          rw [hk]
      _ = (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) (a * G)
            * ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
              (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))))) ^ (k + 1) := by
          rw [← map_mul, ← hY]
      _ = (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)) (a * G)
            * ((algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
              (MvPolynomial.C ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m)))) ^ (k + 1))) := by
          rw [← map_pow]
      _ = (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
            (a * G *
              MvPolynomial.C ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))) ^ (k + 1))) := by
          rw [← map_mul, ← MvPolynomial.C_pow]
  -- Right-hand side.
  have hR : awayMap 𝕜 n G ((tPoly 𝕜 n ((cG0 * (d * m)) ^ k * m)) * b0 * G₀)
      = (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G))
          (a * G *
            MvPolynomial.C ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * (d * m))) ^ (k + 1))) := by
    rw [awayMap_apply]
    rw [map_mul, map_mul, map_mul, spreadMap_tPoly, hb0, hG₀]
    simp only [map_mul, map_pow, mul_pow]
    first | refl_ring1 | ring
  rw [hL, hR]

end Work.MotA
