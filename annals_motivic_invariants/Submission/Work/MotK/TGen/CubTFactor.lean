import Mathlib
import Submission.Work.MotK.TGen.CubTRedDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.CubTFactor` — the exact factorisation `cubT = C (a·b·h) · cubTRed`

The cubic `cubT a b h = kleinTwBilin p (kleinTwR chart3)` (the junk cone factor of the target
equation of the `T`-twisted link) is exactly `a·b·h` times the normalised cubic `cubTRed a b h`
of `Submission/Work/MotK/TGen/CubTRedDefs.lean`:

  `cubT a b h = C (a·b·h) · cubTRed a b h`.

Proof.  The polar form of the T-twisted quadric `kleinTwQ = kleinTwP0` expands as

  `kleinTwBilin a b h u v = -2ab·u₀v₀ + a²h·(u₂v₃ + u₃v₂) - b²h·(u₁v₄ + u₄v₁)`,

and at the rational point `p = pRa a b h = (1,0,1,b/(a·h),0)` the only surviving terms are
`v₀`, `v₃` and `v₂`, with the field identity `a²h · (b/(a·h)) = a·b` (needing `a ≠ 0`, `h ≠ 0`)
turning the `v₂`-coefficient into `a·b`.  Substituting `v = kleinTwR chart3` and expanding the
three twisted cubics `R₀, R₂, R₃` at the chart `(0, x₀, x₁, x₂, 1)` leaves a polynomial identity
in `K[a,b,h][x₀,x₁,x₂]`, closed by `ring` after pushing all `MvPolynomial.C` of products into
products of `C`s.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

/-- **The polar expansion of the T-twisted Klein quadric**: the polar form of
`kleinTwQ = kleinTwP0` is `-2ab·u₀v₀ + a²h·(u₂v₃ + u₃v₂) - b²h·(u₁v₄ + u₄v₁)`. -/
lemma kleinTwBilin_polar' {R : Type*} [CommRing R] (a b h : R) (u v : Fin 5 → R) :
    Work.MotK.kleinTwBilin a b h u v
      = -2*a*b*(u 0 * v 0) + a^2*h*(u 2 * v 3 + u 3 * v 2)
          - b^2*h*(u 1 * v 4 + u 4 * v 1) := by
  simp only [Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ, Work.MotK.kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

/-- **The polar form at the link point `pRa`**: for `p = pRa a b h = (1,0,1,b/(a·h),0)` the
polar form reduces to `-2ab·v₀ + a²h·v₃ + ab·v₂` (the `v₂`-coefficient `a²h·(b/(a·h))` being
`a·b`). -/
lemma kleinTwBilin_pRa_eq (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (v : Fin 5 → MvPolynomial (Fin 3) K) :
    Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (Work.MotK.pRa a b h) v
      = -(2 * MvPolynomial.C a * MvPolynomial.C b) * v 0
        + (MvPolynomial.C a ^ 2 * MvPolynomial.C h) * v 3
        + (MvPolynomial.C a * MvPolynomial.C b) * v 2 := by
  rw [kleinTwBilin_polar']
  have hc : a^2 * h * (b / (a*h)) = a * b := by
    have h1 : a * h ≠ 0 := mul_ne_zero ha hh
    field_simp
  have hca : ((MvPolynomial.C a)^2 * MvPolynomial.C h : MvPolynomial (Fin 3) K)
      = MvPolynomial.C (a^2*h) := by rw [← MvPolynomial.C_pow, ← MvPolynomial.C_mul]
  have hab : (MvPolynomial.C (a^2*h) * MvPolynomial.C (b/(a*h)) : MvPolynomial (Fin 3) K)
      = MvPolynomial.C (a*b) := by rw [← MvPolynomial.C_mul, hc]
  have hCab : (MvPolynomial.C (a*b) : MvPolynomial (Fin 3) K)
      = MvPolynomial.C a * MvPolynomial.C b := by rw [MvPolynomial.C_mul]
  simp only [Work.MotK.pRa_apply, Work.MotK.kleinPointT, Fin.isValue,
    map_one, map_zero, zero_mul, mul_zero, add_zero, sub_zero, one_mul]
  rw [hca, mul_add,
    show (MvPolynomial.C (a^2*h) * (MvPolynomial.C (b/(a*h)) * v 2) : MvPolynomial (Fin 3) K)
      = MvPolynomial.C (a*b) * v 2 by rw [← mul_assoc, hab],
    hCab]
  first | refl_ring1 | ring

theorem CubTFactor (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.TGen.cubT a b h = MvPolynomial.C (a * b * h) * Work.MotK.TGen.cubTRed a b h := by
  rw [Work.MotK.TGen.cubT, kleinTwBilin_pRa_eq K a b h ha hh]
  simp only [Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2,
    Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.chart3]
  simp
  simp only [Work.MotK.TGen.cubTRed]
  simp only [map_mul, map_pow, map_ofNat]
  first | refl_ring1 | ring

end Work.MotK.TGen
