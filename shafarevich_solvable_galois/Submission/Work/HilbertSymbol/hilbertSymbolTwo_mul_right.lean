import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Padics.PadicIntegers
import Submission.Work.HilbertSymbol.epsZ_mul
import Submission.Work.HilbertSymbol.omegaZ_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-!
# Multiplicativity of the `2`-adic Hilbert symbol in the second argument

We prove `(a, b₁ b₂)_2 = (a, b₁)_2 * (a, b₂)_2` for `a b₁ b₂ : ℚˣ`, where `(·,·)_2` is the
explicit `2`-adic Hilbert symbol of `Submission.Work.HilbertSymbol.Basic`:

`(a,b)_2 = signOf (ε(u) ε(v) + α ω(v) + β ω(u))`, with `u = unitPart 2 a`, `v = unitPart 2 b`,
`α = padicVal 2 a`, `β = padicVal 2 b`.

The content is that `ε = epsZ` and `ω = omegaZ` are group homomorphisms `ℤ_[2]ˣ → ZMod 2`
(so `u ↦ unitPart` and `b ↦ padicVal` being multiplicative, the arguments of `signOf` add up),
together with `signOf (m + n) = signOf m * signOf n`.
-/

theorem hilbertSymbolTwo_mul_right (a b₁ b₂ : ℚˣ) :
    hilbertSymbolTwo a (b₁ * b₂) = hilbertSymbolTwo a b₁ * hilbertSymbolTwo a b₂ := by
  simp only [hilbertSymbolTwo]
  rw [unitPart_mul, padicVal_mul, epsZ_mul, omegaZ_mul, ← signOf_add]
  congr 1
  push_cast
  ring

end Work.HilbertSymbol
