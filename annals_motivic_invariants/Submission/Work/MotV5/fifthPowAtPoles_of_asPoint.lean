import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.tp_as

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# From an Artin–Schreier point to the fifth-power pole condition

`Work.MotV5.FifthPowAtPoles 𝕜 K g` asks that the value of `g` be a fifth power of the value group
at every valuation of `K` trivial on `𝕜` at which `g` has a pole.  This file proves that it is
*implied* by the existence of a `K`-rational point of the Artin–Schreier twist `C^AS_g` of the
Klein curve, in the coordinate form consumed by the master valuation lemma
`Work.MotV5.tp_as`: a tuple `y : Fin 5 → K` with `y ≠ 0` whose *Galois coordinates*
`x_k = ∑_j y_j (W + k)^j` (`W⁵ - W = g`, i.e. `Work.MotV.asCoord (asRoot g) y`) satisfy the Klein
equations `kleinP a b x k = 0`.

This is the characteristic-`5` analogue of the characteristic-`≠ 5` step "TP applied to the
`K`-point of the twisted curve `C_{h₁h₂^{±1}}`" in the proof of the rigidity of the link: the
cocycle comparison comparing two isomorphic twists produces such a point, and this lemma converts
it into the fifth-power condition whose negation is `Work.MotV5.exponent_rigidity_AS`.

The proof is a direct instantiation of `tp_as` over `RatFunc 𝕜`: the Klein parameters `D.a`, `D.b`
are constants of the base field, so at every valuation trivial on `𝕜` the two hypotheses
`v a = 1` and `v (a² - ab - b²) = 1` of `tp_as` are automatic (`D.a * D.b ≠ 0` and
`D.a ^ 2 - D.a * D.b - D.b ^ 2 ≠ 0` hold for `ASGood D`). -/

set_option autoImplicit false

namespace Work.MotV5

open Work.MotV

/-- **The Artin–Schreier point of `C^AS_g` forces `g` to be fifth-power valued at its poles.**
Given Klein data `D` in characteristic `5`, a class `g : RatFunc 𝕜` and a nonzero tuple
`y : Fin 5 → RatFunc 𝕜` whose Galois coordinates `asCoord (asRoot g) y` satisfy the Klein equations
`kleinP a b · k = 0`, every valuation of `RatFunc 𝕜`, trivial on `𝕜`, at which `g` has a pole has
`v g` a fifth power of the value group. -/
theorem fifthPowAtPoles_of_asPoint (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : KleinData.ASGood D) (g : RatFunc 𝕜)
    (y : Fin 5 → RatFunc 𝕜) (hy : y ≠ 0)
    (heq : ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
      (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
      (Work.MotV.asCoord (asRoot g)
        (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j))) k = 0) :
    FifthPowAtPoles 𝕜 (RatFunc 𝕜) g := by
  obtain ⟨hGood, -, -, hsm⟩ := hD
  intro v hv hg
  have ha_ne : D.a ≠ 0 := fun h0 =>
    Work.MotV.KleinData.Good.ab_ne hGood (by rw [h0, zero_mul])
  have hb_ne : D.b ≠ 0 := fun h0 =>
    Work.MotV.KleinData.Good.ab_ne hGood (by rw [h0, mul_zero])
  refine tp_as (F := RatFunc 𝕜) (L := Work.MotV.Kb 𝕜) v (asRoot g) g (asRoot_spec g)
    (a := algebraMap 𝕜 (RatFunc 𝕜) D.a) (b := algebraMap 𝕜 (RatFunc 𝕜) D.b)
    (hv D.a ha_ne) (hv D.b hb_ne) ?_ hy heq hg
  have hconst : (algebraMap 𝕜 (RatFunc 𝕜) D.a) ^ 2
      - (algebraMap 𝕜 (RatFunc 𝕜) D.a) * (algebraMap 𝕜 (RatFunc 𝕜) D.b)
      - (algebraMap 𝕜 (RatFunc 𝕜) D.b) ^ 2
      = algebraMap 𝕜 (RatFunc 𝕜) (D.a ^ 2 - D.a * D.b - D.b ^ 2) := by
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
  rw [hconst]
  exact hv _ hsm

end Work.MotV5
