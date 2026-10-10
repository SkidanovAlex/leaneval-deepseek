import Mathlib
import Submission.Work.MotV.tp
import Submission.Work.MotV.twCoord_eq

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- Node BR (the bridge): the Kummer parameter `h` of the T-twist is fifth-power valued in the
twist field `F_h = twistFieldT D h`, for `h ≠ 0`.

Route.  Apply `Work.MotV.tp` (node TP, available from `Submission.Work.MotV.Aliases`) inside the
field `F = twistFieldT D h` at each valuation `v : Valuation (twistFieldT D h) ℤᵐ⁰` with
`TrivOn 𝕜 v`, with `a := algebraMap 𝕜 (twistFieldT D h) D.a`,
`b := algebraMap 𝕜 (twistFieldT D h) D.b`,
`h := algebraMap (RatFunc 𝕜) (twistFieldT D h) h` and
`y i := algebraMap (twistFieldT D h) (Om D) (twCoord D h i)` (each `twCoord D h i` lies in `F_h`
by construction of `twistFieldT` as the adjoin of `Set.range (twCoord D h)`).
* `v a = v b = 1`: `TrivOn` plus `D.Good.ab_ne` (`a ≠ 0`, `b ≠ 0`).
* `h ≠ 0`: from `hh` and injectivity of the algebra maps of fields.
* `y ≠ 0`: `twCoord D h 0 = w^0 * (κ 0 / κ 0) = 1`.
* the twisted equations: `Work.MotV.twCoord_eq` in `Om D`, pushed into `F_h` by injectivity of
  `algebraMap (twistFieldT D h) (Om D)` (the polynomial `kleinTw` commutes with that map, the
  coefficients `D.a`, `D.b`, `h` being scalars).
`tp` then gives `∃ u : twistFieldT D h, v (algebraMap h) = v u ^ 5`, which is exactly
`FifthPowerValued 𝕜 (algebraMap (RatFunc 𝕜) (twistFieldT D h) h)`. -/
theorem bridge {𝕜 : Type} [Field 𝕜] (D : KleinData 𝕜) (hD : D.Good) (h : RatFunc 𝕜) (hh : h ≠ 0) :
    FifthPowerValued 𝕜 (algebraMap (RatFunc 𝕜) (twistFieldT D h) h) := by
  intro v hv
  -- the twisted point `y`, transported into the twist field `F_h`
  let y : Fin 5 → twistFieldT D h := fun i =>
    ⟨twCoord D h i, IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩
  -- `v` is trivial on `𝕜`, hence on the coefficients `a, b`
  have ha : v (algebraMap 𝕜 (twistFieldT D h) D.a) = 1 :=
    hv D.a fun h0 => hD.ab_ne (by rw [h0, zero_mul])
  have hb : v (algebraMap 𝕜 (twistFieldT D h) D.b) = 1 :=
    hv D.b fun h0 => hD.ab_ne (by rw [h0, mul_zero])
  -- `h ≠ 0` in `F_h` (algebra maps of fields are injective)
  have hhF : algebraMap (RatFunc 𝕜) (twistFieldT D h) h ≠ 0 := by
    intro h0
    exact hh ((algebraMap (RatFunc 𝕜) (twistFieldT D h)).injective (by rw [h0, map_zero]))
  -- the zeroth twisted coordinate is `1`
  have hy0 : y 0 = 1 := by
    apply Subtype.ext
    show twCoord D h 0 = (1 : Om D)
    simp [twCoord, div_self (hD.coord0_ne (Kb 𝕜))]
  have hy : y ≠ 0 := by
    intro hzero
    have h1 : y 0 = 0 := by rw [hzero]; rfl
    rw [hy0] at h1
    exact one_ne_zero h1
  -- the twisted Klein equations, in the twist field
  have heq : ∀ k, kleinTw (algebraMap 𝕜 (twistFieldT D h) D.a)
      (algebraMap 𝕜 (twistFieldT D h) D.b) (algebraMap (RatFunc 𝕜) (twistFieldT D h) h) y k = 0 := by
    intro k
    -- push the equation into `Om D` along the injective algebra map and use `twCoord_eq`
    apply (algebraMap (twistFieldT D h) (Om D)).injective
    rw [map_zero]
    have hφa : (algebraMap (twistFieldT D h) (Om D)) (algebraMap 𝕜 (twistFieldT D h) D.a)
        = algebraMap 𝕜 (Om D) D.a := by
      rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (twistFieldT D h),
        ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (twistFieldT D h) (Om D),
        ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Om D)]
    have hφb : (algebraMap (twistFieldT D h) (Om D)) (algebraMap 𝕜 (twistFieldT D h) D.b)
        = algebraMap 𝕜 (Om D) D.b := by
      rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (twistFieldT D h),
        ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (twistFieldT D h) (Om D),
        ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Om D)]
    have hφh : (algebraMap (twistFieldT D h) (Om D)) (algebraMap (RatFunc 𝕜) (twistFieldT D h) h)
        = algebraMap (RatFunc 𝕜) (Om D) h := by
      rw [← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (twistFieldT D h) (Om D)]
    have hmap : (algebraMap (twistFieldT D h) (Om D))
        (kleinTw (algebraMap 𝕜 (twistFieldT D h) D.a) (algebraMap 𝕜 (twistFieldT D h) D.b)
          (algebraMap (RatFunc 𝕜) (twistFieldT D h) h) y k)
       = kleinTw (algebraMap 𝕜 (Om D) D.a) (algebraMap 𝕜 (Om D) D.b)
          (algebraMap (RatFunc 𝕜) (Om D) h) (twCoord D h) k := by
      simp only [kleinTw, twMon, map_add, map_sub, map_neg, map_mul, map_pow, map_one,
        apply_ite (algebraMap (twistFieldT D h) (Om D)), IntermediateField.algebraMap_apply,
        hφa, hφb, hφh]
      dsimp only [y]
    rw [hmap, twCoord_eq D hD h hh k]
  exact Work.MotV.tp (v := v) (a := algebraMap 𝕜 (twistFieldT D h) D.a)
    (b := algebraMap 𝕜 (twistFieldT D h) D.b)
    (h := algebraMap (RatFunc 𝕜) (twistFieldT D h) h) (y := y) ha hb hhF hy heq

end Work.MotV
