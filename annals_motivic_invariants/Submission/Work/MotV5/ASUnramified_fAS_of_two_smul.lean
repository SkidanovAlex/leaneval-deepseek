import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.ASUnramified_smul_of_pow_eq

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The bridge with a parameter different from the class of the field

`Work.MotV5.Nodes.bridge_AS` (and `Nodes/fifthPowAtPoles_AS`, `Nodes/poleFibre_asTwist`) is stated
for the twist field of a class `g` with the *same* `g` as the parameter.  The rigidity, however,
needs the bridge on the twist field `F_{2·fAS}` at the parameter `fAS` (see
`Nodes/v1_AS_of_bridge`, hypothesis `hB₂`): this is the instance that `Work.MotV5.base_preserved_AS`
consumes when it is applied to `θ.symm`.

The two parameters differ by a nonzero element of the prime field
(`2 • fAS 𝕜 = 2 · fAS 𝕜`, and `fAS 𝕜 = 3 · (2 • fAS 𝕜)` in characteristic `5`), and `℘` is
`𝔽₅`-linear, so the two bridge conditions are *equivalent*:
`Work.MotV5.ASUnramified_smul_of_pow_eq` (proved) gives the implication
`ASUnramified 𝕜 F t (c · g) → ASUnramified 𝕜 F t g` for `c⁵ = c`, `c ≠ 0`.

The corollary below is the only instance the branch uses: the parameter `fAS 𝕜` on a twist field for
which the parameter `2 • fAS 𝕜` is known to be unramified. -/

set_option autoImplicit false

namespace Work.MotV5

/-- **The bridge at the parameter `fAS 𝕜` follows from the bridge at `2 • fAS 𝕜`.**  Indeed
`algebraMap (2 • fAS 𝕜) = algebraMap (2 : 𝕜) * algebraMap (fAS 𝕜)`, and `2⁵ = 2 ≠ 0` in
characteristic `5`, so `Work.MotV5.ASUnramified_smul_of_pow_eq` with `c := 2` applies. -/
theorem ASUnramified_fAS_of_two_smul (𝕜 F : Type) [Field 𝕜] [CharP 𝕜 5] [Field F] [Algebra 𝕜 F]
    [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F] (t : F)
    (h : Work.MotV5.ASUnramified 𝕜 F t (algebraMap (RatFunc 𝕜) F (2 • Work.MotV.fAS 𝕜))) :
    Work.MotV5.ASUnramified 𝕜 F t (algebraMap (RatFunc 𝕜) F (Work.MotV.fAS 𝕜)) := by
  have hpar : algebraMap (RatFunc 𝕜) F (2 • Work.MotV.fAS 𝕜)
      = algebraMap 𝕜 F (2 : 𝕜) * algebraMap (RatFunc 𝕜) F (Work.MotV.fAS 𝕜) := by
    rw [nsmul_eq_mul, Nat.cast_ofNat, ← map_ofNat (algebraMap 𝕜 (RatFunc 𝕜)) 2,
      IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) F, map_mul]
  rw [hpar] at h
  have hc5 : (2 : 𝕜) ^ 5 = 2 := by
    rw [show (2 : 𝕜) ^ 5 = ((32 : ℕ) : 𝕜) by norm_num,
      CharP.cast_eq_mod 𝕜 5 32]
    norm_num
  have hc0 : (2 : 𝕜) ≠ 0 := by
    intro h0
    have h2 : ((2 : ℕ) : 𝕜) = 0 := by simpa using h0
    have hdvd : 5 ∣ 2 := (CharP.cast_eq_zero_iff 𝕜 5 2).mp h2
    norm_num at hdvd
  exact ASUnramified_smul_of_pow_eq 𝕜 F t (algebraMap (RatFunc 𝕜) F (Work.MotV.fAS 𝕜)) (2 : 𝕜)
    hc5 hc0 h

end Work.MotV5
