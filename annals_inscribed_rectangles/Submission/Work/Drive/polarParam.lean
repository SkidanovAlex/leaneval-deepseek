import Mathlib

/-!
# The polar parametrisation of the disk by (direction, signed radius)

The radial-collapse transport (Hugelmeyer's Lemma 2, `Submission/Work/Drive/TRANSPORT_COLLAPSE_STATUS.md`)
computes the collapsed count at `s = 1` by *reparametrising the box fibres*: a point `u` of the parameter
square corresponds to the disk point `ζ u = sqDisk (foldBox u)`, and the two conditions
`colPlane β Q 1 u = V y` (the collapsed plane) and `diskPlane Q u = W z` (the plane itself) read, in the
coordinates

> `ζ u = (1 - 2 σ) · e^{i π t}`  (`t` = direction, `σ` = signed radius),

exactly as `coreLoop Q t = V y` and `diamLoop Q t σ = W z`.  This file provides the two functions

* `dirParam z` — the **direction** of `z`, lying in `[0, 1)`;
* `radParam z` — the **signed radius** of `z`, lying in `[0, 1]` for `‖z‖ ≤ 1`,

characterised by the identity `z = (1 - 2 radParam z) · exp (π i dirParam z)` (`radParam z = 1/2` iff
`z = 0`), and by the *uniqueness* of the pair: a pair `(t, σ) ∈ [0,1) × [0,1]` with
`z = (1 - 2σ) · exp (π i t)` is `(dirParam z, radParam z)`.  The uniqueness is what makes the
reparametrisation a bijection and is proved as `Work.Drive.polarParam_unique`.

The construction is elementary: on the branch `0 ≤ arg z` one takes `t = arg z / π` and
`σ = (1 - ‖z‖)/2`, on the branch `arg z < 0` one takes `t = arg z/π + 1` and `σ = (1 + ‖z‖)/2`, and on
the single remaining ray (`arg z = π`, the negative real axis) one takes `t = 0`, `σ = (1 + ‖z‖)/2`.
-/

noncomputable section

namespace Work.Drive

/-- **The direction of `z`**: the unique `t ∈ [0,1)` with `z = (1 - 2σ) · e^{iπt}` for some `σ ∈ [0,1]`. -/
def dirParam (z : ℂ) : ℝ :=
  if Complex.arg z = Real.pi then 0
  else if 0 ≤ Complex.arg z then Complex.arg z / Real.pi
  else Complex.arg z / Real.pi + 1

/-- **The signed radius of `z`**: the unique `σ ∈ [0,1]` with `z = (1 - 2σ) · e^{iπ (dirParam z)}`
(`σ < 1/2` iff `z` points in the direction `dirParam z`, `σ > 1/2` iff it points the other way). -/
def radParam (z : ℂ) : ℝ :=
  if Complex.arg z = Real.pi then (1 + ‖z‖) / 2
  else if 0 ≤ Complex.arg z then (1 - ‖z‖) / 2
  else (1 + ‖z‖) / 2

end Work.Drive
