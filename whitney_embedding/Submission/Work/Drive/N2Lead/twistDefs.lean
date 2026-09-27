import Mathlib
import Submission.Work.Drive.N2C.defs

/-!
# Tier D (`D2d`): the twist toolkit of the Möbius saddle certificate

The definitions of §4 `D2d.1` of `Submission/Work/Drive/N2Lead/NOTES_LEAD_mobiusSaddle.md`
(the note writes them in namespace `Work.Drive.N2C`; here they are `Work.Drive.N2Lead`):

* `rot02 t`, `rot12 t` — the rotations of `ℝ³` about the axes `e₁` and `e₀`;
* `twistY a s` — the horizontal **slab twist** about the `y`-axis, rigid outside the slab
  `|y| < a`; `twistY a 1` is the half-turn `(x, y, z) ↦ (-x, y, -z)` for `y ≤ -a`;
* `twistX ε s` — the vertical slab twist about the `x`-axis, rigid outside `|x| < ε`;
  `twistX ε (-1)` is `(x, y, z) ↦ (x, -y, -z)` for `x ≥ ε`;
* `pushY D ε s` — the vertical push, rigid off `|y| < ε`;
* `AmbientPath F` — the hypotheses of the level-isotopy constructor
  `Work.Drive.N2C.isLevelIsotopy_ambient` (Tier B1), together with `F 0 = id`;
* `StarAboutZero g I` — the star-shapedness (positive angular rate) condition consumed by the
  star-shaped certificate interface `D2d.5`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- The ambient space of the window drawings. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Rotation of `ℝ³` about the `e₁`-axis by `t` (acting on the `(e₀, e₂)`-plane). -/
noncomputable def rot02 (t : ℝ) (v : E3) : E3 :=
  WithLp.toLp 2 ![v 0 * Real.cos t - v 2 * Real.sin t, v 1,
    v 0 * Real.sin t + v 2 * Real.cos t]

/-- Rotation of `ℝ³` about the `e₀`-axis by `t` (acting on the `(e₁, e₂)`-plane). -/
noncomputable def rot12 (t : ℝ) (v : E3) : E3 :=
  WithLp.toLp 2 ![v 0, v 1 * Real.cos t - v 2 * Real.sin t,
    v 1 * Real.sin t + v 2 * Real.cos t]

/-- **The horizontal slab twist.**  Each vertical circle orbit of the `y`-axis is rotated rigidly by
the angle `s * π * smoothTransition ((a - y) / (2a))`; the map is the identity for `y ≥ a` and the
half-turn `(x, y, z) ↦ (-x, y, -z)` for `y ≤ -a`. -/
noncomputable def twistY (a s : ℝ) (v : E3) : E3 :=
  rot02 (s * Real.pi * Real.smoothTransition ((a - v 1) / (2 * a))) v

/-- **The vertical slab twist.**  Each circle orbit of the `x`-axis is rotated rigidly by the angle
`s * π * smoothTransition ((x + ε) / (2ε))`; the map is the identity for `x ≤ -ε` and the half-turn
`(x, y, z) ↦ (x, -y, -z)` for `x ≥ ε`. -/
noncomputable def twistX (ε s : ℝ) (v : E3) : E3 :=
  rot12 (s * Real.pi * Real.smoothTransition ((v 0 + ε) / (2 * ε))) v

/-- **The vertical push**, rigid off the band `|y| < ε`. -/
noncomputable def pushY (D ε s : ℝ) (v : E3) : E3 :=
  WithLp.toLp 2 ![v 0,
    v 1 + Real.smoothTransition s * D * (2 * Real.smoothTransition ((v 1 + ε) / (2 * ε)) - 1),
    v 2]

/-- **An ambient path** `F : ℝ → ℝ³ → ℝ³`: the slice `F s` is an injective immersion for every `s`,
`(s, v) ↦ F s v` is smooth, and `F 0` is the identity.  These are the hypotheses of the level
isotopy constructor `Work.Drive.N2C.isLevelIsotopy_ambient` (Tier B1) plus the initial condition. -/
structure AmbientPath (F : ℝ → E3 → E3) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry F)
  inj : ∀ s : ℝ, Function.Injective (F s)
  imm : ∀ (s : ℝ) (w : E3), Function.Injective (fderiv ℝ (F s) w)
  zero : ∀ v : E3, F 0 v = v

/-- **Star-shapedness about the origin** of the planar projection of a curve `g` on the parameter set
`I`: the angular rate `x * y' - y * x'` has a constant non-zero sign. -/
def StarAboutZero (g : ℝ → E3) (I : Set ℝ) : Prop :=
  (∀ t ∈ I, 0 < g t 0 * deriv (fun u => g u 1) t - g t 1 * deriv (fun u => g u 0) t) ∨
  (∀ t ∈ I, g t 0 * deriv (fun u => g u 1) t - g t 1 * deriv (fun u => g u 0) t < 0)

/-- **The squash** `(x, y, z) ↦ (x, y, (1 - s) z)`: it flattens `ℝ³` onto the plane `z = 0` at
time `s = 1`.  Tier B2 of the coherent-window design. -/
noncomputable def sq (s : ℝ) (v : E3) : E3 :=
  WithLp.toLp 2 ![v 0, v 1, (1 - s) * v 2]

/-- The planar projection `(x, y) ↦ x + i y` of `ℝ³` used by the star-shaped certificate. -/
noncomputable def proj2 (v : E3) : ℂ := ⟨v 0, v 1⟩

/-- The polar angle of the endpoint `E₁ = √(-η + i m)` of the pinned top arc (design §1: `φ_E`). -/
noncomputable def mobiusPhiE (η m : ℝ) : ℝ := Complex.arg (Complex.sqrt ((-η : ℂ) + (m : ℂ) * Complex.I))

/-- The end of the pinned set used by the polar profile: `d φ = dist (φ, πℤ)`. -/
noncomputable def mobiusDist (φ : ℝ) : ℝ :=
  Metric.infDist φ (Set.range (fun k : ℤ => (k : ℝ) * Real.pi))

end

end Work.Drive.N2Lead
