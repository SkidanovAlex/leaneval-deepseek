import Mathlib
import ChallengeDeps

/-!
# Rectangular peg: shared vocabulary for the generating-function route (`Work.RPV.Defs`)

This file is the **shared vocabulary** of the rectangular-peg development
(route design `RECTPEG_ROUTE_LEAD.md`).  Every definition and structure used by the
node statements `RECTPEG_ROUTE_STATEMENTS.lean.txt` lives here, copied verbatim
(namespace aside: the route document used `RectPeg`, the workspace convention puts
everything under `Submission/Work/RPV/` in namespace `Work.RPV`).

It contains definitions only: no lemmas and no unfinished proofs.  The lemma API lives in the
sibling modules
* `Submission.Work.RPV.VBasic`  -- elementary algebra of the coordinate charts,
* `Submission.Work.RPV.Glue`    -- the glue from the node theorems to the challenge.

Conventions (see §3.1 of the route design).

* `PS` is `T^*ℝ² = ℝ⁴` with points `((q₁,q₂),(p₁,p₂))`; `q₂` is an **angle**, all data
  are `2π`-periodic in it (`Tk` shifts it by `2πk`).
* `symp` is `ω = dp₁∧dq₁ + dp₂∧dq₂`; `ωC` is `Im(conj a * b)` on `ℂ`.
* `chordPS z w a` is a chord of `ℂ²` seen in `PS`, with `a` a lift of `arg (z-w)`;
  `levelPt u σ a` is a point of the level `K₀ = -1-σ` with reduced coordinate `u`.
* `tau θ` is the time-`θ` flow of `K₀` (`v ↦ e^{iθ}v`, `q₂ ↦ q₂+θ`), `tau π` is the
  chord swap, and `uproj` is the invariant reduced coordinate `e^{iq₂}(p₁+iq₁)`.
* `CptPerHam` is a compactly supported, `2π`-periodic time-dependent Hamiltonian and
  `IsFlow H Φ` says `Φ` solves its Hamiltonian ODE; `hamVF` is that vector field.
* `LagFamily` is a compactly supported `τ_π`-symmetric Lagrangian isotopy of the zero
  section, `CurveIsotopy` an isotopy of embedded area-`π` curves from the unit circle,
  `HasThetaRect S φ` the normalised rectangle-existence statement.

**Never redeclare these**: import `Submission.Work.RPV.Defs`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPV

/-! ## V. Vocabulary -/

/-- Phase space `T^*ℝ² = ℝ⁴`, points `((q₁, q₂), (p₁, p₂))`.  `q₂` is an angle: all data are
`2π`-periodic in `q₂`. -/
abbrev PS := (ℝ × ℝ) × (ℝ × ℝ)

/-- `ω = dp₁∧dq₁ + dp₂∧dq₂`. -/
def symp (a b : PS) : ℝ := a.2.1 * b.1.1 + a.2.2 * b.1.2 - a.1.1 * b.2.1 - a.1.2 * b.2.2

/-- shift of the angle `q₂` by `2πk`. -/
def Tk (k : ℤ) (x : PS) : PS := ((x.1.1, x.1.2 + 2 * π * k), x.2)

/-- zero section `p = 0`. -/
def Zsec : Set PS := {x | x.2 = 0}

/-- standard parametrisation of the zero section. -/
def stdZ (x t : ℝ) : PS := ((x, t), (0, 0))

/-- `K₀ = p₂ - (q₁² + p₁²)/2`.  On chords, `K₀ = |z - w|²/4 - 1`. -/
def K0 (x : PS) : ℝ := x.2.2 - (x.1.1 ^ 2 + x.2.1 ^ 2) / 2

/-- time-`θ` flow of `K₀`: rotation by `θ` in the `(q₁,p₁)` plane, `q₂ ↦ q₂ + θ`.
In the chord model this is `v ↦ e^{iθ} v` (rotation about the diagonal). -/
def tau (θ : ℝ) (x : PS) : PS :=
  ((x.1.1 * Real.cos θ - x.2.1 * Real.sin θ, x.1.2 + θ),
   (x.1.1 * Real.sin θ + x.2.1 * Real.cos θ, x.2.2))

/-- reduced coordinate `u = e^{i q₂} (p₁ + i q₁)` (invariant of the `K₀`-flow). -/
def uproj (x : PS) : ℂ := Complex.exp (x.1.2 * I) * (x.2.1 + x.1.1 * I)

/-- Hamiltonian vector field for `ω`: `q̇ = ∂_p H`, `ṗ = -∂_q H`. -/
def hamVF (H : PS → ℝ) (x : PS) : PS :=
  ((fderiv ℝ H x ((0, 0), (1, 0)), fderiv ℝ H x ((0, 0), (0, 1))),
   (-fderiv ℝ H x ((1, 0), (0, 0)), -fderiv ℝ H x ((0, 1), (0, 0))))

/-- The chord `(z, w)` of `ℂ²` (with `a` a lift of `arg (z - w)`) as a point of `PS`:
`u = (z+w)/√2`, `q₂ = a`, `p₁ + i q₁ = e^{-ia} u`, `p₂ = (|z|²+|w|²)/2 - 1`. -/
def chordPS (z w : ℂ) (a : ℝ) : PS :=
  (((Complex.exp (-(a : ℂ) * I) * ((z + w) / (Real.sqrt 2 : ℂ))).im, a),
   ((Complex.exp (-(a : ℂ) * I) * ((z + w) / (Real.sqrt 2 : ℂ))).re,
    (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 - 1))

/-- The point on the level `K₀ = -1 - σ` with reduced coordinate `u` and phase `q₂ = a`. -/
def levelPt (u : ℂ) (σ a : ℝ) : PS :=
  (((Complex.exp (-(a : ℂ) * I) * u).im, a),
   ((Complex.exp (-(a : ℂ) * I) * u).re, ‖u‖ ^ 2 / 2 - σ - 1))

/-- `ω_ℂ(a, b) = Im (conj a * b) = dx∧dy (a, b)`. -/
def ωC (a b : ℂ) : ℝ := ((starRingEnd ℂ) a * b).im

/-- Linearisation of `chordPS` at `(z, w)` (with `a = arg(z-w)`) in the direction `(ζ, η)`. -/
def dchord (z w : ℂ) (a : ℝ) (ζ η : ℂ) : PS :=
  let da : ℝ := ((ζ - η) / (z - w)).im
  let du : ℂ := Complex.exp (-(a : ℂ) * I) *
      ((ζ + η) / (Real.sqrt 2 : ℂ) - (da : ℂ) * I * ((z + w) / (Real.sqrt 2 : ℂ)))
  ((du.im, da), (du.re, ((starRingEnd ℂ) z * ζ).re + ((starRingEnd ℂ) w * η).re))

/-! ## CORE: structures -/

/-- A time-dependent Hamiltonian on `PS`, `C⁴`, `2π`-periodic in `q₂`, vanishing when
`|q₁| + |p₁| + |p₂| ≥ R`. -/
structure CptPerHam where
  H : ℝ → PS → ℝ
  smooth : ContDiff ℝ 4 (fun z : ℝ × PS => H z.1 z.2)
  per : ∀ t x, H t (Tk 1 x) = H t x
  R : ℝ
  supp : ∀ t x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → H t x = 0

/-- `Φ` is the (time-`0`-based) flow of the time-dependent Hamiltonian `H`. -/
def IsFlow (H : ℝ → PS → ℝ) (Φ : ℝ → PS → PS) : Prop :=
  (∀ x, Φ 0 x = x) ∧ ∀ x t, HasDerivAt (fun s => Φ s x) (hamVF (H t) (Φ t x)) t

/-- `∂_q W` and `∂_P W` as vectors. -/
def dq (W : PS → ℝ) (q P : ℝ × ℝ) : ℝ × ℝ :=
  (fderiv ℝ W (q, P) ((1, 0), (0, 0)), fderiv ℝ W (q, P) ((0, 1), (0, 0)))
def dP (W : PS → ℝ) (q P : ℝ × ℝ) : ℝ × ℝ :=
  (fderiv ℝ W (q, P) ((0, 0), (1, 0)), fderiv ℝ W (q, P) ((0, 0), (0, 1)))

/-- `W` is a type-2 generating function of `ψ`:
`ψ(q,p) = (Q,P) ⇔ p = P + ∂_q W(q,P) ∧ Q = q + ∂_P W(q,P)`. -/
def IsType2GF (ψ : PS → PS) (W : PS → ℝ) : Prop :=
  ∀ q p Q P : ℝ × ℝ, ψ (q, p) = (Q, P) ↔ (p = P + dq W q P ∧ Q = q + dP W q P)

/-- explicit type-2 generating function of `τ_δ` (`|δ| < π/2`). -/
def Wrot (δ : ℝ) (x : PS) : ℝ :=
  (1 / Real.cos δ - 1) * x.1.1 * x.2.1 - Real.tan δ / 2 * (x.1.1 ^ 2 + x.2.1 ^ 2) + δ * x.2.2

/-- the discrete (broken-geodesic) action of a chain of `n+1` maps with generating functions
`W j`; variables `q : Fin (n+1) → ℝ²` (`q₀ … qₙ`) and `P : Fin n → ℝ²` (`P₁ … Pₙ`); boundary
conditions `p₀ = 0` and `P_{n+1} = 0`. -/
def chainAction (n : ℕ) (W : Fin (n + 1) → PS → ℝ) (q : Fin (n + 1) → ℝ × ℝ)
    (P : Fin n → ℝ × ℝ) : ℝ :=
  (∑ j : Fin n, ((P j).1 * ((q j.succ).1 - (q j.castSucc).1) +
      (P j).2 * ((q j.succ).2 - (q j.castSucc).2)))
  - ∑ j : Fin (n + 1), W j (q j, if h : (j : ℕ) < n then P ⟨j, h⟩ else 0)

/-! ## A3: structures -/

/-- A compactly supported, `τ_π`-symmetric Lagrangian isotopy of the zero section, parametrised
by `(x, t) ∈ ℝ × ℝ` (`t` mod `2π`). -/
structure LagFamily where
  ℓ : ℝ → ℝ × ℝ → PS
  smooth : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ℓ z.1 z.2)
  per : ∀ τ x t, ℓ τ (x, t + 2 * π) = Tk 1 (ℓ τ (x, t))
  inj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t x' t' (k : ℤ), ℓ τ (x', t') = Tk k (ℓ τ (x, t)) →
    x' = x ∧ ∃ m : ℤ, t' = t + 2 * π * m
  imm : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t (a b : ℝ),
    a • deriv (fun y => ℓ τ (y, t)) x + b • deriv (fun s => ℓ τ (x, s)) t = 0 → a = 0 ∧ b = 0
  lag : ∀ τ x t, symp (deriv (fun y => ℓ τ (y, t)) x) (deriv (fun s => ℓ τ (x, s)) t) = 0
  X0 : ℝ
  std : ∀ τ x t, X0 ≤ |x| → ℓ τ (x, t) = stdZ x t
  start : ∀ x t, ℓ 0 (x, t) ∈ Zsec
  start_surj : ∀ z ∈ Zsec, ∃ x t, ℓ 0 (x, t) = z
  symm : ∀ τ x t, ℓ τ (-x, t + π) = tau π (ℓ τ (x, t))

/-! ## B: structures -/

/-- A smooth isotopy of embedded, area-`π`, positively oriented closed curves starting at the
unit circle (`t` is `2π`-periodic). -/
structure CurveIsotopy where
  c : ℝ → ℝ → ℂ
  smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)
  per : ∀ τ t, c τ (t + 2 * π) = c τ t
  inj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t', c τ t = c τ t' → ∃ m : ℤ, t' = t + 2 * π * m
  imm : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, deriv (c τ) t ≠ 0
  start : ∀ t, c 0 t = Complex.exp (t * I)
  area : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
    (1 / 2) * ∫ t in (0 : ℝ)..(2 * π), ωC (c τ t) (deriv (c τ) t) = π

/-! ## G: glue -/

/-- The hypothesis of the challenge, packaged as an abbreviation so that statements can mention it
without spelling out the manifold notation: `γ` is a `C^∞` embedding of the circle into `ℂ`.
It is definitionally equal to `IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ`, so a proof of
`IsSmoothJordan γ` can be used wherever the challenge's hypothesis is expected and conversely. -/
def IsSmoothJordan (γ : Circle → ℂ) : Prop := IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ

/-- `θ`-rectangle existence in normalised form. -/
def HasThetaRect (S : Set ℂ) (φ : ℝ) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, ∃ x' ∈ S, ∃ y' ∈ S,
    x ≠ y ∧ x + y = x' + y' ∧ x' - y' = Complex.exp (φ * I) * (x - y)

end Work.RPV
