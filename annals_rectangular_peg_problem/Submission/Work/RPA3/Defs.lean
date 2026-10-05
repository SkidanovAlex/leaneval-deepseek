import Mathlib
import ChallengeDeps

/-!
# RPA3: the shared vocabulary (subset relevant to block A3)

This is a copy of the vocabulary of the route design (`RECTPEG_ROUTE_STATEMENTS.lean.txt`,
namespace `RectPeg`), placed here in namespace `Work.RPA3` so that no declaration in this
directory clashes with the copies written by other subprojects.  Every definition is
character-for-character the one of the route design; the bridge to the `RectPeg` namespace is a
plain structure literal (see `Work.RPA3.Bridge`, when the RPV vocabulary file exists).

A3 is the block "exact Lagrangian isotopy extension": the flux primitive `flux_primitive`, the
tubular/Weinstein extension `D2`, the follow-the-family argument, and the assembly
`lag_isotopy_extension`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

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

/-! ## V-lemmas (node `V`, elementary algebra) -/

theorem K0_tau (θ : ℝ) (x : PS) : K0 (tau θ x) = K0 x := by
  simp only [K0, tau]
  have h := Real.sin_sq_add_cos_sq θ
  linear_combination (-(x.1.1 ^ 2 + x.2.1 ^ 2) / 2) * h

theorem tau_pi (x : PS) : tau π x = ((-x.1.1, x.1.2 + π), (-x.2.1, x.2.2)) := by
  simp [tau]

theorem K0_levelPt (u : ℂ) (σ a : ℝ) : K0 (levelPt u σ a) = -1 - σ := by
  simp only [K0, levelPt]
  have h1 : ‖Complex.exp (-(a : ℂ) * I) * u‖ = ‖u‖ := by
    rw [norm_mul, Complex.norm_exp]; simp
  have h2 := Complex.sq_norm (Complex.exp (-(a : ℂ) * I) * u)
  rw [Complex.normSq_apply, h1] at h2
  nlinarith [h2]

/-! ## The complex structure `J` used by the tubular construction

`J(q, p) = (p, -q)`; it is `ω`-compatible: `symp (J a) (J b) = symp a b`, `symp a (J a) = |a|²`
(in the standard Euclidean coordinates of `PS`), so in particular `symp a (J a) > 0` for `a ≠ 0`.
This is the `J` of the route design, §4.4 D2. -/

/-- `J(q,p) = (p,-q)`. -/
def J (x : PS) : PS := (x.2, (-x.1.1, -x.1.2))

/-! ## Structures -/

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

/-- The same data, with the embedding and Lagrangian conditions required for **all** `τ ∈ ℝ`
(no restriction to the unit interval).  `LagFamilyAll` differs from `LagFamily` only in the fields
`inj` and `imm`, which are required for every `τ` here (the Lagrangian condition `lag` is
unrestricted in `LagFamily` too).  Every `LagFamily` can be put in this form by reparametrising
the `τ` variable with a smooth step function, and the machinery of block A3 that needs the
embedding conditions away from `τ ∈ [0,1]` (the tubular extension) is phrased for this structure,
which carries exactly the hypotheses those arguments use. -/
structure LagFamilyAll where
  ℓ : ℝ → ℝ × ℝ → PS
  smooth : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ℓ z.1 z.2)
  per : ∀ τ x t, ℓ τ (x, t + 2 * π) = Tk 1 (ℓ τ (x, t))
  inj : ∀ τ x t x' t' (k : ℤ), ℓ τ (x', t') = Tk k (ℓ τ (x, t)) →
    x' = x ∧ ∃ m : ℤ, t' = t + 2 * π * m
  imm : ∀ τ x t (a b : ℝ),
    a • deriv (fun y => ℓ τ (y, t)) x + b • deriv (fun s => ℓ τ (x, s)) t = 0 → a = 0 ∧ b = 0
  lag : ∀ τ x t,
    symp (deriv (fun y => ℓ τ (y, t)) x) (deriv (fun s => ℓ τ (x, s)) t) = 0
  X0 : ℝ
  std : ∀ τ x t, X0 ≤ |x| → ℓ τ (x, t) = stdZ x t
  start : ∀ x t, ℓ 0 (x, t) ∈ Zsec
  start_surj : ∀ z ∈ Zsec, ∃ x t, ℓ 0 (x, t) = z
  symm : ∀ τ x t, ℓ τ (-x, t + π) = tau π (ℓ τ (x, t))

/-- Forget the all-`τ` hypotheses. -/
def LagFamilyAll.toLagFamily (L : LagFamilyAll) : LagFamily where
  ℓ := L.ℓ
  smooth := L.smooth
  per := L.per
  inj := fun τ _ x t x' t' k h => L.inj τ x t x' t' k h
  imm := fun τ _ x t a b h => L.imm τ x t a b h
  lag := L.lag
  X0 := L.X0
  std := L.std
  start := L.start
  start_surj := L.start_surj
  symm := L.symm

end Work.RPA3
