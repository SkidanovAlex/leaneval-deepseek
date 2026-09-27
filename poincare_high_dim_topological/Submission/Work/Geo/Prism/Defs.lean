import Mathlib
import Submission.Work.PL.Defs

/-!
# The prism chapter: definitions (area A1, `Submission/Work/Geo/Prism/`)

Blueprint: `Submission/Work/NOTES_LEAD_poincare_blueprint.md` §2, items G1, G1' and G2.
Pure `ℝⁿ` geometry: no manifold, no charts.

Notation (blueprint §2): `Pr a b = E a × E b × ℝ`.  A point is `(y, z, t)`: `y` is the
"thickness" direction `Y` of the product `E a`, `z` is the base direction `Z`, `t` is the
stretch direction `ℝ`.

The whole construction rests on one explicit "stretch" map of `ℝ`.  For `a b c t : ℝ` put

  `str a b c t = t + (c - b) * clamp01 ((t - a) / (b - a))`,

where `clamp01 x = min 1 (max 0 x)`.  When `a < b` this is the piecewise linear
homeomorphism of `ℝ` that is the identity on `(-∞, a]`, maps `[a, b]` linearly onto `[a, c]`
and translates `[b, ∞)` by `c - b`.  It is a *total* continuous function of all four
variables, which is what makes the continuity of the prism homeomorphism painless: every
"degenerate" instance (`a = b`, i.e. zero length) is the identity, by Lean's `x / 0 = 0`
convention.

The prism "push" of Newman (G1) is then the two-step family

  `prismTheta s ℓ δ t = str (s+ℓ) (s+2ℓ) (s+ℓ+min δ ℓ) (str s (s+min δ ℓ) (s+ℓ) t)`,

which is the identity outside `[s, s + ℓ + min δ ℓ]`, maps `[s, s + min δ ℓ]` linearly onto
`[s, s+ℓ]` and maps `[s+min δ ℓ, s+ℓ+min δ ℓ]` linearly onto `[s+ℓ, s+ℓ+min δ ℓ]`.  Its
inverse is `prismThetaInv`.

All names below live in namespace `Work.Geo.Prism`.
-/

open Set Metric
open scoped Topology
open Classical

namespace Work.Geo.Prism

/-- The prism space `Pr a b = E a × E b × ℝ`.  A point `(y, z, t)`: `y` is the thickness
direction `Y`, `z` the base direction `Z`, `t` the stretch direction. -/
abbrev Pr (a b : ℕ) : Type := PL.E a × PL.E b × ℝ

/-- `clamp01 x = min 1 (max 0 x)`, the projection of `ℝ` onto `[0,1]`. -/
noncomputable def clamp01 (x : ℝ) : ℝ := min 1 (max 0 x)

/-- The elementary stretch of `ℝ`: when `a < b` and `a < c` this is the homeomorphism of
`ℝ` fixing `(-∞, a]`, mapping `[a, b]` linearly onto `[a, c]` and translating `[b, ∞)` by
`c - b`.  Total in all four variables, so it is jointly continuous. -/
noncomputable def str (a b c t : ℝ) : ℝ := t + (c - b) * clamp01 ((t - a) / (b - a))

/-- The two-step prism stretch (see the module docstring).  With `μ = min δ ℓ` it is the
identity outside `[s, s + ℓ + μ]`, sends `[s, s + μ]` linearly onto `[s, s+ℓ]` and
`[s+μ, s+ℓ+μ]` linearly onto `[s+ℓ, s+ℓ+μ]`. -/
noncomputable def prismTheta (s ℓ δ t : ℝ) : ℝ :=
  str (s + ℓ) (s + 2 * ℓ) (s + ℓ + min δ ℓ) (str s (s + min δ ℓ) (s + ℓ) t)

/-- The inverse of `prismTheta s ℓ δ` (as a function of `t`). -/
noncomputable def prismThetaInv (s ℓ δ t : ℝ) : ℝ :=
  str s (s + ℓ) (s + min δ ℓ) (str (s + ℓ) (s + ℓ + min δ ℓ) (s + 2 * ℓ) t)

/-- The thickness taper `1 - ‖y‖/η`, clamped at `0`. -/
noncomputable def lam {a : ℕ} (η : ℝ) (y : PL.E a) : ℝ := max 0 (1 - ‖y‖ / η)

/-- The length over `z` of the stretch: `max 0 (γ z - φ z)`, and `0` off `F`.  This is the
function that is *continuous* although the `if` looks discontinuous: on `frontier F` one has
`φ = γ`, so its value is `0` there and hence it is the gluing of two continuous functions. -/
noncomputable def len {b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ) (z : PL.E b) : ℝ :=
  if z ∈ F then max 0 (γ z - φ z) else 0

/-- The explicit prism push of Newman (G1), as a function.  Its parameters are the floor
`φ`, the top `γ`, the taper radius `η` and the floor-slab height `δ`. -/
noncomputable def prismPushFun {a b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ)
    (η δ : ℝ) (x : Pr a b) : Pr a b :=
  (x.1, x.2.1, prismTheta (φ x.2.1) (lam η x.1 * len F φ γ x.2.1) δ x.2.2)

/-- The inverse of `prismPushFun`. -/
noncomputable def prismPushInvFun {a b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ)
    (η δ : ℝ) (x : Pr a b) : Pr a b :=
  (x.1, x.2.1, prismThetaInv (φ x.2.1) (lam η x.1 * len F φ γ x.2.1) δ x.2.2)

/-- The "prism" over `F` between the floor `φ` and the top `γ`, inside `{y = 0}`. -/
def prismSet {a b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ) : Set (Pr a b) :=
  {x | x.1 = 0 ∧ x.2.1 ∈ F ∧ φ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ x.2.1}

/-- The "closed slab" of thickness `δ` above the floor `φ` over `F`, with thickness `η` in
the `Y` direction: the compact support of `prismPushFun`. -/
def tube {a b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ) (η δ : ℝ) : Set (Pr a b) :=
  closedBall (0 : PL.E a) η ×ˢ {q : PL.E b × ℝ | q.1 ∈ F ∧ φ q.1 ≤ q.2 ∧ q.2 ≤ γ q.1 + δ}

/-- `AffDimLE C d`: the affine dimension of `C` is at most `d` (as an integer, so `d < 0`
forces `C = ∅`): there is a point `p` such that the span of the differences `x - p`,
`x ∈ C`, has `finrank ≤ d`. -/
def AffDimLE {m : ℕ} (C : Set (PL.E m)) (d : ℤ) : Prop :=
  ∃ p : PL.E m, (Module.finrank ℝ (Submodule.span ℝ ((fun x => x -ᵥ p) '' C)) : ℤ) ≤ d

/-- A "convex piecewise linear" function: the pointwise maximum (supremum) of a finite
nonempty family of affine functions.  Such a function is convex, continuous, and its
epigraph is a finite union of polyhedra. -/
def ConvexPL {q : ℕ} (γ : PL.E q → ℝ) : Prop :=
  ∃ (S : Finset (PL.E q →ᵃ[ℝ] ℝ)) (hS : S.Nonempty), ∀ z, γ z = S.sup' hS (fun f => f z)

/-- A "concave piecewise linear" function: the pointwise minimum (infimum) of a finite
nonempty family of affine functions. -/
def ConcavePL {q : ℕ} (γ : PL.E q → ℝ) : Prop :=
  ∃ (S : Finset (PL.E q →ᵃ[ℝ] ℝ)) (hS : S.Nonempty), ∀ z, γ z = S.inf' hS (fun f => f z)

/-- `DomDim₂`, the version of Newman's "dimension ≤ d" for subsets of a product `X × Y` of
real vector spaces: `C` is covered by finitely many simplices `convexHull ℝ s` with
`|s| ≤ d + 1` vertices.  This is the form used for the prism pieces (E4 engulfs `Π J`,
a subset of `Pr a b = E a × (E b × ℝ)`). -/
def DomDim₂ {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (C : Set (X × Y)) (d : ℤ) : Prop :=
  ∃ S : Finset (Finset (X × Y)), (∀ s ∈ S, (s.card : ℤ) ≤ d + 1) ∧
    C ⊆ ⋃ s ∈ S, convexHull ℝ (s : Set (X × Y))

end Work.Geo.Prism
