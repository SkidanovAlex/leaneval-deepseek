import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# C11a (maximal inequality for leafwise measures) — private definitions

This module sets up the language in which the proof of `P_MaxLeaf` (EKL (10), L06 Thm A.1)
is organised.  Nothing here is part of the frozen contract; `IsPlaqueAlgebra`, `atom`,
`shape`, `ballU`, `Uij`, `IsLeafwise`, `IsAInvariant` are the contract's objects
(`Submission/Work/EKLContract/Defs.lean`).

## The plan

`μ` is an `A`-invariant probability on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, `U = U_ij` a root group and
`ν` a system of leafwise measures for `U` (so `ν x` is a Radon measure carried by `U`).
The bad set is

  `S = {x ∈ X' | ∃ r > 0, α * ν x (ballU r) < ∫_{ballU r} f (g • x) dν x}`.

The proof follows L06 Appendix A, made uniform in `μ` by using the contract's `condexp`
field in place of an explicit disintegration:

* a *plaque algebra* `(Z, m)` (`IsPlaqueAlgebra U Z m`) with `μ Z` arbitrarily close to `1`
  and with `atom m x ⊇ ballU r̄ • x` for all `x ∈ Z` — this is the geometric input,
  isolated in `plaqueAlgebra_exists` below;
* on each atom, the leafwise measures at different points are proportional (they are
  push-forwards of `ν` to the leaf), so the bad condition becomes a bad condition for a
  fixed measure on the leaf `U_ij ≅ ℝ`; the one-dimensional Besicovitch covering theorem
  then bounds the leaf-measure of the bad set by `(N/α) * ∫ f dν`;
* integrating over `Z` with the `condexp` field finishes the estimate.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

noncomputable section

namespace Work.EKLComp

/-- `x` has trivial stabiliser in the root group `U_ij`: the leaf through `x` is embedded
(in the sense of L06 (3.1)), equivalently `s ↦ u_ij(s) • x` is injective.

PROOF IDEA for `μ (Free i j hij)ᶜ = 0` (no use of `P_X3` or of leafwise measures is needed,
only the `A`-invariance of the probability `μ` and that `Γ₃` is discrete):
for `a > 0` put `P a = {x | ∃ s, 0 < |s| ≤ a, u_ij(s) • x = x}`.  Since `U_ij ≅ ℝ` is abelian,
`u(s) • (aDiag t • x) = aDiag t • (u(e ^ (t j - t i) * s) • x)`, so
`aDiag t • P a = P (e ^ (t j - t i) * a)`; as `(aDiag t) • ·` preserves `μ`, `a ↦ μ (P a)` is
constant on `(0,∞)`.  A closed subgroup of `ℝ` is `{0}`, `αℤ` or `ℝ`; it cannot be `ℝ` because
`U_ij ⊆ gΓ₃g⁻¹` would put the connected group `U_ij` inside a discrete one.  Hence
`P a ↓ P 0` with `P 0 = {x | ∀ a, ∃ s, 0 < |s| ≤ a, u_ij(s)•x = x} = ∅` (a stabiliser `αℤ`
with `α > 0` forces `|s| ≥ α`), so `μ (P a) = 0` for every `a`, and
`Freeᶜ = ⋃ n, P (1/n)`. -/
def Free (i j : Fin 3) (hij : i ≠ j) : Set X3 :=
  {x | ∀ u ∈ Uij hij, u • x = x → u = 1}

/-- The `U_ij`-leaf of `x`, as a subset of `X₃`. -/
def leaf (i j : Fin 3) (hij : i ≠ j) (x : X3) : Set X3 :=
  (fun g : SL3 => g • x) '' (Uij hij : Set SL3)

/-- The system of leafwise measures, pushed to the leaf: `leafMeasure ν x` is a measure on
`X₃` carried by the `U_ij`-leaf of `x`.  Two points of the same leaf have proportional
`leafMeasure`s (exactly the `equivariant` field of `IsLeafwise`).

PROOF IDEA for proportionality: if `y = u • x` with `u ∈ U_ij` then `equivariant` gives
`ν x = c • (ν y).map (· * u)`, and applying `·.map (g ↦ g • x)` and using
`(g * u) • x = g • (u • x) = g • y` turns this into
`leafMeasure ν x = c • leafMeasure ν y`. -/
def leafMeasure (ν : X3 → Measure SL3) (x : X3) : Measure X3 :=
  (ν x).map (fun g => g • x)

/-! ## The bad sets of the maximal inequality -/

/-- The bad condition at scale `r`, in `ℝ≥0∞` form: the `ν x`-average of `f` over the
`U_ij`-ball of radius `r` through `x` exceeds `α`.  This is the `ℝ≥0∞` version of the
condition appearing in `P_MaxLeaf`; the two agree whenever the restriction of `f` to the
ball is `ν x`-integrable. -/
def BadENN (i j : Fin 3) (hij : i ≠ j) (ν : X3 → Measure SL3) (f : X3 → ℝ) (x : X3)
    (α r : ℝ) : Prop :=
  ENNReal.ofReal α * ν x (ballU hij r)
    < ∫⁻ g in ballU hij r, ENNReal.ofReal (f (g • x)) ∂(ν x)

/-- The set of points which are bad for some radius. -/
def BadSet (i j : Fin 3) (hij : i ≠ j) (ν : X3 → Measure SL3) (f : X3 → ℝ) (α : ℝ) : Set X3 :=
  {x | ∃ r : ℝ, 0 < r ∧ BadENN i j hij ν f x α r}

/-- The set appearing in the frozen statement `P_MaxLeaf` (with the Bochner integral). -/
def FrozenBadSet (i j : Fin 3) (hij : i ≠ j) (ν : X3 → Measure SL3) (f : X3 → ℝ) (α : ℝ) :
    Set X3 :=
  {x | ∃ r : ℝ, 0 < r ∧
    α * (ν x (ballU hij r)).toReal < ∫ g in ballU hij r, f (g • x) ∂(ν x)}

/-- The `ℝ≥0∞`-form bad set at a *bounded* scale: bad at some radius `< rbar`. -/
def BadSetLt (i j : Fin 3) (hij : i ≠ j) (ν : X3 → Measure SL3) (f : X3 → ℝ) (α rbar : ℝ) :
    Set X3 :=
  {x | ∃ r : ℝ, 0 < r ∧ r < rbar ∧ BadENN i j hij ν f x α r}

/-- The bad set with *rational* radius, at some radius `< rbar`. -/
def BadSetRat (i j : Fin 3) (hij : i ≠ j) (ν : X3 → Measure SL3) (f : X3 → ℝ) (α rbar : ℝ) :
    Set X3 :=
  {x | ∃ r : ℚ, 0 < r ∧ (r : ℝ) < rbar ∧ BadENN i j hij ν f x α (r : ℝ)}

/-! ## The geometric input -/

/-- **The geometric input for C11a** (L06 Lemma A.2, the "flower"/plaque construction of
Pisa §5–6): for an `A`-invariant probability `μ` and radii `ε, r̄ > 0` there is a plaque algebra
`(Z, m)` for `U_ij` with `Z ⊆ Free`, together with a Borel "good" set `G ⊆ Z` of measure
`≥ 1 - ε` such that the `U_ij`-leaf ball of radius `r̄` around every point of `G` is contained
in its `m`-atom.

TWO MEASURABILITY CAVEATS (both essential, both verified by a referee):
* `G` is required to be measurable for the AMBIENT Borel structure only, *not* for `m`.  The
  statement writes `MeasurableSet[instMeasurableSpaceX3] G` explicitly so that type-class capture
  by the bound variable `m` cannot weaken it into `MeasurableSet[m] G`.
* the ball condition is required only on `G ⊆ Z` and not on all of `Z`.  Indeed if it held on an
  `m`-measurable set of points (or on all of `Z`), then for `x` in that set and `|t| ≤ r̄` the
  point `u(t) • x` lies in `atom m x`, hence (for an `m`-measurable set, which is a union of
  atoms) again in the set, so `{s | u(s) • x ∈ atom m x}` is closed under adding `[-r̄, r̄]` and
  equals `ℝ`: `atom m x = U_ij • x`, contradicting the bounded-shape clause of
  `IsPlaqueAlgebra`.  So the good set must be a proper large-measure Borel subset of `Z`, exactly
  as in L06 (`X''` there, defined by leaf-coordinate conditions and generally not in the plaque
  σ-algebra).

PROOF IDEA.  Write `u(s) = uij hij s`, `M = {m : SL3 | m i j = 0}`.  For `g₀ : SL3` and small
`ε₀, R > 0` the set `Π = {u(s) * m | s ∈ (-R,R), m ∈ M, ‖m - g₀‖ < ε₀}` is open in `SL3` and
`π = mkX` is injective on it (if `u(s)m = u(s')m'γ` with `γ ∈ Γ₃` then `γ = m'⁻¹ u(s-s') m` is
close to `1`, hence `= 1`, and then `δ m_jj = 0` for `m ∈ M` forces `s = s'`, `m = m'`).
So `B = π '' Π` is open, with a Borel transverse coordinate `τ` and "plaques"
`τ⁻¹ {m} = {u(σ) • x | σ ∈ (-R,R)}`; from `π '' Π` one sees that the quotient map is open, so
these are the local charts of `X₃ = SL₃(ℝ)/SL₃(ℤ)`.
Every point of `X₃` is the centre of such a box, and `X₃` is second countable (Mathlib's
`TopologicalSpace.QuotientGroup` instances + `SecondCountableTopology SL₃`), so Lindelöf gives a
countable cover; continuity from below gives finitely many boxes `B_1,…,B_M` with
`μ (⋃_{j≤M} B_j) ≥ 1 - ε/2`.  For `x ∈ ⋃ B_j` let `J(x) = {j | x ∈ B_j}` and `s_j(x) ∈ (-R,R)`
the plaque coordinate in box `j`; the set
`Z₀ = ⋃_{J}` `{x ∈ ⋂_{j ∈ J} B_j : J(x) = J}` is Borel, and
`Good_λ = ⋃_J {x ∈ ⋂_{j ∈ J} B_j : J(x) = J, ∀ j ∈ J, |s_j(x)| + 4 e^{-λ} r̄ ≤ R}`
has `μ (Z₀ \ Good_λ) → 0` as `λ → ∞` (the coordinate conditions increase to `B_j`).
Now take `t` with `t i - t j = λ` large and push everything forward by `a = aDiag t`: `μ` is
preserved, the plaque parameter is multiplied by `e ^ λ`, so `a (Good_λ)` is a set of the same
measure on which the leaf ball of radius `r̄` lies in the pushed plaque.  Let `m` be the
σ-algebra generated by the countably many sets `a (Z₀ ∩ Free ∩ τ_j⁻¹ V_n)` and
`a (Z₀ ∩ Free)` (`V_n` a countable base of the transverse piece), and put
`Z = a (Z₀ ∩ Free)`, `G = a (Good_λ ∩ Free)`.  The atoms of `m` are the pushed plaques cut to
`Free`, hence contained in `Z` and in `U_ij • x`, with relatively open bounded shape (here
`Z ⊆ Free` is what makes the shape bounded: on a free point the set of `u` with `u • x` back in
the plaque is a single interval).  Finally, if `q` is the homeomorphism of `X₃` induced by
`aDiag t` (or if one reads the atoms through the explicit coordinate `aDiag t * v * (aDiag t)⁻¹`
of the pushed plaques), the ball condition on `G` is exactly
`B_{r̄}(a x) = a (B_{e^{-λ} r̄}(x)) ⊆ a (atom of x) = atom of a x`. -/
def PlaqueAlgebraExists (i j : Fin 3) (hij : i ≠ j) : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ →
  ∀ ε rbar : ℝ, 0 < ε → 0 < rbar →
    ∃ (Z G : Set X3) (m : MeasurableSpace X3),
      Z ⊆ Free i j hij ∧ IsPlaqueAlgebra (Uij hij) Z m ∧
      MeasurableSet[instMeasurableSpaceX3] G ∧ G ⊆ Z ∧ ENNReal.ofReal (1 - ε) ≤ μ G ∧
      ∀ x ∈ G, ∀ u ∈ (ballU hij rbar : Set SL3), u • x ∈ atom m x

end Work.EKLComp
