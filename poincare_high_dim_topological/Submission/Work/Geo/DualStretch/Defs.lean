/-
A6 `Geo/DualStretch` — the Stallings/Connell stretch between dual skeleta (Newman §16).

This file fixes the vocabulary of the area.  Everything is pure `ℝⁿ` geometry; no `M`, no charts.

Notation (see `Submission/Work/NOTES_LEAD_poincare_blueprint.md` §2 G7):
* `P : Cx n` is a finite geometric simplicial complex in `E n` (we always assume `P.space = closedCube β`).
* `Low P p`   : the `p`-skeleton, i.e. the union of the simplices spanned by faces with `≤ p+1` vertices.
* `High P p`  : the dual `(n-p-1)`-skeleton, i.e. the union over chains of faces with `≥ p+2` vertices
                of the simplices spanned by the barycentres of the chain.
* every `x ∈ P.space` is decomposed by the barycentric subdivision of `P` into the sum of a "low"
  part `A(x)` and a "high" part `B(x)` over the level sets of the barycentric coordinates; `S(x)` is
  the total high mass.  `stretch` rescales `B` by a constant `M > 1` and renormalises.

Both `A`, `B`, `S` are sums over the *fixed* finite family `cands P hP` of all subsets of faces of `P`,
which makes them continuous functions of `x` (see `Continuity.lean`).
-/
import Submission.Work.PL.Defs

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open PL (E Cx closedCube openCube)

set_option linter.unusedVariables false

variable {n : ℕ}

/-- The topological boundary of the sup-norm cube `closedCube β` in `E n`. -/
def bdryCube (β : ℝ) : Set (E n) := {x | ∃ i, |x i| = β}

/-- The barycentre of a finite set of points; `bary ∅ = 0`. -/
noncomputable def bary (s : Finset (E n)) : E n := (s.card : ℝ)⁻¹ • ∑ v ∈ s, v

/-- A family of faces totally ordered by inclusion. -/
def IsChain (T : Finset (Finset (E n))) : Prop := ∀ σ ∈ T, ∀ τ ∈ T, σ ⊆ τ ∨ τ ⊆ σ

/-- The `p`-skeleton of `P`: the union of the simplices spanned by faces with at most `p+1` vertices. -/
def Low (P : Cx n) (p : ℕ) : Set (E n) := {x | ∃ s ∈ P.faces, s.card ≤ p + 1 ∧ x ∈ PL.simp s}

/-- The dual `(n-p-1)`-skeleton of `P`: the union over chains `T` of faces with at least `p+2`
vertices of the convex hull of the barycentres of the members of `T`. -/
def High (P : Cx n) (p : ℕ) : Set (E n) :=
  {x | ∃ T : Finset (Finset (E n)), (T : Set (Finset (E n))) ⊆ P.faces ∧ T.Nonempty ∧ IsChain T ∧
    (∀ σ ∈ T, p + 2 ≤ σ.card) ∧ x ∈ PL.simp (T.image bary)}

/-- The low side of the split at a level set `τ`: `τ` is small (at most `p+1` vertices).
This is the *cardinality* (p-skeleton) criterion; the cube boundary is dealt with by the taper
`taperM` instead. -/
def LowFace (β : ℝ) (p : ℕ) (τ : Finset (E n)) : Prop := τ.card ≤ p + 1

/-- A face of `P` containing `x` and contained in every face of `P` containing `x`
(the carrier face of `x`; `∅` when `x ∉ P.space`). -/
noncomputable def carrier (P : Cx n) (x : E n) : Finset (E n) :=
  if h : ∃ σ ∈ P.faces, x ∈ PL.simp σ ∧ ∀ ρ ∈ P.faces, x ∈ PL.simp ρ → σ ⊆ ρ then h.choose else ∅

/-- Barycentric coordinates of `x` with respect to its carrier face; zero off that face. -/
noncomputable def coord (P : Cx n) (x : E n) (v : E n) : ℝ :=
  if _ : v ∈ carrier P x then
    (if h : ∃ μ : E n → ℝ, (∀ w ∈ carrier P x, 0 ≤ μ w) ∧
        (∑ w ∈ carrier P x, μ w = 1) ∧ (∑ w ∈ carrier P x, μ w • w = x) then h.choose else 0) v
  else 0

/-- All vertices occurring in `P`. -/
noncomputable def verts (P : Cx n) (hP : P.faces.Finite) : Finset (E n) :=
  hP.toFinset.biUnion id

/-- All subsets of faces of `P`: the possible level sets of the subdivision. -/
noncomputable def cands (P : Cx n) (hP : P.faces.Finite) : Finset (Finset (E n)) :=
  hP.toFinset.biUnion (fun σ => σ.powerset)

/-- Minimum of `μ` on a finite set (`0` on the empty set). -/
noncomputable def minVal (s : Finset (E n)) (μ : E n → ℝ) : ℝ :=
  if h : s.Nonempty then (s.image μ).min' (h.image _) else 0

/-- Maximum of `μ` on a finite set (`0` on the empty set). -/
noncomputable def maxVal (s : Finset (E n)) (μ : E n → ℝ) : ℝ :=
  if h : s.Nonempty then (s.image μ).max' (h.image _) else 0

/-- The mass of the barycentric-subdivision simplex indexed by `τ`: the difference of the level value
of `τ` and the level value of the next level set.  Non-zero masses occur exactly at the level sets of
the coordinates, and there they are positive. -/
noncomputable def massG (P : Cx n) (hP : P.faces.Finite) (x : E n) (τ : Finset (E n)) : ℝ :=
  max 0 ((τ.card : ℝ) * (minVal τ (coord P x) - maxVal (verts P hP \ τ) (coord P x)))

/-- The mass of a level set, computed with respect to a fixed face (used for the local analysis). -/
noncomputable def massOf (σ : Finset (E n)) (μ : E n → ℝ) (τ : Finset (E n)) : ℝ :=
  max 0 ((τ.card : ℝ) * (minVal τ μ - maxVal (σ \ τ) μ))

/-- The low part `A(x)` of `x`. -/
noncomputable def AOf (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) : E n :=
  ∑ τ ∈ cands P hP, if LowFace β p τ then massG P hP x τ • bary τ else 0

/-- The high part `B(x)` of `x`. -/
noncomputable def BOf (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) : E n :=
  ∑ τ ∈ cands P hP, if LowFace β p τ then 0 else massG P hP x τ • bary τ

/-- The total high mass `S(x)`. -/
noncomputable def SOf (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) : ℝ :=
  ∑ τ ∈ cands P hP, if LowFace β p τ then 0 else massG P hP x τ

/-- The low end of the join segment through `x` (`0` when it is not defined). -/
noncomputable def uOf (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) : E n :=
  if 1 - SOf β p P hP x = 0 then 0 else (1 - SOf β p P hP x)⁻¹ • AOf β p P hP x

/-- The high end of the join segment through `x` (`0` when it is not defined). -/
noncomputable def wOf (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) : E n :=
  if SOf β p P hP x = 0 then 0 else (SOf β p P hP x)⁻¹ • BOf β p P hP x

/-- Clamp to `[0,1]`. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

/-- The join-segment data `(u,w)` of a point: its low and high endpoints. -/
noncomputable def segOf (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (x : E n) : E n × E n :=
  (uOf β p P hP x, wOf β p P hP x)

/-- The set of join segments contained in the boundary of the cube. -/
def BdrySeg (β : ℝ) : Set (E n × E n) :=
  {q | ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • q.1 + t • q.2 ∈ bdryCube β}

/-- The taper of the stretch: `1` on segments lying in the boundary of the cube (so that the
resulting map is the identity there), and `M` on segments at distance at least `(β-α)/2` from it
(in particular on all segments meeting `closedCube α`). -/
noncomputable def taperM (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (α M : ℝ) (x : E n) : ℝ :=
  1 + (M - 1) * clamp01 (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2))

/-- The stretch with a prescribed rescaling factor `Mb x` of the high part. -/
noncomputable def stretchM (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (Mb : E n → ℝ)
    (x : E n) : E n :=
  if x ∈ P.space then
    (1 + (Mb x - 1) * SOf β p P hP x)⁻¹ • (AOf β p P hP x + (Mb x) • BOf β p P hP x)
  else x

/-- The stretch map: rescale the high part by the taper and renormalise. -/
noncomputable def stretch (P : Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (α M : ℝ) (x : E n) : E n :=
  stretchM β p P hP (taperM β p P hP α M) x

end Work.Geo.DualStretch
