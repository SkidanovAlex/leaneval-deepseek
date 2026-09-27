import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.borelOrbitImage

/-!
# `Work.EKLC6Core.CellSysDefs` — the cell system of the conull plaque family

Vocabulary for `Work.EKLC6Core.exists_plaque_family_conull`: a countable family of pairwise
disjoint small open "cells" covering a conull set, each contained in a `V (δ/2)`-ball around a
point `mkX (g k)`, with the injectivity/smallness conditions at the centres, thin boundaries and
summable thinness constants.

The *lifted ball* of the `k`-th cell is `lifted δ (g k) = V δ · g k`, on which `mkX` is injective;
the *cylinder generators* are `gen U δ (g k) O`, the image of the intersection of the lifted ball
with the `U`-saturation of `O`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The lifted ball `V δ · g` around a point of `SL₃(ℝ)`. -/
def lifted (δ : ℝ) (g : SL3) : Set SL3 := (fun v : SL3 => v * g) '' (V δ)

/-- The left `U`-saturation of a set `O` of group elements. -/
def satU (U : Subgroup SL3) (O : Set SL3) : Set SL3 := {h | ∃ u ∈ U, ∃ o ∈ O, u * o = h}

/-- A cylinder generator: the image in `X₃` of the intersection of the lifted ball with the
`U`-saturation of `O`. -/
def gen (U : Subgroup SL3) (δ : ℝ) (g : SL3) (O : Set SL3) : Set X3 :=
  mkX '' (satU U O ∩ lifted δ g)

/-- The cell around `g` at radius `δ`. -/
def cell (δ : ℝ) (g : SL3) : Set X3 := mkX '' (lifted δ g)

/-- The `V η`-collar of the boundary of a set, pushed into `X₃` by the action. -/
def VThickX (η : ℝ) (s : Set X3) : Set X3 :=
  (fun p : SL3 × X3 => p.1 • p.2) '' ((V η) ×ˢ s)

/-- **The cell system** for the conull plaque family: countably many pairwise disjoint small open
cells covering a conull set, each inside a `V (δ k / 2)`-ball about a centre satisfying the
injectivity condition (so that `mkX` is injective on the lifted ball `V (δ k) · g k`) and the
smallness ("goodness") condition needed to identify the atoms, with summable thin-boundary
constants.

## How such a system is built (Pisa 7.38, iterated)

* Start with `L 0 = univ` (closed).  At stage `j`, take a compact `K j ⊆ L j` with
  `μ (L j \ K j) ≤ ε * μ (L j)` (`ε = 1/2` say) and cover `K j` by finitely many balls of radius
  `ρ j`, where the radii are chosen at *differentiability points* of `x ↦ μ (Vball x)` so that
  each ball has a thin frontier (`Work.EKLC6Core.exists_thin_radius`), and where the centres are
  taken in the *good* set (see below); then replace the balls by their staircase pieces and take
  interiors, so the pieces are open, disjoint and have thin frontiers
  (`Work.EKLC6Core.thin_boundary_partition`, `Work.EKLC6Core.exists_pattern_partition_thin`).
  Set `L (j+1) = L j \` (the new cells): again closed, with `μ (L (j+1)) ≤ 2 ε μ (L j)`, so
  `μ (L j) → 0` and the total leftover `⋂ j L j` is `μ`-null.
* **The goodness/injectivity constraints are pointwise**: `hgood` (with `v = v' = 1`) forces the
  lifted ball `V (δ k) · g k` to avoid the set `P = {x : Stab x ∩ U ≠ {1}}` of points with a
  non-trivial `U`-stabiliser, and `hinj` forces the same with `V (4 δ k)`.  So cells of scale `δ`
  must keep `δ`-distance `≳ δ` from `P`; this is the standard **multi-scale** structure, and it is
  compatible with `hcover` because `μ P = 0` (`Work.EKLC6Core.ae_free_orbit_of_contraction`), so a
  countable family of scales with `δ → 0` still covers a conull set.
* **Thinness, with a finite total constant, is the point to get right** (`hthin` with
  `∑' c < ∞`): a cell of scale `δ k` near `P` contributes a frontier collar of size `≳ δ k⁷`
  (`dim X₃ = 8`), and the cells at scale `δ` cover roughly the `δ`-neighbourhood of `P`, of measure
  `m δ`.  The sum `∑ k c k ≈ ∑ δ (m δ / δ)` is finite as soon as `m δ = O (δ^{1+ε})` for some
  `ε > 0`; the Borel–Cantelli argument (`ae_margin_cellsys`) only needs
  `∑ n μ (Nbd (c μ0^n)) < ∞`, so if the decay `m δ = O (δ^θ)` with `θ ≤ 1` makes the union collar
  behave like `η^θ`, one should weaken `hthin` here to

    `∃ C θ, 0 < θ ∧ ∀ η > 0, μ (⋃ k, VThickX η (frontier (Q k))) ≤ ofReal (C * η ^ θ)`

  (or keep the finite-total-constant form if the collapse `∑ δ m δ / δ < ∞` can be proved). -/
structure CellSys (μ : MeasureTheory.Measure X3) (U : Subgroup SL3) where
  /-- the cells -/
  Q : ℕ → Set X3
  hopen : ∀ k, IsOpen (Q k)
  hdisj : ∀ k l, k ≠ l → Disjoint (Q k) (Q l)
  hcover : μ ((⋃ k, Q k))ᶜ = 0
  /-- the radii -/
  δ : ℕ → ℝ
  hδpos : ∀ k, 0 < δ k
  hδsmall : ∀ k, δ k ≤ 1 / 16
  /-- the centres, as lifts -/
  g : ℕ → SL3
  hsub : ∀ k, Q k ⊆ (fun v : SL3 => v • mkX (g k)) '' (V (δ k / 2))
  /-- injectivity of `mkX` on the lifted ball: no two `V (2 δ k)`-perturbations of the centre
  agree -/
  hinj : ∀ k (v₁ v₂ : SL3), v₁ ∈ V (4 * δ k) → v₂ ∈ V (4 * δ k) →
    v₁ • mkX (g k) = v₂ • mkX (g k) → v₁ = v₂
  /-- the "goodness" of the centre: the lifted ball contains no lattice correction -/
  hgood : ∀ k (u : SL3) (v v' γ : SL3), u ∈ U → v ∈ V (δ k) → v' ∈ V (δ k) → γ ∈ Γ3 →
    u * v * g k = v' * g k * γ → γ = 1
  /-- the thin-boundary constant and exponent: the `η`-collar of the union of the frontiers of
  the cells has measure `O (η ^ θ)`.  (This is the quantitative thinness that the Borel–Cantelli
  tracking argument needs: `∑ n (c μ0^n)^θ < ∞` for `μ0 < 1`.) -/
  C : ℝ
  hC0 : 0 ≤ C
  θ : ℝ
  hθ0 : 0 < θ
  hthin : ∀ η : ℝ, 0 < η → μ (⋃ k, VThickX η (frontier (Q k)))
    ≤ ENNReal.ofReal (C * η ^ θ)

end Work.EKLC6Core

namespace Work.EKLC6Core

open Work.EKLContract

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3}

/-- Monotonicity of the displacement neighbourhoods. -/
theorem V_mono' {s t : ℝ} (h : s ≤ t) : V s ⊆ V t :=
  fun g hg i j => lt_of_lt_of_le (hg i j) h

/-- The **clipped** cylinder generator of the `k`-th cell: the image in `Q k` of the intersection
of the lifted ball `V (δ k) · g k` with the `U`-saturation of `O m`.  The clipping by `Q k` is
essential: an unclipped generator of one cell would spill into the neighbouring cells and destroy
the atom computation. -/
def genC (S : CellSys μ U) (O : ℕ → Set SL3) (k m : ℕ) : Set X3 :=
  mkX '' (satU U (O m) ∩ lifted (S.δ k) (S.g k)) ∩ S.Q k

/-- The generating family of the cell system: the cells together with the clipped cylinder
generators built from a countable family `O` of subsets of `SL₃(ℝ)`. -/
def fam (S : CellSys μ U) (O : ℕ → Set SL3) : Set (Set X3) :=
  Set.range S.Q ∪ Set.range (fun p : ℕ × ℕ => genC S O p.1 p.2)

/-- The σ-algebra generated by the cell system and the cylinders. -/
def MSig (S : CellSys μ U) (O : ℕ → Set SL3) : MeasurableSpace X3 :=
  MeasurableSpace.generateFrom (fam S O)

/-- The lift of a point of a cell: the unique element of the lifted ball mapping to it. -/
noncomputable def lift (S : CellSys μ U) (k : ℕ) (y : X3) : SL3 := by
  classical
  exact if h : y ∈ S.Q k then Classical.choose (S.hsub k h) * S.g k else 1

end Work.EKLC6Core
