import Mathlib.Analysis.Convex.Measure
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.QBop.ae_abox_slot_notMem_frontier`

For almost every configuration `x` of the centred `N`-particle box
`abox N ℓ = (acube ℓ)ᴺ`, the slot-`j` coordinate `x j` lies *off* the boundary
`frontier (acube ℓ)` of the one-particle centred cube.  Equivalently: no
coordinate of `x j` is pinned to the value `±ℓ/2` except on a null set.  This
is the side condition one needs whenever a quantity is discontinuous on the
faces of the box (FS's `χ_Λ`, the Dirichlet extension by zero, ...) while the
measure lives on the closed box.

## Proof route

* `convex_acube` — `acube ℓ` is a product of closed intervals `Icc (−ℓ/2) (ℓ/2)`,
  hence convex in `ℝ³ = EuclideanSpace ℝ (Fin 3)`;
* `volume_frontier_acube` — the frontier of a convex subset of a
  finite-dimensional real vector space is null for any additive Haar measure
  (`Convex.addHaar_frontier`, with `volume` an additive Haar measure on `ℝ³`);
* the marginal step: `volume` on `X N = Fin N → ℝ³` is *definitionally*
  `Measure.pi (fun _ : Fin N => volume)` (this is the corpus's `rfl` rewrite
  also used in `Submission/CentreBox.lean`), and
  `Measure.pi_eval_preimage_null` says that a set which constrains one
  coordinate only through a `μ j`-null set is itself `Measure.pi μ`-null;
* finally `Measure.restrict_apply_le` bounds the measure restricted to
  `abox N ℓ` by the ambient one, and `MeasureTheory.ae_iff` converts the
  almost-everywhere statement into this null-set statement.

The hypothesis `hℓ : 0 < ℓ` is inherited verbatim from the requester's
statement; the argument does not need it (for `ℓ ≤ 0` the cube `acube ℓ` is
empty or a point, so `abox N ℓ` is null and the statement holds vacuously).
-/

noncomputable section

open MeasureTheory
open scoped Topology ENNReal

namespace Work.BoseFixB3.QBop

-- `hℓ : 0 < ℓ` of the requested statement is not needed by the argument (see the
-- module docstring): the statement also holds for `ℓ ≤ 0`, where the cube is
-- empty or a point.  Silenced rather than renamed so that the statement stays
-- character-for-character the requester's.
set_option linter.unusedVariables false

/-- The centred cube `acube ℓ` is convex: membership is coordinatewise and each
coordinate is constrained to a closed interval. -/
lemma convex_acube (ℓ : ℝ) : Convex ℝ (Submission.BoseGases.acube ℓ) := by
  intro x hx y hy a b ha hb hab m
  have hx' : x m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hx m
  have hy' : y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hy m
  have h := (convex_Icc (-ℓ / 2) (ℓ / 2)) hx' hy' ha hb hab
  simpa using h

/-- The frontier of the centred cube is Lebesgue-null in `ℝ³`: it is the
frontier of a convex set, and the Lebesgue measure on `ℝ³` is an additive Haar
measure. -/
lemma volume_frontier_acube (ℓ : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (frontier (Submission.BoseGases.acube ℓ)) = 0 :=
  (convex_acube ℓ).addHaar_frontier (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-- A set of configurations that constrains a single slot `j` only through a
Lebesgue-null subset of `ℝ³` is null for the ambient product measure on `X N`. -/
lemma volume_preimage_slot_null {N : ℕ} (j : Fin N) {s : Set (EuclideanSpace ℝ (Fin 3))}
    (hs : (volume : Measure (EuclideanSpace ℝ (Fin 3))) s = 0) :
    (volume : Measure (Submission.BoseGases.X N))
      {x : Submission.BoseGases.X N | x j ∈ s} = 0 := by
  rw [show (volume : Measure (Submission.BoseGases.X N))
      = Measure.pi (fun _ : Fin N => (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      from rfl]
  exact Measure.pi_eval_preimage_null _ hs

theorem ae_abox_slot_notMem_frontier {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin N) :
    ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)),
      x j ∉ frontier (Submission.BoseGases.acube ℓ) := by
  have hnull : (volume : Measure (Submission.BoseGases.X N))
      {x : Submission.BoseGases.X N | x j ∈ frontier (Submission.BoseGases.acube ℓ)} = 0 :=
    volume_preimage_slot_null j (volume_frontier_acube ℓ)
  rw [MeasureTheory.ae_iff]
  simp only [not_not]
  have hle := Measure.restrict_apply_le (μ := (volume : Measure (Submission.BoseGases.X N)))
    (Submission.BoseGases.abox N ℓ)
    {x : Submission.BoseGases.X N | x j ∈ frontier (Submission.BoseGases.acube ℓ)}
  exact le_antisymm (le_trans hle (le_of_eq hnull)) bot_le

end Work.BoseFixB3.QBop
