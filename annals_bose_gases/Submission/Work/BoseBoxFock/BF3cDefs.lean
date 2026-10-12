import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.Nodes
import Submission.Work.BoseBoxFock.sectorSliceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.BF3cDefs` — the sector vocabulary of the box ↔ model bridge (BF3c)

Two decompositions of a box state `Φ : X n → ℝ` are needed by `box_to_model` (`BF3C_PLAN_S7.md`):

* the **θ-sectors** of this file: the commuting slot projections `aP_i` (mean over the box,
  `Submission.Q0Sector.aP`) and `aQ_i = 1 − aP_i = 1 − aP` give, for every `S : Finset (Fin n)`,
  the projection

      `thetaSector ℓ S Φ = Π_{i ∈ S} aP_i · Π_{i ∉ S} aQ_i Φ
                         = Σ_{T ⊇ S} (−1)^{|T| − |S|} meanProj ℓ T Φ`

  onto the states with *exactly* the slots in `S` in the condensate.  `n₊ = Σ_i aQ_i` acts on
  `thetaSector ℓ S Φ` as `(n − |S|)`, so the box moment bound `SpectralNPlusLe ℓ M Φ` forces
  `thetaSector ℓ S Φ = 0` whenever `n − |S| > M`; this is the source of the model-side
  `ExcWindow` requirement (`BF3C_PLAN_S7.md` §1(c), §3 P2).

* the **V/W sectors** are the `Work.BoseBoxFock.slotExact e S Φ` of `FibreProjDefs.lean`
  (already defined there), with `e` the honest mode family; they are the fibres the *energy* is
  diagonal in (BF3C_PLAN_S7.md §1(a), §3 P3).

The definitions mirror `FibreProjDefs.slotExact`: the only change is that the slot kernel `PV e`
(projection onto `span{e l}`) is replaced by the constant `(ℓ³)⁻¹` (projection onto the
constants on the box), so that `meanProj ℓ T` is the *product of the slot means*.
-/

noncomputable section

open MeasureTheory Submission.BoseGases
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false


/-- The mean projection on the slot set `S` of a box state: the mean over the box of every slot
in `S`, the other slots kept.  This is the iterated `aP ℓ i` over `i ∈ S`
(`aP ℓ i Φ x = (ℓ³)⁻¹ ∫_{y ∈ acube ℓ} Φ (update x i y)`). -/
noncomputable def meanProj {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n))
    (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) : ℝ :=
  ∫ z in Set.pi Set.univ
      (fun _i : {i : Fin n // i ∈ S} => Submission.BoseGases.acube ℓ),
    (∏ _i : {i : Fin n // i ∈ S}, (ℓ ^ 3)⁻¹) *
      Φ (fun i => if h : i ∈ S then z ⟨i, h⟩ else x i)

/-- **The `S`-θ-sector**: the part of `Φ` whose slots in `S` are in the condensate and whose slots
outside `S` are not, written by inclusion–exclusion over the supersets of `S`:
`thetaSector ℓ S Φ = Σ_{T ⊇ S} (−1)^{|T| − |S|} meanProj ℓ T Φ`. -/
noncomputable def thetaSector {n : ℕ} (ℓ : ℝ) (S : Finset (Fin n))
    (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) : ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
    (-1 : ℝ) ^ (T.card - S.card) * meanProj ℓ T Φ x

/-- The `k`-θ-sector of `Φ`: the sum of the `S`-θ-sectors over the slot sets of cardinality `k`.
This is the component of `Φ` with exactly `k` particles in the condensate, i.e. the
`n₊ = n − k` eigenspace component. -/
noncomputable def thetaSectorCard {n : ℕ} (ℓ : ℝ) (k : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k), thetaSector ℓ S Φ x

/-! ## The partial pairing of a state on a slot set (the model map of BF3c)

`box_to_model` must produce a *model* vector from a box state.  The fibre selection of
`BF3C_PLAN_S7.md` §1 works on the V/W sector `Θ = slotExact e S Φ`, and the model map is the
**partial pairing** of the sector against an ONB of the complement variables, followed by
`boxCompress` (`BF3C_PLAN.md` §5, `BF3C_PLAN_S7.md` §1(b), §5).  These two definitions are the
vocabulary of that construction. -/

/-- **The partial pairing of `Θ` against the test function `ψ` on the complement slots**:
`pairOf S Θ ψ u = ∫ conj(ψ y) · Θ(u on S, y off S) dy`.  For a *symmetric* `Θ` the result is
automatically symmetric in the `S`-slots, hence (being built from `V`-modes) a legitimate
`j = S.card`-particle bosonic state — this is `BF3C_PLAN_S7.md` §5(i). -/
noncomputable def pairOf {n : ℕ} (S : Finset (Fin n))
    (Θ : Submission.BoseGases.X n → ℂ)
    (ψ : ({i : Fin n // i ∉ S} → EuclideanSpace ℝ (Fin 3)) → ℂ) :
    ({i : Fin n // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ :=
  fun u => ∫ y, star (ψ y) * Θ (pairCoord S u y)

end Work.BoseBoxFock
