import Mathlib
import Submission.Work.Drive.hdenseDesignData
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.diamCoreParity
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.endsParity
import Submission.Work.Drive.chartShiftHsurj

/-!
# The one-parameter design data of the `hdense` node (`NOTES_LEAD_hdense.md`)

The `hdense` node `Work.Drive.hdense_sideGerm` is the three-block analogue of the `hn2` endpoint
`Work.Drive.RefTripleAt`: everything is taken at **one** parameter `t : ℝ¹²` of the perturbation
`chartPert`, and the residual obligations are the *producers* of the conditions at that `t`.

This file contains only the three definitions of the lead's note (§2), so that the producers and the
endpoint agree on the vocabulary:

* `Work.Drive.DiamFamReg Q θ c P` — the regularity data of the two deformation families
  `diamFam Q θ`, `arcFam Q θ` against the sweep `clampedSweep c (fun s => 1-s) P` at the core-meet
  angle `θ`: this is exactly the four hypotheses `htransD`, `hfaceD`, `htransA`, `hfaceA` of
  `Work.Drive.odd_ncard_diamMeet_iff_coreSideCount` (`diamCoreParity.lean`), i.e. `ht5` at that angle;
* `Work.Drive.T6GenAtD Q P₁ P₂ c₁ c₂` — `T6GenAt` together with `DiamFamReg` at every core meet: the
  at-one-parameter inputs of the transport `T6`;
* `Work.Drive.DesignTripleAt Q c cblk u t` — the design's goodness (`DesignGoodData`), the class-triple
  oddness (`hodd`), and the three `T6GenAtD` blocks at the parameter `t`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- Joint `C^∞`-smoothness of a family of `2`-chains in the design parameter (relative to the concrete
structure `Work.Drive.cappingCharted`).  Stated as a definition so that statements about it can be
written without the local `ChartedSpace CappingSpace` instance. -/
def IsSmoothFam₂ {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  ContMDiff (modelWithCornersSelf ℝ (P × EuclideanSpace ℝ (Fin 2)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : P × EuclideanSpace ℝ (Fin 2) => A q.1 q.2)

/-- Joint `C^∞`-smoothness of a family of `3`-chains in the design parameter. -/
def IsSmoothFam₃ {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace) : Prop :=
  ContMDiff (modelWithCornersSelf ℝ (P × EuclideanSpace ℝ (Fin 3)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2)

/-- **The `DiamFamReg` conditions for abstract chains**: the same four clauses as `DiamFamReg`, with
the two deformation families `diamFam Q θ`, `arcFam Q θ` replaced by abstract `A`, `A'` and the sweep
`clampedSweep c (fun s => 1 - s) P` by an abstract `D`.  This is the form in which the *openness* of
the conditions in a family of chains can be stated. -/
def DiamFamRegL (A A' : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (D : EuclideanSpace ℝ (Fin 3) → CappingSpace) : Prop :=
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A u = D x →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) A u).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) D x).toLinearMap = ⊤) ∧
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A u = D x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
    (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
          mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ τ j ≠ 0)) ∧
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A' u = D x →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) A' u).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) D x).toLinearMap = ⊤) ∧
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A' u = D x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
    (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
          mfderiv (𝓡 2) (𝓡 4) A' u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) A' u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ τ j ≠ 0))

/-- **The *box-restricted* `DiamFamReg` conditions.**  Same clauses as `DiamFamRegL`, except that the
two *transversality* clauses are only required at meet points **in the box** (`u ∈ unitBox 1`,
`x ∈ unitBox 2`) — which is where the parity engine consumes them.  Unlike `DiamFamRegL` (whose
unbounded transversality clause is **not** open in a family parameter, see
`Submission/Work/Drive/NOTE_DiamFamReg_not_open.md`), this condition *is* open, so it is the form the
producer of the `hdense` data can supply. -/
def DiamFamRegBox (A A' : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (D : EuclideanSpace ℝ (Fin 3) → CappingSpace) : Prop :=
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A u = D x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) A u).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) D x).toLinearMap = ⊤) ∧
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A u = D x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
    (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
          mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) A u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ τ j ≠ 0)) ∧
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A' u = D x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    LinearMap.range (mfderiv (𝓡 2) (𝓡 4) A' u).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) D x).toLinearMap = ⊤) ∧
  (∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)), A' u = D x →
    u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
    (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
    (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
          mfderiv (𝓡 2) (𝓡 4) A' u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) A' u σ = mfderiv (𝓡 3) (𝓡 4) D x τ ∧ τ j ≠ 0))

/-- **`Work.Drive.DiamFamReg` (H4's `T6GenAtD.lean`, now itself box-restricted) is the instance of
`Work.Drive.DiamFamRegBox` at `A := diamFam Q θ`, `A' := arcFam Q θ`, `D := clampedSweep c (1-·) P`.** -/
theorem DiamFamReg_iff_DiamFamRegBox {Q : ℂ → CappingSpace} {θ c : ℝ}
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace} :
    DiamFamReg Q θ c P ↔
      DiamFamRegBox (diamFam Q θ) (arcFam Q θ) (clampedSweep c (fun s => 1 - s) P) :=
  Iff.of_eq rfl

-- **`T6GenAtDBox` (the box-restricted, `def`-free form).**  The declaration of this name lives in
-- `Submission/Work/Drive/T6GenAtD.lean` (as `abbrev T6GenAtDBox := T6GenAtD`, whose `DiamFamReg` is
-- already the box-restricted quartet, so it is *definitionally equal* to the `DiamFamRegBox` form
-- written here earlier).  The duplicate `def` that used to sit at this spot made this module
-- unbuildable ("`T6GenAtDBox` has already been declared", `T6GenAtD` is imported above), which blocked
-- `Work.Drive.eventually_DiamFamRegBox`, `Work.Drive.germDataAt`,
-- `Work.Drive.hdense_identity_of_designTripleAt` and `Work.Drive.dense_T6GenAtDBox_design`; it has been
-- removed (H3 lane, 2026-09-27, as requested by the status note of `Drive/hdense_sideGerm.lean`).

/-- **The design's one-parameter data of the `hdense` node**: the perturbed-design goodness, the
class-triple oddness, and the three `T6GenAtD` blocks of the block triple at the time `t`. -/
def DesignTripleAt (Q : ℂ → CappingSpace) (c : ℝ) (cblk : Fin 3 → ℝ)
    (u : Fin 3 → UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  DesignGoodData Q c cblk u t ∧
    Odd (classTripleSet
      (fun k z => chartPert (blk k t) (rotPresentation Q (u k) z))).ncard ∧
    ∀ k : Fin 3,
      T6GenAtDBox (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
        (cblk (k + 1)) (cblk (k + 2))

end

end Work.Drive

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The per-block transport conclusion `hblock` at the design's triple and parameter**: the `T6`
equivalence of block `k`.  This is the conclusion of the transport wrapper (item (E1) of
`NOTES_LEAD_hdense.md` §3, H4's lane) at the blocks of the design; it is carried as a hypothesis of
the endpoint `Work.Drive.hdense_identity_of_designTripleAt` until that wrapper lands, at which point
it follows from `DesignTripleAt`'s third conjunct. -/
def BlockT6At (Q : ℂ → CappingSpace) (c : ℝ) (cblk : Fin 3 → ℝ)
    (u : Fin 3 → UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  ∀ k : Fin 3,
    Odd ((topBdryMeet CappingSpace
        (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) k).ncard) ↔
      (Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
            (cblk (k + 1))
            (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1)))
        ∧ Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
            (cblk (k + 2))
            (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))))

/-- **The germ-lane data at the six ordered pairs of the design's triple.**  These are the inputs of
`Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt_guarded` at the two levels `c`, `cblk j` and at the six
angles `u j - u k`: the parity locality at each level and the cross-level parity agreement.  They are
the "germ locality" hypotheses of the route (proved lemmas
`Work.Drive.sideGerm_parity_eq_of_close_of_separation` and
`Work.Drive.odd_coreSideCount_eq_of_levelBand` with their own separation/`GoodPair` inputs). -/
def GermDataAt (Q : ℂ → CappingSpace) (c : ℝ) (cblk : Fin 3 → ℝ)
    (u : Fin 3 → UnitAddCircle) (ε : ℝ) : Prop :=
  (∀ (k j : Fin 3), k ≠ j →
    ∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖t‖ < ε → ‖t'‖ < ε →
      GoodAt (fun s p => chartPert s p) Q c (u j - u k) t →
      GoodAt (fun s p => chartPert s p) Q c (u j - u k) t' →
      Odd (CntAt (fun s p => chartPert s p) Q c (u j - u k) t) =
        Odd (CntAt (fun s p => chartPert s p) Q c (u j - u k) t'))
  ∧ (∀ (k j : Fin 3), k ≠ j →
    ∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖t‖ < ε → ‖t'‖ < ε →
      GoodAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t →
      GoodAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t' →
      Odd (CntAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t) =
        Odd (CntAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t'))
  ∧ (∀ (k j : Fin 3), k ≠ j →
    ∀ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4), ‖t‖ < ε →
      GoodAt (fun s p => chartPert s p) Q c (u j - u k) t →
      GoodAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t →
      Odd (CntAt (fun s p => chartPert s p) Q c (u j - u k) t) =
        Odd (CntAt (fun s p => chartPert s p) Q (cblk j) (u j - u k) t))

end

end Work.Drive
