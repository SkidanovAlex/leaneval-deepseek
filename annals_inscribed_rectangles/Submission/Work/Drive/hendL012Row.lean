import Mathlib
import Submission.Work.Drive.sweepGenericityGeneral
import Submission.Work.Drive.chartPert_linPlaneChart
import Submission.Work.Drive.pairRegLinBase
import Submission.Work.Drive.blockPlaneInvariant
import Submission.Work.Drive.blockVocabulary

/-!
# The `hendL012` row of the ends-clause design — the last class-level row, by the general sweep
genericity

`Work.Drive.exists_endTripleReg_sweepGeneral` (`Drive/sweepGenericityGeneral.lean`) produces, for an
arbitrary triple `P` of plane presentations, a small parameter `t` at which

`EndTripleReg (planeClassMap (chartPert (blk 0 t) ∘ P 0)) (planeClassMap (chartPert (blk 1 t) ∘ P 1))
  (planeClassMap (chartPert (blk 2 t) ∘ P 2))`

holds.  The row `hendL012` of `hasClassLinearization_of_endData` (`NOTES_LEAD_hodd_blockT6.md` §3) has
a **linear** first block (a `linPlaneChart` model) and two perturbed *rotated charts of the curve's
chart* `Q` in the second and third blocks — the one row that no linear/incidence criterion and no
`Meet3Hyp` of the design's own triple can produce (the mixed trio has a frozen first block).

This file supplies the two steps that turn the general theorem into that row:

* `planeClassMap_chartPert_diskPlane_linPlaneChart` — the **first argument is level- and
  perturbation-independent in the right sense**: the class map of the *transported linear model*
  `chartPert τ ∘ diskPlane (linPlaneChart Φ c hc)` is the class map of the linear plane chart with
  functional `Φ.trans (classEquiv τ)`.  (Proof: `chartPert` commutes with `diskPlane`,
  `Work.Drive.chartPert_linPlaneChart` transports the functional, and
  `Work.Drive.planeClassMap_diskPlane_linPlaneChart_eq_of_level` removes the level.)
* `Work.Drive.exists_hendL012_row_chartPert` — the row itself: for a **fixed** linear iso `Φ`, two
  plane presentations `P₁`, `P₂` (smooth, seam-invariant, `foldBox`-invariant) and any open set `A`
  accumulating at `0`, there is `t ∈ A` of norm `< ε'` with

  `EndTripleReg (planeClassMap (diskPlane (linPlaneChart (Φ.trans (classEquiv (blk 0 t))) cl hcl)))
    (planeClassMap (fun y => chartPert (blk 1 t) (P₁ y)))
    (planeClassMap (fun y => chartPert (blk 2 t) (P₂ y)))`.

**Design consequence (important).**  The first argument of the row delivered here is the linear model
*transported by* `classEquiv (blk 0 t)`, i.e. `chartPert (blk 0 t) ∘ linPlaneOf Φ cl hcl` read as a
class map.  This is *not* an artefact: the family `sweepChartFam` perturbs its block `0` like the other
two (that is what gives the family its full parameter reach, hence the richness `hrich` of the
localized Sard), so the only linear-plane row obtainable from a sweep genericity is the transported
one.  A consumer that wants the row with a *fixed* `lin 0` must instead use a frozen first block — for
which the richness of the localized Sard is *not* available from `richness_sweepChartFam` (a frozen
block loses its parameter directions, and the level coordinate of a chain cannot be restored by a box
reparametrisation because `Work.Drive.meet3Hyp_of_boxReparam`'s face condition forbids shearing it).
The clean way to consume the row below is therefore to instantiate the whole ends-clause assembly
`Work.Drive.hasClassLinearization_of_endData` with the **transported** first functional
`(Φ 0).trans (classEquiv (blk 0 t))` — the other rows involving `lin 0` are then *open* conditions on
the plane, all true at `t = 0`, hence in a neighbourhood of `0` (and the Sard's parameter can be taken
arbitrarily small), while `Work.Drive.chartPert_linPlaneChart` and the level-independence of the class
map identify `lin 0` with `chartPert (blk 0 t) ∘ linPlaneOf Φ cl hcl` up to that transport.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 2000000

noncomputable section

/-- **`chartPert` commutes with `diskPlane`**: the chart perturbation of a disk presentation is the
disk presentation of the perturbed chart. -/
theorem chartPert_diskPlane (τ : Eucl 3) (Q : ℂ → CappingSpace) :
    (fun y : EuclideanSpace ℝ (Fin 2) => chartPert τ (diskPlane Q y))
      = diskPlane (fun z : ℂ => chartPert τ (Q z)) := rfl

/-- **The class map of the transported linear model.**  The class map of
`chartPert τ ∘ diskPlane (linPlaneChart Φ c hc)` is the class map of the linear plane chart whose
functional is `Φ.trans (classEquiv τ)` — at *any* level (`c` is arbitrary positive), because the class
map of a linear plane chart does not depend on the level. -/
theorem planeClassMap_chartPert_diskPlane_linPlaneChart (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (τ : Eucl 3) :
    planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert τ (diskPlane (linPlaneChart Φ c hc) y))
      = planeClassMap (diskPlane (linPlaneChart (Φ.trans (classEquiv τ)) c hc)) := by
  have h1 : (fun y : EuclideanSpace ℝ (Fin 2) => chartPert τ (diskPlane (linPlaneChart Φ c hc) y))
      = diskPlane (fun z : ℂ => chartPert τ (linPlaneChart Φ c hc z)) := rfl
  rw [h1]
  have h2 : (fun z : ℂ => chartPert τ (linPlaneChart Φ c hc z))
      = linPlaneChart (Φ.trans (classEquiv τ))
          (((levelScale τ ⟨c, hc⟩ : Set.Ioi (0 : ℝ))) : ℝ) (levelScale τ ⟨c, hc⟩).2 := by
    funext z
    exact congrFun (chartPert_linPlaneChart Φ c hc τ) z
  rw [h2]
  exact (planeClassMap_diskPlane_linPlaneChart_eq_of_level (Φ.trans (classEquiv τ)) c
    (((levelScale τ ⟨c, hc⟩ : Set.Ioi (0 : ℝ))) : ℝ) hc (levelScale τ ⟨c, hc⟩).2).symm

/-- **The `hendL012` row**, from the general sweep genericity: at a parameter `t ∈ A` of norm `< ε'`,
the three class maps (transported linear model, and the two chart-perturbed presentations) satisfy
`EndTripleReg`. -/
theorem exists_hendL012_row_chartPert {Q : ℂ → CappingSpace}
    (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP₁ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₁)
    (hP₂ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₂)
    (hseam₁ : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₁ y = P₁ (seamInv2 y))
    (hseam₂ : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₂ y = P₂ (seamInv2 y))
    (hinv₁ : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P₁ (affRep e mm y) = P₁ y)
    (hinv₂ : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P₂ (affRep e mm y) = P₂ y)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hA0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t‖ < δ)
    (ε' : ℝ) (hε' : 0 < ε')
    (hlevel : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < ε' →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        c 0 < levelOf (chartPert ((blk k) t) ((![diskPlane (linPlaneChart Φ cl hcl), P₁, P₂] :
          Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) k y))) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧ t ∈ A ∧
      EndTripleReg
        (planeClassMap (diskPlane (linPlaneChart (Φ.trans (classEquiv ((blk 0) t))) cl hcl)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 1) t) (P₁ y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 2) t) (P₂ y))) := by
  classical
  obtain ⟨t, htε, htA, htriple⟩ :=
    exists_endTripleReg_sweepGeneral (Q := Q) (fun s p => chartPert s p) (isChartPert_chartPert Q)
      c hc hcdist hc10 hc20
      (![diskPlane (linPlaneChart Φ cl hcl), P₁, P₂] :
        Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
      (by
        intro k
        fin_cases k
        · exact contMDiff_diskPlane (linPlaneChart_contMDiff Φ cl hcl)
        · exact hP₁
        · exact hP₂)
      (by
        intro k y hy
        fin_cases k
        · exact (diskPlane_seamInv2 (Q := linPlaneChart Φ cl hcl)
            (fun z hz => linPlaneChart_neg Φ cl hcl hz) hy).symm
        · exact hseam₁ y hy
        · exact hseam₂ y hy)
      (by
        intro e mm he k y
        fin_cases k
        · exact diskPlane_affRep he mm (linPlaneChart Φ cl hcl) y
        · exact hinv₁ e mm he y
        · exact hinv₂ e mm he y)
      A hAopen hA0 ε' hε' hlevel
  refine ⟨t, htε, htA, ?_⟩
  have hPM : planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
        chartPert ((blk 0) t)
          ((![diskPlane (linPlaneChart Φ cl hcl), P₁, P₂] :
            Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 0 y))
      = planeClassMap (diskPlane (linPlaneChart (Φ.trans (classEquiv ((blk 0) t))) cl hcl)) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 0) t)
          ((![diskPlane (linPlaneChart Φ cl hcl), P₁, P₂] :
            Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 0 y))
        = (fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert ((blk 0) t) (diskPlane (linPlaneChart Φ cl hcl) y)) from rfl]
    exact planeClassMap_chartPert_diskPlane_linPlaneChart Φ cl hcl ((blk 0) t)
  rw [hPM] at htriple
  exact htriple


/-- **The two `Meet3Hyp` families of the design at *one* parameter** (`NOTES_LEAD_hodd_blockT6.md` §3):
the design's own triple (all three blocks perturbed rotated charts of `Q`) and the *mixed* triple whose
first block is a linear disk model (at a level `cl` above the truncation levels).  Both are transverse
at the same `t ∈ A`, by the family form of the general sweep genericity
(`Work.Drive.exists_meet3Hyp_sweepChartFam_family`, `ι := Bool`).

This is the Sard side of the class-level rows `hend012` (from the first family, via
`Work.Drive.endTripleReg_of_meet3Hyp_sweeps_unrestricted`) and `hendL012` (from the second, via the
transport of `Work.Drive.exists_hendL012_row_chartPert`): the *same* `t` is needed for both, because the
seven rows of `Work.Drive.hasClassLinearization_of_endData` are all evaluated at that single parameter.
The other rows involving a linear model (`PairReg lin₀lin₁`, `EndTripleReg lin₁lin₀P̂₂`,
`EndTripleReg lin₂lin₀lin₁`, and in the *reference* triple also `PairReg lin₀P̂₂`, `EndTripleReg
lin₁lin₀P̂₂`) are then open conditions on the plane, so they can be added to `A` (they hold at `t = 0`).
-/
theorem exists_twoMeet3Hyp_design_mixed {Q : ℂ → CappingSpace}
    (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (a c' : UnitAddCircle)
    (Pcfg : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPcfg : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Pcfg k))
    (hPcfgseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → Pcfg k y = Pcfg k (seamInv2 y))
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hA0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t‖ < δ)
    (ε' : ℝ) (hε' : 0 < ε') :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧ t ∈ A ∧
      Meet3Hyp CappingSpace (sweepChartFam Pcfg (fun s p => chartPert s p) c t) ∧
      Meet3Hyp CappingSpace
        (sweepChartFam (![diskPlane (linPlaneChart Φ cl hcl), Pcfg 1, Pcfg 2] :
            Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
          (fun s p => chartPert s p) c t) := by
  classical
  have hmod : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (diskPlane (linPlaneChart Φ cl hcl)) :=
    contMDiff_diskPlane (linPlaneChart_contMDiff Φ cl hcl)
  have hmodseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
      diskPlane (linPlaneChart Φ cl hcl) y = diskPlane (linPlaneChart Φ cl hcl) (seamInv2 y) :=
    fun y hy => (diskPlane_seamInv2 (Q := linPlaneChart Φ cl hcl)
      (fun z hz => linPlaneChart_neg Φ cl hcl hz) hy).symm
  obtain ⟨t, htε, htA, hboth⟩ :=
    exists_meet3Hyp_sweepChartFam_family (ι := Fin 2) (Q := Q) (fun s p => chartPert s p)
      (isChartPert_chartPert Q) c hc hcdist
      (![Pcfg, ![diskPlane (linPlaneChart Φ cl hcl), Pcfg 1, Pcfg 2]] :
        Fin 2 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
      (by
        intro j k
        fin_cases j
        · exact hPcfg k
        · fin_cases k
          · exact hmod
          · exact hPcfg 1
          · exact hPcfg 2)
      (by
        intro j k y hy
        fin_cases j
        · exact hPcfgseam k y hy
        · fin_cases k
          · exact hmodseam y hy
          · exact hPcfgseam 1 y hy
          · exact hPcfgseam 2 y hy)
      A hAopen hA0 ε' hε'
  have hfun0 : (![Pcfg, ![diskPlane (linPlaneChart Φ cl hcl), Pcfg 1, Pcfg 2]] :
      Fin 2 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 0 = Pcfg := by
    funext k y
    fin_cases k <;> rfl
  have hfun1 : (![Pcfg, ![diskPlane (linPlaneChart Φ cl hcl), Pcfg 1, Pcfg 2]] :
      Fin 2 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 1
      = ![diskPlane (linPlaneChart Φ cl hcl), Pcfg 1, Pcfg 2] := by
    funext k y
    fin_cases k <;> rfl
  refine ⟨t, htε, htA, ?_, ?_⟩
  · have h := hboth 0
    rw [hfun0] at h
    exact h
  · have h := hboth 1
    rw [hfun1] at h
    exact h


/-- **The `EndTripleReg` row of a chart-perturbed family of plane presentations**, from the family's
`Meet3Hyp` of the radial sweeps: the bridge `Work.Drive.endTripleReg_of_meet3Hyp_sweeps_unrestricted`
with the `foldBox`-invariance and the perturbed level bound as inputs.  (Factored out of the next
theorem so that its applications do not have to unify the large `Meet3Hyp` in the *expected* type.) -/
theorem endTripleReg_chartPert_family
    (Q₀ : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ₀ : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Q₀ k))
    (hQ₀inv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), Q₀ k (affRep e mm y) = Q₀ k y)
    (t : EuclideanSpace ℝ (Fin 12)) (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (hlev₀ : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      c 0 < levelOf (chartPert ((blk k) t) (Q₀ k y)))
    (hmeet : Meet3Hyp CappingSpace (sweepChartFam Q₀ (fun s p => chartPert s p) c t)) :
    EndTripleReg (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
        chartPert ((blk 0) t) (Q₀ 0 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 1) t) (Q₀ 1 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 2) t) (Q₀ 2 y))) := by
  have hΞc : ChartPert (fun _ : ℂ => Q₀ 0 0) 4 (fun s p => chartPert s p) :=
    isChartPert_chartPert (fun _ : ℂ => Q₀ 0 0)
  have hPhat : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk k) t) (Q₀ k y)) :=
    fun k => (contMDiff_apply_of_chartPert hΞc ((blk k) t)).comp (hQ₀ k)
  have hinv' : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        (fun y' : EuclideanSpace ℝ (Fin 2) => chartPert ((blk k) t) (Q₀ k y')) (affRep e mm y)
          = (fun y' : EuclideanSpace ℝ (Fin 2) => chartPert ((blk k) t) (Q₀ k y')) y :=
    fun e mm he k y => congrArg (chartPert ((blk k) t)) (hQ₀inv e mm he k y)
  have hmeet' : Meet3Hyp CappingSpace
      (fun k : Fin 3 => clampedSweep (c k) (fun r => 1 - r)
        (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk k) t) (Q₀ k y))) := by
    have hfun : (fun k : Fin 3 => clampedSweep (c k) (fun r => 1 - r)
          (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk k) t) (Q₀ k y)))
        = sweepChartFam Q₀ (fun s p => chartPert s p) c t := by
      funext k x
      rfl
    rw [hfun]
    exact hmeet
  exact endTripleReg_of_meet3Hyp_sweeps_unrestricted c (fun r => 1 - r)
    (fun k y => chartPert ((blk k) t) (Q₀ k y)) (by fun_prop) hPhat hc hc10 hc20
    (by norm_num) (by norm_num) (fun _ _ => by fun_prop)
    (fun _ _ => by intro a b hab; linarith [hab]) hinv' hlev₀ hmeet'

/-- **The two `EndTripleReg` rows `hend012` and `hendL012` of the design's triple at one parameter**
(the Sard side of `Work.Drive.ClassRowsAt`'s third and fourth conjunct,
`Submission/Work/Drive/classRows.lean`).  The two families of
`Work.Drive.exists_twoMeet3Hyp_design_mixed` are converted by
`Work.Drive.endTripleReg_chartPert_family`.  The first argument of the second row is the linear model
**transported** by `classEquiv (blk 0 t)` (see the module docstring for why no other form is available
from a sweep genericity). -/
theorem exists_classRows34_design {Q : ℂ → CappingSpace}
    (Φ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (Pcfg : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPcfg : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Pcfg k))
    (hPcfgseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → Pcfg k y = Pcfg k (seamInv2 y))
    (hPcfginv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), Pcfg k (affRep e mm y) = Pcfg k y)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hA0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t‖ < δ)
    (ε' : ℝ) (hε' : 0 < ε')
    (hlevel : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < ε' →
      ∀ (j : Fin 2) (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        c 0 < levelOf (chartPert ((blk k) t)
          ((![Pcfg, ![diskPlane (linPlaneChart Φ cl hcl), Pcfg 1, Pcfg 2]] :
            Fin 2 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) j k y))) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧ t ∈ A ∧
      EndTripleReg (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 0) t) (Pcfg 0 y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 1) t) (Pcfg 1 y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 2) t) (Pcfg 2 y))) ∧
      EndTripleReg
        (planeClassMap (diskPlane (linPlaneChart (Φ.trans (classEquiv ((blk 0) t))) cl hcl)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 1) t) (Pcfg 1 y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 2) t) (Pcfg 2 y))) := by
  classical
  have hmod : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (diskPlane (linPlaneChart Φ cl hcl)) :=
    contMDiff_diskPlane (linPlaneChart_contMDiff Φ cl hcl)
  obtain ⟨t, htε, htA, hmeet0, hmeet1⟩ :=
    exists_twoMeet3Hyp_design_mixed (Q := Q) Φ cl hcl
      (0 : UnitAddCircle) (0 : UnitAddCircle) Pcfg hPcfg hPcfgseam c hc hcdist A hAopen hA0 ε' hε'
  set Qm : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    ![diskPlane (linPlaneChart Φ cl hcl), Pcfg 1, Pcfg 2] with hQm
  have hrow0 := endTripleReg_chartPert_family Pcfg hPcfg hPcfginv t c hc hc10 hc20
    (fun k y => hlevel t htε 0 k y) hmeet0
  have hrow1 := endTripleReg_chartPert_family Qm
    (by
      intro k
      fin_cases k
      · exact hmod
      · exact hPcfg 1
      · exact hPcfg 2)
    (by
      intro e mm he k y
      fin_cases k
      · exact diskPlane_affRep he mm (linPlaneChart Φ cl hcl) y
      · exact hPcfginv e mm he 1 y
      · exact hPcfginv e mm he 2 y)
    t c hc hc10 hc20
    (by
      intro k y
      fin_cases k
      · exact hlevel t htε 1 0 y
      · exact hlevel t htε 1 1 y
      · exact hlevel t htε 1 2 y)
    hmeet1
  have hQm0 : Qm 0 = diskPlane (linPlaneChart Φ cl hcl) := rfl
  have hPM : planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 0) t) (Qm 0 y))
      = planeClassMap (diskPlane (linPlaneChart (Φ.trans (classEquiv ((blk 0) t))) cl hcl)) := by
    rw [hQm0]
    exact planeClassMap_chartPert_diskPlane_linPlaneChart Φ cl hcl ((blk 0) t)
  refine ⟨t, htε, htA, hrow0, ?_⟩
  rw [hPM] at hrow1
  exact hrow1



/-- **`EndTripleReg` is symmetric in its first two arguments** (a local copy, to avoid importing the
assembly module `hasClassLinearization_of_endData`). -/
theorem endTripleReg_swap12_local
    {F A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (h : EndTripleReg F A B) : EndTripleReg A F B := by
  intro y₀ y₁ y₂ h01 h02
  obtain ⟨hF, hA, hB, hI⟩ := h y₁ y₀ y₂ h01.symm (h01.symm.trans h02)
  refine ⟨hA, hF, hB, ?_⟩
  rw [inf_comm (mfderiv (𝓡 2) (𝓡 3) A y₀).range (mfderiv (𝓡 2) (𝓡 3) F y₁).range]
  exact hI

/-- **The three `EndTripleReg` rows of the design's triple that involve a linear model, at one
parameter**: `hend012` (the design's own triple), `hendL012` and `hendL10P2`.  The three families

* `Pcfg` (the design's three perturbed rotated charts),
* `![model₀, Pcfg 1, Pcfg 2]`,
* `![model₀, model₁, Pcfg 2]`

are made transverse at the *same* `t` by `Work.Drive.exists_meet3Hyp_sweepChartFam_family`
(`ι := Fin 3`), and each is converted by `Work.Drive.endTripleReg_chartPert_family`; for the third one
the first two arguments are exchanged by `endTripleReg_cyclic` + `endTripleReg_swap23`
(`EndTripleReg` is fully symmetric in its three arguments).  The first argument of a row with a linear
model is the model **transported** by the corresponding `classEquiv (blk · t)` (see the module
docstring). -/
theorem exists_classRows345_design {Q : ℂ → CappingSpace}
    (Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (Pcfg : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hPcfg : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Pcfg k))
    (hPcfgseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → Pcfg k y = Pcfg k (seamInv2 y))
    (hPcfginv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), Pcfg k (affRep e mm y) = Pcfg k y)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k')
    (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hA0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t‖ < δ)
    (ε' : ℝ) (hε' : 0 < ε')
    (hlevel : ∀ (t : EuclideanSpace ℝ (Fin 12)), ‖t‖ < ε' →
      ∀ (j : Fin 3) (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        c 0 < levelOf (chartPert ((blk k) t)
          ((![Pcfg, ![diskPlane (linPlaneChart Φ₀ cl hcl), Pcfg 1, Pcfg 2],
              ![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl),
                Pcfg 2]] : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) j k y))) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧ t ∈ A ∧
      EndTripleReg (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 0) t) (Pcfg 0 y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 1) t) (Pcfg 1 y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 2) t) (Pcfg 2 y))) ∧
      EndTripleReg
        (planeClassMap (diskPlane (linPlaneChart (Φ₀.trans (classEquiv ((blk 0) t))) cl hcl)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 1) t) (Pcfg 1 y)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 2) t) (Pcfg 2 y))) ∧
      EndTripleReg
        (planeClassMap (diskPlane (linPlaneChart (Φ₁.trans (classEquiv ((blk 1) t))) cl hcl)))
        (planeClassMap (diskPlane (linPlaneChart (Φ₀.trans (classEquiv ((blk 0) t))) cl hcl)))
        (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 2) t) (Pcfg 2 y))) := by
  classical
  have hmod : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (diskPlane (linPlaneChart Φ₀ cl hcl)) :=
    contMDiff_diskPlane (linPlaneChart_contMDiff Φ₀ cl hcl)
  have hmod' : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (diskPlane (linPlaneChart Φ₁ cl hcl)) :=
    contMDiff_diskPlane (linPlaneChart_contMDiff Φ₁ cl hcl)
  have hmodinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        diskPlane (linPlaneChart Φ₀ cl hcl) (affRep e mm y)
          = diskPlane (linPlaneChart Φ₀ cl hcl) y :=
    fun e mm he y => diskPlane_affRep he mm (linPlaneChart Φ₀ cl hcl) y
  have hmodinv' : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        diskPlane (linPlaneChart Φ₁ cl hcl) (affRep e mm y)
          = diskPlane (linPlaneChart Φ₁ cl hcl) y :=
    fun e mm he y => diskPlane_affRep he mm (linPlaneChart Φ₁ cl hcl) y
  obtain ⟨t, htε, htA, hmeets⟩ :=
    exists_meet3Hyp_sweepChartFam_family (ι := Fin 3) (Q := Q) (fun s p => chartPert s p)
      (isChartPert_chartPert Q) c hc hcdist
      (![Pcfg, ![diskPlane (linPlaneChart Φ₀ cl hcl), Pcfg 1, Pcfg 2],
          ![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl),
            Pcfg 2]] : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
      (by
        intro j k
        fin_cases j
        · exact hPcfg k
        · fin_cases k
          · exact hmod
          · exact hPcfg 1
          · exact hPcfg 2
        · fin_cases k
          · exact hmod
          · exact hmod'
          · exact hPcfg 2)
      (by
        intro j k y hy
        fin_cases j
        · exact hPcfgseam k y hy
        · fin_cases k
          · exact (diskPlane_seamInv2 (Q := linPlaneChart Φ₀ cl hcl)
              (fun z hz => linPlaneChart_neg Φ₀ cl hcl hz) hy).symm
          · exact hPcfgseam 1 y hy
          · exact hPcfgseam 2 y hy
        · fin_cases k
          · exact (diskPlane_seamInv2 (Q := linPlaneChart Φ₀ cl hcl)
              (fun z hz => linPlaneChart_neg Φ₀ cl hcl hz) hy).symm
          · exact (diskPlane_seamInv2 (Q := linPlaneChart Φ₁ cl hcl)
              (fun z hz => linPlaneChart_neg Φ₁ cl hcl hz) hy).symm
          · exact hPcfgseam 2 y hy)
      A hAopen hA0 ε' hε'
  -- the three families
  have hFam0 : Pcfg = (![Pcfg, ![diskPlane (linPlaneChart Φ₀ cl hcl), Pcfg 1, Pcfg 2],
      ![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl),
        Pcfg 2]] : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 0 := rfl
  have hFam1 : (![diskPlane (linPlaneChart Φ₀ cl hcl), Pcfg 1, Pcfg 2] :
      Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
      = (![Pcfg, ![diskPlane (linPlaneChart Φ₀ cl hcl), Pcfg 1, Pcfg 2],
      ![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl),
        Pcfg 2]] : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 1 := rfl
  have hFam2 : (![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl),
        Pcfg 2] : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
      = (![Pcfg, ![diskPlane (linPlaneChart Φ₀ cl hcl), Pcfg 1, Pcfg 2],
      ![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl),
        Pcfg 2]] : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 2 := rfl
  have hrow0 := endTripleReg_chartPert_family Pcfg hPcfg hPcfginv t c hc hc10 hc20
    (fun k y => hlevel t htε 0 k y) (hFam0 ▸ hmeets 0)
  have hrow1 := endTripleReg_chartPert_family
    (![diskPlane (linPlaneChart Φ₀ cl hcl), Pcfg 1, Pcfg 2] :
      Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (by
      intro k
      fin_cases k
      · exact hmod
      · exact hPcfg 1
      · exact hPcfg 2)
    (by
      intro e mm he k y
      fin_cases k
      · exact hmodinv e mm he y
      · exact hPcfginv e mm he 1 y
      · exact hPcfginv e mm he 2 y)
    t c hc hc10 hc20
    (fun k y => hFam1 ▸ hlevel t htε 1 k y) (hFam1 ▸ hmeets 1)
  have hrow2 := endTripleReg_chartPert_family
    (![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl), Pcfg 2] :
      Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (by
      intro k
      fin_cases k
      · exact hmod
      · exact hmod'
      · exact hPcfg 2)
    (by
      intro e mm he k y
      fin_cases k
      · exact hmodinv e mm he y
      · exact hmodinv' e mm he y
      · exact hPcfginv e mm he 2 y)
    t c hc hc10 hc20
    (fun k y => hFam2 ▸ hlevel t htε 2 k y) (hFam2 ▸ hmeets 2)
  -- the transport of the two linear arguments
  have hPM₀ : planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 0) t)
        (diskPlane (linPlaneChart Φ₀ cl hcl) y))
      = planeClassMap (diskPlane (linPlaneChart (Φ₀.trans (classEquiv ((blk 0) t))) cl hcl)) :=
    planeClassMap_chartPert_diskPlane_linPlaneChart Φ₀ cl hcl ((blk 0) t)
  have hPM₁ : planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert ((blk 1) t)
        (diskPlane (linPlaneChart Φ₁ cl hcl) y))
      = planeClassMap (diskPlane (linPlaneChart (Φ₁.trans (classEquiv ((blk 1) t))) cl hcl)) :=
    planeClassMap_chartPert_diskPlane_linPlaneChart Φ₁ cl hcl ((blk 1) t)
  have hcomp1 : (![diskPlane (linPlaneChart Φ₀ cl hcl), Pcfg 1, Pcfg 2] :
      Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 0
      = diskPlane (linPlaneChart Φ₀ cl hcl) := by funext y; rfl
  have hcomp2a : (![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl),
      Pcfg 2] : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 0
      = diskPlane (linPlaneChart Φ₀ cl hcl) := by funext y; rfl
  have hcomp2b : (![diskPlane (linPlaneChart Φ₀ cl hcl), diskPlane (linPlaneChart Φ₁ cl hcl),
      Pcfg 2] : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) 1
      = diskPlane (linPlaneChart Φ₁ cl hcl) := by funext y; rfl
  refine ⟨t, htε, htA, hrow0, ?_, ?_⟩
  · rw [hcomp1] at hrow1
    rw [hPM₀] at hrow1
    exact hrow1
  · rw [hcomp2a, hcomp2b] at hrow2
    rw [hPM₀, hPM₁] at hrow2
    exact endTripleReg_swap12_local hrow2

end

end Work.Drive
