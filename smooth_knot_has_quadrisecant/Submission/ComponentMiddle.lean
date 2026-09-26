import Mathlib
import ChallengeDeps
import Submission.ComponentChart

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S252 — the continuous unique-middle selection on a component (TWICE-branch
item (ii), VERIFIED, sorry-free)

The TWICE family-production endpoint (`no_twiceWinding_data`, S248 in
ComponentIntervalSide.lean) is pure assembly *given* three geometric data
items: (i) the component circle chart `χ : Circle ≃ₜ TrisecantComponent r
c₀` (fleet L65 + `trisecantComponent_compactSide`, S249); (ii) a
continuous unique-middle selection `μ` on the component with
`μ z ∈ MiddlePointsOnClass r (z : OSub r)`; (iii) the TWICE measurement
giving the full-period advancing real lift `G`.  This module delivers item
(ii) for **every** connected component (interval or circular):

1. **`componentMiddle`** (VERIFIED) — the canonical strict middle of the
   class of a component point: `componentMiddle c₀ z =
   classMiddle r ((z : OSub r) : OpenMobius) (z : OSub r).2` (the
   canonical choice of MiddleConvergence);
2. **`componentMiddle_mem_middleSet`** (VERIFIED) — membership
   `componentMiddle c₀ z ∈ MiddlePointsOnClass r ((z : OSub r) :
   OpenMobius)` (unconditional: `classMiddle_mem_middleSet`);
3. **`seqContinuous_componentMiddle`** (VERIFIED) — *sequential*
   continuity of `componentMiddle`: for a sequence of component points
   converging to `p`, the canonical middles converge to the canonical
   middle of `p`'s class.  Proof: the class sequence converges in
   `OpenMobius` (continuity of the class projection); take a strict
   representative `z₀` of the limit class (`strictRep_of_trisecant`);
   the strict-middle convergence
   `middle_tendsto_of_strictBase` (OpenMapAssembly, instancing
   `MiddleConvergence.middle_tendsto_of_class_tendsto` with the
   fundamental-domain transverse representatives supplied by
   `TorusGeneralPositionTransverse`) gives convergence to the strict
   middle `(z₀ : KnotParamTriple).2.2`; the canonical middle of the
   class equals that strict middle under `QuadrisecantFree`
   (`strict_middle_unique_on_class` — both are strict middles of the
   class of `chordOfZeroSet h z₀`);
4. **`componentMiddle_continuous`** (VERIFIED) — the *topological*
   continuity upgrade: the component space
   `TrisecantComponent r c₀` (a subspace of the second-countable band)
   is a `SequentialSpace`, so `SeqContinuous.continuous` turns (3) into
   `Continuous (componentMiddle c₀)`;
5. **`exists_continuous_unique_middle_on_component`** (VERIFIED) — the
   packaged item (ii): every component carries a continuous canonical
   middle selection into `MiddlePointsOnClass`.

Together with (i) (S249) the TWICE branch reduces to item (iii), the
measurement of the winding (`G` advancing a full period per circuit), and
the ONCE branch has its half-period-advance avatar; both are recorded as
Layer-C brick (c).
-/

/-- **The canonical strict middle of a component point (S252)**: the
canonical strict middle (`classMiddle`, MiddleConvergence) of the secant
class `(z : OSub r)` underlying the component point `z : TrisecantComponent
r c₀`.  Under `QuadrisecantFree` it is the *unique* middle of the class,
so it is a genuine function of the component parameter — the middle
selection that the once/twice winding analysis keeps continuous. -/
noncomputable def componentMiddle {r : ℝ → Space} (c₀ : OSub r)
    (z : TrisecantComponent r c₀) : AddCircle period :=
  classMiddle r ((z : OSub r) : OpenMobius) (z : OSub r).2

/-- **The canonical middle of a component point is a middle point of its
class (S252)**: `componentMiddle c₀ z ∈ MiddlePointsOnClass r (z : OSub r)`
— the membership content of the middle selection, from
`classMiddle_mem_middleSet`. -/
lemma componentMiddle_mem_middleSet {r : ℝ → Space} (c₀ : OSub r)
    (z : TrisecantComponent r c₀) :
    componentMiddle c₀ z ∈ MiddlePointsOnClass r ((z : OSub r) : OpenMobius) := by
  dsimp [componentMiddle]
  exact classMiddle_mem_middleSet r ((z : OSub r) : OpenMobius) (z : OSub r).2

/-- **Sequential continuity of the component middle (S252)**: for a
sequence `xₙ` of points of the component `TrisecantComponent r c₀`
converging to `p`, the canonical middles of the underlying classes
converge to the canonical middle of the class of `p`.  Proof: strict-base
middle convergence (`middle_tendsto_of_strictBase`) at a strict
representative `z₀` of the limit class, whose strict middle equals the
canonical middle of the class by `strict_middle_unique_on_class` under
`QuadrisecantFree`. -/
lemma seqContinuous_componentMiddle {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) : SeqContinuous (componentMiddle (r := r) c₀) := by
  classical
  intro x p hx
  -- the class sequence over the O-subset and its membership
  let y : ℕ → OpenMobius := fun n => (((x n : TrisecantComponent r c₀) : OSub r) : OpenMobius)
  have hyO : ∀ n : ℕ, y n ∈ trisecantSet r := fun n =>
    (((x n : TrisecantComponent r c₀) : OSub r).2)
  -- the class projection is continuous, so yₙ → class of p
  have hclcont : Continuous (fun z : TrisecantComponent r c₀ =>
      (((z : TrisecantComponent r c₀) : OSub r) : OpenMobius)) := by
    exact (continuous_subtype_val : Continuous (fun w : OSub r => (w : OpenMobius))).comp
      (continuous_subtype_val : Continuous (fun z : TrisecantComponent r c₀ => (z : OSub r)))
  have hy : Tendsto y atTop
      (𝓝 ((((p : TrisecantComponent r c₀) : OSub r) : OpenMobius))) := by
    dsimp [y]
    exact (hclcont.tendsto p).comp hx
  -- a strict representative of the limit class
  have hpc : (((p : TrisecantComponent r c₀) : OSub r) : OpenMobius) ∈ trisecantSet r :=
    (p : OSub r).2
  rcases strictRep_of_trisecant h hpc with ⟨z₀, hz₀str, hz₀cls⟩
  have hz₀clsM : mobiusCover (chordOfZeroSet h z₀) =
      (((p : TrisecantComponent r c₀) : OSub r) : OpenMobius) := by
    exact ((zeroChordClass_eq_mobiusCover_chordOfZeroSet h z₀).symm.trans hz₀cls)
  have hyZ : Tendsto y atTop (𝓝 (zeroChordClass h z₀)) := by
    simpa [hz₀cls] using hy
  -- strict-middle convergence at the strict base
  have hmid := middle_tendsto_of_strictBase h hqf hz₀str hgp hyO hyZ
  -- the strict middle of the base equals the canonical middle of the class
  have hlim : ((z₀ : KnotParamTriple).2.2) =
      classMiddle r (((p : TrisecantComponent r c₀) : OSub r) : OpenMobius) (p : OSub r).2 := by
    exact strict_middle_unique_on_class h hqf (p := chordOfZeroSet h z₀)
      (q := chordOfZeroSet h z₀) rfl
      (strict_middle_of_strictZero h hz₀str)
      (classMiddle_middle_on_rep
        (((p : TrisecantComponent r c₀) : OSub r) : OpenMobius) (p : OSub r).2
        (chordOfZeroSet h z₀) hz₀clsM)
  -- rewrite the limit value to the canonical middle of p's class
  have hmid' : Tendsto (fun n : ℕ => classMiddle r (y n) (hyO n)) atTop
      (𝓝 (classMiddle r (((p : TrisecantComponent r c₀) : OSub r) : OpenMobius) (p : OSub r).2)) := by
    simpa [hlim] using hmid
  -- match the middle function with componentMiddle
  change Tendsto (fun n : ℕ => componentMiddle c₀ (x n)) atTop
      (𝓝 (componentMiddle c₀ p))
  dsimp [componentMiddle, y, hyO]
  exact hmid'

/-- **Continuity of the component middle (S252)**: under a smooth knot in
transverse torus general position with no quadrisecants, the canonical
middle selection `componentMiddle c₀` is continuous on every connected
component `TrisecantComponent r c₀` of the trisecant set.  The component
(a subspace of the second-countable band) is a `SequentialSpace`, so the
sequential continuity of `seqContinuous_componentMiddle` upgrades to
topological continuity (`SeqContinuous.continuous`). -/
theorem componentMiddle_continuous {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) : Continuous (componentMiddle (r := r) c₀) := by
  exact SeqContinuous.continuous (seqContinuous_componentMiddle h hqf hgp c₀)

/-- **The continuous unique-middle selection on a component (S252,
packaged item (ii) of the TWICE family production)**: every connected
component `TrisecantComponent r c₀` of the trisecant set carries a
continuous map `μ` into the parameter circle whose value at `z` is a
middle point of the underlying secant class `(z : OSub r)`.  This is the
`μ`/`hμc`/`hμ` datum consumed by `no_twiceWinding_data` (S248) once the
component is circular. -/
theorem exists_continuous_unique_middle_on_component {r : ℝ → Space}
    (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    ∃ μ : TrisecantComponent r c₀ → AddCircle period,
      Continuous μ ∧
        ∀ z : TrisecantComponent r c₀,
          μ z ∈ MiddlePointsOnClass r ((z : OSub r) : OpenMobius) := by
  refine ⟨componentMiddle c₀, ?_, ?_⟩
  · exact componentMiddle_continuous h hqf hgp c₀
  · intro z
    exact componentMiddle_mem_middleSet c₀ z

end LeanEval.KnotTheory.Quadrisecant
