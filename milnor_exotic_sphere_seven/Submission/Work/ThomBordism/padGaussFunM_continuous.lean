import Mathlib
import Submission.Work.ThomBordism.padGaussFunM

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the padded `σ`-corrected Gauss map (arbitrary padding)

`Work.ThomBordism.padGaussFunM` is the oriented Gauss map `V → G̃r_k(ℝ^{k+m})` of the normal data of
an embedding `V ↪ ℝ^{8+k}`, padding the `σ`-corrected normal frame into the ambient space
`ℝ^{k+m}` (`8 ≤ m`).  This file proves that it is continuous, the `m`-general form of
`Work.ThomBordism.Grassmann.continuous_padGaussFun` (`_gtd/P4.lean`, the case `m = 10`).

The structure of the argument is the same as in `_gtd/P3` + `_gtd/P4`:

* the corrected frame of a chart is continuous on the chart (`continuousOn_padGFrameM`);
* two charts give the same point of the Grassmannian (`padGFrameM_soAct`), so that the *chartwise*
  Gauss map `ogMk k m (padGaussStiefelM …)` is a continuous local expression for the global Gauss
  map (`padGaussFunM_eq_of_mem`), which is enough because the chart sets are open and cover `V`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism.Grassmann

open Work.PTGeometric
open Work.ThomBordism.PontryaginThom Work.ThomBordism.Gauss Work.ThomBordism.OrthFrame

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- Two charts give the same padded frame up to the `SO(k)`-action. -/
theorem padGFrameM_soAct (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (i j : CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    padGFrameM E ND m hm i x
      = soActFun (gauge E ND j x * frameChange E ND i j x * gauge E ND i x)
          (padGFrameM E ND m hm j x) := by
  funext a
  change padIsomM k m hm (gframe E ND i x a)
    = ∑ b, (gauge E ND j x * frameChange E ND i j x * gauge E ND i x) b a
      • padIsomM k m hm (gframe E ND j x b)
  have h := congrFun (gframe_expand E ND i j hx) a
  rw [h]
  change padIsomM k m hm (∑ b, (gauge E ND j x * frameChange E ND i j x
        * gauge E ND i x) b a • gframe E ND j x b)
    = ∑ b, (gauge E ND j x * frameChange E ND i j x * gauge E ND i x) b a
      • padIsomM k m hm (gframe E ND j x b)
  simp only [map_sum, map_smul]

/-- **The chartwise form of the padded Gauss map**: on the base set of a chart, the padded Gauss map
is the `ogMk`-image of the padded corrected frame of that chart. -/
theorem padGaussFunM_eq_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    padGaussFunM E ND m hm x
      = ogMk k m ⟨padGFrameM E ND m hm i x, padGFrameM_orthonormal E ND m hm i hx⟩ := by
  rw [padGaussFunM_eq]
  refine Quotient.sound ⟨⟨gauge E ND (ND.D.indexAt x) x
      * frameChange E ND i (ND.D.indexAt x) x * gauge E ND i x,
      isSO_gchange E ND i (ND.D.indexAt x) ⟨hx, ND.D.mem_baseSet_at x⟩⟩, ?_⟩
  apply Subtype.ext
  exact padGFrameM_soAct E ND m hm i (ND.D.indexAt x) ⟨hx, ND.D.mem_baseSet_at x⟩

/-- The padded `σ`-corrected normal frame is continuous on the base set of its chart. -/
theorem continuousOn_padGFrameM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (i : CoverIdx V k) :
    ContinuousOn (fun x : V.pt => padGFrameM E ND m hm i x) (ND.D.baseSet i) := by
  rw [continuousOn_pi]
  intro a
  have hfun : (fun x : V.pt => padGFrameM E ND m hm i x a)
      = fun x => padEuc k m hm
          ((if (a : ℕ) = 0 then sigma E ND i x else 1) • Tubular.orthFrame E ND i x a) := by
    funext x
    show padIsomM k m hm (gframe E ND i x a)
      = padEuc k m hm
          ((if (a : ℕ) = 0 then sigma E ND i x else 1) • Tubular.orthFrame E ND i x a)
    rw [gframe_apply, map_smul, padIsomM_apply, map_smul]
  rw [hfun]
  refine (padEuc k m hm).continuous.comp_continuousOn ?_
  refine ContinuousOn.smul (f := fun x : V.pt => (if (a : ℕ) = 0 then sigma E ND i x else 1))
    (g := fun x : V.pt => Tubular.orthFrame E ND i x a) ?_
    (Tubular.continuousOn_orthFrame E ND i a)
  by_cases ha : (a : ℕ) = 0
  · rw [show (fun x : V.pt => (if (a : ℕ) = 0 then sigma E ND i x else 1))
        = fun x => sigma E ND i x from funext fun x => by rw [if_pos ha]]
    exact continuousOn_sigma E ND i
  · rw [show (fun x : V.pt => (if (a : ℕ) = 0 then sigma E ND i x else 1))
        = fun _ => (1 : ℝ) from funext fun x => by rw [if_neg ha]]
    exact continuousOn_const

/-- The candidate point of the Stiefel manifold defined by the chart `i` (junk off the chart). -/
def padGaussStiefelM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (i : CoverIdx V k) (x : V.pt) : Stiefel k m := by
  classical
  exact if h : x ∈ ND.D.baseSet i then
    ⟨padGFrameM E ND m hm i x, padGFrameM_orthonormal E ND m hm i h⟩
    else Classical.choice (nonempty_stiefel k m)

theorem padGaussStiefelM_of_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (i : CoverIdx V k) {x : V.pt} (h : x ∈ ND.D.baseSet i) :
    padGaussStiefelM E ND m hm i x
      = ⟨padGFrameM E ND m hm i x, padGFrameM_orthonormal E ND m hm i h⟩ := by
  classical
  rw [padGaussStiefelM]
  exact dif_pos h

theorem continuousOn_padGaussStiefelM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) (i : CoverIdx V k) :
    ContinuousOn (padGaussStiefelM E ND m hm i) (ND.D.baseSet i) := by
  refine Tubular.continuousOn_subtype_of_eqOn (g := padGaussStiefelM E ND m hm i)
    (f := fun x : V.pt => padGFrameM E ND m hm i x) (continuousOn_padGFrameM E ND m hm i) ?_
  intro x hx
  rw [padGaussStiefelM_of_mem E ND m hm i hx]

end

end Work.ThomBordism.Grassmann

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann

noncomputable section

/-- **The padded `σ`-corrected Gauss map is continuous in the point** (arbitrary padding `m ≥ 8`):
the `m`-general form of `Work.ThomBordism.Grassmann.continuous_padGaussFun` (`_gtd/P4.lean`, case
`m = 10`), proved from the chartwise continuity of `padGFrameM` and the continuity of `ogMk` on the
Stiefel bundle.  Port `padGaussStiefel`/`padGaussStiefel_eq` (`_gtd/P3.lean`) to arbitrary `m` along
the way if needed.  Needed by the canonical-lift repair of
`Submission/Work/ThomBordism/NOTE_SIGMA_GAUSS_SESSION34.md` §3. -/
theorem padGaussFunM_continuous {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (m : ℕ) (hm : 8 ≤ m) :
    Continuous (Work.ThomBordism.padGaussFunM E ND m hm) := by
  rw [continuous_iff_continuousAt]
  intro x
  set i := ND.D.indexAt x with hi
  have hmem : x ∈ ND.D.baseSet i := ND.D.mem_baseSet_at x
  have hopen : IsOpen (ND.D.baseSet i) := ND.D.isOpen_baseSet i
  have hloc : ContinuousOn (fun y => ogMk k m (padGaussStiefelM E ND m hm i y))
      (ND.D.baseSet i) :=
    (ogMk k m).continuous.comp_continuousOn (continuousOn_padGaussStiefelM E ND m hm i)
  refine (hloc.continuousAt (hopen.mem_nhds hmem)).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with y hy
  rw [padGaussStiefelM_of_mem E ND m hm i hy]
  exact (padGaussFunM_eq_of_mem E ND m hm i hy).symm

end

end Work.ThomBordism
