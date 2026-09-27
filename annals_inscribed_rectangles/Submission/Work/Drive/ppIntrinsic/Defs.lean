import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Bdry
import Submission.Work.Drive.ppIntrinsic.FlowGen

/-!
# The chart-free pair-equation set `Zpp` of the intrinsic pair meet

`Work.Drive.ppMeet E E' V W` is the set of points `x = (s,u,y,z)` of the `9`-box at which the two
pair equations `E s u = V y` and `E' s u = W z` hold.  The *chart-free* equation set
`Work.Drive.Zpp E E' V W` is the same set *without* the box condition:

`Zpp E E' V W = {x | E (ftS x) (ftU x) = V (ftY x) ∧ E' (ftS x) (ftU x) = W (ftZ x)}`.

This is the closed set which carries the local graph structure (in a chart at the common value), and
whose intersection with the unit box is `ppMeet`:

`ppMeet E E' V W = Zpp E E' V W ∩ unitBox 8`.

The intrinsic mod-2 parity argument localises on `Zpp` (the closed set `Z` of the generic lemmas
`Work.Drive.ppIntrinsic.flowGen_mapsTo_of_localGraph` and
`Work.Drive.ppIntrinsic.finite_and_even_ncard_bdry_of_localGraph`), with the compact set
`K = ppMeet E E' V W = Zpp ∩ unitBox 8`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The chart-free pair-equation set**: the points of `ℝ⁹` at which the two pair equations
`E s u = V y` and `E' s u = W z` hold.  It is closed (for continuous chains) and its intersection with
the unit box is the pair meet set `Work.Drive.ppMeet`. -/
def Zpp (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M) :
    Set (EuclideanSpace ℝ (Fin 9)) :=
  {x | E (ftS x) (ftU x) = V (ftY x) ∧ E' (ftS x) (ftU x) = W (ftZ x)}

@[simp] lemma mem_Zpp {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {x : EuclideanSpace ℝ (Fin 9)} :
    x ∈ Zpp E E' V W ↔ E (ftS x) (ftU x) = V (ftY x) ∧ E' (ftS x) (ftU x) = W (ftZ x) :=
  Iff.rfl

/-- The pair meet set is the part of the chart-free equation set inside the unit box. -/
theorem ppMeet_eq_Zpp_inter (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) :
    ppMeet E E' V W = Zpp E E' V W ∩ Submission.Drive.unitBox 8 := by
  ext x
  simp only [Zpp, ppMeet, Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

/-- The chart-free equation set is closed for continuous chains. -/
theorem isClosed_Zpp (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (hE : Continuous (Function.uncurry E))
    (hE' : Continuous (Function.uncurry E')) (hV : Continuous V) (hW : Continuous W) :
    IsClosed (Zpp E E' V W) := by
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 9) => E (ftS x) (ftU x) :=
    hE.comp (show Continuous fun x : EuclideanSpace ℝ (Fin 9) => (ftS x, ftU x) from by
      refine Continuous.prodMk ?_ ?_
      · show Continuous fun x : EuclideanSpace ℝ (Fin 9) => x 0
        fun_prop
      · show Continuous fun x : EuclideanSpace ℝ (Fin 9) =>
          WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩)
        fun_prop)
  have h2 : Continuous fun x : EuclideanSpace ℝ (Fin 9) => V (ftY x) :=
    hV.comp (show Continuous fun x : EuclideanSpace ℝ (Fin 9) => ftY x from by
      show Continuous fun x : EuclideanSpace ℝ (Fin 9) =>
        WithLp.toLp 2 (fun i : Fin 3 => x ⟨3 + i.val, by omega⟩)
      fun_prop)
  have h3 : Continuous fun x : EuclideanSpace ℝ (Fin 9) => E' (ftS x) (ftU x) :=
    hE'.comp (show Continuous fun x : EuclideanSpace ℝ (Fin 9) => (ftS x, ftU x) from by
      refine Continuous.prodMk ?_ ?_
      · show Continuous fun x : EuclideanSpace ℝ (Fin 9) => x 0
        fun_prop
      · show Continuous fun x : EuclideanSpace ℝ (Fin 9) =>
          WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩)
        fun_prop)
  have h4 : Continuous fun x : EuclideanSpace ℝ (Fin 9) => W (ftZ x) :=
    hW.comp (show Continuous fun x : EuclideanSpace ℝ (Fin 9) => ftZ x from by
      show Continuous fun x : EuclideanSpace ℝ (Fin 9) =>
        WithLp.toLp 2 (fun i : Fin 3 => x ⟨6 + i.val, by omega⟩)
      fun_prop)
  have h : Zpp E E' V W =
      ({x | E (ftS x) (ftU x) = V (ftY x)} ∩ {x | E' (ftS x) (ftU x) = W (ftZ x)}) := by
    ext x; simp [Zpp]
  rw [h]
  exact (isClosed_eq h1 h2).inter (isClosed_eq h3 h4)

end

end Work.Drive
