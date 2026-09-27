import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLComp.U_generated_by_Uball

namespace Work.EKLC6Route

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract Work.EKLC6Core

/-- `VtSet t` is closed: it is the finite intersection of the closed conditions "the entry `(i,j)`
vanishes", over the pairs with `t i < t j`. -/
lemma isClosed_VtSet (t : Fin 3 → ℝ) : IsClosed (VtSet t) := by
  have h : VtSet t = ⋂ (i : Fin 3), ⋂ (j : Fin 3), ⋂ (_ : t i < t j),
      {g : SL3 | (g : Matrix (Fin 3) (Fin 3) ℝ) i j = 0} := by
    ext g
    simp only [VtSet, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (by fun_prop) continuous_const

/-- The chart set `{x | uc x ∈ Uball (Uminus t) a ∧ θ x ∈ VtSet t ∩ V b ∧ (uc x * θ x) • z0 = x}` is
Borel.  Suggested ingredients: `Work.EKLComp.X3Background` gives `T2Space X3` and
`SecondCountableTopology X3`, whence `MeasurableEq X3` via `isClosed_diagonal.measurableSet`;
`Work.EKLC6Core.uminus_isHoro t` gives `IsClosed (Uminus t : Set SL3)`;
`Work.EKLContract.Lemmas.SL3Topology.2` gives `SecondCountableTopology SL3` (needed for
`Measurable (fun x => (uc x * θ x) • z0)` by `fun_prop`). -/
theorem chartSet_measurable {t : Fin 3 → ℝ} {z0 : Work.EKLContract.X3}
    {uc θ : Work.EKLContract.X3 → Work.EKLContract.SL3}
    (huc : Measurable uc) (hθ : Measurable θ) (a b : ℝ) :
    MeasurableSet (Work.EKLC6Route.chartSet t z0 uc θ a b) := by
  -- The `uc`-condition: `Uball (Uminus t) a` is Borel.
  have hUball : MeasurableSet (Work.EKLComp.Uball (Uminus t) a) := by
    rw [Work.EKLComp.Uball_eq_inter]
    exact ((uminus_isHoro t).1.1.measurableSet).inter
      (Work.EKLComp.isOpen_UballOpen a).measurableSet
  -- The `θ`-condition: `VtSet t ∩ V b` is Borel (`V b = UballOpen b` definitionally).
  have hCB : MeasurableSet (VtSet t ∩ V b) :=
    (isClosed_VtSet t).measurableSet.inter (Work.EKLComp.isOpen_UballOpen b).measurableSet
  -- The graph condition: `x ↦ (uc x * θ x) • z0` is measurable and `X₃` is Hausdorff.
  have hEc : MeasurableSet {x : X3 | (uc x * θ x) • z0 = x} := by
    have hb : Measurable (fun x : X3 => θ x • z0) := by
      have hpair : Measurable (fun x : X3 => (θ x, z0)) := Measurable.prod hθ measurable_const
      exact continuous_smul.measurable.comp hpair
    have hf : Measurable (fun x : X3 => (uc x * θ x) • z0) := by
      have hpair : Measurable (fun x : X3 => (uc x, θ x • z0)) := Measurable.prod huc hb
      have hcomp : Measurable (fun x : X3 => uc x • (θ x • z0)) :=
        continuous_smul.measurable.comp hpair
      simpa only [mul_smul] using hcomp
    have hdiag : MeasurableSet {p : X3 × X3 | p.1 = p.2} := isClosed_diagonal.measurableSet
    have hg : Measurable (fun x : X3 => ((uc x * θ x) • z0, x)) :=
      Measurable.prod hf measurable_id
    exact hg hdiag
  have hE : chartSet t z0 uc θ a b =
      {x : X3 | uc x ∈ Work.EKLComp.Uball (Uminus t) a} ∩
      {x : X3 | θ x ∈ VtSet t ∩ V b} ∩
      {x : X3 | (uc x * θ x) • z0 = x} := by
    ext x
    simp only [chartSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hE]
  exact ((huc hUball).inter (hθ hCB)).inter hEc

end Work.EKLC6Route
