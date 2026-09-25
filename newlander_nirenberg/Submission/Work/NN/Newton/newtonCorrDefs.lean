/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliary definitions for the Newton correction

`Work.NN.Newton.newtonCorrection` produces the linearised Newton correction `v_l` of the
KAM/Newton iteration of `Submission/Work/NN/Newton/DESIGN.md`.  The construction is

  `F^{(p)}_q := Lcoef A z_p q`,   `η^{(p)} := ∂̄₀ F^{(p)}`,   `ψ^{(p)} := flatTwoThin η^{(p)}`,
  `G^{(p)} := F^{(p)} - ψ^{(p)}`,  `v_p := flatOneThin G^{(p)}`.

This file records the two objects `coordDatum A p = F^{(p)}` and `coordDefect A p = η^{(p)}`,
so that the auxiliary lemmas about them can be stated without unfolding `Lcoef` and `ddbar`.
-/
import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.Proj
import Submission.Work.NN.Newton.DefectDefs

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

/-- **The flat `∂̄`-defect of the coordinate datum**:
`η^{(p)}_{jk} = Δ̄_j F^{(p)}_k - Δ̄_k F^{(p)}_j`, the `(0,2)`-array `ddbar Jstd (coordDatum A p)`. -/
def coordDefect {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (p : Fin n) : Fin n → Fin n → Work.NN.Core.Cn n → ℂ :=
  fun j k z => Work.NN.Final.ddbar (Work.NN.Core.JstdCn n) (coordDatum A p) j k z

@[simp] lemma coordDefect_apply {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (p j k : Fin n)
    (z : Work.NN.Core.Cn n) :
    coordDefect A p j k z
      = Work.CR.Flat.dbarCoord j (coordDatum A p k) z
        - Work.CR.Flat.dbarCoord k (coordDatum A p j) z := by
  simp [coordDefect, Work.NN.Final.ddbar_std]



section Basic

variable {n : ℕ}

/-- The coordinate datum is `(i/2)·(A z e_q)_p`, the `p`-th coordinate of the perturbation array
in the direction `e_q`. -/
lemma coordDatum_eq_fun (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (p q : Fin n) :
    coordDatum A p q = fun z => (Complex.I / 2) * (A z (Pi.single q (1 : ℂ))) p := by
  funext z
  simp only [coordDatum, Work.NN.Core.Lcoef]
  have h : fderiv ℝ (fun y : Work.NN.Core.Cn n => y p) z = ContinuousLinearMap.proj p := by
    have h' : (fun y : Work.NN.Core.Cn n => y p)
        = (ContinuousLinearMap.proj p : Work.NN.Core.Cn n →L[ℝ] ℂ) := rfl
    rw [h', ContinuousLinearMap.fderiv]
  rw [h]
  simp

/-- The coordinate datum is smooth whenever `A` is. -/
lemma coordDatum_contDiffOn {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {r : ℝ} (hA : ∀ m : ℕ, ContDiffOn ℝ m A
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) (p q : Fin n) (m : ℕ) :
    ContDiffOn ℝ m (coordDatum A p q)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := by
  rw [coordDatum_eq_fun]
  have h1 : ContDiffOn ℝ m (fun z => A z (Pi.single q (1 : ℂ)))
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := by
    simpa using (hA m).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ m (fun z => (A z (Pi.single q (1 : ℂ))) p)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      ContDiff.comp_contDiffOn ((ContinuousLinearMap.proj p).contDiff) h1
  exact (contDiffOn_const (c := Complex.I / 2)).mul h2

/-- Pointwise form of the smoothness of the coordinate datum. -/
lemma coordDatum_contDiffAt {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {r : ℝ} (hA : ∀ m : ℕ, ContDiffOn ℝ m A
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) (p q : Fin n)
    {z : Work.NN.Core.Cn n} (hz : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
    (m : ℕ) : ContDiffAt ℝ m (coordDatum A p q) z :=
  (coordDatum_contDiffOn hA p q m).contDiffAt
    ((Work.CR.Flat.isOpen_polydisc 0 (fun _ => r)).mem_nhds hz)

/-- The flat `∂̄`-defect of the coordinate datum is smooth whenever `A` is. -/
lemma coordDefect_contDiffOn {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {r : ℝ} (hA : ∀ m : ℕ, ContDiffOn ℝ m A
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) (p j k : Fin n) (m : ℕ) :
    ContDiffOn ℝ m (coordDefect A p j k)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := by
  have hinf : ∀ q : Fin n, ContDiffOn ℝ (∞ : ℕ∞ω) (coordDatum A p q)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) :=
    fun q => contDiffOn_infty.mpr (coordDatum_contDiffOn (r := r) hA p q)
  have h1 : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun z => Work.CR.Flat.dbarCoord j (coordDatum A p k) z)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) :=
    Work.NN.Final.contDiffOn_dbarCoord
      (Work.CR.Flat.isOpen_polydisc 0 (fun _ => r)) (hinf k) j
  have h2 : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun z => Work.CR.Flat.dbarCoord k (coordDatum A p j) z)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) :=
    Work.NN.Final.contDiffOn_dbarCoord
      (Work.CR.Flat.isOpen_polydisc 0 (fun _ => r)) (hinf j) k
  have h := h1.sub h2
  refine ((contDiffOn_infty.mp h) m).congr (fun z _ => ?_)
  simp [coordDefect, Work.NN.Final.ddbar_std]

/-- The defect is antisymmetric. -/
lemma coordDefect_antisymm
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (p j k : Fin n)
    (z : Work.NN.Core.Cn n) :
    coordDefect A p j k z = - coordDefect A p k j z := by
  simp only [coordDefect, Work.NN.Final.ddbar, Work.NN.Final.dbarOne_std]
  ring

end Basic

end Work.NN.Newton
