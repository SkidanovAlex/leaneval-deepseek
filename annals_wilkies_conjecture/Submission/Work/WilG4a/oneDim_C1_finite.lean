/-
  WilG4a — `oneDim_C1_finite`.

  A one-variable function `g : ℝ → ℝ` whose graph is an `Ω F D 2`-set of a sharply o-minimal
  structure `S` with sharp cell decomposition has only finitely many points of non-`C¹`-ness.

  The route is the one-dimensional sandwich, and it uses `SharpCD` only:

  * the non-differentiability locus `N = {x | ¬ DifferentiableAt ℝ g x}` is finite
    (`nondiff_locus_finite_sharpCD`: `N` is `Ω`-definable by `derivGraph_mem`, and it has empty
    interior because an interval of non-differentiability would, by `cont_off_finite`, contain a
    sub-interval of continuity, contradicting `nondiff_interval_free`; an `Ω`-definable subset of
    `ℝ¹` with empty interior is finite by `SOMin.comps` via
    `Work.WilG1.Calc.finite_of_interior_empty`);

  * the discontinuity locus `Z = {x | ¬ ContinuousAt (deriv g) x}` of Mathlib's junk-extended
    derivative is finite as well, because the graph of `deriv g` is `Ω`-definable
    (`derivGraph_mem`) and `cont_off_finite` applies to it;

  * finally, if `x` is outside the finite set `N ∪ Z`, then — this is where the *finiteness* of
    the union, and not merely a pointwise condition, is used — a whole interval around `x`
    avoids `N ∪ Z`, so on it `g` is differentiable and `deriv g` is continuous; hence `g` is
    `C¹` there (`contDiffOn_succ_iff_deriv_of_isOpen`), in particular at `x`.
-/
import Mathlib
import Submission.Work.WilG4a.derivGraph_mem
import Submission.Work.WilG4a.cont_off_finite
import Submission.Work.WilG4a.nondiff_interval_free
import Submission.Work.WilG1.Calc.finite_of_interior_empty
import Submission.Work.WilG4a.nondiff_locus_finite_sharpCD
import Submission.Work.WilG4a.oneDim_nonCk_finite

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4a

open WilkiesDesign

/-- The non-`C¹` locus of `g` is contained in the union of the non-differentiability locus of
`g` and the discontinuity locus of `deriv g`.

The proof needs the *finiteness* of that union and not just the pointwise condition: the
pointwise implication "`DifferentiableAt ℝ g x` and `ContinuousAt (deriv g) x` imply
`ContDiffAt ℝ 1 g x`" is false in general (a function can be differentiable at a single point,
e.g. `x ↦ x²` on the rationals and `0` on the irrationals, while `deriv` — junk-extended by
`0` off the differentiability locus — is continuous there).  It is the finiteness that supplies
an open interval around `x` on which the hypotheses hold everywhere, and on which
`contDiffOn_succ_iff_deriv_of_isOpen` produces `C¹`-ness. -/
theorem nonC1_locus_subset_of_nondiff_union (g : ℝ → ℝ)
    (hNfin : {x : ℝ | ¬ DifferentiableAt ℝ g x}.Finite)
    (hZfin : {x : ℝ | ¬ ContinuousAt (deriv g) x}.Finite) :
    {x : ℝ | ¬ ContDiffAt ℝ 1 g x} ⊆
      {x : ℝ | ¬ DifferentiableAt ℝ g x} ∪ {x : ℝ | ¬ ContinuousAt (deriv g) x} := by
  intro x hx
  by_contra hcon
  obtain ⟨η, hη, hηsub⟩ := exists_Ioo_disjoint_finite (hNfin.union hZfin) hcon
  set I : Set ℝ := Set.Ioo (x - η) (x + η) with hI
  have hIopen : IsOpen I := isOpen_Ioo
  have hIx : x ∈ I := ⟨by linarith, by linarith⟩
  have hgood : ∀ y ∈ I, DifferentiableAt ℝ g y ∧ ContinuousAt (deriv g) y := by
    intro y hy
    have hyout : y ∉ ({x : ℝ | ¬ DifferentiableAt ℝ g x} ∪
        {x : ℝ | ¬ ContinuousAt (deriv g) x}) := by
      intro hc
      have hmem : y ∈ Set.Ioo (x - η) (x + η) ∩ ({x : ℝ | ¬ DifferentiableAt ℝ g x} ∪
          {x : ℝ | ¬ ContinuousAt (deriv g) x}) := ⟨hy, hc⟩
      rw [hηsub] at hmem
      exact Set.notMem_empty y hmem
    rw [Set.mem_union, not_or] at hyout
    exact ⟨by simpa only [Set.mem_ofPred_eq, not_not] using hyout.1,
      by simpa only [Set.mem_ofPred_eq, not_not] using hyout.2⟩
  have hdiff : DifferentiableOn ℝ g I := fun y hy => (hgood y hy).1.differentiableWithinAt
  have hcont : ContinuousOn (deriv g) I := fun y hy => (hgood y hy).2.continuousWithinAt
  have hcdOn : ContDiffOn ℝ 1 g I := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hIopen]
    exact ⟨hdiff, fun h => absurd h (by simp), by rwa [contDiffOn_zero]⟩
  exact hx (hcdOn.contDiffAt (hIopen.mem_nhds hIx))

theorem oneDim_C1_finite (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    {x : ℝ | ¬ ContDiffAt ℝ 1 g x}.Finite := by
  have hNfin : {x : ℝ | ¬ DifferentiableAt ℝ g x}.Finite :=
    nondiff_locus_finite_sharpCD S hcd g hg
  obtain ⟨a, b, hD⟩ := derivGraph_mem S F
  have hZfin : {x : ℝ | ¬ ContinuousAt (deriv g) x}.Finite :=
    cont_off_finite S hcd (deriv g) (hD D g hg).2
  exact (hNfin.union hZfin).subset (nonC1_locus_subset_of_nondiff_union g hNfin hZfin)

end Work.WilG4a
