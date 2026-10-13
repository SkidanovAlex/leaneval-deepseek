import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.Wilkies.Defs
import Submission.Work.WilC5.finite_subset_iUnion_monotone

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC5

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- **The definable closure is finitary.** A point `x` definable over an arbitrary parameter set
`A` is already definable over a *finite* subset `T ⊆ A`: a first-order formula is a finite
syntactic object, so it involves only finitely many parameters.  This is Mathlib's
`Set.definable_iff_finitely_definable` transported through the definition of `Dcl`
(`Dcl A = {x | A.Definable₁ LRc {x}}`). -/
theorem dcl_finite_params {M : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LRc M]
    {A : Set M} {x : M} (hx : x ∈ Work.WilC2.Dcl A) :
    ∃ T : Set M, T.Finite ∧ T ⊆ A ∧ x ∈ Work.WilC2.Dcl T := by
  rw [Work.WilC2.mem_dcl, Set.Definable₁] at hx
  obtain ⟨A0, hA0, hdef⟩ := (Set.definable_iff_finitely_definable).mp hx
  exact ⟨(A0 : Set M), A0.finite_toSet, hA0, by
    rw [Work.WilC2.mem_dcl, Set.Definable₁]; exact hdef⟩

theorem dcl_iUnion_chain {M : Type}
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc M]
    {ι : Type} [LinearOrder ι] [Nonempty ι] (A : ι → Set M) (hmono : Monotone A)
    (hA : ∀ i, Work.WilC2.Dcl (A i) ⊆ A i) :
    Work.WilC2.Dcl (⋃ i, A i) ⊆ ⋃ i, A i := by
  intro x hx
  -- `x` is definable from finitely many of the parameters in `⋃ i, A i`,
  obtain ⟨T, hTfin, hTA, hxT⟩ := dcl_finite_params hx
  -- finitely many parameters of an increasing chain live below a single index,
  obtain ⟨i, hTi⟩ := finite_subset_iUnion_monotone hmono hTfin hTA
  -- and `A i` is closed under `Dcl`.
  exact Set.mem_iUnion.mpr ⟨i, hA i (Work.WilC2.dcl_mono hTi hxT)⟩

end Work.WilC5
