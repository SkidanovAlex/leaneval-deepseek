import Mathlib
import Submission.Work.DSMX0U.ModelF
import Submission.Work.DSMX0U.Tower

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

set_option linter.style.haveILetI false

theorem quasiIsoAt_towerModelMap_gt {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Work.DSMX0U.Cell A C c₀ q), Work.DSMX0U.StepData A s)
    (M : ℤ) (s₀ : Work.DSMX0U.Cell A C c₀ (M + 1))
    (φ : Work.DSMX0U.towerModel hstep M s₀ ⟶ C)
    {N : ℤ} (hN : ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (C.homology i))
    (hMN : N ≤ M) {i : ℤ} (hi : M < i) :
    QuasiIsoAt φ i := by
  -- Above `M` the model complex vanishes, and the cohomology of `C` vanishes above `N ≤ M`;
  -- hence both homology modules in degree `i > M` are zero and the induced map is an isomorphism.
  rw [quasiIsoAt_iff_isIso_homologyMap]
  haveI hP : (towerModel hstep M s₀).IsStrictlyLE M :=
    (CochainComplex.isStrictlyLE_iff (towerModel hstep M s₀) M).mpr
      (fun j hj => towerModel_isZero_of_gt hstep M s₀ hj)
  haveI hPh : CategoryTheory.Limits.IsZero ((towerModel hstep M s₀).homology i) :=
    CochainComplex.isZero_of_isLE (towerModel hstep M s₀) M i hi
  haveI hCh : CategoryTheory.Limits.IsZero (C.homology i) :=
    hN i (lt_of_le_of_lt hMN hi)
  exact CategoryTheory.Limits.IsZero.isIso hPh hCh (HomologicalComplex.homologyMap φ i)

end Work.DSMX0U
