/-
Area DSCOH — exactness of the chart Čech complex in one degree kills the homology there.

The chart Čech complex `Work.DSCOH.chartCech ℳ` has differentials `cechDiff ℳ q` in degree `q`,
so its `(q+1)`-st homology is `ker (cechDiff (q+1)) / range (cechDiff q)`.  Hence the exactness
condition `range (cechDiff q) = ker (cechDiff (q+1))` at the single degree `q + 1` makes that
homology group vanish: this is the file's theorem `chartCech_exact_isZero_homology`.

The general homological input (a cochain complex of `A`-modules is acyclic in degree `q + 1` as
soon as the alternating pattern of differentials is exact there) is isolated below as
`isZero_homology_of_range_eq_ker`, and is the only thing the proof of the special case needs:
the two differentials of `chartCech` are `cechDiff q` and `cechDiff (q + 1)` by construction
(`CochainComplex.of_d`).
-/
import Mathlib
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.Cech

namespace Work.DSCOH

open CategoryTheory

/-- **A cochain complex of modules is acyclic where it is exact.**

If the differential `K.d q (q + 1) : K^q ⟶ K^{q+1}` has range the kernel of
`K.d (q + 1) (q + 2) : K^{q+1} ⟶ K^{q+2}`, then the `(q+1)`-st homology of `K` is zero. -/
theorem isZero_homology_of_range_eq_ker {A : Type*} [CommRing A]
    (K : CochainComplex (ModuleCat A) ℕ) (q : ℕ)
    (h : LinearMap.range (ModuleCat.Hom.hom (K.d q (q + 1))) =
      LinearMap.ker (ModuleCat.Hom.hom (K.d (q + 1) (q + 2)))) :
    CategoryTheory.Limits.IsZero (K.homology (q + 1)) := by
  -- `IsZero` of the homology is exactness of `K` in degree `q + 1`, and exactness there is
  -- exactness of the short complex `K^q → K^{q+1} → K^{q+2}`.
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' K q (q + 1) (q + 2)
    (ComplexShape.prev_eq' (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl))
    (ComplexShape.next_eq' (ComplexShape.up ℕ)
      (show (ComplexShape.up ℕ).Rel (q + 1) (q + 2) from rfl))]
  -- For a short complex of modules, exactness is precisely `range = ker`.
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact h

theorem chartCech_exact_isZero_homology {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M]
    [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ)
    (h : LinearMap.range (cechDiff (A := A) (n := n) (M := M) ℳ q) =
      LinearMap.ker (cechDiff (A := A) (n := n) (M := M) ℳ (q + 1))) :
    CategoryTheory.Limits.IsZero ((chartCech (A := A) (n := n) (M := M) ℳ).homology (q + 1)) := by
  -- The differential of the chart Čech complex in degree `q` is `cechDiff ℳ q`, by its very
  -- construction (`chartCechOf`/`chartCech` are built with `CochainComplex.of`).
  refine isZero_homology_of_range_eq_ker (K := chartCech (A := A) (n := n) (M := M) ℳ) q ?_
  have hf : ModuleCat.Hom.hom ((chartCech (A := A) (n := n) (M := M) ℳ).d q (q + 1)) =
      cechDiff (A := A) (n := n) (M := M) ℳ q := by
    simp only [chartCech, chartCechOf, CochainComplex.of_d]
    exact ModuleCat.hom_ofHom _
  have hg : ModuleCat.Hom.hom ((chartCech (A := A) (n := n) (M := M) ℳ).d (q + 1) (q + 2)) =
      cechDiff (A := A) (n := n) (M := M) ℳ (q + 1) := by
    -- `CochainComplex.of_d` produces the index `(q + 1) + 1`, which is definitionally `q + 2`.
    change ModuleCat.Hom.hom ((chartCech (A := A) (n := n) (M := M) ℳ).d (q + 1) ((q + 1) + 1)) =
      cechDiff (A := A) (n := n) (M := M) ℳ (q + 1)
    simp only [chartCech, chartCechOf, CochainComplex.of_d]
    exact ModuleCat.hom_ofHom _
  rw [hf, hg]
  exact h

end Work.DSCOH
