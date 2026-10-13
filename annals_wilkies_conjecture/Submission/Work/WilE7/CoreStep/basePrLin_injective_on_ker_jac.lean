import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.jac_range_eq_top_of_good
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.WilE7.exists_ker_equiv

namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- **Injectivity of the base projection on the tangent space.**

Let `T : Stratum 0 (n+q)` be a `Good` absolute stratum and `z ∈ T.X.set`.  The defining
equations of `T` are `T.j` analytic functions whose differential `jac T z` is surjective onto
`ℝ^{T.j}` (`Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux`), so by rank–nullity the tangent
space `ker (jac T z)` has dimension `(0 + (n+q)) - T.j = n + q - T.j`.  The hypothesis
`projRank T z = n + q - T.j` says that the image of that tangent space under the base
projection `basePrLin n q : ℝ^{0+(n+q)} → ℝ^n` has the *same* dimension.  A linear map whose
range has the same (finite) dimension as its domain is injective; applied to
`(basePrLin n q).comp (ker (jac T z)).subtype : ker (jac T z) → ℝ^n` this is the claim. -/
theorem basePrLin_injective_on_ker_jac {n q : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + q))
    (hT : T.Good) (z : Fin (0 + (n + q)) → ℝ) (hz : z ∈ T.X.set)
    (hrank : Work.WilE7.MainDesign.projRank T z = n + q - T.j) :
    Function.Injective ((Work.WilE7.MainDesign.basePrLin n q).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype) := by
  -- the differential of the defining equations is surjective (Good stratum)
  have hsurj : (Work.WilE7.MainDesign.jac T z).range = ⊤ :=
    Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux T hT hz
  -- ... hence the tangent space has dimension `(0 + (n+q)) - T.j`
  have hdom : Module.finrank ℝ ↥(Work.WilE7.MainDesign.jac T z).ker = (0 + (n + q)) - T.j :=
    Work.WilE7.finrank_ker_of_surjective (Work.WilE7.MainDesign.jac T z) hsurj
  -- ... and by hypothesis its projection has the same dimension
  have himg : Module.finrank ℝ ↥((Work.WilE7.MainDesign.jac T z).ker.map
      (Work.WilE7.MainDesign.basePrLin n q)) = n + q - T.j := hrank
  -- the range of the composite is exactly that projection of the tangent space
  have hfin : Module.finrank ℝ ↥(((Work.WilE7.MainDesign.basePrLin n q).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype).range)
      = Module.finrank ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T z)) := by
    rw [LinearMap.range_comp (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype
      (Work.WilE7.MainDesign.basePrLin n q), Submodule.range_subtype, himg, hdom]
    simp
  -- so the kernel of the composite has dimension `0`, i.e. is trivial
  have hker0 : Module.finrank ℝ ↥(((Work.WilE7.MainDesign.basePrLin n q).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype).ker) = 0 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((Work.WilE7.MainDesign.basePrLin n q).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype)
    rw [hfin] at h
    omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)

end Work.WilE7.CoreStep
