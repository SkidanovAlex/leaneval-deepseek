import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.coreLT_succ.SubStratum
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.WilE7.exists_ker_equiv

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.Endgame

/-- **Nonvanishing of a tangent vector with vanishing `projTop`-image.**

Let `T : Stratum 0 (n + (m+1))` be an absolute `Good` stratum and `w ∈ T.X.set`.  By `Good`, the
differential of the defining equations, `jac T w`, is surjective onto `ℝ^{T.j}`
(`Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux`), so rank–nullity gives
`dim ker (jac T w) = (0 + (n+(m+1))) - T.j = dim T`.  The hypothesis `HImm T` says that the
composite `φ := projTopLin n m ∘ absPtLin (n+(m+1))` (i.e. the linear map underlying
`projTop = π_{n+1}`) has image of the *same* dimension `n + (m+1) - T.j` on that tangent space.
A linear map whose range has the same finite dimension as its domain is injective, so
`ker (jac T w) ∩ ker φ = 0`: a tangent vector of `T` at `w` whose `π_{n+1}`-image vanishes is
zero. -/
theorem eq_zero_of_mem_ker_jac_of_projTop_eq_zero {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good)
    (himm : Work.WilE7.CoreLTSuccPlan.HImm T)
    {w : Fin (0 + (n + (m + 1))) → ℝ} (hw : w ∈ T.X.set)
    {τ : Fin (0 + (n + (m + 1))) → ℝ}
    (hτ : τ ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T w))
    (hzero : Work.WilE7.CoreStep.projTopLin n m
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)) τ) = 0) : τ = 0 := by
  -- The differential of the defining equations is surjective (Good stratum).
  have hsurj : (Work.WilE7.MainDesign.jac T w).range = ⊤ :=
    Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux T hT hw
  -- ... hence the tangent space has dimension `(0 + (n+(m+1))) - T.j`.
  have hdom : Module.finrank ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T w))
      = (0 + (n + (m + 1))) - T.j :=
    Work.WilE7.finrank_ker_of_surjective (Work.WilE7.MainDesign.jac T w) hsurj
  -- ... and by `HImm` its `projTop`-image has the same dimension.
  have himg : Module.finrank ℝ ↥((LinearMap.ker (Work.WilE7.MainDesign.jac T w)).map
      ((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) = n + (m + 1) - T.j := himm w hw
  -- The range of the composite `projTopLin ∘ absPtLin` on the tangent space is that image.
  have hfin : Module.finrank ℝ ↥(((Work.WilE7.CoreStep.projTopLin n m).comp
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).subtype).range
      = Module.finrank ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T w)) := by
    rw [LinearMap.range_comp (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).subtype
      ((Work.WilE7.CoreStep.projTopLin n m).comp (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))),
      Submodule.range_subtype, himg, hdom]
    simp
  -- So the kernel of the composite has dimension `0`, i.e. the composite is injective.
  have hker0 : Module.finrank ℝ ↥(((Work.WilE7.CoreStep.projTopLin n m).comp
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).subtype).ker = 0 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).subtype)
    rw [hfin] at h
    omega
  have hinj : Function.Injective (((Work.WilE7.CoreStep.projTopLin n m).comp
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).subtype) :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker0)
  -- `τ` lies in the kernel of the composite by `hzero`.
  have hmem0 : (((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).subtype)
      ⟨τ, hτ⟩ = 0 := by
    simpa using hzero
  have hz : (⟨τ, hτ⟩ : ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T w))) = 0 := by
    apply hinj
    rw [hmem0]
    simp
  simpa using congrArg Subtype.val hz

end Work.WilE7.Endgame
