import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.CoreStep.projTop_image_nhds_of_himm
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv

set_option autoImplicit false

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-- The differential (`jac`) of the equations of a `Good` absolute stratum is surjective at every
point of the stratum: the `Good` rank condition on the fibre Jacobian, transported to the full
Jacobian by reindexing its columns, gives full row rank. -/
theorem range_jac_eq_top_of_good_abs {q : ℕ} (S : WilkiesDesign.E.Stratum 0 q) (hS : S.Good)
    {z : Fin (0 + q) → ℝ} (hz : z ∈ S.X.set) :
    (Work.WilE7.MainDesign.jac S z).range = ⊤ := by
  rw [Work.WilE7.DimAPI.jac_eq_fderiv S z]
  exact Work.WilE7.DimAPI.range_fderiv_good_eq_top S hS hz

/-- On a `Good` stratum, the tangent space `ker (jac S z)` has dimension `n + 1` as soon as
`S.j = m`: the ambient space `ℝ^(0+(n+(m+1)))` has dimension `n + m + 1` and the surjective
`jac S z` has image `ℝ^(S.j) = ℝ^m`. -/
theorem finrank_ker_jac_of_good {n m : ℕ} (S : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hS : S.Good) (hj : S.j = m) {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ S.X.set) :
    Module.finrank ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac S z)) = n + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Work.WilE7.MainDesign.jac S z)
  rw [range_jac_eq_top_of_good_abs S hS hz] at h
  have htop : Module.finrank ℝ ↥(⊤ : Submodule ℝ (Fin S.j → ℝ)) = m := by
    rw [Submodule.topEquiv.finrank_eq, Module.finrank_fin_fun, hj]
  rw [htop, Module.finrank_fin_fun] at h
  omega

/-- **Maximal rank forces injectivity.**  The `(n+1)`-projection restricted to the tangent space
`ker (jac S z)` is injective as soon as it has maximal rank `n + 1`: the target has dimension
`n + 1` and, by `finrank_ker_jac_of_good`, so does the source; hence the rank–nullity equality
forces the kernel of the restriction to vanish. -/
theorem ker_comp_subtype_eq_bot_of_finrank {n m : ℕ}
    (S : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hS : S.Good) (hj : S.j = m) {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ S.X.set)
    (hrank : Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
      ((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) = n + 1) :
    LinearMap.ker
      (((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac S z)).subtype) = ⊥ := by
  have hKdim := finrank_ker_jac_of_good S hS hj hz
  have hkerdim : Module.finrank ℝ (LinearMap.ker
      (((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac S z)).subtype)) = 0 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac S z)).subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype] at h
    rw [hrank, hKdim] at h
    omega
  exact (Submodule.finrank_eq_zero).mp hkerdim

/-- **From the maximal tangential rank of `π_{n+1}` to the injectivity hypothesis `himm`.**

If the image of the tangent space `ker (jac S z)` under the linear `(n+1)`-projection
`projTopLin ∘ absPtLin` has dimension `n + 1`, then that projection is injective on the tangent
space; decomposing it into its base part `basePrLin n (m+1)` and its last (vertical) coordinate
`levelOf n m`, this says exactly that a tangent vector with vanishing base coordinates and
vanishing level is zero. -/
theorem himm_of_finrank {n m : ℕ} (S : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hS : S.Good) (hj : S.j = m)
    {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ S.X.set)
    (hrank : Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S z)).map
      ((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) = n + 1) :
    ∀ v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac S z),
      Work.WilE7.MainDesign.basePrLin n (m + 1) v = 0 →
      Work.CoreStep.levelOf n m v = 0 → v = 0 := by
  intro v hv hbase hlevel
  have hkerbot := ker_comp_subtype_eq_bot_of_finrank S hS hj hz hrank
  have hLv : ((Work.WilE7.CoreStep.projTopLin n m).comp
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))) v = 0 := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [Work.CoreStep.projTopLin_absPtLin_last]; exact hlevel
    · intro i'; rw [Work.CoreStep.projTopLin_absPtLin_castSucc]; exact congrFun hbase i'
  have hmem : (⟨v, hv⟩ : LinearMap.ker (Work.WilE7.MainDesign.jac S z)) ∈ LinearMap.ker
      (((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac S z)).subtype) := hLv
  rw [hkerbot] at hmem
  exact Subtype.ext_iff.mp ((Submodule.mem_bot ℝ).mp hmem)

end Work.CoreStep
