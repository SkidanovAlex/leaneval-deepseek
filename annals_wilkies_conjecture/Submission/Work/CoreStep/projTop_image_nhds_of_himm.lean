import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.CoreStep.CrossDefs
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.CoreStep.locSubmersion_of_finrank
import Submission.Work.WilE7.CoreStep.finrank_projTop_of_not_critSet

set_option autoImplicit false

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.CoreStep
open Work.WilE7.MainDesign

/-! ## Component bookkeeping for the linear map `projTopLin ∘ absPtLin`

The map `(projTopLin n m).comp (absPtLin (n + (m+1)))` is the linear map underlying `projTop ∘
absPt` (it is `topPrLin n m`).  Its `castSucc`-components are exactly `basePrLin n (m+1)` and its
last component is exactly `levelOf n m`; these two identities turn the injectivity hypothesis
`himm` into the statement that this map is injective on the tangent space `ker (jac T z)`. -/

/-- The linear map `projTopLin ∘ absPtLin` is the continuous linear map `topPrLin`. -/
theorem projTopLin_absPtLin_eq_topPrLin {n m : ℕ} (w : Fin (0 + (n + (m + 1))) → ℝ) :
    ((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))) w
      = Work.WilE7.CoreStep.topPrLin n m w := by
  rw [Work.WilE7.CoreStep.topPrLin_apply, LinearMap.comp_apply,
    Work.WilE7.CoreStep.absPtLin_apply, Work.WilE7.CoreStep.projTopLin_apply]

/-- The `castSucc`-component of `projTopLin ∘ absPtLin` is `basePrLin`. -/
theorem projTopLin_absPtLin_castSucc {n m : ℕ}
    (w : Fin (0 + (n + (m + 1))) → ℝ) (i : Fin n) :
    ((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))) w i.castSucc
      = Work.WilE7.MainDesign.basePrLin n (m + 1) w i := by
  rw [LinearMap.comp_apply, Work.WilE7.CoreStep.absPtLin_apply,
    Work.WilE7.CoreStep.projTopLin_apply, Work.WilE7.CoreStep.projTop_castSucc]
  rfl

/-- The last component of `projTopLin ∘ absPtLin` is `levelOf`. -/
theorem projTopLin_absPtLin_last {n m : ℕ} (w : Fin (0 + (n + (m + 1))) → ℝ) :
    ((Work.WilE7.CoreStep.projTopLin n m).comp
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))) w (Fin.last n)
      = levelOf n m w := by
  rw [LinearMap.comp_apply, Work.WilE7.CoreStep.absPtLin_apply,
    Work.WilE7.CoreStep.projTopLin_apply, Work.WilE7.CoreStep.projTop_last]
  rfl

/-- **Injectivity of the tangential `π_{n+1}`.**  The hypothesis `himm` says precisely that the
linear map `projTopLin ∘ absPtLin` (base coordinates together with the vertical coordinate) has
trivial kernel on the tangent space `ker (jac T z)` of the stratum at `z`. -/
theorem ker_projTop_of_himm {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    {z : Fin (0 + (n + (m + 1))) → ℝ}
    (himm : ∀ v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T z),
      Work.WilE7.MainDesign.basePrLin n (m + 1) v = 0 →
      Work.CoreStep.levelOf n m v = 0 → v = 0) :
    LinearMap.ker
      (((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro ⟨v, hv⟩ hmem
  have hLv : ((Work.WilE7.CoreStep.projTopLin n m).comp
      (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))) v = 0 := hmem
  refine Subtype.ext (himm v hv ?_ ?_)
  · funext i
    have h := congrFun hLv i.castSucc
    rw [projTopLin_absPtLin_castSucc] at h
    simpa using h
  · have h := congrFun hLv (Fin.last n)
    rw [projTopLin_absPtLin_last] at h
    simpa using h

/-- **From injectivity to the maximal tangential rank.**  If `projTopLin ∘ absPtLin` is injective on
`ker (jac T z)` and `T.j = m`, then the image of the tangent space has dimension `n + 1`, i.e. the
`π_{n+1}`-tangential rank is maximal.  The dimension of `ker (jac T z)` is `≥ n + 1` because
`jac T z` maps into `ℝ^{T.j} = ℝ^m`, while the image of `projTopLin ∘ absPtLin` on it has dimension
at most `n + 1` because it lives inside `ℝ^{n+1}`. -/
theorem finrank_projTop_of_himm {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hj : T.j = m) {z : Fin (0 + (n + (m + 1))) → ℝ}
    (hker : LinearMap.ker
      (((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype) = ⊥) :
    Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) = n + 1 := by
  -- the map `projTopLin ∘ absPtLin` is injective on `ker (jac T z)`
  have hkey : Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))))
      = Module.finrank ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T z)) := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1)))).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype, hker] at h
    simpa using h
  -- `dim (ker (jac T z)) ≥ n + 1`
  have hge : n + 1 ≤ Module.finrank ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T z)) := by
    have h := LinearMap.finrank_range_add_finrank_ker (Work.WilE7.MainDesign.jac T z)
    have hle : Module.finrank ℝ (LinearMap.range (Work.WilE7.MainDesign.jac T z)) ≤ m := by
      calc Module.finrank ℝ (LinearMap.range (Work.WilE7.MainDesign.jac T z))
          ≤ Module.finrank ℝ (Fin T.j → ℝ) := Submodule.finrank_le _
        _ = T.j := by simp
        _ = m := hj
    rw [Module.finrank_fin_fun] at h
    omega
  -- `dim (image) ≤ n + 1`
  have hle' : Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) ≤ n + 1 := by
    calc _ ≤ Module.finrank ℝ (Fin (n + 1) → ℝ) := Submodule.finrank_le _
      _ = n + 1 := by simp
  omega

theorem projTop_image_nhds_of_himm {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good) (hj : T.j = m)
    {z : Fin (0 + (n + (m + 1))) → ℝ} (hz : z ∈ T.X.set)
    (himm : ∀ v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T z),
      Work.WilE7.MainDesign.basePrLin n (m + 1) v = 0 →
      Work.CoreStep.levelOf n m v = 0 → v = 0) :
    ∃ V ∈ nhds (Work.WilE7.MainDesign.absPt z),
      Work.WilE7.CoreStep.projTop n m '' (Work.WilE7.MainDesign.absSet T ∩ V)
        ∈ nhds (Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt z)) := by
  have hfull := finrank_projTop_of_himm T hj (ker_projTop_of_himm T himm)
  obtain ⟨U, hU, hUsub⟩ := Work.WilE7.CoreStep.locSubmersion_of_finrank T hT hz hfull
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  rw [Set.inter_univ]
  exact Filter.mem_of_superset hU hUsub

end Work.CoreStep
