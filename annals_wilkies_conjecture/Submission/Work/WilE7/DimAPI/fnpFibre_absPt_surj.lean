import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.Nondrop.FibreCalc
import Submission.Work.WilE5.Basic

namespace Work.WilE7.DimAPI

open WilkiesDesign WilkiesDesign.E

/-- Reassembling an absolute point `z : Fin (0 + N) → ℝ` from its trivial base projection and
its `absPt` (`Fin N → ℝ`) part. -/
theorem fnpAppend_projFirst_absPt {N : ℕ} (z : Fin (0 + N) → ℝ) :
    Fin.append (projFirst 0 N z) (Work.WilE7.MainDesign.absPt z) = z := by
  have h : projSnd 0 N z = Work.WilE7.MainDesign.absPt z := by
    funext l; simp [projSnd, Work.WilE7.MainDesign.absPt]
  rw [← h]
  exact Work.WilE7.Nondrop.fnpAppend_proj z

theorem fnpFibre_absPt_surj {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) (hS : S.Good)
    (z : Fin (0 + N) → ℝ) (hz : z ∈ S.X.set) :
    Function.Surjective (fderiv ℝ (Work.WilE7.Nondrop.fnpFibre S
        (WilkiesDesign.E.projFirst 0 N z)) (Work.WilE7.MainDesign.absPt z)) ∧
      Module.finrank ℝ (fderiv ℝ (Work.WilE7.Nondrop.fnpFibre S
        (WilkiesDesign.E.projFirst 0 N z)) (Work.WilE7.MainDesign.absPt z)).ker = N - S.j := by
  have happ : Fin.append (WilkiesDesign.E.projFirst 0 N z) (Work.WilE7.MainDesign.absPt z) = z :=
    fnpAppend_projFirst_absPt z
  have hrank : (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
      eaEval S.X.c (eaD S.X.c (Work.WilE5.yDir 0 l) (S.h a))
        (Fin.append (WilkiesDesign.E.projFirst 0 N z) (Work.WilE7.MainDesign.absPt z))).rank
      = S.j := by
    rw [happ]
    exact Work.WilE5.Stratum.good_rank hS hz
  have htop := Work.WilE7.Nondrop.fnpFibre_range_eq_top_of_rank S
    (WilkiesDesign.E.projFirst 0 N z) (Work.WilE7.MainDesign.absPt z) hrank
  refine ⟨fun w => ?_, Work.WilE7.Nondrop.fnpFinrank_ker S _ _ htop⟩
  exact LinearMap.mem_range.mp (htop ▸ Submodule.mem_top)

end Work.WilE7.DimAPI
