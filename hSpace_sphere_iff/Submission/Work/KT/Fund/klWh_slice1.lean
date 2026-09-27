import Mathlib
import Submission.Work.KT.Fund.kl_wh_defs

namespace Work.KT.Fund

open Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The `X`-coordinate of `incl1 X p` is `p.1`. -/
@[simp] lemma incl1_fst_klWh (p : X × Sph ℂ) : ((incl1 X) p).1.1 = p.1 := rfl

/-- The time coordinate of `incl1 X p` is `1`. -/
@[simp] lemma incl1_t_klWh (p : X × Sph ℂ) : ((((incl1 X) p).1.2 : ℝ) : ℂ) = 1 := rfl

/-- The circle coordinate of `incl1 X p` is `p.2`. -/
@[simp] lemma incl1_snd_klWh (p : X × Sph ℂ) : ((incl1 X) p).2 = p.2 := rfl

/-- **The `t = 1` slice of the homotopy `klWh` is the "outside" factor `klW`.**
Substituting `t = 1` into `H_t = t z (1 - E) + (1 - E) b + E` returns exactly
`klW = E + z (1 - E) + (1 - E) b`. -/
theorem klWh_slice1 (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Work.KT.Fund.klWh X n b E).map (fun f => f.comp (Work.KT.Fund.incl1 X))
      = Work.KT.Fund.klW X n b E := by
  ext i j p
  change klWh X n b E i j (incl1 X p) = klW X n b E i j p
  simp only [klWh, klW, klP, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, klSZ_apply, klz_apply, klProj_apply,
    pullMat_apply, ContinuousMap.comp_apply, Finset.sum_apply, ContinuousMap.coe_sum,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, ContinuousMap.zero_apply, DFunLike.ite_apply, smul_eq_mul,
    incl1_fst_klWh, incl1_t_klWh, incl1_snd_klWh, one_mul]
  abel

end

end Work.KT.Fund
