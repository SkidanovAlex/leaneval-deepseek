import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB.ThompsonWeakClosed

namespace Work.ZJB2.Step1

open scoped Pointwise
open Subgroup

/-- **F1.** If `J(S) ≤ Q` for a `p`-subgroup `Q`, then `J(Q) = J(S)`.

Choose a Sylow `p`-subgroup `S₄ ⊇ Q` and `d` with `S = S₄^d`.  Then
`J(S) = J(S₄^d) = J(S₄)^d`; since `J(S) ≤ Q ≤ S₄`, weak closedness of `J(S₄)` in `S₄`
gives `J(S₄)^d = J(S₄)`, so `J(S) = J(S₄)`.  Finally `J(S₄) ≤ Q ≤ S₄` and
`J(Q) = J(S₄)` (Gorenstein 2.2). -/
theorem thompsonJEqOfLeProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.ThompsonJEqOfLeProp p G := by
  intro S Q hQp hJQ
  -- a Sylow `p`-subgroup `S₄` containing the `p`-subgroup `Q`
  obtain ⟨S₄, hQleS₄⟩ := hQp.exists_le_sylow
  -- `S` is a conjugate of `S₄`
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq G S₄ S
  have hdsub : (S : Subgroup G) = (S₄ : Subgroup G).map (MulAut.conj d).toMonoidHom := by
    have h := congrArg (fun (P : Sylow p G) => (P : Subgroup G)) hd
    simp only [Sylow.coe_subgroup_smul] at h
    rw [Subgroup.pointwise_smul_def] at h
    exact h.symm
  -- `J(S) = J(S₄)^d`
  have hJd : Work.GW2.thompsonJ (S : Subgroup G)
      = (Work.GW2.thompsonJ (S₄ : Subgroup G)).map (MulAut.conj d).toMonoidHom := by
    rw [hdsub, Work.GW2.thompsonJ_map_conj]
  -- weak closedness: `J(S₄)^d ≤ S₄` forces `J(S₄)^d = J(S₄)`
  have hJS : Work.GW2.thompsonJ (S : Subgroup G) = Work.GW2.thompsonJ (S₄ : Subgroup G) := by
    have hle : (Work.GW2.thompsonJ (S₄ : Subgroup G)).map (MulAut.conj d).toMonoidHom
        ≤ (S₄ : Subgroup G) := by
      rw [← hJd]
      exact hJQ.trans hQleS₄
    have hclosed := Work.ZJB.thompsonJ_map_conj_eq_of_le (S₄ : Subgroup G) d hle
    exact hJd.trans hclosed
  -- Gorenstein 2.2: `J(S₄) ≤ Q ≤ S₄` gives `J(Q) = J(S₄)`
  have hJ4leQ : (S₄ : Subgroup G).thompsonJAbelian ≤ Q := by
    rw [← Work.GW2.thompsonJ_eq_thompsonJAbelian (S₄ : Subgroup G), ← hJS]
    exact hJQ
  have hres := Subgroup.thompsonJAbelian_eq_of_le_of_le hJ4leQ hQleS₄
  rw [Work.GW2.thompsonJ_eq_thompsonJAbelian Q, hres,
    ← Work.GW2.thompsonJ_eq_thompsonJAbelian (S₄ : Subgroup G), hJS]

end Work.ZJB2.Step1
