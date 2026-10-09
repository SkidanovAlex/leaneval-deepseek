import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.ProP.exists_pCentralSeries_le_ker
import Submission.Work.Shrinking.Refined
import Submission.Work.Shrinking.pCentralSeries_le_succ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- **The generic kernel statement for the *refined* filtration.**  The filtration used in
Theorem 15 of Schmidt–Wingberg is not the `p`-central series itself but its refinement
`P_{(i,j)} = (P_i ∩ P_j) P_{i+1}` (available as `Work.Shrinking.pCentralRefined`, which refines
the series: `pCentralRefined p F (ν+1) (ν+1) = F^(n)(ν)`).  For every homomorphism from the free
group on `n` generators to a finite `p`-group some term of the refined filtration lies in the
kernel.

Proof: take `ν` with `pCentralSeries p (FreeGroup (Fin n)) ν ≤ φ.ker`
(`Work.ProP.exists_pCentralSeries_le_ker`) and put `i = j = ν + 1`: then
`pCentralRefined p F (ν+1) (ν+1) = (P_ν ⊓ P_ν) ⊔ P_{ν+1} = P_ν ≤ φ.ker`, using
`Work.Shrinking.pCentralSeries_antitone` for `P_{ν+1} ≤ P_ν`. -/
theorem exists_pCentralRefined_le_ker {p : ℕ} [Fact p.Prime] (n : ℕ) {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (φ : FreeGroup (Fin n) →* P) :
    ∃ i j : ℕ, Work.Shrinking.pCentralRefined p (FreeGroup (Fin n)) i j ≤ φ.ker := by
  obtain ⟨ν, hν⟩ := exists_pCentralSeries_le_ker (p := p) n hP φ
  refine ⟨ν + 1, ν + 1, ?_⟩
  have hle : Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) (ν + 1) ≤
      Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν :=
    Work.Shrinking.pCentralSeries_le_succ p _ ν
  rw [Work.Shrinking.pCentralRefined, Nat.add_sub_cancel, inf_idem]
  rwa [sup_eq_left.mpr hle]

end Work.ProP
