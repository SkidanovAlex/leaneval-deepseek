import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.spanning_Mp_idealIOdd
import Submission.Work.Asymptotics.OddRepNoGo
import Submission.Work.Residues.basis_quotient_IdealI
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Residues.IdealImDefs
import Submission.Work.Asymptotics.indep_Mp_idealIOdd

namespace Work.Asymptotics

open Work.Kernels

/-- **The six classes `[MpElem i]` span `R ⧸ 𝓘_odd`** (CKMRV, proof of Proposition 3.2(1),
odd weight): every element of `R` is congruent modulo `𝓘_odd` to a `ℂ`-linear combination of
the six elements `MpElem i`, and the six classes are linearly independent
(`Work.Asymptotics.indep_Mp_idealIOdd`).  Hence the `ℂ`-span of the six elements meets the
odd-weight defect ideal only in `0`. -/
theorem spMpSpan_inf_idealIOdd :
    Work.Asymptotics.spMpSpan ⊓ Work.Asymptotics.idealIOdd = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxs, hxi⟩ := Submodule.mem_inf.mp hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hxs
  rw [← hc] at hxi ⊢
  rw [Submodule.mem_bot]
  have h0 : Submodule.mkQ idealIOdd (∑ i, c i • MpElem i) = 0 :=
    (Submodule.Quotient.mk_eq_zero idealIOdd).mpr hxi
  rw [map_sum] at h0
  simp only [map_smul] at h0
  have hcz : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp indep_Mp_idealIOdd c h0
  simp [hcz]

end Work.Asymptotics
