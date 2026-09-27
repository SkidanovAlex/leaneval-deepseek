import Mathlib
import Submission.Work.EKLC6Core.cell_relthin_cover2
import Submission.Work.EKLC6Core.bad_inCol_shell
import Submission.Work.EKLC6Core.bad_outCol_upper_alt

/-!
# `Work.EKLC6Core.bad_subset_shells_alt`

The statement of `Work.EKLC6Core.bad_subset_shells` proved from the two ingredient lemmas
`bad_inCol_shell` and `bad_outCol_upper_alt` (proved in their own modules).  The body is the author's
proof in `Submission/Work/EKLC6Core/bad_subset_shells.lean`, which reaches the conclusion from
exactly those two lemmas; it is reproduced here so that the consumer is not blocked while that
file's local stubs are replaced by imports.
-/

namespace Work.EKLC6Core

open MeasureTheory Work.EKLContract

set_option linter.unusedVariables false

noncomputable section

theorem bad_subset_shells_alt (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure μ] (y : ℕ → Work.EKLContract.X3)
    (hcover : ∀ z : Work.EKLContract.X3, ∃ n : ℕ, n ∈ Work.EKLC6Core.sel y ∧
      z ∈ Work.EKLC6Core.cellBall μ y n)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ Work.EKLC6Core.epsZero) {z : Work.EKLContract.X3}
    {k : ℕ} (hz : z ∈ Work.EKLC6Core.Qcell μ y k)
    (hm : Work.EKLC6Core.cellMargin (Work.EKLC6Core.Qcell μ y) k z <
      ε * Work.EKLC6Core.injCap z) :
    ∃ j : ℕ, j ∈ Work.EKLC6Core.sel y ∧
      z ∈ Work.EKLC6Core.shell μ y (Work.EKLC6Core.deltac * ε) j := by
  -- ## Step 1: there is a displacement `v ∈ V (ε * injCap z)` moving `z` out of its cell
  have hηpos : 0 < ε * injCap z := mul_pos hε0 (injCap_pos z)
  have heps1 : epsZero ≤ 1 := by rw [epsZero, deltac]; norm_num
  have hη2 : ε * injCap z ≤ 2 := by
    have h1 := injCap_le_half z
    nlinarith [le_of_lt hε0, hε1, heps1, h1]
  have hcross : ∃ v : SL3, v ∈ V (ε * injCap z) ∧ v • z ∉ Qcell μ y k := by
    by_contra hcon
    push_neg at hcon
    have hmem : ε * injCap z ∈ {r : ℝ | 0 < r ∧ r ≤ 2 ∧
        ∀ v : SL3, v ∈ V r → v • z ∈ Qcell μ y k} := ⟨hηpos, hη2, hcon⟩
    have hle : ε * injCap z ≤ cellMargin (Qcell μ y) k z := by
      rw [cellMargin]
      exact le_csSup ⟨2, fun r hr => hr.2.1⟩ hmem
    linarith
  obtain ⟨v, hv, hvznot⟩ := hcross
  -- ## Step 2: `k` is selected and `z` lies in the `k`-th cell ball
  have hk_sel : k ∈ sel y := by
    by_contra hk
    have hzB : z ∈ cellBall μ y k := Qcell_subset μ y k hz
    rw [cellBall_eq_empty hk] at hzB
    exact absurd hzB (Set.notMem_empty z)
  have hzBk : z ∈ Work.EKLComp.Vball (cellRad μ y k) (y k) := by
    have h := Qcell_subset μ y k hz
    rwa [cellBall_eq hk_sel] at h
  -- ## Step 3: split according to whether `v • z` is still in the `k`-th cell ball
  by_cases hcase : v • z ∈ cellBall μ y k
  · -- ### Case 2: `v • z` is still in the `k`-th ball; it must have crossed an earlier ball
    have hl_exists : ∃ l : ℕ, l < k ∧ v • z ∈ closure (cellBall μ y l) := by
      by_contra hcon
      push_neg at hcon
      have hmem : v • z ∈ Qcell μ y k := by
        refine ⟨hcase, ?_⟩
        simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_compl_iff]
        intro l hl
        exact hcon l hl
      exact hvznot hmem
    obtain ⟨l, hlk, hvl⟩ := hl_exists
    have hl_sel : l ∈ sel y := by
      by_contra hl
      rw [cellBall_eq_empty hl, closure_empty] at hvl
      exact absurd hvl (Set.notMem_empty (v • z))
    have hcellpos : 0 < cellRad μ y l := cellRad_pos hl_sel
    have hδpos : 0 < deltac * ε := mul_pos deltac_pos hε0
    have hδ1 : deltac * ε ≤ 1 := deltac_eps_le_one hε1
    set ρ : ℝ := cellRad μ y l * (1 + deltac * ε / 2) with hρdef
    have hρ_lo : cellRad μ y l ≤ ρ := by rw [hρdef]; nlinarith [hδpos, hcellpos]
    have hρ_hi : ρ ≤ cellRad μ y l * (1 + deltac * ε / 2) := le_of_eq hρdef
    have hρ_gt : cellRad μ y l < ρ := by rw [hρdef]; nlinarith [hδpos, hcellpos]
    have hvl2 : v • z ∈ closure (Work.EKLComp.Vball (cellRad μ y l) (y l)) := by
      rwa [cellBall_eq hl_sel] at hvl
    have hvl' : v • z ∈ Work.EKLComp.Vball ρ (y l) :=
      Work.Misiurewicz.closure_Vball_subset_Vball_of_lt (y l) hρ_gt hvl2
    have hup : z ∈ Work.EKLComp.Vball (cellRad μ y l * (1 + deltac * ε)) (y l) :=
      bad_outCol_upper_alt hl_sel hk_sel hε0 hε1 hzBk hv hρ_lo hρ_hi hvl'
    have hnotcl : z ∉ closure (cellBall μ y l) := by
      have hh : z ∈ ⋂ l' ∈ Set.Iio k, (closure (cellBall μ y l'))ᶜ := hz.2
      simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_compl_iff] at hh
      exact hh l hlk
    have hlow : z ∉ Work.EKLComp.Vball (cellRad μ y l * (1 - deltac * ε)) (y l) := by
      intro hzlow
      apply hnotcl
      rw [cellBall_eq hl_sel]
      exact subset_closure (Work.Misiurewicz.Vball_mono (y l)
        (by nlinarith [hcellpos, hδpos, hδ1]) hzlow)
    refine ⟨l, hl_sel, ?_⟩
    rw [shell]
    exact ⟨hup, hlow⟩
  · -- ### Case 1: `v • z` left the `k`-th ball: the "inside collar"
    have hvz_out : v • z ∉ Work.EKLComp.Vball (cellRad μ y k) (y k) := by
      rw [cellBall_eq hk_sel] at hcase
      exact hcase
    exact ⟨k, hk_sel, bad_inCol_shell hk_sel hε0 hε1 hzBk hv hvz_out⟩

end

end Work.EKLC6Core
