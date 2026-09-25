import Mathlib
import Submission.Work.NN.Newton.FTdefs

namespace Work.NN.Newton.FTcut

/-- The product of the `ℂⁿ`-cutoff `ftCut n a b` (which is `≡ 1` on the polydisc of radius `a`
and `≡ 0` outside the polydisc of radius `b < 1`) with a function `u` that is `C¹` only on the
unit polydisc is globally `C¹`.

Indeed, at a point `z` inside the unit polydisc both factors are `C¹` (the cutoff is globally
`C^∞`, and `u` is `C¹` near `z` since the unit polydisc is open), while at a point `z` outside the
unit polydisc some coordinate has norm `≥ 1 > b`, so `ftCut` vanishes on a whole neighbourhood of
`z` and the product is locally the zero function. -/
theorem contDiff_ftCut_mul {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb1 : b < 1)
    {u : (Fin n → ℂ) → ℂ}
    (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 (fun _ => 1))) :
    ContDiff ℝ 1 (fun z => Work.NN.Newton.ftCut n a b z * u z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1)
  · -- Inside the unit polydisc: both factors are `C¹` at `z`.
    have hu_at : ContDiffAt ℝ 1 u z :=
      hu.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 (fun _ => 1)).mem_nhds hz)
    have hf_at : ContDiffAt ℝ 1 (Work.NN.Newton.ftCut n a b) z :=
      ((Work.NN.Newton.contDiff_ftCut a b).of_le (by norm_num)).contDiffAt
    exact hf_at.mul hu_at
  · -- Outside the unit polydisc some coordinate has norm `≥ 1 > b`, so `ftCut` vanishes nearby.
    have hz' : ∃ j : Fin n, 1 ≤ ‖z j‖ := by
      simpa [Work.CR.Flat.mem_polydisc] using hz
    obtain ⟨j, hj⟩ := hz'
    have hb_lt : b < ‖z j‖ := lt_of_lt_of_le hb1 hj
    have hmem : {w : Fin n → ℂ | b < ‖w j‖} ∈ nhds z :=
      ((continuous_apply j).norm.isOpen_preimage _ isOpen_Ioi).mem_nhds hb_lt
    have hev : (fun w => Work.NN.Newton.ftCut n a b w * u w) =ᶠ[nhds z] (fun _ => 0) := by
      filter_upwards [hmem] with w hw
      rw [Work.NN.Newton.ftCut_eq_zero ha hab (le_of_lt hw), zero_mul]
    exact (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq hev

end Work.NN.Newton.FTcut
