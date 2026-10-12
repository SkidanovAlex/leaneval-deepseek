import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SlotWord

/-- **The support of the sliding small-box cutoff lies in `B(u)`.**

`chiSmallB M L d u x = chiScale L x · chiSmall M ((L·d)⁻¹ • x − u)` is the
product of the corpus bump at the big-box scale `L` and the cosine-`M`-th-power
bump at the small-box scale `L·d`.  If it is non-zero then both factors are
non-zero:
* `chiScale L x ≠ 0` forces `‖x‖ < L/2`, hence `|x_j| ≤ L/2` for every `j`
  (`chiSmallB_support_big_box`), i.e. `x ∈ acube L`;
* `chiSmall M ((L·d)⁻¹ • x − u) ≠ 0` forces every coordinate of
  `(L·d)⁻¹ • x − u` into the unit face slab `|·| ≤ 1/2`
  (`chiSmallB_support_small_box`); multiplying by `L·d > 0` turns this into
  `x − (L·d)•u ∈ acube (L·d)`.

Together these are exactly `x ∈ dlBox L d u`. -/
theorem chiSmallB_support_mem_dlBox {M : ℕ} (hM : 1 ≤ M) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    {u x : EuclideanSpace ℝ (Fin 3)} (hx : Submission.BoseGases.chiSmallB M L d u x ≠ 0) :
    x ∈ Submission.BoseGases.dlBox L d u := by
  have hc : 0 < L * d := mul_pos hL hd
  rw [Submission.BoseGases.mem_dlBox_iff]
  constructor
  · rw [Submission.BoseGases.mem_acube_iff]
    intro m
    rw [Set.mem_Icc]
    have hb := abs_le.mp (Submission.BoseGases.chiSmallB_support_big_box hM hL hx m)
    constructor <;> linarith [hb.1, hb.2]
  · rw [Submission.BoseGases.mem_acube_iff]
    intro m
    rw [Set.mem_Icc]
    have h :=
      Submission.BoseGases.chiSmallB_support_small_box (M := M) hM (u := u) (x := x) hx m
    have hrew : (L * d)⁻¹ • x - u = (L * d)⁻¹ • (x - (L * d) • u) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    rw [hrew] at h
    have hsmul : ((L * d)⁻¹ • (x - (L * d) • u)).ofLp m
        = (L * d)⁻¹ * (x - (L * d) • u).ofLp m := by simp
    rw [hsmul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))] at h
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hc)
    have hfin : |(x - (L * d) • u).ofLp m| ≤ (L * d) / 2 := by
      calc |(x - (L * d) • u).ofLp m|
          = (L * d) * ((L * d)⁻¹ * |(x - (L * d) • u).ofLp m|) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
        _ ≤ (L * d) * (1 / 2) := hmul
        _ = (L * d) / 2 := by ring
    have hf := abs_le.mp hfin
    exact ⟨by linarith [hf.1], by linarith [hf.2]⟩

end Work.SlotWord
