import Mathlib
import Submission.Work.Pert.pert2v2.walk_to_window
import Submission.Work.Pert.pert2v2.fatou_proper_im
import Submission.Work.Pert.liftF_lower_ends
import Submission.Work.Pert.waist_low

/-!
# `Work.Pert.pert2v2.waist_return_bound_up`

**The return map `Φm ∘ Tt α` differs from `Φm` by a BOUNDED amount in the waist.**  For a
near-translation `F` on the lower gate `Qm Ξ α` with Fatou coordinate `Φm`, exponentially close to
`z ↦ z + 1` above a height, the deck translate `Tt α ς = ς - 1/α` of a waist point `ς` satisfies

  `∃ K C, ∀ ς, |ς.re| + 2 < |ς.im| - Ξ → K ≤ ς.im → ‖Φm (Tt α ς) - Φm ς‖ ≤ C`.

This is the boundedness (not the limit) of `R̃_f - id` that the Phragmén–Lindelöf/periodicity
pieces of the assembly (`pert2v2.lower_end_close_of_line`, `norm_le_of_periodic_*`) consume.

**The proof, and why it is *uniform* in `Re ς`.**  The waist hypothesis is exactly
`ς ∈ Qm Ξ α ∧ Tt α ς ∈ Qm Ξ α` (`Work.Pert.mem_waist_iff`), so both points make sense as arguments
of `Φm`.  Mathematically `Φm z ≈ z + c` at the upper end (the contract's `FatouEnds`, fed by the
exponential decay `hdecU`), hence `Φm (Tt α ς) - Φm ς → -1/α`; but the contract's `FatouEnds`
threshold in its window `|z.re - x| ≤ 2` depends on the centre `x`, so the asymptotic cannot be
applied "at `Re ς`" uniformly over the unbounded region.  The fix is the walk
`Work.Pert.pert2v2.walk_to_window`: it carries *any* gate point of large height to a gate point of
`Re ∈ [-2, 2]` while preserving the drift `Φm - id` up to `1`.  Applying `FatouEnds` at the single
centre `x = 0` then pins the drift of both `ς` and `Tt α ς` to the same end constant `c` within
`2`, and the assembly
`Φm (Tt α ς) - Φm ς = (drift (Tt α ς) - c) - (drift ς - c) - 1/α`
gives the bound `‖1/α‖ + 4`.

Only `hF`, `hα`, `hQAdm`, `hNT`, `hΦm` and `hdecU` are used; `Φp`, `hrel` and the upper gate play
no role in this bound (they belong to the *limit* statement `R_close`, not to boundedness).
-/

namespace Work.Pert.pert2v2

/-- **Boundedness of the return translate in the waist.**  See the module docstring for the route. -/
theorem waist_return_bound_up {u : ℂ → ℂ} {σ α d : ℂ} {Ξ : ℝ} {F Φm Φp : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ) (hα : MandelDim.InF1 α)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hQAdmp : MandelDim.QAdm (some ((Ξ : ℂ))) (some (-(Ξ : ℂ) + 1 / α)))
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hNTp : MandelDim.NearTranslationL1 F (Work.Pert.Qp Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn F Φm (Work.Pert.Qm Ξ α))
    (hΦp : MandelDim.IsFatouCoordOn F Φp (Work.Pert.Qp Ξ α))
    (hrel : ∀ z ∈ Work.Pert.Qp Ξ α, Φm (Work.Pert.Tt α z) = Φp z + d)
    (hdecU : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y < z.im →
      ‖F z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im))) :
    ∃ K C : ℝ, ∀ ς : ℂ, |ς.re| + 2 < |ς.im| - Ξ → K ≤ ς.im →
      ‖Φm (Work.Pert.Tt α ς) - Φm ς‖ ≤ C := by
  obtain ⟨M, κ, Y, hM, hκ, hdec⟩ := hdecU
  -- `𝓕₁` is preserved, strictly, by inversion: the waist is the symmetric window
  have hF1 : |(1 / α).im| < (1 / α).re := Work.Pert.abs_im_one_div_lt_re_one_div hα
  -- the pointwise near-translation and the Abel relation of `Φm` on the lower gate
  have hntOn : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α) := hNT.1
  have habel : ∀ w ∈ Work.Pert.Qm Ξ α, F w ∈ Work.Pert.Qm Ξ α → Φm (F w) = Φm w + 1 :=
    hΦm.2.2
  -- the walk to the *fixed* window `|Re| ≤ 2`, preserving the drift `Φm - id` up to `1`
  obtain ⟨Kw, hKw⟩ := walk_to_window (Ξ := Ξ) (α := α) (F := F) (Φ := Φm)
    (M := M) (κ := κ) (Ydec := Y) hntOn habel hdec hM hκ
  -- the upper-end asymptotics of `Φm` *at the window* `|x| ≤ 2`, from the exponential decay
  obtain ⟨c, hc⟩ := (hF.2.2.2.2.2 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) F Φm 1 M κ Y
    hQAdm hntOn hΦm hκ (by norm_num)).1 hdec
  obtain ⟨Y', hY'⟩ := hc 0 1 (by norm_num)
  refine ⟨max Kw (Y' + 1) + |(1 / α).im| + 1, ‖1 / α‖ + 5, ?_⟩
  intro ς hreg hK
  -- the two points to compare: `ς` and its deck translate `Tt α ς = ς - 1/α`
  have hwa : ς ∈ Work.Pert.Qm Ξ α ∧ Work.Pert.Tt α ς ∈ Work.Pert.Qm Ξ α :=
    (Work.Pert.mem_waist_iff hF1).mpr (by linarith)
  obtain ⟨hz1, hz2⟩ := hwa
  have hTim : (Work.Pert.Tt α ς).im = ς.im - (1 / α).im := by
    simp only [Work.Pert.Tt, Complex.sub_im]
  -- heights: both are above the walk threshold and the asymptotic threshold
  have him1 : Kw ≤ ς.im := by
    have h1 : Kw ≤ max Kw (Y' + 1) := le_max_left _ _
    have h3 : 0 ≤ |(1 / α).im| := abs_nonneg _
    linarith
  have him2ge : max Kw (Y' + 1) + 1 ≤ (Work.Pert.Tt α ς).im := by
    rw [hTim]
    have h2 : (1 / α).im ≤ |(1 / α).im| := le_abs_self _
    linarith
  have him2 : Kw ≤ (Work.Pert.Tt α ς).im := by
    have h1 : Kw ≤ max Kw (Y' + 1) := le_max_left _ _
    linarith
  obtain ⟨z1', hz1'Q, hz1're, hz1'im, hz1'drift⟩ := hKw ς hz1 him1
  obtain ⟨z2', hz2'Q, hz2're, hz2'im, hz2'drift⟩ := hKw (Work.Pert.Tt α ς) hz2 him2
  have hY1 : Y' < z1'.im := by
    have h1 : Y' + 1 ≤ max Kw (Y' + 1) := le_max_right _ _
    have h3 : 0 ≤ |(1 / α).im| := abs_nonneg _
    linarith
  have hY2 : Y' < z2'.im := by
    have h1 : Y' + 1 ≤ max Kw (Y' + 1) := le_max_right _ _
    linarith
  -- the two window values, both within `1` of the end constant
  have hc1 : ‖(Φm z1' - z1') - c‖ < 1 := by
    have hre : |z1'.re - 0| ≤ 2 := by
      rw [sub_zero, abs_le]
      exact ⟨hz1're.1, hz1're.2⟩
    simpa using hY' z1' hz1'Q hY1 hre
  have hc2 : ‖(Φm z2' - z2') - c‖ < 1 := by
    have hre : |z2'.re - 0| ≤ 2 := by
      rw [sub_zero, abs_le]
      exact ⟨hz2're.1, hz2're.2⟩
    simpa using hY' z2' hz2'Q hY2 hre
  -- hence the drift `Φm - id` is within `2` of the end constant at both points
  have hdr1 : ‖(Φm ς - ς) - c‖ ≤ 2 := by
    have htri : ‖(Φm ς - ς) - c‖
        ≤ ‖(Φm ς - ς) - (Φm z1' - z1')‖ + ‖(Φm z1' - z1') - c‖ := by
      have h : (Φm ς - ς) - c = ((Φm ς - ς) - (Φm z1' - z1')) + ((Φm z1' - z1') - c) := by
        ring
      rw [h]
      exact norm_add_le _ _
    have heq : ‖(Φm ς - ς) - (Φm z1' - z1')‖ = ‖(Φm z1' - z1') - (Φm ς - ς)‖ := by
      have h : (Φm ς - ς) - (Φm z1' - z1') = -((Φm z1' - z1') - (Φm ς - ς)) := by ring
      rw [h, norm_neg]
    linarith [htri, heq, hz1'drift, hc1]
  have hdr2 : ‖(Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - c‖ ≤ 2 := by
    have htri : ‖(Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - c‖
        ≤ ‖(Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - (Φm z2' - z2')‖
          + ‖(Φm z2' - z2') - c‖ := by
      have h : (Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - c
          = ((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - (Φm z2' - z2'))
            + ((Φm z2' - z2') - c) := by ring
      rw [h]
      exact norm_add_le _ _
    have heq : ‖(Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - (Φm z2' - z2')‖
        = ‖(Φm z2' - z2') - (Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς)‖ := by
      have h : (Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - (Φm z2' - z2')
          = -((Φm z2' - z2') - (Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς)) := by ring
      rw [h, norm_neg]
    linarith [htri, heq, hz2'drift, hc2]
  -- assembly: the difference of two drifts, plus the deck translation `-1/α`
  have hkey : Φm (Work.Pert.Tt α ς) - Φm ς
      = ((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - c) - ((Φm ς - ς) - c) - 1 / α := by
    rw [show Work.Pert.Tt α ς = ς - 1 / α from by simp [Work.Pert.Tt]]
    ring
  calc ‖Φm (Work.Pert.Tt α ς) - Φm ς‖
      = ‖((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - c) - ((Φm ς - ς) - c) - 1 / α‖ := by
        rw [hkey]
    _ ≤ ‖((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - c) - ((Φm ς - ς) - c)‖ + ‖1 / α‖ :=
        norm_sub_le _ _
    _ ≤ (2 + 2) + ‖1 / α‖ := by
        have h := norm_sub_le ((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς) - c) ((Φm ς - ς) - c)
        linarith [h, hdr1, hdr2]
    _ ≤ ‖1 / α‖ + 5 := by linarith

end Work.Pert.pert2v2
