import Mathlib
import Submission.Work.Pert.pert2v2.high_piece_data

namespace Work.Pert.pert2v2

/-- **The high piece of the two-piece glue, with an arbitrary half-width `R1`.**  This is
`Work.Pert.pert2v2.high_piece_data` with the window `{|Re w| < 1/2}` widened to `{|Re w| < R1}`:
the openness argument never uses the value `1/2`, only that the window is open, and the holomorphy
of `retOf` holds on the whole of `Φ '' (Qm Ξ α ∩ Qp Ξ α)`.

* First conjunct: `Qm Ξ α`, `Qp Ξ α` are open (`Work.Fatou.Qreg.isOpen_Qreg` and
  `Work.Pert.RBlock4.isOpen_Qm`), hence so is their intersection and — by
  `Work.Pert.pert2v2.isOpen_image_of_open` (holomorphic `Φ` with `deriv Φ ≠ 0`) — its image under
  `Φ`; intersect with the open strip `{|Re| < R1 ∧ Tb < |Im|}` (open for any real `R1`, `Tb`).
* Second conjunct: `Work.Pert.RBlock4.retOf_holo` gives
  `DifferentiableOn ℂ (retOf Φ (Qm Ξ α) α) (Φ '' (Qm Ξ α ∩ Qp Ξ α))` from the three hypotheses
  verbatim; restrict to the (smaller) window by `DifferentiableOn.mono`. -/
theorem high_piece_data_wide {Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Tb R1 : ℝ}
    (hΦm : DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α))
    (hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α))
    (hder : ∀ z ∈ Work.Pert.Qm Ξ α, deriv Φ z ≠ 0) :
    IsOpen ({w : ℂ | |w.re| < R1 ∧ Tb < |w.im|} ∩
        Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)) ∧
      DifferentiableOn ℂ (Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α)
        ({w : ℂ | |w.re| < R1 ∧ Tb < |w.im|} ∩
          Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)) := by
  -- the open window `{|Re w| < R1, Tb < |Im w|}`
  have hstrip : IsOpen {w : ℂ | |w.re| < R1 ∧ Tb < |w.im|} :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im.abs)
  -- the two gates are open, hence so is their intersection and its image under `Φ`
  have hQp : IsOpen (Work.Pert.Qp Ξ α) := by
    unfold Work.Pert.Qp
    exact Work.Fatou.Qreg.isOpen_Qreg _ _
  have hII : IsOpen (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) :=
    (Work.Pert.RBlock4.isOpen_Qm Ξ α).inter hQp
  have himg : IsOpen (Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)) :=
    isOpen_image_of_open (Work.Pert.RBlock4.isOpen_Qm Ξ α) hΦm hder hII Set.inter_subset_left
  refine ⟨hstrip.inter himg, ?_⟩
  exact (Work.Pert.RBlock4.retOf_holo hΦm hinj hder).mono Set.inter_subset_right

end Work.Pert.pert2v2
