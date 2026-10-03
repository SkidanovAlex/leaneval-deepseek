import Mathlib
import Submission.Work.Pert.pert2v2.HsegRow
import Submission.Work.Pert.pert2v2.EfFloorDiffV2.EfFloor_sub_id_differentiableOn
import Submission.Work.Pert.pert2v2.HdiffRow.EfFloor_sub_id_differentiableOn_Qp
import Submission.Work.Pert.pert2v2.EfFloor

/-!
# `Work.Pert.pert2v2.HdiffRow.EfFloor_hdiff_of_step`

The `hdiff` input of the (A.4.4) row `pert2v2.a44_row`: differentiability of the floor-based
`ℤ`-extension `EfFloor Φm Φp Q - id` on the band `{y ≤ Im}`.

The two ingredients:

* `HsegRow.herb1_hlvl_of_step` turns **one legal walk step** of the gate
  (`F (invOn Φm Q u) ∈ Q ∩ Qp`, with `Φm (F z) = Φm z + 1` and `Φp (F z) = Φp z + 1`) into
  * the honest level-`1` cover `herb1` (`u + 1 ∈ Φm '' Q` for the canonical representative `u`),
  * the level-`1` value relation `hlvl` (`Φp` of the preimage of `u + 1` is `Φp` of the preimage
    of `u` plus `1`);

* `EfFloor_sub_id_differentiableOn_Qp` is the analytic core with `Φp` only known to be holomorphic
  on the second open set `Qp`: the walk hypotheses also say that the relevant preimages
  `invOn Φm Q u` and `invOn Φm Q (u+1)` lie in `Qp` (`hQp0 = hςP`, and `hQp1` from `hstepP`
  plus `habQ`, since `Φm (F ς) = u + 1` pins the chosen preimage of `u + 1` to `F ς`).
-/

namespace Work.Pert.pert2v2.HdiffRow

theorem EfFloor_hdiff_of_step {Q Qp : Set ℂ} {Φm Φp F : ℂ → ℂ} {y : ℝ}
    (hQopen : IsOpen Q) (hQpopen : IsOpen Qp)
    (hΦm : DifferentiableOn ℂ Φm Q) (hder : ∀ z ∈ Q, deriv Φm z ≠ 0)
    (hInj : Set.InjOn Φm Q) (hΦp : DifferentiableOn ℂ Φp Qp)
    (herb : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Q)
    (hstep : ∀ w : ℂ, y ≤ w.im →
      F (Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ))) ∈ Q)
    (habQ : ∀ z ∈ Q, F z ∈ Q → Φm (F z) = Φm z + 1)
    (hςP : ∀ w : ℂ, y ≤ w.im → Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ)) ∈ Qp)
    (hstepP : ∀ w : ℂ, y ≤ w.im →
      F (Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ))) ∈ Qp)
    (habP : ∀ z ∈ Qp, F z ∈ Qp → Φp (F z) = Φp z + 1) :
    DifferentiableOn ℂ (fun w : ℂ => Work.Pert.pert2v2.EfFloor Φm Φp Q w - w)
      {w : ℂ | y ≤ w.im} := by
  -- the honest level-`1` cover and the level-`1` value relation, from one legal walk step
  obtain ⟨herb1, hlvl⟩ :=
    herb1_hlvl_of_step hInj habQ hstep habP hςP hstepP herb
  -- the chosen preimage of the shifted representative lies in `Qp`: it is the walk image
  have hQp1 : ∀ w : ℂ, y ≤ w.im →
      Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1) ∈ Qp := by
    intro w hw
    set ς := Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ)) with hς
    have hmem : w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Q := herb w hw
    have hςQ : ς ∈ Q := Work.Pert.invOn_mem hmem
    have hςΦ : Φm ς = w - (((⌊w.re⌋ : ℤ)) : ℂ) := Work.Pert.invOn_spec hmem
    have hFQ : F ς ∈ Q := hstep w hw
    have hFΦ : Φm (F ς) = w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1 := by rw [habQ ς hςQ hFQ, hςΦ]
    have hinv : Work.Pert.invOn Φm Q (w - (((⌊w.re⌋ : ℤ)) : ℂ) + 1) = F ς :=
      Work.Pert.invOn_eq hInj ⟨F ς, hFQ, hFΦ⟩ hFQ hFΦ
    rw [hinv]
    exact hstepP w hw
  exact EfFloor_sub_id_differentiableOn_Qp hQopen hQpopen hΦm hder hInj hΦp
    herb herb1 hlvl hςP hQp1

end Work.Pert.pert2v2.HdiffRow
