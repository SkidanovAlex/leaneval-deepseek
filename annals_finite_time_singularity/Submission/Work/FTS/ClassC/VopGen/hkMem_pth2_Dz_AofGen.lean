import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.FTS.EllipticEst.Prop.aslotTwoShift
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.Cores.HonSlot
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.VopGen

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# `hkMem_pth2_Dz_AofGen` — the honesty of `∂_θ²(D_z(z²∂_z²Ψ))` for a level-`2` weak datum

The target is `HkMem α 0 (∂_θ² D_z (Aof Ψ))` for every datum of the weak class
`TT.EllWeakPos α 2 F Ψ` (`Aof Ψ = z²∂_z²Ψ`).  This is the `∂_θ²`-slot honesty consumed by the
angular `(1,1)`-step of the `A`-slot chain (`Cores/ASlot11Aux/CoreASlot11.lean`: the clause
`∫_θ (∂_θ² X)² σ_η < ∞` for `X = D_z(Aof Ψ)`), and it is the angular companion of the already
proved `Prop.hkMem_zero_Dz_Aof` (`HkMem α 0 (D_z(Aof Ψ))`).

## Route

Write `B := ∂_θ²Ψ`.  On the open quadrant

* `∂_θ²(D_z(Aof Ψ)) = D_z(∂_θ²(Aof Ψ))` (Clairaut: `∂_θ²` commutes with `D_z = z∂_z`,
  `AeDataAofAux.pz_pthIter_comm_Q0`, after moving the constant-in-`θ` factor `z` out of the
  `θ`-derivative, `AeDataAofAux.pthIter_fst_mul`);
* `∂_θ²(Aof Ψ) = z²∂_z²(∂_θ²Ψ) = z²∂_z²B` (`AeDataAofAux.pthIter_two_zsq_pzIter2_eq`);
* `z²∂_z²B = D_z²B − D_zB` (`AeDataAofAux.zsq_pzIter2_eq_open`), so that by the linearity of
  `D_z` on a difference (`DzAmgm.Q0_pz_sub`)

  `∂_θ²(D_z(Aof Ψ)) = D_z(D_z²B − D_zB) = D_z³B − D_z²B`  on the open quadrant.

The two summands are honest at order `0`: `D_z²B` from the pure slot `i = 2` of `HkMem α 2 B`
(`h.memB`) and `D_z³B = D_z²(D_zB)` from the pure slot `i = 2` of `HkMem α 2 (D_zB)`
(`h.memZPth2`), both by the slot extraction `Cores.HkMem_zero_of_DzIter_slot`; a sum of two
honest functions is honest (`HkMem_add_open`, `LocData.HkMem_const_mul` for the sign), and the
transfer to the target function is the open-quadrant congruence `Cert.GbarSin.HkMem_congr_Q0`.
-/

/-- **The `ℋ⁰`-honesty of `∂_θ²(D_z(z²∂_z²Ψ))`** for a level-`2` weak datum. -/
theorem hkMem_pth2_Dz_AofGen {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.Spaces.HkMem α 0 (fun z θ => Work.Spaces.pthIter 2
      (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_pthIter hΨ 2
  have hA : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Aof Ψ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨ.pzIter 2)
  -- the pointwise identity `∂_θ²(D_z(Aof Ψ)) = D_z³B − D_z²B` on the open quadrant
  have key : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter 3 (Work.Spaces.pthIter 2 Ψ) z θ
        - Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ := by
    intro z hz θ hθ
    have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
    -- § the constant-in-`θ` factor `z` leaves the `θ`-derivative
    have h1 : Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ
        = z * Work.Spaces.pthIter 2 (Work.Spaces.pz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ := by
      have hr : Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))
          = fun z θ => z * Work.Spaces.pthIter 2
              (Work.Spaces.pz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ := by
        change Work.Spaces.pthIter 2
            (fun z θ => z * Work.Spaces.pz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ)
          = fun z θ => z * Work.Spaces.pthIter 2
              (Work.Spaces.pz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ
        exact Work.FTS.EllipticEst.H2W.AeDataAofAux.pthIter_fst_mul (fun y : ℝ => y)
          (Work.Spaces.pz (Work.FTS.EllipticEst.H2W.Aof Ψ)) 2
      rw [hr]
    -- § Clairaut: `∂_θ²∂_z = ∂_z∂_θ²`
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.pz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ :=
      (Work.FTS.EllipticEst.H2W.AeDataAofAux.pz_pthIter_comm_Q0 hA 2 hpt).symm
    -- § `∂_θ²(z²∂_z²Ψ) = z²∂_z²(∂_θ²Ψ)`
    have h3 : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ
        = Work.Spaces.pz (fun z θ => z ^ 2
            * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ) z θ := by
      refine Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 (fun q hq => ?_) hpt
      obtain ⟨hz', hθa, hθb⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      exact Work.FTS.EllipticEst.H2W.AeDataAofAux.pthIter_two_zsq_pzIter2_eq hΨ hz' ⟨hθa, hθb⟩
    -- § `z²∂_z²B = D_z²B − D_zB`
    have h4 : Work.Spaces.pz (fun z θ => z ^ 2
          * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ) z θ
        = Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
            - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) z θ := by
      refine Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 (fun q hq => ?_) hpt
      obtain ⟨hz', hθa, hθb⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      exact Work.FTS.EllipticEst.H2W.AeDataAofAux.zsq_pzIter2_eq_open hB hz' ⟨hθa, hθb⟩
    -- § linearity of `∂_z` on a difference
    have h5 : Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
          - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
          - Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.FTS.EllipticEst.DzAmgm.Q0_pz_sub
        (Work.FTS.EllipticEst.DzAmgm.differentiableAt_slice_z_of (hB.DzIter 2) hz hθ)
        (Work.FTS.EllipticEst.DzAmgm.differentiableAt_slice_z_of (hB.DzIter 1) hz hθ)
    rw [h1, h2, h3, h4, h5]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    ring
  -- § the two honest summands
  have hY : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.Cores.HkMem_zero_of_DzIter_slot (α := α) (k := 2) (i := 2)
      le_rfl hB h.memB
  have hX : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 3 (Work.Spaces.pthIter 2 Ψ)) := by
    have hZ : Work.Spaces.HkMem α 2 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) := by
      change Work.Spaces.HkMem α 2
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
      exact h.memZPth2
    have h' := Work.FTS.EllipticEst.Cores.HkMem_zero_of_DzIter_slot (α := α) (k := 2) (i := 2)
      le_rfl (hB.Dz) hZ
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h'
  -- § closure under the difference
  have hsum : Work.Spaces.HkMem α 0 (fun z θ =>
      Work.Spaces.DzIter 3 (Work.Spaces.pthIter 2 Ψ) z θ
      + (-1) * Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open (hB.DzIter 3)
      (Work.FTS.EllipticEst.SmoothOpen.const_mul' (-1) (hB.DzIter 2)) hX
      (Work.FTS.LocData.HkMem_const_mul α 0 (-1) hY)
  have hu : Work.Spaces.HkMem α 0 (fun z θ =>
      Work.Spaces.DzIter 3 (Work.Spaces.pthIter 2 Ψ) z θ
      - Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hsum (fun z _ θ _ => by ring)
  -- § transfer to the target along the open-quadrant identity `key`
  exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hu key

end Work.FTS.ClassC.VopGen
