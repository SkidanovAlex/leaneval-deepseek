import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS.EllipticEst.EllGap.MLevelBookkeeping.mLevel_hasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SBpsiP.SelfUprime` — finite-order smoothness of the slot iterates

The `U`-slot `U'(Ψ) = U(Ψ)/sin 2θ` with `U(Ψ) = -3Ψ - αG·z∂_zΨ` is `C²` on the open quadrant
`Qd` as soon as `Ψ` is `C³` there (`∂_z` costs one order, the division by the nonvanishing
`sin 2θ` costs none), and each application of `D_z = z∂_z` costs one further order:

  `Ψ ∈ C³(Qd)  ⟹  D_z^j U'(Ψ) ∈ C^{2-j}(Qd)`,   `j ≤ 2`.

This is what turns the `SlotBd` hypotheses (continuity of `D_z^j U'(Ψ)`, `j ≤ 2`) into the
hypotheses of the differentiation identity `SBpsiP.J_Dz_eq`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SBpsiP

open Work.FTS.StreamBdryIface (Uprime)

set_option autoImplicit false

/-- `U'(Ψ)` is `C²` on the open quadrant for a `C³` `Ψ`. -/
theorem Uprime_contDiffOn_two {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.Construction.Qd := h3.of_le (by norm_num)
  have hpz : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Ψ)) Work.Construction.Qd :=
    Work.FTS.EllipticEst.EllGap.MLevelBookkeeping.contDiffOn_uncurry_pz_of_isOpen hQd h3
  have hnum : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      -3 * Function.uncurry Ψ p - αG * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Construction.Qd :=
    (contDiffOn_const.mul h2).sub ((contDiffOn_const.mul contDiff_fst.contDiffOn).mul hpz)
  have hden : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Construction.Qd :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hne : ∀ p ∈ Work.Construction.Qd, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    have hθ1 : 0 < p.2 := hp.2.1
    have hθ2 : p.2 < Real.pi / 2 := hp.2.2
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  refine (hnum.div hden hne).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry, Uprime, Work.Construction.Uop, Work.Construction.s2,
    Work.Spaces.pz, Pi.div_apply]

/-- `D_z U'(Ψ)` is `C¹` on the open quadrant. -/
theorem DzUprime_contDiffOn_one {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (Uprime αG Ψ))) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hU : ContDiffOn ℝ 2 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    Uprime_contDiffOn_two h3
  have hpz : ContDiffOn ℝ 1
      (Function.uncurry (Work.Spaces.pz (Uprime αG Ψ))) Work.Construction.Qd :=
    Work.FTS.EllipticEst.EllGap.MLevelBookkeeping.contDiffOn_uncurry_pz_of_isOpen hQd hU
  refine (contDiff_fst.contDiffOn.mul hpz).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rfl

/-- `D_z(D_z U'(Ψ))` is continuous on the open quadrant. -/
theorem Dz2Uprime_contDiffOn_zero {αG : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ContDiffOn ℝ 0
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz (Uprime αG Ψ))))
      Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hDz1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.Spaces.Dz (Uprime αG Ψ))) Work.Construction.Qd :=
    DzUprime_contDiffOn_one h3
  have hpz : ContDiffOn ℝ 0
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz (Uprime αG Ψ))))
      Work.Construction.Qd :=
    Work.FTS.EllipticEst.EllGap.MLevelBookkeeping.contDiffOn_uncurry_pz_of_isOpen hQd hDz1
  refine (contDiff_fst.contDiffOn.mul hpz).congr (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rfl

/-- **Finite-order smoothness of the slot iterates**: `D_z^j U'(Ψ) ∈ C^{2-j}` on `Qd`, `j ≤ 2`. -/
theorem UprimeIterSmooth_self {αG : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    ∀ j : ℕ, j ≤ 2 → ContDiffOn ℝ (2 - j)
      (Function.uncurry (Work.Spaces.DzIter j (Uprime αG Ψ))) Work.Construction.Qd := by
  have hU := Uprime_contDiffOn_two (αG := αG) h3
  have hDz1 := DzUprime_contDiffOn_one (αG := αG) h3
  have hDz2 := Dz2Uprime_contDiffOn_zero (αG := αG) h3
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact hU
  · exact hDz1
  · exact hDz2

end Work.FTS_StreamBdry.SBpsiP
