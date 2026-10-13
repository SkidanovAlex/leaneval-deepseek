import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.bslOp_div_s2_hasDerivAt
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.uprime_le` — `∂_θ (psiP αG Ψ / sin 2θ)` is bounded on the quadrant

The object `u := psiP αG Ψ / sin 2θ` is the `U`-slot part of the stream function divided by
`sin 2θ`.  By the elliptic law for `psiP` (`SB3.P2Aux.bslOp_div_s2_hasDerivAt`) it solves the
singular second-order ODE

  `u'' + (4 cos 2θ / sin 2θ - tan θ) u' = -(α² D_z² u + 5 α D_z u) - F/sin 2θ`

on the open quadrant.  The right hand side is controlled by `|F| ≤ Mf` and `|D_z^j u| ≤ M`
(`j ≤ 2`, from `SB3.psiP_DzLe`), and the derivative itself by `|∂_θ psiP| ≤ K'`
(`SB3.pth_DzIter_le`) through `sin 2θ · u' = ∂_θ psiP - 2 cos 2θ · u`.  The abstract
singular-ODE bound `UprimeAux.ode_deriv_bound_fam` then gives the result.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The `θ`-identity `sin 2θ · u' = ∂_θ psiP - 2 cos 2θ · u`. -/
lemma s2_mul_u1 {αG : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hCt : ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ))
    (hsne : Work.Construction.s2 θ ≠ 0) :
    Work.Construction.s2 θ * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ
      = deriv (fun θ' => psiP αG Ψ z θ') θ
        - 2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ) := by
  have hslice : ContDiffAt ℝ 2 (fun θ' => psiP αG Ψ z θ') θ := by
    have h2 := hCt.comp θ (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
    convert h2 using 1
    funext x; rfl
  have hP : HasDerivAt (fun θ' => psiP αG Ψ z θ') (deriv (fun θ' => psiP αG Ψ z θ') θ) θ :=
    (hslice.differentiableAt (by norm_num)).hasDerivAt
  have hs : HasDerivAt (fun θ' : ℝ => Work.Construction.s2 θ') (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have h3 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rw [h3] at h2
    exact h2
  have hdiv := hP.div hs hsne
  have hf : ((fun θ' => psiP αG Ψ z θ') / (fun θ' => Work.Construction.s2 θ'))
      = (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') := by
    funext x; rfl
  have hval : deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ
      = (deriv (fun θ' => psiP αG Ψ z θ') θ * Work.Construction.s2 θ
          - psiP αG Ψ z θ * (2 * Real.cos (2 * θ))) / Work.Construction.s2 θ ^ 2 := by
    have h := hdiv.deriv
    rw [hf] at h
    exact h
  rw [hval]
  field_simp
  try ring

/-- The `θ`-slice of `psiP αG Ψ / sin 2θ`, as a two-variable function. -/
abbrev ufun (αG : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  psiP αG Ψ z θ / Work.Construction.s2 θ

theorem uprime_le {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf) :
    ∃ K : ℝ, 0 < K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |deriv (fun θ' => Work.FTS.StreamBdryIface.psiP αG Ψ z θ'
        / Work.Construction.s2 θ') θ| ≤ K := by
  have hQdopen : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB3.P2Aux.isOpen_Qd_asm
  have hC3 : ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.P2Aux.psiP_c3 hαG h3 hslot
  have hslaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ :=
    Work.FTS_StreamBdry.SB3.P2Aux.bslOp_psiP hαG hsol h3 hslot
  have hCt2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ) := fun z θ hmem =>
    (hC3.contDiffAt (hQdopen.mem_nhds hmem)).of_le (by norm_num)
  have hode0 := Work.FTS_StreamBdry.SB3.P2Aux.bslOp_div_s2_hasDerivAt
    (α := αG) (Q := psiP αG Ψ) (F := F) hCt2 hslaw
  -- the membership witness `(1, π/4) ∈ Qd`
  have hmem0 : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd := by
    rw [Work.FTS_StreamBdry.mem_Qd]
    exact ⟨by norm_num, by positivity, by linarith [Real.pi_pos]⟩
  have hM_nonneg : 0 ≤ M := by
    have h := (hslot 1 (Real.pi / 4) hmem0).1 0 (by norm_num)
    rw [Work.Spaces.DzIter_zero] at h
    exact le_trans (abs_nonneg _) h
  have hMf_nonneg : 0 ≤ Mf := by
    have h1 : |F 1 0| ≤ Mf :=
      (hF.2.2.1 1 0 (by norm_num) ⟨le_refl (0 : ℝ), by positivity⟩).1
    have h2 : F 1 0 = 0 := (hF.2.2.2.1 1 (by norm_num)).1
    rw [h2, abs_zero] at h1
    exact h1
  -- the `D_z`-bounds on `u`
  have hdiv := Work.FTS_StreamBdry.SB3.P2Aux.div_identities (P := psiP αG Ψ) hC3
  have hDzLe : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
    fun z θ hmem => (Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot) z θ hmem
  have huDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M := by
    intro z θ hmem j hj
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have h := hdiv.1 z θ hmem j (by omega)
    rw [h, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    exact hDzLe z θ hmem j hj
  -- the `H` of the abstract ODE bound
  have hH : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |-(F z θ) / Work.Construction.s2 θ
        - (αG ^ 2 * Work.Spaces.DzIter 2
            (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
          + 5 * αG * Work.Spaces.Dz
            (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)|
        ≤ Mf / Work.Construction.s2 θ + (αG ^ 2 * M + 5 * αG * M) := by
    intro z θ hmem
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hFle : |F z θ| ≤ Mf :=
      (hF.2.2.1 z θ (Work.FTS_StreamBdry.Qd_pos hmem) (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)).1
    have h1 : |Work.Spaces.DzIter 2
        (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M :=
      huDz z θ hmem 2 (by norm_num)
    have h2 : |Work.Spaces.Dz
        (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ M :=
      huDz z θ hmem 1 (by norm_num)
    have habs : |F z θ / Work.Construction.s2 θ| ≤ Mf / Work.Construction.s2 θ := by
      rw [abs_div, abs_of_pos hsp]
      exact div_le_div_of_nonneg_right hFle hsp.le
    have h4 : |αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        + 5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ αG ^ 2 * M + 5 * αG * M := by
      refine (abs_add_le _ _).trans ?_
      have ha : |αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ αG ^ 2 * M := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ αG ^ 2)]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hb : |5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ| ≤ 5 * αG * M := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 5 * αG)]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
    have heq : -(F z θ) / Work.Construction.s2 θ
          - (αG ^ 2 * Work.Spaces.DzIter 2
              (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
            + 5 * αG * Work.Spaces.Dz
              (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)
        = -((F z θ / Work.Construction.s2 θ)
            + (αG ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
              + 5 * αG * Work.Spaces.Dz
                (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)) := by ring
    rw [heq, abs_neg]
    exact (abs_add_le _ _).trans (add_le_add habs h4)
  -- the crude bound on `u'`
  have hSg : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ max M (2 * M / αG) * Work.Construction.s2 θ := by
    intro z θ hmem j hj
    have hsp : 0 ≤ Work.Construction.s2 θ := le_of_lt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
    rcases (by omega : j ≤ 2 ∨ j = 3) with hj2 | hj3
    · have h := hDzLe z θ hmem j hj2
      have hMM : M ≤ max M (2 * M / αG) := le_max_left _ _
      nlinarith [h, hMM, hsp]
    · subst hj3
      have h := Work.FTS_StreamBdry.SB3.psiP_D3_le hαG h3 hslot z θ hmem
      have hMM : 2 * M / αG ≤ max M (2 * M / αG) := le_max_right _ _
      nlinarith [h, hMM, hsp]
  obtain ⟨Kp, hKp⟩ := Work.FTS_StreamBdry.SB3.pth_DzIter_le (Sg := max M (2 * M / αG))
    hαG h3 hslot hSg
  have hcrude : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.s2 θ
        * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ| ≤ Kp + 2 * M := by
    intro z θ hmem
    have hsp : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hsne : Work.Construction.s2 θ ≠ 0 := ne_of_gt hsp
    have hid : Work.Construction.s2 θ
          * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ
        = deriv (fun θ' => psiP αG Ψ z θ') θ
          - 2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ) :=
      s2_mul_u1 (hCt := hCt2 z θ hmem) hsne
    have h1 : |deriv (fun θ' => psiP αG Ψ z θ') θ| ≤ Kp := hKp z θ hmem 0 (by norm_num)
    have h2 : |psiP αG Ψ z θ / Work.Construction.s2 θ| ≤ M := by
      rw [abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
      exact hDzLe z θ hmem 0 (by norm_num)
    have h3 : |2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ)| ≤ 2 * M := by
      have hc : |Real.cos (2 * θ)| ≤ 1 := by
        rw [abs_le]
        exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have h1 : |2 * Real.cos (2 * θ)| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        linarith [hc]
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    calc |Work.Construction.s2 θ
          * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ|
        = |deriv (fun θ' => psiP αG Ψ z θ') θ
            - 2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ)| := by rw [hid]
      _ ≤ |deriv (fun θ' => psiP αG Ψ z θ') θ|
            + |2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ)| := by
          simpa using abs_sub_le (deriv (fun θ' => psiP αG Ψ z θ') θ) 0
            (2 * Real.cos (2 * θ) * (psiP αG Ψ z θ / Work.Construction.s2 θ))
      _ ≤ Kp + 2 * M := add_le_add h1 h3
  -- the ODE in the exact shape of `ode_deriv_bound_fam`
  have hode : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ'))
        ((fun z θ => -(F z θ) / Work.Construction.s2 θ
            - (αG ^ 2 * Work.Spaces.DzIter 2
                (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
              + 5 * αG * Work.Spaces.Dz
                (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ)) z θ
          - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
            * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ) θ := by
    intro z θ hmem
    refine (hode0 z θ hmem).congr_deriv ?_
    ring
  -- assemble
  have hKp_nonneg : 0 ≤ Kp := le_trans (abs_nonneg _) (hKp 1 (Real.pi / 4) hmem0 0 (by norm_num))
  have hC_nonneg : 0 ≤ αG ^ 2 * M + 5 * αG * M := by nlinarith [hM_nonneg, hαG]
  have hC1_nonneg : 0 ≤ Kp + 2 * M := by linarith [hKp_nonneg, hM_nonneg]
  obtain ⟨K, hK0, hK⟩ := Work.FTS_StreamBdry.SB6.UprimeAux.ode_deriv_bound_fam
    (u := fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ)
    (H := fun z θ => -(F z θ) / Work.Construction.s2 θ
      - (αG ^ 2 * Work.Spaces.DzIter 2
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ
        + 5 * αG * Work.Spaces.Dz
          (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ))
    hMf_nonneg hC_nonneg hC1_nonneg hode
    (fun z θ hmem => hH z θ hmem) hcrude
  exact ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z θ hmem => by
    have h := hK z θ hmem
    exact le_trans h (le_max_left _ _)⟩

end Work.FTS_StreamBdry.SB6
