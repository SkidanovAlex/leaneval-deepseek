import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.bslOp_div_s2_hasDerivAt
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.pthIter2_eq
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.bslOp_Dz_comm
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.fam_ode_deriv_bound_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.pthIter2_le` — the second `θ`-derivative of the `U`-slot part

`|∂_θ² (D_z^j (psiP αG Ψ))| ≤ K` on the open quadrant, for `j ≤ 1`, under `IsBslSolPos`,
`C³`-regularity of `Ψ`, the slot bounds `SlotBd` and the source facts `SrcOK`.

The route.  Write `P = psiP αG Ψ` and `u = P/s2`.  The `D_z`-bounds `|D_z^jP| ≤ K s2` (`j ≤ 3`)
give `|D_z^j u| ≤ K` (the division identities `P2Aux.div_identities`), and the elliptic law
`bslOp αG P = F` (`P2Aux.bslOp_psiP`, from the SB1′ gauge decomposition) turns into the singular
second-order ODE `u'' + c u' = -F/s2 - (αG²D_z²u + 5αG D_zu)` with
`c = 4cos2θ/sin2θ - tanθ` (`P2Aux.bslOp_div_s2_hasDerivAt`), whose weighted first-order bound is
`P2Aux.fam_ode_deriv_bound`.  The explicit formula
`∂_θ²P = -4 s2 u + 2 sin²θ u' - F - s2(αG²D_z²u + 5αG D_zu)` (`P2Aux.pthIter2_eq`) then bounds
`∂_θ²P` by `4M + 2K + Mf + (αG²M + 5αG M)`.  The `j = 1` case repeats the same argument for
`Q = D_zP`, `F ↦ D_zF` (`P2Aux.bslOp_Dz_comm`, `P2Aux.div_identities`).
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB3

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP gaugeMode)
open Work.FTS_StreamBdry.SB3.P2Aux


theorem pthIter2_le_reproved {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf) :
    ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ∀ j ≤ 1, |Work.Spaces.pthIter 2 (Work.Spaces.DzIter j
        (Work.FTS.StreamBdryIface.psiP αG Ψ)) z θ| ≤ K := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd_asm
  have hQdpt : ((1 : ℝ), π / 4) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr
      ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hMnn : 0 ≤ M :=
    le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SlotBd.Uprime_le hslot hQdpt)
  have hMfnn : 0 ≤ Mf := by
    have hθ : (π / 4 : ℝ) ∈ Work.Spaces.Iθ :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SrcOK.F_le hF (z := 1) (by norm_num) hθ)
  have hDz2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
    fun z θ h j hj => Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z θ h j hj
  have hDz3 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 3 (psiP αG Ψ) z θ| ≤ (2 * M / αG) * Work.Construction.s2 θ :=
    fun z θ h => Work.FTS_StreamBdry.SB3.psiP_D3_le hαG h3 hslot z θ h
  have hPc2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hPc3 : ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    psiP_c3 hαG h3 hslot
  have hDzP_c2 : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dz (psiP αG Ψ))) Work.Construction.Qd :=
    Dz_smooth_of hV hPc3
  have hCtP : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ) :=
    fun z θ h => hPc2.contDiffAt (hV.mem_nhds h)
  have hCtQ1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.Dz (psiP αG Ψ))) (z, θ) :=
    fun z θ h => hDzP_c2.contDiffAt (hV.mem_nhds h)
  have hsliceP : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun θ' => psiP αG Ψ z θ') θ := fun z θ h =>
    Work.Spaces.differentiableAt_curry_right ((hCtP z θ h).differentiableAt (by norm_num))
  have hsliceQ1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun θ' => Work.Spaces.Dz (psiP αG Ψ) z θ') θ := fun z θ h =>
    Work.Spaces.differentiableAt_curry_right ((hCtQ1 z θ h).differentiableAt (by norm_num))
  have hlawP : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ := bslOp_psiP hαG hsol h3 hslot
  have hlawDzP : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (Work.Spaces.Dz (psiP αG Ψ)) z θ = Work.Spaces.Dz F z θ := by
    intro z θ hmem
    rw [bslOp_Dz_comm hmem (hPc3.contDiffAt (hV.mem_nhds hmem))]
    show z * Work.Spaces.pz (Work.Elliptic.bslOp αG (psiP αG Ψ)) z θ
      = z * Work.Spaces.pz F z θ
    congr 1
    have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Work.Construction.Qd :=
      (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hmem)
    have hev : (fun z' => Work.Elliptic.bslOp αG (psiP αG Ψ) z' θ) =ᶠ[𝓝 z]
        (fun z' => F z' θ) := by
      filter_upwards [hnb] with z' hz'
      exact hlawP z' θ hz'
    show deriv (fun z' => Work.Elliptic.bslOp αG (psiP αG Ψ) z' θ) z
      = deriv (fun z' => F z' θ) z
    rw [hev.deriv_eq]
  have hFb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |F z θ| ≤ Mf := by
    intro z θ hmem
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
    exact Work.FTS_StreamBdry.SrcOK.F_le hF hz ⟨le_of_lt hθ1, le_of_lt hθ2⟩
  have hDzFb : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.Dz F z θ| ≤ Mf := by
    intro z θ hmem
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
    exact Work.FTS_StreamBdry.SrcOK.Dz_le hF hz ⟨le_of_lt hθ1, le_of_lt hθ2⟩
  have hdiv := div_identities (P := psiP αG Ψ) hPc3
  have hC1nn : 0 ≤ αG ^ 2 * M + 5 * αG * M := by
    have h1 : 0 ≤ αG ^ 2 * M := mul_nonneg (by positivity) hMnn
    have h2 : 0 ≤ 5 * αG * M := mul_nonneg (by positivity) hMnn
    linarith
  have hC2nn : 0 ≤ αG ^ 2 * (2 * M / αG) + 5 * αG * M := by
    have h1 : 0 ≤ αG ^ 2 * (2 * M / αG) := mul_nonneg (by positivity) (by positivity)
    have h2 : 0 ≤ 5 * αG * M := mul_nonneg (by positivity) hMnn
    linarith
  -- `u = psiP/s2` bounds
  have hub : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |psiP αG Ψ z θ / Work.Construction.s2 θ| ≤ M := fun z θ h =>
    abs_div_s2_le_of (Work.FTS_StreamBdry.s2_pos_of_Qd h) (hDz2 z θ h 0 (by norm_num))
  have hu1b : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 1 (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ M := by
    intro z θ h
    rw [hdiv.1 z θ h 1 (by norm_num)]
    exact abs_div_s2_le_of (Work.FTS_StreamBdry.s2_pos_of_Qd h) (hDz2 z θ h 1 (by norm_num))
  have hu2b : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ M := by
    intro z θ h
    rw [hdiv.1 z θ h 2 (by norm_num)]
    exact abs_div_s2_le_of (Work.FTS_StreamBdry.s2_pos_of_Qd h) (hDz2 z θ h 2 (by norm_num))
  have hu3b : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 3 (fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ) z θ|
        ≤ 2 * M / αG := by
    intro z θ h
    rw [hdiv.1 z θ h 3 (by norm_num)]
    exact abs_div_s2_le_of (Work.FTS_StreamBdry.s2_pos_of_Qd h) (hDz3 z θ h)
  -- `u₁ = (D_z psiP)/s2` bounds
  have hq1b : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.Dz (psiP αG Ψ) z θ / Work.Construction.s2 θ| ≤ M := fun z θ h =>
    abs_div_s2_le_of (Work.FTS_StreamBdry.s2_pos_of_Qd h) (hDz2 z θ h 1 (by norm_num))
  have hq1u1b : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 1 (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
        / Work.Construction.s2 θ) z θ| ≤ M := by
    intro z θ h
    rw [hdiv.2 z θ h 1 (by norm_num)]
    exact abs_div_s2_le_of (Work.FTS_StreamBdry.s2_pos_of_Qd h) (hDz2 z θ h 2 (by norm_num))
  have hq1u2b : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 2 (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
        / Work.Construction.s2 θ) z θ| ≤ 2 * M / αG := by
    intro z θ h
    rw [hdiv.2 z θ h 2 (by norm_num)]
    exact abs_div_s2_le_of (Work.FTS_StreamBdry.s2_pos_of_Qd h) (hDz3 z θ h)
  -- the ODEs
  have hode : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ'))
        ((-(F z θ) / Work.Construction.s2 θ
            - (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ
                  / Work.Construction.s2 θ) z θ
              + 5 * αG * Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ
                  / Work.Construction.s2 θ) z θ))
          - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
              * deriv (fun θ' => psiP αG Ψ z θ' / Work.Construction.s2 θ') θ) θ :=
    fun z θ h => (bslOp_div_s2_hasDerivAt (α := αG) hCtP hlawP z θ h).congr_deriv (by ring)
  have hode1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => Work.Spaces.Dz (psiP αG Ψ) z θ'
          / Work.Construction.s2 θ'))
        ((-(Work.Spaces.Dz F z θ) / Work.Construction.s2 θ
            - (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
                  / Work.Construction.s2 θ) z θ
              + 5 * αG * Work.Spaces.Dz (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
                  / Work.Construction.s2 θ) z θ))
          - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
              * deriv (fun θ' => Work.Spaces.Dz (psiP αG Ψ) z θ'
                  / Work.Construction.s2 θ') θ) θ :=
    fun z θ h => (bslOp_div_s2_hasDerivAt (α := αG) hCtQ1 hlawDzP z θ h).congr_deriv (by ring)
  -- `H` bounds
  have hHbound : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |-(F z θ) / Work.Construction.s2 θ
        - (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ
              / Work.Construction.s2 θ) z θ
          + 5 * αG * Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ
              / Work.Construction.s2 θ) z θ)|
        ≤ Mf / Work.Construction.s2 θ + (αG ^ 2 * M + 5 * αG * M) := by
    intro z θ hmem
    have hsp := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hA : |-(F z θ) / Work.Construction.s2 θ| ≤ Mf / Work.Construction.s2 θ := by
      rw [abs_div, abs_neg, abs_of_pos hsp]
      exact div_le_div_of_nonneg_right (hFb z θ hmem) (le_of_lt hsp)
    have hB := abs_comb_le_of hαG (hu2b z θ hmem) (hu1b z θ hmem)
    calc |-(F z θ) / Work.Construction.s2 θ
          - (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ
                / Work.Construction.s2 θ) z θ
            + 5 * αG * Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ
                / Work.Construction.s2 θ) z θ)|
        ≤ |-(F z θ) / Work.Construction.s2 θ|
          + |αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ
                / Work.Construction.s2 θ) z θ
            + 5 * αG * Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ
                / Work.Construction.s2 θ) z θ| := abs_sub _ _
      _ ≤ Mf / Work.Construction.s2 θ + (αG ^ 2 * M + 5 * αG * M) := add_le_add hA hB
  have hHboundQ : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |-(Work.Spaces.Dz F z θ) / Work.Construction.s2 θ
        - (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
              / Work.Construction.s2 θ) z θ
          + 5 * αG * Work.Spaces.Dz (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
              / Work.Construction.s2 θ) z θ)|
        ≤ Mf / Work.Construction.s2 θ + (αG ^ 2 * (2 * M / αG) + 5 * αG * M) := by
    intro z θ hmem
    have hsp := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hA : |-(Work.Spaces.Dz F z θ) / Work.Construction.s2 θ|
        ≤ Mf / Work.Construction.s2 θ := by
      rw [abs_div, abs_neg, abs_of_pos hsp]
      exact div_le_div_of_nonneg_right (hDzFb z θ hmem) (le_of_lt hsp)
    have hB := abs_comb_le_of hαG (hq1u2b z θ hmem) (hq1u1b z θ hmem)
    calc |-(Work.Spaces.Dz F z θ) / Work.Construction.s2 θ
          - (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
                / Work.Construction.s2 θ) z θ
            + 5 * αG * Work.Spaces.Dz (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
                / Work.Construction.s2 θ) z θ)|
        ≤ |-(Work.Spaces.Dz F z θ) / Work.Construction.s2 θ|
          + |αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
                / Work.Construction.s2 θ) z θ
            + 5 * αG * Work.Spaces.Dz (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
                / Work.Construction.s2 θ) z θ| := abs_sub _ _
      _ ≤ Mf / Work.Construction.s2 θ + (αG ^ 2 * (2 * M / αG) + 5 * αG * M) :=
          add_le_add hA hB
  obtain ⟨K1, hK1nn, hK1⟩ := fam_ode_deriv_bound_proved
    (u := fun z θ => psiP αG Ψ z θ / Work.Construction.s2 θ)
    (H := fun z θ => -(F z θ) / Work.Construction.s2 θ
      - (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => psiP αG Ψ z θ
            / Work.Construction.s2 θ) z θ
          + 5 * αG * Work.Spaces.Dz (fun z θ => psiP αG Ψ z θ
            / Work.Construction.s2 θ) z θ))
    hMnn hMfnn hC1nn
    (fun z θ h => differentiableAt_div_s2 (hsliceP z θ h)
      (ne_of_gt (Work.FTS_StreamBdry.s2_pos_of_Qd h))) hode hub hHbound
  obtain ⟨K2, hK2nn, hK2⟩ := fam_ode_deriv_bound_proved
    (u := fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ / Work.Construction.s2 θ)
    (H := fun z θ => -(Work.Spaces.Dz F z θ) / Work.Construction.s2 θ
      - (αG ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
            / Work.Construction.s2 θ) z θ
          + 5 * αG * Work.Spaces.Dz (fun z θ => Work.Spaces.Dz (psiP αG Ψ) z θ
            / Work.Construction.s2 θ) z θ))
    hMnn hMfnn hC2nn
    (fun z θ h => differentiableAt_div_s2 (hsliceQ1 z θ h)
      (ne_of_gt (Work.FTS_StreamBdry.s2_pos_of_Qd h))) hode1 hq1b hHboundQ
  -- the two pointwise conclusions
  have hmain : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pthIter 2 (psiP αG Ψ) z θ|
        ≤ 4 * M + 2 * K1 + Mf + (αG ^ 2 * M + 5 * αG * M) := by
    intro z θ hmem
    have hsp := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hs2le : Work.Construction.s2 θ ≤ 1 := by
      rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
    rw [pthIter2_eq (α := αG) hCtP hlawP z θ hmem]
    exact abs_four_le_of
      (abs_four_s2_mul_le_of (le_of_lt hsp) hs2le hMnn (hub z θ hmem))
      (abs_two_sin_sq_mul_le_of hK1nn (hK1 z θ hmem))
      (hFb z θ hmem)
      (abs_s2_mul_le_of (le_of_lt hsp) hs2le hC1nn
        (abs_comb_le_of hαG (hu2b z θ hmem) (hu1b z θ hmem)))
  have hmain1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 (psiP αG Ψ)) z θ|
        ≤ 4 * M + 2 * K2 + Mf + (αG ^ 2 * (2 * M / αG) + 5 * αG * M) := by
    intro z θ hmem
    have hsp := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hs2le : Work.Construction.s2 θ ≤ 1 := by
      rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
    show |Work.Spaces.pthIter 2 (Work.Spaces.Dz (psiP αG Ψ)) z θ| ≤
      4 * M + 2 * K2 + Mf + (αG ^ 2 * (2 * M / αG) + 5 * αG * M)
    rw [pthIter2_eq (α := αG) hCtQ1 hlawDzP z θ hmem]
    exact abs_four_le_of
      (abs_four_s2_mul_le_of (le_of_lt hsp) hs2le hMnn (hq1b z θ hmem))
      (abs_two_sin_sq_mul_le_of hK2nn (hK2 z θ hmem))
      (hDzFb z θ hmem)
      (abs_s2_mul_le_of (le_of_lt hsp) hs2le hC2nn
        (abs_comb_le_of hαG (hq1u2b z θ hmem) (hq1u1b z θ hmem)))
  refine ⟨max (4 * M + 2 * K1 + Mf + (αG ^ 2 * M + 5 * αG * M))
    (4 * M + 2 * K2 + Mf + (αG ^ 2 * (2 * M / αG) + 5 * αG * M)), ?_⟩
  intro z θ hmem j hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact le_trans (hmain z θ hmem) (le_max_left _ _)
  · exact le_trans (hmain1 z θ hmem) (le_max_right _ _)


end Work.FTS_StreamBdry.SB3
