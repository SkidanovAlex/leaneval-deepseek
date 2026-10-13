import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.pth_DzIter_le` — the angular derivative of the `U`-slot part

The second and third conjuncts of `sb3_bounds`: for a `C³` stream function `Ψ` on the open
quadrant `Qd = (0,∞) × (0,π/2)` whose slot `U'(Ψ)` satisfies the `SlotBd` bounds and whose
particular solution `P := psiP αG Ψ` satisfies `|D_z^j P| ≤ Sg·sin 2θ` for `j ≤ 3`, the plain
angular derivative `∂_θ(D_z^j P)` is bounded on `Qd` for `j ≤ 1`.

## The mechanism

`∂_θ P = V(P) + tan θ·P` where `V(Ψ) = ∂_θΨ - tan θ·Ψ` (`Construction.Vop`).  The point of the
statement is that `V` **cannot see the gauge mode** `gaugeMode αG = z^{-3/αG}/cos θ`
(`Vop_gaugeMode`), while SB1′ (`Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts`) says that
`Ψ - P` *is* a multiple of the gauge mode on `Qd`.  Hence

  `V(P) = V(Ψ)`   (`Vop_psiP_eq`, proved here),

and since `SlotBd` bounds `|D_z^j (V Ψ)|` for `j ≤ 1` (`SlotBd.V_le`), while `hK` bounds the
`z`-derivatives of `P` itself, both cases `j ≤ 1` are immediate:

* `j = 0`: `|∂_θP| ≤ |V Ψ| + |tan θ·P| ≤ M + 2 Sg`, using
  `tan θ·sin 2θ = 2 sin²θ ≤ 2` (`tan_mul_s2`);
* `j = 1`: Clairaut (`Work.Spaces.pz_pth_comm`, from `SB3.psiP_c2`) and the angular/rational
  commutation `∂_θ(D_zP) = z·∂_θ∂_zP = z·∂_z∂_θP` turn `∂_θ(D_zP)` into
  `D_z(V Ψ) + tan θ·D_zP`, bounded by `M + 2 Sg`.

Every step is carried out on `Qd` only (where `sin 2θ > 0` and `cos θ > 0`): the boundary
`θ = 0, π/2` is exactly where `tan θ` is not differentiable.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3

open Work.FTS.StreamBdryIface (Uprime SlotBd gaugeMode psiP)

set_option autoImplicit false

/-! ## §0 Local regularity helpers on the open quadrant -/

/-- The `θ`-partial of a function of class `C^{n+1}` on the open quadrant is of class `C^n`. -/
theorem contDiffOn_uncurry_pth_qd {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) Work.Construction.Qd := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hchain : ∀ p ∈ Work.Construction.Qd,
      Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hQd.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p)
      Work.Construction.Qd := h.fderiv_of_isOpen hQd (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) Work.Construction.Qd :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- A `z`-slice of `V Ψ = ∂_θΨ - tan θ·Ψ` is differentiable on the open quadrant, because
`Ψ` is `C³` there (so `∂_θΨ` is `C²`, hence differentiable in `z`). -/
theorem differentiableAt_Vop_slice {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Vop Ψ z' θ) z := by
  have hQd : IsOpen Work.Construction.Qd := Work.FTS_StreamBdry.SB1.isOpen_Qd
  have hpth_sm : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Work.Construction.Qd :=
    contDiffOn_uncurry_pth_qd (n := 2) h3
  have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.pth Ψ z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpth_sm.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmem))
  have hd2 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    Work.FTS_StreamBdry.SB1.diffAt_z_slice hmem h3
  change DifferentiableAt ℝ (fun z' => Work.Spaces.pth Ψ z' θ - Real.tan θ * Ψ z' θ) z
  exact hd1.sub (hd2.const_mul (Real.tan θ))

/-! ## §1 The gauge mode is `V`-invisible, and `V(psiP) = V(Ψ)` -/

/-- The gauge mode is `V`-invisible, in the `∂_θ` form: `∂_θ(gaugeMode) = tan θ · gaugeMode`. -/
lemma pth_gaugeMode_eq {αG z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pth (gaugeMode αG) z θ = Real.tan θ * gaugeMode αG z θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd h)
  have hh := Work.FTS_StreamBdry.Vop_gaugeMode (αG := αG) (z := z) (θ := θ) hc
  rw [Work.Construction.Vop] at hh
  linarith

/-- **`V` cannot see the gauge mode**: `V(psiP αG Ψ) = V(Ψ)` on the open quadrant.

This is the only place where SB1′ enters: `Ψ - psiP αG Ψ = κ·gaugeMode` on `Qd`
(`SB1.sb1_gauge_of_parts`), and both `∂_θ` (on the difference) and `V(gaugeMode)` are handled
by the explicit formula `∂_θ(gaugeMode) = tan θ·gaugeMode`. -/
lemma Vop_psiP_eq {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Vop (psiP αG Ψ) z θ = Work.Construction.Vop Ψ z θ := by
  have hpdiff : Work.FTS_StreamBdry.PsiPDiff αG M Ψ :=
    Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot) hpdiff
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  intro z θ hmem
  have hsub := Work.FTS_StreamBdry.SB1.Vop_sub_psiP (αG := αG) (M := M) (Ψ := Ψ) hmem h3 hpdiff
  have hθm := Work.FTS_StreamBdry.Qd_theta_mem hmem
  have hzpos := Work.FTS_StreamBdry.Qd_pos hmem
  -- the difference `Ψ - psiP` is `κ·gaugeMode` near `θ`
  have hev : (fun θ' => Ψ z θ' - psiP αG Ψ z θ')
      =ᶠ[𝓝 θ] (fun θ' => κ * gaugeMode αG z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθm] with θ' hθ'
    have hh := hκ z θ' (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hθ'.1, hθ'.2⟩)
    linarith
  have hpthW : Work.Spaces.pth (fun z' θ' => Ψ z' θ' - psiP αG Ψ z' θ') z θ
      = κ * Work.Spaces.pth (gaugeMode αG) z θ := by
    have h := hev.deriv_eq
    rw [deriv_const_mul_field] at h
    simpa only [Work.Spaces.pth] using h
  have hκz : Ψ z θ - psiP αG Ψ z θ = κ * gaugeMode αG z θ := by
    have hh := hκ z θ hmem
    linarith
  have hgV : Work.Spaces.pth (gaugeMode αG) z θ = Real.tan θ * gaugeMode αG z θ :=
    pth_gaugeMode_eq hmem
  have hzero : Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ = 0 := by
    rw [← hsub, Work.Construction.Vop, hpthW, hκz, hgV]
    ring
  linarith

/-! ## §2 The `j = 1` split: `∂_z ∂_θ P = ∂_z(V Ψ) + tan θ · ∂_z P` -/

/-- The `θ`-identity `∂_θP = V(Ψ) + tan θ·P` holds with `z`-independent coefficients, so its
`z`-derivative splits as `∂_z(V Ψ) + tan θ·∂_zP`.  The two summands are differentiable in `z`
(`V Ψ` because `∂_θΨ` is `C²` on the open quadrant, `tan θ·P` by `PsiPDiff`), which is exactly
what `deriv_add` needs. -/
lemma pz_pth_psiP_eq {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) {z θ : ℝ} (hmem : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ)) z θ
      = Work.Spaces.pz (Work.Construction.Vop Ψ) z θ
        + Real.tan θ * Work.Spaces.pz (psiP αG Ψ) z θ := by
  have hpdiff : Work.FTS_StreamBdry.PsiPDiff αG M Ψ :=
    Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot
  have hV := Vop_psiP_eq hαG h3 hslot
  have hzpos := Work.FTS_StreamBdry.Qd_pos hmem
  have hθm := Work.FTS_StreamBdry.Qd_theta_mem hmem
  have hev : (fun z' => Work.Spaces.pth (psiP αG Ψ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.Vop Ψ z' θ
        + Real.tan θ * psiP αG Ψ z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
    have hm' : (z', θ) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz', hθm.1, hθm.2⟩
    have hh := hV z' θ hm'
    rw [Work.Construction.Vop] at hh
    linarith
  rw [show Work.Spaces.pz (Work.Spaces.pth (psiP αG Ψ)) z θ
      = deriv (fun z' => Work.Spaces.pth (psiP αG Ψ) z' θ) z from rfl, hev.deriv_eq]
  have hd1 : DifferentiableAt ℝ (fun z' => Work.Construction.Vop Ψ z' θ) z :=
    differentiableAt_Vop_slice h3 hmem
  have hd2 : DifferentiableAt ℝ (fun z' => Real.tan θ * psiP αG Ψ z' θ) z :=
    (hpdiff z θ hmem).1.const_mul (Real.tan θ)
  rw [show (fun z' => Work.Construction.Vop Ψ z' θ + Real.tan θ * psiP αG Ψ z' θ)
      = (fun z' => Work.Construction.Vop Ψ z' θ)
        + (fun z' => Real.tan θ * psiP αG Ψ z' θ) from rfl,
    deriv_add hd1 hd2, deriv_const_mul_field]
  rfl

/-! ## §3 The theorem -/

theorem pth_DzIter_le {αG M Sg : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hK : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ Sg * Work.Construction.s2 θ) :
    ∃ K', ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 1,
      |Work.Spaces.pth (Work.Spaces.DzIter j
        (Work.FTS.StreamBdryIface.psiP αG Ψ)) z θ| ≤ K' := by
  refine ⟨M + 2 * Sg, ?_⟩
  -- `Sg ≥ 0` from `hK` at the interior point `(1, π/4)`, where `s2 = 1`
  have hSg0 : 0 ≤ Sg := by
    have h1 : |Work.Spaces.DzIter 0 (psiP αG Ψ) (1 : ℝ) (Real.pi / 4)|
        ≤ Sg * Work.Construction.s2 (Real.pi / 4) :=
      hK 1 (Real.pi / 4) Work.FTS_StreamBdry.SB1.Qd_nonempty 0 (by norm_num)
    have h2 : Work.Construction.s2 (Real.pi / 4) = 1 := by
      rw [Work.Construction.s2_eq, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
        Real.sin_pi_div_two]
    rw [Work.Spaces.DzIter_zero, h2, mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  intro z θ hmem j hj
  have hθm := Work.FTS_StreamBdry.Qd_theta_mem hmem
  have hcospos : 0 < Real.cos θ := Work.FTS_StreamBdry.cos_pos_of_Qd hmem
  have htan_nonneg : 0 ≤ Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθm.1])
        (by linarith [hθm.2, Real.pi_pos])))
      (le_of_lt hcospos)
  -- the elementary bound `|tan θ·X| ≤ 2 Sg` whenever `|X| ≤ Sg·s2 θ`
  have htanX : ∀ X : ℝ, |X| ≤ Sg * Work.Construction.s2 θ →
      |Real.tan θ * X| ≤ 2 * Sg := by
    intro X hX
    have h1 : Real.tan θ * |X| ≤ Real.tan θ * (Sg * Work.Construction.s2 θ) :=
      mul_le_mul_of_nonneg_left hX htan_nonneg
    have h2 : Real.tan θ * (Sg * Work.Construction.s2 θ) = 2 * Sg * Real.sin θ ^ 2 := by
      rw [show Real.tan θ * (Sg * Work.Construction.s2 θ)
          = Sg * (Real.tan θ * Work.Construction.s2 θ) from by ring,
        Work.FTS_StreamBdry.tan_mul_s2 (ne_of_gt hcospos)]
      ring
    have h3 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    rw [abs_mul, abs_of_nonneg htan_nonneg]
    calc Real.tan θ * |X| ≤ Real.tan θ * (Sg * Work.Construction.s2 θ) := h1
      _ = 2 * Sg * Real.sin θ ^ 2 := h2
      _ ≤ 2 * Sg * 1 := mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = 2 * Sg := by ring
  interval_cases j
  · -- `j = 0`: `∂_θP = V(Ψ) + tan θ·P`
    have hkey : Work.Spaces.pth (psiP αG Ψ) z θ
        = Work.Construction.Vop Ψ z θ + Real.tan θ * psiP αG Ψ z θ := by
      have hh := Vop_psiP_eq hαG h3 hslot z θ hmem
      rw [Work.Construction.Vop] at hh
      linarith
    have hb1 : |Work.Construction.Vop Ψ z θ| ≤ M :=
      Work.FTS_StreamBdry.SlotBd.V_le hslot hmem (j := 0) (by norm_num)
    have hb2 : |Real.tan θ * psiP αG Ψ z θ| ≤ 2 * Sg :=
      htanX _ (hK z θ hmem 0 (by norm_num))
    rw [Work.Spaces.DzIter_zero, hkey]
    exact (abs_add_le _ _).trans (add_le_add hb1 hb2)
  · -- `j = 1`: `∂_θ(D_zP) = D_z(V Ψ) + tan θ·D_zP`
    have hcd : ContDiffAt ℝ 2 (Function.uncurry (psiP αG Ψ)) (z, θ) :=
      (Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot).contDiffAt
        (Work.FTS_StreamBdry.SB1.isOpen_Qd.mem_nhds hmem)
    have hstep1 : Work.Spaces.pth (Work.Spaces.Dz (psiP αG Ψ)) z θ
        = z * Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ)) z θ := by
      show deriv (fun θ' => z * Work.Spaces.pz (psiP αG Ψ) z θ') θ
        = z * Work.Spaces.pth (Work.Spaces.pz (psiP αG Ψ)) z θ
      rw [deriv_const_mul_field]
      rfl
    have hfinal : Work.Spaces.pth (Work.Spaces.Dz (psiP αG Ψ)) z θ
        = Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ
          + Real.tan θ * Work.Spaces.Dz (psiP αG Ψ) z θ := by
      rw [hstep1, (Work.Spaces.pz_pth_comm hcd).symm, pz_pth_psiP_eq hαG h3 hslot hmem]
      simp only [Work.Spaces.Dz]
      ring
    have hb1 : |Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ| ≤ M := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
        Work.FTS_StreamBdry.SlotBd.V_le hslot hmem (j := 1) (by norm_num)
    have hb2 : |Real.tan θ * Work.Spaces.Dz (psiP αG Ψ) z θ| ≤ 2 * Sg :=
      htanX _ (by
        simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
          hK z θ hmem 1 (by norm_num))
    rw [show Work.Spaces.DzIter 1 (psiP αG Ψ) = Work.Spaces.Dz (psiP αG Ψ) from rfl,
      hfinal]
    exact (abs_add_le _ _).trans (add_le_add hb1 hb2)

end Work.FTS_StreamBdry.SB3
