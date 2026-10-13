/-
# Row 19 — the missing `(k = 1, j = 4)` slot of `𝒱(Φ̃_*)`

The target of this file is `abs_DthIter_four_VsW_le`:

`|D_θ^4 (VsW α Φs) z θ| ≤ C · (max Cs 0 · α) · ((α + sin 2θ) sin(2θ)^{α/5}) · min z 1`

for a frozen `StarPkg α Cs Φs`.  The frozen fields control `𝒱(Φ̃_*) = Vop (PhiTs α Φs)` only in
`𝒲^{4,∞}` (slots `k + j ≤ 4`) and `∂_θ 𝒰(Φ̃_*) = pth (Uop (PhiTs α Φs))` in `𝒲^{5,∞}`
(slots `k + j ≤ 5`); the slot `(k = 1, j = 4)` of `𝒱` — the `z`-vanishing of `D_θ^4 𝒱` — is one
order above the `𝒱`-field, and the angular summands of a naive Leibniz expansion of
`D_θ^4 (tan θ · 𝒰)` do not vanish individually.

The way out is the **pure algebra identity** of `helpers/Row19Ident.lean`,

  `∂_θ 𝒰 = -(2 𝒱 + ℛ + α · D_z 𝒱)`   (on the open quadrant),

which expresses the defect `∂_θ 𝒱` through the two fields.  Applying `D_θ^4` to it (the
`(k=0, j=4)`-slots of `𝒰` and of `ℛ`, and the `(k=1, j=4)`-slot of `𝒰` for the `z`-derivative)
turns the target into a **singular linear ODE in `z`** for `g(t) = D_θ^4 𝒱(t,θ)`:

  `α t g'(t) + 2 g(t) + H(t) = 0`,   `H(t) := D_θ^4 (∂_θ𝒰)(t,θ) + D_θ^4 ℛ(t,θ)`,

with `|H(t) - H(0)| ≤ 2 M Λ t` (`M = max Cs 0 · α`, `Λ = (α + sin 2θ) sin(2θ)^{α/5}`): the
`𝒰`-part of the difference is bounded by the field derivative, and the `ℛ`-part by
`|D_θ^4 ℛ(t)| ≤ M Λ t/(1+t)`, where the `(z+1)/z`-factor of the `ℛ`-field supplies exactly the
`z`-vanishing.  The singular ODE is integrated with the explicit solution
`g(t) = -(1/α) t^{-2/α} ∫_0^t s^{2/α-1} H(s) ds`, giving
`|g(z) - g(0)| ≤ 2 M Λ z/(2+α) ≤ 2 M Λ z`.  Since `VsW = 𝒱 - 𝒱(0,·)`, this is the target for
`0 < z ≤ 1`; the cases `z = 0` and `z ≥ 1` are `Split.DthIter_VsW_zero` and
`Split.abs_DthIter_four_VsW_le`.

Note that the elliptic equation (`StarPkg.sol`) is *not* used: everything rests on the
`𝒱`- and `∂_θ𝒰`-fields together with the algebraic identity, hence on the *frozen* data.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.Row19Ident
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.abs_le_of_singular_ode
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.dthIter_four_Rop_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.pz_dthIter_four_pthU_le
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)
open Work.FTS.Nonlinear.Pieces.RNP.row19.helpers
  (abs_le_of_singular_ode dthIter_four_Rop_le pz_dthIter_four_pthU_le)

/-- `𝒱(Ψ) = ∂_θΨ - tan θ·Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothQuad_Vop {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad Ψ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) := by
  have hpth : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth Ψ) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hsm)
  have htan : Work.FTS.LocData.SmoothQuad (fun _ θ : ℝ => Real.tan θ) := by
    refine Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry ?_
    have hfun : Function.uncurry (fun _ θ : ℝ => Real.tan θ)
        = fun p : ℝ × ℝ => Real.tan p.2 := rfl
    rw [hfun]
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2)
        (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.contDiff_sin.comp contDiff_snd).contDiffOn
    have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
        (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.contDiff_cos.comp contDiff_snd).contDiffOn
    have hrew : (fun p : ℝ × ℝ => Real.tan p.2)
        = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 := by
      funext p
      exact Real.tan_eq_sin_div_cos p.2
    rw [hrew]
    exact hsin.div hcos (fun p hp => ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩))
  have hprod : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => Real.tan θ * Ψ z θ) :=
    Work.FTS.LocData.smoothQuad_mul htan hsm
  exact Work.FTS.LocData.smoothQuad_sub hpth hprod

/-- `D_z` commutes with the `D_θ`-iterates on the open quadrant, for `SmoothQuad` data. -/
theorem dz_dthIter_comm_smoothQuad {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (i : ℕ) : ∀ z θ, -1 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DthIter i (Work.Spaces.Dz g) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter i g) z θ := by
  induction i with
  | zero => intro z θ _ _; rfl
  | succ n ih =>
    intro z θ hz hθ
    have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter n g)) (z, θ) :=
      ((hsm.DthIter n).contDiffAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds (show (z, θ) ∈
          Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hz, hθ⟩))).of_le
        (by simp [Work.Stability.smoothOrder])
    have heq : (fun θ' => Work.Spaces.DthIter n (Work.Spaces.Dz g) z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.Dz (Work.Spaces.DthIter n g) z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact ih z θ' hz hθ'
    have h1 : Work.Spaces.Dth (Work.Spaces.DthIter n (Work.Spaces.Dz g)) z θ
        = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter n g)) z θ := by
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]
    rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, h1,
      (Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter n g) hcd).symm]

/-- The `z`-slice of a `D_θ`-iterate of a `SmoothQuad` function is differentiable on the open
quadrant. -/
theorem differentiableAt_slice_z_DthIter {G : ℝ → ℝ → ℝ} (hG : Work.FTS.LocData.SmoothQuad G)
    (b : ℕ) {t θ : ℝ} (ht : -1 < t) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun s => Work.Spaces.DthIter b G s θ) t :=
  (((hG.DthIter b).curry_z hθ).differentiableOn
    Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds ht)

/-- The `z`-slice of `D_θ^b G - D_θ^b G(0,·)` with its honest `deriv`. -/
theorem hasDerivAt_slice_z_DthIter_sub {G : ℝ → ℝ → ℝ} (hG : Work.FTS.LocData.SmoothQuad G)
    (b : ℕ) {θ t : ℝ} (ht : -1 < t) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s => Work.Spaces.DthIter b G s θ - Work.Spaces.DthIter b G 0 θ)
      (deriv (fun s => Work.Spaces.DthIter b G s θ - Work.Spaces.DthIter b G 0 θ) t) t := by
  have hd : DifferentiableAt ℝ (fun s => Work.Spaces.DthIter b G s θ) t :=
    differentiableAt_slice_z_DthIter hG b ht hθ
  have h2 : deriv (fun s : ℝ => Work.Spaces.DthIter b G s θ - Work.Spaces.DthIter b G 0 θ) t
      = deriv (fun s : ℝ => Work.Spaces.DthIter b G s θ) t := by
    change deriv ((fun s : ℝ => Work.Spaces.DthIter b G s θ)
      - fun _ : ℝ => Work.Spaces.DthIter b G 0 θ) t = _
    rw [deriv_sub hd (differentiableAt_const _), deriv_const, sub_zero]
  rw [h2]
  exact (hd.hasDerivAt.sub (hasDerivAt_const (c := Work.Spaces.DthIter b G 0 θ) t)).congr_deriv
    (by rw [sub_zero])

/-- **The `D_θ^4`-form of the row-19 identity.**  For `Ψ` smooth on the open quadrant and
`(z,θ)` in it,

  `α z ∂_z(D_θ^4 𝒱) + 2 D_θ^4 𝒱 + D_θ^4(∂_θ𝒰) + D_θ^4 ℛ = 0`,

where `𝒰 = Uop α Ψ`, `𝒱 = Vop Ψ`, `ℛ = Rop α Ψ`. -/
theorem dthIter4_ident {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad Ψ)
    {z θ : ℝ} (hz : -1 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    α * z * Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ)) z θ
      + 2 * Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) z θ
      + Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) z θ
      + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) z θ = 0 := by
  have hV : Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) := smoothQuad_Vop hsm
  have hU : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsm
  have hpthU : Work.FTS.LocData.SmoothQuad
      (Work.Spaces.pth (Work.Construction.Uop α Ψ)) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hU)
  have hR : Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) :=
    Work.FTS.Nonlinear.Pieces.RNP.smoothQuad_Rop hsm
  have hDzV : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz (Work.Construction.Vop Ψ)) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Dz hV
  have h2V : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => 2 * Work.Construction.Vop Ψ z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul 2 hV
  have hαDzV : Work.FTS.LocData.SmoothQuad
      (fun z θ : ℝ => α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul α hDzV
  have hRG : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ =>
      Work.Construction.Rop α Ψ z θ + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) :=
    Work.FTS.LocData.smoothQuad_add hR hαDzV
  have hG : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ =>
      2 * Work.Construction.Vop Ψ z θ
        + (Work.Construction.Rop α Ψ z θ
            + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ)) :=
    Work.FTS.LocData.smoothQuad_add h2V hRG
  -- the combined function vanishes on the open quadrant
  have hzero_on : ∀ z' θ', -1 < z' → 0 < θ' → θ' < Real.pi / 2 →
      (fun z θ => Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
          + (2 * Work.Construction.Vop Ψ z θ
              + (Work.Construction.Rop α Ψ z θ
                  + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ))) z' θ'
        = (fun _ _ : ℝ => (0 : ℝ)) z' θ' := by
    intro z' θ' hz' h1 h2
    have h := pth_Uop_eq_neg (α := α) hsm hz' (show θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      from ⟨h1, h2⟩)
    show Work.Spaces.pth (Work.Construction.Uop α Ψ) z' θ'
        + (2 * Work.Construction.Vop Ψ z' θ'
            + (Work.Construction.Rop α Ψ z' θ'
                + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z' θ')) = 0
    rw [h]
    ring
  have hkey : Work.Spaces.DthIter 4 (fun z θ => Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      + (2 * Work.Construction.Vop Ψ z θ
          + (Work.Construction.Rop α Ψ z θ
              + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ))) z θ = 0 := by
    rw [DthIter_congr_Ioi hzero_on 4 z θ hz hθ.1 hθ.2, DthIter_zero_fun 4 z θ]
  -- linearity of `D_θ^4` on the two sums
  have hsplit1 : Work.Spaces.DthIter 4 (fun z θ => Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      + (2 * Work.Construction.Vop Ψ z θ
          + (Work.Construction.Rop α Ψ z θ
              + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ))) z θ
      = Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) z θ
        + Work.Spaces.DthIter 4 (fun z θ => 2 * Work.Construction.Vop Ψ z θ
            + (Work.Construction.Rop α Ψ z θ
                + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ)) z θ :=
    DthIter_add_smoothQuad hpthU hG 4 z θ hz hθ.1 hθ.2
  have hsplit2 : Work.Spaces.DthIter 4 (fun z θ => 2 * Work.Construction.Vop Ψ z θ
      + (Work.Construction.Rop α Ψ z θ
          + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ)) z θ
      = Work.Spaces.DthIter 4 (fun z θ : ℝ => 2 * Work.Construction.Vop Ψ z θ) z θ
        + Work.Spaces.DthIter 4 (fun z θ => Work.Construction.Rop α Ψ z θ
            + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) z θ :=
    DthIter_add_smoothQuad h2V hRG 4 z θ hz hθ.1 hθ.2
  have hsplit3 : Work.Spaces.DthIter 4 (fun z θ => Work.Construction.Rop α Ψ z θ
      + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) z θ
      = Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) z θ
        + Work.Spaces.DthIter 4 (fun z θ : ℝ =>
            α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) z θ :=
    DthIter_add_smoothQuad hR hαDzV 4 z θ hz hθ.1 hθ.2
  have hcm2 : Work.Spaces.DthIter 4 (fun z θ : ℝ => 2 * Work.Construction.Vop Ψ z θ) z θ
      = 2 * Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) z θ := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul 4 2 (Work.Construction.Vop Ψ)]
  have hcmα : Work.Spaces.DthIter 4 (fun z θ : ℝ =>
        α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) z θ
      = α * Work.Spaces.DthIter 4 (Work.Spaces.Dz (Work.Construction.Vop Ψ)) z θ := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul 4 α
      (Work.Spaces.Dz (Work.Construction.Vop Ψ))]
  have hcomm : Work.Spaces.DthIter 4 (Work.Spaces.Dz (Work.Construction.Vop Ψ)) z θ
      = z * Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ)) z θ := by
    have h' := dz_dthIter_comm_smoothQuad hV 4 z θ hz hθ
    rw [h']
    rfl
  rw [hsplit1, hsplit2, hsplit3, hcm2, hcmα, hcomm] at hkey
  linarith [hkey]

/-- Lagrange mean-value bound in `z` on `[0,z]`: if `h` is continuous on `[0,z]`,
differentiable on `(0,z)` with `|h'| ≤ K` there, then `|h t - h 0| ≤ K t` for every
`t ∈ [0,z]`. -/
theorem abs_sub_le_mul_of_deriv_bound_Icc {h : ℝ → ℝ} {K z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn h (Set.Icc 0 z))
    (hdiff : ∀ t ∈ Set.Ioo 0 z, HasDerivAt h (deriv h t) t)
    (hK : ∀ t ∈ Set.Ioo 0 z, |deriv h t| ≤ K) :
    ∀ t ∈ Set.Icc 0 z, |h t - h 0| ≤ K * t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · rw [← h0, sub_self, abs_zero, mul_zero]
  · have hcont_t : ContinuousOn h (Set.Icc 0 t) := hcont.mono (Set.Icc_subset_Icc le_rfl ht.2)
    have hdiff_t : DifferentiableOn ℝ h (Set.Ioo 0 t) := fun x hx =>
      (hdiff x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope h hpos hcont_t hdiff_t
    have hcI : c ∈ Set.Ioo (0 : ℝ) z := ⟨hc.1, lt_of_lt_of_le hc.2 ht.2⟩
    have h1 : h t - h 0 = (t - 0) * deriv h c := by
      rw [hcd]; field_simp
    rw [h1, sub_zero, abs_mul, abs_of_pos hpos]
    calc t * |deriv h c| ≤ t * K := mul_le_mul_of_nonneg_left (hK c hcI) (le_of_lt hpos)
      _ = K * t := by ring

/-- A continuous function at `0` which is dominated by `C t` on `(0,1)` vanishes at `0`. -/
theorem eq_zero_of_continuousAt_of_abs_le {k : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hcont : ContinuousAt k 0) (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |k t| ≤ C * t) :
    k 0 = 0 := by
  have h1 : Filter.Tendsto k (𝓝[>] (0 : ℝ)) (𝓝 (k 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto k (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (f := k) (a := fun t : ℝ => C * t) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)]
        with t ht hlt
      rw [Real.norm_eq_abs]
      exact h t hlt
    · have hc : Filter.Tendsto (fun t : ℝ => C * t) (𝓝 (0 : ℝ)) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).continuousAt.tendsto
      simpa using hc.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h1 h2

/-- **The singular-ODE step, abstractly.**  For `Ψ` smooth on the open quadrant, a point
`(z,θ)` with `z > 0`, and a constant `C ≥ 0` bounding the `(k=1,j=4)`-slot of `∂_θ𝒰` and the
`(k=0,j=4)`-slot of `ℛ` (by `C` and `C·t` respectively), the `z`-difference of `D_θ^4 𝒱`
is at most `2 C z`. -/
theorem dthIter_four_Vop_sub_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad Ψ) {z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {C : ℝ} (hC : 0 ≤ C)
    (hU_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) z, |deriv (fun s : ℝ =>
      Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) s θ) t| ≤ C)
    (hR_bound : ∀ t : ℝ, 0 < t →
      |Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ| ≤ C * t) :
    |Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) z θ
      - Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ| ≤ 2 * C * z := by
  have hVsm : Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) := smoothQuad_Vop hsm
  have hSmU : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth (Work.Construction.Uop α Ψ)) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU
        (Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsm))
  have hSmR : Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) :=
    Work.FTS.Nonlinear.Pieces.RNP.smoothQuad_Rop hsm
  -- continuity of the slices on `[0,z]`
  have hcont_U : ContinuousOn (fun t : ℝ => Work.Spaces.DthIter 4
      (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ) (Set.Icc 0 z) :=
    ((hSmU.DthIter 4).curry_z hθ).continuousOn.mono
      (fun t ht => Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hcont_R : ContinuousOn (fun t : ℝ => Work.Spaces.DthIter 4
      (Work.Construction.Rop α Ψ) t θ) (Set.Icc 0 z) :=
    ((hSmR.DthIter 4).curry_z hθ).continuousOn.mono
      (fun t ht => Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hcont_u : ContinuousOn (fun t : ℝ => Work.Spaces.DthIter 4
      (Work.Construction.Vop Ψ) t θ - Work.Spaces.DthIter 4
        (Work.Construction.Vop Ψ) 0 θ) (Set.Icc 0 z) :=
    (((hVsm.DthIter 4).curry_z hθ).continuousOn.mono
      (fun t ht => Set.mem_Ioi.mpr (by linarith [ht.1]))).sub continuousOn_const
  have hcont_W : ContinuousOn (fun t : ℝ => (Work.Spaces.DthIter 4
        (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
        + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
      - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
        + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)) (Set.Icc 0 z) :=
    (hcont_U.add hcont_R).sub continuousOn_const
  -- `D_θ^4 ℛ(0,·) = 0` (continuity plus the `t`-weight of the field)
  have hR_zero : Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ = 0 := by
    refine eq_zero_of_continuousAt_of_abs_le (k := fun t : ℝ => Work.Spaces.DthIter 4
      (Work.Construction.Rop α Ψ) t θ) hC ?_ ?_
    · exact ((hSmR.DthIter 4).curry_z hθ).continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0))
    · intro t ht
      exact hR_bound t ht.1
  -- the source is `≤ 2 C t`
  have hW_bound : ∀ t ∈ Set.Icc 0 z, |(Work.Spaces.DthIter 4
        (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
        + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
      - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
        + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)| ≤ (2 * C) * t := by
    intro t ht
    have hdiff : ∀ s ∈ Set.Ioo (0 : ℝ) z, HasDerivAt (fun u : ℝ => Work.Spaces.DthIter 4
        (Work.Spaces.pth (Work.Construction.Uop α Ψ)) u θ)
        (deriv (fun u : ℝ => Work.Spaces.DthIter 4
          (Work.Spaces.pth (Work.Construction.Uop α Ψ)) u θ) s) s :=
      fun s hs => (differentiableAt_slice_z_DthIter (hSmU.DthIter 4) 0
        (by linarith [hs.1]) hθ).hasDerivAt
    have hU_piece := abs_sub_le_mul_of_deriv_bound_Icc hz hcont_U hdiff hU_deriv t ht
    have hR_piece : |Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ
        - Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ| ≤ C * t := by
      rw [hR_zero, sub_zero]
      rcases eq_or_lt_of_le ht.1 with h0 | hpos
      · rw [← h0, hR_zero]
        simp
      · exact hR_bound t hpos
    have hAB : (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
          + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
        - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
          + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)
        = (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
            - Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ)
          + (Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ
            - Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ) := by ring
    rw [hAB]
    calc |(Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
            - Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ)
          + (Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ
            - Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)|
        ≤ |Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
              - Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ|
            + |Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ
              - Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ| := abs_add_le _ _
      _ ≤ C * t + C * t := add_le_add hU_piece hR_piece
      _ = (2 * C) * t := by ring
  -- the singular ODE
  have hode : ∀ t ∈ Set.Ioo (0 : ℝ) z,
      α * t * deriv (fun s : ℝ => Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) s θ
          - Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ) t
        + 2 * (Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) t θ
          - Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ)
        + ((Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
            + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
          - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
            + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)) = 0 := by
    intro t ht
    have ht_quad : -1 < t := by linarith [ht.1]
    have hd : DifferentiableAt ℝ (fun s : ℝ => Work.Spaces.DthIter 4
        (Work.Construction.Vop Ψ) s θ) t :=
      differentiableAt_slice_z_DthIter (hVsm.DthIter 4) 0 ht_quad hθ
    have h_g : deriv (fun s : ℝ => Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) s θ
        - Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ) t
        = Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ)) t θ := by
      change deriv ((fun s : ℝ => Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) s θ)
        - fun _ : ℝ => Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ) t = _
      rw [deriv_sub hd (differentiableAt_const _), deriv_const, sub_zero]
      rfl
    have h1 := dthIter4_ident (α := α) hsm ht_quad hθ
    have h2 := dthIter4_ident (α := α) hsm (show (-1 : ℝ) < 0 by norm_num) hθ
    simp only [mul_zero, zero_mul, zero_add, add_zero] at h2
    rw [h_g]
    linarith [h1, h2]
  have hbound := abs_le_of_singular_ode (u := fun t : ℝ => Work.Spaces.DthIter 4
        (Work.Construction.Vop Ψ) t θ - Work.Spaces.DthIter 4
          (Work.Construction.Vop Ψ) 0 θ)
      (W := fun t : ℝ => (Work.Spaces.DthIter 4
            (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
          + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
        - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
          + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ))
      (C := 2 * C) hα hz (by positivity) hcont_u
      (fun t ht => hasDerivAt_slice_z_DthIter_sub hVsm 4 (by linarith [ht.1]) hθ)
      hode hcont_W hW_bound (by ring)
  exact hbound

/-- **The core estimate for `0 < z < 1`.** -/
theorem dthIter_four_VsW_le_near {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Set.Ioo (0 : ℝ) 1, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DthIter 4 (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * z := by
  intro z hz θ hθ
  have hz0 : (0 : ℝ) < z := hz.1
  have hΨ : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hs.smooth
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hL0 : 0 ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    mul_nonneg hM0 hΛ0
  have hU_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) z, |deriv (fun s : ℝ => Work.Spaces.DthIter 4
      (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) s θ) t|
      ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    intro t ht
    have htI : t ∈ Work.Spaces.Iz := le_of_lt ht.1
    have h := pz_dthIter_four_pthU_le (α := α) (Cs := Cs) (Φs := Φs) hα hs t htI θ hθI
    have ht1 : (0 : ℝ) < 1 + t := by linarith [ht.1]
    have hdiv : max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        / (1 + t) ≤ max Cs 0 * α
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      rw [div_le_iff₀ ht1]
      simpa using mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + t by linarith [ht.1]) hL0
    simpa only [Work.Spaces.pz] using h.trans hdiv
  have hR_bound : ∀ t : ℝ, 0 < t → |Work.Spaces.DthIter 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) t θ|
      ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * t := by
    intro t ht
    have h := dthIter_four_Rop_le (α := α) (Cs := Cs) (Φs := Φs) hα hs t ht θ hθI
    have ht1 : (0 : ℝ) < 1 + t := by linarith
    have hfac : t / (1 + t) ≤ t := by
      rw [div_le_iff₀ ht1]; nlinarith [ht]
    calc |Work.Spaces.DthIter 4 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) t θ|
        ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * (t / (1 + t)) := h
      _ ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * t :=
          mul_le_mul_of_nonneg_left hfac hL0
  have hmain := dthIter_four_Vop_sub_le (α := α) (Ψ := Work.FTS.Nonlin.PhiTs α Φs) hΨ
    hα hz0 hθ hL0 hU_deriv hR_bound
  have heq : Work.Spaces.DthIter 4 (VsW α Φs) z θ
      = Work.Spaces.DthIter 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ
        - Work.Spaces.DthIter 4
            (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) 0 θ :=
    DthIter_VsW_eq hα hs 4 z θ (by linarith [hz0]) hθ.1 hθ.2
  rw [heq]
  exact hmain.trans_eq (by ring_nf)

/-- **Row 19, the missing order.**  For a frozen `StarPkg α Cs Φs` and `0 < α ≤ 1`, the
`(k = 0, j = 4)`-slot of the `θ`-derivative of the split `VsW = 𝒱(Φ̃_*) - 𝒱(Φ̃_*)(0,·)` is
controlled by `(max Cs 0 · α)·((α + sin 2θ) sin(2θ)^{α/5})·min z 1`. -/
theorem abs_DthIter_four_VsW_le : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DthIter 4 (Work.FTS.Nonlinear.Pieces.RNP.row19.VsW α Φs) z θ|
        ≤ C * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
  refine ⟨2, by norm_num, ?_⟩
  intro α Cs Φs hs hα hα1 z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, DthIter_VsW_zero]
    have hne : α / 5 ≠ 0 := ne_of_gt (by linarith)
    simp [Real.zero_rpow hne]
  by_cases hz1 : z < 1
  · have hnear := dthIter_four_VsW_le_near (α := α) (Cs := Cs) (Φs := Φs) hα hα1 hs
      z ⟨hzpos, hz1⟩ θ hθ
    rw [min_eq_left (le_of_lt hz1)]
    calc |Work.Spaces.DthIter 4 (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * z := hnear
      _ = 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * z := by ring
  · have hz1' : 1 ≤ z := le_of_not_gt hz1
    have hgl := abs_DthIter_VsW_le (α := α) (Cs := Cs) (Φs := Φs) hα hs 4
      (by norm_num) (by norm_num) z hz θ ⟨hθ.1.le, hθ.2.le⟩
    rw [min_eq_right hz1']
    calc |Work.Spaces.DthIter 4 (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := hgl
      _ = 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * 1 := by ring

end Work.FTS.Nonlinear.Pieces.RNP.row19
