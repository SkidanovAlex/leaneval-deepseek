import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.lip_edge_trace
import Submission.Work.FTS_StreamBdry.SB25.pze_aux
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25Aux3.trace_Vop_psiP`

The `θ = π/2` edge trace of the `V`-slot of the `U`-slot part `P := psiP αG Ψ` of a stream
function, with the linear rate `((αG² + 5αG + 6)·M + Mf)·(π/2 - θ)`.

On the open quadrant the elliptic law in `D`-form (`SB3.law_psiP`) reads

  `∂_θ V(P) = -(αG² D_z²P + 5αG D_zP + 6P) - F`,

and `SB3.psiP_DzLe` bounds `|D_z^j P| ≤ M·sin 2θ` (`j ≤ 2`), while `SrcOK` bounds `|F| ≤ Mf`.
Hence `|∂_θ V(P)| ≤ (αG²+5αG+6)·M + Mf` on the quadrant (using `sin 2θ ≤ 1` and `M ≥ 0`, the
latter forced by `SlotBd`), i.e. the slices of `V(P)` are uniformly Lipschitz in `θ`.  The leaf
`SB25.lip_edge_trace` converts a uniform `θ`-Lipschitz bound into a continuous edge trace at
`θ = π/2` approached at the linear rate, which is exactly the statement.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25Aux3

open Work.FTS.StreamBdryIface (psiP SlotBd SrcOK)

set_option autoImplicit false

theorem trace_Vop_psiP {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hsrc : Work.FTS.StreamBdryIface.SrcOK F L Mf) :
    ∃ Vb : ℝ → ℝ, ContinuousOn Vb (Set.Ioi 0) ∧
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        |Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ - Vb z|
          ≤ ((αG ^ 2 + 5 * αG + 6) * M + Mf) * (Real.pi / 2 - θ) := by
  -- `sin 2θ ≤ 1` and the boundary datum `M ≥ 0` forced by `SlotBd`
  have hM0 : 0 ≤ M := by
    have h := Work.FTS_StreamBdry.SlotBd.Dz_le hslot (z := 1) (θ := Real.pi / 4)
      Work.FTS_StreamBdry.SB1.Qd_nonempty (j := 0) (by norm_num)
    exact le_trans (abs_nonneg _) h
  have hcoef : 0 ≤ αG ^ 2 + 5 * αG + 6 := by nlinarith [sq_nonneg αG, hαG]
  -- the pointwise bound on the `θ`-derivative, i.e. the Lipschitz constant of the slices
  have hmain : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Construction.Vop (psiP αG Ψ)) z θ|
        ≤ (αG ^ 2 + 5 * αG + 6) * M + Mf := by
    intro z θ hmem
    have hθm := Work.FTS_StreamBdry.Qd_theta_mem hmem
    have hzpos := Work.FTS_StreamBdry.Qd_pos hmem
    have hs2pos := Work.FTS_StreamBdry.s2_pos_of_Qd hmem
    have hs2le : Work.Construction.s2 θ ≤ 1 := by
      rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
    have hs2M : M * Work.Construction.s2 θ ≤ M := by
      simpa using mul_le_mul_of_nonneg_left hs2le hM0
    -- the elliptic law in `D`-form for `psiP`
    have hlaw := Work.FTS_StreamBdry.SB3.law_psiP hαG hsol h3 hslot z θ hmem
    -- `|D_z^j psiP| ≤ M sin 2θ` for `j ≤ 2`
    have hDz := Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot
    have hD2 : |Work.Spaces.DzIter 2 (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
      hDz z θ hmem 2 (by norm_num)
    have hD1 : |Work.Spaces.Dz (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
      hDz z θ hmem 1 (by norm_num)
    have hD0 : |psiP αG Ψ z θ| ≤ M * Work.Construction.s2 θ :=
      hDz z θ hmem 0 (by norm_num)
    -- the source bound
    have hF : |F z θ| ≤ Mf :=
      Work.FTS_StreamBdry.SrcOK.F_le hsrc hzpos (Work.FTS_StreamBdry.Qd_theta_Iθ hmem)
    -- the three weighted summands
    have hA : |αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ|
        ≤ αG ^ 2 * (M * Work.Construction.s2 θ) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg αG)]
      exact mul_le_mul_of_nonneg_left hD2 (sq_nonneg αG)
    have hB : |5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ|
        ≤ 5 * αG * (M * Work.Construction.s2 θ) := by
      have h5 : (0 : ℝ) ≤ 5 * αG := by linarith
      rw [abs_mul, abs_of_nonneg h5]
      exact mul_le_mul_of_nonneg_left hD1 h5
    have hC : |6 * psiP αG Ψ z θ| ≤ 6 * (M * Work.Construction.s2 θ) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      exact mul_le_mul_of_nonneg_left hD0 (by norm_num)
    have htri : |αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
          + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ|
        ≤ |αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ|
          + |5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ| + |6 * psiP αG Ψ z θ| := by
      have h₁ := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
        + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ) (6 * psiP αG Ψ z θ)
      have h₂ := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ)
        (5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ)
      linarith [abs_nonneg (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ),
        abs_nonneg (5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ),
        abs_nonneg (6 * psiP αG Ψ z θ)]
    have hsum : αG ^ 2 * (M * Work.Construction.s2 θ)
          + 5 * αG * (M * Work.Construction.s2 θ) + 6 * (M * Work.Construction.s2 θ)
        = (αG ^ 2 + 5 * αG + 6) * (M * Work.Construction.s2 θ) := by ring
    rw [hlaw]
    have hneg : -(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
          + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ) - F z θ
        = -(αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
          + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ + F z θ) := by
      ring
    rw [hneg, abs_neg]
    have hsplit := abs_add_le (αG ^ 2 * Work.Spaces.DzIter 2 (psiP αG Ψ) z θ
      + 5 * αG * Work.Spaces.Dz (psiP αG Ψ) z θ + 6 * psiP αG Ψ z θ) (F z θ)
    have hfin : (αG ^ 2 + 5 * αG + 6) * (M * Work.Construction.s2 θ) + Mf
        ≤ (αG ^ 2 + 5 * αG + 6) * M + Mf := by
      have := mul_le_mul_of_nonneg_left hs2M hcoef
      linarith
    linarith
  -- smoothness of `Vop (psiP αG Ψ)` on the open quadrant
  have hVopΨ : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop Ψ))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB25.pze_contDiffOn_uncurry_Vop_Qd (Ψ := Ψ) h3
  have hVopP : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Vop (psiP αG Ψ))) Work.Construction.Qd :=
    hVopΨ.congr (fun p hp => by
      obtain ⟨z, θ⟩ := p
      exact Work.FTS_StreamBdry.SB3.Vop_psiP_eq (αG := αG) (M := M) (Ψ := Ψ)
        hαG h3 hslot z θ hp)
  have hcont : ContinuousOn (Function.uncurry (Work.Construction.Vop (psiP αG Ψ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hVopP.continuousOn
  have hdiff : ∀ z θ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      DifferentiableAt ℝ (fun θ' => Work.Construction.Vop (psiP αG Ψ) z θ') θ := by
    intro z θ hz hθ
    have hmem : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ.1, hθ.2⟩
    exact Work.Spaces.differentiableAt_curry_right
      ((hVopP.differentiableOn (by norm_num)).differentiableAt
        (Work.FTS_StreamBdry.SB1.isOpen_Qd.mem_nhds hmem))
  -- the edge trace at `θ = π/2`
  obtain ⟨fa, fb, _hfa, hfb, hrt⟩ :=
    Work.FTS_StreamBdry.SB25.lip_edge_trace (Work.Construction.Vop (psiP αG Ψ)) 0 (Real.pi / 2)
      ((αG ^ 2 + 5 * αG + 6) * M + Mf) (by linarith [Real.pi_pos]) hcont hdiff
      (fun z θ hz hθ => hmain z θ ⟨hz, hθ.1, hθ.2⟩)
  exact ⟨fb, hfb, fun z θ hmem =>
    (hrt z θ (Work.FTS_StreamBdry.Qd_pos hmem) (Work.FTS_StreamBdry.Qd_theta_mem hmem)).2⟩

end Work.FTS_StreamBdry.SB25Aux3
