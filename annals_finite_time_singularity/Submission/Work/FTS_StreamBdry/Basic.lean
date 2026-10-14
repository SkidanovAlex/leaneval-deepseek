import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_aux
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS_RegExport.RXVP.vz7_nonneg_of_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP

open scoped Real

/-- The angular coefficient `c2m θ = cos 2θ − sin²θ` is bounded by `2` in absolute value
(its range is `[-2, 1]`). -/
theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
  have h2 : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
    exact Real.sin_sq_le_one θ
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num


end Work.FTS_RegExport.RXVP
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.ropStar_theta_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# **A4** — the `θ`-Hölder modulus of the star part `ℛ(Φ̃_*)`

`Work.FTS_RegExport.THL.ropStar_theta_holder`: for `0 < αG ≤ 1` and a star datum
`hStar : Final.StarPkgo2 αG Cs Φs`, the function `θ ↦ ℛ_{αG}(Φ̃_*)(z,θ)` is `αG/5`-Hölder on
`(0,π/2)`, uniformly for `z > 0`.

## Route

Write `Ψ := Φ̃_* = PhiTil αG (Fstar αG) Φs` and `F := (z+1)/z · ℛ_{αG}(Ψ)` (the normalised
quantity of the star package).  The field `StarPkgo2.RW` of the package bounds the `𝒲^{4,∞}`-norm
of `F` by `Cs·αG`; the leaf `Work.Spaces.pz_Dth_sup_bound` extracts from it the *sharp* pointwise
bound
  `|D_θ F| ≤ Cs αG · (αG + sin 2θ) · sin(2θ)^{αG/5}`.
Since `D_θ F = sin 2θ · ∂_θ F` and `∂_θ F = (z+1)/z · ∂_θ ℛ_{αG}(Ψ)` (differentiability of the
`θ`-slice of `ℛ`, see `ropStar_slice_differentiableAt`), division by `sin 2θ` gives
  `|∂_θ ℛ_{αG}(Ψ)(z,·)| ≤ 2 Cs αG · sin(2θ)^{αG/5 − 1}`,
which is exactly the hypothesis of the one-dimensional leaf **A1a**
`Work.FTS_RegExport.THL.holder_of_deriv_sin_bound` at `p = αG/5`.

The differentiability of the slice is the only smoothness input: `ℛ(Ψ)` is `C^∞` on the open
quadrant (`NRow10aux.smoothOpen_Rop`, from `StarPkgo.smooth` and the closed form
`Θ(F_*) = sin 2θ/(2(1+z))`), so its `θ`-slices are differentiable at interior angles.
-/

namespace Work.FTS_RegExport.THL

open scoped Real Topology
open MeasureTheory Set

open Work.FTS.Galerkin (Fn)

/-- **Differentiability of the `θ`-slice of `ℛ(Φ̃_*)`.**  `Φ̃_* = Φs - Θ(F_*)` is `C^∞` on the
open quadrant, hence so is `ℛ(Φ̃_*)`; the `θ`-slice at `z > 0` is therefore differentiable at
every interior angle. -/
private theorem ropStar_slice_differentiableAt {αG Cs : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {Φs : Fn} (hStar : Work.FTS.Final.StarPkgo2 αG Cs Φs)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Rop αG
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ') θ := by
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) := by
    have h := Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs (α := αG) (Cs := Cs)
      hαG hαG1 hStar.toStarPkgo
    simpa only [Work.FTS.Nonlin.PhiTs] using h
  have hRopsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop αG (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_Rop hΨsm
  have hcd : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Rop αG
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.forall hRopsm 2
  have hslice : ContDiffOn ℝ 2 (fun θ' => Work.Construction.Rop αG
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : Set.MapsTo (fun θ' : ℝ => (z, θ')) (Set.Ioo 0 (Real.pi / 2))
        Work.FTS.EllipticEst.Q0 := by
      intro θ' hθ'
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨hz, hθ'.1, hθ'.2⟩
    exact (hcd.comp (((contDiffOn_const (c := z)).prodMk contDiffOn_id)) hmap).congr
      (fun y _ => rfl)
  exact (hslice.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- **The pointwise `θ`-derivative bound for `ℛ(Φ̃_*)`**, in the `sin(2θ)^{αG/5 − 1}` shape
required by `holder_of_deriv_sin_bound`. -/
private theorem ropStar_pth_le {αG Cs : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {Φs : Fn} (hStar : Work.FTS.Final.StarPkgo2 αG Cs Φs)
    {z x : ℝ} (hz : 0 < z) (hx : x ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    |Work.Spaces.pth (Work.Construction.Rop αG
        (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)) z x|
      ≤ (2 * Cs * αG) * Real.sin (2 * x) ^ (αG / 5 - 1) := by
  have hx0 : 0 < x := hx.1
  have hx2 : x < Real.pi / 2 := hx.2
  -- abbreviations (definitional, so every `rewrite` below is `rfl`-level unfolding)
  set Ψ : ℝ → ℝ → ℝ := Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs with hΨ
  set F : ℝ → ℝ → ℝ := fun z θ => (z + 1) / z * Work.Construction.Rop αG Ψ z θ with hF
  -- **(1)** the `θ`-slice of `ℛ(Ψ)` is differentiable at `x`
  have hdiff : DifferentiableAt ℝ (fun θ' => Work.Construction.Rop αG Ψ z θ') x := by
    rw [hΨ]
    exact ropStar_slice_differentiableAt hαG hαG1 hStar hz hx
  -- **(2)** `∂_θ F = (z+1)/z · ∂_θ ℛ(Ψ)`
  have hpth : Work.Spaces.pth F z x
      = (z + 1) / z * Work.Spaces.pth (Work.Construction.Rop αG Ψ) z x := by
    simp only [Work.Spaces.pth, hF]
    exact deriv_const_mul ((z + 1) / z) hdiff
  -- **(3)** the sharp bound on `D_θ F = sin 2θ · ∂_θ F` from the star package
  have hmem : Work.Spaces.WlInfMem αG 4 F := by
    rw [hF, hΨ]; simpa only [Work.FTS.Nonlin.PhiTs] using hStar.RW.1
  have hbd : Work.Spaces.WlInf αG 4 F ≤ Cs * αG := by
    rw [hF, hΨ]; simpa only [Work.FTS.Nonlin.PhiTs] using hStar.RW.2
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : x ∈ Work.Spaces.Iθ := ⟨le_of_lt hx0, le_of_lt hx2⟩
  have hb := Work.Spaces.pz_Dth_sup_bound αG hαG 4 F hmem 1 0 le_rfl (by norm_num)
    z x hzI hθI
  have hb' : |Work.Spaces.Dth F z x| ≤ Work.Spaces.WlInf αG 4 F
        * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5)) := by
    simpa using hb
  have hsin_nn : 0 ≤ Real.sin (2 * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hnn : 0 ≤ (αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5) :=
    mul_nonneg (add_nonneg (le_of_lt hαG) hsin_nn) (Real.rpow_nonneg hsin_nn _)
  have hD : |Work.Spaces.Dth F z x|
      ≤ Cs * αG * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5)) :=
    le_trans hb' (mul_le_mul_of_nonneg_right hbd hnn)
  -- **(4)** divide by `sin 2θ · (z+1)/z ≥ sin 2θ`, and use `sin 2θ ≤ 1`, `αG ≤ 1`
  have hs0 : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hc0 : 0 < (z + 1) / z := div_pos (by linarith) hz
  have hc1 : 1 ≤ (z + 1) / z := by rw [le_div_iff₀ hz]; linarith
  have hCsa : 0 ≤ Cs * αG := by
    have h1' : 0 ≤ Work.Spaces.WlInf αG 4 F := by
      rw [Work.Spaces.WlInf]
      exact add_nonneg (Work.Spaces.wlZSum_nonneg αG 4 F hmem)
        (Work.Spaces.wlThSum_nonneg αG 4 F hmem)
    linarith
  have hD' : Real.sin (2 * x)
        * (((z + 1) / z) * |Work.Spaces.pth (Work.Construction.Rop αG Ψ) z x|)
      ≤ Cs * αG * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5)) := by
    have h := hD
    rw [Work.Spaces.Dth, hpth, abs_mul, abs_mul, abs_of_pos hs0, abs_of_pos hc0] at h
    exact h
  have hrs : Real.sin (2 * x) ^ (αG / 5 - 1) * Real.sin (2 * x)
      = Real.sin (2 * x) ^ (αG / 5) := by
    have h1 : Real.sin (2 * x) ^ ((αG / 5 - 1)) * Real.sin (2 * x) ^ (1:ℝ)
        = Real.sin (2 * x) ^ ((αG / 5 - 1) + 1) :=
      (Real.rpow_add hs0 (αG / 5 - 1) 1).symm
    rw [Real.rpow_one] at h1
    rw [h1]; congr 1; ring
  have hbase : 0 ≤ Real.sin (2 * x) ^ (αG / 5) := Real.rpow_nonneg hsin_nn _
  have hsg : αG + Real.sin (2 * x) ≤ 2 := by
    have := Real.sin_le_one (2 * x); linarith
  have h2 : Cs * αG * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5))
      ≤ (2 * Cs * αG * Real.sin (2 * x) ^ (αG / 5 - 1))
        * (Real.sin (2 * x) * ((z + 1) / z)) := by
    have heq : (2 * Cs * αG * Real.sin (2 * x) ^ (αG / 5 - 1))
          * (Real.sin (2 * x) * ((z + 1) / z))
        = 2 * Cs * αG * Real.sin (2 * x) ^ (αG / 5) * ((z + 1) / z) := by
      rw [← hrs]; ring
    rw [heq]
    have hle2 : αG + Real.sin (2 * x) ≤ 2 * ((z + 1) / z) := by linarith
    calc Cs * αG * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5))
        = (Cs * αG * Real.sin (2 * x) ^ (αG / 5)) * (αG + Real.sin (2 * x)) := by ring
      _ ≤ (Cs * αG * Real.sin (2 * x) ^ (αG / 5)) * (2 * ((z + 1) / z)) :=
          mul_le_mul_of_nonneg_left hle2 (mul_nonneg hCsa hbase)
      _ = 2 * Cs * αG * Real.sin (2 * x) ^ (αG / 5) * ((z + 1) / z) := by ring
  have hkey : |Work.Spaces.pth (Work.Construction.Rop αG Ψ) z x|
        * (Real.sin (2 * x) * ((z + 1) / z))
      ≤ (2 * Cs * αG * Real.sin (2 * x) ^ (αG / 5 - 1))
        * (Real.sin (2 * x) * ((z + 1) / z)) := by
    have h1 : |Work.Spaces.pth (Work.Construction.Rop αG Ψ) z x|
          * (Real.sin (2 * x) * ((z + 1) / z))
        = Real.sin (2 * x) * (((z + 1) / z)
            * |Work.Spaces.pth (Work.Construction.Rop αG Ψ) z x|) := by ring
    rw [h1]; exact le_trans hD' h2
  exact le_of_mul_le_mul_right hkey (mul_pos hs0 hc0)

theorem ropStar_theta_holder {αG Cs : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} (hStar : Work.FTS.Final.StarPkgo2 αG Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |Work.Construction.Rop αG (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ
        - Work.Construction.Rop αG
            (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ'|
        ≤ C * |θ - θ'| ^ (αG / 5) := by
  have hα5pos : 0 < αG / 5 := by linarith
  have hα5le : αG / 5 ≤ 1 := by linarith
  -- the derivative bound is available with the constant `2 Cs αG`
  have hC0 : 0 ≤ 2 * Cs * αG := by
    have hmem : Work.Spaces.WlInfMem αG 4 (fun z θ => (z + 1) / z * Work.Construction.Rop αG
        (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ) := by
      simpa only [Work.FTS.Nonlin.PhiTs] using hStar.RW.1
    have hbd : Work.Spaces.WlInf αG 4 (fun z θ => (z + 1) / z * Work.Construction.Rop αG
        (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ) ≤ Cs * αG := by
      simpa only [Work.FTS.Nonlin.PhiTs] using hStar.RW.2
    have h1 : 0 ≤ Work.Spaces.WlInf αG 4 (fun z θ => (z + 1) / z * Work.Construction.Rop αG
        (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ) := by
      rw [Work.Spaces.WlInf]
      exact add_nonneg (Work.Spaces.wlZSum_nonneg αG 4 _ hmem)
        (Work.Spaces.wlThSum_nonneg αG 4 _ hmem)
    linarith
  refine ⟨2 * (Real.pi / 4) ^ (1 - αG / 5) / (αG / 5) * (2 * Cs * αG), ?_, ?_⟩
  · exact mul_nonneg (div_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)) (by linarith)) hC0
  · intro z hz θ hθ θ' hθ'
    have hd : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt (fun θ'' =>
        Work.Construction.Rop αG
          (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ'')
        (Work.Spaces.pth (Work.Construction.Rop αG
          (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)) z x) x := by
      intro x hx
      exact (ropStar_slice_differentiableAt hαG hαG1 hStar hz hx).hasDerivAt
    have hb : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.Spaces.pth (Work.Construction.Rop αG
          (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)) z x|
        ≤ (2 * Cs * αG) * Real.sin (2 * x) ^ (αG / 5 - 1) := by
      intro x hx
      exact ropStar_pth_le hαG hαG1 hStar hz hx
    exact holder_of_deriv_sin_bound hα5pos hα5le hC0 hd hb θ hθ θ' hθ'

end Work.FTS_RegExport.THL
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.vopStar_theta_holder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL

open MeasureTheory Set

theorem vopStar_theta_holder {αG Cs : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} (hStar : Work.FTS.Final.StarPkgo2 αG Cs Φs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |Work.Construction.Vop (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ
        - Work.Construction.Vop
            (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ'|
        ≤ C * |θ - θ'| ^ (αG / 5) := by
  set g : ℝ → ℝ → ℝ := Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs with hg
  set f : ℝ → ℝ → ℝ := Work.Construction.Vop g with hf
  have hmem : Work.Spaces.WlInfMem αG 4 f := by
    rw [hf, hg]
    exact hStar.VW.1
  have hle : Work.Spaces.WlInf αG 4 f ≤ Cs * αG := by
    rw [hf, hg]
    exact hStar.VW.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hf, hg]
    exact (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.1
  have hWnn : 0 ≤ Work.Spaces.WlInf αG 4 f := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg αG 4 f hmem)
      (Work.Spaces.wlThSum_nonneg αG 4 f hmem)
  have hCnn : 0 ≤ Cs * αG := le_trans hWnn hle
  have hp : 0 < αG / 5 := by linarith
  have hp1 : αG / 5 ≤ 1 := by linarith
  refine ⟨2 * (Real.pi / 4) ^ (1 - αG / 5) / (αG / 5) * (2 * (Cs * αG)), ?_, ?_⟩
  · have h1 : 0 ≤ (Real.pi / 4) ^ (1 - αG / 5) :=
      Real.rpow_nonneg (by linarith [Real.pi_pos]) _
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) h1) hp.le) (by linarith)
  · intro z hz θ hθ θ' hθ'
    have hs : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.sin (2 * x) := by
      intro x hx
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
        (by linarith [Real.pi_pos, hx.2])
    have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        HasDerivAt (fun θ' => f z θ') (Work.Spaces.pth f z x) x := by
      intro x hx
      have hc0 : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => f z θ')
          (Set.Ioo (0:ℝ) (Real.pi / 2)) := hsm.curry_θ hz
      have hc : ContDiffOn ℝ 1 (fun θ' => f z θ') (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
        hc0.of_le (WithTop.coe_le_coe.mpr le_top)
      have hd1 : DifferentiableOn ℝ (fun θ' => f z θ') (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
        hc.differentiableOn one_ne_zero
      have hdiff : DifferentiableAt ℝ (fun θ' => f z θ') x :=
        hd1.differentiableAt (isOpen_Ioo.mem_nhds hx)
      simpa only [Work.Spaces.pth] using hdiff.hasDerivAt
    have hb : ∀ x ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |Work.Spaces.pth f z x| ≤ (2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5 - 1) := by
      intro x hx
      have hsx : 0 < Real.sin (2 * x) := hs x hx
      have hxIθ : x ∈ Work.Spaces.Iθ := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
      have hD := Work.Spaces.pz_Dth_sup_bound αG hαG 4 f hmem 1 0 le_rfl (by norm_num)
        z x hzIz hxIθ
      simp only [Work.Spaces.pzIter_zero, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
        pow_zero, div_one] at hD
      have hsnn : 0 ≤ Real.sin (2 * x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [Real.pi_pos, hx.2])
      have hpos : 0 ≤ (αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hsx.le _)
      have h1 : |Work.Spaces.Dth f z x|
          ≤ (Cs * αG) * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5)) :=
        hD.trans (mul_le_mul_of_nonneg_right hle hpos)
      have h2 : αG + Real.sin (2 * x) ≤ 2 := by
        have := Real.sin_le_one (2 * x); linarith
      have hsin2nn : 0 ≤ Real.sin (2 * x) ^ (αG / 5) := Real.rpow_nonneg hsx.le _
      have h3 : |Work.Spaces.Dth f z x| ≤ (2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5) := by
        calc |Work.Spaces.Dth f z x|
            ≤ (Cs * αG) * ((αG + Real.sin (2 * x)) * Real.sin (2 * x) ^ (αG / 5)) := h1
          _ ≤ (Cs * αG) * (2 * Real.sin (2 * x) ^ (αG / 5)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hsin2nn) hCnn
          _ = (2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5) := by ring
      have hDth : |Work.Spaces.Dth f z x| = Real.sin (2 * x) * |Work.Spaces.pth f z x| := by
        simp only [Work.Spaces.Dth, abs_mul, abs_of_pos hsx]
      rw [hDth] at h3
      have hrp : Real.sin (2 * x) ^ (αG / 5) / Real.sin (2 * x)
          = Real.sin (2 * x) ^ (αG / 5 - 1) := by
        rw [Real.rpow_sub hsx, Real.rpow_one]
      calc |Work.Spaces.pth f z x|
          = (Real.sin (2 * x) * |Work.Spaces.pth f z x|) / Real.sin (2 * x) := by
            rw [mul_comm (Real.sin (2 * x)) (|Work.Spaces.pth f z x|),
              mul_div_cancel_right₀ (|Work.Spaces.pth f z x|) (ne_of_gt hsx)]
        _ ≤ ((2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5)) / Real.sin (2 * x) :=
            div_le_div_of_nonneg_right h3 hsx.le
        _ = (2 * (Cs * αG)) * (Real.sin (2 * x) ^ (αG / 5) / Real.sin (2 * x)) := by ring
        _ = (2 * (Cs * αG)) * Real.sin (2 * x) ^ (αG / 5 - 1) := by rw [hrp]
    exact holder_of_deriv_sin_bound hp hp1 (by linarith) hderiv hb θ hθ θ' hθ'

end Work.FTS_RegExport.THL
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.Basic` — vocabulary and elementary API for the StreamBdry (`SB`) area

This module is the entry point of the `FTS_StreamBdry` subproject (curric-46 lead): the
producers `sb1_gauge`, `sb0_psiField`, `sb3_bounds`, `sb2_dthDV`, `sb2_c2`, `sb4_near0`,
`sb5_barrier`, `sb5_decay`, `sb6_rates`, `slice_inputs`, `hid9''_of_parts` of
`Submission/Work/FTS/StreamBdryIface/Producers.lean` (frozen) are proved under the
names `<name>_proved`, with *identical* types.

## The object of study

`Ψ : Fn = ℝ → ℝ → ℝ` is the (slice of the) stream function, on the open quadrant
`Qd = (0,∞) × (0,π/2)`.  The `U`-slot is
`U'(Ψ) = Uop αG Ψ / s2`, where `Uop αG Ψ = -3Ψ - αG z ∂_zΨ` and `s2 θ = sin 2θ`, so that
the *level-0 ODE*
`αG·D_zΨ + 3Ψ = -s2·U'(Ψ)`  (`D_zΨ = z ∂_zΨ`)
holds **by definition** on `Qd`.  Its general solution is
`Ψ = psiP αG Ψ + c(θ)·z^{-3/αG}` with
`psiP αG Ψ = -(s2/αG)·∫₀¹ v^{3/αG-1}·U'(Ψ)(zv) dv`  (the particular solution).
SB1′ shows the constant of integration is `κ/cos θ`, i.e. the gauge mode
`gaugeMode αG = z^{-3/αG}/cos θ` is the only ambiguity; SB2–SB6 then run on `psiP`.

## Conventions of this file

* `Iint αG Ψ z θ = ∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv`, so that `psiP = -(s2/αG)·Iint`
  *definitionally* (`psiP_eq_Iint`).
* `gaugeGen k z θ = z^{-k}/cos θ`, so that `gaugeMode αG = gaugeGen (3/αG)` definitionally
  (`gaugeMode_eq_gaugeGen`); the algebra of `U(gaugeGen k) = V(gaugeGen k) = 0` is done with
  the abstract exponent `k` and the single relation `αG·k = 3`.
* everything is stated on `Qd`, where `s2 θ > 0` and `cos θ > 0`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP psiHatP SB5Barrier oddPerS)
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §0 Vocabulary -/


/-- The integral `I(z,θ) = ∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv`; `psiP = -(s2/αG)·I`. -/
def Iint (αG : ℝ) (Ψ : Fn) : Fn := fun z θ =>
  ∫ v in (0 : ℝ)..1, v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ

/-- The gauge mode with an abstract exponent: `z^{-k}/cos θ`. -/
def gaugeGen (k : ℝ) : Fn := fun z θ => z ^ (-k) / Real.cos θ

/-- `psiP` *is* `-(s2/αG)·Iint`, definitionally. -/
lemma psiP_eq_Iint (αG : ℝ) (Ψ : Fn) (z θ : ℝ) :
    psiP αG Ψ z θ = -(Work.Construction.s2 θ / αG) * Iint αG Ψ z θ := rfl



/-! ## §1 Membership and sign facts on the open quadrant -/

lemma mem_Qd {z θ : ℝ} : (z, θ) ∈ Work.Construction.Qd ↔ 0 < z ∧ 0 < θ ∧ θ < π / 2 := by
  simp [Work.Construction.Qd]

lemma Qd_pos {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) : 0 < z := (mem_Qd.mp h).1

lemma Qd_theta_mem {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) : θ ∈ Ioo 0 (π / 2) :=
  ⟨(mem_Qd.mp h).2.1, (mem_Qd.mp h).2.2⟩

lemma Qd_theta_Iθ {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) : θ ∈ Work.Spaces.Iθ :=
  ⟨le_of_lt (mem_Qd.mp h).2.1, le_of_lt (mem_Qd.mp h).2.2⟩

lemma s2_pos_of_Ioo {θ : ℝ} (h : θ ∈ Ioo (0 : ℝ) (π / 2)) : 0 < Work.Construction.s2 θ := by
  rw [Work.Construction.s2_eq]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2])

lemma s2_pos_of_Qd {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    0 < Work.Construction.s2 θ := s2_pos_of_Ioo (Qd_theta_mem h)

lemma cos_pos_of_Ioo {θ : ℝ} (h : θ ∈ Ioo (0 : ℝ) (π / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩

lemma cos_pos_of_Qd {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    0 < Real.cos θ := cos_pos_of_Ioo (Qd_theta_mem h)

lemma s2_nonneg_of_Iθ {θ : ℝ} (h : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Construction.s2 θ := by
  rw [Work.Construction.s2_eq]
  exact Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [h.1], by linarith [h.2, Real.pi_pos]⟩

/-- `s2 = 2 sin θ cos θ`, the form in which the angular cancellations are done. -/
lemma s2_eq_two_sin_cos (θ : ℝ) :
    Work.Construction.s2 θ = 2 * Real.sin θ * Real.cos θ := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]

/-- `tan θ · s2 θ = 2 sin²θ` (the bounded form of the product, at `π/2`). -/
lemma tan_mul_s2 {θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Real.tan θ * Work.Construction.s2 θ = 2 * Real.sin θ ^ 2 := by
  rw [s2_eq_two_sin_cos, Real.tan_eq_sin_div_cos]
  field_simp

/-! ## §2 The level-0 ODE, by definition -/

/-- `s2·U' = Uop` on the open quadrant (the only place where the division by `s2` is undone). -/
lemma s2_mul_Uprime {αG : ℝ} (Ψ : Fn) {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Construction.s2 θ * Uprime αG Ψ z θ = Work.Construction.Uop αG Ψ z θ := by
  rw [Uprime, mul_div_cancel₀ _ (ne_of_gt (s2_pos_of_Qd h))]

/-- **The level-0 ODE**, which holds by definition of `Uprime`:
`αG·D_zΨ + 3Ψ = -s2·U'(Ψ)` on the open quadrant. -/
lemma ode_of_Uprime {αG : ℝ} (Ψ : Fn) {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    αG * z * Work.Spaces.pz Ψ z θ + 3 * Ψ z θ = -Work.Construction.s2 θ * Uprime αG Ψ z θ := by
  rw [neg_mul, s2_mul_Uprime Ψ h, Work.Construction.Uop]
  ring


/-! ## §3 The gauge mode is slot-invisible -/

lemma pz_gaugeGen {k z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.pz (gaugeGen k) z θ = -k * z ^ (-k - 1) / Real.cos θ := by
  have h : HasDerivAt (fun z' : ℝ => z' ^ (-k)) (-k * z ^ (-k - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz)
  have h2 : HasDerivAt (fun z' : ℝ => gaugeGen k z' θ)
      (-k * z ^ (-k - 1) / Real.cos θ) z := by
    simpa [gaugeGen, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      h.div_const (Real.cos θ)
  exact h2.deriv

lemma pth_gaugeGen {k z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Spaces.pth (gaugeGen k) z θ = z ^ (-k) * (Real.sin θ / Real.cos θ ^ 2) := by
  have h1 : HasDerivAt (fun θ' : ℝ => (Real.cos θ')⁻¹) (Real.sin θ / Real.cos θ ^ 2) θ := by
    have h0 : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have h2 := h0.inv (by simpa using hc)
    convert h2 using 1
    ring
  have h3 : HasDerivAt (fun θ' : ℝ => gaugeGen k z θ')
      (z ^ (-k) * (Real.sin θ / Real.cos θ ^ 2)) θ := by
    simpa [gaugeGen, div_eq_mul_inv] using h1.const_mul (z ^ (-k))
  exact h3.deriv

/-- The algebra behind `U(gauge) = 0`, with an abstract exponent. -/
lemma gaugeGen_Uop_alg {αG k z θ : ℝ} (hk : αG * k = 3) (hz : z ≠ 0) :
    αG * z * (-k * z ^ (-k - 1) / Real.cos θ) + 3 * (z ^ (-k) / Real.cos θ) = 0 := by
  have hp : z ^ (-k - 1) * z = z ^ (-k) := by
    rw [← Real.rpow_add_one hz (-k - 1)]
    norm_num
  have hp' : z * z ^ (-k - 1) = z ^ (-k) := by rw [mul_comm, hp]
  have h1 : αG * z * (-k * z ^ (-k - 1) / Real.cos θ) + 3 * (z ^ (-k) / Real.cos θ)
      = (αG * (-k) * (z * z ^ (-k - 1)) + 3 * z ^ (-k)) / Real.cos θ := by ring
  rw [h1, hp', show αG * (-k) = -3 from by linarith [hk]]
  ring

/-- `U(gaugeMode) = 0` on points with `z ≠ 0`. -/
lemma Uop_gaugeGen {αG k : ℝ} (hk : αG * k = 3) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Construction.Uop αG (gaugeGen k) z θ = 0 := by
  rw [Work.Construction.Uop, pz_gaugeGen (k := k) hz, gaugeGen]
  have := gaugeGen_Uop_alg (αG := αG) (k := k) (z := z) (θ := θ) hk hz
  linarith [this]

/-- `U(gaugeMode) = 0` on the open quadrant. -/
lemma Uop_gaugeMode {αG : ℝ} (hαG : 0 < αG) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Construction.Uop αG (gaugeMode αG) z θ = 0 :=
  Uop_gaugeGen (k := 3 / αG) (by field_simp) hz

/-- `V(gaugeMode) = 0` wherever `cos θ ≠ 0`. -/
lemma Vop_gaugeGen {k : ℝ} {z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Construction.Vop (gaugeGen k) z θ = 0 := by
  rw [Work.Construction.Vop, pth_gaugeGen (k := k) hc, gaugeGen, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- `V(gaugeMode) = 0` wherever `cos θ ≠ 0`. -/
lemma Vop_gaugeMode {αG : ℝ} {z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Construction.Vop (gaugeMode αG) z θ = 0 :=
  Vop_gaugeGen (k := 3 / αG) (z := z) hc


/-! ## §4 Slot bounds, unfolded -/

/-- The three slot bounds of `SlotBd`, extracted. -/
lemma SlotBd.Dz_le {αG M : ℝ} {Ψ : Fn} (h : SlotBd αG Ψ M) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) {j : ℕ} (hj : j ≤ 2) :
    |Work.Spaces.DzIter j (Uprime αG Ψ) z θ| ≤ M := (h z θ hmem).1 j hj

lemma SlotBd.mixed_le {αG M : ℝ} {Ψ : Fn} (h : SlotBd αG Ψ M) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) :
    |Work.Spaces.mixed 0 1 (Uprime αG Ψ) z θ| ≤ M := (h z θ hmem).2.1

lemma SlotBd.V_le {αG M : ℝ} {Ψ : Fn} (h : SlotBd αG Ψ M) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) {j : ℕ} (hj : j ≤ 1) :
    |Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z θ| ≤ M := (h z θ hmem).2.2 j hj

lemma SlotBd.Uprime_le {αG M : ℝ} {Ψ : Fn} (h : SlotBd αG Ψ M) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) : |Uprime αG Ψ z θ| ≤ M :=
  SlotBd.Dz_le h hmem (j := 0) (by norm_num)

/-- `SrcOK`, extracted: `|F| ≤ Mf` on the closed angular strip. -/
lemma SrcOK.F_le {F : Fn} {L Mf : ℝ} (h : SrcOK F L Mf) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) : |F z θ| ≤ Mf := (h.2.2.1 z θ hz hθ).1

/-- `SrcOK`, extracted: `|D_zF| ≤ Mf` on the closed angular strip. -/
lemma SrcOK.Dz_le {F : Fn} {L Mf : ℝ} (h : SrcOK F L Mf) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.Dz F z θ| ≤ Mf := (h.2.2.1 z θ hz hθ).2

/-! ## §5 Named targets (the statements handed to delegated lemmas) -/

/-- **The level-0 ODE for `psiP`** (SB1 engine).  Consumed by SB1′ (`sb1_gauge`), SB2, SB3. -/
def PsiPOde (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    αG * z * Work.Spaces.pz (psiP αG Ψ) z θ + 3 * psiP αG Ψ z θ
      = -Work.Construction.s2 θ * Uprime αG Ψ z θ


/-- **`psiP` is differentiable in each variable on the open quadrant** (SB1 engine: the `z`-half is
what the constancy argument in `z` needs, the `θ`-half what the `c' = tan θ·c` step needs). -/
def PsiPDiff (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    DifferentiableAt ℝ (fun z' => psiP αG Ψ z' θ) z ∧
    DifferentiableAt ℝ (fun θ' => psiP αG Ψ z θ') θ

/-- **`V(psiP)` is bounded in `z` near `z = 0`, at every fixed `θ`** (SB1 engine: this is the
"`psiP` carries `s2` and `|D_θU'| ≤ M`" input of SB1′; it is what forces the constant of
integration to be `κ/cos θ` rather than a general `c(θ)`). -/
def VopPsiPBnd (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ θ ∈ Ioo (0 : ℝ) (π / 2), ∃ C : ℝ, ∀ z ∈ Ioo (0 : ℝ) 1,
    |Work.Construction.Vop (psiP αG Ψ) z θ| ≤ C

/-- **`|psiP| ≤ M·s2/3`-type bound** (SB1/SB3: `|D_z^j psiP| ≤ M·s2` for `j ≤ 2`, straight from the
integral formula and the `SlotBd` slots). -/
def PsiPDzLe (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j : ℕ, j ≤ 2 →
    |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ




end Work.FTS_StreamBdry
end
end
