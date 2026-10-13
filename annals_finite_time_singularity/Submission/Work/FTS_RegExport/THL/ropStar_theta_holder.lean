import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.THL.holder_of_deriv_sin_bound
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen

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
