import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_L12_slice_facts
import Submission.Work.FTS_RegExport.RXT.SysAux.Theta_ops
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.Thetapart_dz_bound`

The `Θ`-part of `U(Φ)/sin 2θ` is *radial*: for the singular part
`Θ α F = (1/(4α)) sin 2θ · L₁₂(F)(z)` of the stream function,

`U(Θ α F)(z,θ)/sin 2θ = -(3/(4α)) L₁₂(F)(z) + (1/4) (F,K)_{L²_θ}(z)`

on the open quadrant (this is the second identity of
`Work.FTS_RegExport.RXT.SysAux.Theta_ops`, which needs only the index-raising identity
`z ∂_z L₁₂(F) = -(F,K)_{L²_θ}`).  Hence `D_z` of that quotient is a radial function, and the
target of this file bounds it by `K·z` for `0 < z ≤ 1`.

The ingredients are all available in the workspace:

* `Work.FTS_RegExport.RXT.SysAux.FK_L12_slice_facts` gives, for a slice `F` that is `C⁴` on the
  open quadrant, whose `mixed`-jets of order `≤ 2` are bounded by `B·z^{3/2}/(1+z)²`, and which
  carries `L₁₂(F)(0) = 0`: the pointwise bounds on `(F,K)_{L²_θ}` and on its `D_z`-jet
  (`z·∂_z(F,K)`), the `C²`-regularity of `z ↦ (F,K)_{L²_θ}(z)`, and the derivative identity
  `∂_z L₁₂(F) = -(F,K)/z`;
* the two analytic inputs are `Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved` (the jet
  bounds at rate `z^{3/2}/(1+z)²`, from `LimApprox`) and
  `Work.FTS_RegExport.RXB.l12_zero_lim_proved` (`L₁₂(slice g τ)(0) = 0`), both from the
  `DynOK'` hypothesis; the `C⁴`-regularity of the slice comes from `RegPkgMin.c4`, i.e. from the
  `DynOK` half of `DynOK'`.
-/

noncomputable section

open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB4

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The `Θ`-part of `U(Φ)/sin 2θ` is radial and `O(z)` near `z = 0`.**

For a slice `F` that is `C⁴` on the open quadrant, whose `mixed`-jets of order `≤ 2` decay like
`z^{3/2}/(1+z)²` and which carries `L₁₂(F)(0) = 0`, the `D_z`-derivative of the quotient
`U(Θ α F)/sin 2θ` is `O(z)` on `0 < z ≤ 1` (uniformly in `θ ∈ (0,π/2)`). -/
lemma thetapart_dz_aux {α B : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    (hCd : ContDiffOn ℝ 4 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hb : ∀ b c : ℕ, c + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b c F z θ| ≤ B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hL12zero : Work.Construction.L12 F 0 = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.Construction.Uop α (Work.Construction.Theta α F) z θ
        / Work.Construction.s2 θ) z θ| ≤ K * z := by
  obtain ⟨C, hCpos, hFKj, -, hFKcont, -, hL12d⟩ :=
    Work.FTS_RegExport.RXT.SysAux.FK_L12_slice_facts (B := B) hCd hb hL12zero
  -- the index-raising identity in the form consumed by `Theta_ops`
  have hL12d' : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 F z') z = -Work.Construction.FK F z := by
    intro z hz
    rw [(hL12d z hz).deriv]
    field_simp
  -- the closed form of `U(Θ α F)`
  have hOps : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Construction.Uop α (Work.Construction.Theta α F) z θ
        = (1 / 2) * (-(3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z
            + (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK F z) := by
    intro z θ hz hθ hθ2
    have h := (Work.FTS_RegExport.RXT.SysAux.Theta_ops (αG := α) hα hL12d'
      z θ hz hθ hθ2).2.1
    rw [← h]
    ring
  -- the radial function `W = U(Θ α F)/sin 2θ`
  set W : ℝ → ℝ := fun z => -(3 / (4 * α)) * Work.Construction.L12 F z
    + (1 / 4) * Work.Construction.FK F z with hWdef
  have hW_eq : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Uop α (Work.Construction.Theta α F) z θ / Work.Construction.s2 θ
        = W z := by
    intro z θ hzθ
    obtain ⟨hz, hθ0, hθ2⟩ := mem_Qd.mp hzθ
    have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt (s2_pos_of_Qd hzθ)
    rw [hOps z θ hz hθ0 hθ2, hWdef]
    simp only [Work.Construction.s2_eq] at hs2 ⊢
    field_simp
    ring
  refine ⟨(3 / (4 * α)) * C + C / 4, by positivity, ?_⟩
  intro z θ hzθ hz1
  obtain ⟨hz, hθ0, hθ2⟩ := mem_Qd.mp hzθ
  -- unfold `D_z` and `pz`
  rw [Work.Spaces.Dz, Work.Spaces.pz]
  -- the `z`-slice of the quotient agrees with `W` on a neighbourhood of `z`
  have heq : (fun z' : ℝ => Work.Construction.Uop α (Work.Construction.Theta α F) z' θ
        / Work.Construction.s2 θ) =ᶠ[𝓝 z] W := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hW_eq z' θ (mem_Qd.mpr ⟨hz', hθ0, hθ2⟩)
  rw [Filter.EventuallyEq.deriv_eq heq]
  -- the derivative of `W`, via `HasDerivAt`
  have hFKdiff : DifferentiableOn ℝ (fun z' : ℝ => Work.Construction.FK F z') (Set.Ioi 0) :=
    hFKcont.differentiableOn (by norm_num)
  have hFKdiffAt : DifferentiableAt ℝ (fun z' : ℝ => Work.Construction.FK F z') z :=
    hFKdiff.differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hWh : HasDerivAt W
      (-(3 / (4 * α)) * (-(Work.Construction.FK F z) / z)
        + (1 / 4) * deriv (fun z' : ℝ => Work.Construction.FK F z') z) z := by
    rw [hWdef]
    exact ((hL12d z hz).const_mul (-(3 / (4 * α)))).add
      (hFKdiffAt.hasDerivAt.const_mul (1 / 4))
  have hWderiv : deriv W z
      = -(3 / (4 * α)) * (-(Work.Construction.FK F z) / z)
        + (1 / 4) * deriv (fun z' : ℝ => Work.Construction.FK F z') z := hWh.deriv
  rw [hWderiv]
  -- the two pieces: the `L₁₂`-derivative is `-(F,K)/z`, and `z·∂_z(F,K)` is the `D_z`-jet
  have hpiece1 : z * (-(3 / (4 * α)) * (-(Work.Construction.FK F z) / z))
      = (3 / (4 * α)) * Work.Construction.FK F z := by
    first | (field_simp; ring) | field_simp | ring
  have hpiece2 : z * ((1 / 4) * deriv (fun z' : ℝ => Work.Construction.FK F z') z)
      = (1 / 4) * Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0 := by
    show z * ((1 / 4) * deriv (fun z' : ℝ => Work.Construction.FK F z') z)
      = (1 / 4) * (z * deriv (fun z' : ℝ => Work.Construction.FK F z') z)
    ring
  rw [mul_add, hpiece1, hpiece2]
  -- bounds on the two pieces
  have h1 : |Work.Construction.FK F z| ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    simpa only [Work.Spaces.DzIter_zero] using hFKj 0 (by norm_num) z hz
  have h2 : |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0|
      ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := hFKj 1 (by norm_num) z hz
  have hcoef1 : 0 ≤ 3 / (4 * α) := by positivity
  have hcoef2 : 0 ≤ (1 : ℝ) / 4 := by norm_num
  -- `z^{3/2}/(1+z)² ≤ z` for `0 < z ≤ 1`
  have hwt_le : z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ z := by
    have h := Work.FTS_RegExport.RXT.SysAux.L12Wt_div_le_one hz
    rw [Work.FTS_RegExport.RXT.SysAux.L12Wt, div_le_iff₀ hz] at h
    simpa using h
  have hKnn : 0 ≤ (3 / (4 * α)) * C + C / 4 := by positivity
  calc |(3 / (4 * α)) * Work.Construction.FK F z
          + (1 / 4) * Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0|
      ≤ |(3 / (4 * α)) * Work.Construction.FK F z|
          + |(1 / 4) * Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0| :=
        abs_add_le _ _
    _ = (3 / (4 * α)) * |Work.Construction.FK F z|
          + (1 / 4) * |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK F z) z 0| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hcoef1, abs_of_nonneg hcoef2]
    _ ≤ (3 / (4 * α)) * (C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
          + (1 / 4) * (C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hcoef1)
          (mul_le_mul_of_nonneg_left h2 hcoef2)
    _ = ((3 / (4 * α)) * C + C / 4) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
    _ ≤ ((3 / (4 * α)) * C + C / 4) * z := mul_le_mul_of_nonneg_left hwt_le hKnn

theorem Thetapart_dz_bound {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.Dz (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp a)
        (Work.Construction.Theta (Work.FTS.Regularity.pExp a) (Work.FTS.Galerkin.slice g τ)) z θ
          / Work.Construction.s2 θ) z θ| ≤ K * z := by
  intro τ hτ
  have hα : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hα1 : Work.FTS.Regularity.pExp a ≤ 1 := Work.FTS.Regularity.pExp_le_one ha13
  have hregMin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp a) g :=
    Work.FTS.Final.DynOK.regPkgMin hOK.1
  -- the jet bounds at the weight `z^{3/2}/(1+z)²` on a horizon containing `τ`
  obtain ⟨B, -, hB⟩ :=
    lim_mixed_plainE hα hα1 hOK.2 (τ + 1) (by linarith)
  refine thetapart_dz_aux (α := Work.FTS.Regularity.pExp a) (B := B)
    (F := Work.FTS.Galerkin.slice g τ) hα ?_ ?_ ?_
  · exact hregMin.c4 τ hτ
  · intro b c hbc z θ hz hθ0 hθ2
    exact hB τ ⟨hτ, by linarith⟩ b c hbc z θ hz hθ0 hθ2
  · exact l12_zero_plainE hα hOK.2 τ hτ

end Work.FTS_StreamBdry.SB4
