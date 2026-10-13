import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Acf
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.FKle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/Decomp` — the coefficient majorants of the `N`-zero-mode estimate

The four pointwise bounds of the zero-mode estimate: the `ℛ`, `𝒰`, `𝒱`-coefficients of
`Ξ = PhiTil α (F_*+f) (Φs + E f)` (split into the star and the perturbation residuals, and
priced by `StarPkgo`/`EllPkgGo` + the `ℋ⁴`-Agmon bound) and the angular moment `FK (F_*+f)`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The arithmetic glue of the four coefficient bounds.**  A star coefficient bounded by
`Cstar · max Cs 0 · α` (with `Cstar` dominated by the `Kcoef` bracket) plus a perturbation
coefficient bounded by `Cp α^{-1/2} Ce · Xn α f` add up to at most `Kcoef`. -/
theorem add_le_Kcoef {α M Ce Cs Cp Cu Cag Cstar K R : ℝ} {f : Fn}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M)
    (hCp : 0 < Cp) (hCu : 0 < Cu) (hCag : 0 < Cag) (hCe0 : 0 < Ce)
    (hCs0 : 0 ≤ Cstar) (hCsle : Cstar ≤ Cp + Cu + Cag + 1)
    (hM : Work.FTS.Nonlin.Xn α f ≤ M)
    (hK : K ≤ Cstar * max Cs 0 * α)
    (hR : R ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) :
    K + R ≤ Kcoef α M Ce Cs Cp Cu Cag := by
  have hr0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hr1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_rpow_neg_half hα0 hα1
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith
  have hM1' : (0 : ℝ) ≤ 1 + M := by linarith
  have hCs1 : max Cs 0 ≤ 1 + |Ce| + |Cs| := by
    refine le_trans (max_le (le_abs_self Cs) (abs_nonneg Cs)) ?_
    have := abs_nonneg Ce
    linarith
  have hCs0' : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hAb0 : (0 : ℝ) ≤ 1 + |Ce| + |Cs| := le_trans hCs0' hCs1
  have hZ0 : 0 < Cp + Cu + Cag + 1 := by linarith
  have hX1 : Work.FTS.Nonlin.Xn α f ≤ 1 + M := by linarith
  -- the star part
  have hK1 : K ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
    refine le_trans hK ?_
    have hCM : Cstar * max Cs 0 ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) :=
      mul_le_mul hCsle hCs1 hCs0' hZ0.le
    have hCM0 : 0 ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) :=
      mul_nonneg hZ0.le hAb0
    have hαle : α ≤ α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      nlinarith [hr1, hM1, hM0, hα1, hα0]
    refine le_trans (mul_le_mul_of_nonneg_right hCM hα0.le) ?_
    calc (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α
        ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|)
            * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) :=
          mul_le_mul_of_nonneg_left hαle hCM0
      _ = (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
          ring
  -- the perturbation part
  have hR1 : R ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
    refine le_trans hR ?_
    have hCe_le : Ce ≤ 1 + |Ce| + |Cs| := by
      have := abs_nonneg Cs
      linarith [le_abs_self Ce]
    have hP0 : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
      mul_nonneg (mul_nonneg hCp.le hr0) hM1'
    have hstep1 : Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * (1 + M) :=
      mul_le_mul_of_nonneg_left hX1 (mul_nonneg (mul_nonneg hCp.le hr0) hCe0.le)
    have hstep2 : Cp * α ^ (-(1 / 2 : ℝ)) * Ce * (1 + M)
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce| + |Cs|) * (1 + M) := by
      calc Cp * α ^ (-(1 / 2 : ℝ)) * Ce * (1 + M)
          = (Cp * α ^ (-(1 / 2 : ℝ)) * (1 + M)) * Ce := by ring
        _ ≤ (Cp * α ^ (-(1 / 2 : ℝ)) * (1 + M)) * (1 + |Ce| + |Cs|) :=
            mul_le_mul_of_nonneg_left hCe_le hP0
        _ = Cp * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce| + |Cs|) * (1 + M) := by ring
    have hstep3 : Cp * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce| + |Cs|) * (1 + M)
        ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      have hQ0 : 0 ≤ (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
        mul_nonneg (mul_nonneg hAb0 hr0) hM1'
      calc Cp * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce| + |Cs|) * (1 + M)
          = ((1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M)) * Cp := by ring
        _ ≤ ((1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M)) * (Cp + Cu + Cag + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hQ0
        _ = (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
            ring
    exact le_trans hstep1 (le_trans hstep2 hstep3)
  have hA0 : 0 ≤ (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
    mul_nonneg (mul_nonneg (mul_nonneg hZ0.le hAb0) hr0) hM1'
  have : K + R ≤ 2 * ((Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|)
      * α ^ (-(1 / 2 : ℝ)) * (1 + M)) := by linarith
  refine le_trans this ?_
  rw [Kcoef]
  nlinarith [hA0]

/-- **The four coefficient majorants.**  On the open quadrant the three coefficients
`ℛ(Ξ)`, `𝒰(Ξ)`, `𝒱(Ξ)` of `Ξ = PhiTil α (F_*+f) (Φs + Ef)` and the angular moment
`FK (F_*+f)` are all bounded by `Kcoef`. -/
theorem NZ_coefs {α M Ce Cs : ℝ} {f Ef Φs : Fn} {Cp Cu Cag : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M) (hCe0 : 0 < Ce)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem4 : Work.Spaces.HkMem α 4 f)
    (hmem7 : Work.Spaces.HkMem α 7 f) (hM : Work.FTS.Nonlin.Xn α f ≤ M)
    (hstar : Work.FTS.VocabO.StarPkgo α Cs Φs)
    (hgo : Work.FTS.VocabO.EllPkgGo α Ce f Ef)
    (hCp : 0 < Cp) (hCu : 0 < Cu) (hCag : 0 < Cag)
    (hresR : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ|
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
    (hresU : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ / Work.Construction.s2 θ|
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
    (hresV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ|
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
    (hUstar : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ Cu * max Cs 0 * α)
    (hsupf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |f z θ| ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag ∧
      |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag ∧
      |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag ∧
      |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
        ≤ Kcoef α M Ce Cs Cp Cu Cag := by
  intro z θ hz hθ hθ2
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hp0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hCe1 : (1 : ℝ) ≤ 1 + |Ce| + |Cs| := by
    have h1 := abs_nonneg Ce
    have h2 := abs_nonneg Cs
    linarith
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith
  have hX1 : Work.FTS.Nonlin.Xn α f ≤ 1 + M := by linarith
  have hmaxCs : max Cs 0 ≤ 1 + |Ce| + |Cs| := by
    refine le_trans (max_le (le_abs_self Cs) (abs_nonneg Cs)) ?_
    have := abs_nonneg Ce; linarith
  have hCe' : Ce ≤ 1 + |Ce| + |Cs| := by
    have := abs_nonneg Cs; linarith [le_abs_self Ce, abs_nonneg Ce]
  -- =============== 1. the `L₁₂`-additivity and the decomposition of `Ξ`
  have hL : ∀ z' : ℝ, 0 < z' → Work.Construction.L12 (Work.Construction.Ftot α f) z'
      = Work.Construction.L12 (Work.Construction.Fstar α) z' + Work.Construction.L12 f z' :=
    fun z' hz' => NZaux.L12AddFstar hα0 hα1 hso hmem4 z' hz'
  have hsliceθ : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ) z θ')
      = (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α f Ef z θ') := by
    funext θ'
    have h := hL z hz
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.Ftot] at h ⊢
    rw [h]
    ring
  have hslicez : (fun z' => Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ
          + Work.Construction.PhiTil α f Ef z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    have h := hL z' hz'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.Ftot] at h ⊢
    rw [h]
    ring
  have hval : Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α f Ef z θ := congrFun hsliceθ θ
  -- =============== 2. differentiability of the two halves
  have hΞs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα0 hα1 hstar
  have hΞszd : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ) z :=
    Work.FTS.NonlinRows.Rl1.openSlice_diffZ hΞs hz ⟨hθ, hθ2⟩
  have hΞstd : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_diffT hΞs hz ⟨hθ, hθ2⟩
  have h12cd : ContDiffOn ℝ 6 (fun z' => Work.Construction.L12 f z') (Set.Ioi (0 : ℝ)) :=
    Work.FTS.StrongPersist.contDiffOn6_L12_of hso hmem7
  have h12diff : DifferentiableAt ℝ (fun z' => Work.Construction.L12 f z') z :=
    (h12cd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hΞpdef : Work.FTS.Nonlin.PhiTg α f Ef
      = fun z' θ' => Ef z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 f z' := rfl
  have hΞpzd : DifferentiableAt ℝ (fun z' => Work.FTS.Nonlin.PhiTg α f Ef z' θ) z := by
    rw [hΞpdef]
    exact (hgo.smooth.hasDerivAt_slice ⟨hθ, hθ2⟩ hz).differentiableAt.sub
      ((differentiableAt_const ((1 / (4 * α)) * Work.Construction.s2 θ)).mul h12diff)
  have hs2d : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hΞptd : DifferentiableAt ℝ (fun θ' => Work.FTS.Nonlin.PhiTg α f Ef z θ') θ := by
    rw [hΞpdef]
    exact (Work.FTS.NonlinRows.Rl1.openSlice_diffT hgo.smooth hz ⟨hθ, hθ2⟩).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2d).mul
        (differentiableAt_const _))
  -- =============== 3. the additivity of the three operators
  have hpzP : Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pz (Work.Construction.PhiTil α f Ef) z θ := by
    have hderiv := hslicez.deriv_eq
    have hsum := Work.FTS.Nonlinear.Pieces.pz_add_of_diff hΞszd hΞpzd
    simp only [Work.Spaces.pz] at hsum hderiv ⊢
    exact hderiv.trans hsum
  have hpthP : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pth (Work.Construction.PhiTil α f Ef) z θ := by
    have hderiv := congrArg (fun F : ℝ → ℝ => deriv F θ) hsliceθ
    have hsum := Work.FTS.Nonlinear.Pieces.pth_add_of_diff hΞstd hΞptd
    simp only [Work.Spaces.pth] at hsum hderiv ⊢
    exact hderiv.trans hsum
  have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ := by
    simp only [Work.Construction.Rop]
    rw [hval, hpzP, hpthP]
    ring
  have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ := by
    simp only [Work.Construction.Uop]
    rw [hval, hpzP]
    ring
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ := by
    simp only [Work.Construction.Vop]
    rw [hval, hpthP]
    ring
  -- =============== 4. the three coefficient bounds
  have hRle : |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag := by
    have h1 := Work.FTS.NonlinRows.Rl1.star_Rop_le hα0 hstar z hz θ ⟨hθ, hθ2⟩
    have h2 := hresR z θ hz hθ hθ2
    rw [hRop]
    refine le_trans (le_trans (abs_add_le _ _) (add_le_add h1 h2)) ?_
    exact add_le_Kcoef (Cstar := 1) (K := max Cs 0 * α)
      (R := Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
      hα0 hα1 hM0 hCp hCu hCag hCe0 (by norm_num) (by linarith) hM (by simp) (le_refl _)
  have hUle : |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag := by
    have h1 := hUstar z θ hz hθI
    have h2 := hresU z θ hz hθ hθ2
    have h3 : |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ|
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
      have hs2n : Work.Construction.s2 θ ≠ 0 := by
        have hsp : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith)
            (by linarith [hθ2, Real.pi_pos])
        rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
        exact ne_of_gt hsp
      have hEq : |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ|
          = |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ| * |Work.Construction.s2 θ| := by
        rw [← abs_mul, div_mul_cancel₀ _ hs2n]
      calc |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ|
          = |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ| * |Work.Construction.s2 θ| := hEq
        _ ≤ |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ| * 1 :=
            mul_le_mul_of_nonneg_left
              (show |Work.Construction.s2 θ| ≤ 1 from Real.abs_sin_le_one (2 * θ))
              (abs_nonneg _)
        _ = |Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ| := mul_one _
        _ ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := h2
    rw [hUop]
    refine le_trans (le_trans (abs_add_le _ _) (add_le_add h1 h3)) ?_
    exact add_le_Kcoef (Cstar := Cu) (K := Cu * max Cs 0 * α)
      (R := Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
      hα0 hα1 hM0 hCp hCu hCag hCe0 hCu.le (by linarith) hM (le_refl _) (le_refl _)
  have hVle : |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ)) z θ| ≤ Kcoef α M Ce Cs Cp Cu Cag := by
    have h1 := Work.FTS.NonlinRows.Rl1.star_Vop_le hα0 hstar z hz θ ⟨hθ, hθ2⟩
    have h2 := hresV z θ hz hθ hθ2
    rw [hVop]
    refine le_trans (le_trans (abs_add_le _ _) (add_le_add h1 h2)) ?_
    exact add_le_Kcoef (Cstar := 1) (K := max Cs 0 * α)
      (R := Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f)
      hα0 hα1 hM0 hCp hCu hCag hCe0 (by norm_num) (by linarith) hM (by simp) (le_refl _)
  have hFKle : |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
      ≤ Kcoef α M Ce Cs Cp Cu Cag := by
    refine le_trans (FK_le hα0 hα1 hM0 hCag hM hsupf hz) ?_
    have hr0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
    have hM1 : (0 : ℝ) ≤ 1 + M := by linarith
    have hAb0 : (0 : ℝ) ≤ 1 + |Ce| + |Cs| := by positivity
    have hZ0 : 0 < Cp + Cu + Cag + 1 := by linarith
    have hstep : 100 * (1 + Cag) ≤ 1000 * (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) := by
      have hA : (100 : ℝ) * (1 + Cag) ≤ 1000 * (Cp + Cu + Cag + 1) := by linarith
      have hB : (1000 : ℝ) * (Cp + Cu + Cag + 1)
          ≤ 1000 * (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|) :=
        le_mul_of_one_le_right (le_of_lt (by linarith)) (by linarith)
      linarith
    calc 100 * (1 + Cag) * α ^ (-(1 / 2 : ℝ)) * (1 + M)
        = (100 * (1 + Cag)) * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) := by ring
      _ ≤ (1000 * (Cp + Cu + Cag + 1) * (1 + |Ce| + |Cs|))
            * (α ^ (-(1 / 2 : ℝ)) * (1 + M)) :=
          mul_le_mul_of_nonneg_right hstep (mul_nonneg hr0 hM1)
      _ = Kcoef α M Ce Cs Cp Cu Cag := by rw [Kcoef]; ring
  exact ⟨hRle, hUle, hVle, hFKle⟩

end Work.FTS.StrongPersist.H6Rows
