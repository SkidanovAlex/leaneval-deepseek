/-
# `CoupledVf` — the `ℋ³`-bound for `Mf f · Vf α f`

Part of the assembly of `Work.FTS.StrongPersist.L3Rhs.N0gCoupled` (the coupled half of the
`L3RhsN0gBlock` estimate).  Here:

* `Vf_integrand_le`: the pointwise bound `HkIntegrand α 3 (Vf α f) ≤ C (1/α)² HkIntegrand α 6 f`
  on `Iz × Iθ` (the three summands of `Vf`, the angular multiplier `c₂(θ) = 1 - 3 sin²θ` and the
  shifts `D_θ`, `D_z`);
* `P1_integrand_le`: the bound for the product `Mf f · Vf α f` by the algebraic multiplier
  estimate `zmul_pt`, using a uniform-in-`z` bound `K` on the `Zop`-jets of `L₁₂(f)`.

Nothing here is a proof obligation of the caller.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gDecomp
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkIntegrand HkMem HkNorm HkSq Dz Dth pth)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem cd_c2m : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
    Work.FTS.EllipticEst.Q0 := by
  unfold Work.Construction.c2m
  fun_prop

theorem cd_sinSq : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
    Work.FTS.EllipticEst.Q0 := by fun_prop

/-- **The pointwise bound for the `f`-dependent factor `Vf`.** -/
theorem Vf_integrand_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        HkIntegrand α 3 (Vf α f) z θ ≤ C * (1 / α) ^ 2 * HkIntegrand α 6 f z θ := by
  obtain ⟨Cang, hCangpos, hCangall⟩ := Work.Blocks.HkMul_ang_le 3
  have hCang2 : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        HkIntegrand α 3 (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ Cang * HkIntegrand α 3 f z θ :=
    fun α f hα hα1 hso => (hCangall α f hα hα1 hso).2.1
  refine ⟨21 + 72 * Cang, by positivity, ?_⟩
  intro α hα hα1 f hso z hz θ hθ
  -- the three summands of `Vf`
  set X1 : Fn := fun z θ => (1 / α) * f z θ with hX1
  set X2 : Fn := fun z θ => (3 / (2 * α)) * (Dth f z θ) with hX2
  set X3 : Fn := fun z θ => -(Work.Construction.c2m θ * Dz f z θ) with hX3
  have hVfeq : Vf α f = fun z θ => X1 z θ + X2 z θ + X3 z θ := by
    funext z θ
    simp only [Vf, hX1, hX2, hX3, Dth, Work.Construction.s2_eq]
    ring
  -- the smoothness certificates
  have hX1c : ContDiffOn ℝ 3 (Function.uncurry X1) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (hso.forall 3)
  have hX2c : ContDiffOn ℝ 3 (Function.uncurry X2) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul (hso.Dth.forall 3)
  have hX3c : ContDiffOn ℝ 3 (Function.uncurry X3) Work.FTS.EllipticEst.Q0 :=
    (cd_c2m.mul (hso.Dz.forall 3)).neg
  have hX12c : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => X1 z θ + X2 z θ))
      Work.FTS.EllipticEst.Q0 := hX1c.add hX2c
  -- zero cases
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
    norm_num
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin,
      Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin]
    norm_num
  -- the main case
  have h6 : ∀ (u : Fn), HkIntegrand α 3 u z θ ≤ HkIntegrand α 6 u z θ := fun u =>
    Work.FTS.StrongPersist.HkIntegrand_le_of_le α (by norm_num) u z θ
  have h46 : ∀ (u : Fn), HkIntegrand α 4 u z θ ≤ HkIntegrand α 6 u z θ := fun u =>
    Work.FTS.StrongPersist.HkIntegrand_le_of_le α (by norm_num : 4 ≤ 6) u z θ
  -- `X1`
  have hb1 : HkIntegrand α 3 X1 z θ = (1 / α) ^ 2 * HkIntegrand α 3 f z θ := by
    rw [hX1]
    exact Work.FTS.LocData.HkIntegrand_const_mul α 3 (1 / α) f z θ
  -- `X2`
  have hb2 : HkIntegrand α 3 X2 z θ = (3 / (2 * α)) ^ 2 * HkIntegrand α 3 (Dth f) z θ := by
    rw [hX2]
    exact Work.FTS.LocData.HkIntegrand_const_mul α 3 (3 / (2 * α)) (Dth f) z θ
  have hDth : HkIntegrand α 3 (Dth f) z θ ≤ HkIntegrand α 6 f z θ := by
    have h : Dth f = Work.Spaces.mixed 0 1 f := by
      funext z θ
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero, Dth]
    rw [h]
    exact le_trans (Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα 3 1 0 hso z hz θ hθ)
      (h46 f)
  -- `X3`
  have hDz : HkIntegrand α 3 (Dz f) z θ ≤ HkIntegrand α 6 f z θ := by
    have h : Dz f = Work.Spaces.mixed 1 0 f := by
      funext z θ
      simp only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter]
    rw [h]
    exact le_trans (Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα 3 0 1 hso z hz θ hθ)
      (h46 f)
  have hsin2 : HkIntegrand α 3 (fun z θ => Real.sin θ ^ 2 * Dz f z θ) z θ
      ≤ Cang * HkIntegrand α 3 (Dz f) z θ :=
    hCang2 α (Dz f) hα hα1 hso.Dz z hz θ hθ
  -- the two additivity steps
  have step1 : HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ + X3 z θ) z θ
      ≤ 2 * HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ) z θ + 2 * HkIntegrand α 3 X3 z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3 hX12c hX3c z hz θ hθ
  have step2 : HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ) z θ
      ≤ 2 * HkIntegrand α 3 X1 z θ + 2 * HkIntegrand α 3 X2 z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3 hX1c hX2c z hz θ hθ
  -- decompose `X3 = -Dz f + 3 (sin²θ · Dz f)`
  have hX3eq : X3 = fun z θ => (-1 : ℝ) * Dz f z θ + 3 * (Real.sin θ ^ 2 * Dz f z θ) := by
    funext z θ
    simp only [hX3, Work.Construction.c2m_eq]
    have hcos : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
      rw [Real.cos_two_mul', Real.cos_sq']; ring
    rw [hcos]
    ring
  have hX3c' : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => (-1 : ℝ) * Dz f z θ
      + 3 * (Real.sin θ ^ 2 * Dz f z θ))) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (hso.Dz.forall 3)).add
      (contDiffOn_const.mul (((by fun_prop : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2)
        Work.FTS.EllipticEst.Q0)).mul (hso.Dz.forall 3)))
  have step3 : HkIntegrand α 3 X3 z θ
      ≤ 2 * HkIntegrand α 3 (fun z θ => (-1 : ℝ) * Dz f z θ) z θ
        + 2 * HkIntegrand α 3 (fun z θ => 3 * (Real.sin θ ^ 2 * Dz f z θ)) z θ := by
    rw [hX3eq]
    exact Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3
      (contDiffOn_const.mul (hso.Dz.forall 3))
      (contDiffOn_const.mul (((by fun_prop : ContDiffOn ℝ 3
        (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0)).mul (hso.Dz.forall 3)))
      z hz θ hθ
  have hcm1 : HkIntegrand α 3 (fun z θ => (-1 : ℝ) * Dz f z θ) z θ
      = 1 * HkIntegrand α 3 (Dz f) z θ := by
    rw [Work.FTS.LocData.HkIntegrand_const_mul α 3 (-1) (Dz f) z θ]
    norm_num
  have hcm3 : HkIntegrand α 3 (fun z θ => 3 * (Real.sin θ ^ 2 * Dz f z θ)) z θ
      = 9 * HkIntegrand α 3 (fun z θ => Real.sin θ ^ 2 * Dz f z θ) z θ := by
    rw [Work.FTS.LocData.HkIntegrand_const_mul α 3 3
      (fun z θ => Real.sin θ ^ 2 * Dz f z θ) z θ]
    norm_num
  -- scaling facts
  have hα2le : α ^ 2 ≤ 1 := by nlinarith [hα1, hα]
  have hone : (1 : ℝ) ≤ (1 / α) ^ 2 := by
    rw [div_pow, one_pow]
    exact one_le_one_div (by positivity) hα2le
  have hcoef : (3 / (2 * α)) ^ 2 = (9 / 4) * (1 / α) ^ 2 := by
    field_simp
    ring
  have hI6nn : 0 ≤ HkIntegrand α 6 f z θ := Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hX12b : HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ) z θ
      ≤ (2 * (1 / α) ^ 2 + (9 / 2) * (1 / α) ^ 2) * HkIntegrand α 6 f z θ := by
    have h := step2
    rw [hb1, hb2, hcoef] at h
    have h3 : (9 / 4) * (1 / α) ^ 2 * HkIntegrand α 3 (Dth f) z θ
        ≤ (9 / 4) * (1 / α) ^ 2 * HkIntegrand α 6 f z θ :=
      mul_le_mul_of_nonneg_left hDth (by positivity)
    have h1 : (1 / α) ^ 2 * HkIntegrand α 3 f z θ
        ≤ (1 / α) ^ 2 * HkIntegrand α 6 f z θ :=
      mul_le_mul_of_nonneg_left (h6 f) (by positivity)
    nlinarith [h, h1, h3]
  have hX3b : HkIntegrand α 3 X3 z θ
      ≤ (4 + 36 * Cang) * HkIntegrand α 6 f z θ := by
    have h := step3
    rw [hcm1, hcm3] at h
    have hs : HkIntegrand α 3 (fun z θ => Real.sin θ ^ 2 * Dz f z θ) z θ
        ≤ Cang * HkIntegrand α 6 f z θ :=
      le_trans hsin2 (mul_le_mul_of_nonneg_left hDz hCangpos.le)
    nlinarith [h, hs, hDz, hI6nn, hCangpos]
  have hfinal : HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ + X3 z θ) z θ
      ≤ (21 + 72 * Cang) * (1 / α) ^ 2 * HkIntegrand α 6 f z θ := by
    have h := step1
    have h2 : 2 * HkIntegrand α 3 (fun z θ => X1 z θ + X2 z θ) z θ
        ≤ 2 * ((2 * (1 / α) ^ 2 + (9 / 2) * (1 / α) ^ 2) * HkIntegrand α 6 f z θ) :=
      mul_le_mul_of_nonneg_left hX12b (by norm_num)
    have h3 : 2 * HkIntegrand α 3 X3 z θ
        ≤ 2 * ((4 + 36 * Cang) * HkIntegrand α 6 f z θ) :=
      mul_le_mul_of_nonneg_left hX3b (by norm_num)
    have h4 : (2 * (2 * (1 / α) ^ 2 + (9 / 2) * (1 / α) ^ 2) + 2 * (4 + 36 * Cang))
        * HkIntegrand α 6 f z θ ≤ (21 + 72 * Cang) * (1 / α) ^ 2 * HkIntegrand α 6 f z θ := by
      refine mul_le_mul_of_nonneg_right ?_ hI6nn
      nlinarith [hone, hCangpos]
    nlinarith [h, h2, h3, h4]
  rw [hVfeq]
  exact hfinal

/-! ## The `Vf`-part of the coupled product -/

theorem smoothOpen_sin_two : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ θ : ℝ => Real.sin (2 * θ))) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun _ θ : ℝ => Real.sin (2 * θ))
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
  rw [h1]
  exact (((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn)).of_le le_top

theorem smoothOpen_c2m : Work.FTS.EllipticEst.SmoothOpen
    (fun _ θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun _ θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
      = fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2 := rfl
  rw [h1]
  exact ((((Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)).sub
    ((Real.contDiff_sin.comp contDiff_snd).pow 2)).contDiffOn)).of_le le_top

theorem smoothOpen_Vf {α : ℝ} {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) : Work.FTS.EllipticEst.SmoothOpen (Vf α f) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (1 / α) * f z θ) :=
    contDiffOn_const.mul hso
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)) :=
    contDiffOn_const.mul (smoothOpen_sin_two.mul hso.pth)
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Spaces.Dz f z θ) :=
    smoothOpen_c2m.mul hso.Dz
  have hmain : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (1 / α) * f z θ + (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)
        - (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Spaces.Dz f z θ) := (h1.add h2).sub h3
  have hfun : (fun z θ =>
      (1 / α) * f z θ + (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)
        - (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Spaces.Dz f z θ) = Vf α f := by
    funext z θ
    simp only [Vf, Work.Construction.s2_eq, Work.Construction.c2m_eq]
    ring
  rwa [hfun] at hmain

/-- **The pointwise bound for `Mf f · Vf α f`.** -/
theorem P1_integrand_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hL12 : Work.Construction.L12 f 0 = 0)
    {Cjet : ℝ} (hCjetnn : 0 ≤ Cjet)
    (hjet : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z|
        ≤ Cjet * Work.Spaces.HkNorm α 4 f)
    {CV : ℝ}
    (hVf : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (Vf α f) z θ
        ≤ CV * (1 / α) ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Vf α f z θ) z θ
        ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 3 * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2
            * CV * (1 / α) ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ := by
  intro z hz θ hθ
  set φ : ℝ → ℝ := fun z => Work.Construction.L12 f z with hφdef
  have hφeq : (fun z θ => Mf f z θ * Vf α f z θ) = fun z θ => φ z * Vf α f z θ := by
    funext z θ
    simp only [Mf, hφdef]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [hφeq, Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
    norm_num
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [hφeq, Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin,
      Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα hsin]
    norm_num
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le hθ.1 with h | h
      · exact h
      · exact absurd (by rw [← h]; simp) hsin
    · rcases lt_or_eq_of_le hθ.2 with h | h
      · exact h
      · exact absurd (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hsin
  have hsoVf : Work.FTS.EllipticEst.SmoothOpen (Vf α f) := smoothOpen_Vf hso
  have hφc : ∀ i : ℕ, i ≤ 3 → ContDiffOn ℝ (i : WithTop ℕ∞) φ (Set.Ioi (0 : ℝ)) := by
    intro i hi
    have h4 : ContDiffOn ℝ 4 φ (Set.Ioi (0 : ℝ)) :=
      Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hso hmem (by norm_num)
    exact h4.of_le (by exact_mod_cast (by omega : i ≤ 4))
  have hle : ∀ i : ℕ, (i : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := fun i =>
    WithTop.coe_le_coe.mpr le_top
  have hVs : ∀ i : ℕ, ContDiffOn ℝ (i : WithTop ℕ∞) (fun z' => Vf α f z' θ)
      (Set.Ioi (0 : ℝ)) := fun i =>
    ((hsoVf.curry_z hθ').of_le (hle i))
  have hDs : ∀ i j : ℕ, ContDiffOn ℝ (j : WithTop ℕ∞)
      (fun z' => Work.Spaces.DthIter i (Vf α f) z' θ) (Set.Ioi (0 : ℝ)) := fun i j =>
    (((hsoVf.DthIter i).curry_z hθ').of_le (hle j))
  have hexpZ : ∀ i ≤ 3, Work.Spaces.DzIter i (fun z θ => φ z * Vf α f z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.Zop^[b] φ z * Work.Spaces.DzIter (i - b) (Vf α f) z θ) :=
    fun i hi => Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i φ (Vf α f) isOpen_Ioi
      (hφc i hi) (hVs i) z hzpos
  have hexpM : ∀ j i, 1 ≤ i → i + j ≤ 3 →
      Work.Spaces.mixed j i (fun z θ => φ z * Vf α f z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Spaces.Zop^[b] φ z * Work.Spaces.mixed (j - b) i (Vf α f) z θ) :=
    fun j i hi hij => Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i φ (Vf α f) isOpen_Ioi
      (hφc j (by omega)) (hDs i j) z hzpos
  have hB : ∀ b ≤ 3, |Work.Spaces.Zop^[b] φ z| ≤ Cjet * Work.Spaces.HkNorm α 4 f := by
    intro b hb
    exact hjet b hb z hzpos
  have hKnn : 0 ≤ Cjet * Work.Spaces.HkNorm α 4 f :=
    mul_nonneg hCjetnn (Real.sqrt_nonneg _)
  have hzm := Work.FTS.StrongPersist.L3Aux.zmul_pt α 3 φ (Vf α f) hKnn hB hexpZ hexpM
  rw [hφeq]
  have htarget := hVf z hz θ hθ
  have hzmc : Work.FTS.StrongPersist.L3Aux.zmulConst 3
      * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2
        * Work.Spaces.HkIntegrand α 3 (Vf α f) z θ
      ≤ Work.FTS.StrongPersist.L3Aux.zmulConst 3
        * (1 + Cjet * Work.Spaces.HkNorm α 4 f) ^ 2
          * (CV * (1 / α) ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
    mul_le_mul_of_nonneg_left htarget
      (mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos 3).le (sq_nonneg _))
  exact le_trans hzm (le_trans hzmc (le_of_eq (by ring)))

end Work.FTS.StrongPersist.L3Rhs
