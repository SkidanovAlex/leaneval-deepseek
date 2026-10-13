import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.Nonlinear.Open.Rl2
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.FinalClock.L12LinearSub
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpMod

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The two elementary shapes used by the transport difference

The datum of the transport zero mode is `F_g(z,θ) = 3·D_θ g(z,θ)/(1+z)`; this file proves the
Lipschitz (difference) estimate for the `L₁₂`-zero-mode of that datum by

1. linearising `L₁₂` in its profile (`Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen`, for
   `C^∞`-on-the-open-quadrant, `ℋ⁴`-honest data);
2. identifying the difference datum with the datum of `h = g - g'` (a *pointwise* identity which
   needs the angular derivatives only off the two angular boundary lines);
3. bounding the resulting `L₁₂(3·D_θ h/(1+z))(0)` by the row estimate `Nonlinear.Open.Rl2`
   applied to `h`, and comparing `ℋ⁴` with `ℋ⁵`.

The regularity/honesty of the datum `F_g` is produced from `g`'s `RegQ α 6` by writing
`3/(1+z) = 3 - 3·z/(1+z)` and using the bounded-radial-factor calculus (`NRow10aux`). -/

/-- `(z,θ) ↦ 3·f(z,θ)/(1+z)` is `C^∞` on the open quadrant whenever `f` is. -/
theorem smoothOpen_three_div_mul {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * f z θ / (1 + z)) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => 3 / (1 + z)) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 3 / (1 + p.1)) Work.FTS.EllipticEst.Q0
    refine contDiffOn_const.div (contDiffOn_const.add contDiffOn_fst) ?_
    intro p hp
    have hp1 : (0 : ℝ) < 1 + p.1 := by
      have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      linarith
    positivity
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (3 / (1 + z)) * f z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul h1 hf
  have hfun : Function.uncurry (fun z θ => 3 * f z θ / (1 + z))
      = Function.uncurry (fun z θ => (3 / (1 + z)) * f z θ) := by
    funext p
    simp only [Function.uncurry]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  simp only [Work.FTS.EllipticEst.SmoothOpen] at h2 ⊢
  rw [hfun]
  exact h2

/-- **Angular additivity of `D_θ` for a pointwise decomposition.**  If `g = g' + h` pointwise
and `g'`, `h` are `C^∞` on the open quadrant, then `D_θ g = D_θ g' + D_θ h` on
`(0,∞) × [0,π/2]`: in the interior this is the product rule `deriv_add`, and on the two
boundary lines `θ = 0`, `θ = π/2` both sides vanish because `sin(2θ) = 0` there. -/
theorem Dth_add_of_pointwise {g g' h : ℝ → ℝ → ℝ}
    (hg'sm : Work.FTS.EllipticEst.SmoothOpen g') (hhsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hgh : ∀ z θ, g z θ = g' z θ + h z θ) :
    ∀ z θ, 0 < z → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dth g z θ = Work.Spaces.Dth g' z θ + Work.Spaces.Dth h z θ := by
  intro z θ hz hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    simp only [Work.Spaces.Dth]
    rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
    ring
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · subst h2
      simp only [Work.Spaces.Dth]
      rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      ring
    · have hpth := Work.FTS.GalFields.RHS.pth_add_of_smoothOpen hg'sm hhsm hgh z θ hz h0 h2
      simp only [Work.Spaces.Dth]
      rw [hpth]
      ring

/-- Congruence of the `L₁₂`-density on the angular interval. -/
theorem L12dens_congr_of_Iθ {a b : ℝ → ℝ → ℝ} {s : ℝ}
    (h : ∀ θ ∈ Work.Spaces.Iθ, a s θ = b s θ) :
    Work.Construction.L12dens a s = Work.Construction.L12dens b s := by
  rw [Work.Construction.L12dens, Work.Construction.L12dens, Work.FM.L12dens]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [h θ hθ]

/-- Congruence of `L₁₂` from the congruence of its densities on the outer half-line. -/
theorem L12_congr_of_dens {a b : ℝ → ℝ → ℝ} {z : ℝ}
    (h : ∀ s ∈ Set.Ioi z, Work.Construction.L12dens a s = Work.Construction.L12dens b s) :
    Work.Construction.L12 a z = Work.Construction.L12 b z := by
  rw [Work.Construction.L12, Work.Construction.L12, Work.FM.L12]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h

/-- **The datum `3·D_θ g/(1+z)` of a `RegQ α 5`-profile is `C^∞` on the open quadrant and
honest in `ℋ⁴`.**  The proof writes `3/(1+z) = 3 - 3·z/(1+z)`, splits the datum into
`3·D_θ g` and `3·(φ·D_θ g)` (`φ(z) = z/(1+z)`, bounded with all its `D_z`-iterates bounded by
`1`), and uses the closure of `ℋ⁴` under subtraction on smooth data. -/
theorem smoothOpen_and_hkMem_three_div_Dth {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hreg : Work.FTS.Nonlin.RegQ α 5 g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) ∧
      Work.Spaces.HkMem α 4 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hreg.1
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) := hsm.Dth
  have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
    Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α 4 (by linarith) hreg
  obtain ⟨Cphi, _hCphi, hmulphi⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  have hphiMem : Work.Spaces.HkMem α 4
      (fun z θ => Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth g z θ) :=
    (hmulphi hα hα1 ⟨hDthSm, hDthMem⟩).1
  have hphiSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen hDthSm
  constructor
  · exact smoothOpen_three_div_mul hDthSm
  · have h1 : Work.Spaces.HkMem α 4 (fun z θ => 3 * Work.Spaces.Dth g z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 4 3 hDthMem
    have h2 : Work.Spaces.HkMem α 4
        (fun z θ => 3 * (Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth g z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 4 3 hphiMem
    have hsub : Work.Spaces.HkMem α 4
        (fun z θ => 3 * Work.Spaces.Dth g z θ
          - 3 * (Work.FTS.NonlinRows.NRow10aux.phiF z * Work.Spaces.Dth g z θ)) :=
      Work.FTS.GalBasis.hkMem_sub_open α 4
        (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hDthSm)
        (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hphiSm) h1 h2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsub ?_
    intro z hz θ hθ
    have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < z from hz])
    simp only [Work.FTS.NonlinRows.NRow10aux.phiF]
    field_simp
    ring

theorem transport_L12_diff {α α₂ Ci Ct Ce Cs : ℝ}
    {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ g g' h : Work.FTS.Galerkin.Fn,
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h →
      (∀ z θ, h z θ = g z θ - g' z θ) → α ≤ 1 →
      |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0
        - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g' z θ / (1 + z)) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h := by
  obtain ⟨K0, hK0pos, hK0⟩ := Work.FTS.Nonlinear.Open.Rl2 IP hN hE
  refine ⟨K0 + 1, by linarith, ?_⟩
  intro g g' h hg hg' hh hdiff hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  -- the pointwise decomposition `g = g' + h`
  have hgh : ∀ z θ, g z θ = g' z θ + h z θ := by
    intro z θ
    have := hdiff z θ
    linarith
  have hg'sm : Work.FTS.EllipticEst.SmoothOpen g' :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg'.reg.1
  have hhsm : Work.FTS.EllipticEst.SmoothOpen h :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hh.reg.1
  -- regularity/honesty of the two data `3·D_θg/(1+z)`, `3·D_θg'/(1+z)`
  have hreg5g : Work.FTS.Nonlin.RegQ α 5 g :=
    Work.FTS.LocDataExt.RegQ_mono (by norm_num) hg.reg
  have hreg5g' : Work.FTS.Nonlin.RegQ α 5 g' :=
    Work.FTS.LocDataExt.RegQ_mono (by norm_num) hg'.reg
  have hdataG := smoothOpen_and_hkMem_three_div_Dth hα hα1 hreg5g
  have hdataG' := smoothOpen_and_hkMem_three_div_Dth hα hα1 hreg5g'
  -- linearity of `L₁₂` in the profile
  have hlin : Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0
      - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g' z θ / (1 + z)) 0
      = Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)
          - 3 * Work.Spaces.Dth g' z θ / (1 + z)) 0 :=
    Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen hdataG.1 hdataG'.1
      hdataG.2 hdataG'.2 0 le_rfl
  -- the difference datum is the datum of `h`
  have hcongr : Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)
        - 3 * Work.Spaces.Dth g' z θ / (1 + z)) 0
      = Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth h z θ / (1 + z)) 0 := by
    refine L12_congr_of_dens (fun s hs => ?_)
    refine L12dens_congr_of_Iθ (fun θ hθ => ?_)
    have hDthAdd := Dth_add_of_pointwise hg'sm hhsm hgh s θ hs hθ
    rw [hDthAdd]
    ring
  rw [hlin, hcongr]
  -- the row estimate at `h`, and the `ℋ⁴ ≤ ℋ⁵` comparison
  have hb := hK0 hα hα1 hαα₂ hh hstar.toStarPkgo (hell h hh)
  have hXn : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num)
      (Work.FTS.OpenPkg.galClass_HkMem5 hh)
  have hX0 : 0 ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have hXg0 : 0 ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hXg'0 : 0 ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  calc |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth h z θ / (1 + z)) 0|
      ≤ K0 * Work.FTS.Nonlin.Xn α h := hb
    _ ≤ K0 * Work.FTS.GalFields.Xn5 α h :=
        mul_le_mul_of_nonneg_left hXn (le_of_lt hK0pos)
    _ ≤ (K0 + 1) * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
          * Work.FTS.GalFields.Xn5 α h := by
        refine mul_le_mul_of_nonneg_right ?_ hX0
        nlinarith [hK0pos.le, hXg0, hXg'0]

end Work.FTS.GalFields.RHS.SharpMod
