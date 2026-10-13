/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/VopAux/orthSourceHkNorm_classC` — the `orthSource` transfer on the class `C`

For a datum `g` of the linear class `C` (`Work.FTS.ClassC.ClassC α g`) and every level `k ≤ 7`,

  `|orthSource g|_{ℋ^k} ≤ C |g|_{ℋ^k}`,

where `orthSource g = g - (15/4)·sin 2θ · F_*(g)` is the source of the *straightened* elliptic
problem (`bslOp α Ψ̂ = orthSource g`) and `F_*(g)(z) = ∫_θ g(z,θ) sinθcos²θ dθ` is the angular
moment.  This is the class-`C` instance of `Work.FTS.EllSol.orthSource_HkNorm_le` (which is stated
for `GalClass`/`EllClassO`); the only class fields used are `SmoothOpen g`, `HkMem α k g` and the
all-order smoothness of `F_*(g)` — all of which `ClassC` carries (`reg`, `mem`, `fsm`), the last
one replacing the `EllClassO`-ODE route of the sibling.

The two inputs are the proved `Cert.Fstar_Hk_le_open` (the bound
`|F_*(g)·sin 2θ|_{ℋ^k} ≤ C|g|_{ℋ^k}` from the *smoothness + honesty* of `g` alone) and the
honesty of that term (`Cert.HkMem_bmom_sin_of_smoothOpen`); the rest is the triangle inequality.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.EllipticEst.Fstar_Hk_le_open
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The `orthSource` transfer on the class `C`.** -/
theorem orthSourceHkNorm_classC (k : ℕ) (hk : k ≤ 7) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : Fn), 0 < α → α ≤ 1 → ClassC α g →
      Work.Spaces.HkNorm α k (Work.Elliptic.orthSource g) ≤ C * Work.Spaces.HkNorm α k g := by
  obtain ⟨Cf, hCfpos, hCf⟩ := Work.FTS.EllipticEst.Fstar_Hk_le_open k
  refine ⟨Real.sqrt 2 * (1 + (15 / 4) * Cf), ?_, ?_⟩
  · have h2 : (0 : ℝ) < 1 + (15 / 4) * Cf := by
      have := mul_pos (by norm_num : (0 : ℝ) < 15 / 4) hCfpos
      linarith
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) h2
  · intro α g hα hα1 hg
    have hgsm : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
    have hgraw : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry g)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hgsm
    have hmem : Work.Spaces.HkMem α k g :=
      Work.FTS.EllipticEst.TT.HkMem_descend_open hk hgraw hg.mem
    have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hg.fsm
    have hsin : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
    have hPHIsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.SmoothOpen.sep_mul hFsm hsin
    have hPHIraw : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hPHIsm
    have hPHImem : Work.Spaces.HkMem α k
        (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
      have h :=
        Work.FTS.EllipticEst.Cert.HkMem_bmom_sin_of_smoothOpen α k g hα hα1 hgsm hmem
      simpa only [Work.FTS.EllipticEst.Bmom_zero] using h
    have hSsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
      hPHIsm.const_mul' (-(15 / 4))
    have hSraw : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry
          (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSsm
    have hSmem : Work.Spaces.HkMem α k
        (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ))) :=
      Work.FTS.LocData.HkMem_const_mul α k (-(15 / 4)) hPHImem
    have horth : Work.Elliptic.orthSource g
        = fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)) := by
      funext z θ
      simp only [Work.Elliptic.orthSource]
      ring
    have hsum := Work.FTS.EllipticEst.HkNorm_add_le α k hgraw hSraw hmem hSmem
    have hcm := Work.FTS.EllipticEst.HkNorm_const_mul α k (-(15 / 4)) hPHIraw
    have hPhi := hCf α g hα hα1 hgraw hmem
    rw [horth]
    calc Work.Spaces.HkNorm α k
          (fun z θ => g z θ + (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k g
            + Work.Spaces.HkNorm α k
              (fun z θ => (-(15 / 4)) * (Work.Elliptic.Fstar g z * Real.sin (2 * θ)))) :=
          hsum
      _ = Real.sqrt 2 * (Work.Spaces.HkNorm α k g
            + (15 / 4) * Work.Spaces.HkNorm α k
              (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))) := by
          rw [hcm, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 15 / 4)]
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k g
            + (15 / 4) * (Cf * Work.Spaces.HkNorm α k g)) := by
          have h1 : (15 / 4) * Work.Spaces.HkNorm α k
                (fun z θ => Work.Elliptic.Fstar g z * Real.sin (2 * θ))
              ≤ (15 / 4) * (Cf * Work.Spaces.HkNorm α k g) :=
            mul_le_mul_of_nonneg_left hPhi (by norm_num)
          exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * (1 + (15 / 4) * Cf) * Work.Spaces.HkNorm α k g := by ring

end Work.FTS.ClassC
