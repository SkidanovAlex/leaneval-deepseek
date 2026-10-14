import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.PzHkNormFour =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.PZeroAux.PzHkNormFour`

The projection `Work.FTS.StrongEps.Pz` of the lead's design (`PZero.lean`),

  `P₀ f = f − (L₁₂ f 0 / L₁₂(bump)(0)) • bump`,

is *bounded* in the weighted `ℋᵏ`-norm, **with the input measured in `ℋ⁴`**:

  `∃ A > 0, ∀ α ∈ (0,1], ∀ k ≤ 4, ∀ f, SmoothOpen f → HkMem α 4 f →
      ‖P₀ f‖_{ℋᵏ} ≤ A ‖f‖_{ℋ⁴}`.

This is the `ℋ⁴`-input sharpening of the sibling lemma `hkNorm_Pz_le` (same directory), which
measures the input in `ℋ⁶`.  The proof is the same argument; the only place where the *input*
order is used is the zero-mode estimate `OpenPkg.l12zero_field`,
`|L₁₂ f 0| ≤ 3 |f|_{ℋ⁴}`, whose hypothesis is exactly the open-quadrant class
`HQo α 4 f = SmoothOpen f ∧ HkMem α 4 f`.  Every other ingredient is order-agnostic:

* **subadditivity** of the weighted norm on the open quadrant, `HkNorm_add_fts`;
* **absolute homogeneity**, `HkNorm_const_mul` (here applied to `bump`, which is `C^∞` on the
  whole plane, hence `SmoothOpen`);
* a **uniform bound** for the correction profile, `exists_HkNorm_bump_le`, and its membership
  `hkMem_bump` (both proved in the sibling file);
* the monotonicity `HkNorm α k f ≤ HkNorm α 4 f` for `k ≤ 4` (`StrongLWP.HkNorm_mono_of_mem`)
  and `pzNorm > 0` (`PZeroAux.pzNorm_pos`).

Everything is assembled with `Work.Spaces.HkNorm α k = √(HkSq α k)`, ending with
`A = √2 (1 + 3 B / pzNorm)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **`P₀` is bounded on `ℋᵏ`, uniformly in the parameter `α` and the order `k ≤ 4`, with the
input measured in `ℋ⁴`.**

`P₀ f = f + (−c) • bump` with `c = L₁₂ f 0 / pzNorm`; the subadditivity of the norm on the open
quadrant (`HkNorm_add_fts`), its absolute homogeneity (`HkNorm_const_mul`), the proven zero-mode
bound `|L₁₂ f 0| ≤ 3 |f|_{ℋ⁴}` (`OpenPkg.l12zero_field`, whose hypothesis is `HQo α 4 f`), the
monotonicity `|f|_{ℋᵏ} ≤ |f|_{ℋ⁴}` and the uniform bound `‖bump‖_{ℋᵏ} ≤ B` give the constant
`A = √2 (1 + 3 B / pzNorm)`. -/
theorem PzHkNormFour :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 4 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz f) ≤ A * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα k hk f hfsm hm4
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    have hmemk : Work.Spaces.HkMem α k f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm k hk hm4
    -- the zero-mode bound (input order four, exactly `HQo α 4 f`)
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hm4⟩
    have hnormk4 : Work.Spaces.HkNorm α k f ≤ Work.Spaces.HkNorm α 4 f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := k) hk hm4
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    -- the correction coefficient is controlled by the `ℋ⁴`-norm
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 4 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by ring
    -- the correction profile
    have hbmem : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump := hkMem_bump α k
    have hbnorm : Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B := hB α hα k (by omega)
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry (fun z θ => (-(Work.Construction.L12 f 0
          / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => (smoothOpen_const_mul_gen (-(Work.Construction.L12 f 0
        / Work.FTS.StrongEps.pzNorm)) Work.FTS.StrongEps.smoothOpen_bump).forall n
    have hgmem : Work.Spaces.HkMem α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      HkMem_const_mul_gen _ hbmem
    -- `Pz f` in the additive shape needed by the subadditivity lemma
    have hPz : Work.FTS.StrongEps.Pz f
        = fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply]
      ring
    rw [hPz]
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α k
      (fun n => hfsm.forall n) hgsm hmemk hgmem
    have hcm : Work.Spaces.HkNorm α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α k _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α k (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 4 f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hnormk4 ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α 4 f := by ring

end Work.FTS.StrongEps.PZeroAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.PzJepsHkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.PZeroAux

theorem PzJepsHkMem {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {f : ℝ → ℝ → ℝ} (k : ℕ)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f)) := by
  -- `J_ε` preserves `ℋ^k`-membership (E1, `HkMem_Jeps`) ...
  have hJ : Work.Spaces.HkMem α k (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsm hmem
  -- ... and it is `C^∞` on the open quadrant.
  have hsJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsm
  -- The projection subtracts a constant multiple of the correction profile `bump`.
  set c : ℝ := -(Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0
      / Work.FTS.StrongEps.pzNorm) with hc
  have hb : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump :=
    Work.FTS.StrongEps.PZeroAux.classC_Pz_hkMem_bump α k
  have hcm : Work.Spaces.HkMem α k (fun z θ => c * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen c hb
  have hscm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * Work.FTS.StrongEps.bump z θ) :=
    Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen c Work.FTS.StrongEps.smoothOpen_bump
  have hPz : Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f)
      = fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ + c * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, hc]
    ring
  rw [hPz]
  exact Work.FTS.EllipticEst.HkMem_add_open hsJ hscm hJ hcm

end Work.FTS.StrongEps.PZeroAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false

/-! ## The two families of summands of `HkIntegrand` -/






/-! ## Monotonicity of the angular weight in `α` -/





/-! ## The pointwise comparison of the integrands -/



/-! ## Monotonicity of `HkSq` -/


/-! ## The target -/


end Work.FTS.StrongEps.PZeroAux
end
end
