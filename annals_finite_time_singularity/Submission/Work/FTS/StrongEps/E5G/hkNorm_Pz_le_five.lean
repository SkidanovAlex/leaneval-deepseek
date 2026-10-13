import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5G.hkNorm_Pz_le_four
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.EllipticEst.HkNorm_add_fts
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem hkNorm_Pz_le_five : ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Pz f) ≤ A * Work.Spaces.HkNorm α 5 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα f hfsm hm5
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    -- the `ℋ⁴`-membership used by the zero-mode estimate
    have hm4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm 4 (by norm_num) hm5
    have hnorm45 : Work.Spaces.HkNorm α 4 f ≤ Work.Spaces.HkNorm α 5 f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) hm5
    -- the zero-mode bound, upgraded from `ℋ⁴` to `ℋ⁵`
    have hl12_4 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hm4⟩
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 5 f :=
      le_trans hl12_4 (mul_le_mul_of_nonneg_left hnorm45 hC₁nn)
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    -- the correction coefficient is controlled by the `ℋ⁵`-norm
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 5 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f := by ring
    -- the correction profile
    have hbmem : Work.Spaces.HkMem α 5 Work.FTS.StrongEps.bump :=
      Work.FTS.StrongEps.PZeroAux.hkMem_bump α 5
    have hbnorm : Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump ≤ B :=
      hB α hα 5 (by norm_num)
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen _
        Work.FTS.StrongEps.smoothOpen_bump
    have hgmem : Work.Spaces.HkMem α 5
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _ hbmem
    -- `Pz f` in the additive shape needed by the subadditivity lemma
    have hPz : Work.FTS.StrongEps.Pz f
        = fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply]
      ring
    rw [hPz]
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α 5
      (fun n => hfsm.forall n) (fun n => hgsm.forall n) hm5 hgmem
    have hcm : Work.Spaces.HkNorm α 5
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 5 _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α 5 (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 5 f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 5 f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α 5 f := by ring

end Work.FTS.StrongEps.E5G
