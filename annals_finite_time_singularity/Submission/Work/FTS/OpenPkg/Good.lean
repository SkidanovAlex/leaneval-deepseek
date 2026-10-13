/-
# `Work.FTS.OpenPkg.Good` — the pair (`C^4` on the quadrant, honest in `ℋ⁴`)

The primed `IP`-interface `Work.FTS.OpenPkg.N4Extra'` consumes, in its `add`/`smul`/`neg`/
`congr` clauses, the *honesty* `Work.Spaces.HkMem α 4 f` of the functions it is applied to.
For the pieces of the §8 assembly the honesty is part of the row interface
(`Work.FTS.OpenPkg.PiecesHk`), and for *sums* of pieces it has to be produced from the
`C^4`-smoothness of the summands (`Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four`).

This file packages the pair "`C^4` on the open quadrant `Q0` **and** honest in `ℋ⁴`" as the
structure `Good`, with the closure properties (`add`, `const_mul`, `neg`, and transfer along
equality on `Q0`) that the assembly needs.  It also records the `C^4`-smoothness of the two
auxiliary blocks of `gRHS`, `AK α` and the modulation term `N_*`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A function which is `C^4` on the open quadrant and honest in `ℋ^4`. -/
structure Good (α : ℝ) (f : Fn) : Prop where
  c4 : ContDiffOn ℝ 4 (Function.uncurry f) Q0
  hk : Work.Spaces.HkMem α 4 f

namespace Good

variable {α : ℝ} {f g : Fn}

/-- Sums of good functions are good. -/
theorem add (hf : Good α f) (hg : Good α g) :
    Good α (fun z θ => f z θ + g z θ) :=
  ⟨hf.c4.add hg.c4,
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four hf.c4 hg.c4 hf.hk hg.hk⟩

/-- Constant multiples of good functions are good (the integrand is homogeneous of degree two). -/
theorem const_mul (c : ℝ) (hf : Good α f) : Good α (fun z θ => c * f z θ) := by
  refine ⟨contDiffOn_const.mul hf.c4, ?_⟩
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := fun z θ => c * f z θ)
    (M := fun z θ => c ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
    (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α le_rfl
      (contDiffOn_const.mul hf.c4)) ?_ ?_ ?_
  · intro z hz
    exact (hf.hk.1 z hz).const_mul (c ^ 2)
  · have htarget : IntegrableOn
        (fun z : ℝ => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        Work.Spaces.Iz := hf.hk.2.const_mul (c ^ 2)
    refine htarget.congr_fun ?_ measurableSet_Ici
    intro z hz
    exact (MeasureTheory.integral_const_mul (c ^ 2)
      (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)).symm
  · intro z hz θ hθ
    rw [Work.FTS.LocData.HkIntegrand_const_mul]

/-- Negation preserves goodness. -/
theorem neg (hf : Good α f) : Good α (fun z θ => -f z θ) := by
  have := hf.const_mul (-1)
  simpa using this

/-- Transfer of goodness along equality on the open quadrant. -/
theorem of_eqOn (hu : Good α f) (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
    f z θ = g z θ) : Good α g :=
  ⟨hu.c4.congr (fun p hp => (h p.1 hp.1 p.2 hp.2).symm),
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hu.hk h⟩

/-- Transfer of goodness along an identity valid on the open quadrant. -/
theorem of_eqOn_Qd (hu : Good α f) (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = g z θ) :
    Good α g :=
  hu.of_eqOn (fun z hz θ hθ => h z θ ⟨hz, hθ⟩)

end Good

/-! ## The two auxiliary blocks -/

/-- `Γ(θ) = (sinθcos²θ)^{α/3}` is smooth on the quadrant. -/
theorem contDiffOn_Gam_Q0 (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Q0 := by
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2) Q0 :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Q0, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [Set.mem_Ioo.mp hp.2 |>.1, Real.pi_pos])
      (by linarith [Set.mem_Ioo.mp hp.2 |>.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
    positivity
  simpa only [Work.Spaces.Gam] using
    hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

/-- `AK α = (Γ(θ)/c α)·2z²/(1+z)³` is smooth on the quadrant. -/
theorem contDiffOn_four_AK (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.AK α)) Q0 := by
  have hcne : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hGam := (contDiffOn_Gam_Q0 α 4).div contDiffOn_const (fun p hp => hcne)
  have hrad : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3) Q0 :=
    (contDiffOn_const.mul (contDiffOn_fst.pow 2)).div
      ((contDiffOn_const.add contDiffOn_fst).pow 3)
      (fun p hp => pow_ne_zero 3 (ne_of_gt
        (by linarith [Set.mem_Ioi.mp hp.1] : (0 : ℝ) < 1 + p.1)))
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)) = Function.uncurry (Work.Construction.AK α) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.AK]
  rw [← hfun]
  exact hGam.mul hrad

end Work.FTS.OpenPkg
