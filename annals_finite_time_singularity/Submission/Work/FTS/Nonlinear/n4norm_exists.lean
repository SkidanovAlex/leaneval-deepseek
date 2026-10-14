import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.H2.HProdQ
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.L6Aux.ZslotSupBound6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2_blocks =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Joint differentiability of finite order implies block continuity

The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` are first-order with smooth coefficients,
so `mixed b a g = D_z^b D_θ^a g` costs `a + b` derivatives.  The following finite-order
companion of `Work.FTS.LocData.contDiffOn_mixed` (which is stated at the top order
`smoothOrder`) is what the block bookkeeping needs; it is independent of the `α`-ledger.

The three one-step lemmas express `pz`, `pth` as the first partial of `fderiv ℝ (uncurry ·)`
(`Work.Spaces.pz_eq_fderiv`, `Work.Spaces.pth_eq_fderiv`) and differentiate under `fderiv`
(`ContDiffOn.fderivWithin`, with `fderivWithin = fderiv` on the open set). -/

theorem contDiffOn_pth_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Function.uncurry (Work.Spaces.pth G) p
      = (fderiv ℝ (Function.uncurry G) p) (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := ((N : ℕ) : WithTop ℕ∞)) hV.uniqueDiffOn
      (by rw [Nat.cast_add, Nat.cast_one])
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

theorem contDiffOn_pz_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Function.uncurry (Work.Spaces.pz G) p
      = (fderiv ℝ (Function.uncurry G) p) (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := ((N : ℕ) : WithTop ℕ∞)) hV.uniqueDiffOn
      (by rw [Nat.cast_add, Nat.cast_one])
    refine h'.congr (fun p hp => ?_)
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

theorem contDiffOn_Dth_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hpth := contDiffOn_pth_nat hV h
  have hsin : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V := by fun_prop
  have := hsin.mul hpth
  refine this.congr (fun p hp => ?_)
  simp only [Function.uncurry, Work.Spaces.Dth]

theorem contDiffOn_Dz_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := contDiffOn_pz_nat hV h
  have hfst : ContDiffOn ℝ (((N : ℕ)) : WithTop ℕ∞) (fun p : ℝ × ℝ => p.1) V := contDiffOn_fst
  have := hfst.mul hpz
  refine this.congr (fun p hp => ?_)
  simp only [Function.uncurry, Work.Spaces.Dz]

/-- `D_θ`-iterates cost one order each. -/
theorem contDiffOn_DthIter_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i t : ℕ), ContDiffOn ℝ (((i + t : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V →
      ContDiffOn ℝ (((t : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  intro i
  induction i with
  | zero =>
      intro t h
      simpa using h
  | succ i ih =>
      intro t h
      have h' : ContDiffOn ℝ (((i + (t + 1) : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V := by
        have heq : (((i + (t + 1) : ℕ)) : WithTop ℕ∞) = ((((i + 1) + t : ℕ)) : WithTop ℕ∞) := by
          rw [Nat.add_assoc, Nat.add_comm t 1, ← Nat.add_assoc]
        rw [heq]; exact h
      have hi := ih (t + 1) h'
      have := contDiffOn_Dth_nat (G := Work.Spaces.DthIter i G) hV (N := t) hi
      simpa only [Work.Spaces.DthIter_succ] using this

/-- `D_z`-iterates cost one order each. -/
theorem contDiffOn_DzIter_nat {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (j t : ℕ), ContDiffOn ℝ (((j + t : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V →
      ContDiffOn ℝ (((t : ℕ)) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DzIter j G)) V := by
  intro j
  induction j with
  | zero =>
      intro t h
      simpa using h
  | succ j ih =>
      intro t h
      have h' : ContDiffOn ℝ (((j + (t + 1) : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V := by
        have heq : (((j + (t + 1) : ℕ)) : WithTop ℕ∞) = ((((j + 1) + t : ℕ)) : WithTop ℕ∞) := by
          rw [Nat.add_assoc, Nat.add_comm t 1, ← Nat.add_assoc]
        rw [heq]; exact h
      have hj := ih (t + 1) h'
      have := contDiffOn_Dz_nat (G := Work.Spaces.DzIter j G) hV (N := t) hj
      simpa only [Work.Spaces.DzIter_succ] using this

/-- **Joint `C^m` on an open set gives continuity of every mixed block of total order `≤ m`.**
Since each of `D_z`, `D_θ` is a first-order operator with smooth coefficients (`z` resp.
`sin 2θ`), the block `mixed b a g = D_z^b D_θ^a g` costs `a + b` derivatives. -/
theorem contDiffOn_mixed_nat {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {m : ℕ}
    (h : ContDiffOn ℝ (((m : ℕ)) : WithTop ℕ∞) (Function.uncurry g) V) {a b : ℕ}
    (hab : a + b ≤ m) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed b a g)) V := by
  obtain ⟨t, ht⟩ : ∃ t, m = a + b + t := ⟨m - (a + b), (Nat.add_sub_of_le hab).symm⟩
  subst ht
  have h1 : ContDiffOn ℝ (((a + (b + t) : ℕ)) : WithTop ℕ∞) (Function.uncurry g) V := by
    have heq : ((((a + b) + t : ℕ)) : WithTop ℕ∞) = (((a + (b + t) : ℕ)) : WithTop ℕ∞) := by
      rw [Nat.add_assoc]
    rw [heq] at h; exact h
  have h2 := contDiffOn_DthIter_nat (G := g) hV a (b + t) h1
  have h3 := contDiffOn_DzIter_nat (G := Work.Spaces.DthIter a g) hV b t h2
  exact h3.continuousOn

/-! ## The theorem -/


end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.n4norm_exists =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary identity: `(α^{-1/2})² = α^{-1}` -/

theorem rpow_neg_half_sq {α : ℝ} (hα : 0 < α) :
    (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
  rw [sq, ← Real.rpow_add hα, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by ring,
    Real.rpow_neg_one]

/-! ## `prod`: `ℋ⁴` is closed under products -/

theorem prod_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
      Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.HProdQ
  refine ⟨Real.sqrt (10 * C) + 1, by positivity, ?_⟩
  intro α hα f g hf hg
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  obtain ⟨hmem, hsq⟩ := hC α f g hα.1 hα1 hf hg
  refine ⟨hmem, ?_⟩
  have hRnn : 0 ≤ Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
      * Work.FTS.Nonlin.Xn α g := by
    have h1 : (0 : ℝ) ≤ Real.sqrt (10 * C) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
    have h3 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
    positivity
  have hsq' : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
      ≤ (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have hfac : C / (Work.Spaces.gam α - 1) = 10 * C * α⁻¹ := by
      rw [Work.Spaces.gam_sub_one]; field_simp
    have hfnn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
    have hgnn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
    have hR2 : (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g) ^ 2
        = 10 * C * α⁻¹ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
      have h3 : (Work.FTS.Nonlin.Xn α f) ^ 2 = Work.Spaces.HkSq α 4 f := by
        rw [show Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) from rfl,
          Real.sq_sqrt hfnn]
      have h4 : (Work.FTS.Nonlin.Xn α g) ^ 2 = Work.Spaces.HkSq α 4 g := by
        rw [show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl,
          Real.sq_sqrt hgnn]
      calc (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
            * Work.FTS.Nonlin.Xn α g) ^ 2
          = (Real.sqrt (10 * C)) ^ 2 * (α ^ (-(1 / 2 : ℝ))) ^ 2
              * (Work.FTS.Nonlin.Xn α f) ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
        _ = 10 * C * α⁻¹ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
            rw [h3, h4, rpow_neg_half_sq hα.1, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 10 * C)]
    have hsq2 : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
        ≤ 10 * C * α⁻¹ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
      rwa [hfac] at hsq
    rw [hR2]
    exact hsq2
  rw [show Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)) from rfl]
  calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ))
      ≤ Real.sqrt ((Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g) ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g := Real.sqrt_sq hRnn
    _ ≤ (Real.sqrt (10 * C) + 1) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (10 * C) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have h3 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
        have h4 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg h2 h3) h4,
          mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4]

/-! ## `wprod`: `𝒲^{4,∞} × ℋ⁴ → ℋ⁴` -/


/-! ## `wtoh`: the weighted `𝒲^{4,∞}`-bound controls `ℋ⁴` -/


/-! ## `l12H`: `L₁₂` is bounded on `ℋ⁴` -/

theorem l12H_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn,
      Work.FTS.Nonlin.RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
        ≤ C * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.L12HQ
  exact ⟨C, hCpos, fun α hα g hg h0 => hC α g hα.1 (le_trans hα.2 hα₂1) hg h0⟩

/-! ## `l12zero`: the zero mode of `L₁₂` -/

theorem l12zero_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn,
      Work.FTS.Nonlin.RegQ α 4 f →
      |Work.Construction.L12 f 0| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.L12ZeroQ
  refine ⟨C, hCpos, ?_⟩
  intro α hα f hf
  have h := hC α f hα.1 (le_trans hα.2 hα₂1) hf
  rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
  exact h

/-! ## `fkH`: the radial angular moment `FK g` -/

theorem fkH_field {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn,
      Work.FTS.Nonlin.RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
        ≤ C * Work.FTS.Nonlin.Xn α g :=
  Work.FTS.Nonlinear.N4Fields.fk_field hα₂ hα₂1

/-! ## `radialMul`: lossless product with a function of `z` alone -/

theorem radialMul_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ (r : ℝ → ℝ) (g : Fn),
      Work.FTS.LocData.SmoothQuad (fun z _ => r z) → Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0)
        Filter.atTop (nhds 0)) →
      (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
      Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => r z * g z θ)
        ≤ C * Work.FTS.Nonlin.Xn α (fun z _ => r z) * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.Nonlinear.RadialProd.radial_prod
  exact ⟨C, hCpos, fun α hα r g hr hg hrm hgm hdecr hdecg =>
    hC α hα.1 (le_trans hα.2 hα₂1) r g hr hg hrm hgm hdecr hdecg⟩

/-! ## `wmul`: the `𝒲^{4,∞}`-product rule -/


/-! ## `l12diff`: differentiability of `z ↦ L₁₂(g)(z)` on `(0,∞)` -/

theorem l12diff_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.HkMem α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z := by
  intro α hα g hsm hmem z hz
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  -- the density is integrable on `(0,∞)` and continuous at `z`
  have hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.H2.L12densIntegrable α g hα.1 hα1 hsm hmem
  obtain ⟨hQang_deriv, hQang_cont⟩ := Work.FTS.H2.QangDiff α g hα.1 hα1 hsm hmem
  have hdens_contOn : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi (0 : ℝ)) := by
    have hdiv : ContinuousOn (fun z => Work.Elliptic.Qang g 0 z / z) (Set.Ioi (0 : ℝ)) :=
      (hQang_cont 0 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
    exact hdiv.congr (fun z _ => Work.Elliptic.L12dens_eq_Qang_div g z)
  have hdens_contAt : ContinuousAt (Work.Elliptic.L12dens g) z :=
    hdens_contOn.continuousAt (isOpen_Ioi.mem_nhds hz)
  -- the primitive `t ↦ ∫_0^t dens` is differentiable at `z`
  have hInt0z : IntervalIntegrable (Work.Elliptic.L12dens g) volume (0 : ℝ) z := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
    exact hint.mono_set Set.Ioc_subset_Ioi_self
  have hprim : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, Work.Elliptic.L12dens g s)
      (Work.Elliptic.L12dens g z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt0z
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hdens_contOn z hz) hdens_contAt
  -- `L₁₂(g)(t) = (L₁₂(g)(z) + ∫_0^z dens) - ∫_0^t dens` near `z`
  have hev : (fun t => Work.Elliptic.L12 g t) =ᶠ[𝓝 z]
      fun t => (Work.Elliptic.L12 g z + ∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens g s)
        - ∫ s in (0 : ℝ)..t, Work.Elliptic.L12dens g s := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    have htpos : 0 < t := ht
    have hzint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi z) :=
      hint.mono_set (Ioi_subset_Ioi hz.le)
    have htint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi t) :=
      hint.mono_set (Ioi_subset_Ioi htpos.le)
    have hmain : (∫ s in Set.Ioi z, Work.Elliptic.L12dens g s)
        - (∫ s in Set.Ioi t, Work.Elliptic.L12dens g s)
        = ∫ s in z..t, Work.Elliptic.L12dens g s := by
      rcases le_total z t with hle | hle
      · exact intervalIntegral.integral_Ioi_sub_Ioi hzint hle
      · have h := intervalIntegral.integral_Ioi_sub_Ioi htint hle
        rw [intervalIntegral.integral_symm (a := t) (b := z)]
        linarith
    have hsplit : (∫ s in z..t, Work.Elliptic.L12dens g s)
        = (∫ s in (0 : ℝ)..t, Work.Elliptic.L12dens g s)
          - ∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens g s := by
      have h0z : IntervalIntegrable (Work.Elliptic.L12dens g) volume (0 : ℝ) z := hInt0z
      have hzt : IntervalIntegrable (Work.Elliptic.L12dens g) volume z t := by
        rw [intervalIntegrable_iff]
        refine hint.mono_set ?_
        intro x hx
        have h1 : min z t < x := by
          rcases le_total z t with h | h
          · rw [uIoc_of_le h] at hx
            exact lt_of_le_of_lt (min_le_left _ _) hx.1
          · rw [uIoc_of_ge h] at hx
            exact lt_of_le_of_lt (min_le_right _ _) hx.1
        exact lt_of_le_of_lt (le_min hz.le htpos.le) h1
      have h := intervalIntegral.integral_add_adjacent_intervals h0z hzt
      linarith
    rw [Work.Elliptic.L12, Work.Elliptic.L12]
    linarith
  have hdiff : DifferentiableAt ℝ
      (fun t => (Work.Elliptic.L12 g z + ∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens g s)
        - ∫ s in (0 : ℝ)..t, Work.Elliptic.L12dens g s) z :=
    (differentiableAt_const _).sub hprim.differentiableAt
  have hEll : DifferentiableAt ℝ (fun t => Work.Elliptic.L12 g t) z :=
    hdiff.congr_of_eventuallyEq hev
  simpa [Work.FTS.H2.constructionL12_eq_ellipticL12 g] using hEll


end Work.FTS.Nonlinear
end
end
