import Mathlib
import Submission.Work.FQCInputs.PrincipalContinuity
import Submission.Work.FQCInputs.muQC_zero
import Submission.Work.FQCInputs.principal_muQC_zero
import Submission.Work.FQCInputs.continuous_muQC_apply
import Submission.Work.FQCInputs.support_muQC_subset_closedBall
import Submission.Work.FQCInputs.continuous_theta_apply
import Submission.Work.FQCInputs.continuous_iteratedDeriv_two_F
import Submission.Work.FQCInputs.continuous_F_uncurry
import Submission.Work.FQCInputs.eventually_iteratedDeriv_two_eq_zero
import Submission.Work.FQCInputs.Poly
import Submission.Work.FQCInputs.SimpleTransfer
import Submission.Work.FQC.muQC_admissible_pg
import Submission.Work.FQC.zero_of_conj
import Submission.Work.FQC.conj_is_tricorn_pg
import Submission.Work.FQC.transfer_parabolic_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## Auxiliary lemmas -/

/-- `iteratedDeriv 2 (fun z => f z - z) w = iteratedDeriv 2 f w` for `f` twice differentiable
at `w` (the identity contributes nothing to the second derivative). -/
theorem iteratedDeriv_two_sub_id {f : ℂ → ℂ} {w : ℂ} (hf : ContDiffAt ℂ 2 f w) :
    iteratedDeriv 2 (fun z : ℂ => f z - z) w = iteratedDeriv 2 f w := by
  rw [show (fun z : ℂ => f z - z) = (f - id) from rfl, iteratedDeriv_sub hf contDiffAt_id,
    iteratedDeriv_id]
  norm_num

/-- **The fixed points of `F c = (T_c)^{10}` are finite.**  `F c` is a polynomial map and it is
*not* the identity, because `z₁` is a simple parabolic point of `F c`. -/
theorem finite_fixedPoints {c : ℂ} (d : Work.EL.RootParabolic c) :
    {z : ℂ | Work.EL.F c z = z}.Finite := by
  obtain ⟨p, hp⟩ := exists_poly_F c
  have hq : p - Polynomial.X ≠ 0 := by
    intro hzero
    have hid : Work.EL.F c = id := by
      funext z
      have h := congrArg (fun q : Polynomial ℂ => q.eval z) hzero
      rw [hp]
      have h2 : p.eval z = z := by
        simpa [Polynomial.eval_sub, Polynomial.eval_X, sub_eq_zero] using h
      simpa using h2
    have h0 : iteratedDeriv 2 (id : ℂ → ℂ) d.z₁ = 0 := by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
        show deriv (id : ℂ → ℂ) = fun _ => (1 : ℂ) from funext fun z => deriv_id z]
      exact deriv_const _ _
    exact d.simple (by rw [hid]; exact h0)
  refine (Polynomial.finite_setOfPred_isRoot hq).subset ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X]
  rw [hp] at hz
  simp only at hz
  rw [hz]
  ring

/-- Fixed points of a conjugate map are the images of fixed points. -/
theorem fixed_of_conj {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) {z : ℂ}
    (hz : Work.EL.F c₂ z = z) : ∃ e : ℂ, Work.EL.F c e = e ∧ z = θ e := by
  refine ⟨θ.symm z, ?_, (θ.apply_symm_apply z).symm⟩
  have h := Work.FQC.conj_F θ hconj (θ.symm z)
  rw [θ.apply_symm_apply z] at h
  rw [hz] at h
  have h2 : θ (Work.EL.F c (θ.symm z)) = θ (θ.symm z) := by rw [h, θ.apply_symm_apply]
  exact θ.injective h2

/-- The fixed points of `F c` other than `z₁`, as a finset. -/
noncomputable def fixedFinset {c : ℂ} (d : Work.EL.RootParabolic c) : Finset ℂ :=
  ((finite_fixedPoints d).toFinset).erase d.z₁

theorem mem_fixedFinset {c : ℂ} (d : Work.EL.RootParabolic c) (e : ℂ) :
    e ∈ fixedFinset d ↔ Work.EL.F c e = e ∧ e ≠ d.z₁ := by
  rw [fixedFinset, Finset.mem_erase, Set.Finite.mem_toFinset]
  tauto

theorem eq_z₁_of_fixedFinset_eq_empty {c : ℂ} (d : Work.EL.RootParabolic c)
    (h : fixedFinset d = ∅) {e : ℂ} (he : Work.EL.F c e = e) : e = d.z₁ := by
  by_contra hne
  have hmem : e ∈ fixedFinset d := (mem_fixedFinset d e).mpr ⟨he, hne⟩
  rw [h] at hmem
  exact absurd hmem (Finset.notMem_empty e)

/-! ## The canonical conjugacy of the deformation -/

/-- The conjugacy produced by the deformation at the parameter `t`. -/
noncomputable def thetaHomeo {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (P : Set ℂ) (t : ℝ) : ℂ ≃ₜ ℂ :=
  Work.MRMT.Found.principal (Work.FQC.muQC d fl P t)

/-- **The deformation conjugates `T_c` to `T_{θ_t c}`.** -/
theorem thetaHomeo_conj {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) (t : ℝ) (z : ℂ) :
    thetaHomeo d fl hpetal.Pg t (Tantibar c z)
      = Tantibar (thetaHomeo d fl hpetal.Pg t c) (thetaHomeo d fl hpetal.Pg t z) := by
  show (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) (Tantibar c z)
      = Tantibar ((Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) c)
          ((Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) z)
  obtain ⟨c₂', hc₂'⟩ := Work.FQC.conj_is_tricorn_pg d fl hpetal t
  have h0 : (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) 0 = 0 :=
    Work.FQC.zero_of_conj
      (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)).bijective hc₂'
  have hc : (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)) c = c₂' := by
    have h := hc₂' 0
    rw [h0] at h
    rw [show Tantibar c 0 = c from by simp [Tantibar],
      show Tantibar c₂' 0 = c₂' from by simp [Tantibar]] at h
    exact h
  rw [hc]
  exact hc₂' z

/-- The conjugacy for the holomorphic tenth iterate. -/
theorem thetaHomeo_F_conj {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) (t : ℝ) (z : ℂ) :
    thetaHomeo d fl hpetal.Pg t (Work.EL.F c z)
      = Work.EL.F (thetaHomeo d fl hpetal.Pg t c) (thetaHomeo d fl hpetal.Pg t z) :=
  Work.FQC.conj_F (thetaHomeo d fl hpetal.Pg t) (thetaHomeo_conj d fl hpetal t) z

/-- Continuity of the conjugacy in the parameter, pointwise. -/
theorem continuous_thetaHomeo {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) (z : ℂ) :
    Continuous fun t : ℝ => thetaHomeo d fl hpetal.Pg t z :=
  Work.FQCInputs.continuous_theta_apply PrincipalContinuity.found d fl hpetal z

/-- **Continuity of the transported second derivative in the parameter.** -/
theorem continuous_G {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) :
    Continuous fun t : ℝ => iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
      (thetaHomeo d fl hpetal.Pg t d.z₁) := by
  have hpair : Continuous fun t : ℝ =>
      (thetaHomeo d fl hpetal.Pg t c, thetaHomeo d fl hpetal.Pg t d.z₁) :=
    (continuous_thetaHomeo d fl hpetal c).prodMk (continuous_thetaHomeo d fl hpetal d.z₁)
  show Continuous (Function.comp (fun q : ℂ × ℂ => iteratedDeriv 2 (Work.EL.F q.1) q.2)
    (fun t : ℝ => (thetaHomeo d fl hpetal.Pg t c, thetaHomeo d fl hpetal.Pg t d.z₁)))
  exact Work.FQCInputs.continuous_iteratedDeriv_two_F.comp hpair

/-- The transported point is fixed by the transported map. -/
theorem thetaHomeo_fixed {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) (t : ℝ) :
    Work.EL.F (thetaHomeo d fl hpetal.Pg t c) (thetaHomeo d fl hpetal.Pg t d.z₁)
      = thetaHomeo d fl hpetal.Pg t d.z₁ := by
  have h := thetaHomeo_F_conj d fl hpetal t d.z₁
  rw [Work.FQC.F_fix c d] at h
  exact h.symm

/-- The multiplier of the transported parabolic point is `1`. -/
theorem deriv_thetaHomeo_eq_one {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) (t : ℝ) :
    deriv (Work.EL.F (thetaHomeo d fl hpetal.Pg t c)) (thetaHomeo d fl hpetal.Pg t d.z₁) = 1 :=
  Work.FQCInputs.deriv_F_transfer d (thetaHomeo d fl hpetal.Pg t) (thetaHomeo_conj d fl hpetal t)
    (Work.MRMT.Found.principal_decay (Work.FQC.muQC_admissible_pg d fl hpetal t))

/-- The transported parabolic point is simple at `t = 0` (`θ_0 = id` and `d.simple`). -/
theorem G_zero_ne {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) :
    iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg 0 c))
      (thetaHomeo d fl hpetal.Pg 0 d.z₁) ≠ 0 := by
  have hθ0 : ∀ z : ℂ, thetaHomeo d fl hpetal.Pg 0 z = z := by
    intro z
    have h := congrFun (Work.FQCInputs.principal_muQC_zero d fl hpetal.Pg) z
    show (⇑(Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg 0))) z = z
    exact h
  rw [hθ0 c, hθ0 d.z₁]
  exact d.simple

/-! ## The isolation of the transported parabolic point -/

/-- **The other fixed points stay away.**  If `F c` has a fixed point other than `z₁`, the
transported parabolic point `θ_t z₁` is, for `t` near `t₀`, the only fixed point of
`F (θ_t c)` in a small ball around `θ_{t₀} z₁`. -/
theorem iso_eventually_nonempty {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) {t₀ : ℝ} (hEne : (fixedFinset d).Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t in 𝓝 t₀,
      ∀ z ∈ Metric.closedBall (thetaHomeo d fl hpetal.Pg t₀ d.z₁) ε,
        Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z = 0 →
          z = thetaHomeo d fl hpetal.Pg t d.z₁ := by
  set m : ℝ := (fixedFinset d).inf' hEne
    (fun e => ‖thetaHomeo d fl hpetal.Pg t₀ e - thetaHomeo d fl hpetal.Pg t₀ d.z₁‖)
    with hmdef
  have hmpos : 0 < m := by
    rw [hmdef, Finset.lt_inf'_iff hEne]
    intro e he
    have he' := (mem_fixedFinset d e).mp he
    have hne : thetaHomeo d fl hpetal.Pg t₀ e ≠ thetaHomeo d fl hpetal.Pg t₀ d.z₁ := by
      intro hcon
      exact he'.2 ((thetaHomeo d fl hpetal.Pg t₀).injective hcon)
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  refine ⟨m / 8, by linarith, ?_⟩
  have hltE : ∀ᶠ t in 𝓝 t₀, ∀ e ∈ fixedFinset d,
      (3 : ℝ) / 4 * m < ‖thetaHomeo d fl hpetal.Pg t e - thetaHomeo d fl hpetal.Pg t d.z₁‖ := by
    rw [Finset.eventually_all]
    intro e he
    have hle : m ≤ ‖thetaHomeo d fl hpetal.Pg t₀ e - thetaHomeo d fl hpetal.Pg t₀ d.z₁‖ := by
      rw [hmdef]
      exact Finset.inf'_le _ he
    have hf : Continuous fun t : ℝ =>
        ‖thetaHomeo d fl hpetal.Pg t e - thetaHomeo d fl hpetal.Pg t d.z₁‖ :=
      ((continuous_thetaHomeo d fl hpetal e).sub (continuous_thetaHomeo d fl hpetal d.z₁)).norm
    have hmem : t₀ ∈ {t : ℝ |
        (3 : ℝ) / 4 * m < ‖thetaHomeo d fl hpetal.Pg t e - thetaHomeo d fl hpetal.Pg t d.z₁‖} := by
      simp only [Set.mem_setOf_eq]
      linarith
    exact (isOpen_Ioi.preimage hf).mem_nhds hmem
  have hwclose : ∀ᶠ t in 𝓝 t₀,
      ‖thetaHomeo d fl hpetal.Pg t d.z₁ - thetaHomeo d fl hpetal.Pg t₀ d.z₁‖ ≤ m / 8 := by
    have hpos : (0 : ℝ) < m / 8 := by linarith
    have hball : ∀ᶠ t in 𝓝 t₀,
        dist (thetaHomeo d fl hpetal.Pg t d.z₁) (thetaHomeo d fl hpetal.Pg t₀ d.z₁) < m / 8 :=
      (continuous_thetaHomeo d fl hpetal d.z₁).continuousAt (Metric.ball_mem_nhds _ hpos)
    filter_upwards [hball] with t ht
    rw [dist_eq_norm] at ht
    exact le_of_lt ht
  filter_upwards [hltE, hwclose] with t htE htw
  have htw' : ‖thetaHomeo d fl hpetal.Pg t₀ d.z₁ - thetaHomeo d fl hpetal.Pg t d.z₁‖
      ≤ m / 8 := by
    rw [norm_sub_rev]
    exact htw
  intro z hz hPz
  obtain ⟨e, hefix, hze⟩ :=
    fixed_of_conj (thetaHomeo d fl hpetal.Pg t) (thetaHomeo_conj d fl hpetal t)
      (sub_eq_zero.mp hPz)
  by_cases he : e = d.z₁
  · rw [hze, he]
  · exfalso
    have heE : e ∈ fixedFinset d := (mem_fixedFinset d e).mpr ⟨hefix, he⟩
    have h3 := htE e heE
    have h5 : ‖z - thetaHomeo d fl hpetal.Pg t₀ d.z₁‖ ≤ m / 8 := by
      have h := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at h
    have h4 : ‖thetaHomeo d fl hpetal.Pg t e - thetaHomeo d fl hpetal.Pg t d.z₁‖ ≤ m / 4 := by
      calc ‖thetaHomeo d fl hpetal.Pg t e - thetaHomeo d fl hpetal.Pg t d.z₁‖
          = ‖z - thetaHomeo d fl hpetal.Pg t d.z₁‖ := by rw [hze]
        _ ≤ ‖z - thetaHomeo d fl hpetal.Pg t₀ d.z₁‖
              + ‖thetaHomeo d fl hpetal.Pg t₀ d.z₁ - thetaHomeo d fl hpetal.Pg t d.z₁‖ := by
            rw [show z - thetaHomeo d fl hpetal.Pg t d.z₁
                = (z - thetaHomeo d fl hpetal.Pg t₀ d.z₁)
                  + (thetaHomeo d fl hpetal.Pg t₀ d.z₁
                      - thetaHomeo d fl hpetal.Pg t d.z₁) from by ring]
            exact norm_add_le _ _
        _ ≤ m / 8 + m / 8 := add_le_add h5 htw'
        _ = m / 4 := by ring
    linarith

/-- If `z₁` is the only fixed point of `F c`, then the only fixed point of `F (θ_t c)` in any
ball around `θ_{t₀} z₁` is `θ_t z₁`. -/
theorem iso_of_unique_fixed {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) {t₀ t : ℝ} {ε : ℝ}
    (hE : ∀ e : ℂ, Work.EL.F c e = e → e = d.z₁) :
    ∀ z ∈ Metric.closedBall (thetaHomeo d fl hpetal.Pg t₀ d.z₁) ε,
      Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z = 0 →
        z = thetaHomeo d fl hpetal.Pg t d.z₁ := by
  intro z _ hPz
  obtain ⟨e, hefix, hze⟩ :=
    fixed_of_conj (thetaHomeo d fl hpetal.Pg t) (thetaHomeo_conj d fl hpetal t)
      (sub_eq_zero.mp hPz)
  rw [hze, hE e hefix]

/-! ## Openness of the zero set -/

/-- **The local Hurwitz step for the deformation.**  If the transported second derivative
vanishes at `t₀`, it vanishes for all `t` near `t₀`. -/
theorem G_eventually_zero {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) {t₀ : ℝ}
    (hG0 : iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t₀ c))
      (thetaHomeo d fl hpetal.Pg t₀ d.z₁) = 0) :
    ∀ᶠ t in 𝓝 t₀, iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
      (thetaHomeo d fl hpetal.Pg t d.z₁) = 0 := by
  have hiso : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t in 𝓝 t₀,
      ∀ z ∈ Metric.closedBall (thetaHomeo d fl hpetal.Pg t₀ d.z₁) ε,
        Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z = 0 →
          z = thetaHomeo d fl hpetal.Pg t d.z₁ := by
    by_cases hEne : (fixedFinset d).Nonempty
    · exact iso_eventually_nonempty d fl hpetal hEne
    · rw [Finset.not_nonempty_iff_eq_empty] at hEne
      refine ⟨1, one_pos, ?_⟩
      refine Filter.Eventually.of_forall ?_
      intro t
      exact iso_of_unique_fixed d fl hpetal (t₀ := t₀) (t := t) (ε := 1)
        (fun e he => eq_z₁_of_fixedFinset_eq_empty d hEne he)
  obtain ⟨ε, hε, hiso⟩ := hiso
  have hpoly : ∀ t : ℝ, ∃ p : Polynomial ℂ,
      (fun z : ℂ => Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z) = fun z => p.eval z := by
    intro t
    obtain ⟨p, hp⟩ := exists_poly_F (thetaHomeo d fl hpetal.Pg t c)
    refine ⟨p - Polynomial.X, ?_⟩
    funext z
    rw [Polynomial.eval_sub, Polynomial.eval_X]
    have h := congrFun hp z
    rw [h]
  have hcont : Continuous fun q : ℝ × ℂ =>
      Work.EL.F (thetaHomeo d fl hpetal.Pg q.1 c) q.2 - q.2 := by
    have h1 : Continuous fun q : ℝ × ℂ => thetaHomeo d fl hpetal.Pg q.1 c :=
      (continuous_thetaHomeo d fl hpetal c).comp continuous_fst
    exact (Work.FQCInputs.continuous_F_uncurry.comp (h1.prodMk continuous_snd)).sub continuous_snd
  have h2cont : ContinuousAt (fun t : ℝ =>
      iteratedDeriv 2 (fun z : ℂ => Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z)
        (thetaHomeo d fl hpetal.Pg t d.z₁)) t₀ := by
    have heq : (fun t : ℝ =>
        iteratedDeriv 2 (fun z : ℂ => Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z)
          (thetaHomeo d fl hpetal.Pg t d.z₁))
        = fun t : ℝ => iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
            (thetaHomeo d fl hpetal.Pg t d.z₁) := by
      funext t
      exact iteratedDeriv_two_sub_id
        (((Work.FQC.differentiable_F (thetaHomeo d fl hpetal.Pg t c)).contDiff (n := 2)).contDiffAt)
    rw [heq]
    exact (continuous_G d fl hpetal).continuousAt
  have h0 : ∀ t : ℝ,
      Work.EL.F (thetaHomeo d fl hpetal.Pg t c) (thetaHomeo d fl hpetal.Pg t d.z₁)
        - thetaHomeo d fl hpetal.Pg t d.z₁ = 0 := by
    intro t
    rw [sub_eq_zero]
    exact thetaHomeo_fixed d fl hpetal t
  have h1 : ∀ t : ℝ,
      deriv (fun z : ℂ => Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z)
        (thetaHomeo d fl hpetal.Pg t d.z₁) = 0 := by
    intro t
    rw [show (fun z : ℂ => Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z)
        = (Work.EL.F (thetaHomeo d fl hpetal.Pg t c) - id) from rfl,
      deriv_sub (Work.FQC.differentiable_F (thetaHomeo d fl hpetal.Pg t c)).differentiableAt
        differentiableAt_id,
      deriv_id, deriv_thetaHomeo_eq_one d fl hpetal t]
    ring
  have ht₀' : iteratedDeriv 2
      (fun z : ℂ => Work.EL.F (thetaHomeo d fl hpetal.Pg t₀ c) z - z)
        (thetaHomeo d fl hpetal.Pg t₀ d.z₁) = 0 := by
    rw [iteratedDeriv_two_sub_id
      (((Work.FQC.differentiable_F (thetaHomeo d fl hpetal.Pg t₀ c)).contDiff (n := 2)).contDiffAt)]
    exact hG0
  have hres := Work.FQCInputs.eventually_iteratedDeriv_two_eq_zero
    (P := fun t z => Work.EL.F (thetaHomeo d fl hpetal.Pg t c) z - z)
    (w := fun t => thetaHomeo d fl hpetal.Pg t d.z₁)
    hε hpoly hcont (continuous_thetaHomeo d fl hpetal d.z₁).continuousAt h2cont h0 h1 hiso ht₀'
  refine hres.mono ?_
  intro t ht
  rw [← iteratedDeriv_two_sub_id
    (((Work.FQC.differentiable_F (thetaHomeo d fl hpetal.Pg t c)).contDiff (n := 2)).contDiffAt)]
  exact ht

/-! ## The continuation argument -/

/-- **The transported parabolic point is simple**, for the canonical conjugacy
`θ t = principal (muQC d fl Pg t)`: with `c₂ t = θ t c` and `w t = θ t d.z₁`, the second
derivative `iteratedDeriv 2 (F (c₂ t)) (w t)` never vanishes.

This is the continuation argument of `Submission/Work/NOTES_LEAD_mandelbar_simple.md` §3: the
zero set `N = {t | iteratedDeriv 2 (F (θ t c)) (θ t z₁) = 0}` misses `0`
(`G_zero_ne`), is closed (`continuous_G`), and is open (`G_eventually_zero`).  As `ℝ` is
connected, `N = ∅`. -/
theorem canonical_simple {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) :
    ∀ t : ℝ,
      iteratedDeriv 2 (Work.EL.F (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t) c))
        (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t) d.z₁) ≠ 0 := by
  have hNopen : IsOpen {t : ℝ | iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
      (thetaHomeo d fl hpetal.Pg t d.z₁) = 0} := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    exact G_eventually_zero d fl hpetal ht₀
  have hGcont := continuous_G d fl hpetal
  have hSopen : IsOpen {t : ℝ | iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
      (thetaHomeo d fl hpetal.Pg t d.z₁) ≠ 0} :=
    (isOpen_ne (x := (0 : ℂ))).preimage hGcont
  have hmain : ∀ t : ℝ, iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
      (thetaHomeo d fl hpetal.Pg t d.z₁) ≠ 0 := by
    have hSclosed : IsClosed {t : ℝ | iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
        (thetaHomeo d fl hpetal.Pg t d.z₁) ≠ 0} := by
      have heq : {t : ℝ | iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
          (thetaHomeo d fl hpetal.Pg t d.z₁) ≠ 0}
          = {t : ℝ | iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
              (thetaHomeo d fl hpetal.Pg t d.z₁) = 0}ᶜ := by
        ext t
        by_cases h : iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
            (thetaHomeo d fl hpetal.Pg t d.z₁) = 0 <;> simp [h]
      rw [heq]
      exact hNopen.isClosed_compl
    have hS : IsClopen {t : ℝ | iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
        (thetaHomeo d fl hpetal.Pg t d.z₁) ≠ 0} := ⟨hSclosed, hSopen⟩
    have hne : ({t : ℝ | iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
        (thetaHomeo d fl hpetal.Pg t d.z₁) ≠ 0}).Nonempty := ⟨0, G_zero_ne d fl hpetal⟩
    have huniv := hS.eq_univ hne
    intro t
    have ht : t ∈ ({t : ℝ | iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
        (thetaHomeo d fl hpetal.Pg t d.z₁) ≠ 0}) := by rw [huniv]; trivial
    exact ht
  intro t
  show iteratedDeriv 2 (Work.EL.F (thetaHomeo d fl hpetal.Pg t c))
      (thetaHomeo d fl hpetal.Pg t d.z₁) ≠ 0
  exact hmain t

theorem simpleTransfer_all {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) :
    ∀ t : ℝ, Work.FQC.SimpleTransfer d fl hpetal.Pg t := by
  intro t c₂ θ hθ hconj
  have hconj' : ∀ z : ℂ, Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t) (Tantibar c z)
      = Tantibar c₂ (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t) z) := by
    intro z
    have h := hconj z
    rw [hθ] at h
    exact h
  have h0 : Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t) 0 = 0 :=
    Work.FQC.zero_of_conj
      (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t)).bijective hconj'
  have hc₂ : c₂ = Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t) c := by
    have h := hconj' 0
    rw [h0] at h
    rw [show Tantibar c 0 = c from by simp [Tantibar],
      show Tantibar c₂ 0 = c₂ from by simp [Tantibar]] at h
    exact h.symm
  have hz₁ : θ d.z₁ = Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t) d.z₁ :=
    congrFun hθ d.z₁
  rw [hc₂, hz₁]
  exact canonical_simple d fl hpetal t

end Work.FQCInputs

end
