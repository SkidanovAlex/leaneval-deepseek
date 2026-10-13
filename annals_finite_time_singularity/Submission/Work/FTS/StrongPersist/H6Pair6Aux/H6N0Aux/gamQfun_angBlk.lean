/-
Copyright: work module for the Elgindi finite-time singularity project.

# Angular integrability of the `dthU`-jets of `a·(Γ(θ)·q(θ))`

`Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.gamQfun_angBlk`: for every `α ∈ (0,1]` and every
real `a` with `|a| ≤ 20` the function

  `θ ↦ (a·Γ(θ)·q(θ))² sin(2θ)^{-η} + ∑_{1 ≤ i ≤ 6} (D_θ^i (a·Γ·q)(θ))² sin(2θ)^{-γ(α)}`

is integrable on the angular interval `Iθ = [0, π/2]`.

## Route

* **The angular jets of `Γ·q` are `Tfun`-multiples of `Γ`.**  On the open interval
  `(0,π/2)` the product rule for `D_θ`, the identity `D_θ Γ = α q Γ` (`Spaces.dthU_Gam`)
  and the recursion defining `Tfun` (`Tfun (j+1) = D_θ (Tfun j) + α q Tfun j`) give

  `D_θ^i (Γ·q) = Tfun i α · Γ`   on `(0,π/2)`   (`dthU_iter_GamQ`),

  by induction on `i`; the induction hypothesis is used only through
  `Filter.EventuallyEq.deriv_eq`, which is local.
* **The `Tfun`-jets are uniformly bounded.**  `Spaces.Tfun_iter_bounded` gives, for each
  order `i`, a bound valid for all `α ∈ (0,1]` and all `θ ∈ Iθ`; collecting the finitely
  many orders `i ≤ 6` into one constant `Ctf` yields `|D_θ^i (a·Γ·q)| ≤ Kf·Γ` on all of
  `Iθ` (`GQjet_bound`): on the interior by the identity above, at the endpoints because
  `sin(2θ) = 0` kills the jets of order `≥ 1` and `Γ` vanishes there.
* **The two weight blocks are integrable.**  `Γ(α,·)² sin(2θ)^{-η}` and
  `Γ(α,·)² sin(2θ)^{-γ(α)}` are integrable by `Coercivity.dthIterAng_sq_integrable_eta`
  resp. `..._gam` (their `i = 0` instance is `Γ` itself), so the majorant
  `angMaj α = Kf²·Γ²sin(2θ)^{-η} + 7·Kf²·Γ²sin(2θ)^{-γ}` is integrable.
* **Measurability.**  The first summand is continuous on `Iθ`; the `i`-th angular jet
  agrees on `(0,π/2)` with the continuous function `a·Tfun i α·Γ` (`GQjet_continuousOn`),
  and `(0,π/2)` is a.e. equal to `Iθ`.  Domination by `angMaj` then gives the result via
  `Integrable.mono'`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Coercivity.dthIterAng_sq_integrable
import Submission.Work.Coercivity.gamDth_l2_bound
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## The integrand, the majorant and the constants -/

/-- The angular integrand of the statement: the `η`-weighted square of `a·Γ·q` plus the
`γ`-weighted squares of its angular jets up to order six. -/
noncomputable def angBlk (α a : ℝ) : ℝ → ℝ := fun θ =>
  (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  + ∑ i ∈ Finset.range 7,
      (if 1 ≤ i then
        (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
       else 0)

/-- A uniform bound for the coefficient sequence `Tfun i α`, `i ≤ 6`, obtained from
`Work.Spaces.Tfun_iter_bounded`. -/
lemma Tfun_bound6 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 6 → ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → |Work.Spaces.Tfun i α θ| ≤ C := by
  choose M hM using fun i : ℕ => Work.Spaces.Tfun_iter_bounded i
  refine ⟨1 + ∑ i ∈ Finset.range 7, M i 0, ?_, ?_⟩
  · have h : 0 ≤ ∑ i ∈ Finset.range 7, M i 0 := Finset.sum_nonneg (fun i _ => (hM i).1 0)
    linarith
  · intro i _ α hαIoc θ hθ
    obtain ⟨hα, hα1⟩ := hαIoc
    have hMi : |Work.Spaces.Tfun i α θ| ≤ M i 0 := by
      have h := (hM i).2 α hα hα1 θ hθ 0
      simpa only [Function.iterate_zero_apply] using h
    have hsum : M i 0 ≤ ∑ l ∈ Finset.range 7, M l 0 :=
      Finset.single_le_sum (fun l _ => (hM l).1 0) (Finset.mem_range.mpr (by omega))
    linarith

/-- The numerical constant bounding all `Tfun i α` with `i ≤ 6`, `α ∈ (0,1]`, `θ ∈ Iθ`. -/
noncomputable def Ctf : ℝ := Classical.choose Tfun_bound6

lemma Ctf_pos : 0 < Ctf := (Classical.choose_spec Tfun_bound6).1

lemma Tfun_le_Ctf : ∀ i : ℕ, i ≤ 6 → ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → |Work.Spaces.Tfun i α θ| ≤ Ctf :=
  (Classical.choose_spec Tfun_bound6).2

/-- The constant of the jet bound: `|D_θ^i (a Γ q)| ≤ Kf·Γ` on `Iθ` for `|a| ≤ 20`, `i ≤ 6`. -/
noncomputable def Kf : ℝ := 20 * (Ctf + 1)

lemma Kf_pos : 0 < Kf := by
  have h := Ctf_pos
  rw [Kf]; nlinarith

/-- The angular majorant of `angBlk α a`: the two `Γ`-weighted weight blocks. -/
noncomputable def angMaj (α : ℝ) : ℝ → ℝ := fun θ =>
  Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    + (7 * Kf ^ 2) * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))

/-! ## The angular jets of `Γ·q` -/

/-- Continuity of `Γ(α,·)`, everywhere (so in particular on `Iθ` and on the open interval). -/
lemma gam_continuous (α : ℝ) (hα : 0 ≤ α) : Continuous (fun θ => Work.Spaces.Gam α θ) := by
  change Continuous (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
  have hbase : Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) := by fun_prop
  exact hbase.rpow_const (p := α / 3) (fun x => Or.inr (by linarith))

/-- **The angular jets of `Γ·q` on the open interval.**  `D_θ^i (Γ q) = Tfun i α · Γ` on
`(0,π/2)`: the product rule for `D_θ`, the identity `D_θ Γ = α q Γ` and the very definition
of the coefficient sequence `Tfun`. -/
lemma dthU_iter_GamQ {α : ℝ} (hα : 0 < α) (i : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t))
      (fun θ => Work.Spaces.Tfun i α θ * Work.Spaces.Gam α θ) (Set.Ioo 0 (Real.pi / 2)) := by
  induction i with
  | zero =>
      intro θ _
      simp only [Function.iterate_zero_apply, Work.Spaces.Tfun_zero]
      ring
  | succ i ih =>
      intro θ hθ
      have hev : (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t))
          =ᶠ[𝓝 θ] (fun t => Work.Spaces.Tfun i α t * Work.Spaces.Gam α t) :=
        ih.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hθ)
      have hder := hev.deriv_eq
      have hT : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.Tfun i α t) θ :=
        ((Work.Spaces.Tfun_smooth i α).differentiable (by simp)).differentiableAt
      have hG : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.Gam α t) θ :=
        Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
      calc Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ
          = Work.Spaces.dthU
              (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ := by
            rw [Function.iterate_succ_apply']
        _ = Work.Spaces.dthU (fun t => Work.Spaces.Tfun i α t * Work.Spaces.Gam α t) θ := by
            rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply, hder]
        _ = Work.Spaces.dthU (fun t : ℝ => Work.Spaces.Tfun i α t) θ * Work.Spaces.Gam α θ
              + Work.Spaces.Tfun i α θ * Work.Spaces.dthU (fun t : ℝ => Work.Spaces.Gam α t) θ :=
            Work.Spaces.dthU_mul_apply (fun t : ℝ => Work.Spaces.Tfun i α t)
              (fun t : ℝ => Work.Spaces.Gam α t) θ hT hG
        _ = Work.Spaces.Tfun (i + 1) α θ * Work.Spaces.Gam α θ := by
            rw [Work.Spaces.dthU_Gam α θ hα hθ, Work.Spaces.dthU_apply,
              Work.Spaces.Tfun_succ]
            ring

/-! ## Bounds and continuity of the angular jets -/

/-- **The jet bound.**  For `|a| ≤ 20` and `i ≤ 6` the `i`-th angular jet of `a·(Γ·q)` is
bounded by `Kf·Γ` on `Iθ`. -/
lemma GQjet_bound {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (ha : |a| ≤ 20)
    {i : ℕ} (hi : i ≤ 6) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ|
      ≤ Kf * Work.Spaces.Gam α θ := by
  have hG : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hT : |Work.Spaces.Tfun i α θ| ≤ Ctf := Tfun_le_Ctf i hi α ⟨hα, hα1⟩ θ hθ
  have hpi : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  have hinner : |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ|
      ≤ Ctf * Work.Spaces.Gam α θ := by
    rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · have hid := dthU_iter_GamQ hα i (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h0, h1⟩)
        rw [hid, abs_mul, abs_of_nonneg hG]
        exact mul_le_mul_of_nonneg_right hT hG
      · subst h1
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · subst hi0
          simp only [Function.iterate_zero_apply]
          rw [Work.Spaces.Gam_zero_right α (ne_of_gt hα)]
          simp
        · rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' _ hipos hpi,
            Work.Spaces.Gam_zero_right α (ne_of_gt hα)]
          simp
    · subst h0
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        simp only [Function.iterate_zero_apply]
        rw [Work.Spaces.Gam_zero_left α (ne_of_gt hα)]
        simp
      · rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' _ hipos (by simp),
          Work.Spaces.Gam_zero_left α (ne_of_gt hα)]
        simp
  rw [show Work.Spaces.dthU^[i] (fun t : ℝ => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t))
        = fun θ => a * Work.Spaces.dthU^[i]
            (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ from
      Work.Spaces.dthU_iter_const_mul i a
        (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t)]
  rw [abs_mul]
  calc |a| * |Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ|
      ≤ 20 * (Ctf * Work.Spaces.Gam α θ) :=
        mul_le_mul ha hinner (abs_nonneg _) (by norm_num)
    _ ≤ Kf * Work.Spaces.Gam α θ := by
        rw [Kf]
        nlinarith [hG, Ctf_pos.le]

/-- **Continuity of the angular jets on the open interval.**  On `(0,π/2)` the `i`-th jet of
`a·(Γ·q)` agrees with the continuous function `a·Tfun i α·Γ`. -/
lemma GQjet_continuousOn {α a : ℝ} (hα : 0 < α) (i : ℕ) :
    ContinuousOn (fun θ => Work.Spaces.dthU^[i]
        (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hcont_exp : Continuous
      (fun θ : ℝ => a * (Work.Spaces.Tfun i α θ * Work.Spaces.Gam α θ)) :=
    continuous_const.mul
      ((Work.Spaces.Tfun_smooth i α).continuous.mul (gam_continuous α (le_of_lt hα)))
  have heq : Set.EqOn
      (fun θ => Work.Spaces.dthU^[i]
        (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ)
      (fun θ => a * (Work.Spaces.Tfun i α θ * Work.Spaces.Gam α θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ hθ
    show Work.Spaces.dthU^[i]
        (fun t : ℝ => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ
      = a * (Work.Spaces.Tfun i α θ * Work.Spaces.Gam α θ)
    rw [show Work.Spaces.dthU^[i]
          (fun t : ℝ => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t))
        = fun θ => a * Work.Spaces.dthU^[i]
            (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ from
      Work.Spaces.dthU_iter_const_mul i a
        (fun t : ℝ => Work.Spaces.Gam α t * Work.Spaces.qfun t)]
    simp only []
    rw [dthU_iter_GamQ hα i hθ]
  exact hcont_exp.continuousOn.congr heq

/-! ## The main theorem -/

theorem gamQfun_angBlk : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1, ∀ a : ℝ, |a| ≤ 20 →
    MeasureTheory.IntegrableOn (fun θ =>
        (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7,
            (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
             else 0)) Work.Spaces.Iθ := by
  refine ⟨1, one_pos, fun α hαIoc a ha => ?_⟩
  obtain ⟨hα, hα1⟩ := hαIoc
  change MeasureTheory.IntegrableOn (angBlk α a) Work.Spaces.Iθ
  have hs0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- the two weight blocks are integrable
  have hEtaInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
    simpa only [Work.Coercivity.CT.DthIterAng_zero] using
      Work.Coercivity.dthIterAng_sq_integrable_eta α hα hα1 0
  have hGamInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ := by
    simpa only [Work.Coercivity.CT.DthIterAng_zero] using
      Work.Coercivity.dthIterAng_sq_integrable_gam α hα hα1 0
  have hmaj : MeasureTheory.IntegrableOn (angMaj α) Work.Spaces.Iθ :=
    (hEtaInt.const_mul (Kf ^ 2)).add (hGamInt.const_mul (7 * Kf ^ 2))
  -- pointwise domination on `Iθ`
  have hdom : ∀ θ ∈ Work.Spaces.Iθ, angBlk α a θ ≤ angMaj α θ := by
    intro θ hθ
    have hsθ := hs0 θ hθ
    have hsE : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hsθ _
    have hsG : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsθ _
    have h0 : (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      have hb := GQjet_bound (i := 0) hα hα1 ha (Nat.zero_le 6) hθ
      have hb' : |a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)|
          ≤ Kf * Work.Spaces.Gam α θ := by
        simpa only [Function.iterate_zero_apply] using hb
      have hsq : (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
          ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := by
        calc (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
            = |a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)| ^ 2 := by rw [sq_abs]
          _ ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb' 2
      calc (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right hsq hsE
        _ = Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            ring
    have hsum : (∑ i ∈ Finset.range 7,
          (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
           else 0))
        ≤ ∑ _i ∈ Finset.range 7,
            Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1]
        have hi6 : i ≤ 6 := by have := Finset.mem_range.mp hi; omega
        have hb := GQjet_bound (i := i) hα hα1 ha hi6 hθ
        have hsq : (Work.Spaces.dthU^[i]
              (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
            ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := by
          calc (Work.Spaces.dthU^[i]
                (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
              = |Work.Spaces.dthU^[i]
                  (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ| ^ 2 := by
                rw [sq_abs]
            _ ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        calc (Work.Spaces.dthU^[i]
                (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            ≤ (Kf * Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
              mul_le_mul_of_nonneg_right hsq hsG
          _ = Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      · simpa only [if_neg h1] using
          mul_nonneg (sq_nonneg Kf) (mul_nonneg (sq_nonneg (Work.Spaces.Gam α θ)) hsG)
    have hsum2 : (∑ _i ∈ Finset.range 7,
          Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        = 7 * Kf ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    simp only [angBlk, angMaj]
    linarith [h0, hsum, le_of_eq hsum2]
  -- measurability of the integrand
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hGamC : Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := gam_continuous α (le_of_lt hα)
  have hFmeas : AEStronglyMeasurable
      (fun θ : ℝ => a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ))
      (volume.restrict Work.Spaces.Iθ) :=
    (continuous_const.mul (hGamC.mul Work.Spaces.qfun_smooth.continuous)).aestronglyMeasurable
  have hEtaMeas : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) :=
    (Measurable.pow_const
        (Real.measurable_sin.comp (measurable_const.mul measurable_id)) (-(Work.Spaces.eta)))
      |>.aestronglyMeasurable
  have hmeasi : ∀ i : ℕ, i ≤ 6 → AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.dthU^[i]
          (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) := by
    intro i _
    have hcont_i := GQjet_continuousOn (α := α) (a := a) hα i
    have hcont_sin : ContinuousOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine ContinuousOn.rpow_const (by fun_prop) ?_
      intro θ hθ
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact ((hcont_i.pow 2).mul hcont_sin).aestronglyMeasurable measurableSet_Ioo
  have hsumMeas : AEStronglyMeasurable
      (∑ i ∈ Finset.range 7, fun θ : ℝ =>
        (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
         else 0)) (volume.restrict Work.Spaces.Iθ) := by
    refine Finset.aestronglyMeasurable_sum _ (fun i hi => ?_)
    by_cases h1 : 1 ≤ i
    · have hi6 : i ≤ 6 := by have := Finset.mem_range.mp hi; omega
      simpa only [if_pos h1] using hmeasi i hi6
    · simpa only [if_neg h1] using
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ))).aestronglyMeasurable
  have hstep : angBlk α a = (fun θ : ℝ => (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      + (∑ i ∈ Finset.range 7, fun θ : ℝ =>
        (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
         else 0)) := by
    funext θ
    simp only [angBlk, Pi.add_apply, Finset.sum_apply]
  have hmeas : AEStronglyMeasurable (angBlk α a) (volume.restrict Work.Spaces.Iθ) := by
    rw [hstep]
    exact (hFmeas.pow 2 |>.mul hEtaMeas).add hsumMeas
  -- conclude by domination
  refine hmaj.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hnn : 0 ≤ angBlk α a θ := by
    simp only [angBlk]
    refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hs0 θ hθ) _)) ?_
    refine Finset.sum_nonneg (fun i hi => ?_)
    by_cases h1 : 1 ≤ i
    · simpa only [if_pos h1] using
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hs0 θ hθ) _)
    · simpa only [if_neg h1] using le_refl (0 : ℝ)
  rw [Real.norm_of_nonneg hnn]
  exact hdom θ hθ

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
