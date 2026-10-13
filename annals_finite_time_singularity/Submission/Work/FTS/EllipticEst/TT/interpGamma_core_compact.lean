/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.interpGamma_core_compact`

The compact-support case of the interpolation core: for `G` which is `C^∞` on the open quadrant
and supported in a compact rectangle `[A,B] × [c,d]` with `0 < A`, `0 < c < d < π/2`,

  `Xint α G ≤ √(DDint α G · TTint α G)`

where `Xint`, `DDint`, `TTint` are the three weighted functionals of `TT.interpGammaDefs`.

The proof is the classical chain

* slicewise (`z` fixed) angular integration by parts with the *light* weight
  `σ_a = sin(2θ)^{2-γ}` (`σ_a'' ≤ 0`, so the two extra terms have the good sign):
  `∫_θ (D_z∂_θG)²σ_a ≤ -∫_θ (D_zG)(D_z∂_θ²G)σ_a`;
* integration over `z` against `w²` (both sides honest because the integrands are supported in
  the compact rectangle);
* the radial `T`-adjoint `∫_z w² (D_zG)(D_z∂_θ²G) = -∫_z w² (D_z²G + b D_zG)(∂_θ²G)`;
* Cauchy–Schwarz in the two variables.

Everything is `sorry`-free; the file rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.radialPairIBP
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.EllipticEst.TT.slice_ibp_sigA_compact
import Submission.Work.FTS.EllipticEst.TT.swap_prod_supported
import Submission.Work.FTS.EllipticEst.TT.interp_amgm_rect
import Submission.Work.FTS.EllipticEst.TT.radial_ibp_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. Vanishing off the support rectangle

If the (uncurried) `h` vanishes off `[A,B] × [c,d]`, then so does every derivative built from
`∂_z`, `∂_θ`, `D_z = z∂_z`, `D_θ = sin(2θ)∂_θ`: off the closed rectangle the function is
*identically* zero on a neighbourhood of the point, so all iterated derivatives vanish. -/

lemma vanishesOff_pz {A B c d : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → h z θ = 0) :
    ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.pz h z θ = 0 := by
  intro z θ hz
  rcases hz with hz | hz
  · refine Work.EllipticEst.Core.deriv_eq_zero_of_eventuallyEq_zero ?_
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hz] with z' hz'
    exact hh z' θ (Or.inl hz')
  · have h0 : (fun z' => h z' θ) = fun _ => (0 : ℝ) := funext (fun z' => hh z' θ (Or.inr hz))
    show deriv (fun z' => h z' θ) z = 0
    rw [h0, deriv_const]

lemma vanishesOff_pth {A B c d : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → h z θ = 0) :
    ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.pth h z θ = 0 := by
  intro z θ hz
  rcases hz with hz | hz
  · have h0 : (fun θ' => h z θ') = fun _ => (0 : ℝ) := funext (fun θ' => hh z θ' (Or.inl hz))
    show deriv (fun θ' => h z θ') θ = 0
    rw [h0, deriv_const]
  · refine Work.EllipticEst.Core.deriv_eq_zero_of_eventuallyEq_zero ?_
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hz] with θ' hθ'
    exact hh z θ' (Or.inr hθ')

lemma vanishesOff_Dz {A B c d : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → h z θ = 0) :
    ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.Dz h z θ = 0 := by
  intro z θ hz
  have hpz := vanishesOff_pz hh z θ hz
  change z * Work.Spaces.pz h z θ = 0
  rw [hpz, mul_zero]

lemma vanishesOff_Dth {A B c d : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → h z θ = 0) :
    ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.Dth h z θ = 0 := by
  intro z θ hz
  have hpth := vanishesOff_pth hh z θ hz
  change Real.sin (2 * θ) * Work.Spaces.pth h z θ = 0
  rw [hpth, mul_zero]

lemma vanishesOff_pzIter {A B c d : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → h z θ = 0) (n : ℕ) :
    ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.pzIter n h z θ = 0 := by
  induction n with
  | zero => exact hh
  | succ n ih => simpa only [Work.Spaces.pzIter_succ] using vanishesOff_pz ih

lemma vanishesOff_pthIter {A B c d : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → h z θ = 0) (n : ℕ) :
    ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.pthIter n h z θ = 0 := by
  induction n with
  | zero => exact hh
  | succ n ih => simpa only [Work.Spaces.pthIter_succ] using vanishesOff_pth ih

lemma vanishesOff_DzIter {A B c d : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → h z θ = 0) (n : ℕ) :
    ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.DzIter n h z θ = 0 := by
  induction n with
  | zero => exact hh
  | succ n ih => simpa only [Work.Spaces.DzIter_succ] using vanishesOff_Dz ih

lemma vanishesOff_DthIter {A B c d : ℝ} {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → h z θ = 0) (n : ℕ) :
    ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.DthIter n h z θ = 0 := by
  induction n with
  | zero => exact hh
  | succ n ih => simpa only [Work.Spaces.DthIter_succ] using vanishesOff_Dth ih

/-! ## 2. Smoothness on the closed angular interval from smoothness on the open one

For a function which vanishes outside a compact subinterval `[c,d] ⊂ (0,π/2)`, smoothness on the
open interval upgrades to smoothness on the closed interval `Iθ`: at the two endpoints the
function is identically zero on a neighbourhood. -/

lemma contDiffOn_Icc_of_contDiffOn_Ioo_of_supp {n : ℕ} {f : ℝ → ℝ} {c d : ℝ}
    (hc : 0 < c) (hd : d < Real.pi / 2)
    (hf : ContDiffOn ℝ n f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hsupp : ∀ θ : ℝ, θ ∉ Set.Icc c d → f θ = 0) :
    ContDiffOn ℝ n f (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  intro θ hθ
  by_cases h1 : θ < c
  · have hev : f =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds h1] with θ' hθ'
      exact hsupp θ' (by rintro ⟨h2, -⟩; exact absurd h2 (not_le.mpr hθ'))
    exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev).contDiffWithinAt
  · by_cases h2 : d < θ
    · have hev : f =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds h2] with θ' hθ'
        exact hsupp θ' (by rintro ⟨-, h3⟩; exact absurd h3 (not_le.mpr hθ'))
      exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev).contDiffWithinAt
    · have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨lt_of_lt_of_le hc (not_lt.mp h1), lt_of_le_of_lt (not_lt.mp h2) hd⟩
      exact (hf.contDiffAt (isOpen_Ioo.mem_nhds hθmem)).contDiffWithinAt

/-! ## 3. Derivative identities for the slices of `G`

For `z > 0` and `θ ∈ (0,π/2)` the angular derivatives of the `θ`-slice of `D_zG` are the
corresponding slices of `D_z∂_θG`, resp. `D_z∂_θ²G` (Clairaut on the open quadrant). -/

lemma deriv_slice_Dz {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.Dz G z θ') θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  exact (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall G).mp hG) 1) hmem

lemma deriv2_slice_Dz {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  have hEq1 : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz G)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth G))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall G).mp hG) 1
  have hEq2 : Set.EqOn
      (Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth G))))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G))))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth G)).mp hG.pth) 1
  have hfd : deriv (fun θ' => Work.Spaces.Dz G z θ')
      = fun θ' => Work.Spaces.pth (Work.Spaces.Dz G) z θ' := by
    funext θ'; rfl
  rw [hfd]
  show Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ
  rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq1 hmem]
  exact hEq2 hmem

/-! ## 4. The slicewise interpolation inequality

For `z ≥ 0`, with `σ_a = sigA α` the light weight:

  `∫_θ (D_z∂_θG)² σ_a ≤ -∫_θ (D_zG)(D_z∂_θ²G) σ_a`

(`0 ≤ z` is enough: at `z = 0` both sides are `0`). -/

lemma slice_ineq_compact {G : ℝ → ℝ → ℝ} {α c d : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hc : 0 < c) (hcd : c ≤ d) (hd : d < Real.pi / 2)
    (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hθsupp : ∀ z θ : ℝ, θ ∉ Set.Icc c d → G z θ = 0)
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * sigA α θ)
      ≤ - ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz G z θ) * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ)
            * sigA α θ := by
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    simp [Work.Spaces.Dz]
  · have hf : ContDiffOn ℝ 2 (fun θ' => Work.Spaces.Dz G z θ')
        (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_Icc_of_contDiffOn_Ioo_of_supp hc hd
        (((hG.Dz).curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder]))
        (fun θ hθ => by
          have h0 : (fun z' => G z' θ) = fun _ => (0 : ℝ) :=
            funext (fun z' => hθsupp z' θ hθ)
          change z * deriv (fun z' => G z' θ) z = 0
          rw [h0, deriv_const, mul_zero])
    have hsuppf : ∀ θ : ℝ, θ ∉ Set.Icc c d → (fun θ' => Work.Spaces.Dz G z θ') θ = 0 :=
      fun θ hθ => by
        have h0 : (fun z' => G z' θ) = fun _ => (0 : ℝ) := funext (fun z' => hθsupp z' θ hθ)
        change z * deriv (fun z' => G z' θ) z = 0
        rw [h0, deriv_const, mul_zero]
    have hS := slice_ibp_sigA_compact α hα hα4 hc hcd hd hf hsuppf
    have hIoo : ∀ g : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, g θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g θ := fun g =>
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm
    have hpt1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv (fun θ' => Work.Spaces.Dz G z θ') θ) ^ 2 * sigA α θ
          = (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * sigA α θ :=
      fun θ hθ => by rw [deriv_slice_Dz hG hzpos hθ]
    have hpt2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (fun θ' => Work.Spaces.Dz G z θ') θ
            * deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ * sigA α θ
          = (Work.Spaces.Dz G z θ) * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ)
              * sigA α θ :=
      fun θ hθ => by rw [deriv2_slice_Dz hG hzpos hθ]
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * sigA α θ)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * sigA α θ := hIoo _
      _ = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv (fun θ' => Work.Spaces.Dz G z θ') θ) ^ 2 * sigA α θ :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
            (fun θ hθ => (hpt1 θ hθ).symm)
      _ = ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => Work.Spaces.Dz G z θ') θ) ^ 2 * sigA α θ := (hIoo _).symm
      _ ≤ - ∫ θ in Work.Spaces.Iθ, (fun θ' => Work.Spaces.Dz G z θ') θ
            * deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ * sigA α θ := hS
      _ = - ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (fun θ' => Work.Spaces.Dz G z θ') θ
            * deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ * sigA α θ := by rw [hIoo]
      _ = - ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (Work.Spaces.Dz G z θ) * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ)
              * sigA α θ := by
          rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hpt2 θ hθ)]
      _ = - ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G z θ) * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ)
              * sigA α θ := by rw [hIoo]

/-! ## 5. Continuity on the support rectangle -/

lemma R0_subset_Q0 {A B c d : ℝ} (hA : 0 < A) (hc : 0 < c) (hd : d < Real.pi / 2) :
    Set.Icc A B ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  rw [Work.FTS.EllipticEst.mem_Q0]
  exact ⟨lt_of_lt_of_le hA hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩

lemma continuousOn_wsq_fst :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.EllipticEst.Q0 := by
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    rw [show (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 from by
      funext z; rw [Work.Spaces.w]]
    refine ContinuousOn.pow (ContinuousOn.div ?_ ?_ ?_) 2
    · fun_prop
    · fun_prop
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  exact hw.comp continuousOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

lemma continuousOn_sigA_snd {α : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ => sigA α p.2) Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  show ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
    Work.FTS.EllipticEst.Q0
  refine hsin.rpow_const (fun p hp => Or.inl ?_)
  have hp' := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp'.2.1])
    (by linarith [hp'.2.2, Real.pi_pos]))

lemma continuousOn_bcoef_fst :
    ContinuousOn (fun p : ℝ × ℝ => bcoef p.1) (Set.Ioi 0 ×ˢ Set.univ) := by
  show ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1)) (Set.Ioi 0 ×ˢ Set.univ)
  refine ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
    (continuousOn_const.add continuousOn_fst) (fun p hp => ?_)
  have hpos : 0 < p.1 := hp.1
  linarith

/-! ## 6. The main theorem -/

theorem interpGamma_core_compact :
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧
        (∀ z θ : ℝ, θ ∉ Set.Icc a b → G z θ = 0)) →
      (∃ a b : ℝ, 0 < a ∧ a < b ∧
        (∀ z : ℝ, z ∉ Set.Icc a b → ∀ θ : ℝ, G z θ = 0)) →
      Work.FTS.EllipticEst.TT.Xint α G
        ≤ Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
            * Work.FTS.EllipticEst.TT.TTint α G) := by
  intro α G hα hα4 hG hθbox hZbox
  obtain ⟨c, d, hc, hcd, hd, hθsupp⟩ := hθbox
  obtain ⟨A, B, hA, hAB, hZsupp⟩ := hZbox
  -- the common support hypothesis, in the disjunctive form
  have hvan : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → G z θ = 0 :=
    fun z θ h => h.elim (fun h1 => hZsupp z h1 θ) (fun h2 => hθsupp z θ h2)
  -- vanishing of the relevant derivatives off the rectangle
  have hvDzG : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → Work.Spaces.Dz G z θ = 0 :=
    vanishesOff_Dz hvan
  have hvDzpthG : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d →
      Work.Spaces.Dz (Work.Spaces.pth G) z θ = 0 :=
    vanishesOff_Dz (vanishesOff_pth hvan)
  have hvDzpth2G : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d →
      Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ = 0 :=
    vanishesOff_Dz (vanishesOff_pthIter hvan 2)
  have hvpth2G : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d →
      Work.Spaces.pthIter 2 G z θ = 0 :=
    vanishesOff_pthIter hvan 2
  have hvDzDzG : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d →
      Work.Spaces.Dz (Work.Spaces.Dz G) z θ = 0 :=
    vanishesOff_Dz (vanishesOff_Dz hvan)
  -- the integrands
  set U : ℝ → ℝ → ℝ := fun z θ =>
    (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ with hU
  set W : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.Dz G z θ)
    * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ) * (Work.Spaces.w z) ^ 2 * sigA α θ with hW
  set H : ℝ → ℝ → ℝ := fun z θ =>
    (Work.Spaces.Dz (Work.Spaces.Dz G) z θ + bcoef z * Work.Spaces.Dz G z θ)
      * (Work.Spaces.pthIter 2 G z θ) * (Work.Spaces.w z) ^ 2 * sigA α θ with hH
  -- continuity on the closed rectangle
  have hsub : Set.Icc A B ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := R0_subset_Q0 hA hc hd
  have hcontU : ContinuousOn (Function.uncurry U) (Set.Icc A B ×ˢ Set.Icc c d) := by
    rw [hU]
    exact ContinuousOn.mul (ContinuousOn.mul
      ((((hG.pth).Dz).continuousOn.mono hsub).pow 2)
      (continuousOn_wsq_fst.mono hsub)) (continuousOn_sigA_snd.mono hsub)
  have hcontW : ContinuousOn (Function.uncurry W) (Set.Icc A B ×ˢ Set.Icc c d) := by
    rw [hW]
    exact ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul
      (((hG.Dz).continuousOn.mono hsub))
      ((((hG.pth).pth).Dz).continuousOn.mono hsub))
      (continuousOn_wsq_fst.mono hsub)) (continuousOn_sigA_snd.mono hsub)
  have hcontH : ContinuousOn (Function.uncurry H) (Set.Icc A B ×ˢ Set.Icc c d) := by
    rw [hH]
    exact ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.mul
      (ContinuousOn.add ((((hG.Dz).Dz).continuousOn.mono hsub))
        (((continuousOn_bcoef_fst.mono (fun p hp => ⟨lt_of_lt_of_le hA hp.1.1, trivial⟩)).mul
          ((hG.Dz).continuousOn.mono hsub))))
      ((((hG.pth).pth).continuousOn.mono hsub)))
      (continuousOn_wsq_fst.mono hsub)) (continuousOn_sigA_snd.mono hsub)
  -- supports
  have hsuppU : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → U z θ = 0 := by
    intro z θ hz
    simp only [hU]
    rw [hvDzpthG z θ hz]
    ring
  have hsuppW : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → W z θ = 0 := by
    intro z θ hz
    simp only [hW]
    rw [hvDzG z θ hz]
    ring
  have hsuppH : ∀ z θ : ℝ, z ∉ Set.Icc A B ∨ θ ∉ Set.Icc c d → H z θ = 0 := by
    intro z θ hz
    simp only [hH]
    rcases hz with hz | hz
    · rw [hvDzDzG z θ (Or.inl hz), hvDzG z θ (Or.inl hz)]
      ring
    · rw [hvpth2G z θ (Or.inr hz)]
      ring
  -- Fubini + marginal integrability
  have hswapU := swap_prod_supported hA hAB hc hcd hd (f := U) hcontU hsuppU
  have hswapW := swap_prod_supported hA hAB hc hcd hd (f := W) hcontW hsuppW
  have hswapH := swap_prod_supported hA hAB hc hcd hd (f := H) hcontH hsuppH
  have hmargU : MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, U z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hswapU.2.1
  have hmargW : MeasureTheory.Integrable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, W z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hswapW.2.1
  -- ## Step 1: the pointwise slice inequality, integrated against `w²`
  have hstep1 : Work.FTS.EllipticEst.TT.Xint α G
      ≤ - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, W z θ := by
    have hXU : Work.FTS.EllipticEst.TT.Xint α G
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, U z θ := by
      rw [Xint, hU]
    rw [hXU]
    have hmono : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, U z θ)
        ≤ ∫ z in Work.Spaces.Iz, (-(∫ θ in Work.Spaces.Iθ, W z θ)) := by
      refine MeasureTheory.setIntegral_mono_on hmargU hmargW.neg measurableSet_Ici
        (fun z hz => ?_)
      have hI : (∫ θ in Work.Spaces.Iθ, U z θ) = (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * sigA α θ) := by
        rw [hU, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        ring
      have hJ : (∫ θ in Work.Spaces.Iθ, W z θ) = (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ) * sigA α θ) := by
        rw [hW, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        ring
      rw [hI, hJ]
      have hslice := slice_ineq_compact (G := G) hα hα4 hc hcd.le hd hG hθsupp hz
      have hthis := mul_le_mul_of_nonneg_left hslice (sq_nonneg (Work.Spaces.w z))
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * sigA α θ)
          ≤ (Work.Spaces.w z) ^ 2 * (-(∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ)
                * sigA α θ)) := hthis
        _ = -((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ)
                * sigA α θ)) := by ring
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, U z θ)
        ≤ ∫ z in Work.Spaces.Iz, (-(∫ θ in Work.Spaces.Iθ, W z θ)) := hmono
      _ = - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, W z θ :=
          MeasureTheory.integral_neg (f := fun z : ℝ => ∫ θ in Work.Spaces.Iθ, W z θ)
  -- ## Step 2: Fubini in `(z,θ)` and the radial `T`-adjoint
  have hstep2 : - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, W z θ
      = ∫ θ in Work.Spaces.Iθ, sigA α θ * (∫ z in Work.Spaces.Iz,
          (Work.Spaces.Dz (Work.Spaces.Dz G) z θ + bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pthIter 2 G z θ) * (Work.Spaces.w z) ^ 2) := by
    rw [hswapW.2.2]
    have hinner : (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, W z θ)
        = ∫ θ in Work.Spaces.Iθ, -(sigA α θ * (∫ z in Work.Spaces.Iz,
            (Work.Spaces.Dz (Work.Spaces.Dz G) z θ + bcoef z * Work.Spaces.Dz G z θ)
              * (Work.Spaces.pthIter 2 G z θ) * (Work.Spaces.w z) ^ 2)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      have h1 : (∫ z in Work.Spaces.Iz, W z θ) = sigA α θ
          * (∫ z in Work.Spaces.Iz, (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pthIter 2 G) z θ) * (Work.Spaces.w z) ^ 2) := by
        simp only [hW, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        ring
      rw [h1, radial_ibp_slice hA hAB hc hd hG hZsupp hθsupp hθ]
      ring
    rw [hinner, MeasureTheory.integral_neg]
    simp
  -- ## Step 3: rewriting the `θ`-outer form as the `z`-outer form of `H`
  have hstep3 : (∫ θ in Work.Spaces.Iθ, sigA α θ * (∫ z in Work.Spaces.Iz,
        (Work.Spaces.Dz (Work.Spaces.Dz G) z θ + bcoef z * Work.Spaces.Dz G z θ)
          * (Work.Spaces.pthIter 2 G z θ) * (Work.Spaces.w z) ^ 2))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, H z θ := by
    rw [hswapH.2.2]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    simp only [hH, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    ring
  -- ## Step 4: Cauchy–Schwarz in the two variables
  have hstep4 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, H z θ)
      ≤ Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
          * Work.FTS.EllipticEst.TT.TTint α G) := by
    rw [hH, DDint, TTint]
    refine interp_amgm_rect hA hAB hc hcd hd hα hα4
      (P := fun z θ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ
        + bcoef z * Work.Spaces.Dz G z θ)
      (Q := fun z θ => Work.Spaces.pthIter 2 G z θ) ?_ ?_ ?_ ?_
    · exact ContinuousOn.add ((((hG.Dz).Dz).continuousOn.mono hsub))
        (((continuousOn_bcoef_fst.mono (fun p hp => ⟨lt_of_lt_of_le hA hp.1.1, trivial⟩)).mul
          ((hG.Dz).continuousOn.mono hsub)))
    · intro z θ hz
      rcases hz with hz | hz
      · rw [hvDzDzG z θ (Or.inl hz), hvDzG z θ (Or.inl hz)]
        ring
      · rw [hvDzDzG z θ (Or.inr hz), hvDzG z θ (Or.inr hz)]
        ring
    · exact (((hG.pth).pth).continuousOn.mono hsub)
    · intro z θ hz
      exact hvpth2G z θ hz
  calc Work.FTS.EllipticEst.TT.Xint α G
      ≤ - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, W z θ := hstep1
    _ = ∫ θ in Work.Spaces.Iθ, sigA α θ * (∫ z in Work.Spaces.Iz,
          (Work.Spaces.Dz (Work.Spaces.Dz G) z θ + bcoef z * Work.Spaces.Dz G z θ)
            * (Work.Spaces.pthIter 2 G z θ) * (Work.Spaces.w z) ^ 2) := hstep2
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, H z θ := hstep3
    _ ≤ Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
        * Work.FTS.EllipticEst.TT.TTint α G) := hstep4

end Work.FTS.EllipticEst.TT
