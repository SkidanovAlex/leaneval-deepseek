import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.SliceHyp
import Submission.Work.FTS.EllipticEst.Honest.I4GlobalAssembly
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeWAux

set_option maxHeartbeats 1600000

/-!
# `aeI4Of`: the `I₄` upper bound from the single-slice inequality

`Work.FTS.EllipticEst.Honest.SliceIneq` is the *single-angular-slice* inequality

`∫_θ ∂_θ(tan θ·Φ)·Φ''·σ ≤ 50∫_θ(Φ/cos θ)²σ + √(∫_θ(Φ/cos θ)²σ)·√(∫_θ(Φ'')²σ)`

for `Φ : ℝ → ℝ` of class `C²` on `(0,π/2)` whose two weighted squares are integrable.

The lemma below turns it into the *two-dimensional* (`z`-integrated) `I₄` upper bound in the
weakest hypothesis class in which the assembly makes sense: `u` smooth on the open quadrant,
`HkMem α 0 (u/cos θ)` and `HkMem α 0 (∂_θθu)`.  Neither the equation `bslOp α u = G`, nor the
Dirichlet data, nor the solvability conditions, nor the honesty of `G`/`z²∂_zz u` are needed:
the source term of the honest statement simply disappears from the estimate, and for every
`z > 0` the slice `Φ := u z ·` satisfies the hypotheses of `SliceIneq` because the two weighted
`θ`-integrals are `(w2 z)⁻¹`-multiples of `HkIntegrand`-slices of the two honest functions.

The constant produced is `51`.
-/

/-- **The slicewise `I₄` inequality in the weak class.**

Let `u` be smooth on the open quadrant, `HkMem α 0 (∂_θθ u)` and `HkMem α 0 (u / cos θ)`.  Then for
every `z > 0` the `θ`-slice `θ ↦ u z θ` satisfies the single-slice inequality of
`Work.FTS.EllipticEst.Honest.SliceIneq`: the two weighted squares are integrable on `Iθ` (they are
`(w2 z)⁻¹`-multiples of the corresponding `HkIntegrand`-slices).

This is `Work.FTS.EllipticEst.Honest.I4SliceStep` with the `Hon α F Ψ` hypothesis weakened to the
two facts that proof actually consumes (the slice smoothness for the `C²` requirement and
`HkMem α 0 (∂_θθ u)` for the integrability of the `∂_θθ`-slice). -/
theorem sliceStepOf (hS : Work.FTS.EllipticEst.Honest.SliceIneq) {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ))
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ
          * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ 50 * (∫ θ in Work.Spaces.Iθ,
            (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        + Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 u z θ) ^ 2
                * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  -- (1) the slice is `C²` on the open interval
  have hslice : ContDiffOn ℝ 2 (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 := hsm 2
    have hg : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have hcomp := h2.comp hg (fun θ hθ => ⟨hz, hθ⟩)
    simpa [Function.comp_def] using hcomp
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw2ne : Work.FTS.EllipticEst.AngSecond.w2 z ≠ 0 := by
    have hwpos := Work.FTS.EllipticEst.AngSecond.w_pos hz
    simp only [Work.FTS.EllipticEst.AngSecond.w2]
    positivity
  -- (2) integrability of the two weighted squares, from `HkMem α 0 (u/cos)` and `HkMem α 0 (∂_θθu)`
  have hptQ : Set.EqOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => u z θ / Real.cos θ) z θ)
      (fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
        * ((u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      Work.Spaces.Iθ := by
    intro θ hθ
    beta_reduce
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
      Work.FTS.EllipticEst.Honest.sq_profile_eq (fun z θ => u z θ / Real.cos θ) z θ
        (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ),
      Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hQz : MeasureTheory.IntegrableOn
      (fun θ => (u z θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)) := by
    have h0 := MeasureTheory.IntegrableOn.congr_fun (hQ.1 z hzI) hptQ measurableSet_Icc
    have h1 := Work.FTS.EllipticEst.Honest.I4IntegrableOnOfConstMul h0 hw2ne measurableSet_Icc
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    show (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      = (u z θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
    rfl
  have hptB : Set.EqOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)
      (fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
        * ((Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      Work.Spaces.Iθ := by
    intro θ hθ
    beta_reduce
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
      Work.FTS.EllipticEst.Honest.sq_profile_eq (Work.Spaces.pthIter 2 u) z θ
        (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ),
      Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hBz : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun θ' => u z θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Icc 0 (Real.pi / 2)) := by
    have h0 := MeasureTheory.IntegrableOn.congr_fun (hB.1 z hzI) hptB measurableSet_Icc
    have h1 := Work.FTS.EllipticEst.Honest.I4IntegrableOnOfConstMul h0 hw2ne measurableSet_Icc
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    show (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      = (deriv (deriv (fun θ' => u z θ')) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
    rw [Work.FTS.EllipticEst.AngSecond.sig]
    rfl
  -- (3) instantiate the assumed slice inequality
  have hsl := hS (fun θ : ℝ => u z θ) hslice hQz hBz
  refine le_trans hsl ?_
  exact le_of_eq rfl

/-- **The `I₄` upper bound, from the single-slice inequality.**

Given `Work.FTS.EllipticEst.Honest.SliceIneq`, the estimate
`IP (∂_θ(tan θ·u)) (∂_θθu) ≤ C (‖u/cos θ‖² + ‖u/cos θ‖·‖∂_θθu‖)`

holds for every `α` and every `u` smooth on the open quadrant with `HkMem α 0 (u / cos θ)` and
`HkMem α 0 (∂_θθ u)`.

Proof: for each `z > 0` apply the slice inequality (`sliceStepOf`) to the slice `u z`; the two
weighted `θ`-integrals are `(w2 z)⁻¹`-multiples of the corresponding `HkSq`-slices
(`Honest.hksq_eq_w2_sliceIntegral`), multiply by `w2 z ≥ 0` and integrate in `z`; the cross term
`∫_z w2·√A·√B` is bounded by the radial Cauchy–Schwarz
(`AngSecond.setIntegral_w_mul_sqrt_le`, with the two `z`-integrals identified with
`HkSq α 0 (u/cos θ)` resp. `HkSq α 0 (∂_θθu)`).  The `z = 0` slice contributes `0` because
`w2 0 = 0`, so the pointwise domination `Fz ≤ Gz` holds on all of `Iz`.  The source term of the
honest statement is absent from the conclusion and is never used. -/
theorem aeI4Of (hslice : Work.FTS.EllipticEst.Honest.SliceIneq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) →
      Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
          (Work.Spaces.pthIter 2 u)
        ≤ C * (Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
            + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ))
              * Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
  refine ⟨51, by norm_num, ?_⟩
  intro α u hsm hQmem hBmem
  set Q : ℝ → ℝ → ℝ := fun z θ => u z θ / Real.cos θ with hQdef
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u with hBdef
  set U : ℝ → ℝ → ℝ :=
    fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ with hUdef
  set A : ℝ → ℝ := fun z =>
    ∫ θ in Work.Spaces.Iθ, (Q z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ with hAdef
  set Bz : ℝ → ℝ := fun z =>
    ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ with hBzdef
  set Fz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.w2 z
      * Work.FTS.EllipticEst.AngSecond.sig θ with hFzdef
  set Gz : ℝ → ℝ := fun z => Work.FTS.EllipticEst.AngSecond.w2 z
    * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)) with hGzdef
  -- `HkSq α 0 g` is the iterated integral of `w z² ∫_θ g² σ`
  have hA := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral (α := α) (g := Q) hQmem
  have hBz' := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral (α := α) (g := B) hBmem
  have hAint : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * A z) Work.Spaces.Iz := hA.1
  have hBzint : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * Bz z) Work.Spaces.Iz := hBz'.1
  have hAval : ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z * A z
      = Work.Spaces.HkSq α 0 Q := hA.2
  have hBzval : ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z * Bz z
      = Work.Spaces.HkSq α 0 B := hBz'.2
  -- the two angular slice integrals are nonnegative
  have hA0 : ∀ z, 0 ≤ A z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
  have hBz0 : ∀ z, 0 ≤ Bz z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
  -- the radial Cauchy–Schwarz for the cross term
  have hcross := Work.FTS.EllipticEst.AngSecond.setIntegral_w_mul_sqrt_le (s := Work.Spaces.Iz)
    (m := Work.FTS.EllipticEst.AngSecond.w2) (A := A) (B := Bz)
    Work.FTS.EllipticEst.AngSecond.w2_nonneg hA0 hBz0 hAint hBzint
  have hcrossB : (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z))
      ≤ Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) := by
    refine le_trans hcross.2 ?_
    rw [hAval, hBzval]
  -- integrability and value of `∫_z Gz`
  have hGsum : (fun z => Work.FTS.EllipticEst.AngSecond.w2 z
        * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)))
      = fun z => 50 * (Work.FTS.EllipticEst.AngSecond.w2 z * A z)
          + Work.FTS.EllipticEst.AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) :=
    funext fun z => by ring
  have hGint : MeasureTheory.IntegrableOn Gz Work.Spaces.Iz := by
    rw [hGzdef, hGsum]
    exact (hAint.const_mul 50).add hcross.1
  have hGval : ∫ z in Work.Spaces.Iz, Gz z
      = 50 * (Work.Spaces.HkSq α 0 Q)
        + ∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) := by
    rw [hGzdef, hGsum]
    rw [MeasureTheory.integral_add (hAint.const_mul 50) hcross.1,
      MeasureTheory.integral_const_mul, hAval]
  -- the pointwise domination `Fz ≤ Gz` on `Iz`
  have hpoint : ∀ z ∈ Work.Spaces.Iz, Fz z ≤ Gz z := by
    intro z hz
    rcases eq_or_ne z 0 with hz0 | hz0
    · -- at `z = 0` both sides vanish because `w2 0 = 0`
      subst hz0
      have hw0 : Work.FTS.EllipticEst.AngSecond.w2 0 = 0 := by
        rw [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
        norm_num
      have hFz0 : Fz 0 = 0 := by
        rw [hFzdef]
        beta_reduce
        simp only [hw0, mul_zero]
        simp
      have hGz0 : Gz 0 = 0 := by
        rw [hGzdef]
        beta_reduce
        rw [hw0]; ring
      rw [hFz0, hGz0]
    · -- at `z > 0` use the slice inequality
      have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hsl := sliceStepOf hslice hsm hBmem hQmem hzpos
      have hsl' : (∫ θ in Work.Spaces.Iθ,
            U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.sig θ)
          ≤ 50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z) := hsl
      have hconst : Fz z = Work.FTS.EllipticEst.AngSecond.w2 z
          * (∫ θ in Work.Spaces.Iθ,
              U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.sig θ) := by
        rw [hFzdef]
        beta_reduce
        rw [show (fun θ => U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)
            = (fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
                * (U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.sig θ)) from
          funext fun θ => by ring]
        exact MeasureTheory.integral_const_mul _ _
      have hGz : Gz z = Work.FTS.EllipticEst.AngSecond.w2 z
          * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)) := by
        rw [hGzdef]
      rw [hconst, hGz]
      exact mul_le_mul_of_nonneg_left hsl'
        (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
  have hFG : Fz ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz] Gz :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
      (Filter.Eventually.of_forall fun z hz => hpoint z hz)
  have hGz0 : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz] Gz :=
    Filter.Eventually.of_forall fun z => by
      rw [hGzdef]
      exact mul_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
        (add_nonneg (mul_nonneg (by norm_num) (hA0 z))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  -- the iterated integral is the pairing, and the assembly
  have hIP : Work.FTS.EllipticEst.AngSecond.IP U B = ∫ z in Work.Spaces.Iz, Fz z := by
    rw [hFzdef]
    rfl
  have hfinal : Work.FTS.EllipticEst.AngSecond.IP U B
      ≤ 50 * (Work.Spaces.HkSq α 0 Q)
        + Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) := by
    calc Work.FTS.EllipticEst.AngSecond.IP U B = ∫ z in Work.Spaces.Iz, Fz z := hIP
      _ ≤ ∫ z in Work.Spaces.Iz, Gz z :=
          Work.FTS.EllipticEst.integral_le_integral_of_ae_le hFG hGint hGz0
      _ = 50 * (Work.Spaces.HkSq α 0 Q)
            + ∫ z in Work.Spaces.Iz,
                Work.FTS.EllipticEst.AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) :=
          hGval
      _ ≤ 50 * (Work.Spaces.HkSq α 0 Q)
            + Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) :=
          add_le_add le_rfl hcrossB
  have hQ0 : 0 ≤ Work.Spaces.HkSq α 0 Q :=
    Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α Q
  have hc0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  linarith [hfinal, hQ0, hc0]

end Work.FTS.EllipticEst.H2W.AeWAux
