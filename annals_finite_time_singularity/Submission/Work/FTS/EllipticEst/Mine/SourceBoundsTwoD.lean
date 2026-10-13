/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Mine.SourceBoundsTwoD`

The source slots of the level-`2` elliptic estimate: for `1 ≤ γ ≤ 3/2`, `D > 0` there is
`C > 0` such that for every weak datum `EllWeakPos α 2 F Ψ`, `0 < α ≤ 1/4`, `γ ≤ gam α`, the
four *assumed* slot bounds

* `∫∫ w²(∂_θ²(z²∂_z²Ψ))²σ₄ ≤ D|F|²`, `∫∫ w²(∂_θ(z²∂_z²Ψ))²σ₂ ≤ D|F|²`,
* `∫∫ w²(∂_θ(D_zΨ))²σ₂ ≤ D|F|²`, `∫∫ w²(∂_θ²(D_zΨ))²σ₄ ≤ D|F|²`

together with the plain `F`-slots (`FSlotsTwoD`) bound the two *source* slots

* `∫∫ w²(∂_θG)²σ₂ ≤ C|F|²` and `∫∫ w²(∂_θ²G)²σ₄ ≤ C|F|²`, `G = Gsrc α F Ψ`.

## The argument

Write `G = F + α²Φ + α(5+α)Λ` with `Φ = z²∂_z²Ψ` and `Λ = D_zΨ` (the definition of `Gsrc`).
On the open quadrant all three summands are `C^∞`, so (for `z > 0`, `0 < θ < π/2`)

`∂_θG = ∂_θF + α²∂_θΦ + α(5+α)∂_θΛ`,  `∂_θ²G = ∂_θ²F + α²∂_θ²Φ + α(5+α)∂_θ²Λ`

(`SrcBnd.GsrcPthOne`, `SrcBnd.GsrcPthTwo`), and the *reverse* form
`α(5+α)∂_θΛ = ∂_θG − ∂_θF − α²∂_θΦ` (and the analogous second-order identity) is used
together with the elementary inequality `(x+y+z)² ≤ 3(x²+y²+z²)`.

The whole content is then the *junk-value* bookkeeping of the Bochner integral: the slot
`(∂_θΛ)²σ₂` is **not** known to be integrable (nothing in the hypothesis class controls
`D_zΨ`), so the domination of `(∂_θG)²σ₂` by the three slots can only be used in the case where
the `Λ`-slot *is* integrable.  In the other case the reverse identity shows that the `G`-slot is
non-integrable as well, so *both* Bochner integrals vanish by `MeasureTheory.integral_undef`
and the inequality is trivial.  The same dichotomy is then repeated one level up, in the
`z`-variable, to combine the bound with the four hypotheses.

## Layout

* `slotFun`, `slot`: the weighted angular slot `w²·((∂_θⁿX)²σ)` of a datum `X`, pointwise and
  integrated over `Iθ`;
* the elementary nonnegativity/vanishing lemmas, the continuity of `σ₂`, `σ₄` on the open
  quadrant, and the three algebraic inequalities;
* `slot_dichotomy`: at a fixed `z`, the two comparison inequalities for the *integrals* over
  `Iθ`, by cases on the integrability of the `Λ`-slot;
* `slotBound_core`: the `z`-level assembly of the dichotomy, the four bounds and the arithmetic;
* `cmp_one`, `cmp_two`: the pointwise comparison inequalities at levels `1` (weight `σ₂`) and
  `2` (weight `σ₄`), from the two derivative identities;
* `SourceBoundsTwoD`: the instantiation of the two cores and the assembly.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.SrcBnd.GsrcPthOne
import Submission.Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo
import Submission.Work.FTS.EllipticEst.SrcBnd.SlotAESM
import Submission.Work.FTS.EllipticEst.SrcBnd.SlotIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000



namespace Work.FTS.EllipticEst.Mine

/-! ## The slot functions -/

/-- The pointwise weighted angular slot of level `n` with weight `σ`:
`w(z)²·((∂_θⁿX(z,θ))²·σ(θ))`.  The factor `w(z)²` is kept *inside* so that the slot vanishes
identically at `z = 0`; this is what makes the measurability statements uniform in `z`. -/
private def slotFun (n : ℕ) (σ : ℝ → ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n X z θ) ^ 2 * σ θ)

/-- The angular slot of level `n` with weight `σ`, integrated over `Iθ`. -/
private def slot (n : ℕ) (σ : ℝ → ℝ) (X : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, slotFun n σ X z θ

private lemma slotFun_nonneg {n : ℕ} {σ : ℝ → ℝ}
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ) (X : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ slotFun n σ X z θ :=
  mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hσnn θ hθ))

private lemma slot_nonneg {n : ℕ} {σ : ℝ → ℝ}
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ) (X : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ slot n σ X z :=
  integral_nonneg_of_ae
    (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => slotFun_nonneg hσnn X z θ hθ)

private lemma slotFun_eq_zero_of_left {n : ℕ} {σ : ℝ → ℝ} (X : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : (Work.Spaces.w z) ^ 2 = 0) : slotFun n σ X z θ = 0 := by
  simp [slotFun, h]

private lemma slotFun_eq_zero_of_right {n : ℕ} {σ : ℝ → ℝ} (X : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : σ θ = 0) : slotFun n σ X z θ = 0 := by
  simp [slotFun, h]

private lemma w_zero_sq : (Work.Spaces.w 0) ^ 2 = 0 := by
  norm_num [Work.Spaces.w]

/-! ## The angular weights `σ₂ = sin(2θ)^{2-γ}` and `σ₄ = sin(2θ)^{4-γ}` -/

private lemma sig2_zero_left {γ : ℝ} (hγ : γ ≤ 3 / 2) : sig2 γ 0 = 0 := by
  rw [sig2, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by linarith)

private lemma sig2_zero_right {γ : ℝ} (hγ : γ ≤ 3 / 2) : sig2 γ (Real.pi / 2) = 0 := by
  rw [sig2, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by linarith)

private lemma sig4_zero_left {γ : ℝ} (hγ : γ ≤ 3 / 2) : sig4 γ 0 = 0 := by
  rw [sig4, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by linarith)

private lemma sig4_zero_right {γ : ℝ} (hγ : γ ≤ 3 / 2) : sig4 γ (Real.pi / 2) = 0 := by
  rw [sig4, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by linarith)

private lemma sin_two_pos_of_mem_Q0 {p : ℝ × ℝ}
    (hp : p ∈ Work.FTS.EllipticEst.Q0) : 0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

private lemma sig2_continuousOn (γ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => sig2 γ p.2) Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 :=
    fun p hp => ne_of_gt (sin_two_pos_of_mem_Q0 hp)
  change ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)).rpow (2 - γ))
    Work.FTS.EllipticEst.Q0
  exact hsin.rpow_const (fun p hp => Or.inl (hne p hp))

private lemma sig4_continuousOn (γ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => sig4 γ p.2) Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 :=
    fun p hp => ne_of_gt (sin_two_pos_of_mem_Q0 hp)
  change ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)).rpow (4 - γ))
    Work.FTS.EllipticEst.Q0
  exact hsin.rpow_const (fun p hp => Or.inl (hne p hp))

/-! ## Three algebraic inequalities -/

private lemma add_sq_le_three (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

private lemma sq_three_le (a b c α : ℝ) :
    (a + α ^ 2 * b + α * (5 + α) * c) ^ 2
      ≤ 3 * a ^ 2 + 3 * α ^ 4 * b ^ 2 + 3 * α ^ 2 * (5 + α) ^ 2 * c ^ 2 := by
  nlinarith [sq_nonneg (a - α ^ 2 * b), sq_nonneg (α ^ 2 * b - α * (5 + α) * c),
    sq_nonneg (a - α * (5 + α) * c)]

private lemma sq_rev_le (s a b d α : ℝ) (h : s = a + α ^ 2 * b + α * (5 + α) * d) :
    (α * (5 + α)) ^ 2 * d ^ 2 ≤ 3 * (s ^ 2 + a ^ 2 + α ^ 4 * b ^ 2) := by
  have h' : α * (5 + α) * d = s - a - α ^ 2 * b := by linarith [h]
  have h2 : ((α * (5 + α)) * d) ^ 2 = (s - a - α ^ 2 * b) ^ 2 := by rw [h']
  rw [show (α * (5 + α)) ^ 2 * d ^ 2 = ((α * (5 + α)) * d) ^ 2 by ring, h2]
  nlinarith [add_sq_le_three s (-a) (-(α ^ 2 * b))]

/-! ## The `θ`-level dichotomy -/

/-- **The `θ`-level dichotomy.**  At a fixed `z`, the two comparison inequalities between the
integrals over `Iθ` of the `F`-, `Φ`-, `Λ`- and `G`-slots.  The `Λ`-slot is not known to be
integrable; if it is, the two pointwise comparisons integrate directly, and if it is not, the
reverse comparison shows that the `G`-slot is not integrable either and both integrals vanish
by the junk-value convention. -/
private lemma slot_dichotomy (n : ℕ) (σ : ℝ → ℝ) (F Φ Λ G : ℝ → ℝ → ℝ) (α z : ℝ)
    (hα : 0 < α) (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hI : ∀ θ ∈ Work.Spaces.Iθ, slotFun n σ G z θ
      ≤ 3 * slotFun n σ F z θ + 3 * α ^ 4 * slotFun n σ Φ z θ
        + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ)
    (hII : ∀ θ ∈ Work.Spaces.Iθ, (α * (5 + α)) ^ 2 * slotFun n σ Λ z θ
      ≤ 3 * (slotFun n σ G z θ + slotFun n σ F z θ + α ^ 4 * slotFun n σ Φ z θ))
    (hFint : IntegrableOn (slotFun n σ F z) Work.Spaces.Iθ)
    (hPint : IntegrableOn (slotFun n σ Φ z) Work.Spaces.Iθ)
    (hLaesm : AEStronglyMeasurable (slotFun n σ Λ z) (volume.restrict Work.Spaces.Iθ))
    (hGaesm : AEStronglyMeasurable (slotFun n σ G z) (volume.restrict Work.Spaces.Iθ)) :
    slot n σ G z
        ≤ 3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z + 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z
      ∧ (α * (5 + α)) ^ 2 * slot n σ Λ z
        ≤ 3 * (slot n σ G z + slot n σ F z + α ^ 4 * slot n σ Φ z) := by
  have hθmeas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hAL : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ slotFun n σ Λ z θ :=
    fun θ hθ => slotFun_nonneg hσnn Λ z θ hθ
  have hAG : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ slotFun n σ G z θ :=
    fun θ hθ => slotFun_nonneg hσnn G z θ hθ
  have hc : 0 < (α * (5 + α)) ^ 2 := by positivity
  by_cases hLint : IntegrableOn (slotFun n σ Λ z) Work.Spaces.Iθ
  · have hdom : Integrable (fun θ => 3 * slotFun n σ F z θ + 3 * α ^ 4 * slotFun n σ Φ z θ
        + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ) (volume.restrict Work.Spaces.Iθ) :=
      ((hFint.const_mul 3).add (hPint.const_mul (3 * α ^ 4))).add
        (hLint.const_mul (3 * α ^ 2 * (5 + α) ^ 2))
    have hGint : IntegrableOn (slotFun n σ G z) Work.Spaces.Iθ :=
      Integrable.mono' hdom hGaesm
        (ae_restrict_of_forall_mem hθmeas fun θ hθ => by
          rw [Real.norm_of_nonneg (hAG θ hθ)]
          exact hI θ hθ)
    constructor
    · have hmono : (∫ θ in Work.Spaces.Iθ, slotFun n σ G z θ)
          ≤ (∫ θ in Work.Spaces.Iθ, (3 * slotFun n σ F z θ + 3 * α ^ 4 * slotFun n σ Φ z θ
              + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ)) :=
        MeasureTheory.integral_mono_of_nonneg
          (μ := volume.restrict Work.Spaces.Iθ)
          (f := slotFun n σ G z)
          (g := fun θ => 3 * slotFun n σ F z θ + 3 * α ^ 4 * slotFun n σ Φ z θ
            + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ)
          (ae_restrict_of_forall_mem hθmeas hAG) hdom
          (ae_restrict_of_forall_mem hθmeas hI)
      have hA : (∫ θ in Work.Spaces.Iθ, 3 * slotFun n σ F z θ) = 3 * slot n σ F z := by
        rw [MeasureTheory.integral_const_mul]; simp only [slot]
      have hB : (∫ θ in Work.Spaces.Iθ, 3 * α ^ 4 * slotFun n σ Φ z θ)
          = 3 * α ^ 4 * slot n σ Φ z := by
        rw [MeasureTheory.integral_const_mul]; simp only [slot]
      have hC : (∫ θ in Work.Spaces.Iθ, 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ)
          = 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z := by
        rw [MeasureTheory.integral_const_mul]; simp only [slot]
      have hAB : (∫ θ in Work.Spaces.Iθ, 3 * slotFun n σ F z θ + 3 * α ^ 4 * slotFun n σ Φ z θ)
          = (∫ θ in Work.Spaces.Iθ, 3 * slotFun n σ F z θ)
            + (∫ θ in Work.Spaces.Iθ, 3 * α ^ 4 * slotFun n σ Φ z θ) :=
        MeasureTheory.integral_add (hFint.const_mul 3) (hPint.const_mul (3 * α ^ 4))
      have htot : (∫ θ in Work.Spaces.Iθ, 3 * slotFun n σ F z θ + 3 * α ^ 4 * slotFun n σ Φ z θ
            + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ)
          = (∫ θ in Work.Spaces.Iθ, 3 * slotFun n σ F z θ + 3 * α ^ 4 * slotFun n σ Φ z θ)
            + (∫ θ in Work.Spaces.Iθ, 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ) :=
        MeasureTheory.integral_add ((hFint.const_mul 3).add (hPint.const_mul (3 * α ^ 4)))
          (hLint.const_mul (3 * α ^ 2 * (5 + α) ^ 2))
      have hrhs : (∫ θ in Work.Spaces.Iθ, (3 * slotFun n σ F z θ
            + 3 * α ^ 4 * slotFun n σ Φ z θ + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ))
          = 3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z
            + 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z := by
        linarith [hA, hB, hC, hAB, htot]
      rw [hrhs] at hmono
      exact hmono
    · have hdom2 : Integrable (fun θ => 3 * (slotFun n σ G z θ + slotFun n σ F z θ
          + α ^ 4 * slotFun n σ Φ z θ)) (volume.restrict Work.Spaces.Iθ) :=
        (((hGint.add hFint).add (hPint.const_mul (α ^ 4))).const_mul 3)
      have hmono : (∫ θ in Work.Spaces.Iθ, (α * (5 + α)) ^ 2 * slotFun n σ Λ z θ)
          ≤ (∫ θ in Work.Spaces.Iθ, 3 * (slotFun n σ G z θ + slotFun n σ F z θ
              + α ^ 4 * slotFun n σ Φ z θ)) :=
        MeasureTheory.integral_mono_of_nonneg
          (μ := volume.restrict Work.Spaces.Iθ)
          (f := fun θ => (α * (5 + α)) ^ 2 * slotFun n σ Λ z θ)
          (g := fun θ => 3 * (slotFun n σ G z θ + slotFun n σ F z θ
            + α ^ 4 * slotFun n σ Φ z θ))
          (ae_restrict_of_forall_mem hθmeas fun θ hθ => mul_nonneg (sq_nonneg _) (hAL θ hθ))
          hdom2 (ae_restrict_of_forall_mem hθmeas hII)
      have hlhs : (∫ θ in Work.Spaces.Iθ, (α * (5 + α)) ^ 2 * slotFun n σ Λ z θ)
          = (α * (5 + α)) ^ 2 * slot n σ Λ z := by
        rw [MeasureTheory.integral_const_mul]
        simp only [slot]
      have hc3 : (∫ θ in Work.Spaces.Iθ, 3 * (slotFun n σ G z θ + slotFun n σ F z θ
            + α ^ 4 * slotFun n σ Φ z θ))
          = 3 * (∫ θ in Work.Spaces.Iθ, (slotFun n σ G z θ + slotFun n σ F z θ
            + α ^ 4 * slotFun n σ Φ z θ)) :=
        MeasureTheory.integral_const_mul 3 _
      have hGF : (∫ θ in Work.Spaces.Iθ, slotFun n σ G z θ + slotFun n σ F z θ)
          = (∫ θ in Work.Spaces.Iθ, slotFun n σ G z θ)
            + (∫ θ in Work.Spaces.Iθ, slotFun n σ F z θ) :=
        MeasureTheory.integral_add hGint hFint
      have hGFP : (∫ θ in Work.Spaces.Iθ, slotFun n σ G z θ + slotFun n σ F z θ
            + α ^ 4 * slotFun n σ Φ z θ)
          = (∫ θ in Work.Spaces.Iθ, slotFun n σ G z θ + slotFun n σ F z θ)
            + (∫ θ in Work.Spaces.Iθ, α ^ 4 * slotFun n σ Φ z θ) :=
        MeasureTheory.integral_add (hGint.add hFint) (hPint.const_mul (α ^ 4))
      have hP4 : (∫ θ in Work.Spaces.Iθ, α ^ 4 * slotFun n σ Φ z θ)
          = α ^ 4 * slot n σ Φ z := by
        rw [MeasureTheory.integral_const_mul]; simp only [slot]
      have hG3 : (∫ θ in Work.Spaces.Iθ, slotFun n σ G z θ) = slot n σ G z := rfl
      have hF3 : (∫ θ in Work.Spaces.Iθ, slotFun n σ F z θ) = slot n σ F z := rfl
      have hrhs2 : (∫ θ in Work.Spaces.Iθ, 3 * (slotFun n σ G z θ + slotFun n σ F z θ
            + α ^ 4 * slotFun n σ Φ z θ))
          = 3 * (slot n σ G z + slot n σ F z + α ^ 4 * slot n σ Φ z) := by
        linarith [hc3, hGFP, hGF, hP4, hG3, hF3]
      rw [hlhs, hrhs2] at hmono
      exact hmono
  · have hLz : slot n σ Λ z = 0 := by
      rw [slot]
      exact MeasureTheory.integral_undef hLint
    have hGz : slot n σ G z = 0 := by
      rw [slot]
      refine MeasureTheory.integral_undef ?_
      intro hGint
      exact hLint (Integrable.mono'
        (f := slotFun n σ Λ z)
        (g := fun θ => (3 / (α * (5 + α)) ^ 2) * (slotFun n σ G z θ + slotFun n σ F z θ
          + α ^ 4 * slotFun n σ Φ z θ))
        (((hGint.add hFint).add (hPint.const_mul (α ^ 4))).const_mul _) hLaesm
        (ae_restrict_of_forall_mem hθmeas fun θ hθ => by
          rw [Real.norm_of_nonneg (hAL θ hθ)]
          rw [div_mul_eq_mul_div, le_div_iff₀ hc]
          nlinarith [hII θ hθ]))
    constructor
    · rw [hGz, hLz]
      have h1 : 0 ≤ slot n σ F z := slot_nonneg hσnn F z
      have h2 : 0 ≤ slot n σ Φ z := slot_nonneg hσnn Φ z
      have h3 : 0 ≤ α ^ 4 * slot n σ Φ z := mul_nonneg (by positivity) h2
      nlinarith [h1, h3, sq_nonneg α, sq_nonneg (α ^ 2), sq_nonneg (5 + α)]
    · rw [hGz, hLz]
      have h1 : 0 ≤ slot n σ F z := slot_nonneg hσnn F z
      have h2 : 0 ≤ slot n σ Φ z := slot_nonneg hσnn Φ z
      have h3 : 0 ≤ α ^ 4 * slot n σ Φ z := mul_nonneg (by positivity) h2
      nlinarith [h1, h3, sq_nonneg α, sq_nonneg (α ^ 2), sq_nonneg (5 + α)]

/-! ## The `z`-level assembly -/

/-- **The core bound.**  Given the two pointwise comparison inequalities, the `θ`-integrability
of the `F`- and `Φ`-slots, the a.e. measurability of the `Λ`- and `G`-slots and the four
integrated bounds, the `G`-slot is bounded by `(3C₁ + 9D)|F|²`. -/
private theorem slotBound_core (n : ℕ) (σ : ℝ → ℝ) (F Φ Λ G : ℝ → ℝ → ℝ)
    (α C₁ D : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hC₁ : 0 < C₁) (hD : 0 < D)
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (hI : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, slotFun n σ G z θ
      ≤ 3 * slotFun n σ F z θ + 3 * α ^ 4 * slotFun n σ Φ z θ
        + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun n σ Λ z θ)
    (hII : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (α * (5 + α)) ^ 2 * slotFun n σ Λ z θ
        ≤ 3 * (slotFun n σ G z θ + slotFun n σ F z θ + α ^ 4 * slotFun n σ Φ z θ))
    (hFint : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (slotFun n σ F z) Work.Spaces.Iθ)
    (hPint : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (slotFun n σ Φ z) Work.Spaces.Iθ)
    (hLaesm : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (slotFun n σ Λ z) (volume.restrict Work.Spaces.Iθ))
    (hGaesm : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (slotFun n σ G z) (volume.restrict Work.Spaces.Iθ))
    (hCaesm : AEStronglyMeasurable (slot n σ Λ) (volume.restrict Work.Spaces.Iz))
    (hFintz : IntegrableOn (slot n σ F) Work.Spaces.Iz)
    (hPintz : IntegrableOn (slot n σ Φ) Work.Spaces.Iz)
    (hFbd : ∫ z in Work.Spaces.Iz, slot n σ F z ≤ C₁ * Work.Spaces.HkSq α 2 F)
    (hPbd : ∫ z in Work.Spaces.Iz, slot n σ Φ z ≤ D * Work.Spaces.HkSq α 2 F)
    (hLbd : ∫ z in Work.Spaces.Iz, slot n σ Λ z ≤ D * Work.Spaces.HkSq α 2 F) :
    ∫ z in Work.Spaces.Iz, slot n σ G z ≤ (3 * C₁ + 9 * D) * Work.Spaces.HkSq α 2 F := by
  have hzmeas : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hHK : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hpt : ∀ z ∈ Work.Spaces.Iz, slot n σ G z
      ≤ 3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z + 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z :=
    fun z hz => (slot_dichotomy n σ F Φ Λ G α z hα hσnn (hI z hz) (hII z hz)
      (hFint z hz) (hPint z hz) (hLaesm z hz) (hGaesm z hz)).1
  have hpt2 : ∀ z ∈ Work.Spaces.Iz, (α * (5 + α)) ^ 2 * slot n σ Λ z
      ≤ 3 * (slot n σ G z + slot n σ F z + α ^ 4 * slot n σ Φ z) :=
    fun z hz => (slot_dichotomy n σ F Φ Λ G α z hα hσnn (hI z hz) (hII z hz)
      (hFint z hz) (hPint z hz) (hLaesm z hz) (hGaesm z hz)).2
  by_cases hLintz : IntegrableOn (slot n σ Λ) Work.Spaces.Iz
  · have hdom : IntegrableOn (fun z => 3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z
        + 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z) Work.Spaces.Iz :=
      ((hFintz.const_mul 3).add (hPintz.const_mul (3 * α ^ 4))).add
        (hLintz.const_mul _)
    have hmono : (∫ z in Work.Spaces.Iz, slot n σ G z)
        ≤ (∫ z in Work.Spaces.Iz, (3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z
            + 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z)) :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := volume.restrict Work.Spaces.Iz)
        (f := slot n σ G)
        (g := fun z => 3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z
          + 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z)
        (ae_restrict_of_forall_mem hzmeas fun z _ => slot_nonneg hσnn G z) hdom
        (ae_restrict_of_forall_mem hzmeas hpt)
    have hA : (∫ z in Work.Spaces.Iz, 3 * slot n σ F z)
        = 3 * (∫ z in Work.Spaces.Iz, slot n σ F z) :=
      MeasureTheory.integral_const_mul 3 _
    have hB : (∫ z in Work.Spaces.Iz, 3 * α ^ 4 * slot n σ Φ z)
        = 3 * α ^ 4 * (∫ z in Work.Spaces.Iz, slot n σ Φ z) :=
      MeasureTheory.integral_const_mul _ _
    have hC : (∫ z in Work.Spaces.Iz, 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z)
        = 3 * α ^ 2 * (5 + α) ^ 2 * (∫ z in Work.Spaces.Iz, slot n σ Λ z) :=
      MeasureTheory.integral_const_mul _ _
    have hAB : (∫ z in Work.Spaces.Iz, 3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z)
        = (∫ z in Work.Spaces.Iz, 3 * slot n σ F z)
          + (∫ z in Work.Spaces.Iz, 3 * α ^ 4 * slot n σ Φ z) :=
      MeasureTheory.integral_add (hFintz.const_mul 3) (hPintz.const_mul (3 * α ^ 4))
    have htot : (∫ z in Work.Spaces.Iz, 3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z
          + 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z)
        = (∫ z in Work.Spaces.Iz, 3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z)
          + (∫ z in Work.Spaces.Iz, 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z) :=
      MeasureTheory.integral_add ((hFintz.const_mul 3).add (hPintz.const_mul (3 * α ^ 4)))
        (hLintz.const_mul (3 * α ^ 2 * (5 + α) ^ 2))
    have hrhs : (∫ z in Work.Spaces.Iz, (3 * slot n σ F z + 3 * α ^ 4 * slot n σ Φ z
          + 3 * α ^ 2 * (5 + α) ^ 2 * slot n σ Λ z))
        = 3 * (∫ z in Work.Spaces.Iz, slot n σ F z)
          + 3 * α ^ 4 * (∫ z in Work.Spaces.Iz, slot n σ Φ z)
          + 3 * α ^ 2 * (5 + α) ^ 2 * (∫ z in Work.Spaces.Iz, slot n σ Λ z) := by
      linarith [hA, hB, hC, hAB, htot]
    rw [hrhs] at hmono
    have h1 : 3 * (∫ z in Work.Spaces.Iz, slot n σ F z)
        ≤ 3 * (C₁ * Work.Spaces.HkSq α 2 F) := by linarith [hFbd]
    have h2 : 3 * α ^ 4 * (∫ z in Work.Spaces.Iz, slot n σ Φ z)
        ≤ 3 * α ^ 4 * (D * Work.Spaces.HkSq α 2 F) :=
      mul_le_mul_of_nonneg_left hPbd (by positivity)
    have h3 : 3 * α ^ 2 * (5 + α) ^ 2 * (∫ z in Work.Spaces.Iz, slot n σ Λ z)
        ≤ 3 * α ^ 2 * (5 + α) ^ 2 * (D * Work.Spaces.HkSq α 2 F) :=
      mul_le_mul_of_nonneg_left hLbd (by positivity)
    have h4 : α ^ 4 ≤ 1 := pow_le_one₀ (n := 4) hα.le (by linarith)
    have h5a : α ^ 2 ≤ 1 / 16 := by nlinarith [hα.le, hα4]
    have h5b : (5 + α) ^ 2 ≤ (21 / 4) ^ 2 := by nlinarith [hα.le, hα4]
    have h5 : α ^ 2 * (5 + α) ^ 2 ≤ 2 := by
      have := mul_le_mul h5a h5b (by positivity) (by norm_num)
      linarith
    have hDH : 0 ≤ D * Work.Spaces.HkSq α 2 F := mul_nonneg hD.le hHK
    have h4' := mul_le_mul_of_nonneg_right h4 hDH
    have h5' := mul_le_mul_of_nonneg_right h5 hDH
    have harith : 3 * (C₁ * Work.Spaces.HkSq α 2 F)
          + 3 * α ^ 4 * (D * Work.Spaces.HkSq α 2 F)
          + 3 * α ^ 2 * (5 + α) ^ 2 * (D * Work.Spaces.HkSq α 2 F)
        ≤ (3 * C₁ + 9 * D) * Work.Spaces.HkSq α 2 F := by
      nlinarith [hHK]
    linarith [hmono, h1, h2, h3, harith]
  · have hGintz : ¬ IntegrableOn (slot n σ G) Work.Spaces.Iz := by
      intro hGint
      refine hLintz (Integrable.mono'
        (f := slot n σ Λ)
        (g := fun z => (3 / (α * (5 + α)) ^ 2) * (slot n σ G z + slot n σ F z
          + α ^ 4 * slot n σ Φ z))
        (((hGint.add hFintz).add (hPintz.const_mul (α ^ 4))).const_mul _) hCaesm ?_)
      refine ae_restrict_of_forall_mem hzmeas fun z hz => ?_
      rw [Real.norm_of_nonneg (slot_nonneg hσnn Λ z)]
      have hcz : 0 < (α * (5 + α)) ^ 2 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hcz]
      nlinarith [hpt2 z hz]
    rw [MeasureTheory.integral_undef hGintz]
    have : 0 < 3 * C₁ + 9 * D := by linarith
    exact mul_nonneg this.le hHK

/-- The `Iθ`-slot `slot n σ X z` is the integral of `slotFun`. -/
private lemma slot_eq_integral (n : ℕ) (σ : ℝ → ℝ) (X : ℝ → ℝ → ℝ) (z : ℝ) :
    slot n σ X z = ∫ θ in Work.Spaces.Iθ, slotFun n σ X z θ := rfl


/-! ## Converting the slot form into the statement form -/

private lemma setIntegral_slot_eq (n : ℕ) (σ : ℝ → ℝ) (X : ℝ → ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, slot n σ X z)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter n X z θ) ^ 2 * σ θ) := by
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have h : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * ((Work.Spaces.pthIter n X z θ) ^ 2 * σ θ))
      = (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter n X z θ) ^ 2 * σ θ) :=
    MeasureTheory.integral_const_mul _ _
  simpa only [slot, slotFun] using h

/-! ## The pointwise comparison inequalities at the two levels -/
private lemma cmp_one {α γ : ℝ} (hγ2 : γ ≤ 3 / 2) {F Ψ : ℝ → ℝ → ℝ}
    (hFso : Work.FTS.EllipticEst.SmoothOpen F) (hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        slotFun 1 (sig2 γ) (Gsrc α F Ψ) z θ
          ≤ 3 * slotFun 1 (sig2 γ) F z θ
            + 3 * α ^ 4 * slotFun 1 (sig2 γ)
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun 1 (sig2 γ)
                (Work.Spaces.DzIter 1 Ψ) z θ)
      ∧ (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (α * (5 + α)) ^ 2 * slotFun 1 (sig2 γ) (Work.Spaces.DzIter 1 Ψ) z θ
          ≤ 3 * (slotFun 1 (sig2 γ) (Gsrc α F Ψ) z θ + slotFun 1 (sig2 γ) F z θ
            + α ^ 4 * slotFun 1 (sig2 γ)
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)) := by
  constructor
  · intro z hz θ hθ
    rcases lt_or_eq_of_le (Set.mem_Ici.mp hz) with hzpos | hz0
    · rcases lt_or_eq_of_le hθ.1 with hθpos | hθ0
      · rcases lt_or_eq_of_le hθ.2 with hθlt | hθtop
        · have hid := Work.FTS.EllipticEst.SrcBnd.GsrcPthOne (α := α) hFso hΨso z θ hzpos ⟨hθpos, hθlt⟩
          have hfac : 0 ≤ (Work.Spaces.w z) ^ 2 * sig2 γ θ :=
            mul_nonneg (sq_nonneg _) (sig2_nonneg_of_mem_Iθ hθ)
          have hbase : (Work.Spaces.pthIter 1 (Gsrc α F Ψ) z θ) ^ 2
              ≤ 3 * (Work.Spaces.pthIter 1 F z θ) ^ 2
                + 3 * α ^ 4 * (Work.Spaces.pthIter 1
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
                + 3 * α ^ 2 * (5 + α) ^ 2
                    * (Work.Spaces.pthIter 1 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 := by
            rw [hid]
            exact sq_three_le _ _ _ α
          calc slotFun 1 (sig2 γ) (Gsrc α F Ψ) z θ
              = ((Work.Spaces.w z) ^ 2 * sig2 γ θ)
                  * (Work.Spaces.pthIter 1 (Gsrc α F Ψ) z θ) ^ 2 := by
                simp only [slotFun]; ring
            _ ≤ ((Work.Spaces.w z) ^ 2 * sig2 γ θ)
                  * (3 * (Work.Spaces.pthIter 1 F z θ) ^ 2
                    + 3 * α ^ 4 * (Work.Spaces.pthIter 1
                        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
                    + 3 * α ^ 2 * (5 + α) ^ 2
                        * (Work.Spaces.pthIter 1 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hbase hfac
            _ = 3 * slotFun 1 (sig2 γ) F z θ
                  + 3 * α ^ 4 * slotFun 1 (sig2 γ)
                      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                  + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun 1 (sig2 γ)
                      (Work.Spaces.DzIter 1 Ψ) z θ := by
                simp only [slotFun]; ring
        · rw [hθtop]
          have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 1 (sig2 γ) X z (Real.pi / 2) = 0 :=
            fun X => slotFun_eq_zero_of_right X (sig2_zero_right hγ2)
          simp only [hz1]
          norm_num
      · rw [hθ0.symm]
        have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 1 (sig2 γ) X z 0 = 0 :=
          fun X => slotFun_eq_zero_of_right X (sig2_zero_left hγ2)
        simp only [hz1]
        norm_num
    · rw [hz0.symm]
      have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 1 (sig2 γ) X 0 θ = 0 :=
        fun X => slotFun_eq_zero_of_left X w_zero_sq
      simp only [hz1]
      norm_num
  · intro z hz θ hθ
    rcases lt_or_eq_of_le (Set.mem_Ici.mp hz) with hzpos | hz0
    · rcases lt_or_eq_of_le hθ.1 with hθpos | hθ0
      · rcases lt_or_eq_of_le hθ.2 with hθlt | hθtop
        · have hid := Work.FTS.EllipticEst.SrcBnd.GsrcPthOne (α := α) hFso hΨso z θ hzpos ⟨hθpos, hθlt⟩
          have hfac : 0 ≤ (Work.Spaces.w z) ^ 2 * sig2 γ θ :=
            mul_nonneg (sq_nonneg _) (sig2_nonneg_of_mem_Iθ hθ)
          have hbase := sq_rev_le (Work.Spaces.pthIter 1 (Gsrc α F Ψ) z θ)
            (Work.Spaces.pthIter 1 F z θ)
            (Work.Spaces.pthIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
            (Work.Spaces.pthIter 1 (Work.Spaces.DzIter 1 Ψ) z θ) α hid
          calc (α * (5 + α)) ^ 2 * slotFun 1 (sig2 γ) (Work.Spaces.DzIter 1 Ψ) z θ
              = ((Work.Spaces.w z) ^ 2 * sig2 γ θ)
                  * ((α * (5 + α)) ^ 2
                    * (Work.Spaces.pthIter 1 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) := by
                simp only [slotFun]; ring
            _ ≤ ((Work.Spaces.w z) ^ 2 * sig2 γ θ)
                  * (3 * ((Work.Spaces.pthIter 1 (Gsrc α F Ψ) z θ) ^ 2
                    + (Work.Spaces.pthIter 1 F z θ) ^ 2
                    + α ^ 4 * (Work.Spaces.pthIter 1
                        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2)) :=
                mul_le_mul_of_nonneg_left hbase hfac
            _ = 3 * (slotFun 1 (sig2 γ) (Gsrc α F Ψ) z θ + slotFun 1 (sig2 γ) F z θ
                  + α ^ 4 * slotFun 1 (sig2 γ)
                      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) := by
                simp only [slotFun]; ring
        · rw [hθtop]
          have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 1 (sig2 γ) X z (Real.pi / 2) = 0 :=
            fun X => slotFun_eq_zero_of_right X (sig2_zero_right hγ2)
          simp only [hz1]
          norm_num
      · rw [hθ0.symm]
        have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 1 (sig2 γ) X z 0 = 0 :=
          fun X => slotFun_eq_zero_of_right X (sig2_zero_left hγ2)
        simp only [hz1]
        norm_num
    · rw [hz0.symm]
      have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 1 (sig2 γ) X 0 θ = 0 :=
        fun X => slotFun_eq_zero_of_left X w_zero_sq
      simp only [hz1]
      norm_num

/-! ## The two-dimensional statement -/

private lemma cmp_two {α γ : ℝ} (hγ2 : γ ≤ 3 / 2) {F Ψ : ℝ → ℝ → ℝ}
    (hFso : Work.FTS.EllipticEst.SmoothOpen F) (hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        slotFun 2 (sig4 γ) (Gsrc α F Ψ) z θ
          ≤ 3 * slotFun 2 (sig4 γ) F z θ
            + 3 * α ^ 4 * slotFun 2 (sig4 γ)
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun 2 (sig4 γ)
                (Work.Spaces.DzIter 1 Ψ) z θ)
      ∧ (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (α * (5 + α)) ^ 2 * slotFun 2 (sig4 γ) (Work.Spaces.DzIter 1 Ψ) z θ
          ≤ 3 * (slotFun 2 (sig4 γ) (Gsrc α F Ψ) z θ + slotFun 2 (sig4 γ) F z θ
            + α ^ 4 * slotFun 2 (sig4 γ)
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)) := by
  constructor
  · intro z hz θ hθ
    rcases lt_or_eq_of_le (Set.mem_Ici.mp hz) with hzpos | hz0
    · rcases lt_or_eq_of_le hθ.1 with hθpos | hθ0
      · rcases lt_or_eq_of_le hθ.2 with hθlt | hθtop
        · have hid := Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo (α := α) hFso hΨso z θ hzpos ⟨hθpos, hθlt⟩
          have hfac : 0 ≤ (Work.Spaces.w z) ^ 2 * sig4 γ θ :=
            mul_nonneg (sq_nonneg _) (sig4_nonneg_of_mem_Iθ hθ)
          have hbase : (Work.Spaces.pthIter 2 (Gsrc α F Ψ) z θ) ^ 2
              ≤ 3 * (Work.Spaces.pthIter 2 F z θ) ^ 2
                + 3 * α ^ 4 * (Work.Spaces.pthIter 2
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
                + 3 * α ^ 2 * (5 + α) ^ 2
                    * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 := by
            rw [hid]
            exact sq_three_le _ _ _ α
          calc slotFun 2 (sig4 γ) (Gsrc α F Ψ) z θ
              = ((Work.Spaces.w z) ^ 2 * sig4 γ θ)
                  * (Work.Spaces.pthIter 2 (Gsrc α F Ψ) z θ) ^ 2 := by
                simp only [slotFun]; ring
            _ ≤ ((Work.Spaces.w z) ^ 2 * sig4 γ θ)
                  * (3 * (Work.Spaces.pthIter 2 F z θ) ^ 2
                    + 3 * α ^ 4 * (Work.Spaces.pthIter 2
                        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
                    + 3 * α ^ 2 * (5 + α) ^ 2
                        * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hbase hfac
            _ = 3 * slotFun 2 (sig4 γ) F z θ
                  + 3 * α ^ 4 * slotFun 2 (sig4 γ)
                      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
                  + 3 * α ^ 2 * (5 + α) ^ 2 * slotFun 2 (sig4 γ)
                      (Work.Spaces.DzIter 1 Ψ) z θ := by
                simp only [slotFun]; ring
        · rw [hθtop]
          have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 2 (sig4 γ) X z (Real.pi / 2) = 0 :=
            fun X => slotFun_eq_zero_of_right X (sig4_zero_right hγ2)
          simp only [hz1]
          norm_num
      · rw [hθ0.symm]
        have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 2 (sig4 γ) X z 0 = 0 :=
          fun X => slotFun_eq_zero_of_right X (sig4_zero_left hγ2)
        simp only [hz1]
        norm_num
    · rw [hz0.symm]
      have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 2 (sig4 γ) X 0 θ = 0 :=
        fun X => slotFun_eq_zero_of_left X w_zero_sq
      simp only [hz1]
      norm_num
  · intro z hz θ hθ
    rcases lt_or_eq_of_le (Set.mem_Ici.mp hz) with hzpos | hz0
    · rcases lt_or_eq_of_le hθ.1 with hθpos | hθ0
      · rcases lt_or_eq_of_le hθ.2 with hθlt | hθtop
        · have hid := Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo (α := α) hFso hΨso z θ hzpos ⟨hθpos, hθlt⟩
          have hfac : 0 ≤ (Work.Spaces.w z) ^ 2 * sig4 γ θ :=
            mul_nonneg (sq_nonneg _) (sig4_nonneg_of_mem_Iθ hθ)
          have hbase := sq_rev_le (Work.Spaces.pthIter 2 (Gsrc α F Ψ) z θ)
            (Work.Spaces.pthIter 2 F z θ)
            (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) α hid
          calc (α * (5 + α)) ^ 2 * slotFun 2 (sig4 γ) (Work.Spaces.DzIter 1 Ψ) z θ
              = ((Work.Spaces.w z) ^ 2 * sig4 γ θ)
                  * ((α * (5 + α)) ^ 2
                    * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) := by
                simp only [slotFun]; ring
            _ ≤ ((Work.Spaces.w z) ^ 2 * sig4 γ θ)
                  * (3 * ((Work.Spaces.pthIter 2 (Gsrc α F Ψ) z θ) ^ 2
                    + (Work.Spaces.pthIter 2 F z θ) ^ 2
                    + α ^ 4 * (Work.Spaces.pthIter 2
                        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2)) :=
                mul_le_mul_of_nonneg_left hbase hfac
            _ = 3 * (slotFun 2 (sig4 γ) (Gsrc α F Ψ) z θ + slotFun 2 (sig4 γ) F z θ
                  + α ^ 4 * slotFun 2 (sig4 γ)
                      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) := by
                simp only [slotFun]; ring
        · rw [hθtop]
          have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 2 (sig4 γ) X z (Real.pi / 2) = 0 :=
            fun X => slotFun_eq_zero_of_right X (sig4_zero_right hγ2)
          simp only [hz1]
          norm_num
      · rw [hθ0.symm]
        have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 2 (sig4 γ) X z 0 = 0 :=
          fun X => slotFun_eq_zero_of_right X (sig4_zero_left hγ2)
        simp only [hz1]
        norm_num
    · rw [hz0.symm]
      have hz1 : ∀ X : ℝ → ℝ → ℝ, slotFun 2 (sig4 γ) X 0 θ = 0 :=
        fun X => slotFun_eq_zero_of_left X w_zero_sq
      simp only [hz1]
      norm_num

/-! ## The two-dimensional statement -/

theorem SourceBoundsTwoD (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      γ ≤ Work.Spaces.gam α →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * Work.FTS.EllipticEst.Mine.sig4 γ θ)) ≤ D * Work.Spaces.HkSq α 2 F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * Work.FTS.EllipticEst.Mine.sig2 γ θ)) ≤ D * Work.Spaces.HkSq α 2 F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 1 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.Mine.sig2 γ θ)) ≤ D * Work.Spaces.HkSq α 2 F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.Mine.sig4 γ θ)) ≤ D * Work.Spaces.HkSq α 2 F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 1 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.Mine.sig2 γ θ)
        ≤ C * Work.Spaces.HkSq α 2 F)
      ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
              * Work.FTS.EllipticEst.Mine.sig4 γ θ)
        ≤ C * Work.Spaces.HkSq α 2 F) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := FSlotsTwoD γ hγ1 hγ2
  refine ⟨3 * C₁ + 9 * D, by linarith, ?_⟩
  intro α F Ψ hα hα4 hγg hweak h1 h2 h3 h4
  -- smoothness of the four data
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hweak.smooth
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨso)
      (fun z θ hz hθ hθ' => hweak.eq z hz θ hθ hθ')
  have hΦso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl (hΨso.pzIter 2)
    simpa using h
  have hΛso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) := hΨso.DzIter 1
  have hZpso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) := by
    have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hΨso.pz
    simpa using h
  have hGso : Work.FTS.EllipticEst.SmoothOpen (Gsrc α F Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl hFso
          (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hΦso))
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α)) hZpso))
      (fun z θ _ _ _ => by simp only [Gsrc])
  -- the two weights
  have hσ2nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ sig2 γ θ := fun θ hθ => sig2_nonneg_of_mem_Iθ hθ
  have hσ4nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ sig4 γ θ := fun θ hθ => sig4_nonneg_of_mem_Iθ hθ
  have hσ2c := sig2_continuousOn γ
  have hσ4c := sig4_continuousOn γ
  -- the pointwise comparisons
  have hcmp1 := cmp_one (α := α) (γ := γ) hγ2 hFso hΨso
  have hcmp2 := cmp_two (α := α) (γ := γ) hγ2 hFso hΨso
  -- the pointwise domination by the `H²`-integrand
  have hbF1 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 1 F z θ) ^ 2 * sig2 γ θ)
        ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 2 F z θ := by
    intro z _ θ hθ
    simpa using sig2_slot_pointwise α hα γ hγ2 hγg F z θ hθ
  have hbP1 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 1
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 * sig2 γ θ)
        ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
    intro z _ θ hθ
    simpa using sig2_slot_pointwise α hα γ hγ2 hγg
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ hθ
  have hbF2 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 * sig4 γ θ)
        ≤ (10 : ℝ) * Work.Spaces.HkIntegrand α 2 F z θ := by
    intro z _ θ hθ
    change (Work.Spaces.w z) ^ 2
      * ((deriv (fun t => Work.Spaces.pth F z t) θ) ^ 2 * sig4 γ θ)
      ≤ (10 : ℝ) * Work.Spaces.HkIntegrand α 2 F z θ
    exact sig4_slot_pointwise α hα γ hγ2 hγg F z θ hθ
  have hbP2 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 * sig4 γ θ)
        ≤ (10 : ℝ) * Work.Spaces.HkIntegrand α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
    intro z _ θ hθ
    change (Work.Spaces.w z) ^ 2
      * ((deriv (fun t => Work.Spaces.pth (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z t) θ) ^ 2
          * sig4 γ θ)
      ≤ (10 : ℝ) * Work.Spaces.HkIntegrand α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
    exact sig4_slot_pointwise α hα γ hγ2 hγg
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ hθ
  -- the slot integrability packages
  have hFI1 := Work.FTS.EllipticEst.SrcBnd.SlotIntegrable (α := α) (f := F) (σ := sig2 γ) (C := 1) 1
    hFso hσ2c hσ2nn hweak.memF (by norm_num) hbF1
  have hPI1 := Work.FTS.EllipticEst.SrcBnd.SlotIntegrable (α := α) (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    (σ := sig2 γ) (C := 1) 1 hΦso hσ2c hσ2nn hweak.memA (by norm_num) hbP1
  have hFI2 := Work.FTS.EllipticEst.SrcBnd.SlotIntegrable (α := α) (f := F) (σ := sig4 γ) (C := 10) 2
    hFso hσ4c hσ4nn hweak.memF (by norm_num) hbF2
  have hPI2 := Work.FTS.EllipticEst.SrcBnd.SlotIntegrable (α := α) (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
    (σ := sig4 γ) (C := 10) 2 hΦso hσ4c hσ4nn hweak.memA (by norm_num) hbP2
  -- the four hypotheses in slot form
  have hb1 : (∫ z in Work.Spaces.Iz, slot 2 (sig4 γ)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ≤ D * Work.Spaces.HkSq α 2 F := by
    rw [setIntegral_slot_eq]; exact h1
  have hb2 : (∫ z in Work.Spaces.Iz, slot 1 (sig2 γ)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ≤ D * Work.Spaces.HkSq α 2 F := by
    rw [setIntegral_slot_eq]; exact h2
  have hb3 : (∫ z in Work.Spaces.Iz, slot 1 (sig2 γ) (Work.Spaces.DzIter 1 Ψ) z)
        ≤ D * Work.Spaces.HkSq α 2 F := by
    rw [setIntegral_slot_eq]; exact h3
  have hb4 : (∫ z in Work.Spaces.Iz, slot 2 (sig4 γ) (Work.Spaces.DzIter 1 Ψ) z)
        ≤ D * Work.Spaces.HkSq α 2 F := by
    rw [setIntegral_slot_eq]; exact h4
  -- the two `F`-slot bounds, split off from `FSlotsTwoD`
  have hbF : (∫ z in Work.Spaces.Iz, slot 2 (sig4 γ) F z) ≤ C₁ * Work.Spaces.HkSq α 2 F
      ∧ (∫ z in Work.Spaces.Iz, slot 1 (sig2 γ) F z) ≤ C₁ * Work.Spaces.HkSq α 2 F := by
    have hsum := hC₁ α F hα hγg hweak.memF
    have e1 := setIntegral_slot_eq 2 (sig4 γ) F
    have e2 := setIntegral_slot_eq 1 (sig2 γ) F
    have hnn1 : 0 ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 F z θ) ^ 2 * sig4 γ θ) := by
      refine integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ici fun z _ => ?_)
      refine mul_nonneg (sq_nonneg _)
        (integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_))
      exact mul_nonneg (sq_nonneg _) (sig4_nonneg_of_mem_Iθ hθ)
    have hnn2 : 0 ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 F z θ) ^ 2 * sig2 γ θ) := by
      refine integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ici fun z _ => ?_)
      refine mul_nonneg (sq_nonneg _)
        (integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_))
      exact mul_nonneg (sq_nonneg _) (sig2_nonneg_of_mem_Iθ hθ)
    constructor
    · rw [e1]; linarith [hsum, hnn2]
    · rw [e2]; linarith [hsum, hnn1]
  -- the two cores
  have hG1 : (∫ z in Work.Spaces.Iz, slot 1 (sig2 γ) (Gsrc α F Ψ) z)
      ≤ (3 * C₁ + 9 * D) * Work.Spaces.HkSq α 2 F :=
    slotBound_core 1 (sig2 γ) F (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.DzIter 1 Ψ) (Gsrc α F Ψ) α C₁ D hα hα4 hC₁pos hD hσ2nn
      hcmp1.1 hcmp1.2 (fun z hz => hFI1.1 z hz) (fun z hz => hPI1.1 z hz)
      (fun z hz => (Work.FTS.EllipticEst.SrcBnd.SlotAESM 1 hΛso hσ2c).1 z hz)
      (fun z hz => (Work.FTS.EllipticEst.SrcBnd.SlotAESM 1 hGso hσ2c).1 z hz)
      (Work.FTS.EllipticEst.SrcBnd.SlotAESM 1 hΛso hσ2c).2 hFI1.2 hPI1.2 hbF.2 hb2 hb3
  have hG2 : (∫ z in Work.Spaces.Iz, slot 2 (sig4 γ) (Gsrc α F Ψ) z)
      ≤ (3 * C₁ + 9 * D) * Work.Spaces.HkSq α 2 F :=
    slotBound_core 2 (sig4 γ) F (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.DzIter 1 Ψ) (Gsrc α F Ψ) α C₁ D hα hα4 hC₁pos hD hσ4nn
      hcmp2.1 hcmp2.2 (fun z hz => hFI2.1 z hz) (fun z hz => hPI2.1 z hz)
      (fun z hz => (Work.FTS.EllipticEst.SrcBnd.SlotAESM 2 hΛso hσ4c).1 z hz)
      (fun z hz => (Work.FTS.EllipticEst.SrcBnd.SlotAESM 2 hGso hσ4c).1 z hz)
      (Work.FTS.EllipticEst.SrcBnd.SlotAESM 2 hΛso hσ4c).2 hFI2.2 hPI2.2 hbF.1 hb1 hb4
  constructor
  · rw [← setIntegral_slot_eq 1 (sig2 γ) (Gsrc α F Ψ)]
    exact hG1
  · rw [← setIntegral_slot_eq 2 (sig4 γ) (Gsrc α F Ψ)]
    exact hG2

end Work.FTS.EllipticEst.Mine
