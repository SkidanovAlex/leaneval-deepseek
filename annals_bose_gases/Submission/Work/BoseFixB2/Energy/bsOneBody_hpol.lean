import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BoseFixB2.Polar.additive_bddAbove_continuous
import Submission.Work.BoseFixB2.Polar.polarForm_add
import Submission.Work.BoseKinLoc.Word.bsOneBody_const_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.bsOneBody_hpol`

The one-body big-box kinetic form `Work.BSKinetic.bsOneBody ℓ (fsKinCoeff c) u`
is a genuine **quadratic form** of the state, so it is *homogeneously polarised*:

`bsOneBody (t·f + g) − bsOneBody (t·f − g) = t · (bsOneBody (f + g) − bsOneBody (f − g))`.

## The route

On a state space where `Q` satisfies the parallelogram law, is `2`-homogeneous and
nonnegative, the identity is **not** a purely algebraic consequence of the first two
properties: the defect `t ↦ (Q (t • x + y) − Q (t • x − y)) − t (Q (x + y) − Q (x − y))`
is then an arbitrary derivation of `ℝ` (see `Work.BoseFixB2.Polar.par_polarisation`,
which is *false* as written).  Nonnegativity rules the defect out: writing
`A s = (Q (s • x + y) − Q (s • x − y)) / 4`, additivity of `A` (from the parallelogram
law, `Work.BoseFixB2.Polar.polarForm_add`) together with nonnegativity of the two
values `Q (s • x ± y)` bounds `|A s| ≤ (s ^ 2 * Q x + Q y) / 2`, hence `A` is continuous
(`Work.BoseFixB2.Polar.additive_bddAbove_continuous`), hence `ℝ`-linear.  This is the
abstract lemma `hpol_par_hom_nonneg` of §1.

The state space can not be *all* functions: the parallelogram law for `bsOneBody` is only
available for `C^∞` states (`bsOneBody_parallelogram_local`, §2).  So the abstract lemma
is applied on the `ℝ`-submodule `SmoothFn` of smooth functions (§3), where

* the parallelogram law is `bsOneBody_parallelogram_local`,
* `2`-homogeneity is `Work.BoseKinLoc.Word.bsOneBody_const_mul`,
* nonnegativity is `Work.BSKinetic.bsOneBody_nonneg` (with `fsKinCoeff_nonneg`).

## The parallelogram law (§2)

`bsOneBody` is reduced to the *shifted, anchored* form
`bsOneBody ℓ F u ψ = (2π)⁻³ · bsW F (bsShift ℓ ψ u)` (`Work.BSKinetic.Decomp.bsOneBody_eq_bsW_shift`,
where `bsW F h = ∫_p F(‖p‖)·‖bsPsi h p‖²`).  On the shifted states `bsShift ℓ ψ u` (smooth,
compactly supported, `Work.BSKinetic.Decomp.{contDiff_bsShift,hasCompactSupport_bsShift}`) the
map `ψ ↦ bsShift ℓ ψ u` is `ℝ`-linear and `bsPsi` is additive
(`Work.BSKinetic.Decomp.bsPsi_sub`, and `bsPsi_add` below), so the parallelogram law is the
pointwise parallelogram law for the complex norms, integrated against the integrable weight
`Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq`.
-/

noncomputable section

open scoped Topology
open MeasureTheory Filter

namespace Work.BoseFixB2.Energy

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The abstract lemma: nonnegative quadratic forms are homogeneously polarised -/

/-- **An additive continuous function `ℝ → ℝ` is `ℝ`-linear.**  Such an `F` is `ℚ`-linear
(`map_rat_smul`), hence agrees with `t ↦ t * F 1` on the rationals, which are dense in `ℝ`;
both sides being continuous, the equality holds everywhere. -/
private lemma additive_continuous_eq_mul (F : ℝ → ℝ)
    (hadd : ∀ s t : ℝ, F (s + t) = F s + F t) (hcont : Continuous F) (t : ℝ) :
    F t = t * F 1 := by
  have hF0 : F 0 = 0 := by
    have h := hadd 0 0
    rw [zero_add] at h
    linarith
  let f : ℝ →+ ℝ := { toFun := F, map_zero' := hF0, map_add' := hadd }
  have hfcont : Continuous f := hcont
  have hkey : (f : ℝ → ℝ) = fun t => t * F 1 := by
    refine (Rat.denseRange_cast).equalizer hfcont ?_ ?_
    · fun_prop
    · funext q
      have h := map_rat_smul f q (1 : ℝ)
      rw [Rat.smul_one_eq_cast, Rat.smul_def] at h
      simpa [f] using h
  exact congr_fun hkey t

/-- **Homogeneous polarisation of a nonnegative quadratic form.**

For `Q : V → ℝ` on a real vector space satisfying the parallelogram law, `2`-homogeneity
and nonnegativity, the polar form is `ℝ`-homogeneous in its first argument.  This is the
nonnegativity version of the (false without an extra hypothesis)
`Work.BoseFixB2.Polar.par_polarisation`: the missing hypothesis is supplied here by
nonnegativity, which bounds the defect `s ↦ Q (s • x + y) − s ^ 2 * Q x − Q y`. -/
theorem hpol_par_hom_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : V → ℝ)
    (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y)
    (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x)
    (hnn : ∀ x : V, 0 ≤ Q x) :
    ∀ (t : ℝ) (x y : V), Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y)) := by
  intro t x y
  have hQneg : ∀ z : V, Q (-z) = Q z := by
    intro z
    have h := hhom (-1) z
    simpa using h
  -- the polar form along the line `s ↦ s • x + y`
  set A : ℝ → ℝ := fun s => (Q (s • x + y) - Q (s • x - y)) / 4 with hA
  have hAval : ∀ s : ℝ, A s = (Q (s • x + y) - Q (s • x - y)) / 4 := by
    intro s
    simp only [hA]
  -- additivity of `A`, from the parallelogram law
  have hAadd : ∀ s u : ℝ, A (s + u) = A s + A u := by
    intro s u
    have h := Work.BoseFixB2.Polar.polarForm_add Q hpar hhom (s • x) (u • x) y
    rw [← add_smul] at h
    simpa only [hAval] using h
  have hA0 : A 0 = 0 := by
    have h := hAadd 0 0
    simp only [zero_add] at h
    linarith
  have hAneg : ∀ s : ℝ, A (-s) = -A s := by
    intro s
    have h := hAadd s (-s)
    rw [add_neg_cancel, hA0] at h
    linarith
  -- the two quadratic identities along the line
  have hsum : ∀ s : ℝ, Q (s • x + y) + Q (s • x - y) = 2 * (s ^ 2 * Q x) + 2 * Q y := by
    intro s
    have h := hpar (s • x) y
    rw [hhom s x] at h
    linarith
  have hphi : ∀ s : ℝ, Q (s • x + y) = s ^ 2 * Q x + Q y + 2 * A s := by
    intro s
    have h1 := hsum s
    have h2 := hAval s
    linarith
  have hphi' : ∀ s : ℝ, Q (s • x - y) = s ^ 2 * Q x + Q y - 2 * A s := by
    intro s
    have h1 := hphi (-s)
    have h2 : Q ((-s) • x + y) = Q (s • x - y) := by
      rw [neg_smul, show -(s • x) + y = -(s • x - y) by abel, hQneg]
    rw [h2, hAneg s] at h1
    have hs2 : (-s) ^ 2 = s ^ 2 := by ring
    rw [hs2] at h1
    linarith
  -- nonnegativity bounds `A`
  have hbound : ∀ s : ℝ, |A s| ≤ (s ^ 2 * Q x + Q y) / 2 := by
    intro s
    have h1 := hnn (s • x + y)
    have h2 := hnn (s • x - y)
    have hp := hphi s
    have hp' := hphi' s
    rw [abs_le]
    constructor <;> linarith
  -- hence `A` is continuous and `ℝ`-linear
  have hcont : Continuous A := by
    refine Work.BoseFixB2.Polar.additive_bddAbove_continuous hAadd
      ⟨(Q x + Q y) / 2, 1, one_pos, ?_⟩
    intro s hs
    have hb := abs_le.mp (hbound s)
    have hs2 : s ^ 2 ≤ 1 := by
      have hlt := abs_lt.mp hs
      nlinarith [hlt.1, hlt.2]
    have hQx : 0 ≤ Q x := hnn x
    have hprod : 0 ≤ (1 - s ^ 2) * Q x := mul_nonneg (by linarith) hQx
    linarith [hb.1, hb.2, hprod]
  have hlin : A t = t * A 1 := additive_continuous_eq_mul A hAadd hcont t
  have hl : Q (t • x + y) - Q (t • x - y) = 4 * A t := by
    have h := hAval t
    linarith
  have hr : Q (x + y) - Q (x - y) = 4 * A 1 := by
    have h := hAval 1
    simp only [one_smul] at h
    linarith
  rw [hl, hr, hlin]
  ring

/-! ## 2. The parallelogram law for `bsOneBody` on smooth states -/

/-- The box mean is additive on continuous states. -/
private lemma bsMean_add {ℓ : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Work.BSKinetic.bsMean ℓ u (fun z => f z + g z)
      = Work.BSKinetic.bsMean ℓ u f + Work.BSKinetic.bsMean ℓ u g := by
  rw [Work.BSKinetic.bsMean, Work.BSKinetic.bsMean, Work.BSKinetic.bsMean]
  rw [show (∫ z in acube ℓ, (f (ℓ • u + z) + g (ℓ • u + z)))
      = (∫ z in acube ℓ, f (ℓ • u + z)) + ∫ z in acube ℓ, g (ℓ • u + z) from
    integral_add
      (ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.acube_isCompact ℓ)
        ((hf.comp (by fun_prop)).continuousOn))
      (ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.acube_isCompact ℓ)
        ((hg.comp (by fun_prop)).continuousOn))]
  ring

/-- The box mean is subtractive on continuous states. -/
private lemma bsMean_sub {ℓ : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Work.BSKinetic.bsMean ℓ u (fun z => f z - g z)
      = Work.BSKinetic.bsMean ℓ u f - Work.BSKinetic.bsMean ℓ u g := by
  rw [Work.BSKinetic.bsMean, Work.BSKinetic.bsMean, Work.BSKinetic.bsMean]
  rw [show (∫ z in acube ℓ, (f (ℓ • u + z) - g (ℓ • u + z)))
      = (∫ z in acube ℓ, f (ℓ • u + z)) - ∫ z in acube ℓ, g (ℓ • u + z) from
    integral_sub
      (ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.acube_isCompact ℓ)
        ((hf.comp (by fun_prop)).continuousOn))
      (ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.acube_isCompact ℓ)
        ((hg.comp (by fun_prop)).continuousOn))]
  ring

/-- The `p`-transform `bsPsi` is additive on smooth compactly supported states. -/
private lemma bsPsi_add {h₁ h₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hd₁ : ContDiff ℝ (⊤ : ℕ∞) h₁) (hc₁ : HasCompactSupport h₁)
    (hd₂ : ContDiff ℝ (⊤ : ℕ∞) h₂) (hc₂ : HasCompactSupport h₂)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BSKinetic.Decomp.bsPsi (fun z => h₁ z + h₂ z) p
      = Work.BSKinetic.Decomp.bsPsi h₁ p + Work.BSKinetic.Decomp.bsPsi h₂ p := by
  rw [Work.BSKinetic.Decomp.bsPsi, Work.BSKinetic.Decomp.bsPsi, Work.BSKinetic.Decomp.bsPsi,
    kinFT, kinFT, kinFT]
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (((h₁ z + h₂ z : ℝ) : ℂ))
        = Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((h₁ z : ℝ) : ℂ)
          + Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((h₂ z : ℝ) : ℂ) := by
    intro z; push_cast; ring
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_add (Work.BSKinetic.Decomp.integrable_phase_mul hd₁ hc₁ p)
    (Work.BSKinetic.Decomp.integrable_phase_mul hd₂ hc₂ p)]

/-- **The anchored parallelogram law.**  For smooth compactly supported states `h₁, h₂`,
`bsW F (h₁ + h₂) + bsW F (h₁ − h₂) = 2·bsW F h₁ + 2·bsW F h₂`. -/
private lemma bsW_parallelogram_local {c : ℝ} {h₁ h₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hd₁ : ContDiff ℝ (⊤ : ℕ∞) h₁) (hc₁ : HasCompactSupport h₁)
    (hd₂ : ContDiff ℝ (⊤ : ℕ∞) h₂) (hc₂ : HasCompactSupport h₂) :
    Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) (fun z => h₁ z + h₂ z)
      + Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) (fun z => h₁ z - h₂ z)
      = 2 * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h₁
        + 2 * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h₂ := by
  have hA := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) (hd₁.add hd₂) (hc₁.add hc₂)
  have hB := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) (hd₁.sub hd₂) (hc₁.sub hc₂)
  have hC := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) hd₁ hc₁
  have hD := Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq (c := c) hd₂ hc₂
  have hp : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi (fun z => h₁ z + h₂ z) p‖ ^ 2
        + Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi (fun z => h₁ z - h₂ z) p‖ ^ 2
      = 2 * (Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h₁ p‖ ^ 2)
        + 2 * (Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h₂ p‖ ^ 2) := by
    intro p
    rw [bsPsi_add hd₁ hc₁ hd₂ hc₂ p, Work.BSKinetic.Decomp.bsPsi_sub hd₁ hc₁ hd₂ hc₂ p]
    have h := parallelogram_law_with_norm ℂ (Work.BSKinetic.Decomp.bsPsi h₁ p)
      (Work.BSKinetic.Decomp.bsPsi h₂ p)
    linear_combination (Submission.BoseGases.fsKinCoeff c ‖p‖) * h
  simp only [Work.BSKinetic.Decomp.bsW]
  rw [← integral_add hA hB, integral_congr_ae (Eventually.of_forall hp)]
  rw [integral_add (hC.const_mul 2) (hD.const_mul 2), integral_const_mul, integral_const_mul]

/-- **The parallelogram law for the one-body big-box kinetic form** on smooth states. -/
private lemma bsOneBody_parallelogram_local {ℓ c : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z + g z)
      + Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z - g z)
      = 2 * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u f
        + 2 * Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u g := by
  have hℓ' : ℓ ≠ 0 := ne_of_gt hℓ
  have hShiftAdd : Work.BSKinetic.Decomp.bsShift ℓ (fun z => f z + g z) u
      = fun z => Work.BSKinetic.Decomp.bsShift ℓ f u z + Work.BSKinetic.Decomp.bsShift ℓ g u z := by
    funext z
    rw [Work.BSKinetic.Decomp.bsShift_apply, Work.BSKinetic.Decomp.bsShift_apply,
      Work.BSKinetic.Decomp.bsShift_apply, bsMean_add u hf.continuous hg.continuous]
    ring
  have hShiftSub : Work.BSKinetic.Decomp.bsShift ℓ (fun z => f z - g z) u
      = fun z => Work.BSKinetic.Decomp.bsShift ℓ f u z - Work.BSKinetic.Decomp.bsShift ℓ g u z := by
    funext z
    rw [Work.BSKinetic.Decomp.bsShift_apply, Work.BSKinetic.Decomp.bsShift_apply,
      Work.BSKinetic.Decomp.bsShift_apply, bsMean_sub u hf.continuous hg.continuous]
    ring
  rw [Work.BSKinetic.Decomp.bsOneBody_eq_bsW_shift hℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z + g z),
    Work.BSKinetic.Decomp.bsOneBody_eq_bsW_shift hℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z - g z),
    Work.BSKinetic.Decomp.bsOneBody_eq_bsW_shift hℓ (Submission.BoseGases.fsKinCoeff c) u f,
    Work.BSKinetic.Decomp.bsOneBody_eq_bsW_shift hℓ (Submission.BoseGases.fsKinCoeff c) u g]
  rw [hShiftAdd, hShiftSub]
  have hpar := bsW_parallelogram_local (c := c)
    (h₁ := Work.BSKinetic.Decomp.bsShift ℓ f u)
    (h₂ := Work.BSKinetic.Decomp.bsShift ℓ g u)
    (Work.BSKinetic.Decomp.contDiff_bsShift hℓ hf u)
    (Work.BSKinetic.Decomp.hasCompactSupport_bsShift hℓ' u)
    (Work.BSKinetic.Decomp.contDiff_bsShift hℓ hg u)
    (Work.BSKinetic.Decomp.hasCompactSupport_bsShift hℓ' u)
  linear_combination ((2 * Real.pi) ^ 3)⁻¹ * hpar

/-! ## 3. The smooth-function module -/

/-- The `ℝ`-submodule of `C^∞` functions `ℝ³ → ℝ`.  This is the state space on which the
parallelogram law for `bsOneBody` is at our disposal. -/
def SmoothFn : Submodule ℝ (EuclideanSpace ℝ (Fin 3) → ℝ) where
  carrier := {ψ | ContDiff ℝ (⊤ : ℕ∞) ψ}
  zero_mem' := by
    rw [Set.mem_ofPred_eq]
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    rw [Set.mem_ofPred_eq] at hf hg ⊢
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    rw [Set.mem_ofPred_eq] at hf ⊢
    exact hf.const_smul c

/-! ## 4. The target -/

theorem bsOneBody_hpol {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => t * f z + g z) - Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => t * f z - g z) = t * (Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z + g z) - Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z - g z)) := by
  set Q : SmoothFn → ℝ :=
    fun ψ => Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u ψ.1 with hQ
  have hpar : ∀ x y : SmoothFn, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y := by
    intro x y
    rw [hQ]
    exact bsOneBody_parallelogram_local hℓ u x.2 y.2
  have hhom : ∀ (s : ℝ) (x : SmoothFn), Q (s • x) = s ^ 2 * Q x := by
    intro s x
    rw [hQ]
    exact Work.BoseKinLoc.Word.bsOneBody_const_mul (ℓ := ℓ) (Submission.BoseGases.fsKinCoeff c) u s x.1
  have hnn : ∀ x : SmoothFn, 0 ≤ Q x := by
    intro x
    rw [hQ]
    exact Work.BSKinetic.bsOneBody_nonneg
      (F := Submission.BoseGases.fsKinCoeff c) (fun r => fsKinCoeff_nonneg c r) u x.1
  have hmain := hpol_par_hom_nonneg Q hpar hhom hnn t ⟨f, hf⟩ ⟨g, hg⟩
  have h1 : Q (t • (⟨f, hf⟩ : SmoothFn) + ⟨g, hg⟩)
      = Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => t * f z + g z) := by
    rw [hQ]; rfl
  have h2 : Q (t • (⟨f, hf⟩ : SmoothFn) - ⟨g, hg⟩)
      = Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => t * f z - g z) := by
    rw [hQ]; rfl
  have h3 : Q ((⟨f, hf⟩ : SmoothFn) + ⟨g, hg⟩)
      = Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z + g z) := by
    rw [hQ]; rfl
  have h4 : Q ((⟨f, hf⟩ : SmoothFn) - ⟨g, hg⟩)
      = Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => f z - g z) := by
    rw [hQ]; rfl
  rw [← h1, ← h2, ← h3, ← h4]
  exact hmain

end Work.BoseFixB2.Energy
