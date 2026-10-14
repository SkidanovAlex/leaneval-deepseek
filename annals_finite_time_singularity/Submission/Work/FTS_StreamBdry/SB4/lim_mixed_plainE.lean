import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
-- ===== merged: Submission.Work.FTS_MuLipC.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_MuLipC

open Work.FTS.Galerkin (Fn Fam slice muDyn)

set_option autoImplicit false

/-! ## The paper's envelope -/

/-- The envelope `α² + √α·X + α^{-3/2}·X²` of the three single-profile rows
(`Work.FTS.NonlinRows.Rl1.Env`). -/
def Env (α X : ℝ) : ℝ := α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2

theorem Env_nonneg {α X : ℝ} (hα : 0 ≤ α) (hX : 0 ≤ X) : 0 ≤ Env α X := by
  refine add_nonneg (add_nonneg (sq_nonneg α) ?_) ?_
  · exact mul_nonneg (Real.sqrt_nonneg α) hX
  · exact mul_nonneg (Real.rpow_nonneg hα _) (sq_nonneg X)

/-! ## The three fields of the modulation -/

/-- The `N₀`-field of the profile `g`: `N₀ α (F_*+g) g`. -/
def Sn0 (α : ℝ) (g : Fn) : Fn := Work.Construction.N0 α (Work.Construction.Ftot α g) g

/-- The `N`-field of the profile `g` at the stream function `Φ_s + E g`. -/
def Sn (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fn) : Fn :=
  Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + E g z θ)

/-- The transport field `3 D_θg/(1+z)`. -/
def Tf (g : Fn) : Fn := fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)

@[simp] theorem Sn0_apply (α : ℝ) (g : Fn) (z θ : ℝ) :
    Sn0 α g z θ = Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ := rfl

@[simp] theorem Sn_apply (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fn) (z θ : ℝ) :
    Sn α Φs E g z θ
      = Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + E g z θ) z θ :=
  rfl

@[simp] theorem Tf_apply (g : Fn) (z θ : ℝ) :
    Tf g z θ = 3 * Work.Spaces.Dth g z θ / (1 + z) := rfl

/-- **The modulation at the constant family is the `mufunS` of the three fields** `Sn0`, `Sn`,
`Tf`.  This is `Work.FTS_MuLamOK.muDyn_lambda_zero` together with the definition of
`Work.Construction.mufunS` (both sides unfold to the same `L₁₂`-expression). -/
theorem muDyn_const_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fn) :
    muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.cst g)) (Work.FTS.FinalV2.cst g) 0
      = (1 / (2 * α)) * (Work.Construction.L12 (Sn0 α g) 0
          + Work.Construction.L12 (Sn α Φs E g) 0)
        + (1 / (2 * α)) * Work.Construction.L12 (Tf g) 0 := rfl

/-! ## The three difference rows -/

/-- **The difference row of `N₀`.**  For `ClassC` profiles of `ℋ⁴`-size `≤ C₀α²` the `L₁₂`-zero
mode of the quadratic field `N₀ α (F_*+g) g` is Lipschitz in the profile, with a constant
depending on `α` and `C₀` only. -/
def DiffRow0 (α C₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ f f' : Fn,
    Work.FTS.ClassC.ClassC α f → Work.FTS.ClassC.ClassC α f' →
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α f' ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Sn0 α f) 0 - Work.Construction.L12 (Sn0 α f') 0|
      ≤ K * Work.FTS.Nonlin.Xn α (f - f')

/-- **The difference row of `N`.**  Same statement for the bilinear field
`N α (F_*+g) (Φ_s + E g)`; here `E` is a *linear* map (that is the hypothesis of the frozen
producer) so that `E(f − f') = E f − E f'`, and `Φ_s` satisfies the star package. -/
def DiffRow1 (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ f f' : Fn,
    Work.FTS.ClassC.ClassC α f → Work.FTS.ClassC.ClassC α f' →
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α f' ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0|
      ≤ K * Work.FTS.Nonlin.Xn α (f - f')

/-- **The difference row of the transport term.**  The transport zero-mode is *linear* in the
profile, so its difference row is the single-profile row of `Work.FTS.NonlinRows.rl2`
(`KMu2_row`), transported to the difference `f − f'` on the class. -/
def DiffRow2 (α C₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ f f' : Fn,
    Work.FTS.ClassC.ClassC α f → Work.FTS.ClassC.ClassC α f' →
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α f' ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0|
      ≤ K * Work.FTS.Nonlin.Xn α (f - f')

/-! ## The arithmetic: the three difference rows give `MuLipC` -/

/-- **The class-`C` Lipschitz bound from the three difference rows.**  `2α·μ` is the *sum* of the
three `L₁₂`-zero-modes, so the difference `μ(f) − μ(f')` is `(1/(2α))` times the sum of the three
differences, and the triangle inequality gives the constant `(K₀+K₁+K₂)/(2α)`. -/
theorem muLipC_of_diffRows {α C₀ : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (h0 : DiffRow0 α C₀) (h1 : DiffRow1 α C₀ Φs E) (h2 : DiffRow2 α C₀) :
    Work.FTS.FinalV2.MuLipC α C₀ Φs E := by
  obtain ⟨K0, hK0, hrow0⟩ := h0
  obtain ⟨K1, hK1, hrow1⟩ := h1
  obtain ⟨K2, hK2, hrow2⟩ := h2
  refine ⟨(K0 + K1 + K2) / (2 * α), by positivity, ?_⟩
  intro f f' hf hf' hXf hXf'
  have hA := hrow0 f f' hf hf' hXf hXf'
  have hB := hrow1 f f' hf hf' hXf hXf'
  have hC := hrow2 f f' hf hf' hXf hXf'
  set X : ℝ := Work.FTS.Nonlin.Xn α (f - f') with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact Work.Spaces.HkNorm_nonneg α 4 _
  have hsum : |Work.Construction.L12 (Sn0 α f) 0 - Work.Construction.L12 (Sn0 α f') 0
      + (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0)
      + (Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0)|
      ≤ (K0 + K1 + K2) * X := by
    have ht1 := abs_add_le (Work.Construction.L12 (Sn0 α f) 0
        - Work.Construction.L12 (Sn0 α f') 0)
      (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0)
    have ht2 := abs_add_le
      ((Work.Construction.L12 (Sn0 α f) 0 - Work.Construction.L12 (Sn0 α f') 0)
        + (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0))
      (Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0)
    rw [hX] at hA hB hC
    linarith
  rw [muDyn_const_eq, muDyn_const_eq]
  have hfac : (1 / (2 * α)) * (Work.Construction.L12 (Sn0 α f) 0
        + Work.Construction.L12 (Sn α Φs E f) 0)
      + (1 / (2 * α)) * Work.Construction.L12 (Tf f) 0
      - ((1 / (2 * α)) * (Work.Construction.L12 (Sn0 α f') 0
        + Work.Construction.L12 (Sn α Φs E f') 0)
      + (1 / (2 * α)) * Work.Construction.L12 (Tf f') 0)
      = (1 / (2 * α)) * ((Work.Construction.L12 (Sn0 α f) 0
            - Work.Construction.L12 (Sn0 α f') 0)
          + (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0)
          + (Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0)) := by
    ring
  rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
  calc (1 / (2 * α)) * |Work.Construction.L12 (Sn0 α f) 0
          - Work.Construction.L12 (Sn0 α f') 0
        + (Work.Construction.L12 (Sn α Φs E f) 0 - Work.Construction.L12 (Sn α Φs E f') 0)
        + (Work.Construction.L12 (Tf f) 0 - Work.Construction.L12 (Tf f') 0)|
      ≤ (1 / (2 * α)) * ((K0 + K1 + K2) * X) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (K0 + K1 + K2) / (2 * α) * X := by ring

end Work.FTS_MuLipC
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved` (RX-A2)

For a `LimApprox` datum `g` (the limit family of the strong route: on every horizon `[0,T]` it is
the `Qd`-jet limit of class-`C` approximants `gn` with uniform `ℋ⁴`-smallness `C₀ α²` and a
uniform `ℋ⁴`-Lipschitz modulus `L₀` in the fake time `τ`), the mixed slots of order `≤ 2` of the
slices `slice g τ` are

* **uniformly bounded** on the open quadrant: `|D_z^bD_θ^a g(·,·,τ)| ≤ 10/√(γ-1)·(C₀ α²)`, and
* **`τ`-Lipschitz**: `|D_z^bD_θ^a g(·,·,τ) - D_z^bD_θ^a g(·,·,τ')| ≤ C·|τ - τ'|`,

both uniformly in `τ, τ' ∈ [0,T]` and `(z,θ) ∈ Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)`.

This is the `(b,a)`-uniform form of the interior estimate that the domination arguments for the
angular parametric integrals of `coeff_C2` need.

## The proof

Both halves are limits of the corresponding bounds for the approximants `gn`.

*Uniform bound.* The class-`C` interior `L^∞`–`ℋ⁴` trade-off
`Work.FTS.StrongEps.SupPort.classC_mixed_sup_le`,
`|mixed b a f z θ| ≤ 10/√(γ-1)·Xn α f`, applied to `f = slice (gn n) τ` and combined with the
`Xn`-smallness clause `Xn α (slice (gn n) τ) ≤ C₀ α²` bounds every approximant; the `Qd`-jet
convergence clause of `LimApprox` then passes the bound to `slice g τ` (`le_of_tendsto`).

*Lipschitz bound.* `ClassC α` is a linear subspace, so the *difference*
`slice (gn n) τ - slice (gn n) τ'` is again class-`C` (`StrongEps.EComparison.classC_sub`);
`classC_mixed_sup_le` prices its slot by `Xn α` of the difference, which the Lipschitz clause of
`LimApprox` bounds by `L₀|τ - τ'|`; the additivity `mixed b a F - mixed b a G = mixed b a (F - G)`
on the open quadrant (`EllipticEst.TTSlot11Aux.mixed_sub_open`) identifies the slot of the
difference with the difference of the slots, and the jet convergence of `LimApprox` again passes
the bound to the limit.

The Lipschitz half is proved here rather than imported from
`Submission.Work.FTS_RegExport.RXT.lim_mixed_lip` because that sibling module does not currently
build (its final `le_of_tendsto` has its two arguments in the wrong order); the argument below is
the same one, written out.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXA2

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.FinalV2 (LimApprox)

set_option autoImplicit false

theorem lim_mixed_bounds_proved {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ b a : ℕ,
      a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (C₀ * αG ^ 2) ∧
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
            - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ|
            ≤ L * |τ - τ'| := by
  obtain ⟨gn, _B, L₀, hC, hLip, hjet, _hmu⟩ := hA T hT
  have hc : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0,
    mul_nonneg hc (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  refine ⟨?_, ?_⟩
  · -- ## the uniform bound
    have h1 : ∀ n : ℕ,
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ|
          ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (C₀ * αG ^ 2) := by
      intro n
      refine le_trans (Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1
        (hC n τ hτ).1 b a hab hzθ) ?_
      exact mul_le_mul_of_nonneg_left (hC n τ hτ).2.1 hc
    have h2 : Tendsto (fun n : ℕ =>
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ|) atTop
        (𝓝 |Work.Spaces.mixed b a (slice g τ) z θ|) :=
      (hjet τ hτ b a (by omega) z θ hzθ).abs
    exact le_of_tendsto h2 (Eventually.of_forall h1)
  · -- ## the τ-Lipschitz bound
    have hbd : ∀ᶠ n : ℕ in atTop,
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
          - Work.Spaces.mixed b a (slice (gn n) τ') z θ|
        ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0 * |τ - τ'| := by
      refine Eventually.of_forall (fun n => ?_)
      set F : Work.FTS.Galerkin.Fn := slice (gn n) τ with hF
      set G : Work.FTS.Galerkin.Fn := slice (gn n) τ' with hG
      have hsub : Work.FTS.ClassC.ClassC αG (fun z θ => F z θ - G z θ) :=
        Work.FTS.StrongEps.EComparison.classC_sub (hC n τ hτ).1 (hC n τ' hτ').1
      have hsup := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub b a hab hzθ
      have hlin := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open
        (hC n τ hτ).1.reg (hC n τ' hτ').1.reg b a z θ hz hθ0 hθ1
      have hlip : Work.FTS.Nonlin.Xn αG (fun z θ => F z θ - G z θ)
          ≤ max L₀ 0 * |τ - τ'| :=
        le_trans (hLip n τ hτ τ' hτ')
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      calc |Work.Spaces.mixed b a F z θ - Work.Spaces.mixed b a G z θ|
          = |Work.Spaces.mixed b a (fun z θ => F z θ - G z θ) z θ| := by
            rw [hlin]
        _ ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1)
              * Work.FTS.Nonlin.Xn αG (fun z θ => F z θ - G z θ) := hsup
        _ ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (max L₀ 0 * |τ - τ'|) :=
            mul_le_mul_of_nonneg_left hlip hc
        _ = 10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0 * |τ - τ'| := by ring
    have htend : Tendsto (fun n : ℕ =>
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
          - Work.Spaces.mixed b a (slice (gn n) τ') z θ|) atTop
        (𝓝 |Work.Spaces.mixed b a (slice g τ) z θ
          - Work.Spaces.mixed b a (slice g τ') z θ|) :=
      ((hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)).abs
    exact le_of_tendsto htend hbd

end Work.FTS_RegExport.RXA2
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.SliceDiffAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.SliceDiffAux`

Auxiliary vocabulary for `Work.FTS_RegExport.RXR1.slice_diff_weighted`.

The target lemma bounds the mixed slots of order `≤ 1` of the *difference of two slices*
`slice g τ - slice g τ'` of a `LimApprox` family by

  `C · (z^{3/2}/(1+z)²) · |τ - τ'|`

uniformly on the open quadrant.  The single analytic input is the weighted pointwise bound
`hw` on the mixed slots of order `≤ 2` of any profile which is `C^∞` on the open quadrant and
honest in `ℋ⁴` and in the boundary traces.  This file fixes

* `SliceW` — the radial weight `z^{3/2}/(1+z)²` (an `abbrev`, so that it is syntactically the
  same expression as the one appearing in the hypothesis `hw`);
* `HwBnd β C` — the inner part of that hypothesis, as a predicate;
* the two definitional identities `mixed 1 0 f = z·∂_z f` and `mixed 0 1 f = sin 2θ·∂_θ f`;
* the elementary consequences of `SliceW` used to make the bounds uniform on a compact
  subinterval of `(0,∞)`.
-/

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS_RegExport.RXR1

/-- The radial weight `z^{3/2}/(1+z)²` of the weighted slot bound. -/
abbrev SliceW (z : ℝ) : ℝ := z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2

/-- **The weighted slot bound**: the inner part of the hypothesis `hw` of the target lemma.
`C` bounds the mixed slots of order `≤ 2` of a class-`C⁴` profile by the weight `SliceW` times
its `ℋ⁴`-norm. -/
def HwBnd (β C : ℝ) : Prop :=
  ∀ f : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem β 4 f →
    Work.FTS.Nonlin.BdryTraces β 4 f →
    ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ C * SliceW z * Work.Spaces.HkNorm β 4 f

lemma SliceW_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ SliceW z :=
  div_nonneg (Real.rpow_nonneg hz _) (by positivity)


/-- `mixed 1 0 f = z · ∂_z f` (definitional). -/
lemma mixed_one_zero_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 0 f z θ = z * Work.Spaces.pzIter 1 f z θ := rfl

/-- `mixed 0 1 f = sin(2θ) · ∂_θ f` (definitional). -/
lemma mixed_zero_one_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 f z θ = Real.sin (2 * θ) * Work.Spaces.pthIter 1 f z θ := rfl

/-- `SliceW z / z = z^{1/2}/(1+z)²`. -/
lemma SliceW_div_eq {z : ℝ} (hz : 0 < z) :
    SliceW z / z = z ^ ((1 : ℝ) / 2) / (1 + z) ^ 2 := by
  have h : z ^ ((3 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * z := by
    rw [show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hz,
      Real.rpow_one]
  simp only [SliceW]
  rw [h]
  field_simp

/-- `SliceW z / (z·z) = z^{-1/2}/(1+z)²`. -/
lemma SliceW_div_sq_eq {z : ℝ} (hz : 0 < z) :
    SliceW z / (z * z) = z ^ (-(1 : ℝ) / 2) / (1 + z) ^ 2 := by
  have h : z ^ ((3 : ℝ) / 2) = z ^ (-(1 : ℝ) / 2) * (z * z) := by
    rw [show ((3 : ℝ) / 2) = -(1 : ℝ) / 2 + 1 + 1 by norm_num, Real.rpow_add hz,
      Real.rpow_add hz, Real.rpow_one]
    ring
  simp only [SliceW]
  rw [h]
  field_simp

/-- On `(0, 2z+1)` the weight `SliceW (·)/·` is bounded by `√(2z+1)`. -/
lemma SliceW_div_le_sqrt {z z' : ℝ} (hz : 0 < z) (hz' : z / 2 ≤ z') (hz'' : z' ≤ 2 * z + 1) :
    SliceW z' / z' ≤ Real.sqrt (2 * z + 1) := by
  have hz'0 : 0 < z' := lt_of_lt_of_le (by linarith) hz'
  rw [SliceW_div_eq hz'0, Real.sqrt_eq_rpow]
  have h1 : z' ^ ((1 : ℝ) / 2) / (1 + z') ^ 2 ≤ z' ^ ((1 : ℝ) / 2) / 1 := by
    refine div_le_div_of_nonneg_left (Real.rpow_nonneg hz'0.le _) one_pos ?_
    nlinarith
  rw [div_one] at h1
  exact h1.trans (Real.rpow_le_rpow hz'0.le hz'' (by norm_num))

/-- On `(z/2, ∞)` the weight `SliceW (·)/(·)²` is bounded by `(z/2)^{-1/2}`. -/
lemma SliceW_div_sq_le {z z' : ℝ} (hz : 0 < z) (hz' : z / 2 ≤ z') :
    SliceW z' / (z' * z') ≤ (z / 2) ^ (-(1 : ℝ) / 2) := by
  have hz'0 : 0 < z' := lt_of_lt_of_le (by linarith) hz'
  rw [SliceW_div_sq_eq hz'0]
  have h1 : z' ^ (-(1 : ℝ) / 2) / (1 + z') ^ 2 ≤ z' ^ (-(1 : ℝ) / 2) / 1 := by
    refine div_le_div_of_nonneg_left (Real.rpow_nonneg hz'0.le _) one_pos ?_
    nlinarith
  rw [div_one] at h1
  exact h1.trans (Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < z / 2) hz'
    (by norm_num))

end Work.FTS_RegExport.RXR1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus`

The mixed slots `D_z^bD_θ^a g(·,·,τ)` of the limit family of `LimApprox` are Lipschitz in the
fake time `τ` on every horizon `[0,T]`, for `a + b ≤ 2`, with the *weighted* space-time factor
`z^{3/2}/(1+z)²`:

`|D_z^bD_θ^a g(·,·,τ) - D_z^bD_θ^a g(·,·,τ')| ≤ L · z^{3/2}/(1+z)² · |τ - τ'|`.

This is the weighted refinement of `Work.FTS_RegExport.RXT.lim_mixed_lip` (which uses the
*constant* interior trade-off `ClassC_mixed_sup_le`).  The argument is the same:

* the approximating families `gn` of `LimApprox` are class-`C` slices whose `ℋ⁴`-difference is
  Lipschitz in `τ` (`Xn αG (slice (gn n) τ - slice (gn n) τ') = HkNorm αG 4 (…) ≤ L₀|τ - τ'|`);
* `ClassC` is a subspace, so the difference `slice (gn n) τ - slice (gn n) τ'` is again of class
  `C` (`EComparison.classC_sub`), hence `SmoothOpen`, honestly in `ℋ⁴` and satisfying the
  boundary traces up to order `4` (`classC_sub_hyp`);
* the **weighted** interior `L^∞`–`ℋ⁴` trade-off `abs_mixed_le_HkNorm_C4_w_proved` turns the
  `ℋ⁴`-Lipschitz bound into the pointwise weighted bound on every slot of the difference;
* `mixed_sub_open` identifies the slot of the difference with the difference of the slots, and
  the `C⁴`-jet convergence of `LimApprox` passes the bound to the limit.
-/

namespace Work.FTS_RegExport.RXR5.Pieces

open scoped Real Topology
open Filter

theorem mixed_slice_tau_modulus {αG C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ|
        ≤ L * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by
  -- the weighted interior `L^∞`–`ℋ⁴` trade-off, with a constant independent of the datum
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  -- the class-`C` approximants of the `LimApprox` clause
  obtain ⟨gn, _B, L₀, hC, hLip, hjet, _hmu⟩ := hA T hT
  refine ⟨Cw * max L₀ 0, mul_nonneg hCw0 (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  have hw0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  -- the slotwise bound on every approximant
  have hbd : ∀ᶠ n : ℕ in atTop,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|
      ≤ Cw * max L₀ 0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by
    refine Eventually.of_forall (fun n => ?_)
    set F : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice (gn n) τ with hF
    set G : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice (gn n) τ' with hG
    have hclsF : Work.FTS.ClassC.ClassC αG F := (hC n τ hτ).1
    have hclsG : Work.FTS.ClassC.ClassC αG G := (hC n τ' hτ').1
    -- the difference is again of class `C`, hence `ℋ⁴`-honest with the traces
    have hsub : Work.FTS.ClassC.ClassC αG (fun z θ => F z θ - G z θ) :=
      Work.FTS.StrongEps.EComparison.classC_sub hclsF hclsG
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ => F z θ - G z θ))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsub.reg 4
    have hmem : Work.Spaces.HkMem αG 4 (fun z θ => F z θ - G z θ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hsub.reg 4 (by norm_num) hsub.mem
    have htr : Work.FTS.Nonlin.BdryTraces αG 4 (fun z θ => F z θ - G z θ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) hsub.tr
    have h1 := hCw (fun z θ => F z θ - G z θ) h4 hmem htr b a hab z θ hz hθ0 hθ1
    -- the slot of the difference is the difference of the slots
    have hlin := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open
      hclsF.reg hclsG.reg b a z θ hz hθ0 hθ1
    -- the `ℋ⁴`-Lipschitz clause of `LimApprox`
    have hlip : Work.Spaces.HkNorm αG 4 (fun z θ => F z θ - G z θ) ≤ max L₀ 0 * |τ - τ'| :=
      le_trans (hLip n τ hτ τ' hτ')
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    calc |Work.Spaces.mixed b a F z θ - Work.Spaces.mixed b a G z θ|
        = |Work.Spaces.mixed b a (fun z θ => F z θ - G z θ) z θ| := by rw [hlin]
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm αG 4 (fun z θ => F z θ - G z θ) := h1
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (max L₀ 0 * |τ - τ'|) :=
          mul_le_mul_of_nonneg_left hlip (mul_nonneg hCw0 hw0)
      _ = Cw * max L₀ 0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by ring
  -- pass the slotwise bound to the limit along the jet convergence of `LimApprox`
  have htend : Filter.Tendsto (fun n : ℕ =>
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|) atTop
      (𝓝 |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ|) :=
    ((hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)).abs
  exact le_of_tendsto htend hbd

end Work.FTS_RegExport.RXR5.Pieces
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.lim_mixed_lip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.lim_mixed_lip`

The slots `D_z^bD_θ^a g(·,·,τ)` of the limit family of `LimApprox` are Lipschitz in the fake
time `τ` on every horizon `[0,T]`, for `a + b ≤ 2`.

The approximating families `gn` of the `LimApprox` clause are class-`C` slices whose
`ℋ⁴`-difference is Lipschitz in `τ` (`Xn α (slice (gn n) τ - slice (gn n) τ') ≤ L|τ - τ'|`).
`ClassC` is a subspace, so the *difference* `slice (gn n) τ - slice (gn n) τ'` is again of
class `C`, and the interior `L^∞`–`ℋ⁴` trade-off `ClassC_mixed_sup_le`
(`|D_z^bD_θ^a f(z,θ)| ≤ 10/√(γ-1)·|f|_{ℋ⁴}`) turns the `ℋ⁴`-Lipschitz bound into a
pointwise bound on every slot of the difference.  `mixed_sub_open` identifies the slot of the
difference with the difference of the slots, and the jet convergence of `LimApprox` passes the
bound to the limit.
-/

namespace Work.FTS_RegExport.RXT

open scoped Real Topology
open Filter

theorem lim_mixed_lip {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ| ≤ L * |τ - τ'| := by
  obtain ⟨gn, _B, L₀, hC, hLip, hjet, _hmu⟩ := hA T hT
  have hγ1 : 0 < Work.Spaces.gam αG - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hc : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0,
    mul_nonneg hc (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  have hbd : ∀ᶠ n : ℕ in atTop,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0 * |τ - τ'| := by
    refine Eventually.of_forall (fun n => ?_)
    set F : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice (gn n) τ with hF
    set G : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice (gn n) τ' with hG
    have hsub : Work.FTS.ClassC.ClassC αG (fun z θ => F z θ - G z θ) :=
      Work.FTS.StrongEps.EComparison.classC_sub (hC n τ hτ).1 (hC n τ' hτ').1
    have hsup := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub b a hab hzθ
    have hlin := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open
      (hC n τ hτ).1.reg (hC n τ' hτ').1.reg b a z θ hz hθ0 hθ1
    have hlip : Work.FTS.Nonlin.Xn αG (fun z θ => F z θ - G z θ) ≤ max L₀ 0 * |τ - τ'| := by
      refine le_trans (hLip n τ hτ τ' hτ') ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
    calc |Work.Spaces.mixed b a F z θ - Work.Spaces.mixed b a G z θ|
        = |Work.Spaces.mixed b a (fun z θ => F z θ - G z θ) z θ| := by rw [hlin]
      _ ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1)
            * Work.FTS.Nonlin.Xn αG (fun z θ => F z θ - G z θ) := hsup
      _ ≤ 10 / Real.sqrt (Work.Spaces.gam αG - 1) * (max L₀ 0 * |τ - τ'|) :=
          mul_le_mul_of_nonneg_left hlip hc
      _ = 10 / Real.sqrt (Work.Spaces.gam αG - 1) * max L₀ 0 * |τ - τ'| := by ring
  have htend : Tendsto (fun n : ℕ =>
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|) atTop
      (𝓝 |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ|) :=
    ((hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)).abs
  exact le_of_tendsto htend hbd

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB4

theorem lim_mixed_plainE {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  -- the interior trade-off: `|mixed b a f| ≤ Cw · z^{3/2}/(1+z)² · |f|_{ℋ⁴}`
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  -- the `LimApprox` clause at the horizon `T`
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ := hA T hT
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn αG (Work.FTS.Galerkin.slice (gn 0) 0) :=
    Work.Spaces.HkNorm_nonneg αG 4 _
  have hC0sq : 0 ≤ C₀ * αG ^ 2 := le_trans hX0 (hC 0 0 hT0).2.1
  refine ⟨Cw * (C₀ * αG ^ 2), mul_nonneg hCw0 hC0sq, ?_⟩
  intro τ hτ b a hab z θ hz hθ0 hθ1
  have hw0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  -- the existential constant of the approximating sequence is uniform in `n`
  have hbound : ∀ n : ℕ,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro n
    have hcls : Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) := (hC n τ hτ).1
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hcls.reg 4
    have hmem : Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 4 (by norm_num) hcls.mem
    have htr : Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcls.tr
    have h1 := hCw _ h4 hmem htr b a hab z θ hz hθ0 hθ1
    have h2 : Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
      (hC n τ hτ).2.1
    calc |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := h1
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (C₀ * αG ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCw0 hw0)
      _ = Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  exact le_of_tendsto ((hjet τ hτ b a (by omega) z θ hzθ).abs)
    (Filter.Eventually.of_forall hbound)

end Work.FTS_StreamBdry.SB4
end
