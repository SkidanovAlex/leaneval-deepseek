/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted interval integration-by-parts identity with weight `σ = sin(2θ)^{2-γ}`

This file proves `Work.FTS.EllipticEst.remov.slice_ibp_w`: with `v := u/cos θ`,
`σ(θ) := sin(2θ)^{2-γ}` and `a < b` inside `(0, π/2)`,

`∫_a^b [4 sin θ σ + ½(σ cos)'] (v'')² + ½ ∫_a^b (σ cos)' (v')² + 4 ∫_a^b sin θ σ v v''
  = ∫_a^b σ g' v'' + ½ [ σ cos θ ((v'')² + (v')²) ]_a^b`.

It is the `Ψ := σ` instance of the abstract identity `slice_ibp_aux_w` below (which has an
arbitrary weight `Ψ` and multiplier `Φ = cos θ · Ψ`), so that the two coefficients are
`4 sin θ σ + ½(σ cos)'` and `(σ cos)'`.  The differentiated equation

`g' = -cos θ v''' + 4 sin θ v'' - cos θ v' + 4 sin θ v`

on `(0, π/2)` is `gprime_v_form`, obtained by combining the `u`-form of `g'`
(`slice_gprime_ident`) with the three `u`-in-terms-of-`v` identities of
`slice_v_identities`.

The content of the abstract identity is a two-fold integration by parts: with
`K x = ½ Φ x ((v'' x)² + (v' x)²)` one has the *pointwise* identity

`(4 sin x Ψ + ½Φ')(v'')² + ½Φ'(v')² + 4 sin x Ψ v v'' = Ψ g' v'' + K'`

on `[a,b]` (because `Φ = cos·Ψ` turns the `Ψ g' v''` expansion into `-Φ v''v''' - Φ v'v'' +
4 sin·Ψ·((v'')² + v v'')`), and `∫_a^b K' = K b - K a`.  No endpoint analysis is needed:
everything lives on `[a,b] ⊂ (0, π/2)`, where `sin(2θ) > 0` and `cos θ > 0`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice_v_identities
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-- The `k`-th iterated derivative of a `C^n` function is `C^{n-k}`, pointwise.

Proved via `ContDiffWithinAt.derivWithin` on `Set.univ`, where `derivWithin f univ = deriv f`. -/
lemma contDiffAt_deriv_of_le_w {f : ℝ → ℝ} {x : ℝ} {n m : WithTop ℕ∞} (h : ContDiffAt ℝ n f x)
    (hm : m + 1 ≤ n) : ContDiffAt ℝ m (deriv f) x := by
  have h1 := h.contDiffWithinAt.derivWithin (𝕜 := ℝ) (s := Set.univ) (x := x) (m := m)
    uniqueDiffOn_univ hm (Set.mem_univ x)
  rwa [derivWithin_univ, contDiffWithinAt_univ] at h1

/-- The differentiated equation in `v`-form: with `v = u/cos θ` on `(0, π/2)`,

`g' = -cos θ · v''' + 4 sin θ · v'' - cos θ · v' + 4 sin θ · v`.

Combination of `slice_gprime_ident` (`g' = -u''' + (tan θ·u)'' - 6u'`) with the three
`v`-identities of `slice_v_identities` for `u'''`, `(tan θ·u)''` and `u'`. -/
theorem gprime_v_form (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ
        = - Real.cos θ * deriv (fun t => deriv (fun s => deriv (fun r => u r / Real.cos r) s) t) θ
          + 4 * Real.sin θ * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ
          - Real.cos θ * deriv (fun s => u s / Real.cos s) θ
          + 4 * Real.sin θ * (u θ / Real.cos θ) := by
  intro θ hθ
  rw [slice_gprime_ident u g hu hg θ hθ, (slice_v_identities u hu θ hθ).2.1,
    (slice_v_identities u hu θ hθ).2.2.1, (slice_v_identities u hu θ hθ).2.2.2]
  ring

/-- **The abstract weighted interval integration-by-parts identity.**  For functions
`v, g, Φ, Ψ` of class `C³, C¹, C², C⁰` on `[a,b]` (`a < b`) with `Φ = cos·Ψ` on `[a,b]` and
satisfying the differentiated equation `g' = -cos θ v''' + 4 sin θ v'' - cos θ v' + 4 sin θ v`,

`∫_a^b [4 sin θ Ψ + ½Φ'] (v'')² + ½ ∫_a^b Φ' (v')² + 4 ∫_a^b sin θ Ψ v v''
  = ∫_a^b Ψ g' v'' + ½ [ Φ ((v'')² + (v')²) ]_a^b`.

Proof: `K x = ½ Φ x ((v''x)² + (v'x)²)` has derivative equal to the difference of the two
integrands (pointwise, using `Φ = cos·Ψ` and the equation), so the fundamental theorem of
calculus gives the two `a`-`b` integral forms of the identity. -/
lemma slice_ibp_aux_w {v g Φ Ψ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv1 : ∀ x ∈ Set.Icc a b, HasDerivAt v (deriv v x) x)
    (hv2 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hv3 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv (deriv v)) (deriv (deriv (deriv v)) x) x)
    (hΦ1 : ∀ x ∈ Set.Icc a b, HasDerivAt Φ (deriv Φ x) x)
    (hΦ2 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv Φ) (deriv (deriv Φ) x) x)
    (hΦΨ : ∀ x ∈ Set.Icc a b, Φ x = Real.cos x * Ψ x)
    (heq : ∀ x ∈ Set.Icc a b, deriv g x
        = -Real.cos x * deriv (deriv (deriv v)) x + 4 * Real.sin x * deriv (deriv v) x
          - Real.cos x * deriv v x + 4 * Real.sin x * v x)
    (hc3 : ContinuousOn (deriv (deriv (deriv v))) (Set.Icc a b))
    (hcΨ : ContinuousOn Ψ (Set.Icc a b)) :
    (∫ x in a..b, (4 * Real.sin x * Ψ x + (1 / 2) * deriv Φ x) * (deriv (deriv v) x) ^ 2)
      + (1 / 2) * (∫ x in a..b, deriv Φ x * (deriv v x) ^ 2)
      + 4 * (∫ x in a..b, Real.sin x * Ψ x * v x * deriv (deriv v) x)
    = (∫ x in a..b, Ψ x * deriv g x * deriv (deriv v) x)
      + (1 / 2) * (Φ b * ((deriv (deriv v) b) ^ 2 + (deriv v b) ^ 2)
          - Φ a * ((deriv (deriv v) a) ^ 2 + (deriv v a) ^ 2)) := by
  have hab' : a ≤ b := le_of_lt hab
  have hc1 : ContinuousOn (deriv v) (Set.Icc a b) :=
    fun x hx => (hv2 x hx).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (deriv (deriv v)) (Set.Icc a b) :=
    fun x hx => (hv3 x hx).continuousAt.continuousWithinAt
  have hcv : ContinuousOn v (Set.Icc a b) :=
    fun x hx => (hv1 x hx).continuousAt.continuousWithinAt
  have hcΦ : ContinuousOn Φ (Set.Icc a b) :=
    fun x hx => (hΦ1 x hx).continuousAt.continuousWithinAt
  have hcΦ' : ContinuousOn (deriv Φ) (Set.Icc a b) :=
    fun x hx => (hΦ2 x hx).continuousAt.continuousWithinAt
  have hdg : ContinuousOn (deriv g) (Set.Icc a b) := by
    have hR : ContinuousOn (fun x => -Real.cos x * deriv (deriv (deriv v)) x
        + 4 * Real.sin x * deriv (deriv v) x - Real.cos x * deriv v x
        + 4 * Real.sin x * v x) (Set.Icc a b) := by fun_prop
    exact hR.congr heq
  set K : ℝ → ℝ := fun x =>
    (1/2) * (Φ x * (deriv (deriv v) x * deriv (deriv v) x + deriv v x * deriv v x)) with hK
  set Q : ℝ → ℝ := fun x => (1/2) * (deriv Φ x * (deriv (deriv v) x * deriv (deriv v) x
      + deriv v x * deriv v x)
      + Φ x * ((deriv (deriv (deriv v)) x * deriv (deriv v) x
          + deriv (deriv v) x * deriv (deriv (deriv v)) x)
        + (deriv (deriv v) x * deriv v x + deriv v x * deriv (deriv v) x))) with hQ
  have hQcont : ContinuousOn Q (Set.Icc a b) := by rw [hQ]; fun_prop
  have hQint : IntervalIntegrable Q volume a b := ContinuousOn.intervalIntegrable_of_Icc hab' hQcont
  have hKder : ∀ x ∈ Set.uIcc a b, HasDerivAt K (Q x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab'] at hx
    rw [hK, hQ]
    have h1 : HasDerivAt (fun y => deriv v y * deriv v y)
        (deriv (deriv v) x * deriv v x + deriv v x * deriv (deriv v) x) x :=
      (hv2 x hx).mul (hv2 x hx)
    have h2 : HasDerivAt (fun y => deriv (deriv v) y * deriv (deriv v) y)
        (deriv (deriv (deriv v)) x * deriv (deriv v) x
          + deriv (deriv v) x * deriv (deriv (deriv v)) x) x :=
      (hv3 x hx).mul (hv3 x hx)
    have hG := h2.add h1
    exact ((hΦ1 x hx).mul hG).const_mul (1/2)
  have hFTCK : ∫ x in a..b, Q x = K b - K a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hKder hQint
  have hKval : K b - K a = (1/2) * (Φ b * ((deriv (deriv v) b) ^ 2 + (deriv v b) ^ 2)
      - Φ a * ((deriv (deriv v) a) ^ 2 + (deriv v a) ^ 2)) := by
    rw [hK]; ring
  have hpt : ∀ x ∈ Set.Icc a b,
      (4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2
        + (1/2) * (deriv Φ x * (deriv v x) ^ 2)
        + 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x)
      = Ψ x * deriv g x * deriv (deriv v) x + Q x := by
    intro x hx
    simp only [hQ]
    rw [heq x hx, hΦΨ x hx]
    ring
  have hint1 : IntervalIntegrable
      (fun x => (4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2)
      volume a b := by
    have h : ContinuousOn
        (fun x => (4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2)
        (Set.Icc a b) := by fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc hab' h
  have hint2 : IntervalIntegrable (fun x => (1/2) * (deriv Φ x * (deriv v x) ^ 2)) volume a b := by
    have h : ContinuousOn (fun x => (1/2) * (deriv Φ x * (deriv v x) ^ 2)) (Set.Icc a b) := by
      fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc hab' h
  have hint3 : IntervalIntegrable (fun x => 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x))
      volume a b := by
    have h : ContinuousOn (fun x => 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x))
        (Set.Icc a b) := by fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc hab' h
  have hintR : IntervalIntegrable (fun x => Ψ x * deriv g x * deriv (deriv v) x) volume a b := by
    have h : ContinuousOn (fun x => Ψ x * deriv g x * deriv (deriv v) x) (Set.Icc a b) := by
      fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc hab' h
  have hInt : (∫ x in a..b, ((4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2
        + (1/2) * (deriv Φ x * (deriv v x) ^ 2)
        + 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x)))
      = (∫ x in a..b, (4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2)
        + (1/2) * (∫ x in a..b, deriv Φ x * (deriv v x) ^ 2)
        + 4 * (∫ x in a..b, Real.sin x * Ψ x * v x * deriv (deriv v) x) := by
    rw [intervalIntegral.integral_add (hint1.add hint2) hint3, intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hcongr : (∫ x in a..b, ((4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2
        + (1/2) * (deriv Φ x * (deriv v x) ^ 2)
        + 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x)))
      = ∫ x in a..b, (Ψ x * deriv g x * deriv (deriv v) x + Q x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab'] at hx
    exact hpt x hx
  have hmain : (∫ x in a..b, ((4 * Real.sin x * Ψ x + (1/2) * deriv Φ x) * (deriv (deriv v) x) ^ 2
        + (1/2) * (deriv Φ x * (deriv v x) ^ 2)
        + 4 * (Real.sin x * Ψ x * v x * deriv (deriv v) x)))
      = (∫ x in a..b, Ψ x * deriv g x * deriv (deriv v) x)
        + (1/2) * (Φ b * ((deriv (deriv v) b) ^ 2 + (deriv v b) ^ 2)
          - Φ a * ((deriv (deriv v) a) ^ 2 + (deriv v a) ^ 2)) := by
    rw [hcongr, intervalIntegral.integral_add hintR hQint, hFTCK, hKval]
  rw [← hInt, hmain]

/-- The weighted interval integration-by-parts identity with weight `σ(θ) = sin(2θ)^{2-γ}`.
With `v := u/cos`, `a < b` in `(0,π/2)`:
`∫_a^b [4 sin θ · σ + ½(σ cos)'] (v'')² + ½ ∫_a^b (σ cos)' (v')² + 4 ∫_a^b sin θ σ v v''
  = ∫_a^b σ g' v''  +  ½ [ σ cos θ ((v'')² + (v')²) ]_a^b`.
From `Lzero1 u = g` in `v`-form (`-cos θ v'' + 3 sin θ v' - 4 cos θ v = g`), differentiate to get
`g' = -cos θ v''' + 4 sin θ v'' - cos θ v' + 4 sin θ v`, multiply by `-σ v''`, integrate by parts
twice.  No endpoint analysis: everything is on `[a,b] ⊂ (0,π/2)`.

Useful ingredients already in the workspace: `Work.FTS.EllipticEst.remov.slice_v_identities`
gives `Lzero1 u = -cos θ v'' + 3 sin θ v' - 4 cos θ v`, `u''' = cos θ v''' - 3 sin θ v'' - 3 cos θ v' + sin θ v`
and `u' = cos θ v' - sin θ v` on `(0,π/2)`; `Work.FTS.EllipticEst.remov.slice_gprime_ident`
gives `deriv g θ = -deriv(deriv(deriv u)) θ + ...` in the `u`-form.  Combining the two gives
the `v`-form of `g'` used above. -/
theorem slice_ibp_w (γ : ℝ) (a b : ℝ) (hab : a < b) (ha : 0 < a) (hb : b < Real.pi / 2)
    {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    (∫ θ in a..b, (4 * Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + (1 / 2) * deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ)
        * (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2)
      + (1 / 2) * (∫ θ in a..b,
            deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) θ
          * (deriv (fun t => u t / Real.cos t) θ) ^ 2)
      + 4 * (∫ θ in a..b, Real.sin θ * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          * (u θ / Real.cos θ)
          * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ)
      = (∫ θ in a..b, Real.rpow (Real.sin (2 * θ)) (2 - γ) * deriv g θ
          * deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ)
        + (1 / 2) * (Real.cos b * Real.rpow (Real.sin (2 * b)) (2 - γ)
              * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) b) ^ 2
                + (deriv (fun t => u t / Real.cos t) b) ^ 2)
            - Real.cos a * Real.rpow (Real.sin (2 * a)) (2 - γ)
              * ((deriv (fun t => deriv (fun s => u s / Real.cos s) t) a) ^ 2
                + (deriv (fun t => u t / Real.cos t) a) ^ 2)) := by
  have hab' : a ≤ b := le_of_lt hab
  have hmem : ∀ x ∈ Set.Icc a b, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    exact ⟨by linarith [ha, hx.1], by linarith [hx.2, hb]⟩
  have hcos_ne : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2]⟩)
  have hvcd : ContDiffOn ℝ 3 (fun s => u s / Real.cos s) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn hcos_ne
  have hv3 : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 3 (fun s => u s / Real.cos s) x :=
    fun x hx => hvcd.contDiffAt (isOpen_Ioo.mem_nhds (hmem x hx))
  have hv1 : ∀ x ∈ Set.Icc a b, HasDerivAt (fun s => u s / Real.cos s)
      (deriv (fun s => u s / Real.cos s) x) x :=
    fun x hx => ((hv3 x hx).differentiableAt (by norm_num)).hasDerivAt
  have hdv2 : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 (deriv (fun s => u s / Real.cos s)) x :=
    fun x hx => contDiffAt_deriv_of_le_w (m := 2) (hv3 x hx) (by norm_num)
  have hv2 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv (fun s => u s / Real.cos s))
      (deriv (deriv (fun s => u s / Real.cos s)) x) x :=
    fun x hx => ((hdv2 x hx).differentiableAt (by norm_num)).hasDerivAt
  have hdv3 : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 1 (deriv (deriv (fun s => u s / Real.cos s))) x :=
    fun x hx => contDiffAt_deriv_of_le_w (m := 1) (hdv2 x hx) (by norm_num)
  have hv3' : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv (deriv (fun s => u s / Real.cos s)))
      (deriv (deriv (deriv (fun s => u s / Real.cos s))) x) x :=
    fun x hx => ((hdv3 x hx).differentiableAt (by norm_num)).hasDerivAt
  have hc3 : ContinuousOn (deriv (deriv (deriv (fun s => u s / Real.cos s)))) (Set.Icc a b) := by
    intro x hx
    have h0 : ContDiffAt ℝ 0 (deriv (deriv (deriv (fun s => u s / Real.cos s)))) x :=
      contDiffAt_deriv_of_le_w (m := 0) (hdv3 x hx) (by norm_num)
    exact (continuousWithinAt_univ _ x).mp h0.continuousWithinAt |>.continuousWithinAt
  have hsin2pos : ∀ x ∈ Set.Icc a b, 0 < Real.sin (2 * x) := by
    intro x hx
    have hxi := hmem x hx
    exact Real.sin_pos_of_mem_Ioo ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
  have hsin2cd : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 (fun t => Real.sin (2 * t)) x := by
    intro x hx
    exact (Real.contDiff_sin.contDiffAt).comp x (contDiffAt_const.mul contDiffAt_id)
  have hΨcd : ∀ x ∈ Set.Icc a b,
      ContDiffAt ℝ 2 (fun t => Real.rpow (Real.sin (2 * t)) (2 - γ)) x := by
    intro x hx
    exact (hsin2cd x hx).rpow contDiffAt_const (ne_of_gt (hsin2pos x hx))
  have hΦcd : ∀ x ∈ Set.Icc a b,
      ContDiffAt ℝ 2 (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x := by
    intro x hx
    exact (Real.contDiff_cos.contDiffAt).mul (hΨcd x hx)
  have hΦ1 : ∀ x ∈ Set.Icc a b,
      HasDerivAt (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ))
        (deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)) x) x :=
    fun x hx => ((hΦcd x hx).differentiableAt (by norm_num)).hasDerivAt
  have hΦ2 : ∀ x ∈ Set.Icc a b,
      HasDerivAt (deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ)))
        (deriv (deriv (fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ))) x) x :=
    fun x hx => ((contDiffAt_deriv_of_le_w (m := 1) (hΦcd x hx) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hcΨ : ContinuousOn (fun t => Real.rpow (Real.sin (2 * t)) (2 - γ)) (Set.Icc a b) := by
    intro x hx
    exact ((hΨcd x hx).continuousAt).continuousWithinAt
  have heq : ∀ x ∈ Set.Icc a b, deriv g x
      = -Real.cos x * deriv (deriv (deriv (fun s => u s / Real.cos s))) x
        + 4 * Real.sin x * deriv (deriv (fun s => u s / Real.cos s)) x
        - Real.cos x * deriv (fun s => u s / Real.cos s) x
        + 4 * Real.sin x * (u x / Real.cos x) :=
    fun x hx => gprime_v_form u g hu hg x (hmem x hx)
  exact slice_ibp_aux_w (v := fun s => u s / Real.cos s)
    (g := g)
    (Φ := fun t => Real.cos t * Real.rpow (Real.sin (2 * t)) (2 - γ))
    (Ψ := fun t => Real.rpow (Real.sin (2 * t)) (2 - γ))
    hab hv1 hv2 hv3' hΦ1 hΦ2 (fun x hx => rfl) heq hc3 hcΨ

end Work.FTS.EllipticEst.remov
