import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXR1.slice_diff_bound
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_deriv4_of_uniform_H6
import Submission.Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.slice_deriv_equi`

Equicontinuity of the `z`-derivative of the `τ`-difference quotient of the slices of a
`LimApprox` family `g`.

The hypothesis `LimApprox α C₀ Φs E g` produces, for every horizon `T > 0`, class-`C` profiles
`gn n` whose mixed jets converge pointwise on the open quadrant `Qd` to those of `g`, with the
uniform `ℋ⁴`-Lipschitz-in-`τ` bound `Xn α (slice (gn n) τ - slice (gn n) τ') ≤ L|τ-τ'|`.

The two conclusions are the `L^∞` bound `|∂_z q_τ(z)| ≤ (10/√(γ-1)) L / z` and the
`1/z`-Lipschitz bound `|∂_z q_τ(z) - ∂_z q_τ(z')| ≤ 2(10/√(γ-1)) L |1/z - 1/z'|` for the
difference quotient `q_τ(z) = (slice g τ (z,θ) - slice g 0 (z,θ))/τ`.

The proof:

* `Work.FTS.StrongEps.LocUnif.exists_limData` + `conclusion_of_limData` upgrade the pointwise
  convergence of the `(0,0)`-jet to `ContDiffOn ℝ 4` of `slice g τ` on the open quadrant, which
  is what the chain rule below needs;
* the *difference* of two class-`C` slices is again `ℋ⁴`-honest with the `BdryTraces`-vanishing
  (`classC_sub_hyp`), so `mixed_abs_le_of_smoothOpen` bounds its mixed slots of order `≤ 2` by
  `10/√(γ-1) · Xn α (slice (gn n) τ - slice (gn n) 0) ≤ 10/√(γ-1) · L τ`;
* `mixed_sub_of_contDiffOn_four` turns the difference of the two limits into the mixed jet of the
  difference, and the pointwise convergence of the approximants passes the bounds to the limit;
* the `1/z`-Lipschitz bound is the fundamental theorem of calculus applied to
  `t ↦ mixed 1 0 (f - f') t θ / t` on the approximants (whose second derivative obeys
  `2·C/t²`), and then passed to the limit pointwise.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR1

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Two calculus helpers -/

/-- `∫_a^b dt/t² = 1/a - 1/b` for `0 < a ≤ b`. -/
theorem integral_one_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / t ^ 2 = 1 / a - 1 / b := by
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -(1 / t)) (1 / x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    have h := (hasDerivAt_inv hx0).neg
    have hfun : (fun t : ℝ => -(1 / t)) = fun t : ℝ => -(t⁻¹) := by funext t; rw [one_div]
    have hval : -(-(x ^ 2)⁻¹) = 1 / x ^ 2 := by rw [neg_neg, one_div]
    rw [hfun, ← hval]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hx.1))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]; ring

/-- **The `z`-derivative of the slice**, from `C⁴`-smoothness of the uncurried function on the
open quadrant. -/
theorem hasDerivAt_slice_of_four {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => f z' θ) (Work.Spaces.pz f z θ) z := by
  have hmap : ContDiffOn ℝ 4 (fun x : ℝ => (x, θ)) (Set.Ioi 0) :=
    (contDiffOn_id : ContDiffOn ℝ 4 (fun z : ℝ => z) (Set.Ioi 0)).prodMk
      (contDiffOn_const (c := θ))
  have hslice : ContDiffOn ℝ 4 (fun z' : ℝ => f z' θ) (Set.Ioi 0) := by
    have h := hf.comp hmap (fun x hx => ⟨hx, hθ⟩)
    rw [show (Function.uncurry f) ∘ (fun x : ℝ => (x, θ)) = fun z' => f z' θ from rfl] at h
    exact h
  have hdiff : DifferentiableAt ℝ (fun z' : ℝ => f z' θ) z :=
    (hslice.differentiableOn (by norm_num : (4 : WithTop ℕ∞) ≠ 0)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  simpa [Work.Spaces.pz] using hdiff.hasDerivAt

/-- **The `1/z`-Lipschitz bound for the quotient `t ↦ mixed 1 0 f t θ / t`.**

If `f` is `C^∞` on the open quadrant and the first two mixed `z`-slots of `f` at the angle `θ`
are bounded by `C`, then `t ↦ mixed 1 0 f t θ / t` is `2C`-Lipschitz for the metric
`|1/z - 1/z'|`.  (The bound is the fundamental theorem of calculus; the derivative of the
quotient is `(∂_z D_z f·t - D_z f)/t²` and both summands are `≤ C`.) -/
theorem smooth_lip1z {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {C : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb1 : ∀ t : ℝ, 0 < t → |Work.Spaces.mixed 1 0 f t θ| ≤ C)
    (hb2 : ∀ t : ℝ, 0 < t → |Work.Spaces.mixed 2 0 f t θ| ≤ C) :
    ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ),
      |Work.Spaces.mixed 1 0 f z θ / z - Work.Spaces.mixed 1 0 f z' θ / z'|
        ≤ 2 * C * |1 / z - 1 / z'| := by
  have hF_deriv : ∀ t ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun s : ℝ => Work.Spaces.mixed 1 0 f s θ / s)
        ((Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ * t - Work.Spaces.mixed 1 0 f t θ) / t ^ 2)
        t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h2 : HasDerivAt (fun s : ℝ => Work.Spaces.mixed 1 0 f s θ)
        (Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ) t :=
      (hf.mixed 1 0).hasDerivAt_slice hθ ht
    have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h := h2.div h1 ht0
    have hfun : ((fun s : ℝ => Work.Spaces.mixed 1 0 f s θ) / fun s : ℝ => s)
        = fun s : ℝ => Work.Spaces.mixed 1 0 f s θ / s := by
      funext s; rfl
    rw [hfun] at h
    simpa only [mul_one] using h
  have hF_bound : ∀ t ∈ Set.Ioi (0:ℝ),
      |(Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ * t - Work.Spaces.mixed 1 0 f t θ) / t ^ 2|
        ≤ 2 * C / t ^ 2 := by
    intro t ht
    have ht0 : 0 < t := ht
    have hpz : |Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ| * t ≤ C := by
      have hid : t * Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ
          = Work.Spaces.mixed 2 0 f t θ := rfl
      have h2 := hb2 t ht0
      rw [← hid, abs_mul, abs_of_pos ht0, mul_comm] at h2
      exact h2
    have hn : |Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ * t - Work.Spaces.mixed 1 0 f t θ|
        ≤ 2 * C := by
      calc |Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ * t - Work.Spaces.mixed 1 0 f t θ|
          ≤ |Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ * t| + |Work.Spaces.mixed 1 0 f t θ| :=
            abs_sub _ _
        _ = |Work.Spaces.pz (Work.Spaces.mixed 1 0 f) t θ| * t + |Work.Spaces.mixed 1 0 f t θ| := by
            rw [abs_mul, abs_of_pos ht0]
        _ ≤ 2 * C := by linarith [hpz, hb1 t ht0]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
    exact div_le_div_of_nonneg_right hn (by positivity)
  have hmain : ∀ a b : ℝ, 0 < a → 0 < b → a ≤ b →
      |Work.Spaces.mixed 1 0 f b θ / b - Work.Spaces.mixed 1 0 f a θ / a|
        ≤ 2 * C * (1 / a - 1 / b) := by
    intro a b ha hb hab
    have hsub : Set.Icc a b ⊆ Set.Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
    have hsub' : Set.uIcc a b ⊆ Set.Ioi (0:ℝ) := by rwa [Set.uIcc_of_le hab]
    have hnum : ContinuousOn (fun s : ℝ =>
        Work.Spaces.pz (Work.Spaces.mixed 1 0 f) s θ * s - Work.Spaces.mixed 1 0 f s θ)
        (Set.Ioi (0:ℝ)) :=
      (((hf.mixed 1 0).pz.curry_z hθ).continuousOn.mul continuousOn_id).sub
        ((hf.mixed 1 0).curry_z hθ).continuousOn
    have hint1 : IntervalIntegrable
        (fun s : ℝ => (Work.Spaces.pz (Work.Spaces.mixed 1 0 f) s θ * s
          - Work.Spaces.mixed 1 0 f s θ) / s ^ 2) volume a b :=
      (ContinuousOn.div hnum (continuousOn_id.pow 2)
        (fun x hx => pow_ne_zero 2 (ne_of_gt hx))).mono hsub' |>.intervalIntegrable
    have hint2 : IntervalIntegrable (fun t : ℝ => 2 * C / t ^ 2) volume a b :=
      (ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
        (fun x hx => pow_ne_zero 2 (ne_of_gt hx))).mono hsub' |>.intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hF_deriv x (hsub' hx)) hint1
    have hstep : |Work.Spaces.mixed 1 0 f b θ / b - Work.Spaces.mixed 1 0 f a θ / a|
        ≤ ∫ s in a..b,
          |(Work.Spaces.pz (Work.Spaces.mixed 1 0 f) s θ * s
            - Work.Spaces.mixed 1 0 f s θ) / s ^ 2| := by
      rw [show Work.Spaces.mixed 1 0 f b θ / b - Work.Spaces.mixed 1 0 f a θ / a
          = ∫ s in a..b, (Work.Spaces.pz (Work.Spaces.mixed 1 0 f) s θ * s
            - Work.Spaces.mixed 1 0 f s θ) / s ^ 2 from hFTC.symm]
      exact intervalIntegral.abs_integral_le_integral_abs hab
    calc |Work.Spaces.mixed 1 0 f b θ / b - Work.Spaces.mixed 1 0 f a θ / a|
        ≤ ∫ s in a..b,
            |(Work.Spaces.pz (Work.Spaces.mixed 1 0 f) s θ * s
              - Work.Spaces.mixed 1 0 f s θ) / s ^ 2| := hstep
      _ ≤ ∫ t in a..b, 2 * C / t ^ 2 :=
            intervalIntegral.integral_mono_on hab hint1.abs hint2 (fun x hx => hF_bound x (hsub hx))
      _ = 2 * C * (1 / a - 1 / b) := by
            rw [show (fun t : ℝ => 2 * C / t ^ 2) = fun t : ℝ => (2 * C) * (1 / t ^ 2) by
                funext t; ring,
              intervalIntegral.integral_const_mul, integral_one_div_sq ha hab]
  intro z hz z' hz'
  rcases le_total z z' with h | h
  · rw [abs_sub_comm (Work.Spaces.mixed 1 0 f z θ / z),
      abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le hz h))]
    exact hmain z z' hz hz' h
  · have h1 : |1 / z - 1 / z'| = 1 / z' - 1 / z := by
      rw [abs_sub_comm (1 / z), abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le hz' h))]
    rw [h1]
    exact hmain z' z hz' hz h

/-! ## The main theorem -/

theorem slice_deriv_equi {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα1 : α ≤ 1) (hA : Work.FTS.FinalV2.LimApprox α C₀ Φs E g)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ),
        |deriv (fun z'' => (Work.FTS.Galerkin.slice g τ z'' θ - Work.FTS.Galerkin.slice g 0 z'' θ)/τ) z|
          ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * L / z) ∧
      (∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ),
        |deriv (fun z'' => (Work.FTS.Galerkin.slice g τ z'' θ - Work.FTS.Galerkin.slice g 0 z'' θ)/τ) z
          - deriv (fun z'' => (Work.FTS.Galerkin.slice g τ z'' θ - Work.FTS.Galerkin.slice g 0 z'' θ)/τ) z'|
          ≤ 2 * (10 / Real.sqrt (Work.Spaces.gam α - 1)) * L * |1/z - 1/z'|) := by
  classical
  obtain ⟨gn, B, L₀, hCC, hLip, hjet, -⟩ := hA 1 one_pos
  set c : ℝ := 10 / Real.sqrt (Work.Spaces.gam α - 1) with hcdef
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hcpos : 0 < c := by
    rw [hcdef]
    exact div_pos (by norm_num) (Real.sqrt_pos.mpr hγ)
  have hL0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  -- ### `C⁴`-regularity of the limit slices
  have hC4 : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    have hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice (gn n) τ) :=
      fun n => (hCC n τ hτ).1.reg
    have hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (gn n) τ) :=
      fun n => Work.FTS.OpenPkg.HkMem_mono_open (hCC n τ hτ).1.reg 6 (by norm_num)
        (hCC n τ hτ).1.mem
    have hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice (gn n) τ) ≤ B :=
      fun n => (hCC n τ hτ).2.2
    obtain ⟨φ, hφ, F, hF⟩ := Work.FTS.StrongEps.LocUnif.exists_limData hα hsm hmem hb
      (Work.FTS.StrongEps.LocUnif.inputs_of_children hα)
    obtain ⟨hconv, hcd4, -⟩ := Work.FTS.StrongEps.LocUnif.conclusion_of_limData hsm hF
    have hFeq : ∀ p ∈ Work.FTS.EllipticEst.Q0,
        F 0 0 p.1 p.2 = Work.FTS.Galerkin.slice g τ p.1 p.2 := by
      intro p hp
      have huni : Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn (φ n)) τ p.1 p.2)
          Filter.atTop (𝓝 (F 0 0 p.1 p.2)) :=
        ((hconv {p} isCompact_singleton (by simpa [Set.singleton_subset_iff] using hp)).tendsto_at
          (Set.mem_singleton p))
      have hjet' : Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn (φ n)) τ p.1 p.2)
          Filter.atTop (𝓝 (Work.FTS.Galerkin.slice g τ p.1 p.2)) := by
        have h := (hjet τ hτ 0 0 (by norm_num) p.1 p.2 (by exact hp)).comp hφ.tendsto_atTop
        have hcomp : ((fun n => Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice (gn n) τ)
              p.1 p.2) ∘ φ)
            = fun n => Work.FTS.Galerkin.slice (gn (φ n)) τ p.1 p.2 := by
          funext n
          simp
        rwa [hcomp] at h
      exact tendsto_nhds_unique huni hjet'
    refine hcd4.congr ?_
    intro p hp
    simp only [Function.uncurry]
    exact (hFeq p hp).symm
  -- ### the pointwise limits of the mixed jets of the differences
  have hlimΔ : ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc (0:ℝ) 1) (b a : ℕ) (hab : b + a ≤ 4)
      (t : ℝ) (ht : 0 < t),
      Filter.Tendsto (fun n => Work.Spaces.mixed b a
          (fun z θ' => Work.FTS.Galerkin.slice (gn n) τ z θ'
            - Work.FTS.Galerkin.slice (gn n) 0 z θ') t θ)
        Filter.atTop
        (𝓝 (Work.Spaces.mixed b a
          (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') t θ)) := by
    intro τ hτ b a hab t ht
    have hpq : (t, θ) ∈ Work.Construction.Qd := ⟨ht, hθ.1, hθ.2⟩
    have hl : (fun n => Work.Spaces.mixed b a
        (fun z θ' => Work.FTS.Galerkin.slice (gn n) τ z θ'
          - Work.FTS.Galerkin.slice (gn n) 0 z θ') t θ)
        = fun n => Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) t θ
            - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) 0) t θ := by
      funext n
      exact (Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four (j := b) (i := a) hab ht hθ
        ((hCC n τ hτ).1.reg.forall 4) ((hCC n 0 hL0mem).1.reg.forall 4))
    have hr : Work.Spaces.mixed b a
        (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
          - Work.FTS.Galerkin.slice g 0 z θ') t θ
        = Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) t θ
            - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g 0) t θ :=
      Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four (j := b) (i := a) hab ht hθ
        (hC4 τ hτ) (hC4 0 hL0mem)
    rw [hl, hr]
    exact (hjet τ hτ b a hab t θ hpq).sub (hjet 0 hL0mem b a hab t θ hpq)
  -- ### the n-level bounds on the two mixed slots of the difference
  have hnbd : ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (t : ℝ) (ht : 0 < t),
      (|Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice (gn n) τ z θ'
          - Work.FTS.Galerkin.slice (gn n) 0 z θ') t θ| ≤ c * ((max L₀ 0) * τ)) ∧
      (|Work.Spaces.mixed 2 0 (fun z θ' => Work.FTS.Galerkin.slice (gn n) τ z θ'
          - Work.FTS.Galerkin.slice (gn n) 0 z θ') t θ| ≤ c * ((max L₀ 0) * τ)) := by
    intro τ hτ n t ht
    have hsub := classC_sub_hyp (f := Work.FTS.Galerkin.slice (gn n) τ)
      (g := Work.FTS.Galerkin.slice (gn n) 0) (hCC n τ hτ).1 (hCC n 0 hL0mem).1
    have hxn : Work.Spaces.HkNorm α 4
        (Work.FTS.Galerkin.slice (gn n) τ - Work.FTS.Galerkin.slice (gn n) 0)
        ≤ (max L₀ 0) * τ := by
      have h := hLip n τ hτ 0 hL0mem
      rw [sub_zero, abs_of_nonneg hτ.1] at h
      exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left L₀ 0) hτ.1)
    constructor
    · refine (Work.FTS.StrongEps.SupPort.mixed_abs_le_of_smoothOpen (α := α) hα hα1 hsub.1
        hsub.2.1 hsub.2.2 1 0 (by norm_num) ht hθ.1 hθ.2).trans ?_
      rw [hcdef]
      exact mul_le_mul_of_nonneg_left hxn (le_of_lt hcpos)
    · refine (Work.FTS.StrongEps.SupPort.mixed_abs_le_of_smoothOpen (α := α) hα hα1 hsub.1
        hsub.2.1 hsub.2.2 2 0 (by norm_num) ht hθ.1 hθ.2).trans ?_
      rw [hcdef]
      exact mul_le_mul_of_nonneg_left hxn (le_of_lt hcpos)
  -- ### the derivative of the difference quotient
  have hderiv_of : ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc (0:ℝ) 1) (hτ0 : 0 < τ) (t : ℝ) (ht : 0 < t),
      deriv (fun z'' : ℝ => (Work.FTS.Galerkin.slice g τ z'' θ
          - Work.FTS.Galerkin.slice g 0 z'' θ)/τ) t
        = Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') t θ / (t * τ) := by
    intro τ hτ hτ0 t ht
    have htne : t ≠ 0 := ne_of_gt ht
    have hτne : τ ≠ 0 := ne_of_gt hτ0
    have hA : HasDerivAt (fun z'' : ℝ => Work.FTS.Galerkin.slice g τ z'' θ)
        (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) t θ) t :=
      hasDerivAt_slice_of_four (hC4 τ hτ) hθ ht
    have hB : HasDerivAt (fun z'' : ℝ => Work.FTS.Galerkin.slice g 0 z'' θ)
        (Work.Spaces.pz (Work.FTS.Galerkin.slice g 0) t θ) t :=
      hasDerivAt_slice_of_four (hC4 0 hL0mem) hθ ht
    have hsubd : deriv (fun z'' : ℝ => (Work.FTS.Galerkin.slice g τ z'' θ
        - Work.FTS.Galerkin.slice g 0 z'' θ)) t
        = Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) t θ
          - Work.Spaces.pz (Work.FTS.Galerkin.slice g 0) t θ :=
      (hA.sub hB).deriv
    have h1 : deriv (fun z'' : ℝ => (Work.FTS.Galerkin.slice g τ z'' θ
        - Work.FTS.Galerkin.slice g 0 z'' θ)/τ) t
        = (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) t θ
          - Work.Spaces.pz (Work.FTS.Galerkin.slice g 0) t θ)/τ := by
      rw [deriv_div_const, hsubd]
    have hpzA : Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) t θ
        = Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) t θ / t := by
      have h : Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) t θ
          = t * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) t θ := rfl
      rw [h, mul_div_cancel_left₀ _ htne]
    have hpzB : Work.Spaces.pz (Work.FTS.Galerkin.slice g 0) t θ
        = Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g 0) t θ / t := by
      have h : Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g 0) t θ
          = t * Work.Spaces.pz (Work.FTS.Galerkin.slice g 0) t θ := rfl
      rw [h, mul_div_cancel_left₀ _ htne]
    have hlin : Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) t θ
        - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g 0) t θ
        = Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') t θ :=
      (Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four (j := 1) (i := 0) (by norm_num) ht hθ
        (hC4 τ hτ) (hC4 0 hL0mem)).symm
    rw [h1, hpzA, hpzB]
    rw [show Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) t θ / t
          - Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g 0) t θ / t
        = Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') t θ / t by rw [← hlin]; ring]
    field_simp
  -- ### conclusion: the `L^∞` bound
  have hconj1 : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ),
      |deriv (fun z'' => (Work.FTS.Galerkin.slice g τ z'' θ
        - Work.FTS.Galerkin.slice g 0 z'' θ)/τ) z| ≤ c * (max L₀ 0) / z := by
    intro τ hτ z hz
    have hIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ.1.le, hτ.2⟩
    have hzτ : 0 < z * τ := mul_pos hz hτ.1
    have hM : |Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
        - Work.FTS.Galerkin.slice g 0 z θ') z θ| ≤ c * ((max L₀ 0) * τ) :=
      le_of_tendsto' ((hlimΔ τ hIcc 1 0 (by norm_num) z hz).abs)
        (fun n => (hnbd τ hIcc n z hz).1)
    rw [hderiv_of τ hIcc hτ.1 z hz, abs_div, abs_of_pos hzτ]
    calc |Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') z θ| / (z * τ)
        ≤ (c * ((max L₀ 0) * τ)) / (z * τ) := div_le_div_of_nonneg_right hM hzτ.le
      _ = c * (max L₀ 0) / z := by
            rw [div_eq_div_iff (ne_of_gt hzτ) (ne_of_gt hz)]
            ring
  -- ### conclusion: the `1/z`-Lipschitz bound
  have hconj2 : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z ∈ Set.Ioi (0:ℝ), ∀ z' ∈ Set.Ioi (0:ℝ),
      |deriv (fun z'' => (Work.FTS.Galerkin.slice g τ z'' θ
          - Work.FTS.Galerkin.slice g 0 z'' θ)/τ) z
        - deriv (fun z'' => (Work.FTS.Galerkin.slice g τ z'' θ
          - Work.FTS.Galerkin.slice g 0 z'' θ)/τ) z'|
        ≤ 2 * c * (max L₀ 0) * |1 / z - 1 / z'| := by
    intro τ hτ z hz z' hz'
    have hIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ.1.le, hτ.2⟩
    -- the n-level Lipschitz bound
    have hn : ∀ n : ℕ,
        |Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice (gn n) τ z θ'
              - Work.FTS.Galerkin.slice (gn n) 0 z θ') z θ / z
            - Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice (gn n) τ z θ'
              - Work.FTS.Galerkin.slice (gn n) 0 z θ') z' θ / z'|
          ≤ 2 * (c * ((max L₀ 0) * τ)) * |1 / z - 1 / z'| := by
      intro n
      exact smooth_lip1z ((classC_sub_hyp (hCC n τ hIcc).1 (hCC n 0 hL0mem).1).1)
        hθ (fun t ht => (hnbd τ hIcc n t ht).1) (fun t ht => (hnbd τ hIcc n t ht).2)
        z hz z' hz'
    -- the limit
    have hlim2 : Filter.Tendsto (fun n =>
          Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice (gn n) τ z θ'
              - Work.FTS.Galerkin.slice (gn n) 0 z θ') z θ / z
          - Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice (gn n) τ z θ'
              - Work.FTS.Galerkin.slice (gn n) 0 z θ') z' θ / z')
        Filter.atTop
        (𝓝 (Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
              - Work.FTS.Galerkin.slice g 0 z θ') z θ / z
          - Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
              - Work.FTS.Galerkin.slice g 0 z θ') z' θ / z')) :=
      ((hlimΔ τ hIcc 1 0 (by norm_num) z hz).div_const z).sub
        ((hlimΔ τ hIcc 1 0 (by norm_num) z' hz').div_const z')
    have hM2 : |Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') z θ / z
          - Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') z' θ / z'|
        ≤ 2 * (c * ((max L₀ 0) * τ)) * |1 / z - 1 / z'| :=
      le_of_tendsto' hlim2.abs (fun n => hn n)
    rw [hderiv_of τ hIcc hτ.1 z hz, hderiv_of τ hIcc hτ.1 z' hz']
    have hsplit : Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') z θ / (z * τ)
          - Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') z' θ / (z' * τ)
        = (Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') z θ / z
          - Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
            - Work.FTS.Galerkin.slice g 0 z θ') z' θ / z') / τ := by
      field_simp
    rw [hsplit, abs_div, abs_of_pos hτ.1]
    calc |Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
              - Work.FTS.Galerkin.slice g 0 z θ') z θ / z
            - Work.Spaces.mixed 1 0 (fun z θ' => Work.FTS.Galerkin.slice g τ z θ'
              - Work.FTS.Galerkin.slice g 0 z θ') z' θ / z'| / τ
        ≤ (2 * (c * ((max L₀ 0) * τ)) * |1 / z - 1 / z'|) / τ :=
          div_le_div_of_nonneg_right hM2 hτ.1.le
      _ = 2 * c * (max L₀ 0) * |1 / z - 1 / z'| := by
            have hτne : τ ≠ 0 := ne_of_gt hτ.1
            field_simp
  exact ⟨max L₀ 0, le_max_right _ _, hconj1, hconj2⟩

end Work.FTS_RegExport.RXR1
