import Mathlib
import Submission.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Work.SimplyConnected.ABS.poleConstant_deriv
import Submission.Work.SimplyConnected.ABS.exists_holomorphic_div_of_logPole
import Submission.Work.SimplyConnected.ABS.subharmonicOnX_norm_of_holomorphic
import Submission.MaxPrincipleX
import Submission.Work.Modulus.Unsatisfiable

/-!
# The rigidity of the extremal maximiser, without any decay hypothesis

Let `E` be a positive harmonic function on `X ∖ {x₀}` with a *unit* logarithmic pole at `x₀` which
dominates the extremal family at `x₀` (`‖g x‖ ≤ exp (-(E x))`), and suppose `E` has a holomorphic
*modulus* `Φ` (holomorphic on `X`, simple zero at `x₀`, `‖Φ x‖ = exp (-(E x))` off `x₀`).

Then every member `f` of the extremal family which *maximises* the chart derivative at `x₀` attains
the envelope:

  `‖f x‖ = exp (-(E x))`  for all `x ≠ x₀`

(`rigidity_of_maximizer_of_modulus`).  This is Ahlfors' rigidity, and it is the step that converts
the (open) modulus problem into the Green-modulus identity; no decay of `E` at the ideal boundary
and no relative compactness of the superlevel sets is used.

## The proof, and the two limits at the pole

* `Φ ∈ 𝔽_{x₀}` (it is bounded by `1` and vanishes at `x₀`), so the maximality of `f` gives
  `‖Φ'(x₀)‖ ≤ ‖f'(x₀)‖`.
* The domination `‖f x‖ ≤ exp (-(E x))`, divided by `‖ζ‖` and passed to the limit `x → x₀`, gives
  `‖f'(x₀)‖ ≤ exp (-c)`, where `c` is the pole constant of `E` (`exists_poleConstant`).
* The derivative of the modulus is `‖Φ'(x₀)‖ = exp (-c)`
  (`norm_deriv_modulus_eq_exp_neg_poleConstant`).
  Hence `‖f'(x₀)‖ = ‖Φ'(x₀)‖ = exp (-c)`, i.e. the quotient `R := f / Φ` has `‖R x₀‖ = 1`.
* `R` extends holomorphically to `X` (`exists_holomorphic_div_of_logPole`) and `‖R‖ ≤ 1` off
  `x₀` by the domination, so `‖R‖` is a subharmonic function with a maximum at `x₀`: the strong
  maximum principle (`SubharmonicOnX.eq_of_isMaxOn`) gives `‖R‖ ≡ 1`, whence the rigidity.

The two pointwise limits at the pole are `tendsto_norm_div_sub_of_hasDerivAt` (the slope of a
holomorphic function vanishing at the base point) and the arithmetic of `exp`/`log`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}

/-- **The norm of the slope tends to the norm of the derivative.**  For `F` holomorphic at `a` with
`F a = 0` one has `‖F w‖ / ‖w - a‖ → ‖F'(a)‖` as `w → a`, `w ≠ a`. -/
theorem tendsto_norm_div_sub_of_hasDerivAt {F : ℂ → ℂ} {a : ℂ}
    (h : HasDerivAt F (deriv F a) a) (h0 : F a = 0) :
    Filter.Tendsto (fun w : ℂ => ‖F w‖ / ‖w - a‖) (𝓝[≠] a) (𝓝 ‖deriv F a‖) := by
  have h1 : Filter.Tendsto (fun w : ℂ => ‖slope F a w‖) (𝓝[≠] a) (𝓝 ‖deriv F a‖) :=
    h.tendsto_slope.norm
  refine h1.congr' ?_
  filter_upwards with w
  rw [slope_def_field, h0, sub_zero, norm_div]

/-- **The upper bound at the pole.**  If `E` has pole constant `c` at `x₀` and dominates `f`, then
`‖f'(x₀)‖ ≤ exp (-c)` (chart derivative at `x₀`). -/
theorem norm_deriv_le_exp_neg_poleConstant {E : X → ℝ} {f : X → ℂ}
    (hfhol : Submission.HolomorphicOnX f Set.univ) (hf0 : f x₀ = 0)
    (hdom : ∀ x : X, x ≠ x₀ → ‖f x‖ ≤ Real.exp (-(E x)))
    {c : ℝ}
    (hc : Filter.Tendsto
      (fun w : ℂ => E ((chartAt ℂ x₀).symm w) + Real.log ‖w - (chartAt ℂ x₀) x₀‖)
      (𝓝[≠] ((chartAt ℂ x₀) x₀)) (𝓝 c)) :
    ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤ Real.exp (-c) := by
  set a : ℂ := (chartAt ℂ x₀) x₀ with ha
  set F : ℂ → ℂ := f ∘ (chartAt ℂ x₀).symm with hF
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hsymm : (chartAt ℂ x₀).symm a = x₀ := by
    rw [ha]; exact (chartAt ℂ x₀).left_inv hsrc
  have hFa : AnalyticAt ℂ F a := hfhol x₀ (mem_univ x₀)
  have hF0 : F a = 0 := by
    simp only [hF, Function.comp_apply, hsymm]
    exact hf0
  have hderiv : HasDerivAt F (deriv F a) a := hFa.differentiableAt.hasDerivAt
  have hS := tendsto_norm_div_sub_of_hasDerivAt hderiv hF0
  have hR : Filter.Tendsto (fun w : ℂ => Real.exp (-(E ((chartAt ℂ x₀).symm w)
      + Real.log ‖w - a‖))) (𝓝[≠] a) (𝓝 (Real.exp (-c))) :=
    (Real.continuous_exp.tendsto (-c)).comp hc.neg
  refine le_of_tendsto_of_tendsto hS hR ?_
  have hball₀ : ∀ᶠ w : ℂ in 𝓝 ((chartAt ℂ x₀) x₀), w ∈ (chartAt ℂ x₀).target :=
    IsOpen.mem_nhds (chartAt ℂ x₀).open_target ((chartAt ℂ x₀).map_source hsrc)
  have hball : ∀ᶠ w : ℂ in 𝓝[≠] a, w ∈ (chartAt ℂ x₀).target :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hball₀
  filter_upwards [self_mem_nhdsWithin, hball] with w hwne hwt
  have hna : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
  have hne : (chartAt ℂ x₀).symm w ≠ x₀ := by
    intro hcon
    have h1 : w = a := by
      have h2 : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = w := (chartAt ℂ x₀).right_inv hwt
      rw [hcon] at h2
      rw [← ha] at h2
      exact h2.symm
    exact hwne h1
  have hstep : ‖F w‖ / ‖w - a‖
      ≤ Real.exp (-(E ((chartAt ℂ x₀).symm w))) / ‖w - a‖ :=
    div_le_div_of_nonneg_right (hdom ((chartAt ℂ x₀).symm w) hne) hna.le
  have harith : Real.exp (-(E ((chartAt ℂ x₀).symm w))) / ‖w - a‖
      = Real.exp (-(E ((chartAt ℂ x₀).symm w) + Real.log ‖w - a‖)) := by
    have h1 : -(E ((chartAt ℂ x₀).symm w) + Real.log ‖w - a‖)
        = -(E ((chartAt ℂ x₀).symm w)) + -(Real.log ‖w - a‖) := by ring
    rw [h1, Real.exp_add, div_eq_mul_inv]
    congr 1
    rw [Real.exp_neg, Real.exp_log hna]
  rw [← harith]
  exact hstep

/-- **The modulus is a member of the extremal family** (bounded by `1`, vanishes at the pole), from
the positivity of `E` off the pole. -/
theorem modulus_mem_extremalFamily' {E : X → ℝ} {Φ : X → ℂ}
    (hΦhol : Submission.HolomorphicOnX Φ Set.univ) (hΦpole : Submission.HasLogPoleAt x₀ Φ)
    (hEpos : ∀ x : X, x ≠ x₀ → 0 < E x)
    (hΦmod : ∀ x : X, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x))) :
    Φ ∈ Submission.extremalFamily x₀ := by
  have hzero : Φ x₀ = 0 := Submission.phi_zero_of_logPole hΦhol hΦpole
  refine ⟨hΦhol, fun x => ?_, hzero⟩
  by_cases hx : x = x₀
  · subst hx
    rw [hzero, norm_zero]
    norm_num
  · rw [hΦmod x hx]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hEpos x hx).le)

/-- **Ahlfors' rigidity, decay-free.**  Under the hypotheses above, a maximiser `f` of the chart
derivative at `x₀` attains the envelope `E` off the pole. -/
theorem rigidity_of_maximizer_of_modulus {E : X → ℝ} {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hmax : ∀ g ∈ Submission.extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hEpos : ∀ x : X, x ≠ x₀ → 0 < E x)
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {x₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {x₀}) x₀ E)
    (hdom : ∀ x : X, x ≠ x₀ → ‖f x‖ ≤ Real.exp (-(E x)))
    (hmod : ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧
      Submission.HasLogPoleAt x₀ Φ ∧ (∀ x : X, x ≠ x₀ → ‖Φ x‖ = Real.exp (-(E x)))) :
    ∀ x : X, x ≠ x₀ → ‖f x‖ = Real.exp (-(E x)) := by
  classical
  obtain ⟨Φ, hΦhol, hΦpole, hΦmod⟩ := hmod
  have hΦmem : Φ ∈ Submission.extremalFamily x₀ :=
    modulus_mem_extremalFamily' hΦhol hΦpole hEpos hΦmod
  have hΦne : ∀ x : X, x ≠ x₀ → Φ x ≠ 0 := fun x hx h0 =>
    (Real.exp_ne_zero (-(E x))) ((hΦmod x hx).symm.trans (by rw [h0, norm_zero]))
  -- ## the pole constant
  obtain ⟨c, hc⟩ := exists_poleConstant (x₀ := x₀) hEharm hpole
  -- ## the derivative of the modulus
  have hΦderiv : ‖deriv (Φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ = Real.exp (-c) :=
    norm_deriv_modulus_eq_exp_neg_poleConstant (x₀ := x₀) hΦhol
      (Submission.phi_zero_of_logPole hΦhol hΦpole) hΦmod
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (IsOpen.mem_nhds (chartAt ℂ x₀).open_target
          ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)))) hc
  -- ## the two bounds on the derivative of `f`
  have hfle : ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤ Real.exp (-c) :=
    norm_deriv_le_exp_neg_poleConstant (x₀ := x₀) hf.1 hf.2.2 hdom hc
  have hfge : Real.exp (-c) ≤ ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
    rw [← hΦderiv]
    exact hmax Φ hΦmem
  have hfeq : ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ = Real.exp (-c) :=
    le_antisymm hfle hfge
  -- ## the quotient `R := f / Φ` extends holomorphically to `X`
  obtain ⟨R, hRhol, hRval⟩ := exists_holomorphic_div_of_logPole (x₀ := x₀) hf hΦhol hΦpole hΦne
  -- ## the limits of the two slope norms at the pole
  set a : ℂ := (chartAt ℂ x₀) x₀ with ha
  have hsrc : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hsymm : (chartAt ℂ x₀).symm a = x₀ := by
    rw [ha]; exact (chartAt ℂ x₀).left_inv hsrc
  have hfslope : Filter.Tendsto
      (fun w : ℂ => ‖f ((chartAt ℂ x₀).symm w)‖ / ‖w - a‖) (𝓝[≠] a) (𝓝 (Real.exp (-c))) := by
    have h0 : (f ∘ (chartAt ℂ x₀).symm) a = 0 := by
      simp only [Function.comp_apply, hsymm]; exact hf.2.2
    have h := tendsto_norm_div_sub_of_hasDerivAt
      ((hf.1 x₀ (mem_univ x₀)).differentiableAt.hasDerivAt) h0
    rw [hfeq] at h
    exact h
  have hΦslope : Filter.Tendsto
      (fun w : ℂ => ‖Φ ((chartAt ℂ x₀).symm w)‖ / ‖w - a‖) (𝓝[≠] a) (𝓝 (Real.exp (-c))) := by
    have h0 : (Φ ∘ (chartAt ℂ x₀).symm) a = 0 := by
      simp only [Function.comp_apply, hsymm]
      exact Submission.phi_zero_of_logPole hΦhol hΦpole
    have h := tendsto_norm_div_sub_of_hasDerivAt
      ((hΦhol x₀ (mem_univ x₀)).differentiableAt.hasDerivAt) h0
    rw [hΦderiv] at h
    exact h
  -- ## their quotient tends to `1`
  have hquot : Filter.Tendsto
      (fun w : ℂ => ‖f ((chartAt ℂ x₀).symm w)‖ / ‖Φ ((chartAt ℂ x₀).symm w)‖)
      (𝓝[≠] a) (𝓝 1) := by
    have hdiv : Filter.Tendsto
        (fun w : ℂ => (‖f ((chartAt ℂ x₀).symm w)‖ / ‖w - a‖)
          / (‖Φ ((chartAt ℂ x₀).symm w)‖ / ‖w - a‖)) (𝓝[≠] a)
        (𝓝 (Real.exp (-c) / Real.exp (-c))) :=
      hfslope.div hΦslope (Real.exp_ne_zero _)
    have hone : Real.exp (-c) / Real.exp (-c) = 1 := div_self (Real.exp_ne_zero _)
    rw [hone] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hwne
    have hna : ‖w - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwne)
    field_simp
  -- ## transport to `X`
  have hquotX : Filter.Tendsto (fun x : X => ‖f x‖ / ‖Φ x‖) (𝓝[≠] x₀) (𝓝 1) := by
    have hsrc₀ : ∀ᶠ x : X in 𝓝 x₀, x ∈ (chartAt ℂ x₀).source :=
      IsOpen.mem_nhds (chartAt ℂ x₀).open_source hsrc
    have hsrc_nhds : ∀ᶠ x : X in 𝓝[≠] x₀, x ∈ (chartAt ℂ x₀).source :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hsrc₀
    have hc' : Filter.Tendsto (chartAt ℂ x₀) (𝓝[≠] x₀) (𝓝[≠] (chartAt ℂ x₀) x₀) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨(((chartAt ℂ x₀).continuousAt hsrc).tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin, hsrc_nhds] with x hxne hxsrc
      intro hcon
      exact hxne ((chartAt ℂ x₀).injOn hxsrc hsrc (hcon.trans ha))
    have hc2 := hquot.comp hc'
    refine hc2.congr' ?_
    filter_upwards [hsrc_nhds] with x hxsrc
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x₀).left_inv hxsrc]
  -- ## `‖R x₀‖ = 1`
  have hRlim1 : Filter.Tendsto (fun x : X => ‖R x‖) (𝓝[≠] x₀) (𝓝 1) := by
    refine hquotX.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hxne
    rw [hRval x hxne, norm_div]
  have hRlim2 : Filter.Tendsto (fun x : X => ‖R x‖) (𝓝[≠] x₀) (𝓝 ‖R x₀‖) :=
    (((Submission.HolomorphicOnXAt.continuousAt (hRhol x₀ (mem_univ x₀))).norm).tendsto).mono_left
      nhdsWithin_le_nhds
  haveI hneBot : (𝓝[≠] x₀).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    rw [mem_closure_iff]
    intro U hU hxU
    obtain ⟨y, hyU, hyne⟩ := Work.Modulus.exists_ne_of_mem_nhds (hU.mem_nhds hxU)
    exact ⟨y, hyU, hyne⟩
  have hR0 : ‖R x₀‖ = 1 := tendsto_nhds_unique hRlim2 hRlim1
  -- ## `‖R‖ ≤ 1` and the maximum principle
  have hRle : ∀ x : X, ‖R x‖ ≤ 1 := by
    intro x
    by_cases hx : x = x₀
    · rw [hx, hR0]
    · rw [hRval x hx, norm_div, hΦmod x hx]
      exact div_le_one_of_le₀ (hdom x hx) (Real.exp_pos _).le
  have hRsub : Submission.SubharmonicOnX (fun x : X => ‖R x‖) Set.univ :=
    subharmonicOnX_norm_of_holomorphic hRhol
  have hRconst : ∀ x : X, ‖R x‖ = 1 := by
    have hmax' : ∀ x : X, ‖R x‖ ≤ ‖R x₀‖ := by
      intro x
      rw [hR0]
      exact hRle x
    have h := Submission.SubharmonicOnX.eq_of_isMaxOn hRsub hmax'
    intro x
    rw [h x, hR0]
  -- ## conclude
  intro x hx
  have h1 : f x = R x * Φ x := by
    rw [hRval x hx, div_mul_cancel₀ (f x) (hΦne x hx)]
  rw [h1, norm_mul, hRconst x, one_mul, hΦmod x hx]

namespace Work.SimplyConnected.ABS


/-- **A simple zero factorizes.**  If `F` is analytic at `a`, vanishes there and has non-zero
derivative, then `F w = (w - a) * H w` near `a` with `H` analytic at `a` and `H a ≠ 0`. -/
theorem exists_simpleZero_factorization {a : ℂ} {F : ℂ → ℂ} (hana : AnalyticAt ℂ F a)
    (h0 : F a = 0) (hd : deriv F a ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧ H a ≠ 0 ∧ (∀ᶠ w in 𝓝 a, F w = (w - a) * H w) := by
  have hnotzero : ¬ ∀ᶠ w in 𝓝 a, F w = 0 := by
    intro h
    have heq : Filter.EventuallyEq (𝓝 a) F (fun _ : ℂ => 0) := h
    have hd0 : deriv F a = 0 := by
      rw [heq.deriv_eq]
      simp
    exact hd hd0
  obtain ⟨k, g, hgana, hgne, hgeq⟩ := hana.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
  have hge : Filter.EventuallyEq (𝓝 a) F (fun w : ℂ => (w - a) ^ k * g w) := by
    filter_upwards [hgeq] with w hw
    simpa [smul_eq_mul] using hw
  have hk1 : 1 ≤ k := by
    have hval : F a = (a - a) ^ k * g a := hge.self_of_nhds
    by_contra h
    have hk0 : k = 0 := Nat.lt_one_iff.mp (not_le.mp h)
    rw [hk0, pow_zero, one_mul] at hval
    exact hgne (hval.symm.trans h0)
  have hk : k = 1 := by
    by_contra hk
    have hk2 : 2 ≤ k := by
      have h1 : 1 < k := Nat.lt_of_le_of_ne hk1 (fun h => hk h.symm)
      omega
    have hder : deriv F a = deriv (fun w : ℂ => (w - a) ^ k * g w) a := hge.deriv_eq
    have hz : deriv (fun w : ℂ => (w - a) ^ k * g w) a = 0 := by
      have hfac : (fun w : ℂ => (w - a) ^ k * g w)
          = fun w : ℂ => (w - a) ^ 2 * ((w - a) ^ (k - 2) * g w) := by
        funext w
        have hpow : (w - a) ^ k = (w - a) ^ 2 * (w - a) ^ (k - 2) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hpow]
        ring
      rw [hfac]
      have hd1 : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ 2) a :=
        (differentiableAt_id.sub (differentiableAt_const a)).pow 2
      have hd2 : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ (k - 2) * g w) a :=
        ((differentiableAt_id.sub (differentiableAt_const a)).pow _).mul hgana.differentiableAt
      change deriv ((fun w : ℂ => (w - a) ^ 2) * (fun w : ℂ => (w - a) ^ (k - 2) * g w)) a = 0
      rw [deriv_mul hd1 hd2]
      have h1 : deriv (fun w : ℂ => (w - a) ^ 2) a = 0 := by
        have hda : DifferentiableAt ℂ (fun w : ℂ => w - a) a :=
          differentiableAt_id.sub (differentiableAt_const a)
        have hp := deriv_pow hda 2
        change deriv ((fun w : ℂ => w - a) ^ 2) a = 0
        rw [hp]
        simp
      have h2 : (a - a) ^ 2 = 0 := by ring
      rw [h1, zero_mul, h2, zero_mul, add_zero]
    rw [hz] at hder
    exact hd hder
  refine ⟨g, hgana, hgne, ?_⟩
  filter_upwards [hge] with w hw
  rw [hw, hk, pow_one]

end Work.SimplyConnected.ABS
