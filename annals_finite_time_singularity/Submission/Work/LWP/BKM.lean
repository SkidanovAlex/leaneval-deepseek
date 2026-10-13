/-
# `Work.LWP.BKM` — item 3: the Beale–Kato–Majda continuation criterion

The BKM criterion itself is the named input `BKMExtension` of `Work.LWP.Inputs`:

  a solution on `[0,T)` whose BKM integral stays bounded as `t ↑ T` extends past `T`.

This module delivers the pieces of item 3 that are *provable* from it, i.e. the conversion of
the criterion into the shape the main theorem needs — a solution on `[0,T)` with
`∫₀ᵗ‖ω(·,s)‖_{L∞} ds → ∞` at `T⁻`:

* `Work.LWP.tendsto_atTop_nhdsLT_of_monotoneOn` — for a function monotone on `[0,T)`,
  unboundedness above on `[0,T)` is exactly divergence at `T⁻`;
* `Work.LWP.exists_bound_of_not_tendsto_atTop` — its contrapositive form: a monotone function
  which does *not* diverge is bounded on `[0,T)`;
* `Work.LWP.bkm_bound_of_integrable` — a finite Lebesgue integral over `(0,T)` bounds the
  BKM integral on `[0,T)` (the form in which the criterion is stated in the paper);
* `Work.LWP.bkm_divergence_of_maximal` — **the main result of item 3**: if the criterion holds
  and `(p,u)` is a maximal solution on `[0,T)`, then its BKM integral diverges at `T`;
* `Work.LWP.bkm_divergence_of_maximal_one` — the `T = 1` instance, which is *literally* the
  blow-up clause of the main theorem.

The analytic content behind `BKMExtension` — the logarithmic Calderón–Zygmund estimate for
`∇u = ∇(-Δ)^{-1}(∇×ω)` and the logarithmic Grönwall inequality
`Work.LWP.BKM.gronwall_log` (in `Submission/Work/LWP/BKM/`) — is not available in Mathlib and is
recorded in `NOTES.md`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.LWP.Inputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-! ## Divergence at the left endpoint -/

/-- `Ioo t T` is a neighbourhood of `T` in the filter `𝓝[<] T` (for `t < T`). -/
theorem Ioo_mem_nhdsWithin_Iio' {t T : ℝ} (h : t < T) : Ioo t T ∈ 𝓝[<] T := by
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨Ioi t, isOpen_Ioi.mem_nhds h, ?_⟩
  rintro x ⟨hxt, hxT⟩
  exact ⟨hxt, hxT⟩

/-- **Characterisation of divergence at the left endpoint for a monotone function.**
A function monotone on `[0,T)` tends to `atTop` along `𝓝[<] T` exactly when it is unbounded above
on `[0,T)`. (Note that the limit is a real number only in the "diverges" sense: `atTop` on `ℝ`
has no top element, so this says `∀ a, ∃ t < T, a ≤ f t`.) -/
theorem tendsto_atTop_nhdsLT_iff_of_monotoneOn {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : MonotoneOn f (Ico 0 T)) :
    Tendsto f (𝓝[<] T) atTop ↔ ∀ a : ℝ, ∃ t ∈ Ico 0 T, a ≤ f t := by
  constructor
  · intro h a
    have hev : ∀ᶠ x in 𝓝[<] T, a ≤ f x := tendsto_atTop.1 h a
    obtain ⟨v, hv, hvs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
    obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.mp hv
    -- the point `t` below `T`, but still `≥ 0`, and inside the ball around `T`
    have hmax : max (T - ε / 2) 0 < T := max_lt (by linarith) hT
    set t : ℝ := (max (T - ε / 2) 0 + T) / 2 with htdef
    have ht0 : 0 ≤ t := by
      simp only [htdef]
      linarith [le_max_right (T - ε / 2) 0]
    have htT : t < T := by
      simp only [htdef]; linarith [hmax]
    have htv : t ∈ v := by
      apply hεv
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith : t - T < 0)]
      have : T - ε / 4 ≤ t := by
        simp only [htdef]; linarith [le_max_left (T - ε / 2) 0]
      linarith
    exact ⟨t, ⟨ht0, htT⟩, hvs ⟨htv, htT⟩⟩
  · intro h
    rw [tendsto_atTop]
    intro b
    obtain ⟨t, ht, htle⟩ := h b
    refine Filter.mem_of_superset (Ioo_mem_nhdsWithin_Iio' ht.2) ?_
    rintro x ⟨hxt, hxT⟩
    have hx0 : 0 ≤ x := le_trans ht.1 (le_of_lt hxt)
    have : f t ≤ f x := hf ht ⟨hx0, hxT⟩ (le_of_lt hxt)
    exact le_trans htle this

/-- **Contrapositive form**: a function monotone on `[0,T)` which does not diverge at `T⁻` is
bounded above on `[0,T)`. -/
theorem exists_bound_of_not_tendsto_atTop {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : MonotoneOn f (Ico 0 T)) (h : ¬ Tendsto f (𝓝[<] T) atTop) :
    ∃ a : ℝ, ∀ t ∈ Ico 0 T, f t ≤ a := by
  rw [tendsto_atTop_nhdsLT_iff_of_monotoneOn hT hf] at h
  push Not at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun t ht => le_of_lt (ha t ht)⟩

/-! ## The BKM integral -/

/-- A finite Lebesgue integral of a non-negative function on `(0,T)` bounds its interval integrals
on `[0,T)`.  This is the bridge between the paper's formulation of the Beale–Kato–Majda criterion
(`∫₀^T ‖ω(·,s)‖_{L∞} ds < ∞`) and the form in which `BKMExtension` uses it. -/
theorem bkm_bound_of_integrable {f : ℝ → ℝ} {T : ℝ}
    (hint : IntegrableOn f (Ioc 0 T)) (hnn : ∀ x, 0 ≤ f x) :
    ∃ M : ℝ, ∀ t ∈ Ico 0 T, (∫ s in 0..t, f s) ≤ M := by
  refine ⟨∫ s in Ioc 0 T, f s, fun t ht => ?_⟩
  rw [intervalIntegral.integral_of_le ht.1]
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall hnn)
    (Filter.Eventually.of_forall fun x hx => ⟨hx.1, le_trans hx.2 (le_of_lt ht.2)⟩)

/-! ## Divergence of the BKM integral at a maximal time -/

/-- **The Beale–Kato–Majda continuation criterion**, in the integrated form used by the paper:
a solution on `[0,T)` whose vorticity is integrable in space-time up to `T` extends past `T`. -/
theorem bkm_continuation {α : NNReal} (hBKM : BKMExtension α)
    {u₀ : R3 → R3} {T : ℝ} {p : R3 → ℝ → ℝ} {u : R3 → ℝ → R3}
    (hsol : IsLocalEulerEquationSolution p u₀ T u)
    (hst : ∀ S ∈ Ioo 0 T, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 S))
    (hint : IntegrableOn (fun s => ⨆ x, ‖vorticity (fun y => u y s) x‖) (Ioc 0 T))
    (hnn : ∀ s, 0 ≤ ⨆ x, ‖vorticity (fun y => u y s) x‖) :
    ∃ T' : ℝ, T < T' ∧ ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
      IsLocalEulerEquationSolution p' u₀ T' u' ∧ ExtendsField u u' T :=
  hBKM u₀ T p u hsol hst (bkm_bound_of_integrable hint hnn)

/-- **Item 3, main result: the BKM integral of a maximal solution diverges at the maximal time.**

Suppose the Beale–Kato–Majda criterion `BKMExtension` holds, and let `(p,u)` be a solution on
`[0,T)` which cannot be extended past `T` (a `MaximalSolution`).  If the BKM integral
`bkm u t = ∫₀ᵗ ⨆ₓ‖ω(x,s)‖ ds` stayed bounded as `t ↑ T`, the criterion would extend the solution
past `T`, contradicting maximality.  Hence it diverges.

The monotonicity hypothesis is automatic whenever the vorticity is bounded on `[0,T)`
(`Work.LWP.bkm_monoOn`); it is kept explicit so that this conversion does not depend on an
integrability statement about the vorticity. -/
theorem bkm_divergence_of_maximal {α : NNReal} (hBKM : BKMExtension α)
    {u₀ : R3 → R3} {T : ℝ} (hmax : MaximalSolution α u₀ T)
    (hmono : MonotoneOn (bkm hmax.u) (Ico 0 T)) :
    Tendsto (bkm hmax.u) (𝓝[<] T) atTop := by
  by_contra hcon
  obtain ⟨M, hM⟩ := exists_bound_of_not_tendsto_atTop hmax.T_pos hmono hcon
  obtain ⟨T', hT', p', u', hsol', hext⟩ :=
    hBKM u₀ T hmax.p hmax.u hmax.sol hmax.spacetime ⟨M, hM⟩
  exact hmax.maximal ⟨T', hT', p', u', hsol', hext⟩

/-- **The `T = 1` instance**, in exactly the shape used by the main theorem: the solution exists
on `[0,1)`, is odd at every time, is jointly `C^{1,α}` on every compact strip, and
`∫₀ᵗ ⨆ₓ‖ω(x,s)‖ ds → ∞` as `t → 1⁻`. -/
theorem bkm_divergence_of_maximal_one {α : NNReal} (hBKM : BKMExtension α)
    {u₀ : R3 → R3} (hmax : MaximalSolution α u₀ 1)
    (hmono : MonotoneOn (bkm hmax.u) (Ico 0 1)) :
    IsLocalEulerEquationSolution hmax.p u₀ 1 hmax.u ∧
      (∀ t ∈ Ico 0 1, IsOdd (hmax.u · t)) ∧
      (∀ T ∈ Ioo 0 1, IsContDiffHolderOn ℝ α hmax.u.uncurry (univ ×ˢ Icc 0 T)) ∧
      Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => hmax.u y s) x‖)
        (𝓝[<] 1) atTop :=
  ⟨hmax.sol, hmax.odd, hmax.spacetime, bkm_divergence_of_maximal hBKM hmax hmono⟩


/-! ## Monotonicity of the BKM integral -/

/-- **Monotonicity of `bkm u` on `[0,T)`.**  As soon as the integrand
`s ↦ ⨆ x, ‖ω(x,s)‖` is non-negative and integrable on `(0,t)` for every `t < T`, the BKM integral
is non-decreasing.  This is the hypothesis under which `bkm_divergence_of_maximal` applies. -/
theorem bkm_monoOn {u : R3 → ℝ → R3} {T : ℝ} (_hT : 0 ≤ T)
    (hnn : ∀ s, 0 ≤ (⨆ x, ‖vorticity (fun y => u y s) x‖))
    (h : ∀ t ∈ Ico 0 T, IntegrableOn (fun s => ⨆ x, ‖vorticity (fun y => u y s) x‖)
      (Ioc 0 t)) :
    MonotoneOn (bkm u) (Ico 0 T) := by
  intro a ha b hb hab
  simp only [bkm]
  rw [intervalIntegral.integral_of_le ha.1, intervalIntegral.integral_of_le hb.1]
  exact setIntegral_mono_set (h b hb) (Filter.Eventually.of_forall hnn)
    (Filter.Eventually.of_forall fun x hx => ⟨hx.1, le_trans hx.2 hab⟩)


/-- `bkm` is *definitionally* the expression appearing in the challenge's statement. -/
theorem bkm_eq_challenge_integral (u : R3 → ℝ → R3) (t : ℝ) :
    bkm u t = ∫ s in 0..t, ⨆ x, ‖(vorticity (u · s)) x‖ := rfl

/-- **The `T = 1` consumer shape without the monotonicity side condition**: it is enough that the
vorticity sup-norm is non-negative and integrable on `(0,t)` for every `t < 1`, which is the
situation of the assembly's construction. -/
theorem bkm_divergence_of_maximal_one_of_integrable {α : NNReal} (hBKM : BKMExtension α)
    {u₀ : R3 → R3} (hmax : MaximalSolution α u₀ 1)
    (hnn : ∀ s, 0 ≤ (⨆ x, ‖vorticity (fun y => hmax.u y s) x‖))
    (hint : ∀ t ∈ Ico 0 1,
      IntegrableOn (fun s => ⨆ x, ‖vorticity (fun y => hmax.u y s) x‖) (Ioc 0 t)) :
    IsLocalEulerEquationSolution hmax.p u₀ 1 hmax.u ∧
      (∀ t ∈ Ico 0 1, IsOdd (hmax.u · t)) ∧
      (∀ T ∈ Ioo 0 1, IsContDiffHolderOn ℝ α hmax.u.uncurry (univ ×ˢ Icc 0 T)) ∧
      Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => hmax.u y s) x‖)
        (𝓝[<] 1) atTop :=
  bkm_divergence_of_maximal_one hBKM hmax (bkm_monoOn (T := 1) zero_le_one hnn hint)

end Work.LWP
