import Mathlib
import Submission.Work.Modular.Lattice

namespace Work.Modular

open Work.Modular
open Filter Topology
open UpperHalfPlane

/-!
# The theta series at the cusp `i∞`

For a discrete submodule `L ⊆ ℝⁿ` (a lattice of possibly non-full rank) the theta series
`Θ_L τ = ∑_{x ∈ L} exp (π i τ ‖x‖²)` tends to `1` as `τ` tends to the cusp `i∞`: the summand
at `x = 0` equals `1`, and every other summand decays like `exp (-π (Im τ) ‖x‖²)`, uniformly
in `τ` once `Im τ ≥ 1`.

The estimate is the following.  Since `L` is discrete, `0` is isolated in `L`, so there is a
separation constant `δ > 0` with `‖x‖ ≥ δ` for every nonzero `x ∈ L`.  Writing `y = Im τ ≥ 1`
and splitting `π y ‖x‖² = π y ‖x‖²/2 + π y ‖x‖²/2`, the two halves are bounded by
`exp (-π δ² y / 2)` (because `‖x‖ ≥ δ`) and by `exp (-π ‖x‖²/2)` (because `y ≥ 1`); hence the
whole tail of the series is at most `exp (-π δ² y / 2) · ∑_{x ∈ L} exp (-π ‖x‖²/2)`, and the
constant multiplying the exponential is finite because the Gaussian series over a discrete
lattice converges (`summable_exp_neg_mul_norm_sq` below).

## Main results

* `Work.Modular.exists_pos_le_norm_of_discrete`: the separation constant of a discrete lattice.
* `Work.Modular.summable_exp_neg_mul_norm_sq`: `∑_{x ∈ L} exp (-c ‖x‖²)` converges for `c > 0`.
* `Work.Modular.thetaSeries_atImInfty`: `Θ_L τ → 1` as `τ → i∞`.
-/

/-- A discrete submodule `L ⊆ ℝⁿ` is *separated*: there is `δ > 0` with `‖x‖ ≥ δ` for every
nonzero `x ∈ L`.  Indeed `{0}` is open in the discrete space `L`, so some ball around `0` meets
`L` only in `0`. -/
theorem exists_pos_le_norm_of_discrete {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : L, x ≠ 0 → δ ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (IsOpen.mem_nhds (isOpen_discrete ({0} : Set L)) (Set.mem_singleton 0))
  refine ⟨ε, hε, fun x hx => ?_⟩
  by_contra h
  have h1 : x ∈ Metric.ball (0 : L) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_not_ge h
  exact hx (by simpa using hball h1)

/-- The Gaussian series over a discrete lattice converges: `∑_{x ∈ L} exp (-c ‖x‖²) < ∞` for
every `c > 0`.

For the proof, let `m = finrank ℤ L + 1`; by `ZLattice.summable_norm_pow_inv` the series
`∑_{x ∈ L} ‖x‖^{-m}` converges, and outside `x = 0` (an exceptional set of finite measure for
`Summable`) the separation constant `δ` gives
`exp (-c ‖x‖²) ≤ exp (-c δ ‖x‖) ≤ m! / (c δ)^m · ‖x‖^{-m}`,
where the last inequality is `m! ≤ (c δ ‖x‖)^m exp (c δ ‖x‖)`, a consequence of the Taylor
series of `exp`. -/
theorem summable_exp_neg_mul_norm_sq {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] {c : ℝ} (hc : 0 < c) :
    Summable (fun x : L => Real.exp (-c * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_of_discrete L
  set m : ℕ := Module.finrank ℤ L + 1 with hm
  have hpoly : Summable (fun z : L => ‖z‖⁻¹ ^ m) :=
    ZLattice.summable_norm_pow_inv L m (by omega)
  have hK : Summable (fun z : L => (m.factorial : ℝ) / (c * δ) ^ m * ‖z‖⁻¹ ^ m) :=
    hpoly.mul_left _
  refine Summable.of_norm_bounded_eventually hK ?_
  filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton (0 : L))] with z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  have hzt : δ ≤ ‖z‖ := hsep z hz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hδ hzt
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Submodule.norm_coe]
  have h1 : -c * ‖z‖ ^ 2 ≤ -(c * δ * ‖z‖) := by
    nlinarith [mul_nonneg hc.le (mul_nonneg (sub_nonneg.mpr hzt) hzpos.le)]
  have h2 : ((c * δ * ‖z‖) ^ m) / (m.factorial : ℝ) ≤ Real.exp (c * δ * ‖z‖) :=
    Real.pow_div_factorial_le_exp (c * δ * ‖z‖) (by positivity) m
  have h3 : (Real.exp (c * δ * ‖z‖))⁻¹ ≤ (m.factorial : ℝ) / (c * δ * ‖z‖) ^ m := by
    rw [← one_div]
    have h := one_div_le_one_div_of_le
      (a := (c * δ * ‖z‖) ^ m / (m.factorial : ℝ)) (by positivity) h2
    rwa [one_div_div] at h
  have h4 : (m.factorial : ℝ) / (c * δ * ‖z‖) ^ m
      = (m.factorial : ℝ) / (c * δ) ^ m * ‖z‖⁻¹ ^ m := by
    rw [mul_pow, inv_pow]
    field_simp
  calc Real.exp (-c * ‖z‖ ^ 2)
      ≤ Real.exp (-(c * δ * ‖z‖)) := Real.exp_le_exp.mpr h1
    _ = (Real.exp (c * δ * ‖z‖))⁻¹ := Real.exp_neg _
    _ ≤ (m.factorial : ℝ) / (c * δ * ‖z‖) ^ m := h3
    _ = (m.factorial : ℝ) / (c * δ) ^ m * ‖z‖⁻¹ ^ m := h4

/-- The modulus of the summand `exp (π i τ ‖x‖²)` of the theta series is
`exp (-π (Im τ) ‖x‖²)`. -/
theorem norm_thetaTerm {n : ℕ} (τ : ℍ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖thetaTerm τ x‖ = Real.exp (-(Real.pi * (τ : ℂ).im) * ‖x‖ ^ 2) := by
  rw [thetaTerm, Complex.norm_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * (τ : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ)
      = (((Real.pi * (‖x‖ ^ 2 : ℝ)) : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) by push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

/-- The theta series of a discrete lattice is absolutely summable at every point of the upper
half plane. -/
theorem summable_thetaTerm {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] (τ : ℍ) :
    Summable (fun x : L => thetaTerm τ (x : EuclideanSpace ℝ (Fin n))) := by
  have hc : 0 < Real.pi * (τ : ℂ).im := by
    have := τ.2
    rw [UpperHalfPlane.coe_im] at this
    positivity
  refine Summable.of_norm_bounded
    (g := fun x : L => Real.exp (-(Real.pi * (τ : ℂ).im) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2))
    (summable_exp_neg_mul_norm_sq L hc) ?_
  intro x
  rw [norm_thetaTerm, Submodule.norm_coe]

/-- At the cusp `i∞` the theta series of a discrete lattice tends to `1`: only the summand at
`x = 0` survives, and the tail is uniformly small because `∑_{x ∈ L} exp (-π y ‖x‖²)` is
dominated by the convergent Gaussian sum over the lattice when `y = Im τ` is large. -/
theorem thetaSeries_atImInfty {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] : Tendsto (thetaSeries L) UpperHalfPlane.atImInfty (𝓝 1) := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_of_discrete L
  -- Split off the constant term at `x = 0`.
  have hdecomp : ∀ τ : ℍ, thetaSeries L τ
      = 1 + ∑' x : L, (if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n))) := by
    intro τ
    rw [thetaSeries, Summable.tsum_eq_add_tsum_ite (summable_thetaTerm L τ) 0]
    have h0 : thetaTerm τ (↑(0 : L) : EuclideanSpace ℝ (Fin n)) = 1 := by
      simp only [ZeroMemClass.coe_zero, thetaTerm_zero]
    rw [h0]
  -- The tail is dominated by `exp (-π δ² y / 2)` times the Gaussian sum over `L`.
  have htail_bound : ∀ τ : ℍ, 1 ≤ (τ : ℂ).im →
      ‖∑' x : L, (if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n)))‖
        ≤ Real.exp (-(Real.pi * δ ^ 2 * (τ : ℂ).im / 2))
          * (∑' x : L, Real.exp (-(Real.pi / 2) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
    intro τ hy
    set y : ℝ := (τ : ℂ).im with hydef
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hcy : 0 < Real.pi * y := by positivity
    have hsumm1 : Summable (fun x : L =>
        ‖(if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n)))‖) := by
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
        (summable_exp_neg_mul_norm_sq L hcy)
      by_cases hx : x = 0
      · simp [hx]
      · rw [if_neg hx, norm_thetaTerm, Submodule.norm_coe]
    have hnorm : ∀ x : L, ‖(if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n)))‖
        = (if x = 0 then 0
            else Real.exp (-(Real.pi * y) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · rw [if_neg hx, if_neg hx, norm_thetaTerm, Submodule.norm_coe]
    have hsumm2 : Summable (fun x : L => (if x = 0 then 0
        else Real.exp (-(Real.pi * y) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2))) := by
      refine Summable.of_nonneg_of_le (fun x => by split <;> positivity) (fun x => ?_)
        (summable_exp_neg_mul_norm_sq L hcy)
      by_cases hx : x = 0
      · simp [hx]
      · simp only [if_neg hx, le_refl]
    have hpoint : ∀ x : L,
        (if x = 0 then 0 else Real.exp (-(Real.pi * y) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2))
          ≤ Real.exp (-(Real.pi * δ ^ 2 * y / 2))
            * Real.exp (-(Real.pi / 2) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
      intro x
      by_cases hx : x = 0
      · simp only [if_pos hx]
        positivity
      · simp only [if_neg hx]
        have hxδ : δ ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ := hsep x hx
        have hxpos : 0 < ‖(x : EuclideanSpace ℝ (Fin n))‖ := lt_of_lt_of_le hδ hxδ
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hA : δ ^ 2 ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by nlinarith [hxδ, hδ]
        have hB : y ≤ 2 * y - 1 := by linarith
        have key : δ ^ 2 * y ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 * (2 * y - 1) :=
          mul_le_mul hA hB (le_of_lt hy0) (by positivity)
        nlinarith [key, Real.pi_pos]
    calc ‖∑' x : L, (if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n)))‖
        ≤ ∑' x : L, ‖(if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n)))‖ :=
          norm_tsum_le_tsum_norm hsumm1
      _ = ∑' x : L, (if x = 0 then 0
            else Real.exp (-(Real.pi * y) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) :=
          tsum_congr hnorm
      _ ≤ ∑' x : L, Real.exp (-(Real.pi * δ ^ 2 * y / 2))
            * Real.exp (-(Real.pi / 2) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) :=
          Summable.tsum_le_tsum hpoint hsumm2
            ((summable_exp_neg_mul_norm_sq L (by positivity : (0 : ℝ) < Real.pi / 2)).mul_left _)
      _ = Real.exp (-(Real.pi * δ ^ 2 * y / 2))
            * (∑' x : L, Real.exp (-(Real.pi / 2) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
          rw [tsum_mul_left]
  -- `Im τ → ∞` along the cusp, and the dominating bound tends to `0`.
  have hev : ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty, (1 : ℝ) ≤ (τ : ℂ).im := by
    rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
    exact ⟨1, fun z hz => by simpa only [Set.mem_ofPred_eq, UpperHalfPlane.coe_im] using hz⟩
  have him : Tendsto (fun τ : ℍ => (τ : ℂ).im) UpperHalfPlane.atImInfty atTop := by
    simpa only [UpperHalfPlane.atImInfty, UpperHalfPlane.coe_im] using
      tendsto_comap (f := UpperHalfPlane.im) (x := atTop)
  have htailnorm : Tendsto
      (fun τ : ℍ => ‖∑' x : L, (if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n)))‖)
      UpperHalfPlane.atImInfty (𝓝 0) := by
    have hlin : Tendsto (fun τ : ℍ => Real.pi * δ ^ 2 * (τ : ℂ).im / 2)
        UpperHalfPlane.atImInfty atTop := by
      have h := him.const_mul_atTop (show (0 : ℝ) < Real.pi * δ ^ 2 / 2 by positivity)
      have heq : (fun τ : ℍ => (Real.pi * δ ^ 2 / 2) * (τ : ℂ).im)
          = (fun τ : ℍ => Real.pi * δ ^ 2 * (τ : ℂ).im / 2) := by
        funext τ; ring
      rwa [heq] at h
    have hexp : Tendsto (fun τ : ℍ => Real.exp (-(Real.pi * δ ^ 2 * (τ : ℂ).im / 2)))
        UpperHalfPlane.atImInfty (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr hlin)
    have hg : Tendsto (fun τ : ℍ => Real.exp (-(Real.pi * δ ^ 2 * (τ : ℂ).im / 2))
        * (∑' x : L, Real.exp (-(Real.pi / 2) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)))
        UpperHalfPlane.atImInfty (𝓝 0) := by
      have h := hexp.mul_const
        (∑' x : L, Real.exp (-(Real.pi / 2) * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2))
      simpa only [zero_mul] using h
    refine squeeze_zero' (Eventually.of_forall fun τ => norm_nonneg _) ?_ hg
    filter_upwards [hev] with τ hτ
    exact htail_bound τ hτ
  have htail : Tendsto
      (fun τ : ℍ => ∑' x : L, (if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n))))
      UpperHalfPlane.atImInfty (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr htailnorm
  have hmain : Tendsto (fun τ : ℍ => (1 : ℂ) + ∑' x : L,
      (if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n))))
      UpperHalfPlane.atImInfty (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds.add htail :
      Tendsto (fun τ : ℍ => (1 : ℂ) + ∑' x : L,
        (if x = 0 then 0 else thetaTerm τ (x : EuclideanSpace ℝ (Fin n))))
        UpperHalfPlane.atImInfty (𝓝 ((1 : ℂ) + 0)))
  exact hmain.congr' (Eventually.of_forall fun τ => (hdecomp τ).symm)

end Work.Modular
