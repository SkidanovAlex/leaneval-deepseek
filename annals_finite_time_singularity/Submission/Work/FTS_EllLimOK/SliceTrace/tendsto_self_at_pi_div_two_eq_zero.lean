import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The trace `f` vanishes at `π/2`

If `f` is a function on `(0, π/2)` whose weighted square integral
`∫₀^{π/2} (f θ / cos θ)² dθ` is finite and which has a finite limit `J` at `π/2` from the
left, then necessarily `J = 0`, so `f → 0`.

The point is that `cos θ ≈ π/2 - θ` near `π/2`: the weight `1/cos²θ` is *not* integrable
there.  If `f → J ≠ 0`, then `|f| > d` for some `d > 0` on a whole tail `(t, π/2)`, and on the
sub-interval `(π/2 - θ, π/2)` of length `θ` we have `cos x ≤ θ`, whence

`(f x / cos x)² > d²/θ²`,  so  `∫_{π/2-θ}^{π/2} (f/cos)² > d²/θ`,

which is unbounded as `θ → 0⁺`, contradicting integrability.

The integrability of `f` at the endpoint is therefore strong enough to force the value of the
limit on its own; the `C¹`-hypothesis is not needed (it is part of the caller's context).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_EllLimOK.SliceTrace

/-- **No small value forces a divergent integral.**  If `∫_t^{π/2} (f θ / cos θ)² dθ` is
finite and `t ∈ (0, π/2)`, then `f` must take a value of modulus at most `d` somewhere on
`(t, π/2)`, for every `d > 0`.

Indeed, if `|f| > d` on all of `(t, π/2)`, then on `(π/2 - θ, π/2)` we have `cos x ≤ θ`
(because `cos x = sin (π/2 - x) ≤ π/2 - x < θ`), hence the integrand dominates the
constant `d²/θ²`, and the sub-interval has length `θ`:
`d²/θ ≤ ∫_{π/2-θ}^{π/2} (f/cos)² ≤ ∫_t^{π/2} (f/cos)²`, impossible for small `θ`. -/
theorem exists_abs_le_of_integrable_inv_cos_sq_aux {f : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2) (Set.Ioo t (Real.pi / 2)))
    {d : ℝ} (hd : 0 < d) :
    ∃ τ ∈ Set.Ioo t (Real.pi / 2), |f τ| ≤ d := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set G : ℝ → ℝ := fun θ => (f θ / Real.cos θ) ^ 2 with hG
  set D : ℝ := ∫ θ in Set.Ioo t (Real.pi / 2), G θ with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    exact MeasureTheory.integral_nonneg (fun x => by rw [hG]; positivity)
  -- the key lower bound `d²/θ ≤ D` for every short tail length `θ`
  have hmain : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2 - t), d ^ 2 / θ ≤ D := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθu : θ < Real.pi / 2 - t := hθ.2
    have hsub : Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2) ⊆ Set.Ioo t (Real.pi / 2) := by
      intro x hx
      exact ⟨by linarith [hx.1, hθu], hx.2⟩
    have hGs : IntegrableOn G (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) := hint.mono_set hsub
    have hconst : IntegrableOn (fun _ : ℝ => d ^ 2 / θ ^ 2) (Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2)) := by
      apply integrableOn_const
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
      · finiteness
    have hpoint : ∀ x ∈ Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), d ^ 2 / θ ^ 2 ≤ G x := by
      intro x hx
      have hx1 : Real.pi / 2 - θ < x := hx.1
      have hx2 : x < Real.pi / 2 := hx.2
      have hxpos : 0 < x := by linarith [hx1, hθu, ht.1, Real.pi_pos]
      have hcos_pos : 0 < Real.cos x :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hxpos], hx2⟩
      have hcos_le : Real.cos x ≤ θ := by
        have hc : Real.cos x = Real.sin (Real.pi / 2 - x) := (Real.sin_pi_div_two_sub x).symm
        rw [hc]
        calc Real.sin (Real.pi / 2 - x) ≤ Real.pi / 2 - x := Real.sin_le (by linarith)
          _ ≤ θ := by linarith [hx1]
      have hfx : d < |f x| := hcon x ⟨by linarith [hx1, hθu], hx2⟩
      have hgoal : d ^ 2 / θ ^ 2 ≤ (f x / Real.cos x) ^ 2 := by
        rw [div_pow, div_le_div_iff₀ (by positivity : (0 : ℝ) < θ ^ 2)
          (by positivity : (0 : ℝ) < Real.cos x ^ 2)]
        have hdc : d * Real.cos x < |f x| * θ :=
          calc d * Real.cos x ≤ d * θ := mul_le_mul_of_nonneg_left hcos_le hd.le
            _ < |f x| * θ := mul_lt_mul_of_pos_right hfx hθ0
        have hsq : (d * Real.cos x) ^ 2 < (|f x| * θ) ^ 2 :=
          pow_lt_pow_left₀ hdc (by positivity) (by norm_num)
        nlinarith [hsq, sq_abs (f x), sq_nonneg (Real.cos x), sq_nonneg θ]
      simpa [hG] using hgoal
    have hmono : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), (d ^ 2 / θ ^ 2 : ℝ)
        ≤ ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), G x :=
      setIntegral_mono_on hconst hGs measurableSet_Ioo hpoint
    have hval : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), (d ^ 2 / θ ^ 2 : ℝ) = d ^ 2 / θ := by
      rw [setIntegral_const, Real.volume_real_Ioo,
        max_eq_left (show (0 : ℝ) ≤ Real.pi / 2 - (Real.pi / 2 - θ) by linarith), smul_eq_mul]
      field_simp
      ring
    have hb : ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), G x ≤ D := by
      rw [hD]
      refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => by rw [hG]; positivity) ?_
      exact Filter.Eventually.of_forall fun x hx => hsub hx
    linarith [hval ▸ hmono]
  -- now choose a tail length shorter than `π/2 - t` and with `d²/θ > D`
  set m : ℝ := min (Real.pi / 2 - t) (d ^ 2 / (D + 1)) with hm
  have hmpos : 0 < m := by
    rw [hm]; exact lt_min (by linarith [ht.2]) (div_pos (by positivity) (by linarith))
  have hmle_left : m ≤ Real.pi / 2 - t := by rw [hm]; exact min_le_left _ _
  have hmle_right : m ≤ d ^ 2 / (D + 1) := by rw [hm]; exact min_le_right _ _
  have hθmem : m / 2 ∈ Set.Ioo 0 (Real.pi / 2 - t) := ⟨by linarith, by linarith⟩
  have h1 := hmain (m / 2) hθmem
  have hD1 : 0 < D + 1 := by linarith
  have hmD : m * (D + 1) ≤ d ^ 2 := by
    calc m * (D + 1) ≤ (d ^ 2 / (D + 1)) * (D + 1) :=
          mul_le_mul_of_nonneg_right hmle_right hD1.le
      _ = d ^ 2 := by field_simp
  have h2 : 2 * (D + 1) ≤ d ^ 2 / (m / 2) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < m / 2)]
    nlinarith [hmD]
  linarith [h1, h2, hDnn]

theorem tendsto_self_at_pi_div_two_eq_zero {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) (hlim : ∃ J : ℝ, Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds J)) (hint : MeasureTheory.IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2) (Set.Ioo 0 (Real.pi / 2))) : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨J, hJ⟩ := hlim
  -- the limit `J` has to be `0`: otherwise `|f| > d > 0` on a tail, contradicting the
  -- existence of a point where `|f| ≤ d`
  have hJ0 : J = 0 := by
    by_contra hJne
    have hJpos : 0 < |J| := abs_pos.mpr hJne
    set d : ℝ := |J| / 2 with hddef
    have hd : 0 < d := by rw [hddef]; linarith [hJpos]
    have hdJ : d < |J| := by rw [hddef]; exact half_lt_self hJpos
    have hopen : IsOpen {y : ℝ | d < |y|} := isOpen_lt continuous_const continuous_abs
    have hgood : {y : ℝ | d < |y|} ∈ 𝓝 J := hopen.mem_nhds hdJ
    have hev : ∀ᶠ θ in 𝓝[<] (Real.pi / 2), d < |f θ| := hJ.eventually hgood
    obtain ⟨t₀, ht₀lt, hsub₀⟩ := (nhdsLT_basis (Real.pi / 2)).mem_iff.mp hev
    set t : ℝ := max t₀ (Real.pi / 4) with htdef
    have ht_mem : t ∈ Set.Ioo 0 (Real.pi / 2) := by
      rw [htdef, Set.mem_Ioo]
      exact ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) (le_max_right t₀ (Real.pi / 4)),
        max_lt ht₀lt (by linarith [Real.pi_pos])⟩
    have hsub : Set.Ioo t (Real.pi / 2) ⊆ {θ | d < |f θ|} := by
      intro θ hθ
      exact hsub₀ ⟨lt_of_le_of_lt (le_max_left t₀ (Real.pi / 4)) hθ.1, hθ.2⟩
    have hint' : MeasureTheory.IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2)
        (Set.Ioo t (Real.pi / 2)) :=
      hint.mono_set (Set.Ioo_subset_Ioo ht_mem.1.le le_rfl)
    obtain ⟨τ, hτ, hτle⟩ := exists_abs_le_of_integrable_inv_cos_sq_aux ht_mem hint' hd
    exact absurd (hsub hτ) (not_lt.mpr hτle)
  rw [hJ0] at hJ
  exact hJ

end Work.FTS_EllLimOK.SliceTrace
