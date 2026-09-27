import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.SymDefs
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.sigma_orbit_tendsto_multiple
import Submission.Work.EQ.exists_repr_Ioo_two_pi

/-!
# The `eqT`-orbit of an off-axis point of a normalised equichordal curve converges to a real
point of the curve

Setting (see `Submission/Work/EQ/DESIGN.md`): `ρ₁, ρ₂` are the radial functions of a normalised
two-point equichordal curve with chord length `1` about the foci `O₁ = -a/2`, `O₂ = a/2`
(`NormEqCurve a ρ₁ ρ₂`), `P θ = polarPt (-(a/2)) (ρ₁ θ) θ` is the point of the curve at polar
angle `θ` about `O₁`, and `eqT a = chordMap (O₁ a) ∘ chordMap (O₂ a)` is Rychlik's equichordal
map, which sends the curve to itself.

The hypotheses of the statement describe the induced action of `eqT a` on the angle: there is an
increasing homeomorphism `σ` of `ℝ` with

* `P (σ θ) = eqT a (P θ)` (`hσeq`),
* `σ (θ + 2π) = σ θ + 2π` (`hσper`), `σ 0 = 0`, `σ π = π`,
* `σ` has no fixed point in `(0, π)` nor in `(π, 2π)` (`hfix1`, `hfix2`).

Since `σ` is an order isomorphism, it is continuous and strictly increasing; together with
`σ 0 = 0`, `σ π = π`, `σ (2π) = 2π` (from `hσper` at `0`) it preserves each of the intervals
`(0, π)` and `(π, 2π)`, on which it has no fixed points.  So on each of them the orbit of a point
is strictly monotone and converges to one of the endpoints
(`Work.EQ.sigma_orbit_tendsto_multiple`, using `Work.EQ.orbit_tendsto_lower` /
`Work.EQ.orbit_tendsto_upper`).

For a point with `P θ` off the real axis, i.e. `sin θ ≠ 0` (the imaginary part of `P θ` is
`ρ₁ θ sin θ` with `ρ₁ θ > 0`), we pass to the representative `x ∈ (0, 2π)` of `θ` modulo `2π`
(`Work.EQ.exists_repr_Ioo_two_pi`), for which `P x = P θ` by `2π`-periodicity of `ρ₁` and of
`polarPt` in the angle.  The `σ`-orbit of `x` converges to `L ∈ {0, π, 2π}`
(`sigma_orbit_tendsto_multiple`), hence, by continuity of `θ ↦ P θ`, the `eqT`-orbit of `P θ`,
which is `n ↦ P (σ^[n] θ)` (`eqT_iterate_polarPt`), converges to `P L`; that limit has vanishing
imaginary part (`sin L = 0`) and lies on the curve by construction. -/

namespace Work.EQ

open Complex

/-- `polarPt` is periodic in the angle with any integer multiple of `2π` as period. -/
lemma polarPt_int_mul_two_pi (c r θ : ℝ) (m : ℤ) :
    polarPt c r (θ + m * (2 * Real.pi)) = polarPt c r θ := by
  have hper : Function.Periodic (fun t : ℝ => polarPt c r t) (2 * Real.pi) := fun t => by
    simp only [polarPt]
    rw [show ((↑(t + 2 * Real.pi) : ℂ)) * Complex.I
        = (↑t : ℂ) * Complex.I + (2 * ↑Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  exact hper.int_mul m θ

/-- **The `eqT`-orbit follows the `σ`-orbit of the angle**: the `n`-th iterate of `eqT a` at the
curve point of angle `θ` is the curve point of angle `σ^[n] θ`. -/
lemma eqT_iterate_polarPt {a : ℝ} {ρ₁ : ℝ → ℝ} {σ : ℝ ≃o ℝ}
    (hσeq : ∀ θ, eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ (σ θ)) (σ θ))
    (θ : ℝ) (n : ℕ) :
    (eqT a)^[n] (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ (σ^[n] θ)) (σ^[n] θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hσeq, Function.iterate_succ_apply' σ n θ]

theorem eqT_orbit_tendsto_real {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) {σ : ℝ ≃o ℝ}
    (hσper : ∀ θ, σ (θ + 2 * Real.pi) = σ θ + 2 * Real.pi)
    (hσeq : ∀ θ, eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ (σ θ)) (σ θ))
    (hσ0 : σ 0 = 0) (hσπ : σ Real.pi = Real.pi)
    (hfix1 : ∀ θ, 0 < θ → θ < Real.pi → σ θ ≠ θ)
    (hfix2 : ∀ θ, Real.pi < θ → θ < 2 * Real.pi → σ θ ≠ θ)
    {θ : ℝ} (hθ : (polarPt (-(a/2)) (ρ₁ θ) θ).im ≠ 0) :
    ∃ Q : ℂ, Q.im = 0 ∧ Q ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) ∧
      Filter.Tendsto (fun n : ℕ => (eqT a)^[n] (polarPt (-(a/2)) (ρ₁ θ) θ))
        Filter.atTop (nhds Q) := by
  obtain ⟨hcont₁, -, hpos₁, -, hchord₁, -, -⟩ := hC
  -- `2π`-periodicity of the radial function, from the chord identity
  have hper₁ : Function.Periodic ρ₁ (2 * Real.pi) := by
    intro t
    have h1 := hchord₁ t
    have h2 := hchord₁ (t + Real.pi)
    have harg : t + Real.pi + Real.pi = t + 2 * Real.pi := by ring
    rw [harg] at h2
    linarith
  -- `P θ` off the real axis means `sin θ ≠ 0`
  have hsinθ : Real.sin θ ≠ 0 := by
    intro hs
    refine hθ ?_
    rw [nec_polarPt_im, hs, mul_zero]
  -- representative of `θ` modulo `2π` in `(0, 2π)`
  obtain ⟨x, k, hx0, hx2π, hθx, hsinx⟩ := exists_repr_Ioo_two_pi hsinθ
  have hxne : x ≠ Real.pi := by
    intro hxpi
    have h0 : Real.sin x = 0 := by rw [hxpi, Real.sin_pi]
    rw [hsinx] at h0
    exact hsinθ h0
  -- the two curve points coincide
  have hPt : polarPt (-(a/2)) (ρ₁ θ) θ = polarPt (-(a/2)) (ρ₁ x) x := by
    rw [hθx, hper₁.int_mul k x, polarPt_int_mul_two_pi]
  -- the `σ`-orbit of the representative converges to `0`, `π` or `2π`
  obtain ⟨L, hL, hlimσ⟩ := sigma_orbit_tendsto_multiple hσper hσ0 hσπ hfix1 hfix2 hx0 hx2π
  -- continuity of the polar parametrisation turns that into convergence of the curve points
  have hPcont : Continuous (fun t : ℝ => polarPt (-(a/2)) (ρ₁ t) t) := by
    unfold polarPt
    fun_prop
  have hlimP : Filter.Tendsto (fun n : ℕ => polarPt (-(a/2)) (ρ₁ (σ^[n] x)) (σ^[n] x))
      Filter.atTop (nhds (polarPt (-(a/2)) (ρ₁ L) L)) := by
    have h := (hPcont.tendsto L).comp hlimσ
    simpa [Function.comp_def] using h
  -- the limit point is on the real axis
  have hQim : (polarPt (-(a/2)) (ρ₁ L) L).im = 0 := by
    rw [nec_polarPt_im]
    rcases hL with h | h | h
    · rw [h, Real.sin_zero, mul_zero]
    · rw [h, Real.sin_pi, mul_zero]
    · rw [h]; simp
  -- the `eqT`-orbit of `P x` is the `σ`-orbit of `x` through `P`
  have hcongr : (fun n : ℕ => (eqT a)^[n] (polarPt (-(a/2)) (ρ₁ x) x)) =
      (fun n : ℕ => polarPt (-(a/2)) (ρ₁ (σ^[n] x)) (σ^[n] x)) :=
    funext fun n => eqT_iterate_polarPt hσeq x n
  exact ⟨polarPt (-(a/2)) (ρ₁ L) L, hQim, Set.mem_range_self L,
    by rw [hPt, hcongr]; exact hlimP⟩

end Work.EQ
