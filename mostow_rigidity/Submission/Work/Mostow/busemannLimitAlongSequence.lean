import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.BdExt.lawCosines
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.BusemannLipschitz

/-!
# The Busemann limit along a sequence escaping in a direction

If `z k → ∞` in the chart model `E n` and the directions `(‖z k‖)⁻¹ • z k` converge to a boundary
point `ζ ∈ Sph n`, then for every fixed `w` the difference of hyperbolic distances
`hdist w (z k) - hdist 0 (z k)` converges to the Busemann function `busemann ζ w`.

The two algebraic inputs are

* `arcoshArgNormMul` : `tpart w * tpart z - ⟪w,z⟫ = ‖z‖ (tpart w · √(1+‖z‖⁻²) - ‖z‖⁻¹⟪w,z⟫)`,
  i.e. the argument of `hdist w z` is `‖z‖`-times a quantity converging to `lev ζ w`;
* `arcoshMulSubTendsto` : the difference of `arcosh` of two such products converges to the
  difference of the logarithms of the limits.
-/

namespace Work.Mostow

open Submission.Mostow

/-! ## Elementary algebra -/

/-- `arcosh (r x) = log r + log (x + √(x² - r⁻²))` for `r > 0`. -/
private lemma arcosh_mul_eq_log (r X : ℝ) (hr : 0 < r) (hX : 0 < X) :
    Real.arcosh (r * X) = Real.log r + Real.log (X + Real.sqrt (X ^ 2 - (r⁻¹) ^ 2)) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hsq : (r * X) ^ 2 - 1 = r ^ 2 * (X ^ 2 - (r⁻¹) ^ 2) := by
    have h1 : r ^ 2 * (r⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hrne, one_pow]
    rw [mul_sub, h1, mul_pow]
  have hroot : Real.sqrt (r ^ 2 * (X ^ 2 - (r⁻¹) ^ 2))
      = r * Real.sqrt (X ^ 2 - (r⁻¹) ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq (le_of_lt hr)]
  have hpos : (0 : ℝ) < X + Real.sqrt (X ^ 2 - (r⁻¹) ^ 2) :=
    lt_of_lt_of_le hX (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  rw [Real.arcosh, hsq, hroot,
    show r * X + r * Real.sqrt (X ^ 2 - (r⁻¹) ^ 2)
      = r * (X + Real.sqrt (X ^ 2 - (r⁻¹) ^ 2)) by ring,
    Real.log_mul hrne (ne_of_gt hpos)]

/-- **Rescaling the argument of `hdist` by `‖z‖`.**  For `z ≠ 0`,
`tpart w * tpart z - ⟪w,z⟫ = ‖z‖ (tpart w · √(1 + ‖z‖⁻²) - ‖z‖⁻¹ ⟪w,z⟫)`. -/
lemma arcoshArgNormMul {n : ℕ} {w z : Submission.Mostow.E n} (hz : 0 < ‖z‖) :
    Submission.Mostow.tpart w * Submission.Mostow.tpart z - inner ℝ w z
      = ‖z‖ * (Submission.Mostow.tpart w * Real.sqrt (1 + ((‖z‖)⁻¹) ^ 2)
          - (‖z‖)⁻¹ * inner ℝ w z) := by
  have hsqrt : ‖z‖ * Real.sqrt (1 + ((‖z‖)⁻¹) ^ 2) = Submission.Mostow.tpart z := by
    have hstep : ‖z‖ * Real.sqrt (1 + ((‖z‖)⁻¹) ^ 2)
        = Real.sqrt (‖z‖ ^ 2 * (1 + ((‖z‖)⁻¹) ^ 2)) := by
      rw [Real.sqrt_mul (sq_nonneg ‖z‖), Real.sqrt_sq (le_of_lt hz)]
    rw [hstep, Submission.Mostow.tpart]
    congr 1
    have h1 : ‖z‖ ^ 2 * ((‖z‖)⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hz), one_pow]
    rw [mul_add, mul_one, h1]
    ring
  have key : ‖z‖ * (Submission.Mostow.tpart w * Real.sqrt (1 + ((‖z‖)⁻¹) ^ 2)
        - (‖z‖)⁻¹ * inner ℝ w z)
      = Submission.Mostow.tpart w * (‖z‖ * Real.sqrt (1 + ((‖z‖)⁻¹) ^ 2)) - inner ℝ w z := by
    rw [mul_sub]
    rw [show ‖z‖ * ((‖z‖)⁻¹ * inner ℝ w z) = inner ℝ w z by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hz), one_mul]]
    ring
  rw [← hsqrt, key]

/-! ## The real-analysis limit -/

/-- **Difference of `arcosh` of two divergent products.**  If `r k → +∞`, `A k → a > 0`,
`B k → b > 0`, and eventually `1 ≤ r k * A k`, `1 ≤ r k * B k`, then
`arcosh (r k * A k) - arcosh (r k * B k) → log a - log b`. -/
lemma arcoshMulSubTendsto {r A B : ℕ → ℝ} {a b : ℝ}
    (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hA : Filter.Tendsto A Filter.atTop (nhds a)) (hB : Filter.Tendsto B Filter.atTop (nhds b))
    (ha : 0 < a) (hb : 0 < b)
    (h1 : ∀ᶠ k in Filter.atTop, 1 ≤ r k * A k)
    (h2 : ∀ᶠ k in Filter.atTop, 1 ≤ r k * B k) :
    Filter.Tendsto (fun k => Real.arcosh (r k * A k) - Real.arcosh (r k * B k))
      Filter.atTop (nhds (Real.log a - Real.log b)) := by
  have hrpos : ∀ᶠ k in Filter.atTop, 0 < r k := hr.eventually (Filter.eventually_gt_atTop 0)
  have hApos : ∀ᶠ k in Filter.atTop, 0 < A k := by
    filter_upwards [hrpos, h1] with k hrk hk
    have hlt : 0 < r k * A k := lt_of_lt_of_le zero_lt_one hk
    have : 0 < (r k)⁻¹ * (r k * A k) := mul_pos (inv_pos.mpr hrk) hlt
    rwa [inv_mul_cancel_left₀ (ne_of_gt hrk) (A k)] at this
  have hBpos : ∀ᶠ k in Filter.atTop, 0 < B k := by
    filter_upwards [hrpos, h2] with k hrk hk
    have hlt : 0 < r k * B k := lt_of_lt_of_le zero_lt_one hk
    have : 0 < (r k)⁻¹ * (r k * B k) := mul_pos (inv_pos.mpr hrk) hlt
    rwa [inv_mul_cancel_left₀ (ne_of_gt hrk) (B k)] at this
  have hr2 : Filter.Tendsto (fun k => (r k)⁻¹ ^ 2) Filter.atTop (nhds 0) := by
    simpa using hr.inv_tendsto_atTop.pow 2
  have hsA : Filter.Tendsto (fun k => Real.sqrt (A k ^ 2 - (r k)⁻¹ ^ 2)) Filter.atTop (nhds a) := by
    have h := ((hA.pow 2).sub hr2).sqrt
    have hlim : Real.sqrt (a ^ 2 - 0) = a := by rw [sub_zero, Real.sqrt_sq (le_of_lt ha)]
    rwa [hlim] at h
  have hsB : Filter.Tendsto (fun k => Real.sqrt (B k ^ 2 - (r k)⁻¹ ^ 2)) Filter.atTop (nhds b) := by
    have h := ((hB.pow 2).sub hr2).sqrt
    have hlim : Real.sqrt (b ^ 2 - 0) = b := by rw [sub_zero, Real.sqrt_sq (le_of_lt hb)]
    rwa [hlim] at h
  have hUA : Filter.Tendsto (fun k => A k + Real.sqrt (A k ^ 2 - (r k)⁻¹ ^ 2))
      Filter.atTop (nhds (2 * a)) := by
    have h := hA.add hsA
    rwa [show a + a = 2 * a by ring] at h
  have hUB : Filter.Tendsto (fun k => B k + Real.sqrt (B k ^ 2 - (r k)⁻¹ ^ 2))
      Filter.atTop (nhds (2 * b)) := by
    have h := hB.add hsB
    rwa [show b + b = 2 * b by ring] at h
  have hident : ∀ᶠ k in Filter.atTop,
      Real.log (A k + Real.sqrt (A k ^ 2 - (r k)⁻¹ ^ 2))
          - Real.log (B k + Real.sqrt (B k ^ 2 - (r k)⁻¹ ^ 2))
        = Real.arcosh (r k * A k) - Real.arcosh (r k * B k) := by
    filter_upwards [hrpos, hApos, hBpos] with k hrk hAk hBk
    rw [arcosh_mul_eq_log (r k) (A k) hrk hAk, arcosh_mul_eq_log (r k) (B k) hrk hBk]
    ring
  have hlog : Filter.Tendsto
      (fun k => Real.log (A k + Real.sqrt (A k ^ 2 - (r k)⁻¹ ^ 2))
        - Real.log (B k + Real.sqrt (B k ^ 2 - (r k)⁻¹ ^ 2)))
      Filter.atTop (nhds (Real.log (2 * a) - Real.log (2 * b))) :=
    (hUA.log (ne_of_gt (by positivity))).sub (hUB.log (ne_of_gt (by positivity)))
  have hlim : Real.log (2 * a) - Real.log (2 * b) = Real.log a - Real.log b := by
    rw [Real.log_mul (by norm_num) (ne_of_gt ha), Real.log_mul (by norm_num) (ne_of_gt hb)]
    ring
  rw [hlim] at hlog
  exact Filter.Tendsto.congr' hident hlog

/-! ## The Busemann limit -/

/-- **The Busemann limit along a sequence escaping in a direction.**  If `z k → ∞` in the chart
model and the directions `(‖z k‖)⁻¹ • z k` converge to a boundary point `ζ ∈ Sph n`, then for
every fixed `w`
`hdist w (z k) - hdist 0 (z k) → busemann ζ w`.

Proof sketch (reviewers verified the algebra): `hdist u v = arcosh (tpart u * tpart v - ⟪u,v⟫)`,
so with `r k = ‖z k‖`, `e k = (r k)⁻¹ • z k`,
`hdist w (z k) = arcosh (r k * A k)` with `A k = tpart w * √(1 + (r k)⁻²) - ⟪w, e k⟫ → lev ζ w`
and `hdist 0 (z k) = arcosh (r k * B k)` with `B k = √(1 + (r k)⁻²) → 1`; finally, on the tail
where `r k > 1` and `A k > 0` (`lev_pos`),
`arcosh (r a) - arcosh (r b) = log ((a + √(a² - r⁻²)) / (b + √(b² - r⁻²))) → log a - log b`
(`Real.arcosh`, `Real.log_div`, `Real.log_mul`), and `Real.log (lev ζ w) = busemann ζ w`. -/
theorem busemannLimitAlongSequence (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (z : ℕ → Submission.Mostow.E n) (ζ : Submission.Mostow.E n) (hζ : ζ ∈ Submission.Mostow.Sph n)
    (hnorm : Filter.Tendsto (fun k => ‖z k‖) Filter.atTop Filter.atTop)
    (hdir : Filter.Tendsto (fun k => (‖z k‖)⁻¹ • z k) Filter.atTop (nhds ζ)) (w : Submission.Mostow.E n) :
    Filter.Tendsto (fun k => Submission.Mostow.hdist w (z k) - Submission.Mostow.hdist (0 : Submission.Mostow.E n) (z k))
      Filter.atTop (nhds (Submission.Mostow.busemann ζ w)) := by
  have hrpos : ∀ᶠ k in Filter.atTop, (0 : ℝ) < ‖z k‖ :=
    hnorm.eventually (Filter.eventually_gt_atTop 0)
  have hinv2 : Filter.Tendsto (fun k : ℕ => ((‖z k‖)⁻¹) ^ 2) Filter.atTop (nhds 0) := by
    simpa using hnorm.inv_tendsto_atTop.pow 2
  have hcone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have hs : Filter.Tendsto (fun k : ℕ => Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2)) Filter.atTop (nhds 1) := by
    have h := hcone.add hinv2
    have h2 := h.sqrt
    simpa using h2
  have hinner : Filter.Tendsto (fun k : ℕ => (‖z k‖)⁻¹ * inner ℝ w (z k)) Filter.atTop
      (nhds (inner ℝ w ζ)) := by
    have hcont : Continuous (fun v : E n => inner ℝ w v) := continuous_const.inner continuous_id
    have h1 : Filter.Tendsto (fun k : ℕ => inner ℝ w ((‖z k‖)⁻¹ • z k)) Filter.atTop
        (nhds (inner ℝ w ζ)) := (hcont.tendsto ζ).comp hdir
    have h2 : (fun k : ℕ => (‖z k‖)⁻¹ * inner ℝ w (z k))
        = fun k : ℕ => inner ℝ w ((‖z k‖)⁻¹ • z k) := by
      funext k; rw [real_inner_smul_right]
    rw [h2]; exact h1
  have hcw : Filter.Tendsto (fun _ : ℕ => tpart w) Filter.atTop (nhds (tpart w)) := tendsto_const_nhds
  have hAconv : Filter.Tendsto
      (fun k : ℕ => tpart w * Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2) - (‖z k‖)⁻¹ * inner ℝ w (z k))
      Filter.atTop (nhds (lev ζ w)) := by
    have h := (hcw.mul hs).sub hinner
    simpa [lev] using h
  have hBconv : Filter.Tendsto (fun k : ℕ => Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2)) Filter.atTop
      (nhds 1) := hs
  have hev1 : ∀ᶠ k in Filter.atTop,
      1 ≤ ‖z k‖ * (tpart w * Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2) - (‖z k‖)⁻¹ * inner ℝ w (z k)) := by
    filter_upwards [hrpos] with k hk
    have h := one_le_cosh_hdist w (z k)
    rwa [arcoshArgNormMul (w := w) hk] at h
  have hev2 : ∀ᶠ k in Filter.atTop, 1 ≤ ‖z k‖ * Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2) := by
    filter_upwards [hrpos] with k hk
    have h := one_le_cosh_hdist (0 : E n) (z k)
    rw [arcoshArgNormMul (w := (0 : E n)) hk] at h
    simpa [tpart] using h
  have hident : ∀ᶠ k in Filter.atTop,
      Real.arcosh (‖z k‖ * (tpart w * Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2)
            - (‖z k‖)⁻¹ * inner ℝ w (z k)))
        - Real.arcosh (‖z k‖ * Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2))
        = hdist w (z k) - hdist (0 : E n) (z k) := by
    filter_upwards [hrpos] with k hk
    rw [hdist, hdist, arcoshArgNormMul (w := w) hk, arcoshArgNormMul (w := (0 : E n)) hk]
    have h0 : tpart (0 : E n) = 1 := by simp [tpart]
    have hi0 : inner ℝ (0 : E n) (z k) = 0 := inner_zero_left (z k)
    simp only [h0, hi0, mul_zero, sub_zero, one_mul]
  have hmain := arcoshMulSubTendsto (r := fun k => ‖z k‖)
    (A := fun k => tpart w * Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2) - (‖z k‖)⁻¹ * inner ℝ w (z k))
    (B := fun k => Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2))
    hnorm hAconv hBconv (lev_pos ζ hζ w) one_pos hev1 hev2
  have hfinal : Filter.Tendsto
      (fun k : ℕ => Real.arcosh (‖z k‖ * (tpart w * Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2)
            - (‖z k‖)⁻¹ * inner ℝ w (z k)))
        - Real.arcosh (‖z k‖ * Real.sqrt (1 + ((‖z k‖)⁻¹) ^ 2)))
      Filter.atTop (nhds (busemann ζ w)) := by
    simpa [Real.log_one, busemann, lev] using hmain
  exact Filter.Tendsto.congr' hident hfinal

end Work.Mostow
