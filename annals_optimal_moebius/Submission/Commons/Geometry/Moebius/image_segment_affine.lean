import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Geometry.Moebius.embedding_lipschitz_strip

namespace Commons.Geometry.Moebius

open Commons.PaperMoebius

/-- **Equality in the triangle inequality, positional form.**

If a point `P` of a real inner product space has `‖P - A‖ = t ‖B - A‖` and
`‖B - P‖ = (1 - t) ‖B - A‖`, then `P` is the point of the segment `[A, B]` at
parameter `t`.  (Note that for `t ∉ [0, 1]` the two hypotheses force the
degenerate case `B = A`, so no hypothesis on `t` is needed.) -/
theorem eq_smul_add_of_norm_eq_norm_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {A B P : E} {t : ℝ}
    (h1 : ‖P - A‖ = t * ‖B - A‖) (h2 : ‖B - P‖ = (1 - t) * ‖B - A‖) :
    P = (1 - t) • A + t • B := by
  have hx : t * ‖B - A‖ + (1 - t) * ‖B - A‖ = ‖B - A‖ := by ring
  -- The two distances add up, so we have equality in the triangle inequality.
  have hsum : ‖P - A‖ + ‖B - P‖ = ‖B - A‖ := by linarith [h1, h2, hx]
  have htri : ‖(P - A) + (B - P)‖ = ‖P - A‖ + ‖B - P‖ := by
    have he : (P - A) + (B - P) = B - A := by abel
    rw [he, hsum]
  -- `norm_add_eq_iff_real` : equality in the triangle inequality means the two
  -- summands are nonnegative multiples of each other.
  have hsmul : ‖B - P‖ • (P - A) = ‖P - A‖ • (B - P) := norm_add_eq_iff_real.mp htri
  rw [h2, h1] at hsmul
  by_cases hc : ‖B - A‖ = 0
  · -- Degenerate case: `B = A`.
    have hPA : P = A := by
      have hz : ‖P - A‖ = 0 := by rw [h1, hc, mul_zero]
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    have hBA : B = A := sub_eq_zero.mp (norm_eq_zero.mp hc)
    rw [hPA, hBA, ← add_smul]
    simp
  · -- Cancel the scalar `‖B - A‖ ≠ 0`.
    have h' : ‖B - A‖ • ((1 - t) • (P - A)) = ‖B - A‖ • (t • (B - P)) := by
      rw [← mul_smul, ← mul_smul, mul_comm ‖B - A‖ (1 - t), mul_comm ‖B - A‖ t]
      exact hsmul
    have hcancel : (1 - t) • (P - A) = t • (B - P) := (smul_right_inj hc).mp h'
    have key : (1 - t) • (P - A) - t • (B - P) = P - ((1 - t) • A + t • B) := by
      module
    have hz : P - ((1 - t) • A + t • B) = 0 := by
      rw [← key]
      exact sub_eq_zero.mpr hcancel
    exact sub_eq_zero.mp hz

/-- **A `1`-Lipschitz map that preserves one chord maps a segment affinely.**

Let `s` be a convex subset of a real normed space `E`, let `f : E → F` into a
real inner product space be `1`-Lipschitz along `s`, and let `A, B ∈ s` be such
that `f` preserves the distance `‖B - A‖`.  Then `f` is affine on the whole
segment `[A, B]`.

This is the convex/Lipschitz general form of `image_segment_affine`: the
Möbius embedding case below applies it to `s = unitStrip`, using that the
within-derivative of an isometric immersion is a linear isometry. -/
theorem image_segment_affine_of_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {s : Set E} (hs : Convex ℝ s) {f : E → F}
    (hlip : ∀ x ∈ s, ∀ y ∈ s, ‖f y - f x‖ ≤ ‖y - x‖)
    {A B : E} (hA : A ∈ s) (hB : B ∈ s)
    (hpre : ‖f B - f A‖ = ‖B - A‖) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    f ((1 - t) • A + t • B) = (1 - t) • f A + t • f B := by
  set P : E := (1 - t) • A + t • B with hPdef
  have hPmem : P ∈ s := by
    rw [hPdef]
    exact hs hA hB (by linarith [ht.2]) ht.1 (by ring)
  have hPA : P - A = t • (B - A) := by rw [hPdef]; module
  have hBP : B - P = (1 - t) • (B - A) := by rw [hPdef]; module
  -- The Lipschitz bounds from the two ends of the segment.
  have h1 : ‖f P - f A‖ ≤ t * ‖B - A‖ := by
    have h := hlip A hA P hPmem
    rw [hPA, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h
    exact h
  have h2 : ‖f B - f P‖ ≤ (1 - t) * ‖B - A‖ := by
    have h := hlip P hPmem B hB
    rw [hBP, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])] at h
    exact h
  -- ... and the reverse triangle inequality for the images.
  have htri : ‖f B - f A‖ ≤ ‖f B - f P‖ + ‖f P - f A‖ := by
    have he : f B - f A = (f B - f P) + (f P - f A) := by abel
    rw [he]
    exact norm_add_le _ _
  have hx : t * ‖B - A‖ + (1 - t) * ‖B - A‖ = ‖B - A‖ := by ring
  -- All inequalities are equalities.
  have hsum : ‖f P - f A‖ + ‖f B - f P‖ = ‖B - A‖ := by
    linarith [h1, h2, htri, hpre, hx]
  have ha1' : ‖f P - f A‖ = t * ‖B - A‖ := by linarith [h1, h2, hsum, hx]
  have ha2' : ‖f B - f P‖ = (1 - t) * ‖B - A‖ := by linarith [h1, h2, hsum, hx]
  have ha1 : ‖f P - f A‖ = t * ‖f B - f A‖ := by rw [hpre]; exact ha1'
  have ha2 : ‖f B - f P‖ = (1 - t) * ‖f B - f A‖ := by rw [hpre]; exact ha2'
  exact eq_smul_add_of_norm_eq_norm_sub ha1 ha2

theorem image_segment_affine {a : ℝ} {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hf : Commons.PaperMoebius.IsMoebiusEmbedding a f)
    {A B : EuclideanSpace ℝ (Fin 2)}
    (hA : A ∈ Commons.PaperMoebius.unitStrip) (hB : B ∈ Commons.PaperMoebius.unitStrip)
    (hpre : ‖f B - f A‖ = ‖B - A‖) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    f ((1 - t) • A + t • B) = (1 - t) • f A + t • f B :=
  image_segment_affine_of_lipschitz unitStrip_convex
    (fun _ hx _ hy => embedding_lipschitz_strip hf hx hy) hA hB hpre ht

end Commons.Geometry.Moebius