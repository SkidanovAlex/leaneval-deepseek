import Mathlib
import Submission.Work.OdeCont.defs

/-!
# The successive differences of the Picard iterates as integrals

For the initial value problem `X' = F(z, X)`, `X(z₀) = y`, the Picard iterates are

`iter (n+1) z = y + ∫ t in 0..1, (z - z₀) • F (z₀ + t • (z - z₀)) (iter n (z₀ + t • (z - z₀)))`.

Subtracting the defining equations for `iter (n+2)` and `iter (n+1)` at a point `z` and using
linearity of the interval integral (and `a • (x - y) = a • x - a • y`) gives

`iter (n+2) z - iter (n+1) z
   = ∫ t in 0..1, (z - z₀) • (F (z₀ + t • (z - z₀)) (iter (n+1) (z₀ + t • (z - z₀)))
                              - F (z₀ + t • (z - z₀)) (iter n (z₀ + t • (z - z₀))))`,

which is the `n`-th term of the telescoping series defining `iterLimit`. The only non-formal
input is that the integrands are continuous on `[0,1]`: this is where convexity of `S` is used,
to know that the whole segment `z₀ + t • (z - z₀)`, `t ∈ [0,1]`, lies in `S` and hence that
`w ↦ F w (iter k w)`, continuous on `S`, may be evaluated along it.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace Work.OdeCont

/-- Convexity: the point `z₀ + t • (z - z₀)` of the segment from `z₀` to `z` lies in `S`
whenever `z₀, z ∈ S`, `S` is convex, and `t ∈ [0,1]`. -/
private lemma iter_sub_eq_integral_seg_mem {S : Set ℂ} (hS : Convex ℝ S) {z₀ z : ℂ}
    (hz₀ : z₀ ∈ S) (hz : z ∈ S) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    z₀ + t • (z - z₀) ∈ S := by
  have h_eq : z₀ + t • (z - z₀) = (1 - t) • z₀ + t • z := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [h_eq]
  exact (convex_iff_add_mem.mp hS hz₀ hz) (by linarith) (by linarith) (by ring)

/-- `t ↦ F (z₀ + t • (z - z₀)) (iter k (z₀ + t • (z - z₀)))` is continuous on `[0,1]`,
as the composition of the continuous map `t ↦ z₀ + t • (z - z₀)` (which maps `[0,1]` into the
convex set `S`) with `w ↦ F w (iter k w)`, continuous on `S`. -/
private lemma iter_sub_eq_integral_contOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) (S : Set ℂ)
    (hS : Convex ℝ S) (hz₀ : z₀ ∈ S)
    (hGcont : ∀ n, ContinuousOn (fun w => F w (iter F z₀ y n w)) S)
    (n : ℕ) (z : ℂ) (hz : z ∈ S) :
    ContinuousOn (fun t : ℝ => F (z₀ + t • (z - z₀))
      (iter F z₀ y n (z₀ + t • (z - z₀)))) (Set.Icc 0 1) := by
  have hφ : ContinuousOn (fun t : ℝ => z₀ + t • (z - z₀)) (Set.Icc 0 1) := by
    apply ContinuousOn.add continuousOn_const
    exact continuousOn_id.smul continuousOn_const
  exact (hGcont n).comp' hφ fun t ht =>
    iter_sub_eq_integral_seg_mem hS hz₀ hz ht.1 ht.2

theorem iter_sub_eq_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) (S : Set ℂ)
    (hS : Convex ℝ S) (hz₀ : z₀ ∈ S)
    (hGcont : ∀ n, ContinuousOn (fun w => F w (iter F z₀ y n w)) S)
    (n : ℕ) (z : ℂ) (hz : z ∈ S) :
    iter F z₀ y (n+2) z - iter F z₀ y (n+1) z
      = ∫ t in (0:ℝ)..1, (z - z₀) •
          (F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀)))
            - F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀)))) := by
  have hcont1 := iter_sub_eq_integral_contOn F z₀ y S hS hz₀ hGcont (n+1) z hz
  have hcont0 := iter_sub_eq_integral_contOn F z₀ y S hS hz₀ hGcont n z hz
  have hInt1 : IntervalIntegrable
      (fun t : ℝ => (z - z₀) • F (z₀ + t • (z - z₀)) (iter F z₀ y (n+1) (z₀ + t • (z - z₀))))
      volume 0 1 :=
    (hcont1.const_smul (z - z₀)).intervalIntegrable_of_Icc zero_le_one
  have hInt0 : IntervalIntegrable
      (fun t : ℝ => (z - z₀) • F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀))))
      volume 0 1 :=
    (hcont0.const_smul (z - z₀)).intervalIntegrable_of_Icc zero_le_one
  -- unfold the two defining integrals and cancel the common initial term `y`
  rw [iter_succ F z₀ y (n+1) z, iter_succ F z₀ y n z]
  rw [add_sub_add_left_eq_sub]
  -- linearity of the interval integral in the integrand
  rw [← integral_sub hInt1 hInt0]
  -- `a • x - a • y = a • (x - y)`
  congr 1 with t
  rw [← smul_sub]

end Work.OdeCont
