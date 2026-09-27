import Mathlib
import Submission.Work.KT.EG.KLG.linBig_defs
import Submission.Work.KT.EG.KLG.isUnit_mobius_family
import Submission.Work.KT.Fund.isUnit_matrix_forall

namespace Work.KT.EG.KLG

/-!
# `Work.KT.EG.KLG.isUnit_linBig`

The matrix `linBig X a b t₀` over `C((X × I) × S¹, ℂ)` is the homotopy

  `z • (a + (s t₀) b) + (s t₀) • a + b`   (`s` the interval coordinate, `z` the circle coordinate)

which deforms `z • a + b` (`s = 0`) to `z • (a + t₀ b) + t₀ • a + b` (`s = 1`).  If `z • a + b` is
pointwise invertible for every `|z| = 1` and `t₀ ∈ [0, 1)`, then every slice of the homotopy is
invertible, by the Möbius identity

  `z • (A + t B) + t A + B = (1 + t z) • (((z + t)/(1 + t z)) • A + B)`

together with the fact that `(z + t)/(1 + t z)` lies on the unit circle when `‖z‖ = 1` and
`|t| < 1`.
-/

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The constant function `cylConst t₀` evaluated at a point. -/
lemma cylConst_apply {Y : Type} [TopologicalSpace Y] (t₀ : ℝ) (q : Y) :
    (cylConst t₀ : C(Y, ℂ)) q = (t₀ : ℂ) := by
  simp [cylConst]

/-- Pointwise evaluation of `linBig`: at `q = ((x, s), z)` it is
`z • (a(x) + (s t₀) • b(x)) + (s t₀) • a(x) + b(x)`. -/
lemma linBig_eval {n : ℕ} (a b : Matrix (Fin n) (Fin n) C(X, ℂ)) (t₀ : ℝ)
    (q : (X × unitInterval) × Sph ℂ) :
    (linBig X a b t₀).map (fun f => f q)
      = ((q.2 : Sph ℂ) : ℂ) • (a.map (fun f => f q.1.1)
          + (((((q.1.2 : unitInterval) : ℝ) * t₀ : ℝ)) : ℂ) • b.map (fun f => f q.1.1))
        + (((((q.1.2 : unitInterval) : ℝ) * t₀ : ℝ)) : ℂ) • a.map (fun f => f q.1.1)
        + b.map (fun f => f q.1.1) := by
  ext i j
  simp only [linBig, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Work.KT.EG.pullBig_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    Work.KT.EG.tCyl_apply, cylConst_apply, Work.KT.EG.zCyl,
    Work.KT.zUnit_apply, smul_eq_mul, ← Complex.ofReal_mul]

/-- **Möbius unit criterion with a real parameter.**  If `‖z‖ = 1`, `0 ≤ r < 1` and every unit
circle point `w` makes `w • A + B` invertible, then `z • (A + r B) + r A + B` is invertible. -/
lemma isUnit_mobius_real {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hz : ‖z‖ = 1)
    (hu : ∀ w : ℂ, ‖w‖ = 1 → IsUnit (w • A + B)) :
    IsUnit (z • (A + (r : ℂ) • B) + (r : ℂ) • A + B) := by
  have htz : 1 + (r : ℂ) * z ≠ 0 := by
    intro hzero
    have h1 : (r : ℂ) * z = -1 := by linear_combination hzero
    have h2 : ‖(r : ℂ) * z‖ = 1 := by rw [h1]; norm_num
    rw [norm_mul, hz, mul_one, norm_ofReal_complex, abs_of_nonneg hr0] at h2
    linarith
  have hζ : ‖(z + (r : ℂ)) / (1 + (r : ℂ) * z)‖ = 1 := by
    have hsq := normSq_mobius z r hz
    have hne : Complex.normSq (1 + (r : ℂ) * z) ≠ 0 :=
      fun h => htz (Complex.normSq_eq_zero.mp h)
    have hmain : Complex.normSq ((z + (r : ℂ)) / (1 + (r : ℂ) * z)) = 1 := by
      rw [Complex.normSq_div, hsq, div_self hne]
    rw [Complex.normSq_eq_norm_sq] at hmain
    nlinarith [norm_nonneg ((z + (r : ℂ)) / (1 + (r : ℂ) * z))]
  exact isUnit_mobius A B z (r : ℂ) htz (hu _ hζ)

theorem isUnit_linBig (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ}
    (a b : Matrix (Fin n) (Fin n) C(X, ℂ)) (t₀ : ℝ) (ht0 : 0 ≤ t₀) (ht1 : t₀ < 1)
    (hu : ∀ (x : X) (z : ℂ), ‖z‖ = 1 →
      IsUnit (z • (a.map (fun f => f x)) + b.map (fun f => f x))) :
    IsUnit (Work.KT.EG.KLG.linBig X a b t₀) := by
  rw [Work.KT.Fund.isUnit_matrix_forall]
  intro q
  rw [linBig_eval X a b t₀ q]
  refine isUnit_mobius_real (a.map (fun f => f q.1.1)) (b.map (fun f => f q.1.1))
    ((q.2 : Sph ℂ) : ℂ) (((q.1.2 : unitInterval) : ℝ) * t₀) ?_ ?_ ?_ ?_
  · exact mul_nonneg q.1.2.2.1 ht0
  · nlinarith [q.1.2.2.1, q.1.2.2.2, ht1]
  · have h := Metric.mem_sphere.mp q.2.2
    rwa [dist_eq_norm, sub_zero] at h
  · intro w hw
    exact hu q.1.1 w hw

end Work.KT.EG.KLG
