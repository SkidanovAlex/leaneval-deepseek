import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound
import Submission.Work.NN.Core.CzBfar.volume_ball_le

namespace Work.NN.Core.CzBfar

open MeasureTheory Set

/-- Far-field bound for the singular integral: if `F` is bounded by `A` and vanishes off the
sup-norm ball of radius `r`, and the translated support window `{x | ‖z + x‖ < r}` stays outside
the Euclidean ball of radius `3r`, then `‖∫ bmDzKernel i l x · F (z+x)‖ ≤ C A`.

Indeed the integrand is supported in the sup-norm ball of radius `r` around `-z`, where the kernel
is bounded by `n/(3r)^{2n}`, and that ball has volume `≤ C r^{2n}` (`volume_ball_le`). -/
theorem far_single_bound {n : ℕ} (hn : 0 < n) (i l : Fin n) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (Fin n → ℂ) → ℂ) (A : ℝ) (z : Fin n → ℂ),
      0 ≤ A → (∀ x, ‖F x‖ ≤ A) → (∀ x, r ≤ ‖x‖ → F x = 0) →
      (∀ x, ‖z + x‖ < r → 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x) →
      ‖∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x)‖ ≤ C * A := by
  classical
  obtain ⟨Cvol, hCvolpos, hCvol⟩ := volume_ball_le hn
  refine ⟨Cvol * ((n : ℝ) / 3 ^ (2 * n)), by positivity, ?_⟩
  intro F A z hA hbdd hsupp hgeo
  set g : (Fin n → ℂ) → ℂ := fun x => Work.CR.Flat.Cauchy.bmDzKernel i l x * F (z + x) with hgdef
  set T : Set (Fin n → ℂ) := {x | ‖z + x‖ < r} with hTdef
  have hTball : T = Metric.ball (-z) r := by
    ext x
    simp only [hTdef, Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
    rw [add_comm z x, sub_neg_eq_add]
  have hTfin : volume T < ⊤ := by
    rw [hTball]; exact MeasureTheory.measure_ball_lt_top
  have hg0 : ∀ x, x ∉ T → g x = 0 := by
    intro x hx
    have hx' : r ≤ ‖z + x‖ := by
      rw [hTdef] at hx
      simp only [Set.mem_setOf_eq] at hx
      exact le_of_not_gt hx
    simp [hgdef, hsupp (z + x) hx']
  have hpt : ∀ x ∈ T, ‖g x‖ ≤ (n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * A := by
    intro x hx
    have hxr : ‖z + x‖ < r := by
      rw [hTdef] at hx; exact hx
    have h3r : 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x := hgeo x hxr
    have hxne : x ≠ 0 := by
      intro h0
      rw [h0] at h3r
      simp only [Work.CR.Flat.Cauchy.eucNorm_zero] at h3r
      linarith
    have hker := Work.CR.Flat.Cauchy.BmDzCzAux.norm_bmDzKernel_le i l hxne
    have hden : (3 * r) ^ (2 * n) ≤ Work.CR.Flat.Cauchy.eucNorm x ^ (2 * n) :=
      pow_le_pow_left₀ (by linarith) h3r _
    have hdenpos : 0 < (3 * r) ^ (2 * n) := pow_pos (by linarith) _
    have h1 : (n : ℝ) / Work.CR.Flat.Cauchy.eucNorm x ^ (2 * n)
        ≤ (n : ℝ) / (3 * r) ^ (2 * n) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg n) hdenpos hden
    have h2 : (n : ℝ) / (3 * r) ^ (2 * n) = (n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) := by
      rw [mul_pow]
      field_simp
    calc ‖g x‖ = ‖Work.CR.Flat.Cauchy.bmDzKernel i l x‖ * ‖F (z + x)‖ := by
          simp only [hgdef, norm_mul]
      _ ≤ ((n : ℝ) / Work.CR.Flat.Cauchy.eucNorm x ^ (2 * n)) * A :=
          mul_le_mul hker (hbdd (z + x)) (norm_nonneg _)
            (div_nonneg (Nat.cast_nonneg n) (pow_nonneg (Work.CR.Flat.Cauchy.eucNorm_nonneg x) _))
      _ ≤ ((n : ℝ) / (3 * r) ^ (2 * n)) * A := mul_le_mul_of_nonneg_right h1 hA
      _ = (n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * A := by rw [h2]
  have hvolT : (volume T).toReal ≤ Cvol * r ^ (2 * n) := by
    rw [hTball]
    exact hCvol (-z) r hr
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hg0]
  have hmain : ‖∫ x in T, g x‖
      ≤ ((n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * A) * (volume T).toReal :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const hTfin hpt
  have hnum : ((n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * A) * (Cvol * r ^ (2 * n))
      = Cvol * ((n : ℝ) / 3 ^ (2 * n)) * A := by
    field_simp
  calc ‖∫ x in T, g x‖
      ≤ ((n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * A) * (volume T).toReal := hmain
    _ ≤ ((n : ℝ) / r ^ (2 * n) / 3 ^ (2 * n) * A) * (Cvol * r ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left hvolT (by positivity)
    _ = Cvol * ((n : ℝ) / 3 ^ (2 * n)) * A := hnum

end Work.NN.Core.CzBfar
