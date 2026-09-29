import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory Set

/-- The real logarithm is invariant under `u ↦ u / ρ` composed with `|·|`:
`log (ρ / u) = log (ρ / |u|)`. -/
private lemma log_div_eq_log_div_abs {ρ : ℝ} (hρ : 0 < ρ) (u : ℝ) :
    Real.log (ρ / u) = Real.log (ρ / |u|) := by
  rw [← Real.log_abs (ρ / u), abs_div, abs_of_pos hρ]

theorem rcLogKernel_integrable {ρ s : ℝ} (hρ : 0 < ρ) :
    MeasureTheory.Integrable (fun t : ℝ => max (Real.log (ρ / |t - s|)) 0)
      MeasureTheory.volume := by
  -- `u ↦ log (ρ / u)` is interval integrable near the origin, being the logarithm of a
  -- meromorphic function.
  have hmero : MeromorphicOn (fun u : ℝ => ρ / u) (Set.uIcc (-ρ) ρ) :=
    (MeromorphicOn.const (U := Set.uIcc (-ρ) ρ) ρ).div
      (MeromorphicOn.id (U := Set.uIcc (-ρ) ρ))
  have hbase0 : IntervalIntegrable (Real.log ∘ (fun u : ℝ => ρ / u)) volume (-ρ) ρ :=
    hmero.intervalIntegrable_log
  have hbase : IntervalIntegrable (fun u : ℝ => Real.log (ρ / |u|)) volume (-ρ) ρ :=
    IntervalIntegrable.congr (f := Real.log ∘ (fun u : ℝ => ρ / u))
      (g := fun u : ℝ => Real.log (ρ / |u|))
      (fun u _ => log_div_eq_log_div_abs hρ u) hbase0
  -- Translate the interval so that it is centred at `s`.
  have hshift : IntervalIntegrable (fun t : ℝ => Real.log (ρ / |t - s|)) volume (s - ρ) (s + ρ) := by
    have h := hbase.comp_sub_right s
    have h₁ : ((-ρ) + s) = (s - ρ) := by ring
    have h₂ : (ρ + s) = (s + ρ) := by ring
    rwa [h₁, h₂] at h
  have hρle : s - ρ ≤ s + ρ := by linarith
  have hIO : IntegrableOn (fun t : ℝ => Real.log (ρ / |t - s|)) (Set.Ioo (s - ρ) (s + ρ)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hρle).mp hshift
  -- On the interval, the logarithm is nonnegative, so the positive part is the function itself.
  have hIO' : IntegrableOn (fun t : ℝ => max (Real.log (ρ / |t - s|)) 0)
      (Set.Ioo (s - ρ) (s + ρ)) volume := by
    refine hIO.congr_fun ?_ measurableSet_Ioo
    intro t ht
    rw [Set.mem_Ioo] at ht
    rcases eq_or_ne t s with rfl | hne
    · simp
    · have hlt : |t - s| < ρ := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hpos : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr hne)
      have h1 : 1 < ρ / |t - s| := (one_lt_div hpos).mpr hlt
      have h2 : 0 ≤ Real.log (ρ / |t - s|) := Real.log_nonneg h1.le
      exact (max_eq_left h2).symm
  -- The kernel vanishes outside the interval, so integrability on the interval suffices.
  refine hIO'.integrable_of_forall_notMem_eq_zero (fun t ht => ?_)
  have hge : ρ ≤ |t - s| := by
    by_contra h
    rw [not_le] at h
    rw [abs_lt] at h
    exact ht ⟨by linarith [h.1], by linarith [h.2]⟩
  have h0 : 0 ≤ ρ / |t - s| := div_nonneg hρ.le (abs_nonneg _)
  have h1 : ρ / |t - s| ≤ 1 := (div_le_one (lt_of_lt_of_le hρ hge)).mpr hge
  have h2 : Real.log (ρ / |t - s|) ≤ 0 := Real.log_nonpos h0 h1
  exact max_eq_right h2

end Work.TMComp.RealCartan
