import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.SinCompleteDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Auxiliary lemmas for `Work.FTS.EllipticEst.sin_complete_Ioc`.

The odd extension `sinOdd F` of `F` has all Fourier coefficients on the circle of period `2L`
equal (up to a constant) to the sine coefficients `∫_0^L F θ sin (n π θ / L) dθ`; Parseval's
identity then forces `F` to vanish a.e.
-/

open MeasureTheory Set
open scoped Interval

namespace Work.FTS.EllipticEst

/-- The odd extension of an `L²` function on `(0,L)` is `L²` on `(-L,L)`. -/
theorem sinOdd_memLp {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MemLp F 2 (volume.restrict (Ioc (0:ℝ) L))) :
    MemLp (sinOdd F) 2 (volume.restrict (Ioc (-L) L)) := by
  have hpos : MemLp (sinOdd F) 2 (volume.restrict (Ioc (0:ℝ) L)) := by
    refine MemLp.ae_eq ?_ (hmem.ofReal (K := ℂ))
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact (sinOdd_of_pos hx.1).symm
  have hneg : MemLp (sinOdd F) 2 (volume.restrict (Ioc (-L) 0)) := by
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ico (0:ℝ) L = Set.Ioc (-L) 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_Ioc]
      constructor
      · intro hx; exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1]⟩
      · intro hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmap : Measure.map (fun x : ℝ => -x) (volume.restrict (Ioc (-L) 0))
        = volume.restrict (Ico (0:ℝ) L) := by
      have h := measurableEmbedding_neg.restrict_map (volume : Measure ℝ) (Set.Ico (0:ℝ) L)
      rw [Measure.map_neg_eq_self] at h
      rw [hpre] at h
      exact h.symm
    have hg : MemLp (fun y : ℝ => (F y : ℂ)) 2 (volume.restrict (Ico (0:ℝ) L)) := by
      rw [Measure.restrict_congr_set
        (MeasureTheory.Ico_ae_eq_Ioc' (μ := volume) (a := (0:ℝ)) (b := L) (by simp) (by simp))]
      exact hmem.ofReal (K := ℂ)
    have hcomp : MemLp (fun x : ℝ => (F (-x) : ℂ)) 2 (volume.restrict (Ioc (-L) 0)) := by
      have h' : MemLp (fun y : ℝ => (F y : ℂ)) 2
          (Measure.map (fun x : ℝ => -x) (volume.restrict (Ioc (-L) 0))) := by
        rw [hmap]; exact hg
      have h2 := h'.comp_of_map (f := fun x : ℝ => -x) measurable_neg.aemeasurable
      exact h2
    refine MemLp.ae_eq ?_ (memLp_neg_iff.mpr hcomp)
    rw [← Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Ioc' (μ := volume) (a := (-L)) (b := (0:ℝ)) (by simp))]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    simp only [Pi.neg_apply, sinOdd_of_neg hx.2]
  have hμ : volume.restrict (Ioc (-L) L)
      = volume.restrict (Ioc (-L) 0) + volume.restrict (Ioc (0:ℝ) L) := by
    have hun : Set.Ioc (-L) L = Set.Ioc (-L) 0 ∪ Set.Ioc (0:ℝ) L := by
      ext x
      simp only [Set.mem_Ioc, Set.mem_union]
      constructor
      · intro hx
        by_cases h : x ≤ 0
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr ⟨lt_of_not_ge h, hx.2⟩
      · rintro (hx | hx)
        · exact ⟨hx.1, by linarith [hx.2]⟩
        · exact ⟨by linarith [hx.1], hx.2⟩
    have hd : Disjoint (Set.Ioc (-L) 0) (Set.Ioc (0:ℝ) L) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx'.1 (not_lt.mpr hx.2)
    rw [hun, Measure.restrict_union hd measurableSet_Ioc]
  rw [hμ]
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
  · exact hneg.aestronglyMeasurable.add_measure hpos.aestronglyMeasurable
  · rw [integrable_add_measure]
    exact ⟨(memLp_two_iff_integrable_sq_norm hneg.aestronglyMeasurable).mp hneg,
      (memLp_two_iff_integrable_sq_norm hpos.aestronglyMeasurable).mp hpos⟩

/-- If all the sine coefficients `∫_0^L F θ sin (n π θ / L) dθ` for `n ≥ 1` vanish, then the
same integrals vanish for *all* integer frequencies, as complex integrals. -/
theorem sinInt_eq_zero {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (h : ∀ n : ℕ, 0 < n → ∫ θ in (0:ℝ)..L, F θ * Real.sin (n * Real.pi * θ / L) = 0) :
    ∀ m : ℤ, ∫ θ in (0:ℝ)..L, (Real.sin (Real.pi * m * θ / L) : ℂ) * (F θ : ℂ) = 0 := by
  have hcast : ∀ m : ℤ,
      (∫ θ in (0:ℝ)..L, (Real.sin (Real.pi * m * θ / L) : ℂ) * (F θ : ℂ))
        = ((∫ θ in (0:ℝ)..L, Real.sin (Real.pi * m * θ / L) * F θ : ℝ) : ℂ) := by
    intro m
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Complex.ofReal_mul]
  have key : ∀ k : ℤ, 0 < k →
      (∫ θ in (0:ℝ)..L, Real.sin (Real.pi * k * θ / L) * F θ) = 0 := by
    intro k hk
    have hk0 : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
    have hk' : 0 < k.toNat := by
      refine Nat.pos_of_ne_zero (fun h0 => ?_)
      rw [h0] at hk0
      simp at hk0
      omega
    have hkR : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hk0
    have h1 := h k.toNat hk'
    have h2 : (∫ θ in (0:ℝ)..L, Real.sin (Real.pi * k * θ / L) * F θ)
        = ∫ θ in (0:ℝ)..L, F θ * Real.sin (k.toNat * Real.pi * θ / L) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [hkR]
      rw [show Real.pi * (k : ℝ) * θ / L = (k : ℝ) * Real.pi * θ / L from by ring]
      ring
    rw [h2, h1]
  intro m
  rw [hcast m]
  have hreal : (∫ θ in (0:ℝ)..L, Real.sin (Real.pi * m * θ / L) * F θ) = 0 := by
    rcases lt_trichotomy m 0 with hm | hm | hm
    · have hmn : 0 < -m := by omega
      have hpt : ∀ θ : ℝ, Real.sin (Real.pi * (m : ℝ) * θ / L) * F θ
          = -(Real.sin (Real.pi * (-(m : ℝ)) * θ / L) * F θ) := by
        intro θ
        have harg : Real.pi * (m : ℝ) * θ / L = -(Real.pi * (-(m : ℝ)) * θ / L) := by ring
        rw [harg, Real.sin_neg]
        ring
      have hargh : (∫ θ in (0:ℝ)..L, Real.sin (Real.pi * m * θ / L) * F θ)
          = -(∫ θ in (0:ℝ)..L, Real.sin (Real.pi * (-m) * θ / L) * F θ) := by
        rw [← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
      rw [hargh, neg_eq_zero]
      simpa using key (-m) hmn
    · rw [hm]; simp
    · exact key m hm
  rw [hreal, Complex.ofReal_zero]

/-- If the odd extension of `F` has vanishing `L²` norm on `Ioc (-L) L`, then `F` vanishes a.e.
on `Ioc 0 L`. -/
theorem sinOdd_ae_eq_zero {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ}
    (hmem : MemLp (sinOdd F) 2 (volume.restrict (Ioc (-L) L)))
    (hint : ∫ x in (-L)..L, ‖sinOdd F x‖ ^ 2 = 0) :
    F =ᵐ[volume.restrict (Ioc (0:ℝ) L)] 0 := by
  have hInt : Integrable (fun x => ‖sinOdd F x‖ ^ 2) (volume.restrict (Ioc (-L) L)) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hII : IntervalIntegrable (fun x => ‖sinOdd F x‖ ^ 2) volume (-L) L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (-L : ℝ) ≤ L)]
    exact hInt
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (-L) L ∪ Ioc L (-L))] (fun x => ‖sinOdd F x‖ ^ 2) :=
    Filter.Eventually.of_forall fun x => by positivity
  have hzero := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnn hII).mp hint
  have hU : Ioc (-L) L ∪ Ioc L (-L) = Ioc (-L) L := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc]
    refine ⟨fun h => ?_, fun h => Or.inl h⟩
    rcases h with h | h
    · exact h
    · exact absurd (lt_of_lt_of_le h.1 h.2) (not_lt.mpr (by linarith : (-L : ℝ) ≤ L))
  rw [hU] at hzero
  have h1 : sinOdd F =ᵐ[volume.restrict (Ioc (-L) L)] 0 := by
    filter_upwards [hzero] with x hx
    simpa [sq_eq_zero_iff, norm_eq_zero] using hx
  have hsub : Ioc (0:ℝ) L ⊆ Ioc (-L) L := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have h2 : sinOdd F =ᵐ[volume.restrict (Ioc (0:ℝ) L)] 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub h1
  filter_upwards [h2, self_mem_ae_restrict measurableSet_Ioc] with x hx hxm
  rw [sinOdd_of_pos hxm.1] at hx
  exact Complex.ofReal_eq_zero.mp hx

end Work.FTS.EllipticEst
