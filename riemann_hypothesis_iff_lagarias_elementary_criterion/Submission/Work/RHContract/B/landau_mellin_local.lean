import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.B.head_analytic
import Submission.Work.RHContract.B.landau_mellin_core_c

namespace Work.RHContract.B

open MeasureTheory

noncomputable section

/-- The "head" of the Mellin transform below, the integral over the compact interval `(1, x₀]`;
it is entire in `s` (see `head_analytic`). -/
def mellinHead (f : ℝ → ℝ) (x₀ : ℝ) (s : ℂ) : ℂ :=
  ∫ x in (1 : ℝ)..x₀, (f x : ℂ) * (x : ℂ) ^ (-s - 1)

theorem landau_mellin_local
    (f : ℝ → ℝ) (x₀ c r : ℝ) (hx₀ : 1 ≤ x₀) (hr : 0 < r) (hmeas : Measurable f)
    (hnonneg : ∀ x : ℝ, x₀ ≤ x → 0 ≤ f x)
    (hint : ∀ a : ℝ, c < a → MeasureTheory.IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioi 1))
    (hcont : ∃ G : ℂ → ℂ, AnalyticOn ℂ G (Metric.ball (c : ℂ) r) ∧
        ∀ s : ℂ, c < s.re → G s = ∫ x in Set.Ioi 1, (f x : ℂ) * (x : ℂ) ^ (-s - 1)) :
    ∃ a : ℝ, a < c ∧ MeasureTheory.IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioi 1) := by
  obtain ⟨G, hGan, hGi⟩ := hcont
  -- Integrability of `f` on `(1, x₀]`, from `hint` at any exponent `> c`.
  have hf_loc : IntegrableOn f (Set.Ioc 1 x₀) := by
    have h1 : IntegrableOn (fun x : ℝ => f x * x ^ (-(c+1) - 1)) (Set.Ioc 1 x₀) :=
      (hint (c+1) (by linarith)).mono_set Set.Ioc_subset_Ioi_self
    have hcont' : ContinuousOn (fun x : ℝ => x ^ (c+2)) (Set.Icc 1 x₀) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (by
        have : (0:ℝ) < x := by linarith [hx.1]
        exact ne_of_gt this))
    have h2 : IntegrableOn (fun x : ℝ => (f x * x ^ (-(c+1) - 1)) * x ^ (c+2)) (Set.Ioc 1 x₀) :=
      h1.mul_continuousOn_of_subset hcont' measurableSet_Ioc isCompact_Icc Set.Ioc_subset_Icc_self
    refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioc
    change f x * x ^ (-(c+1) - 1) * x ^ (c+2) = f x
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    rw [mul_assoc, ← Real.rpow_add hx0]
    have : -(c+1) - 1 + (c+2) = 0 := by ring
    rw [this, Real.rpow_zero, mul_one]
  -- The continuation of the tail.
  have hhead : AnalyticOn ℂ (mellinHead f x₀) (Metric.ball (c : ℂ) r) := by
    have hd : Differentiable ℂ (mellinHead f x₀) := head_analytic f x₀ hx₀ hf_loc
    exact hd.differentiableOn.analyticOn Metric.isOpen_ball
  have hA : AnalyticOn ℂ (fun s : ℂ => G s - mellinHead f x₀ s) (Metric.ball (c : ℂ) r) :=
    hGan.sub hhead
  have hAint : ∀ s : ℂ, c < s.re →
      (fun s : ℂ => G s - mellinHead f x₀ s) s
        = ∫ x in Set.Ioi x₀, (f x : ℂ) * (x:ℂ)^(-s-1) := by
    intro s hs
    change G s - (∫ x in (1:ℝ)..x₀, (f x : ℂ) * (x:ℂ)^(-s-1))
        = ∫ x in Set.Ioi x₀, (f x : ℂ) * (x:ℂ)^(-s-1) ∂volume
    have hG_eq : G s = ∫ x in Set.Ioi 1, (f x:ℂ)*(x:ℂ)^(-s-1) ∂volume := hGi s hs
    have hhead_eq : (∫ x in (1:ℝ)..x₀, (f x : ℂ) * (x:ℂ)^(-s-1))
        = ∫ x in Set.Ioc 1 x₀, (f x:ℂ)*(x:ℂ)^(-s-1) ∂volume := intervalIntegral.integral_of_le hx₀
    have hInt1 : IntegrableOn (fun x => (f x:ℂ)*(x:ℂ)^(-s-1)) (Set.Ioi 1) := by
      have hfc : AEStronglyMeasurable (fun x : ℝ => (f x : ℂ)) (volume.restrict (Set.Ioi 0)) :=
        (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable
      have hnorm : IntegrableOn (fun x : ℝ => x ^ ((-s).re - 1) * ‖(f x : ℂ)‖) (Set.Ioi 1) := by
        have h := (hint s.re hs).norm
        refine (integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioi).mp h
        have hx0 : (0:ℝ) < x := by linarith [Set.mem_Ioi.mp hx]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _), Complex.norm_real,
          Real.norm_eq_abs, Complex.neg_re]
        ring
      have hkey := (mellin_convergent_iff_norm (E := ℂ) (f := fun x : ℝ => (f x : ℂ))
        (T := Set.Ioi 1) (s := -s) (Set.Ioi_subset_Ioi (by norm_num)) measurableSet_Ioi hfc).mpr hnorm
      simpa only [smul_eq_mul, mul_comm] using hkey
    have hU : Set.Ioi (1:ℝ) = Set.Ioc 1 x₀ ∪ Set.Ioi x₀ := by
      have h := Set.Ioc_union_Ioi (a:=1) (b:=x₀) (c:=x₀) (by simp)
      rw [min_eq_left hx₀] at h
      exact h.symm
    have hsplit : ∫ x in Set.Ioi 1, (f x:ℂ)*(x:ℂ)^(-s-1) ∂volume
        = ∫ x in Set.Ioc 1 x₀, (f x:ℂ)*(x:ℂ)^(-s-1) ∂volume
          + ∫ x in Set.Ioi x₀, (f x:ℂ)*(x:ℂ)^(-s-1) ∂volume := by
      rw [hU]
      exact MeasureTheory.setIntegral_union (μ := volume) (f := fun x => (f x:ℂ)*(x:ℂ)^(-s-1))
        (s := Set.Ioc 1 x₀) (t := Set.Ioi x₀)
        (Set.Ioc_disjoint_Ioi (le_refl x₀)) measurableSet_Ioi
        (hInt1.mono_set Set.Ioc_subset_Ioi_self) (hInt1.mono_set (Set.Ioi_subset_Ioi hx₀))
    rw [hG_eq, hhead_eq, hsplit]
    rw [add_sub_cancel_left]
  -- The abstract Landau lemma.
  have hconv : ∀ a : ℝ, c < a → IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioi x₀) :=
    fun a ha => (hint a ha).mono_set (Set.Ioi_subset_Ioi hx₀)
  obtain ⟨a, hac, htail⟩ := landau_mellin_core_c f x₀ c r hr hx₀ hmeas hnonneg hconv
    (fun s : ℂ => G s - mellinHead f x₀ s) hA hAint
  refine ⟨a, hac, ?_⟩
  -- Add back the compact piece `(1, x₀]`.
  have hIoc : IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioc 1 x₀) := by
    have hca : ContinuousOn (fun x : ℝ => x ^ (-a-1)) (Set.Icc 1 x₀) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (by
        have : (0:ℝ) < x := by linarith [hx.1]
        exact ne_of_gt this))
    exact hf_loc.mul_continuousOn_of_subset hca measurableSet_Ioc isCompact_Icc Set.Ioc_subset_Icc_self
  have hU : Set.Ioi (1:ℝ) = Set.Ioc 1 x₀ ∪ Set.Ioi x₀ := by
    have h := Set.Ioc_union_Ioi (a:=1) (b:=x₀) (c:=x₀) (by simp)
    rw [min_eq_left hx₀] at h
    exact h.symm
  rw [hU]
  exact hIoc.union htail

end

end Work.RHContract.B
