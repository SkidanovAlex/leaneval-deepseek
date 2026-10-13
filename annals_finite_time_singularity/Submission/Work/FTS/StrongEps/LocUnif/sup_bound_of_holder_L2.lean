import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set

/-- **Averaging lemma (one dimensional).** If `f` is integrable on `[u,v]` (`u < v`) and its
integral on `[u,v]` is at most `C`, then `f` takes a value at most `(C+1)/(v-u)` somewhere on
`[u,v]`.  (The constant `C+1` instead of `C` is what makes the argument work with a plain
pointwise comparison, no strictness or attainment of a minimum is needed.) -/
private lemma exists_le_of_setIntegral_le {u v C : ℝ} {f : ℝ → ℝ} (huv : u < v)
    (hfint : IntegrableOn f (Set.Icc u v)) (hC : ∫ x in Set.Icc u v, f x ≤ C) :
    ∃ x ∈ Set.Icc u v, f x ≤ (C + 1) / (v - u) := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hle : ∀ x ∈ Set.Icc u v, (C + 1) / (v - u) ≤ f x := fun x hx => (h x hx).le
  have hμ : volume (Set.Icc u v) ≠ ⊤ := by simp
  have hge := setIntegral_ge_of_const_le (s := Set.Icc u v) (f := f)
    (c := (C + 1) / (v - u)) measurableSet_Icc hμ hle hfint
  rw [Real.volume_real_Icc_of_le huv.le, smul_eq_mul] at hge
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
  have hone : (v - u) * ((C + 1) / (v - u)) = C + 1 := by field_simp
  rw [hone] at hge
  linarith

theorem sup_bound_of_holder_L2 {ι : Type*} {M : ι → ℝ → ℝ → ℝ} {a b c d C₁ C₂ : ℝ}
    (hab : a < b) (hcd : c < d) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcont : ∀ n : ι, ContinuousOn (fun p : ℝ × ℝ => M n p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hholder : ∀ n p q, p ∈ Set.Icc a b ×ˢ Set.Icc c d → q ∈ Set.Icc a b ×ˢ Set.Icc c d →
      |M n p.1 p.2 - M n q.1 q.2| ≤ C₁ * dist p q ^ (1 / 2 : ℝ))
    (hL2 : ∀ n, ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (M n z θ) ^ 2 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n p, p ∈ Set.Icc a b ×ˢ Set.Icc c d → |M n p.1 p.2| ≤ C := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hKpos : 0 < ((C₂ + 1) / (b - a) + 1) / (d - c) := by
    have h1 : 0 < (C₂ + 1) / (b - a) := div_pos (by linarith) hba
    exact div_pos (by linarith) hdc
  refine ⟨√(((C₂ + 1) / (b - a) + 1) / (d - c))
      + C₁ * ((b - a) + (d - c)) ^ (1 / 2 : ℝ) + 1, ?_, ?_⟩
  · have hs : 0 < √(((C₂ + 1) / (b - a) + 1) / (d - c)) := Real.sqrt_pos.mpr hKpos
    have hr : 0 ≤ ((b - a) + (d - c)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have := mul_nonneg hC₁ hr
    linarith
  · intro n p hp
    -- ### Step 1: a point `z₀` whose `θ`-slice energy is small.
    --
    -- The (iterated) hypothesis `hL2` is a statement about the honest value of the outer
    -- integral, which requires the outer integrand to be integrable.  We obtain integrability
    -- from continuity, by clamping the two variables into the box: the clamped function is
    -- globally continuous and agrees with `M n` on the box.
    have hexists : ∃ z ∈ Set.Icc a b, (∫ θ in Set.Icc c d, (M n z θ) ^ 2) ≤ (C₂ + 1) / (b - a) := by
      have hcl1 : Continuous fun t : ℝ => max a (min b t) :=
        continuous_const.max (continuous_const.min continuous_id)
      have hcl2 : Continuous fun t : ℝ => max c (min d t) :=
        continuous_const.max (continuous_const.min continuous_id)
      have hm1 : ∀ t : ℝ, max a (min b t) ∈ Set.Icc a b := fun t =>
        ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩
      have hm2 : ∀ t : ℝ, max c (min d t) ∈ Set.Icc c d := fun t =>
        ⟨le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
      have hid1 : ∀ t ∈ Set.Icc a b, max a (min b t) = t := fun t ht => by
        rw [min_eq_right ht.2, max_eq_right ht.1]
      have hid2 : ∀ t ∈ Set.Icc c d, max c (min d t) = t := fun t ht => by
        rw [min_eq_right ht.2, max_eq_right ht.1]
      set G : ℝ → ℝ → ℝ := fun z θ => (M n (max a (min b z)) (max c (min d θ))) ^ 2 with hG
      have hpair : Continuous fun q : ℝ × ℝ =>
          (max a (min b q.1), max c (min d q.2)) :=
        continuous_prodMk.mpr
          ⟨hcl1.comp continuous_fst, hcl2.comp continuous_snd⟩
      have hcomp : Continuous fun q : ℝ × ℝ =>
          M n (max a (min b q.1)) (max c (min d q.2)) :=
        (hcont n).comp_continuous hpair (fun q => ⟨hm1 q.1, hm2 q.2⟩)
      have hGc : Continuous (Function.uncurry G) := by
        change Continuous fun q : ℝ × ℝ =>
            (M n (max a (min b q.1)) (max c (min d q.2))) ^ 2
        exact hcomp.pow 2
      have hHc : Continuous fun z : ℝ => ∫ θ in c..d, G z θ :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := G) hGc c d
      have hHG : ∀ z ∈ Set.Icc a b,
          (∫ θ in c..d, G z θ) = ∫ θ in Set.Icc c d, (M n z θ) ^ 2 := by
        intro z hz
        rw [intervalIntegral.integral_of_le hcd.le,
          MeasureTheory.integral_Icc_eq_integral_Ioc]
        refine setIntegral_congr_fun measurableSet_Ioc (fun θ hθ => ?_)
        simp only [hG, hid1 z hz, hid2 θ ⟨hθ.1.le, hθ.2⟩]
      have hHint : IntegrableOn (fun z : ℝ => ∫ θ in c..d, G z θ) (Set.Icc a b) :=
        hHc.integrableOn_Icc
      have hhint : IntegrableOn (fun z : ℝ => ∫ θ in Set.Icc c d, (M n z θ) ^ 2)
          (Set.Icc a b) :=
        (integrableOn_congr_fun (fun z hz => hHG z hz) measurableSet_Icc).mp hHint
      exact exists_le_of_setIntegral_le hab hhint (hL2 n)
    obtain ⟨z₀, hz₀mem, hz₀le⟩ := hexists
    -- ### Step 2: a point `θ₀` whose value is small.
    have hslice : ContinuousOn (fun θ : ℝ => M n z₀ θ) (Set.Icc c d) :=
      (hcont n).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => ⟨hz₀mem, hθ⟩)
    have hslice2 : ContinuousOn (fun θ : ℝ => (M n z₀ θ) ^ 2) (Set.Icc c d) :=
      hslice.pow 2
    obtain ⟨θ₀, hθ₀mem, hθ₀le⟩ :=
      exists_le_of_setIntegral_le hcd hslice2.integrableOn_Icc hz₀le
    -- ### Step 3: Hölder continuity transfers the bound to every point of the box.
    have hq : (z₀, θ₀) ∈ Set.Icc a b ×ˢ Set.Icc c d := ⟨hz₀mem, hθ₀mem⟩
    have hA : |M n z₀ θ₀| ≤ √(((C₂ + 1) / (b - a) + 1) / (d - c)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hθ₀le
    have hdist : dist p (z₀, θ₀) ≤ (b - a) + (d - c) := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
      constructor
      · rw [abs_le]; constructor <;> linarith [hp.1.1, hp.1.2, hz₀mem.1, hz₀mem.2]
      · rw [abs_le]; constructor <;> linarith [hp.2.1, hp.2.2, hθ₀mem.1, hθ₀mem.2]
    have hrpow : dist p (z₀, θ₀) ^ (1 / 2 : ℝ) ≤ ((b - a) + (d - c)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow dist_nonneg hdist (by norm_num)
    calc |M n p.1 p.2| ≤ |M n p.1 p.2 - M n z₀ θ₀| + |M n z₀ θ₀| := by
          have h := abs_add_le (M n p.1 p.2 - M n z₀ θ₀) (M n z₀ θ₀)
          rwa [sub_add_cancel] at h
      _ ≤ C₁ * dist p (z₀, θ₀) ^ (1 / 2 : ℝ) + √(((C₂ + 1) / (b - a) + 1) / (d - c)) :=
          add_le_add (hholder n p (z₀, θ₀) hp hq) hA
      _ ≤ C₁ * ((b - a) + (d - c)) ^ (1 / 2 : ℝ)
            + √(((C₂ + 1) / (b - a) + 1) / (d - c)) :=
          add_le_add (mul_le_mul_of_nonneg_left hrpow hC₁) le_rfl
      _ ≤ √(((C₂ + 1) / (b - a) + 1) / (d - c))
            + C₁ * ((b - a) + (d - c)) ^ (1 / 2 : ℝ) + 1 := by linarith

end Work.FTS.StrongEps.LocUnif
