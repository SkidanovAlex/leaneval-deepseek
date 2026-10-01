import Mathlib

namespace Work.ZeroDensity.LogFree

open MeasureTheory Set

/-- The intervals `Ioc (X * exp(-((j+1)η))) (X * exp(-(jη)))` for `j : ℤ` tile `(0, ∞)`.
Consequently, for `f` integrable on `(0, ∞)`, the integrals over these intervals sum
(HasSum) to the integral over `(0, ∞)`. -/
theorem HB7TilingIoi {X η : ℝ} (hX : 0 < X) (hη : 0 < η) {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi 0)) :
    HasSum (fun j : ℤ => ∫ y in Set.Ioc (X * Real.exp (-(((j : ℝ) + 1) * η)))
                    (X * Real.exp (-((j : ℝ) * η))), f y)
      (∫ y in Set.Ioi 0, f y) := by
  set a : ℤ → ℝ := fun j => X * Real.exp (-((j:ℝ) * η)) with ha
  have ha_eq : ∀ j : ℤ, a j = X * Real.exp (-((j:ℝ) * η)) := by intro j; rw [ha]
  have hlit : ∀ j : ℤ, X * Real.exp (-(((j:ℝ)+1)*η)) = a (j+1) := by
    intro j; rw [ha_eq (j+1)]; push_cast; ring_nf
  have hmono : ∀ i j : ℤ, i ≤ j → a j ≤ a i := by
    intro i j hij
    rw [ha_eq i, ha_eq j]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hX)
    rw [Real.exp_le_exp]
    have hij' : (i:ℝ) * η ≤ (j:ℝ) * η :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (le_of_lt hη)
    linarith
  have hmeas : ∀ j : ℤ,
      MeasurableSet (Set.Ioc (X * Real.exp (-(((j:ℝ)+1)*η))) (X * Real.exp (-((j:ℝ)*η)))) :=
    fun j => measurableSet_Ioc
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun j : ℤ => Set.Ioc (X * Real.exp (-(((j:ℝ)+1)*η))) (X * Real.exp (-((j:ℝ)*η))))) := by
    intro i j hij
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hxj
    rw [Set.mem_Ioc] at hx hxj
    rw [← ha_eq i] at hx
    rw [← ha_eq j] at hxj
    rw [hlit i] at hx
    rw [hlit j] at hxj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hle : a j ≤ a (i+1) := hmono (i+1) j (by omega)
      linarith [hx.1, hx.2, hxj.2, hle]
    · have hle : a i ≤ a (j+1) := hmono (j+1) i (by omega)
      linarith [hxj.1, hxj.2, hx.2, hle]
  have hunion : (⋃ j : ℤ, Set.Ioc (X * Real.exp (-(((j:ℝ)+1)*η))) (X * Real.exp (-((j:ℝ)*η)))) = Set.Ioi 0 := by
    ext y
    rw [Set.mem_iUnion, Set.mem_Ioi]
    constructor
    · rintro ⟨j, hj⟩
      rw [Set.mem_Ioc] at hj
      have hpos : 0 < X * Real.exp (-(((j:ℝ)+1)*η)) := mul_pos hX (Real.exp_pos _)
      linarith [hj.1]
    · intro hy
      refine ⟨⌊(Real.log X - Real.log y)/η⌋, ?_⟩
      rw [Set.mem_Ioc]
      constructor
      · have hA : 0 < X * Real.exp (-(((⌊(Real.log X - Real.log y)/η⌋:ℝ)+1)*η)) :=
          mul_pos hX (Real.exp_pos _)
        rw [← Real.log_lt_log_iff hA hy]
        rw [Real.log_mul (ne_of_gt hX) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
        have h1 : (Real.log X - Real.log y)/η < ((⌊(Real.log X - Real.log y)/η⌋:ℝ) + 1) :=
          Int.lt_floor_add_one _
        rw [div_lt_iff₀ hη] at h1
        linarith
      · have hB : 0 < X * Real.exp (-((⌊(Real.log X - Real.log y)/η⌋:ℝ)*η)) :=
          mul_pos hX (Real.exp_pos _)
        rw [← Real.log_le_log_iff hy hB]
        rw [Real.log_mul (ne_of_gt hX) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
        have h2 : ((⌊(Real.log X - Real.log y)/η⌋:ℝ)) * η ≤ Real.log X - Real.log y := by
          have h := mul_le_mul_of_nonneg_right (Int.floor_le ((Real.log X - Real.log y)/η)) (le_of_lt hη)
          rwa [div_mul_cancel₀ _ (ne_of_gt hη)] at h
        linarith
  have h := hasSum_integral_iUnion (μ := volume) hmeas hdisj (by rwa [hunion])
  simpa [hunion] using h

end Work.ZeroDensity.LogFree
