import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.Defs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe.ddiSharp.one

private lemma normSq_mean_le_gen {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ) (x : ℤ) :
    ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z x‖ ^ 2
      ≤ ((Fintype.card Z : ℝ))⁻¹ * ∑ z, ‖G z x‖ ^ 2 := by
  classical
  by_cases hZ : Fintype.card Z = 0
  · haveI : IsEmpty Z := Fintype.card_eq_zero_iff.mp hZ
    simp [hZ]
  · have hcard : (0 : ℝ) < (Fintype.card Z : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hZ
    have h1 : ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z x‖ ^ 2
        = ((Fintype.card Z : ℝ))⁻¹ ^ 2 * ‖∑ z, G z x‖ ^ 2 := by
      rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    rw [h1]
    have h2 : ‖∑ z, G z x‖ ^ 2 ≤ (Fintype.card Z : ℝ) * ∑ z, ‖G z x‖ ^ 2 := by
      have h3 : ‖∑ z, G z x‖ ≤ ∑ z, ‖G z x‖ := norm_sum_le _ _
      have h4 : (0 : ℝ) ≤ ‖∑ z, G z x‖ := norm_nonneg _
      calc ‖∑ z, G z x‖ ^ 2 ≤ (∑ z, ‖G z x‖) ^ 2 := pow_le_pow_left₀ h4 h3 2
        _ ≤ (Finset.univ.card : ℝ) * ∑ z, ‖G z x‖ ^ 2 := by
            have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset Z))
              (f := fun _ : Z => (1 : ℝ)) (g := fun z => ‖G z x‖)
            simpa using hcs
        _ = (Fintype.card Z : ℝ) * ∑ z, ‖G z x‖ ^ 2 := by simp
    calc ((Fintype.card Z : ℝ))⁻¹ ^ 2 * ‖∑ z, G z x‖ ^ 2
        ≤ ((Fintype.card Z : ℝ))⁻¹ ^ 2 * ((Fintype.card Z : ℝ) * ∑ z, ‖G z x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((Fintype.card Z : ℝ))⁻¹ * ∑ z, ‖G z x‖ ^ 2 := by field_simp

private theorem tsum_normSq_Gbar_le' {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ) (L : ℕ) (a : ℤ)
    (hG : ∀ z x, ‖G z x‖ ≤ 1)
    (hsupp : ∀ z, ∃ c0 : ℤ, ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → G z (x + c0) = 0) :
    (∑' x : ℤ, ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)‖ ^ 2) ≤ 2 * (L : ℝ) + 1 := by
  classical
  let c0 : Z → ℤ := fun z => Classical.choose (hsupp z)
  have hc0 : ∀ z, ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → G z (x + c0 z) = 0 :=
    fun z => Classical.choose_spec (hsupp z)
  let W : Finset ℤ := Finset.univ.biUnion (fun z => (Work.Peluse.symIcc L).image (fun t => t + c0 z))
  have hoff : ∀ x : ℤ, x ∉ W → ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z x = 0 := by
    intro x hx
    rw [Finset.sum_eq_zero (fun z _ => ?_), mul_zero]
    have hmem : x - c0 z ∉ Work.Peluse.symIcc L := fun h =>
      hx (Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ z, Finset.mem_image.mpr ⟨x - c0 z, h, by ring⟩⟩)
    have h0 := hc0 z (x - c0 z) hmem
    rwa [show x - c0 z + c0 z = x from by ring] at h0
  have hcard_symIcc : ((Work.Peluse.symIcc L).card : ℝ) = 2 * (L : ℝ) + 1 := by
    rw [Work.Peluse.symIcc, Int.card_Icc]
    have h2 : ((L : ℤ) + 1 - (-(L : ℤ))).toNat = 2 * L + 1 := by omega
    rw [h2]
    push_cast
    ring
  -- rewrite the LHS as a finite sum over the window
  have hLHS : (∑' x : ℤ, ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)‖ ^ 2)
      = ∑ x ∈ W.image (fun t => t - a), ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)‖ ^ 2 := by
    refine tsum_eq_sum (fun x hx => ?_)
    have hxa : x + a ∉ W := fun h => hx (Finset.mem_image.mpr ⟨x + a, h, by ring⟩)
    rw [hoff (x + a) hxa]
    simp
  rw [hLHS]
  -- per-row bound
  have hrow : ∀ z : Z, (∑ x ∈ W.image (fun t => t - a), ‖G z (x + a)‖ ^ 2) ≤ 2 * (L : ℝ) + 1 := by
    intro z
    have hsub : (Work.Peluse.symIcc L).image (fun t => t + c0 z - a) ⊆ W.image (fun t => t - a) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨t + c0 z, Finset.mem_biUnion.mpr
        ⟨z, Finset.mem_univ z, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩, by ring⟩
    have hzero : ∀ x ∈ W.image (fun t => t - a), x ∉ (Work.Peluse.symIcc L).image (fun t => t + c0 z - a)
        → ‖G z (x + a)‖ ^ 2 = 0 := by
      intro x _ hxs
      have hmem : x + a - c0 z ∉ Work.Peluse.symIcc L := fun h =>
        hxs (Finset.mem_image.mpr ⟨x + a - c0 z, h, by ring⟩)
      have h0 := hc0 z (x + a - c0 z) hmem
      rw [show x + a - c0 z + c0 z = x + a from by ring] at h0
      rw [h0]; simp
    rw [← Finset.sum_subset hsub hzero]
    calc ∑ x ∈ (Work.Peluse.symIcc L).image (fun t => t + c0 z - a), ‖G z (x + a)‖ ^ 2
        ≤ ∑ _x ∈ (Work.Peluse.symIcc L).image (fun t => t + c0 z - a), (1 : ℝ) :=
          Finset.sum_le_sum (fun x _ => by
            have h := hG z (x + a)
            nlinarith [norm_nonneg (G z (x + a))])
      _ = ((Work.Peluse.symIcc L).image (fun t => t + c0 z - a)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (Work.Peluse.symIcc L).card := by exact_mod_cast Finset.card_image_le
      _ = 2 * (L : ℝ) + 1 := hcard_symIcc
  calc ∑ x ∈ W.image (fun t => t - a), ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)‖ ^ 2
      ≤ ∑ x ∈ W.image (fun t => t - a), ((Fintype.card Z : ℝ))⁻¹ * ∑ z, ‖G z (x + a)‖ ^ 2 :=
        Finset.sum_le_sum (fun x _ => normSq_mean_le_gen G (x + a))
    _ = ((Fintype.card Z : ℝ))⁻¹ * ∑ z, (∑ x ∈ W.image (fun t => t - a), ‖G z (x + a)‖ ^ 2) := by
        have h1 : ∀ x : ℤ, ((Fintype.card Z : ℝ))⁻¹ * ∑ z, ‖G z (x + a)‖ ^ 2
            = ∑ z ∈ (Finset.univ : Finset Z), ((Fintype.card Z : ℝ))⁻¹ * ‖G z (x + a)‖ ^ 2 := by
          intro x; rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ((Fintype.card Z : ℝ))⁻¹ * ∑ z : Z, (2 * (L : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => hrow z)) (by positivity)
    _ ≤ 2 * (L : ℝ) + 1 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [show ((Finset.univ : Finset Z).card : ℝ) = (Fintype.card Z : ℝ) from rfl]
        by_cases hM : Fintype.card Z = 0
        · rw [hM]
          simp only [Nat.cast_zero, inv_zero, zero_mul]
          positivity
        · rw [← mul_assoc, inv_mul_cancel₀ (by
            have : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast hM
            exact this), one_mul]

theorem tsum_avgNormSq_le {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ) (L : ℕ) (a : ℤ)
    (hG : ∀ z x, ‖G z x‖ ≤ 1)
    (hsupp : ∀ z, ∃ c₀ : ℤ, ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → G z (x + c₀) = 0) :
    (∑' x : ℤ, ‖avgFn G (x + a)‖ ^ 2) ≤ 2 * (L : ℝ) + 1 :=
  tsum_normSq_Gbar_le' G L a hG hsupp

end Work.Peluse.Ulower.StepLe.ddiSharp.one
