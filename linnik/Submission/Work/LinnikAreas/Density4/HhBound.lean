import Mathlib
import Submission.Work.LinnikAreas.Density4.MuSqTotientDefs
import Submission.Work.LinnikAreas.Density4.AssemblyAux

open Finset BigOperators

namespace Work.LinnikAreas.Density4

noncomputable section

/-- The inner fibre sum arising from the reindexed harmonic identity. -/
def QQ (z u : ℕ) : ℝ :=
  ∑ v ∈ u.divisors.filter (fun v => u * v ≤ z),
    ((ArithmeticFunction.moebius v : ℤ) : ℝ) * (harmonic (z / (u * v)) : ℝ)

lemma QQ_one (z : ℕ) (hz : 1 ≤ z) : QQ z 1 = (harmonic z : ℝ) := by
  rw [QQ, Nat.divisors_one]
  have hp : (1 * 1 ≤ z) = True := by simp [hz]
  rw [show (Finset.filter (fun v => 1 * v ≤ z) ({1} : Finset ℕ)) = {1} from by
    apply Finset.filter_true_of_mem
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv; simpa using hz]
  simp

lemma QQ_small (z u : ℕ) (hu : Squarefree u) (hu2 : 2 ≤ u) (huz : u * u ≤ z) :
    |QQ z u| ≤ (2:ℝ)^(u.primeFactors.card) * (1 + Real.log u) := by
  have hu0 : u ≠ 0 := by omega
  have hu1 : 1 ≤ u := by omega
  have huz1 : u ≤ z := le_trans (le_mul_of_one_le_right (by omega) (by omega)) huz
  have hX0 : (0:ℝ) ≤ (2:ℝ)^(u.primeFactors.card) := by positivity
  have hfil : u.divisors.filter (fun v => u * v ≤ z) = u.divisors := by
    apply Finset.filter_true_of_mem
    intro v hv
    have hvu : v ≤ u := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hv).1
    calc u * v ≤ u * u := Nat.mul_le_mul_left u hvu
      _ ≤ z := huz
  rw [QQ, hfil]
  -- bound |Σ_v A_v * H_v|
  set X : ℝ := Real.log ((z:ℝ)/(u:ℝ)) with hX
  have hδ : ∀ v ∈ u.divisors,
      (0:ℝ) ≤ (harmonic (z/(u*v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ))
      ∧ (harmonic (z/(u*v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)) ≤ 1 := by
    intro v hv
    have hvd : v ∣ u := (Nat.mem_divisors.mp hv).1
    have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos hvd (by omega)))
    have huv1 : 1 ≤ u * v := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hvu : v ≤ u := Nat.le_of_dvd (by omega) hvd
    have huvz : u * v ≤ z := by
      calc u * v ≤ u * u := Nat.mul_le_mul_left u hvu
        _ ≤ z := huz
    have hb := harmonic_log_bounds z (u*v) huv1 huvz
    refine ⟨?_, ?_⟩ <;> linarith [hb.1, hb.2]
  -- split
  have hsplit : (∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * (harmonic (z / (u * v)) : ℝ))
      = (∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * ((harmonic (z / (u * v)) : ℝ)
            - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ))))
        + (∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * Real.log ((z:ℝ)/((u*v : ℕ) : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro v hv; ring
  rw [hsplit]
  -- piece 1
  have hpiece1 : |∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ)
      * ((harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)))| ≤ (2:ℝ)^(u.primeFactors.card) := by
    have h1 : |∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ)
        * ((harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)))|
        ≤ ∑ v ∈ u.divisors, |((ArithmeticFunction.moebius v : ℤ) : ℝ)
        * ((harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ v ∈ u.divisors, |((ArithmeticFunction.moebius v : ℤ) : ℝ)
        * ((harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)))| ≤ 1 := by
      intro v hv
      have hμ : |((ArithmeticFunction.moebius v : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        have : |ArithmeticFunction.moebius v| ≤ 1 := by
          rcases ArithmeticFunction.moebius_eq_or v with h | h | h <;> rw [h] <;> norm_num
        exact_mod_cast this
      have hδv := hδ v hv
      rw [abs_mul]
      calc |((ArithmeticFunction.moebius v : ℤ) : ℝ)| * |(harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ))|
          ≤ 1 * 1 := by
            apply mul_le_mul hμ (abs_le.mpr ⟨by linarith [hδv.1], by linarith [hδv.2]⟩) (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc |∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ)
          * ((harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)))|
        ≤ ∑ v ∈ u.divisors, |((ArithmeticFunction.moebius v : ℤ) : ℝ)
          * ((harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)))| := h1
      _ ≤ ∑ v ∈ u.divisors, (1:ℝ) := Finset.sum_le_sum h2
      _ = (u.divisors.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ((2:ℝ)^(u.primeFactors.card)) := by rw [card_divisors_sqfree u hu]; push_cast; ring
  -- piece 2
  have hpiece2 : |∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * Real.log ((z:ℝ)/((u*v : ℕ) : ℝ))|
      ≤ (2:ℝ)^(u.primeFactors.card) * Real.log u := by
    have hterm : ∀ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * Real.log ((z:ℝ)/((u*v : ℕ) : ℝ))
        = ((ArithmeticFunction.moebius v : ℤ) : ℝ) * (Real.log ((z:ℝ)/(u:ℝ)) - Real.log (v:ℝ)) := by
      intro v hv
      have hvd : v ∣ u := (Nat.mem_divisors.mp hv).1
      have hv0 : 0 < v := Nat.pos_of_dvd_of_pos hvd (by omega)
      have hv0r : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv0
      have hz0r : (0:ℝ) < (z:ℝ) := by exact_mod_cast (show 0 < z by omega)
      have hu0r : (0:ℝ) < (u:ℝ) := by exact_mod_cast (show 0 < u by omega)
      have hcast : ((z:ℝ)/((u*v : ℕ) : ℝ)) = ((z:ℝ)/(u:ℝ))/(v:ℝ) := by
        rw [Nat.cast_mul]; field_simp
      rw [hcast, Real.log_div (by positivity) (by positivity)]
    rw [Finset.sum_congr rfl hterm]
    have hzero : (∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ)) = 0 := by
      rw [sum_moebius_divisors, if_neg (by omega : u ≠ 1)]
    have hval : (∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ)
        * (Real.log ((z:ℝ)/(u:ℝ)) - Real.log (v:ℝ)))
        = - ∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * Real.log (v:ℝ) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, zero_sub]
    rw [hval, abs_neg]
    calc |∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * Real.log (v:ℝ)|
        ≤ ∑ v ∈ u.divisors, |((ArithmeticFunction.moebius v : ℤ) : ℝ) * Real.log (v:ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ u.divisors, Real.log (v:ℝ) := by
          apply Finset.sum_le_sum
          intro v hv
          have hvd : v ∣ u := (Nat.mem_divisors.mp hv).1
          have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.mpr
            (Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos hvd (by omega)))
          have hlognn : 0 ≤ Real.log (v:ℝ) := Real.log_nonneg (by exact_mod_cast hv1)
          have hμ : |((ArithmeticFunction.moebius v : ℤ) : ℝ)| ≤ 1 := by
            rw [← Int.cast_abs]
            have : |ArithmeticFunction.moebius v| ≤ 1 := by
              rcases ArithmeticFunction.moebius_eq_or v with h | h | h <;> rw [h] <;> norm_num
            exact_mod_cast this
          rw [abs_mul]
          calc |((ArithmeticFunction.moebius v : ℤ) : ℝ)| * |Real.log (v:ℝ)|
              ≤ 1 * Real.log (v:ℝ) := by
                rw [abs_of_nonneg hlognn]
                exact mul_le_mul_of_nonneg_right hμ hlognn
            _ = Real.log (v:ℝ) := one_mul _
      _ ≤ (2:ℝ)^(u.primeFactors.card) * Real.log u := sum_log_divisors_le u hu
  calc |(∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ)
        * ((harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ))))
      + (∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)))|
      ≤ |(∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ)
        * ((harmonic (z / (u * v)) : ℝ) - Real.log ((z:ℝ)/((u*v : ℕ) : ℝ))))|
        + |(∑ v ∈ u.divisors, ((ArithmeticFunction.moebius v : ℤ) : ℝ) * Real.log ((z:ℝ)/((u*v : ℕ) : ℝ)))| :=
          abs_add_le _ _
    _ ≤ (2:ℝ)^(u.primeFactors.card) + (2:ℝ)^(u.primeFactors.card) * Real.log u := add_le_add hpiece1 hpiece2
    _ = (2:ℝ)^(u.primeFactors.card) * (1 + Real.log u) := by ring

end

end Work.LinnikAreas.Density4

namespace Work.LinnikAreas.Density4

noncomputable section

lemma harmonic_nonneg_real (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  have := harmonic_eq_sum_Icc (n := n)
  rw [this]
  push_cast
  apply Finset.sum_nonneg
  intro k hk
  rw [Finset.mem_Icc] at hk
  positivity

lemma QQ_large (z u : ℕ) (hz : 1 ≤ z) (hu : Squarefree u) (hu2 : 2 ≤ u) (huz : z < u * u) :
    |QQ z u| ≤ (2:ℝ)^(u.primeFactors.card) * (1 + Real.log z / 2) := by
  have hu0 : 0 < u := by omega
  have hz0 : 0 < z := by omega
  rw [QQ]
  have hlog_half : Real.log z / 2 ≤ Real.log u := by
    have hzle : (z:ℝ) ≤ (u:ℝ)^2 := by
      calc (z:ℝ) ≤ ((u*u : ℕ) : ℝ) := by exact_mod_cast (le_of_lt huz)
        _ = (u:ℝ)^2 := by push_cast; ring
    have h2 : Real.log (z:ℝ) ≤ 2 * Real.log (u:ℝ) := by
      calc Real.log (z:ℝ) ≤ Real.log ((u:ℝ)^2) := Real.log_le_log (by exact_mod_cast hz0) hzle
        _ = 2 * Real.log (u:ℝ) := by rw [Real.log_pow]; push_cast; ring
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
  have hterm : ∀ v ∈ u.divisors.filter (fun v => u * v ≤ z),
      |((ArithmeticFunction.moebius v : ℤ) : ℝ) * (harmonic (z / (u * v)) : ℝ)| ≤ 1 + Real.log z / 2 := by
    intro v hv
    have huvz : u * v ≤ z := (Finset.mem_filter.mp hv).2
    have hvdiv : v ∈ u.divisors := (Finset.mem_filter.mp hv).1
    have hvd : v ∣ u := (Nat.mem_divisors.mp hvdiv).1
    have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos hvd hu0))
    have huv1 : 1 ≤ u * v := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hb := harmonic_log_bounds z (u*v) huv1 huvz
    have hDnn : (0:ℝ) ≤ (harmonic (z / (u * v)) : ℝ) := by
      have hlog0 : 0 ≤ Real.log ((z:ℝ)/((u*v:ℕ):ℝ)) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ (by positivity), one_mul]
        exact_mod_cast huvz
      linarith [hb.1]
    have hμ : |((ArithmeticFunction.moebius v : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      have : |ArithmeticFunction.moebius v| ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or v with h | h | h <;> rw [h] <;> norm_num
      exact_mod_cast this
    have hloguv_le : Real.log ((z:ℝ)/((u*v:ℕ):ℝ)) ≤ Real.log ((z:ℝ)/(u:ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hv1r : (1:ℝ) ≤ (v:ℝ) := by exact_mod_cast hv1
      have hz0r : (0:ℝ) ≤ (z:ℝ) := by positivity
      have hu0r : (0:ℝ) ≤ (u:ℝ) := by positivity
      push_cast
      have hle : (u:ℝ) ≤ (u:ℝ) * (v:ℝ) := by nlinarith [hv1r, hu0r]
      exact mul_le_mul_of_nonneg_left hle hz0r
    have hlogu_le : Real.log ((z:ℝ)/(u:ℝ)) ≤ Real.log z / 2 := by
      rw [Real.log_div (by positivity) (by positivity)]
      linarith
    rw [abs_mul, abs_of_nonneg hDnn]
    calc |((ArithmeticFunction.moebius v : ℤ) : ℝ)| * (harmonic (z / (u * v)) : ℝ)
        ≤ 1 * (harmonic (z / (u * v)) : ℝ) := mul_le_mul_of_nonneg_right hμ hDnn
      _ = (harmonic (z / (u * v)) : ℝ) := one_mul _
      _ ≤ Real.log ((z:ℝ)/((u*v:ℕ):ℝ)) + 1 := hb.2
      _ ≤ Real.log ((z:ℝ)/(u:ℝ)) + 1 := by linarith
      _ ≤ Real.log z / 2 + 1 := by linarith
      _ = 1 + Real.log z / 2 := by ring
  calc |∑ v ∈ u.divisors.filter (fun v => u * v ≤ z),
        ((ArithmeticFunction.moebius v : ℤ) : ℝ) * (harmonic (z / (u * v)) : ℝ)|
      ≤ ∑ v ∈ u.divisors.filter (fun v => u * v ≤ z),
        |((ArithmeticFunction.moebius v : ℤ) : ℝ) * (harmonic (z / (u * v)) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ u.divisors.filter (fun v => u * v ≤ z), (1 + Real.log z / 2) :=
        Finset.sum_le_sum hterm
    _ = ((u.divisors.filter (fun v => u * v ≤ z)).card : ℝ) * (1 + Real.log z / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2:ℝ)^(u.primeFactors.card)) * (1 + Real.log z / 2) := by
        have hc : ((u.divisors.filter (fun v => u * v ≤ z)).card : ℝ) ≤ (2:ℝ)^(u.primeFactors.card) := by
          have := Finset.card_le_card (Finset.filter_subset (fun v => u * v ≤ z) u.divisors)
          rw [card_divisors_sqfree u hu] at this
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right hc (by positivity)

end

end Work.LinnikAreas.Density4

namespace Work.LinnikAreas.Density4

noncomputable section

/-- The reindexed harmonic sum is bounded by `log z + (1 + 2C)`, where `C` bounds the
log-weighted squarefree sum `Σ cw u · 2^ω(u) · (1 + log u)`. -/
theorem hh_reindex_sum_le (C : ℝ) (hC : 0 < C)
    (hBdd : ∀ M : ℕ, (∑ u ∈ (Finset.Icc 1 M).filter Squarefree,
        cw u * (2:ℝ)^(u.primeFactors.card) * (1 + Real.log u)) ≤ C) :
    ∀ z : ℕ, 1 ≤ z →
      (∑ u ∈ (Finset.Icc 1 z).filter Squarefree, cw u * QQ z u) ≤ Real.log z + (1 + 2*C) := by
  intro z hz
  have hlogz : (0:ℝ) < 1 + Real.log z / 2 := by
    have h : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz)
    linarith
  have hBz : (∑ u ∈ (Finset.Icc 1 z).filter Squarefree,
      cw u * (2:ℝ)^(u.primeFactors.card) * (1 + Real.log u)) ≤ C := hBdd z
  have hstep1 : (∑ u ∈ (Finset.Icc 1 z).filter Squarefree, cw u * QQ z u)
      ≤ ∑ u ∈ (Finset.Icc 1 z).filter Squarefree, cw u * |QQ z u| := by
    apply Finset.sum_le_sum
    intro u hu
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (cw_nonneg u)
  have hsplit : (∑ u ∈ (Finset.Icc 1 z).filter Squarefree, cw u * |QQ z u|)
      = (∑ u ∈ (((Finset.Icc 1 z).filter Squarefree).filter (fun u => u = 1)), cw u * |QQ z u|)
        + ((∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
              (fun u => u * u ≤ z)), cw u * |QQ z u|)
          + (∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
              (fun u => ¬ (u * u ≤ z))), cw u * |QQ z u|)) := by
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 z).filter Squarefree) (fun u => u = 1)]
    rw [← Finset.sum_filter_add_sum_filter_not (((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)) (fun u => u * u ≤ z)]
  have h1 : (∑ u ∈ (((Finset.Icc 1 z).filter Squarefree).filter (fun u => u = 1)), cw u * |QQ z u|)
      ≤ 1 + Real.log z := by
    have hset : ((Finset.Icc 1 z).filter Squarefree).filter (fun u => u = 1) = {1} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨_, _⟩, _⟩, h1⟩; exact h1
      · rintro rfl; exact ⟨⟨⟨le_refl 1, hz⟩, squarefree_one⟩, rfl⟩
    rw [hset, Finset.sum_singleton, cw_one, one_mul, QQ_one z hz,
      abs_of_nonneg (harmonic_nonneg_real z)]
    exact harmonic_le_one_add_log z
  have hsub2 : ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter (fun u => u * u ≤ z))
      ⊆ (Finset.Icc 1 z).filter Squarefree := by
    intro u hu
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
  have h2 : (∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
        (fun u => u * u ≤ z)), cw u * |QQ z u|) ≤ C := by
    calc (∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
            (fun u => u * u ≤ z)), cw u * |QQ z u|)
        ≤ ∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
            (fun u => u * u ≤ z)), cw u * ((2:ℝ)^(u.primeFactors.card) * (1 + Real.log u)) := by
          apply Finset.sum_le_sum
          intro u hu
          have huU : u ∈ (Finset.Icc 1 z).filter Squarefree := hsub2 hu
          have hsq : Squarefree u := (Finset.mem_filter.mp huU).2
          have hu1 : 1 ≤ u := (Finset.mem_Icc.mp (Finset.mem_filter.mp huU).1).1
          have hu_ne1 : u ≠ 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
          have hu2 : 2 ≤ u := by omega
          have huz : u * u ≤ z := (Finset.mem_filter.mp hu).2
          exact mul_le_mul_of_nonneg_left (QQ_small z u hsq hu2 huz) (cw_nonneg u)
      _ ≤ ∑ u ∈ (Finset.Icc 1 z).filter Squarefree,
            cw u * ((2:ℝ)^(u.primeFactors.card) * (1 + Real.log u)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub2
          intro u hu _
          apply mul_nonneg (cw_nonneg u)
          apply mul_nonneg (by positivity)
          have hu1 : 1 ≤ u := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).1
          have hu1r : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu1
          linarith [Real.log_nonneg hu1r]
      _ = ∑ u ∈ (Finset.Icc 1 z).filter Squarefree,
            cw u * (2:ℝ)^(u.primeFactors.card) * (1 + Real.log u) := by
          apply Finset.sum_congr rfl; intro u hu; ring
      _ ≤ C := hBz
  have hsub3 : ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter (fun u => ¬ (u * u ≤ z)))
      ⊆ (Finset.Icc 1 z).filter Squarefree := by
    intro u hu
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
  have h3 : (∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
        (fun u => ¬ (u * u ≤ z))), cw u * |QQ z u|) ≤ C := by
    have hlt : ∀ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
        (fun u => ¬ (u * u ≤ z))), z < u * u := fun u hu => lt_of_not_ge (Finset.mem_filter.mp hu).2
    have hlogu : ∀ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
        (fun u => ¬ (u * u ≤ z))), Real.log z / 2 ≤ Real.log u := by
      intro u hu
      have huU : u ∈ (Finset.Icc 1 z).filter Squarefree := hsub3 hu
      have hzu : z < u * u := hlt u hu
      have hzle : (z:ℝ) ≤ (u:ℝ)^2 := by
        calc (z:ℝ) ≤ ((u*u : ℕ) : ℝ) := by exact_mod_cast (le_of_lt hzu)
          _ = (u:ℝ)^2 := by push_cast; ring
      have h2l : Real.log (z:ℝ) ≤ 2 * Real.log (u:ℝ) := by
        calc Real.log (z:ℝ) ≤ Real.log ((u:ℝ)^2) :=
              Real.log_le_log (by exact_mod_cast (show 0 < z by omega)) hzle
          _ = 2 * Real.log (u:ℝ) := by rw [Real.log_pow]; push_cast; ring
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    calc (∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
            (fun u => ¬ (u * u ≤ z))), cw u * |QQ z u|)
        ≤ ∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
            (fun u => ¬ (u * u ≤ z))), cw u * ((2:ℝ)^(u.primeFactors.card) * (1 + Real.log z / 2)) := by
          apply Finset.sum_le_sum
          intro u hu
          have huU : u ∈ (Finset.Icc 1 z).filter Squarefree := hsub3 hu
          have hsq : Squarefree u := (Finset.mem_filter.mp huU).2
          have hu1 : 1 ≤ u := (Finset.mem_Icc.mp (Finset.mem_filter.mp huU).1).1
          have hu_ne1 : u ≠ 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
          have hu2 : 2 ≤ u := by omega
          exact mul_le_mul_of_nonneg_left (QQ_large z u hz hsq hu2 (hlt u hu)) (cw_nonneg u)
      _ = (1 + Real.log z / 2) * ∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
            (fun u => ¬ (u * u ≤ z))), cw u * (2:ℝ)^(u.primeFactors.card) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u hu; ring
      _ ≤ (1 + Real.log z / 2) * (C / (1 + Real.log z / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hlogz)
          rw [le_div_iff₀ hlogz]
          calc (∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
                  (fun u => ¬ (u * u ≤ z))), cw u * (2:ℝ)^(u.primeFactors.card)) * (1 + Real.log z / 2)
              = ∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
                  (fun u => ¬ (u * u ≤ z))), cw u * (2:ℝ)^(u.primeFactors.card) * (1 + Real.log z / 2) := by
                rw [Finset.sum_mul]
            _ ≤ ∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
                  (fun u => ¬ (u * u ≤ z))), cw u * (2:ℝ)^(u.primeFactors.card) * (1 + Real.log u) := by
                apply Finset.sum_le_sum; intro u hu
                apply mul_le_mul_of_nonneg_left (by linarith [hlogu u hu])
                apply mul_nonneg (cw_nonneg u); positivity
            _ ≤ ∑ u ∈ (Finset.Icc 1 z).filter Squarefree,
                  cw u * (2:ℝ)^(u.primeFactors.card) * (1 + Real.log u) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsub3
                intro u hu _
                apply mul_nonneg (mul_nonneg (cw_nonneg u) (by positivity))
                have hu1 : 1 ≤ u := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).1
                have hu1r : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu1
                linarith [Real.log_nonneg hu1r]
            _ ≤ C := hBz
      _ = C := by rw [mul_div_cancel₀ C (ne_of_gt hlogz)]
  calc (∑ u ∈ (Finset.Icc 1 z).filter Squarefree, cw u * QQ z u)
      ≤ ∑ u ∈ (Finset.Icc 1 z).filter Squarefree, cw u * |QQ z u| := hstep1
    _ = (∑ u ∈ (((Finset.Icc 1 z).filter Squarefree).filter (fun u => u = 1)), cw u * |QQ z u|)
        + ((∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
              (fun u => u * u ≤ z)), cw u * |QQ z u|)
          + (∑ u ∈ ((((Finset.Icc 1 z).filter Squarefree).filter (fun u => u ≠ 1)).filter
              (fun u => ¬ (u * u ≤ z))), cw u * |QQ z u|)) := hsplit
    _ ≤ (1 + Real.log z) + (C + C) := by linarith [h1, h2, h3]
    _ = Real.log z + (1 + 2*C) := by ring

end

end Work.LinnikAreas.Density4
