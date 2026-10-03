import Mathlib

namespace Work.FIArea3

/-- The divisor hyperbola: `√n ≤ D` implies `τ(n) ≤ 2·#{d ≤ D : d ∣ n}` (pairing `d ↔ n/d`).
(A private copy of this already exists inside `Submission/Work/FIArea3/tau_gnorm_gBox_bound.lean`;
this is the public version, for reuse by `polbox_tau_absDelta_sum_le` and by the round-6 agents.) -/
theorem tau_le_two_mul_card_dvd (n D : ℕ) (hD : Real.sqrt (n : ℝ) ≤ (D : ℝ)) :
    ((n.divisors.card : ℕ) : ℝ) ≤ 2 * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ) := by
  classical
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    set S : Finset ℕ := (Finset.Icc 1 D).filter (fun d => d ∣ n) with hS
    have hsub : n.divisors ⊆ S ∪ S.image (fun d => n / d) := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      obtain ⟨hdvd, -⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
      have hdn : d ≤ n := Nat.le_of_dvd hnpos hdvd
      by_cases hle : d ≤ D
      · exact Finset.mem_union_left _
          (by rw [hS, Finset.mem_filter]
              exact ⟨Finset.mem_Icc.mpr ⟨hdpos, hle⟩, hdvd⟩)
      · have hDlt : D < d := by omega
        have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
        have hDR : Real.sqrt (n : ℝ) < (d : ℝ) := lt_of_le_of_lt hD (by exact_mod_cast hDlt)
        have h2 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := Nat.cast_div_le
        have h3 : (n : ℝ) / (d : ℝ) < (n : ℝ) / Real.sqrt (n : ℝ) :=
          div_lt_div_of_pos_left (by exact_mod_cast hnpos) hsqrtpos hDR
        have h4 : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
          rw [div_eq_iff (ne_of_gt hsqrtpos)]
          nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]
        have h6 : ((n / d : ℕ) : ℝ) < Real.sqrt (n : ℝ) := lt_of_le_of_lt h2 (h4 ▸ h3)
        have h5 : ((n / d : ℕ) : ℝ) < (D : ℝ) := lt_of_lt_of_le h6 hD
        have hlt' : n / d < D := by exact_mod_cast h5
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n / d, by
          rw [hS, Finset.mem_filter]
          exact ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos hdn hdpos, hlt'.le⟩,
            Nat.div_dvd_of_dvd hdvd⟩, Nat.div_div_self hdvd hn⟩)
    have hcard : n.divisors.card ≤ 2 * S.card := by
      calc n.divisors.card ≤ (S ∪ S.image (fun d => n / d)).card := Finset.card_le_card hsub
        _ ≤ S.card + (S.image (fun d => n / d)).card := Finset.card_union_le _ _
        _ ≤ S.card + S.card := by
            have : (S.image (fun d => n / d)).card ≤ S.card := Finset.card_image_le
            omega
        _ = 2 * S.card := by ring
    have : ((n.divisors.card : ℕ) : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hcard
    rw [hS] at this
    exact this

end Work.FIArea3
