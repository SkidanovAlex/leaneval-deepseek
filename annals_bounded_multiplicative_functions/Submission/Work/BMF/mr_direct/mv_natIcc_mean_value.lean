import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_decomp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators

/-- If `p ∈ natIcc A B` and `0 < B` then `A ≤ p ≤ B`. -/
lemma natIcc_bounds_gen {A B : ℝ} (hB : 0 < B) {p : ℕ} (hp : p ∈ natIcc A B) :
    A ≤ (p : ℝ) ∧ (p : ℝ) ≤ B := by
  rw [natIcc, Finset.mem_Icc] at hp
  exact ⟨le_trans (Nat.le_ceil A) (by exact_mod_cast hp.1),
    le_trans (by exact_mod_cast hp.2) (Nat.floor_le hB.le)⟩

/-- Distinct naturals in `natIcc A B` (with `0 < A`, `A ≤ B`) are separated by at least `1/B`
in the logarithmic variable. -/
lemma log_sep_natIcc_gen {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {m n : ℕ}
    (hm : m ∈ natIcc A B) (hn : n ∈ natIcc A B) (hmn : m ≠ n) :
    1 / B ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hBpos : 0 < B := lt_of_lt_of_le hA hAB
  have hm' := natIcc_bounds_gen hBpos hm
  have hn' := natIcc_bounds_gen hBpos hn
  have hmp : (0 : ℝ) < (m : ℝ) := by linarith [hm'.1]
  have hnp : (0 : ℝ) < (n : ℝ) := by linarith [hn'.1]
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hlog : Real.log ((m : ℝ) / (n : ℝ)) = Real.log (m : ℝ) - Real.log (n : ℝ) :=
      Real.log_div hmp.ne' hnp.ne'
    have hle : 1 - (m : ℝ) / (n : ℝ) ≤ Real.log (n : ℝ) - Real.log (m : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) / (n : ℝ) by positivity)
      rw [hlog] at h
      linarith
    have hltlog : Real.log (m : ℝ) < Real.log (n : ℝ) := Real.log_lt_log hmp (by exact_mod_cast hlt)
    have habs : |Real.log (m : ℝ) - Real.log (n : ℝ)| = Real.log (n : ℝ) - Real.log (m : ℝ) := by
      rw [abs_of_neg (sub_neg.mpr hltlog)]
      ring
    rw [habs]
    have hnm : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      have h2 : m + 1 ≤ n := by omega
      have h3 : ((m : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h2
      linarith
    have step1 : (1 : ℝ) / (n : ℝ) ≤ 1 - (m : ℝ) / (n : ℝ) := by
      rw [show (1 : ℝ) - (m : ℝ) / (n : ℝ) = ((n : ℝ) - (m : ℝ)) / (n : ℝ) by
            rw [sub_div, div_self hnp.ne']]
      exact div_le_div_of_nonneg_right hnm hnp.le
    have step2 : (1 : ℝ) / B ≤ (1 : ℝ) / (n : ℝ) :=
      one_div_le_one_div_of_le hnp (by linarith [hn'.2])
    linarith
  · have hlog : Real.log ((n : ℝ) / (m : ℝ)) = Real.log (n : ℝ) - Real.log (m : ℝ) :=
      Real.log_div hnp.ne' hmp.ne'
    have hle : 1 - (n : ℝ) / (m : ℝ) ≤ Real.log (m : ℝ) - Real.log (n : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / (m : ℝ) by positivity)
      rw [hlog] at h
      linarith
    have hltlog : Real.log (n : ℝ) < Real.log (m : ℝ) := Real.log_lt_log hnp (by exact_mod_cast hgt)
    have habs : |Real.log (m : ℝ) - Real.log (n : ℝ)| = Real.log (m : ℝ) - Real.log (n : ℝ) := by
      rw [abs_of_pos (sub_pos.mpr hltlog)]
    rw [habs]
    have hnm : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
      have h2 : n + 1 ≤ m := by omega
      have h3 : ((n : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h2
      linarith
    have step1 : (1 : ℝ) / (m : ℝ) ≤ 1 - (n : ℝ) / (m : ℝ) := by
      rw [show (1 : ℝ) - (n : ℝ) / (m : ℝ) = ((m : ℝ) - (n : ℝ)) / (m : ℝ) by
            rw [sub_div, div_self hmp.ne']]
      exact div_le_div_of_nonneg_right hnm hmp.le
    have step2 : (1 : ℝ) / B ≤ (1 : ℝ) / (m : ℝ) :=
      one_div_le_one_div_of_le hmp (by linarith [hm'.2])
    linarith

/-- The mean value assumption forces the constant `C₀` to be nonnegative. -/
lemma c0_nonneg_of_mv (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2) :
    0 ≤ C₀ := by
  have h := hC₀ 1 one_pos 1 (fun _ => 0) (fun _ => 1)
    (fun i j hij => absurd (Subsingleton.elim i j) hij) 0 0 le_rfl
  simpa using h

theorem mv_natIcc_mean_value (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2) :
    ∀ (d : ℕ → ℂ) (A B S : ℝ), 0 < A → A ≤ B → 0 ≤ S →
      (∫ t in (-S)..S,
          ‖∑ n ∈ Work.BMF.natIcc A B, d n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        ≤ (2 * S + 3 * C₀ * B) * ∑ n ∈ Work.BMF.natIcc A B, ‖d n‖ ^ 2 / (n : ℝ) ^ 2 := by
  have hC₀nn : 0 ≤ C₀ := c0_nonneg_of_mv C₀ hC₀
  intro d A B S hA hAB hS
  have hBpos : 0 < B := lt_of_lt_of_le hA hAB
  set N := (Work.BMF.natIcc A B).card with hN
  set e : ↥(Work.BMF.natIcc A B) ≃ Fin N := Finset.equivFin _ with he
  set b : Fin N → ℂ := fun i =>
    d (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) /
      ((((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) : ℂ) with hb
  set μ : Fin N → ℝ := fun i =>
    -(Real.log ((((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) : ℝ)) with hmu
  have hδ : 0 < 1 / B := by positivity
  have hsep : ∀ i j : Fin N, i ≠ j → 1 / B ≤ |μ i - μ j| := by
    intro i j hij
    have hne : (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) ≠
        (((e.symm j : ↥(Work.BMF.natIcc A B)) : ℕ)) := by
      intro h'
      exact hij (e.symm.injective (Subtype.coe_injective h'))
    have hi : (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) ∈ Work.BMF.natIcc A B := (e.symm i).2
    have hj : (((e.symm j : ↥(Work.BMF.natIcc A B)) : ℕ)) ∈ Work.BMF.natIcc A B := (e.symm j).2
    have hkey := log_sep_natIcc_gen hA hAB hi hj hne
    rw [hmu]
    simp only []
    rw [show -(Real.log ((((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ)))
        - -(Real.log ((((e.symm j : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ)))
        = Real.log ((((e.symm j : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ))
          - Real.log ((((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ) : ℝ)) by ring, abs_sub_comm]
    exact hkey
  have hsum_eq : ∀ t : ℝ, (∑ n ∈ Work.BMF.natIcc A B,
        d n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = ∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ))) := by
    intro t
    rw [← Finset.sum_attach (Work.BMF.natIcc A B)
          (fun n => d n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))),
        ← Finset.univ_eq_attach (Work.BMF.natIcc A B)]
    rw [← Equiv.sum_comp e.symm (fun x : ↥(Work.BMF.natIcc A B) =>
          d ((x : ℕ)) * (((x : ℕ)) : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hb, hmu]
    have hn1 : 1 ≤ (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) := by
      have hmem : (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) ∈ Work.BMF.natIcc A B := (e.symm i).2
      have hb1 := (natIcc_bounds_gen hBpos hmem).1
      have hpos : (0 : ℝ) < ((((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) : ℝ) := by linarith
      have hposn : 0 < (((e.symm i : ↥(Work.BMF.natIcc A B)) : ℕ)) := by exact_mod_cast hpos
      omega
    rw [Work.BMF.cpow_neg_one_sub_I _ hn1 t]
    ring
  have hint : (∫ t in (-S)..S, ‖∑ n ∈ Work.BMF.natIcc A B,
        d n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun z => ‖z‖ ^ 2) (hsum_eq t)
  have hS2 : (∑ i : Fin N, ‖b i‖ ^ 2)
      = ∑ n ∈ Work.BMF.natIcc A B, ‖d n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [← Equiv.sum_comp e (fun i : Fin N => ‖b i‖ ^ 2)]
    have h1 : ∀ x : ↥(Work.BMF.natIcc A B),
        ‖b (e x)‖ ^ 2 = ‖d ((x : ℕ)) / (((x : ℕ)) : ℂ)‖ ^ 2 := by
      intro x; simp only [hb]; rw [Equiv.symm_apply_apply]
    simp only [h1]
    rw [← Finset.sum_attach (Work.BMF.natIcc A B) (fun n => ‖d n‖ ^ 2 / (n : ℝ) ^ 2)]
    rw [Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_div, Complex.norm_natCast, div_pow]
  have hS2nn : (0 : ℝ) ≤ ∑ n ∈ Work.BMF.natIcc A B, ‖d n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hcoef : S - (-S) + C₀ / (1 / B) = 2 * S + C₀ * B := by
    rw [one_div, div_inv_eq_mul]; ring
  have hls := hC₀ (1 / B) hδ N μ b hsep (-S) S (by linarith)
  rw [hcoef, hS2] at hls
  calc (∫ t in (-S)..S, ‖∑ n ∈ Work.BMF.natIcc A B,
        d n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ i : Fin N, b i * Complex.exp (Complex.I * ((μ i : ℂ) * (t : ℂ)))‖ ^ 2 := hint
    _ ≤ (2 * S + C₀ * B) * ∑ n ∈ Work.BMF.natIcc A B, ‖d n‖ ^ 2 / (n : ℝ) ^ 2 := hls
    _ ≤ (2 * S + 3 * C₀ * B) * ∑ n ∈ Work.BMF.natIcc A B, ‖d n‖ ^ 2 / (n : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hS2nn
        nlinarith [mul_nonneg hC₀nn hBpos.le]

end Work.BMF.mr_direct
