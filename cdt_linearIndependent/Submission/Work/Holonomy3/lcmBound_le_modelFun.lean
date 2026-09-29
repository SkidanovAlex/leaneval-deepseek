import Mathlib
import Submission.Work.Holonomy3.model_deps
import Submission.Work.Holonomy3.modelFun_eq_H
import Submission.Work.Holonomy3.lcmBound_eq_modelFun

namespace Work.Holonomy3

open scoped BigOperators

noncomputable section

/-- `H` is nondecreasing. -/
private lemma H_mono_nat (m n : ℕ) (h : m ≤ n) : Submission.CDT.Lcm2Bound.H m ≤ Submission.CDT.Lcm2Bound.H n := by
  unfold Submission.CDT.Lcm2Bound.H
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => by positivity)
  exact Finset.Icc_subset_Icc_right h

private lemma add_max_zero (a b : ℝ) : a + max b 0 = max (a + b) a := by
  rcases le_total b 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : a + b ≤ a), add_zero]
  · rw [max_eq_left h, max_eq_left (by linarith : a ≤ a + b)]

/-- The increasing step. -/
private lemma psi_inc (w t : ℝ) (hw : 0 ≤ w) (ht : 1 ≤ t) (u : ℕ)
    (hu : ⌊(t - 1) / max 1 w⌋₊ ≤ u) :
    Submission.CDT.Lcm2Bound.H u + max (t / ((u : ℝ) + 1) - w) 0
      ≤ Submission.CDT.Lcm2Bound.H (u + 1) + max (t / ((u : ℝ) + 2) - w) 0 := by
  have hBpos : (0 : ℝ) < max 1 w := by positivity
  have hupos : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hHu : Submission.CDT.Lcm2Bound.H u ≤ Submission.CDT.Lcm2Bound.H (u + 1) :=
    H_mono_nat u (u + 1) (Nat.le_succ u)
  have hHu' : Submission.CDT.Lcm2Bound.H (u + 1)
      = Submission.CDT.Lcm2Bound.H u + 1 / ((u : ℝ) + 1) := by
    have h := Submission.CDT.Lcm2Bound.H_succ u
    rw [h]; norm_num
  have hu1 : ((u : ℕ) : ℝ) + 1 > (t - 1) / max 1 w := by
    have h1 : ((⌊(t - 1) / max 1 w⌋₊ : ℕ) : ℝ) + 1 > (t - 1) / max 1 w :=
      Nat.lt_floor_add_one _
    have h2 : ((⌊(t - 1) / max 1 w⌋₊ : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
    linarith
  rw [add_max_zero, add_max_zero]
  by_cases hcase : t - 1 ≤ w * ((u : ℝ) + 1)
  · -- `w(u+1) ≥ t-1` : `H (u+1)` dominates both
    apply max_le
    · refine le_trans ?_ (le_max_right _ _)
      rw [hHu']
      have h1 : (t - 1) / ((u : ℝ) + 1) ≤ w := (div_le_iff₀ hupos).mpr hcase
      have h2 : t / ((u : ℝ) + 1) - 1 / ((u : ℝ) + 1) ≤ w := by
        rw [div_sub_div_same]; exact h1
      linarith
    · exact le_trans hHu (le_max_right _ _)
  · -- `w(u+1) < t-1` : here `w < 1` and `u+2 ≥ t`, so `g (u+1) ≥ g u`
    rw [not_le] at hcase
    have hw1 : w < 1 := by
      by_contra hcon
      rw [not_lt] at hcon
      have hBw : max 1 w = w := max_eq_right hcon
      rw [hBw] at hu1
      have h3 : (t - 1) < w * ((u : ℝ) + 1) := by
        have h4 := (div_lt_iff₀ (lt_of_lt_of_le one_pos hcon)).mp hu1
        linarith [h4]
      linarith
    have hut2 : t ≤ (u : ℝ) + 2 := by
      have hKt : ⌊(t - 1) / max 1 w⌋₊ = ⌊t - 1⌋₊ := by
        rw [max_eq_left hw1.le, div_one]
      have h1 : ((⌊t - 1⌋₊ : ℕ) : ℝ) + 1 > t - 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊t - 1⌋₊ : ℕ) : ℝ) ≤ (u : ℝ) := by
        rw [← hKt]; exact_mod_cast hu
      linarith
    apply max_le
    · refine le_trans ?_ (le_max_left _ _)
      rw [hHu']
      have h1 : t / ((u : ℝ) + 1) - t / ((u : ℝ) + 2) ≤ 1 / ((u : ℝ) + 1) := by
        have hsplit : t / ((u : ℝ) + 1) - t / ((u : ℝ) + 2)
            = t / (((u : ℝ) + 1) * ((u : ℝ) + 2)) := by
          field_simp
          ring
        have h2 : t / (((u : ℝ) + 1) * ((u : ℝ) + 2)) ≤ 1 / ((u : ℝ) + 1) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < ((u : ℝ) + 1) * ((u : ℝ) + 2))]
          have hsimp : (1:ℝ) / ((u : ℝ) + 1) * (((u : ℝ) + 1) * ((u : ℝ) + 2)) = (u : ℝ) + 2 := by
            rw [one_div, ← mul_assoc, inv_mul_cancel₀ (by positivity : ((u:ℝ)+1) ≠ 0), one_mul]
          rw [hsimp]
          exact hut2
        rw [hsplit]; exact h2
      linarith
    · exact le_trans hHu (le_max_right _ _)

/-- The decreasing step. -/
private lemma psi_dec (w t : ℝ) (hw : 0 ≤ w) (ht : 1 ≤ t) (v : ℕ)
    (hv : v + 1 ≤ ⌊(t - 1) / max 1 w⌋₊) :
    Submission.CDT.Lcm2Bound.H (v + 1) + max (t / ((v : ℝ) + 2) - w) 0
      ≤ Submission.CDT.Lcm2Bound.H v + max (t / ((v : ℝ) + 1) - w) 0 := by
  have hBpos : (0 : ℝ) < max 1 w := by positivity
  have hvpos : (0 : ℝ) < (v : ℝ) + 1 := by positivity
  have hHv' : Submission.CDT.Lcm2Bound.H (v + 1)
      = Submission.CDT.Lcm2Bound.H v + 1 / ((v : ℝ) + 1) := by
    have h := Submission.CDT.Lcm2Bound.H_succ v
    rw [h]; norm_num
  have hvle : (v : ℝ) + 1 ≤ (t - 1) / max 1 w := by
    have h1 : ((⌊(t - 1) / max 1 w⌋₊ : ℕ) : ℝ) ≤ (t - 1) / max 1 w :=
      Nat.floor_le (by positivity)
    have h2 : ((v : ℕ) : ℝ) + 1 ≤ ((⌊(t - 1) / max 1 w⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hv
    linarith
  have hmulB : ((v : ℝ) + 1) * max 1 w ≤ t - 1 := (le_div_iff₀ hBpos).mp hvle
  rw [add_max_zero, add_max_zero]
  apply max_le
  · -- `g (v+1) ≤ g v`
    refine le_trans ?_ (le_max_left _ _)
    rw [hHv']
    have hv2 : (v : ℝ) + 2 ≤ t := by
      have hB1 : (1:ℝ) ≤ max 1 w := le_max_left _ _
      have h1 : (t - 1) / max 1 w ≤ t - 1 := by
        rw [div_le_iff₀ hBpos]
        have := mul_le_mul_of_nonneg_left hB1 (by linarith : (0:ℝ) ≤ t - 1)
        linarith [this]
      linarith
    have h1 : 1 / ((v : ℝ) + 1) ≤ t / ((v : ℝ) + 1) - t / ((v : ℝ) + 2) := by
      have hsplit : t / ((v : ℝ) + 1) - t / ((v : ℝ) + 2)
          = t / (((v : ℝ) + 1) * ((v : ℝ) + 2)) := by
        field_simp
        ring
      have h2 : 1 / ((v : ℝ) + 1) ≤ t / (((v : ℝ) + 1) * ((v : ℝ) + 2)) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < ((v : ℝ) + 1) * ((v : ℝ) + 2))]
        have hsimp : (1:ℝ) / ((v : ℝ) + 1) * (((v : ℝ) + 1) * ((v : ℝ) + 2)) = (v : ℝ) + 2 := by
          rw [one_div, ← mul_assoc, inv_mul_cancel₀ (by positivity : ((v:ℝ)+1) ≠ 0), one_mul]
        rw [hsimp]
        exact hv2
      rw [hsplit]; exact h2
    linarith
  · -- `H (v+1) ≤ g v`, via `(t-1)/(v+1) ≥ w`
    refine le_trans ?_ (le_max_left _ _)
    rw [hHv']
    have h1 : w ≤ (t - 1) / ((v : ℝ) + 1) := by
      rw [le_div_iff₀ hvpos]
      have hBle : w ≤ max 1 w := le_max_right _ _
      have h2 : w * ((v : ℝ) + 1) ≤ ((v : ℝ) + 1) * max 1 w := by
        rw [mul_comm w]
        exact mul_le_mul_of_nonneg_left hBle (by positivity)
      linarith
    have h2 : t / ((v : ℝ) + 1) - 1 / ((v : ℝ) + 1) ≥ w := by
      rw [div_sub_div_same]; exact h1
    linarith

private theorem H_psi_min_aux (w : ℝ) (hw : 0 ≤ w) (t : ℝ) (ht : 1 ≤ t) (j : ℕ) (hj : 1 ≤ j) :
    Submission.CDT.Lcm2Bound.H ⌊(t - 1) / max 1 w⌋₊
      + max (t / (((⌊(t - 1) / max 1 w⌋₊ + 1 : ℕ)) : ℝ) - w) 0
    ≤ Submission.CDT.Lcm2Bound.H (j - 1) + max (t / (j : ℝ) - w) 0 := by
  set K : ℕ := ⌊(t - 1) / max 1 w⌋₊ with hK
  set Ψ : ℕ → ℝ := fun u => Submission.CDT.Lcm2Bound.H u + max (t / ((u : ℝ) + 1) - w) 0 with hΨ
  have hinc : ∀ u, K ≤ u → Ψ u ≤ Ψ (u + 1) := by
    intro u hu
    have hcast : ((u + 1 : ℕ) : ℝ) + 1 = (u : ℝ) + 2 := by push_cast; ring
    simp only [hΨ, hcast]
    exact psi_inc w t hw ht u (by simpa only [hK] using hu)
  have hdec : ∀ v, v + 1 ≤ K → Ψ (v + 1) ≤ Ψ v := by
    intro v hv
    have hcast : ((v + 1 : ℕ) : ℝ) + 1 = (v : ℝ) + 2 := by push_cast; ring
    simp only [hΨ, hcast]
    exact psi_dec w t hw ht v (by simpa only [hK] using hv)
  have key : Ψ K ≤ Ψ (j - 1) := by
    rcases le_total K (j - 1) with h | h
    · exact Nat.le_induction (le_refl (Ψ K)) (fun n hn ih => le_trans ih (hinc n hn)) (j - 1) h
    · have hdown : ∀ d, Ψ K ≤ Ψ (K - d) := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          by_cases hd : d + 1 ≤ K
          · have h1 : K - (d + 1) + 1 = K - d := by omega
            have h2 : K - (d + 1) + 1 ≤ K := by omega
            rw [← h1] at ih
            exact le_trans ih (hdec (K - (d + 1)) h2)
          · have h1 : K - (d + 1) = K - d := by omega
            rw [h1]; exact ih
      have h3 := hdown (K - (j - 1))
      have h4 : K - (K - (j - 1)) = j - 1 := by omega
      rwa [h4] at h3
  have hjc : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    rw [Nat.cast_sub hj]; ring
  rw [hΨ] at key
  simp only [Nat.cast_add, Nat.cast_one, hK, hjc] at key ⊢
  exact key

/-- `modelFun` is 1-Lipschitz and nonincreasing in its parameter on `w ≥ 0` for `t ≥ 1`. -/
private theorem modelFun_param_lipschitz (w v : ℝ) (hw : 0 ≤ w) (hwv : w ≤ v) (t : ℝ) (ht : 1 ≤ t) :
    Submission.CDT.IntegratedLcm.modelFun w t
      ≤ Submission.CDT.IntegratedLcm.modelFun v t + (v - w) := by
  have hv0 : 0 ≤ v := le_trans hw hwv
  have h1 := H_psi_min_aux w hw t ht (⌊(t - 1) / max 1 v⌋₊ + 1) (Nat.le_add_left 1 _)
  have h2 := modelFun_eq_H v hv0 t ht
  have h3 := modelFun_eq_H w hw t ht
  have hcast : ((⌊(t - 1) / max 1 v⌋₊ + 1 : ℕ) : ℝ) = (⌊(t - 1) / max 1 v⌋₊ : ℝ) + 1 := by
    push_cast; ring
  have h4 : max (t / (((⌊(t - 1) / max 1 v⌋₊ + 1 : ℕ)) : ℝ) - w) 0
      ≤ max (t / (((⌊(t - 1) / max 1 v⌋₊ + 1 : ℕ)) : ℝ) - v) 0 + (v - w) := by
    have h5 : t / (((⌊(t - 1) / max 1 v⌋₊ + 1 : ℕ)) : ℝ) - w
        = (t / (((⌊(t - 1) / max 1 v⌋₊ + 1 : ℕ)) : ℝ) - v) + (v - w) := by ring
    rw [h5]
    apply max_le
    · linarith [le_max_left (t / (((⌊(t - 1) / max 1 v⌋₊ + 1 : ℕ)) : ℝ) - v) 0]
    · linarith [le_max_right (t / (((⌊(t - 1) / max 1 v⌋₊ + 1 : ℕ)) : ℝ) - v) 0]
  rw [h3, h2]
  have h1' : Submission.CDT.Lcm2Bound.H ⌊(t - 1) / max 1 w⌋₊
      + max (t / (((⌊(t - 1) / max 1 w⌋₊ + 1 : ℕ)) : ℝ) - w) 0
      ≤ Submission.CDT.Lcm2Bound.H ⌊(t - 1) / max 1 v⌋₊
        + max (t / (((⌊(t - 1) / max 1 v⌋₊ + 1 : ℕ)) : ℝ) - w) 0 := by
    simpa using h1
  linarith

/-- The right-hand side of the paper's Lemma `lcm-2` (2) at `k = D`, `l = ⌊ξD⌋` (as formalised in
`Submission.CDT.Lcm2Bound.log_Lge_le_uniform`) is at most `D` times the model function `modelFun ξ`
evaluated at `n/D`, up to the additive constant `2`; here `H m = Σ_{a ≤ m} 1/a`.
(Checked numerically with exact rational arithmetic for many `ξ`, `m`, `D ≤ 1000` and all
`D ≤ n ≤ (m+1)D`: the maximum of the difference is `< 1`.) -/
theorem lcmBound_le_modelFun (D : ℕ) (hD : 1 ≤ D) (ξ : ℝ) (hξ0 : 0 ≤ ξ) {n : ℕ} (hn : D ≤ n) :
    (D : ℝ) * Submission.CDT.Lcm2Bound.H ((n - D) / max D ⌊ξ * D⌋₊)
      + max ((n : ℝ) / (((n + (⌊ξ * D⌋₊ - D)) / max D ⌊ξ * D⌋₊ : ℕ) : ℝ) - (⌊ξ * D⌋₊ : ℝ)) 0
    ≤ (D : ℝ) * Submission.CDT.IntegratedLcm.modelFun ξ ((n : ℝ) / D) + 2 := by
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hxD : (1:ℝ) ≤ (n:ℝ)/(D:ℝ) := by
    rw [le_div_iff₀ hD0]
    simpa using (by exact_mod_cast hn : ((D:ℝ)) ≤ ((n:ℝ)))
  have hle : ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ) ≤ ξ * (D:ℝ) := Nat.floor_le (by positivity)
  have hlt : ξ * (D:ℝ) < ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlam0 : 0 ≤ ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ) := by positivity
  have hlamxi : ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ) ≤ ξ := by
    rw [div_le_iff₀ hD0]
    exact hle
  have hlip := modelFun_param_lipschitz (((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ)) ξ hlam0 hlamxi
    ((n:ℝ)/(D:ℝ)) hxD
  have hcast : (D:ℝ) * (((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ)) = ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ) := by
    field_simp
  have hDxi : (D:ℝ) * (ξ - ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ)) ≤ 1 := by
    have hh : (D:ℝ) * (ξ - ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ))
        = (D:ℝ)*ξ - ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ) := by rw [mul_sub, hcast]
    rw [hh]; linarith
  have hL := lcmBound_eq_modelFun D hD ξ hξ0 hn
  rw [hL]
  have h2 : (D:ℝ) * Submission.CDT.IntegratedLcm.modelFun (((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ)) ((n:ℝ)/(D:ℝ))
      ≤ (D:ℝ) * Submission.CDT.IntegratedLcm.modelFun ξ ((n:ℝ)/(D:ℝ))
        + (D:ℝ) * (ξ - ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ)) := by
    calc (D:ℝ) * Submission.CDT.IntegratedLcm.modelFun (((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ)) ((n:ℝ)/(D:ℝ))
        ≤ (D:ℝ) * (Submission.CDT.IntegratedLcm.modelFun ξ ((n:ℝ)/(D:ℝ))
            + (ξ - ((⌊ξ * (D:ℝ)⌋₊ : ℕ) : ℝ)/(D:ℝ))) :=
          mul_le_mul_of_nonneg_left hlip hD0.le
      _ = _ := by ring
  linarith

end
end Work.Holonomy3
