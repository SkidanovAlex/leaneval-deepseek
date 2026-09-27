import Mathlib

namespace Work.Drive

/-- Core construction of the reparametrisation.

Given `e < a < s` and `a < 1`, and a parameter `μ > 0` such that the affine map
`g t = s + μ * (t - 1)` is above the identity on `(-∞, a]`, the function
`ψ t = (1 - χ t) * t + χ t * g t`, where `χ` is a smooth increasing step from `0`
on `(-∞, e]` to `1` on `[a, ∞)`, satisfies all the required properties.  The
derivative is `(1 - χ t) + χ t * μ + χ' t * (g t - t)`, a convex combination of
`1` and `μ` plus a nonnegative correction. -/
theorem smoothTransition_reparam_core {e s a μ : ℝ} (hea : e < a) (has : a < s)
    (ha1 : a < 1) (hμ : 0 < μ) (hgt : ∀ t : ℝ, t ≤ a → t ≤ s + μ * (t - 1)) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ t : ℝ, 0 < deriv ψ t) ∧
      (∀ t : ℝ, t ≤ e → ψ t = t) ∧
      ψ 1 = s ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ψ t ≤ s) ∧
      ∃ (μ' a' : ℝ), 0 < μ' ∧ a' < 1 ∧ ∀ t : ℝ, a' ≤ t → t ≤ 1 → ψ t = s + μ' * (t - 1) := by
  have hLpos : 0 < a - e := sub_pos.mpr hea
  let χ : ℝ → ℝ := fun t => Real.smoothTransition ((t - e) / (a - e))
  let g : ℝ → ℝ := fun t => s + μ * (t - 1)
  let ψ : ℝ → ℝ := fun t => (1 - χ t) * t + χ t * g t
  have hχ_smth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    dsimp only [χ]; fun_prop
  have hχ_zero : ∀ t, t ≤ e → χ t = 0 := by
    intro t ht
    have h : (t - e) / (a - e) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hLpos.le
    simpa only [χ] using Real.smoothTransition.zero_of_nonpos h
  have hχ_one : ∀ t, a ≤ t → χ t = 1 := by
    intro t ht
    have h1 : 1 ≤ (t - e) / (a - e) := by
      rw [le_div_iff₀ hLpos]; linarith
    simpa only [χ] using Real.smoothTransition.one_of_one_le h1
  have hχ_mem : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1 := fun t =>
    ⟨by simpa only [χ] using Real.smoothTransition.nonneg ((t - e) / (a - e)),
     by simpa only [χ] using Real.smoothTransition.le_one ((t - e) / (a - e))⟩
  have hχ_mono : Monotone χ := by
    intro x y hxy
    simp only [χ]
    exact Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (sub_le_sub_right hxy e) hLpos.le)
  have hχdnn : ∀ t, 0 ≤ deriv χ t := fun _ => Monotone.deriv_nonneg hχ_mono
  have hχd_zero : ∀ t, a < t → deriv χ t = 0 := by
    intro t ht
    have hmem : Set.Ici a ∈ nhds t :=
      Filter.mem_of_superset (Ioi_mem_nhds ht) (fun u hu => Set.mem_Ici.mpr (le_of_lt hu))
    have hev : χ =ᶠ[nhds t] (fun _ : ℝ => (1 : ℝ)) :=
      Filter.Eventually.mono hmem (fun u hu => hχ_one u (Set.mem_Ici.mp hu))
    rw [hev.deriv_eq, deriv_const]
  have hg_smth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    dsimp only [g]; fun_prop
  have hψ_smth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    dsimp only [ψ]
    exact ((contDiff_const.sub hχ_smth).mul contDiff_id).add (hχ_smth.mul hg_smth)
  have hψderiv : ∀ t, deriv ψ t = (1 - χ t) + χ t * μ + deriv χ t * (g t - t) := by
    intro t
    have hχd : HasDerivAt χ (deriv χ t) t :=
      ((hχ_smth.differentiable (by simp)).differentiableAt).hasDerivAt
    have hgd : HasDerivAt g μ t := by
      dsimp only [g]
      have h1 : HasDerivAt (fun u : ℝ => u - 1) 1 t := (hasDerivAt_id t).sub_const 1
      have h2 : HasDerivAt (fun u : ℝ => μ * (u - 1)) μ t := by
        simpa using h1.const_mul μ
      exact h2.const_add s
    have h1 : HasDerivAt (fun u : ℝ => (1 - χ u) * u)
        ((-(deriv χ t)) * t + (1 - χ t) * 1) t := (hχd.const_sub 1).mul (hasDerivAt_id t)
    have h2 : HasDerivAt (fun u : ℝ => χ u * g u) ((deriv χ t) * g t + χ t * μ) t :=
      hχd.mul hgd
    have hpsi : ψ = (fun u : ℝ => (1 - χ u) * u) + (fun u : ℝ => χ u * g u) := rfl
    have hsum := h1.add h2
    rw [hpsi, hsum.deriv]
    ring
  refine ⟨ψ, hψ_smth, ?_, ?_, ?_, ?_, μ, a, hμ, ha1, ?_⟩
  · intro t
    have hconv : 0 < (1 - χ t) + χ t * μ := by
      have h1 := (hχ_mem t).1
      have h2 := (hχ_mem t).2
      by_cases hμ1 : 1 ≤ μ
      · nlinarith [mul_le_mul_of_nonneg_left hμ1 h1]
      · have hμ1' : μ < 1 := not_le.mp hμ1
        nlinarith [mul_le_mul_of_nonneg_left hμ1'.le (sub_nonneg.mpr h2), hμ]
    rw [hψderiv t]
    rcases lt_or_ge a t with ht | ht
    · rw [hχd_zero t ht]
      simp only [zero_mul, add_zero]
      linarith
    · have hgt' : 0 ≤ g t - t := by dsimp only [g]; linarith [hgt t ht]
      have := mul_nonneg (hχdnn t) hgt'
      linarith
  · intro t ht
    have h0 : χ t = 0 := hχ_zero t ht
    dsimp only [ψ]
    rw [h0]
    ring
  · have h1 : χ 1 = 1 := hχ_one 1 (le_of_lt ha1)
    dsimp only [ψ, g]
    rw [h1]
    ring
  · intro t _ ht1
    rcases lt_or_ge a t with ht | ht
    · have h1 : χ t = 1 := hχ_one t ht.le
      have hψg : ψ t = g t := by dsimp only [ψ]; rw [h1]; ring
      rw [hψg]
      dsimp only [g]
      nlinarith [hμ, ht1]
    · have hgs : g t ≤ s := by dsimp only [g]; nlinarith [hμ, ht1]
      have hts : t ≤ s := le_trans ht has.le
      calc ψ t = (1 - χ t) * t + χ t * g t := rfl
        _ ≤ (1 - χ t) * s + χ t * s := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hts (sub_nonneg.mpr (hχ_mem t).2)
              · exact mul_le_mul_of_nonneg_left hgs (hχ_mem t).1
        _ = s := by ring
  · intro t hat _
    have h1 : χ t = 1 := hχ_one t hat
    dsimp only [ψ, g]
    rw [h1]
    ring

theorem exists_reparamLand {e s : ℝ} (he : 0 < e) (heh : e < 1 / 2) (hes : e < s) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ t : ℝ, 0 < deriv ψ t) ∧
      (∀ t : ℝ, t ≤ e → ψ t = t) ∧
      ψ 1 = s ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ψ t ≤ s) ∧
      ∃ (μ a : ℝ), 0 < μ ∧ a < 1 ∧ ∀ t : ℝ, a ≤ t → t ≤ 1 → ψ t = s + μ * (t - 1) := by
  by_cases h1s : 1 ≤ s
  · refine smoothTransition_reparam_core (e := e) (s := s) (a := (e + 1) / 2) (μ := 1)
      ?_ ?_ ?_ one_pos ?_
    · linarith
    · linarith
    · linarith
    · intro t _
      linarith
  · have hs1 : s < 1 := not_le.mp h1s
    set a : ℝ := (e + s) / 2 with ha
    set μ : ℝ := (s - a) / (1 - a) with hμdef
    have hae : e < a := by rw [ha]; linarith
    have has : a < s := by rw [ha]; linarith
    have ha1 : a < 1 := by rw [ha]; linarith
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    have hμ : 0 < μ := by
      rw [hμdef]; exact div_pos (by linarith) (by linarith)
    have hgt : ∀ t : ℝ, t ≤ a → t ≤ s + μ * (t - 1) := by
      intro t ht
      have hkey : μ * (1 - a) = s - a := by
        rw [hμdef, div_mul_cancel₀ (s - a) h1a]
      have hμlt : μ < 1 := by
        rw [hμdef, div_lt_iff₀ (by linarith : (0 : ℝ) < 1 - a)]
        linarith
      rw [← sub_nonneg]
      have hdiff : s + μ * (t - 1) - t = (1 - μ) * (a - t) := by
        linear_combination -hkey
      rw [hdiff]
      exact mul_nonneg (by linarith) (by linarith)
    exact smoothTransition_reparam_core hae has ha1 hμ hgt

end Work.Drive
