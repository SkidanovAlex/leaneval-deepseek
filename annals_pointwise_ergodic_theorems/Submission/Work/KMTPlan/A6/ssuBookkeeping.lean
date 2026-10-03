import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Filter Topology

/-- `x ^ s · 2 ^ (-(ρ x)) → 0` at `+∞` for `ρ > 0` (exponential beats polynomial). -/
private lemma tendsto_mul_two_rpow_neg_atTop (ρ : ℝ) (hρ : 0 < ρ) (s : ℝ) :
    Tendsto (fun x : ℝ => x ^ s * (2 : ℝ) ^ (-(ρ * x))) atTop (𝓝 0) := by
  have hc : 0 < Real.log 2 * ρ := mul_pos (Real.log_pos one_lt_two) hρ
  have hfun : (fun x : ℝ => x ^ s * (2 : ℝ) ^ (-(ρ * x)))
      = fun x : ℝ => x ^ s * Real.exp (-(Real.log 2 * ρ) * x) := by
    funext x
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
      show Real.log 2 * (-(ρ * x)) = -(Real.log 2 * ρ) * x by ring]
  rw [hfun]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s _ hc

/-- For any `M N P : ℝ` and `c > 0`, eventually
`M (1 + x 2 ^ (ρ x / 2) + x) + N x + P < c · 2 ^ (ρ x)`: the exponential `2 ^ (ρ x)` dominates
the polynomial expression.  This is the single analytic input of `ssuBookkeeping`. -/
private lemma eventually_const_lt_const_mul_two_rpow
    (ρ : ℝ) (hρ : 0 < ρ) (M N P c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      M * (1 + x * (2 : ℝ) ^ (ρ * x / 2) + x) + N * x + P < c * (2 : ℝ) ^ (ρ * x) := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hρ2 : 0 < ρ / 2 := by linarith
  have hA' : Tendsto (fun x : ℝ => (2 : ℝ) ^ (-(ρ * x))) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using tendsto_mul_two_rpow_neg_atTop ρ hρ 0
  have hxA' : Tendsto (fun x : ℝ => x * (2 : ℝ) ^ (-(ρ * x))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_mul_two_rpow_neg_atTop ρ hρ 1
  have hD : Tendsto (fun x : ℝ => (2 : ℝ) ^ (-(ρ * x / 2))) atTop (𝓝 0) := by
    refine (tendsto_mul_two_rpow_neg_atTop (ρ/2) hρ2 0).congr' (Eventually.of_forall ?_)
    intro x
    simp only [Real.rpow_zero, one_mul]
    rw [show -(ρ * x / 2) = -(ρ / 2 * x) by ring]
  have hxD : Tendsto (fun x : ℝ => x * (2 : ℝ) ^ (-(ρ * x / 2))) atTop (𝓝 0) := by
    refine (tendsto_mul_two_rpow_neg_atTop (ρ/2) hρ2 1).congr' (Eventually.of_forall ?_)
    intro x
    simp only [Real.rpow_one]
    rw [show -(ρ * x / 2) = -(ρ / 2 * x) by ring]
  have hcomb : Tendsto (fun x : ℝ =>
        M * ((2:ℝ)^(-(ρ*x)) + (x * (2:ℝ)^(-(ρ*x/2)) + x * (2:ℝ)^(-(ρ*x))))
        + (N * (x * (2:ℝ)^(-(ρ*x))) + P * (2:ℝ)^(-(ρ*x)))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun x : ℝ =>
        M * ((2:ℝ)^(-(ρ*x)) + (x * (2:ℝ)^(-(ρ*x/2)) + x * (2:ℝ)^(-(ρ*x))))) atTop (𝓝 0) := by
      simpa using (hA'.add (hxD.add hxA')).const_mul M
    have hrest : Tendsto (fun x : ℝ =>
        N * (x * (2:ℝ)^(-(ρ*x))) + P * (2:ℝ)^(-(ρ*x))) atTop (𝓝 0) := by
      simpa using (hxA'.const_mul N).add (hA'.const_mul P)
    simpa using hsum.add hrest
  have hBA' : ∀ x : ℝ, (2:ℝ)^(ρ*x/2) * (2:ℝ)^(-(ρ*x)) = (2:ℝ)^(-(ρ*x/2)) := by
    intro x
    rw [← Real.rpow_add h2, show ρ*x/2 + -(ρ*x) = -(ρ*x/2) by ring]
  have hkey : ∀ x : ℝ,
      M * ((2:ℝ)^(-(ρ*x)) + (x * (2:ℝ)^(-(ρ*x/2)) + x * (2:ℝ)^(-(ρ*x))))
      + (N * (x * (2:ℝ)^(-(ρ*x))) + P * (2:ℝ)^(-(ρ*x)))
      = (M * (1 + x * (2:ℝ)^(ρ*x/2) + x) + N * x + P) * (2:ℝ)^(-(ρ*x)) := by
    intro x
    have h1 : (1 + x * (2:ℝ)^(ρ*x/2) + x) * (2:ℝ)^(-(ρ*x))
        = (2:ℝ)^(-(ρ*x)) + x * (2:ℝ)^(-(ρ*x/2)) + x * (2:ℝ)^(-(ρ*x)) := by
      rw [show (1 + x * (2:ℝ)^(ρ*x/2) + x) * (2:ℝ)^(-(ρ*x))
          = (2:ℝ)^(-(ρ*x)) + x * ((2:ℝ)^(ρ*x/2) * (2:ℝ)^(-(ρ*x)))
            + x * (2:ℝ)^(-(ρ*x)) by ring, hBA' x]
    rw [show (M * (1 + x * (2:ℝ)^(ρ*x/2) + x) + N * x + P) * (2:ℝ)^(-(ρ*x))
          = M * ((1 + x * (2:ℝ)^(ρ*x/2) + x) * (2:ℝ)^(-(ρ*x)))
            + N * (x * (2:ℝ)^(-(ρ*x))) + P * (2:ℝ)^(-(ρ*x)) by ring, h1]
    ring
  have hlt := hcomb.eventually_lt tendsto_const_nhds hc
  filter_upwards [hlt] with x hx
  have hx' : (M * (1 + x * (2:ℝ)^(ρ*x/2) + x) + N * x + P) * (2:ℝ)^(-(ρ*x)) < c := by
    rw [← hkey x]; exact hx
  have hA'pos : 0 < (2:ℝ)^(-(ρ*x)) := Real.rpow_pos_of_pos h2 _
  have hinv : ((2:ℝ)^(-(ρ*x)))⁻¹ = (2:ℝ)^(ρ*x) := by
    rw [Real.rpow_neg h2.le, inv_inv]
  calc M * (1 + x * (2:ℝ)^(ρ*x/2) + x) + N * x + P
      = (M * (1 + x * (2:ℝ)^(ρ*x/2) + x) + N * x + P) * (2:ℝ)^(-(ρ*x))
          * ((2:ℝ)^(-(ρ*x)))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hA'pos.ne', mul_one]
    _ < c * ((2:ℝ)^(-(ρ*x)))⁻¹ := mul_lt_mul_of_pos_right hx' (inv_pos.mpr hA'pos)
    _ = c * (2:ℝ)^(ρ*x) := by rw [hinv]

/-- Monotonicity of `l ↦ C (1 + l · 2 ^ (ρ l / 2) + l) + l`. -/
private lemma mono_two_rpow_add (ρ : ℝ) (hρ : 0 < ρ) (C : ℝ) (hC : 0 ≤ C) {l L : ℕ}
    (hl : l ≤ L) :
    C * (1 + (l:ℝ) * (2:ℝ)^(ρ*(l:ℝ)/2) + (l:ℝ)) + (l:ℝ)
      ≤ C * (1 + (L:ℝ) * (2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) + (L:ℝ) := by
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hlR : (l:ℝ) ≤ (L:ℝ) := by exact_mod_cast hl
  have hbl : (2:ℝ)^(ρ*(l:ℝ)/2) ≤ (2:ℝ)^(ρ*(L:ℝ)/2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    have hpos : 0 ≤ ρ * ((L:ℝ) - (l:ℝ)) := mul_nonneg (le_of_lt hρ) (by linarith)
    nlinarith [hpos]
  have hprod : (l:ℝ)*(2:ℝ)^(ρ*(l:ℝ)/2) ≤ (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) :=
    mul_le_mul hlR hbl (Real.rpow_pos_of_pos h2pos _).le (Nat.cast_nonneg L)
  have hcore : (1 + (l:ℝ)*(2:ℝ)^(ρ*(l:ℝ)/2) + (l:ℝ))
      ≤ (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) := by linarith
  have := mul_le_mul_of_nonneg_left hcore hC
  linarith [hlR]

theorem ssuBookkeeping (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (cI : ℝ) (hcI : 0 < cI)
    (Cna Csep Kdev Kerr : ℝ) (hCna : 0 ≤ Cna) (hCsep : 0 ≤ Csep)
    (hKdev : 0 ≤ Kdev) (hKerr : 0 ≤ Kerr) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ (L u : ℕ), L₀ ≤ L → (L : ℝ) ≤ (u : ℝ) →
      (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (u : ℝ) →
      ∃ E : ℕ, 2 ≤ E ∧ (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (E : ℝ) ∧
        Cna * (1 + (L : ℝ) * (2 : ℝ) ^ (ρ * (L : ℝ) / 2) + (L : ℝ)) + 2 ≤ 2 * (u : ℝ) ∧
        (∀ l : ℕ, l ≤ L → Csep * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)) + 1
          ≤ 3 * (u : ℝ)) ∧
        (∀ l : ℕ, l ≤ L → Csep * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)) + 1
          ≤ (E : ℝ) - (l : ℝ) + 1) ∧
        Kdev * (1 + (L : ℝ) * (2 : ℝ) ^ (ρ * (L : ℝ) / 2) + (L : ℝ))
          + 2 * (2 : ℝ) ^ (ρ * (L : ℝ)) + Kdev ≤ (E : ℝ) ∧
        (E : ℝ) + (cI / 2) * (L : ℝ) + Kerr ≤ 3 * (u : ℝ) := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1
    (eventually_const_lt_const_mul_two_rpow ρ hρ Kdev (cI/2) (Kdev + Kerr + 1) 1 one_pos)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    (eventually_const_lt_const_mul_two_rpow ρ hρ Csep (1 + cI/2) (Kerr + 1) 3 (by norm_num))
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.1
    (eventually_const_lt_const_mul_two_rpow ρ hρ Cna 0 2 2 (by norm_num))
  refine ⟨max 1 (Nat.ceil (max X₁ (max X₂ X₃)) + 1), le_max_left _ _, ?_⟩
  intro L u hLL₀ hLu hu
  have hXL : max X₁ (max X₂ X₃) ≤ (L:ℝ) := by
    have h1 : Nat.ceil (max X₁ (max X₂ X₃)) + 1 ≤ L := le_trans (le_max_right 1 _) hLL₀
    have h2 : ((Nat.ceil (max X₁ (max X₂ X₃)) + 1 : ℕ) : ℝ) ≤ (L:ℝ) := by exact_mod_cast h1
    have h3 : max X₁ (max X₂ X₃) ≤ (Nat.ceil (max X₁ (max X₂ X₃)) : ℝ) := Nat.le_ceil _
    push_cast at h2
    linarith
  have hX₁' : X₁ ≤ (L:ℝ) := le_trans (le_max_left _ _) hXL
  have hX₂' : X₂ ≤ (L:ℝ) := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hXL)
  have hX₃' : X₃ ≤ (L:ℝ) := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hXL)
  have hx0 : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hA1 : (1:ℝ) ≤ (2:ℝ)^(ρ*(L:ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
      (show (0:ℝ) ≤ ρ*(L:ℝ) by positivity)
    simpa using this
  have hBpos : (0:ℝ) < (2:ℝ)^(ρ*(L:ℝ)/2) := Real.rpow_pos_of_pos h2pos _
  have h1 := hX₁ (L:ℝ) hX₁'
  have h2 := hX₂ (L:ℝ) hX₂'
  have h3 := hX₃ (L:ℝ) hX₃'
  simp only [one_mul] at h1
  simp only [add_mul, one_mul, zero_mul, add_zero] at h2 h3
  have hterm : (0:ℝ) < 1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ) := by
    have : 0 ≤ (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) := mul_nonneg hx0 hBpos.le
    linarith
  have hnn : (0:ℝ) ≤ Kdev * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) :=
    mul_nonneg hKdev hterm.le
  have hcI1 : (cI/2)*(L:ℝ) + Kerr + 1 < (2:ℝ)^(ρ*(L:ℝ)) := by
    linarith
  set K : ℝ := max (Kdev * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ))
        + 2*(2:ℝ)^(ρ*(L:ℝ)) + Kdev)
      (Csep * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) + (L:ℝ)) with hKdef
  have hK1 : Kdev * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) + 2*(2:ℝ)^(ρ*(L:ℝ)) + Kdev ≤ K := by
    rw [hKdef]; exact le_max_left _ _
  have hK2 : Csep * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) + (L:ℝ) ≤ K := by
    rw [hKdef]; exact le_max_right _ _
  have h2t1 : (2:ℝ) ≤ Kdev * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ))
      + 2*(2:ℝ)^(ρ*(L:ℝ)) + Kdev := by linarith [hA1, hnn, hKdev]
  have hat1 : (2:ℝ)^(ρ*(L:ℝ)) ≤ Kdev * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ))
      + 2*(2:ℝ)^(ρ*(L:ℝ)) + Kdev := by linarith [hA1, hnn, hKdev]
  have hKlt : K < 3*(2:ℝ)^(ρ*(L:ℝ)) - (cI/2)*(L:ℝ) - Kerr - 1 := by
    have hb3 : Kdev * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) + 2*(2:ℝ)^(ρ*(L:ℝ)) + Kdev
        < 3*(2:ℝ)^(ρ*(L:ℝ)) - (cI/2)*(L:ℝ) - Kerr - 1 := by linarith [h1]
    have hb4 : Csep * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) + (L:ℝ)
        < 3*(2:ℝ)^(ρ*(L:ℝ)) - (cI/2)*(L:ℝ) - Kerr - 1 := by linarith [h2]
    rw [hKdef]
    exact max_lt hb3 hb4
  refine ⟨Nat.ceil K, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hE : (2:ℝ) ≤ ((Nat.ceil K : ℕ) : ℝ) :=
      le_trans h2t1 (le_trans hK1 (Nat.le_ceil K))
    exact_mod_cast hE
  · exact le_trans hat1 (le_trans hK1 (Nat.le_ceil K))
  · linarith [h3, hu]
  · intro l hl
    have hl0 : (0:ℝ) ≤ (l:ℝ) := Nat.cast_nonneg l
    have hmono := mono_two_rpow_add ρ hρ Csep hCsep hl
    have hcIL : (0:ℝ) ≤ (cI/2)*(L:ℝ) := mul_nonneg (by linarith) hx0
    linarith [hmono, h2, hu, hl0, hcIL, hKerr]
  · intro l hl
    have hmono := mono_two_rpow_add ρ hρ Csep hCsep hl
    have hE : ((Nat.ceil K : ℕ) : ℝ)
        ≥ Csep * (1 + (L:ℝ)*(2:ℝ)^(ρ*(L:ℝ)/2) + (L:ℝ)) + (L:ℝ) :=
      le_trans hK2 (Nat.le_ceil K)
    linarith [hmono, hE]
  · exact le_trans hK1 (Nat.le_ceil K)
  · have hElt : ((Nat.ceil K : ℕ) : ℝ) < 3*(2:ℝ)^(ρ*(L:ℝ)) - (cI/2)*(L:ℝ) - Kerr := by
      have hc := Nat.ceil_lt_add_one (show (0:ℝ) ≤ K by linarith [h2t1, hK1])
      linarith [hKlt]
    linarith [hElt, hu]

end Work.KMTPlan.A6
