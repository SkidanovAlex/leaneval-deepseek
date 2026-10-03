import Mathlib

namespace Work.A3

/-- The two real-variable consequences of the transition-arc hypothesis `|β| * N^d ≤ (N/q)^{d/(d+1)} / 100`: raising to the `d`-th power gives the product bound `|β| N^{d²/(d+1)} q^{d/(d+1)} ≤ 1/100` (note `d²/(d+1) - d = -d/(d+1)`), and raising to the power `-1/d` gives the lower bound `|β|^{-1/d} ≥ 100^{1/d} N^{d/(d+1)} q^{1/(d+1)}` for the decay scale of the singular integral.  Proof: divide by `N^d`, use `(N/q)^{d/(d+1)} = N^{d/(d+1)}q^{-d/(d+1)}`, `(N^{d/(d+1)})^d = (N^d)^{1/(d+1)}`-style `Real.rpow_mul` manipulations, and monotonicity of `t ↦ t^{-1/d}`. -/
lemma beta_caseA_bounds (N d q : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) (hq : 1 ≤ q)
    {β : ℝ} (hβ : 0 < |β|)
    (hmain : |β| * (N:ℝ)^d ≤ ((N:ℝ)/(q:ℝ))^((d:ℝ)/((d:ℝ)+1)) / 100) :
    (|β| * (N:ℝ)^(((d:ℝ)^2)/((d:ℝ)+1)) * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) ≤ 1/100)
      ∧ (100^(1/(d:ℝ)) * (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1))
          ≤ |β|^(-(1:ℝ)/(d:ℝ))) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd1pos : (0:ℝ) < (d:ℝ) + 1 := by linarith
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hd1ne : (d:ℝ) + 1 ≠ 0 := ne_of_gt hd1pos
  have hNnn : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNpos
  have hqnn : (0:ℝ) ≤ (q:ℝ) := le_of_lt hqpos
  -- Rewrite the hypothesis with `Real.rpow`: `N^d` as a real power and `(N/q)^{d/(d+1)}`
  -- as `N^{d/(d+1)} / q^{d/(d+1)}`.
  have hmainr : |β| * (N:ℝ)^((d:ℝ)) ≤
      ((N:ℝ)^((d:ℝ)/((d:ℝ)+1)) / (q:ℝ)^((d:ℝ)/((d:ℝ)+1))) / 100 := by
    simpa only [Real.rpow_natCast, Real.div_rpow hNnn hqnn] using hmain
  have hqrpos : 0 < (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) := Real.rpow_pos_of_pos hqpos _
  -- Multiply by `100 * q^{d/(d+1)}` and cancel the power of `q`.
  have hA : |β| * (N:ℝ)^((d:ℝ)) * 100 * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) ≤
      (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) := by
    have hstep1 : |β| * (N:ℝ)^((d:ℝ)) * 100 ≤
        (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) / (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) := by
      have h := mul_le_mul_of_nonneg_right hmainr (by norm_num : (0:ℝ) ≤ (100:ℝ))
      simpa only [div_mul_cancel₀ _ (by norm_num : (100:ℝ) ≠ 0)] using h
    have h := mul_le_mul_of_nonneg_right hstep1 (le_of_lt hqrpos)
    simpa only [div_mul_cancel₀ _ (ne_of_gt hqrpos)] using h
  have hNrpos : 0 < (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) := Real.rpow_pos_of_pos hNpos _
  -- Divide by `N^{d/(d+1)}`.
  have hB : |β| * (N:ℝ)^((d:ℝ)) * 100 * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) /
      (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) ≤ 1 := by
    have h := div_le_div_of_nonneg_right hA (le_of_lt hNrpos)
    rwa [div_self (ne_of_gt hNrpos)] at h
  -- First conclusion: the exponent identity `d²/(d+1) = d - d/(d+1)`.
  have hgoal1 : |β| * (N:ℝ)^(((d:ℝ)^2)/((d:ℝ)+1)) * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) ≤ 1/100 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 100)]
    have hpow : (N:ℝ)^(((d:ℝ)^2)/((d:ℝ)+1)) =
        (N:ℝ)^((d:ℝ)) / (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) := by
      have hdr : ((d:ℝ)^2)/((d:ℝ)+1) = (d:ℝ) - (d:ℝ)/((d:ℝ)+1) := by
        field_simp
        ring
      rw [hdr, Real.rpow_sub hNpos]
    rw [hpow]
    calc |β| * ((N:ℝ)^((d:ℝ)) / (N:ℝ)^((d:ℝ)/((d:ℝ)+1))) * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) * 100
        = |β| * (N:ℝ)^((d:ℝ)) * 100 * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) /
            (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) := by ring
      _ ≤ 1 := hB
  -- Second conclusion: raise to the power `-1/d` and use monotonicity for `z ≤ 0`.
  have hz : (-(1:ℝ)/(d:ℝ)) ≤ 0 := by
    rw [neg_div]
    exact neg_nonpos.mpr (div_nonneg zero_le_one (le_of_lt hdpos))
  have hPpos : 0 < |β| * (N:ℝ)^(((d:ℝ)^2)/((d:ℝ)+1)) * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) :=
    mul_pos (mul_pos hβ (Real.rpow_pos_of_pos hNpos _)) (Real.rpow_pos_of_pos hqpos _)
  have hchain : ((1:ℝ)/100)^(-(1:ℝ)/(d:ℝ)) ≤
      (|β| * (N:ℝ)^(((d:ℝ)^2)/((d:ℝ)+1)) * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)))^(-(1:ℝ)/(d:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hPpos hgoal1 hz
  -- `(1/100)^{-1/d} = 100^{1/d}`.
  have hL : ((1:ℝ)/100)^(-(1:ℝ)/(d:ℝ)) = (100:ℝ)^(1/(d:ℝ)) := by
    have h100 : (1:ℝ)/100 = (100:ℝ)^(-1:ℝ) := by
      rw [Real.rpow_neg_one, one_div]
    rw [h100, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 100)]
    congr 1
    rw [show (-(1:ℝ)/(d:ℝ)) = -((1:ℝ)/(d:ℝ)) by rw [neg_div]]
    ring
  have hXz : ((d:ℝ)^2)/((d:ℝ)+1) * (-(1:ℝ)/(d:ℝ)) = -((d:ℝ)/((d:ℝ)+1)) := by
    rw [show (-(1:ℝ)/(d:ℝ)) = -((1:ℝ)/(d:ℝ)) by rw [neg_div]]
    field_simp
  have hrz : ((d:ℝ)/((d:ℝ)+1)) * (-(1:ℝ)/(d:ℝ)) = -(1/((d:ℝ)+1)) := by
    rw [show (-(1:ℝ)/(d:ℝ)) = -((1:ℝ)/(d:ℝ)) by rw [neg_div]]
    field_simp
  have hnaX : (0:ℝ) ≤ (N:ℝ)^(((d:ℝ)^2)/((d:ℝ)+1)) := Real.rpow_nonneg hNnn _
  have hnb : (0:ℝ) ≤ (q:ℝ)^((d:ℝ)/((d:ℝ)+1)) := Real.rpow_nonneg hqnn _
  -- `P^{-1/d} = |β|^{-1/d} N^{-d/(d+1)} q^{-1/(d+1)}`.
  have hR : (|β| * (N:ℝ)^(((d:ℝ)^2)/((d:ℝ)+1)) * (q:ℝ)^((d:ℝ)/((d:ℝ)+1)))^(-(1:ℝ)/(d:ℝ))
      = |β|^(-(1:ℝ)/(d:ℝ)) * (N:ℝ)^(-((d:ℝ)/((d:ℝ)+1))) *
          (q:ℝ)^(-(1/((d:ℝ)+1))) := by
    rw [Real.mul_rpow (mul_nonneg (abs_nonneg β) hnaX) hnb,
        Real.mul_rpow (abs_nonneg β) hnaX,
        ← Real.rpow_mul hNnn, ← Real.rpow_mul hqnn, hXz, hrz]
  have hfin : (100:ℝ)^(1/(d:ℝ)) * (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1))
      ≤ |β|^(-(1:ℝ)/(d:ℝ)) := by
    have hbb : 0 < (q:ℝ)^(1/((d:ℝ)+1)) := Real.rpow_pos_of_pos hqpos _
    have hmul : (100:ℝ)^(1/(d:ℝ)) *
          ((N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1)))
        ≤ (|β|^(-(1:ℝ)/(d:ℝ)) * (N:ℝ)^(-((d:ℝ)/((d:ℝ)+1))) *
            (q:ℝ)^(-(1/((d:ℝ)+1)))) *
          ((N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1))) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (mul_pos hNrpos hbb))
      rw [← hL, ← hR]
      exact hchain
    have hcollapse : (|β|^(-(1:ℝ)/(d:ℝ)) * (N:ℝ)^(-((d:ℝ)/((d:ℝ)+1))) *
            (q:ℝ)^(-(1/((d:ℝ)+1)))) *
          ((N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1))) = |β|^(-(1:ℝ)/(d:ℝ)) := by
      have haa : (N:ℝ)^(-((d:ℝ)/((d:ℝ)+1))) * (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) = 1 := by
        rw [← Real.rpow_add hNpos]
        simp
      have hcc : (q:ℝ)^(-(1/((d:ℝ)+1))) * (q:ℝ)^(1/((d:ℝ)+1)) = 1 := by
        rw [← Real.rpow_add hqpos]
        simp
      calc (|β|^(-(1:ℝ)/(d:ℝ)) * (N:ℝ)^(-((d:ℝ)/((d:ℝ)+1))) *
              (q:ℝ)^(-(1/((d:ℝ)+1)))) *
            ((N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1)))
          = |β|^(-(1:ℝ)/(d:ℝ)) * ((N:ℝ)^(-((d:ℝ)/((d:ℝ)+1))) * (N:ℝ)^((d:ℝ)/((d:ℝ)+1))) *
            ((q:ℝ)^(-(1/((d:ℝ)+1))) * (q:ℝ)^(1/((d:ℝ)+1))) := by ring
        _ = |β|^(-(1:ℝ)/(d:ℝ)) := by rw [haa, hcc]; ring
    have hthis := hmul
    rw [hcollapse] at hthis
    calc (100:ℝ)^(1/(d:ℝ)) * (N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1))
        = (100:ℝ)^(1/(d:ℝ)) * ((N:ℝ)^((d:ℝ)/((d:ℝ)+1)) * (q:ℝ)^(1/((d:ℝ)+1))) := by ring
      _ ≤ |β|^(-(1:ℝ)/(d:ℝ)) := hthis
  exact ⟨hgoal1, hfin⟩

end Work.A3
