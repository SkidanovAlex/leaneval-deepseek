import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.solve_adi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-!
# The "sixth scale step" hypothesis for `annals_bounded_multiplicative_functions`

`Work.N8.scale_step6_hyp` chooses, for every large `X`, a bounded even integer `ℓ` and verifies
the numerical side conditions needed by the Step-6 assembly.
-/

/-- For `θ, ε > 0` the following five inequalities hold simultaneously for all sufficiently
large `X`: `3 ≤ X`, `3 ≤ X^θ`, `ε·log X ≤ X^(ε²/4)`, `max (max B 1) k! + 1 ≤ X^(ε²/2)` and
`1 ≤ (ε²/2)·log X`. -/
theorem scale_step6_aux_X0 (k : ℕ) (θ ε : ℝ) (B : ℝ) (hθ₀ : 0 < θ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 3 ≤ X ∧ 3 ≤ X ^ θ ∧ ε * Real.log X ≤ X ^ (ε ^ 2 / 4) ∧
      max (max B 1) ((k.factorial : ℝ)) + 1 ≤ X ^ (ε ^ 2 / 2) ∧
      1 ≤ (ε ^ 2 / 2) * Real.log X := by
  have hδ : 0 < ε ^ 2 / 2 := by positivity
  have hδ' : 0 < ε ^ 2 / 4 := by positivity
  have h3X : ∀ᶠ X : ℝ in Filter.atTop, 3 ≤ X := Filter.eventually_ge_atTop 3
  have h1 : ∀ᶠ X : ℝ in Filter.atTop, 3 ≤ X ^ θ :=
    (tendsto_rpow_atTop hθ₀).eventually (Filter.eventually_ge_atTop 3)
  have h3 : ∀ᶠ X : ℝ in Filter.atTop,
      max (max B 1) ((k.factorial : ℝ)) + 1 ≤ X ^ (ε ^ 2 / 2) :=
    (tendsto_rpow_atTop hδ).eventually (Filter.eventually_ge_atTop _)
  have h4 : ∀ᶠ X : ℝ in Filter.atTop, 1 ≤ (ε ^ 2 / 2) * Real.log X :=
    (Real.tendsto_log_atTop.const_mul_atTop hδ).eventually (Filter.eventually_ge_atTop 1)
  have h2 : ∀ᶠ X : ℝ in Filter.atTop, ε * Real.log X ≤ X ^ (ε ^ 2 / 4) := by
    have hb := ((isLittleO_log_rpow_atTop hδ').const_mul_left ε).bound
      (show (0 : ℝ) < 1 by norm_num)
    have hge1 : ∀ᶠ X : ℝ in Filter.atTop, (1 : ℝ) ≤ X := Filter.eventually_ge_atTop 1
    filter_upwards [hb, hge1] with X hb hX1
    have hXpos : 0 ≤ X := by linarith
    have hxpow : 0 ≤ X ^ (ε ^ 2 / 4) := Real.rpow_nonneg hXpos _
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hmul : 0 ≤ ε * Real.log X := mul_nonneg (le_of_lt hε) hlogX
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hmul, abs_of_nonneg hxpow] at hb
    simpa using hb
  have hall : ∀ᶠ X : ℝ in Filter.atTop,
      3 ≤ X ∧ 3 ≤ X ^ θ ∧ ε * Real.log X ≤ X ^ (ε ^ 2 / 4) ∧
        max (max B 1) ((k.factorial : ℝ)) + 1 ≤ X ^ (ε ^ 2 / 2) ∧
        1 ≤ (ε ^ 2 / 2) * Real.log X := by
    filter_upwards [h3X, h1, h2, h3, h4] with X h3X h1 h2 h3 h4
    exact ⟨h3X, h1, h2, h3, h4⟩
  exact Filter.eventually_atTop.mp hall

/-- There is an even `Lbig ≥ 2` with `(ε²/2)(Lbig - 1) ≥ 1 - θ` and
`(ε²/4)·Lbig ≥ (1-θ)(2+ε)`. -/
theorem scale_step6_aux_Lbig (θ ε : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε) :
    ∃ Lbig : ℕ, 2 ≤ Lbig ∧ (∃ m : ℕ, Lbig = 2 * m) ∧
      ε ^ 2 / 2 * ((Lbig : ℝ) - 1) ≥ 1 - θ ∧
      ε ^ 2 / 4 * (Lbig : ℝ) ≥ (1 - θ) * (2 + ε) := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have h1θ : 0 < 1 - θ := by linarith
  have h2ε : 0 < 2 + ε := by linarith
  set A : ℝ := max (2 * (1 - θ) / ε ^ 2 + 1) (max (4 * (1 - θ) * (2 + ε) / ε ^ 2) 2) with hA
  have hA1 : 2 * (1 - θ) / ε ^ 2 + 1 ≤ A := le_max_left _ _
  have hA2 : 4 * (1 - θ) * (2 + ε) / ε ^ 2 ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hA3 : (2 : ℝ) ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨n, hn⟩ := exists_nat_ge (A / 2)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℝ) ≤ A / 2 := by linarith
    linarith
  have hL2 : 2 ≤ 2 * n := by
    have : 1 ≤ n := Nat.one_le_cast.mp hn1
    omega
  have hAL : A ≤ ((2 * n : ℕ) : ℝ) := by
    have : A ≤ 2 * (n : ℝ) := by linarith
    simpa using this
  refine ⟨2 * n, hL2, ⟨n, rfl⟩, ?_, ?_⟩
  · have hle : 2 * (1 - θ) / ε ^ 2 + 1 ≤ ((2 * n : ℕ) : ℝ) := le_trans hA1 hAL
    have hsub : 2 * (1 - θ) / ε ^ 2 ≤ ((2 * n : ℕ) : ℝ) - 1 := by linarith
    have hkey : ε ^ 2 / 2 * (2 * (1 - θ) / ε ^ 2) = 1 - θ := by field_simp
    calc (1 - θ) = ε ^ 2 / 2 * (2 * (1 - θ) / ε ^ 2) := hkey.symm
      _ ≤ ε ^ 2 / 2 * (((2 * n : ℕ) : ℝ) - 1) := mul_le_mul_of_nonneg_left hsub (by positivity)
  · have hle : 4 * (1 - θ) * (2 + ε) / ε ^ 2 ≤ ((2 * n : ℕ) : ℝ) := le_trans hA2 hAL
    have hkey : ε ^ 2 / 4 * (4 * (1 - θ) * (2 + ε) / ε ^ 2) = (1 - θ) * (2 + ε) := by field_simp
    calc (1 - θ) * (2 + ε) = ε ^ 2 / 4 * (4 * (1 - θ) * (2 + ε) / ε ^ 2) := hkey.symm
      _ ≤ ε ^ 2 / 4 * ((2 * n : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hle (by positivity)

/-- Lower bound for `π₀(P₁) = P₁ / log P₁` in terms of the prime scale `P₁`. -/
theorem scale_step6_aux_pi0 (ε X P₁ : ℝ) (hε : 0 < ε) (hX : 1 < X)
    (hP1lo : X ^ (ε ^ 2 / 2) ≤ P₁) (hP1hi : P₁ ≤ X ^ ε)
    (hlog : ε * Real.log X ≤ X ^ (ε ^ 2 / 4)) :
    X ^ (ε ^ 2 / 4) ≤ Work.BMF.pi0 P₁ := by
  have hXpos : 0 < X := by linarith
  have hδ : 0 < ε ^ 2 / 2 := by positivity
  have hP1pos : 0 < P₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hP1lo
  have hP1gt1 : 1 < P₁ := lt_of_lt_of_le (Real.one_lt_rpow hX hδ) hP1lo
  have hlogP1pos : 0 < Real.log P₁ := Real.log_pos hP1gt1
  have hlogP1le : Real.log P₁ ≤ ε * Real.log X := by
    have h := Real.log_le_log hP1pos hP1hi
    rwa [Real.log_rpow hXpos ε] at h
  rw [Work.BMF.pi0, le_div_iff₀ hlogP1pos]
  have hnonneg : 0 ≤ X ^ (ε ^ 2 / 4) := Real.rpow_nonneg (le_of_lt hXpos) _
  calc X ^ (ε ^ 2 / 4) * Real.log P₁ ≤ X ^ (ε ^ 2 / 4) * (ε * Real.log X) :=
        mul_le_mul_of_nonneg_left hlogP1le hnonneg
    _ ≤ X ^ (ε ^ 2 / 4) * X ^ (ε ^ 2 / 4) := mul_le_mul_of_nonneg_left hlog hnonneg
    _ = X ^ (ε ^ 2 / 2) := by
          rw [← Real.rpow_add hXpos]
          congr 1; ring
    _ ≤ P₁ := hP1lo

theorem scale_step6_hyp (k : ℕ) (θ ε : ℝ) (B : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2)
    (hε : 0 < ε) (hεθ : ε ≤ θ / 100) :
    ∃ Lbig : ℕ, 2 ≤ Lbig ∧ ∃ X₀ : ℝ, ∀ X H P₁ P₂ : ℝ, X₀ ≤ X → X ^ θ ≤ H →
      H ≤ X ^ (1 - θ) → X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ →
      P₂ ≤ X ^ ε →
      ∃ ℓ : ℕ, 2 ≤ ℓ ∧ (∃ m : ℕ, ℓ = 2 * m) ∧ ℓ ≤ Lbig ∧
        (X / H) ^ (2 + ε) ≤ (Work.BMF.pi0 P₁) ^ ℓ ∧ (X / H) ≤ P₁ ^ (ℓ - 1) ∧
        max B 1 ≤ P₁ ∧ (k.factorial : ℝ) < P₁ ∧
        1 ≤ 4000 * (ℓ : ℝ) * (2 : ℝ) ^ ℓ * Real.log P₁ ∧ 3 ≤ X / H := by
  obtain ⟨Lbig, hLbig2, hLbig_even, hLbigC3, hLbigC4⟩ := scale_step6_aux_Lbig θ ε hθ₀ hθ₁ hε
  obtain ⟨X₀, hX₀⟩ := scale_step6_aux_X0 k θ ε B hθ₀ hε
  refine ⟨Lbig, hLbig2, X₀, ?_⟩
  intro X H P₁ P₂ hX hHθ hH1θ hP1lo hP1hi hP2lo hP2hi
  obtain ⟨hX3, hXθ, hlogX, hBk, hlogX2⟩ := hX₀ X hX
  have hXpos : 0 < X := by linarith
  have hXnonneg : 0 ≤ X := le_of_lt hXpos
  have hX1 : 1 ≤ X := by linarith
  have hLbig1 : 1 ≤ Lbig := by omega
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos θ) hHθ
  have hXHθ : X ^ θ ≤ X / H := by
    have h1 : X / X ^ (1 - θ) ≤ X / H :=
      div_le_div_of_nonneg_left hXnonneg hHpos hH1θ
    have heq : X / X ^ (1 - θ) = X ^ θ := by
      have h := Real.rpow_sub hXpos (1 : ℝ) (1 - θ)
      rw [Real.rpow_one] at h
      rw [← h]; congr 1; ring
    rw [← heq]; exact h1
  have hXH3 : 3 ≤ X / H := le_trans hXθ hXHθ
  have hXH1θ : X / H ≤ X ^ (1 - θ) := by
    have h1 : X / H ≤ X / X ^ θ :=
      div_le_div_of_nonneg_left hXnonneg (Real.rpow_pos_of_pos hXpos θ) hHθ
    have heq : X / X ^ θ = X ^ (1 - θ) := by
      have h := Real.rpow_sub hXpos (1 : ℝ) θ
      rw [Real.rpow_one] at h
      exact h.symm
    rwa [heq] at h1
  have hpow_eq : (X ^ (ε ^ 2 / 2)) ^ (Lbig - 1) = X ^ (ε ^ 2 / 2 * ((Lbig : ℝ) - 1)) := by
    rw [← Real.rpow_natCast (X ^ (ε ^ 2 / 2)) (Lbig - 1), ← Real.rpow_mul hXnonneg]
    congr 1
    rw [Nat.cast_sub hLbig1, Nat.cast_one]
  have hstep1 : X ^ (1 - θ) ≤ (X ^ (ε ^ 2 / 2)) ^ (Lbig - 1) := by
    rw [hpow_eq]
    exact Real.rpow_le_rpow_of_exponent_le hX1 hLbigC3
  have hstep2 : (X ^ (ε ^ 2 / 2)) ^ (Lbig - 1) ≤ P₁ ^ (Lbig - 1) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hXnonneg _) hP1lo (Lbig - 1)
  have hXH_le_P1 : X / H ≤ P₁ ^ (Lbig - 1) := le_trans (le_trans hXH1θ hstep1) hstep2
  have hpi0 : X ^ (ε ^ 2 / 4) ≤ Work.BMF.pi0 P₁ :=
    scale_step6_aux_pi0 ε X P₁ hε (by linarith) hP1lo hP1hi hlogX
  have hXHpos : 0 < X / H := div_pos hXpos hHpos
  have hXH_pi0 : (X / H) ^ (2 + ε) ≤ (Work.BMF.pi0 P₁) ^ Lbig := by
    calc (X / H) ^ (2 + ε) ≤ (X ^ (1 - θ)) ^ (2 + ε) :=
          Real.rpow_le_rpow (le_of_lt hXHpos) hXH1θ (by linarith)
      _ = X ^ ((1 - θ) * (2 + ε)) := (Real.rpow_mul hXnonneg (1 - θ) (2 + ε)).symm
      _ ≤ X ^ (ε ^ 2 / 4 * (Lbig : ℝ)) := Real.rpow_le_rpow_of_exponent_le hX1 hLbigC4
      _ = (X ^ (ε ^ 2 / 4)) ^ Lbig := by
            rw [Real.rpow_mul hXnonneg, Real.rpow_natCast]
      _ ≤ (Work.BMF.pi0 P₁) ^ Lbig :=
            pow_le_pow_left₀ (Real.rpow_nonneg hXnonneg _) hpi0 Lbig
  have hmax_lt : max (max B 1) ((k.factorial : ℝ)) < P₁ :=
    lt_of_lt_of_le (lt_add_one _) (le_trans hBk hP1lo)
  have hmaxB : max B 1 ≤ P₁ := le_trans (le_max_left _ _) (le_of_lt hmax_lt)
  have hkfact : (k.factorial : ℝ) < P₁ := lt_of_le_of_lt (le_max_right _ _) hmax_lt
  have hlogP1 : 1 ≤ Real.log P₁ := by
    have h1 : Real.log (X ^ (ε ^ 2 / 2)) ≤ Real.log P₁ :=
      Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hP1lo
    rw [Real.log_rpow hXpos] at h1
    linarith
  have hfac : 1 ≤ 4000 * (Lbig : ℝ) * (2 : ℝ) ^ Lbig := by
    have h2L : (2 : ℝ) ≤ (Lbig : ℝ) := by exact_mod_cast hLbig2
    have h2p : (4 : ℝ) ≤ (2 : ℝ) ^ Lbig := by
      have h : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ Lbig :=
        pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hLbig2
      norm_num at h
      exact h
    have h1 : (2 : ℝ) * 4 ≤ (Lbig : ℝ) * (2 : ℝ) ^ Lbig := by
      calc (2 : ℝ) * 4 ≤ (Lbig : ℝ) * 4 := by linarith
        _ ≤ (Lbig : ℝ) * (2 : ℝ) ^ Lbig :=
              mul_le_mul_of_nonneg_left h2p (by linarith)
    have hkey : (4000 : ℝ) * 2 * 4 ≤ 4000 * (Lbig : ℝ) * (2 : ℝ) ^ Lbig := by
      calc (4000 : ℝ) * 2 * 4 = 4000 * (2 * 4) := by ring
        _ ≤ 4000 * ((Lbig : ℝ) * (2 : ℝ) ^ Lbig) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 4000 * (Lbig : ℝ) * (2 : ℝ) ^ Lbig := by ring
    linarith
  have hlogfac : 1 ≤ 4000 * (Lbig : ℝ) * (2 : ℝ) ^ Lbig * Real.log P₁ := by
    have ha : (0 : ℝ) ≤ 4000 * (Lbig : ℝ) * (2 : ℝ) ^ Lbig := by positivity
    simpa using mul_le_mul hfac hlogP1 (show (0 : ℝ) ≤ 1 by norm_num) ha
  exact ⟨Lbig, hLbig2, hLbig_even, le_rfl, hXH_pi0, hXH_le_P1, hmaxB, hkfact, hlogfac, hXH3⟩

end Work.N8
