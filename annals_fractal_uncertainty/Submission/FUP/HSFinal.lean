import Submission.FUP.HSTail
import Submission.FUP.Spec
import Submission.Commons.Analysis.Asymptotics.pow_one_sub_le_rpow_neg

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 12: Theorem 5.1 from the single-scale localisation statement

The final assembly: the one-step gain iterated over `m ≤ M - 1` (`M` maximal with
`L^{MT+1} ≤ N`), matched with the lower bound for `f` on `X`, then
`Commons.Analysis.Asymptotics.pow_one_sub_le_rpow_neg`.
-/

namespace Submission.FUP

/-- The norm form of the one-step gain. -/
theorem gain_step_norm {L T m : ℕ} (hL : 3 ≤ L)
    (hT : 1 ≤ T) (Φ : FupCutoff d) (hΦr : Φ.radius ≤ 1) {N : ℝ} (hN : 1 ≤ N) {X Y : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) (hY : Y ⊆ cube (-N) N) (hpor : BoxPorous L (m * T + 1) X)
    {c₂ c₃ α Cstar : ℝ} (hCstar : 0 < Cstar)
    (hLOC : ∀ (α₁ : ℝ), 1 ≤ α₁ → ∀ (γ : ℝᵈ) (Y' : Set ℝᵈ), Y' ⊆ cube (-α₁) α₁ →
        (∀ η : ℝᵈ, (∀ i : Fin d, η i ∈ Set.Icc (-(α₁ + 1)) (α₁ + 1)) →
          AdmitsL1Damping ((fun z : ℝᵈ => η + z) '' (addSet Y' (cube (-2) 2)))
            (4 * (L : ℝ))⁻¹ c₂ c₃ α) →
        ∀ (a : (Fin d → ℤ) → (Fin d → ℝ)),
          (∀ n : Fin d → ℤ, ∀ i : Fin d, 2 * (n i : ℝ) + γ i ≤ a n i ∧
            a n i + locSide L ≤ 2 * (n i : ℝ) + γ i + 2) →
          ∀ f' : Lp ℂ 2 (volume : Measure ℝᵈ),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
              ((𝓕 f' : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y') →
            ‖f'‖ ≤ Cstar * (eLpNorm ((⋃ n : Fin d → ℤ, box (a n) (fun i => a n i + locSide L)).indicator
                (f' : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal)
    (hdamp : ∀ η : ℝᵈ,
        (∀ i : Fin d, η i ∈ Set.Icc (-(N * (rescaleFactor L T m)⁻¹) - 3)
          (N * (rescaleFactor L T m)⁻¹ + 3)) →
        AdmitsL1Damping ((fun z : ℝᵈ => η + z) ''
          (addSet ((rescaleFactor L T m)⁻¹ • Y) (cube (-4) 4)))
          (4 * (L : ℝ))⁻¹ c₂ c₃ α)
    {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ))
    (hsuppY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) :
    (eLpNorm (indFun Φ L T X (m + 1) f) 2 (volume : Measure ℝᵈ)).toReal
      ≤ Real.sqrt (1 - (1 - (eUp Φ L T) ^ 2) / Cstar ^ 2)
        * (eLpNorm (indFun Φ L T X m f) 2 (volume : Measure ℝᵈ)).toReal := by
  have h1 := gain_step hL hT Φ hΦr hN hX hY hpor hCstar hLOC hdamp hf hsuppY
  rw [toReal_eLpNorm_two (memLp_indFun_two (by omega) Φ T (m+1) hX hf),
    toReal_eLpNorm_two (memLp_indFun_two (by omega) Φ T m hX hf)]
  refine sqrt_le_sqrt_mul_sqrt (c := 1 - (1 - (eUp Φ L T) ^ 2) / Cstar ^ 2)
    (by positivity) (by positivity) ?_
  exact h1



/-- **Han–Schlag's Theorem 5.1 from the single-scale localisation statement.** -/
theorem han_schlag_statement_of_localization (hLoc : LocalizationStatement (d := d)) :
    Spec.han_schlag_statement (d := d) := by
  classical
  obtain ⟨cstar, hcstar, hstar⟩ := hLoc
  refine ⟨cstar, hcstar, fun L hL3 c₂ c₃ α hc₂ hc₃ hα => ?_⟩
  obtain ⟨Φ, hΦr⟩ := exists_fupCutoff_radius_le_one d
  have hL1 : (1:ℕ) < L := by omega
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hc₁pos : (0:ℝ) < (2*(L:ℝ))⁻¹ := by positivity
  have hc₁le : (2*(L:ℝ))⁻¹ ≤ 1/2 := by
    rw [inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < 2*(L:ℝ))]
    have h : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
    linarith
  obtain ⟨Cstar, hCstar, hLOC0⟩ := hstar ((2*(L:ℝ))⁻¹) hc₁pos hc₁le c₂ hc₂ c₃ hc₃ α hα
  -- the localisation property in the form used below
  have hLOC : ∀ (α₁ : ℝ), 1 ≤ α₁ → ∀ (γ : ℝᵈ) (Y' : Set ℝᵈ), Y' ⊆ cube (-α₁) α₁ →
      (∀ η : ℝᵈ, (∀ i : Fin d, η i ∈ Set.Icc (-(α₁ + 1)) (α₁ + 1)) →
        AdmitsL1Damping ((fun z : ℝᵈ => η + z) '' (addSet Y' (cube (-2) 2)))
          (4 * (L : ℝ))⁻¹ c₂ c₃ α) →
      ∀ (a : (Fin d → ℤ) → (Fin d → ℝ)),
        (∀ n : Fin d → ℤ, ∀ i : Fin d, 2 * (n i : ℝ) + γ i ≤ a n i ∧
          a n i + locSide L ≤ 2 * (n i : ℝ) + γ i + 2) →
        ∀ f' : Lp ℂ 2 (volume : Measure ℝᵈ),
          (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
            ((𝓕 f' : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y') →
          ‖f'‖ ≤ Cstar * (eLpNorm ((⋃ n : Fin d → ℤ, box (a n) (fun i => a n i + locSide L)).indicator
              (f' : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal :=
    fun α₁ hα₁ γ Y' hY' hd => by
      rw [← two_mul_inv_div_two L] at hd
      simpa only [two_mul_half_locSide L] using hLOC0 α₁ hα₁ γ Y' hY' hd
  -- the constants of the induction
  let d₀ : ℝ := Real.sqrt (1 - 3/(4*Cstar^2))
  have hd₀nonneg : 0 ≤ d₀ := Real.sqrt_nonneg _
  have hd₀lt1 : d₀ < 1 := by
    rw [show d₀ = Real.sqrt (1 - 3/(4*Cstar^2)) from rfl, Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)]
    have hC2 : (0:ℝ) < Cstar^2 := by positivity
    have : (0:ℝ) < 3/(4*Cstar^2) := by positivity
    linarith
  let δ : ℝ := min ((1 - d₀)/(2 - (1 - d₀))) (1/2)
  have hδpos : 0 < δ := by
    rw [show δ = min ((1 - d₀)/(2 - (1 - d₀))) (1/2) from rfl]
    exact lt_min (div_pos (by linarith [hd₀lt1]) (by linarith [hd₀lt1, hd₀nonneg]))
      (by norm_num)
  have hδhalf : δ ≤ 1/2 := by
    rw [show δ = min ((1 - d₀)/(2 - (1 - d₀))) (1/2) from rfl]
    exact min_le_right _ _
  have hδle : δ ≤ (1 - d₀)/(2 - (1 - d₀)) := by
    rw [show δ = min ((1 - d₀)/(2 - (1 - d₀))) (1/2) from rfl]
    exact min_le_left _ _
  obtain ⟨T, hT1, hTs, hTe⟩ := exists_T_tails_le hL1 Φ (ε := δ) hδpos
  have he_le : eUp Φ L T ≤ 1/2 := le_trans hTe hδhalf
  have hs_le : tailMass Φ L T ≤ δ := hTs
  let cc : ℝ := 1 - (1 - (eUp Φ L T)^2)/Cstar^2
  let dstep : ℝ := Real.sqrt cc
  have hcc_le : cc ≤ 1 - 3/(4*Cstar^2) := by
    rw [show cc = 1 - (1 - (eUp Φ L T)^2)/Cstar^2 from rfl]
    have hC2 : (0:ℝ) < Cstar^2 := by positivity
    have he2 : (eUp Φ L T)^2 ≤ (1/2:ℝ)^2 := by nlinarith [eUp_nonneg Φ L T, he_le]
    have hle : (3:ℝ)/(4*Cstar^2) ≤ (1 - (eUp Φ L T)^2)/Cstar^2 := by
      have h1 : (3:ℝ)/4 ≤ 1 - (eUp Φ L T)^2 := by linarith [he2]
      rw [show (3:ℝ)/(4*Cstar^2) = ((3:ℝ)/4)/Cstar^2 from by ring]
      exact div_le_div_of_nonneg_right h1 hC2.le
    linarith
  have hd_le : dstep ≤ d₀ := by
    rw [show dstep = Real.sqrt cc from rfl, show d₀ = Real.sqrt (1 - 3/(4*Cstar^2)) from rfl]
    exact Real.sqrt_le_sqrt hcc_le
  have hd_lt1 : dstep < 1 := lt_of_le_of_lt hd_le hd₀lt1
  have hd_nonneg : 0 ≤ dstep := Real.sqrt_nonneg _
  let γ' : ℝ := 1 - dstep
  have hγ'pos : 0 < γ' := by rw [show γ' = 1 - dstep from rfl]; linarith
  have hγ'lt2 : γ' < 2 := by rw [show γ' = 1 - dstep from rfl]; linarith
  have hγ'ge : 1 - d₀ ≤ γ' := by rw [show γ' = 1 - dstep from rfl]; linarith
  have hs_small : tailMass Φ L T ≤ γ'/(2 - γ') := by
    refine le_trans hs_le (le_trans hδle ?_)
    rw [div_le_div_iff₀ (by linarith [hd₀nonneg]) (by linarith [hγ'lt2])]
    nlinarith [hγ'ge]
  have hs_lt1 : tailMass Φ L T < 1 := by linarith [hδhalf]
  have hkey : (1 - tailMass Φ L T)⁻¹ * dstep ≤ 1 - γ'/2 := by
    have h1s : 0 < 1 - tailMass Φ L T := by linarith
    rw [inv_mul_le_iff₀ h1s]
    have hd : dstep = 1 - γ' := by rw [show γ' = 1 - dstep from rfl]; ring
    rw [hd]
    have hs2 : tailMass Φ L T * (2 - γ') ≤ γ' := by
      have := (le_div_iff₀ (by linarith [hγ'lt2] : (0:ℝ) < 2 - γ')).mp hs_small
      linarith
    nlinarith [hs2]
  obtain ⟨β, C', hβpos, hC'pos, hC'spec⟩ :=
    Commons.Analysis.Asymptotics.pow_one_sub_le_rpow_neg hL1 (by omega : 0 < T)
      (by linarith : (0:ℝ) < γ'/2) (by linarith : γ'/2 < 1)
  have hC''pos : 0 < C'/(1 - γ'/2) := div_pos hC'pos (by linarith [hγ'lt2])
  refine ⟨β, C'/(1 - γ'/2), max 1 (L:ℝ), hβpos, hC''pos, ?_, ?_⟩
  · positivity
  intro N hN X Y hX hpor hY hdamp f hsupp
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNL : (L:ℝ) ≤ N := le_trans (le_max_right _ _) hN
  -- `M`: the maximal `m` with `L^{mT+1} ≤ N`
  have hex : ∃ m : ℕ, N < (L:ℝ)^(m*T+1) := by
    have hpow : Tendsto (fun m : ℕ => (L:ℝ)^(m+1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hL1 : (1:ℝ) < (L:ℝ))).comp
        (tendsto_add_atTop_nat 1)
    obtain ⟨m, hm⟩ := (hpow.eventually_gt_atTop N).exists
    refine ⟨m, lt_of_lt_of_le hm (pow_le_pow_right₀ (by exact_mod_cast hL1.le : (1:ℝ) ≤ (L:ℝ)) ?_)⟩
    have : 1 ≤ T := hT1
    nlinarith
  let M : ℕ := Nat.find hex
  have hM1 : N < (L:ℝ)^(M*T+1) := Nat.find_spec hex
  have hMmin : (L:ℝ)^((M-1)*T+1) ≤ N := by
    rcases Nat.eq_zero_or_pos M with h | h
    · exfalso
      rw [h] at hM1
      simp only [Nat.zero_mul, zero_add, pow_one] at hM1
      linarith
    · have hlt : M - 1 < Nat.find hex := by
        have : M = Nat.find hex := rfl
        omega
      have := Nat.find_min hex hlt
      simp only [not_lt] at this
      exact this
  have hMge1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · exfalso
      rw [h] at hM1
      simp only [Nat.zero_mul, zero_add, pow_one] at hM1
      linarith
    · exact h
  -- the porosity and the damping datum at every step `m' ≤ M-1`
  have hpor' : ∀ m' : ℕ, m' ≤ M - 1 → BoxPorous L (m'*T+1) X := by
    intro m' hm'
    refine hpor (m'*T) ?_
    have hmono : m'*T+1 ≤ (M-1)*T+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hm') 1
    calc (L:ℝ)^(m'*T+1) ≤ (L:ℝ)^((M-1)*T+1) :=
          pow_le_pow_right₀ (by exact_mod_cast hL1.le : (1:ℝ) ≤ (L:ℝ)) hmono
      _ ≤ N := hMmin
  have hdamp' : ∀ m' : ℕ, m' ≤ M - 1 → ∀ η : ℝᵈ,
      (∀ i : Fin d, η i ∈ Set.Icc (-(N * (rescaleFactor L T m')⁻¹) - 3)
        (N * (rescaleFactor L T m')⁻¹ + 3)) →
      AdmitsL1Damping ((fun z : ℝᵈ => η + z) ''
        (addSet ((rescaleFactor L T m')⁻¹ • Y) (cube (-4) 4)))
        (4 * (L : ℝ))⁻¹ c₂ c₃ α := by
    intro m' hm' η hη
    have hmono : m'*T+1 ≤ (M-1)*T+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hm') 1
    have hle : (L:ℝ)^(m'*T+1) ≤ N :=
      le_trans (pow_le_pow_right₀ (by exact_mod_cast hL1.le : (1:ℝ) ≤ (L:ℝ)) hmono) hMmin
    have hηb : ∀ i : Fin d, η i ∈ Set.Icc (-(N * (L:ℝ)^(-(((m'*T : ℕ)) : ℤ))) - 3)
        (N * (L:ℝ)^(-(((m'*T : ℕ)) : ℤ)) + 3) := by
      intro i
      have h := hη i
      have heq : (L:ℝ)^(-(((m'*T : ℕ)) : ℤ)) = (rescaleFactor L T m')⁻¹ := by
        rw [inv_rescaleFactor_eq (L := L) (T := T) (m := m') (by omega), ← Nat.cast_mul]
      rw [← heq] at h
      exact h
    have hη' : ∀ i : Fin d, η i ∈ Set.Icc (-N * (L:ℝ)^(-(((m'*T : ℕ)) : ℤ)) - 3)
        (N * (L:ℝ)^(-(((m'*T : ℕ)) : ℤ)) + 3) := by
      intro i
      have h2 := hηb i
      simp only [Set.mem_Icc] at h2 ⊢
      refine ⟨?_, h2.2⟩
      rw [neg_mul]
      exact h2.1
    have heq2 : (rescaleFactor L T m')⁻¹ = (L:ℝ)^(-(((m'*T : ℕ)) : ℤ)) := by
      rw [inv_rescaleFactor_eq (L := L) (T := T) (m := m') (by omega), ← Nat.cast_mul]
    have h := hdamp (m'*T) hle η hη'
    rw [← heq2] at h
    exact h
  -- the loop
  have hloop : ∀ m' : ℕ, m' ≤ M - 1 →
      (eLpNorm (indFun Φ L T X m' (f : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal
        ≤ dstep ^ m' * (eLpNorm ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2
            (volume : Measure ℝᵈ)).toReal := by
    intro m' hm'
    induction m' with
    | zero => simp [indFun_zero]
    | succ k ih =>
        have hk : k ≤ M - 1 := by omega
        have hstep := gain_step_norm hL3 hT1 Φ hΦr hN1 hX hY
          (hpor' k hk) hCstar hLOC (hdamp' k hk) (Lp.memLp f)
          (by simpa only [Lp.toLp_coeFn] using hsupp)
        rw [show Real.sqrt (1 - (1 - (eUp Φ L T)^2)/Cstar^2) = dstep from rfl] at hstep
        calc (eLpNorm (indFun Φ L T X (k+1) (f : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal
            ≤ dstep * (eLpNorm (indFun Φ L T X k (f : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal :=
              hstep
          _ ≤ dstep * (dstep ^ k * (eLpNorm ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2
                (volume : Measure ℝᵈ)).toReal) :=
              mul_le_mul_of_nonneg_left (ih hk) hd_nonneg
          _ = dstep ^ (k+1) * (eLpNorm ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2
                (volume : Measure ℝᵈ)).toReal := by ring
  have hfinal := hloop (M-1) (le_refl _)
  have hlow := eLpNorm_indicator_le_indFun (L := L) (T := T) (by omega) hT1 Φ hX hs_lt1 (M-1)
    (Lp.memLp f)
  -- assemble
  have hnorm : (eLpNorm ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2
      (volume : Measure ℝᵈ)).toReal = ‖f‖ := (Lp.norm_def f).symm
  have hMne : M ≠ 0 := by omega
  have hpow := hC'spec N (M-1) hN1 hMmin (by rw [Nat.sub_one_add_one hMne]; exact hM1)
  have hpow2 : (1 - γ'/2) ^ (M-1) ≤ (C'/(1-γ'/2)) * N ^ (-β) := by
    have h1 : (1 - γ'/2) ^ (M-1) = (1 - γ'/2)^(M-1+1) * (1 - γ'/2)⁻¹ := by
      rw [pow_succ]
      rw [mul_assoc, mul_inv_cancel₀ (by linarith : (1:ℝ) - γ'/2 ≠ 0), mul_one]
    rw [Nat.sub_one_add_one hMne] at hpow
    rw [h1, Nat.sub_one_add_one hMne]
    have h2 : (1 - γ'/2)^M * (1 - γ'/2)⁻¹ ≤ (C' * N^(-β)) * (1 - γ'/2)⁻¹ :=
      mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (by linarith : (0:ℝ) ≤ 1 - γ'/2))
    refine h2.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]
    ring
  calc (eLpNorm (X.indicator ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)) 2
        (volume : Measure ℝᵈ)).toReal
      ≤ ((1 - tailMass Φ L T) ^ (M-1))⁻¹
          * (eLpNorm (indFun Φ L T X (M-1) (f : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal := hlow
    _ ≤ ((1 - tailMass Φ L T) ^ (M-1))⁻¹
          * (dstep ^ (M-1) * (eLpNorm ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2
              (volume : Measure ℝᵈ)).toReal) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = (((1 - tailMass Φ L T)⁻¹) * dstep) ^ (M-1)
          * (eLpNorm ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2
              (volume : Measure ℝᵈ)).toReal := by
        rw [← inv_pow, ← mul_assoc, ← mul_pow]
    _ ≤ (1 - γ'/2) ^ (M-1)
          * (eLpNorm ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2
              (volume : Measure ℝᵈ)).toReal :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hkey (M-1)) (by positivity)
    _ ≤ (C'/(1 - γ'/2)) * N ^ (-β)
          * (eLpNorm ((f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) 2
              (volume : Measure ℝᵈ)).toReal :=
        mul_le_mul_of_nonneg_right hpow2 (by positivity)
    _ = C'/(1 - γ'/2) * N ^ (-β) * ‖f‖ := by rw [hnorm]

end Submission.FUP
