import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.cost_arith_aux
import Submission.Work.BoseC3QAll.sum_W1alpha_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.wta_bound_aux` — the θ-word (`σ₂`) estimate

The `θ`-word `Wta = Σ_{s ∈ suppL}c_s•(ã_{-s}†+ã_{-s})` of `R1` (the `σ₂`-word
`κC`, FS's `T₁` — the term FS treat as tiny and which is *not*, see the `D7`
correction of the design note) is bounded below by the **energy gap**:

`-(costTa)‖Φ‖² - (b/800)ℓ⁻²⟨n₊⟩ ≤ ⟨Φ, Wta Φ⟩`.

## The argument

* **The coefficients.**  `c_s = -(z/ℓ³)Σ_{k∈P_H}f_L(s)W₁(k)q3Denom(s,k)α_kα_{s-k}κC_{sk}`
  with `κC = (α_k-α_{s-k})(χ̂²(s)-χ̂(k)χ̂(s-k))`.  On `P_H^q` one has
  `1-α² ≥ 1/2` (so `q3Denom ≤ 4`) and `|α| ≤ 64K₀𝓁`; `κC` is bounded by
  `alpha_lip` (`|α_{s-k}-α_{-k}| ≤ K₀𝓁K_Ha‖k_s‖ ≤ K₀𝓁K_HK_L√t`) times
  `1+K₀²η² ≤ 1+K₀²`; and `Σ_k|W₁(k)α_k| ≤ 2ρ_zK₀aℓ³`
  (`sum_abs_W1_alpha_le`).  Hence `|c_s| ≤ Mc·f_L(s)` (no count of `P_H` is
  needed: the multiplicity is compensated by the `ℓ²`-weight in `sum_W1sq`).
* **The weighted AM–GM.**  `|⟨Φ,Wta Φ⟩| ≤ 2Σ_s|c_s|√A_s√N` with
  `A_s = ⟨ã_{-s}Φ,ã_{-s}Φ⟩`, `N = ‖Φ‖²`; the AM–GM with the weights `(b/800)ℓ⁻²`
  and `(800/b)ℓ²` gives `2|c_s|√A_s√N ≤ (b/800)ℓ⁻²A_s + (800/b)ℓ²c_s²N`;
  summing, `Σ_sA_s ≤ ⟨n₊⟩` (`Work.BoseB7A.TildeData.ta_le_N`) and
  `Σ_sc_s² ≤ Mc²#suppL ≤ Mc²K₀(K_ℓK_L)³` (`count_PL`), so the second sum is
  `costTa·N` — with `costTa = (800/b)ℓ²K₀(K_ℓK_L)³Mc²` (the *box* side `ℓ`).
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedVariables false

set_option maxHeartbeats 1000000

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7
open Work.BoseBox

universe u v

/-! ## 1. Two elementary AM–GM lemmas -/

/-- `2√A√B ≤ A + B` for `A,B ≥ 0`. -/
theorem two_sqrt_mul_sqrt_le' {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    2 * Real.sqrt A * Real.sqrt B ≤ A + B := by
  nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B), Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- The weighted AM–GM: `2c√A√B ≤ A + c²B` for `A,B,c ≥ 0`. -/
theorem amgm_simple {A B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c) :
    2 * c * (Real.sqrt A * Real.sqrt B) ≤ A + c ^ 2 * B := by
  have h1 : 2 * Real.sqrt A * Real.sqrt (c ^ 2 * B) ≤ A + c ^ 2 * B :=
    two_sqrt_mul_sqrt_le' hA (by positivity)
  have h2 : Real.sqrt (c ^ 2 * B) = c * Real.sqrt B := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ c ^ 2), Real.sqrt_sq hc]
  rw [h2] at h1
  linarith [h1]

/-! ## 2. `K₀ ≥ 0` from `Q3KernelFSAll` -/

theorem K0_nonneg_of_kernel' {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (K₀ : ℝ) (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F)
    (E : Q3Env.{u} Mode) (hv : FSParamsView E) (hK : Q3KernelFSAll K₀ F T E) : 0 ≤ K₀ := by
  by_contra hneg
  have hneg' : K₀ < 0 := not_le.mp hneg
  have hcp := hK.count_PL
  have hcard : (0 : ℝ) ≤ (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hKl : 0 < E.Kl := lt_of_lt_of_le zero_lt_one hv.one_le_Kl
  have hKL : 0 < E.KL := lt_of_lt_of_le zero_lt_one hv.one_le_KL
  have hpos : 0 < (E.Kl * E.KL) ^ 3 := pow_pos (mul_pos hKl hKL) 3
  have hneg2 : K₀ * (E.Kl * E.KL) ^ 3 < 0 := mul_neg_of_neg_of_pos hneg' hpos
  linarith

/-! ## 3. The pointwise bound on the `θ`-word coefficients -/

/-- `|cTa F T E s| ≤ Mc·f_L(s)`. -/
theorem cTa_pointwise (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
        ∀ s : Mode, |cTa F T E s| ≤ Mc K₀ E hv * E.fL s := by
  obtain ⟨t₁, ht₁, H₁⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, H₂⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK s
  have h1 := H₁ F T E hv (le_trans hle (min_le_left _ _)) hb hK
  have h2 := H₂ F T E hv (le_trans hle (min_le_right _ _)) hb hK
  obtain ⟨hαeven, _hAB, hhalf, hα, _hD⟩ := h1
  obtain ⟨hPHsub, hsub, -⟩ := h2
  have hK0 : 0 ≤ K₀ := K0_nonneg_of_kernel' K₀ F T E hv hK
  have h𝓁0 : 0 ≤ E.lille := lille_nn E hv
  have hr0 : 0 ≤ E.rho := (rho_pos E hv).le
  have ha0 : 0 ≤ E.aScat := hv.a_pos.le
  have hℓ0 : 0 < E.ell := ell_pos E hv
  have hη0 : 0 ≤ eta E := eta_nn E hv
  have hKH0 : 0 ≤ E.KH := (Work.BoseC3QAll.KH_pos E hv).le
  have hKL0 : 0 ≤ E.KL := KL_nonneg E hv
  have hμ0 : 0 ≤ E.mu := (mu_pos E hv).le
  have hfLs0 : 0 ≤ E.fL s := hK.fL_nonneg s
  -- each summand of `cTa`
  have hpt : ∀ k ∈ F.PHset E,
      |gA E s k * bA E s k * (-(kC E s k))|
        ≤ E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
            * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
          * (|E.W1 k| * |E.alpha k|) := by
    intro k hk
    by_cases hfLs : E.fL s = 0
    · rw [show |gA E s k * bA E s k * (-(kC E s k))| = 0 by rw [gA, hfLs]; simp, hfLs]
      simp
    by_cases hW : E.W1 k = 0
    · -- both sides carry the factor `Ŵ₁ k`
      rw [show |gA E s k * bA E s k * (-(kC E s k))| = 0 by rw [gA, hW]; simp, hW]
      simp
    · have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
      have hqk : F.PHq E.KH E.aScat k := hPHsub k hkPH
      have hqk' : F.PHq E.KH E.aScat (-k) := by
        simp only [FockData.PHq, F.kmom_neg, norm_neg]
        exact hqk
      have hqsk : F.PHq E.KH E.aScat (s - k) := hsub s k hfLs hk hW
      -- `q3Denom ≤ 4`
      have hprod : (1 / 4 : ℝ) ≤ (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) := by
        have h3 : (1 / 2 : ℝ) ≤ 1 - E.alpha k ^ 2 := hhalf k hqk
        have h4 : (1 / 2 : ℝ) ≤ 1 - E.alpha (s - k) ^ 2 := hhalf (s - k) hqsk
        have h3' : (0 : ℝ) ≤ 1 - E.alpha k ^ 2 := by linarith
        have h34 : (1 / 2) * (1 / 2) ≤ (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) :=
          mul_le_mul h3 h4 (by norm_num) h3'
        linarith [h34]
      have hprodpos : 0 < (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) := by linarith [hprod]
      have hq3 : |E.q3Denom s k| ≤ 4 := by
        have hgoal : 1 / ((1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2)) ≤ 4 := by
          rw [div_le_iff₀ hprodpos]
          nlinarith [hprod]
        calc |E.q3Denom s k| = 1 / ((1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2)) := by
              rw [Q3Env.q3Denom, abs_of_pos (one_div_pos.mpr hprodpos)]
          _ ≤ 4 := hgoal
      -- `|kC|`
      have hkmom : F.kmom (s - k) - F.kmom (-k) = F.kmom s := by
        rw [hK.kmom_subW s k hfLs hk hW, F.kmom_neg, sub_neg_eq_add, sub_add_cancel]
      have hkC1 : |E.alpha k - E.alpha (s - k)|
          ≤ 2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat))) := by
        have hlip := hK.alpha_lip (s - k) (-k) hqsk hqk'
        have hstep : |E.alpha (s - k) - E.alpha (-k)| ≤ K₀ * E.lille * (E.KH * E.aScat)
            * ‖F.kmom s‖ := by
          rw [← hkmom]
          exact hlip
        have hPL : ‖F.kmom s‖ ≤ 2 * (E.KL * Real.sqrt (E.mu * E.aScat)) :=
          hK.fL_supp2 s hfLs
        have hval : |E.alpha k - E.alpha (s - k)| = |E.alpha (s - k) - E.alpha (-k)| := by
          rw [abs_sub_comm, hαeven k]
        rw [hval]
        refine le_trans hstep ?_
        have h3 : 0 ≤ K₀ * E.lille * (E.KH * E.aScat) := by positivity
        calc K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom s‖
            ≤ K₀ * E.lille * (E.KH * E.aScat)
                * (2 * (E.KL * Real.sqrt (E.mu * E.aScat))) :=
              mul_le_mul_of_nonneg_left hPL h3
          _ = 2 * (K₀ * E.lille * (E.KH * E.aScat)
                * (E.KL * Real.sqrt (E.mu * E.aScat))) := by ring
      have hkC2 : |E.hatChiSq s - E.hatChi k * E.hatChi (s - k)| ≤ 1 + K₀ ^ 2 := by
        have h5 : |E.hatChiSq s| ≤ 1 := hK.hatChiSq_le s
        have h6 : |E.hatChi k| ≤ K₀ * eta E := hK.hatChi_small k hqk
        have h7 : |E.hatChi (s - k)| ≤ K₀ * eta E := hK.hatChi_small (s - k) hqsk
        have h8 : |E.hatChi k * E.hatChi (s - k)| ≤ (K₀ * eta E) * (K₀ * eta E) := by
          rw [abs_mul]
          exact mul_le_mul h6 h7 (abs_nonneg _) (by positivity)
        have h9 : (K₀ * eta E) * (K₀ * eta E) ≤ K₀ ^ 2 := by
          have hη1 : eta E ≤ 1 := by
            rw [errA_eta E hv]
            exact fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
          have hη2 : eta E * eta E ≤ 1 := by nlinarith [hη0, hη1]
          have hK2 : 0 ≤ K₀ * K₀ := mul_nonneg hK0 hK0
          nlinarith [hη2, hK2, hK0, hη0]
        have h10 : |E.hatChiSq s - E.hatChi k * E.hatChi (s - k)|
            ≤ |E.hatChiSq s| + |E.hatChi k * E.hatChi (s - k)| :=
          abs_sub (E.hatChiSq s) (E.hatChi k * E.hatChi (s - k))
        nlinarith [h5, h8, h9, h10]
      have hkC : |kC E s k| ≤ 2 * (K₀ * E.lille * (E.KH * E.aScat)
          * (E.KL * Real.sqrt (E.mu * E.aScat))) * (1 + K₀ ^ 2) := by
        rw [kC, abs_mul]
        have h5 : 0 ≤ 2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat))) := by
          positivity
        exact mul_le_mul hkC1 hkC2 (abs_nonneg _) h5
      have hαsk : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hα (s - k) hqsk
      have hsign : |bA E s k| = |E.alpha k| * |E.alpha (s - k)| := by rw [bA, abs_mul]
      have hgA : |gA E s k| = E.fL s * |E.W1 k| * |E.q3Denom s k| := by
        rw [gA, abs_mul, abs_mul, abs_of_nonneg hfLs0]
      have hkey : |gA E s k * bA E s k * (-(kC E s k))|
          = E.fL s * |E.W1 k| * |E.q3Denom s k| * |bA E s k| * |kC E s k| := by
        simp only [abs_mul, abs_neg, hgA]
        try ring
      rw [hkey]
      have hAK : |E.alpha (s - k)| * |kC E s k|
          ≤ (64 * K₀ * E.lille)
            * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))
              * (1 + K₀ ^ 2)) :=
        mul_le_mul hαsk hkC (abs_nonneg _) (by positivity)
      have h6 : |E.q3Denom s k| * (|E.alpha (s - k)| * |kC E s k|)
          ≤ 4 * ((64 * K₀ * E.lille)
            * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))
              * (1 + K₀ ^ 2))) :=
        mul_le_mul hq3 hAK (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (by norm_num : (0 : ℝ) ≤ 4)
      calc E.fL s * |E.W1 k| * |E.q3Denom s k| * |bA E s k| * |kC E s k|
          = E.fL s * |E.W1 k| * |E.alpha k|
              * (|E.q3Denom s k| * (|E.alpha (s - k)| * |kC E s k|)) := by
            rw [hsign]; ring
        _ ≤ E.fL s * |E.W1 k| * |E.alpha k|
              * (4 * ((64 * K₀ * E.lille)
                * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))
                  * (1 + K₀ ^ 2)))) := by
            refine mul_le_mul_of_nonneg_left h6 ?_
            exact mul_nonneg (mul_nonneg hfLs0 (abs_nonneg _)) (abs_nonneg _)
        _ = E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
              * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
            * (|E.W1 k| * |E.alpha k|) := by ring
  -- sum over `k`
  have hsum := sum_abs_W1_alpha_le K₀ F T E hK hv
  have hsum2 : ∑ k ∈ F.PHset E, (|E.W1 k| * |E.alpha k|)
      ≤ 2 * E.rho * K₀ * E.aScat * E.ell ^ 3 := by
    simpa only [abs_mul] using hsum
  have hbig : |∑ k ∈ F.PHset E, (gA E s k * bA E s k * (-(kC E s k)))|
      ≤ E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
          * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
        * ∑ k ∈ F.PHset E, (|E.W1 k| * |E.alpha k|) := by
    calc |∑ k ∈ F.PHset E, (gA E s k * bA E s k * (-(kC E s k)))|
        ≤ ∑ k ∈ F.PHset E, |gA E s k * bA E s k * (-(kC E s k))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ F.PHset E, E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
            * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
            * (|E.W1 k| * |E.alpha k|) := Finset.sum_le_sum hpt
      _ = E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
            * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
          * ∑ k ∈ F.PHset E, (|E.W1 k| * |E.alpha k|) := by
          rw [Finset.mul_sum]
  -- `a√(μa) = √t`
  have hsqrt : E.aScat * Real.sqrt (E.mu * E.aScat) = Real.sqrt hv.t := by
    have h2 : (E.aScat * Real.sqrt (E.mu * E.aScat)) ^ 2 = hv.t := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hμ0 ha0)]
      rw [show E.aScat ^ 2 * (E.mu * E.aScat) = E.mu * E.aScat ^ 3 by ring, hv.mu_eq]
    have h3 : (Real.sqrt hv.t) ^ 2 = hv.t := Real.sq_sqrt hv.t_pos.le
    have h4 : (E.aScat * Real.sqrt (E.mu * E.aScat)) ^ 2 = (Real.sqrt hv.t) ^ 2 := by
      rw [h2, h3]
    have h5 : 0 ≤ E.aScat * Real.sqrt (E.mu * E.aScat) :=
      mul_nonneg ha0 (Real.sqrt_nonneg _)
    calc E.aScat * Real.sqrt (E.mu * E.aScat)
        = Real.sqrt ((E.aScat * Real.sqrt (E.mu * E.aScat)) ^ 2) := (Real.sqrt_sq h5).symm
      _ = Real.sqrt ((Real.sqrt hv.t) ^ 2) := by rw [h4]
      _ = Real.sqrt hv.t := Real.sqrt_sq (Real.sqrt_nonneg _)
  -- assemble
  rw [cTa, abs_mul, abs_div, abs_of_pos (pow_pos hℓ0 3)]
  have hz3 : 0 ≤ |E.z| / E.ell ^ 3 := div_nonneg (abs_nonneg _) (by positivity)
  have hmain : |E.z| / E.ell ^ 3 * |∑ k ∈ F.PHset E, (gA E s k * bA E s k * (-(kC E s k)))|
      ≤ Mc K₀ E hv * E.fL s := by
    have hstep1 : |E.z| / E.ell ^ 3 * |∑ k ∈ F.PHset E, (gA E s k * bA E s k * (-(kC E s k)))|
        ≤ |E.z| / E.ell ^ 3 * (E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
            * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
            * (2 * E.rho * K₀ * E.aScat * E.ell ^ 3)) := by
      have hnn : 0 ≤ |E.z| / E.ell ^ 3 * E.fL s * (4 * (64 * K₀ * E.lille)
          * (1 + K₀ ^ 2) * (2 * (K₀ * E.lille * (E.KH * E.aScat)
            * (E.KL * Real.sqrt (E.mu * E.aScat))))) := by positivity
      have h2' := mul_le_mul_of_nonneg_left hsum2 hnn
      calc |E.z| / E.ell ^ 3 * |∑ k ∈ F.PHset E, (gA E s k * bA E s k * (-(kC E s k)))|
          ≤ |E.z| / E.ell ^ 3 * (E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
              * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
              * ∑ k ∈ F.PHset E, (|E.W1 k| * |E.alpha k|)) :=
            mul_le_mul_of_nonneg_left hbig hz3
        _ = (|E.z| / E.ell ^ 3 * E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
              * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat))))))
              * ∑ k ∈ F.PHset E, (|E.W1 k| * |E.alpha k|) := by ring
        _ ≤ (|E.z| / E.ell ^ 3 * E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
              * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat))))))
              * (2 * E.rho * K₀ * E.aScat * E.ell ^ 3) := h2'
        _ = |E.z| / E.ell ^ 3 * (E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
              * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
              * (2 * E.rho * K₀ * E.aScat * E.ell ^ 3)) := by ring
    have hstep2 : |E.z| / E.ell ^ 3 * (E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
          * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
          * (2 * E.rho * K₀ * E.aScat * E.ell ^ 3))
        ≤ Mc K₀ E hv * E.fL s := by
      have hkey : |E.z| / E.ell ^ 3 * (E.fL s * (4 * (64 * K₀ * E.lille) * (1 + K₀ ^ 2)
            * (2 * (K₀ * E.lille * (E.KH * E.aScat) * (E.KL * Real.sqrt (E.mu * E.aScat)))))
            * (2 * E.rho * K₀ * E.aScat * E.ell ^ 3))
          = E.fL s * (1024 * (1 + K₀ ^ 2) * |E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL
              * Real.sqrt hv.t * E.rho * E.aScat) := by
        rw [← hsqrt]
        field_simp
        ring
      rw [hkey]
      rw [Mc]
      have hY : 0 ≤ (1 + K₀ ^ 2) * (|E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL
          * Real.sqrt hv.t * E.rho * E.aScat) := by
        have h7 : 0 ≤ 1 + K₀ ^ 2 := by positivity
        have h8 : 0 ≤ |E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL * Real.sqrt hv.t
            * E.rho * E.aScat := by positivity
        exact mul_nonneg h7 h8
      have h1024 : 0 ≤ 1024 * ((1 + K₀ ^ 2) * (|E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL
            * Real.sqrt hv.t * E.rho * E.aScat)) := by positivity
      calc E.fL s * (1024 * (1 + K₀ ^ 2) * |E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL
            * Real.sqrt hv.t * E.rho * E.aScat)
          = E.fL s * (1024 * ((1 + K₀ ^ 2) * (|E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL
              * Real.sqrt hv.t * E.rho * E.aScat))) := by ring
        _ ≤ ((1 + K₀ ^ 2) * (1024 * |E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL
              * Real.sqrt hv.t * E.rho * E.aScat)) * E.fL s := le_of_eq (by ring)
    exact le_trans hstep1 hstep2
  simpa only [mul_comm] using hmain


/-! ## 4. The weighted AM–GM and the θ-word bound -/

/-- The weighted AM–GM: `2c√A√B ≤ αA + βc²B` for `A,B,c ≥ 0`, `α,β > 0`, `αβ = 1`. -/
theorem amgm_weighted {A B c α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β = 1) :
    2 * c * (Real.sqrt A * Real.sqrt B) ≤ α * A + β * c ^ 2 * B := by
  have h1 : 2 * Real.sqrt (α * A) * Real.sqrt (β * c ^ 2 * B) ≤ α * A + β * c ^ 2 * B :=
    two_sqrt_mul_sqrt_le' (by positivity) (by positivity)
  have h2 : Real.sqrt (α * A) * Real.sqrt (β * c ^ 2 * B) = c * (Real.sqrt A * Real.sqrt B) := by
    rw [Real.sqrt_mul hα.le, Real.sqrt_mul (by positivity : 0 ≤ β * c ^ 2),
      Real.sqrt_mul hβ.le, Real.sqrt_sq hc]
    have hs : Real.sqrt α * Real.sqrt β = 1 := by
      rw [← Real.sqrt_mul hα.le, hαβ, Real.sqrt_one]
    calc Real.sqrt α * Real.sqrt A * (Real.sqrt β * c * Real.sqrt B)
        = (Real.sqrt α * Real.sqrt β) * c * (Real.sqrt A * Real.sqrt B) := by ring
      _ = c * (Real.sqrt A * Real.sqrt B) := by rw [hs]; ring
  have h1' : 2 * (Real.sqrt (α * A) * Real.sqrt (β * c ^ 2 * B)) ≤ α * A + β * c ^ 2 * B := by
    rw [show 2 * (Real.sqrt (α * A) * Real.sqrt (β * c ^ 2 * B))
        = 2 * Real.sqrt (α * A) * Real.sqrt (β * c ^ 2 * B) by ring]
    exact h1
  rw [h2] at h1'
  calc 2 * c * (Real.sqrt A * Real.sqrt B)
      = 2 * (c * (Real.sqrt A * Real.sqrt B)) := by ring
    _ ≤ α * A + β * c ^ 2 * B := h1'


end Est1

end Work.BoseC3QAll
