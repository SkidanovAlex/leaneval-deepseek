import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Est1.wta_bound_aux
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
/-- The `θ`-word (`σ₂`) is bounded below by the energy gap. -/
theorem Wta_bound_aux (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : Work.BoseB7A.TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          - (costTa K₀ E hv) * F.normSq Φ
              - (E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ
            ≤ F.qw Φ (Wta F T E) := by
  obtain ⟨t₁, ht₁, H₁⟩ := cTa_pointwise K₀ b₀ hb₀
  refine ⟨t₁, ht₁, ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK Φ hΦ
  have hc := H₁ F T E hv hle hb hK
  have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
  have hℓpos : 0 < E.ell := ell_pos E hv
  have hK0 : 0 ≤ K₀ := K0_nonneg_of_kernel' K₀ F T E hv hK
  have h𝓁0 : 0 ≤ E.lille := lille_nn E hv
  have hMc0 : 0 ≤ Mc K₀ E hv := by
    rw [Mc]
    have h1 : 0 ≤ 1024 * |E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL * Real.sqrt hv.t
        * E.rho * E.aScat := by
      have h2 : 0 ≤ Real.sqrt hv.t := Real.sqrt_nonneg _
      have h3 : 0 ≤ E.rho := (rho_pos E hv).le
      have h4 : 0 ≤ E.KH := (Work.BoseC3QAll.KH_pos E hv).le
      have h5 : 0 ≤ E.KL := KL_nonneg E hv
      have h6 : 0 ≤ E.lille := lille_nn E hv
      have h7 : 0 ≤ E.aScat := hv.a_pos.le
      have h8 : 0 ≤ K₀ ^ 3 := pow_nonneg hK0 3
      have h9 : 0 ≤ E.lille ^ 2 := pow_nonneg h6 2
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) h8) h9) h4) h5) h2) h3) h7
    exact mul_nonneg (by positivity) h1
  -- the weights
  have hαpos : 0 < (E.b / 800) * E.ell ^ (-(2 : ℝ)) := by positivity
  have hβpos : 0 < (800 / E.b) * E.ell ^ 2 := by positivity
  have hαβ : ((E.b / 800) * E.ell ^ (-(2 : ℝ))) * ((800 / E.b) * E.ell ^ 2) = 1 := by
    have h1 : E.b / 800 * (800 / E.b) = 1 := by field_simp
    have h2 : E.ell ^ (-(2 : ℝ)) * E.ell ^ 2 = 1 := by
      rw [Real.rpow_neg hℓpos.le, Real.rpow_two,
        inv_mul_cancel₀ (ne_of_gt (pow_pos hℓpos 2))]
    rw [show ((E.b / 800) * E.ell ^ (-(2 : ℝ))) * ((800 / E.b) * E.ell ^ 2)
        = (E.b / 800 * (800 / E.b)) * (E.ell ^ (-(2 : ℝ)) * E.ell ^ 2) by ring, h1, h2,
      mul_one]
  -- expansion of the word
  have hexp : F.qw Φ (Wta F T E)
      = ∑ s ∈ suppL E, cTa F T E s * (2 * F.bp (T.ta (-s) Φ) Φ) := by
    rw [Wta]
    simp only [FockData.qw, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    simp only [LinearMap.add_apply, map_add, LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [T.taDag_adjoint, F.bp_symm]
    ring
  rw [hexp]
  -- the per-`s` AM–GM (the *lower* bound: the statement needs a lower bound on the word)
  have hstep : ∀ s ∈ suppL E,
      - (((E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.ta (-s) Φ) (T.ta (-s) Φ))
        + ((800 / E.b) * E.ell ^ 2 * (cTa F T E s) ^ 2) * F.normSq Φ)
      ≤ cTa F T E s * (2 * F.bp (T.ta (-s) Φ) Φ) := by
    intro s hs
    have hP0 : 0 ≤ F.bp (T.ta (-s) Φ) (T.ta (-s) Φ) := F.bp_nonneg _
    have hN0 : 0 ≤ F.normSq Φ := F.normSq_nonneg Φ
    have hcs : |F.bp (T.ta (-s) Φ) Φ|
        ≤ Real.sqrt (F.bp (T.ta (-s) Φ) (T.ta (-s) Φ)) * Real.sqrt (F.normSq Φ) :=
      Work.BoseB7.bp_cauchy_abs F _ _
    have hAM := amgm_weighted hP0 hN0 (abs_nonneg (cTa F T E s)) hαpos hβpos hαβ
    have hAM' : 2 * |cTa F T E s| * (Real.sqrt (F.bp (T.ta (-s) Φ) (T.ta (-s) Φ))
          * Real.sqrt (F.normSq Φ))
        ≤ ((E.b / 800) * E.ell ^ (-(2 : ℝ))) * F.bp (T.ta (-s) Φ) (T.ta (-s) Φ)
          + ((800 / E.b) * E.ell ^ 2) * |cTa F T E s| ^ 2 * F.normSq Φ := hAM
    have habs : |cTa F T E s * (2 * F.bp (T.ta (-s) Φ) Φ)|
        = 2 * |cTa F T E s| * |F.bp (T.ta (-s) Φ) Φ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hbound : |cTa F T E s * (2 * F.bp (T.ta (-s) Φ) Φ)|
        ≤ 2 * |cTa F T E s| * (Real.sqrt (F.bp (T.ta (-s) Φ) (T.ta (-s) Φ))
          * Real.sqrt (F.normSq Φ)) := by
      rw [habs]
      exact mul_le_mul_of_nonneg_left hcs (by positivity)
    have hsq : |cTa F T E s| ^ 2 = (cTa F T E s) ^ 2 := sq_abs _
    rw [hsq] at hAM'
    linarith [neg_abs_le (cTa F T E s * (2 * F.bp (T.ta (-s) Φ) Φ)), hbound, hAM']
  -- the two sums
  have hsum_gap : ∑ s ∈ suppL E,
        (E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.ta (-s) Φ) (T.ta (-s) Φ)
      ≤ (E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hta := T.ta_le_N (excited Mode) (fun s hs => (Finset.mem_erase.mp hs).1) Φ
    have hid : F.bp ((∑ j ∈ excited Mode, T.taDag j ∘ₗ T.ta j) Φ) Φ
        = ∑ j ∈ excited Mode, F.bp (T.ta j Φ) (T.ta j Φ) := by
      rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun j _ => T.taDag_adjoint j (T.ta j Φ) Φ
    have hsub' : (suppL E).image (Equiv.neg Mode) ⊆ excited Mode := by
      intro j hj
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
      simp only [Equiv.neg_apply, excited, Finset.mem_erase, Finset.mem_univ, and_true]
      exact neg_ne_zero.mpr (suppL_ne_zero hs)
    calc ∑ s ∈ suppL E, F.bp (T.ta (-s) Φ) (T.ta (-s) Φ)
        = ∑ j ∈ (suppL E).image (Equiv.neg Mode), F.bp (T.ta j Φ) (T.ta j Φ) := by
          rw [Finset.sum_image (g := Equiv.neg Mode)
            (f := fun j => F.bp (T.ta j Φ) (T.ta j Φ))
            (fun a _ b _ h => neg_injective (by simpa only [Equiv.neg_apply] using h))]
          simp only [Equiv.neg_apply]
      _ ≤ ∑ j ∈ excited Mode, F.bp (T.ta j Φ) (T.ta j Φ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun j _ _ => F.bp_nonneg _)
      _ = F.bp ((∑ j ∈ excited Mode, T.taDag j ∘ₗ T.ta j) Φ) Φ := hid.symm
      _ ≤ F.bp (T.N Φ) Φ := hta
  have hsum_cost : ∑ s ∈ suppL E, (800 / E.b) * E.ell ^ 2 * (cTa F T E s) ^ 2
      ≤ costTa K₀ E hv := by
    have h1 : ∀ s ∈ suppL E, (cTa F T E s) ^ 2 ≤ (Mc K₀ E hv) ^ 2 := by
      intro s hs
      have h2 : |cTa F T E s| ≤ Mc K₀ E hv := by
        have h3 := hc s
        have h4 : E.fL s ≤ 1 := hK.fL_le_one s
        calc |cTa F T E s| ≤ Mc K₀ E hv * E.fL s := h3
          _ ≤ Mc K₀ E hv * 1 := mul_le_mul_of_nonneg_left h4 hMc0
          _ = Mc K₀ E hv := mul_one _
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h2 : ∑ s ∈ suppL E, (cTa F T E s) ^ 2
        ≤ (Mc K₀ E hv) ^ 2 * ((suppL E).card : ℝ) := by
      calc ∑ s ∈ suppL E, (cTa F T E s) ^ 2
          ≤ ∑ _s ∈ suppL E, (Mc K₀ E hv) ^ 2 := Finset.sum_le_sum h1
        _ = (Mc K₀ E hv) ^ 2 * ((suppL E).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    have h3 := suppL_card_le (K₀ := K₀) (F := F) (T := T) (E := E) hK
    have h4 : (Mc K₀ E hv) ^ 2 * ((suppL E).card : ℝ)
        ≤ (Mc K₀ E hv) ^ 2 * (K₀ * (E.Kl * E.KL) ^ 3) :=
      mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    have h5 : (800 / E.b) * E.ell ^ 2 * ((Mc K₀ E hv) ^ 2 * (K₀ * (E.Kl * E.KL) ^ 3))
        = costTa K₀ E hv := by
      rw [costTa]; ring
    calc ∑ s ∈ suppL E, (800 / E.b) * E.ell ^ 2 * (cTa F T E s) ^ 2
        = (800 / E.b) * E.ell ^ 2 * ∑ s ∈ suppL E, (cTa F T E s) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (800 / E.b) * E.ell ^ 2 * ((Mc K₀ E hv) ^ 2 * ((suppL E).card : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (800 / E.b) * E.ell ^ 2 * ((Mc K₀ E hv) ^ 2 * (K₀ * (E.Kl * E.KL) ^ 3)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = costTa K₀ E hv := h5
  -- assemble
  have hmain : -((E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ
        + costTa K₀ E hv * F.normSq Φ)
      ≤ ∑ s ∈ suppL E, cTa F T E s * (2 * F.bp (T.ta (-s) Φ) Φ) := by
    have h := Finset.sum_le_sum hstep
    rw [Finset.sum_neg_distrib] at h
    rw [Finset.sum_add_distrib] at h
    have hb : ∑ s ∈ suppL E, ((800 / E.b) * E.ell ^ 2 * (cTa F T E s) ^ 2) * F.normSq Φ
        ≤ costTa K₀ E hv * F.normSq Φ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hsum_cost (F.normSq_nonneg Φ)
    have htot : (∑ s ∈ suppL E,
            (E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.ta (-s) Φ) (T.ta (-s) Φ))
          + ∑ s ∈ suppL E, ((800 / E.b) * E.ell ^ 2 * (cTa F T E s) ^ 2) * F.normSq Φ
        ≤ (E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ
          + costTa K₀ E hv * F.normSq Φ :=
      add_le_add hsum_gap hb
    linarith [h, htot]
  have hgoal : -(costTa K₀ E hv) * F.normSq Φ
        - (E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ
      = -((E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ
        + costTa K₀ E hv * F.normSq Φ) := by ring
  rw [hgoal]
  exact hmain

end Est1

end Work.BoseC3QAll
