import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.estR1_defs
import Submission.Work.BoseC3QAll.q3Denom_le_four
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.Est1.Wb2_bound` — the `σ₁`-word `κA(b_{s-k}† + b_{s-k})`
of FS `lem:EstimatesOnQ3-js` (piece **C**, family 3)

The word

`Wb2 = (z/ℓ³) Σ_{s∈suppL} Σ_{k∈P_H} γ_{sk}β_{sk}κA_{sk} · (b_{s-k}† + b_{s-k})`

is estimated by Cauchy–Schwarz against the kinetic reserve on the quarter region
`P_H^q`: for every `Φ` in FS's number window,

`-(costB3)‖Φ‖² - (𝓁²/8)⟨Φ, dNumOpR(P_H^q) Φ⟩ ≤ ⟨Φ, Wb2 Φ⟩`.

The proof is the standard absorption: with `c_{sk}` the coefficient of the
`(s,k)`-summand and `ε = 𝓁²/(8#suppL)`,

`2 c_{sk}⟨b_{s-k}Φ, Φ⟩ ≥ -(c_{sk}²/(ε 𝒟_{s-k}))‖Φ‖² - ε 𝒟_{s-k}‖b_{s-k}Φ‖²`,

`Σ_{s∈suppL} Σ_{k∈P_H} 𝒟_{s-k}‖b_{s-k}Φ‖² ≤ #suppL · ⟨dNumOpR(P_H^q)⟩`
(`k ↦ s-k` is injective and `s-k ∈ P_H^q`), and the coefficient sum is
dominated by `2^38 K₀⁹ #suppL 𝓁⁴η²ρ³a⁷K_H⁴`, which the arithmetic of the
parameter point converts into `(8#suppL/𝓁²)·(…) ≤ costB3`.
-/

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.BoseC3QAll.Est1

open Work.BoseB7
open Submission.BoseGases (bogS bogAlpha bogS_nonneg)

/-! ## 1. Elementary form lemmas -/

/-- Linearity of `qw` in the operator (a sum of scalar multiples). -/
theorem qw_finset_sum_aux {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    {ι : Type*} (F : FockData Mode) (Φ : F.H) (t : Finset ι) (c : ι → ℝ)
    (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (∑ i ∈ t, c i • X i) = ∑ i ∈ t, c i * F.qw Φ (X i) := by
  have h1 : (∑ i ∈ t, c i • X i) Φ = ∑ i ∈ t, c i • (X i Φ) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply]
  calc F.qw Φ (∑ i ∈ t, c i • X i)
      = F.bp (∑ i ∈ t, c i • (X i Φ)) Φ := by rw [FockData.qw, h1]
    _ = (∑ i ∈ t, F.bp (c i • (X i Φ))) Φ := by rw [map_sum]
    _ = ∑ i ∈ t, F.bp (c i • (X i Φ)) Φ := by rw [LinearMap.sum_apply]
    _ = ∑ i ∈ t, c i * F.bp (X i Φ) Φ :=
        Finset.sum_congr rfl fun i _ => by
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    _ = ∑ i ∈ t, c i * F.qw Φ (X i) :=
        Finset.sum_congr rfl fun i _ => by rw [FockData.qw]

/-- The same for a double sum. -/
theorem qw_double_sum_aux {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (Φ : F.H) (S K : Finset Mode) (c : Mode → Mode → ℝ)
    (X : Mode → Mode → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (∑ s ∈ S, ∑ k ∈ K, c s k • X s k)
      = ∑ s ∈ S, ∑ k ∈ K, c s k * F.qw Φ (X s k) := by
  have h1 : (∑ s ∈ S, ∑ k ∈ K, c s k • X s k)
      = ∑ s ∈ S, (1 : ℝ) • (∑ k ∈ K, c s k • X s k) := by
    exact Finset.sum_congr rfl fun s _ => (one_smul _ _).symm
  rw [h1, qw_finset_sum_aux F Φ S (fun _ => 1) (fun s => ∑ k ∈ K, c s k • X s k)]
  simp only [one_mul]
  exact Finset.sum_congr rfl fun s _ => qw_finset_sum_aux F Φ K (c s) (X s)

/-- The quadratic form of `b_q† + b_q` is twice the cross term:
`⟨(b_q†+b_q)Φ,Φ⟩ = 2⟨b_qΦ,Φ⟩`. -/
theorem qw_bOp_add_aux {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (α : Mode → ℝ) (q : Mode) (Φ : F.H) :
    F.qw Φ (F.bOpDag α q + F.bOp α q) = 2 * F.bp (F.bOp α q Φ) Φ := by
  rw [FockData.qw, LinearMap.add_apply, map_add, LinearMap.add_apply,
    bp_bOpDag F α q Φ Φ, F.bp_symm Φ (F.bOp α q Φ)]
  ring

/-! ## 2. The single-pair Young inequality -/

/-- **The absorption of one summand.**  For real `c`, `ε, D > 0` and any `Φ`,

`-(c²/(εD))‖Φ‖² - εD‖b_qΦ‖² ≤ c⟨(b_q†+b_q)Φ,Φ⟩`.

This is Cauchy–Schwarz `|⟨b_qΦ,Φ⟩| ≤ ‖b_qΦ‖‖Φ‖` followed by Young's inequality
`2|c|‖b_qΦ‖‖Φ‖ ≤ εD‖b_qΦ‖² + (c²/(εD))‖Φ‖²`. -/
theorem wb2_pair_absorb_aux {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (α : Mode → ℝ) (q : Mode) (Φ : F.H)
    {c ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    -(c ^ 2 / (ε * D)) * F.bp Φ Φ - (ε * D) * F.bp (F.bOp α q Φ) (F.bOp α q Φ)
      ≤ c * F.bp ((F.bOpDag α q + F.bOp α q) Φ) Φ := by
  set W := F.bp Φ Φ with hW
  set X := F.bp (F.bOp α q Φ) (F.bOp α q Φ) with hX
  set B := F.bp (F.bOp α q Φ) Φ with hB
  have hWnn : 0 ≤ W := F.bp_nonneg Φ
  have hXnn : 0 ≤ X := F.bp_nonneg _
  have ht : 0 < ε * D := mul_pos hε hD
  -- Cauchy–Schwarz `|⟨b_qΦ,Φ⟩| ≤ ‖b_qΦ‖‖Φ‖`
  have hcs : |B| ≤ Real.sqrt X * Real.sqrt W := by
    rw [hB, hX, hW]
    exact bp_cauchy_abs F _ Φ
  -- Young `2|c|‖b_qΦ‖‖Φ‖ ≤ εD‖b_qΦ‖² + (c²/(εD))‖Φ‖²`
  have hy := two_mul_le_eps_inv ht (Real.sqrt X) (|c| * Real.sqrt W)
  have hXsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt hXnn
  have hWsq : (|c| * Real.sqrt W) ^ 2 = c ^ 2 * W := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hWnn]
  have hcrit : 2 * |c| * |B| ≤ ε * D * X + c ^ 2 / (ε * D) * W := by
    rw [hXsq, hWsq] at hy
    have h4 : (ε * D) * X + (ε * D)⁻¹ * (c ^ 2 * W) = ε * D * X + c ^ 2 / (ε * D) * W := by
      rw [inv_mul_eq_div]
      ring
    rw [h4] at hy
    have h3 : 2 * |c| * |B| ≤ 2 * |c| * (Real.sqrt X * Real.sqrt W) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    have h5 : 2 * |c| * (Real.sqrt X * Real.sqrt W)
        = 2 * Real.sqrt X * (|c| * Real.sqrt W) := by ring
    linarith [h3, h5.le, h5.ge, hy]
  have hgoal : -(ε * D * X + c ^ 2 / (ε * D) * W) ≤ c * (2 * B) := by
    have h3 : |c * (2 * B)| = 2 * |c| * |B| := by
      rw [show c * (2 * B) = 2 * c * B by ring, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h4 := neg_abs_le (c * (2 * B))
    rw [h3] at h4
    linarith [h4, hcrit]
  have hadj : F.bp ((F.bOpDag α q + F.bOp α q) Φ) Φ = 2 * B := by
    rw [LinearMap.add_apply, map_add, LinearMap.add_apply, bp_bOpDag,
      F.bp_symm Φ (F.bOp α q Φ), hB]
    ring
  rw [hadj]
  linarith [hgoal]

/-! ## 3. A Finset reindexing lemma -/

/-- A sum over an injectively reindexed finset is at most the sum over a larger
finset (the terms need only be nonnegative *on the larger finset*). -/
theorem sum_le_sum_image {ι : Type*} [DecidableEq ι] {t u : Finset ι} {φ : ι → ι}
    (hφ : ∀ i j, φ i = φ j → i = j) (hsub : ∀ i ∈ t, φ i ∈ u) {f : ι → ℝ}
    (hf : ∀ i ∈ u, 0 ≤ f i) : ∑ i ∈ t, f (φ i) ≤ ∑ j ∈ u, f j := by
  rw [← Finset.sum_image (fun x hx y hy h => hφ x y h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hsub)
    fun j hj _ => hf j hj

/-! ## 4. The three auxiliary bounds -/

/-- The coefficient of the `(s,k)` summand of `Wb2`. -/
noncomputable def wb2coef {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : ℝ :=
  (E.z / E.ell ^ 3) * (gA E s k * bA E s k * kA T E s k)

theorem wb2coef_expand {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) :
    Wb2 F T E = ∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
      wb2coef F T E s k • (F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k)) := rfl

/-- `a/(b*d) = (1/b)*(a/d)` for `b, d ≠ 0`. -/
theorem div_mul_div_eq (a b d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / (b * d) = (1 / b) * (a / d) := by
  field_simp

/-- `|α_k| ≤ 2ρ|Ŵ₁(k)|/‖k‖²` on `P_H^q`. -/
theorem alpha_abs_le_of_PHq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {F : FockData Mode} {E : Q3Env Mode} {k : Mode}
    (hkn : 0 < ‖F.kmom k‖) (hρ : 0 ≤ E.rho)
    (hA : 0 < E.A k) (hAge : ‖F.kmom k‖ ^ 2 / 2 ≤ E.A k) (hBeq : E.B k = E.rho * E.W1 k) :
    |E.alpha k| ≤ 2 * E.rho * |E.W1 k| / ‖F.kmom k‖ ^ 2 := by
  have hbog : 0 ≤ bogS (E.A k) (E.B k) := bogS_nonneg _ _
  have hden : 0 < E.A k + bogS (E.A k) (E.B k) := by linarith
  have h1 : |E.alpha k| = |E.B k| / (E.A k + bogS (E.A k) (E.B k)) := by
    rw [Work.BoseB7.Q3Env.alpha, alphaCoef, bogAlpha, abs_div, abs_of_pos hden]
  have h2 : |E.B k| / (E.A k + bogS (E.A k) (E.B k)) ≤ |E.B k| / E.A k :=
    div_le_div_of_nonneg_left (abs_nonneg _) hA (by linarith)
  have h3 : |E.B k| / E.A k ≤ |E.B k| / (‖F.kmom k‖ ^ 2 / 2) :=
    div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hAge
  have h4 : |E.B k| / (‖F.kmom k‖ ^ 2 / 2) = 2 * E.rho * |E.W1 k| / ‖F.kmom k‖ ^ 2 := by
    rw [hBeq, abs_mul, abs_of_nonneg hρ]
    field_simp
  linarith [h1.le, h1.ge, h2, h3]

/-- **The coefficient sum.** -/
theorem wb2_coef_sum_aux (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E →
        ∑ s ∈ suppL E, ∑ k ∈ F.PHset E, (wb2coef F T E s k) ^ 2 / E.D (s - k)
          ≤ (2 : ℝ) ^ 38 * K₀ ^ 9 * ((suppL E).card : ℝ)
              * E.lille ^ 4 * (eta E) ^ 2 * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4 := by
  obtain ⟨t₁, ht₁, h₁⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, h₂⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t₃, ht₃, h₃⟩ := q3Denom_le_four K₀ b₀ hb₀
  refine ⟨min t₁ (min t₂ t₃), lt_min ht₁ (lt_min ht₂ ht₃), ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK
  have hle₁ : hv.t ≤ t₁ := le_trans htle (min_le_left _ _)
  have hle₂ : hv.t ≤ t₂ := le_trans htle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hle₃ : hv.t ≤ t₃ := le_trans htle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hαeven, hAB, hHalf, hαle, hDq⟩ := h₁ F T E hv hle₁ hb hK
  obtain ⟨hPHsub, hsubPHq, -⟩ := h₂ F T E hv hle₂ hb hK
  have hDen4 := h₃ F T E hv hle₃ hb hK
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hKl : 0 < E.Kl := lt_of_lt_of_le one_pos hv.one_le_Kl
  have hell : 0 < E.ell := ell_pos E hv
  have hlille : 0 < E.lille := lille_pos E hv
  have hρ : 0 < E.rho := rho_pos E hv
  have hK0 : 0 ≤ K₀ := by
    have h := hK.sum_hatChiSq
    have hnn : 0 ≤ ∑ s ∈ (excited Mode), |E.hatChiSq s| :=
      Finset.sum_nonneg fun s _ => abs_nonneg _
    linarith
  have hη : 0 ≤ eta E := by
    rw [eta]
    refine Real.rpow_nonneg ?_ _
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hKl) _) hlille.le
  set C1 : ℝ := (E.rho / E.ell ^ 3) * (2 : ℝ) ^ 34 * K₀ ^ 8 * E.lille ^ 4
    * E.KH ^ 2 * E.aScat ^ 4 * (eta E) ^ 2 with hC1def
  have hC1nn : 0 ≤ C1 := by
    rw [hC1def]
    positivity
  -- the per-summand bound
  have hper : ∀ s ∈ suppL E, ∀ k ∈ F.PHset E,
      (wb2coef F T E s k) ^ 2 / E.D (s - k) ≤ C1 * E.alpha k ^ 2 := by
    intro s hs k hk
    have hfL : E.fL s ≠ 0 := suppL_fL_ne_zero hs
    by_cases hW : E.W1 k = 0
    · -- `Ŵ₁ k = 0` makes the coefficient vanish
      have hz : (wb2coef F T E s k) ^ 2 = 0 := by rw [wb2coef, gA, hW]; ring
      rw [hz, zero_div]
      exact mul_nonneg hC1nn (sq_nonneg _)
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hkq : F.PHq E.KH E.aScat k := hPHsub k hkPH
    have hskq : F.PHq E.KH E.aScat (s - k) := hsubPHq s k hfL hk hW
    have hcut : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom (s - k)‖ := hskq
    have hkn : 0 < ‖F.kmom (s - k)‖ := lt_of_lt_of_le (by positivity) hcut
    have hDpos : 0 < E.D (s - k) := by
      have := hDq (s - k) hskq
      nlinarith [sq_nonneg ‖F.kmom (s - k)‖]
    have hfL2 : (E.fL s) ^ 2 ≤ 1 := pow_le_one₀ (hK.fL_nonneg s) (hK.fL_le_one s)
    have hW12 : (E.W1 k) ^ 2 ≤ K₀ ^ 2 * E.aScat ^ 2 := by
      calc (E.W1 k) ^ 2 = |E.W1 k| ^ 2 := (sq_abs _).symm
        _ ≤ (K₀ * E.aScat) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hK.W1_le k) 2
        _ = K₀ ^ 2 * E.aScat ^ 2 := by ring
    have hQ2 : (E.q3Denom s k) ^ 2 ≤ 16 := by
      have hden : 0 < (1 - E.alpha k ^ 2) * (1 - E.alpha (s - k) ^ 2) := by
        have h1 := hHalf k hkq
        have h2 := hHalf (s - k) hskq
        nlinarith
      have hQpos : 0 < E.q3Denom s k := by
        rw [Work.BoseB7.Q3Env.q3Denom]
        exact div_pos one_pos hden
      have habs : |E.q3Denom s k| ≤ 4 := abs_le.mpr ⟨by linarith, hDen4 s k hfL hk hW⟩
      calc (E.q3Denom s k) ^ 2 = |E.q3Denom s k| ^ 2 := (sq_abs _).symm
        _ ≤ 4 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = 16 := by norm_num
    have hαk2 : (E.alpha k) ^ 2 ≤ (2 : ℝ) ^ 12 * K₀ ^ 2 * E.lille ^ 2 := by
      have h1 := hαle k hkq
      have h2 : |E.alpha k| ^ 2 ≤ (64 * K₀ * E.lille) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 : (64 * K₀ * E.lille) ^ 2 = (2 : ℝ) ^ 12 * K₀ ^ 2 * E.lille ^ 2 := by ring
      rw [sq_abs, h3] at h2
      exact h2
    have hαsk2 : (E.alpha (s - k)) ^ 2 / E.D (s - k)
        ≤ (2 : ℝ) ^ 18 * K₀ ^ 2 * E.lille ^ 2 * E.KH ^ 2 * E.aScat ^ 2 := by
      have h1 : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hαle (s - k) hskq
      have h2 : (E.alpha (s - k)) ^ 2 ≤ (2 : ℝ) ^ 12 * K₀ ^ 2 * E.lille ^ 2 := by
        have h2' : |E.alpha (s - k)| ^ 2 ≤ (64 * K₀ * E.lille) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
        have h3 : (64 * K₀ * E.lille) ^ 2 = (2 : ℝ) ^ 12 * K₀ ^ 2 * E.lille ^ 2 := by ring
        rw [sq_abs, h3] at h2'
        exact h2'
      have hk2 : 1 / (16 * E.KH ^ 2 * E.aScat ^ 2) ≤ ‖F.kmom (s - k)‖ ^ 2 := by
        have hnn : 0 ≤ 1 / (4 * E.KH * E.aScat) := by positivity
        have h2 : (1 / (4 * E.KH * E.aScat)) ^ 2 ≤ ‖F.kmom (s - k)‖ ^ 2 :=
          pow_le_pow_left₀ hnn hcut 2
        have h3 : (1 / (4 * E.KH * E.aScat)) ^ 2 = 1 / (16 * E.KH ^ 2 * E.aScat ^ 2) := by
          rw [div_pow]
          ring
        rwa [h3] at h2
      have h4 : (4 : ℝ) ≤ 64 * E.KH ^ 2 * E.aScat ^ 2 * ‖F.kmom (s - k)‖ ^ 2 := by
        have h5 := mul_le_mul_of_nonneg_left hk2
          (by positivity : 0 ≤ 64 * E.KH ^ 2 * E.aScat ^ 2)
        have h6 : 64 * E.KH ^ 2 * E.aScat ^ 2 * (1 / (16 * E.KH ^ 2 * E.aScat ^ 2)) = 4 := by
          field_simp
          ring
        linarith [h5, h6.le, h6.ge]
      have hDinv : 1 / E.D (s - k) ≤ 64 * E.KH ^ 2 * E.aScat ^ 2 := by
        have h7 : 1 / E.D (s - k) ≤ 1 / (‖F.kmom (s - k)‖ ^ 2 / 4) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          have := hDq (s - k) hskq
          linarith
        have h8 : 1 / (‖F.kmom (s - k)‖ ^ 2 / 4)
            = 4 / ‖F.kmom (s - k)‖ ^ 2 := by
          field_simp
        have h9 : 4 / ‖F.kmom (s - k)‖ ^ 2 ≤ 64 * E.KH ^ 2 * E.aScat ^ 2 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖F.kmom (s - k)‖ ^ 2)]
          linarith [h4]
        linarith [h7, h8.le, h8.ge, h9]
      calc (E.alpha (s - k)) ^ 2 / E.D (s - k)
          = (E.alpha (s - k)) ^ 2 * (1 / E.D (s - k)) := by ring
        _ ≤ ((2 : ℝ) ^ 12 * K₀ ^ 2 * E.lille ^ 2)
              * (64 * E.KH ^ 2 * E.aScat ^ 2) :=
            mul_le_mul h2 hDinv (by positivity) (by positivity)
        _ = (2 : ℝ) ^ 18 * K₀ ^ 2 * E.lille ^ 2 * E.KH ^ 2 * E.aScat ^ 2 := by ring
    have hccr2 : (T.ccrX (-s) (-k)) ^ 2 ≤ K₀ ^ 2 * (eta E) ^ 2 := by
      have hfL' : E.fL (-s) ≠ 0 := by rw [hK.fL_even s]; exact hfL
      have hnk : F.PHq E.KH E.aScat (-k) := by
        show 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom (-k)‖
        rw [F.kmom_neg k, norm_neg]
        exact hkq
      have h1 := hK.ccrX_small (-s) (-k) hfL' hnk
      have h2 : |T.ccrX (-s) (-k)| ^ 2 ≤ (K₀ * eta E) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 : (K₀ * eta E) ^ 2 = K₀ ^ 2 * (eta E) ^ 2 := by ring
      rw [sq_abs, h3] at h2
      exact h2
    have hexp : (wb2coef F T E s k) ^ 2 / E.D (s - k)
        = E.z ^ 2 / E.ell ^ 6 * (E.fL s) ^ 2 * (E.W1 k) ^ 2 * (E.q3Denom s k) ^ 2
          * (E.alpha k) ^ 2 * ((E.alpha (s - k)) ^ 2 / E.D (s - k)) * (E.alpha k) ^ 2
          * (T.ccrX (-s) (-k)) ^ 2 := by
      simp only [wb2coef, gA, bA, kA]
      field_simp
    rw [hexp]
    calc E.z ^ 2 / E.ell ^ 6 * (E.fL s) ^ 2 * (E.W1 k) ^ 2 * (E.q3Denom s k) ^ 2
          * (E.alpha k) ^ 2 * ((E.alpha (s - k)) ^ 2 / E.D (s - k)) * (E.alpha k) ^ 2
          * (T.ccrX (-s) (-k)) ^ 2
        ≤ E.z ^ 2 / E.ell ^ 6 * 1 * (K₀ ^ 2 * E.aScat ^ 2) * 16
          * (E.alpha k) ^ 2
          * ((2 : ℝ) ^ 18 * K₀ ^ 2 * E.lille ^ 2 * E.KH ^ 2 * E.aScat ^ 2)
          * ((2 : ℝ) ^ 12 * K₀ ^ 2 * E.lille ^ 2) * (K₀ ^ 2 * (eta E) ^ 2) := by
          gcongr
      _ = C1 * E.alpha k ^ 2 := by
          have hz : E.z ^ 2 / E.ell ^ 6 = E.rho / E.ell ^ 3 := by
            rw [Work.BoseB7.zsq_eq E hv]
            field_simp
          rw [hz, hC1def]
          ring_nf
  -- summing the per-summand bounds
  have hsum1 : (∑ s ∈ suppL E, ∑ k ∈ F.PHset E, (wb2coef F T E s k) ^ 2 / E.D (s - k))
      ≤ ∑ s ∈ suppL E, ∑ k ∈ F.PHset E, C1 * E.alpha k ^ 2 :=
    Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun k hk => hper s hs k hk
  have hsum2 : (∑ s ∈ suppL E, ∑ k ∈ F.PHset E, C1 * E.alpha k ^ 2)
      = C1 * (((suppL E).card : ℝ) * ∑ k ∈ F.PHset E, E.alpha k ^ 2) := by
    have hinner : ∀ s : Mode, (∑ k ∈ F.PHset E, C1 * E.alpha k ^ 2)
        = C1 * ∑ k ∈ F.PHset E, E.alpha k ^ 2 := fun s => by
      rw [← Finset.mul_sum]
    rw [show (∑ s ∈ suppL E, ∑ k ∈ F.PHset E, C1 * E.alpha k ^ 2)
        = ∑ s ∈ suppL E, C1 * ∑ k ∈ F.PHset E, E.alpha k ^ 2 from
      Finset.sum_congr rfl fun s _ => hinner s]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  -- the sum of `α_k²`
  have hsumα : (∑ k ∈ F.PHset E, E.alpha k ^ 2)
      ≤ (2 : ℝ) ^ 4 * E.rho ^ 2 * E.KH ^ 2 * E.aScat ^ 2 * E.ell ^ 3 * K₀ * E.aScat := by
    have hstep : ∀ k ∈ F.PHset E,
        (E.alpha k) ^ 2 ≤ 4 * E.rho ^ 2 * (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4 := by
      intro k hk
      have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
      have hkq : F.PHq E.KH E.aScat k := hPHsub k hkPH
      have hAge : ‖F.kmom k‖ ^ 2 / 2 ≤ E.A k := hK.A_ge k hkq
      have hcutk : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom k‖ := hkq
      have hposk : 0 < ‖F.kmom k‖ := lt_of_lt_of_le (by positivity) hcutk
      have hApos : 0 < E.A k := by
        have h2 : 0 < ‖F.kmom k‖ ^ 2 / 2 := by positivity
        linarith
      have hα := alpha_abs_le_of_PHq hposk (le_of_lt hρ) hApos hAge (hK.B_eq k)
      have hsq : (E.alpha k) ^ 2 ≤ (2 * E.rho * |E.W1 k| / ‖F.kmom k‖ ^ 2) ^ 2 := by
        have h2 : |E.alpha k| ^ 2 ≤ (2 * E.rho * |E.W1 k| / ‖F.kmom k‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hα 2
        rwa [sq_abs] at h2
      calc (E.alpha k) ^ 2 ≤ (2 * E.rho * |E.W1 k| / ‖F.kmom k‖ ^ 2) ^ 2 := hsq
        _ = 4 * E.rho ^ 2 * (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4 := by
            rw [div_pow, mul_pow, sq_abs]
            ring
    have h1 : (∑ k ∈ F.PHset E, E.alpha k ^ 2)
        ≤ ∑ k ∈ F.PHset E, 4 * E.rho ^ 2 * (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4 :=
      Finset.sum_le_sum hstep
    have h2 : (∑ k ∈ F.PHset E, 4 * E.rho ^ 2 * (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4)
        = 4 * E.rho ^ 2 * ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h3 : (∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4)
        ≤ (2 * E.KH * E.aScat) ^ 2 * ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2 := by
      have hstep' : ∀ k ∈ F.PHset E,
          (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4 ≤ (2 * E.KH * E.aScat) ^ 2
            * ((E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) := by
        intro k hk
        have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
        have hcut : 1 / (2 * E.KH * E.aScat) ≤ ‖F.kmom k‖ := hkPH
        have hnorm : 0 < ‖F.kmom k‖ := lt_of_lt_of_le (by positivity) hcut
        have hkey : 1 / ‖F.kmom k‖ ^ 2 ≤ (2 * E.KH * E.aScat) ^ 2 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖F.kmom k‖ ^ 2)]
          have hsq : 1 ≤ (2 * E.KH * E.aScat) ^ 2 * ‖F.kmom k‖ ^ 2 := by
            have h2 : (1 / (2 * E.KH * E.aScat)) ^ 2 ≤ ‖F.kmom k‖ ^ 2 :=
              pow_le_pow_left₀ (by positivity) hcut 2
            have h3 : (1 / (2 * E.KH * E.aScat)) ^ 2 = 1 / (2 * E.KH * E.aScat) ^ 2 := by
              rw [div_pow]
              norm_num
            rw [h3] at h2
            have h4 : 1 / (2 * E.KH * E.aScat) ^ 2 * (2 * E.KH * E.aScat) ^ 2 = 1 := by
              field_simp
            nlinarith [h2, h4, hnorm]
          linarith [hsq]
        have hWnn : 0 ≤ (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2 := by positivity
        calc (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4
            = ((E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) * (1 / ‖F.kmom k‖ ^ 2) := by ring
          _ ≤ ((E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) * (2 * E.KH * E.aScat) ^ 2 :=
              mul_le_mul_of_nonneg_left hkey hWnn
          _ = (2 * E.KH * E.aScat) ^ 2 * ((E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) := by ring
      calc (∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4)
          ≤ ∑ k ∈ F.PHset E, (2 * E.KH * E.aScat) ^ 2
              * ((E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) := Finset.sum_le_sum hstep'
        _ = (2 * E.KH * E.aScat) ^ 2 * ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2 := by
            rw [← Finset.mul_sum]
    have h4 : (∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2)
        ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
      have hsub : F.PHset E ⊆ (excited Mode).filter (F.PHq E.KH E.aScat) := by
        intro k hk
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hk).1, hPHsub k (Finset.mem_filter.mp hk).2⟩
      have h5 : (∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2)
          ≤ ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
      have h6 : (E.ell ^ (3 : ℝ))⁻¹ * (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            (E.W1 q) ^ 2 / ‖F.kmom q‖ ^ 2) ≤ K₀ * E.aScat := by
        have h := hK.sum_W1sq
        rwa [Real.rpow_neg hell.le] at h
      have h6' : (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            (E.W1 q) ^ 2 / ‖F.kmom q‖ ^ 2) ≤ E.ell ^ (3 : ℝ) * (K₀ * E.aScat) := by
        have hcancel : E.ell ^ (3 : ℝ) * (E.ell ^ (3 : ℝ))⁻¹ = 1 :=
          mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hell 3))
        calc (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
              (E.W1 q) ^ 2 / ‖F.kmom q‖ ^ 2)
            = E.ell ^ (3 : ℝ) * ((E.ell ^ (3 : ℝ))⁻¹
                * ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
                    (E.W1 q) ^ 2 / ‖F.kmom q‖ ^ 2) := by
              rw [← mul_assoc, hcancel, one_mul]
          _ ≤ E.ell ^ (3 : ℝ) * (K₀ * E.aScat) :=
              mul_le_mul_of_nonneg_left h6 (by positivity)
      have h6'' : (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            (E.W1 q) ^ 2 / ‖F.kmom q‖ ^ 2) ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
        rw [show E.ell ^ (3 : ℝ) = E.ell ^ 3 from Real.rpow_natCast E.ell 3] at h6'
        exact h6'
      exact le_trans h5 h6''
    calc (∑ k ∈ F.PHset E, E.alpha k ^ 2)
        ≤ ∑ k ∈ F.PHset E, 4 * E.rho ^ 2 * (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4 := h1
      _ = 4 * E.rho ^ 2 * ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 4 := h2
      _ ≤ 4 * E.rho ^ 2 * ((2 * E.KH * E.aScat) ^ 2
            * ∑ k ∈ F.PHset E, (E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 4 * E.rho ^ 2
            * ((2 * E.KH * E.aScat) ^ 2 * (E.ell ^ 3 * (K₀ * E.aScat))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h4 (by positivity)) (by positivity)
      _ = (2 : ℝ) ^ 4 * E.rho ^ 2 * E.KH ^ 2 * E.aScat ^ 2 * E.ell ^ 3 * K₀ * E.aScat := by
          ring
  -- the final constant
  calc (∑ s ∈ suppL E, ∑ k ∈ F.PHset E, (wb2coef F T E s k) ^ 2 / E.D (s - k))
      ≤ ∑ s ∈ suppL E, ∑ k ∈ F.PHset E, C1 * E.alpha k ^ 2 := hsum1
    _ = C1 * (((suppL E).card : ℝ) * ∑ k ∈ F.PHset E, E.alpha k ^ 2) := hsum2
    _ ≤ C1 * (((suppL E).card : ℝ)
          * ((2 : ℝ) ^ 4 * E.rho ^ 2 * E.KH ^ 2 * E.aScat ^ 2 * E.ell ^ 3 * K₀ * E.aScat)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC1nn
        exact mul_le_mul_of_nonneg_left hsumα (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ 38 * K₀ ^ 9 * ((suppL E).card : ℝ)
          * E.lille ^ 4 * (eta E) ^ 2 * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4 := by
        rw [hC1def]
        field_simp


end Work.BoseC3QAll.Est1
