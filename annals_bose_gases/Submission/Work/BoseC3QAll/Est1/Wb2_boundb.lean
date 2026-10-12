import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseC3QAll.Est1.Wb2_bound
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
/-- **The reserve dominance.** -/
theorem wb2_reserve_dom_aux (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E → ∀ Φ : F.H,
        ∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
            E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)
          ≤ ((suppL E).card : ℝ) *
              ∑ q ∈ (Work.BoseB7.excited Mode).filter (F.PHq E.KH E.aScat),
                E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) := by
  obtain ⟨t₁, ht₁, h₁⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, h₂⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK Φ
  have hle₁ : hv.t ≤ t₁ := le_trans htle (min_le_left _ _)
  have hle₂ : hv.t ≤ t₂ := le_trans htle (min_le_right _ _)
  obtain ⟨hαeven, hAB, hHalf, hαle, hDq⟩ := h₁ F T E hv hle₁ hb hK
  obtain ⟨hPHsub, hsubPHq, -⟩ := h₂ F T E hv hle₂ hb hK
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  -- `kmom 0 = 0` and hence `0 ∉ P_H^q`
  have hkmom0 : F.kmom (0 : Mode) = 0 := by
    have h := F.kmom_neg (0 : Mode)
    rw [neg_zero] at h
    have h2 : F.kmom 0 + F.kmom 0 = 0 := by
      nth_rewrite 1 [h]
      exact neg_add_cancel _
    have h3 : (2 : ℝ) • F.kmom (0 : Mode) = 0 := by rw [two_smul]; exact h2
    rcases smul_eq_zero.mp h3 with h4 | h4
    · norm_num at h4
    · exact h4
  have hPHq_ne0 : ∀ q : Mode, F.PHq E.KH E.aScat q → q ≠ 0 := by
    intro q hq hq0
    have hcut : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom q‖ := hq
    rw [hq0, hkmom0, norm_zero] at hcut
    have hpos : 0 < 1 / (4 * E.KH * E.aScat) := by positivity
    linarith
  have hDnn : ∀ q : Mode, F.PHq E.KH E.aScat q → 0 ≤ E.D q := by
    intro q hq
    have := hDq q hq
    nlinarith [sq_nonneg ‖F.kmom q‖]
  set R := ∑ q ∈ (Work.BoseB7.excited Mode).filter (F.PHq E.KH E.aScat),
      E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) with hRdef
  have hRnn : 0 ≤ R :=
    Finset.sum_nonneg fun q hq =>
      mul_nonneg (hDnn q (Finset.mem_filter.mp hq).2) (F.bp_nonneg _)
  have hper : ∀ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
        E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ) ≤ R := by
    intro s hs
    refine sum_le_sum_image (t := (F.PHset E).filter (fun k => E.W1 k ≠ 0))
      (u := (Work.BoseB7.excited Mode).filter (F.PHq E.KH E.aScat))
      (φ := fun k => s - k)
      (f := fun q => E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
      (fun i j hij => sub_right_inj.mp hij) ?_ ?_
    · intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_erase.mpr
          ⟨hPHq_ne0 (s - k) (hsubPHq s k (suppL_fL_ne_zero hs) hk1 hk2), Finset.mem_univ _⟩
      · exact hsubPHq s k (suppL_fL_ne_zero hs) hk1 hk2
    · intro q hq
      exact mul_nonneg (hDnn q (Finset.mem_filter.mp hq).2) (F.bp_nonneg _)
  calc ∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
        E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)
      ≤ ∑ s ∈ suppL E, R := Finset.sum_le_sum fun s hs => hper s hs
    _ = ((suppL E).card : ℝ) * R := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The arithmetic of the constant.** -/
theorem wb2_arith_aux (K₀ : ℝ) (hK0 : 0 ≤ K₀)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) {Nf : ℝ}
    (hNf : 1 ≤ Nf) (hNfK : Nf ≤ K₀ * (E.Kl * E.KL) ^ 3) :
    (8 * Nf / E.lille ^ 2) *
        ((2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4 * (eta E) ^ 2
          * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4)
      ≤ costB3 K₀ E := by
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hlille : 0 < E.lille := lille_pos E hv
  have hρ : 0 < E.rho := rho_pos E hv
  have hmupos : 0 < E.mu := mu_pos E hv
  have hKlnn : 0 ≤ E.Kl := le_of_lt (lt_of_lt_of_le one_pos hv.one_le_Kl)
  have hKLnn : 0 ≤ E.KL := le_of_lt (lt_of_lt_of_le one_pos hv.one_le_KL)
  have hη : 0 ≤ eta E := by
    rw [eta]
    refine Real.rpow_nonneg ?_ _
    exact mul_nonneg (Real.rpow_nonneg hKlnn _) hlille.le
  -- `𝓁 = μa³K_H²`
  have h𝓁 : E.lille = E.mu * E.aScat ^ 3 * E.KH ^ 2 := by
    simp only [Work.BoseB7.Q3Env.lille, Work.BoseB7.lille]
  -- the three numeric ingredients
  have hNfnn : 0 ≤ Nf := le_trans zero_le_one hNf
  have hNf2 : Nf ^ 2 ≤ K₀ ^ 2 * (E.Kl * E.KL) ^ 6 := by
    have h1 : Nf ^ 2 ≤ (K₀ * (E.Kl * E.KL) ^ 3) ^ 2 :=
      pow_le_pow_left₀ hNfnn hNfK 2
    have h2 : (K₀ * (E.Kl * E.KL) ^ 3) ^ 2 = K₀ ^ 2 * (E.Kl * E.KL) ^ 6 := by ring
    rw [h2] at h1
    exact h1
  have hρ2 : E.rho ^ 2 ≤ (2 : ℝ) ^ 6 * E.mu ^ 2 := by
    have h := rho_le E hv
    nlinarith [h, hmupos, hρ]
  have hkey : Nf ^ 2 * E.rho ^ 2 * E.aScat ^ 6 * E.KH ^ 4
      ≤ (2 : ℝ) ^ 6 * K₀ ^ 2 * (E.Kl * E.KL) ^ 6 * E.lille ^ 2 := by
    have hρ2nn : 0 ≤ E.rho ^ 2 := sq_nonneg _
    have h2nn : 0 ≤ (2 : ℝ) ^ 6 * E.mu ^ 2 := by positivity
    have h1 : Nf ^ 2 * E.rho ^ 2
        ≤ (K₀ ^ 2 * (E.Kl * E.KL) ^ 6) * ((2 : ℝ) ^ 6 * E.mu ^ 2) :=
      mul_le_mul hNf2 hρ2 hρ2nn (by positivity)
    have ha6 : 0 ≤ E.aScat ^ 6 := by positivity
    have hK4 : 0 ≤ E.KH ^ 4 := by positivity
    have h2 : Nf ^ 2 * E.rho ^ 2 * E.aScat ^ 6 * E.KH ^ 4
        ≤ (K₀ ^ 2 * (E.Kl * E.KL) ^ 6) * ((2 : ℝ) ^ 6 * E.mu ^ 2)
          * E.aScat ^ 6 * E.KH ^ 4 := by
      calc Nf ^ 2 * E.rho ^ 2 * E.aScat ^ 6 * E.KH ^ 4
          = (Nf ^ 2 * E.rho ^ 2) * (E.aScat ^ 6 * E.KH ^ 4) := by ring
        _ ≤ ((K₀ ^ 2 * (E.Kl * E.KL) ^ 6) * ((2 : ℝ) ^ 6 * E.mu ^ 2))
              * (E.aScat ^ 6 * E.KH ^ 4) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (K₀ ^ 2 * (E.Kl * E.KL) ^ 6) * ((2 : ℝ) ^ 6 * E.mu ^ 2)
              * E.aScat ^ 6 * E.KH ^ 4 := by ring
    have h3 : (K₀ ^ 2 * (E.Kl * E.KL) ^ 6) * ((2 : ℝ) ^ 6 * E.mu ^ 2)
          * E.aScat ^ 6 * E.KH ^ 4
        = (2 : ℝ) ^ 6 * K₀ ^ 2 * (E.Kl * E.KL) ^ 6 * E.lille ^ 2 := by
      rw [h𝓁]; ring
    linarith [h2, h3.le, h3.ge]
  -- conclusion
  have hA1 : (8 * Nf / E.lille ^ 2) *
        ((2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4 * (eta E) ^ 2
          * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4)
      = 8 * Nf * ((2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4 * (eta E) ^ 2
          * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4) / E.lille ^ 2 := by ring
  rw [hA1, div_le_iff₀ (by positivity : (0 : ℝ) < E.lille ^ 2), costB3]
  have hgoal1 : 8 * Nf * ((2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4 * (eta E) ^ 2
        * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4)
      = (2 : ℝ) ^ 41 * Nf ^ 2 * K₀ ^ 9 * E.lille ^ 4 * (eta E) ^ 2
        * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4 := by ring
  have hgoal2 : 2048 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2
        * E.rho * E.aScat * E.lille ^ 2
      = (2 : ℝ) ^ 47 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 6 * (eta E) ^ 2
        * E.rho * E.aScat := by ring
  rw [hgoal1, hgoal2]
  have hsufficient : (2 : ℝ) ^ 41 * Nf ^ 2 * K₀ ^ 9 * E.lille ^ 4 * (eta E) ^ 2
        * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4
      ≤ (2 : ℝ) ^ 47 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 6 * (eta E) ^ 2
        * E.rho * E.aScat := by
    have hc : 0 ≤ (2 : ℝ) ^ 41 * K₀ ^ 9 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat :=
      by positivity
    have hfull := mul_le_mul_of_nonneg_left hkey hc
    have e1 : (2 : ℝ) ^ 41 * K₀ ^ 9 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat
          * (Nf ^ 2 * E.rho ^ 2 * E.aScat ^ 6 * E.KH ^ 4)
        = (2 : ℝ) ^ 41 * Nf ^ 2 * K₀ ^ 9 * E.lille ^ 4 * (eta E) ^ 2
          * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4 := by ring
    have e2 : (2 : ℝ) ^ 41 * K₀ ^ 9 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat
          * ((2 : ℝ) ^ 6 * K₀ ^ 2 * (E.Kl * E.KL) ^ 6 * E.lille ^ 2)
        = (2 : ℝ) ^ 47 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 6 * (eta E) ^ 2
          * E.rho * E.aScat := by ring
    linarith [hfull, e1.le, e1.ge, e2.le, e2.ge]
  exact hsufficient

/-! ## 5. The assembly -/

theorem Wb2_bound (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
        (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          - (Work.BoseC3QAll.Est1.costB3 K₀ E) * F.normSq Φ
              - (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
            ≤ F.qw Φ (Work.BoseC3QAll.Est1.Wb2 F T E) := by
  obtain ⟨t₁, ht₁, h₁⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, h₂⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t₃, ht₃, h₃⟩ := q3Denom_le_four K₀ b₀ hb₀
  obtain ⟨t₄, ht₄, h₄⟩ := wb2_coef_sum_aux K₀ b₀ hb₀
  obtain ⟨t₅, ht₅, h₅⟩ := wb2_reserve_dom_aux K₀ b₀ hb₀
  refine ⟨min t₁ (min t₂ (min t₃ (min t₄ t₅))),
    lt_min ht₁ (lt_min ht₂ (lt_min ht₃ (lt_min ht₄ ht₅))), ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK Φ hΦ
  have hle₁ : hv.t ≤ t₁ := le_trans htle (min_le_left _ _)
  have hle₂ : hv.t ≤ t₂ :=
    le_trans htle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hle₃ : hv.t ≤ t₃ :=
    le_trans htle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hle₄ : hv.t ≤ t₄ :=
    le_trans htle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hle₅ : hv.t ≤ t₅ :=
    le_trans htle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  obtain ⟨hαeven, hAB, hHalf, hαle, hDq⟩ := h₁ F T E hv hle₁ hb hK
  obtain ⟨hPHsub, hsubPHq, -⟩ := h₂ F T E hv hle₂ hb hK
  have hDen4 := h₃ F T E hv hle₃ hb hK
  have hcoefSum := h₄ F T E hv hle₄ hb hK
  have hresSum := h₅ F T E hv hle₅ hb hK Φ
  -- scalars
  have ha : 0 < E.aScat := hv.a_pos
  have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hKl : 0 < E.Kl := lt_of_lt_of_le one_pos hv.one_le_Kl
  have hKL : 0 < E.KL := lt_of_lt_of_le one_pos hv.one_le_KL
  have hell : 0 < E.ell := ell_pos E hv
  have hmu : 0 < E.mu := mu_pos E hv
  have hlille : 0 < E.lille := lille_pos E hv
  have hρ : 0 < E.rho := rho_pos E hv
  have hKℓKL : 0 < E.Kl * E.KL := mul_pos hKl hKL
  have hK0 : 0 ≤ K₀ := by
    have h := hK.sum_hatChiSq
    have hnn : 0 ≤ ∑ s ∈ (excited Mode), |E.hatChiSq s| :=
      Finset.sum_nonneg fun s _ => abs_nonneg _
    linarith
  have hη : 0 ≤ Work.BoseC3QAll.eta E := by
    rw [eta]
    exact Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hKl.le _) hlille.le) _
  have hDnn : ∀ q : Mode, F.PHq E.KH E.aScat q → 0 < E.D q := by
    intro q hq
    have hcut : 1 / (4 * E.KH * E.aScat) ≤ ‖F.kmom q‖ := hq
    have hpos : 0 < ‖F.kmom q‖ := lt_of_lt_of_le (by positivity) hcut
    have := hDq q hq
    nlinarith [sq_nonneg ‖F.kmom q‖]
  -- the reserve, as a sum
  have hRq : F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
      = ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) := by
    rw [FockData.qw, bp_dNumOpR]
    exact Finset.sum_congr rfl fun q _ => by
      rw [FockData.bNumOp, LinearMap.comp_apply, bp_bOpDag]
  by_cases hNf0 : (suppL E).card = 0
  · -- degenerate case: the word vanishes
    have hS : suppL E = ∅ := Finset.card_eq_zero.mp hNf0
    have hW0 : F.qw Φ (Wb2 F T E) = 0 := by
      rw [Wb2, hS]
      simp only [Finset.sum_empty, FockData.qw, LinearMap.zero_apply, map_zero]
    rw [hW0, hRq]
    have hresnn : 0 ≤ ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
        E.D q * F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) :=
      Finset.sum_nonneg fun q hq =>
        mul_nonneg (le_of_lt (hDnn q (Finset.mem_filter.mp hq).2)) (F.bp_nonneg _)
    have hcostnn : 0 ≤ costB3 K₀ E := by
      rw [costB3]
      positivity
    have hns : 0 ≤ F.normSq Φ := F.normSq_nonneg Φ
    have hl2 : 0 ≤ E.lille ^ 2 / 8 := by positivity
    nlinarith [hresnn, hcostnn, hns, hl2]
  · -- main case
    have hNf1 : (1 : ℝ) ≤ ((suppL E).card : ℝ) := by
      have : 0 < (suppL E).card := Nat.pos_of_ne_zero hNf0
      exact_mod_cast this
    set Nf : ℝ := ((suppL E).card : ℝ) with hNfdef
    have hNfpos : 0 < Nf := by rw [hNfdef]; linarith
    have hNfK : Nf ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
      rw [hNfdef]; exact suppL_card_le hK
    set eps : ℝ := E.lille ^ 2 / (8 * Nf) with hepsdef
    have heps : 0 < eps := by rw [hepsdef]; positivity
    have hDpos' : ∀ s ∈ suppL E, ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → 0 < E.D (s - k) :=
      fun s hs k hk hW => hDnn (s - k) (hsubPHq s k (suppL_fL_ne_zero hs) hk hW)
    -- the quadratic form of the word
    have hqw : F.qw Φ (Wb2 F T E) = ∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
        wb2coef F T E s k * (2 * F.bp (F.bOp E.alpha (s - k) Φ) Φ) := by
      rw [wb2coef_expand, qw_double_sum_aux]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
      rw [qw_bOp_add_aux F E.alpha (s - k) Φ]
    -- the coefficient bound
    have hcoefb : ∑ s ∈ suppL E, ∑ k ∈ F.PHset E, wb2coef F T E s k ^ 2 / E.D (s - k)
        ≤ (2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4 * (Work.BoseC3QAll.eta E) ^ 2
            * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4 := by
      simpa only [wb2coef, ← hNfdef] using hcoefSum
    -- the reserve bound
    have hresb : ∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)
        ≤ Nf * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
      rw [hRq]
      simpa only [← hNfdef] using hresSum
    -- the arithmetic
    have harith : (8 * Nf / E.lille ^ 2) *
        ((2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4 * (Work.BoseC3QAll.eta E) ^ 2
          * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4) ≤ costB3 K₀ E :=
      wb2_arith_aux K₀ hK0 E hv (by rw [hNfdef]; exact hNf1) hNfK
    -- bridges: the sums over `PHset` agree with the sums over its `Ŵ₁ ≠ 0` part
    have hwb0 : ∀ s k : Mode, E.W1 k = 0 → wb2coef F T E s k = 0 := by
      intro s k h0
      rw [wb2coef, gA, h0]
      ring
    have hword_filt : (∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
          wb2coef F T E s k * (2 * F.bp (F.bOp E.alpha (s - k) Φ) Φ))
        = ∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          wb2coef F T E s k * (2 * F.bp (F.bOp E.alpha (s - k) Φ) Φ) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      refine (Finset.sum_filter_of_ne ?_).symm
      intro k hk hf
      intro h0
      exact hf (by rw [hwb0 s k h0]; simp)
    have hcoef_filt : (∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
          wb2coef F T E s k ^ 2 / (eps * E.D (s - k)))
        = ∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          wb2coef F T E s k ^ 2 / (eps * E.D (s - k)) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      refine (Finset.sum_filter_of_ne ?_).symm
      intro k hk hf
      intro h0
      exact hf (by rw [hwb0 s k h0]; simp)
    have hcoef_filt_D : (∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
          wb2coef F T E s k ^ 2 / E.D (s - k))
        = ∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          wb2coef F T E s k ^ 2 / E.D (s - k) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      refine (Finset.sum_filter_of_ne ?_).symm
      intro k hk hf
      intro h0
      exact hf (by rw [hwb0 s k h0]; simp)
    -- the rescaled coefficient sum
    have hsum_range : ∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
        wb2coef F T E s k ^ 2 / (eps * E.D (s - k)) ≤ costB3 K₀ E := by
      rw [hcoef_filt]
      have h1 : (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
            wb2coef F T E s k ^ 2 / (eps * E.D (s - k)))
          = (1 / eps) * (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
              wb2coef F T E s k ^ 2 / E.D (s - k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
        exact div_mul_div_eq _ _ _ (ne_of_gt heps) (ne_of_gt (hDpos' s hs k hk1 hk2))
      have h2 : (1 / eps) * (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
            wb2coef F T E s k ^ 2 / E.D (s - k))
          ≤ (1 / eps) * ((2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4
              * (Work.BoseC3QAll.eta E) ^ 2
              * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
              wb2coef F T E s k ^ 2 / E.D (s - k))
            ≤ ∑ s ∈ suppL E, ∑ k ∈ F.PHset E, wb2coef F T E s k ^ 2 / E.D (s - k) :=
              le_of_eq hcoef_filt_D.symm
          _ ≤ (2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4
                * (Work.BoseC3QAll.eta E) ^ 2
                * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4 := hcoefb
      have h3 : (1 / eps) * ((2 : ℝ) ^ 38 * K₀ ^ 9 * Nf * E.lille ^ 4
              * (Work.BoseC3QAll.eta E) ^ 2
              * E.rho ^ 3 * E.aScat ^ 7 * E.KH ^ 4) ≤ costB3 K₀ E := by
        have h4 : 1 / eps = 8 * Nf / E.lille ^ 2 := by
          rw [hepsdef]
          field_simp
        rw [h4]
        exact harith
      linarith [h1.le, h1.ge, h2, h3]
    -- the rescaled reserve sum
    have hsum_res : eps * (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
        ≤ (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
      have h1 : eps * (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
            E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ))
          ≤ eps * (Nf * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))) :=
        mul_le_mul_of_nonneg_left hresb heps.le
      have h2 : eps * (Nf * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)))
          = (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
        rw [hepsdef]
        field_simp
      linarith [h1, h2.le, h2.ge]
    -- the per-pair sum: the reserve is summed only over the modes with `Ŵ₁ k ≠ 0`
    -- (the modes with `Ŵ₁ k = 0` contribute nothing to the word)
    have hpairsum : -(eps * (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
            E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)))
          - (∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
              wb2coef F T E s k ^ 2 / (eps * E.D (s - k))) * F.bp Φ Φ
        ≤ ∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
            wb2coef F T E s k * (2 * F.bp (F.bOp E.alpha (s - k) Φ) Φ) := by
      have hper : ∀ s ∈ suppL E, ∀ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
          -(eps * (E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)))
            - (wb2coef F T E s k ^ 2 / (eps * E.D (s - k))) * F.bp Φ Φ
          ≤ wb2coef F T E s k * (2 * F.bp (F.bOp E.alpha (s - k) Φ) Φ) := by
        intro s hs k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
        have hD := hDpos' s hs k hk1 hk2
        have h := wb2_pair_absorb_aux (c := wb2coef F T E s k) F E.alpha (s - k) Φ heps hD
        rw [show F.bp ((F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k)) Φ) Φ
              = 2 * F.bp (F.bOp E.alpha (s - k) Φ) Φ from
                qw_bOp_add_aux F E.alpha (s - k) Φ] at h
        linarith [h]
      have h1 : (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
            ( -(eps * (E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)))
              - (wb2coef F T E s k ^ 2 / (eps * E.D (s - k))) * F.bp Φ Φ ))
          ≤ ∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
              wb2coef F T E s k * (2 * F.bp (F.bOp E.alpha (s - k) Φ) Φ) :=
        Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun k hk => hper s hs k hk
      have hsplit : (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
            ( -(eps * (E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)))
              - (wb2coef F T E s k ^ 2 / (eps * E.D (s - k))) * F.bp Φ Φ ))
          = -(eps * (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
                E.D (s - k) * F.bp (F.bOp E.alpha (s - k) Φ) (F.bOp E.alpha (s - k) Φ)))
              - (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
                  wb2coef F T E s k ^ 2 / (eps * E.D (s - k))) * F.bp Φ Φ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
          Finset.sum_mul]
      have hK : (∑ s ∈ suppL E, ∑ k ∈ (F.PHset E).filter (fun k => E.W1 k ≠ 0),
            wb2coef F T E s k ^ 2 / (eps * E.D (s - k))) * F.bp Φ Φ
          ≤ (∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
              wb2coef F T E s k ^ 2 / (eps * E.D (s - k))) * F.bp Φ Φ :=
        mul_le_mul_of_nonneg_right (le_of_eq hcoef_filt.symm) (F.bp_nonneg Φ)
      linarith [h1, hsplit.le, hsplit.ge, hK, hword_filt.le, hword_filt.ge]
    -- conclusion
    have hWnn : 0 ≤ F.bp Φ Φ := F.bp_nonneg Φ
    have hA : (∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
          wb2coef F T E s k ^ 2 / (eps * E.D (s - k))) * F.bp Φ Φ
        ≤ costB3 K₀ E * F.bp Φ Φ := mul_le_mul_of_nonneg_right hsum_range hWnn
    rw [hqw]
    have hns : F.normSq Φ = F.bp Φ Φ := rfl
    rw [hns]
    linarith [hpairsum, hA, hsum_res, hWnn]

end Work.BoseC3QAll.Est1
