import Submission.Work.ConeSwitch.Vocab

/-!
# §12, the Type-A₁ branch with free `(ρ, ε)`

`ErdosFaberLovaszConjecture.s12_branch_A1` (`Submission/EFL/S12MainA.lean`) is the paper's
Type-A₁ argument, but its parameters are pinned to the `σ`-hierarchy: the fullness parameter is
`σ³/10⁴²`, the density is `σ/2`, and every numeric side condition comes from the `S12ANum`
bundle.  That is *not* the form the faithful endgame needs: to consume the faithful
Theorem 10.8 (`GKOStatement`) the §12 A₂ branch must be run at a fullness parameter `ε` chosen
*below the GKO threshold* `ε₀`, and the case split on `IsFull 𝓗 ρ ε` must then be taken at that
same free `(ρ, ε)` — otherwise a graph that is `(ρ,ε)`-full at the free parameter but not at the
pinned one falls outside both branches (the paper's own §12 has *both* cases parametric, which
is why it has no such gap).

This module supplies the missing parametric Type-A₁ branch
`Work.ConeSwitch.s12_branch_A1_faithful`: the same proof as `s12_branch_A1`, with

* `ρ` (density) and `ε` (fullness) free, the absorber density `ρ_abs = ρ/2` (so the numeric
  input is exactly `Work.S12Faithful.S12A2Data`, whose fields are the §12 conditions with
  `σ/2 ↦ ρ`, `σ³/10⁴² ↦ ε`),
* the not-full hypothesis `¬ IsFull 𝓗 ρ ε` (used, as in `S_big_typeA1`, only to produce the
  `S`-is-big implication — vacuously when `U` is small),
* the Type-A₁ reservoir `IsReservoirTypeA1 𝓗 R_res 𝓥 ρ ξ ε` and the Vizing finishing
  (`s12_main_A1`), in place of the Type-A₂ reservoir and the Corollary 10.13 finishing.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Two monotonicity facts for the absorber density

`HugeMargins n ρ ε γ κ ξ` (and hence `S12Margins`, `LeftoverMargins`) is *increasing* in `ρ`:
every field is either `ρ > 0`, `ρ ≤ 1` (both fine for a larger `ρ ≤ 1`) or a lower bound on `ρ`.
This lets a bundle stated at the Type-A₂ absorber density `ρ/2` (`S12A2Data`) be used at the
Type-A₁ density `ρ`, which is what `s12_step2_typeA1` produces. -/

/-- `HugeMargins` is monotone in the density `ρ`. -/
theorem HugeMargins.mono_rho {n : ℕ} {ρ ρ' ε γ κ ξ : ℝ} (h : HugeMargins n ρ ε γ κ ξ)
    (hle : ρ ≤ ρ') (h1 : ρ' ≤ 1) : HugeMargins n ρ' ε γ κ ξ :=
  { hρ := lt_of_lt_of_le h.hρ hle, hρ1 := h1, hε := h.hε, hγ := h.hγ, hκ := h.hκ, hξ := h.hξ,
    hεsmall := h.hεsmall,
    hγε := by nlinarith only [h.hγε, h.hε, le_of_lt h.hρ, hle],
    hnbig := by
      have h2 : γ * ρ * (n : ℝ) ≤ γ * ρ' * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) n)
        exact mul_le_mul_of_nonneg_left hle (le_of_lt h.hγ)
      linarith only [h.hnbig, h2],
    hξγρ := by
      have h2 : γ * ρ ≤ γ * ρ' := mul_le_mul_of_nonneg_left hle (le_of_lt h.hγ)
      linarith only [h.hξγρ, h2] }

/-- The §7 margin bundle `NibbleMarginsStrong` is monotone in its density argument `ρ`
(the only field that is *harder* for a larger `ρ` is `hDgap : D ≤ (1-ρ)n`, which is therefore
an extra hypothesis). -/
theorem NibbleMarginsStrong.mono_rho {n : ℕ} {D : ℝ} {r : ℕ} {β γ ε ρ ρ' ξ : ℝ}
    (h : NibbleMarginsStrong n D r β γ ε ρ ξ) (hρρ' : ρ ≤ ρ') (hρ'1 : ρ' ≤ 1)
    (hDgap' : D ≤ (1 - ρ') * (n : ℝ)) :
    NibbleMarginsStrong n D r β γ ε ρ' ξ :=
  { base :=
      { hn := h.base.hn, hr := h.base.hr, hβ0 := h.base.hβ0, hγ0 := h.base.hγ0,
        hε0 := h.base.hε0, hρ0 := lt_of_lt_of_le h.base.hρ0 hρρ', hξ0 := h.base.hξ0,
        hρ1 := hρ'1, hDlow := h.base.hDlow, hDhigh := h.base.hDhigh, hnr := h.base.hnr,
        hnξ := h.base.hnξ, hnβ := h.base.hnβ, hrγ := h.base.hrγ, hξγ := h.base.hξγ,
        hβγ := h.base.hβγ, hγε := h.base.hγε,
        hγρ := le_trans h.base.hγρ hρρ' }
    hβ := by
      have h1 : γ * ρ * ε ≤ γ * ρ' * ε := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h.base.hε0)
        exact mul_le_mul_of_nonneg_left hρρ' (le_of_lt h.base.hγ0)
      have h2 : (γ * ρ * ε) ^ 2 ≤ (γ * ρ' * ε) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (mul_nonneg h.base.hγ0.le h.base.hρ0.le) h.base.hε0.le)
          h1 2
      linarith only [h.hβ, h2]
    hβ4 := h.hβ4
    hξ := by
      have h1 : γ * ρ * ε ≤ γ * ρ' * ε := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h.base.hε0)
        exact mul_le_mul_of_nonneg_left hρρ' (le_of_lt h.base.hγ0)
      linarith only [h.hξ, h1]
    hξ2 := h.hξ2
    hr := by
      have h1 : γ * ρ * ε * (r : ℝ) ≤ γ * ρ' * ε * (r : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) r)
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h.base.hε0)
        exact mul_le_mul_of_nonneg_left hρρ' (le_of_lt h.base.hγ0)
      linarith only [h.hr, h1]
    hr2 := h.hr2
    hγρ := le_trans h.hγρ hρρ'
    hγρε := by
      have h1 : ρ * ε ≤ ρ' * ε := mul_le_mul_of_nonneg_right hρρ' (le_of_lt h.base.hε0)
      linarith only [h.hγρε, h1]
    hβD := by
      have h1 : γ * ρ * ε * (n : ℝ) ≤ γ * ρ' * ε * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) n)
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h.base.hε0)
        exact mul_le_mul_of_nonneg_left hρρ' (le_of_lt h.base.hγ0)
      linarith only [h.hβD, h1]
    hn := by
      have h1 : γ * ρ * ε * (n : ℝ) ≤ γ * ρ' * ε * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) n)
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h.base.hε0)
        exact mul_le_mul_of_nonneg_left hρρ' (le_of_lt h.base.hγ0)
      linarith only [h.hn, h1]
    hε := h.hε
    hDgap := hDgap'
    hnbig := by
      have hinv : ρ'⁻¹ ≤ ρ⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le h.base.hρ0 hρρ'
      have h2 : (ρ'⁻¹) ^ 6 ≤ (ρ⁻¹) ^ 6 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le h.base.hρ0 hρρ'))) hinv 6
      have h4 : γ * ρ * ε ≤ γ * ρ' * ε := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h.base.hε0)
        exact mul_le_mul_of_nonneg_left hρρ' (le_of_lt h.base.hγ0)
      have hp : (0 : ℝ) < γ * ρ * ε :=
        mul_pos (mul_pos h.base.hγ0 h.base.hρ0) h.base.hε0
      have h5 : (γ * ρ' * ε)⁻¹ ≤ (γ * ρ * ε)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hp h4
      have h6 : ((γ * ρ' * ε)⁻¹) ^ 2 ≤ ((γ * ρ * ε)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hp h4))) h5 2
      have hS : (ρ'⁻¹) ^ 6 + (γ⁻¹) ^ 16 + (γ * ρ' * ε)⁻¹ + ((γ * ρ' * ε)⁻¹) ^ 2 + (r : ℝ) ≤
          (ρ⁻¹) ^ 6 + (γ⁻¹) ^ 16 + (γ * ρ * ε)⁻¹ + ((γ * ρ * ε)⁻¹) ^ 2 + (r : ℝ) := by
        linarith only [h2, h5, h6]
      have hc : (0 : ℝ) ≤ 10 ^ 400 := by positivity
      have hmult := mul_le_mul_of_nonneg_left hS hc
      linarith only [hmult, h.hnbig]
    hDlin := h.hDlin }

/-- `S12Margins` is monotone in the absorber density `ρ_abs`. -/
theorem S12Margins.mono_rho_abs {n r₁ r₀ : ℕ} {β γ ρ ρ_abs ρ_abs' ξ ε κ : ℝ}
    (h : S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε κ) (hle : ρ_abs ≤ ρ_abs') (h1 : ρ_abs' ≤ 1)
    (hDgap : (Dparam n ρ : ℝ) ≤ (1 - ρ_abs') * (n : ℝ)) :
    S12Margins n r₁ r₀ β γ ρ ρ_abs' ξ ε κ :=
  { h with
    hmHuge := HugeMargins.mono_rho h.hmHuge hle h1
    hnib := NibbleMarginsStrong.mono_rho h.hnib hle h1 hDgap }

/-- `LeftoverMargins` is monotone in the absorber density `ρ_abs`. -/
theorem LeftoverMargins.mono_rho_abs {n r₁ : ℕ} {γ ρ ρ_abs ρ_abs' ε ξ : ℝ}
    (h : LeftoverMargins n r₁ γ ρ ρ_abs ε ξ) (hle : ρ_abs ≤ ρ_abs') (h1 : ρ_abs' ≤ 1) :
    LeftoverMargins n r₁ γ ρ ρ_abs' ε ξ :=
  { h with hm := HugeMargins.mono_rho h.hm hle h1 }

/-- **§12, the Type-A₁ branch with free `(ρ, ε)`.** -/
theorem s12_branch_A1_faithful {𝓗 : Hypergraph (Fin n)} {ρ ε γ β ξ ζ η ηr σ₁ : ℝ}
    {r₁ r₀ : ℕ} {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U : Set (Fin n)}
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) ε ρ ξ n)
    (hdata : S12A2Data n r₁ r₀ β γ ρ ξ ε ζ η ηr)
    (hDlb : (1 - σ₁) * (n : ℝ) ≤ (Dparam n ρ : ℝ))
    (hlin : 𝓗.IsLinear) (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hU : U = Vplus 𝓗 (1 - ε))
    (hA : IsTypeA σ₁ γ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ)
    (hnF : ¬ IsFull 𝓗 ρ ε)
    {R_res R_abs : Hypergraph (Fin n)}
    (hresA1 : IsReservoirTypeA1 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε)
    (hRabs : IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n))) ρ ξ ξ)
    (hRabs_sub : R_abs ⊆ R_res) (hRabs_pow2 : R_abs ⊆ 𝓗.pow2) :
    𝓗.chromaticIndex ≤ n := by
  classical
  -- ## the bundle and the leftover margins at the Type-A₁ absorber density `ρ`
  have hρ1' : ρ ≤ 1 := by linarith only [hdata.hρ100]
  have hle : ρ / 2 ≤ ρ := by linarith only [hdata.hρ0]
  have hDgapρ : (Dparam n ρ : ℝ) ≤ (1 - ρ) * (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdata.hm.hn1
    have hρ0 : 0 < ρ := hdata.hρ0
    rw [Dparam]
    have h3 : (⌊(1 - ρ) * ((n : ℝ) - 1)⌋₊ : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) :=
      Nat.floor_le (by nlinarith only [hρ0, hdata.hρ100, hn0, hn1])
    nlinarith only [h3, hρ0, hdata.hρ100, hn0, hn1]
  have hmρ : S12Margins n r₁ r₀ β γ ρ ρ ξ ε (1 / 2) :=
    S12Margins.mono_rho_abs hdata.hm hle hρ1' hDgapρ
  have hleftρ : LeftoverMargins n r₁ γ ρ ρ ε ξ :=
    LeftoverMargins.mono_rho_abs hdata.hleft hle hρ1'
  have hn1 : 1 ≤ n := hdata.hm.hn1
  have hn2 : 2 ≤ n := le_trans (by norm_num) hdata.hm.hn4
  have hγ1 : γ ≤ 1 := hdata.hγ1
  have hβ1 : β ≤ 1 := le_trans hdata.hβγ hγ1
  have hγsqrt1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
  have hρhalf : ρ ≤ 1 / 2 := by linarith only [hdata.hρ100]
  -- ## Step 3
  obtain ⟨Cmed, Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hsing, hVn2U, hVn1char,
    hVn2char, hvert, h3R, hCl⟩ :=
    s12_step3_typeA (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (σ := σ₁)
      (γ₁ := γ) (β := β) (γ := γ) (ρ := ρ) (ε := ε)
      hlin hbig hA le_rfl hdata.hβ0 hdata.hm.hβn hn2 hdata.hm.hr₁β hdata.hεn3 hU
      hdata.hnum3 hDlb
  -- ## Step 4
  have hRabs10 : IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n)))
      ρ (10 * ξ) ξ := IsAbsorber.mono_gamma hRabs (by linarith [hdata.hm.hξ0])
  have hDM : DiffMargins n β :=
    ⟨hdata.hβ0, hβ1, by nlinarith only [hdata.hm.hmDeg.hβn]⟩
  have hbig' : ∀ f ∈ 𝓗, 2 ≤ f.ncard := fun f hf => by
    have h := hbig f hf
    rwa [edgeSize_eq_ncard] at h
  have hξγ : 10 * ξ + 1 / (n : ℝ) ≤ 3 * γ / 2 := by
    have h := hdata.hξsharp
    linarith only [h, hdata.hγ0]
  rcases s12_step4_inst (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (σ := σ₁)
      (γ₁ := γ) (β := β) (γ := γ) (ρ := ρ) (ρ_abs := ρ) (ξ := ξ)
      (ε := ε) hlin hbig' hU hS12 hA hDM hn1 hξγ hRabs10 with
      hχ | ⟨Mdiff, R₁, S₁, hstep4⟩
  · exact hχ
  · -- ## the sharp absorber `R₁`
    have hR₁sharp : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
        ρ (10 * ξ + 1 / (n : ℝ)) ξ :=
      IsAbsorber.delete_step4 hRabs10 hstep4 hS12.hCdiff_card hn1
    -- ## the numeric hypotheses
    have hVn1U : Vn1set 𝓗 ⊆ U := fun v hv => hVn2U (Vn1set_subset_Vn2set 𝓗 hv)
    have hS_big := S_big_typeA1 hlin hbig hU hnF hVn1U
    have hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅ := fun c hc =>
      colourFam_eq_empty (hS12.class_eq_empty_of_buff_union_final hCl c
        (Finset.mem_union_right Cbuff hc))
    have hγs : γ ≤ Real.sqrt γ := hdata.hγs
    have hX : (((Cmed ∪ Cdiff ∪ Chuge).card : ℕ) : ℝ) ≤ 5 * Real.sqrt γ * (n : ℝ) := by
      have hk2 := hdata.hm.hk2
      have h6 : 3 * γ * (n : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
        nlinarith only [hγs, Real.sqrt_nonneg γ, Nat.cast_nonneg (α := ℝ) n]
      linarith only [h3R, hk2, h6]
    have hUCnum1 : ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ) ≤
        (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 2 := by
      have hcfg := hS12.card_final_ge hX hdata.hρ0 (by linarith only [hdata.hρ100]) hn1
      have h15 := hdata.h15ρ
      have h15' : (15 * Real.sqrt γ + ξ) * (n : ℝ) ≤ (ρ * ε / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right h15 (Nat.cast_nonneg (α := ℝ) n)
      nlinarith only [hcfg, h15']
    have hUCnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤ ρ * ε * (n : ℝ) / 4 := by
      have h8 := hdata.h8r₀
      have h8' : (2 : ℝ) ≤ ρ * ε * (r₀ : ℝ) / 4 := by linarith only [h8]
      have hr0 : (0 : ℝ) < (r₀ : ℝ) := by
        have := hdata.hm.hr₀2
        exact_mod_cast (by omega : 0 < r₀)
      rw [div_le_iff₀ hr0]
      nlinarith only [h8', Nat.cast_nonneg (α := ℝ) n]
    have hDn : (Dparam n ρ : ℝ) ≤ (n : ℝ) := by
      have h1 := hdata.hnum3
      have h2 : (0 : ℝ) ≤ (D'param (Dparam n ρ) γ : ℝ) := Nat.cast_nonneg _
      have h3 : (0 : ℝ) ≤ 2 * γ * (n : ℝ) := by
        have := hdata.hγ0; positivity
      have h4 : (0 : ℝ) ≤ 32 / β ^ 2 := by positivity
      linarith only [h1, h2, h3, h4]
    have hdeficitNum : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) +
        2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ) := by
      have hk2 := hdata.hm.hk2
      have hCbuff : ((Cbuff.card : ℕ) : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
        rw [hS12.hCbuff_card]
        have h2 : (D'param (Dparam n ρ) γ : ℝ) ≤ 10 * Real.sqrt γ * (Dparam n ρ : ℝ) := by
          rw [D'param]
          exact Nat.floor_le (by positivity)
        have h4 : 10 * Real.sqrt γ * (Dparam n ρ : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hDn (by positivity)
        linarith only [h2, h4]
      have hCmain : ((Cmain.card : ℕ) : ℝ) ≤ (n : ℝ) := by
        rw [hS12.hCmain_card]
        exact hDn
      have hset : (Cdiff ∪ Chuge ∪ Cmed) = (Cmed ∪ Cdiff ∪ Chuge) := by
        ext x; simp only [Finset.mem_union]; tauto
      have h3R' : (((Cdiff ∪ Chuge ∪ Cmed).card : ℕ) : ℝ) ≤ γ * (n : ℝ) + 32 / β ^ 2 := by
        rw [hset]; exact h3R
      have hcard_union : (Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card ≤
          (Cdiff ∪ Chuge ∪ Cmed).card + Cbuff.card := Finset.card_union_le _ _
      have h1 : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) ≤
          (((Cdiff ∪ Chuge ∪ Cmed).card : ℕ) : ℝ) + ((Cbuff.card : ℕ) : ℝ) := by
        exact_mod_cast hcard_union
      have hfin : γ * (n : ℝ) + 32 / β ^ 2 + 10 * Real.sqrt γ * (n : ℝ) + 2 * γ * (n : ℝ) ≤
          15 * Real.sqrt γ * (n : ℝ) := by
        nlinarith only [hk2, hγs, hdata.hγ0, Real.sqrt_nonneg γ, Nat.cast_nonneg (α := ℝ) n]
      have hCmain' : 2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 2 * γ * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hCmain (by have := hdata.hγ0; positivity)
      linarith only [h1, h3R', hCbuff, hCmain', hfin]
    have hk1 : 1 ≤ Cfinal.card :=
      one_le_card_Cfinal hS12 hX hdata.hρ0 (by linarith only [hdata.hρ100]) hn1 hdata.h30
        (by linarith only [hdata.hρn25])
    have hnum : 1 ≤ ρ * ε * (n : ℝ) / 4 := one_le_rho_eps_mul hdata.h4ρεn
    exact s12_main_A1 (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
      (ρ_abs := ρ) (ξ := ξ) (ε := ε) (κ := 1 / 2) (φ := φ) (U := U)
      (S := U \ Vn1set 𝓗) (S₁ := S₁) (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge)
      (Clarge := Clarge) (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal)
      (R_res := R_res) (R_abs := R_abs) (R₁ := R₁) (Mdiff := Mdiff)
      hlin hbig hNib hleftρ hS12 hsing hvert hresA1 mem_cvFinset_univ mem_cvFinset_U hU
      hstep4 hRabs_pow2 hR₁sharp (by linarith only [hdata.hξsharp, hdata.hγ0]) Set.sdiff_subset
      hS_big hmρ hRabs_sub hVn2U hUCnum1 hUCnum2 hdeficitNum hT1
      (fun v hv hmem => (hstep4.hS₁_sub hmem).2 hv) hk1 hnum

end

end ErdosFaberLovaszConjecture
