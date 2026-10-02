import Submission.Work.S12Faithful.Data

/-!
# The faithful Type-A₂ branch of §12

`Work.S12Faithful.s12_branch_A2_faithful` is `ErdosFaberLovaszConjecture.s12_branch_A2`
(`Submission/EFL/S12MainA2.lean:242`) with the master constant `σ` removed: the
parameters `ρ` (A₂ density), `ε` (fullness), `ζ` (lower-regularity parameter fed to
Corollary 10.13) and `η` (its discrepancy parameter) are *free*, subject only to the
explicitly listed numeric side conditions bundled in `Work.S12Faithful.S12A2Data`.

The proof is the same chain as in `S12MainA2.lean` and feeds the *unchanged* generic
lemmas `s12_to_S12Out` and `s12_finish_A2_gen`; the only differences are that

* `σ/2 ↦ ρ`, `σ/4 ↦ ρ/2`, `σ³/10⁴² ↦ ε`, `σ/10¹⁴ ↦ ζ`, `22σ³/10⁴² ↦ η`,
  `σ/10³⁰ ↦ ηr` (the robustness parameter of `stat:r_rem`);
* every numeric fact that `S12ANum` derived from `σ ≤ 10⁻²⁴` is now a field of
  `S12A2Data`;
* the `hcor` hypothesis (Corollary 10.13 at `(ρ/4, ζ, η)`) is taken as given; the
  caller instantiates it from the *faithful* (existential-threshold) Theorem 10.8
  via `SelfLowerRegular.mono`, see `Work.S12Faithful.s12_A2_main_faithful`.

The parameters `σ₁` (of `IsTypeA`) and `ρ` are now *independent*; the only link is
the Step-3 hypothesis `(1-σ₁)n ≤ Dparam n ρ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **§12, the faithful Type-A₂ branch.**  Given the numeric data `S12A2Data`, a Type-A
colouring with parameters `(σ₁, γ, β, r₁, r₀)`, `(ρ,ε)`-fullness, the Type-A₂ reservoir
data and Corollary 10.13 at `(ρ/4, ζ, η)`, the chromatic index of `𝓗` is at most `n`. -/
theorem s12_branch_A2_faithful {𝓗 : Hypergraph (Fin n)} {ρ ε γ β ξ ζ η ηr σ₁ : ℝ}
    {r₁ r₀ : ℕ} {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U : Set (Fin n)}
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) ε (ρ / 2) ξ n)
    (hdata : S12A2Data n r₁ r₀ β γ ρ ξ ε ζ η ηr)
    (hDlb : (1 - σ₁) * (n : ℝ) ≤ (Dparam n ρ : ℝ))
    (hlin : 𝓗.IsLinear) (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hU : U = Vplus 𝓗 (1 - ε))
    (hA : IsTypeA σ₁ γ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ)
    (hfull : IsFull 𝓗 ρ ε)
    {R_res R_abs : Hypergraph (Fin n)}
    (hRres_pow2 : R_res ⊆ 𝓗.pow2)
    (hRabs : IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n)))
      (ρ / 2) ξ ξ)
    (hRabs_low : LowerRegular (incidentTwo 𝓗 U) R_abs (ρ / 2) ξ)
    (hRabs_sub : R_abs ⊆ R_res) (hRabs_pow2 : R_abs ⊆ 𝓗.pow2)
    (hregres : ∃ Rreg : Hypergraph (Fin n),
      R_res = R_abs ∪ Rreg ∧ IsRegularising 𝓗 R_abs Rreg ρ ξ ε)
    (hcor : ∀ 𝓖 : Hypergraph (Fin n), (∀ e ∈ 𝓖, edgeSize e = 2) →
      SelfLowerRegular 𝓖 Set.univ (ρ / 4) ζ →
      (∀ v : Fin n, ((hypergraphMaxDegree 𝓖 : ℝ) - (degAt 𝓖 v : ℝ)) ≤ η * (n : ℝ)) →
      (({v : Fin n | degAt 𝓖 v < hypergraphMaxDegree 𝓖}.ncard : ℝ) ≥
        (hypergraphMaxDegree 𝓖 : ℝ)) →
      𝓖.Colorable (hypergraphMaxDegree 𝓖)) :
    𝓗.chromaticIndex ≤ n := by
  classical
  have hn1 : 1 ≤ n := hdata.hm.hn1
  have hn2 : 2 ≤ n := le_trans (by norm_num) hdata.hm.hn4
  have hρ4 : ρ ≤ 1 / 4 := by linarith only [hdata.hρ100]
  have hβ1 : β ≤ 1 := le_trans hdata.hβγ hdata.hγ1
  have hγsqrt1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hdata.hγ1
  have hγs : γ ≤ Real.sqrt γ := hdata.hγs
  -- ## Step 3
  obtain ⟨Cmed, Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hsing, hVn2U, hVn1char,
    hVn2char, hvert, h3R, hCl⟩ :=
    s12_step3_typeA (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (σ := σ₁)
      (γ₁ := γ) (β := β) (γ := γ) (ρ := ρ) (ε := ε)
      hlin hbig hA le_rfl hdata.hβ0 hdata.hm.hβn hn2 hdata.hm.hr₁β hdata.hεn3 hU
      hdata.hnum3 hDlb
  -- ## Step 4
  have hRabs10 : IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n)))
      (ρ / 2) (10 * ξ) ξ := IsAbsorber.mono_gamma hRabs (by linarith [hdata.hm.hξ0])
  have hDM : DiffMargins n β := ⟨hdata.hβ0, hβ1, by nlinarith only [hdata.hm.hmDeg.hβn]⟩
  have hbig' : ∀ f ∈ 𝓗, 2 ≤ f.ncard := fun f hf => by
    have h := hbig f hf
    rwa [edgeSize_eq_ncard] at h
  have hξγ : 10 * ξ + 1 / (n : ℝ) ≤ 3 * γ / 2 := by
    have h := hdata.hξsharp
    linarith only [h, hdata.hγ0]
  rcases s12_step4_inst (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (σ := σ₁)
      (γ₁ := γ) (β := β) (γ := γ) (ρ := ρ) (ρ_abs := ρ / 2) (ξ := ξ)
      (ε := ε) (S := U) hlin hbig' hU hS12 hA hDM hn1 hξγ hRabs10 with
      hχ | ⟨Mdiff, R₁, S₁, hstep4⟩
  · exact hχ
  · -- ## the sharp absorber
    have hR₁sharp : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
        (ρ / 2) (10 * ξ + 1 / (n : ℝ)) ξ :=
      IsAbsorber.delete_step4 hRabs10 hstep4 hS12.hCdiff_card hn1
    -- ## the numeric hypotheses
    have hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅ := fun c hc =>
      colourFam_eq_empty (hS12.class_eq_empty_of_buff_union_final hCl c
        (Finset.mem_union_right Cbuff hc))
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
        have h := hdata.hm.hr₀2
        exact_mod_cast (by omega : 0 < r₀)
      rw [div_le_iff₀ hr0]
      nlinarith only [h8', Nat.cast_nonneg (α := ℝ) n]
    have hDn : (Dparam n ρ : ℝ) ≤ (n : ℝ) := by
      have h1 := hdata.hnum3
      have h2 : (0 : ℝ) ≤ (D'param (Dparam n ρ) γ : ℝ) := Nat.cast_nonneg _
      have hg0 := hdata.hγ0
      have h3 : (0 : ℝ) ≤ 2 * γ * (n : ℝ) := by positivity
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
        mul_le_mul_of_nonneg_left hCmain (by
          have hg0 := hdata.hγ0
          positivity)
      linarith only [h1, h3R', hCbuff, hCmain', hfin]
    have hk1 : 1 ≤ Cfinal.card :=
      one_le_card_Cfinal hS12 hX hdata.hρ0 (by linarith only [hdata.hρ100]) hn1 hdata.h30
        (by linarith only [hdata.hρn25])
    have hnum : 1 ≤ ρ * ε * (n : ℝ) / 4 := one_le_rho_eps_mul hdata.h4ρεn
    have hCwLarge : ∀ w : Fin n, ((finalColoursAt φ Cfinal w).card : ℝ) ≤
        2 * (n : ℝ) / (r₀ : ℝ) := fun w => card_finalColoursAt_le_of_T1 hT1 w
    have hS_big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
        (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) ≤ (U.ncard : ℝ) := S_big_typeA2 hdata.h15ε
    -- ## the reservoir data
    obtain ⟨Rreg, hRres_eq, hReg⟩ := hregres
    have hRabs' : IsAbsorber (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) R_abs
        (cvFinset φ U : Set (Set (Fin n))) (ρ / 2) ξ ξ := by
      rw [← hU]; exact hRabs
    have hRabs_low' : LowerRegular (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) R_abs (ρ / 2) ξ := by
      rw [← hU]; exact hRabs_low
    have hresA2 : IsReservoirTypeA2 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε :=
      ⟨hRres_pow2, R_abs, Rreg, hRres_eq, hRabs', hRabs_low', hReg⟩
    -- ## the chain (Steps 5--9)
    obtain ⟨Mprev, R_final, 𝓗fin, hout⟩ :=
      s12_to_S12Out (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
        (ρ_abs := ρ / 2) (ξ := ξ) (ε := ε) (κ := 1 / 2) (φ := φ) (U := U)
        (S := U) (S₁ := S₁) (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge)
        (Clarge := Clarge) (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal)
        (R_res := R_res) (R_abs := R_abs) (R₁ := R₁) (Mdiff := Mdiff)
        hlin hbig hNib hdata.hleft hS12 hsing hvert (Or.inr (Or.inl hresA2)) mem_cvFinset_univ
        mem_cvFinset_U hU hstep4 hRabs_pow2 hR₁sharp (by linarith only [hdata.hξsharp, hdata.hγ0])
        subset_rfl hS_big hdata.hm hRabs_sub hVn2U hCwLarge hUCnum1 hUCnum2 hdeficitNum
    -- ## `stat:r_rem`
    have hdef : ∀ w : Fin n, (degAt (R_abs \ R_final) w : ℝ) ≤ (15 * Real.sqrt γ) * (n : ℝ) := by
      intro w
      have hsub : R_abs \ R_final ⊆ R_res \ R_final :=
        Set.sdiff_subset_sdiff hRabs_sub subset_rfl
      have h3 := hout.hdeficit w
      have h4 : (degAt (R_abs \ R_final) w : ℝ) ≤ (degAt (R_res \ R_final) w : ℝ) := by
        exact_mod_cast degAt_mono hsub w
      linarith only [h3, h4]
    have hfullU : (1 - 10 * ε) * (n : ℝ) ≤ (U.ncard : ℝ) := by
      have h := hfull.1
      rwa [← hU] at h
    have hα0 : (0 : ℝ) ≤ 15 * Real.sqrt γ := by positivity
    have hε10 : 10 * ε ≤ 1 / 2 := by
      have h1 : 1000 * ε ≤ 1 := hdata.hm.hmHuge.hεsmall
      nlinarith only [h1, hdata.hε0]
    have hth : (ξ + Real.sqrt (15 * Real.sqrt γ)) * (n : ℝ) ≤ ηr * (U.ncard : ℝ) := by
      have h2 : ξ + Real.sqrt (15 * Real.sqrt γ) ≤ ηr * (1 - 10 * ε) := by
        have h3 : ηr * (1 / 2) ≤ ηr * (1 - 10 * ε) := by
          nlinarith only [hdata.hηr0, hε10]
        linarith only [hdata.hξεrob, h3]
      have h6 : (0 : ℝ) ≤ 1 - 10 * ε := by linarith only [hε10, hdata.hε0]
      have h7 : (ξ + Real.sqrt (15 * Real.sqrt γ)) * (n : ℝ) ≤
          ηr * ((1 - 10 * ε) * (n : ℝ)) := by
        nlinarith only [h2, h6, Nat.cast_nonneg (α := ℝ) n]
      have h5 : ηr * ((1 - 10 * ε) * (n : ℝ)) ≤ ηr * (U.ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hfullU (le_of_lt hdata.hηr0)
      linarith only [h7, h5]
    have hlr := s12_selfLowerRegular_U (𝓗 := 𝓗) (R_abs := R_abs) (R_final := R_final)
      (U := U) (ρ := ρ) (ξ := ξ) (α := 15 * Real.sqrt γ) (ξ' := ηr)
      (ε := ε) (by rw [hU]) (le_of_lt hdata.hε0)
      hRabs_low hdef hα0
      (by nlinarith only [hfullU, hε10, Nat.cast_nonneg (α := ℝ) n])
      (le_of_lt hdata.hξ0) (le_of_lt hdata.hηr0) (le_of_lt hdata.hρ0) hth
      hdata.hsqrtε hdata.hnumα
    have hcard : ((Set.univ : Set (Fin n)).ncard : ℝ) ≤
        (1 + (1 / 10 ^ 4) * ηr) * (U.ncard : ℝ) := by
      have h1 : (Set.univ : Set (Fin n)).ncard = n := by simp
      rw [h1]
      have h6 := mul_le_mul_of_nonneg_right hdata.hcardc (Nat.cast_nonneg (α := ℝ) n)
      have h4 : (0 : ℝ) ≤ 1 + (1 / 10 ^ 4) * ηr := by
        have he0 := hdata.hηr0
        have h5 : (0 : ℝ) ≤ (1 / 10 ^ 4) * ηr := by positivity
        linarith only [h5]
      have h7 : (1 + (1 / 10 ^ 4) * ηr) * ((1 - 10 * ε) * (n : ℝ)) ≤
          (1 + (1 / 10 ^ 4) * ηr) * (U.ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hfullU h4
      calc (n : ℝ) = 1 * (n : ℝ) := by ring
        _ ≤ ((1 + (1 / 10 ^ 4) * ηr) * (1 - 10 * ε)) * (n : ℝ) := h6
        _ = (1 + (1 / 10 ^ 4) * ηr) * ((1 - 10 * ε) * (n : ℝ)) := by ring
        _ ≤ (1 + (1 / 10 ^ 4) * ηr) * (U.ncard : ℝ) := h7
    have hαt0 : (0 : ℝ) ≤ 1 / 10 ^ 4 := by norm_num
    have hαt1 : (1 / 10 ^ 4 : ℝ) < 1 := by norm_num
    have hreg : SelfLowerRegular R_final Set.univ (ρ / 4) ζ :=
      s12_lowerRegular_final_gen (R_final := R_final) (U := U) (ρ := ρ)
        (η := ηr) (αt := 1 / 10 ^ 4) (ζ := ζ)
        hcard hlr hαt0 hαt1 hdata.hηr0 hdata.hnum1 hdata.hnum2
    have hub : ∀ w : Fin n, (degAt R_res w : ℝ) ≤ (ρ + ξ) * (n : ℝ) := by
      intro w
      rw [hRres_eq]
      by_cases hw : w ∈ Vplus 𝓗 (1 - ε)
      · have h1 := (abs_le.mp (hReg.1 w hw)).2
        have h2 : (degAt 𝓗.pow2 w : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast degAt_le_n 𝓗.pow2 w
        nlinarith only [h1, h2, hdata.hρ0, hdata.hm.hξ0]
      · have h1 := (hReg.2 w hw).2
        have h2 : (0 : ℝ) ≤ ρ * ε * (n : ℝ) := by
          have hρ := hdata.hρ0
          have hε := hdata.hε0
          positivity
        nlinarith only [h1, h2, hdata.hρ0, hdata.hm.hξ0]
    have hlb : ∀ w : Fin n, (ρ - 20 * ε) * (n : ℝ) ≤ (degAt R_res w : ℝ) := by
      intro w
      rw [hRres_eq]
      by_cases hw : w ∈ Vplus 𝓗 (1 - ε)
      · have h1 := (abs_le.mp (hReg.1 w hw)).1
        have h2 : (1 - ε) * (n : ℝ) ≤ (degAt 𝓗.pow2 w : ℝ) := hw
        have h3 : ξ * (n : ℝ) ≤ 19 * ε * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hdata.hξε19 (Nat.cast_nonneg (α := ℝ) n)
        have h5 : ρ * ((1 - ε) * (n : ℝ)) - ξ * (n : ℝ) ≤
            (degAt (R_abs ∪ Rreg) w : ℝ) := by
          have h4 : ρ * ((1 - ε) * (n : ℝ)) ≤ ρ * (degAt 𝓗.pow2 w : ℝ) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt hdata.hρ0)
          linarith only [h4, h1]
        have h7 : ρ * ε * (n : ℝ) ≤ ε * (n : ℝ) := by
          have h8 : ρ ≤ 1 := by linarith only [hdata.hρ100]
          have h9 : (0 : ℝ) ≤ ε * (n : ℝ) := by
            have hε := hdata.hε0
            positivity
          nlinarith only [h8, h9]
        nlinarith only [h5, h3, h7, hdata.hρ0, hdata.hε0]
      · have h1 := (hReg.2 w hw).1
        have h2 : (ρ - 20 * ε) * (n : ℝ) ≤
            max (ρ * (degAt 𝓗.pow2 w : ℝ)) ((ρ - 20 * ε) * (n : ℝ)) := le_max_right _ _
        exact le_trans h2 h1
    have hdelta : ∀ v : Fin n, ((hypergraphMaxDegree R_final : ℝ) - (degAt R_final v : ℝ)) ≤
        η * (n : ℝ) := by
      intro v
      have h1 := s12_delta_le (R_res := R_res) (R_final := R_final) (ρ := ρ) (ξ := ξ)
        (ε := ε) (γ := γ) hout.hRfin_sub
        (fun e he => by rw [edgeSize_eq_ncard]; exact hout.hRfin2 e he)
        (by nlinarith only [hdata.hρ0, hdata.hm.hξ0, Nat.cast_nonneg (α := ℝ) n]) hub hlb
        (fun w => hout.hdeficit w) hdata.hδnum v
      have h2 := mul_le_mul_of_nonneg_right hdata.hη22 (Nat.cast_nonneg (α := ℝ) n)
      linarith only [h1, h2]
    have hdisj : Disjoint (Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff) Cfinal := by
      rw [Finset.disjoint_left]
      intro x hx hxc
      rw [hS12.hCfinal_eq, Finset.mem_sdiff] at hxc
      exact hxc.2 hx
    have hRsub : R_final ⊆ 𝓗 := fun e he =>
      (mem_pow2.mp (hRres_pow2 (hout.hRfin_sub he))).1
    exact s12_finish_A2_gen hout hdisj hRsub hk1 hnum hT1 hreg hdelta hcor

end

end ErdosFaberLovaszConjecture
