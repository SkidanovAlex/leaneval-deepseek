import Submission.EFL.S12ANum
import Submission.EFL.S12Step1Full
import Submission.EFL.Comm.TwoMulLeRpowLog
import Submission.EFL.S12Finish
import Submission.EFL.S12Mprev

import Submission.EFL.NibbleFixed
/-!
# §12: the Type A₁ branch of the proof of Theorem 1.1

This module assembles the Type A₁ case of §12: given a Type A colouring `φ`
of `𝓗_med ∪ 𝓗_large` with `𝓗` *not* `(ρ,ε)`-full (where `ρ = σ/2` and
`ε = σ³/10⁴²` are the constants of `S12ANum`), a false statement
`¬ IsFull 𝓗 (σ/2) (σ³/10⁴²)`, the numerical side conditions `S12ANum`, and the
reservoir/absorber of Step 2, the chromatic index of `𝓗` is at most `n`.

The proof is the paper's Steps 4--10 in the non-`full` case:

* Step 4 extends the (at most one) difficult colour class (`s12_step4_inst`);
* the sharp absorber `R₁ = R_abs ∖ ⋃𝓜_diff` is obtained from `obs:del_absorber`;
* Steps 5--9 produce `𝓜_prev`, `R_final = R_res ∖ ⋃𝓜_prev` and the degree
  bounds UC1--UC4 (`s12_main_A1`);
* Step 10 colours `R_final` with Vizing's theorem.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **The sharp absorber `R₁ = R_abs ∖ ⋃𝓜_diff`.**  Deleting the (at most one)
matching of `𝓜_diff` from `R_abs` increases the absorptivity parameter from
`γ` by `1/n` (Observation `obs:del_absorber`). -/
theorem IsAbsorber.delete_step4 {𝓗 R_abs R₁ : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {r₁ : ℝ} {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S S₁ : Set (Fin n)}
    {Cdiff : Finset (Fin n)}
    {ρ_abs γ₀ γ ξ : ℝ} {Mdiff : Fin n → Set 𝓗}
    (hRabs : IsAbsorber (incidentTwo 𝓗 U) R_abs 𝓥 ρ_abs γ₀ ξ)
    (hstep4 : IsS12Step4 𝓗 φ U S Cdiff R_abs R₁ S₁ Mdiff 𝓥 ρ_abs γ ξ)
    (hcard : Cdiff.card ≤ 1) (hn1 : 1 ≤ n) :
    IsAbsorber (incidentTwo 𝓗 U) R₁ 𝓥 ρ_abs (γ₀ + 1 / (n : ℝ)) ξ := by
  classical
  rw [hstep4.hR₁_eq]
  rcases Nat.eq_zero_or_pos Cdiff.card with h0 | hpos
  · -- `C_diff = ∅`: `𝓜_diff` is empty and `R₁ = R_abs`
    have hC0 : Cdiff = ∅ := Finset.card_eq_zero.mp h0
    have hsub : ∀ c : Fin n, Mdiff c = ∅ := fun c => hstep4.hMdiff_supp c (by rw [hC0]; simp)
    have hfam : famUnionIdx Mdiff = ∅ := by
      ext e
      rw [mem_famUnionIdx]
      constructor
      · rintro ⟨c, hc⟩
        rw [hsub c, mem_famOf] at hc
        obtain ⟨e', he', -⟩ := hc
        exact he'
      · intro he
        exact absurd he (by simp)
    rw [hfam, Set.sdiff_empty]
    exact IsAbsorber.mono_gamma hRabs (by
      have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith)
  · have h1 : Cdiff.card = 1 := by omega
    obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp h1
    have hfam : famUnionIdx Mdiff = famOf (Mdiff c₀) := by
      have hfun : Mdiff = fun c : Fin n => if c ∈ ({c₀} : Finset (Fin n)) then Mdiff c₀ else ∅ := by
        funext c
        by_cases hc : c ∈ ({c₀} : Finset (Fin n))
        · rw [if_pos hc, Finset.mem_singleton.mp hc]
        · rw [if_neg hc]
          exact hstep4.hMdiff_supp c (by rw [hc₀]; exact hc)
      rw [hfun]
      simpa using famUnionIdx_if_le_one (M := Mdiff c₀)
        (C := ({c₀} : Finset (Fin n))) (Finset.mem_singleton_self c₀)
    rw [hfam]
    exact IsAbsorber.delete_famOf hRabs (hstep4.hMdiff_mat c₀) (le_of_eq rfl) hn1

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- `subFam` of the empty family is empty. -/
theorem subFam_empty {𝓖 𝓗 : Hypergraph (Fin n)} :
    subFam (𝓖 := 𝓖) (𝓗 := 𝓗) (∅ : Set 𝓖) = ∅ := by
  ext e
  simp only [mem_subFam, Set.mem_empty_iff_false]
  tauto

/-- The colour class of `φ` (as a family of edges of `𝓗`) is empty when the
colour class is empty. -/
theorem colourFam_eq_empty {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {c : Fin n} (h : φ.colorClass c = ∅) :
    colourFam φ c = ∅ := by
  rw [colourFam, h, subFam_empty]

/-- **§12, the Type A₁ branch.**  For the constants of `S12ANum` (i.e.
`ρ = σ/2 ≤ 10⁻²⁵`, `ε = σ³/10⁴²`, `γ ≤ σ¹⁰/10²⁵⁰`), a colouring `φ` of
`𝓗_med ∪ 𝓗_large` of Type A with `𝓗` *not* `(ρ,ε)`-full, and the
reservoir/absorber of Step 2 (`hR`), the chromatic index of `𝓗` is at most
`n`.  This is the paper's Steps 3--10 in the Type A₁ case. -/
theorem s12_branch_A1 {𝓗 : Hypergraph (Fin n)} {σ γ β ξ ρabs : ℝ} {r₁ r₀ : ℕ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U : Set (Fin n)}
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) (σ ^ 3 / 10 ^ 42) ρabs ξ n)
    (hleft : LeftoverMargins n r₁ γ (σ / 2) ρabs (σ ^ 3 / 10 ^ 42) ξ)
    (hAN : S12ANum n r₁ r₀ β γ σ ξ ρabs)
    (hρab : ρabs = σ / 2 ∨ ρabs = σ / 4)
    (hσ0 : 0 < σ) (hσ24 : σ ≤ (10 : ℝ) ^ (-24 : ℤ)) (hγ0 : 0 < γ)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) (hβ0 : 0 < β) (hβγ : β ≤ γ)
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1))
    (hlin : 𝓗.IsLinear) (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hU : U = Vplus 𝓗 (1 - σ ^ 3 / 10 ^ 42))
    (hA : IsTypeA σ γ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ)
    (hnF : ¬ IsFull 𝓗 (σ / 2) (σ ^ 3 / 10 ^ 42))
    (hR : ∃ R_res R_abs : Hypergraph (Fin n),
      IsReservoirTypeA1 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) (σ / 2) ξ (σ ^ 3 / 10 ^ 42) ∧
      IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n))) ρabs ξ ξ ∧
      R_abs ⊆ R_res ∧ R_abs ⊆ 𝓗.pow2) :
    𝓗.chromaticIndex ≤ n := by
  classical
  obtain ⟨R_res, R_abs, hresA1, hRabs, hRabs_sub, hRabs_pow2⟩ := hR
  have hn1 : 1 ≤ n := hAN.hm.hn1
  have hn2 : 2 ≤ n := le_trans (by norm_num) hAN.hm.hn4
  have hσhalf : σ ≤ 1 / 2 := by
    have h24 := hσ24
    norm_num at h24
    linarith only [h24]
  have hσone : σ ≤ 1 := le_trans hσhalf (by norm_num)
  have hγ1 : γ ≤ 1 := by
    have h1 : σ ^ 10 / 10 ^ 250 ≤ 1 := by
      have h2 : σ ^ 10 ≤ 1 := pow_le_one₀ hσ0.le hσone (n := 10)
      linarith only [h2]
    linarith only [hγσ, h1]
  have hβ1 : β ≤ 1 := le_trans hβγ hγ1
  have hγsqrt1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
  -- ## Step 3
  obtain ⟨Cmed, Cdiff, Chuge, Clarge, Cmain, Cbuff, Cfinal, hS12, hsing, hVn2U, hVn1char,
    hVn2char, hvert, h3R, hCl⟩ :=
    s12_step3_typeA (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (σ := σ)
      (γ₁ := γ) (β := β) (γ := γ) (ρ := σ / 2) (ε := σ ^ 3 / 10 ^ 42)
      hlin hbig hA le_rfl hβ0 hAN.hm.hβn hn2 hAN.hm.hr₁β hAN.hεn3 hU hAN.hnum3 hAN.hDlb
  -- ## Steps 4: the difficult colour class
  have hRabs10 : IsAbsorber (incidentTwo 𝓗 U) R_abs (cvFinset φ U : Set (Set (Fin n)))
      ρabs (10 * ξ) ξ := IsAbsorber.mono_gamma hRabs (by linarith [hAN.hm.hξ0])
  have hDM : DiffMargins n β :=
    ⟨hβ0, hβ1, by nlinarith only [hAN.hm.hmDeg.hβn]⟩
  have hbig' : ∀ f ∈ 𝓗, 2 ≤ f.ncard := fun f hf => by
    have h := hbig f hf
    rwa [edgeSize_eq_ncard] at h
  have hξγ : 10 * ξ + 1 / (n : ℝ) ≤ 3 * γ / 2 := by
    have h := hAN.hξsharp
    linarith only [h, hγ0]
  rcases s12_step4_inst (n := n) (𝓗 := 𝓗) (r₁ := (r₁ : ℝ)) (r₀ := (r₀ : ℝ)) (σ := σ)
      (γ₁ := γ) (β := β) (γ := γ) (ρ := σ / 2) (ρ_abs := ρabs) (ξ := ξ)
      (ε := σ ^ 3 / 10 ^ 42) hlin hbig' hU hS12 hA hDM hn1 hξγ hRabs10 with
      hχ | ⟨Mdiff, R₁, S₁, hstep4⟩
  · exact hχ
  · -- ## the sharp absorber `R₁`
    have hR₁sharp : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
        ρabs (10 * ξ + 1 / (n : ℝ)) ξ :=
      IsAbsorber.delete_step4 hRabs10 hstep4 hS12.hCdiff_card hn1
    -- ## the numeric hypotheses of `s12_main_A1`
    have hVn1U : Vn1set 𝓗 ⊆ U := fun v hv => hVn2U (Vn1set_subset_Vn2set 𝓗 hv)
    have hS_big := S_big_typeA1 hlin hbig hU hnF hVn1U
    have hT1 : ∀ c ∈ Cfinal, colourFam φ c = ∅ := fun c hc =>
      colourFam_eq_empty (hS12.class_eq_empty_of_buff_union_final hCl c
        (Finset.mem_union_right Cbuff hc))
    have hγs : γ ≤ Real.sqrt γ := by
      nlinarith [Real.sq_sqrt hγ0.le, hγsqrt1, Real.sqrt_nonneg γ]
    have hX : (((Cmed ∪ Cdiff ∪ Chuge).card : ℕ) : ℝ) ≤ 5 * Real.sqrt γ * (n : ℝ) := by
      have hk2 := hAN.hm.hk2
      have h6 : 3 * γ * (n : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
        nlinarith only [hγs, Real.sqrt_nonneg γ, Nat.cast_nonneg (α := ℝ) n]
      linarith only [h3R, hk2, h6]
    have hUCnum1 : (σ / 2) * (1 - σ ^ 3 / 10 ^ 42) * (n : ℝ) + ξ * (n : ℝ) ≤
        (Cfinal.card : ℝ) - (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) / 2 := by
      have hcfg := hS12.card_final_ge hX (by positivity) (by linarith only [hσhalf]) hn1
      have h15 := hAN.h15ρ
      have h15' : (15 * Real.sqrt γ + ξ) * (n : ℝ) ≤
          ((σ / 2) * (σ ^ 3 / 10 ^ 42) / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right h15 (Nat.cast_nonneg (α := ℝ) n)
      nlinarith only [hcfg, h15']
    have hUCnum2 : 2 * (n : ℝ) / (r₀ : ℝ) ≤
        (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) / 4 := by
      have h8 := hAN.h8r₀
      have h8' : (2 : ℝ) ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (r₀ : ℝ) / 4 := by
        linarith only [h8]
      have hr0 : (0 : ℝ) < (r₀ : ℝ) := by exact_mod_cast (by omega : 0 < r₀)
      rw [div_le_iff₀ hr0]
      nlinarith only [h8', Nat.cast_nonneg (α := ℝ) n]
    have hDn : (Dparam n (σ / 2) : ℝ) ≤ (n : ℝ) := by
      have h1 := hAN.hnum3
      have h2 : (0 : ℝ) ≤ (D'param (Dparam n (σ / 2)) γ : ℝ) := Nat.cast_nonneg _
      have h3 : (0 : ℝ) ≤ 2 * γ * (n : ℝ) := by positivity
      have h4 : (0 : ℝ) ≤ 32 / β ^ 2 := by positivity
      linarith only [h1, h2, h3, h4]
    have hdeficitNum : (((Cdiff ∪ Chuge ∪ Cmed ∪ Cbuff).card : ℕ) : ℝ) +
        2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ) := by
      have hk2 := hAN.hm.hk2
      have hCbuff : ((Cbuff.card : ℕ) : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
        rw [hS12.hCbuff_card]
        have h2 : (D'param (Dparam n (σ / 2)) γ : ℝ) ≤
            10 * Real.sqrt γ * (Dparam n (σ / 2) : ℝ) := by
          rw [D'param]
          exact Nat.floor_le (by positivity)
        have h4 : 10 * Real.sqrt γ * (Dparam n (σ / 2) : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) :=
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
        nlinarith only [hk2, hγs, hγ0, Real.sqrt_nonneg γ, Nat.cast_nonneg (α := ℝ) n]
      have hCmain' : 2 * γ * ((Cmain.card : ℕ) : ℝ) ≤ 2 * γ * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hCmain (by positivity)
      linarith only [h1, h3R', hCbuff, hCmain', hfin]
    have hk1 : 1 ≤ Cfinal.card :=
      one_le_card_Cfinal hS12 hX (by positivity) (by linarith only [hσhalf]) hn1 hAN.h30
        (by linarith only [hAN.hρn25])
    have hnum : 1 ≤ (σ / 2) * (σ ^ 3 / 10 ^ 42) * (n : ℝ) / 4 :=
      one_le_rho_eps_mul hAN.h4ρεn
    exact s12_main_A1 (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := σ / 2)
      (ρ_abs := ρabs) (ξ := ξ) (ε := σ ^ 3 / 10 ^ 42) (κ := 1 / 2) (φ := φ) (U := U)
      (S := U \ Vn1set 𝓗) (S₁ := S₁) (Cmed := Cmed) (Cdiff := Cdiff) (Chuge := Chuge)
      (Clarge := Clarge) (Cmain := Cmain) (Cbuff := Cbuff) (Cfinal := Cfinal)
      (R_res := R_res) (R_abs := R_abs) (R₁ := R₁) (Mdiff := Mdiff)
      hlin hbig hNib hleft hS12 hsing hvert hresA1 mem_cvFinset_univ mem_cvFinset_U hU
      hstep4 hRabs_pow2 hR₁sharp (by linarith only [hAN.hξsharp, hγ0]) Set.sdiff_subset hS_big
      hAN.hm hRabs_sub hVn2U hUCnum1 hUCnum2 hdeficitNum hT1
      (fun v hv hmem => (hstep4.hS₁_sub hmem).2 hv) hk1 hnum

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **The `cvFinset` bound of §12.**  `|𝓥| ≤ 2n+2 ≤ n^{log n}` for all
sufficiently large `n`, for the family `𝓥` of `(def:cv)`. -/
theorem exists_cvFinset_card_le :
    ∃ N : ℕ, ∀ n ≥ N, ∀ {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
      (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U : Set (Fin n)),
      ((cvFinset φ U).card : ℝ) ≤ (n : ℝ) ^ Real.log (n : ℝ) := by
  obtain ⟨N, hN⟩ := Commons.Analysis.Asymptotics.exists_two_mul_add_two_le_rpow_log
  refine ⟨N, fun n hn 𝓗 r₁ φ U => ?_⟩
  have h1 : ((cvFinset φ U).card : ℝ) ≤ 2 * (n : ℝ) + 2 := by
    have h := cvFinset_card_le (n := n) φ U
    exact_mod_cast h
  have h2 := hN n hn
  linarith only [h1, h2]

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **§12, the Type A₁ branch with a threshold.**  For the constants of the
hierarchy (`σ ≤ 10⁻²⁴`, `γ ≤ σ¹⁰/10²⁵⁰`, `β ≤ γ`, `32 ≤ βr₁`,
`r₁ < (γ/4)(r₀-1)`) there is `N` such that every linear `n`-vertex hypergraph
all of whose edges have at least two vertices, `n ≥ N`, that admits a Type A
colouring `φ` of its medium and large edges with `𝓗` *not*
`(σ/2,σ³/10⁴²)`-full satisfies `χ'(𝓗) ≤ n`. -/
theorem s12_A1_main {σ γ β : ℝ} {r₁ r₀ : ℕ}
    (hNib : NibbleStatementFixed) (hK : KahnStatement)
    (hσ0 : 0 < σ) (hσ24 : σ ≤ (10 : ℝ) ^ (-24 : ℤ)) (hγ0 : 0 < γ)
    (hγσ : γ ≤ σ ^ 10 / 10 ^ 250) (hβ0 : 0 < β) (hβγ : β ≤ γ) (hβsq : β ≤ γ ^ 2 / 16)
    (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      (∀ e ∈ 𝓗, 2 ≤ edgeSize e) →
      (∃ φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n),
        IsTypeA σ γ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ ∧ ¬ IsFull 𝓗 (σ / 2) (σ ^ 3 / 10 ^ 42)) →
      𝓗.chromaticIndex ≤ n := by
  classical
  have hσhalf : σ ≤ 1 / 2 := by
    have h24 := hσ24
    norm_num at h24
    linarith only [h24]
  obtain ⟨ξ, hξ0, N₁, hN₁⟩ :=
    exists_S12ANum (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (σ := σ) (ρabs := σ / 2)
      (Or.inl rfl) hβ0 hγ0 hσ0 hβγ hβsq hβ4 hγσ hσ24 hr₁2 hr₀2 hr₁r₀ hβr1 hr₁β₀ hr₀big
  obtain ⟨N₂, hN₂⟩ :=
    s12_step2_typeA1 (ρ := σ / 2) (ξ := ξ) (by positivity) (by linarith only [hσhalf]) hξ0
  obtain ⟨N₃, hN₃⟩ := exists_cvFinset_card_le
  -- ## the numerical margins of the Leftover Lemma
  have hAN₀ : S12ANum (max N₁ 1) r₁ r₀ β γ σ ξ (σ / 2) := hN₁ (max N₁ 1) (le_max_left _ _)
  have hξsharp : 10 * ξ ≤ γ / 2 := by
    have h := hAN₀.hξsharp
    have h2 : (0 : ℝ) ≤ 1 / (((max N₁ 1 : ℕ)) : ℝ) := by positivity
    linarith only [h, h2]
  obtain ⟨N₄, hN₄⟩ :=
    exists_leftoverMargins_A hK (r₁ := r₁) (σ := σ) (γ := γ) (ξ := ξ) (ρabs := σ / 2)
      hσ0 hσhalf hγ0 hγσ hξ0 hξsharp hAN₀.hsqrtγ (Or.inl rfl)
  refine ⟨max (nibbleThr r₁ (2 * β) (2 * γ) (σ ^ 3 / 10 ^ 42) (σ / 2) ξ)
      (max N₄ (max N₁ (max N₂ N₃))), fun n hn 𝓗 hlin hbig ⟨φ, hA, hnF⟩ => ?_⟩
  have hThr : nibbleThr r₁ (2 * β) (2 * γ) (σ ^ 3 / 10 ^ 42) (σ / 2) ξ ≤ n :=
    le_trans (le_max_left _ _) hn
  have hn₄ : N₄ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hn₂ : N₂ ≤ n := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hn)))
  have hn₃ : N₃ ≤ n := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hn)))
  have hVcard := hN₃ n hn₃ φ (Vplus 𝓗 (1 - σ ^ 3 / 10 ^ 42))
  have hR := hN₂ n hn₂ 𝓗 hlin φ (Vplus 𝓗 (1 - σ ^ 3 / 10 ^ 42)) rfl (hN₁ n hn₁).hm.hn1 hVcard
  -- ## the Nibble Lemma, pointwise at the constants of this branch
  have hβ1 : β ≤ 1 := by
    have hσ1 : σ ≤ 1 := by have h := hσ24; norm_num at h ⊢; linarith
    have hγ1 : γ ≤ 1 := by
      have h3 : σ ^ 10 ≤ 1 := pow_le_one₀ hσ0.le hσ1
      have h4 : (0 : ℝ) < 10 ^ 250 := by norm_num
      have h5 : σ ^ 10 / 10 ^ 250 ≤ 1 := by
        rw [div_le_iff₀ h4]; linarith only [h3]
      linarith only [hγσ, h5]
    linarith only [hβγ, hγ1]
  have hr32 : (32 : ℝ) ≤ (r₁ : ℝ) := by
    have hle : β * (r₁ : ℝ) ≤ (r₁ : ℝ) := by
      simpa using mul_le_mul_of_nonneg_right hβ1 (Nat.cast_nonneg (α := ℝ) r₁)
    linarith only [hβr1, hle]
  have hr3 : 3 ≤ r₁ := by
    have h3 : (3 : ℝ) ≤ (r₁ : ℝ) := by linarith only [hr32]
    exact_mod_cast h3
  have hε9 : 4 * 10 ^ (-9 : ℤ) * (σ ^ 3 / 10 ^ 42) ≤ σ / 2 := by
    have hσ1 : σ ≤ 1 := by have h := hσ24; norm_num at h ⊢; linarith
    have hc : (4 : ℝ) * 10 ^ (-9 : ℤ) = 4 / 10 ^ 9 := by norm_num [zpow_neg]
    rw [hc]
    nlinarith only [hσ0, hσ1, pow_nonneg (le_of_lt hσ0) 2]
  have hMC : Work.Deep.Nibble.MarginsConst r₁ (2 * β) (2 * γ) (σ ^ 3 / 10 ^ 42) (σ / 2) ξ :=
    marginsConst_of_bundle (hN₁ n hn₁).hm.hnib hr3 hε9
  have hNibP : NibblePointwise r₁ (2 * β) (2 * γ) (σ ^ 3 / 10 ^ 42) (σ / 2) ξ n :=
    nibbleAbove_nibbleThr hMC hThr
  exact s12_branch_A1 (ρabs := σ / 2) hNibP (hN₄ n hn₄) (hN₁ n hn₁) (Or.inl rfl) hσ0 hσ24 hγ0
    hγσ hβ0 hβγ hr₁2 hr₀2 hr₁r₀ hβr1 hr₁β₀ hr₀big hlin hbig rfl hA hnF hR

end

end ErdosFaberLovaszConjecture
