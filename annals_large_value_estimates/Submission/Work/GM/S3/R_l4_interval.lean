import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.Rl4Aux
import Submission.Work.GM.S3.l4_expansion
import Submission.Work.GM.S3.l4_scaled_integral
import Submission.Work.GM.S3.l4_scaled_integrable
import Submission.Work.GM.S3.l4_card_bound
import Submission.Work.GM.S3.l4_rpow_absorb

/-!
# GM Lemma 8.3 on an arbitrary fixed interval `[1/C, C]`

This file proves `Work.GM.S3.R_l4_interval`, the version of `Work.GM.S3.R_l4` (GM Lemma 8.3,
`∫_1^2 ‖R‖⁴ ≪ E(W)`) in which `[1,2]` is replaced by an arbitrary interval `[1/C, C]`.

The proof is the same as `R_l4_core` in `Submission/Work/GM/S3/R_l4.lean`, with two changes:

* the change of variables is `v = e^τ` on `[1/C, C]`, i.e. `τ ∈ [-log C, log C]`, and the weight
  `dv = e^τ dτ` is bounded by `C`;
* the majorising bump now has to be `≥ 1` on `[-L, L]` for `L = log C` (rather than on
  `[0, log 2]`); `bump_interval` below produces such a bump, still smooth and compactly
  supported, with rapidly decaying Fourier transform.

Everything else (the expansion of `‖Gfun W τ‖⁴` as the quadruple sum over `Quad W`, the
Fourier-decay bound for the terms with `|t₁+t₂-t₃-t₄| > 1`, and the counting of the remaining
terms by `E(W)`) is exactly as in `R_l4_core`.
-/

namespace Work.GM.S3

open MeasureTheory Finset Complex
open scoped BigOperators
open Submission.GM (Rfun energy Separated)

/-! ## A bump majorising an arbitrary symmetric interval `[-L, L]` -/

/-- For every `L ≥ 0` there is a continuous compactly supported `ψ : ℝ → ℝ`, nonnegative and
`≥ 1` on `[-L, L]`, whose Fourier transform is bounded by some `A` and decays faster than any
power of `|ξ|`.  (The same construction as `Work.GM.S3.l4_bump`, with the interval
`[0, log 2]` replaced by `[-L, L]`.) -/
private theorem bump_interval (L : ℝ) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧
      (∀ x : ℝ, 0 ≤ ψ x) ∧ (∀ x ∈ Set.Icc (-L) L, 1 ≤ ψ x) ∧
      (∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : ℝ,
        ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ A) ∧
      (∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧ ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ Cj / |ξ| ^ j) := by
  -- The product of two smooth steps, equal to `1` on `[-L, L]` and vanishing off
  -- `[-L-1, L+1]`.
  let ψ : ℝ → ℝ :=
    fun x => Real.smoothTransition (x + L + 1) * Real.smoothTransition (L + 1 - x)
  have hψc : Continuous ψ := by
    unfold ψ
    refine Continuous.mul ?_ ?_
    · exact Real.smoothTransition.continuous.comp
        ((continuous_id.add continuous_const).add continuous_const)
    · exact Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id)
  have hψnn : ∀ x : ℝ, 0 ≤ ψ x := by
    intro x
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hψone : ∀ x ∈ Set.Icc (-L) L, 1 ≤ ψ x := by
    intro x hx
    obtain ⟨hx0, hxL⟩ := hx
    have e1 : Real.smoothTransition (x + L + 1) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    have e2 : Real.smoothTransition (L + 1 - x) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith)
    simp [ψ, e1, e2]
  have hψdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    unfold ψ
    fun_prop
  -- The support is contained in the compact interval `[-L-1, L+1]`.
  have hsub : Function.support ψ ⊆ Set.Icc (-(L + 1)) (L + 1) := by
    intro x hx
    rw [Function.mem_support] at hx
    dsimp only [ψ] at hx
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hx
    have hp1 : 0 < x + L + 1 := by
      by_contra h
      exact h1 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
    have hp2 : 0 < L + 1 - x := by
      by_contra h
      exact h2 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
    exact ⟨by linarith, by linarith⟩
  have hψcs : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsub
  have hsubC : Function.support (fun x : ℝ => (ψ x : ℂ)) ⊆ Set.Icc (-(L + 1)) (L + 1) := by
    intro x hx
    apply hsub
    rw [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h])
  have hψCcs : HasCompactSupport (fun x : ℝ => (ψ x : ℂ)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsubC
  have hψCdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (ψ x : ℂ)) := by
    have hh := (Complex.ofRealCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hψdiff
    have hfun : (⇑Complex.ofRealCLM ∘ ψ) = fun x : ℝ => (ψ x : ℂ) := by
      funext x
      exact Complex.ofRealCLM_apply (ψ x)
    rwa [hfun] at hh
  refine ⟨ψ, hψc, hψcs, hψnn, hψone, ?_, ?_⟩
  · -- Boundedness: the Fourier transform is bounded by the `L¹` norm of `ψ`.
    refine ⟨∫ x : ℝ, ‖((ψ x : ℝ) : ℂ)‖, ?_, ?_⟩
    · exact integral_nonneg (fun x => norm_nonneg _)
    · intro ξ
      rw [Real.fourier_eq]
      have h := norm_integral_le_integral_norm (μ := volume)
        (fun v : ℝ => Real.fourierChar (-inner ℝ v ξ) • ((ψ v : ℝ) : ℂ))
      simpa only [Circle.norm_smul] using h
  · -- Decay: a smooth compactly supported function has rapidly decaying Fourier transform.
    intro j
    obtain ⟨C, hC0, hC⟩ :=
      Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay j hψCdiff hψCcs
    refine ⟨C + 1, by linarith, fun ξ hξ => ?_⟩
    have hpos : 0 < |ξ| ^ j := pow_pos (abs_pos.mpr hξ) j
    calc ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖
        ≤ C / |ξ| ^ j := hC ξ hξ
      _ ≤ (C + 1) / |ξ| ^ j := by
          apply div_le_div_of_nonneg_right (by linarith) hpos.le

/-! ## Change of variables `v = e^τ` on an arbitrary positive interval -/

/-- Change of variables `v = e^τ` on an interval `[a,b]` with `0 < a` and `0 < b`:
`∫_a^b g = ∫_{log a}^{log b} e^τ g(e^τ) dτ`.  (Generalisation of `Work.GM.S3.integral_exp_subst`
in `Rl4Aux.lean`, which is the case `a = 1`, `b = 2`.) -/
private theorem integral_exp_subst_general {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (g : ℝ → ℝ) :
    (∫ v in a..b, g v) = ∫ τ in (Real.log a)..(Real.log b), Real.exp τ * g (Real.exp τ) := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      (a := Real.log a) (b := Real.log b) (f := Real.exp) (f' := Real.exp) (g := g)
      Real.continuous_exp.continuousOn
      (fun x hx => Real.hasDerivAt_exp x)
      (fun x hx => (Real.exp_pos x).le)
  rw [Real.exp_log ha, Real.exp_log hb] at h
  exact h.symm

/-! ## The arithmetic and per-term helpers (copies of the private lemmas of `R_l4.lean`) -/

private lemma far_arith_2 {T η : ℝ} (hT : 1 ≤ T) {j : ℕ} {Cj s : ℝ}
    (hCj : 0 ≤ Cj) (hs : 1 < |s|) :
    T ^ η * (Cj / |-(T ^ η * s) / (2 * Real.pi)| ^ j) ≤
      (2 * Real.pi) ^ j * Cj * T ^ (η * (1 - (j : ℝ))) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hTnn : 0 ≤ T := hTpos.le
  have hpi : 0 < 2 * Real.pi := by positivity
  have hApos : 0 < T ^ η := Real.rpow_pos_of_pos hTpos η
  have hAnn : 0 ≤ T ^ η := hApos.le
  have hsj : 1 ≤ |s| ^ j := one_le_pow₀ hs.le
  have hX : |-(T ^ η * s) / (2 * Real.pi)| = T ^ η * |s| / (2 * Real.pi) := by
    rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hAnn, abs_of_pos hpi]
  have hkey : T ^ (η * (1 - (j : ℝ))) = T ^ η / (T ^ η) ^ j := by
    rw [Real.rpow_mul hTnn η (1 - (j:ℝ)), Real.rpow_sub hApos 1 (j:ℝ), Real.rpow_one,
      Real.rpow_natCast]
  rw [hX, div_pow, mul_pow, div_div_eq_mul_div]
  have hstep : Cj * (2 * Real.pi) ^ j / ((T^η)^j * |s|^j) ≤ Cj * (2*Real.pi)^j / (T^η)^j :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hApos j)
      (le_mul_of_one_le_right (pow_nonneg hAnn j) hsj)
  calc T ^ η * (Cj * (2 * Real.pi) ^ j / ((T^η)^j * |s|^j))
      ≤ T ^ η * (Cj * (2 * Real.pi)^j / (T^η)^j) :=
        mul_le_mul_of_nonneg_left hstep hAnn
    _ = (2 * Real.pi)^j * Cj * T ^ (η * (1 - (j:ℝ))) := by
        rw [hkey]
        field_simp

private lemma term_bound_2
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
    {A : ℝ} (hA : ∀ ξ : ℝ, ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ A)
    {j : ℕ} {Cj : ℝ}
    (hCj : ∀ ξ : ℝ, ξ ≠ 0 → ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ Cj / |ξ| ^ j)
    {T η : ℝ} (hT : 1 ≤ T) (hη : 0 < η) (s : ℝ) :
    ‖∫ τ : ℝ, ((ψ (τ / T ^ η) : ℝ) : ℂ) * cexp (I * ((s * τ : ℝ) : ℂ))‖
      ≤ if |s| ≤ 1 then T ^ η * A else (2 * Real.pi) ^ j * Cj * T ^ (η * (1 - (j : ℝ))) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hTnn : 0 ≤ T := hTpos.le
  have hAnn : 0 ≤ T ^ η := Real.rpow_nonneg hTnn η
  have hCjnn : 0 ≤ Cj := by
    have h1 := hCj 1 one_ne_zero
    simpa using le_trans (norm_nonneg _) h1
  rw [l4_scaled_integral hψ hcs hTpos hη s, norm_mul,
    show ‖((T ^ η : ℝ) : ℂ)‖ = |T ^ η| from by simp, abs_of_nonneg hAnn]
  by_cases hs : |s| ≤ 1
  · rw [if_pos hs]
    exact mul_le_mul_of_nonneg_left (hA _) hAnn
  · rw [if_neg hs]
    have hs1 : 1 < |s| := lt_of_not_ge hs
    have hs0 : s ≠ 0 := by intro h; rw [h, abs_zero] at hs1; norm_num at hs1
    have hne : -(T ^ η * s) / (2 * Real.pi) ≠ 0 := by
      simp [hs0, (Real.rpow_pos_of_pos hTpos η).ne']
    refine (mul_le_mul_of_nonneg_left (hCj _ hne) hAnn).trans ?_
    exact far_arith_2 hT hCjnn hs1

private lemma quad_sum_bound_2 {A Kfar : ℝ} (hK : 0 ≤ Kfar)
    {W : Finset ℝ} {c : ℝ × ℝ × ℝ × ℝ → ℝ}
    (hterm : ∀ q, c q ≤ if |qs q| ≤ 1 then A else Kfar) :
    ∑ q ∈ Quad W, c q ≤ (energy W : ℝ) * A + ((Quad W).card : ℝ) * Kfar := by
  classical
  calc ∑ q ∈ Quad W, c q
      ≤ ∑ q ∈ Quad W, (if |qs q| ≤ 1 then A else Kfar) := Finset.sum_le_sum fun q hq => hterm q
    _ = ∑ q ∈ (Quad W).filter (fun q => |qs q| ≤ 1), A
        + ∑ q ∈ (Quad W).filter (fun q => ¬ (|qs q| ≤ 1)), Kfar := Finset.sum_ite _ _
    _ = ((Quad W).filter (fun q => |qs q| ≤ 1)).card * A
        + ((Quad W).filter (fun q => ¬ (|qs q| ≤ 1))).card * Kfar := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ (energy W : ℝ) * A + ((Quad W).card : ℝ) * Kfar := by
        have h1 : ((Quad W).filter (fun q => |qs q| ≤ 1)).card = energy W := energy_eq_filter W
        rw [h1]
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) hK

private lemma final_arith_2 {A K Tη Ne E : ℝ} (hTA : Tη * A ≤ Ne * A)
    (hE : 1 ≤ E) (hNe : 1 ≤ Ne) (hK : 0 ≤ K) :
    E * (Tη * A) + 16 * K ≤ (A + 16 * K + 1) * Ne * E := by
  have hE0 : 0 ≤ E := le_trans zero_le_one hE
  have h1 : E * (Tη * A) ≤ E * (Ne * A) := mul_le_mul_of_nonneg_left hTA hE0
  have hNeE : 1 ≤ Ne * E := by nlinarith [hNe, hE]
  have h2 : 16 * K ≤ 16 * K * (Ne * E) := by nlinarith [hK, hNeE]
  have hne0 : 0 ≤ Ne * E := le_trans zero_le_one hNeE
  calc E * (Tη * A) + 16 * K
      ≤ E * (Ne * A) + 16 * K * (Ne * E) := add_le_add h1 h2
    _ = (A + 16 * K) * (Ne * E) := by ring
    _ ≤ (A + 16 * K + 1) * (Ne * E) :=
        mul_le_mul_of_nonneg_right (by linarith) hne0
    _ = (A + 16 * K + 1) * Ne * E := by ring

/-! ## The core estimate -/

/-- The core `L⁴` estimate on `[-L, L]`: for every `L ≥ 0` and `ε > 0` there are `C > 0`, `N₀`
with `∫_{-L}^{L} ‖Gfun W τ‖⁴ dτ ≤ C N^ε E(W)` for every `N ≥ N₀` and every `(M N)^ε`-separated
`W ⊆ [0, M N]`. -/
theorem R_l4_interval_core (L : ℝ) (hL : 0 ≤ L) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∫ τ in (-L)..L, ‖Gfun W τ‖ ^ 4 ≤ C * (N : ℝ) ^ ε * (energy W : ℝ) := by
  intro ε hε
  obtain ⟨ψ, hψc, hψcs, hψnn, hψge1, ⟨A, hAnn, hAbound⟩, hdecay⟩ := bump_interval L
  have hLneg : -L ≤ L := by linarith
  set η : ℝ := ε / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  set j : ℕ := Nat.ceil (7 / η) + 1 with hjdef
  have hj7 : 7 ≤ η * ((j : ℝ) - 1) := by
    have hc : 7 / η ≤ (Nat.ceil (7 / η) : ℝ) := Nat.le_ceil _
    have hjcast : ((j : ℝ) - 1) = (Nat.ceil (7 / η) : ℝ) := by
      rw [hjdef]; push_cast; ring
    rw [hjcast]
    calc (7 : ℝ) = η * (7 / η) := by field_simp
      _ ≤ η * (Nat.ceil (7 / η) : ℝ) := mul_le_mul_of_nonneg_left hc hη.le
  obtain ⟨Cj, hCjpos, hCjbound⟩ := hdecay j
  refine ⟨(A + 16 * ((2 * Real.pi) ^ j * Cj)) + 1, ?_, 1, ?_⟩
  · have h1 : 0 < (2 * Real.pi) ^ j := pow_pos (by positivity) j
    have h2 : 0 < 16 * ((2 * Real.pi) ^ j * Cj) := by positivity
    linarith
  · intro N hN W hWsub hWsep
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    set T : ℝ := Submission.LargeValues.M N with hTdef
    have hT1 : 1 ≤ T := by rw [hTdef]; exact Submission.LargeValues.M_ge_one hN
    have hTnn : 0 ≤ T := le_trans zero_le_one hT1
    have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
    have hTetanonneg : 0 ≤ T ^ η := Real.rpow_nonneg hTnn η
    have hTeta1 : 1 ≤ T ^ η := Real.one_le_rpow hT1 hη.le
    have hδ1 : 1 ≤ T ^ ε := by
      rw [hTdef]; exact Real.one_le_rpow (Submission.LargeValues.M_ge_one hN) hε.le
    have hWsub' : ∀ t ∈ W, t ∈ Set.Icc 0 T := by
      intro t ht; rw [hTdef]; exact hWsub t ht
    have hWsep' : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → T ^ ε ≤ |t - s| := by
      intro t ht s hs hts; rw [hTdef]; exact hWsep t ht s hs hts
    have hcardW : (W.card : ℝ) ≤ T + 1 := l4_card_bound hT1 hδ1 hWsub' hWsep'
    by_cases hWne : W.Nonempty
    · have henergy1 : (1 : ℝ) ≤ (energy W : ℝ) := by exact_mod_cast one_le_energy hWne
      set K : ℝ := (2 * Real.pi) ^ j * Cj with hKdef
      have hKnn : 0 ≤ K := by
        rw [hKdef]; exact mul_nonneg (pow_nonneg (by positivity) j) hCjpos.le
      have hNeps : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNr hε.le
      have hTeta_absorb : T ^ η ≤ (N : ℝ) ^ ε := by
        rw [hTdef, hηdef]; exact l4_rpow_absorb hε hN
      have hTA : T ^ η * A ≤ (N : ℝ) ^ ε * A := mul_le_mul_of_nonneg_right hTeta_absorb hAnn
      have hQcard : ((Quad W).card : ℝ) ≤ 16 * T ^ 4 := by
        rw [Quad_card]
        push_cast
        calc (W.card : ℝ) ^ 4 ≤ (T + 1) ^ 4 := pow_le_pow_left₀ (by positivity) hcardW 4
          _ ≤ (2 * T) ^ 4 := by
              apply pow_le_pow_left₀ (by positivity)
              linarith
          _ = 16 * T ^ 4 := by ring
      have hKfar_bound : ((Quad W).card : ℝ) * (K * T ^ (η * (1 - (j : ℝ)))) ≤ 16 * K := by
        have h4T : T ^ 4 * T ^ (η * (1 - (j:ℝ))) ≤ 1 := by
          have h4e : (4:ℝ) + η * (1 - (j:ℝ)) ≤ 0 := by linarith [hj7]
          have hT4 : T ^ 4 * T ^ (η * (1 - (j:ℝ))) = T ^ ((4:ℝ) + η * (1 - (j:ℝ))) := by
            rw [← Real.rpow_natCast T 4, ← Real.rpow_add hTpos]
            norm_num
          rw [hT4]
          calc T ^ ((4:ℝ) + η * (1 - (j:ℝ))) ≤ T ^ 0 := Real.rpow_le_rpow_of_exponent_le hT1 h4e
            _ = 1 := by simp
        calc ((Quad W).card : ℝ) * (K * T ^ (η * (1 - (j : ℝ))))
            ≤ (16 * T ^ 4) * (K * T ^ (η * (1 - (j : ℝ)))) := by
              apply mul_le_mul_of_nonneg_right hQcard
              exact mul_nonneg hKnn (Real.rpow_nonneg hTnn _)
          _ = 16 * K * (T ^ 4 * T ^ (η * (1 - (j : ℝ)))) := by ring
          _ ≤ 16 * K * 1 := mul_le_mul_of_nonneg_left h4T (by positivity)
          _ = 16 * K := by ring
      have hscaleint' : ∀ s : ℝ, Integrable (fun τ : ℝ =>
          ((ψ (τ / T ^ η) : ℝ) : ℂ) * cexp (I * ((s * τ : ℝ) : ℂ))) :=
        fun s => l4_scaled_integrable hψc hψcs hTpos hη s
      have hψint0 : Integrable (fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ)) := by
        simpa using hscaleint' 0
      have hcontG : Continuous (fun τ : ℝ => ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4) :=
        (hψc.comp (continuous_id.div_const _)).mul ((Gfun_continuous W).norm.pow 4)
      have hGint : Integrable (fun τ : ℝ => ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4) := by
        refine Integrable.mono' (hψint0.norm.const_mul ((W.card : ℝ) ^ 4))
          hcontG.aestronglyMeasurable ?_
        filter_upwards with τ
        have hcard4 : ‖Gfun W τ‖ ^ 4 ≤ (W.card : ℝ) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_Gfun_le_card W τ) 4
        rw [Real.norm_eq_abs, abs_mul,
          show ‖((ψ (τ / T ^ η) : ℝ) : ℂ)‖ = |ψ (τ / T ^ η)| from by simp,
          abs_of_nonneg (pow_nonneg (norm_nonneg _) 4), abs_of_nonneg (hψnn _)]
        calc ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4
            ≤ ψ (τ / T ^ η) * (W.card : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hcard4 (hψnn _)
          _ = (W.card : ℝ) ^ 4 * ψ (τ / T ^ η) := by ring
      -- The bump majorises the interval `[-L, L]`.
      have hmemψ : ∀ τ ∈ Set.Icc (-L) L, 1 ≤ ψ (τ / T ^ η) := by
        intro τ hτ
        apply hψge1
        have hpos : 0 < T ^ η := Real.rpow_pos_of_pos hTpos η
        obtain ⟨hτ1, hτ2⟩ := hτ
        constructor
        · rw [le_div_iff₀ hpos]; nlinarith [hL, hTeta1, hτ1]
        · rw [div_le_iff₀ hpos]; nlinarith [hL, hTeta1, hτ2]
      have stepBC : ∫ τ in (-L)..L, ‖Gfun W τ‖ ^ 4
          ≤ ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4 := by
        rw [intervalIntegral.integral_of_le hLneg]
        have h1 : IntegrableOn (fun τ : ℝ => ‖Gfun W τ‖ ^ 4) (Set.Icc (-L) L) :=
          (((Gfun_continuous W).norm.pow 4).continuousOn).integrableOn_Icc
        have h2 : IntegrableOn (fun τ : ℝ => ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4)
            (Set.Icc (-L) L) := hGint.integrableOn
        have h3 : ∫ τ in Set.Ioc (-L) L, ‖Gfun W τ‖ ^ 4
            ≤ ∫ τ in Set.Icc (-L) L, ‖Gfun W τ‖ ^ 4 :=
          setIntegral_mono_set h1 (Filter.Eventually.of_forall fun τ => pow_nonneg (norm_nonneg _) 4)
            (Filter.Eventually.of_forall fun τ hτ => ⟨le_of_lt hτ.1, hτ.2⟩)
        have h4 : ∫ τ in Set.Icc (-L) L, ‖Gfun W τ‖ ^ 4
            ≤ ∫ τ in Set.Icc (-L) L, ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4 := by
          refine setIntegral_mono_on h1 h2 measurableSet_Icc fun τ hτ => ?_
          exact le_mul_of_one_le_left (pow_nonneg (norm_nonneg (Gfun W τ)) 4) (hmemψ τ hτ)
        have h5 : ∫ τ in Set.Icc (-L) L, ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4
            ≤ ∫ τ in Set.univ, ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4 :=
          setIntegral_mono_set hGint.integrableOn
            (Filter.Eventually.of_forall fun τ => mul_nonneg (hψnn _) (pow_nonneg (norm_nonneg _) 4))
            (Filter.Eventually.of_forall fun τ _ => trivial)
        have h5' : ∫ τ in Set.Icc (-L) L, ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4
            ≤ ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4 := by
          simpa [setIntegral_univ] using h5
        linarith [h3, h4, h5']
      have hexp : ∀ τ : ℝ, ((‖Gfun W τ‖ ^ 4 : ℝ) : ℂ) =
          ∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)) :=
        fun τ => by simpa [Gfun, Quad, qs] using l4_expansion W τ
      have stepD : ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4
          ≤ ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
              (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))‖ := by
        have hcont_c : Continuous (fun τ : ℝ => (ψ (τ / T ^ η) : ℂ) *
            (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))) := by
          refine (Complex.continuous_ofReal.comp (hψc.comp (continuous_id.div_const _))).mul ?_
          refine continuous_finsetSum _ (fun q hq => ?_)
          have h1 : Continuous (fun τ : ℝ => qs q * τ) := continuous_const.mul continuous_id
          have h2 : Continuous (fun τ : ℝ => ((qs q * τ : ℝ) : ℂ)) :=
            Complex.continuous_ofReal.comp h1
          exact Complex.continuous_exp.comp (continuous_const.mul h2)
        have hIntc : Integrable (fun τ : ℝ => (ψ (τ / T ^ η) : ℂ) *
            (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))) := by
          refine Integrable.mono' (hψint0.norm.const_mul ((Quad W).card : ℝ))
            hcont_c.aestronglyMeasurable ?_
          filter_upwards with τ
          have hsum : ‖∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))‖ ≤ ((Quad W).card : ℝ) := by
            calc ‖∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))‖
                ≤ ∑ q ∈ Quad W, ‖cexp (I * ((qs q * τ : ℝ) : ℂ))‖ := norm_sum_le _ _
              _ = ∑ _q ∈ Quad W, (1 : ℝ) := by
                  refine Finset.sum_congr rfl fun q hq => ?_
                  rw [Complex.norm_exp]; simp
              _ = ((Quad W).card : ℝ) := by simp
          rw [norm_mul, show ‖((ψ (τ / T ^ η) : ℝ) : ℂ)‖ = |ψ (τ / T ^ η)| from by simp]
          calc |ψ (τ / T ^ η)| * ‖∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))‖
              ≤ |ψ (τ / T ^ η)| * ((Quad W).card : ℝ) :=
                mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
            _ = ((Quad W).card : ℝ) * |ψ (τ / T ^ η)| := by ring
        have hre : RCLike.re (∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
            (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))))
            = ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4 := by
          rw [← integral_re hIntc]
          refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
          simp only
          rw [← hexp τ, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
        calc ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4
            = RCLike.re (∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
                (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))) := hre.symm
          _ ≤ ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
                (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))‖ := by
              rw [RCLike.re_to_complex]
              exact Complex.re_le_norm _
      have stepE : (∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
            (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))))
          = ∑ q ∈ Quad W, ∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ)) := by
        have h1 : (∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
              (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))))
            = ∫ τ : ℝ, ∑ q ∈ Quad W, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
          simp only
          rw [Finset.mul_sum]
        rw [h1, integral_finsetSum (Quad W) (fun q hq => hscaleint' (qs q))]
      have stepF : ‖∑ q ∈ Quad W, ∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖
          ≤ ∑ q ∈ Quad W, ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖ :=
        norm_sum_le _ _
      have stepG : ∑ q ∈ Quad W, ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖
          ≤ (energy W : ℝ) * (T ^ η * A) + ((Quad W).card : ℝ) * (K * T ^ (η * (1 - (j : ℝ)))) := by
        refine quad_sum_bound_2 (A := T ^ η * A) (Kfar := K * T ^ (η * (1 - (j : ℝ))))
          (mul_nonneg hKnn (Real.rpow_nonneg hTnn _)) (fun q => ?_)
        rw [hKdef]
        exact term_bound_2 hψc hψcs hAbound hCjbound hT1 hη (qs q)
      calc ∫ τ in (-L)..L, ‖Gfun W τ‖ ^ 4
          ≤ ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4 := stepBC
        _ ≤ ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
              (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))‖ := stepD
        _ = ‖∑ q ∈ Quad W, ∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖ := by
            rw [stepE]
        _ ≤ ∑ q ∈ Quad W, ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖ :=
            stepF
        _ ≤ (energy W : ℝ) * (T ^ η * A) +
              ((Quad W).card : ℝ) * (K * T ^ (η * (1 - (j : ℝ)))) := stepG
        _ ≤ (A + 16 * K + 1) * (N : ℝ) ^ ε * (energy W : ℝ) := by
            refine le_trans (add_le_add le_rfl hKfar_bound) ?_
            exact final_arith_2 hTA henergy1 hNeps hKnn
        _ = (A + 16 * ((2 * Real.pi) ^ j * Cj) + 1) * (N : ℝ) ^ ε * (energy W : ℝ) := by
            rw [hKdef]
    · have hempty : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hWne
      subst hempty
      simp [Gfun, Submission.GM.energy]

/-- **GM Lemma 8.3 on an arbitrary fixed interval `[1/C, C]`.**

The assembly of §10 needs the `L⁴` bound for `|R|²` (via `∫ (ψ₁ R̃²)² ≤ sup ψ₁² ∫ R̃⁴ ≤ C ∫ ‖R‖⁴`)
on the support `[1/4,4]` of the smoothing bump `ψ₂`, not only on `[1,2]`.  This is
`Work.GM.S3.R_l4` with `[1,2]` replaced by `[1/C, C]`:

for every `C ≥ 1` and every `ε > 0` there are `C' > 0`, `N₀` such that for every `N ≥ N₀` and every
`W ⊆ [0, M N]` that is `(M N)^ε`-separated,

`∫_{1/C}^{C} ‖R(v)‖⁴ dv ≤ C' * N^ε * E(W)`.

Proof: identical to `Work.GM.S3.R_l4` (the special case `C = 2`): change variables
`v = exp(-2πτ)` and use a smooth bump `ψ(τ/T^η)` majorizing the (now `[1/C,C]`-adapted) range
together with Poisson summation, which counts the tuples with `|t₁+t₂-t₃-t₄| ≤ T^{-η} ≤ 1`. -/
theorem R_l4_interval :
    ∀ C : ℝ, 1 ≤ C → ∀ ε : ℝ, 0 < ε → ∃ C' : ℝ, 0 < C' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∫ v in (1 / C)..C, ‖Submission.GM.Rfun W v‖ ^ 4 ≤
        C' * (N : ℝ) ^ ε * (Submission.GM.energy W : ℝ) := by
  intro C hC ε hε
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hLnn : 0 ≤ Real.log C := Real.log_nonneg hC
  obtain ⟨C', hC'pos, N₀, hN₀⟩ := R_l4_interval_core (Real.log C) hLnn ε hε
  refine ⟨C * C', mul_pos hCpos hC'pos, N₀, ?_⟩
  intro N hN W hWsub hWsep
  -- change variables `v = e^τ`, `τ ∈ [-log C, log C]`
  have hsub := integral_exp_subst_general (a := 1 / C) (b := C) (by positivity) hCpos
    (fun v => ‖Rfun W v‖ ^ 4)
  have hlow : Real.log (1 / C) = -Real.log C := by rw [one_div, Real.log_inv]
  rw [hsub, hlow]
  have hint : ∀ τ : ℝ, ‖Rfun W (Real.exp τ)‖ ^ 4 = ‖Gfun W τ‖ ^ 4 :=
    fun τ => by rw [Rfun_eq_Gfun_exp]
  simp_rw [hint]
  -- `e^τ ≤ e^{log C} = C` on `[-log C, log C]`
  have hmono : ∫ τ in (-Real.log C)..Real.log C, Real.exp τ * ‖Gfun W τ‖ ^ 4
      ≤ C * ∫ τ in (-Real.log C)..Real.log C, ‖Gfun W τ‖ ^ 4 := by
    have hbase : ∫ τ in (-Real.log C)..Real.log C, Real.exp τ * ‖Gfun W τ‖ ^ 4
        ≤ ∫ τ in (-Real.log C)..Real.log C, C * ‖Gfun W τ‖ ^ 4 := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
      · exact (Real.continuous_exp.mul ((Gfun_continuous W).norm.pow 4)).intervalIntegrable _ _
      · exact (continuous_const.mul ((Gfun_continuous W).norm.pow 4)).intervalIntegrable _ _
      · intro τ hτ
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) 4)
        calc Real.exp τ ≤ Real.exp (Real.log C) := Real.exp_le_exp.mpr hτ.2
          _ = C := Real.exp_log hCpos
    simpa only [intervalIntegral.integral_const_mul] using hbase
  calc ∫ τ in (-Real.log C)..Real.log C, Real.exp τ * ‖Gfun W τ‖ ^ 4
      ≤ C * ∫ τ in (-Real.log C)..Real.log C, ‖Gfun W τ‖ ^ 4 := hmono
    _ ≤ C * (C' * (N : ℝ) ^ ε * (energy W : ℝ)) :=
        mul_le_mul_of_nonneg_left (hN₀ N hN W hWsub hWsep) hCpos.le
    _ = (C * C') * (N : ℝ) ^ ε * (energy W : ℝ) := by ring

end Work.GM.S3
