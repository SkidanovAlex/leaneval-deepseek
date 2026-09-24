import Mathlib
import Submission.GM.Interfaces

/-!
# Objects and elementary lemmas for the area GM §§7, 8, 10 (`S3`)

Definitions used by the lemmas of this area beyond `Submission/GM/Interfaces.lean`:

* `Rtilde` -- GM (7.5), the smoothed version of `|Rfun W|` used in Propositions 7.2 and 10.1;
* elementary facts about `Rfun` and `energy` (the paper's `R` and `E(W) = E`).

Everything here is established by complete proofs (no placeholders).
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (Rfun energy Separated hhat hfun Iterm Spart nzCount)

section RfunBasics

/-- `Rfun W (-v) = Rfun W v`: `Rfun` only depends on `|v|`. -/
theorem Rfun_neg (W : Finset ℝ) (v : ℝ) : Rfun W (-v) = Rfun W v := by
  simp only [Rfun, abs_neg]

/-- The trivial bound `‖R(v)‖ ≤ |W|`. -/
theorem Rfun_norm_le_card (W : Finset ℝ) (v : ℝ) : ‖Rfun W v‖ ≤ (W.card : ℝ) := by
  have h1 : ‖Rfun W v‖ ≤ ∑ t ∈ W, ‖((|v| : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ := by
    simpa only [Rfun] using norm_sum_le (s := W) (f := fun t => ((|v| : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))
  have h2 : ∀ t ∈ W, ‖((|v| : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤ (1 : ℝ) := by
    intro t ht
    rcases eq_or_lt_of_le (abs_nonneg v) with h | h
    · -- v = 0
      have hv : (|v| : ℝ) = 0 := h.symm
      rw [hv, Complex.cpow_def]
      by_cases ht0 : (Complex.I * (t : ℂ)) = 0
      · simp [ht0]
      · simp [ht0]
    · have hpos : 0 < (|v| : ℝ) := h
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      simp
  calc ‖Rfun W v‖ ≤ ∑ t ∈ W, ‖((|v| : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ := h1
    _ ≤ ∑ t ∈ W, (1 : ℝ) := Finset.sum_le_sum h2
    _ = (W.card : ℝ) := by simp

/-- For `x > 0` and real `t`, `(x⁻¹) ^ (I t) = conj (x ^ (I t))`. -/
theorem cpow_inv_ofReal_pureImag (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) = star (((x : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
  have h1 : ((x⁻¹ : ℝ) : ℂ) = (((x : ℝ) : ℂ))⁻¹ := by simp
  have harg : (((x : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  rw [h1, Complex.inv_cpow _ _ harg]
  have hnorm : ‖((x : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    rw [show (Complex.I * (t : ℂ)).re = 0 by rw [Complex.I_mul_re]; simp]
    simp
  rw [Complex.inv_eq_conj hnorm]
  rfl

/-- `‖(x^{it} - 1)‖ ≤ |t| * |log x|` for `x > 0`. -/
theorem cpow_sub_one_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖((x : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)) - 1‖ ≤ |t| * abs (Real.log x) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
  have hlog : Complex.log ((x : ℝ) : ℂ) = ((Real.log x : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.log_re, Complex.ofReal_re]
    · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le]
      simp
  rw [Complex.cpow_def, if_neg hxne, hlog,
    show ((Real.log x : ℝ) : ℂ) * (Complex.I * (t : ℂ)) =
      Complex.I * ((t * Real.log x : ℝ) : ℂ) by push_cast; ring]
  calc ‖Complex.exp (Complex.I * ((t * Real.log x : ℝ) : ℂ)) - 1‖ ≤ ‖(t * Real.log x : ℝ)‖ :=
        Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |t| * abs (Real.log x) := by rw [Real.norm_eq_abs, abs_mul]

/-- Lower bound for `R` near `1`: if `|t| ≤ T` for all `t ∈ W` and
`|log |v|| ≤ 1/(2T)` with `v ≠ 0`, then every term `|v|^{it}` is within `1/2` of `1` and hence
`‖Rfun W v‖ ≥ |W|/2`.  (Used to convert `|W|²` bounds into `sup f` bounds for the smoothed `|R|²`.) -/
theorem Rfun_lower_near_one (W : Finset ℝ) {T v : ℝ} (hT : 0 < T) (hW : ∀ t ∈ W, |t| ≤ T)
    (hv : v ≠ 0) (hv' : abs (Real.log |v|) ≤ 1 / (2 * T)) :
    (W.card : ℝ) / 2 ≤ ‖Rfun W v‖ := by
  have habs : 0 < |v| := abs_pos.mpr hv
  set Z : ℝ → ℂ := fun t => (((|v| : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ)) with hZ
  have hRfun : Rfun W v = ∑ t ∈ W, Z t := rfl
  have hterm : ∀ t ∈ W, ‖Z t - 1‖ ≤ (1:ℝ)/2 := by
    intro t ht
    have h1 : ‖Z t - 1‖ ≤ |t| * abs (Real.log |v|) := cpow_sub_one_le habs t
    have ht' : |t| ≤ T := hW t ht
    have h2 : |t| * abs (Real.log |v|) ≤ (1:ℝ)/2 := by
      calc |t| * abs (Real.log |v|) ≤ T * (1 / (2 * T)) :=
            mul_le_mul ht' hv' (abs_nonneg _) (le_of_lt hT)
        _ = (1:ℝ)/2 := by field_simp
    linarith
  have hsum2 : ∑ _t ∈ W, (1:ℝ)/2 = (W.card : ℝ) * (1/2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsum : ∑ t ∈ W, ‖Z t - 1‖ ≤ (W.card : ℝ) * (1/2) :=
    (Finset.sum_le_sum hterm).trans hsum2.le
  have hkey : (W.card : ℝ) - ∑ t ∈ W, ‖Z t - 1‖ ≤
      ‖(∑ t ∈ W, (1:ℂ)) + ∑ t ∈ W, (Z t - 1)‖ := by
    have h3 : ‖∑ t ∈ W, (1:ℂ)‖ ≤ ‖(∑ t ∈ W, (1:ℂ)) + ∑ t ∈ W, (Z t - 1)‖
        + ‖∑ t ∈ W, (Z t - 1)‖ := by
      have h := norm_add_le ((∑ t ∈ W, (1:ℂ)) + ∑ t ∈ W, (Z t - 1)) (-(∑ t ∈ W, (Z t - 1)))
      have h' : ((∑ t ∈ W, (1:ℂ)) + ∑ t ∈ W, (Z t - 1)) + (-(∑ t ∈ W, (Z t - 1)))
          = ∑ t ∈ W, (1:ℂ) := by abel
      rw [h', norm_neg] at h
      exact h
    have h4 : ‖∑ t ∈ W, (Z t - 1)‖ ≤ ∑ t ∈ W, ‖Z t - 1‖ := norm_sum_le W _
    have h5 : ‖∑ t ∈ W, (1:ℂ)‖ = (W.card : ℝ) := by simp
    linarith
  have hsplit : (∑ t ∈ W, Z t) = (∑ t ∈ W, (1:ℂ)) + ∑ t ∈ W, (Z t - 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t ht => by ring
  rw [hRfun, hsplit]
  linarith [hkey, hsum]

/-- `Rfun W (1/v) = conj (Rfun W v)` for `v ≠ 0` (GM's remark after Prop 7.1). -/
theorem Rfun_one_div (W : Finset ℝ) {v : ℝ} (hv : v ≠ 0) :
    Rfun W (1/v) = star (Rfun W v) := by
  have habs : |1/v| = (|v|)⁻¹ := by rw [one_div, abs_inv]
  rw [Rfun, Rfun, habs, star_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rcases eq_or_lt_of_le (abs_nonneg v) with h | h
  · exfalso
    have : |v| = 0 := h.symm
    exact hv (abs_eq_zero.mp this)
  · exact cpow_inv_ofReal_pureImag |v| h t

/-- Each summand of `Rfun` is continuous away from `0`. -/
theorem cpow_term_continuousAt (t : ℝ) {v : ℝ} (hv : v ≠ 0) :
    ContinuousAt (fun v : ℝ => (((|v| : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ))) v := by
  have hbase : ContinuousAt (fun v : ℝ => (((|v| : ℝ)) : ℂ)) v :=
    (Complex.continuous_ofReal.comp continuous_abs).continuousAt
  refine hbase.cpow continuousAt_const ?_
  rw [Complex.mem_slitPlane_iff]
  left
  simpa using abs_pos.mpr hv

/-- `Rfun W` is continuous at every `v ≠ 0` (at `0` it may jump when `0 ∈ W`). -/
theorem continuousAt_Rfun (W : Finset ℝ) {v : ℝ} (hv : v ≠ 0) : ContinuousAt (Rfun W) v := by
  classical
  induction W using Finset.induction with
  | empty =>
      have h : Rfun (∅ : Finset ℝ) = fun _ : ℝ => (0 : ℂ) := by
        funext u; rw [Rfun]; simp
      rw [h]
      exact continuousAt_const
  | insert t W ht ih =>
      have hfun : Rfun (insert t W) =
          fun u => (((|u| : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ)) + Rfun W u := by
        funext u
        rw [Rfun, Rfun]
        rw [Finset.sum_insert ht]
      rw [hfun]
      exact (cpow_term_continuousAt t hv).add ih

/-- `‖Rfun W‖²` is continuous at every `v ≠ 0`. -/
theorem continuousAt_normSq_Rfun (W : Finset ℝ) {v : ℝ} (hv : v ≠ 0) :
    ContinuousAt (fun v : ℝ => ‖Rfun W v‖ ^ 2) v :=
  ((continuousAt_Rfun W hv).norm.pow 2)

/-- `‖Rfun W (1/v)‖ = ‖Rfun W v‖` for `v ≠ 0`. -/
theorem Rfun_norm_one_div (W : Finset ℝ) {v : ℝ} (hv : v ≠ 0) :
    ‖Rfun W (1/v)‖ = ‖Rfun W v‖ := by
  rw [Rfun_one_div W hv, norm_star]

end RfunBasics

section EnergyBasics

/-- The paper's `E(W) = #{(t₁,t₂,t₃,t₄) ∈ W⁴ : |t₁+t₂-t₃-t₄| ≤ 1}` is at least `|W|²`
(use the tuples `(t,t',t,t')`). -/
theorem card_mul_self_le_energy (W : Finset ℝ) : W.card * W.card ≤ energy W := by
  classical
  have h : (W ×ˢ W).card ≤ ((W ×ˢ W ×ˢ W ×ˢ W).filter
      (fun q : ℝ × ℝ × ℝ × ℝ => |q.1 + q.2.1 - q.2.2.1 - q.2.2.2| ≤ 1)).card := by
    refine Finset.card_le_card_of_injOn (fun p : ℝ × ℝ => (p.1, p.2, p.1, p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1, hp.2, hp.1, hp.2⟩, by simp⟩
    · intro p hp q hq hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 hpq.2.1
  rw [Finset.card_product] at h
  unfold Submission.GM.energy
  exact h

/-- `E(W) ≤ |W|⁴`. -/
theorem energy_le_card_pow_four (W : Finset ℝ) : energy W ≤ W.card ^ 4 := by
  classical
  have hcard : ((W ×ˢ W ×ˢ W ×ˢ W) : Finset (ℝ × ℝ × ℝ × ℝ)).card = W.card ^ 4 := by
    simp [Finset.card_product, pow_succ]
    ring
  rw [energy, ← hcard]
  exact Finset.card_filter_le _ _

end EnergyBasics

section Bumps

/-- `ψ` is a smooth non-negative bump supported on `u ∈ [1/C, C]` with `ψ 1 = 1` and uniformly
bounded derivatives (this is the shape of GM's `ψ̃₂` and of the `ψ₁` of Proposition 10.1). -/
def IsBumpAtOne (ψ : ℝ → ℝ) (C : ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ x, 0 ≤ ψ x) ∧
    (∀ x, ψ x ≠ 0 → x ∈ Set.Icc (1 / C) C) ∧ ψ 1 = 1 ∧
    (∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |iteratedDeriv j ψ x| ≤ c)

/-- `ψ` is a smooth non-negative bump supported on `|x| ≤ C` with `ψ 0 = 1` and uniformly bounded
derivatives (the shape of GM's `ψ̃₁`). -/
def IsBumpAtZero (ψ : ℝ → ℝ) (C : ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ x, 0 ≤ ψ x) ∧
    (∀ x, ψ x ≠ 0 → |x| ≤ C) ∧ ψ 0 = 1 ∧
    (∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |iteratedDeriv j ψ x| ≤ c)

end Bumps

section Rtilde

/-- GM (7.5): the smoothed version of `|R|`,
`Rtilde(u) = (∫ N M ψ₁(N M (u - u')) ψ₂(u') |R(u')|² du')^{1/2}`. -/
noncomputable def Rtilde (W : Finset ℝ) (N : ℕ) (M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (∫ u' : ℝ, (N : ℝ) * M * ψ₁ ((N : ℝ) * M * (u - u')) * ψ₂ u' *
    ‖Rfun W u'‖ ^ 2)

/-- GM (7.5) without the square root: `|Rtilde|²`. -/
noncomputable def RtildeSq (W : Finset ℝ) (N : ℕ) (M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ u' : ℝ, (N : ℝ) * M * ψ₁ ((N : ℝ) * M * (u - u')) * ψ₂ u' * ‖Rfun W u'‖ ^ 2

theorem RtildeSq_nonneg (W : Finset ℝ) (N : ℕ) (M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ)
    (hψ₁ : ∀ x, 0 ≤ ψ₁ x) (hψ₂ : ∀ x, 0 ≤ ψ₂ x) (hM : 0 ≤ M) :
    0 ≤ RtildeSq W N M ψ₁ ψ₂ u := by
  refine integral_nonneg fun u' => ?_
  have h1 : (0 : ℝ) ≤ (N : ℝ) * M := by positivity
  have h2 : (0 : ℝ) ≤ ‖Rfun W u'‖ ^ 2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 (hψ₁ _)) (hψ₂ u')) h2

theorem Rtilde_nonneg (W : Finset ℝ) (N : ℕ) (M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) :
    0 ≤ Rtilde W N M ψ₁ ψ₂ u := Real.sqrt_nonneg _

theorem Rtilde_sq (W : Finset ℝ) (N : ℕ) (M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ)
    (h : 0 ≤ RtildeSq W N M ψ₁ ψ₂ u) :
    Rtilde W N M ψ₁ ψ₂ u ^ 2 = RtildeSq W N M ψ₁ ψ₂ u := Real.sq_sqrt h

end Rtilde

end Work.GM.S3
