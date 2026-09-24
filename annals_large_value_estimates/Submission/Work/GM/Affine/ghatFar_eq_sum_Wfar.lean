import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.psi1hat_decay

/-!
# GM §9: the far part `ghatFar` as the `m₁`-sum of `Bsum · Wfar`

`ghatFar = ghat - ghatRes` keeps, inside each `m₁`-term, only the integers `ℓ` that are *far* from
`ξ/m₁` (`|ℓ - ξ/m₁| > 2/M₃`).  Since `ghat` expands as

`ghat = Σ_{m₁ ∈ R1 M₁} (1/|m₁|) · Bsum(ξ/m₁) · Wsum(ξ/m₁)`,

with `Wsum(x) = M₃ Σ_ℓ ψ̂₁(M₃(ℓ-x))`, the difference is the same sum with the resonance weight `Wsum`
replaced by its *far* part

`Wfar(x) = M₃ Σ_ℓ [|ℓ-x| > 2/M₃] ψ̂₁(M₃(ℓ-x))`.

This is the identity `Wsum = M₃ · (resonant sum) + Wfar`, which requires the summability of the
sequence `ℓ ↦ ψ̂₁(M₃(ℓ-x))` over `ℤ` — supplied here from the faster-than-polynomial decay of `ψ̂₁`
(`psi1hat_decay`, a consequence of `ψ₁` being `C^∞` with compact support).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- **Eventual polynomial bound for `ℓ ↦ ψ̂₁(M₃(ℓ-x))`.**

If `‖ψ̂₁‖ ≤ C/(1+|y|)²` then, along the cofinite filter of `ℤ`, the sequence `ψ̂₁(M₃(ℓ-x))` is
bounded by `(4C/M₃²)·|ℓ|⁻²`: for large `|ℓ|` one has `|ℓ - x| ≥ |ℓ|/2` and hence
`1 + M₃|ℓ-x| ≥ M₃|ℓ|/2`. -/
lemma psi1hat_shift_norm_bound {K M₃ x C : ℝ} (hC : 0 ≤ C) (hM₃ : 0 < M₃)
    (hdecay : ∀ y : ℝ, ‖psi1hat K y‖ ≤ C / (1 + |y|)^2) :
    ∀ᶠ ℓ : ℤ in Filter.cofinite,
      ‖psi1hat K (M₃ * ((ℓ:ℝ) - x))‖ ≤ (4 * C / M₃^2) * |(ℓ:ℝ)| ^ (-(2:ℝ)) := by
  set L : ℝ := 2 * |x| + 1 with hL
  have hev : ∀ᶠ ℓ : ℤ in Filter.cofinite, L ≤ |(ℓ:ℝ)| := by
    rw [Filter.eventually_cofinite]
    set n : ℕ := Nat.ceil (max L 0) with hn
    refine Set.Finite.subset (Set.finite_Icc (-(n:ℤ)) (n:ℤ)) ?_
    intro ℓ hℓ
    rw [Set.mem_Icc]
    have hlt : |(ℓ:ℝ)| < L := not_le.mp hℓ
    have hceil : max L 0 ≤ ((n:ℕ):ℝ) := by rw [hn]; exact Nat.le_ceil _
    have hmax : L ≤ max L 0 := le_max_left _ _
    have hlt2 : |(ℓ:ℝ)| < (n:ℝ) := lt_of_lt_of_le hlt (le_trans hmax hceil)
    have hlt3 : ((|ℓ| : ℤ) : ℝ) < ((n:ℤ):ℝ) := by
      rw [Int.cast_abs, Int.cast_natCast]; exact hlt2
    have h4 : |ℓ| < (n:ℤ) := by exact_mod_cast hlt3
    rw [abs_lt] at h4
    exact ⟨le_of_lt h4.1, le_of_lt h4.2⟩
  filter_upwards [hev] with ℓ hℓ
  have hxle : |x| ≤ |(ℓ:ℝ)| / 2 := by
    have h1 : |x| ≤ L / 2 := by rw [hL]; linarith [abs_nonneg x]
    linarith
  have hℓpos : 0 < |(ℓ:ℝ)| := lt_of_lt_of_le (by rw [hL]; positivity) hℓ
  have hdiff : |(ℓ:ℝ)| / 2 ≤ |(ℓ:ℝ) - x| := by
    have h := abs_sub_abs_le_abs_sub (ℓ:ℝ) x
    linarith
  have hM3ℓ : M₃ * |(ℓ:ℝ)| / 2 ≤ |M₃ * ((ℓ:ℝ) - x)| := by
    rw [abs_mul, abs_of_pos hM₃]; nlinarith [hdiff]
  have hYnn : 0 ≤ |M₃ * ((ℓ:ℝ) - x)| := abs_nonneg _
  have hbY : M₃ * |(ℓ:ℝ)| / 2 ≤ 1 + |M₃ * ((ℓ:ℝ) - x)| := by linarith
  have hsq2 : (M₃ * |(ℓ:ℝ)| / 2)^2 ≤ (1 + |M₃ * ((ℓ:ℝ) - x)|)^2 :=
    pow_le_pow_left₀ (by positivity) hbY 2
  have hden : 0 < (M₃ * |(ℓ:ℝ)| / 2)^2 := by positivity
  have h1 : ‖psi1hat K (M₃ * ((ℓ:ℝ) - x))‖ ≤ C / (1 + |M₃ * ((ℓ:ℝ) - x)|)^2 := hdecay _
  have h2 : C / (1 + |M₃ * ((ℓ:ℝ) - x)|)^2 ≤ C / (M₃ * |(ℓ:ℝ)| / 2)^2 :=
    div_le_div_of_nonneg_left hC hden hsq2
  calc ‖psi1hat K (M₃ * ((ℓ:ℝ) - x))‖ ≤ C / (M₃ * |(ℓ:ℝ)| / 2)^2 := le_trans h1 h2
    _ = (4 * C / M₃^2) * |(ℓ:ℝ)| ^ (-(2:ℝ)) := by
        rw [Real.rpow_neg (abs_nonneg (ℓ:ℝ)), Real.rpow_ofNat]
        field_simp
        ring

/-- The sequence `ℓ ↦ ψ̂₁(M₃(ℓ-x))` is summable over `ℤ`. -/
lemma summable_psi1hat_shift (K M₃ x : ℝ) (hK : 0 < K) (hM₃ : 0 < M₃) :
    Summable (fun ℓ : ℤ => psi1hat K (M₃ * ((ℓ:ℝ) - x))) := by
  obtain ⟨C, hC, hdecay⟩ := psi1hat_decay K hK 2
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (b := (2:ℝ)) (by norm_num)).mul_left (4 * C / M₃^2)) ?_
  exact psi1hat_shift_norm_bound hC.le hM₃ hdecay

/-- The **far** sequence `ℓ ↦ [|ℓ-x| > 2/M₃] ψ̂₁(M₃(ℓ-x))` is summable over `ℤ`. -/
lemma summable_psi1hat_shift_far (K M₃ x : ℝ) (hK : 0 < K) (hM₃ : 0 < M₃) :
    Summable (fun ℓ : ℤ =>
      if |(ℓ:ℝ) - x| > 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - x)) else 0) := by
  obtain ⟨C, hC, hdecay⟩ := psi1hat_decay K hK 2
  have hb := psi1hat_shift_norm_bound (x := x) hC.le hM₃ hdecay
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (b := (2:ℝ)) (by norm_num)).mul_left (4 * C / M₃^2)) ?_
  filter_upwards [hb] with ℓ hℓ
  by_cases h : |(ℓ:ℝ) - x| > 2/M₃
  · rw [if_pos h]; exact hℓ
  · rw [if_neg h]; simp [norm_zero]; positivity

/-- **Splitting the resonance weight `Wsum` into its resonant and far parts.**

`Wsum(x) = M₃ Σ'_ℓ ψ̂₁(M₃(ℓ-x))` is the sum of `M₃ · (Σ'_ℓ [|ℓ-x| ≤ 2/M₃] ψ̂₁(M₃(ℓ-x)))`
(the resonance weight appearing in `ghatRes`) and `Wfar(x)`. -/
lemma Wsum_eq_res_add_Wfar {K M₃ x : ℝ} (hK : 0 < K) (hM₃ : 0 < M₃) :
    Wsum K M₃ x
      = (M₃ : ℂ) * (∑' ℓ : ℤ,
            if |(ℓ:ℝ) - x| ≤ 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - x)) else 0)
        + Wfar K M₃ x := by
  have hA := summable_psi1hat_shift K M₃ x hK hM₃
  have hS₂ := summable_psi1hat_shift_far K M₃ x hK hM₃
  have hS₁ : Summable (fun ℓ : ℤ =>
      if |(ℓ:ℝ) - x| ≤ 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - x)) else 0) := by
    refine (Summable.sub hA hS₂).congr (fun ℓ => ?_)
    by_cases h : |(ℓ:ℝ) - x| > 2/M₃
    · rw [if_neg (not_le.mpr h), if_pos h]; ring
    · rw [if_neg h, if_pos (le_of_not_gt h)]; ring
  have hsum : (∑' ℓ : ℤ, psi1hat K (M₃ * ((ℓ:ℝ) - x)))
      = (∑' ℓ : ℤ,
            if |(ℓ:ℝ) - x| ≤ 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - x)) else 0)
        + (∑' ℓ : ℤ,
            if |(ℓ:ℝ) - x| > 2/M₃ then psi1hat K (M₃ * ((ℓ:ℝ) - x)) else 0) := by
    rw [← Summable.tsum_add hS₁ hS₂]
    refine tsum_congr (fun ℓ => ?_)
    by_cases h : |(ℓ:ℝ) - x| > 2/M₃
    · rw [if_neg (not_le.mpr h), if_pos h]; ring
    · rw [if_neg h, if_pos (le_of_not_gt h)]; ring
  unfold Wsum Wfar
  rw [hsum]
  ring

/-- **The far part of `ghat` is the `m₁`-sum of `Bsum · Wfar`.** -/
theorem ghatFar_eq_sum_Wfar {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (ξ : ℝ) :
    ghatFar K M₁ M₂ M₃ f ξ =
      ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wfar K M₃ (ξ / (m₁ : ℝ)) := by
  have hghat := ghat_eq_sum_Bsum_Wsum hK hM₁ hM₂ hM₃ hf hcs ξ
  rw [ghatFar, hghat]
  simp only [ghatRes]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m₁ _ => ?_)
  have hsplit := Wsum_eq_res_add_Wfar (K := K) (M₃ := M₃) (x := ξ / (m₁:ℝ)) hK hM₃
  rw [hsplit]
  ring

end

end Work.GM.Affine
