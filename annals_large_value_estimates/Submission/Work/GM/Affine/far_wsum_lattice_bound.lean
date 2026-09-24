import Mathlib
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.ghatFar_eq_sum_Wfar
import Submission.Work.GM.Affine.summable_int_inv_one_add_abs_pow

/-!
# Lattice bound for the far weight of GM §9

The three coherent weights `Wwin`, `Wtail`, `Wfar` introduced in
`Submission/Work/GM/Affine/far_part_defs.lean` are (a truncation of) the `m₃`-sum

`W(y) = M₃ Σ_{ℓ ∈ ℤ} ψ̂₁(M₃(ℓ - y))`

over a subset of the integers.  Since `ψ̂₁` is the Fourier transform of a `C^∞` compactly
supported bump, it decays faster than any polynomial, so the *full* sum is summable and
bounded uniformly in `M₃ ≥ 1` and in `y` — the number of integers contributing is at most
proportional to the length of the interval, and their weights decay.  Hence each of the three
weights satisfies a *uniform* bound, and since the statement asks only for a factor
`(1 + |y|)² ≥ 1` on the right, the bound may be taken independent of `y` as well.

The estimates here are deliberately crude: the right hand side of the target is so generous
that no sharpness is needed, only summability of `Σ_ℓ ‖ψ̂₁(M₃(ℓ-y))‖` with a constant
independent of `M₃ ≥ 1` and `y`.
-/

namespace Work.GM.Affine

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

noncomputable section

/-- Every real number has an integer within distance `1/2` (the nearest integer). -/
lemma exists_int_abs_sub_le_half (y : ℝ) : ∃ n : ℤ, |y - (n : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊y + 1 / 2⌋, ?_⟩
  rw [abs_le]
  exact ⟨by have h := Int.floor_le (y + 1 / 2); linarith,
         by have h := Int.lt_floor_add_one (y + 1 / 2); linarith⟩

/-- Comparison of the shifted reciprocal-square kernels.  If `n` is within `1/2` of `y` and
`1 ≤ M₃`, then `(1 + |ℓ - n|)/2 ≤ 1 + M₃|ℓ - y|`, whence the reciprocal-square inequality
below (squaring both sides). -/
lemma div_ker_le {y : ℝ} {n : ℤ} (hn : |y - (n : ℝ)| ≤ 1 / 2) {M₃ Cdec : ℝ}
    (hM₃ : 1 ≤ M₃) (hCdec : 0 < Cdec) (ℓ : ℤ) :
    Cdec / (1 + M₃ * |(ℓ : ℝ) - y|) ^ 2 ≤
      4 * Cdec / (1 + |(ℓ : ℝ) - (n : ℝ)|) ^ 2 := by
  have hM₃nn : 0 ≤ M₃ := by linarith
  set d : ℝ := |(ℓ : ℝ) - (n : ℝ)| with hd
  set e : ℝ := |(ℓ : ℝ) - y| with he
  have he0 : 0 ≤ e := by rw [he]; exact abs_nonneg _
  have hd0 : 0 ≤ d := by rw [hd]; exact abs_nonneg _
  have hdn : d - e ≤ |y - (n : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub ((ℓ : ℝ) - (n : ℝ)) ((ℓ : ℝ) - y)
    have h2 : ((ℓ : ℝ) - (n : ℝ)) - ((ℓ : ℝ) - y) = y - (n : ℝ) := by ring
    rw [← hd, ← he, h2] at h
    exact h
  have hkey : (1 + d) / 2 ≤ 1 + M₃ * e := by
    by_cases h : d ≤ 1
    · have : 0 ≤ M₃ * e := mul_nonneg hM₃nn he0
      linarith
    · push Not at h
      have he2 : d / 2 ≤ e := by linarith [hdn, h]
      have hprod : 0 ≤ (M₃ - 1) * e := mul_nonneg (by linarith) he0
      nlinarith [hprod, he2]
  have h2 : 1 + d ≤ 2 * (1 + M₃ * e) := by linarith
  have hnn : 0 ≤ 1 + d := by linarith
  have hkey2 : (1 + d) ^ 2 ≤ 4 * (1 + M₃ * e) ^ 2 := by
    have h3 : (1 + d) ^ 2 ≤ (2 * (1 + M₃ * e)) ^ 2 := pow_le_pow_left₀ hnn h2 2
    nlinarith [h3]
  have hnum : 0 < (1 + M₃ * e) ^ 2 := by positivity
  have hden : 0 < (1 + d) ^ 2 := by positivity
  rw [div_le_div_iff₀ hnum hden]
  nlinarith [hkey2, hCdec]

/-- An indicator-truncated sum of a summable family is bounded by the bound on the full series:
`‖Σ_ℓ [p ℓ] f ℓ‖ ≤ C` whenever `Σ_ℓ ‖f ℓ‖ ≤ C`. -/
lemma norm_tsum_ite_le_of {f : ℤ → ℂ} (p : ℤ → Prop) [DecidablePred p] {C : ℝ}
    (hsumm : Summable fun ℓ => ‖f ℓ‖) (hC : (∑' ℓ : ℤ, ‖f ℓ‖) ≤ C) :
    ‖∑' ℓ : ℤ, (if p ℓ then f ℓ else 0)‖ ≤ C := by
  have hsumm' : Summable fun ℓ : ℤ => ‖(if p ℓ then f ℓ else 0)‖ := by
    refine Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _) (fun ℓ => ?_) hsumm
    by_cases h : p ℓ
    · simp [h]
    · simp [h]
  calc ‖∑' ℓ : ℤ, (if p ℓ then f ℓ else 0)‖ ≤ ∑' ℓ : ℤ, ‖(if p ℓ then f ℓ else 0)‖ :=
        norm_tsum_le_tsum_norm hsumm'
    _ ≤ ∑' ℓ : ℤ, ‖f ℓ‖ := Summable.tsum_le_tsum (fun ℓ => by
          by_cases h : p ℓ <;> simp [h]) hsumm' hsumm
    _ ≤ C := hC

/-- **Uniform summability and bound for the shifted series of `‖ψ̂₁‖`.**

There is `C > 0` such that for every `M₃ ≥ 1` and every `y` the series
`Σ_ℓ ‖ψ̂₁(M₃(ℓ - y))‖` converges and is bounded by `C`.  The constant is independent of both
`M₃` and `y`: the weights decay like `(1 + M₃|ℓ - y|)^{-2}` and the integers are spread out
at unit spacing. -/
lemma tsum_norm_psi1hat_shift_le (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₃ y : ℝ), 1 ≤ M₃ →
      Summable (fun ℓ : ℤ => ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖) ∧
      (∑' ℓ : ℤ, ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖) ≤ C := by
  obtain ⟨Cdec, hCdec, hdec⟩ := psi1hat_decay K hK 2
  set S : ℝ := ∑' k : ℤ, (1 : ℝ) / (1 + |((k : ℤ) : ℝ)|) ^ 2 with hSdef
  have hSsum : Summable (fun k : ℤ => (1 : ℝ) / (1 + |((k : ℤ) : ℝ)|) ^ 2) :=
    summable_int_inv_one_add_abs_pow 2 (by norm_num)
  have hSnn : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg (fun k => by positivity)
  refine ⟨4 * Cdec * S + 1, by linarith [mul_nonneg hCdec.le hSnn], ?_⟩
  intro M₃ y hM₃
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  obtain ⟨n, hn⟩ := exists_int_abs_sub_le_half y
  -- The dominating sequence, indexed by the nearest integer `n` to `y`.
  have hbase : Summable (fun ℓ : ℤ => (1 : ℝ) / (1 + |(ℓ : ℝ) - (n : ℝ)|) ^ 2) := by
    have h := (Equiv.summable_iff (f := fun k : ℤ => (1 : ℝ) / (1 + |((k : ℤ) : ℝ)|) ^ 2)
        (Equiv.addRight (-n))).mpr hSsum
    refine h.congr (fun ℓ => ?_)
    simp only [Function.comp_apply, Equiv.coe_addRight, Int.cast_add, Int.cast_neg,
      sub_eq_add_neg]
  set G : ℤ → ℝ := fun ℓ => 4 * Cdec / (1 + |(ℓ : ℝ) - (n : ℝ)|) ^ 2 with hGdef
  have hGsumm : Summable G := by
    rw [hGdef]
    refine (hbase.mul_left (4 * Cdec)).congr (fun ℓ => ?_)
    rw [div_eq_mul_one_div, one_div]
    ring
  have hGtsum : (∑' ℓ : ℤ, G ℓ) = 4 * Cdec * S := by
    rw [hGdef, hSdef]
    have hshift : (∑' ℓ : ℤ, (1 : ℝ) / (1 + |(ℓ : ℝ) - (n : ℝ)|) ^ 2)
        = ∑' k : ℤ, (1 : ℝ) / (1 + |((k : ℤ) : ℝ)|) ^ 2 := by
      rw [← Equiv.tsum_eq (Equiv.addRight (-n))
        (fun k : ℤ => (1 : ℝ) / (1 + |((k : ℤ) : ℝ)|) ^ 2)]
      refine tsum_congr (fun ℓ => ?_)
      simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_neg, sub_eq_add_neg]
    rw [show (fun ℓ : ℤ => 4 * Cdec / (1 + |(ℓ : ℝ) - (n : ℝ)|) ^ 2)
          = (fun ℓ : ℤ => 4 * Cdec * ((1 : ℝ) / (1 + |(ℓ : ℝ) - (n : ℝ)|) ^ 2)) from by
        funext ℓ; rw [div_eq_mul_one_div]]
    rw [tsum_mul_left, hshift]
  have hpt : ∀ ℓ : ℤ, ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖ ≤ G ℓ := by
    intro ℓ
    have h1 : ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖ ≤
        Cdec / (1 + |M₃ * ((ℓ : ℝ) - y)|) ^ 2 := hdec _
    have h2 : |M₃ * ((ℓ : ℝ) - y)| = M₃ * |(ℓ : ℝ) - y| := by
      rw [abs_mul, abs_of_pos hM₃pos]
    rw [h2] at h1
    exact le_trans h1 (div_ker_le hn hM₃ hCdec ℓ)
  have hsumm : Summable (fun ℓ : ℤ => ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖) :=
    Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _) hpt hGsumm
  refine ⟨hsumm, ?_⟩
  calc (∑' ℓ : ℤ, ‖psi1hat K (M₃ * ((ℓ : ℝ) - y))‖) ≤ ∑' ℓ : ℤ, G ℓ :=
        Summable.tsum_le_tsum hpt hsumm hGsumm
    _ = 4 * Cdec * S := hGtsum
    _ ≤ 4 * Cdec * S + 1 := by linarith

theorem far_wsum_lattice_bound (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₃ B y : ℝ), 1 ≤ M₃ → 2 ≤ B →
      ‖Wwin K M₃ B y‖ ≤ C * M₃ * (1 + |y|) ^ 2 ∧
      ‖Wtail K M₃ B y‖ ≤ C * M₃ * (1 + |y|) ^ 2 ∧
      ‖Wfar K M₃ y‖ ≤ C * M₃ * (1 + |y|) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := tsum_norm_psi1hat_shift_le K hK
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro M₃ B y hM₃ hB
  have hM₃nn : 0 ≤ M₃ := by linarith
  obtain ⟨hsumm, hbound⟩ := hC₀ M₃ y hM₃
  have hcte : 0 ≤ C₀ + 1 := by linarith
  have hsq : (1 : ℝ) ≤ (1 + |y|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg y])
  have hbase : (0 : ℝ) ≤ (C₀ + 1) * M₃ := mul_nonneg hcte hM₃nn
  -- A truncated sum of the `ψ̂₁`-family is bounded by `C₀`.
  have key : ∀ {p : ℤ → Prop} [DecidablePred p],
      ‖∑' ℓ : ℤ, (if p ℓ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0)‖ ≤ C₀ := by
    intro p _
    exact norm_tsum_ite_le_of p hsumm hbound
  -- The final step from `M₃ * C₀` to the displayed right hand side.
  have fin : ∀ {T : ℂ}, ‖T‖ ≤ C₀ → M₃ * ‖T‖ ≤ (C₀ + 1) * M₃ * (1 + |y|) ^ 2 := by
    intro T hT
    have h1 : M₃ * ‖T‖ ≤ (C₀ + 1) * M₃ := by nlinarith
    have h2 : (C₀ + 1) * M₃ ≤ (C₀ + 1) * M₃ * (1 + |y|) ^ 2 :=
      le_mul_of_one_le_right hbase hsq
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := key (p := fun ℓ : ℤ => 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃)
    unfold Wwin
    rw [norm_mul]
    have hnormM : ‖((M₃ : ℝ) : ℂ)‖ = M₃ := by simp [abs_of_nonneg hM₃nn]
    rw [hnormM]
    exact fin h
  · have h := key (p := fun ℓ : ℤ => B / M₃ < |(ℓ : ℝ) - y| ∧ 2 / M₃ < |(ℓ : ℝ) - y|)
    unfold Wtail
    rw [norm_mul]
    have hnormM : ‖((M₃ : ℝ) : ℂ)‖ = M₃ := by simp [abs_of_nonneg hM₃nn]
    rw [hnormM]
    exact fin h
  · have h := key (p := fun ℓ : ℤ => |(ℓ : ℝ) - y| > 2 / M₃)
    unfold Wfar
    rw [norm_mul]
    have hnormM : ‖((M₃ : ℝ) : ℂ)‖ = M₃ := by simp [abs_of_nonneg hM₃nn]
    rw [hnormM]
    exact fin h

end

end Work.GM.Affine
