import Submission.FUP.Spec
import Submission.FUP.BoxPorosity
import Submission.FUP.Damping
import Submission.FUP.Cubes
import Submission.FUP.Porosity

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators
open Submission.FUP

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Appendix A.1: Cohen's Theorem 1.4 from Han–Schlag's Theorem 5.1

This module formalises §A.1 of Cohen's paper: the comparison between Han–Schlag's original
statement of their conditional fractal uncertainty principle (their Theorem 5.1, recorded as
`Spec.han_schlag_statement`) and the form used in §6 of the paper
(`Spec.FUP_conditional_damping_statement`).

The comparison consists of three parts, exactly as in the paper:

* **Box porosity.**  Han–Schlag use *box porosity* of `X` rather than porosity on balls; the
  appendix lemma `compare_porosity` (formalised as `boxPorous_of_porousOnBalls_lt`) passes from
  one to the other, at scale `L = max 3 ⌈4√d/ν⌉`.
* **Damping.**  Han–Schlag use `ℓ₁` damping functions, `ℓ₂` ones are used in §6; the comparison
  is `admitsL1Damping_of_admitsL2Damping` (with the factor `√d`), together with monotonicity in
  the parameter `c₁` and the choice `c₂ = c₂f σ`.  Session 53: the damping parameter required by
  `Spec.han_schlag_statement` is `(4L)⁻¹` (half of the published `(2L)⁻¹`), which is what the proof
  of Han–Schlag's Corollary 4.2 needs (see `Submission/FUP/HSLocalize.lean`); the comparison with
  the `ℓ₂` damping parameter `ν/(20√d)` still holds because `νL ≤ 5√d` for `L = max 3 ⌈4√d/ν⌉`.
* **Scales.**  Han–Schlag's dilation factor `L^{-n}` is matched with the dilation parameter `s`
  of §6, and the scale `N = ⌈h⁻¹⌉`.
-/

/-- The `L`-adic scale `L^{-n}` written as a `ℤ`-power, matching Han–Schlag's notation. -/
lemma zpow_hss (L n : ℕ) : (L : ℝ) ^ (-(n : ℤ)) = hss L n := by
  rw [hss, zpow_neg, zpow_natCast]

/-- `hss L` is antitone. -/
lemma hss_anti {L m n : ℕ} (hL : 1 ≤ L) (hmn : m ≤ n) : hss L n ≤ hss L m := by
  rw [hss, hss]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hL) hmn)

/-- **Appendix A.1: Theorem 1.4 from Han–Schlag's Theorem 5.1.** -/
theorem FUP_conditional_damping_of_han_schlag (hd : 1 ≤ d)
    (hHS : Spec.han_schlag_statement (d := d)) :
    Spec.FUP_conditional_damping_statement (d := d) := by
  intro ν hν hνhalf c₂ α hc₂ hα
  obtain ⟨c₃star, hc₃star, hHS'⟩ := hHS
  have hdn : (0 : ℝ) < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  refine ⟨c₃star * Real.sqrt (d : ℝ), by positivity, ?_⟩
  intro c₃ hc₃
  have hc₃' : c₃ / Real.sqrt (d : ℝ) ∈ Set.Ioo 0 c₃star := by
    refine ⟨div_pos hc₃.1 hdn, ?_⟩
    rw [div_lt_iff₀ hdn]
    exact hc₃.2
  -- the scale at which Han–Schlag's theorem is applied
  set L : ℕ := max 3 ⌈4 * Real.sqrt (d : ℝ) / ν⌉₊ with hLdef
  have hL3 : 3 ≤ L := le_max_left _ _
  have hLpos : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL3r : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hL4 : 4 * Real.sqrt (d : ℝ) ≤ ν * L := by
    have hceil : 4 * Real.sqrt (d : ℝ) / ν ≤ (⌈4 * Real.sqrt (d : ℝ) / ν⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hle : 4 * Real.sqrt (d : ℝ) / ν ≤ (L : ℝ) :=
      le_trans hceil (by exact_mod_cast le_max_right 3 _)
    rw [div_le_iff₀ hν] at hle
    linarith
  -- the damping parameter `c₁` comparison
  have hc1 : ν / (20 * Real.sqrt (d : ℝ)) ≤ (4 * L : ℝ)⁻¹ := by
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    have hL_le : ν * L ≤ 5 * Real.sqrt (d : ℝ) := by
      have hmax : (L : ℝ) ≤ 4 * Real.sqrt (d : ℝ) / ν + 1 := by
        rw [hLdef, Nat.cast_max]
        refine max_le ?_ (le_of_lt (Nat.ceil_lt_add_one (le_of_lt (div_pos (by positivity) hν))))
        have h2 : (2 : ℝ) ≤ 4 * Real.sqrt (d : ℝ) / ν := by
          rw [le_div_iff₀ hν]
          nlinarith [hνhalf, hsqrt1]
        linarith
      have h1 : ν * (4 * Real.sqrt (d : ℝ) / ν + 1) = 4 * Real.sqrt (d : ℝ) + ν := by
        field_simp
      have h2 := mul_le_mul_of_nonneg_left hmax hν.le
      rw [h1] at h2
      nlinarith [h2, hνhalf, hsqrt1]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 20 * Real.sqrt (d : ℝ))]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * L)]
    linarith [hL_le]
  obtain ⟨β, C, N₀, hβ, hC, hN₀, hHSapp⟩ :=
    hHS' L hL3 c₂ (c₃ / Real.sqrt (d : ℝ)) α hc₂ hc₃' hα
  -- the constant of the conclusion
  set M₀ : ℝ := max 1 N₀ with hM₀def
  have hM₀pos : 0 < M₀ := lt_of_lt_of_le (by norm_num) (le_max_left 1 N₀)
  have hM₀ge : N₀ ≤ M₀ := le_max_right 1 N₀
  set Cf : ℝ := max C (M₀ ^ β) with hCfdef
  have hCfpos : 0 < Cf :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hM₀pos β) (le_max_right C (M₀ ^ β))
  refine ⟨β, Cf, hβ, hCfpos, ?_⟩
  intro h X Y hh hXsub hpor hYsub hdamp f hfsupp
  have hhpos : 0 < h := hh.1
  have hh1 : h < 1 := hh.2
  set N : ℝ := (⌈h⁻¹⌉₊ : ℝ) with hNdef
  have hNge : h⁻¹ ≤ N := by rw [hNdef]; exact Nat.le_ceil _
  have hNlt : N < h⁻¹ + 1 := by
    rw [hNdef]; exact_mod_cast Nat.ceil_lt_add_one (le_of_lt (inv_pos.mpr hhpos))
  have hNpos : 0 < N := lt_of_lt_of_le (inv_pos.mpr hhpos) hNge
  rcases lt_or_ge N N₀ with hcase | hcase
  · -- the remaining range of scales: the trivial `L²` bound
    have hle : (eLpNorm (X.indicator (f : ℝᵈ → ℂ)) 2).toReal ≤ ‖f‖ := by
      rw [Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono (fun x => ?_))
      by_cases hx : x ∈ X
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    refine le_trans hle ?_
    have h1 : h⁻¹ < N₀ := lt_of_le_of_lt hNge hcase
    have hprod_gt : 1 < N₀ * h := by
      have := mul_lt_mul_of_pos_right h1 hhpos
      rwa [inv_mul_cancel₀ hhpos.ne'] at this
    have hp1 : N₀ ^ β ≤ Cf := by
      refine le_trans (Real.rpow_le_rpow hN₀.le hM₀ge hβ.le) ?_
      rw [hCfdef]; exact le_max_right _ _
    have hp2 : 1 ≤ N₀ ^ β * h ^ β := by
      rw [← Real.mul_rpow hN₀.le hhpos.le]
      exact Real.one_le_rpow hprod_gt.le hβ.le
    have hone : (1 : ℝ) ≤ Cf * h ^ β :=
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ N₀ ^ β * h ^ β := by rw [one_mul]; exact hp2
        _ ≤ Cf * h ^ β := mul_le_mul_of_nonneg_right hp1 (Real.rpow_nonneg hhpos.le β)
    calc ‖f‖ = 1 * ‖f‖ := (one_mul _).symm
      _ ≤ Cf * h ^ β * ‖f‖ := mul_le_mul_of_nonneg_right hone (norm_nonneg f)
  · -- the main case: Han–Schlag's theorem applies
    have hYsub' : Y ⊆ cube (-N) N :=
      Set.Subset.trans hYsub (cube_subset (by linarith [hNge]) hNge)
    have hhss_le : ∀ m : ℕ, hss L m ≤ 1 := fun m => by
      rw [hss]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    have hhss_gt : ∀ n : ℕ, (L : ℝ) ^ (n + 1) ≤ N → h < hss L n := by
      intro n hn
      have hle : (L : ℝ) ^ n ≤ (h⁻¹ + 1) / L := by
        rw [le_div_iff₀ hLr]
        calc (L : ℝ) ^ n * L = (L : ℝ) ^ (n + 1) := (pow_succ _ _).symm
          _ ≤ N := hn
          _ ≤ h⁻¹ + 1 := le_of_lt hNlt
      have hinv := inv_anti₀ (pow_pos hLr n) hle
      rw [inv_div] at hinv
      have h3 : h < L / (h⁻¹ + 1) := by
        rw [lt_div_iff₀ (by positivity)]
        have : h * (h⁻¹ + 1) = 1 + h := by field_simp
        rw [this]; linarith [hL3r, hh1]
      exact lt_of_lt_of_le h3 (by simpa [hss] using hinv)
    have hbox : ∀ n : ℕ, (L : ℝ) ^ (n + 1) ≤ N → BoxPorous L (n + 1) X := by
      intro n hn
      refine boxPorous_of_porousOnBalls_lt hLpos hL4 hhpos
        (PorousOnBalls.mono hpor le_rfl le_rfl le_rfl hhpos) ?_
      intro m hm
      have hmn : m ≤ n := by omega
      exact ⟨lt_of_lt_of_le (hhss_gt n hn) (hss_anti (by omega : 1 ≤ L) hmn), hhss_le m⟩
    have hdamp' : ∀ n : ℕ, (L : ℝ) ^ (n + 1) ≤ N → ∀ η : ℝᵈ,
        (∀ i : Fin d, η i ∈ Set.Icc (-N * (L : ℝ) ^ (-(n : ℤ)) - 3)
            (N * (L : ℝ) ^ (-(n : ℤ)) + 3)) →
        AdmitsL1Damping ((fun z : ℝᵈ => η + z) ''
          (addSet ((fun y : ℝᵈ => (L : ℝ) ^ (-(n : ℤ)) • y) '' Y) (cube (-4) 4)))
          ((4 * L : ℝ)⁻¹) c₂ (c₃ / Real.sqrt (d : ℝ)) α := by
      intro n hn η hη
      have hsn : hss L n ∈ Set.Ioc h 1 := ⟨hhss_gt n hn, hhss_le n⟩
      have hsIoc : (L : ℝ) ^ (-(n : ℤ)) ∈ Set.Ioc h 1 := by
        rw [zpow_hss]; exact hsn
      have hspos : 0 < (L : ℝ) ^ (-(n : ℤ)) := by
        rw [zpow_hss]; exact hss_pos hLpos n
      have hsle : (L : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
        rw [zpow_hss]; exact hhss_le n
      have hη' : ∀ i : Fin d, η i ∈ Set.Icc (-h⁻¹ * (L : ℝ) ^ (-(n : ℤ)) - 5)
          (h⁻¹ * (L : ℝ) ^ (-(n : ℤ)) + 5) := by
        intro i
        have hkey : (N - h⁻¹) * (L : ℝ) ^ (-(n : ℤ)) ≤ 2 := by
          have h1 : N - h⁻¹ < 1 := by linarith
          nlinarith [hspos, hsle, h1]
        exact ⟨by linarith [(hη i).1], by linarith [(hη i).2]⟩
      exact admitsL1Damping_mono
        (admitsL1Damping_of_admitsL2Damping (hdamp _ hsIoc η hη') hd
          (le_of_lt hα.1) (le_of_lt hα.2) (le_of_lt hc₃.1))
        hc1 (le_of_lt hc₂.1) le_rfl le_rfl
    refine le_trans (hHSapp N hcase X Y hXsub hbox hYsub' hdamp' f hfsupp) ?_
    have hNinv : N⁻¹ ≤ h := by
      rw [inv_le_comm₀ hNpos hhpos]
      exact hNge
    have hpow : N ^ (-β) ≤ h ^ β := by
      have h1 : (N⁻¹) ^ β ≤ h ^ β :=
        Real.rpow_le_rpow (inv_nonneg.mpr hNpos.le) hNinv hβ.le
      rw [Real.inv_rpow hNpos.le] at h1
      rw [Real.rpow_neg hNpos.le]
      exact h1
    have hCle : C ≤ Cf := by rw [hCfdef]; exact le_max_left _ _
    calc C * N ^ (-β) * ‖f‖ ≤ C * h ^ β * ‖f‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) (norm_nonneg f)
      _ ≤ Cf * h ^ β * ‖f‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg hhpos.le β)) (norm_nonneg f)

end Submission.FUP
