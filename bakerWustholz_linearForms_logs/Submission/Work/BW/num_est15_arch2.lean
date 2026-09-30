import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.num_T
import Submission.Work.BW.split_aux
import Submission.Work.BW.arch2_D0_le
import Submission.Work.BW.arch2_Tmax_le
import Submission.Work.BW.log_ulcm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## Small helpers -/

private lemma acS_eq (K : Type*) [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ) (v : ℕ) :
    acS K r b v = 16 * (r : ℝ) * (dK K : ℝ) * (acH K b v : ℝ) := by
  simp only [acS, pS]
  push_cast
  ring

private lemma gamBound_scale {r : ℕ} (h D : ℝ) :
    (5.44 / (2 * Real.exp 1)) *
        ((((r : ℝ) - 1) * (2 * Real.exp 1) * Real.exp h * D) * Real.exp (-h))
      = 5.44 * ((r : ℝ) - 1) * D := by
  have h1 : Real.exp h * Real.exp (-h) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (5.44 / (2 * Real.exp 1)) *
        ((((r : ℝ) - 1) * (2 * Real.exp 1) * Real.exp h * D) * Real.exp (-h))
      = (5.44 / (2 * Real.exp 1)) *
          ((2 * Real.exp 1) * (((r : ℝ) - 1) * D * (Real.exp h * Real.exp (-h)))) := by ring
    _ = (5.44 / (2 * Real.exp 1)) * ((2 * Real.exp 1) * (((r : ℝ) - 1) * D * 1)) := by rw [h1]
    _ = 5.44 * ((r : ℝ) - 1) * D := by field_simp

/-- The Archimedean accounting of BW (15) at level `J`, weighted by the number of Archimedean places other than the place of `φ` (`m` plays the role of `m₀ = (InfinitePlace.mk φ).mult`). With `S = 16rdh`, `D = acD K σ`, `h = acH K b v`, `d = dK K`, `Λ = gamBound K b v σ`:
* `(d−m)(T'(1+log(1+Λ/T')) − hT') ≤ (d−1)·0.018·S·D/d` for `0 ≤ T' ≤ T*` (concavity in `T'`, maximum `Λe^{-h} ≤ 5.44(r-1)D`, and `5.44(r-1) ≤ 0.018·16rh` for `h ≥ 19`);
* `(d−m)·h·T* ≤ (d−1)·0.735·S·D/d`;
* `(d−m)·(D₀+1)h(1+log μ+2/μ) ≤ (d−1)·0.1·S·D/d` with `μ = 57rd` (for `d ≥ 2` the ratio `(1+log(57rd)+2/(57rd))/(32log(2rd))` is `≤ 0.0967`, worst case `r=d=2`; for `d = 1` both sides vanish when `m ≥ 1`);
* `(d−m)·(t₀ log u(h) − h t₀) ≤ (d−1)·0.075·S·D/d` for `t₀ ≤ T*`, using `log u(h) ≤ h log 3`. -/
theorem num_est15_arch2 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (Tst : ℝ) (hTst : Tst ≤ acT K σ) (hTst0 : 0 ≤ Tst)
    (t0 : ℕ) (ht0 : (t0 : ℝ) ≤ Tst) (m : ℝ) (hm1 : 1 ≤ m) (hmd : m ≤ (dK K : ℝ)) :
    (∀ T' : ℝ, 0 ≤ T' → T' ≤ Tst →
        ((dK K : ℝ) - m) * (T' * (1 + Real.log (1 + gamBound K b v σ / T')) - (acH K b v : ℝ) * T')
          ≤ ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ))) ∧
      (((dK K : ℝ) - m) * ((acH K b v : ℝ) * Tst)
          ≤ ((dK K : ℝ) - 1) * (0.735 * acS K r b v * acD K σ / (dK K : ℝ))) ∧
      (((dK K : ℝ) - m) * ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) *
            (1 + Real.log (57 * r * (dK K : ℝ)) + 1 / (57 * r * (dK K : ℝ)))
          + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) / (57 * r * (dK K : ℝ)))
        ≤ ((dK K : ℝ) - 1) * (0.1 * acS K r b v * acD K σ / (dK K : ℝ))) ∧
      (((dK K : ℝ) - m) * ((t0 : ℝ) * Real.log (ulcm (acH K b v)) - (acH K b v : ℝ) * t0)
        ≤ ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ))) := by
  -- basic facts
  have hr : 2 ≤ r := H.hr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hd1 : 1 ≤ dK K := Module.finrank_pos
  have hdR : (1 : ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd1
  have hd0 : (0 : ℝ) < (dK K : ℝ) := by linarith
  have hh : 19 ≤ acH K b v := (acH_lower H).1
  have hhR : (19 : ℝ) ≤ (acH K b v : ℝ) := by exact_mod_cast hh
  have hh0 : (0 : ℝ) ≤ (acH K b v : ℝ) := by linarith
  have hσ : ∀ j : Fin r, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hDpos : (0 : ℝ) < acD K σ := pD_pos hr hd1 σ hσ
  have hDnn : (0 : ℝ) ≤ acD K σ := le_of_lt hDpos
  have hS : acS K r b v = 16 * (r : ℝ) * (dK K : ℝ) * (acH K b v : ℝ) := acS_eq K b v
  have hTst_le : Tst ≤ 11.75 * (r : ℝ) * acD K σ := by
    have h0 : (0 : ℝ) ≤ (11.75 : ℝ) * (r : ℝ) * acD K σ := by positivity
    have h2 : acT K σ ≤ (11.75 : ℝ) * (r : ℝ) * acD K σ := by
      have := Nat.floor_le h0
      simpa only [acT, pT] using this
    linarith
  have hdm0 : (0 : ℝ) ≤ (dK K : ℝ) - m := by linarith
  have hdle : (dK K : ℝ) - m ≤ (dK K : ℝ) - 1 := by linarith
  have hdnn : (0 : ℝ) ≤ (dK K : ℝ) - 1 := by linarith
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- PART 1: the `Π`-part
    intro T' hT'0 hT'Tst
    have hgb : 0 ≤ gamBound K b v σ := by
      rw [gamBound]
      have h1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
      positivity
    have hunit : T' * (1 + Real.log (1 + gamBound K b v σ / T')) - (acH K b v : ℝ) * T'
        ≤ 5.44 * ((r : ℝ) - 1) * acD K σ := by
      refine le_trans (arch2_Tmax_le hhR hgb hT'0) ?_
      rw [gamBound]
      exact le_of_eq (gamBound_scale (acH K b v : ℝ) (acD K σ))
    have hX0 : (0 : ℝ) ≤ 5.44 * ((r : ℝ) - 1) * acD K σ := by
      have h1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by linarith
      positivity
    have hY1 : 0.018 * acS K r b v * acD K σ / (dK K : ℝ)
        = 0.288 * (r : ℝ) * (acH K b v : ℝ) * acD K σ := by
      rw [hS]
      field_simp
      ring
    have hXY : 5.44 * ((r : ℝ) - 1) * acD K σ
        ≤ 0.018 * acS K r b v * acD K σ / (dK K : ℝ) := by
      rw [hY1]
      apply mul_le_mul_of_nonneg_right _ hDnn
      have h1 : 5.44 * ((r : ℝ) - 1) ≤ 5.44 * (r : ℝ) := by linarith
      have h2 : 5.44 * (r : ℝ) ≤ 0.288 * (r : ℝ) * (acH K b v : ℝ) := by
        have h3 : (5.44 : ℝ) ≤ 0.288 * (acH K b v : ℝ) := by linarith
        nlinarith [mul_le_mul_of_nonneg_right h3 (le_of_lt hr0)]
      linarith
    calc ((dK K : ℝ) - m) * (T' * (1 + Real.log (1 + gamBound K b v σ / T')) - (acH K b v : ℝ) * T')
        ≤ ((dK K : ℝ) - m) * (5.44 * ((r : ℝ) - 1) * acD K σ) :=
          mul_le_mul_of_nonneg_left hunit hdm0
      _ ≤ ((dK K : ℝ) - 1) * (5.44 * ((r : ℝ) - 1) * acD K σ) :=
          mul_le_mul_of_nonneg_right hdle hX0
      _ ≤ ((dK K : ℝ) - 1) * (0.018 * acS K r b v * acD K σ / (dK K : ℝ)) :=
          mul_le_mul_of_nonneg_left hXY hdnn
  · -- PART 2: `h · T*`
    have hnumT := (num_T hr hd1 hh σ hσ).2.2.1
    have hkey : (acH K b v : ℝ) * Tst ≤ 0.735 * acS K r b v * acD K σ / (dK K : ℝ) := by
      have h1 : (acH K b v : ℝ) * Tst ≤ (acH K b v : ℝ) * (acT K σ) :=
        mul_le_mul_of_nonneg_left hTst hh0
      have h2 : (acH K b v : ℝ) * (acT K σ)
          ≤ 0.735 * acS K r b v * acD K σ / (dK K : ℝ) := by
        have h3 : (dK K : ℝ) * (acH K b v : ℝ) * (acT K σ)
            ≤ 0.735 * acS K r b v * acD K σ := by
          simpa only [acT, acS, acD, pT, pS, pD] using hnumT
        rw [le_div_iff₀ hd0]
        nlinarith [h3]
      linarith
    have hY0 : (0 : ℝ) ≤ 0.735 * acS K r b v * acD K σ / (dK K : ℝ) := by positivity
    calc ((dK K : ℝ) - m) * ((acH K b v : ℝ) * Tst)
        ≤ ((dK K : ℝ) - m) * (0.735 * acS K r b v * acD K σ / (dK K : ℝ)) :=
          mul_le_mul_of_nonneg_left hkey hdm0
      _ ≤ ((dK K : ℝ) - 1) * (0.735 * acS K r b v * acD K σ / (dK K : ℝ)) :=
          mul_le_mul_of_nonneg_right hdle hY0
  · -- PART 3: the `Θ`/`D₀`-part
    by_cases hd_one : dK K = 1
    · have hm1' : m = 1 := by
        have h1 : (dK K : ℝ) = 1 := by rw [hd_one]; norm_num
        linarith
      rw [hd_one, hm1']
      norm_num
    · have hd2 : 2 ≤ dK K := by omega
      have hD0le := arch2_D0_le hr hd2 σ hσ
      have hY2 : 0.1 * acS K r b v * acD K σ / (dK K : ℝ)
          = 1.6 * (r : ℝ) * (acH K b v : ℝ) * acD K σ := by
        rw [hS]
        field_simp
        ring
      have hkey : (acH K b v : ℝ) *
            ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (1 + Real.log (57 * r * (dK K : ℝ)) + 1 / (57 * r * (dK K : ℝ)))
              + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) / (57 * r * (dK K : ℝ)))
          ≤ 0.1 * acS K r b v * acD K σ / (dK K : ℝ) := by
        have h1 : (acH K b v : ℝ) *
              ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (1 + Real.log (57 * r * (dK K : ℝ)) + 1 / (57 * r * (dK K : ℝ)))
                + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) / (57 * r * (dK K : ℝ)))
            ≤ (acH K b v : ℝ) * (1.6 * (r : ℝ) * pD r (dK K) σ) :=
          mul_le_mul_of_nonneg_left hD0le hh0
        rw [hY2]
        have : (acH K b v : ℝ) * (1.6 * (r : ℝ) * pD r (dK K) σ)
            = 1.6 * (r : ℝ) * (acH K b v : ℝ) * pD r (dK K) σ := by ring
        linarith [h1, this.le, this.ge]
      have hY3 : (0 : ℝ) ≤ 0.1 * acS K r b v * acD K σ / (dK K : ℝ) := by positivity
      have hsplit : ((dK K : ℝ) - m) * ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) *
              (1 + Real.log (57 * r * (dK K : ℝ)) + 1 / (57 * r * (dK K : ℝ)))
            + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (acH K b v : ℝ) / (57 * r * (dK K : ℝ)))
          = ((dK K : ℝ) - m) * ((acH K b v : ℝ) *
              ((((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (1 + Real.log (57 * r * (dK K : ℝ)) + 1 / (57 * r * (dK K : ℝ)))
                + (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) / (57 * r * (dK K : ℝ)))) := by
        ring
      rw [hsplit]
      calc ((dK K : ℝ) - m) * ((acH K b v : ℝ) * _)
          ≤ ((dK K : ℝ) - m) * (0.1 * acS K r b v * acD K σ / (dK K : ℝ)) :=
            mul_le_mul_of_nonneg_left hkey hdm0
        _ ≤ ((dK K : ℝ) - 1) * (0.1 * acS K r b v * acD K σ / (dK K : ℝ)) :=
            mul_le_mul_of_nonneg_right hdle hY3
  · -- PART 4: the `u(h)^{t₀}` term
    have hlogu : Real.log (ulcm (acH K b v)) ≤ 1.1 * (acH K b v : ℝ) := log_ulcm_le _ hh
    have ht0nn : (0 : ℝ) ≤ (t0 : ℝ) := Nat.cast_nonneg _
    have hloguh : Real.log (ulcm (acH K b v)) - (acH K b v : ℝ) ≤ 0.1 * (acH K b v : ℝ) := by linarith
    have h1 : (t0 : ℝ) * (Real.log (ulcm (acH K b v)) - (acH K b v : ℝ))
        ≤ (t0 : ℝ) * (0.1 * (acH K b v : ℝ)) := mul_le_mul_of_nonneg_left hloguh ht0nn
    have ht0T : (t0 : ℝ) ≤ 11.75 * (r : ℝ) * acD K σ := le_trans ht0 hTst_le
    have h2 : (t0 : ℝ) * (0.1 * (acH K b v : ℝ))
        ≤ 1.2 * (r : ℝ) * (acH K b v : ℝ) * acD K σ := by
      have h3 : (t0 : ℝ) * (0.1 * (acH K b v : ℝ))
          ≤ (11.75 * (r : ℝ) * acD K σ) * (0.1 * (acH K b v : ℝ)) :=
        mul_le_mul_of_nonneg_right ht0T (by positivity)
      have h4 : (11.75 * (r : ℝ) * acD K σ) * (0.1 * (acH K b v : ℝ))
          = 1.175 * (r : ℝ) * (acH K b v : ℝ) * acD K σ := by ring
      rw [h4] at h3
      linarith [h3, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 0.025) (le_of_lt hr0))
        (mul_nonneg hh0 hDnn)]
    have hkey : (t0 : ℝ) * Real.log (ulcm (acH K b v)) - (acH K b v : ℝ) * t0
        ≤ 1.2 * (r : ℝ) * (acH K b v : ℝ) * acD K σ := by
      have heq : (t0 : ℝ) * Real.log (ulcm (acH K b v)) - (acH K b v : ℝ) * t0
          = (t0 : ℝ) * (Real.log (ulcm (acH K b v)) - (acH K b v : ℝ)) := by ring
      rw [heq]; linarith
    have hY4 : 0.075 * acS K r b v * acD K σ / (dK K : ℝ)
        = 1.2 * (r : ℝ) * (acH K b v : ℝ) * acD K σ := by
      rw [hS]
      field_simp
      ring
    have hY4nn : (0 : ℝ) ≤ 0.075 * acS K r b v * acD K σ / (dK K : ℝ) := by positivity
    calc ((dK K : ℝ) - m) * ((t0 : ℝ) * Real.log (ulcm (acH K b v)) - (acH K b v : ℝ) * t0)
        ≤ ((dK K : ℝ) - m) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ)) := by
          rw [hY4]
          exact mul_le_mul_of_nonneg_left hkey hdm0
      _ ≤ ((dK K : ℝ) - 1) * (0.075 * acS K r b v * acD K σ / (dK K : ℝ)) :=
          mul_le_mul_of_nonneg_right hdle hY4nn

end Work.BW
