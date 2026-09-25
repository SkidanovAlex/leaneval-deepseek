import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump
import Submission.Work.BourgainPlan.Maximal.iw_superset

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-! ### Two elementary lemmas underlying the narrow support of `η_n`

The bump `η_n(ξ) = η(2^{n(d−χ)} iwRep ξ)` is supported in the ball of radius
`(1/2)·2^{−n(d−χ)}`, while the MST scale is `ε_{n^l} = exp(−(n^l)^{1/(10l)}) = exp(−n^{1/10})`.
Since `exp(−n^{1/10})` decays only subexponentially, it dominates `(1/2)·2^{−n(d−χ)}` for large
`n` **whatever** the sign of the (fixed, positive) exponent `d − χ` is: this is the classical
"exponential beats subexponential" statement, which we need in the form
`n^{1/10} ≤ ((d−χ) log 2)·n` for large `n`. -/

/-- **Sublinear growth of `n^{1/10}`.** For every `B > 0` there is `n₀` with
`n^{1/10} ≤ B · n` for all `n ≥ n₀`. (Compare tenth powers: the claim is equivalent to
`n ≤ (B n)^{10}`, i.e. to `1 ≤ B^{10} n^9`, and `n ≥ B^{-10} ≥ 1` gives
`B^{10} n^9 ≥ B^{10}·B^{-10} = 1`.) -/
lemma rpow_ten_inv_le_mul (B : ℝ) (hB : 0 < B) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ (1 / 10 : ℝ) ≤ B * (n : ℝ) := by
  refine ⟨max 1 ⌈(B⁻¹) ^ 10⌉₊, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnB : (B⁻¹) ^ 10 ≤ (n : ℝ) := by
    have h : ((⌈(B⁻¹) ^ 10⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    exact le_trans (Nat.le_ceil _) h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have h9 : (n : ℝ) ≤ (n : ℝ) ^ 9 := le_self_pow₀ hnR1 (by norm_num)
  have hprod : (1 : ℝ) ≤ B ^ 10 * (n : ℝ) ^ 9 := by
    have heq : B ^ 10 * (B⁻¹) ^ 10 = 1 := by rw [← mul_pow]; field_simp
    have hle : B ^ 10 * (B⁻¹) ^ 10 ≤ B ^ 10 * (n : ℝ) ^ 9 :=
      mul_le_mul_of_nonneg_left (le_trans hnB h9) (by positivity)
    linarith
  have hnle : (n : ℝ) ≤ (B * (n : ℝ)) ^ 10 := by
    have h : (n : ℝ) * 1 ≤ (n : ℝ) * (B ^ 10 * (n : ℝ) ^ 9) :=
      mul_le_mul_of_nonneg_left hprod hnpos.le
    have heq : (n : ℝ) * (B ^ 10 * (n : ℝ) ^ 9) = (B * (n : ℝ)) ^ 10 := by ring
    linarith
  have hpow : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 10 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num
  have hkey : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 10 ≤ (B * (n : ℝ)) ^ 10 := by
    rw [hpow]; exact hnle
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (10 : ℕ) ≠ 0)).mp hkey

/-- **The MST scale is `exp(−n^{1/10})`**: with `ρ = mstRho l = 1/(10l)` and `N = n^l`,
`N^ρ = n^{1/10}`. -/
lemma mstRho_pow_eq (l : ℕ) (hl : 1 ≤ l) (n : ℕ) (hn : 1 ≤ n) :
    ((n ^ l : ℕ) : ℝ) ^ (mstRho l) = (n : ℝ) ^ (1 / 10 : ℝ) := by
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
    linarith
  rw [mstRho, Nat.cast_pow, ← Real.rpow_natCast (n : ℝ) l,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  congr 1
  field_simp

/-- **The narrow support of the MST level bumps `η_n` at the scale `ε_N = exp(−N^ρ)`** — the support hypothesis of the MST §3–§5 statements (`mst_minor_lp_per_n`'s `hsupp`), discharged: for `ρ = mstRho l = 1/(10l)`, `N = n^l`, `d ≥ 1`, `χ < d` and a bump `η` supported in `[-1/2,1/2]`, the level bump `mstEta d χ η n (ξ) = η (2^{n(d−χ)} · iwRep ξ)` vanishes off the ball of radius `iwEps (mstRho l) (n^l) = exp(−n^{1/10})` for all `n` beyond an explicit threshold. -/
theorem mstEta_support (l : ℕ) (hl : 1 ≤ l) (d : ℕ) (hd : 1 ≤ d) (χ : ℝ) (hχ : 0 < χ)
    (hχd : χ < (d : ℝ)) (η : ℝ → ℂ) (hcont : Continuous η)
    (hsupp : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) (n ^ l) < ‖ξ‖ →
        Work.BourgainPlan.Maximal.mstEta d χ η n ξ = 0 := by
  have hδ : 0 < (d : ℝ) - χ := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set B : ℝ := ((d : ℝ) - χ) * Real.log 2 with hBdef
  have hBpos : 0 < B := by rw [hBdef]; exact mul_pos hδ hlog2
  obtain ⟨n₁, hn₁⟩ := rpow_ten_inv_le_mul B hBpos
  refine ⟨max n₁ 1, fun n hn ξ hξ => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hkey : (n : ℝ) ^ (1 / 10 : ℝ) ≤ B * (n : ℝ) := hn₁ n (le_trans (le_max_left _ _) hn)
  -- the multiplier `c = 2^{n(d−χ)}` of the level bump, and its support radius `1/(2|c|)`
  set c : ℝ := (2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) with hcdef
  have hcnn : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) - χ) := by positivity
  have hc1 : 1 ≤ c := by rw [hcdef]; exact Real.one_le_rpow (by norm_num) hcnn
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  -- the support radius is below the MST scale `iwEps (mstRho l) (n^l) = exp(−n^{1/10})`
  have hle : 1 / (2 * |c|) ≤ iwEps (mstRho l) (n ^ l) := by
    have hcast : 1 / (2 * |c|) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by
      rw [hcdef, abs_of_pos (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) _),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    rw [hcast, iwEps]
    have hexp : (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) = Real.exp (-(B * (n : ℝ))) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hBdef]
      congr 1
      ring
    rw [hexp, mstRho_pow_eq l hl n hn1]
    calc (1 / 2 : ℝ) * Real.exp (-(B * (n : ℝ)))
        ≤ 1 * Real.exp (-(B * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
      _ = Real.exp (-(B * (n : ℝ))) := one_mul _
      _ ≤ Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := Real.exp_le_exp.mpr (by linarith)
  -- the narrow-support lemma for the rescaled bump
  have hlt : 1 / (2 * |c|) < ‖ξ‖ := lt_of_le_of_lt hle hξ
  have hzero := (memLp_scaled_bump (η := η) (c := c) (by rwa [abs_of_pos hcpos]) hcont hsupp).2 ξ hlt
  simpa [mstEta_apply, hcdef] using hzero

end

end Work.BourgainPlan.Maximal
