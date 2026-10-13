import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.eFamEneAux
import Submission.Work.FTS.PhiStar.Series.eFamSupDefs
import Submission.Work.FTS.PhiStar.Series.eFamSupAux.ug_bound
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.eFam_growth_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptQSmooth.CleanAng

set_option maxHeartbeats 1000000

open scoped Real
open Work.FTS.PhiStar.Gegenbauer (eFam gC)

/-! ## 7. The two base cases of the induction -/

/-- **The `θ`-derivative of `eFam m`.**  The radial energy bound `ene m ≤ (Npsi m)²` of
`Series.eFamSupDefs` gives `|(ug m)' x| ≤ Npsi m`, and `ug_bound` gives
`|ug m x| ≤ √(Npsi m)·√(1-x²)`.  Since `(eFam m)' θ = (ug m)'(sin θ) + sin θ·(ug m)(sin θ)/cos²θ`
the two combine into `|(eFam m)' θ| ≤ Npsi m + √(Npsi m)/cos θ`. -/
lemma abs_deriv_eFam_le (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |deriv (eFam m) θ| ≤ Work.FTS.PhiStar.Series.Npsi m
      + Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hsinI : Real.sin θ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [Real.pi_pos, hθ.2]),
      Real.sin_le_one θ⟩
  have hNpos : 0 < Work.FTS.PhiStar.Series.Npsi m := Work.FTS.PhiStar.Series.Npsi_pos m
  -- `|(ug m)'| ≤ Npsi m`
  have hdu : |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)|
      ≤ Work.FTS.PhiStar.Series.Npsi m := by
    have hle := Work.FTS.PhiStar.Series.ene_le m hsinI
    have hnn : 0 ≤ Work.FTS.PhiStar.Series.Npsi m *
        ((1 - (Real.sin θ) ^ 2) * (gC (2 * m + 1) (Real.sin θ)
          * gC (2 * m + 1) (Real.sin θ))) := by
      have h1 : 0 ≤ 1 - (Real.sin θ) ^ 2 := by nlinarith [Real.sin_sq_le_one θ]
      have h2 : 0 ≤ gC (2 * m + 1) (Real.sin θ) * gC (2 * m + 1) (Real.sin θ) :=
        mul_self_nonneg _
      exact mul_nonneg (le_of_lt hNpos) (mul_nonneg h1 h2)
    have hsq : (deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)) ^ 2
        ≤ Work.FTS.PhiStar.Series.Npsi m * Work.FTS.PhiStar.Series.Npsi m := by
      have hen : Work.FTS.PhiStar.Series.ene m (Real.sin θ)
          = deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)
              * deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)
            + Work.FTS.PhiStar.Series.Npsi m *
              ((1 - (Real.sin θ) ^ 2) * (gC (2 * m + 1) (Real.sin θ)
                * gC (2 * m + 1) (Real.sin θ))) := rfl
      rw [hen] at hle
      nlinarith [hle, hnn, sq_nonneg (deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ))]
    calc |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)|
        = Real.sqrt ((deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (Work.FTS.PhiStar.Series.Npsi m * Work.FTS.PhiStar.Series.Npsi m) :=
          Real.sqrt_le_sqrt hsq
      _ = Work.FTS.PhiStar.Series.Npsi m := Real.sqrt_mul_self (le_of_lt hNpos)
  -- `|ug m (sin θ)| ≤ √(Npsi m)·cos θ`
  have hgu : |Work.FTS.PhiStar.Series.ug m (Real.sin θ)|
      ≤ Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ := by
    have h := Work.FTS.PhiStar.Series.eFamSupAux.ug_bound m hsinI
    have h1 : (Work.FTS.PhiStar.Series.ug m (Real.sin θ)) ^ 2
        ≤ (Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hNpos)]
      have hs : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
        have h2 := Real.sin_sq_add_cos_sq θ
        linarith
      rw [hs] at h
      linarith [h]
    calc |Work.FTS.PhiStar.Series.ug m (Real.sin θ)|
        = Real.sqrt ((Work.FTS.PhiStar.Series.ug m (Real.sin θ)) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = |Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ| := Real.sqrt_sq_eq_abs _
      _ = Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ :=
          abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hcos))
  -- the derivative identity
  have hderiv : deriv (eFam m) θ
      = deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)
        + Real.sin θ * Work.FTS.PhiStar.Series.ug m (Real.sin θ) / Real.cos θ ^ 2 := by
    have hq : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) (Real.sin θ)) (Real.sin θ) :=
      (Work.FTS.PhiStar.Series.differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => gC (2 * m + 1) (Real.sin t))
        (deriv (gC (2 * m + 1)) (Real.sin θ) * Real.cos θ) θ :=
      hq.comp θ (Real.hasDerivAt_sin θ)
    have hprod : HasDerivAt (fun t : ℝ => Real.cos t * gC (2 * m + 1) (Real.sin t))
        (-Real.sin θ * gC (2 * m + 1) (Real.sin θ)
          + Real.cos θ * (deriv (gC (2 * m + 1)) (Real.sin θ) * Real.cos θ)) θ :=
      (Real.hasDerivAt_cos θ).mul hcomp
    rw [show eFam m = fun t : ℝ => Real.cos t * gC (2 * m + 1) (Real.sin t) from rfl,
      hprod.deriv, Work.FTS.PhiStar.Series.deriv_ug m (Real.sin θ),
      show Work.FTS.PhiStar.Series.ug m (Real.sin θ)
          = (1 - (Real.sin θ) ^ 2) * gC (2 * m + 1) (Real.sin θ) from rfl]
    have hs : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
      have h2 := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hs]
    field_simp
    ring
  have hmid : |Real.sin θ| * |Work.FTS.PhiStar.Series.ug m (Real.sin θ)| / (Real.cos θ) ^ 2
      ≤ 1 * (Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ)
          / (Real.cos θ) ^ 2 := by
    refine div_le_div_of_nonneg_right (mul_le_mul (Real.abs_sin_le_one θ) hgu (abs_nonneg _)
      (by norm_num)) (by positivity)
  have hfin : 1 * (Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ)
        / (Real.cos θ) ^ 2
      = Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ := by
    field_simp
  rw [hderiv]
  calc |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)
        + Real.sin θ * Work.FTS.PhiStar.Series.ug m (Real.sin θ) / Real.cos θ ^ 2|
      ≤ |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)|
        + |Real.sin θ * Work.FTS.PhiStar.Series.ug m (Real.sin θ) / Real.cos θ ^ 2| :=
        abs_add_le _ _
    _ = |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)|
        + |Real.sin θ| * |Work.FTS.PhiStar.Series.ug m (Real.sin θ)| / (Real.cos θ) ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos (pow_pos hcos 2)]
    _ ≤ Work.FTS.PhiStar.Series.Npsi m
        + 1 * (Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ) / (Real.cos θ) ^ 2 :=
        add_le_add hdu hmid
    _ = Work.FTS.PhiStar.Series.Npsi m
        + Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ := by rw [hfin]

/-- Level `0`: `|eFam m θ| ≤ 3 (m+1)`. -/
lemma growth_zero {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ 0, ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1) := by
  refine ⟨3, by norm_num, ?_⟩
  intro m i hi θ hθ
  have hi0 : i = 0 := by omega
  subst hi0
  have hθI : θ ∈ Work.Spaces.Iθ :=
    ⟨le_of_lt (lt_of_lt_of_le hA hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hB)⟩
  have h1 := Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθI
  have h2 : Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) ≤ 3 * ((m : ℝ) + 1) := sqrt_Npsi_le m
  rw [iteratedDeriv_zero, pow_one]
  linarith [h1, h2]

/-- Levels `0` and `1`: `|eFam m θ| ≤ K (m+1)` and `|(eFam m)' θ| ≤ K (m+1)²`. -/
lemma growth_one {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2) (hAB : A ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ 1, ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1) := by
  have hBpos : 0 < B := lt_of_lt_of_le hA hAB
  have hcosB : 0 < Real.cos B := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hB⟩
  refine ⟨max 3 (6 + 3 / Real.cos B),
    le_trans (by norm_num : (0 : ℝ) ≤ 3) (le_max_left _ _), ?_⟩
  intro m i hi θ hθ
  have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_of_lt_of_le hA hθ.1, lt_of_le_of_lt hθ.2 hB⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hI.1, le_of_lt hI.2⟩
  have hp1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hp0 : (0 : ℝ) < (m : ℝ) + 1 := lt_of_lt_of_le one_pos hp1
  have hcosge : Real.cos B ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hI.1) (by linarith [Real.pi_pos, hI.2]) hθ.2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with hi0 | hi1
  · subst hi0
    rw [iteratedDeriv_zero, pow_one]
    have h1 := Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθI
    have h2 : Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) ≤ 3 * ((m : ℝ) + 1) :=
      sqrt_Npsi_le m
    have h3 : (3 : ℝ) ≤ max 3 (6 + 3 / Real.cos B) := le_max_left _ _
    have hthis : 3 * ((m : ℝ) + 1) ≤ max 3 (6 + 3 / Real.cos B) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hp0)
    linarith [h1, h2, hthis]
  · subst hi1
    rw [iteratedDeriv_one, show (1 : ℕ) + 1 = 2 from rfl]
    have h1 := abs_deriv_eFam_le m hI
    have hcospos : 0 < Real.cos θ := lt_of_lt_of_le hcosB hcosge
    have hrec : 1 / Real.cos θ ≤ 1 / Real.cos B := one_div_le_one_div_of_le hcosB hcosge
    have hN : Work.FTS.PhiStar.Series.Npsi m = (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) := rfl
    have hstep1 : Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ
        ≤ (3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := by
      rw [hN, div_eq_mul_one_div]
      calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) * (1 / Real.cos θ)
          ≤ (3 * ((m : ℝ) + 1)) * (1 / Real.cos B) :=
            mul_le_mul (sqrt_Npsi_le m) hrec (le_of_lt (one_div_pos.mpr hcospos))
              (by positivity)
        _ ≤ (3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := by
            have h1 : 3 * ((m : ℝ) + 1) ≤ 3 * ((m : ℝ) + 1) ^ 2 := by nlinarith [hp1]
            have h2 : 3 * ((m : ℝ) + 1) * (1 / Real.cos B)
                = 3 * ((m : ℝ) + 1) / Real.cos B := by ring
            have h3 : (3 / Real.cos B) * ((m : ℝ) + 1) ^ 2
                = 3 * ((m : ℝ) + 1) ^ 2 / Real.cos B := by ring
            rw [h2, h3]
            exact div_le_div_of_nonneg_right h1 (le_of_lt hcosB)
    have hkey : Work.FTS.PhiStar.Series.Npsi m
          + Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ
        ≤ (6 + 3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := by
      have hdist : (6 + 3 / Real.cos B) * ((m : ℝ) + 1) ^ 2
          = 6 * ((m : ℝ) + 1) ^ 2 + (3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := by ring
      linarith [Npsi_le_six m, hstep1, hdist]
    calc |deriv (eFam m) θ| ≤ Work.FTS.PhiStar.Series.Npsi m
            + Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ := h1
      _ ≤ (6 + 3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := hkey
      _ ≤ max 3 (6 + 3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ## 8. The induction step -/

/-- One step of the induction: from bounds for the derivatives of order `≤ k` the bounds for
order `≤ k+1` follow by differentiating the Sturm–Liouville equation once more. -/
lemma growth_step {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2)
    (Tb Sb : ℕ → ℝ) (hTb0 : ∀ i, 0 ≤ Tb i) (hSb0 : ∀ i, 0 ≤ Sb i)
    (hTb : ∀ i θ, θ ∈ Set.Icc A B →
      |iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ| ≤ Tb i)
    (hSb : ∀ i θ, θ ∈ Set.Icc A B →
      |iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ| ≤ Sb i)
    {k : ℕ} (hk : 1 ≤ k) {K : ℝ} (hK : 0 ≤ K)
    (hIH : ∀ m : ℕ, ∀ i ≤ k, ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1)) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ m : ℕ, ∀ i ≤ k + 1, ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (eFam m) θ| ≤ K' * ((m : ℝ) + 1) ^ (i + 1) := by
  set Cs : ℝ := ∑ i ∈ Finset.range (k - 1 + 1), ((k - 1).choose i : ℝ) * (Tb i + Sb i) with hCs
  have hCs0 : 0 ≤ Cs := by
    rw [hCs]
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (by positivity) (add_nonneg (hTb0 i) (hSb0 i)))
  refine ⟨max K (K * (2 * Cs + 7)), le_trans hK (le_max_left _ _), ?_⟩
  intro m i hi θ hθ
  have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_of_lt_of_le hA hθ.1, lt_of_le_of_lt hθ.2 hB⟩
  have hp1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hp0 : (0 : ℝ) < (m : ℝ) + 1 := lt_of_lt_of_le one_pos hp1
  rcases Nat.eq_or_lt_of_le hi with hik | hik
  · -- `i = k + 1`: the main case, from the differentiated equation
    subst hik
    rw [show k + 1 + 1 = k + 2 by ring]
    have key := eFam_iteratedDeriv_ode m (k - 1) hI
    rw [show k - 1 + 2 = k + 1 by omega] at key
    have hb1 : |tanSum (k - 1) (eFam m) θ| ≤ Cs * (K * ((m : ℝ) + 1) ^ (k + 2)) := by
      rw [tanSum, hCs, Finset.sum_mul]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i hi => ?_))
      have hC0 : (0 : ℝ) ≤ ((k - 1).choose i : ℝ) := by positivity
      have hu : |iteratedDeriv (k - 1 + 1 - i) (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (k + 2) :=
        le_trans (hIH m (k - 1 + 1 - i) (by omega) θ hθ)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 (by omega)) hK)
      calc |((k - 1).choose i : ℝ) *
            (iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ * iteratedDeriv (k - 1 + 1 - i) (eFam m) θ)|
          = ((k - 1).choose i : ℝ) *
            (|iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ| * |iteratedDeriv (k - 1 + 1 - i) (eFam m) θ|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hC0]
        _ ≤ ((k - 1).choose i : ℝ) * (Tb i * (K * ((m : ℝ) + 1) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hTb i θ hθ) hu (abs_nonneg _) (hTb0 i)) hC0
        _ ≤ ((k - 1).choose i : ℝ) * ((Tb i + Sb i) * (K * ((m : ℝ) + 1) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (hSb0 i))
              (mul_nonneg hK (pow_nonneg (le_of_lt hp0) _))) hC0
        _ = ((k - 1).choose i : ℝ) * (Tb i + Sb i) * (K * ((m : ℝ) + 1) ^ (k + 2)) := by ring
    have hb2 : |secSum (k - 1) (eFam m) θ| ≤ Cs * (K * ((m : ℝ) + 1) ^ (k + 2)) := by
      rw [secSum, hCs, Finset.sum_mul]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i hi => ?_))
      have hC0 : (0 : ℝ) ≤ ((k - 1).choose i : ℝ) := by positivity
      have hu : |iteratedDeriv (k - 1 - i) (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (k + 2) :=
        le_trans (hIH m (k - 1 - i) (by omega) θ hθ)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 (by omega)) hK)
      calc |((k - 1).choose i : ℝ) *
            (iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ * iteratedDeriv (k - 1 - i) (eFam m) θ)|
          = ((k - 1).choose i : ℝ) *
            (|iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ| * |iteratedDeriv (k - 1 - i) (eFam m) θ|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hC0]
        _ ≤ ((k - 1).choose i : ℝ) * (Sb i * (K * ((m : ℝ) + 1) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hSb i θ hθ) hu (abs_nonneg _) (hSb0 i)) hC0
        _ ≤ ((k - 1).choose i : ℝ) * ((Tb i + Sb i) * (K * ((m : ℝ) + 1) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left (hTb0 i))
              (mul_nonneg hK (pow_nonneg (le_of_lt hp0) _))) hC0
        _ = ((k - 1).choose i : ℝ) * (Tb i + Sb i) * (K * ((m : ℝ) + 1) ^ (k + 2)) := by ring
    have hb3 : |Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ|
        ≤ 6 * (K * ((m : ℝ) + 1) ^ (k + 2)) := by
      have hfi : |iteratedDeriv (k - 1) (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ k := by
        have h := hIH m (k - 1) (by omega) θ hθ
        rwa [show k - 1 + 1 = k by omega] at h
      have hmul : Work.FTS.PhiStar.Series.eM m * |iteratedDeriv (k - 1) (eFam m) θ|
          ≤ (6 * ((m : ℝ) + 1) ^ 2) * (K * ((m : ℝ) + 1) ^ k) :=
        mul_le_mul (eM_le_six m) hfi (abs_nonneg _) (by positivity)
      have hpow : (6 * ((m : ℝ) + 1) ^ 2) * (K * ((m : ℝ) + 1) ^ k)
          = 6 * (K * ((m : ℝ) + 1) ^ (k + 2)) := by
        rw [show k + 2 = 2 + k by omega, pow_add]
        ring
      rw [abs_mul, abs_of_nonneg (eM_nonneg m)]
      exact le_trans hmul (le_of_eq hpow)
    have htri : |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ
          - Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ|
        ≤ |tanSum (k - 1) (eFam m) θ| + |secSum (k - 1) (eFam m) θ|
          + |Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ| := by
      have h1 : |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ
            - Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ|
          ≤ |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ|
            + |Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le (tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ)
            (-(Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ))
      have h2 : |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ|
          ≤ |tanSum (k - 1) (eFam m) θ| + |secSum (k - 1) (eFam m) θ| := abs_add_le _ _
      linarith
    rw [key]
    calc |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ
          - Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ|
        ≤ Cs * (K * ((m : ℝ) + 1) ^ (k + 2)) + Cs * (K * ((m : ℝ) + 1) ^ (k + 2))
            + 6 * (K * ((m : ℝ) + 1) ^ (k + 2)) := by linarith
      _ = (2 * Cs + 6) * (K * ((m : ℝ) + 1) ^ (k + 2)) := by ring
      _ ≤ max K (K * (2 * Cs + 7)) * ((m : ℝ) + 1) ^ (k + 2) := by
        have h1 : (2 * Cs + 6) * (K * ((m : ℝ) + 1) ^ (k + 2))
            ≤ K * (2 * Cs + 7) * ((m : ℝ) + 1) ^ (k + 2) := by
          nlinarith [hCs0, hK, mul_nonneg hK (pow_nonneg (le_of_lt hp0) (k + 2))]
        exact le_trans h1
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (le_of_lt hp0) _))
  · -- `i < k + 1`, hence `i ≤ k`: monotonicity of the constant
    have hikle : i ≤ k := by omega
    refine le_trans (hIH m i hikle θ hθ) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (le_of_lt hp0) _)

/-! ## 9. The theorem -/

theorem eFam_iteratedDeriv_growth (j : ℕ) {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : θ₂ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Icc θ₁ θ₂ →
      |iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) θ| ≤ C * ((m : ℝ) + 1) ^ (j + 1) := by
  by_cases hle : θ₁ ≤ θ₂
  · choose Tb hTb using exists_bound_iteratedDeriv_tan h₁ h₂
    choose Sb hSb using exists_bound_iteratedDeriv_secsq h₁ h₂
    have hstep : ∀ k : ℕ, (∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ k, ∀ θ ∈ Set.Icc θ₁ θ₂,
          |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1)) →
        (∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ k + 1, ∀ θ ∈ Set.Icc θ₁ θ₂,
          |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1)) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        obtain ⟨K, hK0, hK⟩ := growth_one h₁ h₂ hle
        exact ⟨K, hK0, fun m i hi θ hθ => hK m i (by omega) θ hθ⟩
      · obtain ⟨K, hK0, hK⟩ := hk
        exact growth_step h₁ h₂ Tb Sb (fun i => (hTb i).1) (fun i => (hSb i).1)
          (fun i θ hθ => (hTb i).2 θ hθ) (fun i θ hθ => (hSb i).2 θ hθ) hkpos hK0 hK
    have hmain : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ k, ∀ θ ∈ Set.Icc θ₁ θ₂,
        |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1) := fun k =>
      Nat.rec (growth_zero h₁ h₂) (fun k hk => hstep k hk) k
    obtain ⟨C, hC0, hC⟩ := hmain j
    exact ⟨C, hC0, fun m θ hθ => hC m j le_rfl θ hθ⟩
  · exact ⟨0, le_refl 0, fun m θ hθ => absurd (le_trans hθ.1 hθ.2) hle⟩

end Work.FTS.PhiStar.Honesty.CptQSmooth.CleanAng
