import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.LayerAux
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.abel_sharp
import Submission.Work.ChenPlan.LinearSieve.JR2.budget_shift
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.T_ne_zero_le
import Submission.Work.ChenPlan.LinearSieve.RIMain.sharp_bound.sharp_layer_bound_K0
import Submission.Work.JR.abel_change_of_variables
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_integral_form
import Submission.Work.NumberTheory.Chen.APSwitchUpper.errH_transport

open Finset MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.ChenPlan.LinearSieve.JR2

noncomputable section

open Work.NumberTheory.Chen.APSwitchUpper

lemma half_le_log_two : (1:ℝ)/2 ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
  have h : (Real.exp (1/2))^2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  nlinarith [Real.exp_pos (1/2), h, h2, sq_nonneg (Real.exp (1/2) - 2)]

lemma delta_le {D Z X η : ℝ} (hD : 0 < D) (hX : X = D ^ (1/3:ℝ)) (hX2 : 2 ≤ X)
    (hZpos : 0 < Z) (hZ : X < Z) (hZnear : Z - X ≤ η) (hη0 : 0 ≤ η) :
    3 - Real.log D / Real.log Z ≤ 3 * η := by
  have hXpos : 0 < X := by linarith
  have hlogZpos : 0 < Real.log Z := Real.log_pos (by linarith)
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogD : Real.log D = 3 * Real.log X := by
    rw [hX, Real.log_rpow hD]; ring
  have h1 : 3 - Real.log D / Real.log Z = 3 * (Real.log Z - Real.log X) / Real.log Z := by
    rw [hlogD]; field_simp
  rw [h1]
  have h2 : Real.log Z - Real.log X ≤ η/X := by
    have h3 : Real.log (Z/X) ≤ Z/X - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h4 : Real.log (Z/X) = Real.log Z - Real.log X := Real.log_div hZpos.ne' hXpos.ne'
    rw [h4] at h3
    have h5 : Z/X - 1 = (Z - X)/X := by field_simp
    rw [h5] at h3
    have h6 : (Z - X)/X ≤ η/X := div_le_div_of_nonneg_right hZnear hXpos.le
    linarith [h3, h6]
  have hlZ : (1:ℝ)/2 ≤ Real.log Z := by
    have h : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
    have h2' : Real.log X ≤ Real.log Z := Real.log_le_log hXpos (le_of_lt hZ)
    linarith [half_le_log_two]
  have h3 : 3 * (η/X) / Real.log Z ≤ 3 * η := by
    have hA : 3 * (η/X) / Real.log Z ≤ 3 * (η/X) / (1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlZ
    have hB : 3 * (η/X) / (1/2) ≤ 3 * η := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1/2)]
      have hle : η/X ≤ η * (1/2) := by
        rw [div_le_iff₀ hXpos]
        nlinarith [hη0, hX2]
      linarith [hle]
    linarith [hA, hB]
  have h4 : 3 * (Real.log Z - Real.log X) / Real.log Z ≤ 3 * (η/X) / Real.log Z := by
    refine div_le_div_of_nonneg_right ?_ hlogZpos.le
    linarith [h2]
  linarith [h3, h4]



lemma intervalIntegrable_PhiC_min (k : ℕ) (D ε X : ℝ) (hD : 0 < D) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => PhiC k D ε (min (D ^ (1/t)) X)) volume a b := by
  obtain ⟨C, hC0, hC⟩ := profC_bound (k - 1)
  set B : ℝ := C + |cCoef k ε| * Real.exp (-2) with hB
  have hmPhi : Measurable (fun u : ℝ => PhiC k D ε u) := by
    unfold PhiC
    exact ((profC_measurable (k-1)).comp (by fun_prop)).add
      ((measurable_errH.comp (by fun_prop)).const_mul _)
  have hm : Measurable (fun t : ℝ => PhiC k D ε (min (D ^ (1/t)) X)) := by
    refine hmPhi.comp ?_
    have h1 : (fun t : ℝ => min (D ^ (1/t)) X) = fun t => min (Real.exp (Real.log D * t⁻¹)) X := by
      funext t; rw [Real.rpow_def_of_pos hD, one_div]
    rw [h1]; fun_prop
  have hbound : ∀ t : ℝ, ‖PhiC k D ε (min (D^(1/t)) X)‖ ≤ B := by
    intro t
    rw [Real.norm_eq_abs]
    have h1 : |profC (k-1) (Real.log D / Real.log (min (D^(1/t)) X) - 1)| ≤ C := by
      simpa [Real.norm_eq_abs] using hC (Real.log D / Real.log (min (D^(1/t)) X) - 1)
    have h2 : |cCoef k ε * errH (Real.log D / Real.log (min (D^(1/t)) X) - 1)|
        ≤ |cCoef k ε| * Real.exp (-2) := by
      rw [abs_mul, abs_of_nonneg (errH_nonneg _)]
      exact mul_le_mul_of_nonneg_left (errH_le_exp_neg_two _) (abs_nonneg _)
    unfold PhiC
    calc |profC (k-1) (Real.log D / Real.log (min (D^(1/t)) X) - 1)
            + cCoef k ε * errH (Real.log D / Real.log (min (D^(1/t)) X) - 1)|
        ≤ |profC (k-1) (Real.log D / Real.log (min (D^(1/t)) X) - 1)|
          + |cCoef k ε * errH (Real.log D / Real.log (min (D^(1/t)) X) - 1)| := abs_add_le _ _
      _ ≤ B := by rw [hB]; linarith
  exact ⟨IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable B
          (Filter.Eventually.of_forall hbound),
         IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable B
          (Filter.Eventually.of_forall hbound)⟩


lemma isLinearRange_of_sharpNorm_zero {A : BoundingSieve} {z : ℝ} (h : SharpNorm A z 0) :
    Submission.ChenPlan.IsLinearRange A z 0 := by
  intro w z' hw hw' hz'
  have h1 := h w z' hw hw' hz'
  calc (∏ p ∈ A.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z'), (1 - A.nu p)⁻¹)
      ≤ (1 + 0) * (Real.log z' / Real.log w) := h1
    _ = (Real.log z' / Real.log w) * (1 + 0 / Real.log w) := by ring

/-- `errH s ≥ e^{-3}` for `s ≤ 3`. -/
lemma exp_neg_three_le_errH {s : ℝ} (hs : s ≤ 3) : Real.exp (-3) ≤ errH s := by
  rcases le_or_gt s 2 with h | h
  · rw [errH_of_le_two h]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [errH_eq_exp_neg (le_of_lt h) hs]
    exact Real.exp_le_exp.mpr (by linarith)

lemma pow_three_rpow (D : ℝ) (hD : 0 ≤ D) : ((D ^ (1/3:ℝ))^3) = D := by
  rw [← Real.rpow_natCast (D ^ (1/3:ℝ)) 3, ← Real.rpow_mul hD,
    show (1/3 : ℝ) * ((3:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]

lemma rpow_three_rpow (p : ℝ) (hp : 0 ≤ p) : ((p^3) ^ (1/3:ℝ)) = p := by
  rw [← Real.rpow_natCast p 3, ← Real.rpow_mul hp,
    show ((3:ℕ):ℝ) * (1/3) = 1 by norm_num, Real.rpow_one]


/-- The step identity of the allowance coefficients: `cCoef (k+1) ε` splits as
`990·ε·(99/100)^{k-1} + (99/100)·cCoef k ε`. -/
lemma cCoef_step {k : ℕ} {ε E : ℝ} (hk : 1 ≤ k) :
    cCoef (k + 1) ε * E
      = ε * 990 * (99/100:ℝ) ^ (k - 1) * E + cCoef k ε * ((99/100) * E) := by
  have hpow : (99/100:ℝ) ^ k = (99/100) ^ (k - 1) * (99/100) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  rw [cCoef_succ k ε, hpow]
  unfold cCoef
  ring

/-- **Case (B′) of the induction step of the sharp layer bound** (odd row, `1 ≤ s < 3`). -/
theorem step_small_final {A : BoundingSieve} {ε D z : ℝ} {k : ℕ} (hk : 2 ≤ k) (hkeven : Even k)
    (hB : Work.ChenPlan.LinearSieve.JR2.Budgets) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/100) (hz : 2 ≤ z)
    (hD : 1 ≤ D) (hSharp : Work.ChenPlan.LinearSieve.JR2.SharpNorm A z ε)
    (hs1 : 1 ≤ Real.log D / Real.log z) (hs3 : Real.log D / Real.log z < 3)
    (hnum : ∀ s δ : ℝ, 1 ≤ s → s ≤ 3 → 0 ≤ δ → δ ≤ 1/100000 →
      (1 + ε) * ((3 - δ) / s) * ε * Real.exp (-2)
        + (1 + ε)^2 * ((1 / s) * ((47/50) * Real.exp (-2) + δ * Real.exp (-2)))
        + 2 * δ * Real.exp (-2)
      ≤ (99/100) * Work.NumberTheory.Chen.APSwitchUpper.errH s)
    (hIH : ∀ D' z' : ℝ, 2 ≤ z' → 1 ≤ D' → Work.ChenPlan.LinearSieve.JR2.SharpNorm A z' ε →
      (Odd k → 1 ≤ Real.log D' / Real.log z') → (Even k → 2 ≤ Real.log D' / Real.log z') →
      Work.ChenPlan.LinearSieve.T A k D' z' ≤ Work.ChenPlan.LinearSieve.VfR A z' *
        (Work.NumberTheory.Chen.APSwitchUpper.profC (k - 1) (Real.log D' / Real.log z')
          + Work.ChenPlan.LinearSieve.JR2.cCoef k ε
            * Work.NumberTheory.Chen.APSwitchUpper.errH (Real.log D' / Real.log z'))) :
    Work.ChenPlan.LinearSieve.T A (k + 1) D z ≤ Work.ChenPlan.LinearSieve.VfR A z *
      (Work.NumberTheory.Chen.APSwitchUpper.profC k (Real.log D / Real.log z)
        + Work.ChenPlan.LinearSieve.JR2.cCoef (k + 1) ε
          * Work.NumberTheory.Chen.APSwitchUpper.errH (Real.log D / Real.log z)) := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hEven_succ : Even (k + 1) ↔ False := by
    constructor
    · intro h; exact (Nat.even_add_one.mp h) hkeven
    · intro h; exact h.elim
  rcases eq_or_lt_of_le hε0 with hε0' | hεpos
  · -- ### the case ε = 0: there is no prime of `P` below `z`
    subst hε0'
    have hno := Work.ChenPlan.LinearSieve.RIMain.sharp_bound.no_prime_below_of_isLinearRange_zero
      (isLinearRange_of_sharpNorm_zero hSharp)
    have hT0 : T A (k + 1) D z = 0 := by
      rw [T.eq_2 A D z k]
      refine Finset.sum_eq_zero (fun p hp => ?_)
      obtain ⟨hpmem, hpz, -⟩ := Finset.mem_filter.mp hp
      exact absurd hpz (hno p hpmem)
    rw [hT0]
    refine mul_nonneg (VfR_nonneg A z) (add_nonneg (profC_nonneg _ _) ?_)
    have hc : cCoef (k + 1) (0:ℝ) = 0 := by rw [cCoef]; ring
    rw [hc, zero_mul]
  -- ### setup
  have hz1 : 1 < z := by linarith
  have hzpos : 0 < Real.log z := Real.log_pos hz1
  have hDpos : 0 < D := by linarith
  have hlogDs : Real.log z ≤ Real.log D := by
    have h := (le_div_iff₀ hzpos).mp hs1
    linarith
  have hDz : z ≤ D := by
    have h := Real.exp_le_exp.mpr hlogDs
    rw [Real.exp_log (by linarith : (0:ℝ) < z), Real.exp_log hDpos] at h
    exact h
  have hD1 : 1 < D := lt_of_lt_of_le hz1 hDz
  have hD2 : 2 ≤ D := le_trans hz hDz
  have hlogDpos : 0 < Real.log D := Real.log_pos hD1
  have hOdd : Odd (k + 1) := (Nat.not_even_iff_odd).mp (fun h => (Nat.even_add_one.mp h) hkeven)
  have hTcond_iff : ∀ p : ℕ, Tcond (k + 1) D p ↔ (p:ℝ)^3 ≤ D := by
    intro p
    constructor
    · intro h; exact h.2 (by omega) hOdd
    · intro h; exact ⟨fun h1 => absurd h1 (by omega), fun h2 ho => h⟩
  by_cases hD8 : D < 8
  · -- ### the sum is empty
    have hempty : A.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p:ℝ) < z ∧ Tcond (k + 1) D p) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun p hp => ?_)
      rintro ⟨-, hp3⟩
      have h2 : (2:ℝ) ≤ (p:ℝ) := by
        exact_mod_cast Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
      have h8 : (8:ℝ) ≤ (p:ℝ)^3 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 3
        norm_num at this
        exact this
      have := (hTcond_iff p).mp hp3
      linarith
    rw [T.eq_2 A D z k, hempty, Finset.sum_empty]
    exact mul_nonneg (VfR_nonneg A z)
      (add_nonneg (profC_nonneg _ _) (mul_nonneg (cCoef_nonneg hε0) (errH_nonneg _)))
  -- ### main case: `D ≥ 8`
  have hD8' : (8:ℝ) ≤ D := not_lt.mp hD8
  set X : ℝ := D ^ (1/3 : ℝ) with hXdef
  have hXpos : 0 < X := Real.rpow_pos_of_pos hDpos _
  have hX3 : X ^ 3 = D := by rw [hXdef]; exact pow_three_rpow D hDpos.le
  have hXz : X < z := by
    have h : Real.log D < 3 * Real.log z := by
      have h' := (div_lt_iff₀ hzpos).mp hs3
      linarith
    have h2 : D < z^3 := by
      calc D = Real.exp (Real.log D) := (Real.exp_log hDpos).symm
        _ < Real.exp (3 * Real.log z) := Real.exp_lt_exp.mpr h
        _ = (Real.exp (Real.log z))^3 := Real.exp_nat_mul (Real.log z) 3
        _ = z^3 := by rw [Real.exp_log (by positivity : (0:ℝ) < z)]
    have h3 : D ^ (1/3:ℝ) < z := by
      have h4 := Real.rpow_lt_rpow hDpos.le h2 (by norm_num : (0:ℝ) < 1/3)
      rwa [rpow_three_rpow z (by positivity)] at h4
    rw [hXdef]
    exact h3
  have hX2 : (2:ℝ) ≤ X := by
    have h : (2:ℝ)^3 ≤ X^3 := by rw [hX3]; norm_num; linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity : (0:ℝ) ≤ X) h
  have hlogXval : Real.log D / Real.log X - 1 = 2 := by
    rw [hXdef, Real.log_rpow hDpos]
    have hne : Real.log D ≠ 0 := ne_of_gt hlogDpos
    field_simp
    norm_num
  -- ### the level `Z`
  set n : ℕ := Nat.floor X with hndef
  have hnX : (n:ℝ) ≤ X := by rw [hndef]; exact Nat.floor_le hXpos.le
  have hXn1 : X < (n:ℝ) + 1 := by rw [hndef]; exact Nat.lt_floor_add_one X
  set Z : ℝ := min (X + ε / 1000000) (min ((n:ℝ) + 1) z) with hZdef
  have hZ_gt_X : X < Z := by
    rw [hZdef]
    refine lt_min (by linarith) (lt_min hXn1 hXz)
  have hZpos : 0 < Z := lt_trans hXpos hZ_gt_X
  have hZ_le_z : Z ≤ z := by
    rw [hZdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hZ_le_n1 : Z ≤ (n:ℝ) + 1 := by
    rw [hZdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hZ_le_Xeps : Z ≤ X + ε / 1000000 := by rw [hZdef]; exact min_le_left _ _
  have hZ_near : Z - X ≤ ε / 1000000 := by linarith
  have hZjump : Z < (n:ℝ) + 1 + 1 := by linarith [hZ_le_n1]
  have hnZ : (n:ℝ) < Z := lt_of_le_of_lt hnX hZ_gt_X
  -- ### `δ := 3 - log D / log Z`
  set sZ : ℝ := Real.log D / Real.log Z with hsZdef
  have hZ1 : 1 < Z := lt_of_lt_of_le (by norm_num) (le_trans hX2 (le_of_lt hZ_gt_X))
  have hlogZpos : 0 < Real.log Z := Real.log_pos hZ1
  have hsZ_le3 : sZ ≤ 3 := by
    rw [hsZdef, div_le_iff₀ hlogZpos]
    have hlogZX : Real.log X ≤ Real.log Z := Real.log_le_log hXpos (le_of_lt hZ_gt_X)
    have h : Real.log D = 3 * Real.log X := by
      rw [hXdef, Real.log_rpow hDpos]; ring
    rw [h]
    linarith

  have hdelta_nn : 0 ≤ 3 - sZ := by linarith
  have hdelta_le : 3 - sZ ≤ 3 * (ε/1000000) :=
    delta_le hDpos hXdef hX2 hZpos hZ_gt_X hZ_near (by linarith : (0:ℝ) ≤ ε/1000000)
  have hdelta_small : 3 - sZ ≤ 1/100000 := by
    have : 3 * (ε/1000000) ≤ 1/100000 := by linarith [hε1]
    linarith
  -- ### the two filters agree
  have hpX_of_pow : ∀ p : ℕ, (p:ℝ)^3 ≤ D → (p:ℝ) ≤ X := by
    intro p hp3
    have h := Real.rpow_le_rpow (show (0:ℝ) ≤ (p:ℝ)^3 by positivity) hp3
      (by norm_num : (0:ℝ) ≤ 1/3)
    rw [rpow_three_rpow (p:ℝ) (by positivity)] at h
    exact h
  have hfilter : A.prodPrimes.primeFactors.filter (fun p : ℕ => (p:ℝ) < z ∧ Tcond (k + 1) D p)
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => (2:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) < Z) := by
    refine Finset.filter_congr (fun p hp => ?_)
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    constructor
    · rintro ⟨hpz, hT⟩
      exact ⟨by exact_mod_cast hpprime.two_le,
        lt_of_le_of_lt (hpX_of_pow p ((hTcond_iff p).mp hT)) hZ_gt_X⟩
    · rintro ⟨hp2, hpZ⟩
      have hpn : (p:ℝ) ≤ (n:ℝ) := by
        have h : (p:ℝ) < (n:ℝ) + 1 := lt_of_lt_of_le hpZ hZ_le_n1
        have h' : p < n + 1 := by exact_mod_cast h
        exact_mod_cast (by omega : p ≤ n)
      have hp3 : (p:ℝ)^3 ≤ D := by
        calc (p:ℝ)^3 ≤ X^3 := pow_le_pow_left₀ (by positivity) (le_trans hpn hnX) 3
          _ = D := hX3
      have hpz' : (p:ℝ) < z := lt_of_le_of_lt (le_trans hpn hnX) hXz
      exact ⟨hpz', (hTcond_iff p).mpr hp3⟩
  have hT : T A (k + 1) D z
      = ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (2:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) < Z),
          A.nu p * T A k (D / (p:ℝ)) (p:ℝ) := by
    rw [T.eq_2 A D z k, hfilter]
  set s : ℝ := Real.log D / Real.log z with hsdef
  have hs_pos : 0 < s := by rw [hsdef]; exact div_pos hlogDpos hzpos
  -- ### the child bounds
  have hchild : ∀ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (2:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) < Z),
      T A k (D / (p:ℝ)) (p:ℝ) ≤ VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by
    intro p hp
    obtain ⟨hpmem, hp2, hpZ⟩ := Finset.mem_filter.mp hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
    have hpn : (p:ℝ) ≤ (n:ℝ) := by
      have h : (p:ℝ) < (n:ℝ) + 1 := lt_of_lt_of_le hpZ hZ_le_n1
      have h' : p < n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : p ≤ n)
    have hpX : (p:ℝ) ≤ X := le_trans hpn hnX
    have hp3 : (p:ℝ) ^ 3 ≤ D := by
      calc (p:ℝ)^3 ≤ X^3 := pow_le_pow_left₀ (by positivity) hpX 3
        _ = D := hX3
    have hpz : (p:ℝ) < z := lt_of_le_of_lt hpX hXz
    have hDp1 : 1 ≤ D / (p:ℝ) := by
      rw [le_div_iff₀ hppos]
      have hpp3 : (p:ℝ) ≤ (p:ℝ)^3 := by
        have h1 : (1:ℝ) ≤ (p:ℝ)^2 := by nlinarith
        calc (p:ℝ) = (p:ℝ) * 1 := by ring
          _ ≤ (p:ℝ) * (p:ℝ)^2 := mul_le_mul_of_nonneg_left h1 hppos.le
          _ = (p:ℝ)^3 := by ring
      linarith
    have hσ2 : 2 ≤ Real.log (D / (p:ℝ)) / Real.log (p:ℝ) := by
      rw [le_div_iff₀ (Real.log_pos (by linarith : 1 < (p:ℝ))),
        Real.log_div (ne_of_gt hDpos) (ne_of_gt hppos)]
      have h := Real.log_le_log (by positivity : (0:ℝ) < (p:ℝ)^3) hp3
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    have hres := hIH (D / (p:ℝ)) (p:ℝ) (by linarith) hDp1 (hSharp.sub (le_of_lt hpz))
      (fun hO => absurd hkeven ((Nat.not_even_iff_odd).mpr hO)) (fun _ => hσ2)
    have hσeq : Real.log (D / (p:ℝ)) / Real.log (p:ℝ) = Real.log D / Real.log (p:ℝ) - 1 := by
      rw [Real.log_div (ne_of_gt hDpos) (ne_of_gt hppos), sub_div,
        div_self (ne_of_gt (Real.log_pos (by linarith : 1 < (p:ℝ))))]
    have hΦ : PhiC k D ε (p:ℝ)
        = profC (k - 1) (Real.log D / Real.log (p:ℝ) - 1)
          + cCoef k ε * errH (Real.log D / Real.log (p:ℝ) - 1) := rfl
    rw [hΦ, ← hσeq]
    exact hres
  have hnu_nonneg : ∀ p ∈ A.prodPrimes.primeFactors, 0 ≤ A.nu p := fun p hp =>
    le_of_lt (A.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp)
      (Nat.mem_primeFactors.mp hp).2.1)
  -- ### the majorant `Φt u = Φ (min u X)`
  set Φt : ℝ → ℝ := fun u => PhiC k D ε (min u X) with hΦtdef
  have hΦmonoX : ∀ a b : ℝ, 2 ≤ a → a ≤ b → b ≤ X → PhiC k D ε a ≤ PhiC k D ε b := by
    intro a b ha hab hbX
    have hbl : 1 < b := by linarith
    have hσb : 2 ≤ Real.log D / Real.log b - 1 := by
      have h1 : Real.log b ≤ Real.log X := Real.log_le_log (by linarith) hbX
      have h2 : 0 < Real.log b := Real.log_pos hbl
      have h3 : Real.log D / Real.log X - 1 ≤ Real.log D / Real.log b - 1 :=
        sub_le_sub_right (div_le_div_of_nonneg_left hlogDpos.le h2 h1) 1
      linarith [hlogXval]
    exact PhiC_mono' hε0 hD1 (Nat.even_iff.mp hkeven) (by linarith) hab hσb
  have hΦt_mono : ∀ a b : ℝ, 2 ≤ a → a ≤ b → b ≤ Z → Φt a ≤ Φt b := by
    intro a b ha hab hbZ
    rcases le_or_gt b X with hbX | hbX
    · have haX : a ≤ X := le_trans hab hbX
      rw [hΦtdef]
      simp only
      rw [min_eq_left haX, min_eq_left hbX]
      exact hΦmonoX a b ha hab hbX
    · by_cases haX : a ≤ X
      · have h1 : PhiC k D ε a ≤ PhiC k D ε X := hΦmonoX a X ha haX (le_refl X)
        rw [hΦtdef]
        simp only
        rw [min_eq_left haX, min_eq_right (le_of_lt hbX)]
        exact h1
      · rw [hΦtdef]
        simp only [min_eq_right (le_of_lt (not_le.mp haX)), min_eq_right (le_of_lt hbX)]
        exact le_refl _
  have hΦt_nn : ∀ a : ℝ, 2 ≤ a → a ≤ Z → 0 ≤ Φt a := fun a _ _ => PhiC_nonneg hε0 _
  have hΦt_ge : ∀ p : ℕ, (p:ℝ) ≤ X → PhiC k D ε (p:ℝ) ≤ Φt (p:ℝ) := by
    intro p hpX
    rw [hΦtdef]
    simp only [min_eq_left hpX]
    exact le_refl _
  -- ### the Abel step
  have hV : ∀ u : ℝ, 2 ≤ u → u ≤ Z →
      VfR A u ≤ VfR A Z * ((1 + ε) * (Real.log Z / Real.log u)) :=
    fun u hu huZ => VfR_le_of_sharpNorm (A := A) (z := Z) hε0 (hSharp.sub hZ_le_z) hu huZ le_rfl
  have habel := abel_sharp (A := A) (w := 2) (Z := Z) (ε := ε) hε0 (le_refl 2)
    (lt_of_le_of_lt hX2 hZ_gt_X) hV
    (Φ := Φt) hΦt_mono hΦt_nn
  have hsum : T A (k + 1) D z
      ≤ VfR A Z * (ε * Φt Z + (1 + ε) *
          ∫ u in (2:ℝ)..Z, Φt u * (Real.log Z / (u * (Real.log u)^2))) := by
    rw [hT]
    calc ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (2:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) < Z),
          A.nu p * T A k (D / (p:ℝ)) (p:ℝ)
        ≤ ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (2:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) < Z),
            A.nu p * VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          calc A.nu p * T A k (D / (p:ℝ)) (p:ℝ)
              ≤ A.nu p * (VfR A (p:ℝ) * PhiC k D ε (p:ℝ)) :=
                mul_le_mul_of_nonneg_left (hchild p hp)
                  (hnu_nonneg p (Finset.mem_filter.mp hp).1)
            _ = A.nu p * VfR A (p:ℝ) * PhiC k D ε (p:ℝ) := by ring
      _ ≤ ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => (2:ℝ) ≤ (p:ℝ) ∧ (p:ℝ) < Z),
            A.nu p * VfR A (p:ℝ) * Φt (p:ℝ) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          obtain ⟨hpmem, hp2, hpZ⟩ := Finset.mem_filter.mp hp
          have hpn : (p:ℝ) ≤ (n:ℝ) := by
            have h : (p:ℝ) < (n:ℝ) + 1 := lt_of_lt_of_le hpZ hZ_le_n1
            have h' : p < n + 1 := by exact_mod_cast h
            exact_mod_cast (by omega : p ≤ n)
          have hle := hΦt_ge p (le_trans hpn hnX)
          exact mul_le_mul_of_nonneg_left hle
            (mul_nonneg (hnu_nonneg p hpmem) (VfR_nonneg A _))
      _ ≤ VfR A Z * (ε * Φt Z + (1 + ε) *
            ∫ u in (2:ℝ)..Z, Φt u * (Real.log Z / (u * (Real.log u)^2))) := habel
  -- ### the value of `Φt` at the top
  have hΦX : PhiC k D ε X = profC (k - 1) 2 + cCoef k ε * Real.exp (-2) := by
    show profC (k - 1) (Real.log D / Real.log X - 1)
        + cCoef k ε * errH (Real.log D / Real.log X - 1) = profC (k - 1) 2 + cCoef k ε * Real.exp (-2)
    rw [hlogXval, errH_of_le_two le_rfl]
  have hΦtZ : Φt Z = profC (k - 1) 2 + cCoef k ε * Real.exp (-2) := by
    rw [hΦtdef]
    simp only
    rw [min_eq_right (le_of_lt hZ_gt_X)]
    exact hΦX
  -- ### the change of variables
  have hZ2' : (2:ℝ) ≤ Z := le_trans hX2 (le_of_lt hZ_gt_X)
  have htw3 : (3:ℝ) ≤ Real.log D / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    have h := Real.log_le_log (by norm_num : (0:ℝ) < (8:ℝ)) hD8'
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow] at h
    norm_num at h
    linarith
  have hsZpos : 0 < sZ := div_pos hlogDpos hlogZpos
  have hsZ_tw : sZ ≤ Real.log D / Real.log 2 :=
    div_le_div_of_nonneg_left hlogDpos.le (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hZ2')
  have hDpow_Z : D ^ (1 / sZ) = Z := by
    rw [hsZdef, Real.rpow_def_of_pos hDpos]
    have h : Real.log D * (1 / (Real.log D / Real.log Z)) = Real.log Z := by
      field_simp
    rw [h, Real.exp_log hZpos]
  have hDpow_tw : D ^ (1 / (Real.log D / Real.log 2)) = 2 := by
    rw [Real.rpow_def_of_pos hDpos]
    have h : Real.log D * (1 / (Real.log D / Real.log 2)) = Real.log 2 := by
      field_simp
    rw [h, Real.exp_log (by norm_num)]
  have hintPhi : IntervalIntegrable (fun t : ℝ => Φt (D ^ (1/t))) volume sZ
      (Real.log D / Real.log 2) :=
    intervalIntegrable_PhiC_min k D ε X hDpos sZ (Real.log D / Real.log 2)
  have hcv : (∫ u in (2:ℝ)..Z, Φt u * (Real.log Z / (u * (Real.log u)^2)))
      = (1/sZ) * ∫ t in sZ..(Real.log D / Real.log 2), Φt (D^(1/t)) := by
    have h := Work.JR.abel_change_of_variables (D := D) (f := Φt) hD1 (s := sZ)
      (T := Real.log D / Real.log 2) hsZpos hsZ_tw hintPhi
    rw [hDpow_Z, hDpow_tw] at h
    exact h
  -- ### the value of the integrand on the two halves
  have hval1 : ∀ t ∈ Set.uIcc sZ (3:ℝ),
      Φt (D ^ (1/t)) = profC (k - 1) 2 + cCoef k ε * Real.exp (-2) := by
    intro t ht
    rw [Set.uIcc_of_le hsZ_le3] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hsZpos ht.1
    have hDt : X ≤ D ^ (1/t) := by
      have h : D ^ (1/3:ℝ) ≤ D ^ (1/t) := by
        refine Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ D) ?_
        exact one_div_le_one_div_of_le ht0 ht.2
      rwa [← hXdef] at h
    simp only [hΦtdef]
    rw [min_eq_right hDt]
    exact hΦX
  have hval2 : ∀ t ∈ Set.uIcc (3:ℝ) (Real.log D / Real.log 2),
      Φt (D ^ (1/t)) = profC (k - 1) (t - 1) + cCoef k ε * errH (t - 1) := by
    intro t ht
    rw [Set.uIcc_of_le htw3] at ht
    rcases eq_or_lt_of_le ht.1 with h3 | h3
    · subst h3
      simp only [hΦtdef]
      rw [← hXdef, min_self, hΦX]
      rw [show (3:ℝ) - 1 = 2 by norm_num, errH_of_le_two le_rfl]
    · have ht0 : t ≠ 0 := ne_of_gt (by linarith)
      simp only [hΦtdef]
      have hDt : D ^ (1/t) ≤ X := by
        have h : D ^ (1/t) ≤ D ^ (1/3:ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ D) ?_
          exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) (le_of_lt h3)
        rwa [← hXdef] at h
      rw [min_eq_left hDt]
      exact PhiC_rpow hD1 ht0
  -- ### the integral of the majorant
  have hint : (∫ t in sZ..(Real.log D / Real.log 2), Φt (D^(1/t)))
      = (3 - sZ) * (profC (k - 1) 2 + cCoef k ε * Real.exp (-2))
        + (∫ t in (3:ℝ)..(Real.log D / Real.log 2), profC (k - 1) (t - 1))
        + cCoef k ε * (∫ t in (3:ℝ)..(Real.log D / Real.log 2), errH (t - 1)) := by
    have h1 : IntervalIntegrable (fun t : ℝ => Φt (D ^ (1/t))) volume sZ (3:ℝ) :=
      intervalIntegrable_PhiC_min k D ε X hDpos sZ 3
    have h2 : IntervalIntegrable (fun t : ℝ => Φt (D ^ (1/t))) volume (3:ℝ)
        (Real.log D / Real.log 2) :=
      intervalIntegrable_PhiC_min k D ε X hDpos 3 (Real.log D / Real.log 2)
    have hsplit1 : (∫ t in sZ..(Real.log D / Real.log 2), Φt (D^(1/t)))
        = (∫ t in sZ..(3:ℝ), Φt (D^(1/t)))
          + (∫ t in (3:ℝ)..(Real.log D / Real.log 2), Φt (D^(1/t))) :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    have hconst : (∫ t in sZ..(3:ℝ), Φt (D^(1/t)))
        = (3 - sZ) * (profC (k - 1) 2 + cCoef k ε * Real.exp (-2)) := by
      have hcongr : (∫ t in sZ..(3:ℝ), Φt (D^(1/t)))
          = ∫ t in sZ..(3:ℝ), (profC (k - 1) 2 + cCoef k ε * Real.exp (-2)) :=
        intervalIntegral.integral_congr hval1
      rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    have hrest : (∫ t in (3:ℝ)..(Real.log D / Real.log 2), Φt (D^(1/t)))
        = (∫ t in (3:ℝ)..(Real.log D / Real.log 2), profC (k - 1) (t - 1))
          + cCoef k ε * (∫ t in (3:ℝ)..(Real.log D / Real.log 2), errH (t - 1)) := by
      have hcongr : (∫ t in (3:ℝ)..(Real.log D / Real.log 2), Φt (D^(1/t)))
          = ∫ t in (3:ℝ)..(Real.log D / Real.log 2),
              (profC (k - 1) (t - 1) + cCoef k ε * errH (t - 1)) :=
        intervalIntegral.integral_congr hval2
      rw [hcongr]
      rw [intervalIntegral.integral_add
            (intervalIntegrable_shifted_profC (k - 1) 3 (Real.log D / Real.log 2))
            ((intervalIntegrable_shifted_errH 3 (Real.log D / Real.log 2)).const_mul _),
          intervalIntegral.integral_const_mul]
    rw [hsplit1, hconst, hrest]
    ring
  -- ### the integral estimates
  have hprof : (∫ t in (3:ℝ)..(Real.log D / Real.log 2), profC (k - 1) (t - 1))
      ≤ s * profC k s := by
    simpa [Nat.sub_add_cancel hk1] using
      profile_integral_le_even (k - 1) (even_sub_one_mod hk1 hkeven) hs1 (le_of_lt hs3) htw3
  have hI2 : (∫ u in Set.Ioi (2:ℝ), errH u) ≤ (47/50) * Real.exp (-2) :=
    (errH_sharp_bounds.2.2.2.2.1)
  have herr : (∫ t in (3:ℝ)..(Real.log D / Real.log 2), errH (t - 1))
      ≤ (47/50) * Real.exp (-2) :=
    le_trans (errH_interval_le_Ioi_two htw3) hI2
  -- ### scalar abbreviations
  set P2 : ℝ := profC (k - 1) 2 with hP2def
  set e2 : ℝ := Real.exp (-2) with he2def
  set A0 : ℝ := cCoef k ε with hA0def
  set E : ℝ := errH s with hEdef
  set Q : ℝ := profC k s with hQdef
  set c0 : ℝ := (1 + ε) * (sZ / s) * ε + (1 + ε)^2 * ((3 - sZ) / s) with hc0def
  set d0 : ℝ := (1 + ε)^2 * (1 / s) * (47/50) with hd0def
  have hP2nn : 0 ≤ P2 := by rw [hP2def]; exact profC_nonneg _ _
  have hA0nn : 0 ≤ A0 := by rw [hA0def]; exact cCoef_nonneg hε0
  have he2pos : 0 < e2 := by rw [he2def]; exact Real.exp_pos _
  have hEnn : 0 ≤ E := by rw [hEdef]; exact errH_nonneg s
  have hEpos : 0 < E := by rw [hEdef]; exact errH_pos s hs1
  have hQnn : 0 ≤ Q := by rw [hQdef]; exact profC_nonneg k s
  have hII : (∫ t in sZ..(Real.log D / Real.log 2), Φt (D^(1/t)))
      ≤ (3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2) := by
    rw [hint]
    have h1 : A0 * (∫ t in (3:ℝ)..(Real.log D / Real.log 2), errH (t - 1))
        ≤ A0 * ((47/50) * e2) := mul_le_mul_of_nonneg_left herr hA0nn
    linarith [hprof, h1]
  have hWnn : 0 ≤ (3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2) := by
    have h3 : 0 ≤ 3 - sZ := by linarith
    have h4 : 0 ≤ P2 + A0 * e2 := add_nonneg hP2nn (mul_nonneg hA0nn he2pos.le)
    have h5 : 0 ≤ (47/50 : ℝ) * e2 := mul_nonneg (by norm_num) he2pos.le
    have h7 : 0 ≤ s * Q := mul_nonneg (by linarith) hQnn
    have h8 : 0 ≤ (3 - sZ) * (P2 + A0 * e2) := mul_nonneg h3 h4
    have h9 : 0 ≤ A0 * ((47/50) * e2) := mul_nonneg hA0nn h5
    linarith
  have hX1nn : 0 ≤ ε * (P2 + A0 * e2) + (1 + ε) * (1 / sZ) *
      ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2)) := by
    have h1 : 0 ≤ 1 / sZ := one_div_nonneg.mpr hsZpos.le
    have h2 : 0 ≤ (1 + ε) * (1 / sZ) *
        ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2)) :=
      mul_nonneg (mul_nonneg (by linarith) h1) hWnn
    have h3 : 0 ≤ ε * (P2 + A0 * e2) :=
      mul_nonneg hε0 (add_nonneg hP2nn (mul_nonneg hA0nn he2pos.le))
    linarith
  have hTX : T A (k + 1) D z ≤ VfR A Z * (ε * (P2 + A0 * e2) + (1 + ε) * (1 / sZ) *
      ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2))) := by
    refine le_trans hsum ?_
    refine mul_le_mul_of_nonneg_left ?_ (VfR_nonneg A Z)
    rw [hΦtZ, hcv]
    have h1 : 0 ≤ 1 / sZ := one_div_nonneg.mpr hsZpos.le
    have h3 : (1 + ε) * (1 / sZ) * (∫ t in sZ..(Real.log D / Real.log 2), Φt (D^(1/t)))
        ≤ (1 + ε) * (1 / sZ) * ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2)) :=
      mul_le_mul_of_nonneg_left hII (mul_nonneg (by linarith) h1)
    linarith [h3]
  -- ### the coefficient ratio `VfR Z / VfR z`
  have hratio : Real.log z / Real.log Z = sZ / s := by
    rw [hsZdef, hsdef]
    field_simp
    try ring
  have hVz : VfR A Z ≤ VfR A z * ((1 + ε) * (sZ / s)) := by
    have h := VfR_le_of_sharpNorm (A := A) (z := z) hε0 hSharp (u := Z) hZ2' hZ_le_z le_rfl
    rwa [hratio] at h
  -- ### the two slots of the numerical budget
  have hδ0 : 0 ≤ 3 - sZ := by linarith
  have hδ1 : 3 - sZ ≤ 1/100000 := hdelta_small
  have h97 : (97/100:ℝ)^k ≤ (99/100:ℝ)^(k-1) := by
    have h1 : (97/100:ℝ)^k ≤ (97/100)^(k-1) := by
      have h2 : (97/100:ℝ)^k = (97/100)^(k-1) * (97/100) := by
        conv_lhs => rw [show k = (k-1)+1 by omega]
        rw [pow_succ]
      rw [h2]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ (97:ℝ)/100) (k-1)]
    have h3 : (97/100:ℝ)^(k-1) ≤ (99/100:ℝ)^(k-1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) (k-1)
    linarith
  have h97' : (97/100:ℝ)^(k-1) ≤ (99/100:ℝ)^(k-1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) (k-1)
  have hc0b : c0 ≤ (304/100) * ε := by
    rw [hc0def]
    have h1 : sZ / s ≤ 3 := by
      rw [div_le_iff₀ hs_pos]
      linarith [hsZ_le3, hs1]
    have h2 : (3 - sZ) / s ≤ 3 * ε / 1000000 := by
      rw [div_le_iff₀ hs_pos]
      have h3 : 3 * (ε / 1000000) * 1 ≤ 3 * (ε / 1000000) * s :=
        mul_le_mul_of_nonneg_left hs1 (by positivity)
      linarith [hdelta_le]
    have h4 : (1 + ε) * (sZ / s) * ε ≤ (303/100) * ε := by
      have h4a : (1 + ε) * (sZ / s) * ε ≤ (1 + ε) * 3 * ε :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hε0
      have h4b : (1 + ε) * 3 * ε ≤ (303/100) * ε := by
        have h4c : (1 + ε) * 3 ≤ (303/100) := by linarith
        exact mul_le_mul_of_nonneg_right h4c hε0
      linarith
    have h5 : (1 + ε)^2 * ((3 - sZ) / s) ≤ (1/100) * ε := by
      have h6a : (1 + ε)^2 ≤ 10201/10000 := by nlinarith
      have h6b : (1 + ε)^2 * ((3 - sZ) / s) ≤ (10201/10000) * (3 * ε / 1000000) :=
        mul_le_mul h6a h2 (div_nonneg hδ0 hs_pos.le) (by norm_num)
      nlinarith [h6b, hε0]
    linarith
  have hQb : Q ≤ 20 * (97/100:ℝ)^k * E := by
    rw [hQdef, hEdef]
    exact profC_le_decay k s hs1
  have hP2b : P2 ≤ 20 * (97/100:ℝ)^(k-1) * e2 := by
    have h := profC_le_decay (k - 1) 2 (by norm_num : (1:ℝ) ≤ 2)
    rw [hP2def, he2def]
    rw [errH_of_le_two le_rfl] at h
    exact h
  have he2b : e2 ≤ 3 * E := by
    have hm : e2 = Real.exp 1 * Real.exp (-3) := by
      rw [he2def, ← Real.exp_add]
      norm_num
    rw [hm]
    have h2 : Real.exp (-3) ≤ E := by
      rw [hEdef]
      exact exp_neg_three_le_errH (le_of_lt hs3)
    calc Real.exp 1 * Real.exp (-3) ≤ Real.exp 1 * E :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le
      _ ≤ 3 * E := mul_le_mul_of_nonneg_right (le_of_lt Real.exp_one_lt_three) hEnn
  have hq : Q ≤ 20 * (99/100:ℝ)^(k-1) * E := by
    refine le_trans hQb ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h97 (by norm_num)) hEnn
  have hp : P2 ≤ 20 * (99/100:ℝ)^(k-1) * e2 := by
    refine le_trans hP2b ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h97' (by norm_num)) he2pos.le
  have hslot1 : (2*ε + ε^2) * Q + c0 * P2 ≤ ε * 990 * (99/100:ℝ)^(k-1) * E := by
    have ht1 : (2*ε + ε^2) * Q ≤ (201/100) * ε * (20 * (99/100:ℝ)^(k-1) * E) := by
      have h2e : 2*ε + ε^2 ≤ (201/100) * ε := by nlinarith
      calc (2*ε + ε^2) * Q ≤ (2*ε + ε^2) * (20 * (99/100)^(k-1) * E) :=
            mul_le_mul_of_nonneg_left hq (by nlinarith)
        _ ≤ ((201/100) * ε) * (20 * (99/100)^(k-1) * E) :=
            mul_le_mul_of_nonneg_right h2e (by positivity)
    have ht2 : c0 * P2 ≤ ((304/100) * ε) * (60 * ((99/100:ℝ)^(k-1) * E)) := by
      have hpos : (0:ℝ) ≤ (304/100) * ε := by positivity
      calc c0 * P2 ≤ ((304/100) * ε) * P2 := mul_le_mul_of_nonneg_right hc0b hP2nn
        _ ≤ ((304/100) * ε) * (20 * (99/100)^(k-1) * e2) :=
            mul_le_mul_of_nonneg_left hp hpos
        _ ≤ ((304/100) * ε) * (20 * (99/100)^(k-1) * (3 * E)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left he2b (by positivity)) hpos
        _ = ((304/100) * ε) * (60 * ((99/100)^(k-1) * E)) := by ring
    have hsum' : (2*ε + ε^2) * Q + c0 * P2
        ≤ (201/100) * ε * (20 * (99/100:ℝ)^(k-1) * E)
          + ((304/100) * ε) * (60 * ((99/100:ℝ)^(k-1) * E)) := by
      linarith [ht1, ht2]
    have hεEnn : 0 ≤ ε * E * (99/100:ℝ)^(k-1) := by positivity
    calc (2*ε + ε^2) * Q + c0 * P2
        ≤ (201/100) * ε * (20 * (99/100)^(k-1) * E)
          + ((304/100) * ε) * (60 * ((99/100)^(k-1) * E)) := hsum'
      _ = ((201/100) * 20 + (304/100) * 60) * (ε * E * (99/100)^(k-1)) := by ring
      _ ≤ 990 * (ε * E * (99/100)^(k-1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hεEnn
          norm_num
      _ = ε * 990 * (99/100)^(k-1) * E := by ring
  have hslot2 : A0 * (e2 * c0 + e2 * d0) ≤ A0 * ((99/100) * E) := by
    refine mul_le_mul_of_nonneg_left ?_ hA0nn
    have hnum' := hnum s (3 - sZ) hs1 (le_of_lt hs3) hδ0 hδ1
    rw [← hEdef] at hnum'
    have hnum'' : e2 * (c0 + d0) + 2 * (3 - sZ) * e2 ≤ (99/100) * E := by
      rw [hc0def, hd0def, he2def]
      ring_nf at hnum' ⊢
      linarith [hnum']
    have h2δ : 0 ≤ 2 * (3 - sZ) * e2 := mul_nonneg (by linarith) he2pos.le
    linarith [hnum'', h2δ]
  have hcoe : cCoef (k + 1) ε * E
      = ε * 990 * (99/100:ℝ)^(k-1) * E + A0 * ((99/100) * E) := by
    rw [hA0def]
    exact cCoef_step hk1
  -- ### the final comparison
  have harith : ((1 + ε) * (sZ / s)) * (ε * (P2 + A0 * e2) + (1 + ε) * (1 / sZ) *
      ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2)))
      ≤ Q + cCoef (k + 1) ε * E := by
    have hexp : ((1 + ε) * (sZ / s)) * (ε * (P2 + A0 * e2) + (1 + ε) * (1 / sZ) *
        ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2)))
        = Q + (2*ε + ε^2) * Q + c0 * P2 + A0 * (e2 * c0 + e2 * d0) := by
      rw [hc0def, hd0def]
      field_simp
      ring
    rw [hexp]
    have hsum1 : Q + (2*ε + ε^2) * Q + c0 * P2 + A0 * (e2 * c0 + e2 * d0)
        ≤ Q + ε * 990 * (99/100:ℝ)^(k-1) * E + A0 * ((99/100) * E) := by
      linarith [hslot1, hslot2]
    refine le_trans hsum1 ?_
    rw [hcoe]
    exact le_of_eq (by ring)
  calc T A (k + 1) D z
      ≤ VfR A Z * (ε * (P2 + A0 * e2) + (1 + ε) * (1 / sZ) *
          ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2))) := hTX
    _ ≤ (VfR A z * ((1 + ε) * (sZ / s))) * (ε * (P2 + A0 * e2) + (1 + ε) * (1 / sZ) *
          ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2))) :=
        mul_le_mul_of_nonneg_right hVz hX1nn
    _ = VfR A z * (((1 + ε) * (sZ / s)) * (ε * (P2 + A0 * e2) + (1 + ε) * (1 / sZ) *
          ((3 - sZ) * (P2 + A0 * e2) + s * Q + A0 * ((47/50) * e2)))) := by ring
    _ ≤ VfR A z * (Q + cCoef (k + 1) ε * E) :=
        mul_le_mul_of_nonneg_left harith (VfR_nonneg A z)

end
end Work.ChenPlan.LinearSieve.JR2
