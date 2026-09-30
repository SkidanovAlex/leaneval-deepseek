import Mathlib
import Submission.Work.BW.kummer_state
import Submission.Work.BW.kummer_minkowski_basis
import Submission.Work.BW.kummer_logHeight_le
import Submission.Work.BW.kummer_modifiedHeight_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

variable {K : Type*} [Field K] [NumberField K]

/-- A vanishing `ℤ`-combination of a `ℚ`-linearly independent family has all coefficients zero. -/
lemma intCast_combo_eq_zero {n : ℕ} {v : Fin n → ℂ} (hind : LinearIndependent ℚ v)
    (c : Fin n → ℤ) (h : ∑ i, (c i : ℂ) * v i = 0) : ∀ i, c i = 0 := by
  intro i
  have h' : ∑ i, ((c i : ℚ)) • v i = 0 := by simpa [Rat.smul_def] using h
  have := (Fintype.linearIndependent_iff.mp hind (fun i => (c i : ℚ)) h') i
  exact_mod_cast this

/-- The level-`v` state matrix `s.m` is upper triangular with diagonal entries `2^(v - ν_j)`, so its
determinant equals `2^(v (n-1))`. -/
lemma kummer_state_det {n : ℕ} {φ : K →+* ℂ} {α : Fin n → K} {s : KSt K n} (hs : Inv φ α s) :
    s.m.det = (2 : ℤ) ^ (s.v * (n - 1)) := by
  have htri : s.m.IsUpperTriangular := fun i j hij => hs.tri i j hij
  rw [Matrix.det_of_isUpperTriangular htri]
  have hdiag : ∏ j : Fin n, s.m j j = ∏ j : Fin n, (2 : ℤ) ^ (s.v - s.nu j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hs.diag j]
  rw [hdiag, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum : ∑ j : Fin n, (s.v - s.nu j) = ∑ j, s.v - ∑ j, s.nu j :=
    Finset.sum_tsub_distrib Finset.univ (f := fun _ : Fin n => s.v)
      (g := fun j : Fin n => s.nu j) (fun j _ => hs.nu_le j)
  rw [hsum, hs.sum_nu, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have key : n * s.v - s.v = (n - 1) * s.v := by
    nth_rewrite 2 [← one_mul s.v]
    rw [← Nat.mul_sub_right_distrib]
  rw [key, Nat.mul_comm]

/-- For each column `j` of `s.m * U`, the associated logarithm `lamP` exponentiates to the element
`∏ l, (s.β l) ^ (U l j)`. -/
lemma kummer_exp_state_col {n : ℕ} {φ : K →+* ℂ} {α : Fin n → K} {s : KSt K n} (hs : Inv φ α s)
    (U : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    Complex.exp (lamP φ α s.v (fun j i => (s.m * U) i j) j)
      = φ (∏ l, (s.β l) ^ (U l j)) := by
  set w : Fin n → ℂ := fun l => ∑ i, ((s.m i l : ℤ) : ℂ) * Complex.log (φ (α i)) with hw
  have hw' : ∀ l, w l = ∑ i, ((s.m i l : ℤ) : ℂ) * Complex.log (φ (α i)) := fun l => rfl
  have hexp : ∀ l, Complex.exp (((2 : ℂ) ^ s.v)⁻¹ * w l) = φ (s.β l) := fun l => hs.exp_eq l
  have hlam : lamP φ α s.v (fun j i => (s.m * U) i j) j
      = ∑ l, ((U l j : ℤ) : ℂ) * (((2 : ℂ) ^ s.v)⁻¹ * w l) := by
    rw [lamP]
    rw [show ∑ i, (((s.m * U) i j : ℤ) : ℂ) * Complex.log (φ (α i))
        = ∑ l, ((U l j : ℤ) : ℂ) * w l from by
      calc ∑ i, (((s.m * U) i j : ℤ) : ℂ) * Complex.log (φ (α i))
          = ∑ i, (∑ l, (s.m i l : ℂ) * (U l j : ℂ)) * Complex.log (φ (α i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Matrix.mul_apply]; push_cast; ring
        _ = ∑ i, ∑ l, (s.m i l : ℂ) * (U l j : ℂ) * Complex.log (φ (α i)) := by
            refine Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
        _ = ∑ l, ∑ i, (s.m i l : ℂ) * (U l j : ℂ) * Complex.log (φ (α i)) := Finset.sum_comm
        _ = ∑ l, ((U l j : ℤ) : ℂ) * w l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hw' l, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  rw [hlam, Complex.exp_sum]
  rw [show ∏ l, Complex.exp (((U l j : ℤ) : ℂ) * (((2 : ℂ) ^ s.v)⁻¹ * w l))
      = ∏ l, (φ (s.β l)) ^ (U l j) from ?_]
  · rw [map_prod]
    exact Finset.prod_congr rfl fun l _ => (map_zpow₀ φ (s.β l) (U l j)).symm
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [Complex.exp_int_mul, hexp l]

/-- `(t⁻¹)^n * t^{n-1} = t⁻¹` for `t ≠ 0` and `n ≥ 1`. -/
lemma inv_pow_mul_pow_pred {t : ℝ} (ht : t ≠ 0) {n : ℕ} (hn : 0 < n) :
    t⁻¹ ^ n * t ^ (n - 1) = t⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hsub : m.succ - 1 = m := by omega
  rw [hsub, pow_succ]
  rw [show t⁻¹ ^ m * t⁻¹ * t ^ m = (t⁻¹ ^ m * t ^ m) * t⁻¹ by ring]
  rw [← mul_pow, inv_mul_cancel₀ ht, one_pow, one_mul]

/-- Rearrangement used to normalise the Minkowski product bound: if `∏ W j ≤ M·2^{v(n-1)}·P` then
`∏ (2^{-v} W j) ≤ M·2^{-v}·P`. -/
lemma kummer_prod_mu_arith {n v : ℕ} (hn : 0 < n) (W : Fin n → ℝ) (M P : ℝ)
    (hprod : ∏ j, W j ≤ M * (2 : ℝ) ^ (v * (n - 1)) * P) :
    ∏ j, (((2 : ℝ) ^ v)⁻¹ * W j) ≤ M * (((2 : ℝ) ^ v)⁻¹) * P := by
  have hL : ∏ j : Fin n, (((2 : ℝ) ^ v)⁻¹ * W j)
      = (((2 : ℝ) ^ v)⁻¹) ^ n * ∏ j, W j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hL]
  have hkey : (((2 : ℝ) ^ v)⁻¹) ^ n * (2 : ℝ) ^ (v * (n - 1)) = (((2 : ℝ) ^ v)⁻¹) := by
    rw [pow_mul]
    exact inv_pow_mul_pow_pred (pow_ne_zero _ (by norm_num)) hn
  have hnn : 0 ≤ (((2 : ℝ) ^ v)⁻¹) ^ n := by positivity
  calc (((2 : ℝ) ^ v)⁻¹) ^ n * ∏ j, W j
      ≤ (((2 : ℝ) ^ v)⁻¹) ^ n * (M * (2 : ℝ) ^ (v * (n - 1)) * P) :=
        mul_le_mul_of_nonneg_left hprod hnn
    _ = M * (((2 : ℝ) ^ v)⁻¹) * P := by
        have hrearr : (((2 : ℝ) ^ v)⁻¹) ^ n * (M * (2 : ℝ) ^ (v * (n - 1)) * P)
            = M * ((((2 : ℝ) ^ v)⁻¹) ^ n * (2 : ℝ) ^ (v * (n - 1))) * P := by ring
        rw [hrearr, hkey]

/-- Per-column Lehmer/Minkowski data: with `μ = 2^{-v} ∑ i, |(s.m*U) i j| h'(α i)` one has
`1/(c' d) < μ` and `h'(∏ l, (s.β l)^{U l j}) ≤ c' μ`. -/
lemma kummer_mu_data {n : ℕ} {φ : K →+* ℂ} {α : Fin n → K} (hα : ∀ i, α i ≠ 0)
    (hind : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (c' : ℝ) (hc' : 1 < c')
    (hLeh : ∀ (β : K) (ℓ : ℂ), β ≠ 0 → Complex.exp ℓ = φ β → ℓ ≠ 0 →
      1 < c' * max (Height.logHeight₁ β) ‖ℓ‖)
    {s : KSt K n} (hs : Inv φ α s)
    (U : Matrix (Fin n) (Fin n) ℤ) (j : Fin n)
    (hexp : Complex.exp (lamP φ α s.v (fun j i => (s.m * U) i j) j)
              = φ (∏ l, (s.β l) ^ (U l j)))
    (hcol : ∃ i, (s.m * U) i j ≠ 0) :
    (1 / (c' * (Module.finrank ℚ K : ℝ)) <
        (((2 : ℝ) ^ s.v)⁻¹) * ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i)) ∧
    (BakerWustholz.modifiedHeight φ (∏ l, (s.β l) ^ (U l j)) ≤
        c' * ((((2 : ℝ) ^ s.v)⁻¹) * ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i))) := by
  have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set β : K := ∏ l, (s.β l) ^ (U l j) with hβdef
  set ℓ : ℂ := lamP φ α s.v (fun j i => (s.m * U) i j) j with hℓdef
  set μ : ℝ := (((2 : ℝ) ^ s.v)⁻¹) * ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i) with hμdef
  have hβne : β ≠ 0 := by
    rw [hβdef]
    exact Finset.prod_ne_zero_iff.mpr fun l _ => zpow_ne_zero _ (hs.beta_ne l)
  have hℓne : ℓ ≠ 0 := by
    intro h0
    obtain ⟨i0, hi0⟩ := hcol
    have hsum : ∑ i, (((s.m * U) i j : ℤ) : ℂ) * Complex.log (φ (α i)) = 0 := by
      have h := h0
      rw [hℓdef, lamP] at h
      have hne : ((2 : ℂ) ^ s.v) ≠ 0 := pow_ne_zero _ (by norm_num)
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 (inv_ne_zero hne)
      · exact h1
    exact hi0 (intCast_combo_eq_zero hind (fun i => (s.m * U) i j) hsum i0)
  have hLeh' : 1 < c' * max (Height.logHeight₁ β) ‖ℓ‖ := hLeh β ℓ hβne hexp hℓne
  have hd_hp : ∀ i, Height.logHeight₁ (α i) ≤ (Module.finrank ℚ K : ℝ) * hp φ (α i) := by
    intro i
    have h := logHeight_div_le_hp φ (α i)
    rw [div_le_iff₀ hdpos, mul_comm] at h
    exact h
  have hd_logn : ∀ i, ‖Complex.log (φ (α i))‖ ≤ (Module.finrank ℚ K : ℝ) * hp φ (α i) := by
    intro i
    have h := log_div_le_hp φ (α i)
    rw [div_le_iff₀ hdpos, mul_comm] at h
    exact h
  have hlog : Height.logHeight₁ β ≤ (Module.finrank ℚ K : ℝ) * μ := by
    have hkl := kummer_logHeight_le φ α hα (fun i => (s.m * U) i j) s.v β hexp
    calc Height.logHeight₁ β
        ≤ (((2 : ℝ) ^ s.v)⁻¹) * ∑ i, ((((s.m * U) i j).natAbs : ℝ)) * Height.logHeight₁ (α i) :=
          hkl
      _ ≤ (((2 : ℝ) ^ s.v)⁻¹) * ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| *
            ((Module.finrank ℚ K : ℝ) * hp φ (α i)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Nat.cast_natAbs, Int.cast_abs]
          exact mul_le_mul_of_nonneg_left (hd_hp i) (abs_nonneg _)
      _ = (Module.finrank ℚ K : ℝ) * μ := by
          have hS : (∑ i, |(((s.m * U) i j : ℤ) : ℝ)| *
                ((Module.finrank ℚ K : ℝ) * hp φ (α i)))
              = (Module.finrank ℚ K : ℝ) *
                ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [hS, hμdef]; ring
  have hnrm : ‖ℓ‖ ≤ (Module.finrank ℚ K : ℝ) * μ := by
    rw [hℓdef, lamP, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
    have h1 : ‖∑ i, (((s.m * U) i j : ℤ) : ℂ) * Complex.log (φ (α i))‖
        ≤ (Module.finrank ℚ K : ℝ) *
          ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i) := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul, norm_intCast]
      calc |(((s.m * U) i j : ℤ) : ℝ)| * ‖Complex.log (φ (α i))‖
          ≤ |(((s.m * U) i j : ℤ) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hp φ (α i)) :=
            mul_le_mul_of_nonneg_left (hd_logn i) (abs_nonneg _)
        _ = (Module.finrank ℚ K : ℝ) * (|(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i)) := by ring
    calc ((2 : ℝ) ^ s.v)⁻¹ *
          ‖∑ i, (((s.m * U) i j : ℤ) : ℂ) * Complex.log (φ (α i))‖
        ≤ ((2 : ℝ) ^ s.v)⁻¹ *
            ((Module.finrank ℚ K : ℝ) * ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (Module.finrank ℚ K : ℝ) * μ := by rw [hμdef]; ring
  have hmu : 1 / (c' * (Module.finrank ℚ K : ℝ)) < μ := by
    have hcd : 0 < c' * (Module.finrank ℚ K : ℝ) := mul_pos (by linarith) hdpos
    have hbound : max (Height.logHeight₁ β) ‖ℓ‖ ≤ (Module.finrank ℚ K : ℝ) * μ :=
      max_le hlog hnrm
    have h1 : 1 < c' * ((Module.finrank ℚ K : ℝ) * μ) :=
      lt_of_lt_of_le hLeh' (mul_le_mul_of_nonneg_left hbound (by linarith))
    rw [div_lt_iff₀ hcd]
    nlinarith [h1]
  refine ⟨hmu, ?_⟩
  have hmod := kummer_modifiedHeight_le φ α hα (fun i => (s.m * U) i j) s.v β hβne hexp
  have hmod' : BakerWustholz.modifiedHeight φ β ≤ max (1 / (Module.finrank ℚ K : ℝ)) μ := by
    rw [hμdef]
    exact hmod
  have h1d : 1 / (Module.finrank ℚ K : ℝ) < c' * μ := by
    have hc'pos : 0 < c' := by linarith
    have h := mul_lt_mul_of_pos_left hmu hc'pos
    have heq : c' * (1 / (c' * (Module.finrank ℚ K : ℝ)))
        = 1 / (Module.finrank ℚ K : ℝ) := by
      field_simp
    rwa [heq] at h
  have hμnonneg : 0 ≤ μ := by
    rw [hμdef]
    refine mul_nonneg (by positivity) ?_
    exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_of_lt (hp_pos φ (α i)))
  have hmod_le : max (1 / (Module.finrank ℚ K : ℝ)) μ ≤ c' * μ :=
    max_le (le_of_lt h1d) (by nlinarith [hμnonneg, hc'])
  exact le_trans hmod' hmod_le

/-- Minkowski/Lehmer data attached to a state of the BW §9 induction. There are a unimodular
integral matrix `U` and weights `μ j > 0` with `2^v * μ j = ∑ i, |((s.m * U) i j)| h'(α i)`, the
elements `β'' j = ∏ l, (s.β l) ^ (U l j)` satisfy `exp (lamP φ α v L j) = φ (β'' j)` for the matrix
`L j i = (s.m * U) i j`, one has `h'(β'' j) ≤ c' * μ j` and `1/(c'd) < μ j` (Lehmer, `d = finrank ℚ K`),
and `∏ j, μ j ≤ (n!)²/2^{n-1} * 2^{-v} * ∏ i, h'(α i)` (Minkowski's second inequality). -/
theorem kummer_minkowski_data {K : Type*} [Field K] [NumberField K] {n : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} (hn : 0 < n) (hα : ∀ i, α i ≠ 0)
    (hind : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (c' : ℝ) (hc' : 1 < c')
    (hLeh : ∀ (β : K) (ℓ : ℂ), β ≠ 0 → Complex.exp ℓ = φ β → ℓ ≠ 0 →
      1 < c' * max (Height.logHeight₁ β) ‖ℓ‖)
    {s : KSt K n} (hs : Inv φ α s) :
    ∃ (U : Matrix (Fin n) (Fin n) ℤ) (μ : Fin n → ℝ),
      IsUnit U.det ∧
      (∀ j, 0 < μ j) ∧
      (∀ j, (2:ℝ)^s.v * μ j = ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i)) ∧
      (∀ j, 1 / (c' * (Module.finrank ℚ K : ℝ)) < μ j) ∧
      (∀ j, Complex.exp (lamP φ α s.v (fun j i => ((s.m * U) i j)) j)
              = φ (∏ l, (s.β l) ^ (U l j))) ∧
      (∀ j, BakerWustholz.modifiedHeight φ (∏ l, (s.β l) ^ (U l j)) ≤ c' * μ j) ∧
      ∏ j, μ j ≤ ((n.factorial : ℝ)^2 / 2^(n-1)) * (((2:ℝ)^s.v)⁻¹) * ∏ i, hp φ (α i) := by
  classical
  have hdet_eq : s.m.det = (2 : ℤ) ^ (s.v * (n - 1)) := kummer_state_det hs
  have hdet_ne : s.m.det ≠ 0 := by rw [hdet_eq]; positivity
  obtain ⟨U, hUdet, hUmink⟩ :=
    kummer_minkowski_basis hn s.m hdet_ne (fun i => hp φ (α i)) (fun i => hp_pos φ (α i))
  set wt : Fin n → ℝ :=
    fun j => (((2 : ℝ) ^ s.v)⁻¹) * ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i) with hwtdef
  have hdetU : U.det ≠ 0 := hUdet.ne_zero
  have hdetMU : (s.m * U).det ≠ 0 := by
    rw [Matrix.det_mul, hdet_eq]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdetU
  have hcol : ∀ j, ∃ i, (s.m * U) i j ≠ 0 := by
    intro j
    by_contra h
    push_neg at h
    exact hdetMU (Matrix.det_eq_zero_of_column_eq_zero j h)
  have hexp : ∀ j, Complex.exp (lamP φ α s.v (fun j i => (s.m * U) i j) j)
      = φ (∏ l, (s.β l) ^ (U l j)) := fun j => kummer_exp_state_col hs U j
  refine ⟨U, wt, hUdet, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨i0, hi0⟩ := hcol j
    rw [hwtdef]
    refine mul_pos (by positivity) ?_
    refine Finset.sum_pos' (fun i _ => mul_nonneg (abs_nonneg _) (le_of_lt (hp_pos φ (α i))))
      ⟨i0, Finset.mem_univ _, ?_⟩
    exact mul_pos (abs_pos.mpr (by exact_mod_cast hi0)) (hp_pos φ (α i0))
  · intro j
    rw [hwtdef]
    have hne : ((2 : ℝ) ^ s.v) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · intro j
    simpa [hwtdef] using (kummer_mu_data hα hind c' hc' hLeh hs U j (hexp j) (hcol j)).1
  · intro j
    exact hexp j
  · intro j
    simpa [hwtdef] using (kummer_mu_data hα hind c' hc' hLeh hs U j (hexp j) (hcol j)).2
  · have hW : ∏ j, (∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i))
        ≤ ((n.factorial : ℝ) ^ 2 / 2 ^ (n - 1)) * (2 : ℝ) ^ (s.v * (n - 1)) *
          ∏ i, hp φ (α i) := by
      have h1 : ∏ j, (∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i))
          = ∏ j, (∑ i, hp φ (α i) * |(((s.m * U) i j : ℤ) : ℝ)|) := by
        refine Finset.prod_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      rw [h1]
      refine le_trans hUmink (le_of_eq ?_)
      have hdetabs : |(((s.m.det : ℤ)) : ℝ)| = (2 : ℝ) ^ (s.v * (n - 1)) := by
        rw [hdet_eq]
        have : (((2 : ℤ) ^ (s.v * (n - 1)) : ℤ) : ℝ) = (2 : ℝ) ^ (s.v * (n - 1)) := by
          push_cast; ring
        rw [this, abs_of_nonneg (by positivity)]
      rw [hdetabs]
    have hfin := kummer_prod_mu_arith hn
      (fun j => ∑ i, |(((s.m * U) i j : ℤ) : ℝ)| * hp φ (α i))
      ((n.factorial : ℝ) ^ 2 / 2 ^ (n - 1)) (∏ i, hp φ (α i)) hW
    simpa [hwtdef] using hfin

end Work.BW
