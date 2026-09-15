import Submission.FUP.WeightSum
import Submission.Commons.Analysis.Calculus.cube_bump_deriv_bound_uniformW

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators
open Submission.FUP

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Regularity of the §6.1 weight `ω`

We prove the Kohn–Nirenberg-type symbol estimates `‖D^a ω(x)‖ ≤ C_reg ⟨x⟩^{1-a}` for `a ≤ 3`
satisfied by the weight `ω = Σ_{k₀ ≤ k ≤ K} ω_k` constructed in `WeightSum`.  The key points
are that the bumps carry a derivative constant independent of the grid width (so the catalogue
`bumpConst` below is uniform in `k`), and that only `≤ 4` values of `k` contribute at any point
`x` (the supports are dyadic annuli).
-/

/-- A uniform (in the grid width) bound for the bump derivative constants. -/
noncomputable def bumpConst (d : ℕ) : ℝ :=
  max (coverBumpK (d := d) (1:ℝ) one_pos 0)
    (max (coverBumpK (d := d) (1:ℝ) one_pos 1)
      (max (coverBumpK (d := d) (1:ℝ) one_pos 2)
        (coverBumpK (d := d) (1:ℝ) one_pos 3)))

lemma coverBumpK_eq (W : ℝ) (hW : 0 < W) (a : ℕ) :
    coverBumpK (d := d) W hW a = coverBumpK (d := d) (1:ℝ) one_pos a := rfl

lemma coverBumpK_le_bumpConst (W : ℝ) (hW : 0 < W) {a : ℕ} (ha : a ≤ 3) :
    coverBumpK (d := d) W hW a ≤ bumpConst d := by
  rw [coverBumpK_eq]
  interval_cases a <;> simp [bumpConst]

lemma bumpConst_nonneg : 0 ≤ bumpConst d := by
  have h := coverBumpK_le_bumpConst (d := d) (1:ℝ) one_pos (a := 0) (by norm_num)
  linarith [coverBumpK_nonneg (d := d) (1:ℝ) one_pos (a := 0) (by norm_num)]

/-- **Derivative bound for a single `ω_k`.** -/
lemma norm_iteratedFDeriv_omegaK_le {s α : ℝ} {k a : ℕ} (ha : a ≤ 3)
    (Y : Set ℝᵈ) (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ a (omegaK s α k Y) x‖ ≤
      coefK α k * ((3:ℝ)^d * bumpConst d * (Wk s k) ^ (-(a : ℝ))) := by
  have hcd : ContDiffAt ℝ a (psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k)) x :=
    ((psiK_contDiff (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k)).of_le
      (by exact_mod_cast ha)).contDiffAt
  show ‖iteratedFDeriv ℝ a (fun x => (-(coefK α k)) •
      psiK (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) x) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hcd, norm_smul]
  have hnorm : ‖(-(coefK α k) : ℝ)‖ = coefK α k := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (coefK_nonneg α k)]
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left ?_ (coefK_nonneg α k)
  have h := norm_iteratedFDeriv_psiK_le (Rk k) (Wk s k) (Wk_pos s k) (Nk s k) Y (Ak k) ha x
  have hkb : coverBumpK (d := d) (Wk s k) (Wk_pos s k) a
      = coverBumpK (d := d) (1:ℝ) one_pos a := rfl
  rw [hkb] at h
  refine h.trans ?_
  have hle : coverBumpK (d := d) (1:ℝ) one_pos a ≤ bumpConst d :=
    coverBumpK_le_bumpConst (d := d) (1:ℝ) one_pos ha
  have hWk : 0 ≤ (Wk s k) ^ (-(a : ℝ)) :=
    Real.rpow_nonneg (le_of_lt (Wk_pos s k)) _
  calc (3:ℝ)^d * coverBumpK (d := d) (1:ℝ) one_pos a * (Wk s k) ^ (-(a : ℝ))
      ≤ (3:ℝ)^d * bumpConst d * (Wk s k) ^ (-(a : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hWk
    _ = (3:ℝ)^d * bumpConst d * (Wk s k) ^ (-(a : ℝ)) := rfl


section Bound

/-- `⟨x⟩` in the `rpow` normalisation of the BM statement. -/
noncomputable def br (x : ℝᵈ) : ℝ := (1 + ‖x‖ ^ 2) ^ ((1:ℝ)/2)

lemma br_pos (x : ℝᵈ) : 0 < br x :=
  Real.rpow_pos_of_pos (by positivity) _

lemma br_ge_one (x : ℝᵈ) : 1 ≤ br x := by
  rw [br]
  calc (1:ℝ) = 1 ^ ((1:ℝ)/2) := (Real.one_rpow _).symm
    _ ≤ (1 + ‖x‖^2) ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow zero_le_one (by nlinarith [sq_nonneg ‖x‖]) (by norm_num)

lemma norm_le_br (x : ℝᵈ) : ‖x‖ ≤ br x := by
  have h2 : Real.sqrt (‖x‖^2) ≤ Real.sqrt (1 + ‖x‖^2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖x‖])
  calc ‖x‖ = Real.sqrt (‖x‖^2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ Real.sqrt (1 + ‖x‖^2) := h2
    _ = br x := by rw [br, ← Real.sqrt_eq_rpow]

lemma br_le_sqrt_two_mul {x : ℝᵈ} (hx : 1 ≤ ‖x‖) : br x ≤ Real.sqrt 2 * ‖x‖ := by
  have h2 : (2:ℝ) ^ ((1:ℝ)/2) = Real.sqrt 2 := by rw [Real.sqrt_eq_rpow]
  have h3 : (‖x‖^2) ^ ((1:ℝ)/2) = ‖x‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg x)]
  calc br x = (1 + ‖x‖^2) ^ ((1:ℝ)/2) := rfl
    _ ≤ (2 * ‖x‖^2) ^ ((1:ℝ)/2) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        nlinarith [hx, sq_nonneg ‖x‖]
    _ = (2:ℝ) ^ ((1:ℝ)/2) * (‖x‖^2) ^ ((1:ℝ)/2) :=
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ ‖x‖^2)
    _ = Real.sqrt 2 * ‖x‖ := by rw [h2, h3]

lemma alpha_pos {s α : ℝ} (hs : 0 < s) (hα : 3*s < α) : 0 < α := by linarith

lemma s_lt_alpha {s α : ℝ} (hs : 0 < s) (hα : 3*s < α) : s < α := by linarith

/-- **Scalar bound.**  For `x ∈ A_k`, `(2^k/k^α)·W_k^{-a} ≤ 32⟨x⟩^{1-a}` for `a ≤ 3`. -/
lemma coefK_mul_Wk_rpow_le {s α : ℝ} (hs : 0 < s) (hα : 3*s < α) {k a : ℕ} (ha : a ≤ 3)
    (hk : 1 ≤ k) {x : ℝᵈ} (hk1 : (2:ℝ)^(k-1) ≤ ‖x‖) (hk2 : ‖x‖ ≤ (2:ℝ)^(k+2)) :
    coefK α k * (Wk s k) ^ (-(a:ℝ)) ≤ 32 * br x ^ (1 - (a:ℝ)) := by
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hM : max (k:ℝ) 1 = (k:ℝ) := max_eq_left (by exact_mod_cast hk)
  have hαpos : 0 < α := alpha_pos hs hα
  have hDpos : 0 < (2:ℝ)^k := pow_pos (by norm_num) k
  have hka : 0 < (k:ℝ)^α := Real.rpow_pos_of_pos hkpos α
  have hx1 : 1 ≤ ‖x‖ := by
    have h : (2:ℝ)^0 ≤ (2:ℝ)^(k-1) := pow_le_pow_right₀ (by norm_num) (by omega)
    simp at h; linarith
  have hbr1 : (1:ℝ) ≤ br x := br_ge_one x
  have hbrn : ‖x‖ ≤ br x := norm_le_br x
  have hbr2 : br x ≤ Real.sqrt 2 * ‖x‖ := br_le_sqrt_two_mul hx1
  have hcoef : coefK α k = (2:ℝ)^k / (k:ℝ)^α := by rw [coefK, hM]
  have hWkeq : Wk s k = (2:ℝ)^k / (k:ℝ)^s := Wk_eq s hk
  have hDle : (2:ℝ)^k ≤ 2 * ‖x‖ := by
    have h : (2:ℝ)^k = 2 * (2:ℝ)^(k-1) := by
      conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
      ring
    linarith
  have hDge : ‖x‖ / 4 ≤ (2:ℝ)^k := by
    have h : (2:ℝ)^(k+2) = 4 * (2:ℝ)^k := by rw [pow_succ, pow_succ]; ring
    linarith
  have hbrmul : br x ≤ 4 * Real.sqrt 2 * (2:ℝ)^k := by
    have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h4 : (0:ℝ) < 4 * (2:ℝ)^k := by positivity
    have hle : Real.sqrt 2 * ‖x‖ ≤ Real.sqrt 2 * (4 * (2:ℝ)^k) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hs2)
      linarith
    linarith [hbr2, hle]
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, sub_zero, Real.rpow_one]
    rw [hcoef]
    have h1 : (2:ℝ)^k / (k:ℝ)^α ≤ (2:ℝ)^k := by
      rw [div_le_iff₀ hka]
      nlinarith [hDpos, Real.one_le_rpow (show (1:ℝ) ≤ (k:ℝ) by exact_mod_cast hk) (le_of_lt hαpos)]
    calc (2:ℝ)^k / (k:ℝ)^α ≤ (2:ℝ)^k := h1
      _ ≤ 2 * ‖x‖ := hDle
      _ ≤ 2 * br x := by linarith [hbrn]
      _ ≤ 32 * br x := by linarith [hbr1]
  · -- a ≥ 1
    have hkey : coefK α k * (Wk s k) ^ (-(a:ℝ)) ≤ 1 / ((2:ℝ)^k)^(a-1) := by
      have hWpow : (Wk s k) ^ (-(a:ℝ)) = ((k:ℝ)^(s * a)) / ((2:ℝ)^k)^a := by
        rw [Real.rpow_neg (le_of_lt (Wk_pos s k)), Real.rpow_natCast, hWkeq, div_pow]
        rw [← Real.rpow_natCast ((k:ℝ)^s) a]
        rw [← Real.rpow_mul (le_of_lt hkpos) s (a:ℝ)]
        rw [show s * (a:ℝ) = s * a by ring]
        rw [inv_div]
      rw [hWpow, hcoef]
      have hDa : ((2:ℝ)^k)^a = (2:ℝ)^k * ((2:ℝ)^k)^(a-1) := by
        obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
        rw [pow_succ', Nat.succ_sub_one]
      rw [hDa]
      have hle1 : (k:ℝ)^(s * a) / (k:ℝ)^α ≤ 1 := by
        rw [div_le_one hka]
        exact Real.rpow_le_rpow_of_exponent_le
          (show (1:ℝ) ≤ (k:ℝ) by exact_mod_cast hk) (by
            have : (a:ℝ) ≤ 3 := by exact_mod_cast ha
            nlinarith [hs])
      have hLHS : (2:ℝ)^k / (k:ℝ)^α
            * ((k:ℝ)^(s * a) / ((2:ℝ)^k * ((2:ℝ)^k)^(a-1)))
          = ((k:ℝ)^(s * a) / (k:ℝ)^α) * (1 / ((2:ℝ)^k)^(a-1)) := by
        field_simp
      rw [hLHS]
      calc ((k:ℝ)^(s * a) / (k:ℝ)^α) * (1 / ((2:ℝ)^k)^(a-1))
          ≤ 1 * (1 / ((2:ℝ)^k)^(a-1)) :=
            mul_le_mul_of_nonneg_right hle1 (by positivity)
        _ = 1 / ((2:ℝ)^k)^(a-1) := one_mul _
    refine hkey.trans ?_
    interval_cases a
    · -- a = 1
      have h1 : (1:ℕ) - 1 = 0 := rfl
      rw [h1, pow_zero, div_one, Nat.cast_one, sub_self, Real.rpow_zero, mul_one]
      linarith [hbr1]
    · -- a = 2
      have h1 : (2:ℕ) - 1 = 1 := rfl
      rw [h1, pow_one, Nat.cast_ofNat, show ((1:ℝ) - 2) = -1 by norm_num, Real.rpow_neg_one]
      rw [inv_eq_one_div, mul_one_div]
      have hbr3 : br x ≤ 32 * (2:ℝ)^k := by
        nlinarith [hbrmul, hDpos, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      rw [le_div_iff₀ (br_pos x), div_mul_eq_mul_div, one_mul, div_le_iff₀ hDpos]
      exact hbr3
    · -- a = 3
      have h1 : (3:ℕ) - 1 = 2 := rfl
      rw [h1, Nat.cast_ofNat, show ((1:ℝ) - 3) = -2 by norm_num,
        Real.rpow_neg (by positivity : (0:ℝ) ≤ br x), Real.rpow_two]
      rw [inv_eq_one_div, mul_one_div]
      have hbr3 : br x ^ 2 ≤ 32 * ((2:ℝ)^k)^2 := by
        have hs2 : Real.sqrt 2 ^ 2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
        nlinarith [hbrmul, hDpos, br_pos x, hs2]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < br x ^ 2), div_mul_eq_mul_div, one_mul,
        div_le_iff₀ (by positivity : (0:ℝ) < ((2:ℝ)^k)^2)]
      exact hbr3

/-- At most four dyadic annuli can contain a given point. -/
lemma card_yCover_filter_le_four {s : ℝ} {k₀ K : ℕ} (hk0 : 1 ≤ k₀)
    (hW : ∀ k ∈ Finset.Icc k₀ K, Real.sqrt (d:ℝ) * Wk s k ≤ (2:ℝ)^(k-1))
    (Y : Set ℝᵈ) (x : ℝᵈ) :
    ((Finset.Icc k₀ K).filter
      (fun k => x ∈ yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k))).card ≤ 4 := by
  classical
  set S := (Finset.Icc k₀ K).filter
    (fun k => x ∈ yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k)) with hS
  by_cases hne : S.Nonempty
  · have hmem : S.min' hne ∈ S := S.min'_mem hne
    have hle : ∀ k ∈ S, S.min' hne ≤ k := fun k hk => S.min'_le _ hk
    have hsub : S ⊆ Finset.Icc (S.min' hne) ((S.min' hne)+3) := by
      intro k hk
      refine Finset.mem_Icc.mpr ⟨hle k hk, ?_⟩
      have hkIcc : k ∈ Finset.Icc k₀ K := (Finset.mem_filter.mp hk).1
      have hmIcc : S.min' hne ∈ Finset.Icc k₀ K := (Finset.mem_filter.mp hmem).1
      have hk1 : 1 ≤ k := le_trans hk0 (Finset.mem_Icc.mp hkIcc).1
      have hm1 : 1 ≤ S.min' hne := le_trans hk0 (Finset.mem_Icc.mp hmIcc).1
      have hkx := yCover_subset_annulusRk (k := k) hk1 (hW k hkIcc)
        (Finset.mem_filter.mp hk).2
      have hmx := yCover_subset_annulusRk (k := S.min' hne) hm1 (hW _ hmIcc)
        (Finset.mem_filter.mp hmem).2
      rw [mem_annulus] at hkx hmx
      have hcmp : (2:ℝ)^(k-1) ≤ (2:ℝ)^((S.min' hne)+2) := le_trans hkx.1 hmx.2
      by_contra hcon
      push Not at hcon
      have : (2:ℝ)^((S.min' hne)+2) < (2:ℝ)^(k-1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      linarith
    calc S.card ≤ (Finset.Icc (S.min' hne) ((S.min' hne)+3)).card := Finset.card_le_card hsub
      _ = 4 := by simp; omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

/-- **Regularity of `ω`.**  The Kohn–Nirenberg-type estimate `‖D^a ω(x)‖ ≤ C_reg ⟨x⟩^{1-a}`
for `a ≤ 3`, with `C_reg` depending only on the dimension. -/
theorem norm_iteratedFDeriv_omega_le {s α : ℝ} {k₀ K : ℕ} (hs : 0 < s) (hα : 3*s < α)
    (hk0 : 1 ≤ k₀) (hkK : k₀ ≤ K)
    (hW : ∀ k ∈ Finset.Icc k₀ K, Real.sqrt (d:ℝ) * Wk s k ≤ (2:ℝ)^(k-1))
    (a : ℕ) (ha : a ≤ 3) (Y : Set ℝᵈ) (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ a (omega s α k₀ K Y) x‖ ≤
      (128 * (3:ℝ)^d * bumpConst d) * (1 + ‖x‖^2)^((1-(a:ℝ))/2) := by
  classical
  have hbump0 : (0:ℝ) ≤ bumpConst d := bumpConst_nonneg
  have hcoef0 : (0:ℝ) ≤ (3:ℝ)^d * bumpConst d * 32 := by positivity
  set S := (Finset.Icc k₀ K).filter
    (fun k => x ∈ yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k)) with hS
  have hterm : ∀ k ∈ S, ‖iteratedFDeriv ℝ a (omegaK s α k Y) x‖ ≤
      ((3:ℝ)^d * bumpConst d * 32) * br x ^ (1 - (a:ℝ)) := by
    intro k hkS
    rw [hS, Finset.mem_filter] at hkS
    obtain ⟨hkIcc, hky⟩ := hkS
    have hk1 : 1 ≤ k := le_trans hk0 (Finset.mem_Icc.mp hkIcc).1
    have hmem := yCover_subset_annulusRk (k := k) hk1 (hW k hkIcc) hky
    rw [mem_annulus] at hmem
    have h1 := norm_iteratedFDeriv_omegaK_le (s := s) (α := α) (k := k) (a := a) ha Y x
    have h2 := coefK_mul_Wk_rpow_le hs hα ha hk1 hmem.1 hmem.2
    have h3 : (0:ℝ) ≤ (3:ℝ)^d * bumpConst d := by positivity
    calc ‖iteratedFDeriv ℝ a (omegaK s α k Y) x‖
        ≤ coefK α k * ((3:ℝ)^d * bumpConst d * (Wk s k) ^ (-(a:ℝ))) := h1
      _ = ((3:ℝ)^d * bumpConst d) * (coefK α k * (Wk s k) ^ (-(a:ℝ))) := by ring
      _ ≤ ((3:ℝ)^d * bumpConst d) * (32 * br x ^ (1 - (a:ℝ))) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = ((3:ℝ)^d * bumpConst d * 32) * br x ^ (1 - (a:ℝ)) := by ring
  have hsum' : iteratedFDeriv ℝ a (omega s α k₀ K Y) x
      = ∑ k ∈ Finset.Icc k₀ K, iteratedFDeriv ℝ a (omegaK s α k Y) x := by
    have hpsi : omega s α k₀ K Y
        = fun x => ∑ k ∈ Finset.Icc k₀ K, omegaK s α k Y x := rfl
    rw [hpsi, iteratedFDeriv_sum (fun k _ =>
        (omegaK_contDiff s α k Y).of_le (by exact_mod_cast ha)),
      Finset.sum_apply]
  rw [hsum']
  have hrestrict : ∑ k ∈ Finset.Icc k₀ K, ‖iteratedFDeriv ℝ a (omegaK s α k Y) x‖
      = ∑ k ∈ S, ‖iteratedFDeriv ℝ a (omegaK s α k Y) x‖ := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    by_cases hp : x ∈ yCover (Rk k) (Wk s k) (Nk s k) Y (Ak k)
    · rw [if_pos hp]
    · rw [if_neg hp, iteratedFDeriv_omegaK_eq_zero_of_notMem_yCover ha hp, norm_zero]
  calc ‖∑ k ∈ Finset.Icc k₀ K, iteratedFDeriv ℝ a (omegaK s α k Y) x‖
      ≤ ∑ k ∈ Finset.Icc k₀ K, ‖iteratedFDeriv ℝ a (omegaK s α k Y) x‖ := norm_sum_le _ _
    _ = ∑ k ∈ S, ‖iteratedFDeriv ℝ a (omegaK s α k Y) x‖ := hrestrict
    _ ≤ ∑ _k ∈ S, ((3:ℝ)^d * bumpConst d * 32) * br x ^ (1 - (a:ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (((3:ℝ)^d * bumpConst d * 32) * br x ^ (1 - (a:ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * (((3:ℝ)^d * bumpConst d * 32) * br x ^ (1 - (a:ℝ))) := by
        have hcard : (S.card : ℝ) ≤ 4 := by
          rw [hS]
          exact_mod_cast card_yCover_filter_le_four hk0 hW Y x
        refine mul_le_mul_of_nonneg_right hcard ?_
        have h1 : (0:ℝ) ≤ bumpConst d := bumpConst_nonneg
        have h2 : (0:ℝ) ≤ br x ^ (1 - (a:ℝ)) := Real.rpow_nonneg (le_of_lt (br_pos x)) _
        positivity
    _ = (128 * (3:ℝ)^d * bumpConst d) * (1 + ‖x‖^2)^((1-(a:ℝ))/2) := by
        rw [show br x ^ (1 - (a:ℝ)) = (1 + ‖x‖^2)^((1-(a:ℝ))/2) by
          rw [br, ← Real.rpow_mul (by nlinarith [sq_nonneg ‖x‖] : (0:ℝ) ≤ 1 + ‖x‖^2)]
          ring_nf]
        ring

end Bound

end Submission.FUP
