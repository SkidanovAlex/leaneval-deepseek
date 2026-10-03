import Mathlib
import Submission.Work.KMTPlan.A6.periodizeVarphitildeNtjBound
import Submission.Work.KMTPlan.A6.varphitildeNtj_support
import Submission.Work.KMTPlan.A6.lacunaryFloorGap
import Submission.Work.KMTPlan.A6.lacunaryFloorCount
import Submission.Work.KMTPlan.A6.lacunaryGeometricSumLeENNReal
import Submission.Work.KMTPlan.A6.thresholdScaleCountGt

namespace Work.KMTPlan.A6

open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 2000000

/-! ## Part 1: elementary conversions and counting helpers -/

private lemma enorm_eq_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  norm_num

private lemma enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [enorm_eq_ofReal_norm z,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma enorm_sq_le_of_norm_le {z : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : ‖z‖ ≤ a) :
    ‖z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (a ^ 2) := by
  rw [enorm_sq_eq]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg z])

private lemma card_le_one_of_ball {S : Finset Work.Analysis.IonescuWainger.Circle}
    {θ : Work.Analysis.IonescuWainger.Circle} {r : ℝ}
    (hball : ∀ α ∈ S, ‖θ - α‖ ≤ r)
    (hsep : ∀ α ∈ S, ∀ β ∈ S, α ≠ β → 2 * r < ‖α - β‖) : S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro α hα β hβ
  by_contra hne
  have h1 : ‖α - β‖ ≤ 2 * r := by
    calc ‖α - β‖ = ‖(α - θ) + (θ - β)‖ := by rw [show α - β = (α - θ) + (θ - β) by abel]
      _ ≤ ‖α - θ‖ + ‖θ - β‖ := norm_add_le _ _
      _ = ‖θ - α‖ + ‖θ - β‖ := by rw [norm_sub_rev]
      _ ≤ r + r := add_le_add (hball α hα) (hball β hβ)
      _ = 2 * r := by ring
  linarith [hsep α hα β hβ hne]

private lemma card_le_of_pairwise_gap {S : Finset ℕ} {Lg : ℕ}
    (h : ∀ a ∈ S, ∀ b ∈ S, a < b → b - a ≤ Lg) : S.card ≤ Lg + 1 := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  · have hmin : S.min' hS ∈ S := Finset.min'_mem S hS
    have hmax : S.max' hS ∈ S := Finset.max'_mem S hS
    have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := fun x hx =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩
    have hcard : S.card ≤ (Finset.Icc (S.min' hS) (S.max' hS)).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    rcases lt_or_eq_of_le (Finset.min'_le S (S.max' hS) hmax) with hlt | heq
    · have := h (S.min' hS) hmin (S.max' hS) hmax hlt
      omega
    · omega

/-! ## Part 2: the modified `g`-side bump -/

private lemma norm_kmtEta_sub_le_one_aux (x y : ℝ) :
    ‖Work.KMTContract.kmtEta x - Work.KMTContract.kmtEta y‖ ≤ 1 := by
  have hx : Work.KMTContract.kmtEta x = ((Work.KMTContract.kmtBump x : ℝ) : ℂ) := rfl
  have hy : Work.KMTContract.kmtEta y = ((Work.KMTContract.kmtBump y : ℝ) : ℂ) := rfl
  rw [hx, hy, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  refine ⟨?_, ?_⟩
  · have h1 := Work.KMTContract.kmtEta_le_one y
    have h2 := Work.KMTContract.kmtEta_nonneg x
    linarith
  · have h1 := Work.KMTContract.kmtEta_le_one x
    have h2 := Work.KMTContract.kmtEta_nonneg y
    linarith

private lemma norm_ee_one_aux (x : ℝ) : ‖Work.KMTAreas.A7.ee x‖ = 1 := by
  rw [Work.KMTAreas.A7.ee, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

private lemma norm_varphitildeN_le_one_aux (d N k : ℕ) (ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeN d N k ξ‖ ≤ 1 := by
  rw [Work.KMTAreas.A7.varphitildeN]
  by_cases hk : k = 0
  · rw [if_pos hk]
    exact Work.KMTContract.norm_kmtEta_le _
  · rw [if_neg hk]
    exact norm_kmtEta_sub_le_one_aux _ _

private lemma norm_varphitildeNt_le_one_aux (P : Polynomial ℤ) (N k : ℕ) (t ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖ ≤ 1 := by
  rw [Work.KMTAreas.A7.varphitildeNt, norm_mul, norm_ee_one_aux, mul_one]
  exact norm_varphitildeN_le_one_aux _ _ _ _

private lemma two_rpow_logN_le (N : ℕ) (hN : 2 ≤ N) :
    (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ (N : ℝ) := by
  have hmax : max N 2 = N := max_eq_left hN
  have hlog : Work.Analysis.EndVar.logN N = ((Nat.log 2 N : ℕ) : ℤ) := by
    simp only [Work.Analysis.EndVar.logN, hmax]
  rw [hlog]
  have hcast : (((Nat.log 2 N : ℕ) : ℤ) : ℝ) = ((Nat.log 2 N : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)

/-- The `j = -1` modified bump is the `j = 0` one times the reciprocal of its scale factor. -/
private lemma varphitildeNtj_neg_one_eq (P : Polynomial ℤ) (N k : ℕ) (t : ℝ) (ξ : ℝ) :
    varphitildeNtj P N k (-1) t ξ =
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ))
        : ℂ)⁻¹ * varphitildeNtj P N k 0 t ξ := by
  rw [varphitildeNtj, varphitildeNtj]
  simp only [zpow_neg_one, zpow_zero, one_mul]

/-- **Pointwise bound for the modified bump at `j = -1`.** -/
private lemma varphitildeNtj_neg_one_norm (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ)
    (hN : 2 ≤ N) (hk : 1 ≤ k) (t ξ : ℝ) :
    ‖varphitildeNtj P N k (-1) t ξ‖ ≤ (2 : ℝ) ^ (P.natDegree + 1) := by
  rw [varphitildeNtj_neg_one_eq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    varphitildeNtj_zero]
  by_cases hφ : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ = 0
  · rw [hφ, norm_zero, mul_zero]
    positivity
  · have hlow := (varphitildeNtj_support P hd N k 0 t ξ (by
      rw [varphitildeNtj_zero]; exact hφ)).2 hk
    have hφ1 : ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖ ≤ 1 :=
      norm_varphitildeNt_le_one_aux P N k t ξ
    have hNpow : (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ (N : ℝ) :=
      two_rpow_logN_le N hN
    have hscale : (2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ≤
        (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree := by
      have h1 : (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) =
          (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) *
            (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      have h2 : (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) =
          ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) ^ P.natDegree := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      have h3 : (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) ≤
          (N : ℝ) ^ P.natDegree := by
        rw [h2]
        exact pow_le_pow_left₀ (by positivity) hNpow _
      rw [h1]
      calc (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) *
            (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))
          ≤ (N : ℝ) ^ P.natDegree * (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree := by ring
    have hcξ : (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)) <
        |(2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * ξ| := by
      rw [abs_mul, abs_of_pos (by positivity :
        (0 : ℝ) < (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree)]
      calc (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1))
          < (2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |ξ| := hlow
        _ ≤ ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree) * |ξ| :=
            mul_le_mul_of_nonneg_right hscale (abs_nonneg ξ)
    calc |(2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * ξ|⁻¹
          * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖
        ≤ |(2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * ξ|⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hφ1 (by positivity)
      _ = |(2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * ξ|⁻¹ :=
          mul_one _
      _ ≤ (2 : ℝ) ^ (P.natDegree + 1) := by
          rcases eq_or_lt_of_le (abs_nonneg
            ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (N : ℝ) ^ P.natDegree * ξ)) with h0 | hpos
          · rw [← h0, inv_zero]
            positivity
          · have hpow : (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)) =
                ((2 : ℝ) ^ (P.natDegree + 1))⁻¹ := by
              rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
              congr 1
              have hc : (↑P.natDegree + 1 : ℝ) = ((P.natDegree + 1 : ℕ) : ℝ) := by push_cast; ring
              rw [hc, Real.rpow_natCast]
            rw [inv_le_comm₀ hpos (by positivity)]
            exact le_of_lt (hpow ▸ hcξ)

/-- **Periodised pointwise bound for the modified bump at `j = -1`.** -/
private lemma periodize_neg_one_norm (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (N k : ℕ)
    (hN : 2 ≤ N) (hk : 1 ≤ k) (hlog : (k : ℤ) ≤ Work.Analysis.EndVar.logN N) (t : ℝ)
    (y : Work.Analysis.IonescuWainger.Circle) :
    ‖Work.Analysis.IonescuWainger.periodize (varphitildeNtj P N k (-1) t) y‖
      ≤ (2 : ℝ) ^ (P.natDegree + 2) := by
  set R : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) *
    ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) with hRdef
  have hR1 : R ≤ 1 := by
    rw [hRdef, show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
    refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
    have h1 : (k : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by exact_mod_cast hlog
    nlinarith [Nat.cast_nonneg (α := ℝ) P.natDegree]
  have hvan : ∀ ξ : ℝ, R ≤ |ξ| → varphitildeNtj P N k (-1) t ξ = 0 := by
    intro ξ hξ
    rw [varphitildeNtj_neg_one_eq]
    have h0 : varphitildeNtj P N k 0 t ξ = 0 := by
      by_contra hne
      exact absurd (varphitildeNtj_support_lt P N k 0 t ξ hne) (not_lt.mpr hξ)
    rw [h0, mul_zero]
  rw [periodize_eq_pair hR1 hvan y]
  have hpt : ∀ ξ : ℝ, ‖varphitildeNtj P N k (-1) t ξ‖ ≤ (2 : ℝ) ^ (P.natDegree + 1) :=
    fun ξ => varphitildeNtj_neg_one_norm P (by omega) N k hN hk t ξ
  calc ‖varphitildeNtj P N k (-1) t (circleRep y)
        + varphitildeNtj P N k (-1) t (circleRep y - 1)‖
      ≤ ‖varphitildeNtj P N k (-1) t (circleRep y)‖
        + ‖varphitildeNtj P N k (-1) t (circleRep y - 1)‖ := norm_add_le _ _
    _ ≤ (2 : ℝ) ^ (P.natDegree + 1) + (2 : ℝ) ^ (P.natDegree + 1) :=
        add_le_add (hpt _) (hpt _)
    _ = (2 : ℝ) ^ (P.natDegree + 2) := by rw [pow_succ]; ring

/-- **Window of the periodised modified bump, for every `j`.** -/
private lemma periodize_ball_gen (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ) (j : ℤ)
    (t : ℝ) (y : Work.Analysis.IonescuWainger.Circle)
    (hy : Work.Analysis.IonescuWainger.periodize (varphitildeNtj P N k j t) y ≠ 0) :
    (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ‖y‖ < 1 := by
  obtain ⟨j', hj'⟩ : ∃ j' : ℤ, varphitildeNtj P N k j t
      ((AddCircle.equivIco (1 : ℝ) 0 y).val + (j' : ℝ)) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hy (by
      rw [Work.Analysis.IonescuWainger.periodize]
      have h0 : (fun m : ℤ => varphitildeNtj P N k j t
          ((AddCircle.equivIco (1 : ℝ) 0 y).val + (m : ℝ))) = fun _ : ℤ => (0 : ℂ) :=
        funext fun m => hcon m
      rw [h0, tsum_zero])
  set z : ℝ := (AddCircle.equivIco (1 : ℝ) 0 y).val + (j' : ℝ) with hzdef
  have hzc : ((z : ℝ) : Work.Analysis.IonescuWainger.Circle) = y := by
    rw [hzdef, AddCircle.coe_add]
    have h1 : (((AddCircle.equivIco (1 : ℝ) 0 y).val : ℝ)
        : Work.Analysis.IonescuWainger.Circle) = y := by simp
    have h2 : (((j' : ℝ)) : Work.Analysis.IonescuWainger.Circle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨j', by simp⟩
    rw [h1, h2, add_zero]
  have hzlt : |z| < (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
    varphitildeNtj_support_lt P N k j t z (by rw [hzdef]; exact hj')
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  calc (2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ‖y‖
      = (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) *
            ‖((z : ℝ) : Work.Analysis.IonescuWainger.Circle)‖ := by rw [hzc]
    _ ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ‖(z : ℝ)‖ :=
        mul_le_mul_of_nonneg_left (QuotientAddGroup.norm_mk_le_norm (m := z)) hpos.le
    _ = (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |z| := by rw [Real.norm_eq_abs]
    _ < (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) *
            (2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
        mul_lt_mul_of_pos_left hzlt hpos
    _ = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [show (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
          + (P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) = 0 by ring,
          Real.rpow_zero]

/-- **Annulus of the periodised modified bump at `k ≥ 1`.** -/
private lemma periodize_annulus_gen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (N k : ℕ) (j : ℤ)
    (t : ℝ) (hk1 : (k : ℤ) + 1 ≤ Work.Analysis.EndVar.logN N) (hk : 1 ≤ k)
    (y : Work.Analysis.IonescuWainger.Circle)
    (hy : Work.Analysis.IonescuWainger.periodize (varphitildeNtj P N k j t) y ≠ 0) :
    (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1)) <
      (2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ‖y‖ := by
  set R : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) *
    ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) with hRdef
  have hR4 : R ≤ 1 / 4 := by
    rw [hRdef]
    have hexp : (P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ -2 := by
      have h1 : (k : ℝ) + 1 ≤ (Work.Analysis.EndVar.logN N : ℝ) := by exact_mod_cast hk1
      have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      nlinarith
    have hle : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
        ≤ (2 : ℝ) ^ (-2 : ℝ) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hexp
    calc (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
        ≤ (2 : ℝ) ^ (-2 : ℝ) := hle
      _ = 1 / 4 := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
            Real.rpow_natCast]
          norm_num
  have hvan : ∀ ξ : ℝ, R ≤ |ξ| → varphitildeNtj P N k j t ξ = 0 := by
    intro ξ hξ
    by_contra hne
    exact absurd (varphitildeNtj_support_lt P N k j t ξ hne) (not_lt.mpr hξ)
  obtain ⟨ξ, hξ1, hξ2⟩ := periodize_single hR4 hvan y
  have hne : varphitildeNtj P N k j t ξ ≠ 0 := by
    intro h0
    exact hy (by rw [hξ1, h0])
  have hsupp := (varphitildeNtj_support P (by omega) N k j t ξ hne).2 hk
  calc (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1))
      < (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |ξ| := hsupp
    _ = (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ‖y‖ := by rw [hξ2]


/-! ## Part 3: the symbol family, its bounds, and the counting lemmas -/

/-- The symbol family whose square sum is estimated: on the core condition it is the periodisation
of the modified bump `φ̃_{N,t,j₂}` at `N = ⌊a n⌋`, and it vanishes off the core. -/
noncomputable def iwSqSymb (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) : ℕ → Work.Analysis.IonescuWainger.Circle → ℂ :=
  fun n => Work.Analysis.IonescuWainger.periodize
    (if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
      then varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t else 0)

private lemma iwSqSymb_of_core {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ n : ℕ}
    {j₂ : ℤ} {t : ℝ} {P : Polynomial ℤ} (h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n =
      Work.Analysis.IonescuWainger.periodize (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) := by
  simp only [iwSqSymb, if_pos h]

private lemma iwSqSymb_of_not_core {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ n : ℕ}
    {j₂ : ℤ} {t : ℝ} {P : Polynomial ℤ} (h : ¬ mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n = 0 := by
  simp only [iwSqSymb, if_neg h]
  funext y
  show (∑' _k : ℤ, (0 : ℂ)) = (0 : ℂ)
  exact tsum_zero

/-- If the `logN` of a scale is at least `2` then the scale itself is at least `4`. -/
private lemma four_le_of_logN_ge_two (N : ℕ) (h : (2 : ℤ) ≤ Work.Analysis.EndVar.logN N) :
    4 ≤ N := by
  have h1 : (2 : ℕ) ≤ (Work.Analysis.EndVar.logN N).toNat := by omega
  have h2 : 2 ^ (2 : ℕ) ≤ 2 ^ ((Work.Analysis.EndVar.logN N).toNat) :=
    Nat.pow_le_pow_right (by norm_num) h1
  have h3 : 2 ^ ((Work.Analysis.EndVar.logN N).toNat) ≤ max N 2 := by
    rw [show (Work.Analysis.EndVar.logN N).toNat = Nat.log 2 (max N 2) from rfl]
    exact Nat.pow_log_le_self 2 (by omega)
  have h4 : 4 ≤ max N 2 := by simpa using le_trans h2 h3
  omega

private lemma lt_two_pow_logN_succ (N : ℕ) :
    N < 2 ^ ((Work.Analysis.EndVar.logN N).toNat + 1) := by
  have hlog : (Work.Analysis.EndVar.logN N).toNat = Nat.log 2 (max N 2) := rfl
  rw [hlog]
  exact lt_of_le_of_lt (le_max_left N 2)
    (by simpa using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (max N 2))

/-- **The comparison of two scales satisfying the same annulus condition.** -/
private lemma annulusWindowLe_aux (a : ℕ → NNReal) (d k₂ n n' : ℕ) (hd : 1 ≤ d)
    (h2 : 2 ≤ Nat.floor (a n)) (δ : ℝ)
    (h1 : (2:ℝ)^((d:ℝ) * (((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) - (k₂:ℝ))) * δ
      ∈ Set.Ioo ((2:ℝ)^((-(d + 1) : ℤ) : ℝ)) 1)
    (h3 : (2:ℝ)^((d:ℝ) * (((Work.Analysis.EndVar.logN (Nat.floor (a n')) : ℤ) : ℝ) - (k₂:ℝ))) * δ
      ∈ Set.Ioo ((2:ℝ)^((-(d + 1) : ℤ) : ℝ)) 1) :
    (Nat.floor (a n') : ℝ) ≤ (2:ℝ)^(10:ℕ) * ((Nat.floor (a n) : ℝ)/2) := by
  set L₁ : ℝ := ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) with hL₁
  set L₂ : ℝ := ((Work.Analysis.EndVar.logN (Nat.floor (a n')) : ℤ) : ℝ) with hL₂
  have hApos : 0 < (2:ℝ) ^ ((d:ℝ) * (L₁ - (k₂:ℝ))) * δ :=
    lt_trans (Real.rpow_pos_of_pos (by norm_num) _) h1.1
  have hexpand : (2:ℝ) ^ ((d:ℝ) * (L₂ - (k₂:ℝ))) * δ =
      ((2:ℝ) ^ ((d:ℝ) * (L₁ - (k₂:ℝ))) * δ) * (2:ℝ) ^ ((d:ℝ) * (L₂ - L₁)) := by
    have h : (2:ℝ) ^ ((d:ℝ) * (L₂ - (k₂:ℝ))) =
        (2:ℝ) ^ ((d:ℝ) * (L₁ - (k₂:ℝ))) * (2:ℝ) ^ ((d:ℝ) * (L₂ - L₁)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      ring
    rw [h]; ring
  have hC : (2:ℝ) ^ ((d:ℝ) * (L₂ - L₁)) < (2:ℝ) ^ (((d:ℝ) + 1) : ℝ) := by
    have hunit : (2:ℝ) ^ (((-(d + 1) : ℤ)) : ℝ) * (2:ℝ) ^ (((d:ℝ) + 1) : ℝ) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      have h : (((-(d + 1) : ℤ)) : ℝ) + ((d:ℝ) + 1) = 0 := by push_cast; ring
      rw [h, Real.rpow_zero]
    have hA1 : 1 < ((2:ℝ) ^ ((d:ℝ) * (L₁ - (k₂:ℝ))) * δ) * (2:ℝ) ^ (((d:ℝ) + 1) : ℝ) := by
      have h1' := mul_lt_mul_of_pos_right h1.1
        (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (((d:ℝ) + 1) : ℝ))
      rw [hunit] at h1'
      exact h1'
    rw [hexpand] at h3
    have h3up : (2:ℝ) ^ ((d:ℝ) * (L₁ - (k₂:ℝ))) * δ * (2:ℝ) ^ ((d:ℝ) * (L₂ - L₁)) < 1 := h3.2
    have hprod : ((2:ℝ) ^ ((d:ℝ) * (L₁ - (k₂:ℝ))) * δ) * (2:ℝ) ^ ((d:ℝ) * (L₂ - L₁))
        < ((2:ℝ) ^ ((d:ℝ) * (L₁ - (k₂:ℝ))) * δ) * (2:ℝ) ^ (((d:ℝ) + 1) : ℝ) :=
      lt_trans h3up hA1
    exact (mul_lt_mul_iff_right₀ hApos).mp hprod
  have hexp_lt : (d:ℝ) * (L₂ - L₁) < (d:ℝ) + 1 :=
    (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hC
  set m : ℤ := Work.Analysis.EndVar.logN (Nat.floor (a n')) -
    Work.Analysis.EndVar.logN (Nat.floor (a n)) with hmdef
  have hmcast : L₂ - L₁ = (m : ℝ) := by rw [hL₁, hL₂, hmdef]; push_cast; ring
  have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hmle : m ≤ 1 := by
    by_contra hcon
    have h2 : (2:ℤ) ≤ m := by omega
    have h2' : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast h2
    have hdnn : (0:ℝ) ≤ (d:ℝ) := by linarith
    have hkey : (d:ℝ) * (m:ℝ) < (d:ℝ) + 1 := by rwa [hmcast] at hexp_lt
    have hdm : (d:ℝ) * 2 ≤ (d:ℝ) * (m:ℝ) := mul_le_mul_of_nonneg_left h2' hdnn
    nlinarith
  have hint : Work.Analysis.EndVar.logN (Nat.floor (a n')) ≤
      Work.Analysis.EndVar.logN (Nat.floor (a n)) + 1 := by
    omega
  have htoNat : (Work.Analysis.EndVar.logN (Nat.floor (a n'))).toNat ≤
      (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat + 1 := by
    have h0 := Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n))
    have h0' := Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n'))
    have hcast : ((Work.Analysis.EndVar.logN (Nat.floor (a n'))).toNat : ℤ) =
        Work.Analysis.EndVar.logN (Nat.floor (a n')) := Int.toNat_of_nonneg h0'
    have hcast2 : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) =
        Work.Analysis.EndVar.logN (Nat.floor (a n)) := Int.toNat_of_nonneg h0
    omega
  have hpow : (2 : ℕ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) ≤
      Nat.floor (a n) := by
    rw [show (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat =
      Nat.log 2 (max (Nat.floor (a n)) 2) from rfl, max_eq_left h2]
    exact Nat.pow_log_le_self 2 (by omega)
  have hlt : Nat.floor (a n') < 4 * Nat.floor (a n) := by
    calc Nat.floor (a n') < 2 ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n'))).toNat + 1) :=
          lt_two_pow_logN_succ _
      _ ≤ 2 ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat + 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 * 2 ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) := by ring
      _ ≤ 4 * Nat.floor (a n) := Nat.mul_le_mul_left 4 hpow
  have hreal : (Nat.floor (a n') : ℝ) < 4 * (Nat.floor (a n) : ℝ) := by exact_mod_cast hlt
  calc (Nat.floor (a n') : ℝ) ≤ 4 * (Nat.floor (a n) : ℝ) := le_of_lt hreal
    _ ≤ (2:ℝ)^(10:ℕ) * ((Nat.floor (a n) : ℝ)/2) := by
        have hnn : (0:ℝ) ≤ (Nat.floor (a n) : ℝ) := Nat.cast_nonneg _
        norm_num
        linarith


/-- **The `k₂ = 0` square-sum bound** (uniform in the data, via the lacunary geometric sum). -/
private lemma sqSum_fin_zero (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₁ l₂ k₁ : ℕ) (t : ℝ) (Cgeom : ENNReal)
    (hCgeomb : ∀ δ : ℝ, 0 ≤ δ →
      (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℝ)) ^ P.natDegree * δ) ^ 2 *
        (if ((Nat.floor (a n) : ℝ)) ^ P.natDegree * δ < (2 : ℝ) ^ P.natDegree then 1 else 0)))
        ≤ Cgeom)
    (M : ℕ) (y : Work.Analysis.IonescuWainger.Circle) :
    ∑ n ∈ Finset.range M,
        ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ 0 1 t n y‖ₑ ^ (2 : ℝ) ≤ Cgeom := by
  classical
  refine le_trans ?_ (hCgeomb ‖y‖ (norm_nonneg y))
  refine le_trans (Finset.sum_le_sum fun n _ => ?_) (ENNReal.sum_le_tsum _)
  by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ 0 n
  · rw [iwSqSymb_of_core hc]
    by_cases hy : Work.Analysis.IonescuWainger.periodize
        (varphitildeNtj P (Nat.floor (a n)) 0 1 t) y = 0
    · rw [hy, enorm_zero]
      simp
    · have hbnd := periodizeVarphitildeNtjBound P hd (Nat.floor (a n)) 0 1 (by simp) t
        (Or.inr rfl) (Work.Analysis.EndVar.logN_nonneg _)
      have h2 := hbnd.2.1 rfl y
      have h3 : (Nat.floor (a n) : ℝ) ^ P.natDegree * ‖y‖ < (2 : ℝ) ^ P.natDegree :=
        hbnd.2.2.1 rfl y hy
      refine le_trans (enorm_sq_le_of_norm_le (by positivity) h2) (le_of_eq ?_)
      rw [if_pos h3, mul_one]
  · rw [iwSqSymb_of_not_core hc]
    simp

/-- **The `k₂ ≥ 1` square-sum bound** (count of contributing scales), for an abstract symbol
family satisfying the annulus and term bounds. -/
private lemma sqSum_fin_pos (a : ℕ → NNReal) (d k₂ : ℕ) (hd : 1 ≤ d) (hk₂ : 1 ≤ k₂)
    (Lgap Kcnt X : ℕ)
    (hLgap : ∀ (n n' : ℕ) (x : ℝ), n < n' → 1 ≤ x → x < (Nat.floor (a n) : ℝ) →
      (Nat.floor (a n') : ℝ) ≤ (2:ℝ)^(10:ℕ) * x → n' - n ≤ Lgap)
    (hKcntb : ∀ (M X : ℕ), ((Finset.range M).filter (fun n => Nat.floor (a n) ≤ X)).card
      ≤ Kcnt * (Nat.log 2 (X + 2) + 1))
    (Φ : ℕ → Work.Analysis.IonescuWainger.Circle → ℂ) (C₁ : ℝ) (hC₁nn : 0 ≤ C₁)
    (hC₁b : ∀ (n : ℕ) (y : Work.Analysis.IonescuWainger.Circle), ‖Φ n y‖ ≤ C₁)
    (hann : ∀ (n : ℕ) (y : Work.Analysis.IonescuWainger.Circle), Φ n y ≠ 0 →
      (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) →
      (2:ℝ)^((d:ℝ) * (((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) - (k₂:ℝ))) * ‖y‖
        ∈ Set.Ioo ((2:ℝ)^((-(d + 1) : ℤ) : ℝ)) 1)
    (hB : ∀ (n : ℕ) (y : Work.Analysis.IonescuWainger.Circle), Φ n y ≠ 0 →
      ¬ ((k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))) →
      Nat.floor (a n) ≤ X)
    (M : ℕ) (y : Work.Analysis.IonescuWainger.Circle) :
    ∑ n ∈ Finset.range M, ‖Φ n y‖ₑ ^ (2 : ℝ) ≤
      (((Lgap + 1 + Kcnt * (Nat.log 2 (X + 2) + 1) : ℕ)) : ENNReal) * ENNReal.ofReal (C₁ ^ 2) := by
  classical
  have hsplit1 : ∑ n ∈ (Finset.range M).filter (fun n => Φ n y ≠ 0), ‖Φ n y‖ₑ ^ (2 : ℝ)
      = ∑ n ∈ Finset.range M, ‖Φ n y‖ₑ ^ (2 : ℝ) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro n hn hnn
    simp only [Finset.mem_filter, not_and] at hnn
    have h0 : Φ n y = 0 := by
      by_contra hc
      exact hnn hn hc
    rw [h0]
    simp
  have hset1 : (Finset.range M).filter
        (fun n => Φ n y ≠ 0 ∧ (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)))
      = ((Finset.range M).filter (fun n => Φ n y ≠ 0)).filter
        (fun n => (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))) := by
    ext n; simp only [Finset.mem_filter]; tauto
  have hset2 : (Finset.range M).filter
        (fun n => Φ n y ≠ 0 ∧ ¬ ((k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))))
      = ((Finset.range M).filter (fun n => Φ n y ≠ 0)).filter
        (fun n => ¬ ((k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)))) := by
    ext n; simp only [Finset.mem_filter]; tauto
  have hsplit2 : ∑ n ∈ (Finset.range M).filter (fun n => Φ n y ≠ 0), ‖Φ n y‖ₑ ^ (2 : ℝ)
      = ∑ n ∈ (Finset.range M).filter
            (fun n => Φ n y ≠ 0 ∧ (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))),
            ‖Φ n y‖ₑ ^ (2 : ℝ)
        + ∑ n ∈ (Finset.range M).filter
            (fun n => Φ n y ≠ 0 ∧ ¬ ((k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)))),
            ‖Φ n y‖ₑ ^ (2 : ℝ) := by
    rw [hset1, hset2, Finset.sum_filter_add_sum_filter_not]
  have hcardA : ((Finset.range M).filter
      (fun n => Φ n y ≠ 0 ∧ (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)))).card
      ≤ Lgap + 1 := by
    refine card_le_of_pairwise_gap (Lg := Lgap) ?_
    intro n hn n' hn' hlt
    simp only [Finset.mem_filter] at hn hn'
    obtain ⟨-, hn2, hn3⟩ := hn
    obtain ⟨-, hn2', hn3'⟩ := hn'
    have h4 : (2 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by omega
    have h4n : 4 ≤ Nat.floor (a n) := four_le_of_logN_ge_two _ h4
    have hann_n := hann n y hn2 hn3
    have hann_n' := hann n' y hn2' hn3'
    have hwin := annulusWindowLe_aux a d k₂ n n' hd (by omega) ‖y‖ hann_n hann_n'
    have hx1 : (1 : ℝ) ≤ (Nat.floor (a n) : ℝ) / 2 := by
      have : (4 : ℝ) ≤ (Nat.floor (a n) : ℝ) := by exact_mod_cast h4n
      linarith
    have hx2 : (Nat.floor (a n) : ℝ) / 2 < (Nat.floor (a n) : ℝ) := by
      have : (0 : ℝ) < (Nat.floor (a n) : ℝ) := by exact_mod_cast (by omega : 0 < Nat.floor (a n))
      linarith
    exact hLgap n n' ((Nat.floor (a n) : ℝ) / 2) hlt hx1 hx2 hwin
  have hcardB : ((Finset.range M).filter
      (fun n => Φ n y ≠ 0 ∧ ¬ ((k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))))).card
      ≤ Kcnt * (Nat.log 2 (X + 2) + 1) := by
    refine le_trans (Finset.card_le_card ?_) (hKcntb M X)
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨hn.1, hB n y hn.2.1 hn.2.2⟩
  have hbA : ∑ n ∈ (Finset.range M).filter
        (fun n => Φ n y ≠ 0 ∧ (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))),
        ‖Φ n y‖ₑ ^ (2 : ℝ)
      ≤ (((Finset.range M).filter
          (fun n => Φ n y ≠ 0 ∧ (k₂ : ℤ) + 1 ≤
            Work.Analysis.EndVar.logN (Nat.floor (a n)))).card : ENNReal) *
        ENNReal.ofReal (C₁ ^ 2) := by
    refine le_trans (Finset.sum_le_sum fun n _ => enorm_sq_le_of_norm_le hC₁nn (hC₁b n y)) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hbB : ∑ n ∈ (Finset.range M).filter
        (fun n => Φ n y ≠ 0 ∧ ¬ ((k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)))),
        ‖Φ n y‖ₑ ^ (2 : ℝ)
      ≤ (((Finset.range M).filter
          (fun n => Φ n y ≠ 0 ∧ ¬ ((k₂ : ℤ) + 1 ≤
            Work.Analysis.EndVar.logN (Nat.floor (a n))))).card : ENNReal) *
        ENNReal.ofReal (C₁ ^ 2) := by
    refine le_trans (Finset.sum_le_sum fun n _ => enorm_sq_le_of_norm_le hC₁nn (hC₁b n y)) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [← hsplit1, hsplit2]
  refine le_trans (add_le_add hbA hbB) ?_
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h1 : (((Finset.range M).filter
        (fun n => Φ n y ≠ 0 ∧ (k₂ : ℤ) + 1 ≤
          Work.Analysis.EndVar.logN (Nat.floor (a n)))).card : ENNReal)
      ≤ ((Lgap + 1 : ℕ) : ENNReal) := by exact_mod_cast hcardA
  have h2 : (((Finset.range M).filter
        (fun n => Φ n y ≠ 0 ∧ ¬ ((k₂ : ℤ) + 1 ≤
          Work.Analysis.EndVar.logN (Nat.floor (a n))))).card : ENNReal)
      ≤ ((Kcnt * (Nat.log 2 (X + 2) + 1) : ℕ) : ENNReal) := by exact_mod_cast hcardB
  calc _ ≤ ((Lgap + 1 : ℕ) : ENNReal) + ((Kcnt * (Nat.log 2 (X + 2) + 1) : ℕ) : ENNReal) :=
        add_le_add h1 h2
    _ = (((Lgap + 1 + Kcnt * (Nat.log 2 (X + 2) + 1)) : ℕ) : ENNReal) := by
        push_cast
        ring


/-! ## Part 3c: core facts, term bound, window and annulus of `iwSqSymb` -/

private lemma one_le_uScale (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ Work.KMTAreas.A7.uScale ρ L := by
  rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  have h : (1 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := by
    rw [Int.le_floor, one_mul]
    have hz : (0 : ℝ) ≤ 2 * ρ * (L : ℝ) := by positivity
    have h1 : ((1 : ℤ) : ℝ) = 1 := by norm_num
    rw [h1]
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) :=
          (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hz
  have h0 : (0 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := le_trans (by norm_num) h
  have hone : (1 : ℤ) ≤
      ((⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]
    exact h
  exact_mod_cast hone

private lemma core_logN_ge (ρ : ℝ) (hρ : 0 ≤ ρ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ)
    (hcore : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (k₂ : ℤ) + 2 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
  have huS : 1 ≤ Work.KMTAreas.A7.uScale ρ (max k₁ k₂) := one_le_uScale ρ hρ _
  have hmain := hcore.2.2
  have h2 : k₂ + 2 ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
    have := hmain.2
    omega
  have h0 := Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n))
  have hcast : (((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℕ) : ℤ) =
      Work.Analysis.EndVar.logN (Nat.floor (a n)) := Int.toNat_of_nonneg h0
  omega

private lemma two_le_floor_of_core (ρ : ℝ) (hρ : 0 ≤ ρ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ n : ℕ) (hcore : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) : 2 ≤ Nat.floor (a n) := by
  have h := core_logN_ge ρ hρ C₀ a l₁ l₂ k₁ k₂ n hcore
  have h4 := four_le_of_logN_ge_two (Nat.floor (a n)) (by omega)
  omega

private lemma core_logN_ge_scaleCount (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ)
    (hcore : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (2 : ℤ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ (max (max l₁ l₂) (max k₁ k₂))) ≤
      Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
  have hsc := hcore.2.1
  rw [Work.KMTAreas.A7.splitCut] at hsc
  have hle : 2 ^ (2 ^ (Work.Analysis.EndVar.scaleCount 1 ρ (max (max l₁ l₂) (max k₁ k₂))))
      ≤ max (Nat.floor (a n)) 2 := le_trans (le_of_lt hsc) (le_max_left _ _)
  have h := Nat.le_log_of_pow_le (b := 2) (by norm_num : 1 < 2) hle
  rw [Work.Analysis.EndVar.logN]
  exact_mod_cast h

private lemma iwSqSymb_term_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ)
    (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk2j2 : k₂ ≠ 0 ∨ j₂ = 1)
    (n : ℕ) (y : Work.Analysis.IonescuWainger.Circle) :
    ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n y‖ ≤ (2 : ℝ) ^ (P.natDegree + 2) := by
  by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · rw [iwSqSymb_of_core hc]
    have hN2 : 2 ≤ Nat.floor (a n) := two_le_floor_of_core ρ hρ C₀ a l₁ l₂ k₁ k₂ n hc
    have hlog : (k₂ : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
      have := core_logN_ge ρ hρ C₀ a l₁ l₂ k₁ k₂ n hc
      omega
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hj₂) with hj | hj | hj
    · -- j₂ = -1
      subst hj
      have hk : 1 ≤ k₂ := by
        rcases hk2j2 with h | h
        · omega
        · exact absurd h (by norm_num)
      exact periodize_neg_one_norm P hd (Nat.floor (a n)) k₂ hN2 hk hlog t y
    · -- j₂ = 0
      subst hj
      have hb := (periodizeVarphitildeNtjBound P hd (Nat.floor (a n)) k₂ 0 (by simp) t hk2j2 hlog).1 y
      have : (2 : ℝ) ^ (P.natDegree + 1) ≤ (2 : ℝ) ^ (P.natDegree + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_trans hb this
    · -- j₂ = 1
      subst hj
      have hb := (periodizeVarphitildeNtjBound P hd (Nat.floor (a n)) k₂ 1 (by simp) t hk2j2 hlog).1 y
      have : (2 : ℝ) ^ (P.natDegree + 1) ≤ (2 : ℝ) ^ (P.natDegree + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_trans hb this
  · rw [iwSqSymb_of_not_core hc]
    simp only [Pi.zero_apply, norm_zero]
    positivity

private lemma iwSqSymb_window (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ)
    (hk2j2 : k₂ ≠ 0 ∨ j₂ = 1) (n : ℕ) (hcore : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n)
    (y : Work.Analysis.IonescuWainger.Circle)
    (hy : iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n y ≠ 0) :
    ‖y‖ ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) + P.natDegree) := by
  rw [iwSqSymb_of_core hcore] at hy
  have hN2 : 2 ≤ Nat.floor (a n) := two_le_floor_of_core ρ hρ C₀ a l₁ l₂ k₁ k₂ n hcore
  rcases eq_or_ne k₂ 0 with hk0 | hk0
  · have hj1 : j₂ = 1 := by
      rcases hk2j2 with h | h
      · exact absurd hk0 h
      · exact h
    subst hk0
    subst hj1
    have hbnd := periodizeVarphitildeNtjBound P hd (Nat.floor (a n)) 0 1 (by simp) t
      (Or.inr rfl) (Work.Analysis.EndVar.logN_nonneg _)
    have h3 : (Nat.floor (a n) : ℝ) ^ P.natDegree * ‖y‖ < (2 : ℝ) ^ P.natDegree :=
      hbnd.2.2.1 rfl y hy
    have hNpow : (2 : ℝ) ^ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) ≤
        (Nat.floor (a n) : ℝ) := two_rpow_logN_le _ hN2
    have hNpos : (0 : ℝ) < (Nat.floor (a n) : ℝ) := by
      have : (2 : ℝ) ≤ (Nat.floor (a n) : ℝ) := by exact_mod_cast hN2
      linarith
    have hlt : ‖y‖ < (2 : ℝ) ^ P.natDegree / (Nat.floor (a n) : ℝ) ^ P.natDegree := by
      rw [lt_div_iff₀ (by positivity)]
      linarith [h3]
    have h2pow : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) ≤
        (Nat.floor (a n) : ℝ) := two_rpow_logN_le _ hN2
    calc ‖y‖ ≤ (2 : ℝ) ^ P.natDegree / (Nat.floor (a n) : ℝ) ^ P.natDegree := le_of_lt hlt
      _ ≤ (2 : ℝ) ^ P.natDegree /
            ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) ^ P.natDegree := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          exact pow_le_pow_left₀ (by positivity) h2pow _
      _ = (2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((0 : ℕ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) + P.natDegree) := by
          have hexp : ((P.natDegree : ℝ) *
                ((0 : ℕ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) + P.natDegree)
              = ((P.natDegree : ℝ) *
                (0 - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) + P.natDegree) := by
            norm_num
          rw [hexp]
          have h2 : (2 : ℝ) ^ P.natDegree = (2 : ℝ) ^ ((P.natDegree : ℝ)) :=
            (Real.rpow_natCast 2 P.natDegree).symm
          have h3 : ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) ^ P.natDegree
              = (2 : ℝ) ^ ((P.natDegree : ℝ) *
                  ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)),
              ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            ring_nf
          rw [h2, h3, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
  · have hk₁ : 1 ≤ k₂ := by omega
    have hball := periodize_ball_gen P (by omega) (Nat.floor (a n)) k₂ j₂ t y hy
    have hpos : 0 < (2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) - (k₂ : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    calc ‖y‖ = ((2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) - (k₂ : ℝ))))⁻¹ *
          ((2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) - (k₂ : ℝ))) * ‖y‖) :=
          (inv_mul_cancel_left₀ (ne_of_gt hpos) ‖y‖).symm
      _ ≤ ((2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) - (k₂ : ℝ))))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (le_of_lt hball) (by positivity)
      _ ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) + P.natDegree) := by
          rw [mul_one, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          rw [show -((P.natDegree : ℝ) *
                ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) - (k₂ : ℝ)))
              = ((P.natDegree : ℝ) *
                ((k₂ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))) from by ring]
          refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
          have hd0 : (0 : ℝ) ≤ (P.natDegree : ℝ) := by positivity
          linarith

private lemma iwSqSymb_annulus (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ)
    (hk₂ : 1 ≤ k₂) (n : ℕ) (hcore : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n)
    (y : Work.Analysis.IonescuWainger.Circle)
    (hy : iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n y ≠ 0) :
    (2 : ℝ) ^ (((-(P.natDegree + 1) : ℤ)) : ℝ) <
      (2 : ℝ) ^ ((P.natDegree : ℝ) *
        (((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) - (k₂ : ℝ))) * ‖y‖ := by
  rw [iwSqSymb_of_core hcore] at hy
  have hlog : (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
    have := core_logN_ge ρ hρ C₀ a l₁ l₂ k₁ k₂ n hcore
    omega
  have h := periodize_annulus_gen P hd (Nat.floor (a n)) k₂ j₂ t hlog hk₂ y hy
  have hc : (((-(P.natDegree + 1) : ℤ)) : ℝ) = -(↑P.natDegree + 1) := by push_cast; ring
  rwa [hc]


private lemma iwSqSymb_core_of_ne_zero {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ n : ℕ}
    {j₂ : ℤ} {t : ℝ} {P : Polynomial ℤ} {y : Work.Analysis.IonescuWainger.Circle}
    (h : iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n y ≠ 0) : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n := by
  by_contra hc
  exact h (congrFun (iwSqSymb_of_not_core hc) y)

/-- **The square-function bound for the modified model symbol.** -/
theorem iwSymbolTleSqSumGen (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ W : NNReal, ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₂ : ℤ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → (k₂ ≠ 0 ∨ j₂ = 1) →
      ∀ θ : Work.Analysis.IonescuWainger.Circle,
        (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.Analysis.IonescuWainger.periodize
              (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
               then Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t else 0)) θ‖ₑ ^ (2 : ℝ))
          ≤ (W : ENNReal) ^ 2 := by
  classical
  obtain ⟨Cs, hCs, hsep0⟩ := Work.Analysis.IonescuWainger.iw_height_separated (ρ := ρ) hρ
  obtain ⟨Lmax, hLmax⟩ := thresholdScaleCountGt ρ hρ P.natDegree hd Cs hCs
  obtain ⟨Lgap, hLgap0⟩ := lacunaryFloorGap Λ hΛ ((2 : ℝ) ^ (10 : ℕ)) (by norm_num)
  obtain ⟨Kcnt, hKcnt0⟩ := lacunaryFloorCount Λ hΛ
  obtain ⟨Cgeom, hCgeomne, hCgeomb0⟩ := lacunaryGeometricSumLeENNReal Λ hΛ P.natDegree (by omega)
  obtain ⟨Ccard, hCcardpos, hCcard0⟩ := Work.Analysis.IonescuWainger.iw_height_card_le (ρ := ρ) hρ
  set Nb2 : ℕ := Kcnt * (Nat.log 2 (2 ^ (Lmax + 1) + 2) + 1) with hNb2def
  set C₁ : ℝ := (2 : ℝ) ^ (P.natDegree + 2) with hC₁def
  have hC₁nn : 0 ≤ C₁ := by rw [hC₁def]; positivity
  set Bmax : ENNReal :=
    max Cgeom ((((Lgap + 1 + Nb2 : ℕ)) : ENNReal) * ENNReal.ofReal (C₁ ^ 2)) with hBmaxdef
  have hBmaxne : Bmax ≠ ⊤ := by
    rw [hBmaxdef]
    exact (max_lt (lt_top_iff_ne_top.mpr hCgeomne)
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))).ne
  set AmaxN : ℝ := max (Ccard * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (Lmax : ℝ)))) 1 with hAmaxNdef
  have hAmaxN1 : 1 ≤ AmaxN := le_max_right _ _
  set Wr : ℝ := Bmax.toReal * AmaxN ^ 2 + 1 with hWrdef
  have hWr1 : 1 ≤ Wr := by
    rw [hWrdef]
    have h := ENNReal.toReal_nonneg (a := Bmax)
    nlinarith [sq_nonneg AmaxN]
  have hWrnn : 0 ≤ Wr := by linarith
  let W : NNReal := ⟨Wr, hWrnn⟩
  refine ⟨W, ?_⟩
  intro a l₁ l₂ k₁ k₂ t j₂ hLac ha1 ht hj₂ hk2j2 θ
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ with hAdef
  change (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet A
      (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ₑ ^ (2 : ℝ)) ≤ ((W : ENNReal)) ^ 2
  set L : ℕ := max (max l₁ l₂) (max k₁ k₂) with hLdef
  have hWsq : ((W : ENNReal)) ^ 2 = ENNReal.ofReal (Wr ^ 2) := by
    rw [show (W : ENNReal) = ENNReal.ofReal Wr from
        (ENNReal.ofReal_coe_nnreal (p := W)).symm,
      ← ENNReal.ofReal_pow (show (0 : ℝ) ≤ Wr by linarith)]
  -- abbreviations
  have hLgapA : ∀ (n n' : ℕ) (x : ℝ), n < n' → 1 ≤ x → x < (Nat.floor (a n) : ℝ) →
      (Nat.floor (a n') : ℝ) ≤ (2:ℝ)^(10:ℕ) * x → n' - n ≤ Lgap :=
    fun n n' x => hLgap0 a hLac n n' x
  have hKcntA : ∀ (M X : ℕ), ((Finset.range M).filter (fun n => Nat.floor (a n) ≤ X)).card
      ≤ Kcnt * (Nat.log 2 (X + 2) + 1) := fun M X => hKcnt0 a hLac ha1 M X
  have hCgeombA : ∀ δ : ℝ, 0 ≤ δ →
      (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℝ)) ^ P.natDegree * δ) ^ 2 *
        (if ((Nat.floor (a n) : ℝ)) ^ P.natDegree * δ < (2 : ℝ) ^ P.natDegree then 1 else 0)))
        ≤ Cgeom := fun δ hδ => hCgeomb0 a hLac ha1 δ hδ
  -- the term bound
  have hC₁b : ∀ (n : ℕ) (y : Work.Analysis.IonescuWainger.Circle),
      ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n y‖ ≤ C₁ := by
    intro n y
    rw [hC₁def]
    exact iwSqSymb_term_le P hd ρ hρ.le C₀ a l₁ l₂ k₁ k₂ j₂ t hj₂ hk2j2 n y
  -- the uniform bound for a single frequency
  have hper : ∀ y : Work.Analysis.IonescuWainger.Circle,
      (∑' n : ℕ, ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n y‖ₑ ^ (2 : ℝ)) ≤ Bmax := by
    intro y
    refine ENNReal.tsum_le_of_sum_range_le fun M => ?_
    rcases eq_or_ne k₂ 0 with hk0 | hk0
    · have hj1 : j₂ = 1 := by
        rcases hk2j2 with h | h
        · exact absurd hk0 h
        · exact h
      subst hj1
      subst hk0
      refine le_trans (sqSum_fin_zero P hd ρ C₀ a l₁ l₂ k₁ t Cgeom hCgeombA M y) ?_
      rw [hBmaxdef]
      exact le_max_left _ _
    · have hk₁ : 1 ≤ k₂ := by omega
      have hann : ∀ (n : ℕ) (y' : Work.Analysis.IonescuWainger.Circle),
          iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n y' ≠ 0 →
          (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) →
          (2:ℝ)^((P.natDegree:ℝ) * (((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) - (k₂:ℝ)))
              * ‖y'‖ ∈ Set.Ioo ((2:ℝ)^((-(P.natDegree + 1) : ℤ) : ℝ)) 1 := by
        intro n y' hy hlog
        refine ⟨?_, ?_⟩
        · exact iwSqSymb_annulus P hd ρ hρ.le C₀ a l₁ l₂ k₁ k₂ j₂ t hk₁ n
            (iwSqSymb_core_of_ne_zero hy) y' hy
        · rw [iwSqSymb_of_core (iwSqSymb_core_of_ne_zero hy)] at hy
          exact periodize_ball_gen P (by omega) (Nat.floor (a n)) k₂ j₂ t y' hy
      have hB : ∀ (n : ℕ) (y' : Work.Analysis.IonescuWainger.Circle),
          iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n y' ≠ 0 →
          ¬ ((k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))) →
          Nat.floor (a n) ≤ 2 ^ (Lmax + 1) := by
        intro n y' hy hnot
        have hcore := iwSqSymb_core_of_ne_zero hy
        by_cases hkb : k₂ ≤ Lmax
        · have hle : Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ (k₂ : ℤ) := by omega
          have hlt : Nat.floor (a n) < 2 ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat + 1) :=
            lt_two_pow_logN_succ _
          have htoNat : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat ≤ k₂ := by
            have hcast : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) =
                Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
              Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
            omega
          calc Nat.floor (a n)
              ≤ 2 ^ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat + 1) := le_of_lt hlt
            _ ≤ 2 ^ (k₂ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ 2 ^ (Lmax + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        · have hk₂gt : Lmax < k₂ := by omega
          have hLg : Lmax ≤ L := by omega
          have hgoodcase := hLmax L hLg
          have hscgt : L < 2 ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) := by
            have hcast : (2 : ℝ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L)
                = ((2 : ℕ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) : ℝ) := by
              push_cast
              ring
            rw [hcast] at hgoodcase
            have hdc : (0 : ℝ) < (P.natDegree : ℝ) := by positivity
            have hCs2 : (0 : ℝ) ≤ Cs * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
              mul_nonneg hCs.le (Real.rpow_nonneg (by norm_num) _)
            have hreal : ((L : ℕ) : ℝ) <
                ((2 : ℕ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) : ℝ) := by
              nlinarith [hgoodcase]
            exact_mod_cast hreal
          have hge : (2 : ℤ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L)
              ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
            have h := core_logN_ge_scaleCount ρ C₀ a l₁ l₂ k₁ k₂ n hcore
            rwa [hLdef]
          have hfin : (k₂ : ℤ) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
            have h1 : k₂ + 1 ≤ 2 ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) := by omega
            have h2 : (((k₂ + 1 : ℕ)) : ℤ) ≤ (2 : ℤ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) := by
              rw [show (2 : ℤ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L)
                  = (((2 : ℕ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) : ℕ) : ℤ) from by
                push_cast; ring]
              exact_mod_cast h1
            omega
          exact absurd hfin hnot
      refine le_trans (sqSum_fin_pos a P.natDegree k₂ (by omega) hk₁ Lgap Kcnt (2 ^ (Lmax + 1))
        hLgapA hKcntA (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t) C₁ hC₁nn hC₁b hann hB M y) ?_
      rw [hBmaxdef]
      exact le_max_right _ _
  -- the main bound
  have hmid : (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet A
        (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ₑ ^ (2 : ℝ))
      ≤ ENNReal.ofReal (Bmax.toReal * AmaxN ^ 2) := by
    by_cases hgood : (P.natDegree : ℝ) * (2 : ℝ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L)
        > (3 * P.natDegree + 3 : ℝ) + P.natDegree * (L : ℝ) + Cs * (2 : ℝ) ^ (ρ * (L : ℝ))
    · -- good case
      set sc : ℕ := Work.Analysis.EndVar.scaleCount 1 ρ L with hscdef
      have hscR : (((2 : ℕ) ^ sc : ℕ) : ℝ) = (2 : ℝ) ^ sc := by push_cast; ring
      have hscgt : L < 2 ^ sc := by
        have h := hgood
        have hdc : (0 : ℝ) < (P.natDegree : ℝ) := by positivity
        have hCs2 : (0 : ℝ) ≤ Cs * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
          mul_nonneg hCs.le (Real.rpow_nonneg (by norm_num) _)
        have hreal : (L : ℝ) < ((2 : ℕ) ^ sc : ℝ) := by
          have hcast : ((2 : ℕ) ^ sc : ℝ) = (2 : ℝ) ^ sc := by push_cast; ring
          rw [hcast]
          nlinarith [h]
        exact_mod_cast hreal
      have hgoodR : (P.natDegree : ℝ) * (2 : ℝ) ^ sc
          > (3 * (P.natDegree : ℝ) + 3) + (P.natDegree : ℝ) * (L : ℝ)
            + Cs * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
        exact hgood
      have hlogN_ge : ∀ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n →
          (((2 : ℕ) ^ sc : ℕ) : ℝ) ≤
            ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) := by
        intro n hn
        have h := core_logN_ge_scaleCount ρ C₀ a l₁ l₂ k₁ k₂ n hn
        have h1 : (2 : ℤ) ^ sc ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
          rw [hscdef, hLdef]
          exact h
        have h2 : (2 : ℤ) ^ sc = (((2 : ℕ) ^ sc : ℕ) : ℤ) := by push_cast; ring
        rw [h2] at h1
        exact_mod_cast h1
      have hk₂L : k₂ ≤ L := by
        rw [hLdef]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
      have hl₂L : l₂ ≤ L := by
        rw [hLdef]
        exact le_trans (le_max_right l₁ l₂) (le_max_left _ _)
      have hsep_lt : 2 * (2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree)
          < (2 : ℝ) ^ (-(Cs * (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) := by
        have hkey : (P.natDegree : ℝ) * ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree + 1
            < -(Cs * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) := by
          have hl₂R : (l₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl₂L
          have hρl : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
            refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
            nlinarith [hρ.le]
          have hCs2 : Cs * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ Cs * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
            mul_le_mul_of_nonneg_left hρl hCs.le
          have hkk : (k₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hk₂L
          rw [hscR]
          nlinarith [hgoodR, hCs2, hkk]
        have heq : 2 * (2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree)
            = (2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree + 1) := by
          have hrw := Real.rpow_add (show (0 : ℝ) < 2 by norm_num) (1 : ℝ)
            ((P.natDegree : ℝ) * ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree)
          rw [Real.rpow_one] at hrw
          rw [← hrw]
          congr 1
          ring
        rw [heq]
        exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hkey
      have huniq : ∀ α ∈ A, ∀ β ∈ A,
          (∃ n : ℕ, iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α) ≠ 0) →
          (∃ n : ℕ, iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - β) ≠ 0) → α = β := by
        intro α hα β hβ ⟨n, hn⟩ ⟨n', hn'⟩
        by_contra hne
        have hcn := iwSqSymb_core_of_ne_zero hn
        have hcn' := iwSqSymb_core_of_ne_zero hn'
        have hwn := iwSqSymb_window P hd ρ hρ.le C₀ a l₁ l₂ k₁ k₂ j₂ t hk2j2 n hcn (θ - α) hn
        have hwn' := iwSqSymb_window P hd ρ hρ.le C₀ a l₁ l₂ k₁ k₂ j₂ t hk2j2 n' hcn' (θ - β) hn'
        have hRn : ‖θ - α‖ ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree) := by
          refine le_trans hwn ?_
          have h2sc : (((2 : ℕ) ^ sc : ℕ) : ℝ) ≤
              ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) := by
            exact_mod_cast hlogN_ge n hcn
          refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
          nlinarith [h2sc]
        have hRn' : ‖θ - β‖ ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree) := by
          refine le_trans hwn' ?_
          have h2sc : (((2 : ℕ) ^ sc : ℕ) : ℝ) ≤
              ((Work.Analysis.EndVar.logN (Nat.floor (a n')) : ℤ) : ℝ) := by
            exact_mod_cast hlogN_ge n' hcn'
          refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
          nlinarith [h2sc]
        have hsep' := hsep0 l₂ hα hβ hne
        have hbd : ‖α - β‖ ≤ 2 * (2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree) := by
          calc ‖α - β‖ = ‖(α - θ) + (θ - β)‖ := by rw [show α - β = (α - θ) + (θ - β) by abel]
            _ ≤ ‖α - θ‖ + ‖θ - β‖ := norm_add_le _ _
            _ = ‖θ - α‖ + ‖θ - β‖ := by rw [norm_sub_rev]
            _ ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) *
                  ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree)
                + (2 : ℝ) ^ ((P.natDegree : ℝ) *
                  ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree) := add_le_add hRn hRn'
            _ = 2 * (2 : ℝ) ^ ((P.natDegree : ℝ) *
                  ((k₂ : ℝ) - (((2 : ℕ) ^ sc : ℕ) : ℝ)) + P.natDegree) := by ring
        linarith [hsep_lt, hsep', hbd]
      by_cases hex : ∃ α ∈ A, ∃ n : ℕ, iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α) ≠ 0
      · obtain ⟨αw, hαw, hwit⟩ := hex
        have hm : ∀ n : ℕ, Work.Analysis.IonescuWainger.iwSymbolSet A
              (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ
            = iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - αw) := by
          intro n
          rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply]
          refine Finset.sum_eq_single αw ?_ ?_
          · intro b hb hbne
            by_contra hb0
            exact hbne (huniq b hb αw hαw ⟨n, hb0⟩ hwit)
          · intro hnot
            exact absurd hαw hnot
        refine le_trans ?_ (le_trans (hper (θ - αw)) ?_)
        · refine ENNReal.tsum_le_tsum fun n => ?_
          rw [hm n]
        · calc Bmax = ENNReal.ofReal Bmax.toReal := (ENNReal.ofReal_toReal hBmaxne).symm
            _ = ENNReal.ofReal Bmax.toReal * 1 := (mul_one _).symm
            _ ≤ ENNReal.ofReal Bmax.toReal * ENNReal.ofReal (AmaxN ^ 2) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (by nlinarith [hAmaxN1])
            _ = ENNReal.ofReal (Bmax.toReal * AmaxN ^ 2) := by
                rw [ENNReal.ofReal_mul (ENNReal.toReal_nonneg (a := Bmax))]
      · have hzero : ∀ n : ℕ, Work.Analysis.IonescuWainger.iwSymbolSet A
            (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ = 0 := by
          intro n
          rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply]
          refine Finset.sum_eq_zero fun α hα => ?_
          by_contra hne
          exact hex ⟨α, hα, n, hne⟩
        have h0 : (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet A
              (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ₑ ^ (2 : ℝ)) = 0 := by
          have hfun : (fun n : ℕ => ‖Work.Analysis.IonescuWainger.iwSymbolSet A
              (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ₑ ^ (2 : ℝ))
              = fun _ => (0 : ENNReal) := by
            funext n
            rw [hzero n, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
          rw [hfun, tsum_zero]
        rw [h0]
        positivity
    · -- bad case
      have hLlt : L < Lmax := by
        by_contra hcon
        exact hgood (hLmax L (le_of_not_gt hcon))
      have hl₂Lmax : l₂ ≤ Lmax := by
        have hl : l₂ ≤ L := by
          rw [hLdef]
          exact le_trans (le_max_right l₁ l₂) (le_max_left _ _)
        omega
      have hAcard : ((A.card : ℝ)) ≤ AmaxN := by
        have h1 := hCcard0 l₂
        have h2 : (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ)))
            ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (Lmax : ℝ))) := by
          refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
          refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
          have hl : (l₂ : ℝ) ≤ (Lmax : ℝ) := by exact_mod_cast hl₂Lmax
          nlinarith [hρ.le]
        have h3 : Ccard * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ)))
            ≤ Ccard * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (Lmax : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 hCcardpos.le
        refine le_trans h1 (le_trans h3 ?_)
        rw [hAmaxNdef]
        exact le_max_left _ _
      have hCS : ∀ n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet A
            (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ₑ ^ (2 : ℝ)
          ≤ (A.card : ENNReal) * ∑ α ∈ A,
              ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ₑ ^ (2 : ℝ) := by
        intro n
        have h1 : ‖Work.Analysis.IonescuWainger.iwSymbolSet A
              (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ ^ 2
            ≤ (A.card : ℝ) * ∑ α ∈ A,
                ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ ^ 2 := by
          rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply]
          calc ‖∑ α ∈ A, iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ ^ 2
              ≤ (∑ α ∈ A, ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
            _ ≤ (A.card : ℝ) * ∑ α ∈ A,
                  ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ ^ 2 :=
                sq_sum_le_card_mul_sum_sq
        calc ‖Work.Analysis.IonescuWainger.iwSymbolSet A
              (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ₑ ^ (2 : ℝ)
            = ENNReal.ofReal (‖Work.Analysis.IonescuWainger.iwSymbolSet A
                (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ ^ 2) := enorm_sq_eq _
          _ ≤ ENNReal.ofReal ((A.card : ℝ) * ∑ α ∈ A,
                ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ ^ 2) :=
              ENNReal.ofReal_le_ofReal h1
          _ = (A.card : ENNReal) * ∑ α ∈ A,
                ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ₑ ^ (2 : ℝ) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
              congr 1
              rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => by positivity)]
              exact Finset.sum_congr rfl fun α _ => (enorm_sq_eq _).symm
      have hbody : ∀ M : ℕ, ∑ n ∈ Finset.range M, ‖Work.Analysis.IonescuWainger.iwSymbolSet A
            (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ₑ ^ (2 : ℝ)
          ≤ (ENNReal.ofReal AmaxN) ^ 2 * Bmax := by
        intro M
        calc ∑ n ∈ Finset.range M, ‖Work.Analysis.IonescuWainger.iwSymbolSet A
              (iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n) θ‖ₑ ^ (2 : ℝ)
            ≤ ∑ n ∈ Finset.range M, (A.card : ENNReal) * ∑ α ∈ A,
                ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ₑ ^ (2 : ℝ) :=
              Finset.sum_le_sum fun n _ => hCS n
          _ = (A.card : ENNReal) * ∑ n ∈ Finset.range M, ∑ α ∈ A,
                ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ₑ ^ (2 : ℝ) := by
              rw [Finset.mul_sum]
          _ = (A.card : ENNReal) * ∑ α ∈ A, ∑ n ∈ Finset.range M,
                ‖iwSqSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n (θ - α)‖ₑ ^ (2 : ℝ) := by
              rw [Finset.sum_comm]
          _ ≤ (A.card : ENNReal) * ∑ _α ∈ A, Bmax := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => ?_) (by positivity)
              exact le_trans (ENNReal.sum_le_tsum _) (hper (θ - α))
          _ = (A.card : ENNReal) * ((A.card : ENNReal) * Bmax) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = (A.card : ENNReal) ^ 2 * Bmax := by ring
          _ ≤ (ENNReal.ofReal AmaxN) ^ 2 * Bmax := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have hA : ((A.card : ℕ) : ENNReal) ≤ ENNReal.ofReal AmaxN := by
                rw [← ENNReal.ofReal_natCast]
                exact ENNReal.ofReal_le_ofReal hAcard
              exact pow_le_pow_left₀ (by positivity) hA 2
      refine le_trans (ENNReal.tsum_le_of_sum_range_le hbody) ?_
      calc (ENNReal.ofReal AmaxN) ^ 2 * Bmax
          = ENNReal.ofReal (AmaxN ^ 2) * Bmax := by
            rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ AmaxN by linarith)]
        _ = ENNReal.ofReal (AmaxN ^ 2) * ENNReal.ofReal Bmax.toReal := by
            rw [ENNReal.ofReal_toReal hBmaxne]
        _ = ENNReal.ofReal (AmaxN ^ 2 * Bmax.toReal) := by
            rw [ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (Bmax.toReal * AmaxN ^ 2) := by rw [mul_comm]
  have hstep : Bmax.toReal * AmaxN ^ 2 ≤ Wr ^ 2 := by
    have h1 : Bmax.toReal * AmaxN ^ 2 ≤ Wr := by
      rw [hWrdef]
      linarith
    calc Bmax.toReal * AmaxN ^ 2 ≤ Wr := h1
      _ ≤ Wr ^ 2 := by nlinarith [hWr1]
  refine le_trans hmid ?_
  refine le_trans (ENNReal.ofReal_le_ofReal hstep) ?_
  rw [hWsq]


end Work.KMTPlan.A6

