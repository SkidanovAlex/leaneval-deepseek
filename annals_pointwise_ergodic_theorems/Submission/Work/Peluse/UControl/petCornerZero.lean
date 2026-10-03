import Mathlib
import Submission.Work.Peluse.UControl.peluseProp34Defs
import Submission.Work.Peluse.UControl.l1_pow_lower
import Submission.Work.Peluse.UControl.parBox_card

/-!
# The corner `⌊δ'M⌋ ≤ C` of the PET chapter

This file proves `Work.Peluse.UControl.petCornerZero`: the elementary lower bound for `linFamAvg`
in the *corner* regime of the PET chapter (the regime in which the PET chain cannot run, i.e. where
the window `H` is bounded by a constant `Kc`).

The mathematics is a single-term extraction: at the parameter `a = 0` every direction
`petDir D l c 0 i` vanishes, so the `y`-sum is `M` copies of the same product; with `b` the
*balanced* Boolean family (`#{b = false} = t-1`, `#{b = true} = t`, possible because
`|I (l-1)| = 2t-1`), the product times the outer `f x` is `f x ^ t * conj (f x) ^ t = ‖f x‖^{2t}`,
a nonnegative real.  Hence the `a = 0` fibre of `linFamAvg` is exactly `N⁻¹ ∑_{x∈symIcc N} ‖f x‖^{2t}`,
and the claimed inequality follows from the power-mean (Hölder) inequality `l1_pow_lower` and the
hypothesis `γ N ≤ ∑_{x∈symIcc N} ‖f x‖`.

This is the content of the lemmas `linFamAvg_zero_term` and of the constant bookkeeping in
`NOTES_petChapter5_session13.md` §B.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## Elementary `symIcc` facts -/

private lemma petCorner_mem_symIcc {L : ℕ} {x : ℤ} : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]; omega

private lemma petCorner_natAbs_lt_of_not_mem_symIcc {L : ℕ} {x : ℤ} (h : x ∉ symIcc L) :
    L < x.natAbs := by
  rw [petCorner_mem_symIcc] at h; omega

/-! ## The balanced Boolean family -/

/-- A Boolean family on `Fin n` with exactly `t - 1` false and `t` true values, when `n = 2t - 1`. -/
private lemma exists_balanced_bool (n t : ℕ) (hm : n = 2 * t - 1) (ht : 1 ≤ t) :
    ∃ b : Fin n → Bool,
      (Finset.univ.filter (fun i => b i = false)).card = t - 1 ∧
      (Finset.univ.filter (fun i => b i = true)).card = t := by
  classical
  have hn : t - 1 ≤ n := by omega
  obtain ⟨s, -, hsc⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := t - 1) (by rw [Finset.card_univ, Fintype.card_fin]; exact hn)
  let b : Fin n → Bool := fun i => decide (i ∉ s)
  have hfalse : (Finset.univ.filter (fun i => b i = false)) = s := by
    ext i
    simp only [b, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ s <;> simp [hi]
  refine ⟨b, ?_, ?_⟩
  · rw [hfalse, hsc]
  · have hnot : (Finset.univ.filter (fun i => ¬ (b i = true)))
        = Finset.univ.filter (fun i => b i = false) := by
      refine Finset.filter_congr (fun i _ => ?_)
      cases b i <;> simp
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => b i = true)
    rw [hnot, Finset.card_univ, Fintype.card_fin, hfalse, hsc] at hsplit
    omega

/-- The number of `true` values of a Boolean family with `t - 1` false values on `2t-1` indices. -/
private lemma filter_true_card_eq {n t : ℕ} (b : Fin n → Bool) (hm : n = 2 * t - 1)
    (hb : (Finset.univ.filter (fun i => b i = false)).card = t - 1) :
    (Finset.univ.filter (fun i => b i = true)).card = t := by
  have hnot : (Finset.univ.filter (fun i => ¬ (b i = true)))
      = Finset.univ.filter (fun i => b i = false) := by
    refine Finset.filter_congr (fun i _ => ?_)
    cases b i <;> simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => b i = true)
  rw [hnot, Finset.card_univ, Fintype.card_fin, hb] at hsplit
  omega

/-! ## The direction at the zero parameter -/

/-- At level `j + 1` the direction is a sum of terms carrying a level-`(j+1)` parameter, so it
vanishes for a parameter family that is zero at the level `j + 1`. -/
lemma dir_succ_zero (D : IdxDatum) (l : ℕ) (c : ℤ) (j : ℕ) (w : D.I (j+1))
    (a : (j : ℕ) → D.S j → ℤ) (ha : ∀ s : D.S (j+1), a (j+1) s = 0) :
    D.dir l c (j+1) w a = 0 := by
  simp only [IdxDatum.dir]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  rw [ha s, mul_zero]

/-- `dir` vanishes at every positive level for a parameter family that is zero everywhere. -/
lemma dir_zero_of_one_le (D : IdxDatum) (l : ℕ) (c : ℤ) :
    ∀ (j : ℕ) (_ : 1 ≤ j) (w : D.I j) (a : (j : ℕ) → D.S j → ℤ),
      (∀ k s, a k s = 0) → D.dir l c j w a = 0 := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ k ih =>
    intro _ w a ha
    exact dir_succ_zero D l c k w a (fun s => ha (k+1) s)

/-- Every direction of the datum vanishes at the zero parameter (for `l ≥ 2`). -/
lemma petDir_zero_of_zero (D : IdxDatum) (l : ℕ) (hl : 2 ≤ l) (c : ℤ)
    (i : Fin (Fintype.card (D.I (l - 1)))) :
    petDir D l c (0 : D.Idx l) i = 0 := by
  rw [petDir]
  refine dir_zero_of_one_le D l c (l - 1) (by omega) _ _ (fun k s => ?_)
  simp [IdxDatum.pad]

/-! ## The `a = 0` fibre of `linFamAvg` -/

/-- The value of the `a = 0` fibre of `linFamAvg`: with the balanced Boolean family `b` every
direction vanishes, the `y`-sum contributes the factor `M` (cancelling the `M` of the normalisation
`(NM)⁻¹`), and the remaining product times the outer `f x` is the nonnegative real `‖f x‖^{2t}`. -/
lemma linFib_zero_value {l : ℕ} (D : IdxDatum) (c : ℤ) (N M : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool) (t : ℕ)
    (hm : Fintype.card (D.I (l - 1)) = 2 * t - 1)
    (hb : (Finset.univ.filter (fun i => b i = false)).card = t - 1)
    (ht : 1 ≤ t) (hl : 2 ≤ l) (hN : 0 < N) (hM : 0 < M) (hfs : SupportIn f N) :
    linFib D l c N M f b (fun _ _ => 0) (0 : D.Idx l)
      = (N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t) := by
  classical
  have htrue := filter_true_card_eq b hm hb
  have hcount : ∀ x : ℤ, (∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f x) else f x)) = (f x) ^ (t - 1) * (star (f x)) ^ t := by
    intro x
    have hfil : (Finset.univ.filter (fun i : Fin (Fintype.card (D.I (l - 1))) =>
        ¬ (b i = false))) = Finset.univ.filter (fun i => b i = true) := by
      refine Finset.filter_congr (fun i _ => ?_)
      cases b i <;> simp
    calc (∏ i : Fin (Fintype.card (D.I (l - 1))), (if b i then star (f x) else f x))
        = ∏ i : Fin (Fintype.card (D.I (l - 1))),
            (if (b i = false) then f x else star (f x)) :=
          Finset.prod_congr rfl (fun i _ => by cases b i <;> simp)
      _ = (∏ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card (D.I (l - 1))) => b i = false),
              f x)
            * (∏ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card (D.I (l - 1))) =>
                ¬ (b i = false)), star (f x)) :=
          Finset.prod_ite (fun _ => f x) (fun _ => star (f x))
      _ = (f x) ^ (t - 1) * (star (f x)) ^ t := by
          rw [Finset.prod_const, Finset.prod_const, hb, hfil, htrue]
  have hP : ∀ x : ℤ, f x * (∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f x) else f x)) = (↑(‖f x‖ ^ (2 * t)) : ℂ) := by
    intro x
    rw [hcount x]
    have ht1 : (t - 1) + 1 = t := by omega
    calc f x * ((f x) ^ (t - 1) * (star (f x)) ^ t)
        = (f x * (f x) ^ (t - 1)) * (star (f x)) ^ t := by ring
      _ = (f x) ^ ((t - 1) + 1) * (star (f x)) ^ t := by rw [pow_succ']
      _ = (f x) ^ t * (star (f x)) ^ t := by rw [ht1]
      _ = (f x * star (f x)) ^ t := by rw [mul_pow]
      _ = (↑(Complex.normSq (f x)) : ℂ) ^ t := by
          have hcc : f x * star (f x) = (↑(Complex.normSq (f x)) : ℂ) := by
            simpa only [Complex.star_def] using Complex.mul_conj (f x)
          rw [hcc]
      _ = ↑((Complex.normSq (f x)) ^ t) := (Complex.ofReal_pow _ t).symm
      _ = ↑(‖f x‖ ^ (2 * t)) := by rw [Complex.normSq_eq_norm_sq, pow_mul]
  have hcard : (Finset.Icc 1 M).card = M := by rw [Nat.card_Icc]; omega
  have hinner : ∀ x : ℤ, (∑ y ∈ Finset.Icc 1 M,
        ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0)))
           else f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0))))
      = (M : ℂ) * (∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f x) else f x)) := by
    intro x
    have hconst : ∀ y ∈ Finset.Icc 1 M,
        (∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0)))
           else f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0))))
        = (∏ i : Fin (Fintype.card (D.I (l - 1))), (if b i then star (f x) else f x)) := by
      intro y _
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have harg : x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0) = x := by
        rw [petDir_zero_of_zero D l hl c i]; ring
      rw [harg]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hcard]
  have htsum : (∑' x : ℤ, f x * (∑ y ∈ Finset.Icc 1 M,
        ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0)))
           else f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0)))))
      = (M : ℂ) * (↑(∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) : ℂ) := by
    rw [tsum_congr (fun x => congrArg (fun z => f x * z) (hinner x))]
    have h1 : (∑' x : ℤ, f x * ((M : ℂ) * (∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f x) else f x))))
        = (M : ℂ) * (∑' x : ℤ, f x * (∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f x) else f x))) := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun x => by ring)
    rw [h1]
    congr 1
    rw [tsum_eq_sum (s := symIcc N) (fun x hx => by
      simp [hfs x (petCorner_natAbs_lt_of_not_mem_symIcc hx)])]
    rw [Finset.sum_congr rfl (fun x _ => hP x)]
    exact (Complex.ofReal_sum (s := symIcc N) (fun x => ‖f x‖ ^ (2 * t))).symm
  have hstep : linFib D l c N M f b (fun _ _ => 0) (0 : D.Idx l)
      = ‖((N : ℂ) * (M : ℂ))⁻¹ * (∑' x : ℤ, f x * (∑ y ∈ Finset.Icc 1 M,
          ∏ i : Fin (Fintype.card (D.I (l - 1))),
            (if b i then star (f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0)))
             else f (x + (petDir D l c (0 : D.Idx l) i * (y : ℤ) + 0)))))‖ := rfl
  rw [hstep, htsum]
  have hMne : (M : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hNM : ((N : ℂ) * (M : ℂ))⁻¹ * ((M : ℂ) * (↑(∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) : ℂ))
      = ((N : ℂ))⁻¹ * (↑(∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) : ℂ) := by
    field_simp
  rw [hNM, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun x _ => by positivity))]

/-- The `a = 0` term of the box average: the average of the fibres dominates any single fibre, and
the fibre at the zero parameter is `N⁻¹ ∑_{x∈symIcc N} ‖f x‖^{2t}`. -/
theorem petCornerZero_zeroTerm {l : ℕ} (D : IdxDatum) (c : ℤ) (N M H : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool) (t : ℕ)
    (hm : Fintype.card (D.I (l - 1)) = 2 * t - 1)
    (hb : (Finset.univ.filter (fun i => b i = false)).card = t - 1)
    (ht : 1 ≤ t) (hl : 2 ≤ l) (hN : 0 < N) (hM : 0 < M) (hfs : SupportIn f N) :
    ((D.parBox l H).card : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
      ≤ linFamAvg D l c N M H f b (fun _ _ => 0) := by
  classical
  have h0mem : (0 : D.Idx l) ∈ D.parBox l H := by
    rw [IdxDatum.mem_parBox]
    intro j s
    exact ⟨by simp, by simp⟩
  have hle : (N : ℝ)⁻¹ * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
      ≤ ∑ a ∈ D.parBox l H, linFib D l c N M f b (fun _ _ => 0) a := by
    calc (N : ℝ)⁻¹ * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
        = linFib D l c N M f b (fun _ _ => 0) (0 : D.Idx l) :=
          (linFib_zero_value D c N M f b t hm hb ht hl hN hM hfs).symm
      _ ≤ ∑ a ∈ D.parBox l H, linFib D l c N M f b (fun _ _ => 0) a :=
          Finset.single_le_sum (fun a _ => by simp only [linFib]; exact norm_nonneg _) h0mem
  rw [linFamAvg_eq]
  exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The arithmetic of the corner: the power-mean inequality `l1_pow_lower`, combined with the
`a = 0` lower bound, converts `γ N ≤ ∑_{x∈symIcc N} ‖f x‖` into the target's constant times
`linFamAvg`. -/
theorem petCornerZero_arith {l : ℕ} (D : IdxDatum) (c : ℤ) (N M H Kc : ℕ) (f : ℤ → ℂ)
    (t : ℕ) (γ : ℝ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (hH : H ≤ Kc) (hγ0 : 0 < γ)
    (hL1 : γ * (N : ℝ) ≤ ∑ x ∈ symIcc N, ‖f x‖)
    (hzero : ((D.parBox l H).card : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
      ≤ linFamAvg D l c N M H f b (fun _ _ => 0)) :
    γ ^ (2 * t) ≤
      ((((2 * Kc + 1 : ℕ) : ℝ) ^ (∑ j : Fin l, Fintype.card (D.S j))) * 3 ^ (2 * t - 1)) *
        linFamAvg D l c N M H f b (fun _ _ => 0) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h2t : 1 ≤ 2 * t := by omega
  have hS2nn : (0 : ℝ) ≤ ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t) :=
    Finset.sum_nonneg (fun x _ => by positivity)
  have hLnn : (0 : ℝ) ≤ linFamAvg D l c N M H f b (fun _ _ => 0) := by
    rw [linFamAvg_eq]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun a _ => by simp only [linFib]; exact norm_nonneg _))
  -- Step A: the power-mean inequality, and the `γ N` hypothesis.
  have hholder : (∑ x ∈ symIcc N, ‖f x‖) ^ (2 * t)
      ≤ (((2 * N + 1 : ℕ) : ℝ) ^ (2 * t - 1)) * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) :=
    l1_pow_lower f N t (by omega) ht
  have h1 : (γ * (N : ℝ)) ^ (2 * t) ≤ (∑ x ∈ symIcc N, ‖f x‖) ^ (2 * t) :=
    pow_le_pow_left₀ (by positivity) hL1 (2 * t)
  -- Step B: `2N + 1 ≤ 3N`.
  have h2N : (((2 * N + 1 : ℕ) : ℝ)) ≤ 3 * (N : ℝ) := by
    have h : (((2 * N + 1 : ℕ) : ℝ)) = 2 * (N : ℝ) + 1 := by push_cast; ring
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [h]; linarith
  have h3 : (((2 * N + 1 : ℕ) : ℝ) ^ (2 * t - 1)) * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
      ≤ (3 ^ (2 * t - 1) * (N : ℝ) ^ (2 * t - 1)) * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) := by
    have hbase : (((2 * N + 1 : ℕ) : ℝ)) ^ (2 * t - 1) ≤ (3 * (N : ℝ)) ^ (2 * t - 1) :=
      pow_le_pow_left₀ (by positivity) h2N (2 * t - 1)
    rw [mul_pow] at hbase
    exact mul_le_mul_of_nonneg_right hbase hS2nn
  -- Step C: cancel `N^{2t}`.
  have h5 : γ ^ (2 * t) * (N : ℝ) ^ (2 * t)
      ≤ 3 ^ (2 * t - 1) * (N : ℝ) ^ (2 * t - 1) * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) := by
    have h2 : (γ * (N : ℝ)) ^ (2 * t)
        ≤ (((2 * N + 1 : ℕ) : ℝ) ^ (2 * t - 1)) * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) :=
      le_trans h1 hholder
    have h4 := le_trans h2 h3
    rwa [mul_pow] at h4
  have hcancel : γ ^ (2 * t) * (N : ℝ)
      ≤ 3 ^ (2 * t - 1) * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) := by
    have hDpos : (0 : ℝ) < (N : ℝ) ^ (2 * t - 1) := pow_pos hNpos _
    have hsplit : (N : ℝ) ^ (2 * t) = (N : ℝ) ^ (2 * t - 1) * (N : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel h2t]
    rw [hsplit] at h5
    nlinarith [h5, hDpos, hNpos]
  have hgamma : γ ^ (2 * t) ≤ 3 ^ (2 * t - 1) * ((N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) := by
    have hEq : 3 ^ (2 * t - 1) * ((N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
        = (3 ^ (2 * t - 1) * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) * (N : ℝ)⁻¹ := by ring
    rw [hEq, le_mul_inv_iff₀ hNpos]
    exact hcancel
  -- Step D: the `a = 0` bound and the bound `H ≤ Kc`.
  have hpar : ((D.parBox l H).card : ℝ)
      = (((2 * H + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)) := by
    rw [parBox_card]; push_cast; ring
  have hpc : (0 : ℝ) < (((2 * H + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)) := by
    positivity
  have hz2 : (N : ℝ)⁻¹ * (∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
      ≤ (((2 * H + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)) *
          linFamAvg D l c N M H f b (fun _ _ => 0) := by
    have h1' : ((((2 * H + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)))⁻¹
        * ((N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t))
        ≤ linFamAvg D l c N M H f b (fun _ _ => 0) := by
      rw [← hpar]; exact hzero
    have h2' := mul_le_mul_of_nonneg_left h1' (le_of_lt hpc)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpc), one_mul] at h2'
  have hHK : (((2 * H + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j))
      ≤ (((2 * Kc + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)) := by
    have hle : (((2 * H + 1 : ℕ) : ℝ)) ≤ (((2 * Kc + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show 2 * H + 1 ≤ 2 * Kc + 1 by omega)
    exact pow_le_pow_left₀ (by positivity) hle _
  calc γ ^ (2 * t) ≤ 3 ^ (2 * t - 1) * ((N : ℝ)⁻¹ * ∑ x ∈ symIcc N, ‖f x‖ ^ (2 * t)) := hgamma
    _ ≤ 3 ^ (2 * t - 1) * ((((2 * H + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)) *
          linFamAvg D l c N M H f b (fun _ _ => 0)) :=
        mul_le_mul_of_nonneg_left hz2 (by positivity)
    _ ≤ 3 ^ (2 * t - 1) * ((((2 * Kc + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)) *
          linFamAvg D l c N M H f b (fun _ _ => 0)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hHK hLnn) (by positivity)
    _ = ((((2 * Kc + 1 : ℕ) : ℝ)) ^ (∑ j : Fin l, Fintype.card (D.S j)) * 3 ^ (2 * t - 1)) *
          linFamAvg D l c N M H f b (fun _ _ => 0) := by
        ring

end

/-- **The corner of the PET chapter.**  When the window `H` is bounded by the constant `Kc`, the
average `linFamAvg` is bounded below by `γ^{2t}` up to an explicit constant -- the constant
`(2Kc+1)^{Σ_j |S j|} 3^{2t-1}` of `NOTES_petChapter5_session13.md` §B. -/
theorem petCornerZero {l : ℕ} (D : IdxDatum) (c : ℤ) (N M H Kc : ℕ) (f : ℤ → ℂ)
    (t : ℕ) (γ : ℝ)
    (hm : Fintype.card (D.I (l - 1)) = 2 * t - 1) (ht : 1 ≤ t) (hl : 2 ≤ l)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hH : H ≤ Kc) (hfs : SupportIn f N) (hγ0 : 0 < γ)
    (hL1 : γ * (N : ℝ) ≤ ∑ x ∈ symIcc N, ‖f x‖) :
    ∃ b : Fin (Fintype.card (D.I (l - 1))) → Bool,
      (Finset.univ.filter (fun i => b i = false)).card = t - 1 ∧
      γ ^ (2 * t) ≤
        ((((2 * Kc + 1 : ℕ) : ℝ) ^ (∑ j : Fin l, Fintype.card (D.S j))) * 3 ^ (2 * t - 1)) *
          linFamAvg D l c N M H f b (fun _ _ => 0) := by
  obtain ⟨b, hb, -⟩ := exists_balanced_bool (Fintype.card (D.I (l - 1))) t hm ht
  exact ⟨b, hb,
    petCornerZero_arith D c N M H Kc f t γ b hN ht hH hγ0 hL1
      (petCornerZero_zeroTerm D c N M H f b t hm hb ht hl (by omega) (by omega) hfs)⟩

end Work.Peluse.UControl
