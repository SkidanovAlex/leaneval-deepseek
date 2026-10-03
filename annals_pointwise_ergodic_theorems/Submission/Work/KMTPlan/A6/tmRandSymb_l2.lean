import Mathlib
import Submission.Work.KMTPlan.A6.lacunaryLevel
import Submission.Work.KMTPlan.A6.lowSmallSet_eq_Icc
import Submission.Work.KMTPlan.A6.kmtEta_lipschitz
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Work.KMTPlan.A6.narrow_of_index
import Submission.Work.KMTPlan.A6.L_le_of_threshold_fail
import Submission.Work.KMTAreas.A7.lacModDiffDefs
import Submission.Work.KMTAreas.A7.varphiNt_bounds

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTContract Work.Analysis.EndVar
open Work.KMTAreas.A7

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

-- ============================================================================
-- Part 1: the pointwise supremum bound for the randomised symbol
-- ============================================================================

lemma diff_if_le {act : ℕ → Prop} [DecidablePred act] (V : ℕ → ℂ) {C : ℝ}
    (hV : ∀ m : ℕ, ‖V m‖ ≤ C) (m : ℕ) :
    ‖(if act m then V m else 0) - (if act (m+1) then V (m+1) else 0)‖
      ≤ ‖V (m+1) - V m‖ + (if (act m ↔ act (m+1)) then (0:ℝ) else C) := by
  by_cases h1 : act m <;> by_cases h2 : act (m+1)
  · simp only [h1, h2, if_true, iff_self]
    rw [norm_sub_rev]
    linarith [norm_nonneg (V (m+1) - V m)]
  · simp only [h1, h2, if_true, if_false, not_true_eq_false, iff_false]
    rw [sub_zero]
    have := hV m
    linarith [norm_nonneg (V (m+1) - V m)]
  · simp only [h1, h2, if_true, if_false, not_false_eq_true, iff_true]
    rw [zero_sub, norm_neg]
    have := hV (m+1)
    linarith [norm_nonneg (V (m+1) - V m)]
  · simp only [h1, h2, if_false, if_true]
    rw [sub_zero, norm_zero]
    have : (0:ℝ) ≤ C := le_trans (norm_nonneg (V 0)) (hV 0)
    linarith [norm_nonneg (V (m+1) - V m)]

lemma act_boundary_card {c e K : ℕ} (act : ℕ → Prop) [DecidablePred act]
    (hact : ∀ m : ℕ, act m ↔ (m ≠ 0 ∧ c ≤ m ∧ m ≤ e)) :
    ((Finset.range K).filter (fun m => ¬ (act m ↔ act (m+1)))).card ≤ 3 := by
  have hsub : (Finset.range K).filter (fun m => ¬ (act m ↔ act (m+1))) ⊆ ({0, c-1, e} : Finset ℕ) := by
    intro m hm
    obtain ⟨-, hb⟩ := Finset.mem_filter.mp hm
    by_cases h1 : act m
    · obtain ⟨-, hcm, hme⟩ := (hact m).mp h1
      have h2 : ¬ act (m+1) := fun hc => hb ⟨fun _ => hc, fun _ => h1⟩
      have hC : ¬ (m + 1 ≤ e) := fun h => h2 ((hact (m+1)).mpr ⟨by omega, by omega, h⟩)
      have hme' : m = e := by omega
      subst hme'
      simp
    · have h2 : act (m+1) := by
        by_contra hc
        exact hb ⟨fun h => absurd h h1, fun h => absurd h hc⟩
      obtain ⟨-, hcm, hme⟩ := (hact (m+1)).mp h2
      have h1' : ¬ (m ≠ 0 ∧ c ≤ m ∧ m ≤ e) := fun h => h1 ((hact m).mpr h)
      have hm : m = 0 ∨ m < c := by
        by_cases h : m = 0
        · exact Or.inl h
        · refine Or.inr ?_
          by_contra hc
          push_neg at hc
          exact h1' ⟨h, hc, by omega⟩
      have hme' : m = c - 1 := by omega
      subst hme'
      simp
  calc ((Finset.range K).filter (fun m => ¬ (act m ↔ act (m+1)))).card
      ≤ ({0, c-1, e} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 3 := by
        have h1 : ({0, c-1, e} : Finset ℕ) = insert 0 (insert (c-1) ({e} : Finset ℕ)) := rfl
        rw [h1]
        have h2 := Finset.card_insert_le (0:ℕ) (insert (c-1) ({e} : Finset ℕ))
        have h3 := Finset.card_insert_le (c-1) ({e} : Finset ℕ)
        have h4 : ({e} : Finset ℕ).card = 1 := Finset.card_singleton e
        omega


open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTContract Work.Analysis.EndVar
open Work.KMTAreas.A7

lemma norm_varphiN_le_two (N k₁ : ℕ) (x : ℝ) : ‖varphiN N k₁ x‖ ≤ 2 := by
  by_cases hk : k₁ = 0
  · subst hk
    simp only [varphiN, if_true]
    exact le_trans (norm_kmtEta_le _) (by norm_num)
  · simp only [varphiN, if_neg hk]
    have h1 := norm_kmtEta_le ((2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ)) * x)
    have h2 := norm_kmtEta_le ((2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ) + 1) * x)
    calc ‖kmtEta _ - kmtEta _‖ ≤ ‖kmtEta _‖ + ‖kmtEta _‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num

lemma norm_varphiNt_le_two (N k₁ : ℕ) (t x : ℝ) : ‖varphiNt N k₁ t x‖ ≤ 2 := by
  have h1 : varphiNt N k₁ t x = varphiN N k₁ x * ee ((N : ℝ) * t * x) := rfl
  rw [h1, norm_mul, Work.KMTAreas.A7.norm_ee_eq_one, mul_one]
  exact norm_varphiN_le_two N k₁ x

lemma ee_sub_le (u v : ℝ) : ‖ee u - ee v‖ ≤ 2 * Real.pi * |u - v| := by
  have hmul : ee u = ee v * ee (u - v) := by
    simp only [ee, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : ee v * ee (u - v) - ee v = ee v * (ee (u - v) - 1) := by ring
  rw [hmul, h2, norm_mul, Work.KMTAreas.A7.norm_ee_eq_one, one_mul]
  exact Work.KMTAreas.A7.norm_ee_sub_one_le (u - v)

lemma varphiN_supp_annulus {N k₁ : ℕ} (hk₁ : 1 ≤ k₁) {x : ℝ}
    (h : varphiN N k₁ x ≠ 0) :
    1 / 4 < (2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ)) * |x| ∧
      (2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ)) * |x| < 1 := by
  have hk : k₁ ≠ 0 := by omega
  simp only [varphiN, if_neg hk] at h
  set a : ℝ := (2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ)) with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ) + 1) = (2 : ℝ) * a := by
    rw [ha, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one, mul_comm]
  have h2val : (2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ) + 1) * x = (2:ℝ) * (a * x) := by
    rw [h2]; ring
  constructor
  · by_contra hcon
    push_neg at hcon
    have hax : a * |x| ≤ 1 / 4 := hcon
    have h1 : kmtEta (a * x) = 1 := kmtEta_one (by
      rw [abs_mul, abs_of_pos hapos]; linarith)
    have h2' : kmtEta ((2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ) + 1) * x) = 1 := by
      rw [h2val]
      refine kmtEta_one ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_mul, abs_of_pos hapos]
      linarith
    refine h ?_
    rw [h1, h2']
    norm_num
  · by_contra hcon
    push_neg at hcon
    have h1 : kmtEta (a * x) = 0 := kmtEta_zero (by
      rw [abs_mul, abs_of_pos hapos]; exact hcon)
    have h2' : kmtEta ((2 : ℝ) ^ ((logN N : ℝ) - (k₁ : ℝ) + 1) * x) = 0 := by
      rw [h2val]
      refine kmtEta_zero ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_mul, abs_of_pos hapos]
      linarith
    exact h (by rw [h1, h2']; norm_num)

lemma nat_lt_two_mul_two_pow_logN (N : ℕ) :
    (N : ℝ) < 2 * (2 : ℝ) ^ (logN N : ℝ) := by
  have h1 : N < 2 ^ (Nat.log 2 (max N 2) + 1) :=
    lt_of_le_of_lt (le_max_left _ _)
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2))
  have h2 : ((2 ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) =
      2 * (2 : ℝ) ^ (logN N : ℝ) := by
    rw [logN]
    push_cast
    rw [pow_succ]
    push_cast
    rw [Real.rpow_natCast]
    ring
  have h3 : (N : ℝ) < ((2 ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  rwa [h2] at h3

/-- The level-window arithmetic: two `k₁`-annulus conditions of the same `x ≠ 0` put the two
`Log`-levels within `1` of each other. -/
lemma level_close {k₁ : ℕ} {x : ℝ} (hx : 0 < |x|) {N₁ N₂ : ℕ}
    (h1 : (2 : ℝ) ^ ((logN N₁ : ℝ) - (k₁ : ℝ)) * |x| < 1)
    (h1' : 1 / 4 < (2 : ℝ) ^ ((logN N₁ : ℝ) - (k₁ : ℝ)) * |x|)
    (h2 : (2 : ℝ) ^ ((logN N₂ : ℝ) - (k₁ : ℝ)) * |x| < 1)
    (h2' : 1 / 4 < (2 : ℝ) ^ ((logN N₂ : ℝ) - (k₁ : ℝ)) * |x|) :
    |(logN N₁ - logN N₂ : ℤ)| ≤ 1 := by
  have hp1 : 0 < (2 : ℝ) ^ ((logN N₁ : ℝ) - (k₁ : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hp2 : 0 < (2 : ℝ) ^ ((logN N₂ : ℝ) - (k₁ : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  set t : ℝ := (logN N₁ : ℝ) - (logN N₂ : ℝ) with ht
  have hrpow : (2 : ℝ) ^ t =
      ((2 : ℝ) ^ ((logN N₁ : ℝ) - (k₁ : ℝ)) * |x|) /
        ((2 : ℝ) ^ ((logN N₂ : ℝ) - (k₁ : ℝ)) * |x|) := by
    rw [mul_div_mul_right _ _ (ne_of_gt hx), ← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
    congr 1
    rw [ht]; ring
  have hlow : (1 / 4 : ℝ) < (2 : ℝ) ^ t := by
    rw [hrpow]
    rw [lt_div_iff₀ (mul_pos hp2 hx)]
    nlinarith [h1', h2, hp2, hx]
  have hhigh : (2 : ℝ) ^ t < 4 := by
    rw [hrpow]
    rw [div_lt_iff₀ (mul_pos hp2 hx)]
    nlinarith [h1, h2', hp2, hx]
  have hg2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  have hgm2 : (2 : ℝ) ^ (-2 : ℝ) = (1 / 4 : ℝ) := by norm_num
  have hlt : t < 2 :=
    (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp (by rw [hg2]; exact hhigh)
  have hgt : (-2 : ℝ) < t :=
    (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp (by rw [hgm2]; exact hlow)
  have htcast : t = ((logN N₁ - logN N₂ : ℤ) : ℝ) := by
    rw [ht]; push_cast; ring
  have h2' : (-2 : ℝ) < ((logN N₁ - logN N₂ : ℤ) : ℝ) := by rw [← htcast]; exact hgt
  have h2'' : ((logN N₁ - logN N₂ : ℤ) : ℝ) < 2 := by rw [← htcast]; exact hlt
  rw [abs_le]
  constructor
  · have : (-2 : ℤ) < (logN N₁ - logN N₂) := by exact_mod_cast h2'
    omega
  · have : (logN N₁ - logN N₂) < (2 : ℤ) := by exact_mod_cast h2''
    omega


theorem randSymb_sup_le_aux (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Λ : NNReal) (hΛ : 1 < Λ)
    (Lη : ℝ) (hLη : 0 < Lη)
    (hη : ∀ x y : ℝ, ‖kmtEta x - kmtEta y‖ ≤ Lη * |x - y|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        ∀ x : ℝ,
          ‖Work.KMTAreas.A7.randSymb
            (fun n ξ => if n = 0 then 0
              else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
                then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) ε K x‖ ≤ C := by
  obtain ⟨Mlev, hMlev⟩ := lacunaryLevel
  refine ⟨max 1 (max (24 * (Mlev Λ : ℝ) + 6) (Lη + 4 * Real.pi + 10)), ?_, ?_⟩
  · positivity
  · intro ρ a l₁ l₂ k₁ k₂ K t ε hLac ha1 hε ht x
    have ht1 : t ≤ 1 := ht.2
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have ha_mono : Monotone a := by
      intro i j hij
      induction hij with
      | refl => exact le_rfl
      | @step j hij ih =>
        have hpos : (0 : NNReal) < a j := lt_of_lt_of_le zero_lt_one (ha1 j)
        have hlt : a j < a (j + 1) := by
          have h := hLac j
          have h2 : (Λ : NNReal) * a j < a (j + 1) := (lt_div_iff₀ hpos).mp h
          exact lt_of_le_of_lt (le_mul_of_one_le_left hpos.le (le_of_lt hΛ)) h2
        exact le_trans ih hlt.le
    obtain ⟨c, e, hce⟩ := lowSmallSet_eq_Icc Λ hΛ ρ C₀ a l₁ l₂ k₁ k₂ hLac ha1
    set N : ℕ → ℕ := fun m => Nat.floor (a m)
    set Z : ℕ → ℝ := fun m => (2 : ℝ) ^ (logN (N m) : ℝ)
    set U : ℕ → ℂ := fun m => varphiNt (N m) k₁ t x
    have hNmono : Monotone N := fun i j hij => Nat.floor_mono (ha_mono hij)
    have hZmono : Monotone Z := fun i j hij => by
      have hmax : max (N i) 2 ≤ max (N j) 2 :=
        max_le (le_trans (hNmono hij) (le_max_left _ _)) (le_max_right _ _)
      have hlog : logN (N i) ≤ logN (N j) := by
        rw [logN, logN]
        exact_mod_cast Nat.log_mono_right hmax
      have hle : (logN (N i) : ℝ) ≤ (logN (N j) : ℝ) := by exact_mod_cast hlog
      exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr hle
    have hNlt : ∀ m, (N m : ℝ) < 2 * Z m := fun m => nat_lt_two_mul_two_pow_logN (N m)
    set act : ℕ → Prop := fun m => m ≠ 0 ∧ Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
    have hact : ∀ m, act m ↔ (m ≠ 0 ∧ c ≤ m ∧ m ≤ e) := by
      intro m
      simp only [act]
      rw [hce m]
    set fam : ℕ → ℝ → ℂ := fun n ξ => if n = 0 then 0
      else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
        then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0
    have hfamU : ∀ m, (if m = 0 then (0:ℂ)
        else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
          then Work.KMTAreas.A7.varphiNt (Nat.floor (a m)) k₁ t x else 0)
        = (if act m then U m else 0) := by
      intro m
      by_cases h0 : m = 0
      · subst h0
        rw [if_pos rfl]
        rw [if_neg (by simp : ¬ ((0:ℕ) ≠ 0 ∧ Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0))]
      · have hm0 : m ≠ 0 := h0
        by_cases hls : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
        · have h1 : (if m = 0 then (0:ℂ) else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
              then Work.KMTAreas.A7.varphiNt (Nat.floor (a m)) k₁ t x else 0)
              = Work.KMTAreas.A7.varphiNt (Nat.floor (a m)) k₁ t x := by
            rw [if_neg hm0, if_pos hls]
          have h2 : (if act m then U m else 0) = Work.KMTAreas.A7.varphiNt (Nat.floor (a m)) k₁ t x := by
            rw [if_pos (show act m from ⟨hm0, hls⟩)]
          rw [h1, h2]
        · have h1 : (if m = 0 then (0:ℂ) else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
              then Work.KMTAreas.A7.varphiNt (Nat.floor (a m)) k₁ t x else 0) = 0 := by
            rw [if_neg hm0, if_neg hls]
          have h2 : (if act m then U m else 0) = 0 := by
            rw [if_neg (show ¬ act m from fun h => hls h.2)]
          rw [h1, h2]

    -- the rewritten symbol
    have hrewrite : Work.KMTAreas.A7.randSymb
        (fun n ξ => if n = 0 then 0
          else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
            then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) ε K x
        = ∑ m ∈ Finset.range K, ε m * ((if act (m+1) then U (m+1) else 0)
            - (if act m then U m else 0)) := by
      rw [Work.KMTAreas.A7.randSymb]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hfamU (m+1), hfamU m]
    have hUbd : ∀ m, ‖U m‖ ≤ 2 := fun m => norm_varphiNt_le_two (N m) k₁ t x
    have hbdcard : ((Finset.range K).filter (fun m => ¬ (act m ↔ act (m+1)))).card ≤ 3 :=
      act_boundary_card act hact
    have hS2 : ∑ m ∈ Finset.range K, (if (act m ↔ act (m+1)) then (0:ℝ) else 2) ≤ 6 := by
      have h1 : ∑ m ∈ Finset.range K, (if (act m ↔ act (m+1)) then (0:ℝ) else 2)
          = ∑ m ∈ (Finset.range K).filter (fun m => ¬ (act m ↔ act (m+1))), 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        by_cases h : (act m ↔ act (m+1)) <;> simp [h]
      rw [h1, Finset.sum_const, nsmul_eq_mul]
      have : (((Finset.range K).filter (fun m => ¬ (act m ↔ act (m+1)))).card : ℝ) ≤ 3 := by
        exact_mod_cast hbdcard
      linarith
    have hmain : ‖Work.KMTAreas.A7.randSymb
        (fun n ξ => if n = 0 then 0
          else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
            then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) ε K x‖
        ≤ (∑ m ∈ Finset.range K, ‖U (m+1) - U m‖) + 6 := by
      rw [hrewrite]
      calc ‖∑ m ∈ Finset.range K, ε m * ((if act (m+1) then U (m+1) else 0)
            - (if act m then U m else 0))‖
          ≤ ∑ m ∈ Finset.range K, ‖ε m * ((if act (m+1) then U (m+1) else 0)
            - (if act m then U m else 0))‖ := norm_sum_le _ _
        _ ≤ ∑ m ∈ Finset.range K, ‖(if act (m+1) then U (m+1) else 0)
            - (if act m then U m else 0)‖ := by
            refine Finset.sum_le_sum (fun m hm => ?_)
            rw [norm_mul]
            exact le_trans (mul_le_mul_of_nonneg_right (hε m) (norm_nonneg _))
              (le_of_eq (one_mul _))
        _ ≤ ∑ m ∈ Finset.range K, (‖U (m+1) - U m‖
            + (if (act m ↔ act (m+1)) then (0:ℝ) else 2)) :=
            Finset.sum_le_sum (fun m hm => by
              rw [norm_sub_rev]
              exact diff_if_le U hUbd m)
        _ = (∑ m ∈ Finset.range K, ‖U (m+1) - U m‖)
            + ∑ m ∈ Finset.range K, (if (act m ↔ act (m+1)) then (0:ℝ) else 2) :=
            Finset.sum_add_distrib
        _ ≤ (∑ m ∈ Finset.range K, ‖U (m+1) - U m‖) + 6 := by linarith [hS2]
    rcases Nat.eq_zero_or_pos k₁ with hk | hk
    · -- the bottom height `k₁ = 0`
      subst hk
      have hUform : ∀ m, U m = kmtEta (Z m * x) * ee ((N m : ℝ) * t * x) := by
        intro m
        simp only [U, varphiNt, varphiN, if_true, N, Z]
      have hZnn : ∀ m, 0 ≤ Z m := fun m => Real.rpow_nonneg (by norm_num) _
      have hUzero : ∀ m, 1 ≤ Z m * |x| → U m = 0 := by
        intro m hm
        rw [hUform m, kmtEta_zero (by rw [abs_mul, abs_of_nonneg (hZnn m)]; exact hm), zero_mul]
      have hlip : ∀ m : ℕ, ‖U (m+1) - U m‖ ≤
          Lη * (Z (m+1) - Z m) * |x| + 2 * Real.pi * ((N (m+1) : ℝ) - N m) * t * |x| := by
        intro m
        have hZdiff : |Z (m+1) * x - Z m * x| = (Z (m+1) - Z m) * |x| := by
          rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hZmono (Nat.le_succ m)))]
        have hNle : (N m : ℝ) ≤ N (m+1) := by exact_mod_cast hNmono (Nat.le_succ m)
        have hNdiff : |(N (m+1) : ℝ) * t * x - (N m : ℝ) * t * x| =
            ((N (m+1) : ℝ) - N m) * t * |x| := by
          rw [← sub_mul, ← sub_mul, abs_mul,
            abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hNle) ht0)]
        have h1 := hη (Z (m+1) * x) (Z m * x)
        rw [hZdiff] at h1
        have h5 := ee_sub_le ((N (m+1) : ℝ) * t * x) ((N m : ℝ) * t * x)
        rw [hNdiff] at h5
        rw [hUform (m+1), hUform m]
        have halg : kmtEta (Z (m+1) * x) * ee ((N (m+1) : ℝ) * t * x)
              - kmtEta (Z m * x) * ee ((N m : ℝ) * t * x)
            = (kmtEta (Z (m+1) * x) - kmtEta (Z m * x)) * ee ((N (m+1) : ℝ) * t * x)
              + kmtEta (Z m * x) * (ee ((N (m+1) : ℝ) * t * x) - ee ((N m : ℝ) * t * x)) := by
          ring
        rw [halg]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, Work.KMTAreas.A7.norm_ee_eq_one, mul_one]
        have hA : ‖kmtEta (Z (m+1) * x) - kmtEta (Z m * x)‖ ≤ Lη * ((Z (m+1) - Z m) * |x|) := by
          rw [← hZdiff]; exact hη _ _
        have hC : ‖ee ((N (m+1) : ℝ) * t * x) - ee ((N m : ℝ) * t * x)‖ ≤
            2 * Real.pi * (((N (m+1) : ℝ) - N m) * t * |x|) := by
          rw [← hNdiff]; exact ee_sub_le _ _
        have hBC : ‖kmtEta (Z m * x)‖ *
            ‖ee ((N (m+1) : ℝ) * t * x) - ee ((N m : ℝ) * t * x)‖ ≤
            2 * Real.pi * (((N (m+1) : ℝ) - N m) * t * |x|) := by
          calc _ ≤ 1 * (2 * Real.pi * (((N (m+1) : ℝ) - N m) * t * |x|)) :=
                mul_le_mul (norm_kmtEta_le _) hC (norm_nonneg _) (by positivity)
            _ = _ := by ring
        rw [show Lη * (Z (m+1) - Z m) * |x| + 2 * Real.pi * ((N (m+1) : ℝ) - N m) * t * |x| =
            Lη * ((Z (m+1) - Z m) * |x|) + 2 * Real.pi * (((N (m+1) : ℝ) - N m) * t * |x|) by ring]
        linarith [hA, hBC]
      set A : Finset ℕ := (Finset.range K).filter (fun m => Z (m+1) * |x| < 1)
      have hsumZ : ∑ m ∈ A, (Z (m+1) - Z m) * |x| ≤ 1 := by
        by_cases hne : A.Nonempty
        · set M₀ := A.max' hne
          have hM₀A : M₀ ∈ A := Finset.max'_mem A hne
          have hM₀ub : ∀ m ∈ A, m ≤ M₀ := fun m hm => Finset.le_max' A m hm
          have hkey : Z (M₀ + 1) * |x| < 1 := (Finset.mem_filter.mp hM₀A).2
          have hsub : A ⊆ Finset.range (M₀ + 1) :=
            fun m hm => Finset.mem_range.mpr (Nat.lt_succ_of_le (hM₀ub m hm))
          calc ∑ m ∈ A, (Z (m+1) - Z m) * |x|
              ≤ ∑ m ∈ Finset.range (M₀+1), (Z (m+1) - Z m) * |x| := by
                refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm hnot => ?_)
                have : Z m ≤ Z (m+1) := hZmono (Nat.le_succ m)
                positivity
            _ = (Z (M₀+1) - Z 0) * |x| := by
                rw [← Finset.sum_mul, Finset.sum_range_sub (f := Z)]
            _ ≤ 1 := by
                have hZ0 : 0 ≤ Z 0 := by positivity
                nlinarith [hkey, abs_nonneg x, hZ0]
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
          norm_num
      have hsumN : ∑ m ∈ A, ((N (m+1) : ℝ) - N m) * |x| ≤ 2 := by
        by_cases hne : A.Nonempty
        · set M₀ := A.max' hne
          have hM₀A : M₀ ∈ A := Finset.max'_mem A hne
          have hM₀ub : ∀ m ∈ A, m ≤ M₀ := fun m hm => Finset.le_max' A m hm
          have hkey : Z (M₀ + 1) * |x| < 1 := (Finset.mem_filter.mp hM₀A).2
          have hsub : A ⊆ Finset.range (M₀ + 1) :=
            fun m hm => Finset.mem_range.mpr (Nat.lt_succ_of_le (hM₀ub m hm))
          have hcast : ∑ m ∈ Finset.range (M₀+1), ((N (m+1) : ℝ) - N m)
              = (N (M₀+1) : ℝ) - N 0 := by
            rw [Finset.sum_range_sub (f := fun m => (N m : ℝ))]
          calc ∑ m ∈ A, ((N (m+1) : ℝ) - N m) * |x|
              ≤ ∑ m ∈ Finset.range (M₀+1), ((N (m+1) : ℝ) - N m) * |x| := by
                refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm hnot => ?_)
                have : (N m : ℝ) ≤ N (m+1) := by exact_mod_cast hNmono (Nat.le_succ m)
                positivity
            _ = ((N (M₀+1) : ℝ) - N 0) * |x| := by rw [← Finset.sum_mul, hcast]
            _ ≤ 2 := by
                have h1 : (N (M₀+1) : ℝ) < 2 * Z (M₀+1) := hNlt _
                have h2 : (0:ℝ) ≤ (N 0 : ℝ) := by positivity
                have h3 : 0 ≤ |x| := abs_nonneg x
                nlinarith [hkey, h1, h2, h3]
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
          norm_num
      have hbd1 : ((Finset.range K).filter (fun m => Z m * |x| < 1 ∧ 1 ≤ Z (m+1) * |x|)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro m hm m' hm'
        obtain ⟨-, hm1, hm2⟩ := Finset.mem_filter.mp hm
        obtain ⟨-, hm1', hm2'⟩ := Finset.mem_filter.mp hm'
        by_contra hne2
        rcases lt_or_gt_of_ne hne2 with hlt | hlt
        · have h1 : Z (m+1) ≤ Z m' := hZmono (by omega)
          nlinarith [h1, hm1', abs_nonneg x, hm2, hZmono (Nat.le_succ m)]
        · have h1 : Z (m'+1) ≤ Z m := hZmono (by omega)
          nlinarith [h1, hm1, abs_nonneg x, hm2', hZmono (Nat.le_succ m')]
      have hS1 : ∑ m ∈ Finset.range K, ‖U (m+1) - U m‖ ≤ Lη + 4 * Real.pi + 4 := by
        have hsplit : ∑ m ∈ Finset.range K, ‖U (m+1) - U m‖
            ≤ ∑ m ∈ A, ‖U (m+1) - U m‖
              + ∑ m ∈ (Finset.range K).filter (fun m => m ∉ A), ‖U (m+1) - U m‖ := by
          rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range K) (p := fun m => m ∈ A)]
          have hAeq : (Finset.range K).filter (fun m => m ∈ A) = A := by
            refine Finset.ext (fun m => ?_)
            simp only [Finset.mem_filter]
            exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
          rw [hAeq]
        have hA : ∑ m ∈ A, ‖U (m+1) - U m‖ ≤ Lη + 4 * Real.pi := by
          calc ∑ m ∈ A, ‖U (m+1) - U m‖
              ≤ ∑ m ∈ A, (Lη * (Z (m+1) - Z m) * |x|
                  + 2 * Real.pi * ((N (m+1) : ℝ) - N m) * t * |x|) :=
                Finset.sum_le_sum (fun m hm => hlip m)
            _ = Lη * (∑ m ∈ A, (Z (m+1) - Z m) * |x|)
                + 2 * Real.pi * t * (∑ m ∈ A, ((N (m+1) : ℝ) - N m) * |x|) := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
                congr 1
                · exact Finset.sum_congr rfl (fun m hm => by ring)
                · exact Finset.sum_congr rfl (fun m hm => by ring)
            _ ≤ Lη * 1 + 2 * Real.pi * t * 2 := by
                have h1 : (0:ℝ) ≤ Lη := hLη.le
                have h2 : 0 ≤ 2 * Real.pi * t := by positivity
                nlinarith [hsumZ, hsumN, hLη, Real.pi_pos, ht0]
            _ ≤ Lη + 4 * Real.pi := by nlinarith [hLη, Real.pi_pos, ht1]
        have hB : ∑ m ∈ (Finset.range K).filter (fun m => m ∉ A), ‖U (m+1) - U m‖ ≤ 2 := by
          set Bd : Finset ℕ := (Finset.range K).filter (fun m => Z m * |x| < 1 ∧ 1 ≤ Z (m+1) * |x|)
          have hBd1 : Bd.card ≤ 1 := hbd1
          have heq : ∑ m ∈ (Finset.range K).filter (fun m => m ∉ A), ‖U (m+1) - U m‖
              = ∑ m ∈ ((Finset.range K).filter (fun m => m ∉ A)).filter (fun m => m ∈ Bd),
                  ‖U (m+1) - U m‖ := by
            refine (Finset.sum_subset ?_ ?_).symm
            · intro m hm; exact Finset.mem_of_mem_filter m hm
            · intro m hmB hnotin
              obtain ⟨hmr, hmA⟩ := Finset.mem_filter.mp hmB
              have hmA' : ¬ (Z (m+1) * |x| < 1) := fun h => hmA (Finset.mem_filter.mpr ⟨hmr, h⟩)
              push_neg at hmA'
              have hZm : 1 ≤ Z m * |x| := by
                by_contra hcon
                push_neg at hcon
                exact hnotin (Finset.mem_filter.mpr ⟨hmB, by
                  show m ∈ Bd
                  simp only [Bd, Finset.mem_filter]
                  exact ⟨hmr, hcon, hmA'⟩⟩)
              rw [hUzero m hZm, hUzero (m+1) (by
                have := hZmono (Nat.le_succ m)
                nlinarith [hZm, this, abs_nonneg x]), sub_zero, norm_zero]
          calc ∑ m ∈ (Finset.range K).filter (fun m => m ∉ A), ‖U (m+1) - U m‖
              = _ := heq
            _ ≤ ∑ m ∈ Bd, ‖U (m+1) - U m‖ :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (fun m hm => (Finset.mem_filter.mp hm).2) (fun m hm _ => norm_nonneg _)
            _ ≤ ∑ m ∈ Bd, 2 := by
                refine Finset.sum_le_sum (fun m hm => ?_)
                have hm2 : 1 ≤ Z (m+1) * |x| := by
                  have hmem := hm
                  simp only [Bd, Finset.mem_filter] at hmem
                  exact hmem.2.2
                rw [hUzero (m+1) hm2, zero_sub, norm_neg]
                exact hUbd m
            _ = 2 * (Bd.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
            _ ≤ 2 := by
                have hc : (Bd.card : ℝ) ≤ 1 := by exact_mod_cast hBd1
                linarith
        linarith [hsplit, hA, hB]
      have hC1 : Lη + 4 * Real.pi + 10 ≤ max 1 (max (24 * (Mlev Λ : ℝ) + 6) (Lη + 4 * Real.pi + 10)) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      linarith [hmain, hS1, hC1]
    · -- height `k₁ ≥ 1`
      have hk1 : 1 ≤ k₁ := hk
      have hUz : ∀ m, U m ≠ 0 → 1 / 4 < (2:ℝ) ^ ((logN (N m) : ℝ) - (k₁:ℝ)) * |x| ∧
          (2:ℝ) ^ ((logN (N m) : ℝ) - (k₁:ℝ)) * |x| < 1 := by
        intro m hm
        have hφ : varphiN (N m) k₁ x ≠ 0 := fun h0 => hm (by simp only [U, varphiNt, h0, zero_mul])
        exact varphiN_supp_annulus hk hφ
      have hcount : ((Finset.range (K+1)).filter (fun m => U m ≠ 0)).card ≤ 5 * Mlev Λ := by
        by_cases hne : ((Finset.range (K+1)).filter (fun m => U m ≠ 0)).Nonempty
        · obtain ⟨m₀, hm₀⟩ := hne
          have hm₀U : U m₀ ≠ 0 := (Finset.mem_filter.mp hm₀).2
          set j₀ : ℤ := logN (N m₀)
          have hsub : ((Finset.range (K+1)).filter (fun m => U m ≠ 0))
              ⊆ (Finset.Icc (j₀-2) (j₀+2)).biUnion (fun j =>
                  ((Finset.range (K+1)).filter (fun m => logN (N m) = j))) := by
            intro m hm
            have hmU : U m ≠ 0 := (Finset.mem_filter.mp hm).2
            have hx0' : x ≠ 0 := by
              intro hx0''
              apply hmU
              have hk0 : k₁ ≠ 0 := by omega
              have hz : varphiN (N m) k₁ 0 = 0 := by
                rw [varphiN, if_neg hk0]
                simp only [mul_zero, kmtEta_one (by norm_num : |(0:ℝ)| ≤ 1/2), sub_self]
              simp only [U, varphiNt, hx0'', mul_zero, hz, zero_mul]
            have hxpos : 0 < |x| := abs_pos.mpr hx0'
            have hlev := level_close (k₁ := k₁) hxpos (hUz m hmU).2 (hUz m hmU).1
              (hUz m₀ hm₀U).2 (hUz m₀ hm₀U).1
            refine Finset.mem_biUnion.mpr ⟨logN (N m), ?_, ?_⟩
            · simp only [Finset.mem_Icc]
              rw [abs_le] at hlev
              obtain ⟨h1, h2⟩ := hlev
              constructor <;> omega
            · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1, rfl⟩
          calc ((Finset.range (K+1)).filter (fun m => U m ≠ 0)).card
              ≤ ((Finset.Icc (j₀-2) (j₀+2)).biUnion (fun j =>
                  ((Finset.range (K+1)).filter (fun m => logN (N m) = j)))).card :=
                Finset.card_le_card hsub
            _ ≤ ∑ j ∈ Finset.Icc (j₀-2) (j₀+2),
                  ((Finset.range (K+1)).filter (fun m => logN (N m) = j)).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ j ∈ Finset.Icc (j₀-2) (j₀+2), Mlev Λ :=
                Finset.sum_le_sum (fun j hj => hMlev a Λ hΛ hLac ha1 j (Finset.range (K+1)))
            _ ≤ 5 * Mlev Λ := by
                have h5 : (Finset.Icc (j₀-2) (j₀+2)).card ≤ 5 := by
                  have h5' : ((j₀ + 2) + 1 - (j₀ - 2) : ℤ) = 5 := by ring
                  rw [Int.card_Icc, h5']
                  simp
                rw [Finset.sum_const, smul_eq_mul]
                exact Nat.mul_le_mul_right _ h5
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
          simp
      have hbdum : ∑ m ∈ Finset.range K, ‖U (m+1) - U m‖
          ≤ 4 * (((Finset.range (K+1)).filter (fun m => U m ≠ 0)).card : ℝ) := by
        have hstep : ∑ m ∈ Finset.range K, ‖U (m+1) - U m‖
            ≤ ∑ m ∈ Finset.range K, (‖U (m+1)‖ + ‖U m‖) :=
          Finset.sum_le_sum (fun m hm => norm_sub_le _ _)
        have hstep2 : ∑ m ∈ Finset.range K, (‖U (m+1)‖ + ‖U m‖)
            ≤ 2 * ∑ m ∈ Finset.range (K+1), ‖U m‖ := by
          have h1 : ∑ m ∈ Finset.range K, ‖U (m+1)‖ ≤ ∑ m ∈ Finset.range (K+1), ‖U m‖ := by
            rw [Finset.sum_range_succ']
            exact le_add_of_nonneg_right (norm_nonneg (U 0))
          have h2 : ∑ m ∈ Finset.range K, ‖U m‖ ≤ ∑ m ∈ Finset.range (K+1), ‖U m‖ := by
            rw [Finset.sum_range_succ]
            exact le_add_of_nonneg_right (norm_nonneg (U K))
          rw [Finset.sum_add_distrib]
          linarith
        have hstep3 : ∑ m ∈ Finset.range (K+1), ‖U m‖
            ≤ 2 * (((Finset.range (K+1)).filter (fun m => U m ≠ 0)).card : ℝ) := by
          calc ∑ m ∈ Finset.range (K+1), ‖U m‖
              ≤ ∑ m ∈ Finset.range (K+1), (if U m ≠ 0 then (2:ℝ) else 0) := by
                refine Finset.sum_le_sum (fun m hm => ?_)
                by_cases h : U m = 0
                · simp [h]
                · rw [if_pos h]; exact hUbd m
            _ = ∑ m ∈ (Finset.range (K+1)).filter (fun m => U m ≠ 0), 2 := by
                rw [Finset.sum_filter]
            _ = 2 * (((Finset.range (K+1)).filter (fun m => U m ≠ 0)).card : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        linarith [hstep, hstep2, hstep3]
      have hc : (24 * (Mlev Λ : ℝ) + 6) ≤ max 1 (max (24 * (Mlev Λ : ℝ) + 6) (Lη + 4 * Real.pi + 10)) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have h1 : 4 * (((Finset.range (K+1)).filter (fun m => U m ≠ 0)).card : ℝ)
          ≤ 24 * (Mlev Λ : ℝ) := by
        have h2 : (((Finset.range (K+1)).filter (fun m => U m ≠ 0)).card : ℝ) ≤ 5 * (Mlev Λ : ℝ) := by
          have : (((Finset.range (K+1)).filter (fun m => U m ≠ 0)).card : ℝ) ≤ ((5 * Mlev Λ : ℕ) : ℝ) := by
            exact_mod_cast hcount
          rw [Nat.cast_mul] at this
          exact this
        nlinarith
      linarith [hmain, hbdum, h1, hc]


-- ============================================================================
-- Part 2: the `l^2` bound for the exact-height multiplier with that symbol
-- ============================================================================

theorem supportedInArc_periodize' {k : ℤ} {phi : ℝ → ℂ}
    (hphi : ∀ x, phi x ≠ 0 → x ∈ realArc k) : SupportedInArc k (periodize phi) := by
  intro xi hxi
  obtain ⟨j, hj⟩ : ∃ j : ℤ, phi ((AddCircle.equivIco (1 : ℝ) 0 xi).val + j) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hxi ?_
    unfold periodize
    have h0 : (fun k : ℤ => phi ((AddCircle.equivIco (1 : ℝ) 0 xi).val + k))
        = fun _ : ℤ => (0 : ℂ) := funext fun k => hcon k
    rw [h0, tsum_zero]
  refine ⟨(AddCircle.equivIco (1 : ℝ) 0 xi).val + j, hphi _ hj, ?_⟩
  have hxc : ((AddCircle.equivIco (1 : ℝ) 0 xi).val : Circ) = xi := by simp
  have hjc : ((j : ℝ) : Circ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨j, by simp⟩
  rw [AddCircle.coe_add, hxc, hjc, add_zero]

theorem norm_periodize_le {phi : ℝ → ℂ} {R C : ℝ} (n : ℕ) (hRn : R ≤ (n : ℝ))
    (hphi0 : ∀ x, R < |x| → phi x = 0) (hC : ∀ x, ‖phi x‖ ≤ C) (xi : Circ) :
    ‖periodize phi xi‖ ≤ (2 * (n : ℝ) + 4) * C := by
  set s : Finset ℤ := Finset.Icc (-(n : ℤ) - 2) ((n : ℤ) + 1) with hs
  have hkey : periodize phi xi = ∑ k ∈ s, phi ((AddCircle.equivIco (1 : ℝ) 0 xi).val + k) := by
    unfold periodize
    refine tsum_eq_sum (fun k hk => ?_)
    have hle_1 : ¬ (-(n : ℤ) - 2 ≤ k ∧ k ≤ (n : ℤ) + 1) := by
      intro hcon
      exact hk (by rw [hs, Finset.mem_Icc]; exact hcon)
    have hx := (AddCircle.equivIco (1 : ℝ) 0 xi).prop
    rw [Set.mem_Ico] at hx
    obtain ⟨hx0, hx1⟩ := hx
    by_cases hge : (-(n : ℤ) - 2 ≤ k)
    · have hgt : (n : ℤ) + 1 < k := lt_of_not_ge (fun hle => hle_1 ⟨hge, hle⟩)
      have h2 : ((n : ℝ) + 1 < (k : ℝ)) := by exact_mod_cast hgt
      refine hphi0 _ ?_
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hlt : k < -(n : ℤ) - 2 := lt_of_not_ge hge
      have h2 : (-(k : ℝ)) ≥ (n : ℝ) + 3 := by
        have h1 : (-k : ℤ) ≥ (n : ℤ) + 3 := by omega
        exact_mod_cast h1
      refine hphi0 _ ?_
      have h3 : (AddCircle.equivIco (1 : ℝ) 0 xi).val + (k : ℝ) ≤ -((n : ℝ) + 2) := by linarith
      rw [abs_of_nonpos (by linarith)]
      linarith
  rw [hkey]
  have hcard : (s.card : ℝ) ≤ 2 * (n : ℝ) + 4 := by
    have hcard' : s.card = 2 * n + 4 := by
      rw [hs, Int.card_Icc]
      have hthis : (((n : ℤ) + 1) + 1 - (-(n : ℤ) - 2)) = ((2 * n + 4 : ℕ) : ℤ) := by
        push_cast; ring
      rw [hthis, Int.toNat_natCast]
    rw [hcard']
    push_cast
    linarith
  calc ‖∑ k ∈ s, phi ((AddCircle.equivIco (1 : ℝ) 0 xi).val + k)‖
      ≤ ∑ k ∈ s, ‖phi ((AddCircle.equivIco (1 : ℝ) 0 xi).val + k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ s, C := Finset.sum_le_sum (fun k _ => hC _)
    _ = (s.card : ℝ) * C := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (n : ℝ) + 4) * C := by
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
        exact mul_le_mul_of_nonneg_right hcard hC0

theorem exists_ne_zero_of_randSymb_ne_zero {phi : ℕ → ℝ → ℂ} {eps : ℕ → ℂ} {K : ℕ} {x : ℝ}
    (h : Work.KMTAreas.A7.randSymb phi eps K x ≠ 0) : ∃ n ≤ K, phi n x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  refine h ?_
  unfold Work.KMTAreas.A7.randSymb
  refine Finset.sum_eq_zero (fun n hn => ?_)
  have hnK : n < K := Finset.mem_range.mp hn
  have h1 : phi n x = 0 := hcon n (le_of_lt hnK)
  have h2 : phi (n + 1) x = 0 := hcon (n + 1) (by omega)
  simp [h1, h2]

theorem tmDiffFreqs_subset (rho : ℝ) (l : ℕ) :
    Work.KMTAreas.A7.diffFreqs rho l ⊆ iwArithFreqs rho l := by
  by_cases hl : l = 0
  · subst hl
    simp [Work.KMTAreas.A7.diffFreqs]
  · rw [Work.KMTAreas.A7.diffFreqs, if_neg hl]
    exact Finset.sdiff_subset

theorem nonAliasing_mono {k : ℤ} {A B : Finset Circ} (h : NonAliasing k A) (hBA : B ⊆ A) :
    NonAliasing k B := by
  intro al hal be hbe th hth th' hth' heq
  exact h al (hBA hal) be (hBA hbe) th hth th' hth' heq



theorem two_zpow_eq_rpow (k : ℕ) : (2 : ℝ) ^ (k : ℤ) = (2 : ℝ) ^ (k : ℝ) := by
  rw [zpow_natCast, Real.rpow_natCast]

theorem measurable_family {rho : ℝ} {C0 : ℕ} {a : ℕ → NNReal} {l1 l2 k1 k2 : ℕ} {t : ℝ}
    (m : ℕ) :
    Measurable (fun x : ℝ => if m = 0 then 0 else
      if Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 m
        then Work.KMTAreas.A7.varphiNt (Nat.floor (a m)) k1 t x else 0) := by
  by_cases h0 : m = 0
  · simp only [if_pos h0]; exact measurable_const
  · simp only [if_neg h0]
    by_cases hc : Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 m
    · simp only [if_pos hc]
      exact (Work.KMTAreas.A7.contDiff_varphiNt _ _ _).continuous.measurable
    · simp only [if_neg hc]; exact measurable_const

theorem support_of_family {rho : ℝ} {C0 : ℕ} {a : ℕ → NNReal} {l1 l2 k1 k2 n : ℕ} {t x : ℝ}
    (h : (if n = 0 then 0 else
      if Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 n
        then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k1 t x else 0) ≠ 0) :
    n ≠ 0 ∧ Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 n ∧
      Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k1 t x ≠ 0 := by
  by_cases h0 : n = 0
  · rw [if_pos h0] at h; exact absurd rfl h
  · rw [if_neg h0] at h
    by_cases hc : Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 n
    · rw [if_pos hc] at h; exact ⟨h0, hc, h⟩
    · rw [if_neg hc] at h; exact absurd rfl h

theorem tmRandSymb_l2_main (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (C0 : ℕ) (hC0 : 1 ≤ C0) :
    ∃ rho0 : Real, 0 < rho0 ∧ ∀ rho : Real, 0 < rho → rho ≤ rho0 → ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Lam : NNReal) (l1 l2 k1 k2 K : ℕ) (t : Real) (eps : ℕ → Complex)
        (f : ℤ → Complex),
        1 < Lam → PointwiseErgodicTheorems.Lacunary Lam a → (∀ n, 1 ≤ a n) →
        (∀ n, ‖eps n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : Real) 1 →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm rho l1
            (Work.KMTAreas.A7.randSymb
              (fun n ξ => if n = 0 then 0
                else if Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 n
                  then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k1 t ξ else 0) eps K) f)
          2 MeasureTheory.Measure.count
        ≤ (C Lam : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  refine ⟨min 1 (1 / (2 * (C0 : ℝ))), lt_min zero_lt_one (by positivity), ?_⟩
  intro rho hrho hrhorho0
  have hrho1 : rho ≤ 1 := le_trans hrhorho0 (min_le_left _ _)
  have hrhoC0 : rho * (C0 : ℝ) ≤ 1 / 2 := by
    have h := le_trans hrhorho0 (min_le_right _ _)
    have h2 : rho * (2 * (C0 : ℝ)) ≤ 1 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (C0 : ℝ))).mp h
    nlinarith
  obtain ⟨Crho, hCrhoP, hNA, _⟩ := hA1 rho hrho hrho1
  obtain ⟨L0, hL0⟩ := L_le_of_threshold_fail rho hrho C0 hC0 (max Crho 2) (le_trans (by norm_num : (1:ℝ) ≤ 2) (le_max_right _ _)) hrhoC0
  obtain ⟨Leta, hLetaP, hLeta⟩ := kmtEta_lipschitz
  obtain ⟨Cc, hCcP, hCc⟩ := iw_height_card_le (ρ := rho) hrho
  have hcrux : ∀ Lam : NNReal, 1 < Lam → ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal) (l1 l2 k1 k2 K : ℕ) (t : ℝ) (eps : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Lam a → (∀ n, 1 ≤ a n) → (∀ n, ‖eps n‖ ≤ 1) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ x : ℝ,
          ‖Work.KMTAreas.A7.randSymb
            (fun n ξ => if n = 0 then 0
              else if Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 n
                then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k1 t ξ else 0) eps K x‖ ≤ C :=
    fun Lam hLam => by
      obtain ⟨C, hC, hb⟩ := randSymb_sup_le_aux C0 hC0 Lam hLam Leta hLetaP hLeta
      exact ⟨C, hC, fun a l1 l2 k1 k2 K t eps hLac ha1 heps ht => hb rho a l1 l2 k1 k2 K t eps hLac ha1 heps ht⟩
  let cpsi : NNReal → ℝ := fun Lam => if h : 1 < Lam then Classical.choose (hcrux Lam h) else 1
  have hcpsiP : ∀ Lam : NNReal, 1 < Lam → 0 < cpsi Lam := by
    intro Lam hLam
    simp only [cpsi, dif_pos hLam]
    exact (Classical.choose_spec (hcrux Lam hLam)).1
  have hcpsiB : ∀ (Lam : NNReal) (hLam : 1 < Lam) (a : ℕ → NNReal) (l1 l2 k1 k2 K : ℕ)
      (t : ℝ) (eps : ℕ → ℂ),
      PointwiseErgodicTheorems.Lacunary Lam a → (∀ n, 1 ≤ a n) → (∀ n, ‖eps n‖ ≤ 1) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ x : ℝ,
        ‖Work.KMTAreas.A7.randSymb
          (fun n ξ => if n = 0 then 0
            else if Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 n
              then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k1 t ξ else 0) eps K x‖ ≤ cpsi Lam := by
    intro Lam hLam a l1 l2 k1 k2 K t eps hLac ha1 heps ht
    simp only [cpsi, dif_pos hLam]
    exact (Classical.choose_spec (hcrux Lam hLam)).2 a l1 l2 k1 k2 K t eps hLac ha1 heps ht
  let Kf : ℝ := max 1 (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (L0 : ℝ))) *
    (2 * ((2 ^ L0 : ℕ) : ℝ) + 4))
  have hKf1 : 1 ≤ Kf := le_max_left _ _
  refine ⟨fun Lam => Real.toNNReal (Kf * cpsi Lam + 1), ?_⟩
  intro a Lam l1 l2 k1 k2 K t eps f hLam hLac ha1 heps ht hf
  let psif : ℕ → ℝ → ℂ := fun n ξ => if n = 0 then 0
      else if Work.KMTPlan.A6.lowSmallSet rho C0 a l1 l2 k1 k2 n
        then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k1 t ξ else 0
  have hpsiran : ∀ x : ℝ, ‖Work.KMTAreas.A7.randSymb psif eps K x‖ ≤ cpsi Lam :=
    hcpsiB Lam hLam a l1 l2 k1 k2 K t eps hLac ha1 heps ht
  have hmeaspsif : ∀ m : ℕ, Measurable (psif m) := by
    intro m
    have := measurable_family (rho := rho) (C0 := C0) (a := a) (l1 := l1) (l2 := l2)
      (k1 := k1) (k2 := k2) (t := t) m
    simpa only [psif] using this
  have hmeas : Measurable (Work.KMTAreas.A7.randSymb psif eps K) := by
    unfold Work.KMTAreas.A7.randSymb
    refine Finset.measurable_sum _ (fun n hn => ?_)
    exact Measurable.const_mul (Measurable.sub (hmeaspsif (n+1)) (hmeaspsif n)) (eps n)
  -- the support of the random symbol: radius 2^{k1}
  have hsupp0 : ∀ x : ℝ, Work.KMTAreas.A7.randSymb psif eps K x ≠ 0 → x ∈ realArc (k1 : ℤ) := by
    intro x hx
    obtain ⟨n, hnK, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hx
    have hn' : psif n x ≠ 0 := hn
    have hfam := support_of_family (rho := rho) (C0 := C0) (a := a) (l1 := l1) (l2 := l2)
      (k1 := k1) (k2 := k2) (n := n) (t := t) (x := x) (by simpa only [psif] using hn')
    obtain ⟨-, -, hbump⟩ := hfam
    have hsup := Work.KMTAreas.A7.varphiNt_support_le_all k1 (Nat.floor (a n)) t x hbump
    have hlogN : (0 : ℝ) ≤ (logN (Nat.floor (a n)) : ℝ) := by
      exact_mod_cast Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n))
    have hmono : (2 : ℝ) ^ ((k1 : ℝ) - (logN (Nat.floor (a n)) : ℝ)) ≤ (2 : ℝ) ^ (k1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : |x| ≤ (2 : ℝ) ^ (k1 : ℝ) := le_trans hsup hmono
    have heq : (2 : ℝ) ^ (k1 : ℤ) = (2 : ℝ) ^ (k1 : ℝ) := by
      rw [zpow_natCast, Real.rpow_natCast]
    rw [realArc, Set.mem_Icc, heq]
    exact abs_le.mp h3
  -- the symbol bound
  have hsym : ∀ ξ : Circ,
      ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs rho l1)
        (periodize (Work.KMTAreas.A7.randSymb psif eps K)) ξ‖ ≤ Kf * cpsi Lam + 1 := by
    intro ξ
    by_cases hthr : (k1 : ℝ) + (max Crho 2) * (2 : ℝ) ^ (rho * (l1 : ℝ)) + 2 ≤
        (2 : ℝ) ^ (((Work.KMTPlan.A6.lcL l1 l2 k1 k2 : ℕ) : ℝ) / (C0 : ℝ) - 2)
    · set k : ℤ := ⌊-(max Crho 2) * (2 : ℝ) ^ (rho * (l1 : ℝ))⌋
      have hsupp : ∀ x : ℝ, Work.KMTAreas.A7.randSymb psif eps K x ≠ 0 → x ∈ realArc k := by
        intro x hx
        obtain ⟨n, hnK, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hx
        have hn' : psif n x ≠ 0 := hn
        have hfam := support_of_family (rho := rho) (C0 := C0) (a := a) (l1 := l1) (l2 := l2)
          (k1 := k1) (k2 := k2) (n := n) (t := t) (x := x) (by simpa only [psif] using hn')
        obtain ⟨-, hls, hbump⟩ := hfam
        have hindex := (Work.KMTPlan.A6.lowSmallSet_iff.mp hls).1
        have hle := narrow_of_index rho (max Crho 2) C0 hC0 hindex hthr x hbump
        rw [realArc, Set.mem_Icc]
        exact abs_le.mp hle
      have hgood : GoodMajorArcs rho (max Crho 2) l1 k := by
        show (k : ℝ) ≤ -(max Crho 2) * (2 : ℝ) ^ (rho * (l1 : ℝ))
        exact Int.floor_le _
      have hgood' : GoodMajorArcs rho Crho l1 k := by
        have h1 : Crho * (2 : ℝ) ^ (rho * (l1 : ℝ)) ≤
            (max Crho 2) * (2 : ℝ) ^ (rho * (l1 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hg : (k : ℝ) ≤ -(max Crho 2) * (2 : ℝ) ^ (rho * (l1 : ℝ)) := hgood
        show (k : ℝ) ≤ -Crho * (2 : ℝ) ^ (rho * (l1 : ℝ))
        linarith [hg, h1]
      have hNA' : NonAliasing k (Work.KMTAreas.A7.diffFreqs rho l1) :=
        nonAliasing_mono (hNA l1 k hgood') (tmDiffFreqs_subset rho l1)
      have h2 : (2 : ℝ) ^ (k + 1) < 1 :=
        Work.Analysis.IWMultiplier.two_pow_succ_lt_one_of_goodMajorArcs hgood (le_max_right _ _) hrho
      have hper : ∀ ξ : Circ, ‖periodize (Work.KMTAreas.A7.randSymb psif eps K) ξ‖ ≤ cpsi Lam :=
        fun ξ => Work.Analysis.IWMultiplier.periodize_norm_le h2 hsupp
          (fun x => hpsiran x) ξ
      have hSIA : SupportedInArc k (periodize (Work.KMTAreas.A7.randSymb psif eps K)) :=
        supportedInArc_periodize' hsupp
      have hb := norm_iwSymbolSet_le_of_nonAliasing hNA' hSIA (le_of_lt (hcpsiP Lam hLam)) hper ξ
      have hK : cpsi Lam ≤ Kf * cpsi Lam + 1 := by
        nlinarith [hKf1, hcpsiP Lam hLam]
      calc ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs rho l1)
              (periodize (Work.KMTAreas.A7.randSymb psif eps K)) ξ‖ ≤ cpsi Lam := hb
        _ ≤ Kf * cpsi Lam + 1 := hK
    · have hk1L : k1 ≤ Work.KMTPlan.A6.lcL l1 l2 k1 k2 := by
        rw [Work.KMTPlan.A6.lcL]; omega
      have hl1L : l1 ≤ Work.KMTPlan.A6.lcL l1 l2 k1 k2 := by
        rw [Work.KMTPlan.A6.lcL]; omega
      have hL : Work.KMTPlan.A6.lcL l1 l2 k1 k2 ≤ L0 :=
        hL0 (Work.KMTPlan.A6.lcL l1 l2 k1 k2) k1 l1 hk1L hl1L hthr
      have hk1 : k1 ≤ L0 := le_trans hk1L hL
      have hl1 : l1 ≤ L0 := le_trans hl1L hL
      have hper : ∀ ξ : Circ, ‖periodize (Work.KMTAreas.A7.randSymb psif eps K) ξ‖
          ≤ (2 * ((2 ^ L0 : ℕ) : ℝ) + 4) * cpsi Lam := by
        intro ξ
        refine norm_periodize_le (phi := Work.KMTAreas.A7.randSymb psif eps K) (R := (2 : ℝ) ^ (k1 : ℤ))
          (C := cpsi Lam) (2 ^ L0) ?_ ?_ (fun x => hpsiran x) ξ
        · rw [zpow_natCast]
          calc (2 : ℝ) ^ k1 ≤ (2 : ℝ) ^ L0 := pow_le_pow_right₀ (by norm_num) hk1
            _ = ((2 ^ L0 : ℕ) : ℝ) := by push_cast; ring
        · intro x hx
          by_contra hne
          have hmem := hsupp0 x hne
          rw [realArc, Set.mem_Icc] at hmem
          rw [two_zpow_eq_rpow k1] at hmem
          have habs : |x| ≤ (2 : ℝ) ^ (k1 : ℝ) := abs_le.mpr hmem
          rw [two_zpow_eq_rpow k1] at hx
          linarith
      have hcard : ((Work.KMTAreas.A7.diffFreqs rho l1).card : ℝ) ≤
          Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (L0 : ℝ))) := by
        have hsub : (Work.KMTAreas.A7.diffFreqs rho l1).card ≤ (iwArithFreqs rho l1).card :=
          Finset.card_le_card (tmDiffFreqs_subset rho l1)
        have h1 : ((iwArithFreqs rho l1).card : ℝ) ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (l1 : ℝ))) :=
          hCc l1
        have h2 : (2 : ℝ) ^ (rho * (l1 : ℝ)) ≤ (2 : ℝ) ^ (rho * (L0 : ℝ)) :=
          (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mpr (by
            have : (l1 : ℝ) ≤ (L0 : ℝ) := by exact_mod_cast hl1
            nlinarith [hrho.le])
        have h3 : (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (l1 : ℝ))) ≤
            (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (L0 : ℝ))) :=
          (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mpr h2
        calc ((Work.KMTAreas.A7.diffFreqs rho l1).card : ℝ)
            ≤ ((iwArithFreqs rho l1).card : ℝ) := by exact_mod_cast hsub
          _ ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (l1 : ℝ))) := h1
          _ ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (L0 : ℝ))) :=
              mul_le_mul_of_nonneg_left h3 hCcP.le
      have hb := norm_iwSymbolSet_le (Work.KMTAreas.A7.diffFreqs rho l1)
        (C := (2 * ((2 ^ L0 : ℕ) : ℝ) + 4) * cpsi Lam) hper ξ
      have hKf : Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (L0 : ℝ))) * (2 * ((2 ^ L0 : ℕ) : ℝ) + 4) ≤ Kf :=
        le_max_right _ _
      calc ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs rho l1)
              (periodize (Work.KMTAreas.A7.randSymb psif eps K)) ξ‖
          ≤ ((Work.KMTAreas.A7.diffFreqs rho l1).card : ℝ) * ((2 * ((2 ^ L0 : ℕ) : ℝ) + 4) * cpsi Lam) := hb
        _ ≤ (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (L0 : ℝ)))) * ((2 * ((2 ^ L0 : ℕ) : ℝ) + 4) * cpsi Lam) := by
            apply mul_le_mul_of_nonneg_right hcard
            exact mul_nonneg (by positivity) (hcpsiP Lam hLam).le
        _ = (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (rho * (L0 : ℝ))) * (2 * ((2 ^ L0 : ℕ) : ℝ) + 4)) * cpsi Lam := by
            ring
        _ ≤ Kf * cpsi Lam := mul_le_mul_of_nonneg_right hKf (hcpsiP Lam hLam).le
        _ ≤ Kf * cpsi Lam + 1 := by linarith
  have hPhi : MemLp (iwSymbolSet (Work.KMTAreas.A7.diffFreqs rho l1)
      (periodize (Work.KMTAreas.A7.randSymb psif eps K))) ⊤ circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet _
      (Work.Analysis.IonescuWainger.memLp_periodize (φ := Work.KMTAreas.A7.randSymb psif eps K)
        (R := (2 : ℝ) ^ (k1 : ℤ)) (C := cpsi Lam) hmeas
        (by rw [two_zpow_eq_rpow k1]; exact Real.rpow_nonneg (by norm_num) (k1 : ℝ))
        (fun x hx => by
          by_contra hne
          have hmem := hsupp0 x hne
          rw [realArc, Set.mem_Icc] at hmem
          rw [two_zpow_eq_rpow k1] at hmem
          have habs : |x| ≤ (2 : ℝ) ^ (k1 : ℝ) := abs_le.mpr hmem
          rw [two_zpow_eq_rpow k1] at hx
          linarith)
        (fun x => hpsiran x))
  have hmain := eLpNorm_iwConv_two_le_of_symbol_bound (Work.KMTAreas.A7.diffFreqs rho l1)
    (periodize (Work.KMTAreas.A7.randSymb psif eps K)) (Kf * cpsi Lam + 1)
    (by nlinarith [hcpsiP Lam hLam, hKf1]) hsym hPhi f hf
  change MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs rho l1)
    (periodize (Work.KMTAreas.A7.randSymb psif eps K)) f) 2 MeasureTheory.Measure.count
    ≤ ((Real.toNNReal (Kf * cpsi Lam + 1) : NNReal) : ENNReal)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
  exact hmain



-- ============================================================================
-- Part 3: the lemma
-- ============================================================================

theorem tmRandSymb_l2 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ ρ₀ : Real, 0 < ρ₀ ∧ ∀ ρ : Real, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : Real) (ε : ℕ → Complex) (f : ℤ → Complex),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : Real) 1 →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
            (Work.KMTAreas.A7.randSymb
              (fun n ξ => if n = 0 then 0
                else if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
                  then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0) ε K) f)
          2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := tmRandSymb_l2_main P hd hA1 C₀ hC₀

end Work.KMTPlan.A6
