/-
`Work.HP.DyadicSum.dyadic_summation_pub`: the dyadic summation lemma underlying the bound
`F_{d,n}(B) ≪ B²/(log B)^{1/2}` (Browning--Le Boudec--Sawin, §4).
-/
import Mathlib
import Submission.Work.HP.ceil_logb_bounds

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

/-- Combining inverse `α`-powers: `a^{-s} * a^2 * a^d = a^e` when `e = 2 - s + d`. -/
private lemma rpow_combine {a s d e : ℝ} (ha : 0 < a) (he : e = 2 - s + d) :
    a ^ (-s) * a ^ 2 * a ^ d = a ^ e := by
  have h1 : a ^ (-s) * a ^ 2 = a ^ (2 - s) := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_add ha]
    congr 1
    ring
  have h2 : a ^ (2 - s) * a ^ d = a ^ (2 - s + d) := by
    rw [← Real.rpow_add ha]
  rw [h1, h2, he]

/-- For `u ≥ 1` and `α ≥ 0`, `u^{-α}` is at most `2^α` times the inverse `α`-power of the
dyadic ceiling `2^{⌈log₂ u⌉}`. -/
private lemma inv_rpow_le_two_pow_ceil {u α : ℝ} (hu : 1 ≤ u) (hα : 0 ≤ α) :
    u ^ (-α) ≤ (2 : ℝ) ^ α * (((2 : ℝ) ^ (Nat.ceil (Real.logb 2 u))) ^ (-α)) := by
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  obtain ⟨hle, hle2⟩ := ceil_logb_bounds hu
  set j0 : ℕ := Nat.ceil (Real.logb 2 u) with hj0
  have ha : 0 < (2 : ℝ) ^ j0 := by positivity
  have hdiv : (2 : ℝ) ^ j0 / u ≤ 2 := by
    rw [div_le_iff₀ hu0]; linarith
  have h1 : ((2 : ℝ) ^ j0 / u) ^ α ≤ (2 : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) hdiv hα
  have key : u ^ (-α) * ((2 : ℝ) ^ j0) ^ α = ((2 : ℝ) ^ j0 / u) ^ α := by
    rw [Real.rpow_neg hu0.le α, ← Real.inv_rpow hu0.le α,
      ← Real.mul_rpow (by positivity : (0 : ℝ) ≤ u⁻¹) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ j0)]
    congr 1
    rw [div_eq_mul_inv]; ring
  have hne : ((2 : ℝ) ^ j0) ^ α ≠ 0 := (Real.rpow_pos_of_pos ha α).ne'
  have key2 : u ^ (-α) = ((2 : ℝ) ^ j0 / u) ^ α * (((2 : ℝ) ^ j0) ^ α)⁻¹ := by
    rw [← key, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have key3 : ((2 : ℝ) ^ j0) ^ (-α) = (((2 : ℝ) ^ j0) ^ α)⁻¹ := Real.rpow_neg ha.le α
  rw [key2, ← key3]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ha.le _)

/-- Dyadic shell majorant: for `u ≥ 1`, `α ≥ 0` and `u ≤ 2^I`,
`u^{-α}` is bounded by `2^α` times a sum of dyadic inverses. -/
private lemma inv_rpow_shell_sum {u α : ℝ} {I : ℕ} (hu : 1 ≤ u) (hI : u ≤ (2 : ℝ) ^ I)
    (hα : 0 ≤ α) :
    u ^ (-α) ≤ (2 : ℝ) ^ α * ∑ j ∈ Finset.range (I + 1),
      (((2 : ℝ) ^ j) ^ (-α)) * (if u ≤ (2 : ℝ) ^ j then (1 : ℝ) else 0) := by
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
  set j0 : ℕ := Nat.ceil (Real.logb 2 u) with hj0
  have hu_le : u ≤ (2 : ℝ) ^ j0 := by rw [hj0]; exact (ceil_logb_bounds hu).1
  have hj0I : j0 ≤ I := by
    rw [hj0, Nat.ceil_le]
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hu0).mpr
      (by rw [Real.rpow_natCast]; exact hI)
  have hmem : j0 ∈ Finset.range (I + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj0I)
  have hterm : ((2 : ℝ) ^ j0) ^ (-α) * (if u ≤ (2 : ℝ) ^ j0 then (1 : ℝ) else 0)
      = ((2 : ℝ) ^ j0) ^ (-α) := by rw [if_pos hu_le, mul_one]
  have hnn : ∀ j ∈ Finset.range (I + 1),
      (0 : ℝ) ≤ ((2 : ℝ) ^ j) ^ (-α) * (if u ≤ (2 : ℝ) ^ j then (1 : ℝ) else 0) := by
    intro j _
    by_cases h : u ≤ (2 : ℝ) ^ j
    · rw [if_pos h, mul_one]; exact Real.rpow_nonneg (by positivity) _
    · rw [if_neg h, mul_zero]
  have hsingle : ((2 : ℝ) ^ j0) ^ (-α) ≤ ∑ j ∈ Finset.range (I + 1),
      ((2 : ℝ) ^ j) ^ (-α) * (if u ≤ (2 : ℝ) ^ j then (1 : ℝ) else 0) :=
    le_trans (le_of_eq hterm.symm)
      (Finset.single_le_sum (s := Finset.range (I + 1)) (a := j0)
        (f := fun j => ((2 : ℝ) ^ j) ^ (-α) * (if u ≤ (2 : ℝ) ^ j then (1 : ℝ) else 0))
        hnn hmem)
  calc u ^ (-α) ≤ (2 : ℝ) ^ α * ((2 : ℝ) ^ j0) ^ (-α) := by
        rw [hj0]; exact inv_rpow_le_two_pow_ceil hu hα
    _ ≤ (2 : ℝ) ^ α * ∑ j ∈ Finset.range (I + 1),
        ((2 : ℝ) ^ j) ^ (-α) * (if u ≤ (2 : ℝ) ^ j then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left hsingle (Real.rpow_nonneg (by norm_num) _)

theorem dyadic_summation_pub {γ : Type*} (n : ℕ) (hn : 3 ≤ n) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t)
    (htn : t < (n : ℝ) - 1) (hst : s + t ≤ (n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset γ) (x y D : γ → ℝ) (K V X : ℝ), 0 < K → 1 ≤ V → 1 ≤ X →
      (∀ p ∈ S, 1 ≤ x p ∧ 1 ≤ y p ∧ 1 ≤ D p ∧ D p * V ≤ x p * y p ∧ x p ≤ X ∧ y p ≤ X) →
      (∀ A B Δ : ℝ, 1 ≤ A → 1 ≤ B → 0 < Δ →
        ((S.filter (fun p => x p ≤ A ∧ y p ≤ B ∧ D p ≤ Δ)).card : ℝ)
          ≤ K * A ^ 2 * B ^ 2 * Δ ^ (n - 1)) →
      (∑ p ∈ S, 1 / (D p ^ t * x p ^ s * y p ^ s))
        ≤ C * K * X ^ (2 * ((n : ℝ) + 1 - s - t)) / V ^ ((n : ℝ) - 1 - t) := by
  set d : ℝ := (n : ℝ) - 1 - t with hddef
  set e : ℝ := (n : ℝ) + 1 - s - t with hedef
  have hdpos : 0 < d := by rw [hddef]; linarith
  have he1 : 1 ≤ e := by rw [hedef]; linarith
  have hepos : 0 < e := lt_of_lt_of_le zero_lt_one he1
  have h2d : (1 : ℝ) < (2 : ℝ) ^ d := Real.one_lt_rpow (by norm_num) hdpos
  have h2e : (1 : ℝ) < (2 : ℝ) ^ e := Real.one_lt_rpow (by norm_num) hepos
  set C2 : ℝ := (8 : ℝ) ^ d / ((2 : ℝ) ^ d - 1) with hC2def
  set C1 : ℝ := (2 : ℝ) ^ (2 * e) / ((2 : ℝ) ^ e - 1) with hC1def
  have hC2pos : 0 < C2 := by
    rw [hC2def]; exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
  have hC1pos : 0 < C1 := by
    rw [hC1def]; exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
  refine ⟨(2 : ℝ) ^ (2 * s + t) * C2 * C1 ^ 2, ?_, ?_⟩
  · exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hC2pos) (pow_pos hC1pos 2)
  intro S x y D K V X hK hV hX hpt hcnt
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  set I : ℕ := Nat.ceil (Real.logb 2 X) with hIdef
  have hX_le : X ≤ (2 : ℝ) ^ I := by rw [hIdef]; exact (ceil_logb_bounds hX).1
  have hX_le2 : (2 : ℝ) ^ I ≤ 2 * X := by rw [hIdef]; exact (ceil_logb_bounds hX).2
  have hpair : ∀ j j' : ℕ,
      (∑ p ∈ S.filter (fun p => x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j'), D p ^ (-t))
        ≤ (2 : ℝ) ^ t * K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * C2
            * (((2 : ℝ) ^ j * (2 : ℝ) ^ j') / V) ^ d := by
    intro j j'
    set T := S.filter (fun p => x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j') with hTdef
    by_cases hempty : T = ∅
    · rw [hempty, Finset.sum_empty]
      positivity
    · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨hp0S, hp0c⟩ := Finset.mem_filter.mp hp0
      obtain ⟨hp0x, hp0y⟩ := hp0c
      have hVle : V ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ j' := by
        have h1 : V ≤ D p0 * V := by
          have h3 : 1 ≤ D p0 := (hpt p0 hp0S).2.2.1
          calc V = 1 * V := (one_mul V).symm
            _ ≤ D p0 * V := mul_le_mul_of_nonneg_right h3 hVpos.le
        have hy0 : (0 : ℝ) ≤ y p0 := le_trans zero_le_one (hpt p0 hp0S).2.1
        exact le_trans h1 (le_trans (hpt p0 hp0S).2.2.2.1
          (mul_le_mul hp0x hp0y hy0 (by positivity)))
      have hu1 : 1 ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ j' / V := by
        rw [le_div_iff₀ hVpos, one_mul]; exact hVle
      set u : ℝ := (2 : ℝ) ^ j * (2 : ℝ) ^ j' / V with hudef
      have hu1' : 1 ≤ u := by rw [hudef]; exact hu1
      set Km : ℕ := Nat.ceil (Real.logb 2 u) with hKmdef
      have hKm_le : u ≤ (2 : ℝ) ^ Km := by rw [hKmdef]; exact (ceil_logb_bounds hu1').1
      have hKm_le2 : (2 : ℝ) ^ Km ≤ 2 * u := by rw [hKmdef]; exact (ceil_logb_bounds hu1').2
      have hmaj : ∀ p ∈ T, D p ^ (-t) ≤ (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
            (((2 : ℝ) ^ k) ^ (-t)) * (if D p ≤ (2 : ℝ) ^ k then (1 : ℝ) else 0) := by
        intro p hpT
        obtain ⟨hpS, hpx, hpy⟩ := Finset.mem_filter.mp hpT
        have hD1 : 1 ≤ D p := (hpt p hpS).2.2.1
        have hDle_u : D p ≤ u := by
          rw [hudef, le_div_iff₀ hVpos]
          have hy0 : (0 : ℝ) ≤ y p := le_trans zero_le_one (hpt p hpS).2.1
          exact le_trans (hpt p hpS).2.2.2.1 (mul_le_mul hpx hpy hy0 (by positivity))
        exact inv_rpow_shell_sum hD1 (le_trans hDle_u hKm_le) ht.le
      have hstep2 : (∑ p ∈ T, (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
            (((2 : ℝ) ^ k) ^ (-t)) * (if D p ≤ (2 : ℝ) ^ k then (1 : ℝ) else 0))
          = (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
              (((2 : ℝ) ^ k) ^ (-t)) * ((T.filter (fun p => D p ≤ (2 : ℝ) ^ k)).card : ℝ) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.mul_sum, Finset.sum_boole]
      have hstep3 : (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
              (((2 : ℝ) ^ k) ^ (-t)) * ((T.filter (fun p => D p ≤ (2 : ℝ) ^ k)).card : ℝ)
          ≤ (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
              (((2 : ℝ) ^ k) ^ (-t))
                * (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * ((2 : ℝ) ^ k) ^ (n - 1)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => ?_)) (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hA : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        have hB : (1 : ℝ) ≤ (2 : ℝ) ^ j' := one_le_pow₀ (by norm_num)
        have hDd : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
        have hsub : T.filter (fun p => D p ≤ (2 : ℝ) ^ k) ⊆
            S.filter (fun p => x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j' ∧ D p ≤ (2 : ℝ) ^ k) := by
          intro p hp
          have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
          have hpD : D p ≤ (2 : ℝ) ^ k := (Finset.mem_filter.mp hp).2
          rw [hTdef, Finset.mem_filter] at hpT
          exact Finset.mem_filter.mpr ⟨hpT.1, hpT.2.1, hpT.2.2, hpD⟩
        exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hcnt _ _ _ hA hB hDd)
      have hstep4 : (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
              (((2 : ℝ) ^ k) ^ (-t))
                * (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * ((2 : ℝ) ^ k) ^ (n - 1))
          = (2 : ℝ) ^ t * (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2)
              * ∑ k ∈ Finset.range (Km + 1), ((2 : ℝ) ^ k) ^ d := by
        have hpt' : ∀ k, (((2 : ℝ) ^ k) ^ (-t))
              * (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * ((2 : ℝ) ^ k) ^ (n - 1))
            = (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2) * ((2 : ℝ) ^ k) ^ d := by
          intro k
          have hk1 : ((2 : ℝ) ^ k) ^ (n - 1) = ((2 : ℝ) ^ k) ^ (((n - 1 : ℕ) : ℝ)) :=
            (Real.rpow_natCast _ _).symm
          have hcast : (-t) + (((n - 1 : ℕ) : ℝ)) = d := by
            rw [hddef, Nat.cast_sub (by omega : 1 ≤ n)]; ring
          have hcomb : ((2 : ℝ) ^ k) ^ (-t) * ((2 : ℝ) ^ k) ^ (((n - 1 : ℕ) : ℝ))
              = ((2 : ℝ) ^ k) ^ d := by
            rw [← Real.rpow_add (pow_pos (by norm_num : (0 : ℝ) < 2) k), hcast]
          rw [hk1]
          calc ((2 : ℝ) ^ k) ^ (-t) * (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2
                * ((2 : ℝ) ^ k) ^ (((n - 1 : ℕ) : ℝ)))
              = (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2)
                  * (((2 : ℝ) ^ k) ^ (-t) * ((2 : ℝ) ^ k) ^ (((n - 1 : ℕ) : ℝ))) := by ring
            _ = (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2) * ((2 : ℝ) ^ k) ^ d := by
                rw [hcomb]
        rw [Finset.sum_congr rfl (fun k _ => hpt' k), ← Finset.mul_sum]
        ring
      have hstep5 : ∑ k ∈ Finset.range (Km + 1), ((2 : ℝ) ^ k) ^ d ≤ C2 * u ^ d := by
        have hrw : ∀ k, ((2 : ℝ) ^ k) ^ d = ((2 : ℝ) ^ d) ^ k := by
          intro k
          have h1 : ((2 : ℝ) ^ k) ^ d = (2 : ℝ) ^ (((k : ℕ) : ℝ) * d) := by
            rw [← Real.rpow_natCast (2 : ℝ) k]
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((k : ℕ) : ℝ) d).symm
          have h2 : ((2 : ℝ) ^ d) ^ k = (2 : ℝ) ^ (d * ((k : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ d) k]
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) d ((k : ℕ) : ℝ)).symm
          rw [h1, h2]; congr 1; ring
        rw [Finset.sum_congr rfl (fun k _ => hrw k)]
        have hne : ((2 : ℝ) ^ d) ≠ 1 := ne_of_gt h2d
        rw [geom_sum_eq hne (Km + 1)]
        have hden : 0 < (2 : ℝ) ^ d - 1 := by linarith
        have hnum : ((2 : ℝ) ^ d) ^ (Km + 1) - 1 ≤ ((2 : ℝ) ^ d) ^ (Km + 1) := by
          have : (0 : ℝ) < ((2 : ℝ) ^ d) ^ (Km + 1) := pow_pos (by linarith) _
          linarith
        have hpowK : ((2 : ℝ) ^ d) ^ Km ≤ ((4 : ℝ) * u) ^ d := by
          have h1 : ((2 : ℝ) ^ d) ^ Km = ((2 : ℝ) ^ Km) ^ d := by
            have ha : ((2 : ℝ) ^ d) ^ Km = (2 : ℝ) ^ (d * ((Km : ℕ) : ℝ)) := by
              rw [← Real.rpow_natCast ((2 : ℝ) ^ d) Km]
              exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) d ((Km : ℕ) : ℝ)).symm
            have hb : ((2 : ℝ) ^ Km) ^ d = (2 : ℝ) ^ (((Km : ℕ) : ℝ) * d) := by
              rw [← Real.rpow_natCast (2 : ℝ) Km]
              exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((Km : ℕ) : ℝ) d).symm
            rw [ha, hb]; congr 1; ring
          rw [h1]
          exact Real.rpow_le_rpow (by positivity) (by linarith) hdpos.le
        have hbound : ((2 : ℝ) ^ d) ^ (Km + 1) ≤ (8 : ℝ) ^ d * u ^ d := by
          have h4 : ((4 : ℝ) * u) ^ d = (4 : ℝ) ^ d * u ^ d :=
            Real.mul_rpow (by norm_num) (by positivity)
          have h24 : (2 : ℝ) ^ d * (4 : ℝ) ^ d = (8 : ℝ) ^ d := by
            rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num
          calc ((2 : ℝ) ^ d) ^ (Km + 1)
              = (2 : ℝ) ^ d * ((2 : ℝ) ^ d) ^ Km := by rw [pow_succ]; ring
            _ ≤ (2 : ℝ) ^ d * (((4 : ℝ) * u) ^ d) :=
                mul_le_mul_of_nonneg_left hpowK (by positivity)
            _ = (2 : ℝ) ^ d * ((4 : ℝ) ^ d * u ^ d) := by rw [h4]
            _ = (8 : ℝ) ^ d * u ^ d := by rw [← h24]; ring
        have hfin : ((2 : ℝ) ^ d) ^ (Km + 1) / ((2 : ℝ) ^ d - 1) ≤ C2 * u ^ d := by
          rw [hC2def, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden]
          exact hbound
        calc (((2 : ℝ) ^ d) ^ (Km + 1) - 1) / ((2 : ℝ) ^ d - 1)
            ≤ ((2 : ℝ) ^ d) ^ (Km + 1) / ((2 : ℝ) ^ d - 1) :=
              div_le_div_of_nonneg_right hnum hden.le
          _ ≤ C2 * u ^ d := hfin
      calc (∑ p ∈ T, D p ^ (-t))
          ≤ ∑ p ∈ T, (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
              (((2 : ℝ) ^ k) ^ (-t)) * (if D p ≤ (2 : ℝ) ^ k then (1 : ℝ) else 0) :=
            Finset.sum_le_sum hmaj
        _ = (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
              (((2 : ℝ) ^ k) ^ (-t)) * ((T.filter (fun p => D p ≤ (2 : ℝ) ^ k)).card : ℝ) :=
            hstep2
        _ ≤ (2 : ℝ) ^ t * ∑ k ∈ Finset.range (Km + 1),
              (((2 : ℝ) ^ k) ^ (-t))
                * (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * ((2 : ℝ) ^ k) ^ (n - 1)) :=
            hstep3
        _ = (2 : ℝ) ^ t * (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2)
              * ∑ k ∈ Finset.range (Km + 1), ((2 : ℝ) ^ k) ^ d := hstep4
        _ ≤ (2 : ℝ) ^ t * (K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2) * (C2 * u ^ d) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact hstep5
        _ = (2 : ℝ) ^ t * K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * C2
              * (((2 : ℝ) ^ j * (2 : ℝ) ^ j') / V) ^ d := by
            rw [hudef]; ring
  have hpt2 : ∀ p ∈ S, D p ^ (-t) * x p ^ (-s) * y p ^ (-s)
      ≤ (2 : ℝ) ^ (2 * s) * ∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
          (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
            (if x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0) := by
    intro p hp
    obtain ⟨hx1, hy1, hD1, hDV, hxX, hyX⟩ := hpt p hp
    have hxpos : 0 < x p := lt_of_lt_of_le zero_lt_one hx1
    have hypos : 0 < y p := lt_of_lt_of_le zero_lt_one hy1
    have hDpos : 0 < D p := lt_of_lt_of_le zero_lt_one hD1
    set jx : ℕ := Nat.ceil (Real.logb 2 (x p)) with hjx
    set jy : ℕ := Nat.ceil (Real.logb 2 (y p)) with hjy
    have hxle : x p ≤ (2 : ℝ) ^ jx := by rw [hjx]; exact (ceil_logb_bounds hx1).1
    have hyle : y p ≤ (2 : ℝ) ^ jy := by rw [hjy]; exact (ceil_logb_bounds hy1).1
    have hxI : x p ≤ (2 : ℝ) ^ I := le_trans hxX hX_le
    have hyI : y p ≤ (2 : ℝ) ^ I := le_trans hyX hX_le
    have hjxI : jx ≤ I := by
      rw [hjx, Nat.ceil_le]
      exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hxpos).mpr
        (by rw [Real.rpow_natCast]; exact hxI)
    have hjyI : jy ≤ I := by
      rw [hjy, Nat.ceil_le]
      exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hypos).mpr
        (by rw [Real.rpow_natCast]; exact hyI)
    have hxs : x p ^ (-s) ≤ (2 : ℝ) ^ s * ((2 : ℝ) ^ jx) ^ (-s) := by
      rw [hjx]; exact inv_rpow_le_two_pow_ceil hx1 hs
    have hys : y p ^ (-s) ≤ (2 : ℝ) ^ s * ((2 : ℝ) ^ jy) ^ (-s) := by
      rw [hjy]; exact inv_rpow_le_two_pow_ceil hy1 hs
    have hxy : x p ^ (-s) * y p ^ (-s)
        ≤ (2 : ℝ) ^ (2 * s) * (((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ jy) ^ (-s)) := by
      have hpow : (2 : ℝ) ^ s * (2 : ℝ) ^ s = (2 : ℝ) ^ (2 * s) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      calc x p ^ (-s) * y p ^ (-s)
          ≤ ((2 : ℝ) ^ s * ((2 : ℝ) ^ jx) ^ (-s)) * ((2 : ℝ) ^ s * ((2 : ℝ) ^ jy) ^ (-s)) :=
            mul_le_mul hxs hys (Real.rpow_nonneg hypos.le _) (by positivity)
        _ = (2 : ℝ) ^ (2 * s) * (((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ jy) ^ (-s)) := by
            rw [← hpow]; ring
    have hinner_nn : ∀ j' ∈ Finset.range (I + 1),
        (0 : ℝ) ≤ (((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
          (if x p ≤ (2 : ℝ) ^ jx ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0) := by
      intro j' _
      refine mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)) ?_
      by_cases h : x p ≤ (2 : ℝ) ^ jx ∧ y p ≤ (2 : ℝ) ^ j'
      · rw [if_pos h]; exact Real.rpow_nonneg hDpos.le _
      · rw [if_neg h]
    have hstep_inner : (((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ jy) ^ (-s)) * D p ^ (-t)
        ≤ ∑ j' ∈ Finset.range (I + 1),
            (((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
              (if x p ≤ (2 : ℝ) ^ jx ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0) := by
      refine le_trans (le_of_eq ?_)
        (Finset.single_le_sum (s := Finset.range (I + 1)) (a := jy)
          (f := fun j' => ((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s) *
            (if x p ≤ (2 : ℝ) ^ jx ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0))
          hinner_nn (Finset.mem_range.mpr (Nat.lt_succ_of_le hjyI)))
      rw [if_pos ⟨hxle, hyle⟩]
    have hsummand_nn : ∀ j ∈ Finset.range (I + 1), (0 : ℝ) ≤ ∑ j' ∈ Finset.range (I + 1),
        (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
          (if x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0) := by
      intro j _
      refine Finset.sum_nonneg (fun j' _ => ?_)
      refine mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)) ?_
      by_cases h : x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j'
      · rw [if_pos h]; exact Real.rpow_nonneg hDpos.le _
      · rw [if_neg h]
    have hstep_outer : (∑ j' ∈ Finset.range (I + 1),
            (((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
              (if x p ≤ (2 : ℝ) ^ jx ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0))
        ≤ ∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
            (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
              (if x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0) :=
      Finset.single_le_sum (s := Finset.range (I + 1)) (a := jx)
        (f := fun j => ∑ j' ∈ Finset.range (I + 1),
          ((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s) *
            (if x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0))
        hsummand_nn (Finset.mem_range.mpr (Nat.lt_succ_of_le hjxI))
    calc D p ^ (-t) * x p ^ (-s) * y p ^ (-s)
        = D p ^ (-t) * (x p ^ (-s) * y p ^ (-s)) := by ring
      _ ≤ D p ^ (-t) * ((2 : ℝ) ^ (2 * s)
            * (((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ jy) ^ (-s))) :=
          mul_le_mul_of_nonneg_left hxy (Real.rpow_nonneg hDpos.le _)
      _ = (2 : ℝ) ^ (2 * s)
            * ((((2 : ℝ) ^ jx) ^ (-s) * ((2 : ℝ) ^ jy) ^ (-s)) * D p ^ (-t)) := by ring
      _ ≤ (2 : ℝ) ^ (2 * s) * (∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
            (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
              (if x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans hstep_inner hstep_outer
  have hmain1 : (∑ p ∈ S, D p ^ (-t) * x p ^ (-s) * y p ^ (-s))
      ≤ (2 : ℝ) ^ (2 * s) * ∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
          (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
            (∑ p ∈ S.filter (fun p => x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j'), D p ^ (-t)) := by
    calc (∑ p ∈ S, D p ^ (-t) * x p ^ (-s) * y p ^ (-s))
        ≤ ∑ p ∈ S, (2 : ℝ) ^ (2 * s) * ∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
            (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
              (if x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j' then D p ^ (-t) else 0) :=
          Finset.sum_le_sum hpt2
      _ = (2 : ℝ) ^ (2 * s) * ∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
            (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
              (∑ p ∈ S.filter (fun p => x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j'), D p ^ (-t)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j' _ => ?_)
          rw [← Finset.mul_sum, ← Finset.sum_filter]
  have hmain2 : (2 : ℝ) ^ (2 * s) * ∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
          (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
            (∑ p ∈ S.filter (fun p => x p ≤ (2 : ℝ) ^ j ∧ y p ≤ (2 : ℝ) ^ j'), D p ^ (-t))
      ≤ (2 : ℝ) ^ (2 * s) * ∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
          (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
            ((2 : ℝ) ^ t * K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * C2
              * (((2 : ℝ) ^ j * (2 : ℝ) ^ j') / V) ^ d) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun j' _ => ?_)
    exact mul_le_mul_of_nonneg_left (hpair j j') (by positivity)
  have hmain3 : (2 : ℝ) ^ (2 * s) * ∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
          (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
            ((2 : ℝ) ^ t * K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * C2
              * (((2 : ℝ) ^ j * (2 : ℝ) ^ j') / V) ^ d)
      = (2 : ℝ) ^ (2 * s) * ((2 : ℝ) ^ t * K * C2)
          * (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ j) ^ e) ^ 2 / V ^ d := by
    have hsummand : ∀ j j' : ℕ,
        (((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j') ^ (-s)) *
            ((2 : ℝ) ^ t * K * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j') ^ 2 * C2
              * (((2 : ℝ) ^ j * (2 : ℝ) ^ j') / V) ^ d)
          = ((2 : ℝ) ^ t * K * C2) * (((2 : ℝ) ^ j) ^ e * ((2 : ℝ) ^ j') ^ e) / V ^ d := by
      intro j j'
      have hj : 0 < (2 : ℝ) ^ j := by positivity
      have hj' : 0 < (2 : ℝ) ^ j' := by positivity
      have hdiv : (((2 : ℝ) ^ j * (2 : ℝ) ^ j') / V) ^ d
          = ((2 : ℝ) ^ j) ^ d * ((2 : ℝ) ^ j') ^ d / V ^ d := by
        rw [Real.div_rpow (by positivity) hVpos.le,
          Real.mul_rpow (by positivity) (by positivity)]
      have hcj : ((2 : ℝ) ^ j) ^ (-s) * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ j) ^ d
          = ((2 : ℝ) ^ j) ^ e := rpow_combine hj (by rw [hedef]; ring)
      have hcj' : ((2 : ℝ) ^ j') ^ (-s) * ((2 : ℝ) ^ j') ^ 2 * ((2 : ℝ) ^ j') ^ d
          = ((2 : ℝ) ^ j') ^ e := rpow_combine hj' (by rw [hedef]; ring)
      rw [hdiv]
      rw [← hcj, ← hcj']
      ring
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => hsummand j j'))]
    have hfac : ∀ j j' : ℕ, ((2 : ℝ) ^ t * K * C2) * (((2 : ℝ) ^ j) ^ e * ((2 : ℝ) ^ j') ^ e) / V ^ d
        = (((2 : ℝ) ^ t * K * C2) / V ^ d) * (((2 : ℝ) ^ j) ^ e * ((2 : ℝ) ^ j') ^ e) := by
      intro j j'; ring
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => hfac j j'))]
    have hsum_eq : (∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
          (((2 : ℝ) ^ t * K * C2) / V ^ d) * (((2 : ℝ) ^ j) ^ e * ((2 : ℝ) ^ j') ^ e))
        = (((2 : ℝ) ^ t * K * C2) / V ^ d)
            * (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ j) ^ e) ^ 2 := by
      have h1 : (∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
            (((2 : ℝ) ^ t * K * C2) / V ^ d) * (((2 : ℝ) ^ j) ^ e * ((2 : ℝ) ^ j') ^ e))
          = (((2 : ℝ) ^ t * K * C2) / V ^ d)
            * (∑ j ∈ Finset.range (I + 1), ∑ j' ∈ Finset.range (I + 1),
                ((2 : ℝ) ^ j) ^ e * ((2 : ℝ) ^ j') ^ e) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
      rw [h1]
      congr 1
      rw [← Finset.sum_mul_sum, ← sq]
    rw [hsum_eq]
    ring
  have hgeom : (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ j) ^ e) ≤ C1 * X ^ e := by
    have hrw : ∀ j, ((2 : ℝ) ^ j) ^ e = ((2 : ℝ) ^ e) ^ j := by
      intro j
      have h1 : ((2 : ℝ) ^ j) ^ e = (2 : ℝ) ^ (((j : ℕ) : ℝ) * e) := by
        rw [← Real.rpow_natCast (2 : ℝ) j]
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((j : ℕ) : ℝ) e).symm
      have h2 : ((2 : ℝ) ^ e) ^ j = (2 : ℝ) ^ (e * ((j : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ e) j]
        exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) e ((j : ℕ) : ℝ)).symm
      rw [h1, h2]; congr 1; ring
    rw [Finset.sum_congr rfl (fun j _ => hrw j)]
    have hne : ((2 : ℝ) ^ e) ≠ 1 := ne_of_gt h2e
    rw [geom_sum_eq hne (I + 1)]
    rw [hC1def]
    have hden : 0 < (2 : ℝ) ^ e - 1 := by linarith
    have hnum : ((2 : ℝ) ^ e) ^ (I + 1) - 1 ≤ ((2 : ℝ) ^ e) ^ (I + 1) := by
      have : (0 : ℝ) < ((2 : ℝ) ^ e) ^ (I + 1) := pow_pos (by linarith) _
      linarith
    have hIpow : ((2 : ℝ) ^ e) ^ (I + 1) ≤ (2 : ℝ) ^ (2 * e) * X ^ e := by
      rw [pow_succ]
      have hb : ((2 : ℝ) ^ e) ^ I ≤ (2 * X) ^ e := by
        have h1 : ((2 : ℝ) ^ e) ^ I = ((2 : ℝ) ^ I) ^ e := by
          have ha : ((2 : ℝ) ^ e) ^ I = (2 : ℝ) ^ (e * ((I : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ e) I]
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) e ((I : ℕ) : ℝ)).symm
          have hb' : ((2 : ℝ) ^ I) ^ e = (2 : ℝ) ^ (((I : ℕ) : ℝ) * e) := by
            rw [← Real.rpow_natCast (2 : ℝ) I]
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((I : ℕ) : ℝ) e).symm
          rw [ha, hb']; congr 1; ring
        rw [h1]
        exact Real.rpow_le_rpow (by positivity) hX_le2 hepos.le
      calc ((2 : ℝ) ^ e) ^ I * (2 : ℝ) ^ e ≤ (2 * X) ^ e * (2 : ℝ) ^ e :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = (2 : ℝ) ^ (2 * e) * X ^ e := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hXpos.le]
            have h2e : (2 : ℝ) ^ e * (2 : ℝ) ^ e = (2 : ℝ) ^ (2 * e) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
            linear_combination (X ^ e) * h2e
    refine le_trans (div_le_div_of_nonneg_right hnum hden.le) ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden]
    exact hIpow
  have hfinal : (2 : ℝ) ^ (2 * s) * ((2 : ℝ) ^ t * K * C2)
        * (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ j) ^ e) ^ 2 / V ^ d
      ≤ (2 : ℝ) ^ (2 * s + t) * C2 * C1 ^ 2 * K * X ^ (2 * ((n : ℝ) + 1 - s - t))
          / V ^ ((n : ℝ) - 1 - t) := by
    have hsq : (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ j) ^ e) ^ 2 ≤ (C1 * X ^ e) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _)) hgeom 2
    have hCsq : (C1 * X ^ e) ^ 2 = C1 ^ 2 * X ^ (2 * e) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast (X ^ e) 2]
      have h1 : (X ^ e) ^ ((2 : ℕ) : ℝ) = X ^ (e * ((2 : ℕ) : ℝ)) :=
        (Real.rpow_mul hXpos.le e ((2 : ℕ) : ℝ)).symm
      rw [h1]
      congr 1
      ring
    have hkey : (2 : ℝ) ^ (2 * s) * ((2 : ℝ) ^ t * K * C2)
          * (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ j) ^ e) ^ 2
        ≤ (2 : ℝ) ^ (2 * s + t) * C2 * C1 ^ 2 * K * X ^ (2 * e) := by
      calc (2 : ℝ) ^ (2 * s) * ((2 : ℝ) ^ t * K * C2)
            * (∑ j ∈ Finset.range (I + 1), ((2 : ℝ) ^ j) ^ e) ^ 2
          ≤ (2 : ℝ) ^ (2 * s) * ((2 : ℝ) ^ t * K * C2) * (C1 ^ 2 * X ^ (2 * e)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact le_trans hsq (le_of_eq hCsq)
        _ = (2 : ℝ) ^ (2 * s + t) * C2 * C1 ^ 2 * K * X ^ (2 * e) := by
            have h2st : (2 : ℝ) ^ (2 * s) * (2 : ℝ) ^ t = (2 : ℝ) ^ (2 * s + t) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            linear_combination (K * C2 * (C1 ^ 2 * X ^ (2 * e))) * h2st
    rw [hedef] at hkey
    rw [hddef, hedef]
    exact div_le_div_of_nonneg_right hkey (by positivity)
  have hmain : (∑ p ∈ S, D p ^ (-t) * x p ^ (-s) * y p ^ (-s))
      ≤ (2 : ℝ) ^ (2 * s + t) * C2 * C1 ^ 2 * K * X ^ (2 * ((n : ℝ) + 1 - s - t))
          / V ^ ((n : ℝ) - 1 - t) :=
    le_trans hmain1 (le_trans hmain2 (le_trans (le_of_eq hmain3) hfinal))
  have heq : (∑ p ∈ S, 1 / (D p ^ t * x p ^ s * y p ^ s))
      = ∑ p ∈ S, D p ^ (-t) * x p ^ (-s) * y p ^ (-s) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨hx1, hy1, hD1, -, -, -⟩ := hpt p hp
    have hxpos : 0 < x p := lt_of_lt_of_le zero_lt_one hx1
    have hypos : 0 < y p := lt_of_lt_of_le zero_lt_one hy1
    have hDpos : 0 < D p := lt_of_lt_of_le zero_lt_one hD1
    rw [one_div, mul_inv, mul_inv, ← Real.rpow_neg hDpos.le t,
      ← Real.rpow_neg hxpos.le s, ← Real.rpow_neg hypos.le s]
  rw [heq]
  exact le_trans hmain le_rfl

end Work.HP
