import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.prod_erase_range_sub_factorial
import Submission.Work.KMTPlan.A6.ConcAux.factorial_mul_factorial_dvd_prod_factorial
import Submission.Work.KMTPlan.A6.ConcAux.padicValNat_prod_factorial_le
import Submission.Work.KMTPlan.A6.ConcAux.pow_dvd_mul_of_padicValNat_le
import Submission.Work.KMTPlan.A6.ConcAux.powersetCard_prod_neg_mul
import Submission.Work.KMTPlan.A6.ConcAux.dvd_eval_of_ball

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6.ConcAux

open Finset

/-! ### definitions -/

private def Vd (d : ℕ) : ℕ := ∏ j ∈ Finset.range (d + 1), j.factorial

private def Cof (d i : ℕ) : ℕ := Vd d / (i.factorial * (d - i).factorial)

private def Esym (d l i : ℕ) : ℤ :=
  ∑ t ∈ Finset.powersetCard (d - l) ((Finset.range (d + 1)).erase i), ∏ a ∈ t, (a : ℤ)

private abbrev Dp (d i : ℕ) (x₀ b : ℤ) : ℚ :=
  ∏ j ∈ (Finset.range (d + 1)).erase i,
    ((x₀ : ℚ) + (b : ℚ) * (i : ℚ) - ((x₀ : ℚ) + (b : ℚ) * (j : ℚ)))

private abbrev Ep (d l i : ℕ) (x₀ b : ℤ) : ℚ :=
  ∑ t ∈ Finset.powersetCard (d - l) ((Finset.range (d + 1)).erase i),
    ∏ a ∈ t, ((x₀ : ℚ) - ((x₀ : ℚ) + (b : ℚ) * (a : ℚ)))

private def Nval (d l : ℕ) (x₀ b : ℤ) (val : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range (d + 1),
    val i * (((-1 : ℤ) ^ (d - l)) * ((-1 : ℤ) ^ (d - i))) * (Cof d i : ℤ) * Esym d l i

/-! ### helper lemmas -/

private theorem eval_iterate_derivative_map_intCast (G : Polynomial ℤ) (l : ℕ) (x : ℤ) :
    Polynomial.eval ((x : ℤ) : ℚ) ((Polynomial.derivative^[l]) (G.map (Int.castRingHom ℚ)))
      = (((Polynomial.eval x ((Polynomial.derivative^[l]) G)) : ℤ) : ℚ) := by
  rw [Polynomial.iterate_derivative_map, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (Int.castRingHom ℚ) x

private theorem prod_erase_cast_sub (d i : ℕ) (hi : i ≤ d) (xq b : ℚ) :
    ∏ j ∈ (Finset.range (d + 1)).erase i, (xq + b * (i:ℚ) - (xq + b * (j:ℚ)))
      = b ^ d * ∏ j ∈ (Finset.range (d + 1)).erase i, ((i:ℚ) - (j:ℚ)) := by
  have hcard : ((Finset.range (d + 1)).erase i).card = d := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))]
    simp
  calc ∏ j ∈ (Finset.range (d + 1)).erase i, (xq + b * (i:ℚ) - (xq + b * (j:ℚ)))
      = ∏ j ∈ (Finset.range (d + 1)).erase i, b * ((i:ℚ) - (j:ℚ)) := by
        apply Finset.prod_congr rfl; intro j hj; ring
    _ = (∏ _j ∈ (Finset.range (d + 1)).erase i, b)
          * ∏ j ∈ (Finset.range (d + 1)).erase i, ((i:ℚ) - (j:ℚ)) := Finset.prod_mul_distrib
    _ = b ^ d * ∏ j ∈ (Finset.range (d + 1)).erase i, ((i:ℚ) - (j:ℚ)) := by
        rw [Finset.prod_const, hcard]

private theorem Dp_eq (d i : ℕ) (hi : i ≤ d) (x₀ b : ℤ) :
    Dp d i x₀ b = (b : ℚ) ^ d
      * ((-1 : ℚ) ^ (d - i) * ((i.factorial * (d - i).factorial : ℕ) : ℚ)) := by
  unfold Dp
  rw [prod_erase_cast_sub d i hi (x₀ : ℚ) (b : ℚ)]
  congr 1
  have h3 := congrArg (fun z : ℤ => (z : ℚ)) (prod_erase_range_sub_factorial d i hi)
  rw [Int.cast_prod] at h3
  push_cast at h3
  simpa only [Nat.cast_mul] using h3

private theorem Ep_eq (d l i : ℕ) (x₀ b : ℤ) :
    Ep d l i x₀ b = (-1 : ℚ) ^ (d - l) * (b : ℚ) ^ (d - l)
      * ((Esym d l i : ℤ) : ℚ) := by
  unfold Ep Esym
  rw [powersetCard_prod_neg_mul d l i x₀ b]

private theorem Vd_eq (d i : ℕ) (hi : i ≤ d) :
    (Vd d : ℚ) = ((i.factorial * (d - i).factorial : ℕ) : ℚ) * (Cof d i : ℚ) := by
  have hdvd : i.factorial * (d - i).factorial ∣ Vd d :=
    factorial_mul_factorial_dvd_prod_factorial d i hi
  have hne : (((i.factorial * (d - i).factorial : ℕ)) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.factorial_ne_zero i) (Nat.factorial_ne_zero (d - i)))
  unfold Cof
  rw [Nat.cast_div hdvd hne]
  field_simp

private theorem per_term (d l i : ℕ) (hl : l ≤ d) (hi : i ≤ d) (x₀ b : ℤ) (hb : b ≠ 0) :
    (Vd d : ℚ) * (b : ℚ)^l * (Ep d l i x₀ b / Dp d i x₀ b)
      = ((((-1 : ℤ)^(d - l)) * ((-1 : ℤ)^(d - i)) * (Cof d i : ℤ) * Esym d l i : ℤ) : ℚ) := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hA : (((i.factorial * (d - i).factorial : ℕ)) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.factorial_ne_zero i) (Nat.factorial_ne_zero (d - i)))
  have hDp_ne : Dp d i x₀ b ≠ 0 := by
    rw [Dp_eq d i hi x₀ b]
    exact mul_ne_zero (pow_ne_zero _ hbq) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hA)
  have hsplit : (b : ℚ)^d = (b : ℚ)^l * (b : ℚ)^(d - l) := by
    rw [← pow_add, Nat.add_sub_of_le hl]
  rw [← mul_div_assoc]
  refine (div_eq_iff hDp_ne).mpr ?_
  rw [Dp_eq d i hi x₀ b, Ep_eq d l i x₀ b, Vd_eq d i hi, hsplit]
  push_cast
  rcases Nat.even_or_odd (d - i) with he | ho
  · rw [he.neg_one_pow]; ring
  · rw [ho.neg_one_pow]; ring

private theorem key_identity (G : Polynomial ℤ) {d : ℕ} (hd : G.natDegree = d) {l : ℕ} (hl : l ≤ d)
    (x₀ : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (Vd d : ℚ) * (b : ℚ) ^ l
        * (((Polynomial.eval x₀ ((Polynomial.derivative^[l]) G) : ℤ) : ℚ))
      = (l.factorial : ℚ) * ((Nval d l x₀ b (fun i => G.eval (x₀ + b * i)) : ℤ) : ℚ) := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hvs : Set.InjOn (fun i : ℕ => (x₀ : ℚ) + (b : ℚ) * (i : ℚ))
      (↑(Finset.range (d + 1)) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    have h : (b : ℚ) * (i : ℚ) = (b : ℚ) * (j : ℚ) := by
      simpa using add_left_cancel hij
    have h2 : (i : ℚ) = (j : ℚ) := mul_left_cancel₀ hbq h
    exact_mod_cast h2
  have hP : (G.map (Int.castRingHom ℚ)).degree < ((Finset.range (d + 1)).card : WithBot ℕ) := by
    rw [Finset.card_range]
    calc (G.map (Int.castRingHom ℚ)).degree
        ≤ ((G.map (Int.castRingHom ℚ)).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (d : WithBot ℕ) := by
          rw [← hd]
          exact_mod_cast Polynomial.natDegree_map_le
      _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
  have hk : l < (Finset.range (d + 1)).card := by
    rw [Finset.card_range]; exact Nat.lt_succ_of_le hl
  have hForm := Lagrange.eval_iterate_derivative_eq_sum (s := Finset.range (d + 1))
      (v := fun i : ℕ => (x₀ : ℚ) + (b : ℚ) * (i : ℚ)) hvs (P := G.map (Int.castRingHom ℚ))
      hP (k := l) hk (x₀ : ℚ)
  rw [eval_iterate_derivative_map_intCast] at hForm
  have hcard : (Finset.range (d + 1)).card - (l + 1) = d - l := by
    rw [Finset.card_range]; omega
  rw [hcard] at hForm
  have hVd_ne : (Vd d : ℚ) ≠ 0 := by
    have h : Vd d ≠ 0 := by
      unfold Vd
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.factorial_ne_zero j)
    exact_mod_cast h
  have hX : ((Vd d : ℚ) * (b : ℚ)^l) ≠ 0 := mul_ne_zero hVd_ne (pow_ne_zero _ hbq)
  have hsum : (∑ i ∈ Finset.range (d + 1),
        (Polynomial.eval ((x₀:ℚ) + (b:ℚ) * (i:ℚ)) (G.map (Int.castRingHom ℚ))
            / Dp d i x₀ b) * Ep d l i x₀ b)
      = ((Nval d l x₀ b (fun i => G.eval (x₀ + b * i)) : ℤ) : ℚ) / ((Vd d : ℚ) * (b : ℚ)^l) := by
    simp only [Nval, Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hval : Polynomial.eval ((x₀:ℚ) + (b:ℚ) * (i:ℚ)) (G.map (Int.castRingHom ℚ))
        = ((G.eval (x₀ + b * i) : ℤ) : ℚ) := by
      rw [Polynomial.eval_map]
      rw [show (x₀:ℚ) + (b:ℚ) * (i:ℚ) = ((x₀ + b * i : ℤ) : ℚ) by push_cast; ring]
      exact Polynomial.eval₂_at_apply (Int.castRingHom ℚ) (x₀ + b * i)
    rw [hval]
    have hpt := per_term d l i hl hi' x₀ b hb
    have hE : Ep d l i x₀ b / Dp d i x₀ b
        = ((((-1 : ℤ)^(d - l)) * ((-1 : ℤ)^(d - i)) * (Cof d i : ℤ) * Esym d l i : ℤ) : ℚ)
            / ((Vd d : ℚ) * (b : ℚ)^l) := by
      rw [eq_div_iff hX, mul_comm]
      exact hpt
    rw [div_mul_eq_mul_div, mul_div_assoc, hE, ← mul_div_assoc]
    push_cast
    ring
  rw [hForm, hsum]
  field_simp

theorem fibre_iteratedDeriv_dvd (G : Polynomial ℤ) (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    {a : ZMod (p ^ k)} {m : ℕ} (hm : m ≤ k)
    (hball : ∀ x : ZMod (p ^ k), (p : ℤ) ^ m ∣ ((x.val : ℤ) - (a.val : ℤ)) →
        (p : ℤ) ^ k ∣ G.eval (x.val : ℤ)) :
    ∀ x : ZMod (p ^ k), (p : ℤ) ^ m ∣ ((x.val : ℤ) - (a.val : ℤ)) →
      ∀ l ≤ G.natDegree,
        (p : ℤ) ^ k ∣ (p : ℤ) ^ (l * m + (G.natDegree + 1) * padicValNat p G.natDegree.factorial) *
          ((Polynomial.derivative^[l]) G).eval (x.val : ℤ) := by
  intro x hx l hl
  generalize hd : G.natDegree = d at hl ⊢
  by_cases hg : (Polynomial.eval (x.val : ℤ) ((Polynomial.derivative^[l]) G)) = 0
  · rw [hg, mul_zero]; exact dvd_zero _
  · have hpm : ((p : ℤ) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have hballz : ∀ y : ℤ, (p : ℤ) ^ m ∣ y - (a.val : ℤ) → (p : ℤ) ^ k ∣ G.eval y :=
      fun y hy => dvd_eval_of_ball G p k m hm hball hy
    have hnode : ∀ i : ℕ, (p : ℤ) ^ k ∣ G.eval ((x.val : ℤ) + (p : ℤ) ^ m * i) := by
      intro i
      apply hballz
      have h : (x.val : ℤ) + (p : ℤ) ^ m * i - (a.val : ℤ)
          = ((x.val : ℤ) - (a.val : ℤ)) + (p : ℤ) ^ m * i := by ring
      rw [h]
      exact dvd_add hx (dvd_mul_right _ _)
    have hid := key_identity G hd hl (x.val) (b := (p : ℤ) ^ m) hpm
    have hidZ : (Vd d : ℤ) * ((p : ℤ) ^ m) ^ l
          * (Polynomial.eval (x.val : ℤ) ((Polynomial.derivative^[l]) G))
        = (l.factorial : ℤ)
          * Nval d l (x.val) ((p : ℤ) ^ m) (fun i => G.eval ((x.val : ℤ) + (p : ℤ) ^ m * i)) := by
      exact_mod_cast hid
    have hN : (p : ℤ) ^ k
        ∣ Nval d l (x.val) ((p : ℤ) ^ m) (fun i => G.eval ((x.val : ℤ) + (p : ℤ) ^ m * i)) := by
      unfold Nval
      apply Finset.dvd_sum
      intro i hi
      have h1 : (p : ℤ) ^ k ∣ G.eval ((x.val : ℤ) + (p : ℤ) ^ m * i)
          * (((-1 : ℤ) ^ (d - l)) * ((-1 : ℤ) ^ (d - i))) := dvd_mul_of_dvd_left (hnode i) _
      have h2 : (p : ℤ) ^ k ∣ G.eval ((x.val : ℤ) + (p : ℤ) ^ m * i)
          * (((-1 : ℤ) ^ (d - l)) * ((-1 : ℤ) ^ (d - i))) * (Cof d i : ℤ) :=
        dvd_mul_of_dvd_left h1 _
      exact dvd_mul_of_dvd_left h2 _
    have hpKN : (p : ℤ) ^ k ∣ (Vd d : ℤ) * ((p : ℤ) ^ m) ^ l
        * (Polynomial.eval (x.val : ℤ) ((Polynomial.derivative^[l]) G)) := by
      rw [hidZ]
      exact dvd_mul_of_dvd_right hN _
    have hVdne : Vd d ≠ 0 := by
      unfold Vd
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => Nat.factorial_ne_zero j)
    have hMnat : (((Vd d : ℤ) * ((p : ℤ) ^ m) ^ l).natAbs) = Vd d * (p ^ m) ^ l := by
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_natCast]
    have hpad : padicValNat p (((Vd d : ℤ) * ((p : ℤ) ^ m) ^ l).natAbs)
        ≤ l * m + (d + 1) * padicValNat p d.factorial := by
      rw [hMnat]
      have h1 : padicValNat p (Vd d * (p ^ m) ^ l)
          = padicValNat p (Vd d) + padicValNat p ((p ^ m) ^ l) := by
        rw [padicValNat.mul hVdne (pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))]
      rw [h1]
      have h2 : padicValNat p ((p ^ m) ^ l) = l * m := by
        rw [padicValNat.pow, padicValNat.pow, padicValNat.self (Fact.out : p.Prime).one_lt]
        ring
      rw [h2]
      have h3 : padicValNat p (Vd d) ≤ (d + 1) * padicValNat p d.factorial :=
        padicValNat_prod_factorial_le p d
      linarith
    have hMne : (Vd d : ℤ) * ((p : ℤ) ^ m) ^ l ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hVdne) (pow_ne_zero _ hpm)
    exact pow_dvd_mul_of_padicValNat_le p k (l * m + (d + 1) * padicValNat p d.factorial)
      hMne hg hpKN hpad

end Work.KMTPlan.A6.ConcAux
