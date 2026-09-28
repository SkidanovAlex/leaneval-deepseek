import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DyadicR2Defs

import Submission.Work.HP.DyadicAux.sum_collapse
import Submission.Work.HP.DyadicAux.dFib_two_le
import Submission.Work.HP.DyadicAux.dFib_four_geom
import Submission.Work.HP.DyadicAux.dFib_four_X

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP

/-! ## Elementary helpers -/

/-- Monotonicity of a function `Fin 2 → ℕ` is the comparison of its two values. -/
lemma monotone_fin2_iff (k : Fin 2 → ℕ) : Monotone k ↔ k 0 ≤ k 1 := by
  constructor
  · intro h; exact h (by decide : (0 : Fin 2) ≤ 1)
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Reindex a sum over `Fin 2 → ℕ` as a double sum over pairs. -/
lemma piFinset_fin2_sum (M : ℕ) (g : (Fin 2 → ℕ) → ℝ) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (M + 1)), g k)
      = ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1), g ![p.1, p.2] := by
  rw [Finset.sum_bij' (fun k _ => (k 0, k 1)) (fun p _ => ![p.1, p.2])]
  · intro k hk
    simp only [Finset.mem_product, Finset.mem_range, Fintype.mem_piFinset] at hk ⊢
    exact ⟨hk 0, hk 1⟩
  · intro p hp
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · simpa using (Finset.mem_product.mp hp).1
    · simpa using (Finset.mem_product.mp hp).2
  · intro k hk
    funext i; fin_cases i <;> simp
  · intro p hp
    simp
  · intro k hk
    congr 1
    funext i; fin_cases i <;> simp

/-- Exponent rewriting: `(N-1)a + (N-3)b = (N-3)(a+b) + 2a`. -/
lemma exp1 (N a b : ℕ) (hN : 3 ≤ N) : (N - 1) * a + (N - 3) * b = (N - 3) * (a + b) + 2 * a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  have h1 : 3 + m - 1 = m + 2 := by omega
  have h2 : 3 + m - 3 = m := by omega
  rw [h1, h2]; ring

/-- Exponent rewriting: `(N-1)a + (N-2)b = (N-2)(a+b) + a`. -/
lemma exp2 (N a b : ℕ) (hN : 3 ≤ N) : (N - 1) * a + (N - 2) * b = (N - 2) * (a + b) + a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  have h1 : 3 + m - 1 = m + 2 := by omega
  have h2 : 3 + m - 2 = m + 1 := by omega
  rw [h1, h2]; ring

/-- Exponent rewriting: `Na + (N-2)b = (N-2)(a+b) + 2a`. -/
lemma exp3 (N a b : ℕ) (hN : 3 ≤ N) : N * a + (N - 2) * b = (N - 2) * (a + b) + 2 * a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  have h2 : 3 + m - 2 = m + 1 := by omega
  rw [h2]; ring

/-- Exponent rewriting: `(N-3)s + s = (N-2)s`. -/
lemma expN (N s : ℕ) (hN : 3 ≤ N) : (N - 3) * s + s = (N - 2) * s := by
  have h : N - 3 + 1 = N - 2 := by omega
  calc (N - 3) * s + s = (N - 3) * s + 1 * s := by ring
    _ = ((N - 3) + 1) * s := by rw [add_mul]
    _ = (N - 2) * s := by rw [h]

lemma pow_A (N s a : ℕ) :
    (2 : ℝ) ^ ((N - 3) * s + 2 * a) = (2 : ℝ) ^ ((N - 3) * s) * (4 : ℝ) ^ a := by
  rw [pow_add, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]

lemma pow_B (N s a : ℕ) :
    (2 : ℝ) ^ ((N - 2) * s + a) = (2 : ℝ) ^ ((N - 2) * s) * (2 : ℝ) ^ a := by
  rw [pow_add]

lemma pow_C (N s a : ℕ) :
    (2 : ℝ) ^ ((N - 2) * s + 2 * a) = (2 : ℝ) ^ ((N - 2) * s) * (4 : ℝ) ^ a := by
  rw [pow_add, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]

/-! ## Reduction to pairs -/

lemma dSummand_eq_dPair (N M : ℕ) (X Y : ℝ) (a b : ℕ) (hN : 3 ≤ N) :
    dSummand N X Y M ![a, b] = dPair N X Y M a b := by
  rw [dSummand, dPair]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two, monotone_fin2_iff,
    exp1 N a b hN, exp2 N a b hN, exp3 N a b hN]

lemma dPair_eq_zero {N M : ℕ} {X Y : ℝ} {a b : ℕ} (h : M < a + b) :
    dPair N X Y M a b = 0 := by
  have hnot : ¬ (a ≤ b ∧ a + b ≤ M ∧ (2 : ℝ) ^ a ≤ 2 * X ∧ (2 : ℝ) ^ b ≤ 2 * Y) := by
    rintro ⟨-, h2, -⟩; omega
  rw [dPair, if_neg hnot]

lemma dPair_sub {N M s : ℕ} {X Y : ℝ} {a : ℕ} (hs : s ≤ M) (ha : a ≤ s) :
    dPair N X Y M a (s - a)
      = if a ≤ s - a ∧ (2 : ℝ) ^ a ≤ 2 * X ∧ (2 : ℝ) ^ (s - a) ≤ 2 * Y
        then dGeo N X Y s a else 0 := by
  have hsum : a + (s - a) = s := Nat.add_sub_of_le ha
  by_cases hc : a ≤ s - a ∧ (2 : ℝ) ^ a ≤ 2 * X ∧ (2 : ℝ) ^ (s - a) ≤ 2 * Y
  · rw [if_pos hc, dPair, if_pos]
    · rw [hsum]; rfl
    · exact ⟨hc.1, by rw [hsum]; exact hs, hc.2.1, hc.2.2⟩
  · rw [if_neg hc, dPair, if_neg]
    rintro ⟨h1, h2, h3, h4⟩
    exact hc ⟨h1, h3, h4⟩

lemma range_dPair_eq_dFib (N M s : ℕ) (X Y : ℝ) (hs : s ≤ M) :
    (∑ a ∈ Finset.range (s + 1), dPair N X Y M a (s - a))
      = ∑ a ∈ dFib s X Y, dGeo N X Y s a := by
  rw [dFib, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have ha' : a ≤ s := by
    rw [Finset.mem_range] at ha; omega
  exact dPair_sub hs ha'

/-! ## Bounding the fibre sums -/

lemma fib_geo_le (N s : ℕ) (X Y : ℝ) (hN : 3 ≤ N) (hX : 0 ≤ X) :
    ∑ a ∈ dFib s X Y, dGeo N X Y s a ≤ (32 / 3) * X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) := by
  have hA : ∑ a ∈ dFib s X Y, X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s + 2 * a)
      = X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s) * ∑ a ∈ dFib s X Y, (4 : ℝ) ^ a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by rw [pow_A]; ring)
  have hB : ∑ a ∈ dFib s X Y, X * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s + a)
      = X * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) * ∑ a ∈ dFib s X Y, (2 : ℝ) ^ a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by rw [pow_B]; ring)
  have hC : ∑ a ∈ dFib s X Y, Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s + 2 * a)
      = Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) * ∑ a ∈ dFib s X Y, (4 : ℝ) ^ a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by rw [pow_C]; ring)
  have hsplit : ∑ a ∈ dFib s X Y, dGeo N X Y s a
      = (∑ a ∈ dFib s X Y, X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s + 2 * a))
        + (∑ a ∈ dFib s X Y, X * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s + a))
        + (∑ a ∈ dFib s X Y, Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s + 2 * a)) := by
    simp only [dGeo, Finset.sum_add_distrib]
  have hZ0 : 0 ≤ X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) := by positivity
  have h4g := DyadicAux.dFib_four_geom s X Y
  have h2l := DyadicAux.dFib_two_le s X Y hX
  have h4X := DyadicAux.dFib_four_X s X Y
  have e1 : X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s) * (2 : ℝ) ^ s
      = X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) := by
    rw [show X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s) * (2 : ℝ) ^ s
        = X ^ 2 * Y ^ 2 * ((2 : ℝ) ^ ((N - 3) * s) * (2 : ℝ) ^ s) by ring]
    rw [← pow_add, expN N s hN]
  have ha : X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s) * (∑ a ∈ dFib s X Y, (4 : ℝ) ^ a)
      ≤ X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s) * ((4 / 3) * (2 : ℝ) ^ s) :=
    mul_le_mul_of_nonneg_left h4g (by positivity)
  have han : X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s) * ((4 / 3) * (2 : ℝ) ^ s)
      = (4 / 3) * (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s)) := by
    rw [← e1]; ring
  have hbn' : X * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) * (∑ a ∈ dFib s X Y, (2 : ℝ) ^ a)
      ≤ X * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) * (4 * X) :=
    mul_le_mul_of_nonneg_left h2l (by positivity)
  have hbn : X * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) * (4 * X)
      = 4 * (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s)) := by ring
  have hcn' : Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) * (∑ a ∈ dFib s X Y, (4 : ℝ) ^ a)
      ≤ Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) * ((16 / 3) * X ^ 2) :=
    mul_le_mul_of_nonneg_left h4X (by positivity)
  have hcn : Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) * ((16 / 3) * X ^ 2)
      = (16 / 3) * (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s)) := by ring
  have hfin : (32 / 3) * X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s)
      = (32 / 3) * (X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s)) := by ring
  rw [hsplit, hA, hB, hC, hfin]
  linarith [ha, han, hbn', hbn, hcn', hcn]

/-! ## The geometric sum over `s` -/

lemma geom_N_sum (N M : ℕ) (hN : 3 ≤ N) :
    ∑ s ∈ Finset.range (M + 1), (2 : ℝ) ^ ((N - 2) * s)
      ≤ (2 : ℝ) ^ (N - 2) * (2 : ℝ) ^ ((N - 2) * M) := by
  set r : ℝ := (2 : ℝ) ^ (N - 2) with hr
  have hr1 : 1 < r := by
    rw [hr]
    have h1 : (1:ℕ) ≤ N - 2 := by omega
    have h2 : (2:ℝ)^(1:ℕ) ≤ (2:ℝ)^(N-2) := pow_le_pow_right₀ (by norm_num) h1
    have h3 : (2:ℝ) ≤ (2:ℝ)^(N-2) := by simpa using h2
    exact lt_of_lt_of_le (by norm_num) h3
  have hr2 : 2 ≤ r := by
    rw [hr]
    have h1 : (1:ℕ) ≤ N - 2 := by omega
    have h2 : (2:ℝ)^(1:ℕ) ≤ (2:ℝ)^(N-2) := pow_le_pow_right₀ (by norm_num) h1
    simpa using h2
  have hsum : ∑ s ∈ Finset.range (M + 1), (2 : ℝ) ^ ((N - 2) * s)
      = ∑ s ∈ Finset.range (M + 1), r ^ s := by
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [pow_mul, hr]
  have hmain : ∑ s ∈ Finset.range (M + 1), r ^ s = (r ^ (M + 1) - 1) / (r - 1) :=
    geom_sum_eq (ne_of_gt hr1) (M + 1)
  have hpowM : (2 : ℝ) ^ ((N - 2) * M) = r ^ M := by rw [pow_mul, ← hr]
  rw [hsum, hmain, hpowM]
  have hA : (0:ℝ) ≤ r ^ (M + 1) := pow_nonneg (by linarith) _
  have e1 : (r ^ (M + 1) - 1) / (r - 1) ≤ r ^ (M + 1) / (r - 1) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have e2 : r ^ (M + 1) / (r - 1) ≤ r ^ (M + 1) / 1 :=
    div_le_div_of_nonneg_left hA one_pos (by linarith)
  have e3 : r ^ (M + 1) / 1 = r * r ^ M := by rw [div_one, pow_succ]; ring
  calc (r ^ (M + 1) - 1) / (r - 1) ≤ r ^ (M + 1) / (r - 1) := e1
    _ ≤ r ^ (M + 1) / 1 := e2
    _ = r * r ^ M := e3

lemma pow_le_ceil (N : ℕ) (L : ℝ) (hL : 0 ≤ L) (hN : 2 ≤ N) :
    (2 : ℝ) ^ ((N - 2) * ⌈L⌉₊) ≤ (2 : ℝ) ^ (N - 2) * (2 : ℝ) ^ ((N - 2) * L) := by
  have hMlt : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL
  have hcast : (((N - 2) * ⌈L⌉₊ : ℕ) : ℝ) ≤ ((N - 2 : ℕ) : ℝ) * L + ((N - 2 : ℕ) : ℝ) := by
    push_cast
    have h0 : (0:ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by positivity
    nlinarith [hMlt, h0]
  calc (2 : ℝ) ^ ((N - 2) * ⌈L⌉₊)
      = (2 : ℝ) ^ (((N - 2) * ⌈L⌉₊ : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
    _ ≤ (2 : ℝ) ^ (((N - 2 : ℕ) : ℝ) * L + ((N - 2 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hcast
    _ = (2 : ℝ) ^ (((N - 2 : ℕ) : ℝ) * L) * (2 : ℝ) ^ ((N - 2 : ℕ) : ℝ) :=
        Real.rpow_add (by norm_num) _ _
    _ = (2 : ℝ) ^ ((N - 2) * L) * (2 : ℝ) ^ (N - 2) := by
        rw [Real.rpow_natCast, Nat.cast_sub hN]
        norm_num
    _ = (2 : ℝ) ^ (N - 2) * (2 : ℝ) ^ ((N - 2) * L) := by ring

/-! ## The main theorem -/

theorem dyadic_sum_r2 (N : ℕ) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y L : ℝ), 1 ≤ X → 1 ≤ Y → 0 ≤ L →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (⌈L⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈L⌉₊ ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
          X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 1) * k 0 + (N - 3) * k 1)
            + X * Y ^ 2 * (2 : ℝ) ^ ((N - 1) * k 0 + (N - 2) * k 1)
            + Y ^ 2 * (2 : ℝ) ^ (N * k 0 + (N - 2) * k 1)
        else 0))
      ≤ C * X ^ 2 * Y ^ 2 * 2 ^ ((N - 2) * L) := by
  refine ⟨(32 / 3) * (2 : ℝ) ^ (2 * (N - 2)), by positivity, ?_⟩
  intro X Y L hX hY hL
  set M : ℕ := ⌈L⌉₊ with hM
  have hX0 : (0:ℝ) ≤ X := le_trans zero_le_one hX
  show (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (M + 1)), dSummand N X Y M k)
      ≤ ((32 / 3) * (2 : ℝ) ^ (2 * (N - 2))) * X ^ 2 * Y ^ 2 * 2 ^ ((N - 2) * L)
  have hstep1 : (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (M + 1)), dSummand N X Y M k)
      = ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), dPair N X Y M a b := by
    rw [piFinset_fin2_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
    exact dSummand_eq_dPair N M X Y a b hN
  have hstep2 := DyadicAux.sum_collapse (fun a b => dPair N X Y M a b) M
    (fun a b h => dPair_eq_zero (N:=N) (X:=X) (Y:=Y) h)
  have hstep3 : (∑ s ∈ Finset.range (M + 1), ∑ a ∈ Finset.range (s + 1), dPair N X Y M a (s - a))
      = ∑ s ∈ Finset.range (M + 1), ∑ a ∈ dFib s X Y, dGeo N X Y s a := by
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' : s ≤ M := by
      simp only [Finset.mem_range] at hs; omega
    exact range_dPair_eq_dFib N M s X Y hs'
  have hstep4 : (∑ s ∈ Finset.range (M + 1), ∑ a ∈ dFib s X Y, dGeo N X Y s a)
      ≤ ∑ s ∈ Finset.range (M + 1), (32 / 3) * X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) := by
    refine Finset.sum_le_sum (fun s hs => ?_)
    exact fib_geo_le N s X Y hN hX0
  have hstep5 : (∑ s ∈ Finset.range (M + 1), (32 / 3) * X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s))
      = (32 / 3) * X ^ 2 * Y ^ 2 * ∑ s ∈ Finset.range (M + 1), (2 : ℝ) ^ ((N - 2) * s) := by
    rw [Finset.mul_sum]
  have hgeo := geom_N_sum N M hN
  have hpow : (2 : ℝ) ^ ((N - 2) * M) ≤ (2 : ℝ) ^ (N - 2) * (2 : ℝ) ^ ((N - 2) * L) := by
    rw [hM]
    exact pow_le_ceil N L hL (by omega : 2 ≤ N)
  have hX0' : (0:ℝ) ≤ (32 / 3) * X ^ 2 * Y ^ 2 := by positivity
  have key : (32 / 3) * X ^ 2 * Y ^ 2 * (∑ s ∈ Finset.range (M + 1), (2 : ℝ) ^ ((N - 2) * s))
      ≤ (32 / 3) * X ^ 2 * Y ^ 2
          * ((2 : ℝ) ^ (N - 2) * ((2 : ℝ) ^ (N - 2) * (2 : ℝ) ^ ((N - 2) * L))) := by
    refine mul_le_mul_of_nonneg_left ?_ hX0'
    refine le_trans hgeo ?_
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hA : (32 / 3) * X ^ 2 * Y ^ 2
        * ((2 : ℝ) ^ (N - 2) * ((2 : ℝ) ^ (N - 2) * (2 : ℝ) ^ ((N - 2) * L)))
      = ((32 / 3) * (2 : ℝ) ^ (2 * (N - 2))) * X ^ 2 * Y ^ 2 * 2 ^ ((N - 2) * L) := by
    rw [two_mul, pow_add]; ring
  calc (∑ k ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (M + 1)), dSummand N X Y M k)
      = ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), dPair N X Y M a b := hstep1
    _ = ∑ s ∈ Finset.range (M + 1), ∑ a ∈ Finset.range (s + 1), dPair N X Y M a (s - a) := hstep2
    _ = ∑ s ∈ Finset.range (M + 1), ∑ a ∈ dFib s X Y, dGeo N X Y s a := hstep3
    _ ≤ ∑ s ∈ Finset.range (M + 1), (32 / 3) * X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s) := hstep4
    _ = (32 / 3) * X ^ 2 * Y ^ 2 * ∑ s ∈ Finset.range (M + 1), (2 : ℝ) ^ ((N - 2) * s) := hstep5
    _ ≤ (32 / 3) * X ^ 2 * Y ^ 2
          * ((2 : ℝ) ^ (N - 2) * ((2 : ℝ) ^ (N - 2) * (2 : ℝ) ^ ((N - 2) * L))) := key
    _ = ((32 / 3) * (2 : ℝ) ^ (2 * (N - 2))) * X ^ 2 * Y ^ 2 * 2 ^ ((N - 2) * L) := hA

end Work.HP
