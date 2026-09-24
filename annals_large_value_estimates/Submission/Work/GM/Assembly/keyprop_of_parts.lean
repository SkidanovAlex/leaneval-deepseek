import Mathlib
import Submission.GM.Interfaces

/-! Guidance from the project lead (the requester):

This is GM §12 (proof of Prop 3.1): pure real-exponent algebra, no analysis.
Paper: REFS/GuthMaynard_2405.20552.txt, Section 12 (and Prop 11.2 = Prop 10.1 + Prop 11.1).
-/

open Complex Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Assembly

open Submission.GM Submission.LargeValues

/-! ## Elementary real-exponent helpers -/

/-- `(a+b+c)^p ≤ a^p + b^p + c^p` for `0 ≤ p ≤ 1`, `a,b,c ≥ 0`. -/
lemma rpow_add3_le {p a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : (a + b + c) ^ p ≤ a ^ p + b ^ p + c ^ p := by
  have h1 : (a + b + c) ^ p = ((a + b) + c) ^ p := by ring_nf
  rw [h1]
  have h2 : ((a + b) + c) ^ p ≤ (a + b) ^ p + c ^ p :=
    Real.rpow_add_le_add_rpow (by linarith) hc hp0 hp1
  have h3 : (a + b) ^ p ≤ a ^ p + b ^ p := Real.rpow_add_le_add_rpow ha hb hp0 hp1
  linarith

/-- `x^a * x^b = x^(a+b)` for `0 < x`. -/
lemma rpow_mul2 {x : ℝ} (hx : 0 < x) (a b : ℝ) : x ^ a * x ^ b = x ^ (a + b) :=
  (Real.rpow_add hx a b).symm

/-- `x^a * x^b * x^c = x^(a+b+c)` for `0 < x`. -/
lemma rpow_mul3 {x : ℝ} (hx : 0 < x) (a b c : ℝ) : x ^ a * x ^ b * x ^ c = x ^ (a + b + c) := by
  rw [rpow_mul2 hx a b, rpow_mul2 hx (a + b) c]

/-- `x * x^a = x^(1+a)` for `0 < x`. -/
lemma rpow_self_mul {x : ℝ} (hx : 0 < x) (a : ℝ) : x * x ^ a = x ^ (1 + a) := by
  rw [Real.rpow_add hx 1 a, Real.rpow_one]

/-- `x^a * x = x^(a+1)` for `0 < x`. -/
lemma rpow_mul_self {x : ℝ} (hx : 0 < x) (a : ℝ) : x ^ a * x = x ^ (a + 1) := by
  rw [mul_comm, rpow_self_mul hx a, show 1 + a = a + 1 by ring]

/-- Raise a monomial to a power. -/
lemma rpow_monomial {C N V b f r : ℝ} (hN : 0 < N) (hV : 0 < V) (hC : 0 ≤ C) :
    (C * N ^ b * V ^ f) ^ r = C ^ r * N ^ (b * r) * V ^ (f * r) := by
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hN.le b r, ← Real.rpow_mul hV.le f r]

/-- Solving `X ≤ K * X^a` for `a < 1`. -/
lemma le_of_le_mul_rpow {X K a : ℝ} (hX : 0 ≤ X) (hK : 0 ≤ K) (ha : a < 1)
    (h : X ≤ K * X ^ a) : X ≤ K ^ (1 / (1 - a)) := by
  rcases eq_or_lt_of_le hX with hX0 | hXpos
  · rw [← hX0]; exact Real.rpow_nonneg hK _
  · have h1a : 0 < 1 - a := by linarith
    have hXa : 0 < X ^ a := Real.rpow_pos_of_pos hXpos a
    have hsplit : X ^ (1 - a) * X ^ a = X := by
      rw [← Real.rpow_add hXpos, show 1 - a + a = 1 by ring, Real.rpow_one]
    have hle : X ^ (1 - a) ≤ K := by
      have h'' : X ^ (1 - a) * X ^ a ≤ K * X ^ a := by rw [hsplit]; exact h
      exact le_of_mul_le_mul_right h'' hXa
    calc X = (X ^ (1 - a)) ^ (1 / (1 - a)) := by
          rw [← Real.rpow_mul (le_of_lt hXpos), mul_one_div, div_self (ne_of_gt h1a),
            Real.rpow_one]
      _ ≤ K ^ (1 / (1 - a)) := Real.rpow_le_rpow (Real.rpow_nonneg hX _) hle (by positivity)

/-- `A ≤ N^η` for all large `N` (absorption of constants). -/
theorem nat_le_rpow_ge (A : ℝ) (η : ℝ) (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → A ≤ (N : ℝ) ^ η := by
  by_cases hA1 : A ≤ 1
  · refine ⟨1, fun N hN => ?_⟩
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hle : (1 : ℝ) ^ η ≤ (N : ℝ) ^ η := Real.rpow_le_rpow zero_le_one hN1 hη.le
    rw [Real.one_rpow] at hle
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_gt (A ^ (1 / η))
    refine ⟨n, fun N hN => ?_⟩
    have hNn : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hgt : A ^ (1 / η) < (N : ℝ) := lt_of_lt_of_le hn hNn
    have hcpos : (0 : ℝ) ≤ A ^ (1 / η) := Real.rpow_nonneg hA _
    have hlt : (A ^ (1 / η)) ^ η < (N : ℝ) ^ η := Real.rpow_lt_rpow hcpos hgt hη
    have heq : (A ^ (1 / η)) ^ η = A := by
      rw [← Real.rpow_mul hA, one_div, inv_mul_cancel₀ hη.ne', Real.rpow_one]
    rw [heq] at hlt
    linarith

/-- Auxiliary: for `1 ≤ N` and `V ∈ [N^{7/10}, N^{4/5}]`, if both endpoint linear forms
`(b - 18/5) + (f+4)*s` are `≤ ε/4` for `s = 7/10` and `s = 4/5`, then
`N^(b-18/5) * V^(f+4) ≤ N^(ε/4)`. -/
theorem monomial_bound_aux {N V b f ε : ℝ} (hN : 1 ≤ N) (hV0 : 0 < V)
    (hVlo : N ^ (7 / 10 : ℝ) ≤ V) (hVhi : V ≤ N ^ (4 / 5 : ℝ))
    (h7 : (b - 18 / 5) + (f + 4) * (7 / 10) ≤ ε / 4)
    (h45 : (b - 18 / 5) + (f + 4) * (4 / 5) ≤ ε / 4) :
    N ^ (b - 18 / 5) * V ^ (f + 4) ≤ N ^ (ε / 4) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNnn : 0 ≤ N := le_of_lt hNpos
  have hVnn : 0 ≤ V := le_of_lt hV0
  by_cases hf4 : 0 ≤ f + 4
  · have hVp : V ^ (f + 4) ≤ (N ^ (4 / 5 : ℝ)) ^ (f + 4) :=
      Real.rpow_le_rpow hVnn hVhi hf4
    rw [← Real.rpow_mul hNnn (4 / 5 : ℝ) (f + 4)] at hVp
    have h1 : N ^ (b - 18 / 5) * V ^ (f + 4)
        ≤ N ^ (b - 18 / 5) * N ^ ((4 / 5 : ℝ) * (f + 4)) :=
      mul_le_mul_of_nonneg_left hVp (Real.rpow_nonneg hNnn _)
    rw [← Real.rpow_add hNpos] at h1
    refine le_trans h1 (Real.rpow_le_rpow_of_exponent_le hN ?_)
    linarith [h45]
  · have hf4' : f + 4 < 0 := not_le.mp hf4
    have hVp : V ^ (f + 4) ≤ (N ^ (7 / 10 : ℝ)) ^ (f + 4) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNpos _) hVlo (le_of_lt hf4')
    rw [← Real.rpow_mul hNnn (7 / 10 : ℝ) (f + 4)] at hVp
    have h1 : N ^ (b - 18 / 5) * V ^ (f + 4)
        ≤ N ^ (b - 18 / 5) * N ^ ((7 / 10 : ℝ) * (f + 4)) :=
      mul_le_mul_of_nonneg_left hVp (Real.rpow_nonneg hNnn _)
    rw [← Real.rpow_add hNpos] at h1
    refine le_trans h1 (Real.rpow_le_rpow_of_exponent_le hN ?_)
    linarith [h7]

/-- Comparison of a monomial `C·N^b·V^f` with the target `N^ε · N^{18/5} · V^{-4}`. -/
theorem monomial_bound {N V b f C ε : ℝ} (hN : 1 ≤ N) (hV0 : 0 < V)
    (hVlo : N ^ (7 / 10 : ℝ) ≤ V) (hVhi : V ≤ N ^ (4 / 5 : ℝ)) (hε : 0 < ε)
    (hC : 0 ≤ C) (hCε : C ≤ N ^ (ε / 4))
    (h7 : (b - 18 / 5) + (f + 4) * (7 / 10) ≤ ε / 4)
    (h45 : (b - 18 / 5) + (f + 4) * (4 / 5) ≤ ε / 4) :
    C * N ^ b * V ^ f ≤ N ^ ε * N ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNnn : 0 ≤ N := le_of_lt hNpos
  have hVnn : 0 ≤ V := le_of_lt hV0
  have hK : N ^ (b - 18 / 5) * V ^ (f + 4) ≤ N ^ (ε / 4) :=
    monomial_bound_aux hN hV0 hVlo hVhi h7 h45
  have h2 : C * N ^ (b - 18 / 5) * V ^ (f + 4) ≤ N ^ ε := by
    have h3 : C * (N ^ (b - 18 / 5) * V ^ (f + 4)) ≤ N ^ (ε / 4) * N ^ (ε / 4) :=
      mul_le_mul hCε hK (mul_nonneg (Real.rpow_nonneg hNnn _) (Real.rpow_nonneg hVnn _))
        (Real.rpow_nonneg hNnn _)
    have h4 : N ^ (ε / 4) * N ^ (ε / 4) ≤ N ^ ε := by
      rw [← Real.rpow_add hNpos]
      exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    calc C * N ^ (b - 18 / 5) * V ^ (f + 4)
        = C * (N ^ (b - 18 / 5) * V ^ (f + 4)) := by ring
      _ ≤ N ^ (ε / 4) * N ^ (ε / 4) := h3
      _ ≤ N ^ ε := h4
  have hNb : N ^ b = N ^ (18 / 5 : ℝ) * N ^ (b - 18 / 5) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hVf : V ^ f = V ^ (f + 4) * V ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hV0]; congr 1; ring
  calc C * N ^ b * V ^ f
      = N ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) * (C * N ^ (b - 18 / 5) * V ^ (f + 4)) := by
        rw [hNb, hVf]; ring
    _ ≤ N ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) * N ^ ε :=
        mul_le_mul_of_nonneg_left h2
          (mul_nonneg (Real.rpow_nonneg hNnn _) (Real.rpow_nonneg hVnn _))
    _ = N ^ ε * N ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) := by ring

/-- Constant absorption: `(a · b^{1/3} · c^{1/6})^r ≤ G^6` for `r ≤ 3` and `a,b,c ≤ G`. -/
theorem const_bound {G a b c r : ℝ} (hG : 1 ≤ G) (ha : 0 ≤ a) (haG : a ≤ G)
    (hb : 0 ≤ b) (hbG : b ≤ G) (hc : 0 ≤ c) (hcG : c ≤ G)
    (hr : 0 ≤ r) (hr3 : r ≤ 3) :
    (a * b ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ)) ^ r ≤ G ^ (6 : ℝ) := by
  have hG0 : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hb13 : b ^ (1 / 3 : ℝ) ≤ G ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hb hbG (by norm_num)
  have hc16 : c ^ (1 / 6 : ℝ) ≤ G ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow hc hcG (by norm_num)
  have hbnn : 0 ≤ b ^ (1 / 3 : ℝ) := Real.rpow_nonneg hb _
  have hcnn : 0 ≤ c ^ (1 / 6 : ℝ) := Real.rpow_nonneg hc _
  have h0 : 0 ≤ a * b ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) :=
    mul_nonneg (mul_nonneg ha hbnn) hcnn
  have hprod : a * b ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) ≤ G ^ (3 / 2 : ℝ) := by
    have h1 : a * b ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) ≤ G * G ^ (1 / 3 : ℝ) * G ^ (1 / 6 : ℝ) :=
      mul_le_mul (mul_le_mul haG hb13 hbnn (le_of_lt hG0)) hc16 hcnn (by positivity)
    have h2 : G * G ^ (1 / 3 : ℝ) * G ^ (1 / 6 : ℝ) = G ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + (1 / 3 + 1 / 6) by norm_num, Real.rpow_add hG0,
        Real.rpow_add hG0, Real.rpow_one]
      ring
    linarith [h1, h2.symm.le, h2.le]
  have hpow : (a * b ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ)) ^ r ≤ (G ^ (3 / 2 : ℝ)) ^ r :=
    Real.rpow_le_rpow h0 hprod hr
  have h2 : (G ^ (3 / 2 : ℝ)) ^ r ≤ G ^ (6 : ℝ) := by
    have h3 : (G ^ (3 / 2 : ℝ)) ^ r = G ^ ((3 / 2 : ℝ) * r) :=
      (Real.rpow_mul hG0.le (3 / 2 : ℝ) r).symm
    rw [h3]
    exact Real.rpow_le_rpow_of_exponent_le hG (by linarith)
  linarith [hpow, h2]

/-- Root extraction and comparison: if `C ≤ N^{ε/4}` and the endpoint exponent inequalities
hold, then `(18 · C · N^b · V^f)^r ≤ N^ε · N^{18/5} · V^{-4}`. -/
theorem root_bound {N V ε C b f r : ℝ} (hN : 1 ≤ N) (hV0 : 0 < V)
    (hVlo : N ^ (7 / 10 : ℝ) ≤ V) (hVhi : V ≤ N ^ (4 / 5 : ℝ)) (hε : 0 < ε)
    (hC : 0 ≤ C) (hCε : (18 : ℝ) ^ r * C ^ r ≤ N ^ (ε / 4))
    (h7 : (b * r - 18 / 5) + (f * r + 4) * (7 / 10) ≤ ε / 4)
    (h45 : (b * r - 18 / 5) + (f * r + 4) * (4 / 5) ≤ ε / 4) :
    (18 * (C * N ^ b * V ^ f)) ^ r ≤ N ^ ε * N ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hVnn : 0 ≤ V := le_of_lt hV0
  have hprod0 : 0 ≤ C * N ^ b * V ^ f :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hNpos.le _)) (Real.rpow_nonneg hVnn _)
  have hstep : (18 * (C * N ^ b * V ^ f)) ^ r = (18 : ℝ) ^ r * C ^ r * N ^ (b * r) * V ^ (f * r) := by
    rw [Real.mul_rpow (by norm_num) hprod0, rpow_monomial hNpos hV0 hC]
    ring
  rw [hstep]
  exact monomial_bound hN hV0 hVlo hVhi hε
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hC _)) hCε h7 h45

/-- Variant of `root_bound` taking the definitions of `K` and of the target as hypotheses,
so that no large expression has to be unfolded during unification. -/
theorem root_bound_def {K C N V b f r ε B : ℝ} (hN : 1 ≤ N) (hV0 : 0 < V)
    (hVlo : N ^ (7 / 10 : ℝ) ≤ V) (hVhi : V ≤ N ^ (4 / 5 : ℝ)) (hε : 0 < ε)
    (hB : B = N ^ ε * N ^ (18 / 5 : ℝ) * V ^ (-4 : ℝ)) (hK : K = C * N ^ b * V ^ f)
    (hC : 0 ≤ C) (hCε : (18 : ℝ) ^ r * C ^ r ≤ N ^ (ε / 4))
    (h7 : (b * r - 18 / 5) + (f * r + 4) * (7 / 10) ≤ ε / 4)
    (h45 : (b * r - 18 / 5) + (f * r + 4) * (4 / 5) ≤ ε / 4) :
    (18 * K) ^ r ≤ B := by
  rw [hB, hK]
  exact root_bound hN hV0 hVlo hVhi hε hC hCε h7 h45

/-- The term estimate used in the final bootstrap: `K · X^a ≤ X/(2n)` once
`(2 n K)^{1/(1-a)} ≤ B < X`. -/
theorem term_bound {X B K a n : ℝ} (hX : 0 < X) (hK : 0 ≤ K) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hn : 0 < n) (hB : (2 * n * K) ^ (1 / (1 - a)) ≤ B) (hBX : B < X) :
    K * X ^ a < X / (2 * n) := by
  have h1a : 0 < 1 - a := by linarith
  have hc0 : 0 ≤ 2 * n * K := by positivity
  have hlt : 2 * n * K < X ^ (1 - a) := by
    have h := Real.rpow_lt_rpow (Real.rpow_nonneg hc0 _) (lt_of_le_of_lt hB hBX) h1a
    rw [← Real.rpow_mul hc0] at h
    rw [show (1 / (1 - a)) * (1 - a) = 1 by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt h1a)], Real.rpow_one] at h
    exact h
  have hXa : 0 < X ^ a := Real.rpow_pos_of_pos hX a
  have hsplit : X ^ (1 - a) * X ^ a = X := by
    rw [← Real.rpow_add hX, show 1 - a + a = 1 by ring, Real.rpow_one]
  have h2n : 0 < 2 * n := by linarith
  have hKlt : K < X ^ (1 - a) / (2 * n) := by
    rw [lt_div_iff₀ h2n]
    linarith
  calc K * X ^ a < (X ^ (1 - a) / (2 * n)) * X ^ a :=
        mul_lt_mul_of_pos_right hKlt hXa
    _ = X / (2 * n) := by rw [div_mul_eq_mul_div, hsplit]


lemma rpow_mul2_nn {x : ℝ} (hx : 0 ≤ x) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    x ^ a * x ^ b = x ^ (a + b) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [Real.zero_rpow ha.ne', Real.zero_rpow hb.ne', Real.zero_rpow (by positivity : a + b ≠ 0)]
    ring
  · exact rpow_mul2 h a b

/-- `a · b^{1/3} · c^{1/6} ≤ G^{3/2}` when `a, b, c ≤ G` and `1 ≤ G`. -/
theorem const_le_G32 {G a b c : ℝ} (hG : 1 ≤ G) (ha : 0 ≤ a) (haG : a ≤ G)
    (hb : 0 ≤ b) (hbG : b ≤ G) (hc : 0 ≤ c) (hcG : c ≤ G) :
    a * b ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) ≤ G ^ (3 / 2 : ℝ) := by
  have hG0 : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hb13 : b ^ (1 / 3 : ℝ) ≤ G ^ (1 / 3 : ℝ) := Real.rpow_le_rpow hb hbG (by norm_num)
  have hc16 : c ^ (1 / 6 : ℝ) ≤ G ^ (1 / 6 : ℝ) := Real.rpow_le_rpow hc hcG (by norm_num)
  have hbnn : 0 ≤ b ^ (1 / 3 : ℝ) := Real.rpow_nonneg hb _
  have hcnn : 0 ≤ c ^ (1 / 6 : ℝ) := Real.rpow_nonneg hc _
  have h1 : a * b ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) ≤ G * G ^ (1 / 3 : ℝ) * G ^ (1 / 6 : ℝ) :=
    mul_le_mul (mul_le_mul haG hb13 hbnn (le_of_lt hG0)) hc16 hcnn (by positivity)
  have h2 : G * G ^ (1 / 3 : ℝ) * G ^ (1 / 6 : ℝ) = G ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + (1 / 3 + 1 / 6) by norm_num, Real.rpow_add hG0,
      Real.rpow_add hG0, Real.rpow_one]
    ring
  linarith [h1, h2.le]

/-- `(18)^r K^r ≤ N^{ε/4}` when `K ≤ G^{3/2}`, `r ≤ 3` and `18^3 G^6 ≤ N^{ε/4}`. -/
theorem const_bound' {N K G ε r : ℝ} (hG : 1 ≤ G) (hK : 0 ≤ K) (hKG : K ≤ G ^ (3 / 2 : ℝ))
    (hNc : (18 : ℝ) ^ (3 : ℝ) * G ^ (6 : ℝ) ≤ N ^ (ε / 4)) (hr : 0 ≤ r) (hr3 : r ≤ 3) :
    (18 : ℝ) ^ r * K ^ r ≤ N ^ (ε / 4) := by
  have hG0 : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hGnn : 0 ≤ G := le_of_lt hG0
  have h1 : (18 : ℝ) ^ r ≤ (18 : ℝ) ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hr3
  have h2 : K ^ r ≤ (G ^ (3 / 2 : ℝ)) ^ r := Real.rpow_le_rpow hK hKG hr
  have h3 : (G ^ (3 / 2 : ℝ)) ^ r ≤ G ^ (6 : ℝ) := by
    have h3' : (G ^ (3 / 2 : ℝ)) ^ r = G ^ ((3 / 2 : ℝ) * r) :=
      (Real.rpow_mul hGnn (3 / 2 : ℝ) r).symm
    rw [h3']
    exact Real.rpow_le_rpow_of_exponent_le hG (by linarith)
  have hKr : 0 ≤ K ^ r := Real.rpow_nonneg hK _
  calc (18 : ℝ) ^ r * K ^ r ≤ (18 : ℝ) ^ (3 : ℝ) * G ^ (6 : ℝ) :=
        mul_le_mul h1 (le_trans h2 h3) hKr (Real.rpow_nonneg (by norm_num) _)
    _ ≤ N ^ (ε / 4) := hNc

/-- GM §12 (proof of Prop 3.1): the areas' statements imply Proposition 4.1 in the window form
used by `Submission.LargeValues.theorem_1_1_of_keyprop`; see `Submission/GM/Interfaces.lean`. -/
theorem keyprop_of_parts (hTr : Submission.GM.TraceStatement) (hS2 : Submission.GM.S2Statement)
    (hS3 : Submission.GM.S3Statement) (hE : Submission.GM.EnergyStatement) :
    Submission.LargeValues.KeyPropStatement := by
  intro ε hε N₀
  obtain ⟨C₁, hC₁, N₁, hTr'⟩ := hTr ε hε
  set δ : ℝ := ε / 16 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨C₂, hC₂, N₂, hS2'⟩ := hS2 ε δ hε hδ
  obtain ⟨C₃, hC₃, N₃, hS3'⟩ := hS3 ε δ hε hδ
  obtain ⟨C₄, hC₄, N₄, hE'⟩ := hE δ hδ
  have hC1nn : 0 ≤ C₁ := le_of_lt hC₁
  have hC2nn : 0 ≤ C₂ := le_of_lt hC₂
  have hC3nn : 0 ≤ C₃ := le_of_lt hC₃
  have hC4nn : 0 ≤ C₄ := le_of_lt hC₄
  set G : ℝ := 1 + C₁ + C₂ + C₃ + C₄ with hGdef
  have hG1 : 1 ≤ G := by rw [hGdef]; linarith
  have hC1G : C₁ ≤ G := by rw [hGdef]; linarith
  have hC2G : C₂ ≤ G := by rw [hGdef]; linarith
  have hC3G : C₃ ≤ G := by rw [hGdef]; linarith
  have hC4G : C₄ ≤ G := by rw [hGdef]; linarith
  obtain ⟨Nc, hNc⟩ := nat_le_rpow_ge ((18 : ℝ) ^ (3 : ℝ) * G ^ (6 : ℝ)) (ε / 4)
    (by positivity) (by linarith)
  refine ⟨N₀ + N₁ + N₂ + N₃ + N₄ + Nc + 1, by omega, ?_⟩
  intro N hN V hVlo hVhi b hb W hWsub hWsep hWv
  have hN₁ : N₁ ≤ N := by omega
  have hN₂ : N₂ ≤ N := by omega
  have hN₃ : N₃ ≤ N := by omega
  have hN₄ : N₄ ≤ N := by omega
  have hNc' : Nc ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hMN1 : (1 : ℝ) ≤ M N := M_ge_one hN1
  have hV0 : 0 < V := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos (7 / 10 : ℝ)) hVlo
  have hVnn : 0 ≤ V := le_of_lt hV0
  set X : ℝ := (W.card : ℝ) with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hEnn : (0 : ℝ) ≤ (energy W : ℝ) := Nat.cast_nonneg _
  have hV2 : ((V : ℝ) ^ 2)⁻¹ = (V : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast V 2, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
      ← Real.rpow_neg hVnn (2 : ℝ)]
  have hV4 : ((V : ℝ) ^ 4)⁻¹ = (V : ℝ) ^ (-4 : ℝ) := by
    rw [← Real.rpow_natCast V 4, show ((4 : ℕ) : ℝ) = (4 : ℝ) by norm_num,
      ← Real.rpow_neg hVnn (4 : ℝ)]
  obtain ⟨B2a, hB2adef⟩ : ∃ B2a : ℝ, B2a = (N : ℝ) ^ (2 : ℝ) * X ^ (2 : ℝ) := ⟨_, rfl⟩
  have hB2ann : 0 ≤ B2a := by rw [hB2adef]; positivity
  obtain ⟨B2b, hB2bdef⟩ : ∃ B2b : ℝ, B2b = (N : ℝ) ^ (11 / 5 : ℝ) * X ^ (7 / 4 : ℝ) := ⟨_, rfl⟩
  have hB2bnn : 0 ≤ B2b := by rw [hB2bdef]; positivity
  obtain ⟨B2c, hB2cdef⟩ : ∃ B2c : ℝ, B2c = (N : ℝ) ^ (43 / 20 : ℝ) * X ^ (29 / 16 : ℝ) := ⟨_, rfl⟩
  have hB2cnn : 0 ≤ B2c := by rw [hB2cdef]; positivity
  obtain ⟨B2, hB2def⟩ : ∃ B2 : ℝ, B2 = B2a + B2b + B2c := ⟨_, rfl⟩
  have hB2nn : 0 ≤ B2 := by rw [hB2def]; linarith
  obtain ⟨R2a, hR2adef⟩ : ∃ R2a : ℝ, R2a = (N : ℝ) ^ (2 / 3 : ℝ) * X ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  have hR2ann : 0 ≤ R2a := by rw [hR2adef]; positivity
  obtain ⟨R2b, hR2bdef⟩ : ∃ R2b : ℝ, R2b = (N : ℝ) ^ (11 / 15 : ℝ) * X ^ (7 / 12 : ℝ) := ⟨_, rfl⟩
  have hR2bnn : 0 ≤ R2b := by rw [hR2bdef]; positivity
  obtain ⟨R2c, hR2cdef⟩ : ∃ R2c : ℝ, R2c = (N : ℝ) ^ (43 / 60 : ℝ) * X ^ (29 / 48 : ℝ) := ⟨_, rfl⟩
  have hR2cnn : 0 ≤ R2c := by rw [hR2cdef]; positivity
  obtain ⟨R2, hR2def⟩ : ∃ R2 : ℝ, R2 = R2a + R2b + R2c := ⟨_, rfl⟩
  obtain ⟨B3a, hB3adef⟩ : ∃ B3a : ℝ, B3a = (N : ℝ) ^ (12 / 5 : ℝ) * X ^ (3 / 2 : ℝ) := ⟨_, rfl⟩
  have hB3ann : 0 ≤ B3a := by rw [hB3adef]; positivity
  obtain ⟨B3b, hB3bdef⟩ : ∃ B3b : ℝ,
      B3b = (N : ℝ) ^ (11 / 5 : ℝ) * X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hB3bnn : 0 ≤ B3b := by rw [hB3bdef]; positivity
  obtain ⟨B3, hB3def⟩ : ∃ B3 : ℝ, B3 = B3a + B3b := ⟨_, rfl⟩
  have hB3nn : 0 ≤ B3 := by rw [hB3def]; linarith
  obtain ⟨BEa, hBEadef⟩ : ∃ BEa : ℝ,
      BEa = X * (N : ℝ) ^ (4 : ℝ) * (V : ℝ) ^ (-4 : ℝ) := ⟨_, rfl⟩
  have hBEann : 0 ≤ BEa := by rw [hBEadef]; positivity
  obtain ⟨BEb, hBEbdef⟩ : ∃ BEb : ℝ,
      BEb = X ^ (21 / 8 : ℝ) * (N : ℝ) ^ (13 / 10 : ℝ) * (V : ℝ) ^ (-2 : ℝ) := ⟨_, rfl⟩
  have hBEbnn : 0 ≤ BEb := by rw [hBEbdef]; positivity
  obtain ⟨BEc, hBEcdef⟩ : ∃ BEc : ℝ,
      BEc = X ^ (3 : ℝ) * (N : ℝ) * (V : ℝ) ^ (-2 : ℝ) := ⟨_, rfl⟩
  have hBEcnn : 0 ≤ BEc := by rw [hBEcdef]; positivity
  obtain ⟨BE, hBEdef⟩ : ∃ BE : ℝ, BE = BEa + BEb + BEc := ⟨_, rfl⟩
  have hBEnn : 0 ≤ BE := by rw [hBEdef]; linarith
  obtain ⟨E6a, hE6adef⟩ : ∃ E6a : ℝ,
      E6a = X ^ (1 / 6 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * (V : ℝ) ^ (-2 / 3 : ℝ) := ⟨_, rfl⟩
  have hE6ann : 0 ≤ E6a := by rw [hE6adef]; positivity
  obtain ⟨E6b, hE6bdef⟩ : ∃ E6b : ℝ,
      E6b = X ^ (21 / 48 : ℝ) * (N : ℝ) ^ (13 / 60 : ℝ) * (V : ℝ) ^ (-1 / 3 : ℝ) := ⟨_, rfl⟩
  have hE6bnn : 0 ≤ E6b := by rw [hE6bdef]; positivity
  obtain ⟨E6c, hE6cdef⟩ : ∃ E6c : ℝ,
      E6c = X ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) * (V : ℝ) ^ (-1 / 3 : ℝ) := ⟨_, rfl⟩
  have hE6cnn : 0 ≤ E6c := by rw [hE6cdef]; positivity
  obtain ⟨E6, hE6def⟩ : ∃ E6 : ℝ, E6 = E6a + (E6b + E6c) := ⟨_, rfl⟩
  have hE6nn : 0 ≤ E6 := by rw [hE6def]; linarith
  obtain ⟨R3a, hR3adef⟩ : ∃ R3a : ℝ, R3a = (N : ℝ) ^ (4 / 5 : ℝ) * X ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hR3ann : 0 ≤ R3a := by rw [hR3adef]; positivity
  obtain ⟨R3b, hR3bdef⟩ : ∃ R3b : ℝ, R3b = (N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
      * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6) := ⟨_, rfl⟩
  have hR3bnn : 0 ≤ R3b := by rw [hR3bdef]; positivity
  obtain ⟨R3, hR3def⟩ : ∃ R3 : ℝ, R3 = R3a + R3b := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (N : ℝ) ^ ε * (N : ℝ) ^ (18 / 5 : ℝ) * (V : ℝ) ^ (-4 : ℝ) :=
    ⟨_, rfl⟩
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hBpos : 0 < B := by rw [hBdef]; positivity
  obtain ⟨K0, hK0def⟩ : ∃ K0 : ℝ, K0 = C₁ * (N : ℝ) ^ (2 : ℝ) * (V : ℝ) ^ (-2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨K1, hK1def⟩ : ∃ K1 : ℝ, K1 = C₁ * (N : ℝ) ^ (1 : ℝ) * (V : ℝ) ^ (-2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨K2, hK2def⟩ : ∃ K2 : ℝ,
      K2 = C₁ * C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 + δ * (1 / 3) + 2 / 3) * (V : ℝ) ^ (-2 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨K3, hK3def⟩ : ∃ K3 : ℝ,
      K3 = C₁ * C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 + δ * (1 / 3) + 11 / 15) * (V : ℝ) ^ (-2 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨K4, hK4def⟩ : ∃ K4 : ℝ,
      K4 = C₁ * C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 + δ * (1 / 3) + 43 / 60) * (V : ℝ) ^ (-2 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨K5, hK5def⟩ : ∃ K5 : ℝ,
      K5 = C₁ * C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 + δ * (1 / 3) + 4 / 5) * (V : ℝ) ^ (-2 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨K6, hK6def⟩ : ∃ K6 : ℝ, K6 = C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ)
      * (N : ℝ) ^ (1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 2 / 3)
      * (V : ℝ) ^ ((-2 : ℝ) + (-2 / 3 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨K7, hK7def⟩ : ∃ K7 : ℝ, K7 = C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ)
      * (N : ℝ) ^ (1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 13 / 60)
      * (V : ℝ) ^ ((-2 : ℝ) + (-1 / 3 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨K8, hK8def⟩ : ∃ K8 : ℝ, K8 = C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ)
      * (N : ℝ) ^ (1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 1 / 6)
      * (V : ℝ) ^ ((-2 : ℝ) + (-1 / 3 : ℝ)) := ⟨_, rfl⟩
  have htr0 := hTr' N hN₁ W hWsub hWsep
  have hS1 : ‖Spart 1 N W‖ ≤ 1 := htr0.2.1
  have htrace : X ≤ C₁ * ((N : ℝ) ^ 2 / V ^ 2
      + (N : ℝ) / V ^ 2 * (‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ ^ (1 / 3 : ℝ))) := by
    have h := htr0.2.2 b hb V hV0 hWv
    rw [← hXdef] at h
    exact h
  have hsep1 : Separated W 1 := fun t ht s hs hne =>
    le_trans (Real.one_le_rpow hMN1 hε.le) (hWsep t ht s hs hne)
  have hs2c : ‖Spart 2 N W‖ ≤ C₂ * (N : ℝ) ^ δ * B2 := by
    have h := hS2' N hN₂ W hWsub hWsep
    rw [← hXdef] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hB2def]
    have e1 : (N : ℝ) ^ 2 * X ^ 2 ≤ B2a := by
      rw [hB2adef, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_natCast X 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num]
    have e2 : M N * N * X ^ (7 / 4 : ℝ) ≤ B2b := by
      rw [hB2bdef]
      have h2 : M N * N ≤ (N : ℝ) ^ (11 / 5 : ℝ) := by
        rw [show M N = (N : ℝ) ^ (6 / 5 : ℝ) from rfl, rpow_mul_self hNpos (6 / 5),
          show (6 / 5 : ℝ) + 1 = 11 / 5 by norm_num]
      exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hX0 _)
    have e3 : (N : ℝ) ^ 2 * X ^ (29 / 16 : ℝ) * (M N) ^ (1 / 8 : ℝ) ≤ B2c := by
      rw [hB2cdef]
      have h1 : (M N) ^ (1 / 8 : ℝ) = (N : ℝ) ^ (3 / 20 : ℝ) := by
        rw [show M N = (N : ℝ) ^ (6 / 5 : ℝ) from rfl, ← Real.rpow_mul hNpos.le (6 / 5) (1 / 8),
          show (6 / 5 : ℝ) * (1 / 8) = 3 / 20 by norm_num]
      have h2 : (N : ℝ) ^ 2 * (N : ℝ) ^ (3 / 20 : ℝ) ≤ (N : ℝ) ^ (43 / 20 : ℝ) := by
        rw [← Real.rpow_natCast (N : ℝ) 2, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
          rpow_mul2 hNpos (2 : ℝ) (3 / 20), show (2 : ℝ) + 3 / 20 = 43 / 20 by norm_num]
      have hre : (N : ℝ) ^ 2 * X ^ (29 / 16 : ℝ) * (M N) ^ (1 / 8 : ℝ)
          = (N : ℝ) ^ 2 * (M N) ^ (1 / 8 : ℝ) * X ^ (29 / 16 : ℝ) := by ring
      rw [hre, h1]
      exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hX0 _)
    exact add_le_add (add_le_add e1 e2) e3
  have hs3c : ‖Spart 3 N W‖ ≤ C₃ * (N : ℝ) ^ δ * B3 := by
    have h := hS3' N hN₃ W hWsub hWsep
    rw [← hXdef] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hB3def]
    have hNN : M N * N ≤ (N : ℝ) ^ (11 / 5 : ℝ) := by
      rw [show M N = (N : ℝ) ^ (6 / 5 : ℝ) from rfl, rpow_mul_self hNpos (6 / 5),
        show (6 / 5 : ℝ) + 1 = 11 / 5 by norm_num]
    have hMN2 : (M N) ^ 2 ≤ (N : ℝ) ^ (12 / 5 : ℝ) := by
      rw [show M N = (N : ℝ) ^ (6 / 5 : ℝ) from rfl,
        ← Real.rpow_natCast ((N : ℝ) ^ (6 / 5 : ℝ)) 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
        ← Real.rpow_mul hNpos.le (6 / 5) (2 : ℝ),
        show (6 / 5 : ℝ) * 2 = 12 / 5 by norm_num]
    have e1 : (M N) ^ 2 * X ^ (3 / 2 : ℝ) ≤ B3a := by
      rw [hB3adef]
      exact mul_le_mul_of_nonneg_right hMN2 (Real.rpow_nonneg hX0 _)
    have e2 : M N * N * X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ) ≤ B3b := by
      have hnn : 0 ≤ X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ) := by positivity
      have hmid : (M N * N) * (X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ))
          ≤ (N : ℝ) ^ (11 / 5 : ℝ) * (X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hNN hnn
      rw [hB3bdef]
      calc M N * N * X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ)
          = (M N * N) * (X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ)) := by ring
        _ ≤ (N : ℝ) ^ (11 / 5 : ℝ) * (X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ)) := hmid
        _ = (N : ℝ) ^ (11 / 5 : ℝ) * X ^ (1 / 2 : ℝ) * ((energy W : ℝ)) ^ (1 / 2 : ℝ) := by ring
    exact add_le_add e1 e2
  have hEc : (energy W : ℝ) ≤ C₄ * (N : ℝ) ^ δ * BE := by
    have h := hE' N hN₄ W hWsub hsep1 b hb V hV0 hWv
    rw [← hXdef] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hBEdef]
    have e1 : X * (N : ℝ) ^ 4 / V ^ 4 ≤ BEa := by
      rw [hBEadef, div_eq_mul_inv, hV4, ← Real.rpow_natCast (N : ℝ) 4,
        show ((4 : ℕ) : ℝ) = (4 : ℝ) by norm_num]
    have h1 : (M N) ^ (1 / 4 : ℝ) * (N : ℝ) = (N : ℝ) ^ (13 / 10 : ℝ) := by
      rw [show M N = (N : ℝ) ^ (6 / 5 : ℝ) from rfl, ← Real.rpow_mul hNpos.le (6 / 5) (1 / 4),
        show (6 / 5 : ℝ) * (1 / 4) = 3 / 10 by norm_num, rpow_mul_self hNpos (3 / 10),
        show (3 / 10 : ℝ) + 1 = 13 / 10 by norm_num]
    have e2 : X ^ (21 / 8 : ℝ) * (M N) ^ (1 / 4 : ℝ) * (N : ℝ) / V ^ 2 ≤ BEb := by
      rw [hBEbdef]
      have hre : X ^ (21 / 8 : ℝ) * (M N) ^ (1 / 4 : ℝ) * (N : ℝ) / V ^ 2
          = X ^ (21 / 8 : ℝ) * ((M N) ^ (1 / 4 : ℝ) * (N : ℝ)) * ((V : ℝ) ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]; ring
      rw [hre, h1, hV2]
    have e3 : X ^ 3 * (N : ℝ) / V ^ 2 ≤ BEc := by
      rw [hBEcdef, div_eq_mul_inv, hV2, ← Real.rpow_natCast X 3,
        show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num]
    exact add_le_add (add_le_add e1 e2) e3
  have htri : ‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖
      ≤ 1 + C₂ * (N : ℝ) ^ δ * B2 + C₃ * (N : ℝ) ^ δ * B3 := by
    have hAB := norm_add_le (Spart 1 N W + Spart 2 N W) (Spart 3 N W)
    have hab := norm_add_le (Spart 1 N W) (Spart 2 N W)
    linarith [hAB, hab, hS1, hs2c, hs3c]
  have hW13 : ‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ ^ (1 / 3 : ℝ)
      ≤ 1 + (C₂ * (N : ℝ) ^ δ * B2) ^ (1 / 3 : ℝ) + (C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ) := by
    have hnn : (0 : ℝ) ≤ ‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ := norm_nonneg _
    have h3 := rpow_add3_le (p := (1 / 3 : ℝ)) (a := (1 : ℝ))
      (b := C₂ * (N : ℝ) ^ δ * B2) (c := C₃ * (N : ℝ) ^ δ * B3)
      (by norm_num) (by positivity) (by positivity) (by norm_num) (by norm_num)
    have h2 : ‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ ^ (1 / 3 : ℝ)
        ≤ (1 + C₂ * (N : ℝ) ^ δ * B2 + C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow hnn htri (by norm_num)
    have h1 : (1 : ℝ) ^ (1 / 3 : ℝ) = 1 := Real.one_rpow _
    linarith [h2, h3, h1]
  have hB2root : B2 ^ (1 / 3 : ℝ) ≤ R2 := by
    rw [hB2def, hR2def]
    have h3 := rpow_add3_le (p := (1 / 3 : ℝ)) (a := B2a) (b := B2b) (c := B2c)
      hB2ann hB2bnn hB2cnn (by norm_num) (by norm_num)
    have e1 : B2a ^ (1 / 3 : ℝ) = R2a := by
      rw [hB2adef, hR2adef, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hNpos.le (2 : ℝ) (1 / 3), ← Real.rpow_mul hX0 (2 : ℝ) (1 / 3)]
      norm_num
    have e2 : B2b ^ (1 / 3 : ℝ) = R2b := by
      rw [hB2bdef, hR2bdef, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hNpos.le (11 / 5) (1 / 3), ← Real.rpow_mul hX0 (7 / 4) (1 / 3)]
      norm_num
    have e3 : B2c ^ (1 / 3 : ℝ) = R2c := by
      rw [hB2cdef, hR2cdef, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hNpos.le (43 / 20) (1 / 3), ← Real.rpow_mul hX0 (29 / 16) (1 / 3)]
      norm_num
    refine le_trans h3 ?_
    rw [e1, e2, e3]
  have hE6half : ((energy W : ℝ)) ^ (1 / 6 : ℝ) ≤ C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6 := by
    have h1 : ((energy W : ℝ)) ^ (1 / 6 : ℝ)
        ≤ (C₄ * (N : ℝ) ^ δ * BE) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hEc (by norm_num)
    have hsplit : (C₄ * (N : ℝ) ^ δ * BE) ^ (1 / 6 : ℝ)
        = C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * (BE ^ (1 / 6 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hBEnn, Real.mul_rpow hC4nn (Real.rpow_nonneg hNpos.le _),
        ← Real.rpow_mul hNpos.le δ (1 / 6)]
    rw [hsplit] at h1
    have h3 : BE ^ (1 / 6 : ℝ) ≤ E6 := by
      rw [hBEdef, hE6def]
      have h4 := rpow_add3_le (p := (1 / 6 : ℝ)) (a := BEa) (b := BEb) (c := BEc)
        hBEann hBEbnn hBEcnn (by norm_num) (by norm_num)
      have f1 : BEa ^ (1 / 6 : ℝ) = E6a := by
        rw [hBEadef, hE6adef, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hNpos.le (4 : ℝ) (1 / 6), ← Real.rpow_mul hVnn (-4 : ℝ) (1 / 6)]
        norm_num
      have f2 : BEb ^ (1 / 6 : ℝ) = E6b := by
        rw [hBEbdef, hE6bdef, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hX0 (21 / 8) (1 / 6),
          ← Real.rpow_mul hNpos.le (13 / 10) (1 / 6), ← Real.rpow_mul hVnn (-2 : ℝ) (1 / 6)]
        norm_num
      have f3 : BEc ^ (1 / 6 : ℝ) = E6c := by
        rw [hBEcdef, hE6cdef, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hX0 (3 : ℝ) (1 / 6),
          ← Real.rpow_mul hVnn (-2 : ℝ) (1 / 6)]
        norm_num
      refine le_trans h4 ?_
      rw [f1, f2, f3]
      exact le_of_eq (by ring)
    have hnn : 0 ≤ C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) := by positivity
    have hmid : C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * (BE ^ (1 / 6 : ℝ))
        ≤ C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6 :=
      mul_le_mul_of_nonneg_left h3 hnn
    exact le_trans h1 hmid
  have hB3root : B3 ^ (1 / 3 : ℝ) ≤ R3 := by
    rw [hB3def, hR3def]
    have h := Real.rpow_add_le_add_rpow (p := (1 / 3 : ℝ)) (a := B3a) (b := B3b)
      hB3ann hB3bnn (by norm_num) (by norm_num)
    have e1 : B3a ^ (1 / 3 : ℝ) = R3a := by
      rw [hB3adef, hR3adef, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hNpos.le (12 / 5) (1 / 3), ← Real.rpow_mul hX0 (3 / 2) (1 / 3)]
      norm_num
    have e2 : B3b ^ (1 / 3 : ℝ)
        = (N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ) * ((energy W : ℝ)) ^ (1 / 6 : ℝ) := by
      rw [hB3bdef, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hNpos.le (11 / 5) (1 / 3), ← Real.rpow_mul hX0 (1 / 2) (1 / 3),
        ← Real.rpow_mul hEnn (1 / 2) (1 / 3)]
      norm_num
    refine le_trans h ?_
    rw [e1, e2, hR3bdef]
    have hnn : 0 ≤ (N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ) := by positivity
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hE6half hnn)

  -- expand the rooted S2 term and merge the monomials
  have hT1 : C₁ * ((N : ℝ) / V ^ 2) * 1 ≤ K1 * X ^ (0 : ℝ) := by
    rw [hK1def, Real.rpow_zero, mul_one]
    conv_lhs => rw [div_eq_mul_inv, ← Real.rpow_natCast V 2,
      show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ),
      ← Real.rpow_one (N : ℝ)]
    exact le_of_eq (by ring)
  have hK234 : C₁ * ((N : ℝ) / V ^ 2) * (C₂ * (N : ℝ) ^ δ * B2) ^ (1 / 3 : ℝ)
      ≤ K2 * X ^ (2 / 3 : ℝ) + (K3 * X ^ (7 / 12 : ℝ) + K4 * X ^ (29 / 48 : ℝ)) := by
    have hsplit : (C₂ * (N : ℝ) ^ δ * B2) ^ (1 / 3 : ℝ)
        = C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (B2 ^ (1 / 3 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hB2nn,
        Real.mul_rpow hC2nn (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le δ (1 / 3)]
    have hle : (C₂ * (N : ℝ) ^ δ * B2) ^ (1 / 3 : ℝ)
        ≤ C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R2 := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hB2root (by positivity)
    have hnn : 0 ≤ C₁ * ((N : ℝ) / V ^ 2) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hle hnn) ?_
    rw [hR2def]
    have m2 : C₁ * ((N : ℝ) / V ^ 2) * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R2a)
        = K2 * X ^ (2 / 3 : ℝ) := by
      rw [hK2def, hR2adef, div_eq_mul_inv, ← Real.rpow_natCast V 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ)]
      rw [show C₁ * ((N : ℝ) * (V : ℝ) ^ (-2 : ℝ))
            * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
              * ((N : ℝ) ^ (2 / 3 : ℝ) * X ^ (2 / 3 : ℝ)))
          = C₁ * C₂ ^ (1 / 3 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (N : ℝ) ^ (2 / 3 : ℝ))
            * X ^ (2 / 3 : ℝ) * (V : ℝ) ^ (-2 : ℝ) by ring]
      rw [rpow_self_mul hNpos (δ * (1 / 3)), rpow_mul2 hNpos (1 + δ * (1 / 3)) (2 / 3)]
      ring
    have m3 : C₁ * ((N : ℝ) / V ^ 2) * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R2b)
        = K3 * X ^ (7 / 12 : ℝ) := by
      rw [hK3def, hR2bdef, div_eq_mul_inv, ← Real.rpow_natCast V 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ)]
      rw [show C₁ * ((N : ℝ) * (V : ℝ) ^ (-2 : ℝ))
            * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
              * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (7 / 12 : ℝ)))
          = C₁ * C₂ ^ (1 / 3 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (N : ℝ) ^ (11 / 15 : ℝ))
            * X ^ (7 / 12 : ℝ) * (V : ℝ) ^ (-2 : ℝ) by ring]
      rw [rpow_self_mul hNpos (δ * (1 / 3)), rpow_mul2 hNpos (1 + δ * (1 / 3)) (11 / 15)]
      ring
    have m4 : C₁ * ((N : ℝ) / V ^ 2) * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R2c)
        = K4 * X ^ (29 / 48 : ℝ) := by
      rw [hK4def, hR2cdef, div_eq_mul_inv, ← Real.rpow_natCast V 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ)]
      rw [show C₁ * ((N : ℝ) * (V : ℝ) ^ (-2 : ℝ))
            * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
              * ((N : ℝ) ^ (43 / 60 : ℝ) * X ^ (29 / 48 : ℝ)))
          = C₁ * C₂ ^ (1 / 3 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (N : ℝ) ^ (43 / 60 : ℝ))
            * X ^ (29 / 48 : ℝ) * (V : ℝ) ^ (-2 : ℝ) by ring]
      rw [rpow_self_mul hNpos (δ * (1 / 3)), rpow_mul2 hNpos (1 + δ * (1 / 3)) (43 / 60)]
      ring
    rw [show C₁ * ((N : ℝ) / V ^ 2) * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
            * (R2a + R2b + R2c))
          = C₁ * ((N : ℝ) / V ^ 2) * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R2a)
            + (C₁ * ((N : ℝ) / V ^ 2) * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R2b)
              + C₁ * ((N : ℝ) / V ^ 2) * (C₂ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R2c)) by ring]
    rw [m2, m3, m4]
  have hK5678 : C₁ * ((N : ℝ) / V ^ 2) * (C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ)
      ≤ K5 * X ^ (1 / 2 : ℝ) + (K6 * X ^ (1 / 3 : ℝ) + (K7 * X ^ (29 / 48 : ℝ)
        + K8 * X ^ (2 / 3 : ℝ))) := by
    have hsplit : (C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ)
        = C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (B3 ^ (1 / 3 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hB3nn,
        Real.mul_rpow hC3nn (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le δ (1 / 3)]
    have hle : (C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ)
        ≤ C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R3 := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hB3root (by positivity)
    have hnn : 0 ≤ C₁ * ((N : ℝ) / V ^ 2) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hle hnn) ?_
    rw [hR3def]
    have m5 : C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R3a)
        = K5 * X ^ (1 / 2 : ℝ) := by
      rw [hK5def, hR3adef, div_eq_mul_inv, ← Real.rpow_natCast V 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ)]
      rw [show C₁ * ((N : ℝ) * (V : ℝ) ^ (-2 : ℝ))
            * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
              * ((N : ℝ) ^ (4 / 5 : ℝ) * X ^ (1 / 2 : ℝ)))
          = C₁ * C₃ ^ (1 / 3 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (N : ℝ) ^ (4 / 5 : ℝ))
            * X ^ (1 / 2 : ℝ) * (V : ℝ) ^ (-2 : ℝ) by ring]
      rw [rpow_self_mul hNpos (δ * (1 / 3)), rpow_mul2 hNpos (1 + δ * (1 / 3)) (4 / 5)]
      ring
    have m6 : C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
          * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
            * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6a)))
        = K6 * X ^ (1 / 3 : ℝ) := by
      rw [hK6def, hE6adef, div_eq_mul_inv, ← Real.rpow_natCast V 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ)]
      rw [show C₁ * ((N : ℝ) * (V : ℝ) ^ (-2 : ℝ)) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
            * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
              * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6))
                * (X ^ (1 / 6 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * (V : ℝ) ^ (-2 / 3 : ℝ)))))
          = C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ)
            * ((N : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (N : ℝ) ^ (11 / 15 : ℝ) * (N : ℝ) ^ (δ * (1 / 6))
              * (N : ℝ) ^ (2 / 3 : ℝ))
            * (X ^ (1 / 6 : ℝ) * X ^ (1 / 6 : ℝ))
            * ((V : ℝ) ^ (-2 : ℝ) * (V : ℝ) ^ (-2 / 3 : ℝ)) by ring]
      rw [rpow_self_mul hNpos (δ * (1 / 3)), rpow_mul2 hNpos (1 + δ * (1 / 3)) (11 / 15),
        rpow_mul2 hNpos (1 + δ * (1 / 3) + 11 / 15) (δ * (1 / 6)),
        rpow_mul2 hNpos (1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6)) (2 / 3),
        rpow_mul2_nn hX0 (by norm_num) (by norm_num), rpow_mul2 hV0 (-2) (-2 / 3)]
      ring
    have m7 : C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
          * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
            * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6b)))
        = K7 * X ^ (29 / 48 : ℝ) := by
      rw [hK7def, hE6bdef, div_eq_mul_inv, ← Real.rpow_natCast V 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ)]
      rw [show C₁ * ((N : ℝ) * (V : ℝ) ^ (-2 : ℝ)) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
            * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
              * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6))
                * (X ^ (21 / 48 : ℝ) * (N : ℝ) ^ (13 / 60 : ℝ) * (V : ℝ) ^ (-1 / 3 : ℝ)))))
          = C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ)
            * ((N : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (N : ℝ) ^ (11 / 15 : ℝ) * (N : ℝ) ^ (δ * (1 / 6))
              * (N : ℝ) ^ (13 / 60 : ℝ))
            * (X ^ (1 / 6 : ℝ) * X ^ (21 / 48 : ℝ))
            * ((V : ℝ) ^ (-2 : ℝ) * (V : ℝ) ^ (-1 / 3 : ℝ)) by ring]
      rw [rpow_self_mul hNpos (δ * (1 / 3)), rpow_mul2 hNpos (1 + δ * (1 / 3)) (11 / 15),
        rpow_mul2 hNpos (1 + δ * (1 / 3) + 11 / 15) (δ * (1 / 6)),
        rpow_mul2 hNpos (1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6)) (13 / 60),
        rpow_mul2_nn hX0 (by norm_num) (by norm_num), rpow_mul2 hV0 (-2) (-1 / 3)]
      ring_nf
    have m8 : C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
          * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
            * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6c)))
        = K8 * X ^ (2 / 3 : ℝ) := by
      rw [hK8def, hE6cdef, div_eq_mul_inv, ← Real.rpow_natCast V 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ)]
      rw [show C₁ * ((N : ℝ) * (V : ℝ) ^ (-2 : ℝ)) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
            * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
              * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6))
                * (X ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) * (V : ℝ) ^ (-1 / 3 : ℝ)))))
          = C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ)
            * ((N : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (N : ℝ) ^ (11 / 15 : ℝ) * (N : ℝ) ^ (δ * (1 / 6))
              * (N : ℝ) ^ (1 / 6 : ℝ))
            * (X ^ (1 / 6 : ℝ) * X ^ (1 / 2 : ℝ))
            * ((V : ℝ) ^ (-2 : ℝ) * (V : ℝ) ^ (-1 / 3 : ℝ)) by ring]
      rw [rpow_self_mul hNpos (δ * (1 / 3)), rpow_mul2 hNpos (1 + δ * (1 / 3)) (11 / 15),
        rpow_mul2 hNpos (1 + δ * (1 / 3) + 11 / 15) (δ * (1 / 6)),
        rpow_mul2 hNpos (1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6)) (1 / 6),
        rpow_mul2_nn hX0 (by norm_num) (by norm_num), rpow_mul2 hV0 (-2) (-1 / 3)]
      ring_nf
    rw [show C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * (R3a + R3b))
          = C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R3a)
            + C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3)) * R3b) by ring]
    rw [hR3bdef, hE6def]
    rw [show C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
          * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
            * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * (E6a + (E6b + E6c)))))
          = C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
              * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
                * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6a)))
            + (C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
                * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
                  * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6b)))
              + C₁ * ((N : ℝ) / V ^ 2) * (C₃ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (δ * (1 / 3))
                * ((N : ℝ) ^ (11 / 15 : ℝ) * X ^ (1 / 6 : ℝ)
                  * (C₄ ^ (1 / 6 : ℝ) * (N : ℝ) ^ (δ * (1 / 6)) * E6c)))) by ring]
    rw [m5, m6, m7, m8]
  -- the full five-term upper bound for X
  have hfinal : X ≤ K0 * X ^ (0 : ℝ) + K1 * X ^ (0 : ℝ)
      + (K2 * X ^ (2 / 3 : ℝ) + K3 * X ^ (7 / 12 : ℝ) + K4 * X ^ (29 / 48 : ℝ))
      + (K5 * X ^ (1 / 2 : ℝ) + K6 * X ^ (1 / 3 : ℝ) + K7 * X ^ (29 / 48 : ℝ)
        + K8 * X ^ (2 / 3 : ℝ)) := by
    have h1 : C₁ * ((N : ℝ) ^ 2 / V ^ 2) ≤ K0 * X ^ (0 : ℝ) := by
      rw [hK0def, Real.rpow_zero, mul_one]
      conv_lhs => rw [div_eq_mul_inv, ← Real.rpow_natCast V 2,
        show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, ← Real.rpow_neg hVnn (2 : ℝ),
        ← Real.rpow_natCast (N : ℝ) 2, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num]
      exact le_of_eq (by ring)
    have h2 : C₁ * ((N : ℝ) / V ^ 2
          * (‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ ^ (1 / 3 : ℝ)))
        ≤ C₁ * ((N : ℝ) / V ^ 2)
          * (1 + (C₂ * (N : ℝ) ^ δ * B2) ^ (1 / 3 : ℝ)
            + (C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ)) := by
      rw [show C₁ * ((N : ℝ) / V ^ 2 * (‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ ^ (1 / 3 : ℝ)))
          = C₁ * ((N : ℝ) / V ^ 2) * (‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ ^ (1 / 3 : ℝ))
          by ring]
      exact mul_le_mul_of_nonneg_left hW13 (by positivity)
    have h3 : X ≤ C₁ * ((N : ℝ) ^ 2 / V ^ 2)
        + C₁ * ((N : ℝ) / V ^ 2 * (‖Spart 1 N W + Spart 2 N W + Spart 3 N W‖ ^ (1 / 3 : ℝ))) := by
      refine le_trans htrace (le_of_eq ?_)
      ring
    have h4 : C₁ * ((N : ℝ) / V ^ 2) * (1 + (C₂ * (N : ℝ) ^ δ * B2) ^ (1 / 3 : ℝ)
          + (C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ))
        ≤ K1 * X ^ (0 : ℝ) + ((K2 * X ^ (2 / 3 : ℝ)
            + (K3 * X ^ (7 / 12 : ℝ) + K4 * X ^ (29 / 48 : ℝ)))
          + (K5 * X ^ (1 / 2 : ℝ) + (K6 * X ^ (1 / 3 : ℝ)
            + (K7 * X ^ (29 / 48 : ℝ) + K8 * X ^ (2 / 3 : ℝ))))) := by
      rw [show C₁ * ((N : ℝ) / V ^ 2) * (1 + (C₂ * (N : ℝ) ^ δ * B2) ^ (1 / 3 : ℝ)
            + (C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ))
          = C₁ * ((N : ℝ) / V ^ 2) * 1
            + (C₁ * ((N : ℝ) / V ^ 2) * (C₂ * (N : ℝ) ^ δ * B2) ^ (1 / 3 : ℝ)
              + C₁ * ((N : ℝ) / V ^ 2) * (C₃ * (N : ℝ) ^ δ * B3) ^ (1 / 3 : ℝ)) by ring]
      exact add_le_add hT1 (add_le_add hK234 hK5678)
    linarith [h1, h2, h3, h4]
  have hXleB : X ≤ B := by
    by_contra hcon
    rw [not_le] at hcon
    have hXpos : 0 < X := lt_of_lt_of_le hBpos hcon.le
    have hKG1 : C₁ ≤ G ^ (3 / 2 : ℝ) := by
      have h := const_le_G32 hG1 hC1nn hC1G zero_le_one hG1 zero_le_one hG1
      simpa [Real.one_rpow, mul_one] using h
    have hKG2 : C₁ * C₂ ^ (1 / 3 : ℝ) ≤ G ^ (3 / 2 : ℝ) := by
      have h := const_le_G32 hG1 hC1nn hC1G hC2nn hC2G zero_le_one hG1
      simpa [Real.one_rpow, mul_one] using h
    have hKG3 : C₁ * C₃ ^ (1 / 3 : ℝ) ≤ G ^ (3 / 2 : ℝ) := by
      have h := const_le_G32 hG1 hC1nn hC1G hC3nn hC3G zero_le_one hG1
      simpa [Real.one_rpow, mul_one] using h
    have hKG4 : C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ) ≤ G ^ (3 / 2 : ℝ) :=
      const_le_G32 hG1 hC1nn hC1G hC3nn hC3G hC4nn hC4G
    have ht0 : K0 * X ^ (0 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K0) ^ (1 / (1 - (0 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 0) = 1 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        exact root_bound_def (K := K0) (C := C₁) (b := (2 : ℝ)) (f := (-2 : ℝ)) (r := (1 : ℝ))
          hN1R hV0 hVlo hVhi hε hBdef (by rw [hK0def]) hC1nn
          (const_bound' hG1 hC1nn hKG1 (hNc N hNc') (by norm_num) (by norm_num))
          (by linarith) (by linarith)
      have h := term_bound hXpos (by rw [hK0def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have ht1 : K1 * X ^ (0 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K1) ^ (1 / (1 - (0 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 0) = 1 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        exact root_bound_def (K := K1) (C := C₁) (b := (1 : ℝ)) (f := (-2 : ℝ)) (r := (1 : ℝ))
          hN1R hV0 hVlo hVhi hε hBdef (by rw [hK1def]) hC1nn
          (const_bound' hG1 hC1nn hKG1 (hNc N hNc') (by norm_num) (by norm_num))
          (by linarith) (by linarith)
      have h := term_bound hXpos (by rw [hK1def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have ht2 : K2 * X ^ (2 / 3 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K2) ^ (1 / (1 - (2 / 3 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 2 / 3) = 3 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        have h7 : ((1 + δ * (1 / 3) + 2 / 3) * 3 - 18 / 5) + ((-2 : ℝ) * 3 + 4) * (7 / 10) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        have h45 : ((1 + δ * (1 / 3) + 2 / 3) * 3 - 18 / 5) + ((-2 : ℝ) * 3 + 4) * (4 / 5) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        exact root_bound_def (K := K2) (C := C₁ * C₂ ^ (1 / 3 : ℝ)) (b := 1 + δ * (1 / 3) + 2 / 3)
          (f := (-2 : ℝ)) (r := (3 : ℝ)) hN1R hV0 hVlo hVhi hε hBdef (by rw [hK2def]) (by positivity)
          (const_bound' hG1 (by positivity) hKG2 (hNc N hNc') (by norm_num) (by norm_num))
          h7 h45
      have h := term_bound hXpos (by rw [hK2def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have ht3 : K3 * X ^ (7 / 12 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K3) ^ (1 / (1 - (7 / 12 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 7 / 12) = 12 / 5 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        have h7 : ((1 + δ * (1 / 3) + 11 / 15) * (12 / 5) - 18 / 5)
            + ((-2 : ℝ) * (12 / 5) + 4) * (7 / 10) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        have h45 : ((1 + δ * (1 / 3) + 11 / 15) * (12 / 5) - 18 / 5)
            + ((-2 : ℝ) * (12 / 5) + 4) * (4 / 5) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        exact root_bound_def (K := K3) (C := C₁ * C₂ ^ (1 / 3 : ℝ)) (b := 1 + δ * (1 / 3) + 11 / 15)
          (f := (-2 : ℝ)) (r := (12 / 5 : ℝ)) hN1R hV0 hVlo hVhi hε hBdef (by rw [hK3def]) (by positivity)
          (const_bound' hG1 (by positivity) hKG2 (hNc N hNc') (by norm_num) (by norm_num))
          h7 h45
      have h := term_bound hXpos (by rw [hK3def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have ht4 : K4 * X ^ (29 / 48 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K4) ^ (1 / (1 - (29 / 48 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 29 / 48) = 48 / 19 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        have h7 : ((1 + δ * (1 / 3) + 43 / 60) * (48 / 19) - 18 / 5)
            + ((-2 : ℝ) * (48 / 19) + 4) * (7 / 10) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        have h45 : ((1 + δ * (1 / 3) + 43 / 60) * (48 / 19) - 18 / 5)
            + ((-2 : ℝ) * (48 / 19) + 4) * (4 / 5) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        exact root_bound_def (K := K4) (C := C₁ * C₂ ^ (1 / 3 : ℝ)) (b := 1 + δ * (1 / 3) + 43 / 60)
          (f := (-2 : ℝ)) (r := (48 / 19 : ℝ)) hN1R hV0 hVlo hVhi hε hBdef (by rw [hK4def]) (by positivity)
          (const_bound' hG1 (by positivity) hKG2 (hNc N hNc') (by norm_num) (by norm_num))
          h7 h45
      have h := term_bound hXpos (by rw [hK4def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have ht5 : K5 * X ^ (1 / 2 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K5) ^ (1 / (1 - (1 / 2 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        have h7 : ((1 + δ * (1 / 3) + 4 / 5) * 2 - 18 / 5) + ((-2 : ℝ) * 2 + 4) * (7 / 10) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        have h45 : ((1 + δ * (1 / 3) + 4 / 5) * 2 - 18 / 5) + ((-2 : ℝ) * 2 + 4) * (4 / 5) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        exact root_bound_def (K := K5) (C := C₁ * C₃ ^ (1 / 3 : ℝ)) (b := 1 + δ * (1 / 3) + 4 / 5)
          (f := (-2 : ℝ)) (r := (2 : ℝ)) hN1R hV0 hVlo hVhi hε hBdef (by rw [hK5def]) (by positivity)
          (const_bound' hG1 (by positivity) hKG3 (hNc N hNc') (by norm_num) (by norm_num))
          h7 h45
      have h := term_bound hXpos (by rw [hK5def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have ht6 : K6 * X ^ (1 / 3 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K6) ^ (1 / (1 - (1 / 3 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 1 / 3) = 3 / 2 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        have h7 : ((1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 2 / 3) * (3 / 2) - 18 / 5)
            + (((-2 : ℝ) + (-2 / 3 : ℝ)) * (3 / 2) + 4) * (7 / 10) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        have h45 : ((1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 2 / 3) * (3 / 2) - 18 / 5)
            + (((-2 : ℝ) + (-2 / 3 : ℝ)) * (3 / 2) + 4) * (4 / 5) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        exact root_bound_def (K := K6) (C := C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ))
          (b := 1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 2 / 3)
          (f := (-2 : ℝ) + (-2 / 3 : ℝ)) (r := (3 / 2 : ℝ)) hN1R hV0 hVlo hVhi hε hBdef
          (by rw [hK6def]) (by positivity)
          (const_bound' hG1 (by positivity) hKG4 (hNc N hNc') (by norm_num) (by norm_num))
          h7 h45
      have h := term_bound hXpos (by rw [hK6def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have ht7 : K7 * X ^ (29 / 48 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K7) ^ (1 / (1 - (29 / 48 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 29 / 48) = 48 / 19 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        have h7 : ((1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 13 / 60) * (48 / 19) - 18 / 5)
            + (((-2 : ℝ) + (-1 / 3 : ℝ)) * (48 / 19) + 4) * (7 / 10) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        have h45 : ((1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 13 / 60) * (48 / 19) - 18 / 5)
            + (((-2 : ℝ) + (-1 / 3 : ℝ)) * (48 / 19) + 4) * (4 / 5) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        exact root_bound_def (K := K7) (C := C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ))
          (b := 1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 13 / 60)
          (f := (-2 : ℝ) + (-1 / 3 : ℝ)) (r := (48 / 19 : ℝ)) hN1R hV0 hVlo hVhi hε hBdef
          (by rw [hK7def]) (by positivity)
          (const_bound' hG1 (by positivity) hKG4 (hNc N hNc') (by norm_num) (by norm_num))
          h7 h45
      have h := term_bound hXpos (by rw [hK7def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have ht8 : K8 * X ^ (2 / 3 : ℝ) < X / 18 := by
      have hb : (2 * 9 * K8) ^ (1 / (1 - (2 / 3 : ℝ))) ≤ B := by
        rw [show (1 : ℝ) / (1 - 2 / 3) = 3 by norm_num, show (2 : ℝ) * 9 = 18 by norm_num]
        have h7 : ((1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 1 / 6) * 3 - 18 / 5)
            + (((-2 : ℝ) + (-1 / 3 : ℝ)) * 3 + 4) * (7 / 10) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        have h45 : ((1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 1 / 6) * 3 - 18 / 5)
            + (((-2 : ℝ) + (-1 / 3 : ℝ)) * 3 + 4) * (4 / 5) ≤ ε / 4 := by
          rw [hδdef]; linarith only [hε]
        exact root_bound_def (K := K8) (C := C₁ * C₃ ^ (1 / 3 : ℝ) * C₄ ^ (1 / 6 : ℝ))
          (b := 1 + δ * (1 / 3) + 11 / 15 + δ * (1 / 6) + 1 / 6)
          (f := (-2 : ℝ) + (-1 / 3 : ℝ)) (r := (3 : ℝ)) hN1R hV0 hVlo hVhi hε hBdef
          (by rw [hK8def]) (by positivity)
          (const_bound' hG1 (by positivity) hKG4 (hNc N hNc') (by norm_num) (by norm_num))
          h7 h45
      have h := term_bound hXpos (by rw [hK8def]; positivity) (by norm_num) (by norm_num)
        (by norm_num) hb hcon
      rwa [show X / (2 * 9) = X / 18 by norm_num] at h
    have hsum : K0 * X ^ (0 : ℝ) + K1 * X ^ (0 : ℝ)
        + (K2 * X ^ (2 / 3 : ℝ) + K3 * X ^ (7 / 12 : ℝ) + K4 * X ^ (29 / 48 : ℝ))
        + (K5 * X ^ (1 / 2 : ℝ) + K6 * X ^ (1 / 3 : ℝ) + K7 * X ^ (29 / 48 : ℝ)
          + K8 * X ^ (2 / 3 : ℝ)) < X / 2 := by
      linarith [ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8]
    linarith [hfinal, hsum, hX0]
  have hBconv : B = (N : ℝ) ^ ε * M N * (N : ℝ) ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by
    have hVz : (V : ℝ) ^ (-4 : ℤ) = (V : ℝ) ^ (-4 : ℝ) := by
      have h1 : (V : ℝ) ^ (-4 : ℤ) = ((V : ℝ) ^ 4)⁻¹ := by
        rw [show (-4 : ℤ) = -(4 : ℤ) by norm_num, zpow_neg,
          show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
      have h2 : (V : ℝ) ^ (-4 : ℝ) = ((V : ℝ) ^ 4)⁻¹ := by
        rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg hVnn,
          show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h1, h2]
    have hN18 : (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ) = (N : ℝ) ^ (18 / 5 : ℝ) := by
      rw [rpow_mul2 hNpos (6 / 5) (12 / 5), show (6 / 5 : ℝ) + 12 / 5 = 18 / 5 by norm_num]
    rw [hBdef, show M N = (N : ℝ) ^ (6 / 5 : ℝ) from rfl, hVz]
    calc (N : ℝ) ^ ε * (N : ℝ) ^ (18 / 5 : ℝ) * (V : ℝ) ^ (-4 : ℝ)
        = (N : ℝ) ^ ε * ((N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ))
            * (V : ℝ) ^ (-4 : ℝ) := by rw [hN18]
      _ = (N : ℝ) ^ ε * (N : ℝ) ^ (6 / 5 : ℝ) * (N : ℝ) ^ (12 / 5 : ℝ)
            * (V : ℝ) ^ (-4 : ℝ) := by ring
  rw [hBconv] at hXleB
  exact hXleB
end Work.GM.Assembly
