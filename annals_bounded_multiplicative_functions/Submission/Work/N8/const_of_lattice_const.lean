import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Polynomial

/-- Mean-value bound: a polynomial whose derivative is bounded by `A` on `[x, x+L]`
satisfies `|G b - G a| ≤ A (b - a)` for `x ≤ a ≤ b ≤ x + L`. -/
private lemma abs_eval_sub_le {G : Polynomial ℝ} {x L A : ℝ}
    (hbound : ∀ t ∈ Set.Icc x (x + L), |G.derivative.eval t| ≤ A)
    {a b : ℝ} (ha : x ≤ a) (hb : b ≤ x + L) (hab : a ≤ b) :
    |G.eval b - G.eval a| ≤ A * (b - a) := by
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun s => G.eval s) t :=
    fun t _ => (G.hasDerivAt t).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc a b, ‖deriv (fun s => G.eval s) t‖ ≤ A := by
    intro t ht
    rw [Polynomial.deriv]
    have : t ∈ Set.Icc x (x + L) := ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
    simpa using hbound t this
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv hconv
    (show a ∈ Set.Icc a b from ⟨le_refl a, hab⟩)
    (show b ∈ Set.Icc a b from ⟨hab, le_refl b⟩)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h

/-- Two integers whose images in `ℝ` are within distance `< 1` coincide. -/
private lemma int_eq_of_abs_cast_sub_lt_one {z w : ℤ} (h : |(z : ℝ) - (w : ℝ)| < 1) : z = w := by
  have h1 : ((|z - w| : ℤ) : ℝ) < 1 := by
    rw [Int.cast_abs, Int.cast_sub]; exact h
  have h2 : |z - w| < (1 : ℤ) := by exact_mod_cast h1
  have h3 : |z - w| ≤ 0 := Int.le_of_lt_add_one (by simpa using h2)
  have h4 : |z - w| = 0 := le_antisymm h3 (abs_nonneg _)
  have h5 : z - w = 0 := abs_eq_zero.mp h4
  omega

theorem const_of_lattice_const {k : ℕ} {G : Polynomial ℝ} {x L R A : ℝ}
    (hL : 1 ≤ L) (hR : 0 < R) (hA : 0 ≤ A) (hAR : A * R < 1)
    (hdeg : G.natDegree ≤ k)
    (hbound : ∀ t ∈ Set.Icc x (x + L), |G.derivative.eval t| ≤ A)
    (hRsmall : (k : ℝ) + 1 ≤ L / R)
    (hint : ∀ m : ℤ, ∃ z : ℤ, G.eval (R * m) = z) :
    ∃ c : ℤ, G = Polynomial.C (c : ℝ) := by
  set m0 : ℤ := ⌈x / R⌉ with hm0
  have hLR : ((k : ℝ) + 1) * R ≤ L := (le_div_iff₀ hR).mp hRsmall
  have hxR : x ≤ R * (m0 : ℝ) := by
    have h1 : x / R ≤ (m0 : ℝ) := by rw [hm0]; exact Int.le_ceil (x / R)
    have h2 := mul_le_mul_of_nonneg_left h1 hR.le
    rwa [mul_comm R (x / R), div_mul_cancel₀ x (ne_of_gt hR)] at h2
  have hmul0 : R * (m0 : ℝ) < x + R := by
    have h1 : (m0 : ℝ) < x / R + 1 := by rw [hm0]; exact Int.ceil_lt_add_one (x / R)
    have h2 := mul_lt_mul_of_pos_left h1 hR
    rw [mul_add, mul_one, mul_comm R (x / R), div_mul_cancel₀ x (ne_of_gt hR)] at h2
    linarith
  have hlbound : ∀ n : ℤ, m0 ≤ n → x ≤ R * (n : ℝ) := by
    intro n hn
    have h1 : R * (m0 : ℝ) ≤ R * (n : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hR.le
    linarith
  have hupper : ∀ n : ℤ, n ≤ m0 + (k : ℤ) → R * (n : ℝ) ≤ x + L := by
    intro n hn
    have h1 : R * (n : ℝ) ≤ R * (((m0 + (k:ℤ) : ℤ)) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hR.le
    have h2 : R * (((m0 + (k:ℤ) : ℤ)) : ℝ) = R * (m0:ℝ) + R * (k:ℝ) := by push_cast; ring
    have h3 : R * (m0:ℝ) + R * (k:ℝ) < x + L := by nlinarith [hmul0, hLR]
    linarith
  have hbetween : ∀ n : ℤ, m0 ≤ n → n + 1 ≤ m0 + (k:ℤ) →
      G.eval (R * (n:ℝ)) = G.eval (R * (((n+1 : ℤ)) : ℝ)) := by
    intro n hn1 hn2
    have ha : x ≤ R * (n:ℝ) := hlbound n hn1
    have hb : R * (((n+1:ℤ)) : ℝ) ≤ x + L := hupper (n+1) hn2
    have hnab : R * (n:ℝ) ≤ R * (((n+1:ℤ)) : ℝ) := by
      have : (n:ℝ) ≤ (((n+1:ℤ)) : ℝ) := by push_cast; linarith
      exact mul_le_mul_of_nonneg_left this hR.le
    have hmvt := abs_eval_sub_le hbound ha hb hnab
    have hdiff : R * (((n+1:ℤ)) : ℝ) - R * (n:ℝ) = R := by push_cast; ring
    have hle : |G.eval (R * (((n+1:ℤ)) : ℝ)) - G.eval (R * (n:ℝ))| ≤ A * R := by
      rwa [hdiff] at hmvt
    obtain ⟨za, hza⟩ := hint n
    obtain ⟨zb, hzb⟩ := hint (n+1)
    have hlt : |(zb:ℝ) - (za:ℝ)| < 1 := by
      rw [hzb, hza] at hle
      linarith [hle, hAR]
    have heq : zb = za := int_eq_of_abs_cast_sub_lt_one hlt
    rw [hzb, hza, heq]
  obtain ⟨c, hc⟩ := hint m0
  have hchain : ∀ j : ℕ, j ≤ k →
      G.eval (R * (((m0 + (j:ℤ) : ℤ)) : ℝ)) = G.eval (R * (m0:ℝ)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj' : j ≤ k := by omega
      have hstep := hbetween (m0 + (j:ℤ)) (by omega) (by omega)
      rw [show (((m0 + ((j+1:ℕ):ℤ) : ℤ)) : ℝ) = (((m0 + (j:ℤ)) + 1 : ℤ) : ℝ) from by
            push_cast; ring, ← hstep]
      exact ih hj'
  refine ⟨c, ?_⟩
  set p : Polynomial ℝ := G - Polynomial.C (c : ℝ) with hp
  have hp0 : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p := p)
      (f := fun i : Fin (k+1) => R * (((m0 + ((i:ℕ):ℤ) : ℤ)) : ℝ)) ?_ ?_ ?_
    · intro i j hij
      have h1 : (((m0 + ((i:ℕ):ℤ) : ℤ)) : ℝ) = (((m0 + ((j:ℕ):ℤ) : ℤ)) : ℝ) :=
        mul_left_cancel₀ (ne_of_gt hR) hij
      have h2 : (i:ℤ) = (j:ℤ) := by
        have : m0 + ((i:ℕ):ℤ) = m0 + ((j:ℕ):ℤ) := by exact_mod_cast h1
        omega
      have h3 : (i:ℕ) = (j:ℕ) := by omega
      exact Fin.ext h3
    · intro i
      have hi : (i:ℕ) ≤ k := by have := i.isLt; omega
      rw [hp, Polynomial.eval_sub, Polynomial.eval_C, hchain (i:ℕ) hi, hc]
      ring
    · rw [Fintype.card_fin]
      have hpd : p.natDegree ≤ k := by
        have hsub := Polynomial.natDegree_sub_le G (Polynomial.C (c:ℝ))
        rw [Polynomial.natDegree_C] at hsub
        rw [Nat.max_eq_left (Nat.zero_le G.natDegree)] at hsub
        exact le_trans hsub hdeg
      omega
  have : G - Polynomial.C (c:ℝ) = 0 := by rw [← hp]; exact hp0
  exact sub_eq_zero.mp this

end Work.N8
