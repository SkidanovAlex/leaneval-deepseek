import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors

namespace Commons.NumberTheory.ArithmeticFunction

/-- Hyperbola method: summing a function of the divisor pairs `(d, n/d)` over `n ≤ N`
equals summing over all pairs `(d, e)` with `1 ≤ d`, `1 ≤ e`, `d * e ≤ N`. -/
theorem sum_divisors_swap_hyperbola (f : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), ∑ d ∈ n.divisors, f d (n / d)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), f d e := by
  -- The common set of pairs `(d, e)` with `1 ≤ d ≤ N`, `1 ≤ e ≤ N`, `d * e ≤ N`.
  set P : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x => x.1 * x.2 ≤ N) with hP
  -- ## The right-hand side equals the sum over `P`.
  have hR : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), f d e)
      = ∑ x ∈ P, f x.1 x.2 := by
    have hIcc : ∀ d ∈ Finset.Icc 1 N,
        Finset.Icc 1 (N / d) = (Finset.Icc 1 N).filter (fun e => d * e ≤ N) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : 0 < d := hd1
      ext e
      simp only [Finset.mem_Icc, Finset.mem_filter]
      constructor
      · rintro ⟨he1, he2⟩
        have hde : d * e ≤ N := by
          have := (Nat.le_div_iff_mul_le hdpos).mp he2
          rwa [Nat.mul_comm] at this
        refine ⟨⟨he1, ?_⟩, hde⟩
        calc e = e * 1 := (mul_one e).symm
          _ ≤ e * d := Nat.mul_le_mul_left e hd1
          _ = d * e := Nat.mul_comm e d
          _ ≤ N := hde
      · rintro ⟨⟨he1, _⟩, hde⟩
        refine ⟨he1, (Nat.le_div_iff_mul_le hdpos).mpr ?_⟩
        rwa [Nat.mul_comm] at hde
    calc (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), f d e)
        = ∑ d ∈ Finset.Icc 1 N,
            ∑ e ∈ (Finset.Icc 1 N).filter (fun e => d * e ≤ N), f d e :=
          Finset.sum_congr rfl fun d hd => by rw [hIcc d hd]
      _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
            (if d * e ≤ N then f d e else 0) :=
          Finset.sum_congr rfl fun d _ => Finset.sum_filter _ _
      _ = ∑ x ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
            (if x.1 * x.2 ≤ N then f x.1 x.2 else 0) :=
          (Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
            (fun x : ℕ × ℕ => if x.1 * x.2 ≤ N then f x.1 x.2 else 0)).symm
      _ = ∑ x ∈ P, f x.1 x.2 := by
          rw [hP, Finset.sum_filter]
  -- ## The left-hand side equals the sum over `P`.
  have hL : (∑ n ∈ Finset.range (N + 1), ∑ d ∈ n.divisors, f d (n / d))
      = ∑ x ∈ P, f x.1 x.2 := by
    have step1 : (∑ n ∈ Finset.range (N + 1), ∑ d ∈ n.divisors, f d (n / d))
        = ∑ n ∈ Finset.range (N + 1), ∑ x ∈ n.divisorsAntidiagonal, f x.1 x.2 :=
      Finset.sum_congr rfl fun n _ =>
        (Nat.sum_divisorsAntidiagonal (fun a b => f a b)).symm
    have step2 : (∑ n ∈ Finset.range (N + 1), ∑ x ∈ n.divisorsAntidiagonal, f x.1 x.2)
        = ∑ p ∈ (Finset.range (N + 1)).sigma (fun n => n.divisorsAntidiagonal),
            f p.2.1 p.2.2 :=
      Finset.sum_sigma' _ _ _
    have step3 : (∑ p ∈ (Finset.range (N + 1)).sigma (fun n => n.divisorsAntidiagonal),
            f p.2.1 p.2.2)
        = ∑ x ∈ P, f x.1 x.2 := by
      refine Finset.sum_bij (fun (p : Σ _ : ℕ, ℕ × ℕ) (_ : p ∈ _) => p.2) ?_ ?_ ?_ ?_
      · -- the image of an element lies in `P`
        rintro ⟨n, x⟩ hp
        have hn : n ∈ Finset.range (N + 1) := (Finset.mem_sigma.mp hp).1
        have hx : x ∈ n.divisorsAntidiagonal := (Finset.mem_sigma.mp hp).2
        rw [Finset.mem_range] at hn
        obtain ⟨hmul, hnne⟩ := Nat.mem_divisorsAntidiagonal.mp hx
        have hx1 : 0 < x.1 := Nat.pos_of_ne_zero fun h =>
          hnne (by rw [h, zero_mul] at hmul; exact hmul.symm)
        have hx2 : 0 < x.2 := Nat.pos_of_ne_zero fun h =>
          hnne (by rw [h, mul_zero] at hmul; exact hmul.symm)
        have hx1N : x.1 ≤ N := by
          calc x.1 = x.1 * 1 := (mul_one x.1).symm
            _ ≤ x.1 * x.2 := Nat.mul_le_mul_left x.1 hx2
            _ = n := hmul
            _ ≤ N := by omega
        have hx2N : x.2 ≤ N := by
          calc x.2 = 1 * x.2 := (one_mul x.2).symm
            _ ≤ x.1 * x.2 := Nat.mul_le_mul_right x.2 hx1
            _ = n := hmul
            _ ≤ N := by omega
        rw [hP]
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨⟨hx1, hx1N⟩, ⟨hx2, hx2N⟩⟩, by rw [hmul]; omega⟩
      · -- injectivity
        rintro ⟨n₁, x₁⟩ ha₁ ⟨n₂, x₂⟩ ha₂ heq
        simp only at heq
        have hx₁ : x₁ ∈ n₁.divisorsAntidiagonal := (Finset.mem_sigma.mp ha₁).2
        have hx₂ : x₂ ∈ n₂.divisorsAntidiagonal := (Finset.mem_sigma.mp ha₂).2
        obtain ⟨hm₁, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx₁
        obtain ⟨hm₂, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx₂
        rcases heq with rfl
        rw [← hm₁, hm₂]
      · -- surjectivity
        intro b hb
        obtain ⟨x1, x2⟩ := b
        rw [hP] at hb
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hb
        obtain ⟨⟨⟨hx1, _⟩, ⟨hx2, _⟩⟩, hmul⟩ := hb
        refine ⟨⟨x1 * x2, (x1, x2)⟩, ?_, rfl⟩
        rw [Finset.mem_sigma]
        refine ⟨?_, ?_⟩
        · show x1 * x2 ∈ Finset.range (N + 1)
          rw [Finset.mem_range]; omega
        · show (x1, x2) ∈ (x1 * x2).divisorsAntidiagonal
          rw [Nat.mem_divisorsAntidiagonal]
          exact ⟨rfl, mul_ne_zero (by omega) (by omega)⟩
      · -- the summands agree
        intro p _
        rfl
    exact step1.trans (step2.trans step3)
  rw [hL, hR]

end Commons.NumberTheory.ArithmeticFunction