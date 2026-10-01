import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.Sieve.selberg_double_sum_diagonalization

namespace Commons.NumberTheory.Sieve

open Finset

/-- **Möbius inversion with a real power weight.**  For `n > 0` and any real exponent `σ`,

    ∑_{δ ∣ n} ∑_{k ∣ δ} μ(k) (δ/k)^σ = n^σ ,

i.e. the divisor sum of the Möbius "difference" function `δ ↦ ∑_{k ∣ δ} μ(k) (δ/k)^σ`
reconstructs `n^σ`.  This is `sum_eq_iff_sum_mul_moebius_eq` applied to `m ↦ m^σ`. -/
lemma moebius_divisor_sum_rpow (n : ℕ) (hn : 0 < n) (σ : ℝ) :
    (∑ δ ∈ n.divisors,
        ∑ k ∈ δ.divisors,
          (ArithmeticFunction.moebius k : ℝ) * (((δ / k : ℕ) : ℝ) ^ σ))
      = (n : ℝ) ^ σ := by
  have hF : ∀ m : ℕ, m > 0 →
      (∑ i ∈ m.divisors,
        ∑ k ∈ i.divisors,
          (ArithmeticFunction.moebius k : ℝ) * (((i / k : ℕ) : ℝ) ^ σ))
        = (m : ℝ) ^ σ := by
    refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
      (f := fun (i : ℕ) => ∑ k ∈ i.divisors,
          (ArithmeticFunction.moebius k : ℝ) * (((i / k : ℕ) : ℝ) ^ σ))
      (g := fun (m : ℕ) => (m : ℝ) ^ σ)).mpr ?_
    intro m _
    rw [Nat.sum_divisorsAntidiagonal
      (fun i j => (ArithmeticFunction.moebius i : ℝ) * ((j : ℝ) ^ σ))]
  exact hF n hn

/-- **Diagonalization of the weighted gcd quadratic form.**  Let `T` be a finite set of
positive integers closed under divisors, let `c : ℕ → ℝ` satisfy
`(∑_{δ ∣ n} c δ) = n^σ` for all `n ∈ T`, and let `a : ℕ → ℝ`.  Then

    ∑_{d,e ∈ T} a_d a_e (gcd d e)^σ = ∑_{δ ∈ T} c_δ (∑_{d ∈ T, δ ∣ d} a_d)^2 .

The `σ = 1`, `c = φ` case is the classical Selberg diagonalization. -/
lemma sum_gcd_rpow_diagonalization (T : Finset ℕ) (hTpos : ∀ d ∈ T, 0 < d)
    (hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ T → l ∈ T) (σ : ℝ) (c : ℕ → ℝ)
    (hc : ∀ n ∈ T, (∑ δ ∈ n.divisors, c δ) = (n : ℝ) ^ σ) (a : ℕ → ℝ) :
    (∑ d ∈ T, ∑ e ∈ T, a d * a e * ((Nat.gcd d e : ℝ) ^ σ))
      = ∑ l ∈ T, c l * (∑ d ∈ T.filter (fun d => l ∣ d), a d) ^ 2 := by
  have pointwise : ∀ ⦃d e : ℕ⦄, d ∈ T → e ∈ T →
      (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then c l else 0) = (Nat.gcd d e : ℝ) ^ σ := by
    intro d e hd he
    have hgne : Nat.gcd d e ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d e) (hTpos d hd)).ne'
    have hset : T.filter (fun l => l ∣ d ∧ l ∣ e) = (Nat.gcd d e).divisors := by
      ext l
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨_hlT, hld, hle⟩
        exact ⟨⟨hld, hle⟩, hgne⟩
      · rintro ⟨⟨hld, hle⟩, _⟩
        exact ⟨hTclosed hld hd, hld, hle⟩
    calc (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then c l else 0)
        = ∑ l ∈ T.filter (fun l => l ∣ d ∧ l ∣ e), c l := by rw [Finset.sum_filter]
      _ = ∑ l ∈ (Nat.gcd d e).divisors, c l := by rw [hset]
      _ = (Nat.gcd d e : ℝ) ^ σ := hc _ (hTclosed (Nat.gcd_dvd_left d e) hd)
  have step1 : (∑ d ∈ T, ∑ e ∈ T, a d * a e * ((Nat.gcd d e : ℝ) ^ σ))
      = ∑ d ∈ T, ∑ e ∈ T,
          a d * a e * (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then c l else 0) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    rw [pointwise hd he]
  rw [step1]
  have step2 : (∑ d ∈ T, ∑ e ∈ T,
        a d * a e * (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then c l else 0))
      = ∑ l ∈ T, c l * (∑ d ∈ T.filter (fun d => l ∣ d), a d) ^ 2 := by
    calc (∑ d ∈ T, ∑ e ∈ T,
            a d * a e * (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then c l else 0))
        = ∑ d ∈ T, ∑ e ∈ T, ∑ l ∈ T,
            a d * a e * (if (l ∣ d ∧ l ∣ e) then c l else 0) := by
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro e _
          rw [Finset.mul_sum]
      _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T,
            a d * a e * (if (l ∣ d ∧ l ∣ e) then c l else 0) := by
          rw [triple_sum_swap]
      _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T,
            (if (l ∣ d ∧ l ∣ e) then a d * a e * c l else 0) := by
          apply Finset.sum_congr rfl; intro l _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro e _
          rw [mul_ite, mul_zero]
      _ = ∑ l ∈ T, c l * (∑ d ∈ T.filter (fun d => l ∣ d), a d) ^ 2 := by
          apply Finset.sum_congr rfl; intro l _
          rw [sum_sum_ite, sq]; ring
  rw [step2]

/-- **Selberg diagonalization of the σ-weighted gcd form.**  For `1 ≤ z`, real `σ` and
any weights `w : ℕ → ℝ`,

    ∑_{d,e ≤ z} w_d w_e (gcd d e)^σ / (d^σ e^σ)
      = ∑_{δ ≤ z} (∑_{k ∣ δ} μ(k) (δ/k)^σ) (∑_{d ≤ z, δ ∣ d} w_d / d^σ)^2 .

Write `(gcd d e)^σ = ∑_{δ ∣ gcd d e} c_δ` with `c_δ = ∑_{k ∣ δ} μ(k) (δ/k)^σ`
(Möbius inversion) and exchange the order of summation. -/
theorem selberg_diagonalization_sigma (z : ℕ) (hz : 1 ≤ z) (σ : ℝ) (hσ : 1 ≤ σ)
    (w : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        w d * w e * ((Nat.gcd d e : ℝ) ^ σ) / (((d:ℝ)^σ) * ((e:ℝ)^σ)))
      = ∑ δ ∈ Finset.Icc 1 z,
          (∑ k ∈ δ.divisors, (ArithmeticFunction.moebius k : ℝ) * (((δ / k : ℕ):ℝ) ^ σ))
            * (∑ d ∈ (Finset.Icc 1 z).filter (fun d => δ ∣ d), w d / (d:ℝ)^σ) ^ 2 := by
  have hTpos : ∀ d ∈ Finset.Icc 1 z, 0 < d := by
    intro d hd
    have h1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    omega
  have hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ Finset.Icc 1 z → l ∈ Finset.Icc 1 z := by
    intro l d hld hd
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hld hdpos
    exact Finset.mem_Icc.mpr ⟨by omega, le_trans (Nat.le_of_dvd hdpos hld) hdz⟩
  have hc : ∀ n ∈ Finset.Icc 1 z,
      (∑ δ ∈ n.divisors,
          ∑ k ∈ δ.divisors,
            (ArithmeticFunction.moebius k : ℝ) * (((δ / k : ℕ) : ℝ) ^ σ))
        = (n : ℝ) ^ σ := by
    intro n hn
    exact moebius_divisor_sum_rpow n (hTpos n hn) σ
  have hconv : (∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        w d * w e * ((Nat.gcd d e : ℝ) ^ σ) / (((d:ℝ)^σ) * ((e:ℝ)^σ)))
      = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
          (w d / (d:ℝ)^σ) * (w e / (e:ℝ)^σ) * ((Nat.gcd d e : ℝ) ^ σ) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    have hdpos : (0:ℝ) < (d:ℝ) := by
      have : 0 < d := hTpos d hd
      exact_mod_cast this
    have hepos : (0:ℝ) < (e:ℝ) := by
      have : 0 < e := hTpos e he
      exact_mod_cast this
    have hd0 : (d:ℝ)^σ ≠ 0 := (Real.rpow_pos_of_pos hdpos σ).ne'
    have he0 : (e:ℝ)^σ ≠ 0 := (Real.rpow_pos_of_pos hepos σ).ne'
    rw [div_mul_div_comm, div_mul_eq_mul_div]
  rw [hconv]
  exact sum_gcd_rpow_diagonalization (Finset.Icc 1 z) hTpos hTclosed σ
    (fun δ => ∑ k ∈ δ.divisors,
        (ArithmeticFunction.moebius k : ℝ) * (((δ / k : ℕ):ℝ) ^ σ))
    hc (fun d => w d / (d:ℝ)^σ)

end Commons.NumberTheory.Sieve