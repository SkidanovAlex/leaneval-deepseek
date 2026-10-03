import Mathlib
import Submission.Work.Peluse.MajorArc.Defs

/-!
# Plancherel's identity for the windowed discrete Fourier transform

For `L ≥ 1`, `2K < L` and `A : ℤ → ℂ` supported on the window `[-K, K]`, the discrete Fourier
transform `∑_{n ∈ [-K,K]} A n · e(-kn/L)`, `k = 0, …, L-1`, satisfies the Plancherel identity

  `∑_{k < L} ‖∑_{n ∈ [-K,K]} A n · e(-kn/L)‖² = L · ∑_{n ∈ [-K,K]} ‖A n‖²`.

The elementary proof expands the square, conjugates, and evaluates the resulting sums over `k`
by orthogonality of the additive character `e` over `ℤ/L`; the hypothesis `2K < L` guarantees
that the only pairs `(n,m)` of the window with `L ∣ m - n` are the diagonal ones `m = n`.
-/

open scoped BigOperators

namespace Work.Peluse.Fourier

/-- `ee (n * x) = (ee x) ^ n`. -/
private lemma ee_nat_mul (x : ℝ) : ∀ n : ℕ, ee (n * x) = (ee x) ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Nat.cast_succ, add_mul, one_mul, ee_add, ee_nat_mul x n, pow_succ]

/-- Orthogonality of the additive character over `ℤ/L`. -/
private lemma ee_orthogonality (L : ℕ) (hL : 1 ≤ L) (m : ℤ) :
    ∑ k ∈ Finset.range L, ee ((k : ℝ) * (m : ℝ) / (L : ℝ)) =
      if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
  have hLr : (L : ℝ) ≠ 0 := by positivity
  have hterm : ∀ k : ℕ, ee ((k : ℝ) * (m : ℝ) / (L : ℝ)) = ee ((m : ℝ) / (L : ℝ)) ^ k := by
    intro k
    rw [← ee_nat_mul]
    congr 1
    ring
  have hrL : ee ((m : ℝ) / (L : ℝ)) ^ L = 1 := by
    rw [← ee_nat_mul]
    have h : (L : ℝ) * ((m : ℝ) / (L : ℝ)) = (m : ℝ) := by field_simp
    rw [h, ee_int]
  have hkey : ee ((m : ℝ) / (L : ℝ)) = 1 ↔ (L : ℤ) ∣ m := by
    rw [ee_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      have h2 : (m : ℝ) = (n : ℝ) * (L : ℝ) := by
        rw [div_eq_iff hLr] at hn
        exact hn
      refine ⟨n, ?_⟩
      have h3 : m = n * (L : ℤ) := by exact_mod_cast h2
      rw [h3]; ring
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have h2 : (m : ℝ) = (L : ℝ) * (n : ℝ) := by exact_mod_cast hn
      rw [h2]
      field_simp
  by_cases hd : (L : ℤ) ∣ m
  · rw [if_pos hd]
    have hr1 : ee ((m : ℝ) / (L : ℝ)) = 1 := hkey.mpr hd
    calc ∑ k ∈ Finset.range L, ee ((k : ℝ) * (m : ℝ) / (L : ℝ))
        = ∑ k ∈ Finset.range L, ee ((m : ℝ) / (L : ℝ)) ^ k :=
          Finset.sum_congr rfl (fun k _ => hterm k)
      _ = ∑ _k ∈ Finset.range L, (1 : ℂ) := by rw [hr1]; simp
      _ = (L : ℂ) := by simp
  · rw [if_neg hd]
    have hr1 : ee ((m : ℝ) / (L : ℝ)) ≠ 1 := fun h => hd (hkey.mp h)
    calc ∑ k ∈ Finset.range L, ee ((k : ℝ) * (m : ℝ) / (L : ℝ))
        = ∑ k ∈ Finset.range L, ee ((m : ℝ) / (L : ℝ)) ^ k :=
          Finset.sum_congr rfl (fun k _ => hterm k)
      _ = (ee ((m : ℝ) / (L : ℝ)) ^ L - 1) / (ee ((m : ℝ) / (L : ℝ)) - 1) :=
          geom_sum_eq hr1 L
      _ = 0 := by rw [hrL]; simp

/-- **Plancherel for the windowed DFT.** -/
theorem dftPlancherel (L K : ℕ) (hL : 1 ≤ L) (hKL : 2 * K < L) (A : ℤ → ℂ) :
    (∑ k ∈ Finset.range L,
        ‖∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            A n * Work.Peluse.ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))‖ ^ 2)
      = (L : ℝ) * ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖A n‖ ^ 2 := by
  set I : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) with hI
  -- the only pairs in the window with `L ∣ m - n` are the diagonal ones
  have hif : ∀ n m : ℤ, n ∈ I → m ∈ I → ((L : ℤ) ∣ (m - n) ↔ m = n) := by
    intro n m hn hm
    rw [hI, Finset.mem_Icc] at hn hm
    have hn' : |n| ≤ (K : ℤ) := abs_le.mpr ⟨hn.1, hn.2⟩
    have hm' : |m| ≤ (K : ℤ) := abs_le.mpr ⟨hm.1, hm.2⟩
    have h2K : (2 : ℤ) * (K : ℤ) < (L : ℤ) := by exact_mod_cast hKL
    constructor
    · intro hdvd
      have habs : |m - n| ≤ |m| + |n| := by
        rw [sub_eq_add_neg]
        calc |m + -n| ≤ |m| + |-n| := abs_add_le _ _
          _ = |m| + |n| := by rw [abs_neg]
      have hlt : |m - n| < (L : ℤ) := by linarith
      have h0 : m - n = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      omega
    · intro hmn
      rw [hmn, sub_self]
      exact dvd_zero _
  -- conjugation of the DFT sum
  have hstar : ∀ k : ℕ, star (∑ n ∈ I, A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ)))
      = ∑ n ∈ I, star (A n) * ee ((k : ℝ) * (n : ℝ) / (L : ℝ)) := by
    intro k
    rw [star_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [star_mul, star_ee,
      show -(-((k : ℝ) * (n : ℝ)) / (L : ℝ)) = ((k : ℝ) * (n : ℝ)) / (L : ℝ) by ring]
    ring
  -- the pointwise product of a term and a conjugated term
  have hpt : ∀ (k : ℕ) (n m : ℤ),
      (A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))) *
          (star (A m) * ee ((k : ℝ) * (m : ℝ) / (L : ℝ)))
        = (A n * star (A m)) * ee ((k : ℝ) * ((m - n : ℤ) : ℝ) / (L : ℝ)) := by
    intro k n m
    rw [show (A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))) *
          (star (A m) * ee ((k : ℝ) * (m : ℝ) / (L : ℝ)))
        = (A n * star (A m)) *
            (ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ)) *
              ee ((k : ℝ) * (m : ℝ) / (L : ℝ))) by ring]
    rw [show ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ)) * ee ((k : ℝ) * (m : ℝ) / (L : ℝ))
        = ee ((k : ℝ) * ((m - n : ℤ) : ℝ) / (L : ℝ)) by
          rw [← ee_add]
          congr 1
          push_cast
          ring]
  -- `‖·‖²` as a product with the conjugate
  have hnorm : ∀ k : ℕ,
      ((‖∑ n ∈ I, A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))‖ ^ 2 : ℝ) : ℂ)
        = (∑ n ∈ I, A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))) *
          star (∑ n ∈ I, A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))) := by
    intro k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [Complex.star_def]
  have main : (∑ k ∈ Finset.range L,
        ((‖∑ n ∈ I, A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))‖ ^ 2 : ℝ) : ℂ))
      = (L : ℂ) * ∑ n ∈ I, ((‖A n‖ ^ 2 : ℝ) : ℂ) := by
    calc (∑ k ∈ Finset.range L,
            ((‖∑ n ∈ I, A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))‖ ^ 2 : ℝ) : ℂ))
        = ∑ k ∈ Finset.range L,
            (∑ n ∈ I, A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))) *
              star (∑ n ∈ I, A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))) :=
          Finset.sum_congr rfl (fun k _ => hnorm k)
      _ = ∑ k ∈ Finset.range L, ∑ n ∈ I, ∑ m ∈ I,
            (A n * ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))) *
              (star (A m) * ee ((k : ℝ) * (m : ℝ) / (L : ℝ))) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [hstar k, Finset.sum_mul_sum]
      _ = ∑ k ∈ Finset.range L, ∑ n ∈ I, ∑ m ∈ I,
            (A n * star (A m)) * ee ((k : ℝ) * ((m - n : ℤ) : ℝ) / (L : ℝ)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          exact Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => hpt k n m))
      _ = ∑ n ∈ I, ∑ m ∈ I, ∑ k ∈ Finset.range L,
            (A n * star (A m)) * ee ((k : ℝ) * ((m - n : ℤ) : ℝ) / (L : ℝ)) := by
          calc ∑ k ∈ Finset.range L, ∑ n ∈ I, ∑ m ∈ I,
                (A n * star (A m)) * ee ((k : ℝ) * ((m - n : ℤ) : ℝ) / (L : ℝ))
              = ∑ n ∈ I, ∑ k ∈ Finset.range L, ∑ m ∈ I,
                (A n * star (A m)) * ee ((k : ℝ) * ((m - n : ℤ) : ℝ) / (L : ℝ)) :=
                Finset.sum_comm
            _ = ∑ n ∈ I, ∑ m ∈ I, ∑ k ∈ Finset.range L,
                (A n * star (A m)) * ee ((k : ℝ) * ((m - n : ℤ) : ℝ) / (L : ℝ)) :=
                Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
      _ = ∑ n ∈ I, ∑ m ∈ I,
            (A n * star (A m)) * (if (L : ℤ) ∣ (m - n) then (L : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
          rw [← Finset.mul_sum, ee_orthogonality L hL (m - n)]
      _ = ∑ n ∈ I, ∑ m ∈ I, (A n * star (A m)) * (if m = n then (L : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => ?_))
          by_cases h : m = n
          · subst h; simp
          · have hd : ¬ (L : ℤ) ∣ (m - n) := fun hd => h ((hif n m hn hm).mp hd)
            simp [h, hd]
      _ = ∑ n ∈ I, (A n * star (A n)) * (L : ℂ) := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          calc ∑ m ∈ I, (A n * star (A m)) * (if m = n then (L : ℂ) else 0)
              = ∑ m ∈ I, if m = n then (A n * star (A m)) * (L : ℂ) else 0 :=
                Finset.sum_congr rfl (fun m _ => by by_cases h : m = n <;> simp [h])
            _ = (A n * star (A n)) * (L : ℂ) := by
                rw [Finset.sum_ite_eq' I n (fun m => (A n * star (A m)) * (L : ℂ)), if_pos hn]
      _ = (L : ℂ) * ∑ n ∈ I, ((‖A n‖ ^ 2 : ℝ) : ℂ) := by
          rw [← Finset.sum_mul]
          have h3 : (∑ n ∈ I, A n * star (A n)) = ∑ n ∈ I, ((‖A n‖ ^ 2 : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
            simp only [Complex.star_def]
          rw [h3]
          ring
  exact Complex.ofReal_inj.mp (by
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast] using main)

end Work.Peluse.Fourier
