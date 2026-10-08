import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.s34Engines

namespace Work.BSW.S3

open Work.BSW

/-- **Bender §3.3/3.4 arithmetic** (`Work.BSW.BSWS34ArithProp`).

Inputs: `k = |K| > 4` even, `ε = ±1`, `I = |G:H| = (2k+ε)(k+ε)`, `f = |F|` odd, `n = |K ⊓ M|` even
with `n ∣ k` and `n ∣ f - 1`, `m = |G:M|` with `f n m = 2 k I`, `f ∣ I`, and Bender's counting
inequalities (`k(k+1+3ε) < (k+1)f`, `1 + f(2k/n - 1) ≤ m`, `f ∣ m - (1 + f(2k/n-1))`,
`f(k+1) ≤ I`, `I - f(k+1) ≤ m - (1 + f(2k/n-1))`).

Output: either `ε = 1` with `f = 2k+1`, `n = k` and `I = f(k+1)` (case (i)), or `ε = -1` with
`f = k-1` and `n = 2` (case (ii)).

The proof writes `I = f j` and `m = (2k/n) j`, transports the last counting inequality to the
integer inequality `f(j-k-1) ≤ (2k/n)(j-f) + f - 1` (`s34KeyOfNat`), and then applies the two
integer engines: `s34PosEng` gives `j = k+1` in case `ε = 1` (whence `f = 2k+1`, and the inequality
`1 + f(2k/n-1) ≤ m` forces `2k/n = 2`, i.e. `n = k`), while `s34NegEng` gives `f = k-1` in case
`ε = -1` (whence `n ∣ k` and `n ∣ k-2` force `n = 2`). -/
theorem s34Arith : Work.BSW.BSWS34ArithProp := by
  intro k f n m I ε hk hkeven hε hI hfodd hneven hnpos hndk hndf1 hfnm hfdI hineq h1 h2 h3 h4
  have hfpos : 0 < f := by rcases hfodd with ⟨g, hg⟩; omega
  have hn2 : 2 ≤ n := by rcases hneven with ⟨g, hg⟩; omega
  have hnA : n * (2 * k / n) = 2 * k := Nat.mul_div_cancel' (dvd_mul_of_dvd_right hndk 2)
  have hA2 : 2 ≤ 2 * k / n := by
    rw [Nat.le_div_iff_mul_le hnpos]
    have hnk : n ≤ k := Nat.le_of_dvd (by omega) hndk
    omega
  have hAk : 2 * k / n ≤ k := by
    have h2A : 2 * (2 * k / n) ≤ n * (2 * k / n) := Nat.mul_le_mul_right (2 * k / n) hn2
    omega
  rcases hε with hε1 | hεm1
  · -- case ε = 1
    subst hε1
    have hInat : I = (2 * k + 1) * (k + 1) := by exact_mod_cast hI
    obtain ⟨j, hj⟩ := hfdI
    have hjge : k + 1 ≤ j := by
      have hle : f * (k + 1) ≤ f * j := by rw [← hj]; exact h3
      exact Nat.le_of_mul_le_mul_left hle hfpos
    have hfgek2 : k + 2 ≤ f := by
      by_contra hc
      have hcZ : (f : ℤ) ≤ (k : ℤ) + 1 := by omega
      have hkZ : (0 : ℤ) < (k : ℤ) := by omega
      have hK1 : (0 : ℤ) ≤ (k : ℤ) + 1 := by omega
      have hprod : ((k : ℤ) + 1) * (f : ℤ) ≤ ((k : ℤ) + 1) * ((k : ℤ) + 1) :=
        mul_le_mul_of_nonneg_left hcZ hK1
      nlinarith [hineq, hprod, hkZ]
    have hmA : m = (2 * k / n) * j := by
      have hnm : n * m = 2 * k * j := by
        have hfm : f * (n * m) = f * (2 * k * j) := by
          have hL : f * (n * m) = 2 * k * I := by rw [← mul_assoc]; exact hfnm
          have hR : 2 * k * I = f * (2 * k * j) := by rw [hj]; ring
          rw [hL, hR]
        exact Nat.eq_of_mul_eq_mul_left hfpos hfm
      rw [hnA.symm, mul_assoc] at hnm
      exact Nat.eq_of_mul_eq_mul_left hnpos hnm
    have hkey := s34KeyOfNat k f n m I j hj hmA h1 h3 h4
    have hJeq : j = k + 1 := by
      have hK5 : (5 : ℤ) ≤ (k : ℤ) := by omega
      have hA2Z : (2 : ℤ) ≤ ((2 * k / n : ℕ) : ℤ) := by omega
      have hAKZ : ((2 * k / n : ℕ) : ℤ) ≤ (k : ℤ) := by omega
      have hF1Z : (1 : ℤ) ≤ (f : ℤ) := by omega
      have hJZ : (k : ℤ) + 1 ≤ (j : ℤ) := by omega
      have hFgeZ : (k : ℤ) + 2 ≤ (f : ℤ) := by omega
      have hres := s34PosEng (k : ℤ) (f : ℤ) (j : ℤ) ((2 * k / n : ℕ) : ℤ)
        hK5 hA2Z hAKZ hF1Z hJZ hkey hFgeZ
      omega
    have hfeq : f = 2 * k + 1 := by
      have h2' : f * (k + 1) = (2 * k + 1) * (k + 1) := by
        calc f * (k + 1) = f * j := by rw [hJeq]
          _ = I := hj.symm
          _ = (2 * k + 1) * (k + 1) := hInat
      exact Nat.mul_right_cancel (by omega : 0 < k + 1) h2'
    have hnAeq : n = k := by
      rw [hmA, hJeq] at h1
      have hA1 : 1 ≤ 2 * k / n := by omega
      have h1Z : (1 : ℤ) + (f : ℤ) * (((2 * k / n : ℕ) : ℤ) - 1) ≤
          ((2 * k / n : ℕ) : ℤ) * ((k : ℤ) + 1) := by
        have hc : (((1 + f * (2 * k / n - 1)) : ℕ) : ℤ) ≤
            (((2 * k / n) * (k + 1) : ℕ) : ℤ) := by exact_mod_cast h1
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hA1] at hc
        push_cast at hc
        exact hc
      have hfZ : (f : ℤ) = 2 * (k : ℤ) + 1 := by omega
      have hkZ : (0 : ℤ) < (k : ℤ) := by omega
      have hAle : ((2 * k / n : ℕ) : ℤ) ≤ 2 := by nlinarith [h1Z, hfZ, hkZ]
      have hAtwo : 2 * k / n = 2 := by omega
      have hn2k : n * 2 = 2 * k := by rw [← hnA, hAtwo]
      have hn2k' : n * 2 = k * 2 := by rw [hn2k, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) hn2k'
    exact Or.inl ⟨rfl, hfeq, hnAeq, by rw [hInat, hfeq]⟩
  · -- case ε = -1
    subst hεm1
    have hk1 : 1 ≤ k := by omega
    have hInat : I = (2 * k - 1) * (k - 1) := by
      have ha : ((2 * k - 1 : ℕ) : ℤ) = 2 * (k : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; push_cast; ring
      have hb : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
        rw [Nat.cast_sub hk1]; push_cast; ring
      have hc : (I : ℤ) = (((2 * k - 1) * (k - 1) : ℕ) : ℤ) := by
        push_cast
        rw [ha, hb]
        exact hI
      exact_mod_cast hc
    have hk6 : 6 ≤ k := by rcases hkeven with ⟨g, hg⟩; omega
    obtain ⟨j, hj⟩ := hfdI
    have hjge : k + 1 ≤ j := by
      have hle : f * (k + 1) ≤ f * j := by rw [← hj]; exact h3
      exact Nat.le_of_mul_le_mul_left hle hfpos
    have hfge : k - 1 ≤ f := by
      have hge : k - 2 ≤ f := by
        by_contra hc
        have hcZ : (f : ℤ) ≤ (k : ℤ) - 3 := by omega
        have hkZ : (6 : ℤ) ≤ (k : ℤ) := by omega
        have hK1 : (0 : ℤ) ≤ (k : ℤ) + 1 := by omega
        have hprod : ((k : ℤ) + 1) * (f : ℤ) ≤ ((k : ℤ) + 1) * ((k : ℤ) - 3) :=
          mul_le_mul_of_nonneg_left hcZ hK1
        nlinarith [hineq, hprod, hkZ]
      rcases hfodd with ⟨g, hg⟩
      rcases hkeven with ⟨e, he⟩
      omega
    have hmA : m = (2 * k / n) * j := by
      have hnm : n * m = 2 * k * j := by
        have hfm : f * (n * m) = f * (2 * k * j) := by
          have hL : f * (n * m) = 2 * k * I := by rw [← mul_assoc]; exact hfnm
          have hR : 2 * k * I = f * (2 * k * j) := by rw [hj]; ring
          rw [hL, hR]
        exact Nat.eq_of_mul_eq_mul_left hfpos hfm
      rw [hnA.symm, mul_assoc] at hnm
      exact Nat.eq_of_mul_eq_mul_left hnpos hnm
    have hkey := s34KeyOfNat k f n m I j hj hmA h1 h3 h4
    have hFJz : (f : ℤ) * (j : ℤ) = (2 * (k : ℤ) - 1) * ((k : ℤ) - 1) := by
      have hjZ : (I : ℤ) = (f : ℤ) * (j : ℤ) := by rw [hj]; push_cast; ring
      rw [← hjZ]
      exact hI
    have hfeq : f = k - 1 := by
      have hK6 : (6 : ℤ) ≤ (k : ℤ) := by omega
      have hA2Z : (2 : ℤ) ≤ ((2 * k / n : ℕ) : ℤ) := by omega
      have hAKZ : ((2 * k / n : ℕ) : ℤ) ≤ (k : ℤ) := by omega
      have hF1Z : (1 : ℤ) ≤ (f : ℤ) := by omega
      have hJZ : (k : ℤ) + 1 ≤ (j : ℤ) := by omega
      have hFgeZ : (k : ℤ) - 1 ≤ (f : ℤ) := by omega
      have hres := s34NegEng (k : ℤ) (f : ℤ) (j : ℤ) ((2 * k / n : ℕ) : ℤ)
        hK6 hA2Z hAKZ hF1Z hJZ hkey hFJz hFgeZ
      omega
    have hn_eq : n = 2 := by
      have hnd : n ∣ k - 2 := by
        have h := hndf1
        rw [hfeq] at h
        have he : (k - 1) - 1 = k - 2 := by omega
        rwa [he] at h
      have h2' : n ∣ 2 := by
        have hd := Nat.dvd_sub hndk hnd
        have he : k - (k - 2) = 2 := by omega
        rwa [he] at hd
      have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2'
      omega
    exact Or.inr ⟨rfl, hfeq, hn_eq⟩

end Work.BSW.S3
