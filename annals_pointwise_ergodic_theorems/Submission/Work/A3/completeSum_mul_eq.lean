import Mathlib
import Submission.Work.A3.Circle

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multiplicativity of the complete exponential sum under the Chinese remainder theorem

For `(m,n) = 1` (witnessed by integers `u,v` with `u n + v m = 1`), the complete sum
`completeSum Q a q = ∑_{r<q} e(-2πi a Q(r)/q)` satisfies

`completeSum Q a (m*n) = completeSum Q (a*u) m * completeSum Q (a*v) n`.

The proof is the classical CRT factorisation: the residue `r mod mn` is determined by
`(r mod m, r mod n)`, and for an integer polynomial `Q` one has
`Q(r) ≡ u n Q(r mod m) + v m Q(r mod n) [MOD m*n]`, so the two characters agree.
-/

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

noncomputable section

/-- Integer polynomial evaluation respects congruence modulo `k`. -/
lemma dvd_eval_sub_eval (Q : Polynomial ℤ) {k : ℕ} {x y : ℤ} (h : (k : ℤ) ∣ x - y) :
    (k : ℤ) ∣ Q.eval x - Q.eval y := by
  have hyx : ((y : ℤ) : ZMod k) = ((x : ℤ) : ZMod k) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact h
  have heq : ((Q.eval x : ℤ) : ZMod k) = ((Q.eval y : ℤ) : ZMod k) := by
    rw [show ((Q.eval x : ℤ) : ZMod k)
          = Q.eval₂ (Int.castRingHom (ZMod k)) ((x : ℤ) : ZMod k)
        from (Polynomial.eval₂_at_apply (p := Q) (Int.castRingHom (ZMod k)) x).symm,
        show ((Q.eval y : ℤ) : ZMod k)
          = Q.eval₂ (Int.castRingHom (ZMod k)) ((y : ℤ) : ZMod k)
        from (Polynomial.eval₂_at_apply (p := Q) (Int.castRingHom (ZMod k)) y).symm, hyx]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub (Q.eval y) (Q.eval x) k).mp heq.symm

/-- Periodicity of the character `x ↦ e^{-2πi x/q}` in `x` modulo `q`. -/
lemma exp_char_period (q : ℕ) (hq : q ≠ 0) {X Y : ℤ} (h : (q : ℤ) ∣ X - Y) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((X : ℝ) / (q : ℝ))))
      = Complex.exp (-(2 * Real.pi * Complex.I * ((Y : ℝ) / (q : ℝ)))) := by
  obtain ⟨k, hk⟩ := h
  have hkR : (X : ℝ) - (Y : ℝ) = (q : ℝ) * (k : ℝ) := by
    have h1 : ((X - Y : ℤ) : ℝ) = ((((q : ℤ)) * k : ℤ) : ℝ) := by rw [hk]
    push_cast at h1
    linarith [h1]
  have hd : (X : ℝ) / (q : ℝ) - (Y : ℝ) / (q : ℝ) = (k : ℝ) := by
    field_simp
    linarith
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  push_cast
  have hdC : (↑X : ℂ) / ↑q - ↑Y / ↑q = ↑k := by
    have h2 := congrArg (fun t : ℝ => (t : ℂ)) hd
    push_cast at h2
    exact h2
  linear_combination (-(2 * ↑Real.pi * Complex.I)) * hdC

/-- The Chinese-remainder reindexing of a sum over `range (m*n)` as a double sum over
`range m × range n`, for `m`,`n` coprime. -/
lemma sum_range_mul_eq_sum_prod {M : Type*} [AddCommMonoid M] (m n : ℕ) (hco : m.Coprime n)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (F : ℕ × ℕ → M) :
    (∑ r ∈ Finset.range (m * n), F (r % m, r % n))
      = ∑ r₁ ∈ Finset.range m, ∑ r₂ ∈ Finset.range n, F (r₁, r₂) := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  rw [← Finset.sum_product]
  refine Finset.sum_nbij' (fun r => (r % m, r % n))
    (fun p => (Nat.chineseRemainder hco p.1 p.2 : ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega)⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_range]
    exact Nat.chineseRemainder_lt_mul hco p.1 p.2 hm0 hn0
  · intro a ha
    simp only [Finset.mem_range] at ha
    have h1 : (Nat.chineseRemainder hco (a % m) (a % n) : ℕ) ≡ a [MOD m] :=
      ((Nat.chineseRemainder hco (a % m) (a % n)).prop.1).trans (Nat.mod_modEq a m)
    have h2 : (Nat.chineseRemainder hco (a % m) (a % n) : ℕ) ≡ a [MOD n] :=
      ((Nat.chineseRemainder hco (a % m) (a % n)).prop.2).trans (Nat.mod_modEq a n)
    have h3 : (Nat.chineseRemainder hco (a % m) (a % n) : ℕ) ≡ a [MOD m * n] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨h1, h2⟩
    exact Nat.ModEq.eq_of_lt_of_lt h3
      (Nat.chineseRemainder_lt_mul hco (a % m) (a % n) hm0 hn0) ha
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have h1 := (Nat.chineseRemainder hco p.1 p.2).prop.1
    have h2 := (Nat.chineseRemainder hco p.1 p.2).prop.2
    show ((Nat.chineseRemainder hco p.1 p.2 : ℕ) % m,
          (Nat.chineseRemainder hco p.1 p.2 : ℕ) % n) = (p.1, p.2)
    rw [h1, h2, Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2]
  · intro a ha
    rfl

theorem completeSum_mul_eq (Q : Polynomial ℤ) (a u v : ℤ) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : u * (n : ℤ) + v * (m : ℤ) = 1) :
    Work.A3.completeSum Q a (m * n) = Work.A3.completeSum Q (a * u) m *
      Work.A3.completeSum Q (a * v) n := by
  have hcop : m.Coprime n := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hgn : ((m.gcd n : ℕ) : ℤ) ∣ (n : ℤ) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_right m n)
    have hgm : ((m.gcd n : ℕ) : ℤ) ∣ (m : ℤ) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_left m n)
    have hg : ((m.gcd n : ℕ) : ℤ) ∣ u * (n : ℤ) + v * (m : ℤ) :=
      dvd_add (dvd_mul_of_dvd_right hgn u) (dvd_mul_of_dvd_right hgm v)
    rw [hmn] at hg
    exact Nat.dvd_one.mp (Int.ofNat_dvd.mp hg)
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
  -- the pointwise CRT identity
  have key : ∀ r : ℕ,
      Complex.exp (-(2 * Real.pi * Complex.I *
          ((a : ℝ) * ((Q.eval (r : ℤ) : ℤ) : ℝ) / ((m * n : ℕ) : ℝ))))
        = Complex.exp (-(2 * Real.pi * Complex.I *
            (((a * u : ℤ) : ℝ) * ((Q.eval ((r % m : ℕ) : ℤ) : ℤ) : ℝ) / (m : ℝ))))
          * Complex.exp (-(2 * Real.pi * Complex.I *
            (((a * v : ℤ) : ℝ) * ((Q.eval ((r % n : ℕ) : ℤ) : ℤ) : ℝ) / (n : ℝ)))) := by
    intro r
    set Y : ℤ := (a * u) * (n : ℤ) * Q.eval ((r % m : ℕ) : ℤ)
        + (a * v) * (m : ℤ) * Q.eval ((r % n : ℕ) : ℤ) with hY
    have hun : (1 : ℤ) - u * (n : ℤ) = v * (m : ℤ) := by linarith [hmn]
    have hvn : (1 : ℤ) - v * (m : ℤ) = u * (n : ℤ) := by linarith [hmn]
    have hr1 : (m : ℤ) ∣ (r : ℤ) - ((r % m : ℕ) : ℤ) :=
      Nat.modEq_iff_dvd.mp (Nat.mod_modEq r m)
    have hr2 : (n : ℤ) ∣ (r : ℤ) - ((r % n : ℕ) : ℤ) :=
      Nat.modEq_iff_dvd.mp (Nat.mod_modEq r n)
    have hmdvd : (m : ℤ) ∣ a * Q.eval (r : ℤ) - Y := by
      have h1 : (m : ℤ) ∣ a * (Q.eval (r : ℤ) - Q.eval ((r % m : ℕ) : ℤ)) :=
        dvd_mul_of_dvd_right (dvd_eval_sub_eval Q hr1) a
      have h2 : (m : ℤ) ∣ a * Q.eval ((r % m : ℕ) : ℤ) * ((1 : ℤ) - u * (n : ℤ)) :=
        ⟨a * Q.eval ((r % m : ℕ) : ℤ) * v, by rw [hun]; ring⟩
      have h3 : (m : ℤ) ∣ a * v * (m : ℤ) * Q.eval ((r % n : ℕ) : ℤ) :=
        ⟨a * v * Q.eval ((r % n : ℕ) : ℤ), by ring⟩
      have he : a * Q.eval (r : ℤ) - Y
          = a * (Q.eval (r : ℤ) - Q.eval ((r % m : ℕ) : ℤ))
            + a * Q.eval ((r % m : ℕ) : ℤ) * ((1 : ℤ) - u * (n : ℤ))
            - a * v * (m : ℤ) * Q.eval ((r % n : ℕ) : ℤ) := by rw [hY]; ring
      rw [he]
      exact dvd_sub (dvd_add h1 h2) h3
    have hndvd : (n : ℤ) ∣ a * Q.eval (r : ℤ) - Y := by
      have h1 : (n : ℤ) ∣ a * (Q.eval (r : ℤ) - Q.eval ((r % n : ℕ) : ℤ)) :=
        dvd_mul_of_dvd_right (dvd_eval_sub_eval Q hr2) a
      have h2 : (n : ℤ) ∣ a * Q.eval ((r % n : ℕ) : ℤ) * ((1 : ℤ) - v * (m : ℤ)) :=
        ⟨a * Q.eval ((r % n : ℕ) : ℤ) * u, by rw [hvn]; ring⟩
      have h3 : (n : ℤ) ∣ a * u * (n : ℤ) * Q.eval ((r % m : ℕ) : ℤ) :=
        ⟨a * u * Q.eval ((r % m : ℕ) : ℤ), by ring⟩
      have he : a * Q.eval (r : ℤ) - Y
          = a * (Q.eval (r : ℤ) - Q.eval ((r % n : ℕ) : ℤ))
            + a * Q.eval ((r % n : ℕ) : ℤ) * ((1 : ℤ) - v * (m : ℤ))
            - a * u * (n : ℤ) * Q.eval ((r % m : ℕ) : ℤ) := by rw [hY]; ring
      rw [he]
      exact dvd_sub (dvd_add h1 h2) h3
    have hkey : ((m * n : ℕ) : ℤ) ∣ a * Q.eval (r : ℤ) - Y := by
      have hisc : IsCoprime ((m : ℤ)) ((n : ℤ)) := Nat.isCoprime_iff_coprime.mpr hcop
      have := hisc.mul_dvd hmdvd hndvd
      simpa only [Nat.cast_mul] using this
    have hid1 : ((a * u : ℤ) : ℝ) * ((Q.eval ((r % m : ℕ) : ℤ) : ℤ) : ℝ) / (m : ℝ)
        = (((a * u) * (n : ℤ) * Q.eval ((r % m : ℕ) : ℤ) : ℤ) : ℝ) / ((m * n : ℕ) : ℝ) := by
      push_cast
      field_simp
    have hid2 : ((a * v : ℤ) : ℝ) * ((Q.eval ((r % n : ℕ) : ℤ) : ℤ) : ℝ) / (n : ℝ)
        = (((a * v) * (m : ℤ) * Q.eval ((r % n : ℕ) : ℤ) : ℤ) : ℝ) / ((m * n : ℕ) : ℝ) := by
      push_cast
      field_simp
    have hsum : ((a * u : ℤ) : ℝ) * ((Q.eval ((r % m : ℕ) : ℤ) : ℤ) : ℝ) / (m : ℝ)
        + ((a * v : ℤ) : ℝ) * ((Q.eval ((r % n : ℕ) : ℤ) : ℤ) : ℝ) / (n : ℝ)
        = (Y : ℝ) / ((m * n : ℕ) : ℝ) := by
      rw [hid1, hid2, hY]
      push_cast
      ring
    have hstep1 : Complex.exp (-(2 * Real.pi * Complex.I *
          ((a : ℝ) * ((Q.eval (r : ℤ) : ℤ) : ℝ) / ((m * n : ℕ) : ℝ))))
        = Complex.exp (-(2 * Real.pi * Complex.I *
          (((a * Q.eval (r : ℤ) : ℤ) : ℝ) / ((m * n : ℕ) : ℝ)))) := by
      apply congrArg Complex.exp
      push_cast
      ring
    have hstep2 : Complex.exp (-(2 * Real.pi * Complex.I *
          (((a * Q.eval (r : ℤ) : ℤ) : ℝ) / ((m * n : ℕ) : ℝ))))
        = Complex.exp (-(2 * Real.pi * Complex.I * ((Y : ℝ) / ((m * n : ℕ) : ℝ)))) :=
      exp_char_period (m * n) hmn0 hkey
    have hstep3 : Complex.exp (-(2 * Real.pi * Complex.I * ((Y : ℝ) / ((m * n : ℕ) : ℝ))))
        = Complex.exp (-(2 * Real.pi * Complex.I *
            (((a * u : ℤ) : ℝ) * ((Q.eval ((r % m : ℕ) : ℤ) : ℤ) : ℝ) / (m : ℝ))))
          * Complex.exp (-(2 * Real.pi * Complex.I *
            (((a * v : ℤ) : ℝ) * ((Q.eval ((r % n : ℕ) : ℤ) : ℤ) : ℝ) / (n : ℝ)))) := by
      rw [← Complex.exp_add]
      apply congrArg Complex.exp
      have hcomplex : ((((a * u : ℤ) : ℝ) * ((Q.eval ((r % m : ℕ) : ℤ) : ℤ) : ℝ)
              / (m : ℝ) : ℝ) : ℂ)
          + ((((a * v : ℤ) : ℝ) * ((Q.eval ((r % n : ℕ) : ℤ) : ℤ) : ℝ)
              / (n : ℝ) : ℝ) : ℂ)
          = ((((Y : ℝ) / ((m * n : ℕ) : ℝ) : ℝ)) : ℂ) := by
        rw [← Complex.ofReal_add, hsum]
      push_cast at hcomplex ⊢
      linear_combination (2 * ((Real.pi : ℂ)) * Complex.I) * hcomplex
    exact hstep1.trans (hstep2.trans hstep3)
  -- assembly
  have hstep : Work.A3.completeSum Q a (m * n)
      = ∑ r ∈ Finset.range (m * n),
          (Complex.exp (-(2 * Real.pi * Complex.I *
              (((a * u : ℤ) : ℝ) * ((Q.eval ((r % m : ℕ) : ℤ) : ℤ) : ℝ) / (m : ℝ))))
            * Complex.exp (-(2 * Real.pi * Complex.I *
              (((a * v : ℤ) : ℝ) * ((Q.eval ((r % n : ℕ) : ℤ) : ℤ) : ℝ) / (n : ℝ))))) := by
    rw [completeSum]
    exact Finset.sum_congr rfl (fun r _ => key r)
  have hbij := sum_range_mul_eq_sum_prod m n hcop hm hn
    (fun p : ℕ × ℕ =>
      Complex.exp (-(2 * Real.pi * Complex.I *
          (((a * u : ℤ) : ℝ) * ((Q.eval ((p.1 : ℕ) : ℤ) : ℤ) : ℝ) / (m : ℝ))))
        * Complex.exp (-(2 * Real.pi * Complex.I *
          (((a * v : ℤ) : ℝ) * ((Q.eval ((p.2 : ℕ) : ℤ) : ℤ) : ℝ) / (n : ℝ)))))
  rw [hstep, hbij]
  dsimp only
  rw [← Finset.sum_mul_sum]
  rfl

end

end Work.A3
