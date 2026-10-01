import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Submission.Commons.Algebra.Polynomial.eq_zero_of_mul_sq_eq_C_mul_sq
import Submission.Commons.Algebra.Polynomial.exists_sq_of_derivative_eq_zero_finite

namespace Commons.NumberTheory.Stepanov

open Polynomial
set_option maxHeartbeats 4000000

/-!
# Kopparty's "good basis" lemma (e = 2)

Let `F` be a finite field, `q = #F`, `g ∈ F[X]` not a constant multiple of a square, and let
`A, B ∈ F[X][Y]` with all `X`-degrees `≤ A₀` and `Y`-degree `< q`, where `2*A₀ + 2*(deg g + 1) < q`.
If `(A,B) ≠ (0,0)` then `A(X, X^q) + g(X)^((q-1)/2) * B(X, X^q) ≠ 0`.

The proof follows Kopparty's notes ("The Weil bounds", Lemma 3) in the odd case: square the
relation, multiply by `g`, use `g(X)^q = g(X^q)` and reduce modulo `(X^q - C a)` for a base point
`a` with `g a ≠ 0`; then a valuation/coprimality argument forces `A(X,a) = B(X,a) = 0`, so
`(Y - C a)` divides both and one can descend.

In characteristic `2` the squaring trick loses the parity information, and one instead reduces the
relation `g * A(X,X^q) = g(X)^(q/2) * B(X,X^q)` modulo `(X^(q/2) - C a)^2 = X^q - C(a²)`; the
second-order Taylor expansion of `g(X)^(q/2)` at `a` together with `(g^(q/2))' ≠ 0` (which holds
because `g` is not a constant multiple of a square) yields `B(X,a²) = A(X,a²) = 0`.

## Main items

* `dvd_sq_sub_eval_sub_deriv_smul` : second order Taylor expansion;
* `natDegree_eval_C_le` : substituting `Y ↦ C a` does not increase `X`-degrees;
* `odd_step`, `even_step` : the one-step reductions in the two cases;
* `kopparty_sq_nonvanishing` : the theorem.
-/

/-- Second-order Taylor expansion: `(X - C a)^2` divides
`G - C (G.eval a) - C (G.derivative.eval a) * (X - C a)`. -/
theorem dvd_sq_sub_eval_sub_deriv_smul {F : Type*} [Field F] (G : Polynomial F) (a : F) :
    (Polynomial.X - Polynomial.C a) ^ 2 ∣
      G - Polynomial.C (G.eval a)
        - Polynomial.C (G.derivative.eval a) * (Polynomial.X - Polynomial.C a) := by
  have hT : Polynomial.X ^ 2 ∣ taylor a G - Polynomial.C ((taylor a G).coeff 0)
      - Polynomial.C ((taylor a G).coeff 1) * Polynomial.X := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d <;> simp
  obtain ⟨V, hV⟩ := hT
  refine ⟨V.comp (Polynomial.X - Polynomial.C a), ?_⟩
  have e1 : (taylor a G).comp (Polynomial.X - Polynomial.C a) = G := by
    rw [Polynomial.taylor_apply, Polynomial.comp_assoc]
    have h2 : (Polynomial.X + Polynomial.C a).comp (Polynomial.X - Polynomial.C a)
        = (Polynomial.X : Polynomial F) := by
      rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
      ring
    rw [h2, Polynomial.comp_X]
  have e2 : (Polynomial.C ((taylor a G).coeff 1)).comp (Polynomial.X - Polynomial.C a)
      = Polynomial.C (G.derivative.eval a) := by
    rw [Polynomial.taylor_coeff_one, Polynomial.C_comp]
  have e3 : (Polynomial.C ((taylor a G).coeff 0)) = Polynomial.C (G.eval a) := by
    rw [Polynomial.taylor_coeff_zero]
  have hcomp : (taylor a G - Polynomial.C ((taylor a G).coeff 0)
      - Polynomial.C ((taylor a G).coeff 1) * Polynomial.X).comp (Polynomial.X - Polynomial.C a)
      = G - Polynomial.C (G.eval a)
        - Polynomial.C (G.derivative.eval a) * (Polynomial.X - Polynomial.C a) := by
    rw [Polynomial.sub_comp, Polynomial.sub_comp, Polynomial.mul_comp, e1, e2, e3,
      Polynomial.X_comp, Polynomial.C_comp]
  rw [← hcomp, hV, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]

/-- Substituting `Y ↦ C a` into `A ∈ F[X][Y]` does not increase the `X`-degrees. -/
theorem natDegree_eval_C_le {F : Type*} [Field F] (A : Polynomial (Polynomial F)) (a : F) (k : ℕ)
    (hAd : ∀ i, (A.coeff i).natDegree ≤ k) : (A.eval (Polynomial.C a)).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Polynomial.eval_eq_sum_range]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have h1 : (A.coeff i).coeff N = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hAd i) hN)
  rw [← Polynomial.C_pow, Polynomial.coeff_mul_C, h1, zero_mul]

/-- **Odd case one-step.**  If `q = #F` is odd and `A(X,X^q) + g^((q-1)/2) B(X,X^q) = 0`, then there
is `a` with `g.eval a ≠ 0` and `A(X,a) = B(X,a) = 0`. -/
theorem odd_step {F : Type*} [Field F] [Fintype F] (g : Polynomial F)
    (hnd : ∀ (a : F) (h : Polynomial F), g ≠ Polynomial.C a * h ^ 2)
    (A₀ : ℕ) (hA₀ : 2 * A₀ + 2 * (g.natDegree + 1) < Fintype.card F)
    (hodd : Fintype.card F % 2 = 1)
    (A B : Polynomial (Polynomial F)) (hAd : ∀ i, (A.coeff i).natDegree ≤ A₀)
    (hBd : ∀ i, (B.coeff i).natDegree ≤ A₀)
    (hR : A.eval (Polynomial.X ^ Fintype.card F)
      + g ^ ((Fintype.card F - 1) / 2) * B.eval (Polynomial.X ^ Fintype.card F) = 0) :
    ∃ a : F, g.eval a ≠ 0 ∧ A.eval (Polynomial.C a) = 0 ∧ B.eval (Polynomial.C a) = 0 := by
  set q : ℕ := Fintype.card F with hq
  set u : ℕ := (q - 1) / 2 with hu
  set Xq : Polynomial F := Polynomial.X ^ q with hXq
  have hd_lt : g.natDegree < q := by omega
  have hg0 : g ≠ 0 := by
    intro h0; exact hnd 0 1 (by simp [h0])
  have h2A0d : 2 * A₀ + g.natDegree < q := by omega
  have hA0d : A₀ + g.natDegree < q := by omega
  obtain ⟨a, ha⟩ : ∃ a : F, g.eval a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg0 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p := g) (f := id)
      Function.injective_id (fun i => h i) (by rw [← hq]; exact hd_lt))
  set Ca : Polynomial F := Polynomial.C a with hCa
  set t : Polynomial F := A.eval Xq with ht
  set s : Polynomial F := B.eval Xq with hs
  have h2dvd : 2 ∣ q - 1 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hu2 : u * 2 = q - 1 := by rw [hu]; exact Nat.div_mul_cancel h2dvd
  have hsq : t ^ 2 = g ^ (q - 1) * s ^ 2 := by
    have h1 : t = -(g ^ u * s) := by
      rw [ht, hs]; exact eq_neg_of_add_eq_zero_left (by rw [hu]; exact hR)
    have h1b : t ^ 2 = (g ^ u * s) ^ 2 := by rw [h1]; ring
    rw [h1b, mul_pow]
    have h2 : (g ^ u) ^ 2 = g ^ (q - 1) := by rw [← pow_mul, hu2]
    rw [h2]
  have h4 : g * t ^ 2 = g.comp Xq * s ^ 2 := by
    rw [hsq, ← mul_assoc]
    have hgq : g ^ q = g.comp Xq := by
      rw [hq, hXq]
      exact ((Polynomial.expand_eq_comp_X_pow (R := F) (p := Fintype.card F) (f := g)).symm.trans
        (FiniteField.expand_card g)).symm
    have hgp : g * g ^ (q - 1) = g ^ q := by rw [← pow_succ']; congr 1; omega
    rw [hgp, hgq]
  have hA0' : 2 * A₀ < q := by omega
  have hDa : (A.eval Ca).natDegree ≤ A₀ := natDegree_eval_C_le A a A₀ hAd
  have hDb : (B.eval Ca).natDegree ≤ A₀ := natDegree_eval_C_le B a A₀ hBd
  obtain ⟨hAc, hBc⟩ : A.eval Ca = 0 ∧ B.eval Ca = 0 := by
    have hdiv : (Xq - Ca) ∣ g * A.eval Ca ^ 2 - Polynomial.C (g.eval a) * B.eval Ca ^ 2 := by
      have hdA : (Xq - Ca) ∣ t - A.eval Ca := by
        rw [ht, hXq, hCa]; exact Polynomial.sub_dvd_eval_sub _ _ _
      have hdB : (Xq - Ca) ∣ s - B.eval Ca := by
        rw [hs, hXq, hCa]; exact Polynomial.sub_dvd_eval_sub _ _ _
      have hdg : (Xq - Ca) ∣ g.comp Xq - Polynomial.C (g.eval a) := by
        have hdXa : (Polynomial.X - Polynomial.C a) ∣ g - Polynomial.C (g.eval a) := by
          rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
          simp
        obtain ⟨r, hr⟩ := hdXa
        rw [hCa, hXq]
        refine ⟨r.comp (Polynomial.X ^ q), ?_⟩
        have h1 : (g - Polynomial.C (g.eval a)).comp (Polynomial.X ^ q)
            = g.comp (Polynomial.X ^ q) - Polynomial.C (g.eval a) := by
          rw [Polynomial.sub_comp, Polynomial.C_comp]
        rw [← h1, hr, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.X_comp,
          Polynomial.C_comp]
      have hA2 : (Xq - Ca) ∣ t ^ 2 - A.eval Ca ^ 2 := by
        obtain ⟨r, hr⟩ := hdA
        exact ⟨r * (t + A.eval Ca), by linear_combination (t + A.eval Ca) * hr⟩
      have hB2 : (Xq - Ca) ∣ s ^ 2 - B.eval Ca ^ 2 := by
        obtain ⟨r, hr⟩ := hdB
        exact ⟨r * (s + B.eval Ca), by linear_combination (s + B.eval Ca) * hr⟩
      have hAZ : (Xq - Ca) ∣ A.eval Ca ^ 2 - t ^ 2 := by
        obtain ⟨r, hr⟩ := hA2
        exact ⟨-r, by linear_combination -hr⟩
      have h0 : g * t ^ 2 - g.comp Xq * s ^ 2 = 0 := sub_eq_zero.mpr h4
      have key : g * A.eval Ca ^ 2 - Polynomial.C (g.eval a) * B.eval Ca ^ 2
          = (g * t ^ 2 - g.comp Xq * s ^ 2)
            + ((g.comp Xq - Polynomial.C (g.eval a)) * s ^ 2
              + g * (A.eval Ca ^ 2 - t ^ 2))
            + Polynomial.C (g.eval a) * (s ^ 2 - B.eval Ca ^ 2) := by ring
      rw [key, h0, zero_add]
      apply dvd_add
      · apply dvd_add
        · exact dvd_mul_of_dvd_left hdg _
        · exact dvd_mul_of_dvd_right hAZ g
      · exact dvd_mul_of_dvd_right hB2 _
    have hDdeg : (g * A.eval Ca ^ 2 - Polynomial.C (g.eval a) * B.eval Ca ^ 2).natDegree < q := by
      have h1 : (g * A.eval Ca ^ 2).natDegree ≤ g.natDegree + A₀ * 2 := by
        calc (g * A.eval Ca ^ 2).natDegree ≤ g.natDegree + (A.eval Ca ^ 2).natDegree :=
              Polynomial.natDegree_mul_le
          _ = g.natDegree + (A.eval Ca).natDegree * 2 := by
                rw [Polynomial.natDegree_pow, Nat.mul_comm]
          _ ≤ g.natDegree + A₀ * 2 := by omega
      have h2 : (Polynomial.C (g.eval a) * B.eval Ca ^ 2).natDegree ≤ A₀ * 2 := by
        calc (Polynomial.C (g.eval a) * B.eval Ca ^ 2).natDegree
            ≤ (Polynomial.C (g.eval a)).natDegree + (B.eval Ca ^ 2).natDegree :=
              Polynomial.natDegree_mul_le
          _ = 0 + (B.eval Ca).natDegree * 2 := by
                rw [Polynomial.natDegree_pow, Polynomial.natDegree_C, Nat.mul_comm]
          _ ≤ A₀ * 2 := by omega
      calc (g * A.eval Ca ^ 2 - Polynomial.C (g.eval a) * B.eval Ca ^ 2).natDegree
          ≤ max (g * A.eval Ca ^ 2).natDegree
              (Polynomial.C (g.eval a) * B.eval Ca ^ 2).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ ≤ max (g.natDegree + A₀ * 2) (A₀ * 2) := max_le_max h1 h2
        _ < q := by omega
    have hm : (Xq - Ca).natDegree = q := by rw [hXq, hCa]; exact Polynomial.natDegree_X_pow_sub_C
    have hD0 : g * A.eval Ca ^ 2 - Polynomial.C (g.eval a) * B.eval Ca ^ 2 = 0 :=
      Polynomial.eq_zero_of_dvd_of_natDegree_lt hdiv (by rw [hm]; exact hDdeg)
    exact Commons.Algebra.Polynomial.eq_zero_of_mul_sq_eq_C_mul_sq g _ _ (g.eval a) ha hnd
      (sub_eq_zero.mp hD0)
  exact ⟨a, ha, hAc, hBc⟩

/-- **Even case one-step** (characteristic `2`).  If `q = #F` is even and
`A(X,X^q) + g^((q-1)/2) B(X,X^q) = 0`, then there is `a` with `A(X,a²) = B(X,a²) = 0`. -/
theorem even_step {F : Type*} [Field F] [Fintype F] (g : Polynomial F)
    (hnd : ∀ (a : F) (h : Polynomial F), g ≠ Polynomial.C a * h ^ 2)
    (A₀ : ℕ) (hA₀ : 2 * A₀ + 2 * (g.natDegree + 1) < Fintype.card F)
    (heven : Fintype.card F % 2 = 0)
    (A B : Polynomial (Polynomial F)) (hAd : ∀ i, (A.coeff i).natDegree ≤ A₀)
    (hBd : ∀ i, (B.coeff i).natDegree ≤ A₀)
    (hR : A.eval (Polynomial.X ^ Fintype.card F)
      + g ^ ((Fintype.card F - 1) / 2) * B.eval (Polynomial.X ^ Fintype.card F) = 0) :
    ∃ a : F, A.eval (Polynomial.C (a ^ 2)) = 0 ∧ B.eval (Polynomial.C (a ^ 2)) = 0 := by
  set q : ℕ := Fintype.card F with hq
  have hdl : g.natDegree < q := by omega
  have hg0 : g ≠ 0 := by intro h0; exact hnd 0 1 (by simp [h0])
  have hd1 : 1 ≤ g.natDegree := by
    rcases Nat.eq_zero_or_pos g.natDegree with h | h
    · exfalso
      exact hnd (g.coeff 0) 1 (by simpa using Polynomial.eq_C_of_natDegree_eq_zero h)
    · exact h
  have hq5 : 5 ≤ q := by
    have hab : 2 ≤ g.natDegree + 1 := by omega
    have h4 : 4 < q := by nlinarith [hA₀, hab, Nat.zero_le A₀, Nat.zero_le g.natDegree]
    omega
  have h2char : CharP F 2 := by
    obtain ⟨n, hprime, hqn⟩ := FiniteField.card F (ringChar F)
    have hp2 : ringChar F = 2 := by
      rcases hprime.eq_two_or_odd with h | h
      · exact h
      · exfalso
        have hodd : Odd (ringChar F ^ (n : ℕ)) := (Nat.odd_iff.mpr h).pow
        rw [← hqn] at hodd
        rw [Nat.odd_iff] at hodd
        exact absurd hodd (by rw [hq] at heven; omega)
    rw [← hp2]
    exact inferInstance
  haveI : CharP F 2 := h2char
  have hA0lt : A₀ < q / 2 := by omega
  have hAdlt : A₀ + g.natDegree < q / 2 := by omega
  obtain ⟨m, hm2, hqm⟩ := FiniteField.card F 2
  have hm1 : 1 ≤ (m : ℕ) := m.pos
  set σ : F →+* F := iterateFrobenius F 2 ((m : ℕ) - 1) with hσ
  set P : Polynomial F := g.map σ with hP
  have hσ_inj : Function.Injective σ := σ.injective
  have hq2 : q / 2 = 2 ^ ((m : ℕ) - 1) := by
    rw [hq, hqm]
    exact (by simpa using (Nat.pow_div (x := 2) (m := (m : ℕ)) (n := 1) hm1 (by norm_num) :
      2 ^ (m : ℕ) / 2 ^ 1 = 2 ^ ((m : ℕ) - 1)))
  have hPcomp : g ^ (q / 2) = P.comp (Polynomial.X ^ (q / 2)) := by
    rw [hq2]
    rw [show g ^ 2 ^ ((m : ℕ) - 1) = Polynomial.map σ (Polynomial.expand F (2 ^ ((m : ℕ) - 1)) g) from
      (Polynomial.map_iterateFrobenius_expand (p := 2) (f := g) (n := (m : ℕ) - 1)).symm]
    rw [hP, hσ, Polynomial.expand_eq_comp_X_pow, Polynomial.map_comp]
    simp only [Polynomial.map_pow, Polynomial.map_X]
  have hg' : Polynomial.derivative g ≠ 0 := by
    intro h0
    obtain ⟨h', hh⟩ := Commons.Algebra.Polynomial.exists_sq_of_derivative_eq_zero_finite g h0
    exact hnd 1 h' (by rw [hh, Polynomial.C_1, one_mul])
  have hP' : Polynomial.derivative P ≠ 0 := by
    rw [hP, Polynomial.derivative_map]
    intro h0
    exact hg' (Polynomial.map_eq_zero_iff hσ_inj |>.mp h0)
  obtain ⟨a, ha⟩ : ∃ a : F, (Polynomial.derivative P).eval a ≠ 0 := by
    by_contra h
    push_neg at h
    refine hP' (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (p := Polynomial.derivative P) (f := id) Function.injective_id (fun i => h i) ?_)
    have hlt : (Polynomial.derivative P).natDegree < g.natDegree := by
      rw [hP, Polynomial.derivative_map, Polynomial.natDegree_map_eq_of_injective hσ_inj]
      exact Polynomial.natDegree_derivative_lt (by omega)
    omega
  set Ca : Polynomial F := Polynomial.C a with hCa
  set Ca2 : Polynomial F := Polynomial.C (a ^ 2) with hCa2
  set Xq : Polynomial F := Polynomial.X ^ q with hXq
  set Xh : Polynomial F := Polynomial.X ^ (q / 2) with hXh
  have hCXh : (Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)).natDegree ≤ q / 2 := by
    calc _ ≤ (Polynomial.C ((Polynomial.derivative P).eval a)).natDegree + (Xh - Ca).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ q / 2 := by rw [Polynomial.natDegree_C, hXh, hCa, Polynomial.natDegree_X_pow_sub_C]; omega
  have hsum : (Polynomial.C (P.eval a)
      + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)).natDegree ≤ q / 2 := by
    have h3a : (Polynomial.C (P.eval a)).natDegree ≤ 0 := by rw [Polynomial.natDegree_C]
    calc _ ≤ max (Polynomial.C (P.eval a)).natDegree
            (Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ max 0 (q/2) := max_le_max h3a hCXh
      _ = q/2 := max_eq_right (by omega)
  have hu1 : (q - 1) / 2 + 1 = q / 2 := by omega
  have hp : g * g ^ ((q - 1) / 2) = g ^ (q / 2) := by rw [← hu1, pow_succ']
  have h2q2 : (q / 2) * 2 = q := by omega
  have hXX : (Xh) ^ 2 = Xq := by rw [hXh, hXq, ← pow_mul, h2q2]
  have hCa2' : Ca ^ 2 = Ca2 := by rw [hCa, hCa2, ← Polynomial.C_pow]
  have hChar2 : ∀ x : Polynomial F, -x = x := by
    intro x
    rw [neg_eq_iff_add_eq_zero, ← two_mul,
      show (2 : Polynomial F) = 0 from CharP.cast_eq_zero (Polynomial F) 2, zero_mul]
  have hXqCa2 : Xq - Ca2 = (Xh - Ca) ^ 2 := by
    have h2z : (2 : Polynomial F) = 0 := CharP.cast_eq_zero (Polynomial F) 2
    calc Xq - Ca2 = Xh ^ 2 - Ca ^ 2 := by rw [hXX, hCa2']
      _ = Xh ^ 2 + Ca ^ 2 := by rw [sub_eq_add_neg, hChar2 (Ca ^ 2)]
      _ = (Xh - Ca) ^ 2 := by rw [sub_sq, h2z]; ring
  have h4 : g * A.eval Xq = P.comp Xh * B.eval Xq := by
    have h5 : g * (A.eval Xq + g ^ ((q - 1) / 2) * B.eval Xq) = 0 := by rw [hR, mul_zero]
    have hexp : g * (A.eval Xq + g ^ ((q - 1) / 2) * B.eval Xq)
        = g * A.eval Xq + g ^ (q / 2) * B.eval Xq := by rw [mul_add, ← mul_assoc, hp]
    rw [hexp] at h5
    have hneg : - (g ^ (q / 2) * B.eval Xq) = g ^ (q / 2) * B.eval Xq := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul,
        show (2 : Polynomial F) = 0 from CharP.cast_eq_zero (Polynomial F) 2, zero_mul]
    have h6 : g * A.eval Xq = g ^ (q / 2) * B.eval Xq := by
      have h7 := eq_neg_of_add_eq_zero_left h5
      rwa [hneg] at h7
    rw [h6, hPcomp]
  have hdg : (Xq - Ca2) ∣ P.comp Xh - (Polynomial.C (P.eval a)
      + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)) := by
    rw [hXqCa2]
    obtain ⟨r, hr⟩ := dvd_sq_sub_eval_sub_deriv_smul P a
    refine ⟨r.comp Xh, ?_⟩
    have h1 : (P - Polynomial.C (P.eval a)
        - Polynomial.C ((Polynomial.derivative P).eval a) * (Polynomial.X - Polynomial.C a)).comp Xh
        = P.comp Xh - (Polynomial.C (P.eval a)
          + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)) := by
      simp only [hCa, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.X_comp,
        Polynomial.C_comp]
      ring
    rw [← h1, hr, Polynomial.mul_comp]
    congr 1
    rw [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, hCa]
  have hdA : (Xq - Ca2) ∣ A.eval Xq - A.eval Ca2 := by
    rw [hXq, hCa2]; exact Polynomial.sub_dvd_eval_sub _ _ _
  have hdB : (Xq - Ca2) ∣ B.eval Xq - B.eval Ca2 := by
    rw [hXq, hCa2]; exact Polynomial.sub_dvd_eval_sub _ _ _
  have hdiv : (Xq - Ca2) ∣ g * A.eval Ca2 - (Polynomial.C (P.eval a)
      + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)) * B.eval Ca2 := by
    have hA2 : (Xq - Ca2) ∣ A.eval Xq - A.eval Ca2 := hdA
    have hAZ : (Xq - Ca2) ∣ A.eval Ca2 - A.eval Xq := by
      obtain ⟨r, hr⟩ := hdA
      exact ⟨-r, by linear_combination -hr⟩
    have h0 : g * A.eval Xq - P.comp Xh * B.eval Xq = 0 := sub_eq_zero.mpr h4
    have key : g * A.eval Ca2 - (Polynomial.C (P.eval a)
          + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)) * B.eval Ca2
        = (g * A.eval Xq - P.comp Xh * B.eval Xq)
          + (P.comp Xh - (Polynomial.C (P.eval a)
              + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca))) * B.eval Xq
          + g * (A.eval Ca2 - A.eval Xq)
          + (Polynomial.C (P.eval a)
              + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca))
            * (B.eval Xq - B.eval Ca2) := by ring
    rw [key, h0, zero_add]
    apply dvd_add
    · apply dvd_add
      · exact dvd_mul_of_dvd_left hdg _
      · exact dvd_mul_of_dvd_right hAZ g
    · exact dvd_mul_of_dvd_right hdB _
  have hDdeg : (g * A.eval Ca2 - (Polynomial.C (P.eval a)
      + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)) * B.eval Ca2).natDegree < q := by
    have hAe : (A.eval Ca2).natDegree ≤ A₀ := natDegree_eval_C_le A (a^2) A₀ hAd
    have hBe : (B.eval Ca2).natDegree ≤ A₀ := natDegree_eval_C_le B (a^2) A₀ hBd
    have h1 : (g * A.eval Ca2).natDegree ≤ g.natDegree + A₀ := by
      calc (g * A.eval Ca2).natDegree ≤ g.natDegree + (A.eval Ca2).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ g.natDegree + A₀ := by omega
    have h2 : ((Polynomial.C (P.eval a)
        + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)) * B.eval Ca2).natDegree
        ≤ q / 2 + A₀ := by
      calc _ ≤ (Polynomial.C (P.eval a)
            + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)).natDegree
              + (B.eval Ca2).natDegree := Polynomial.natDegree_mul_le
        _ ≤ q / 2 + A₀ := by omega
    calc _ ≤ max (g * A.eval Ca2).natDegree
            ((Polynomial.C (P.eval a)
              + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)) * B.eval Ca2).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ max (g.natDegree + A₀) (q / 2 + A₀) := max_le_max h1 h2
      _ < q := by omega
  have hD0 : g * A.eval Ca2 - (Polynomial.C (P.eval a)
      + Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca)) * B.eval Ca2 = 0 := by
    have hm : (Xq - Ca2).natDegree = q := by
      rw [hXq, hCa2]; exact Polynomial.natDegree_X_pow_sub_C
    exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hdiv (by rw [hm]; exact hDdeg)
  have hident : g * A.eval Ca2 - Polynomial.C (P.eval a) * B.eval Ca2
      = Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca) * B.eval Ca2 := by
    have h := hD0
    rw [add_mul] at h
    linear_combination h
  have hLdeg : (g * A.eval Ca2 - Polynomial.C (P.eval a) * B.eval Ca2).natDegree < q / 2 := by
    have hAe : (A.eval Ca2).natDegree ≤ A₀ := natDegree_eval_C_le A (a^2) A₀ hAd
    have hBe : (B.eval Ca2).natDegree ≤ A₀ := natDegree_eval_C_le B (a^2) A₀ hBd
    have h1 : (g * A.eval Ca2).natDegree ≤ g.natDegree + A₀ := by
      calc (g * A.eval Ca2).natDegree ≤ g.natDegree + (A.eval Ca2).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ g.natDegree + A₀ := by omega
    have h2 : (Polynomial.C (P.eval a) * B.eval Ca2).natDegree ≤ A₀ := by
      calc (Polynomial.C (P.eval a) * B.eval Ca2).natDegree
          ≤ (Polynomial.C (P.eval a)).natDegree + (B.eval Ca2).natDegree :=
            Polynomial.natDegree_mul_le
        _ = (B.eval Ca2).natDegree := by rw [Polynomial.natDegree_C, zero_add]
        _ ≤ A₀ := hBe
    calc _ ≤ max (g * A.eval Ca2).natDegree (Polynomial.C (P.eval a) * B.eval Ca2).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ max (g.natDegree + A₀) A₀ := max_le_max h1 h2
      _ < q / 2 := by omega
  have hL0 : g * A.eval Ca2 - Polynomial.C (P.eval a) * B.eval Ca2 = 0 := by
    have hdvd : (Xh - Ca) ∣ g * A.eval Ca2 - Polynomial.C (P.eval a) * B.eval Ca2 := by
      rw [hident]
      exact ⟨Polynomial.C ((Polynomial.derivative P).eval a) * B.eval Ca2, by ring⟩
    refine Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd ?_
    rw [hXh, hCa, Polynomial.natDegree_X_pow_sub_C]; exact hLdeg
  have hB0 : B.eval Ca2 = 0 := by
    have hc : Polynomial.C ((Polynomial.derivative P).eval a) ≠ 0 :=
      Polynomial.C_ne_zero.mpr ha
    have hxc : (Xh - Ca) ≠ 0 := by
      intro hcon
      have hx : Xh = Ca := sub_eq_zero.mp hcon
      rw [hXh, hCa] at hx
      have hnd2 := congrArg Polynomial.natDegree hx
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at hnd2
      omega
    have hz : Polynomial.C ((Polynomial.derivative P).eval a) * (Xh - Ca) * B.eval Ca2 = 0 := by
      rw [← hident, hL0]
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hc hxc)
  have hA0 : A.eval Ca2 = 0 := by
    have hz : g * A.eval Ca2 = 0 := by
      have h := hD0
      rw [hB0, mul_zero, sub_zero] at h
      exact h
    exact (mul_eq_zero.mp hz).resolve_left hg0
  exact ⟨a, hA0, hB0⟩

/-- Degree-separation base case: a sum `a + g^u * b` of two low-degree polynomials can only
vanish if `a = b = 0`. -/
theorem const_no_solution {F : Type*} [Field F] [Fintype F] (g : Polynomial F)
    (hnd : ∀ (a : F) (h : Polynomial F), g ≠ Polynomial.C a * h ^ 2)
    (A₀ : ℕ) (hA₀ : 2 * A₀ + 2 * (g.natDegree + 1) < Fintype.card F)
    (a b : Polynomial F) (ha : a.natDegree ≤ A₀) (hb : b.natDegree ≤ A₀)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    a + g ^ ((Fintype.card F - 1) / 2) * b ≠ 0 := by
  set q : ℕ := Fintype.card F with hq
  set u : ℕ := (q - 1) / 2 with hu
  have hg0 : g ≠ 0 := by intro h0; exact hnd 0 0 (by simp [h0])
  have hd1 : 1 ≤ g.natDegree := by
    rcases Nat.eq_zero_or_pos g.natDegree with h | h
    · exfalso
      have hgC : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h
      exact hnd (g.coeff 0) 1 (by rw [← hgC]; ring)
    · exact h
  have hA0u : A₀ < u * g.natDegree := by
    have h2 : A₀ + g.natDegree + 1 ≤ u := by
      rw [hu, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      omega
    have h3 : u ≤ u * g.natDegree := Nat.le_mul_of_pos_right _ hd1
    omega
  intro hcontra
  rcases eq_or_ne b 0 with hb0 | hb0
  · rw [hb0, mul_zero, add_zero] at hcontra
    rcases hab with ha' | hb'
    · exact ha' hcontra
    · exact hb' hb0
  · have hgu : g ^ u ≠ 0 := pow_ne_zero _ hg0
    have hgun : g ^ u * b ≠ 0 := mul_ne_zero hgu hb0
    have ha0 : a = -(g ^ u * b) := eq_neg_of_add_eq_zero_left hcontra
    have hdeg : a.natDegree = (g ^ u * b).natDegree := by rw [ha0, Polynomial.natDegree_neg]
    have hge : u * g.natDegree ≤ (g ^ u * b).natDegree := by
      rw [Polynomial.natDegree_mul hgu hb0, Polynomial.natDegree_pow]
      omega
    omega

/-- If `A = (Y - C c) * A'` and all `X`-degrees of the coefficients of `A` are `≤ A₀`, then the
same holds for `A'`. -/
theorem coeff_natDegree_of_eq_mul_X_sub_C {F : Type*} [Field F]
    (A A' : Polynomial (Polynomial F)) (c : F) (A₀ : ℕ)
    (hAd : ∀ i, (A.coeff i).natDegree ≤ A₀)
    (h : A = (Polynomial.X - Polynomial.C (Polynomial.C c)) * A') :
    ∀ i, (A'.coeff i).natDegree ≤ A₀ := by
  have hcoe : ∀ j, A.coeff (j + 1) = A'.coeff j - Polynomial.C c * A'.coeff (j + 1) := by
    intro j
    rw [h, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
  have hstep : ∀ k, (A'.coeff (k + 1)).natDegree ≤ A₀ → (A'.coeff k).natDegree ≤ A₀ := by
    intro k hk
    have h1 : A'.coeff k = A.coeff (k + 1) + Polynomial.C c * A'.coeff (k + 1) := by
      rw [hcoe k]; ring
    rw [h1]
    calc (A.coeff (k + 1) + Polynomial.C c * A'.coeff (k + 1)).natDegree
        ≤ max (A.coeff (k + 1)).natDegree (Polynomial.C c * A'.coeff (k + 1)).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ max A₀ A₀ := max_le_max (hAd (k + 1))
          (le_trans (Polynomial.natDegree_C_mul_le c (A'.coeff (k + 1))) hk)
      _ = A₀ := max_self A₀
  intro i
  by_cases hi : i ≤ A'.natDegree + 1
  · have hbase : (A'.coeff (A'.natDegree + 1)).natDegree ≤ A₀ := by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.natDegree_zero]
      omega
    exact Nat.decreasingInduction (n := A'.natDegree + 1) (m := i)
      (motive := fun m _ => (A'.coeff m).natDegree ≤ A₀)
      (fun k _ hk => hstep k hk) hbase hi
  · push_neg at hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.natDegree_zero]
    omega

/-- `Y - C c` is a nonzero polynomial. -/
theorem X_sub_C_ne_zero' {F : Type*} [Field F] (c : F) :
    (Polynomial.X - Polynomial.C (Polynomial.C c) : Polynomial (Polynomial F)) ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_zero] at this
  exact one_ne_zero this

/-- Division by `Y - C c` does not increase the `Y`-degree. -/
theorem natDegree_div_le {F : Type*} [Field F] {A A' : Polynomial (Polynomial F)} {c : F}
    (h : A = (Polynomial.X - Polynomial.C (Polynomial.C c)) * A') :
    A'.natDegree ≤ A.natDegree := by
  by_cases h0 : A' = 0
  · rw [h0, Polynomial.natDegree_zero]; exact Nat.zero_le _
  · have hmul : A.natDegree = 1 + A'.natDegree := by
      rw [h, Polynomial.natDegree_mul (X_sub_C_ne_zero' c) h0, Polynomial.natDegree_X_sub_C]
    omega

/-- If `A ≠ 0` and `A = (Y - C c) * A'` then the `Y`-degree strictly decreases. -/
theorem natDegree_div_lt {F : Type*} [Field F] {A A' : Polynomial (Polynomial F)} {c : F}
    (h : A = (Polynomial.X - Polynomial.C (Polynomial.C c)) * A') (hA : A ≠ 0) :
    A'.natDegree < A.natDegree := by
  have h0 : A' ≠ 0 := by intro h0; exact hA (by rw [h, h0, mul_zero])
  have hmul : A.natDegree = 1 + A'.natDegree := by
    rw [h, Polynomial.natDegree_mul (X_sub_C_ne_zero' c) h0, Polynomial.natDegree_X_sub_C]
  omega

/-- **One-step reduction.**  If the Stepanov relation vanishes then `Y - C c` divides both `A`
and `B` for some `c : F`. -/
theorem exists_linear_factor {F : Type*} [Field F] [Fintype F] (g : Polynomial F)
    (hnd : ∀ (a : F) (h : Polynomial F), g ≠ Polynomial.C a * h ^ 2)
    (A₀ : ℕ) (hA₀ : 2 * A₀ + 2 * (g.natDegree + 1) < Fintype.card F)
    (A B : Polynomial (Polynomial F)) (hAd : ∀ i, (A.coeff i).natDegree ≤ A₀)
    (hBd : ∀ i, (B.coeff i).natDegree ≤ A₀)
    (hR : A.eval (Polynomial.X ^ Fintype.card F)
      + g ^ ((Fintype.card F - 1) / 2) * B.eval (Polynomial.X ^ Fintype.card F) = 0) :
    ∃ c : F, (Polynomial.X - Polynomial.C (Polynomial.C c)) ∣ A ∧
      (Polynomial.X - Polynomial.C (Polynomial.C c)) ∣ B := by
  by_cases hodd : Fintype.card F % 2 = 1
  · obtain ⟨a, ha, hAev, hBev⟩ := odd_step g hnd A₀ hA₀ hodd A B hAd hBd hR
    exact ⟨a, (Polynomial.dvd_iff_isRoot.mpr (Polynomial.IsRoot.def.mpr hAev)),
      (Polynomial.dvd_iff_isRoot.mpr (Polynomial.IsRoot.def.mpr hBev))⟩
  · have heven : Fintype.card F % 2 = 0 := by omega
    obtain ⟨a, hAev, hBev⟩ := even_step g hnd A₀ hA₀ heven A B hAd hBd hR
    exact ⟨a ^ 2, (Polynomial.dvd_iff_isRoot.mpr (Polynomial.IsRoot.def.mpr hAev)),
      (Polynomial.dvd_iff_isRoot.mpr (Polynomial.IsRoot.def.mpr hBev))⟩

/-- **Kopparty's "good basis" lemma (e = 2).**  Let `F` be a finite field, `g ∈ F[X]` not a
constant times a square, and let `A, B ∈ F[X][Y] = F[X,Y]` have all `X`-degrees `≤ A₀` and
`Y`-degree `< #F`, with `2*A₀ + 2*(deg g + 1) < #F`.  If `(A,B) ≠ (0,0)` then the specialized
polynomial `A(X, X ^ #F) + g(X)^((#F-1)/2) * B(X, X ^ #F)` is nonzero.

This is the non-vanishing step guaranteeing that the auxiliary polynomial produced by the
dimension count in Stepanov's method for the quadratic character is nontrivial.  (Compare
Kopparty, "The Weil bounds", Lemma 3.) -/
theorem kopparty_sq_nonvanishing {F : Type*} [Field F] [Fintype F]
    (g : Polynomial F) (hnd : ∀ (a : F) (h : Polynomial F), g ≠ Polynomial.C a * h ^ 2)
    (A₀ : ℕ) (hA₀ : 2 * A₀ + 2 * (g.natDegree + 1) < Fintype.card F)
    (A B : Polynomial (Polynomial F)) (hA : A ≠ 0 ∨ B ≠ 0)
    (hAd : ∀ i, (A.coeff i).natDegree ≤ A₀) (hBd : ∀ i, (B.coeff i).natDegree ≤ A₀)
    (hAn : A.natDegree < Fintype.card F) (hBn : B.natDegree < Fintype.card F) :
    A.eval (Polynomial.X ^ Fintype.card F)
      + g ^ ((Fintype.card F - 1) / 2) * B.eval (Polynomial.X ^ Fintype.card F) ≠ 0 := by
  have hqpos : 0 < Fintype.card F := by have := hA₀; omega
  have key : ∀ N : ℕ, ∀ (A B : Polynomial (Polynomial F)),
      A.natDegree + B.natDegree ≤ N →
      (A ≠ 0 ∨ B ≠ 0) →
      (∀ i, (A.coeff i).natDegree ≤ A₀) →
      (∀ i, (B.coeff i).natDegree ≤ A₀) →
      A.natDegree < Fintype.card F → B.natDegree < Fintype.card F →
      A.eval (Polynomial.X ^ Fintype.card F)
        + g ^ ((Fintype.card F - 1) / 2) * B.eval (Polynomial.X ^ Fintype.card F) ≠ 0 := by
    intro N
    induction N with
    | zero =>
      intro A B hN hA hAd hBd hAn hBn hR
      have hAdeg : A.natDegree = 0 := by omega
      have hBdeg : B.natDegree = 0 := by omega
      have hAeq : A = Polynomial.C (A.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hAdeg
      have hBeq : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hBdeg
      have hAev : A.eval (Polynomial.X ^ Fintype.card F) = A.coeff 0 := by
        conv_lhs => rw [hAeq]
        rw [Polynomial.eval_C]
      have hBev : B.eval (Polynomial.X ^ Fintype.card F) = B.coeff 0 := by
        conv_lhs => rw [hBeq]
        rw [Polynomial.eval_C]
      rw [hAev, hBev] at hR
      have hne : A.coeff 0 ≠ 0 ∨ B.coeff 0 ≠ 0 := by
        rcases hA with h | h
        · left; intro h0; exact h (by rw [hAeq, h0, Polynomial.C_0])
        · right; intro h0; exact h (by rw [hBeq, h0, Polynomial.C_0])
      exact const_no_solution g hnd A₀ hA₀ (A.coeff 0) (B.coeff 0) (hAd 0) (hBd 0) hne hR
    | succ n ih =>
      intro A B hN hA hAd hBd hAn hBn hR
      by_cases hsmall : A.natDegree + B.natDegree ≤ n
      · exact ih A B hsmall hA hAd hBd hAn hBn hR
      · push_neg at hsmall
        have htot : A.natDegree + B.natDegree = n + 1 := by omega
        obtain ⟨c, hcA, hcB⟩ := exists_linear_factor g hnd A₀ hA₀ A B hAd hBd hR
        obtain ⟨A', hA'⟩ := hcA
        obtain ⟨B', hB'⟩ := hcB
        have hA'd : ∀ i, (A'.coeff i).natDegree ≤ A₀ :=
          coeff_natDegree_of_eq_mul_X_sub_C A A' c A₀ hAd hA'
        have hB'd : ∀ i, (B'.coeff i).natDegree ≤ A₀ :=
          coeff_natDegree_of_eq_mul_X_sub_C B B' c A₀ hBd hB'
        have hAeval : A.eval (Polynomial.X ^ Fintype.card F)
            = (Polynomial.X ^ Fintype.card F - Polynomial.C c)
              * A'.eval (Polynomial.X ^ Fintype.card F) := by
          rw [hA', Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        have hBeval : B.eval (Polynomial.X ^ Fintype.card F)
            = (Polynomial.X ^ Fintype.card F - Polynomial.C c)
              * B'.eval (Polynomial.X ^ Fintype.card F) := by
          rw [hB', Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        have hfac : A.eval (Polynomial.X ^ Fintype.card F)
            + g ^ ((Fintype.card F - 1) / 2) * B.eval (Polynomial.X ^ Fintype.card F)
            = (Polynomial.X ^ Fintype.card F - Polynomial.C c)
              * (A'.eval (Polynomial.X ^ Fintype.card F)
                + g ^ ((Fintype.card F - 1) / 2) * B'.eval (Polynomial.X ^ Fintype.card F)) := by
          rw [hAeval, hBeval, mul_add]; ring
        have hXqC_ne : Polynomial.X ^ Fintype.card F - Polynomial.C c ≠ 0 := by
          intro h0
          have := Polynomial.natDegree_X_pow_sub_C (R := F)
            (n := Fintype.card F) (r := c)
          rw [h0, Polynomial.natDegree_zero] at this
          omega
        have hR' : A'.eval (Polynomial.X ^ Fintype.card F)
            + g ^ ((Fintype.card F - 1) / 2) * B'.eval (Polynomial.X ^ Fintype.card F) = 0 := by
          have h2 : (Polynomial.X ^ Fintype.card F - Polynomial.C c)
              * (A'.eval (Polynomial.X ^ Fintype.card F)
                + g ^ ((Fintype.card F - 1) / 2) * B'.eval (Polynomial.X ^ Fintype.card F)) = 0 := by
            rw [← hfac]; exact hR
          exact (mul_eq_zero.mp h2).resolve_left hXqC_ne
        have hne' : A' ≠ 0 ∨ B' ≠ 0 := by
          rcases hA with h | h
          · left; intro h0; exact h (by rw [hA', h0, mul_zero])
          · right; intro h0; exact h (by rw [hB', h0, mul_zero])
        have htot' : A'.natDegree + B'.natDegree ≤ n := by
          rcases hA with hA0 | hB0
          · have h1 := natDegree_div_lt hA' hA0
            have h2 := natDegree_div_le hB'
            omega
          · have h1 := natDegree_div_le hA'
            have h2 := natDegree_div_lt hB' hB0
            omega
        have hA'n : A'.natDegree < Fintype.card F := lt_of_le_of_lt (natDegree_div_le hA') hAn
        have hB'n : B'.natDegree < Fintype.card F := lt_of_le_of_lt (natDegree_div_le hB') hBn
        exact ih A' B' htot' hne' hA'd hB'd hA'n hB'n hR'
  exact key (A.natDegree + B.natDegree) A B le_rfl hA hAd hBd hAn hBn

end Commons.NumberTheory.Stepanov