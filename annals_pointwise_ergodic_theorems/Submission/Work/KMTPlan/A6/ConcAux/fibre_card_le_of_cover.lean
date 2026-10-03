/-
#  The fibre-count bound from a `p`-adic ball cover

This file contains the lemma `fibre_card_le_of_cover`, the residue-level estimate

`#{x : ZMod (p ^ k) | (p : ℤ) ^ k ∣ G.eval (x.val : ℤ)} ≤ C * p ^ (k * (1 - 1 / deg G))`

with a constant `C` independent of the prime `p` and the exponent `k`, obtained from the
two hypotheses of the paper (Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional
bilinear polynomial averages*, Appendix C, Proposition `prop:zero`):

* `hcover` : the fibre `{x | p ^ k ∣ G x}` is covered by at most `deg G` balls
  `B_l = {x | x ≡ a_l (mod p ^ (m_l))}` *each of which is contained in the fibre* (the
  "Bernstein ball cover"); and
* `hderiv` : on a ball contained in the fibre the iterated derivatives of `G` are divisible
  by prescribed powers of `p` (this is the `p`-adic consequence of the Bernstein inequality,
  "iterate (i) `d` times and intersect the covers").

The proof is the book-keeping of Proposition `prop:zero`(ii): on a ball of radius `p ^ m`
contained in the fibre, the `d`-th derivative of `G` (which is the nonzero constant
`d ! * lc G`) satisfies `p ^ k ∣ p ^ (d * m + (d+2) v_p (d !)) * (d ! * lc G)`, whence
`k ≤ d * m + (d+2) v_p (d !) + v_p (lc G)`; hence `m` is at least `(k - A) / d` with a
`p`-adically controlled `A`, and the ball has at most `p ^ (k - m) ≲ p ^ (k * (1 - 1/d))`
elements.  Summing over the `≤ d` balls gives the claim.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.ball_card
import Submission.Work.KMTPlan.A6.ConcAux.padicVal_of_dvd

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6.ConcAux

open Polynomial

/-- The `natDegree`-th iterated derivative of a polynomial with integer coefficients is the
constant polynomial `(natDegree !) * lc`. -/
lemma concAux_iterate_derivative_natDegree (G : Polynomial ℤ) :
    (derivative^[G.natDegree]) G =
      Polynomial.C ((G.natDegree.factorial : ℤ) * G.leadingCoeff) := by
  ext m
  rw [Polynomial.coeff_iterate_derivative]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [zero_add, Nat.descFactorial_self, Polynomial.coeff_natDegree, Polynomial.coeff_C,
      if_pos rfl]
    exact nsmul_eq_mul _ _
  · have hlt : G.natDegree < m + G.natDegree := Nat.lt_add_of_pos_left hm
    rw [Polynomial.coeff_C, if_neg (Nat.pos_iff_ne_zero.mp hm),
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    exact nsmul_zero _

/-- `p ^ v_p n ≤ n` for `n ≠ 0`. -/
lemma concAux_pow_padicValNat_le (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    p ^ padicValNat p n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((padicValNat_dvd_iff_le hn).mpr le_rfl)

/-- Elementary real arithmetic of the van der Corput exponent: if `k ≤ d * m + A` then
`p ^ (k - m) ≤ p ^ A * p ^ (k * (1 - 1 / d))` for `p ≥ 2`. -/
lemma concAux_rpow_card_le (p d k m A : ℕ) (hp : 2 ≤ p) (hd : 1 ≤ d) (hm : m ≤ k)
    (hA : k ≤ d * m + A) {C : ℝ} (hC : (p : ℝ) ^ A ≤ C) :
    (p : ℝ) ^ (k - m) ≤ C * (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (d : ℝ))) := by
  rw [← Real.rpow_natCast]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hAR : (0 : ℝ) ≤ (A : ℝ) := by positivity
  have hA' : ((k : ℕ) : ℝ) ≤ (d : ℝ) * ((m : ℕ) : ℝ) + (A : ℝ) := by
    have := Nat.cast_le (α := ℝ).mpr hA
    push_cast at this ⊢
    linarith
  have hexp : ((k - m : ℕ) : ℝ) ≤ (k : ℝ) * (1 - 1 / (d : ℝ)) + (A : ℝ) / (d : ℝ) := by
    rw [Nat.cast_sub hm, div_eq_inv_mul, div_eq_inv_mul]
    nlinarith [hA', hdR, inv_pos.mpr hdR, mul_inv_cancel₀ hdR.ne']
  calc (p : ℝ) ^ ((k - m : ℕ) : ℝ)
      ≤ (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (d : ℝ)) + (A : ℝ) / (d : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 hexp
    _ = (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (d : ℝ))) * (p : ℝ) ^ ((A : ℝ) / (d : ℝ)) := by
        rw [Real.rpow_add (by positivity)]
    _ ≤ (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (d : ℝ))) * C := by
        gcongr
        calc (p : ℝ) ^ ((A : ℝ) / (d : ℝ)) ≤ (p : ℝ) ^ (A : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le hp1
              rw [div_le_iff₀ hdR]; nlinarith [hAR, hd1]
          _ = (p : ℝ) ^ A := by rw [Real.rpow_natCast]
          _ ≤ C := hC
    _ = C * (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (d : ℝ))) := by ring

/-- **The fibre-count bound.**  From a cover of the fibre `{x | p ^ k ∣ G x}` of `ZMod (p ^ k)`
by at most `deg G` `p`-adic balls, each of which is contained in the fibre (`hcover`), and the
divisibility of the iterated derivatives of `G` on balls contained in the fibre (`hderiv`), the
fibre has at most `C * p ^ (k * (1 - 1 / deg G))` elements, with `C` independent of `p` and `k`.

This is the book-keeping of Proposition `prop:zero`(ii) of Krause–Mirek–Tao, Appendix C. -/
theorem fibre_card_le_of_cover (G : Polynomial ℤ) (hd : 1 ≤ G.natDegree)
    (hcover : ∀ (p k : ℕ) [Fact p.Prime], 1 ≤ k →
      ∃ N : ℕ, N ≤ max 1 G.natDegree ∧ ∃ a : Fin N → ZMod (p ^ k), ∃ m : Fin N → ℕ,
        (∀ l : Fin N, m l ≤ k) ∧
        (∀ (l : Fin N) (x : ZMod (p ^ k)), (p : ℤ) ^ (m l) ∣ ((x.val : ℤ) - ((a l).val : ℤ)) →
            (p : ℤ) ^ k ∣ G.eval (x.val : ℤ)) ∧
        (∀ x : ZMod (p ^ k), (p : ℤ) ^ k ∣ G.eval (x.val : ℤ) →
            ∃ l : Fin N, (p : ℤ) ^ (m l) ∣ ((x.val : ℤ) - ((a l).val : ℤ))))
    (hderiv : ∀ (p k : ℕ) [Fact p.Prime], 1 ≤ k → ∀ {a : ZMod (p ^ k)} {m : ℕ}, m ≤ k →
        (∀ x : ZMod (p ^ k), (p : ℤ) ^ m ∣ ((x.val : ℤ) - (a.val : ℤ)) →
            (p : ℤ) ^ k ∣ G.eval (x.val : ℤ)) →
        ∀ x : ZMod (p ^ k), (p : ℤ) ^ m ∣ ((x.val : ℤ) - (a.val : ℤ)) →
          ∀ l ≤ G.natDegree,
            (p : ℤ) ^ k ∣ (p : ℤ) ^ (l * m + (G.natDegree + 1) * padicValNat p G.natDegree.factorial) *
              ((Polynomial.derivative^[l]) G).eval (x.val : ℤ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k →
      ((Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ℤ) ^ k ∣ G.eval (x.val : ℤ))).card : ℝ)
        ≤ C * (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (G.natDegree : ℝ))) := by
  have hG0 : G ≠ 0 := by
    intro h
    rw [h] at hd
    simp at hd
  have hc0 : G.leadingCoeff ≠ 0 := fun h => hG0 (Polynomial.leadingCoeff_eq_zero.mp h)
  refine ⟨(G.natDegree : ℝ) * (((G.natDegree.factorial : ℕ) : ℝ) ^ (G.natDegree + 2)) *
      ((G.leadingCoeff.natAbs : ℕ) : ℝ), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (G.natDegree : ℝ) := by
      exact_mod_cast (by omega : 0 < G.natDegree)
    have h2 : (0 : ℝ) < ((G.natDegree.factorial : ℕ) : ℝ) :=
      by exact_mod_cast (Nat.factorial_pos G.natDegree)
    have h3 : (0 : ℝ) < ((G.leadingCoeff.natAbs : ℕ) : ℝ) :=
      by exact_mod_cast (Int.natAbs_pos.mpr hc0)
    positivity
  intro p hpF k hk
  have hp2 : 2 ≤ p := hpF.out.two_le
  have hpprime : p.Prime := hpF.out
  obtain ⟨N, hN, a, m, hm_le, hball_sub, hlevel_sub⟩ := hcover p k hk
  set S : Finset (ZMod (p ^ k)) :=
    Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ℤ) ^ k ∣ G.eval (x.val : ℤ)) with hSdef
  by_cases hN0 : N = 0
  · have hSempty : S = ∅ := by
      ext x
      constructor
      · intro hx
        rw [hSdef, Finset.mem_filter] at hx
        obtain ⟨l, -⟩ := hlevel_sub x hx.2
        have := l.isLt
        omega
      · intro hx
        simp at hx
    rw [hSempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  · have hNle : N ≤ G.natDegree := by
      have h := hN
      rwa [max_eq_right hd] at h
    set B : Fin N → Finset (ZMod (p ^ k)) := fun l =>
      Finset.univ.filter (fun x : ZMod (p ^ k) =>
        (p : ℤ) ^ (m l) ∣ ((x.val : ℤ) - ((a l).val : ℤ))) with hBdef
    have hSsub : S ⊆ Finset.univ.biUnion B := by
      intro x hx
      rw [hSdef, Finset.mem_filter] at hx
      obtain ⟨l, hl⟩ := hlevel_sub x hx.2
      rw [Finset.mem_biUnion]
      exact ⟨l, Finset.mem_univ l, by rw [hBdef, Finset.mem_filter]; exact ⟨Finset.mem_univ x, hl⟩⟩
    have hcard1 : (S.card : ℝ) ≤ ∑ l : Fin N, ((B l).card : ℝ) := by
      have h1 : S.card ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hSsub
      have h2 : (Finset.univ.biUnion B).card ≤ ∑ l : Fin N, (B l).card :=
        Finset.card_biUnion_le
      calc (S.card : ℝ) ≤ ((Finset.univ.biUnion B).card : ℝ) := by exact_mod_cast h1
        _ ≤ ((∑ l : Fin N, (B l).card : ℕ) : ℝ) := by exact_mod_cast h2
        _ = ∑ l : Fin N, ((B l).card : ℝ) := by push_cast; rfl
    have hper : ∀ l : Fin N, ((B l).card : ℝ) ≤
        (((G.natDegree.factorial : ℕ) : ℝ) ^ (G.natDegree + 2) *
            ((G.leadingCoeff.natAbs : ℕ) : ℝ)) *
          (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (G.natDegree : ℝ))) := by
      intro l
      have hml : m l ≤ k := hm_le l
      have hcardl : (B l).card = p ^ (k - m l) := by
        rw [hBdef]
        exact ball_card p k (m l) hml (a l)
      have hz : ((G.natDegree.factorial : ℤ) * G.leadingCoeff) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) hc0
      have hdiv : (p : ℤ) ^ k ∣
          (p : ℤ) ^ (G.natDegree * (m l) +
              (G.natDegree + 1) * padicValNat p G.natDegree.factorial) *
            ((G.natDegree.factorial : ℤ) * G.leadingCoeff) := by
        have h := hderiv p k hk (hm_le l) (hball_sub l) (a l) (by simp) G.natDegree le_rfl
        rw [concAux_iterate_derivative_natDegree, Polynomial.eval_C] at h
        exact h
      have hkA : k ≤ G.natDegree * (m l) +
          ((G.natDegree + 2) * padicValNat p G.natDegree.factorial +
            padicValNat p G.leadingCoeff.natAbs) := by
        have h := padicVal_of_dvd (z := (G.natDegree.factorial : ℤ) * G.leadingCoeff) p k
          (G.natDegree * (m l) + (G.natDegree + 1) * padicValNat p G.natDegree.factorial)
          hpprime hz hdiv
        rw [Int.natAbs_mul, Int.natAbs_natCast,
          padicValNat.mul (Nat.factorial_ne_zero _) (Int.natAbs_ne_zero.mpr hc0)] at h
        have hkey : (G.natDegree * (m l) + (G.natDegree + 1) * padicValNat p G.natDegree.factorial)
            + (padicValNat p G.natDegree.factorial + padicValNat p G.leadingCoeff.natAbs)
            = G.natDegree * (m l) + ((G.natDegree + 2) * padicValNat p G.natDegree.factorial
                + padicValNat p G.leadingCoeff.natAbs) := by ring
        omega
      have hCb : (p : ℝ) ^ ((G.natDegree + 2) * padicValNat p G.natDegree.factorial +
            padicValNat p G.leadingCoeff.natAbs)
          ≤ ((G.natDegree.factorial : ℕ) : ℝ) ^ (G.natDegree + 2) *
              ((G.leadingCoeff.natAbs : ℕ) : ℝ) := by
        have hnat : p ^ ((G.natDegree + 2) * padicValNat p G.natDegree.factorial +
              padicValNat p G.leadingCoeff.natAbs)
            ≤ G.natDegree.factorial ^ (G.natDegree + 2) * G.leadingCoeff.natAbs := by
          rw [pow_add, mul_comm (G.natDegree + 2) (padicValNat p G.natDegree.factorial),
            pow_mul]
          exact Nat.mul_le_mul
            (Nat.pow_le_pow_left (concAux_pow_padicValNat_le p _ (Nat.factorial_ne_zero _)) _)
            (concAux_pow_padicValNat_le p _ (Int.natAbs_ne_zero.mpr hc0))
        exact_mod_cast hnat
      rw [hcardl, Nat.cast_pow]
      exact concAux_rpow_card_le p G.natDegree k (m l)
        ((G.natDegree + 2) * padicValNat p G.natDegree.factorial +
          padicValNat p G.leadingCoeff.natAbs) hp2 hd hml hkA hCb
    calc (S.card : ℝ) ≤ ∑ l : Fin N, ((B l).card : ℝ) := hcard1
      _ ≤ ∑ l : Fin N, ((((G.natDegree.factorial : ℕ) : ℝ) ^ (G.natDegree + 2) *
            ((G.leadingCoeff.natAbs : ℕ) : ℝ)) *
              (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (G.natDegree : ℝ)))) :=
          Finset.sum_le_sum (fun l _ => hper l)
      _ = (N : ℝ) * ((((G.natDegree.factorial : ℕ) : ℝ) ^ (G.natDegree + 2) *
            ((G.leadingCoeff.natAbs : ℕ) : ℝ)) *
              (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (G.natDegree : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (G.natDegree : ℝ) * ((((G.natDegree.factorial : ℕ) : ℝ) ^ (G.natDegree + 2) *
            ((G.leadingCoeff.natAbs : ℕ) : ℝ)) *
              (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (G.natDegree : ℝ)))) := by
          have hNd : (N : ℝ) ≤ (G.natDegree : ℝ) := by exact_mod_cast hNle
          have hCnn : (0 : ℝ) ≤ ((G.natDegree.factorial : ℕ) : ℝ) ^ (G.natDegree + 2) *
              ((G.leadingCoeff.natAbs : ℕ) : ℝ) := by positivity
          have hpw : (0 : ℝ) ≤ (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (G.natDegree : ℝ))) :=
            Real.rpow_nonneg (by positivity) _
          exact mul_le_mul_of_nonneg_right hNd (mul_nonneg hCnn hpw)
      _ = (G.natDegree : ℝ) * (((G.natDegree.factorial : ℕ) : ℝ) ^ (G.natDegree + 2)) *
            ((G.leadingCoeff.natAbs : ℕ) : ℝ) *
              (p : ℝ) ^ ((k : ℝ) * (1 - 1 / (G.natDegree : ℝ))) := by
          ring

end Work.KMTPlan.A6.ConcAux
