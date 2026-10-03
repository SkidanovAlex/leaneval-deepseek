import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.fibre_ballCover
import Submission.Work.KMTPlan.A6.ConcAux.fibre_iteratedDeriv_dvd
import Submission.Work.KMTPlan.A6.ConcAux.ball_card
import Submission.Work.KMTPlan.A6.ConcAux.padicVal_of_dvd
import Submission.Work.Analysis.Concentration.Basic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Extracting a "good ball" from a large fibre of a polynomial modulo `p ^ k`

This is the ball-extraction step in the proof of Krause--Mirek--Tao's Appendix C,
Proposition `prop:zero` (the concentration estimates for polynomials modulo a prime power),
in the exact form needed by the weak-type estimate.

Given a polynomial `Q ∈ ℤ[X]` of degree `d = Q.natDegree ≥ 1`, a prime `p`, an exponent `k ≥ 1`
and a fibre `{x : ℤ/p^kℤ | Q x = y}` of size `≥ t`, the Bernstein ball cover
(`Work.KMTPlan.A6.ConcAux.fibre_ballCover`) exhibits the fibre as the union of at most `d`
`p`-adic balls *contained* in it.  Some ball therefore carries `≥ t/d` elements, and hence has
level `m` with `p^(k-m) ≥ t/d` — i.e. `k - m ≥ K₀` for the least `K₀` with `p^{K₀} ≥ t/d`.
On that ball, the `p`-adic Bernstein inequality
(`Work.KMTPlan.A6.ConcAux.fibre_iteratedDeriv_dvd`, applied with `l = 1`) gives
`p^k ∣ p^(m + (d+1) v_p(d!)) Q'(x)`, whence `v_p(Q'(x)) ≥ k - m - (d+1)v_p(d!) ≥ K₀ - (d+1)v_p(d!)`;
that is exactly the divisibility `p^(K₀ - (d+1)v_p(d!)) ∣ Q'(x)` required below.

This is the same statement as the helper lemma of
`Submission/Work/KMTPlan/A6/ConcAux/exists_good_ball.lean`, proved here in the namespace
`Work.KMTPlan.A6.ConcAux2` directly from the ball cover and Bernstein lemmas of that area.
-/

namespace Work.KMTPlan.A6.ConcAux2

open Polynomial Finset

theorem exists_good_ball (Q : Polynomial ℤ) (hQ : 1 ≤ Q.natDegree) (p k K₀ : ℕ) [Fact p.Prime] (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) (hA₀ : (Q.natDegree + 1) * padicValNat p Q.natDegree.factorial ≤ K₀) (hmin : ∀ m < K₀, (p : ℝ) ^ m < t / (Q.natDegree : ℝ)) (y : ZMod (p ^ k)) (hy : t ≤ (Work.Analysis.Concentration.polyFiberCard Q (p ^ k) y : ℝ)) : ∃ B : Finset (ZMod (p ^ k)), B ⊆ (Finset.univ.filter (fun x : ZMod (p ^ k) => Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x = y)) ∧ t / (Q.natDegree : ℝ) ≤ (B.card : ℝ) ∧ ∀ x ∈ B, (p : ℤ) ^ (K₀ - (Q.natDegree + 1) * padicValNat p Q.natDegree.factorial) ∣ (Polynomial.derivative Q).eval (x.val : ℤ) := by
  classical
  have hpF : p.Prime := Fact.out
  set d : ℕ := Q.natDegree with hd
  set A : ℕ := (d + 1) * padicValNat p d.factorial with hA
  set G : Polynomial ℤ := Q - Polynomial.C (y.val : ℤ) with hG
  have hGdeg : G.natDegree = d := by
    rw [hG, Polynomial.natDegree_sub_C]
  obtain ⟨N, hN, a, m, hm_le, hball, hcov⟩ :=
    Work.KMTPlan.A6.ConcAux.fibre_ballCover G p k hk
  set S : Finset (ZMod (p ^ k)) :=
    Finset.univ.filter (fun x : ZMod (p ^ k) => Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x = y) with hS
  have hScard : t ≤ (S.card : ℝ) := by
    have h1 : Work.Analysis.Concentration.polyFiberCard Q (p ^ k) y = S.card := by
      rw [hS]; rfl
    rwa [h1] at hy
  have zmod_iff : ∀ (a b : ℤ), ((a : ZMod (p ^ k)) = (b : ZMod (p ^ k))) ↔ (p : ℤ) ^ k ∣ a - b := by
    intro a b
    have h0 : ((a : ZMod (p ^ k)) = (b : ZMod (p ^ k))) ↔ (((a - b : ℤ) : ZMod (p ^ k)) = 0) := by
      rw [Int.cast_sub, sub_eq_zero]
    rw [h0, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_pow]
  have hmem_iff : ∀ x : ZMod (p ^ k),
      (Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x = y)
        ↔ (p : ℤ) ^ k ∣ G.eval (x.val : ℤ) := by
    intro x
    have hx : Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x
        = ((Q.eval (x.val : ℤ) : ℤ) : ZMod (p ^ k)) := by
      have h := Work.Analysis.Concentration.polyEvalZMod_natCast Q (p ^ k) x.val
      rwa [ZMod.natCast_zmod_val x] at h
    have hyv : (((y.val : ℤ)) : ZMod (p ^ k)) = y := by
      rw [Int.cast_natCast]; exact ZMod.natCast_zmod_val y
    have hge : Q.eval (x.val : ℤ) - (y.val : ℤ) = G.eval (x.val : ℤ) := by
      rw [hG, Polynomial.eval_sub, Polynomial.eval_C]
    have hAb : (Work.Analysis.Concentration.polyEvalZMod Q (p ^ k) x = y)
        ↔ (((Q.eval (x.val : ℤ) : ℤ) : ZMod (p ^ k)) = ((y.val : ℤ) : ZMod (p ^ k))) := by
      rw [hx]
      constructor
      · intro h'; rw [h']; exact hyv.symm
      · intro h'; rw [h']; exact hyv
    exact hAb.trans (by rw [zmod_iff, hge])
  set B : Fin N → Finset (ZMod (p ^ k)) := fun l =>
    Finset.univ.filter (fun x : ZMod (p ^ k) => (p : ℤ) ^ (m l) ∣ ((x.val : ℤ) - ((a l).val : ℤ))) with hB
  have hmemS : ∀ x : ZMod (p ^ k), x ∈ S ↔ (p : ℤ) ^ k ∣ G.eval (x.val : ℤ) := by
    intro x
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmem_iff x
  have hBcard : ∀ l : Fin N, (B l).card = p ^ (k - m l) := by
    intro l
    rw [hB]
    exact Work.KMTPlan.A6.ConcAux.ball_card p k (m l) (hm_le l) (a l)
  have hBsub : ∀ l : Fin N, B l ⊆ S := by
    intro l x hx
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hmemS x]
    exact hball l x hx
  have hcovS : S ⊆ Finset.univ.biUnion B := by
    intro x hx
    obtain ⟨l, hl⟩ := hcov x ((hmemS x).mp hx)
    rw [Finset.mem_biUnion]
    exact ⟨l, Finset.mem_univ l, by
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]; exact hl⟩
  have hScard_le : (S.card : ℝ) ≤ ∑ l : Fin N, ((B l).card : ℝ) := by
    have h1 : S.card ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hcovS
    have h2 : (Finset.univ.biUnion B).card ≤ ∑ l : Fin N, (B l).card := Finset.card_biUnion_le
    calc (S.card : ℝ) ≤ ((Finset.univ.biUnion B).card : ℝ) := by exact_mod_cast h1
      _ ≤ ((∑ l : Fin N, (B l).card : ℕ) : ℝ) := by exact_mod_cast h2
      _ = ∑ l : Fin N, ((B l).card : ℝ) := by push_cast; ring
  have hNle : N ≤ d := by
    have h := hN
    rw [hGdeg, max_eq_right hQ] at h
    exact h
  have hpigeon : ∃ l : Fin N, t / (d : ℝ) ≤ ((B l).card : ℝ) := by
    by_cases hN0 : N = 0
    · exfalso
      have hSempty : S = ∅ := by
        ext x
        constructor
        · intro hx
          obtain ⟨l, -, -⟩ := Finset.mem_biUnion.mp (hcovS hx)
          have := l.isLt
          omega
        · intro hx; simp at hx
      rw [hSempty] at hScard
      simp at hScard
      linarith
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
      by_contra hcon
      push Not at hcon
      have hsum_lt : ∑ l : Fin N, ((B l).card : ℝ) < ∑ _l : Fin N, (t / (d : ℝ)) := by
        refine Finset.sum_lt_sum (fun l _ => le_of_lt (hcon l))
          ⟨⟨0, hNpos⟩, Finset.mem_univ _, hcon ⟨0, hNpos⟩⟩
      have hNleR : (N : ℝ) ≤ (d : ℝ) := by exact_mod_cast hNle
      have htnd : (0 : ℝ) ≤ t / (d : ℝ) := by positivity
      have hNd : (N : ℝ) * (t / (d : ℝ)) ≤ (d : ℝ) * (t / (d : ℝ)) :=
        mul_le_mul_of_nonneg_right hNleR htnd
      have hcancel : (d : ℝ) * (t / (d : ℝ)) = t := by field_simp
      have hlt : ∑ l : Fin N, ((B l).card : ℝ) < t := by
        calc ∑ l : Fin N, ((B l).card : ℝ) < ∑ _l : Fin N, (t / (d : ℝ)) := hsum_lt
          _ = (N : ℝ) * (t / (d : ℝ)) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ (d : ℝ) * (t / (d : ℝ)) := hNd
          _ = t := hcancel
      have hle : t ≤ ∑ l : Fin N, ((B l).card : ℝ) := le_trans hScard hScard_le
      linarith
  obtain ⟨l, hl⟩ := hpigeon
  have hkml : K₀ ≤ k - m l := by
    by_contra h
    have h1 : (p : ℝ) ^ (k - m l) < t / (d : ℝ) := hmin (k - m l) (lt_of_not_ge h)
    have h2 : ((B l).card : ℝ) = (p : ℝ) ^ (k - m l) := by
      rw [hBcard l, Nat.cast_pow]
    linarith
  refine ⟨B l, hBsub l, hl, ?_⟩
  intro x hx
  have hx' : (p : ℤ) ^ (m l) ∣ ((x.val : ℤ) - ((a l).val : ℤ)) := by
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx
  have hiter := Work.KMTPlan.A6.ConcAux.fibre_iteratedDeriv_dvd G p k hk (hm_le l) (hball l) x hx' 1
    (by rw [hGdeg]; exact hQ)
  rw [one_mul, hGdeg] at hiter
  rw [Function.iterate_one] at hiter
  rw [hG, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] at hiter
  by_cases hz : (Polynomial.derivative Q).eval (x.val : ℤ) = 0
  · rw [hz]; exact dvd_zero _
  · have hval := Work.KMTPlan.A6.ConcAux.padicVal_of_dvd p k
      (m l + (d + 1) * padicValNat p d.factorial) hpF hz hiter
    rw [← hA] at hval
    have hK : K₀ - A ≤ padicValNat p ((Polynomial.derivative Q).eval (x.val : ℤ)).natAbs := by
      have := hm_le l
      omega
    have hzabs : ((Polynomial.derivative Q).eval (x.val : ℤ)).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.mpr hz
    have hdiv : p ^ (K₀ - A) ∣ ((Polynomial.derivative Q).eval (x.val : ℤ)).natAbs :=
      (padicValNat_dvd_iff_le hzabs).mpr hK
    have hnat : ((p : ℤ) ^ (K₀ - A)).natAbs = p ^ (K₀ - A) := by
      rw [Int.natAbs_pow, Int.natAbs_natCast]
    exact (Int.natAbs_dvd_natAbs).mp (by rwa [hnat])

end Work.KMTPlan.A6.ConcAux2
