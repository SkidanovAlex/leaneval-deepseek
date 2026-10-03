import Mathlib
import Submission.Work.Analysis.Concentration.PrimeUniform
import Submission.Work.KMTPlan.A6.ConcAux2.exists_good_ball
import Submission.Work.KMTPlan.A6.ConcAux2.levelSet_card_le
import Submission.Work.KMTPlan.A6.ConcAux2.card_le_of_good_balls
import Submission.Work.KMTPlan.A6.ConcAux2.weakType_bound_of_count

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fibre concentration on prime powers from the `p`-adic ball cover

This file proves `Work.Analysis.Concentration.Corollary1WeakType P P.natDegree` -- the weak-type
form of Krause--Mirek--Tao's Appendix C, Corollary `cor:1` -- from the `p`-adic ball cover of the
fibres of a polynomial (Proposition `prop:zero`): the fibre `{x : Z/p^k : P(x) = y}` is a union of
at most `deg P` balls contained in it, and on such a ball the iterated derivatives of `P` are
divisible by the corresponding powers of `p` (this is the Bernstein/von der Corput input).

The argument is the paper's proof of `prop:zero`(iii), described:
* for `y` with fibre size `h(y) >= t`, one of the covering balls has `>= t/deg P` elements (so its
  level is at least `log_p(t/deg P)`);
* on that ball the derivative `P'` is divisible by `p^{k-m-A_0}` (Bernstein), so the ball is
  contained in the level set `{p^L | P'}` with `L = K_0 - A_0` for the *minimal* `K_0` with
  `p^{K_0} >= t/deg P`;
* the balls for distinct `y` are disjoint (they lie in distinct fibres), so
  `#{y : h(y) >= t} * t/deg P <= #{x : p^L | P'(x)}`;
* the level set of `P'` of degree `d-1` is estimated by the same cover bound (the "van der Corput"
  step), giving `#{x : p^L | P'(x)} <= C' p^{k - L/(d-1)}`;
* substituting `p^L >= (t/deg P)/p^{A_0}` and `p^{A_0} <= (d!)^{d+1}` (uniform in the prime)
  yields the weak-type bound with a constant depending only on `P`.

The helper lemmas are in `exists_good_ball` (the ball extraction), `card_le_of_good_balls` (the
disjointness/counting step), `levelSet_card_le` (the level set of `P'` at a general level) and
`weakType_bound_of_count` (the final real arithmetic).
-/

namespace Work.KMTPlan.A6.ConcAux2

open Polynomial Finset
open Work.Analysis.Concentration

theorem fibreWeakType_of_cover (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    Work.Analysis.Concentration.Corollary1WeakType P P.natDegree := by
  classical
  have hd1 : 1 ≤ P.natDegree := by omega
  have hcastd : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd1
  -- the level-set estimate for the derivative of P
  obtain ⟨C', hC'pos, hC'bnd⟩ := Work.KMTPlan.A6.ConcAux.fibre_card_le_of_cover (Polynomial.derivative P)
    (by rw [Polynomial.natDegree_derivative]; omega)
    (fun p K _ hK => Work.KMTPlan.A6.ConcAux.fibre_ballCover (Polynomial.derivative P) p K hK)
    (fun p K _ hK a m hm hball => Work.KMTPlan.A6.ConcAux.fibre_iteratedDeriv_dvd (Polynomial.derivative P) p K hK hm hball)
  -- the constants
  set T₀ : ℝ := (P.natDegree : ℝ) * (P.natDegree.factorial : ℝ) ^ (P.natDegree + 1) with hT₀def
  have hfact_pos : (0 : ℝ) < (P.natDegree.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hT₀pos : 0 < T₀ := by rw [hT₀def]; positivity
  have hd2R : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have he_pos : 0 < (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) :=
    div_pos (by linarith) (by linarith)
  set Cbig : ℝ :=
    max (T₀ ^ ((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1))) (C' * T₀ * (P.natDegree : ℝ) ^ 2)
    with hCbigdef
  have hCbigpos : 0 < Cbig :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hT₀pos _) (le_max_left _ _)
  refine ⟨Cbig, hCbigpos, ?_⟩
  intro p K hpF hK t ht
  have hp2 : 2 ≤ p := hpF.out.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp1' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hdR : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
  set A : Finset (ZMod (p ^ K)) :=
    Finset.univ.filter (fun y => t ≤ (polyFiberCard P (p ^ K) y : ℝ)) with hAdef
  have hAcard : (A.card : ℝ) ≤ (p : ℝ) ^ K := by
    calc (A.card : ℝ) ≤ ((Finset.univ : Finset (ZMod (p ^ K))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (p : ℝ) ^ K := by rw [Finset.card_univ, ZMod.card]; push_cast; ring
  set A₀ : ℕ := (P.natDegree + 1) * padicValNat p P.natDegree.factorial with hA₀def
  have hpA₀' : (p : ℝ) ^ A₀ ≤ (P.natDegree.factorial : ℝ) ^ (P.natDegree + 1) := by
    have hpad : p ^ padicValNat p P.natDegree.factorial ≤ P.natDegree.factorial :=
      Work.KMTPlan.A6.ConcAux.concAux_pow_padicValNat_le p _ (Nat.factorial_ne_zero _)
    rw [hA₀def, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hpad) _
  have hpA₀ : (p : ℝ) ^ A₀ ≤ T₀ := by
    rw [hT₀def]
    refine hpA₀'.trans ?_
    nlinarith [hcastd, hfact_pos,
      pow_nonneg (le_of_lt hfact_pos) (P.natDegree + 1)]
  by_cases hsmall : t ≤ T₀
  · -- small t: the trivial bound suffices
    have hone : 1 ≤ T₀ ^ ((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1))
        * t ^ (-((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1))) := by
      have h1 : t ^ ((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1))
          ≤ T₀ ^ ((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) :=
        Real.rpow_le_rpow ht.le hsmall he_pos.le
      have h2 : (0 : ℝ) < t ^ ((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) :=
        Real.rpow_pos_of_pos ht _
      rw [Real.rpow_neg ht.le, ← div_eq_mul_inv, le_div_iff₀ h2, one_mul]
      exact h1
    have hmax : T₀ ^ ((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) ≤ Cbig := by
      rw [hCbigdef]; exact le_max_left _ _
    calc (A.card : ℝ) ≤ (p : ℝ) ^ K := hAcard
      _ = 1 * (p : ℝ) ^ K := by ring
      _ ≤ (T₀ ^ ((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1))
            * t ^ (-((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)))) * (p : ℝ) ^ K :=
          mul_le_mul_of_nonneg_right hone (by positivity)
      _ ≤ Cbig * t ^ (-((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1))) * (p : ℝ) ^ K := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hmax (Real.rpow_nonneg ht.le _)
      _ = Cbig * t ^ (-((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1))) * ((p ^ K : ℕ) : ℝ) := by
          rw [Nat.cast_pow]
  · -- large t: the cover and the derivative give the decay
    push_neg at hsmall
    have htdA₀ : (p : ℝ) ^ A₀ < t / (P.natDegree : ℝ) := by
      rw [lt_div_iff₀ hdR]
      have h2 : (p : ℝ) ^ A₀ * (P.natDegree : ℝ)
          ≤ (P.natDegree.factorial : ℝ) ^ (P.natDegree + 1) * (P.natDegree : ℝ) :=
        mul_le_mul_of_nonneg_right hpA₀' (le_of_lt hdR)
      nlinarith [h2, hsmall, hcastd]
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (t / (P.natDegree : ℝ)) hp1'
    have hex : ∃ m : ℕ, t / (P.natDegree : ℝ) ≤ (p : ℝ) ^ m := ⟨m, hm.le⟩
    set K₀ : ℕ := Nat.find hex with hK₀def
    have hKge : t / (P.natDegree : ℝ) ≤ (p : ℝ) ^ K₀ := Nat.find_spec hex
    have hKmin : ∀ m < K₀, (p : ℝ) ^ m < t / (P.natDegree : ℝ) := by
      intro m hm'
      exact lt_of_not_ge (Nat.find_min hex hm')
    have hA₀lt : A₀ < K₀ := by
      by_contra h
      have h' : K₀ ≤ A₀ := le_of_not_gt h
      have hmono : (p : ℝ) ^ K₀ ≤ (p : ℝ) ^ A₀ := pow_le_pow_right₀ hp1 h'
      linarith [hKge, htdA₀]
    have hA₀K₀ : A₀ ≤ K₀ := le_of_lt hA₀lt
    by_cases hAne : A = ∅
    · rw [hAne, Finset.card_empty, Nat.cast_zero, Nat.cast_pow]
      positivity
    · obtain ⟨y₀, hy₀⟩ := Finset.nonempty_iff_ne_empty.mpr hAne
      rw [hAdef] at hy₀
      have hy₀' : t ≤ (polyFiberCard P (p ^ K) y₀ : ℝ) := (Finset.mem_filter.mp hy₀).2
      have hK₀K : K₀ ≤ K := by
        by_contra h
        have h' : K < K₀ := lt_of_not_ge h
        have hfib : (polyFiberCard P (p ^ K) y₀ : ℝ) ≤ (p : ℝ) ^ K := by
          have h1 : polyFiberCard P (p ^ K) y₀ ≤ p ^ K := by
            calc polyFiberCard P (p ^ K) y₀ ≤ (Finset.univ : Finset (ZMod (p ^ K))).card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
              _ = p ^ K := by rw [Finset.card_univ, ZMod.card]
          exact_mod_cast h1
        have htle : t ≤ (p : ℝ) ^ K := le_trans hy₀' hfib
        have hle : t / (P.natDegree : ℝ) ≤ (p : ℝ) ^ K := by
          rw [div_le_iff₀ hdR]
          nlinarith [htle, ht, hcastd]
        exact absurd hle (not_le.mpr (hKmin K h'))
      have hL1 : 1 ≤ K₀ - A₀ := by omega
      have hLK : K₀ - A₀ ≤ K := by omega
      have hgood : ∀ y : ZMod (p ^ K), y ∈ A → ∃ B : Finset (ZMod (p ^ K)),
          B ⊆ Finset.univ.filter (fun x : ZMod (p ^ K) => polyEvalZMod P (p ^ K) x = y)
          ∧ t / (P.natDegree : ℝ) ≤ (B.card : ℝ)
          ∧ ∀ x ∈ B, (p : ℤ) ^ (K₀ - A₀) ∣ (Polynomial.derivative P).eval (x.val : ℤ) := by
        intro y hy
        rw [hAdef] at hy
        exact exists_good_ball P hd1 p K K₀ hK t ht hA₀K₀ hKmin y
          (Finset.mem_filter.mp hy).2
      have hcount := card_le_of_good_balls (p := p) (k := K) (L := K₀ - A₀) (t := t) ht
        P.natDegree P A (fun y hy => by rw [hAdef] at hy; exact (Finset.mem_filter.mp hy).2) hgood
      have hS := levelSet_card_le (Polynomial.derivative P)
        (by rw [Polynomial.natDegree_derivative]; omega) C' hC'pos hC'bnd p K (K₀ - A₀) hL1 hLK
      have hcomb : (A.card : ℝ) * (t / (P.natDegree : ℝ)) ≤
          C' * (p : ℝ) ^ ((K : ℝ) - (((K₀ - A₀ : ℕ)) : ℝ)
            / (((Polynomial.derivative P).natDegree : ℕ) : ℝ)) :=
        le_trans hcount hS
      have hd'c : (((Polynomial.derivative P).natDegree : ℕ) : ℝ) = (P.natDegree : ℝ) - 1 := by
        rw [Polynomial.natDegree_derivative, Nat.cast_sub hd1]
        push_cast
        ring
      have hmain := weakType_bound_of_count (p := (p : ℝ)) (t := t) (A := (A.card : ℝ)) (C' := C')
        (k := K) (K₀ := K₀) (A₀ := A₀) (d := P.natDegree)
        (d' := (Polynomial.derivative P).natDegree)
        (by exact_mod_cast hp2) ht hd hd'c hC'pos (by positivity) hA₀K₀ hpA₀ hKge hcomb
      rw [hCbigdef, hT₀def, Nat.cast_pow]
      exact hmain

end Work.KMTPlan.A6.ConcAux2
