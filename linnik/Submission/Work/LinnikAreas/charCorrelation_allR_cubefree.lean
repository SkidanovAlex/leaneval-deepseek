import Mathlib
import Submission.Work.LinnikAreas.CorrAllR.Prelude
import Submission.Work.LinnikAreas.CorrAllR.corrSumV_sq_good
import Submission.Work.LinnikAreas.CorrAllR.corrSumV_crt_split

/-!
# The general-`r` correlation bound for cube-free moduli (the singleton case)

This file proves

`Work.LinnikAreas.charCorrelation_allR_cubefree`,

the general-`r` form of `Commons.NumberTheory.DirichletCharacter.charCorrelation6_cubefree_global`:
for a cube-free modulus `q`, a primitive non-trivial Dirichlet character `χ` mod `q`, a `2r`-tuple
of shifts `v` and an index `i` whose value `v i` occurs only once (as an integer!),

`‖∑_{x : ZMod q} χ (∏_{l<r} (x + v_l)) · conj (χ (∏_{l<r} (x + v_{r+l})))‖`
`  ≤ (2r)^{ω(q)} · √q · ∏_{j ≠ i} gcd (q, |v_i - v_j|)`.

The proof is the induction of `charCorrelation6_cubefree_global` (strong induction on `q`, peeling
off one prime at a time via the Chinese remainder theorem), with the local inputs

* `corrSumV_prime_good_local` — the prime-modulus bound `2r √p` in the unique-modulo-`p` case
  (the Weil bound `weil_local_bound` combined with `mult_modEq_of_const_mul_pow`), and
* `CorrAllR.corrSumV_sq_good` — the prime-square bound `2r p` for primitive `χ` mod `p²`,

together with the CRT splitting `CorrAllR.corrSumV_crt_split`.  In the "degenerate" situation, where
some other shift is congruent to `v i` modulo the prime `p` under consideration, the trivial bound
`p` (resp. `p²`) is already dominated by the `gcd` weight, so that case needs no local input.
-/

open Finset
open scoped BigOperators

namespace Work.LinnikAreas

open Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- The sum appearing in the statement of `charCorrelation_allR_cubefree` is `corrSumV`. -/
lemma sum_prod_chi_eq_corrSumV (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℕ)
    (v : Fin (r + r) → ℕ) :
    (∑ x : ZMod q, (∏ l : Fin r, χ ((x : ZMod q) + ((v (Fin.castAdd r l) : ℕ) : ZMod q)))
        * (∏ l : Fin r,
            (starRingEnd ℂ) (χ ((x : ZMod q) + ((v (Fin.natAdd r l) : ℕ) : ZMod q)))))
      = corrSumV q χ r v := by
  rw [corrSumV]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← map_prod (starRingEnd ℂ)
        (fun l : Fin r => χ ((x : ZMod q) + ((v (Fin.natAdd r l) : ℕ) : ZMod q))) Finset.univ,
      ← map_prod χ
        (fun l : Fin r => ((x : ZMod q) + ((v (Fin.castAdd r l) : ℕ) : ZMod q))) Finset.univ,
      ← map_prod χ
        (fun l : Fin r => ((x : ZMod q) + ((v (Fin.natAdd r l) : ℕ) : ZMod q))) Finset.univ]

/-- A congruence of natural numbers modulo `p` implies that `p` divides the absolute value of
their difference. -/
lemma dvd_natAbs_sub_of_zmod_eq {p x y : ℕ} (h : (x : ZMod p) = (y : ZMod p)) :
    p ∣ ((x : ℤ) - (y : ℤ)).natAbs := by
  have h0 : (((x : ℤ) - (y : ℤ) : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
  have h1 : (p : ℤ) ∣ ((x : ℤ) - (y : ℤ)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((x : ℤ) - (y : ℤ)) p).mp h0
  have h2 : ((p : ℤ)).natAbs ∣ (((x : ℤ) - (y : ℤ))).natAbs := Int.natAbs_dvd_natAbs.mpr h1
  simpa using h2

/-- The `gcd` weight `gcdWeightV n v i` is at least `1` when `n ≠ 0`. -/
lemma one_le_gcdWeightV {n : ℕ} (hn : n ≠ 0) {r : ℕ} (v : Fin (r + r) → ℕ) (i : Fin (r + r)) :
    1 ≤ gcdWeightV n v i := by
  refine Finset.one_le_prod₀ (fun j _ => ?_)
  have h : 0 < Nat.gcd n (((v i : ℤ) - (v j : ℤ)).natAbs) :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  exact_mod_cast h

/-- If `d` divides the `j`-th factor of the `gcd` weight, then `d` is at most the whole weight. -/
lemma le_gcdWeightV_of_dvd {n : ℕ} (hn : n ≠ 0) {r : ℕ} (v : Fin (r + r) → ℕ) (i : Fin (r + r))
    {j : Fin (r + r)} (hj : j ≠ i) {d : ℕ}
    (hd : d ∣ Nat.gcd n (((v i : ℤ) - (v j : ℤ)).natAbs)) :
    (d : ℝ) ≤ gcdWeightV n v i := by
  have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
  have hpos : 0 < Nat.gcd n (((v i : ℤ) - (v j : ℤ)).natAbs) :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  have hle : d ≤ Nat.gcd n (((v i : ℤ) - (v j : ℤ)).natAbs) := Nat.le_of_dvd hpos hd
  have hleR : (d : ℝ) ≤ ((Nat.gcd n (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hrest : 1 ≤ ∏ j' ∈ (Finset.univ.erase i).erase j,
      ((Nat.gcd n (((v i : ℤ) - (v j' : ℤ)).natAbs) : ℕ) : ℝ) := by
    refine Finset.one_le_prod₀ (fun j' _ => ?_)
    have h : 0 < Nat.gcd n (((v i : ℤ) - (v j' : ℤ)).natAbs) :=
      Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
    exact_mod_cast h
  calc (d : ℝ) ≤ ((Nat.gcd n (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ) := hleR
    _ ≤ ((Nat.gcd n (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ)
          * ∏ j' ∈ (Finset.univ.erase i).erase j,
              ((Nat.gcd n (((v i : ℤ) - (v j' : ℤ)).natAbs) : ℕ) : ℝ) :=
        le_mul_of_one_le_right (by positivity) hrest
    _ = gcdWeightV n v i := by
        rw [gcdWeightV, ← Finset.mul_prod_erase (Finset.univ.erase i)
          (fun j' => ((Nat.gcd n (((v i : ℤ) - (v j' : ℤ)).natAbs) : ℕ) : ℝ)) hmem]

/-- **The local bound at a prime modulus, unique-modulo-`p` case.**  For a non-trivial character
`χ` modulo a prime `p` and a `2r`-tuple of shifts whose `i`-th entry is unique modulo `p`, the
correlation sum is at most `2r √p`.

The uniqueness modulo `p` forces the "non-degenerate" case of the Weil bound: at the residue
`x = v i` the two multiplicity counts differ (`1` against `0`), which by the contrapositive of
`mult_modEq_of_const_mul_pow` is exactly the non-degeneracy hypothesis of `weil_local_bound`. -/
lemma corrSumV_prime_good_local (p : ℕ) [Fact p.Prime] [NeZero p]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) {r : ℕ} (hr : 1 ≤ r) (v : Fin (r + r) → ℕ)
    (i : Fin (r + r)) (huniq : IsUniqModV p v i) :
    ‖corrSumV p χ r v‖ ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) := by
  classical
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  set a : Fin r → ZMod p := fun l => ((v (Fin.castAdd r l) : ℕ) : ZMod p) with ha
  set b : Fin r → ZMod p := fun l => ((v (Fin.natAdd r l) : ℕ) : ZMod p) with hb
  have hgood : ∃ x : ZMod p,
      (Finset.univ.filter (fun l : Fin r => a l = x)).card % orderOf χ
        ≠ (Finset.univ.filter (fun l : Fin r => b l = x)).card % orderOf χ := by
    rcases lt_or_ge i.val r with hi | hi
    · refine ⟨(v i : ZMod p), ?_⟩
      have hk : Fin.castAdd r (⟨i.val, hi⟩ : Fin r) = i := Fin.ext (by simp)
      have hA : (Finset.univ.filter (fun l : Fin r => a l = (v i : ZMod p))).card = 1 := by
        have hsingle : (Finset.univ.filter (fun l : Fin r => a l = (v i : ZMod p)))
            = {(⟨i.val, hi⟩ : Fin r)} := by
          ext l
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hl
            by_contra hne
            have h1 : Fin.castAdd r l ≠ i := by
              intro hcon
              have hv : l.val = i.val := by simpa [Fin.castAdd] using congrArg Fin.val hcon
              exact hne (Fin.ext (by simpa using hv))
            have hl' : ((v (Fin.castAdd r l) : ℕ) : ZMod p) = (v i : ZMod p) := hl
            exact huniq (Fin.castAdd r l) h1
              ((ZMod.natCast_eq_natCast_iff (v (Fin.castAdd r l)) (v i) p).mp hl')
          · intro hl
            rw [hl]
            show ((v (Fin.castAdd r (⟨i.val, hi⟩ : Fin r)) : ℕ) : ZMod p) = ((v i : ℕ) : ZMod p)
            rw [hk]
        rw [hsingle, Finset.card_singleton]
      have hB : (Finset.univ.filter (fun l : Fin r => b l = (v i : ZMod p))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro l _ hl
        have hne : Fin.natAdd r l ≠ i := by
          intro hcon
          have hv : r + l.val = i.val := by simpa [Fin.natAdd] using congrArg Fin.val hcon
          omega
        have hl' : ((v (Fin.natAdd r l) : ℕ) : ZMod p) = (v i : ZMod p) := hl
        exact huniq (Fin.natAdd r l) hne
          ((ZMod.natCast_eq_natCast_iff (v (Fin.natAdd r l)) (v i) p).mp hl')
      rw [hA, hB, Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < orderOf χ)]
      exact one_ne_zero
    · refine ⟨(v i : ZMod p), ?_⟩
      have hk : Fin.natAdd r (⟨i.val - r, by omega⟩ : Fin r) = i := Fin.ext (by simp; omega)
      have hB : (Finset.univ.filter (fun l : Fin r => b l = (v i : ZMod p))).card = 1 := by
        have hsingle : (Finset.univ.filter (fun l : Fin r => b l = (v i : ZMod p)))
            = {(⟨i.val - r, by omega⟩ : Fin r)} := by
          ext l
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hl
            by_contra hne
            have h1 : Fin.natAdd r l ≠ i := by
              intro hcon
              have hv : r + l.val = i.val := by simpa [Fin.natAdd] using congrArg Fin.val hcon
              exact hne (Fin.ext (by simp; omega))
            have hl' : ((v (Fin.natAdd r l) : ℕ) : ZMod p) = (v i : ZMod p) := hl
            exact huniq (Fin.natAdd r l) h1
              ((ZMod.natCast_eq_natCast_iff (v (Fin.natAdd r l)) (v i) p).mp hl')
          · intro hl
            rw [hl]
            show ((v (Fin.natAdd r (⟨i.val - r, by omega⟩ : Fin r)) : ℕ) : ZMod p)
                = ((v i : ℕ) : ZMod p)
            rw [hk]
        rw [hsingle, Finset.card_singleton]
      have hA : (Finset.univ.filter (fun l : Fin r => a l = (v i : ZMod p))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro l _ hl
        have hne : Fin.castAdd r l ≠ i := by
          intro hcon
          have hv : l.val = i.val := by simpa [Fin.castAdd] using congrArg Fin.val hcon
          omega
        have hl' : ((v (Fin.castAdd r l) : ℕ) : ZMod p) = (v i : ZMod p) := hl
        exact huniq (Fin.castAdd r l) hne
          ((ZMod.natCast_eq_natCast_iff (v (Fin.castAdd r l)) (v i) p).mp hl')
      rw [hA, hB, Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < orderOf χ)]
      exact zero_ne_one
  obtain ⟨x, hx⟩ := hgood
  have hgood_poly : ∀ (c : ZMod p) (Q : Polynomial (ZMod p)),
      (∏ l : Fin r, (Polynomial.X + Polynomial.C (a l) : Polynomial (ZMod p)))
        * (∏ l : Fin r, (Polynomial.X + Polynomial.C (b l) : Polynomial (ZMod p)))
            ^ (orderOf χ - 1)
      ≠ Polynomial.C c * Q ^ (orderOf χ) := by
    intro c Q hcon
    exact hx (Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow hm2 a b hcon x)
  have hsum : corrSumV p χ r v = ∑ x : ZMod p,
      (∏ l : Fin r, χ (x + a l)) * (∏ l : Fin r, (starRingEnd ℂ) (χ (x + b l))) := by
    rw [ha, hb]
    exact (sum_prod_chi_eq_corrSumV p χ r v).symm
  rw [hsum]
  exact weil_local_bound χ hχ r hr a b hgood_poly

/-- **Prime modulus.**  For a non-trivial character `χ` modulo a prime `p`, a `2r`-tuple of
shifts `v` whose `i`-th entry is unique (as an integer), the correlation sum is at most
`2r √p · ∏_{j ≠ i} gcd (p, |v_i - v_j|)`.

If some other shift is congruent to `v i` modulo `p` the `gcd` weight is at least `p` and the
trivial bound `p` suffices; otherwise the uniqueness hypothesis is exactly `IsUniqModV p v i` and
`corrSumV_prime_good_local` gives `2r √p`. -/
lemma corrSumV_prime_bound (p : ℕ) [Fact p.Prime] [NeZero p] (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) {r : ℕ} (hr : 1 ≤ r) (v : Fin (r + r) → ℕ) (i : Fin (r + r))
    (huniq : ∀ j : Fin (r + r), j ≠ i → v j ≠ v i) :
    ‖corrSumV p χ r v‖ ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) * gcdWeightV p v i := by
  have hp : p.Prime := Fact.out
  by_cases hc : ∃ j : Fin (r + r), j ≠ i ∧ (v j : ZMod p) = (v i : ZMod p)
  · obtain ⟨j, hjne, hjeq⟩ := hc
    have hdvd : p ∣ Nat.gcd p (((v i : ℤ) - (v j : ℤ)).natAbs) :=
      Nat.dvd_gcd dvd_rfl (dvd_natAbs_sub_of_zmod_eq hjeq.symm)
    have hW : (p : ℝ) ≤ gcdWeightV p v i := le_gcdWeightV_of_dvd (NeZero.ne p) v i hjne hdvd
    refine (corrSumV_norm_le_card p χ r v).trans ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hsp : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (by linarith)
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hfac : (1 : ℝ) ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) := by nlinarith
    have hfacnn : (0 : ℝ) ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) := le_trans zero_le_one hfac
    calc (p : ℝ) ≤ ((2 * r : ℝ) * Real.sqrt (p : ℝ)) * (p : ℝ) := by nlinarith
      _ ≤ ((2 * r : ℝ) * Real.sqrt (p : ℝ)) * gcdWeightV p v i :=
          mul_le_mul_of_nonneg_left hW hfacnn
  · have huniqmod : IsUniqModV p v i := by
      intro j hj hmod
      exact hc ⟨j, hj, (ZMod.natCast_eq_natCast_iff (v j) (v i) p).mpr hmod⟩
    refine (corrSumV_prime_good_local p χ hχ hr v i huniqmod).trans ?_
    have hW : 1 ≤ gcdWeightV p v i := one_le_gcdWeightV (NeZero.ne p) v i
    have hnn : (0 : ℝ) ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) := by positivity
    calc (2 * r : ℝ) * Real.sqrt (p : ℝ)
          = (2 * r : ℝ) * Real.sqrt (p : ℝ) * 1 := by ring
      _ ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) * gcdWeightV p v i :=
          mul_le_mul_of_nonneg_left hW hnn

/-- **Prime square.**  For a primitive non-trivial character `χ` modulo `p²`, a `2r`-tuple of
shifts `v` whose `i`-th entry is unique (as an integer), the correlation sum is at most
`2r p · ∏_{j ≠ i} gcd (p², |v_i - v_j|)`.  Same dichotomy as in the prime case, using
`CorrAllR.corrSumV_sq_good` in the unique-modulo-`p` case. -/
lemma corrSumV_primeSq_bound (p : ℕ) [Fact p.Prime] [NeZero (p ^ 2)]
    (χ : DirichletCharacter ℂ (p ^ 2)) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {r : ℕ} (hr : 1 ≤ r) (v : Fin (r + r) → ℕ) (i : Fin (r + r))
    (huniq : ∀ j : Fin (r + r), j ≠ i → v j ≠ v i) :
    ‖corrSumV (p ^ 2) χ r v‖ ≤ (2 * r : ℝ) * (p : ℝ) * gcdWeightV (p ^ 2) v i := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  by_cases hc : ∃ j : Fin (r + r), j ≠ i ∧ (v j : ZMod p) = (v i : ZMod p)
  · obtain ⟨j, hjne, hjeq⟩ := hc
    have hdvd : p ∣ Nat.gcd (p ^ 2) (((v i : ℤ) - (v j : ℤ)).natAbs) :=
      Nat.dvd_gcd (⟨p, by ring⟩ : p ∣ p ^ 2) (dvd_natAbs_sub_of_zmod_eq hjeq.symm)
    have hW : (p : ℝ) ≤ gcdWeightV (p ^ 2) v i :=
      le_gcdWeightV_of_dvd (pow_ne_zero 2 hp.pos.ne') v i hjne hdvd
    have htriv : ‖corrSumV (p ^ 2) χ r v‖ ≤ (p : ℝ) ^ 2 := by
      simpa only [Nat.cast_pow] using corrSumV_norm_le_card (p ^ 2) χ r v
    refine htriv.trans ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hpnn : (0 : ℝ) ≤ (p : ℝ) := by linarith
    have hW1 : (1 : ℝ) ≤ gcdWeightV (p ^ 2) v i := le_trans (by linarith : (1 : ℝ) ≤ (p : ℝ)) hW
    calc (p : ℝ) ^ 2 = (p : ℝ) * (p : ℝ) := by ring
      _ ≤ (p : ℝ) * gcdWeightV (p ^ 2) v i := mul_le_mul_of_nonneg_left hW hpnn
      _ ≤ ((2 * r : ℝ) * (p : ℝ)) * gcdWeightV (p ^ 2) v i := by
          apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one hW1)
          nlinarith
  · have huniqmod : IsUniqModV p v i := by
      intro j hj hmod
      exact hc ⟨j, hj, (ZMod.natCast_eq_natCast_iff (v j) (v i) p).mpr hmod⟩
    by_cases hp2 : p = 2
    · -- `p = 2`: the trivial bound already suffices, no local input needed.
      have hp2' : (p : ℝ) = 2 := by rw [hp2]; norm_num
      have htriv : ‖corrSumV (p ^ 2) χ r v‖ ≤ (p : ℝ) ^ 2 := by
        simpa only [Nat.cast_pow] using corrSumV_norm_le_card (p ^ 2) χ r v
      have hW : 1 ≤ gcdWeightV (p ^ 2) v i := one_le_gcdWeightV (pow_ne_zero 2 hp.pos.ne') v i
      have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      calc ‖corrSumV (p ^ 2) χ r v‖ ≤ (p : ℝ) ^ 2 := htriv
        _ = 4 := by rw [hp2']; norm_num
        _ ≤ (2 * r : ℝ) * (p : ℝ) * gcdWeightV (p ^ 2) v i := by
            rw [hp2']; nlinarith
    · refine (CorrAllR.corrSumV_sq_good p χ hprim hχ (by omega) v i huniqmod).trans ?_
      have hW : 1 ≤ gcdWeightV (p ^ 2) v i := one_le_gcdWeightV (pow_ne_zero 2 hp.pos.ne') v i
      have hnn : (0 : ℝ) ≤ (2 * r : ℝ) * (p : ℝ) := by positivity
      calc (2 * r : ℝ) * (p : ℝ) = (2 * r : ℝ) * (p : ℝ) * 1 := by ring
        _ ≤ (2 * r : ℝ) * (p : ℝ) * gcdWeightV (p ^ 2) v i :=
            mul_le_mul_of_nonneg_left hW hnn

/-- **The general-`r` correlation bound for cube-free moduli.** -/
theorem corrSumV_bound (r : ℕ) (hr : 1 ≤ r) :
    ∀ (n : ℕ) [NeZero n], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ n) →
      ∀ (χ : DirichletCharacter ℂ n), χ.IsPrimitive → χ ≠ 1 →
      ∀ (v : Fin (r + r) → ℕ) (i : Fin (r + r)),
        (∀ j : Fin (r + r), j ≠ i → v j ≠ v i) →
        ‖corrSumV n χ r v‖
          ≤ (2 * r : ℝ) ^ (n.primeFactors.card) * Real.sqrt (n : ℝ) * gcdWeightV n v i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnNZ hncube χ hprim hχ v i huniq
    by_cases hpp : IsPrimePow n
    · obtain ⟨p, e, hp, he, hn_eq⟩ := (isPrimePow_nat_iff n).mp hpp
      haveI : Fact p.Prime := ⟨hp⟩
      have he3 : e ≤ 2 := by
        by_contra h
        rw [not_le] at h
        have hd : p ^ 3 ∣ p ^ e := pow_dvd_pow p (by omega)
        rw [hn_eq] at hd
        exact hncube p hp hd
      rcases (by omega : e = 1 ∨ e = 2) with he1 | he2
      · rw [he1, pow_one] at hn_eq
        subst n
        haveI : NeZero p := hnNZ
        rw [hp.primeFactors, Finset.card_singleton, pow_one]
        exact corrSumV_prime_bound p χ hχ hr v i huniq
      · rw [he2] at hn_eq
        subst n
        haveI : NeZero (p ^ 2) := hnNZ
        have hpp2 : (p ^ 2).primeFactors.card = 1 := by
          rw [Nat.primeFactors_pow p (by norm_num : 2 ≠ 0), hp.primeFactors]
          simp
        have hsqrt : Real.sqrt (((p ^ 2 : ℕ)) : ℝ) = (p : ℝ) := by
          rw [Nat.cast_pow, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (p : ℝ))]
        rw [hpp2, hsqrt, pow_one]
        exact corrSumV_primeSq_bound p χ hprim hχ hr v i huniq
    · by_cases hn1 : n = 1
      · subst hn1
        have hW : gcdWeightV 1 v i = 1 := by
          rw [gcdWeightV]
          simp
        rw [hW, Nat.primeFactors_one, Finset.card_empty, pow_zero, Nat.cast_one, Real.sqrt_one,
          mul_one, one_mul]
        exact (corrSumV_norm_le_card 1 χ r v).trans (le_of_eq (by norm_num))
      · have hn2 : 2 ≤ n := by have h := NeZero.ne n; omega
        obtain ⟨u, w, hu1, hw1, huw, huw_eq⟩ := exists_coprime_factorization hn2 hpp
        subst n
        have huNZ : NeZero u := ⟨by omega⟩
        have hwNZ : NeZero w := ⟨by omega⟩
        have hu0 : u ≠ 0 := by omega
        have hw0 : w ≠ 0 := by omega
        have hu_lt : u < u * w := by nlinarith
        have hw_lt : w < u * w := by nlinarith
        have hcu : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u := fun p hp hd =>
          hncube p hp (dvd_mul_of_dvd_left hd w)
        have hcw : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ w := fun p hp hd =>
          hncube p hp (dvd_mul_of_dvd_right hd u)
        have hFLprim := factorLeft_isPrimitive huw χ hprim
        have hFRprim := factorRight_isPrimitive huw χ hprim
        have hFLne : factorLeft huw χ ≠ 1 := by
          intro h
          have hc : (factorLeft huw χ).conductor = 1 := by
            rw [h]; exact DirichletCharacter.conductor_one
          rw [DirichletCharacter.isPrimitive_def] at hFLprim
          omega
        have hFRne : factorRight huw χ ≠ 1 := by
          intro h
          have hc : (factorRight huw χ).conductor = 1 := by
            rw [h]; exact DirichletCharacter.conductor_one
          rw [DirichletCharacter.isPrimitive_def] at hFRprim
          omega
        have hIu := ih u hu_lt hcu (factorLeft huw χ) hFLprim hFLne v i huniq
        have hIw := ih w hw_lt hcw (factorRight huw χ) hFRprim hFRne v i huniq
        rw [CorrAllR.corrSumV_crt_split huw χ r v, norm_mul]
        have hrhs : (0 : ℝ) ≤ (2 * r : ℝ) ^ (u.primeFactors.card) * Real.sqrt (u : ℝ)
            * gcdWeightV u v i :=
          mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (gcdWeightV_nonneg u v i)
        refine (mul_le_mul hIu hIw (norm_nonneg _) hrhs).trans (le_of_eq ?_)
        have hprod : gcdWeightV (u * w) v i = gcdWeightV u v i * gcdWeightV w v i := by
          rw [gcdWeightV, gcdWeightV, gcdWeightV, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl (fun j _ => ?_)
          rw [gcd_mul_gcd_of_coprime huw]
          push_cast
          ring
        have hcard : (u * w).primeFactors.card = u.primeFactors.card + w.primeFactors.card :=
          card_primeFactors_mul_of_coprime hu0 hw0 huw
        have hsq : Real.sqrt (((u * w : ℕ)) : ℝ) = Real.sqrt (u : ℝ) * Real.sqrt (w : ℝ) := by
          rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg u)]
        rw [hprod, hcard, pow_add, hsq]
        ring

/-- **The requested lemma.**  For every `r ≥ 1` there is `Cg > 0` such that for every cube-free
modulus `q`, every primitive non-trivial `χ` mod `q`, and every `2r`-tuple of shifts `v` whose
`i`-th entry occurs only once,

`‖∑_{x : ZMod q} (∏_{l<r} χ (x + v_l)) · (∏_{l<r} conj (χ (x + v_{r+l})))‖`
`  ≤ Cg^{ω(q)} · √q · ∏_{j ≠ i} gcd (q, |v_i - v_j|)`. -/
theorem charCorrelation_allR_cubefree (r : ℕ) (hr : 1 ≤ r) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ {q : ℕ} [NeZero q], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ (v : Fin (r + r) → ℕ) (i : Fin (r + r)),
        (∀ j : Fin (r + r), j ≠ i → v j ≠ v i) →
        ‖(∑ x : ZMod q, (∏ l : Fin r, χ ((x : ZMod q) + ((v (Fin.castAdd r l) : ℕ) : ZMod q)))
            * (∏ l : Fin r, (starRingEnd ℂ) (χ ((x : ZMod q) + ((v (Fin.natAdd r l) : ℕ) : ZMod q)))))‖
          ≤ Cg ^ (q.primeFactors.card) * Real.sqrt (q : ℝ) *
              ∏ j ∈ Finset.univ.erase i,
                ((Nat.gcd q (Int.natAbs ((v i : ℤ) - (v j : ℤ)))) : ℝ) := by
  refine ⟨2 * r, ?_, ?_⟩
  · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  · intro q _ hcube χ hprim hχ v i huniq
    rw [sum_prod_chi_eq_corrSumV]
    have h := corrSumV_bound r hr q hcube χ hprim hχ v i huniq
    simpa only [gcdWeightV] using h

end

end Work.LinnikAreas
