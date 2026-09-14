import Mathlib
import Submission.Vdw.BoxFourier
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log

open Finset

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The number-theoretic weight of the §4 Fourier error term

The Fourier counting inequality `ncard_box_residue_index_le` bounds the number
of box elements whose reduction lies in `T` by

    `|T|·(2H+1)^m/p^m + B/p^m · Σ_{a ≠ 0} ∏_i freqWeight p H (a i)`,

where `B` is a bound for the Fourier coefficients of `T`.  This module
evaluates the **weight sum**: the weights factor over the coordinates, so

    `Σ_{a : (Z/p)^m} ∏_i freqWeight p H (a i) = (Σ_{b : Z/p} freqWeight p H b)^m`,

and the one-dimensional sum is the classical estimate

    `Σ_{b : Z/p} freqWeight p H b ≤ 5 (p + (2H+1)) (1 + log p)`

(split `b = 0`; the tail is controlled by `minrep b ∈ {b.val, p - b.val}` and
the harmonic sum `Σ_{d ≤ p} 1/d ≤ 1 + log p`).  Consequently the error term is
`B/p^m · (5(p + 2H+1)(1 + log p))^m` — the sharp-cutoff form of the paper's
Corollary `index2forms`, with the logarithmic factor that the smooth-cutoff
(Weil) version of §4 removes and which is absorbed by the `H^δ` slack in the
Case-I/Case-III assembly.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The `minrep` sum bound**: summing a nonnegative function of the small
representative `min b.val (p - b.val)` over the nonzero residues is at most
twice the sum over `{1, …, p-1}` (each value of `minrep` occurs at most twice). -/
theorem sum_minrep_le (p : ℕ) [Fact p.Prime] (g : ℕ → ℝ) (hg : ∀ d, 0 ≤ g d) :
    ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, g (min b.val (p - b.val))
      ≤ 2 * ∑ d ∈ (Finset.range p).erase 0, g d := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have h1 : ∀ b ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      g (min b.val (p - b.val)) ≤ g b.val + g (p - b.val) := by
    intro b _
    rcases min_choice (a := b.val) (b := p - b.val) with h | h <;> rw [h]
    · exact le_add_of_nonneg_right (hg _)
    · exact le_add_of_nonneg_left (hg _)
  have hinj1 : ∀ x ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      ∀ y ∈ (Finset.univ : Finset (ZMod p)).erase 0, x.val = y.val → x = y :=
    fun x _ y _ h => ZMod.val_injective p h
  have hsub1 : ((Finset.univ : Finset (ZMod p)).erase 0).image ZMod.val
      ⊆ (Finset.range p).erase 0 := by
    intro d hd
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (ZMod.val_lt b)⟩
    intro hv
    exact hb0 ((ZMod.val_eq_zero b).mp hv)
  have h2 : ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, g b.val
      ≤ ∑ d ∈ (Finset.range p).erase 0, g d := by
    rw [← Finset.sum_image hinj1]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun d _ _ => hg d)
  have hinj2 : ∀ x ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      ∀ y ∈ (Finset.univ : Finset (ZMod p)).erase 0, p - x.val = p - y.val → x = y :=
    fun x hx y hy h =>
      ZMod.val_injective p (by
        have hx1 : x.val < p := ZMod.val_lt x
        have hy1 : y.val < p := ZMod.val_lt y
        omega)
  have hsub2 : ((Finset.univ : Finset (ZMod p)).erase 0).image (fun b => p - b.val)
      ⊆ (Finset.range p).erase 0 := by
    intro d hd
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    have hv0 : b.val ≠ 0 := (ZMod.val_ne_zero b).mpr hb0
    have hvp : b.val < p := ZMod.val_lt b
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have h3 : ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, g (p - b.val)
      ≤ ∑ d ∈ (Finset.range p).erase 0, g d := by
    rw [← Finset.sum_image hinj2]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun d _ _ => hg d)
  calc ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, g (min b.val (p - b.val))
      ≤ ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, (g b.val + g (p - b.val)) :=
        Finset.sum_le_sum h1
    _ = ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, g b.val
        + ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, g (p - b.val) :=
        Finset.sum_add_distrib
    _ ≤ ∑ d ∈ (Finset.range p).erase 0, g d + ∑ d ∈ (Finset.range p).erase 0, g d :=
        add_le_add h2 h3
    _ = 2 * ∑ d ∈ (Finset.range p).erase 0, g d := by ring

/-- **The one-dimensional weight sum**: `Σ_{b : Z/p} freqWeight p H b ≤
5 (p + (2H+1)) (1 + log p)`. -/
theorem sum_freqWeight_le (p : ℕ) [Fact p.Prime] (H : ℕ) :
    ∑ b : ZMod p, freqWeight p H b
      ≤ 5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_of_lt (Fact.out : Nat.Prime p).one_lt))
  set L : ℝ := ((2 * H + 1 : ℕ) : ℝ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact_mod_cast (Nat.le_add_left 1 (2 * H))
  have hLnn : 0 ≤ L := by linarith
  have hsplit : ∑ b : ZMod p, freqWeight p H b
      = L + ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, freqWeight p H b := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
    rw [show freqWeight p H 0 = L from by rw [freqWeight, if_pos rfl, hL]]
    ring
  have htail : ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0, freqWeight p H b
      = ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          min L ((p : ℝ) / (2 * ((min b.val (p - b.val) : ℕ) : ℝ))) := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [freqWeight, if_neg (Finset.mem_erase.mp hb).1]
  have h1 : ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        min L ((p : ℝ) / (2 * ((min b.val (p - b.val) : ℕ) : ℝ)))
      ≤ 2 * ∑ d ∈ (Finset.range p).erase 0, min L ((p : ℝ) / (2 * (d : ℝ))) :=
    sum_minrep_le p (fun d => min L ((p : ℝ) / (2 * (d : ℝ))))
      (fun d => le_min hLnn (by positivity))
  have h2 : ∑ d ∈ (Finset.range p).erase 0, min L ((p : ℝ) / (2 * (d : ℝ)))
      ≤ p / 2 + L + (p / 2) * (1 + Real.log p) := by
    set T : ℝ := (p : ℝ) / (2 * L) with hT
    have hT0 : 0 < T := by rw [hT]; positivity
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range p).erase 0)
      (fun d : ℕ => (d : ℝ) ≤ T)]
    refine add_le_add ?_ ?_
    · calc ∑ d ∈ ((Finset.range p).erase 0).filter (fun d : ℕ => (d : ℝ) ≤ T),
            min L ((p : ℝ) / (2 * (d : ℝ)))
          ≤ ∑ d ∈ ((Finset.range p).erase 0).filter (fun d : ℕ => (d : ℝ) ≤ T), L :=
            Finset.sum_le_sum (fun d _ => min_le_left _ _)
        _ = L * ((((Finset.range p).erase 0).filter (fun d : ℕ => (d : ℝ) ≤ T)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ L * (T + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hLnn
            have hsub : (((Finset.range p).erase 0).filter (fun d : ℕ => (d : ℝ) ≤ T))
                ⊆ Finset.range (Nat.floor T + 1) := by
              intro d hd
              rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hd
              have hle := hd.2
              have hfl := Nat.lt_floor_add_one T
              rw [Finset.mem_range]
              have hcast : (d : ℝ) < (Nat.floor T : ℝ) + 1 := by linarith
              exact_mod_cast hcast
            calc ((((Finset.range p).erase 0).filter (fun d : ℕ => (d : ℝ) ≤ T)).card : ℝ)
                ≤ ((Finset.range (Nat.floor T + 1)).card : ℝ) := by
                  exact_mod_cast Finset.card_le_card hsub
              _ = (Nat.floor T : ℝ) + 1 := by rw [Finset.card_range]; push_cast; ring
              _ ≤ T + 1 := by
                  have := Nat.floor_le (le_of_lt hT0); linarith
        _ = p / 2 + L := by
            rw [hT]; field_simp
    · have hstep : ∀ d ∈ ((Finset.range p).erase 0).filter (fun d : ℕ => ¬ (d : ℝ) ≤ T),
          min L ((p : ℝ) / (2 * (d : ℝ))) ≤ (p / 2) * (1 / (d : ℝ)) := by
        intro d hd
        have hd1 : 1 ≤ d := by
          have := (Finset.mem_erase.mp (Finset.mem_filter.mp hd).1).1
          omega
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hle : (p : ℝ) / (2 * (d : ℝ)) = (p / 2) * (1 / (d : ℝ)) := by
          field_simp
        rw [← hle]
        exact min_le_right _ _
      calc ∑ d ∈ ((Finset.range p).erase 0).filter (fun d : ℕ => ¬ (d : ℝ) ≤ T),
            min L ((p : ℝ) / (2 * (d : ℝ)))
          ≤ ∑ d ∈ ((Finset.range p).erase 0).filter (fun d : ℕ => ¬ (d : ℝ) ≤ T),
              (p / 2) * (1 / (d : ℝ)) := Finset.sum_le_sum hstep
        _ = (p / 2) * ∑ d ∈ ((Finset.range p).erase 0).filter (fun d : ℕ => ¬ (d : ℝ) ≤ T),
              1 / (d : ℝ) := by rw [Finset.mul_sum]
        _ ≤ (p / 2) * ∑ d ∈ (Finset.range p).erase 0, 1 / (d : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun d _ _ => by positivity)
        _ ≤ (p / 2) * (1 + Real.log p) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hpe : (Finset.range p).erase 0 = Finset.Icc 1 (p - 1) := by
              ext d
              simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
              omega
            rw [hpe]
            refine le_trans (Commons.Analysis.ExpLog.harmonic_le_one_add_log (p - 1)
              (by omega)) ?_
            have h2' : (0 : ℝ) < (((p - 1 : ℕ)) : ℝ) := by
              exact_mod_cast (by omega : 0 < p - 1)
            have h3' : (((p - 1 : ℕ)) : ℝ) ≤ (p : ℝ) := by
              push_cast [Nat.cast_sub (le_of_lt (Fact.out : Nat.Prime p).one_lt)]
              linarith
            linarith [Real.log_le_log h2' h3']
  rw [hsplit, htail]
  calc L + ∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        min L ((p : ℝ) / (2 * ((min b.val (p - b.val) : ℕ) : ℝ)))
      ≤ L + 2 * ∑ d ∈ (Finset.range p).erase 0, min L ((p : ℝ) / (2 * (d : ℝ))) := by
        linarith [h1]
    _ ≤ L + 2 * (p / 2 + L + (p / 2) * (1 + Real.log p)) := by linarith [h2]
    _ ≤ 5 * ((p : ℝ) + L) * (1 + Real.log p) := by nlinarith [hpR, hlog0, hLnn]

lemma freqWeight_nonneg (p H : ℕ) (a : ZMod p) : 0 ≤ freqWeight p H a := by
  rw [freqWeight]
  split_ifs
  · exact_mod_cast Nat.zero_le _
  · exact le_min (by positivity) (by positivity)

/-- **The `m`-fold weight sum**: the weights factor over the coordinates, so
the total Fourier weight is at most the `m`-th power of the one-dimensional
bound. -/
theorem sum_freqWeight_prod_le (p : ℕ) [Fact p.Prime] (m H : ℕ) :
    ∑ a : Fin m → ZMod p, ∏ i, freqWeight p H (a i)
      ≤ (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ m := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hfac : ∏ i : Fin m, ∑ b : ZMod p, freqWeight p H b
      = ∑ a : Fin m → ZMod p, ∏ i, freqWeight p H (a i) := by
    rw [Finset.prod_univ_sum (t := fun _ : Fin m => (Finset.univ : Finset (ZMod p)))]
    rw [Fintype.piFinset_univ]
  rw [← hfac, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun b _ => freqWeight_nonneg p H b))
    (sum_freqWeight_le p H) m

/-- **The Fourier counting bound with the weight evaluated**: the number of
coefficient vectors in `(BddInt H)^m` whose reduction mod `p` lies in `T` is at
most the trivial density `|T|·(2H+1)^m/p^m` plus
`B/p^m · (5(p + 2H+1)(1 + log p))^m`, where `B` bounds the Fourier
coefficients of `T` (paper §4, Corollary `index2forms`). -/
theorem ncard_box_residue_le_fourier_bound (p : ℕ) [Fact p.Prime] (m H : ℕ)
    (T : Finset (Fin m → ZMod p)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ a : Fin m → ZMod p, a ≠ 0 →
      ‖∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)‖ ≤ B) :
    (Nat.card {z : BddVec m H // (fun i => ((z i : ℤ) : ZMod p)) ∈ T} : ℝ)
      ≤ (T.card : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ m / (p : ℝ) ^ m
        + B / (p : ℝ) ^ m *
            (5 * ((p : ℝ) + ((2 * H + 1 : ℕ) : ℝ)) * (1 + Real.log p)) ^ m := by
  refine le_trans (ncard_box_residue_index_le p m H T B hB0 hB) ?_
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun a _ _ => Finset.prod_nonneg (fun i _ => freqWeight_nonneg p H (a i)))) ?_
  exact sum_freqWeight_prod_le p m H

end

end Submission.Vdw
