import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_pos
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent
import Submission.Commons.Lattice.SuccessiveMinima.Basic

open MeasureTheory Module

namespace Commons.Lattice.Minkowski

open Commons.Lattice.SuccessiveMinima

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Elementary product/power bound: for a nonnegative sequence `lam` with `lam i ≥ 1` for
`i ≤ j` and `lam i ≥ lam j` for `i ≥ j`, the `(d + 1 - j)`-th power of `lam j` is bounded by
the product `lam 1 * lam 2 * ... * lam d`. -/
private lemma pow_le_prod_successive {lam : ℕ → ℝ} {d j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d)
    (h1 : ∀ i, 1 ≤ i → i ≤ j → 1 ≤ lam i)
    (hmono : ∀ i, j ≤ i → i ≤ d → lam j ≤ lam i) :
    lam j ^ (d + 1 - j) ≤ ∏ i : Fin d, lam (i.val + 1) := by
  have hjn : 0 ≤ lam j := by linarith [h1 j hj le_rfl]
  have hmain : lam j ^ (d + 1 - j) ≤
      (∏ x ∈ Finset.range (j - 1), lam (x + 1)) *
        ∏ x ∈ Finset.range (d + 1 - j), lam ((j - 1) + x + 1) := by
    have hleft : 1 ≤ ∏ x ∈ Finset.range (j - 1), lam (x + 1) := by
      apply Finset.one_le_prod
      intro x hx
      rw [Finset.mem_range] at hx
      exact h1 (x + 1) (by omega) (by omega)
    have hright : lam j ^ (d + 1 - j) ≤
        ∏ x ∈ Finset.range (d + 1 - j), lam ((j - 1) + x + 1) := by
      have hpt : ∀ x ∈ Finset.range (d + 1 - j), lam j ≤ lam ((j - 1) + x + 1) := by
        intro x hx
        rw [Finset.mem_range] at hx
        have hx' : (j - 1) + x + 1 = j + x := by omega
        rw [hx']
        exact hmono (j + x) (by omega) (by omega)
      calc lam j ^ (d + 1 - j)
            = ∏ _x ∈ Finset.range (d + 1 - j), lam j := by
              rw [Finset.prod_const, Finset.card_range]
        _ ≤ ∏ x ∈ Finset.range (d + 1 - j), lam ((j - 1) + x + 1) :=
              Finset.prod_le_prod (fun x _ => hjn) hpt
    have hL0 : 0 ≤ ∏ x ∈ Finset.range (j - 1), lam (x + 1) := le_trans zero_le_one hleft
    calc lam j ^ (d + 1 - j) = 1 * lam j ^ (d + 1 - j) := (one_mul _).symm
      _ ≤ (∏ x ∈ Finset.range (j - 1), lam (x + 1)) *
            ∏ x ∈ Finset.range (d + 1 - j), lam ((j - 1) + x + 1) :=
          mul_le_mul hleft hright (pow_nonneg hjn _) hL0
  calc lam j ^ (d + 1 - j)
        ≤ (∏ x ∈ Finset.range (j - 1), lam (x + 1)) *
            ∏ x ∈ Finset.range (d + 1 - j), lam ((j - 1) + x + 1) := hmain
    _ = ∏ x ∈ Finset.range ((j - 1) + (d + 1 - j)), lam (x + 1) :=
          (Finset.prod_range_add (fun x => lam (x + 1)) (j - 1) (d + 1 - j)).symm
    _ = ∏ x ∈ Finset.range d, lam (x + 1) := by
          rw [show (j - 1) + (d + 1 - j) = d by omega]
    _ = ∏ i : Fin d, lam (i.val + 1) :=
          (Fin.prod_univ_eq_prod_range (fun x => lam (x + 1)) d).symm

/-- Elementary root extraction: from `x ^ n ≤ R` (`n > 0`, `x ≥ 0`) deduce
`x ≤ R ^ (1 / n)`. -/
private lemma le_rpow_inv_of_pow_le {x R : ℝ} {n : ℕ} (hn : 0 < n) (hx : 0 ≤ x)
    (h : x ^ n ≤ R) : x ≤ R ^ ((1 : ℝ) / (n : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hx1 : x = (x ^ n) ^ ((1 : ℝ) / (n : ℝ)) := by
    rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx (n : ℝ) ((1 : ℝ) / (n : ℝ))]
    rw [mul_one_div, div_self hnR, Real.rpow_one]
  have h2 : (x ^ n) ^ ((1 : ℝ) / (n : ℝ)) ≤ R ^ ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_le_rpow (pow_nonneg hx n) h (by positivity)
  exact hx1.trans_le h2

/-- **Short independent lattice vectors from a covolume bound.** If a full `ℤ`-lattice `L` of `ℤ`-rank `d` in a finite-dimensional real inner product space has `covolume ≤ V` and shortest nonzero vector of norm `≥ 1`, then for every `j` with `1 ≤ j ≤ d` there are `j` `ℝ`-independent vectors of `L` of norm at most `(4^d · V / vol(unit ball))^(1/(d+1-j)) + 1`. This combines Minkowski's second theorem (`Commons.Lattice.Minkowski.minkowski_second_upper`: `∏ᵢ λᵢ · vol(unit ball) ≤ 4^d · covolume`), the monotonicity of successive minima (so `λ_j^(d+1-j) ≤ ∏ᵢ λᵢ`, using `λ_i ≥ λ_j` for `i ≥ j` and `λ₁ ≥ 1`), and the realisation of successive minima by independent vectors (`exists_linearIndependent_of_successiveMinimum`, with `ε = 1`). -/
theorem exists_short_independent {d : ℕ} (hd : 0 < d) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfin : Module.finrank ℤ L = d) {V : ℝ} (hV : ZLattice.covolume L ≤ V)
    (hV0 : 0 ≤ V) (hmin : 1 ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum L 1)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d) :
    ∃ v : Fin j → L, LinearIndependent ℝ (fun i => (v i : E)) ∧
      ∀ i : Fin j, ‖(v i : E)‖ ≤
        ((4 : ℝ) ^ d * V / ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : E) 1))) ^
          ((1 : ℝ) / ((d + 1 - j : ℕ) : ℝ)) + 1 := by
  classical
  set A : ℝ := ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : E) 1)) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    exact Commons.Analysis.InnerProductSpace.unitBall_volume_pos
  have hA0 : 0 ≤ A := le_of_lt hApos
  have hjen : 0 < d + 1 - j := by omega
  have hlam_nonneg : 0 ≤ successiveMinimum L j :=
    successiveMinimum_nonneg L j (by rw [hfin]; exact hjd)
  have hpow : successiveMinimum L j ^ (d + 1 - j) ≤
      ∏ i : Fin d, successiveMinimum L (i.val + 1) := by
    apply pow_le_prod_successive hj hjd
    · intro i hi hij
      have hm := successiveMinimum_mono (L := L) (i := 1) (j := i) hi (by rw [hfin]; omega)
      linarith
    · intro i hji hid
      exact successiveMinimum_mono (L := L) (i := j) (j := i) hji (by rw [hfin]; exact hid)
  have hpow4 : (2 : ℝ) ^ (2 * d) = (4 : ℝ) ^ d := by
    rw [pow_mul]; norm_num
  have hMS := minkowski_second_upper hd L hfin
  have hMS' : (∏ i : Fin d, successiveMinimum L (i.val + 1)) * A ≤ (4 : ℝ) ^ d * V := by
    rw [hAdef]
    calc (∏ i : Fin d, successiveMinimum L (i.val + 1)) *
          ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : E) 1))
        ≤ (2 : ℝ) ^ (2 * d) * ZLattice.covolume L := hMS
      _ = (4 : ℝ) ^ d * ZLattice.covolume L := by rw [hpow4]
      _ ≤ (4 : ℝ) ^ d * V := mul_le_mul_of_nonneg_left hV (by positivity)
  have hmul : successiveMinimum L j ^ (d + 1 - j) * A ≤ (4 : ℝ) ^ d * V :=
    le_trans (mul_le_mul_of_nonneg_right hpow hA0) hMS'
  have hdiv : successiveMinimum L j ^ (d + 1 - j) ≤ (4 : ℝ) ^ d * V / A :=
    (le_div_iff₀ hApos).mpr hmul
  have hbound : successiveMinimum L j ≤
      ((4 : ℝ) ^ d * V / A) ^ ((1 : ℝ) / ((d + 1 - j : ℕ) : ℝ)) :=
    le_rpow_inv_of_pow_le hjen hlam_nonneg hdiv
  obtain ⟨v, hvLI, hvbd⟩ :=
    exists_linearIndependent_of_successiveMinimum (L := L) d hfin (by norm_num : (0 : ℝ) < 1)
  refine ⟨fun i => v (Fin.castLE hjd i), ?_, ?_⟩
  · exact hvLI.comp (Fin.castLE hjd) (Fin.castLE_injective hjd)
  · intro i
    have hbi := hvbd (Fin.castLE hjd i)
    have hval : (Fin.castLE hjd i).val = i.val := by simp [Fin.val_castLE]
    rw [hval] at hbi
    have hmono := successiveMinimum_mono (L := L) (i := i.val + 1) (j := j)
      (by omega) (by rw [hfin]; exact hjd)
    have hstep : ‖(v (Fin.castLE hjd i) : E)‖ ≤ successiveMinimum L j + 1 := by linarith
    calc ‖(v (Fin.castLE hjd i) : E)‖ ≤ successiveMinimum L j + 1 := hstep
      _ ≤ ((4 : ℝ) ^ d * V / A) ^ ((1 : ℝ) / ((d + 1 - j : ℕ) : ℝ)) + 1 := by linarith

end Commons.Lattice.Minkowski
