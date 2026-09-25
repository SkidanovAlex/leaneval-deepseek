import Mathlib
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation

namespace Work.BourgainPlan.KPWW

open MeasureTheory
open scoped ENNReal BigOperators

/-- **The `ℓᵖ` norm as a supremum of pairings with finitely supported sequences.**  Let `p, q` be
Hölder conjugate (`Real.HolderConjugate p q`), let `h : ℤ → ℂ` and `c ≥ 0`.  If every pairing of `h`
with a finitely supported sequence `g` is bounded by `c` times the `ℓ^q`-norm of `g`, then `h ∈ ℓ^p`
with `‖h‖_p ≤ c`.

(The converse — Hölder — is the easy direction and is not part of the statement.  No measurability
of `h` is needed: `eLpNorm` is an `∫⁻` of `‖h n‖^p` against the counting measure, which is just a
`tsum`.)

Route.  Fix a finite window `W ⊆ ℤ` and put `S_W := ∑_{n ∈ W} ‖h n‖^p`.  Test the hypothesis with
the extremal sequence `g n := h n * ‖h n‖ ^ (p - 2)` on `W` (zero off `W`).  Since `g n * star (h n)
= ‖h n‖^p` and `‖g n‖ = ‖h n‖ ^ (p - 1)` and `q * (p - 1) = p` (a consequence of
`Real.HolderConjugate`, cf. `HolderConjugate.mul_eq_add`), the hypothesis gives `S_W ≤ c * S_W^(1/q)`,
hence `S_W^(1/p) ≤ c` (split on `S_W = 0`; the exponents satisfy `p - p/q = 1`).  Now let `W` grow:
by `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`, `MeasureTheory.lintegral_count` and
`ENNReal.tsum_eq_iSup_sum`, `eLpNorm h (ofReal p) count = (⨆_W ENNReal.ofReal S_W)^(1/p)`, and
`ENNReal.rpow` with a positive real exponent commutes with `iSup`.  Watch the `Real.rpow` edge cases
`0 ^ y` (`Real.zero_rpow`, `Real.rpow_zero`) and the conversions `ENNReal.ofReal_rpow_of_nonneg`.

This is a `ℤ`/counting-measure analogue of `Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound` (which
is the `volume`-on-`ℝ` version and requires measurability and boundedness of `h`; neither is
available here, and neither is needed on the counting measure). -/
theorem eLpNorm_le_of_pairing_bound {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {h : ℤ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (H : ∀ g : ℤ →₀ ℂ, ‖∑ n ∈ g.support, (g : ℤ → ℂ) n * star (h n)‖
        ≤ c * (∑ n ∈ g.support, ‖g n‖ ^ q) ^ (1 / q)) :
    MeasureTheory.eLpNorm h (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal c := by
  classical
  have hp1 : 1 < p := hpq.lt
  have hq1 : 1 < q := hpq.symm.lt
  have hp_pos : 0 < p := lt_trans zero_lt_one hp1
  have hq_pos : 0 < q := lt_trans zero_lt_one hq1
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hsum1 : 1 / p + 1 / q = 1 := by
    rw [one_div, one_div, hpq.inv_add_inv_eq_one]
  have hsub1 : (p - 1) * q = p := hpq.sub_one_mul_conj
  -- The finite-window estimate: for every finite `W`, `(∑_{n ∈ W} ‖h n‖^p)^(1/p) ≤ c`.
  have key : ∀ W : Finset ℤ, (∑ n ∈ W, ‖h n‖ ^ p) ^ (1 / p) ≤ c := by
    intro W
    set A : ℝ := ∑ n ∈ W, ‖h n‖ ^ p with hAdef
    have hAnn : 0 ≤ A := by
      rw [hAdef]
      exact Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) p)
    -- the extremal test sequence, supported in `W`
    set g : ℤ →₀ ℂ := Work.BourgainPlan.Maximal.extendZeroLM W
      (fun a : ↥W => h a * (((‖h a‖ ^ (p - 2) : ℝ)) : ℂ)) with hgdef
    have hgapp : ∀ n : ℤ, (g : ℤ → ℂ) n
        = if hn : n ∈ W then h n * (((‖h n‖ ^ (p - 2) : ℝ)) : ℂ) else 0 := by
      intro n
      have hh := Work.BourgainPlan.Maximal.extendZeroLM_apply W
        (fun a : ↥W => h a * (((‖h a‖ ^ (p - 2) : ℝ)) : ℂ)) n
      rw [hgdef]
      exact hh
    have hsuppW : g.support ⊆ W := by
      intro n hn
      by_contra hnn
      exact (Finsupp.mem_support_iff.mp hn) (by rw [hgapp n, dif_neg hnn])
    have hzero : ∀ n, n ∈ W → (g : ℤ → ℂ) n = 0 → h n = 0 := by
      intro n hnW hn0
      by_contra hhn
      have hpos : 0 < ‖h n‖ := norm_pos_iff.mpr hhn
      have hp2 : (0 : ℝ) < ‖h n‖ ^ (p - 2) := Real.rpow_pos_of_pos hpos _
      have hne : (((‖h n‖ ^ (p - 2) : ℝ)) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt hp2)
      rw [hgapp n, dif_pos hnW] at hn0
      exact mul_ne_zero hhn hne hn0
    -- the pairing against `star h` is the whole `ℓ^p` mass of `W`
    have hpair : ∑ n ∈ g.support, (g : ℤ → ℂ) n * star (h n) = ((A : ℝ) : ℂ) := by
      have hmc : ∀ n, h n * star (h n) = (((‖h n‖ : ℝ) ^ (2:ℝ) : ℝ) : ℂ) := by
        intro n
        rw [← starRingEnd_apply, Complex.mul_conj', ← Complex.ofReal_pow]
        exact congrArg (fun t : ℝ => (t : ℂ)) (Real.rpow_natCast (‖h n‖) 2).symm
      have hpt : ∀ n ∈ W, (g : ℤ → ℂ) n * star (h n) = ((‖h n‖ ^ p : ℝ) : ℂ) := by
        intro n hnW
        rw [hgapp n, dif_pos hnW]
        calc (h n * (((‖h n‖ ^ (p - 2) : ℝ)) : ℂ)) * star (h n)
            = (((‖h n‖ ^ (p - 2) : ℝ)) : ℂ) * (h n * star (h n)) := by ring
          _ = (((‖h n‖ ^ (p - 2) : ℝ)) : ℂ) * ((((‖h n‖ : ℝ) ^ (2:ℝ) : ℝ)) : ℂ) := by
                rw [hmc n]
          _ = (((‖h n‖ ^ (p - 2) : ℝ) * ((‖h n‖ : ℝ) ^ (2:ℝ) : ℝ) : ℝ) : ℂ) := by
                rw [Complex.ofReal_mul]
          _ = ((‖h n‖ ^ p : ℝ) : ℂ) := by
                congr 1
                rw [← Real.rpow_add' (norm_nonneg (h n)) (by linarith : (p - 2) + 2 ≠ 0)]
                congr 1
                ring
      have h1 : ∑ n ∈ g.support, (g : ℤ → ℂ) n * star (h n)
          = ∑ n ∈ W, (g : ℤ → ℂ) n * star (h n) :=
        Finset.sum_subset hsuppW (fun n _ hn => by
          rw [Finsupp.notMem_support_iff.mp hn, zero_mul])
      have h2 : ∑ n ∈ W, (g : ℤ → ℂ) n * star (h n)
          = ∑ n ∈ W, ((‖h n‖ ^ p : ℝ) : ℂ) :=
        Finset.sum_congr rfl hpt
      rw [h1, h2]
      exact (Complex.ofReal_sum W (fun n => ‖h n‖ ^ p)).symm
    have hH := H g
    rw [hpair] at hH
    have hAb : A ≤ c * (∑ n ∈ g.support, ‖g n‖ ^ q) ^ (1 / q) := by
      rwa [Complex.norm_real, Real.norm_of_nonneg hAnn] at hH
    -- the `ℓ^q` norm of `g` is again the `ℓ^p` mass of `W`
    have hgnorm : ∑ n ∈ g.support, ‖g n‖ ^ q = A := by
      have hpt : ∀ n ∈ g.support, ‖g n‖ ^ q = ‖h n‖ ^ p := by
        intro n hn
        have hnW := hsuppW hn
        have hng : ‖(g : ℤ → ℂ) n‖ = ‖h n‖ ^ (p - 1) := by
          rw [hgapp n, dif_pos hnW, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
          rw [show p - 1 = 1 + (p - 2) from by ring,
            Real.rpow_add' (norm_nonneg (h n)) (by linarith : (1:ℝ) + (p - 2) ≠ 0),
            Real.rpow_one]
        rw [hng, ← Real.rpow_mul (norm_nonneg (h n)) (p - 1) q, hsub1]
      have h1 : ∑ n ∈ g.support, ‖g n‖ ^ q = ∑ n ∈ g.support, ‖h n‖ ^ p :=
        Finset.sum_congr rfl hpt
      have h2 : ∑ n ∈ g.support, ‖h n‖ ^ p = ∑ n ∈ W, ‖h n‖ ^ p :=
        Finset.sum_subset hsuppW (fun n hnW hnns => by
          rw [hzero n hnW (Finsupp.notMem_support_iff.mp hnns), norm_zero,
            Real.zero_rpow hp_ne])
      rw [h1, h2]
    rw [hgnorm] at hAb
    rcases eq_or_lt_of_le hAnn with hA0 | hApos
    · rw [← hA0, Real.zero_rpow (by positivity : (1:ℝ) / p ≠ 0)]
      exact hc
    · have hkey : A = A ^ (1 / p) * A ^ (1 / q) := by
        rw [← Real.rpow_add' hAnn (by linarith [hsum1] : 1 / p + 1 / q ≠ 0), hsum1,
          Real.rpow_one]
      have hAb2 : A ^ (1 / p) * A ^ (1 / q) ≤ c * A ^ (1 / q) := by
        rw [← hkey]
        exact hAb
      exact le_of_mul_le_mul_right hAb2 (Real.rpow_pos_of_pos hApos (1 / q))
  -- assemble: `eLpNorm h (ofReal p) count` is the supremum of the finite-window contributions
  rw [Work.BourgainPlan.Maximal.eLpNorm_count_eq_tsum h hp_pos, ENNReal.tsum_eq_iSup_sum]
  have hmap : (⨆ s : Finset ℤ, ∑ n ∈ s, ENNReal.ofReal (‖h n‖ ^ p)) ^ (1 / p)
      = ⨆ s : Finset ℤ, (∑ n ∈ s, ENNReal.ofReal (‖h n‖ ^ p)) ^ (1 / p) :=
    OrderIso.map_iSup (ENNReal.orderIsoRpow (1 / p) (by positivity : (0:ℝ) < 1 / p))
      (fun s : Finset ℤ => ∑ n ∈ s, ENNReal.ofReal (‖h n‖ ^ p))
  rw [hmap]
  refine iSup_le fun s => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) p)]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg (fun n _ => Real.rpow_nonneg (norm_nonneg _) p))
    (by positivity : (0:ℝ) ≤ 1 / p)]
  exact ENNReal.ofReal_le_ofReal (key s)

end Work.BourgainPlan.KPWW
