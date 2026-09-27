import Mathlib
import Submission.Work.EKLComp.EntPowDefs
import Submission.Work.EKLComp.joinSets_iterate_le
import Submission.Work.EKLComp.tendsto_hPart
import Submission.Work.EKLComp.Hfam_joinSets_joinPart
import Submission.Work.EKLComp.ent_id

/-!
# `ent μ (T^[n]) = n * ent μ T` for a measure-preserving `T`

The Kolmogorov–Sinai entropy (`Work.EKLContract.ent`) of the `n`-th iterate of a
measure-preserving transformation is `n` times the entropy of the transformation
(component `(E6)` of the frozen contract `Work.EKLContract.P_EntropyBasics`).

The proof goes through the partition entropies `hPart`:

* `hPart_iterate_le` : `hPart μ (T^[m+1]) P ≤ (m+1) * hPart μ T P`.
  The join `⋁_{k<N} T^{-k(m+1)} P` is a sub-join of `⋁_{j<N(m+1)} T^{-j} P`, so
  `Hfam μ (joinSets (T^[m+1]) P M) ≤ Hfam μ (joinSets T P (M*(m+1)))`
  (`joinSets_iterate_le`), and the inequality follows by taking the `atTop` limit of
  both sides along `N ↦ Hfam μ (joinSets T P N)/N → hPart μ T P` (`tendsto_hPart`,
  Fekete).

* `le_hPart_iterate` : `(m+1) * hPart μ T P ≤ hPart μ (T^[m+1]) (joinPart hT P (m+1))`,
  where `joinPart hT P (m+1)` is the partition `⋁_{j<m+1} T^{-j}P` of `EntPowDefs.lean`.
  Here the two sides are *equal* at every finite level
  (`Hfam_joinSets_joinPart`), which gives the inequality termwise in the defining
  infimum of `hPart μ (T^[m+1]) ·`.

Assembling, `ent μ (T^[m+1]) = ⨆_Q ofReal (hPart μ (T^[m+1]) Q)` and
`ent μ T = ⨆_P ofReal (hPart μ T P)` differ by the factor `m+1` inside the supremum;
`ENNReal.mul_iSup` moves the factor out.  The case `n = 0` is `ent μ id = 0`
(`ent_id`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X]

/-! ## The two estimates on `hPart` -/

/-- **Upper bound.** `h_μ(T^{m+1}, P) ≤ (m+1) h_μ(T,P)`: the join along `T^[m+1]` is a
sub-join of the join along `T`, and the latter averages tend to `h_μ(T,P)` (Fekete). -/
theorem hPart_iterate_le (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (m : ℕ) :
    hPart μ (T^[m+1]) P ≤ ((m+1 : ℕ) : ℝ) * hPart μ T P := by
  have hseq : Tendsto (fun N : ℕ => (N+1)*(m+1)) atTop atTop := by
    refine tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => ?_⟩)
    calc b ≤ a := ha
      _ ≤ a + 1 := Nat.le_succ a
      _ ≤ (a+1)*(m+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos m)
  have hlim := (tendsto_hPart μ hmp P).comp hseq
  have hlim2 := hlim.const_mul ((m+1 : ℕ) : ℝ)
  refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim2 (fun N => ?_)
  have h1 := Core.hPart_le_avg μ (T^[m+1]) P N
  have h2 : Hfam μ (joinSets (T^[m+1]) P (N+1)) / ((N:ℝ)+1)
      ≤ Hfam μ (joinSets T P ((N+1)*(m+1))) / ((N:ℝ)+1) :=
    div_le_div_of_nonneg_right (joinSets_iterate_le μ hmp.measurable P m (N+1)) (by positivity)
  have h3 : Hfam μ (joinSets T P ((N+1)*(m+1))) / ((N:ℝ)+1)
      = ((m+1 : ℕ) : ℝ) * (Hfam μ (joinSets T P ((N+1)*(m+1))) / (((N+1)*(m+1) : ℕ) : ℝ)) := by
    have hc : (((N+1)*(m+1) : ℕ) : ℝ) = ((N:ℝ)+1) * (((m+1 : ℕ)) : ℝ) := by push_cast; ring
    rw [hc]
    have hN1 : ((N:ℝ)+1) ≠ 0 := by positivity
    have hm1 : (((m+1 : ℕ)) : ℝ) ≠ 0 := by positivity
    field_simp
  calc hPart μ (T^[m+1]) P
      ≤ Hfam μ (joinSets (T^[m+1]) P (N+1)) / ((N:ℝ)+1) := h1
    _ ≤ Hfam μ (joinSets T P ((N+1)*(m+1))) / ((N:ℝ)+1) := h2
    _ = ((m+1 : ℕ) : ℝ) * (Hfam μ (joinSets T P ((N+1)*(m+1))) / (((N+1)*(m+1) : ℕ) : ℝ)) := h3

/-- **Lower bound.** `(m+1) h_μ(T,P) ≤ h_μ(T^{m+1}, ⋁_{j<m+1} T^{-j}P)`: the joins of the
partition `⋁_{j<m+1} T^{-j}P` along `T^{m+1}` are exactly the joins of `P` along `T`, so
the defining infimum of the left-hand side dominates `(m+1) h_μ(T,P)`. -/
theorem le_hPart_iterate (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X} (hT : Measurable T)
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (m : ℕ) :
    ((m+1 : ℕ) : ℝ) * hPart μ T P ≤ hPart μ (T^[m+1]) (joinPart hT P (m+1)) := by
  refine le_ciInf (fun N => ?_)
  have hsub : Subadditive (fun M => Hfam μ (joinSets T P M)) := Core.Hfam_joinSets_add_le μ hmp P
  have hbdd : BddBelow (Set.range fun M : ℕ => Hfam μ (joinSets T P M) / (M : ℝ)) :=
    ⟨0, by rintro y ⟨M, rfl⟩; exact div_nonneg (Core.Hfam_nonneg μ _) (Nat.cast_nonneg M)⟩
  have h1 : hPart μ T P ≤ Hfam μ (joinSets T P ((N+1)*(m+1))) / (((N+1)*(m+1) : ℕ) : ℝ) := by
    rw [Core.hPart_eq_lim μ hmp P hsub]
    exact hsub.lim_le_div hbdd (Nat.mul_ne_zero (Nat.succ_ne_zero N) (Nat.succ_ne_zero m))
  have h2 : ((m+1 : ℕ) : ℝ) * (Hfam μ (joinSets T P ((N+1)*(m+1))) / (((N+1)*(m+1) : ℕ) : ℝ))
      = Hfam μ (joinSets (T^[m+1]) (joinPart hT P (m+1)) (N+1)) / ((N:ℝ)+1) := by
    rw [Hfam_joinSets_joinPart μ hT P m (N+1)]
    have hc : (((N+1)*(m+1) : ℕ) : ℝ) = ((N:ℝ)+1) * (((m+1 : ℕ)) : ℝ) := by push_cast; ring
    rw [hc]
    have hN1 : ((N:ℝ)+1) ≠ 0 := by positivity
    have hm1 : (((m+1 : ℕ)) : ℝ) ≠ 0 := by positivity
    field_simp
  exact le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) (le_of_eq h2)

/-! ## The main theorem -/

theorem ent_pow {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) (n : ℕ) :
    Work.EKLContract.ent μ (T^[n]) = n * Work.EKLContract.ent μ T := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Function.iterate_zero, ent_id μ, Nat.cast_zero, zero_mul]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
    refine le_antisymm ?_ ?_
    · calc ent μ (T^[m+1]) = ⨆ Q : FinPart X, ENNReal.ofReal (hPart μ (T^[m+1]) Q) := rfl
        _ ≤ ⨆ Q : FinPart X, ((m+1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (hPart μ T Q) := by
            refine iSup_le (fun Q => ?_)
            calc ENNReal.ofReal (hPart μ (T^[m+1]) Q)
                ≤ ENNReal.ofReal (((m+1 : ℕ) : ℝ) * hPart μ T Q) :=
                  ENNReal.ofReal_le_ofReal (hPart_iterate_le μ hmp Q m)
              _ = ((m+1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (hPart μ T Q) := by
                  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
              _ ≤ ⨆ P : FinPart X, ((m+1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (hPart μ T P) :=
                  le_iSup (fun P : FinPart X => ((m+1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (hPart μ T P)) Q
        _ = ((m+1 : ℕ) : ℝ≥0∞) * ⨆ P : FinPart X, ENNReal.ofReal (hPart μ T P) :=
            (ENNReal.mul_iSup _ _).symm
        _ = ((m+1 : ℕ) : ℝ≥0∞) * ent μ T := rfl
    · calc ((m+1 : ℕ) : ℝ≥0∞) * ent μ T
          = ((m+1 : ℕ) : ℝ≥0∞) * ⨆ P : FinPart X, ENNReal.ofReal (hPart μ T P) := rfl
        _ = ⨆ P : FinPart X, ((m+1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (hPart μ T P) :=
            ENNReal.mul_iSup _ _
        _ ≤ ⨆ Q : FinPart X, ENNReal.ofReal (hPart μ (T^[m+1]) Q) := by
            refine iSup_le (fun P => ?_)
            calc ((m+1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (hPart μ T P)
                = ENNReal.ofReal (((m+1 : ℕ) : ℝ) * hPart μ T P) := by
                  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
              _ ≤ ENNReal.ofReal (hPart μ (T^[m+1]) (joinPart hT P (m+1))) :=
                  ENNReal.ofReal_le_ofReal (le_hPart_iterate μ hT hmp P m)
              _ ≤ ⨆ Q : FinPart X, ENNReal.ofReal (hPart μ (T^[m+1]) Q) :=
                  le_iSup (fun Q : FinPart X => ENNReal.ofReal (hPart μ (T^[m+1]) Q)) (joinPart hT P (m+1))

end Work.EKLComp
