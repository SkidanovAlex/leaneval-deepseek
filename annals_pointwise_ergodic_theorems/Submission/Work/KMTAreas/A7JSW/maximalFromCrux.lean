import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTAreas.A7Lpd.lacunaryMaxAux
import Submission.Work.KMTAreas.A7G.annuliUniformSigns
import Submission.Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin
import Submission.Port.Aesm

namespace Work.KMTAreas.A7JSW

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- `‖ ‖g x‖ₑ ‖_{ℓᵖ} = ‖g‖_{ℓᵖ}`. -/
lemma eLpNorm_enorm_eq_aux {g : ℤ → ℂ} {p : ENNReal} (h0 : p ≠ 0) (ht : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => ‖g x‖ₑ) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht]
  simp only [enorm_eq_self]

/-- A two-point chain: the jump between two values of a walk is bounded by the chain part. -/
lemma two_point_le_chainPart {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) {i j : ℕ} (hij : i ≤ j) :
    ‖a j - a i‖ₑ ≤ Work.KMTAreas.A7Hi.chainPart r a := by
  have hr0 : (r : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < (r : ℝ) := by
      have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    exact h1.ne'
  refine le_iSup_of_le 1 ?_
  refine le_iSup_of_le (fun t : ℕ => if t = 0 then i else j) ?_
  refine le_iSup_of_le ?_ ?_
  · refine monotone_nat_of_le_succ fun t => ?_
    by_cases ht : t = 0
    · subst ht
      show (if (0 : ℕ) = 0 then i else j) ≤ (if ((0 : ℕ) + 1) = 0 then i else j)
      rw [if_pos rfl, if_neg (by omega)]
      exact hij
    · have h2 : t + 1 ≠ 0 := by omega
      show (if t = 0 then i else j) ≤ (if t + 1 = 0 then i else j)
      rw [if_neg ht, if_neg h2]
  · have hval : (fun t : Fin 1 =>
        a ((fun t : ℕ => if t = 0 then i else j) (t + 1))
          - a ((fun t : ℕ => if t = 0 then i else j) t))
        = fun _ : Fin 1 => a j - a i := by
      funext t
      have ht : (t : ℕ) = 0 := by omega
      rw [ht]
      simp
    rw [hval]
    have h1' := Work.KMTAreas.A7.ofReal_norm_toLp r hr 1 (fun _ : Fin 1 => a j - a i)
    rw [Fin.sum_univ_one] at h1'
    rw [h1', one_div]
    exact le_of_eq (ENNReal.rpow_rpow_inv hr0 _).symm

/-- The two-point comparison without an order hypothesis on the two indices. -/
lemma two_point_le_chainPart' {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) (i j : ℕ) :
    ‖a j - a i‖ₑ ≤ Work.KMTAreas.A7Hi.chainPart r a := by
  rcases le_total i j with h | h
  · exact two_point_le_chainPart hr a h
  · have hneg : a j - a i = -(a i - a j) := by ring
    rw [hneg, enorm_neg]
    exact two_point_le_chainPart hr a h

/-- **The values-supremum is dominated by the value at the (arbitrary) level `N` together with the
chain part of the family.** -/
lemma supPart_le_norm_add_chainPart (ρ : ℝ) (l₁ m₀ N : ℕ) (f : ℤ → ℂ) (x : ℤ) (r : NNReal)
    (hr : 2 ≤ r) :
    Work.KMTAreas.A7Hi.supPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ N f x‖ₑ
        + Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
  refine iSup_le fun n => ?_
  change ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ ≤ _
  have h2 : ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
        - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ N f x‖ₑ
      ≤ Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) :=
    two_point_le_chainPart' hr (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) N n
  have h1 : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x
      = Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ N f x
        + (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ N f x) := by ring
  rw [h1]
  exact (enorm_add_le _ _).trans (add_le_add le_rfl h2)

end Work.KMTAreas.A7JSW

namespace Work.KMTAreas.A7JSW

open MeasureTheory
open scoped ENNReal NNReal BigOperators

end Work.KMTAreas.A7JSW
