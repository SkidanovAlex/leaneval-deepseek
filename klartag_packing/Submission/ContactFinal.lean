import Mathlib
import Submission.ContactSharp
import Submission.Contact
import Submission.GenProc
import Submission.Weight

/-!
# The contact bound `M ≤ 8 · ∑ w` for the exploration process

`Submission.ContactSharp.perTime_contact` gives, for every candidate `y` and every time
`k ∈ [1,K]`,

    P(y is violated at time k) ≤ 8 · tailG ((a₀ - 1/‖y‖²)/(ε√k)) .

Summing over the candidates `y = BoxL i` and over the times gives

    M := ∑_{k<K} E|violSet A_k| ≤ 8 · ∑_i ∑_{k ∈ Icc 1 K} tailG ((a₀ - 1/‖y_i‖²)/(ε√k)) ,

which is exactly `8 · ∑_i w(R y_i)` for the lattice weight `w` of `Submission/Weight.lean`.
-/

namespace Submission.ContactFinal

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.GenProc
open Submission.Contact
open Submission.ContactSharp
open Submission.OpNorm
open Submission.Weight

noncomputable section

variable {d m : ℕ}

/-- The scalar weight attached to a candidate `y`: the sum over the times `k ∈ [1,K]` of the
per-time contact tail. -/
def Wt (K : ℕ) (a₀ ε : ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K, tailG ((a₀ - 1 / ‖y‖ ^ 2) / (ε * Real.sqrt (k : ℝ)))

/-- Splitting off the identity part of the quadratic form. -/
lemma quadFormV_sub_state (a₀ : ℝ) (A : MatV d) (y : Vec d) :
    quadFormV A y = quadFormV (A - a₀ • oneV d) y + a₀ * ‖y‖ ^ 2 := by
  rw [← quadFormV_oneV a₀ y, ← quadFormV_add (A - a₀ • oneV d) (a₀ • oneV d) y,
    sub_add_cancel]

/-- The violation condition in centred form. -/
lemma quadFormV_le_one_iff (a₀ : ℝ) (A : MatV d) (y : Vec d) :
    quadFormV A y ≤ 1 ↔ quadFormV (A - a₀ • oneV d) y ≤ 1 - a₀ * ‖y‖ ^ 2 := by
  rw [quadFormV_sub_state (d := d) a₀ A y]
  constructor <;> intro h <;> linarith

/-- The cardinality of the violated set as a sum of indicators. -/
lemma card_violSet_eq_sum (R : ℝ) (BoxL : Fin m → Vec d) (hinj : Function.Injective BoxL)
    (hBoxR : ∀ i, ‖BoxL i‖ ≤ R) (a₀ : ℝ) (A : MatV d) :
    ((violSet R BoxL A).card : ℝ)
      = ∑ i : Fin m, (if quadFormV (A - a₀ • oneV d) (BoxL i) ≤ 1 - a₀ * ‖BoxL i‖ ^ 2
          then (1 : ℝ) else 0) := by
  classical
  have hL : (violSet R BoxL A).card
      = (Finset.univ.filter (fun i : Fin m =>
          ‖BoxL i‖ ≤ R ∧ quadFormV A (BoxL i) ≤ 1)).card := by
    rw [violSet]
    exact Finset.card_image_of_injective _ hinj
  have hfilter : (Finset.univ.filter (fun i : Fin m =>
        ‖BoxL i‖ ≤ R ∧ quadFormV A (BoxL i) ≤ 1))
      = (Finset.univ.filter (fun i : Fin m =>
        quadFormV (A - a₀ • oneV d) (BoxL i) ≤ 1 - a₀ * ‖BoxL i‖ ^ 2)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => (quadFormV_le_one_iff (d := d) a₀ A (BoxL i)).mp h.2,
      fun h => ⟨hBoxR i, (quadFormV_le_one_iff (d := d) a₀ A (BoxL i)).mpr h⟩⟩
  rw [hL, hfilter, ← Finset.sum_boole (fun i : Fin m =>
      quadFormV (A - a₀ • oneV d) (BoxL i) ≤ 1 - a₀ * ‖BoxL i‖ ^ 2)]

/-- At time `0` the state is `a₀·Id`, so nothing is violated. -/
lemma violSet_zero_card (R : ℝ) (BoxL : Fin m → Vec d) (a₀ ε : ℝ) (K : ℕ)
    (ω : Fin K → MatV d × MatV d) (hmin : ∀ i, 1 < a₀ * ‖BoxL i‖ ^ 2) :
    ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω 0)).card : ℝ) = 0 := by
  classical
  have h0 : proc (projL R BoxL) a₀ ε K ω 0 = a₀ • oneV d := rfl
  have hempty : (Finset.univ.filter (fun i : Fin m =>
      ‖BoxL i‖ ≤ R ∧ quadFormV (a₀ • oneV d) (BoxL i) ≤ 1)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    rintro i - ⟨-, hle⟩
    rw [quadFormV_oneV] at hle
    linarith [hmin i]
  rw [h0, violSet, hempty, Finset.image_empty, Finset.card_empty, Nat.cast_zero]

/-- Transfer of a filtered sum over `Fin K` (excluding `0`) to `Icc 1 K`. -/
lemma sum_fin_ne_zero_le_Icc {G : ℕ → ℝ} (hG : ∀ k, 0 ≤ G k) (K : ℕ) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) ≠ 0), G (k : ℕ))
      ≤ ∑ k ∈ Finset.Icc 1 K, G k := by
  classical
  have h1 : (∑ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) ≠ 0), G (k : ℕ))
      = ∑ m ∈ Finset.range K, (if m ≠ 0 then G m else 0) := by
    rw [Finset.sum_filter, Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [dif_pos (Finset.mem_range.mp hm)]
  rw [h1, ← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hG i)
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm.2, by omega⟩

/-- **The contact bound.**  The expected total number of contacts is at most `8` times the sum
of the per-candidate weights. -/
theorem contact_bound (R : ℝ) (BoxL : Fin m → Vec d) {a₀ ε : ℝ} {K : ℕ}
    (hinj : Function.Injective BoxL) (hε : 0 < ε) (ha₀ : 1 < a₀)
    (hmin : ∀ i, 1 < a₀ * ‖BoxL i‖ ^ 2) (hBoxR : ∀ i, ‖BoxL i‖ ≤ R)
    (M : ℝ) (hM : ∑ i : Fin m, Wt (d := d) K a₀ ε (BoxL i) ≤ M) :
    ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K)
      ≤ 8 * M := by
  classical
  have hWt_nonneg : 0 ≤ ∑ i : Fin m, Wt (d := d) K a₀ ε (BoxL i) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => tailG_nonneg _
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    linarith
  set P : ℕ → Fin m → MatV d → Prop := fun t i A =>
    quadFormV (A - a₀ • oneV d) (BoxL i) ≤ 1 - a₀ * ‖BoxL i‖ ^ 2 with hP
  -- the cardinality of the violated set is a sum of indicators
  have hpt : ∀ (k : Fin K) (ω : Fin K → MatV d × MatV d),
      ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ)
        = ∑ i : Fin m,
            (if P (k : ℕ) i (proc (projL R BoxL) a₀ ε K ω k) then (1 : ℝ) else 0) := by
    intro k ω
    rw [card_violSet_eq_sum R BoxL hinj hBoxR a₀]
  -- measurability and the identification of the integral with a contact probability
  have hset : ∀ (k : Fin K) (i : Fin m),
      MeasurableSet {ω : Fin K → MatV d × MatV d | P (k : ℕ) i
        (proc (projL R BoxL) a₀ ε K ω k)} := by
    intro k i
    refine measurableSet_le ?_ measurable_const
    exact (measurable_quadFormV_left (BoxL i)).comp
      ((measurable_proc (pl := projL R BoxL) (a₀ := a₀) (ε := ε) (K := K)
        (measurable_projL R BoxL) (k : ℕ)).sub measurable_const)
  have hfun : ∀ (k : Fin K) (i : Fin m),
      (fun ω : Fin K → MatV d × MatV d =>
          (if P (k : ℕ) i (proc (projL R BoxL) a₀ ε K ω k) then (1 : ℝ) else 0))
        = ({ω : Fin K → MatV d × MatV d | P (k : ℕ) i
            (proc (projL R BoxL) a₀ ε K ω k)}.indicator fun _ => (1 : ℝ)) := by
    intro k i
    funext ω
    rw [Set.indicator_apply]
    by_cases h : P (k : ℕ) i (proc (projL R BoxL) a₀ ε K ω k) <;> simp [h]
  have hint : ∀ (k : Fin K) (i : Fin m),
      Integrable (fun ω : Fin K → MatV d × MatV d =>
          (if P (k : ℕ) i (proc (projL R BoxL) a₀ ε K ω k) then (1 : ℝ) else 0))
        (sampleLaw d K) := by
    intro k i
    rw [hfun k i]
    exact (MeasureTheory.integrable_const (1 : ℝ)).indicator (hset k i)
  -- per-time, per-candidate bound
  have hterm : ∀ (k : Fin K), (k : ℕ) ≠ 0 → ∀ i : Fin m,
      ∫ ω : Fin K → MatV d × MatV d,
          (if P (k : ℕ) i (proc (projL R BoxL) a₀ ε K ω k) then (1 : ℝ) else 0)
            ∂(sampleLaw d K)
        ≤ 8 * tailG ((a₀ - 1 / ‖BoxL i‖ ^ 2) / (ε * Real.sqrt (k : ℝ))) := by
    intro k _ i
    have h1 : ∫ ω : Fin K → MatV d × MatV d,
          (if P (k : ℕ) i (proc (projL R BoxL) a₀ ε K ω k) then (1 : ℝ) else 0)
            ∂(sampleLaw d K)
        = (sampleLaw d K).real {ω : Fin K → MatV d × MatV d |
            P (k : ℕ) i (proc (projL R BoxL) a₀ ε K ω k)} :=
      MeasureTheory.integral_indicator_one (hset k i)
    have hy : BoxL i ≠ 0 := by
      intro h
      have hlt := hmin i
      rw [h] at hlt
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        mul_eq_zero, one_ne_zero] at hlt
      linarith
    exact le_trans (le_of_eq h1)
      (perTime_contact R BoxL a₀ ε (Nat.le_of_lt k.isLt) hy hε (hmin i))
  -- the time-`0` integral vanishes
  have hzero : ∫ ω : Fin K → MatV d × MatV d,
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω ((⟨0, hK⟩ : Fin K) : ℕ))).card : ℝ)
          ∂(sampleLaw d K) = 0 := by
    rw [show (fun ω : Fin K → MatV d × MatV d =>
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω ((⟨0, hK⟩ : Fin K) : ℕ))).card : ℝ))
        = fun _ => (0 : ℝ) from funext fun ω => violSet_zero_card R BoxL a₀ ε K ω hmin]
    rw [MeasureTheory.integral_const]
    simp
  -- drop the `k = 0` term
  have hsplit : ∑ k : Fin K, ∫ ω : Fin K → MatV d × MatV d,
        ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K)
      = ∑ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) ≠ 0),
          ∫ ω : Fin K → MatV d × MatV d,
            ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k _ hk
    have hk' : (k : ℕ) = 0 := by
      by_contra h
      exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
    have hk0 : k = (⟨0, hK⟩ : Fin K) := Fin.ext (by simpa using hk')
    rw [hk0]
    exact hzero
  rw [hsplit]
  have hstep : ∀ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) ≠ 0),
      ∫ ω : Fin K → MatV d × MatV d,
          ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K)
        ≤ 8 * ∑ i : Fin m, tailG ((a₀ - 1 / ‖BoxL i‖ ^ 2) / (ε * Real.sqrt (k : ℝ))) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have h1 : ∫ ω : Fin K → MatV d × MatV d,
          ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K)
        = ∑ i : Fin m, ∫ ω : Fin K → MatV d × MatV d,
            (if P (k : ℕ) i (proc (projL R BoxL) a₀ ε K ω k) then (1 : ℝ) else 0)
              ∂(sampleLaw d K) := by
      rw [funext (hpt k), MeasureTheory.integral_finsetSum]
      intro i _; exact hint k i
    rw [h1, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hterm k hk.2 i
  calc ∑ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) ≠ 0),
        ∫ ω : Fin K → MatV d × MatV d,
          ((violSet R BoxL (proc (projL R BoxL) a₀ ε K ω k)).card : ℝ) ∂(sampleLaw d K)
      ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) ≠ 0),
          8 * ∑ i : Fin m, tailG ((a₀ - 1 / ‖BoxL i‖ ^ 2) / (ε * Real.sqrt (k : ℝ))) :=
        Finset.sum_le_sum hstep
    _ = 8 * ∑ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) ≠ 0),
          ∑ i : Fin m, tailG ((a₀ - 1 / ‖BoxL i‖ ^ 2) / (ε * Real.sqrt (k : ℝ))) := by
        rw [Finset.mul_sum]
    _ = 8 * ∑ i : Fin m, ∑ k ∈ Finset.univ.filter (fun k : Fin K => (k : ℕ) ≠ 0),
          tailG ((a₀ - 1 / ‖BoxL i‖ ^ 2) / (ε * Real.sqrt (k : ℝ))) := by
        rw [Finset.sum_comm]
    _ ≤ 8 * ∑ i : Fin m, Wt (d := d) K a₀ ε (BoxL i) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
        exact sum_fin_ne_zero_le_Icc
          (G := fun k : ℕ => tailG ((a₀ - 1 / ‖BoxL i‖ ^ 2) / (ε * Real.sqrt (k : ℝ))))
          (fun k => tailG_nonneg _) K
    _ ≤ 8 * M := mul_le_mul_of_nonneg_left hM (by norm_num)

end

end Submission.ContactFinal
