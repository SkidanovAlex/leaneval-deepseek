import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.exclFunOpAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.OscFibDefs`

**The slice-dominated state class for the oscillation (L²-fibre) commutator pairing.**

`Work.BoseFixB1S.commutatorPairingB1` proves the commutator pairing estimate for a fibre weight
`fib` that is *bounded on the cube* (`GoodState`).  The oscillation form
(`Work.BoseFixB1S.commutatorPairingOscB1`) needs the same estimate with only an `L²(A)`
hypothesis on the *centred* fibre `w`, so the fibre multiplier is unbounded and only in `L¹(A)`.

This file provides the minimal state class under which the *algebraic* identities of the `n₀`
functional calculus (the fibre commutation `n0IterFibComm`, the additivity `n0Iter_add`) still
hold.  The slots only ever read their argument through the integrals
`z ↦ Ψ (Function.update x k z)` over `z ∈ A`, so what is needed is not boundedness of `Ψ` on the
box, but domination by the fibre multiplier:

  `OscDom ℓ A w i Ψ  ⟺  Measurable Ψ ∧ ∃ C, ∀ x ∈ abox N ℓ, |Ψ x| ≤ C * (1 + |w (x i)|)`.

For `w ∈ L¹(A)` this class is closed under the slot operators, and every state occurring in the
argument (`fib (· i) · Φ`, its slot projections, and their differences) lies in it.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-! ## Elementary arithmetic helpers -/

theorem one_add_add_le_mul {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    1 + (A + B) ≤ (1 + A) * (1 + B) := by nlinarith [mul_nonneg hA hB]

theorem one_add_sum3_le_mul3 {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    1 + (A + B + C) ≤ (1 + A) * (1 + B) * (1 + C) := by
  nlinarith [mul_nonneg hA hB, mul_nonneg hA hC, mul_nonneg hB hC,
    mul_nonneg (mul_nonneg hA hB) hC]

/-! ## The class -/

/-- **The slice-dominated state class**: measurable states whose pointwise size is dominated by the
fibre multiplier `w (· i)` plus a constant. -/
def OscDom {N : ℕ} (ℓ : ℝ) (A : Set E3) (w : E3 → ℝ) (i : Fin N) (Ψ : X N → ℝ) : Prop :=
  Measurable Ψ ∧ ∃ C : ℝ, ∀ x ∈ abox N ℓ, |Ψ x| ≤ C * (1 + |w (x i)|)

theorem oscDom_measurable {N : ℕ} {ℓ : ℝ} {A : Set E3} {w : E3 → ℝ} {i : Fin N}
    {Ψ : X N → ℝ} (h : OscDom ℓ A w i Ψ) : Measurable Ψ := h.1

/-- A state bounded on the box is slice-dominated. -/
theorem oscDom_of_bound {N : ℕ} {ℓ : ℝ} {A : Set E3} {w : E3 → ℝ} {i : Fin N}
    {Ψ : X N → ℝ} {C : ℝ} (hm : Measurable Ψ) (hb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) :
    OscDom ℓ A w i Ψ := by
  refine ⟨hm, max C 0, fun x hx => ?_⟩
  have h1 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have h2 : (1 : ℝ) ≤ 1 + |w (x i)| := by
    have := abs_nonneg (w (x i)); linarith
  calc |Ψ x| ≤ C := hb x hx
    _ ≤ max C 0 := le_max_left _ _
    _ = max C 0 * 1 := (mul_one _).symm
    _ ≤ max C 0 * (1 + |w (x i)|) := mul_le_mul_of_nonneg_left h2 h1

/-- `GoodState` states are slice-dominated. -/
theorem oscDom_of_goodState {N : ℕ} {ℓ : ℝ} {A : Set E3} {w : E3 → ℝ} {i : Fin N}
    {Ψ : X N → ℝ} (h : GoodState ℓ Ψ) : OscDom ℓ A w i Ψ :=
  oscDom_of_bound h.1 h.2.choose_spec

/-- Sums of slice-dominated states (same slot and multiplier) are slice-dominated. -/
theorem oscDom_add {N : ℕ} {ℓ : ℝ} {A : Set E3} {w : E3 → ℝ} {i : Fin N}
    {Ψ Φ : X N → ℝ} (hΨ : OscDom ℓ A w i Ψ) (hΦ : OscDom ℓ A w i Φ) :
    OscDom ℓ A w i (Ψ + Φ) := by
  obtain ⟨hm, C, hC⟩ := hΨ
  obtain ⟨hm', C', hC'⟩ := hΦ
  refine ⟨hm.add hm', C + C', fun x hx => ?_⟩
  calc |(Ψ + Φ) x| = |Ψ x + Φ x| := rfl
    _ ≤ |Ψ x| + |Φ x| := abs_add_le _ _
    _ ≤ C * (1 + |w (x i)|) + C' * (1 + |w (x i)|) := add_le_add (hC x hx) (hC' x hx)
    _ = (C + C') * (1 + |w (x i)|) := by ring

/-- Differences of slice-dominated states (same slot and multiplier) are slice-dominated. -/
theorem oscDom_sub {N : ℕ} {ℓ : ℝ} {A : Set E3} {w : E3 → ℝ} {i : Fin N}
    {Ψ Φ : X N → ℝ} (hΨ : OscDom ℓ A w i Ψ) (hΦ : OscDom ℓ A w i Φ) :
    OscDom ℓ A w i (Ψ - Φ) := by
  obtain ⟨hm, C, hC⟩ := hΨ
  obtain ⟨hm', C', hC'⟩ := hΦ
  refine ⟨hm.sub hm', C + C', fun x hx => ?_⟩
  calc |(Ψ - Φ) x| = |Ψ x - Φ x| := rfl
    _ ≤ |Ψ x| + |Φ x| := abs_sub _ _
    _ ≤ C * (1 + |w (x i)|) + C' * (1 + |w (x i)|) := add_le_add (hC x hx) (hC' x hx)
    _ = (C + C') * (1 + |w (x i)|) := by ring

/-- The fibre multiplier `w (· i)` times a state bounded on the box is slice-dominated. -/
theorem oscDom_w_mul_bdd {N : ℕ} {ℓ : ℝ} {A : Set E3} {w : E3 → ℝ} {i : Fin N}
    {B : X N → ℝ} {Cb : ℝ} (hwm : Measurable w) (hBm : Measurable B)
    (hB : ∀ x ∈ abox N ℓ, |B x| ≤ Cb) :
    OscDom ℓ A w i (fun x => w (x i) * B x) := by
  refine ⟨(hwm.comp (measurable_pi_apply i)).mul hBm, max Cb 0, fun x hx => ?_⟩
  have h1 : (0 : ℝ) ≤ max Cb 0 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ |w (x i)| := abs_nonneg _
  have h3 : (0 : ℝ) ≤ 1 + |w (x i)| := by linarith
  have h4 : |w (x i)| * |B x| ≤ |w (x i)| * max Cb 0 :=
    mul_le_mul_of_nonneg_left (le_trans (hB x hx) (le_max_left _ _)) h2
  rw [abs_mul]
  calc |w (x i)| * |B x| ≤ |w (x i)| * max Cb 0 := h4
    _ ≤ max Cb 0 * (1 + |w (x i)|) := by
        calc |w (x i)| * max Cb 0 = max Cb 0 * |w (x i)| := by ring
          _ ≤ max Cb 0 * (1 + |w (x i)|) :=
              mul_le_mul_of_nonneg_left (by linarith) h1

/-- Multiplication of a slice-dominated state by a state bounded on the box. -/
theorem oscDom_mul_bdd {N : ℕ} {ℓ : ℝ} {A : Set E3} {w : E3 → ℝ} {i : Fin N}
    {B : X N → ℝ} {Cb : ℝ} (hBm : Measurable B)
    (hB : ∀ x ∈ abox N ℓ, |B x| ≤ Cb) {Ψ : X N → ℝ} (hΨ : OscDom ℓ A w i Ψ) :
    OscDom ℓ A w i (fun x => B x * Ψ x) := by
  obtain ⟨hm, C, hC⟩ := hΨ
  refine ⟨hBm.mul hm, max Cb 0 * max C 0, fun x hx => ?_⟩
  have h1 : (0 : ℝ) ≤ max Cb 0 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have h3 : (0 : ℝ) ≤ 1 + |w (x i)| := by have := abs_nonneg (w (x i)); linarith
  have h4 : |B x| ≤ max Cb 0 := le_trans (hB x hx) (le_max_left _ _)
  have h5 : |Ψ x| ≤ max C 0 * (1 + |w (x i)|) :=
    le_trans (hC x hx) (mul_le_mul_of_nonneg_right (le_max_left _ _) h3)
  rw [abs_mul]
  calc |B x| * |Ψ x| ≤ max Cb 0 * (max C 0 * (1 + |w (x i)|)) :=
        mul_le_mul h4 h5 (abs_nonneg _) h1
    _ = max Cb 0 * max C 0 * (1 + |w (x i)|) := by ring

/-! ## Slot integrability extracted from the class -/

/-- The slot-`k` fibre of a slice-dominated state is integrable over `A`, provided the multiplier
is in `L¹(A)`. -/
theorem oscDom_integrableOn_slot {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    {w : E3 → ℝ} {i : Fin N} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (hw : IntegrableOn w A)
    {Ψ : X N → ℝ} (hΨ : OscDom ℓ A w i Ψ) (k : Fin N) (x : X N) (hx : x ∈ abox N ℓ) :
    IntegrableOn (fun z => Ψ (Function.update x k z)) A volume := by
  obtain ⟨hm, C, hC⟩ := hΨ
  have hAfin : (volume : Measure E3) A < ⊤ := volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hAfin)
  have hwabs : Integrable (fun z : E3 => |w z|) ((volume : Measure E3).restrict A) :=
    (show Integrable w ((volume : Measure E3).restrict A) from hw).abs
  have hone : Integrable (fun z : E3 => 1 + |w z|) ((volume : Measure E3).restrict A) :=
    (MeasureTheory.integrable_const (1 : ℝ)).add hwabs
  set C₁ : ℝ := max C 0 with hC₁def
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hC₁ : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C₁ * (1 + |w (y i)|) := by
    intro y hy
    have h3 : (0 : ℝ) ≤ 1 + |w (y i)| := by have := abs_nonneg (w (y i)); linarith
    exact le_trans (hC y hy) (mul_le_mul_of_nonneg_right (le_max_left _ _) h3)
  refine Integrable.mono' (g := fun z : E3 => C₁ * ((1 + |w z|) * (1 + |w (x i)|))) ?_ ?_ ?_
  · exact (hone.mul_const _).const_mul _
  · exact (hm.comp (by fun_prop : Measurable fun z : E3 => Function.update x k z)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict hA] with z hz
    rw [Real.norm_eq_abs]
    have hmem : Function.update x k z ∈ abox N ℓ := update_mem_abox' hAc hx k hz
    have hb := hC₁ _ hmem
    have hw1 : |w ((Function.update x k z) i)| ≤ |w z| + |w (x i)| := by
      rw [Function.update_apply]
      split_ifs with h1'
      · nlinarith [abs_nonneg (w (x i))]
      · nlinarith [abs_nonneg (w z)]
    calc |Ψ (Function.update x k z)|
        ≤ C₁ * (1 + |w ((Function.update x k z) i)|) := hb
      _ ≤ C₁ * (1 + (|w z| + |w (x i)|)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC₁0
      _ ≤ C₁ * ((1 + |w z|) * (1 + |w (x i)|)) :=
          mul_le_mul_of_nonneg_left (one_add_add_le_mul (abs_nonneg _) (abs_nonneg _)) hC₁0

/-- The two-slot fibre of a slice-dominated state is integrable over `A × A`. -/
theorem oscDom_integrable_prod {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    {w : E3 → ℝ} {i : Fin N} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (hw : IntegrableOn w A)
    {Ψ : X N → ℝ} (hΨ : OscDom ℓ A w i Ψ) (k l : Fin N) (x : X N) (hx : x ∈ abox N ℓ) :
    Integrable (fun p : E3 × E3 => Ψ (Function.update (Function.update x k p.1) l p.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
  obtain ⟨hm, C, hC⟩ := hΨ
  have hAfin : (volume : Measure E3) A < ⊤ := volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hAfin)
  have hwabs : Integrable (fun z : E3 => |w z|) ((volume : Measure E3).restrict A) :=
    (show Integrable w ((volume : Measure E3).restrict A) from hw).abs
  have hone : Integrable (fun z : E3 => 1 + |w z|) ((volume : Measure E3).restrict A) :=
    (MeasureTheory.integrable_const (1 : ℝ)).add hwabs
  set C₁ : ℝ := max C 0 with hC₁def
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hC₁ : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C₁ * (1 + |w (y i)|) := by
    intro y hy
    have h3 : (0 : ℝ) ≤ 1 + |w (y i)| := by have := abs_nonneg (w (y i)); linarith
    exact le_trans (hC y hy) (mul_le_mul_of_nonneg_right (le_max_left _ _) h3)
  refine Integrable.mono'
    (g := fun p : E3 × E3 =>
      C₁ * (((1 + |w p.1|) * (1 + |w p.2|)) * (1 + |w (x i)|))) ?_ ?_ ?_
  · exact ((hone.mul_prod hone).mul_const _).const_mul _
  · exact (hm.comp (by fun_prop : Measurable fun p : E3 × E3 =>
      Function.update (Function.update x k p.1) l p.2)).aestronglyMeasurable
  · rw [MeasureTheory.Measure.prod_restrict]
    filter_upwards [self_mem_ae_restrict (hA.prod hA)] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Real.norm_eq_abs]
    have hmem : Function.update (Function.update x k p.1) l p.2 ∈ abox N ℓ :=
      update_mem_abox' hAc (update_mem_abox' hAc hx k hp1) l hp2
    have hb := hC₁ _ hmem
    have h1 : (0 : ℝ) ≤ |w p.1| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |w p.2| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |w (x i)| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ C₁ := hC₁0
    have hyi : (Function.update (Function.update x k p.1) l p.2) i
        = if i = l then p.2 else if i = k then p.1 else x i := by
      rw [Function.update_apply, Function.update_apply]
    have hkey : |w ((Function.update (Function.update x k p.1) l p.2) i)|
        ≤ |w p.1| + |w p.2| + |w (x i)| := by
      rw [hyi]
      split_ifs with h1' h2'
      · nlinarith [abs_nonneg (w p.1), abs_nonneg (w (x i))]
      · nlinarith [abs_nonneg (w p.2), abs_nonneg (w (x i))]
      · nlinarith [abs_nonneg (w p.1), abs_nonneg (w p.2)]
    calc |Ψ (Function.update (Function.update x k p.1) l p.2)|
        ≤ C₁ * (1 + |w ((Function.update (Function.update x k p.1) l p.2) i)|) := hb
      _ ≤ C₁ * (1 + (|w p.1| + |w p.2| + |w (x i)|)) :=
          mul_le_mul_of_nonneg_left (by linarith) h4
      _ ≤ C₁ * ((1 + |w p.1|) * (1 + |w p.2|) * (1 + |w (x i)|)) :=
          mul_le_mul_of_nonneg_left (one_add_sum3_le_mul3 h1 h2 h3) h4
      _ = C₁ * (((1 + |w p.1|) * (1 + |w p.2|)) * (1 + |w (x i)|)) := by ring

/-- The slot projection of a slice-dominated state is again slice-dominated (the slot mean of the
fibre multiplier is integrable over `A`). -/
theorem oscDom_boxPInd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) {i : Fin N} {Ψ : X N → ℝ}
    (hΨ : OscDom ℓ A w i Ψ) (j : Fin N) :
    OscDom ℓ A w i (UBBInputs8.boxPInd volA A j Ψ) := by
  have hΨ' : OscDom ℓ A w i Ψ := hΨ
  obtain ⟨hm, C, hC⟩ := hΨ
  have hAfin : (volume : Measure E3) A < ⊤ := volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hAfin)
  have hwabs : Integrable (fun z : E3 => |w z|) ((volume : Measure E3).restrict A) :=
    (show Integrable w ((volume : Measure E3).restrict A) from hw).abs
  have hone : Integrable (fun z : E3 => 1 + |w z|) ((volume : Measure E3).restrict A) :=
    (MeasureTheory.integrable_const (1 : ℝ)).add hwabs
  set C₁ : ℝ := max C 0 with hC₁def
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hC₁ : ∀ y ∈ abox N ℓ, |Ψ y| ≤ C₁ * (1 + |w (y i)|) := by
    intro y hy
    have h3 : (0 : ℝ) ≤ 1 + |w (y i)| := by have := abs_nonneg (w (y i)); linarith
    exact le_trans (hC y hy) (mul_le_mul_of_nonneg_right (le_max_left _ _) h3)
  set K : ℝ := ∫ z in A, |w z| with hKdef
  have hK0 : 0 ≤ K := setIntegral_nonneg hA (fun z _ => abs_nonneg _)
  -- the two slot means
  have hK1 : (∫ z in A, (1 : ℝ)) = volA := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, hvolA]
    simp
  have hK2 : (∫ z in A, |w z|) = K := hKdef.symm
  have hKval : (∫ z in A, (1 + |w z|)) = volA + K := by
    rw [integral_add (MeasureTheory.integrable_const (1 : ℝ)) hwabs, hK1, hK2]
  -- the pointwise bound for the slot projection
  have hbound : ∀ x ∈ abox N ℓ,
      |UBBInputs8.boxPInd volA A j Ψ x| ≤ (C₁ * (1 + K / volA)) * (1 + |w (x i)|) := by
    intro x hx
    have hval : (∫ z in A, |Ψ (Function.update x j z)|) ≤ C₁ * (volA + K) * (1 + |w (x i)|) := by
      have hint1 : IntegrableOn (fun z => |Ψ (Function.update x j z)|) A volume :=
        (show Integrable (fun z => Ψ (Function.update x j z)) ((volume : Measure E3).restrict A) from
          oscDom_integrableOn_slot (volA := volA) hℓ hA hAc hw hΨ' j x hx).abs
      have h2 : IntegrableOn (fun z => C₁ * ((1 + |w z|) * (1 + |w (x i)|))) A volume :=
        (hone.mul_const _).const_mul _
      have hpt : (fun z => |Ψ (Function.update x j z)|)
          ≤ᵐ[(volume : Measure E3).restrict A]
            fun z => C₁ * ((1 + |w z|) * (1 + |w (x i)|)) := by
        filter_upwards [self_mem_ae_restrict hA] with z hz
        have hmem : Function.update x j z ∈ abox N ℓ := update_mem_abox' hAc hx j hz
        have hb := hC₁ _ hmem
        have hw1 : |w ((Function.update x j z) i)| ≤ |w z| + |w (x i)| := by
          rw [Function.update_apply]
          split_ifs with h1'
          · nlinarith [abs_nonneg (w (x i))]
          · nlinarith [abs_nonneg (w z)]
        calc |Ψ (Function.update x j z)|
            ≤ C₁ * (1 + |w ((Function.update x j z) i)|) := hb
          _ ≤ C₁ * (1 + (|w z| + |w (x i)|)) :=
              mul_le_mul_of_nonneg_left (by linarith) hC₁0
          _ ≤ C₁ * ((1 + |w z|) * (1 + |w (x i)|)) :=
              mul_le_mul_of_nonneg_left (one_add_add_le_mul (abs_nonneg _) (abs_nonneg _)) hC₁0
      have hmono := setIntegral_mono_ae_restrict hint1 h2 hpt
      have hEq : (∫ z in A, C₁ * ((1 + |w z|) * (1 + |w (x i)|)))
          = C₁ * (volA + K) * (1 + |w (x i)|) := by
        rw [integral_const_mul, integral_mul_const, hKval]
        ring
      exact le_trans hmono (le_of_eq hEq)
    have h1 : |UBBInputs8.boxPInd volA A j Ψ x|
        ≤ (1 / volA) * (∫ z in A, |Ψ (Function.update x j z)|) := by
      have hni : |∫ z in A, Ψ (Function.update x j z)|
          ≤ ∫ z in A, |Ψ (Function.update x j z)| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (f := fun z : E3 => Ψ (Function.update x j z))
            (μ := (volume : Measure E3).restrict A)
      have hind : |A.indicator (fun _ => (1 : ℝ)) (x j)| ≤ 1 := Aind_abs_le_one A (x j)
      have hnn1 : (0 : ℝ) ≤ 1 / volA := by positivity
      have hnn2 : (0 : ℝ) ≤ ∫ z in A, |Ψ (Function.update x j z)| :=
        setIntegral_nonneg hA (fun z _ => abs_nonneg _)
      have hE : |UBBInputs8.boxPInd volA A j Ψ x|
          = (1 / volA) * |∫ z in A, Ψ (Function.update x j z)|
            * |A.indicator (fun _ => (1 : ℝ)) (x j)| := by
        rw [UBBInputs8.boxPInd, abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
      rw [hE]
      calc (1 / volA) * |∫ z in A, Ψ (Function.update x j z)|
            * |A.indicator (fun _ => (1 : ℝ)) (x j)|
          ≤ (1 / volA) * (∫ z in A, |Ψ (Function.update x j z)|) * 1 := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hni hnn1) hind (abs_nonneg _)
              (mul_nonneg hnn1 hnn2)
        _ = (1 / volA) * (∫ z in A, |Ψ (Function.update x j z)|) := by ring
    have h2 : (1 / volA) * (C₁ * (volA + K) * (1 + |w (x i)|))
        = (C₁ * (1 + K / volA)) * (1 + |w (x i)|) := by
      field_simp
      try ring
    calc |UBBInputs8.boxPInd volA A j Ψ x|
        ≤ (1 / volA) * (∫ z in A, |Ψ (Function.update x j z)|) := h1
      _ ≤ (1 / volA) * (C₁ * (volA + K) * (1 + |w (x i)|)) :=
          mul_le_mul_of_nonneg_left hval (by positivity)
      _ = (C₁ * (1 + K / volA)) * (1 + |w (x i)|) := h2
  exact ⟨measurable_boxPInd volA A hA j hm, C₁ * (1 + K / volA), hbound⟩

/-- The slot projection of a slice-dominated state is *bounded* on the box (it is the slot mean
of a function dominated by the integrable `w`). -/
theorem goodState_boxPInd_osc {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) {i : Fin N} {X : X N → ℝ}
    (hX : OscDom ℓ A w i X) : GoodState ℓ (UBBInputs8.boxPInd volA A i X) := by
  have hX' : OscDom ℓ A w i X := hX
  obtain ⟨hm, C, hC⟩ := hX
  have hAfin : (volume : Measure E3) A < ⊤ := volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hAfin)
  have hwabs : Integrable (fun z : E3 => |w z|) ((volume : Measure E3).restrict A) :=
    (show Integrable w ((volume : Measure E3).restrict A) from hw).abs
  have hone : Integrable (fun z : E3 => 1 + |w z|) ((volume : Measure E3).restrict A) :=
    (MeasureTheory.integrable_const (1 : ℝ)).add hwabs
  set C₁ : ℝ := max C 0 with hC₁def
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hC₁ : ∀ y ∈ abox N ℓ, |X y| ≤ C₁ * (1 + |w (y i)|) := by
    intro y hy
    have h3 : (0 : ℝ) ≤ 1 + |w (y i)| := by have := abs_nonneg (w (y i)); linarith
    exact le_trans (hC y hy) (mul_le_mul_of_nonneg_right (le_max_left _ _) h3)
  set K : ℝ := ∫ z in A, |w z| with hKdef
  have hK2 : (∫ z in A, |w z|) = K := hKdef.symm
  have hKval : (∫ z in A, (1 + |w z|)) = volA + K := by
    rw [integral_add (MeasureTheory.integrable_const (1 : ℝ)) hwabs]
    have h1 : (∫ z in A, (1 : ℝ)) = volA := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, hvolA]
      simp
    rw [h1, hK2]
  refine ⟨measurable_boxPInd volA A hA i hm, C₁ * ((volA + K) / volA), fun x hx => ?_⟩
  have hval : (∫ z in A, |X (Function.update x i z)|) ≤ C₁ * (volA + K) := by
    have hint1 : IntegrableOn (fun z => |X (Function.update x i z)|) A volume :=
      (show Integrable (fun z => X (Function.update x i z)) ((volume : Measure E3).restrict A) from
        oscDom_integrableOn_slot (volA := volA) hℓ hA hAc hw hX' i x hx).abs
    have h2 : IntegrableOn (fun z => C₁ * (1 + |w z|)) A volume := hone.const_mul _
    have hmono := setIntegral_mono_ae_restrict hint1 h2
      (by
        filter_upwards [self_mem_ae_restrict hA] with z hz
        have hmem : Function.update x i z ∈ abox N ℓ := update_mem_abox' hAc hx i hz
        have hb := hC₁ _ hmem
        rw [Function.update_self] at hb
        exact le_trans hb (le_of_eq (by ring)))
    refine le_trans hmono (le_of_eq ?_)
    rw [integral_const_mul, hKval]
  have h1 : |UBBInputs8.boxPInd volA A i X x|
      ≤ (1 / volA) * (∫ z in A, |X (Function.update x i z)|) := by
    have hni : |∫ z in A, X (Function.update x i z)|
        ≤ ∫ z in A, |X (Function.update x i z)| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (f := fun z : E3 => X (Function.update x i z))
          (μ := (volume : Measure E3).restrict A)
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := Aind_abs_le_one A (x i)
    have hnn1 : (0 : ℝ) ≤ 1 / volA := by positivity
    have hnn2 : (0 : ℝ) ≤ ∫ z in A, |X (Function.update x i z)| :=
      setIntegral_nonneg hA (fun z _ => abs_nonneg _)
    have hE : |UBBInputs8.boxPInd volA A i X x|
        = (1 / volA) * |∫ z in A, X (Function.update x i z)|
          * |A.indicator (fun _ => (1 : ℝ)) (x i)| := by
      rw [UBBInputs8.boxPInd, abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
    rw [hE]
    calc (1 / volA) * |∫ z in A, X (Function.update x i z)|
          * |A.indicator (fun _ => (1 : ℝ)) (x i)|
        ≤ (1 / volA) * (∫ z in A, |X (Function.update x i z)|) * 1 := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hni hnn1) hind (abs_nonneg _)
            (mul_nonneg hnn1 hnn2)
      _ = (1 / volA) * (∫ z in A, |X (Function.update x i z)|) := by ring
  have h2 : (1 / volA) * (C₁ * (volA + K)) = C₁ * ((volA + K) / volA) := by
    field_simp
    try ring
  calc |UBBInputs8.boxPInd volA A i X x|
      ≤ (1 / volA) * (∫ z in A, |X (Function.update x i z)|) := h1
    _ ≤ (1 / volA) * (C₁ * (volA + K)) := mul_le_mul_of_nonneg_left hval (by positivity)
    _ = C₁ * ((volA + K) / volA) := h2

/-- The single-slot operators preserve the slice-dominated class. -/
theorem oscDom_n0Slot {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) {i : Fin N} (b : Fin N → Bool) (j : Fin N)
    {Ψ : X N → ℝ} (hΨ : OscDom ℓ A w i Ψ) : OscDom ℓ A w i (n0Slot volA A b j Ψ) := by
  by_cases hb : b j = true
  · rw [n0Slot_eq_true volA A b j Ψ hb]
    exact oscDom_boxPInd hℓ hvol hA hvolA hAc hw hΨ j
  · rw [n0Slot_eq_false volA A b j Ψ (bool_eq_false_of_not_eq_true hb)]
    exact oscDom_sub hΨ (oscDom_boxPInd hℓ hvol hA hvolA hAc hw hΨ j)

/-- The slot iteration preserves the slice-dominated class. -/
theorem oscDom_n0Iter {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) {i : Fin N} (b : Fin N → Bool) (l : List (Fin N))
    {Ψ : X N → ℝ} (hΨ : OscDom ℓ A w i Ψ) : OscDom ℓ A w i (n0Iter volA A b l Ψ) := by
  induction l generalizing Ψ with
  | nil => rw [n0Iter]; exact hΨ
  | cons k l ih =>
    rw [n0Iter_cons]
    exact ih (oscDom_n0Slot hℓ hvol hA hvolA hAc hw b k hΨ)

/-! ## The weak two-slot Fubini -/

/-- The two-slot mean is symmetric (Fubini), with the joint integrability as hypothesis. -/
theorem twoMean_comm_int {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ}
    (hint : ∀ x ∈ abox N ℓ, Integrable
      (fun p : E3 × E3 => Ψ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A))) :
    ∀ x ∈ abox N ℓ, twoMean volA A i j Ψ x = twoMean volA A j i Ψ x := by
  intro x hx
  have hInt : Integrable
      (Function.uncurry (fun z w : E3 => Ψ (Function.update (Function.update x i z) j w)))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := hint x hx
  have hswap : (∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
      = ∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x i z) j w) :=
    MeasureTheory.integral_integral_swap hInt
  have h2 : (∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x i z) j w))
      = ∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x j w) i z) := by
    apply integral_congr_ae; filter_upwards with w
    apply integral_congr_ae; filter_upwards with z
    rw [Function.update_comm hij]
  unfold twoMean
  rw [hswap, h2]

/-- The box projections in two different slots commute, with the joint integrability as
hypothesis. -/
theorem boxPInd_boxPInd_comm_int {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ}
    (hint : ∀ x ∈ abox N ℓ, Integrable
      (fun p : E3 × E3 => Ψ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A))) :
    ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x
      = UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x := by
  intro x hx
  rw [boxPInd_twoMean volA A hij.symm Ψ x, boxPInd_twoMean volA A hij Ψ x,
    (twoMean_comm_int hℓ hA hAc hij hint x hx)]
  ring

/-! ## The fibre commutation and the projection identities, without boundedness -/

/-- **The fibre weight `fib (· i)` passes through an iteration that avoids the slot `i`**, for an
arbitrary (not necessarily bounded) fibre function. -/
theorem n0IterFibComm_free {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (fib : E3 → ℝ) (i : Fin N) (b : Fin N → Bool) :
    ∀ (l : List (Fin N)), i ∉ l → ∀ Ψ : X N → ℝ, ∀ x ∈ abox N ℓ,
      n0Iter volA A b l (fun y => fib (y i) * Ψ y) x
        = fib (x i) * n0Iter volA A b l Ψ x := by
  intro l
  induction l with
  | nil => intro _ Ψ x _; rfl
  | cons j l ih =>
    intro hj Ψ x hx
    have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
    have hil : i ∉ l := fun h => hj (List.mem_of_mem_tail h)
    rw [n0Iter_cons, n0Iter_cons]
    have hagree : ∀ y ∈ abox N ℓ,
        n0Slot volA A b j (fun y => fib (y i) * Ψ y) y
          = (fun y => fib (y i) * n0Slot volA A b j Ψ y) y :=
      fun y hy => n0Slot_slot_fib volA A b hji fib Ψ y
    rw [n0Iter_eq_of_eqOn_box hA hAc b
      (f := n0Slot volA A b j (fun y => fib (y i) * Ψ y))
      (g := fun y => fib (y i) * n0Slot volA A b j Ψ y) hagree l x hx]
    exact ih hil (n0Slot volA A b j Ψ) x hx

/-- **The single-slot operators commute with the box projection `P_i` in a different slot**, under
the slice-dominated hypothesis. -/
theorem n0Slot_comm_boxPInd_osc {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) (b : Fin N → Bool) {i k : Fin N} (hki : k ≠ i)
    {X : X N → ℝ} (hX : OscDom ℓ A w i X) :
    ∀ x ∈ abox N ℓ, n0Slot volA A b k (UBBInputs8.boxPInd volA A i X) x
      = UBBInputs8.boxPInd volA A i (n0Slot volA A b k X) x := by
  have hcomm : ∀ y ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A k (UBBInputs8.boxPInd volA A i X) y
        = UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A k X) y :=
    boxPInd_boxPInd_comm_int (volA := volA) hℓ hvol hA hvolA hAc (Ne.symm hki)
      (fun y hy => oscDom_integrable_prod (volA := volA) hℓ hA hAc hw hX i k y hy)
  intro x hx
  by_cases hbk : b k = true
  · rw [n0Slot_eq_true volA A b k _ hbk, n0Slot_eq_true volA A b k X hbk]
    exact hcomm x hx
  · have hbf : b k = false := bool_eq_false_of_not_eq_true hbk
    have hXk : OscDom ℓ A w i (UBBInputs8.boxPInd volA A k X) :=
      oscDom_boxPInd hℓ hvol hA hvolA hAc hw hX k
    have hsub : UBBInputs8.boxPInd volA A i (X - UBBInputs8.boxPInd volA A k X) x
        = UBBInputs8.boxPInd volA A i X x
          - UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A k X) x :=
      boxPInd_sub (Φ := X) (Ψ := UBBInputs8.boxPInd volA A k X) volA A i x
        (oscDom_integrableOn_slot (volA := volA) hℓ hA hAc hw hX i x hx)
        (oscDom_integrableOn_slot (volA := volA) hℓ hA hAc hw hXk i x hx)
    rw [n0Slot_eq_false volA A b k _ hbf, n0Slot_eq_false volA A b k X hbf, hsub]
    simp only [Pi.sub_apply]
    rw [hcomm x hx]

/-- **`P_i`-invariance is preserved by any iteration whose slot `i` branch is `P_i`**: if the list
`L` contains the slot `i` and the pattern `b` takes the `true` branch there, then the iteration
cannot distinguish `P_i X` from `X`. -/
theorem n0Iter_boxPInd_osc {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) {i : Fin N} (b : Fin N → Bool) :
    ∀ (L : List (Fin N)), i ∈ L → b i = true → ∀ {X : X N → ℝ}, OscDom ℓ A w i X →
      ∀ x ∈ abox N ℓ,
        n0Iter volA A b L (UBBInputs8.boxPInd volA A i X) x = n0Iter volA A b L X x := by
  intro L
  induction L with
  | nil => intro hmem _ X hX x _; exact absurd hmem (by simp)
  | cons k l ih =>
    intro hmem hbi X hX x hx
    rw [n0Iter_cons, n0Iter_cons]
    by_cases hki : k = i
    · have hbk : b k = true := by rw [hki]; exact hbi
      rw [n0Slot_eq_true volA A b k _ hbk, n0Slot_eq_true volA A b k X hbk, hki,
        boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i X]
    · have hmem' : i ∈ l := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h (fun hh => hki hh.symm)
        · exact h
      have hXk : OscDom ℓ A w i (n0Slot volA A b k X) :=
        oscDom_n0Slot hℓ hvol hA hvolA hAc hw b k hX
      have hagree : ∀ y ∈ abox N ℓ,
          n0Slot volA A b k (UBBInputs8.boxPInd volA A i X) y
            = UBBInputs8.boxPInd volA A i (n0Slot volA A b k X) y :=
        fun y hy => n0Slot_comm_boxPInd_osc hℓ hvol hA hvolA hAc hw b hki hX y hy
      rw [n0Iter_eq_of_eqOn_box hA hAc b (l := l) hagree x hx]
      exact ih hmem' hbi hXk x hx

/-- **`n0ProjOp S` cannot distinguish `P_i X` from `X` when `i ∈ S`.** -/
theorem n0ProjOp_boxPInd_osc {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w : E3 → ℝ} (hw : IntegrableOn w A) {i : Fin N} (S : Finset (Fin N)) (hiS : i ∈ S)
    {X : X N → ℝ} (hX : OscDom ℓ A w i X) :
    ∀ x ∈ abox N ℓ,
      n0ProjOp volA A S (UBBInputs8.boxPInd volA A i X) x = n0ProjOp volA A S X x := by
  have hbi : (fun j : Fin N => decide (j ∈ S)) i = true := by simp [hiS]
  have hmem : i ∈ List.ofFn (fun j : Fin N => j) := List.mem_ofFn.mpr ⟨i, rfl⟩
  exact n0Iter_boxPInd_osc hℓ hvol hA hvolA hAc hw (fun j : Fin N => decide (j ∈ S))
    (List.ofFn (fun j : Fin N => j)) hmem hbi hX

/-! ## Regrouping a sum over all subsets into `{T, T ∪ {i}}` pairs (own coefficient) -/

/-- **The powerset reorganisation with the coefficient moving with the cardinality.** -/
theorem sum_erase_pair {N : ℕ} (i : Fin N) (g : ℝ → ℝ) (f : Finset (Fin N) → ℝ) :
    (∑ S : Finset (Fin N), g (S.card : ℝ) * f S)
      = ∑ T ∈ (Finset.univ.erase i).powerset,
          (g (T.card : ℝ) * f T + g ((T.card : ℝ) + 1) * f (insert i T)) := by
  classical
  have hsplit := Finset.sum_powerset_insert (s := (Finset.univ.erase i : Finset (Fin N)))
    (a := i) (Finset.notMem_erase i (Finset.univ : Finset (Fin N)))
    (fun S : Finset (Fin N) => g (S.card : ℝ) * f S)
  rw [Finset.insert_erase (Finset.mem_univ i), Finset.powerset_univ] at hsplit
  have hmain : (∑ S : Finset (Fin N), g (S.card : ℝ) * f S)
      = (∑ T ∈ (Finset.univ.erase i).powerset, g (T.card : ℝ) * f T)
        + ∑ T ∈ (Finset.univ.erase i).powerset,
            g ((T.card : ℝ) + 1) * f (insert i T) := by
    rw [hsplit]
    congr 1
    · apply Finset.sum_congr rfl
      intro T hT
      have hiT : i ∉ T := fun h => Finset.notMem_erase i _ ((Finset.mem_powerset.mp hT) h)
      rw [Finset.card_insert_of_notMem hiT, Nat.cast_add, Nat.cast_one]
  rw [hmain, ← Finset.sum_add_distrib]

end Work.BoseFixB1S
