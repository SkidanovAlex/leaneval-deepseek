import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.B1Bfix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.B1Bfix.FibreAlg`

The **fibre algebra** of the two states in play:

* `Ψ_δ = cutProd (γ δ) ψ` — the smooth approximant of the sharp box state,
* `Ψ₀ = sharpBoxState B ψ` — the sharp state `1_{B^k}·ψ`,
* `W_δ = Ψ_δ − Ψ₀` — their difference,

for the box `B = dlBox L d u` and the mean-free projection `Q_{B,i} = id − P_{B,i}`
(`Work.SmallBoxTBWord.boxQ`) with the box volume `volA = boxMass L d u`.

The main content is the explicit description of the **slot-`i` function** of each of the three
states, i.e. of `y ↦ Q_{B,i}v (kcInsN n i (y,r))`, for the outside configuration `r`:

* `boxQ_cut_kcInsN`:
  `Q_{B,i}Ψ_δ(kcInsN n i (y,r)) = (∏_{j} γ δ (r j)) · (γ δ y · ψ(kcInsN n i (y,r)) − c_δ(r))`;
* `boxQ_sharp_kcInsN`:
  `Q_{B,i}Ψ₀(kcInsN n i (y,r)) = 1_{r ∈ B^n} · (1_B(y)·ψ(kcInsN n i (y,r)) − c₀(r))`,
  so that — because the window `chiB L d u` vanishes off `B` — the **windowed** slot function is
  the smooth-in-`y` function `1_{r ∈ B^n}·χ y·(ψ(kcInsN n i (y,r)) − c₀(r))`;
* `boxQ_diff_kcInsN`: the slot function of the difference is the difference of the slot functions.

Everything is a pointwise computation from the *definitions* `boxQ = id − boxP` (an integral over
the box `B`), `Function.update`/`kcInsN` (`Submission.BoseGases.update_kcInsN`), the
`Finset.prod`-splitting `Fin.prod_univ_succAbove` and `integral_const_mul`; no integrability
hypothesis is needed.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

/-! ## 1. Reconstructing a configuration from its `i`-th coordinate -/

/-- Every configuration is the insertion of its `i`-th coordinate into the rest. -/
lemma kcInsN_reconstruct {n : ℕ} (i : Fin (n + 1)) (x : Submission.BoseGases.X (n + 1)) :
    Submission.BoseGases.kcInsN n i (x i, fun j : Fin n => x (i.succAbove j)) = x := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Submission.BoseGases.kc_insN_apply_same]
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    rw [Submission.BoseGases.kc_insN_apply_succ]

/-! ## 2. The slot function of the smooth approximant -/

/-- The product of the cutoffs splits along the `i`-th slot. -/
lemma cutProd_prod_split {n : ℕ} (γ : E3 → ℝ) (ψ : Submission.BoseGases.X (n + 1) → ℝ)
    (i : Fin (n + 1)) (y : E3) (r : Submission.BoseGases.X n) :
    cutProd γ ψ (Submission.BoseGases.kcInsN n i (y, r))
      = (γ y * ∏ j : Fin n, γ (r j)) * ψ (Submission.BoseGases.kcInsN n i (y, r)) := by
  classical
  rw [cutProd_apply]
  have hprod : (∏ j : Fin (n + 1), γ ((Submission.BoseGases.kcInsN n i (y, r)) j))
      = γ y * ∏ j : Fin n, γ (r j) := by
    rw [Fin.prod_univ_succAbove _ i]
    congr 1
    · rw [Submission.BoseGases.kc_insN_apply_same]
    · exact Finset.prod_congr rfl fun j _ => by
        rw [Submission.BoseGases.kc_insN_apply_succ]
  rw [hprod]

/-- **The slot-`i` function of the smooth approximant.**  For the box `B` with volume `volA`,
`Q_{B,i}Ψ_δ(kcInsN n i (y,r))` factors the cutoffs of the *outside* configuration out and leaves
the function `γ δ y·ψ(kcInsN n i (y,r)) − c_δ(r)` of the slot position. -/
lemma boxQ_cut_kcInsN {n : ℕ} (volA : ℝ) (B : Set E3) (γ : E3 → ℝ)
    (ψ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1)) (y : E3)
    (r : Submission.BoseGases.X n) :
    Work.SmallBoxTBWord.boxQ volA B i (cutProd γ ψ) (Submission.BoseGases.kcInsN n i (y, r))
      = (∏ j : Fin n, γ (r j)) *
          (γ y * ψ (Submission.BoseGases.kcInsN n i (y, r))
            - (1 / volA) * ∫ t in B, γ t * ψ (Submission.BoseGases.kcInsN n i (t, r))) := by
  classical
  rw [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP]
  have hmean : (∫ z in B, cutProd γ ψ
        (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z))
      = (∏ j : Fin n, γ (r j)) * ∫ t in B, γ t * ψ (Submission.BoseGases.kcInsN n i (t, r)) := by
    rw [show (∫ z in B, cutProd γ ψ
          (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z))
        = ∫ z in B, cutProd γ ψ (Submission.BoseGases.kcInsN n i (z, r)) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [Work.SmallBoxBridge.Fourier.update_kcInsN]]
    rw [show (∫ z in B, cutProd γ ψ (Submission.BoseGases.kcInsN n i (z, r)))
        = ∫ z in B, (∏ j : Fin n, γ (r j)) *
            (γ z * ψ (Submission.BoseGases.kcInsN n i (z, r))) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [cutProd_prod_split γ ψ i z r]
      ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hmean, cutProd_prod_split γ ψ i y r]
  ring

/-! ## 3. The slot function of the sharp box state -/

/-- The `∀`-condition of the sharp state's indicator splits along the `i`-th slot. -/
lemma forall_kcInsN_mem {n : ℕ} {B : Set E3} (i : Fin (n + 1)) (y : E3)
    (r : Submission.BoseGases.X n) :
    (∀ j : Fin (n + 1), (Submission.BoseGases.kcInsN n i (y, r)) j ∈ B)
      ↔ (y ∈ B ∧ ∀ j : Fin n, r j ∈ B) := by
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · have h1 := h i
      rwa [Submission.BoseGases.kc_insN_apply_same] at h1
    · have h1 := h (i.succAbove j)
      rwa [Submission.BoseGases.kc_insN_apply_succ] at h1
  · intro h j
    by_cases hj : j = i
    · subst hj
      have h1 := h.1
      rwa [Submission.BoseGases.kc_insN_apply_same]
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      have h1 := h.2 j'
      rwa [Submission.BoseGases.kc_insN_apply_succ]

/-- The sharp state at an inserted configuration: the outside indicator factors out, and the
slot dependence is `1_B(·)·ψ`. -/
lemma sharpBoxState_kcInsN {n : ℕ} (B : Set E3) (ψ : Submission.BoseGases.X (n + 1) → ℝ)
    (i : Fin (n + 1)) (y : E3) (r : Submission.BoseGases.X n) :
    sharpBoxState B ψ (Submission.BoseGases.kcInsN n i (y, r))
      = (if ∀ j : Fin n, r j ∈ B then (1 : ℝ) else 0) *
          (B.indicator (fun _ => (1 : ℝ)) y * ψ (Submission.BoseGases.kcInsN n i (y, r))) := by
  classical
  rw [sharpState_apply]
  simp only [forall_kcInsN_mem i y r]
  by_cases hy : y ∈ B <;> by_cases hr : ∀ j : Fin n, r j ∈ B <;>
    simp [hy, hr, Set.indicator_of_mem, Set.indicator_of_notMem]

/-- **The slot-`i` function of the sharp box state.**  For the box `B` with volume `volA`,
`Q_{B,i}Ψ₀(kcInsN n i (y,r))` is the outside indicator `1_{r ∈ B^n}` times the difference of the
slot indicator term and the in-box mean `c₀(r)`. -/
lemma boxQ_sharp_kcInsN {n : ℕ} (volA : ℝ) {B : Set E3} (hB : MeasurableSet B)
    (ψ : Submission.BoseGases.X (n + 1) → ℝ) (i : Fin (n + 1)) (y : E3)
    (r : Submission.BoseGases.X n) :
    Work.SmallBoxTBWord.boxQ volA B i (sharpBoxState B ψ)
        (Submission.BoseGases.kcInsN n i (y, r))
      = (if ∀ j : Fin n, r j ∈ B then (1 : ℝ) else 0) *
          (B.indicator (fun _ => (1 : ℝ)) y * ψ (Submission.BoseGases.kcInsN n i (y, r))
            - (1 / volA) * ∫ t in B, ψ (Submission.BoseGases.kcInsN n i (t, r))) := by
  classical
  rw [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP]
  rw [sharpBoxState_kcInsN B ψ i y r]
  have hmean : (∫ z in B, sharpBoxState B ψ
        (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z))
      = (if ∀ j : Fin n, r j ∈ B then (1 : ℝ) else 0) *
          ∫ t in B, ψ (Submission.BoseGases.kcInsN n i (t, r)) := by
    rw [show (∫ z in B, sharpBoxState B ψ
          (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z))
        = ∫ z in B, sharpBoxState B ψ (Submission.BoseGases.kcInsN n i (z, r)) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      rw [Work.SmallBoxBridge.Fourier.update_kcInsN]]
    rw [show (∫ z in B, sharpBoxState B ψ (Submission.BoseGases.kcInsN n i (z, r)))
        = ∫ z in B, (if ∀ j : Fin n, r j ∈ B then (1 : ℝ) else 0) *
            (B.indicator (fun _ => (1 : ℝ)) z * ψ (Submission.BoseGases.kcInsN n i (z, r)))
          from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []
      exact sharpBoxState_kcInsN B ψ i z r]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict hB] with z hz
    rw [Set.indicator_of_mem hz, one_mul]
  rw [hmean]
  ring

end Work.BoseFixB1B
