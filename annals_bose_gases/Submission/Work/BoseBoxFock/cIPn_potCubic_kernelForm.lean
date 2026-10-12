import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicResiduals
import Submission.Work.BoseBoxFock.boxSlotOf_pair_integrable
import Submission.Work.BoseBoxFock.cIPn_boxSlotOf_two_slot_congr
import Submission.Work.BoseBoxFock.cIPn_potCubic_eq_pairSet_gen
import Submission.Work.BoseBoxFock.integrable_conjEtaOf_mul
import Submission.Work.BoseBoxFock.kernelForm_pinSubst
import Submission.Work.BoseBoxFock.measurable_integral_conjEtaOf_update
import Submission.Work.BoseBoxFock.norm_integral_conjEtaOf_mul_le
import Submission.Work.BoseBoxFock.pinQ_etaOf
import Submission.Work.BoseBoxFock.pinTheta_etaOf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## `cIPn` linearity helpers -/
private lemma cIPn_smul_loc {d : ℕ} (Θ : Work.BoseDict.Xn d → ℂ) (c : ℝ)
    (Ψ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.cIPn d Θ (c • Ψ) = c • Work.BoseDict.cIPn d Θ Ψ := by
  simp only [Work.BoseDict.cIPn, Pi.smul_apply, Complex.real_smul]
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun x => by ring))

/-- `cIPn Θ (Ψ + Χ) = cIPn Θ Ψ + cIPn Θ Χ`. -/
private lemma cIPn_add_loc {d : ℕ} (Θ Ψ Χ : Work.BoseDict.Xn d → ℂ)
    (hΨ : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * Ψ x))
    (hΧ : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * Χ x)) :
    Work.BoseDict.cIPn d Θ (Ψ + Χ) = Work.BoseDict.cIPn d Θ Ψ + Work.BoseDict.cIPn d Θ Χ := by
  simp only [Work.BoseDict.cIPn, Pi.add_apply, mul_add]
  rw [MeasureTheory.integral_add hΨ hΧ]

/-- `cIPn Θ (Σ_{i∈s} Ψ i) = Σ_{i∈s} cIPn Θ (Ψ i)`. -/
private lemma cIPn_finset_sum_loc {d : ℕ} {ι : Type*} (s : Finset ι) (Θ : Work.BoseDict.Xn d → ℂ)
    (Ψ : ι → Work.BoseDict.Xn d → ℂ)
    (h : ∀ i ∈ s, MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * Ψ i x)) :
    Work.BoseDict.cIPn d Θ (∑ i ∈ s, Ψ i) = ∑ i ∈ s, Work.BoseDict.cIPn d Θ (Ψ i) := by
  simp only [Work.BoseDict.cIPn, Finset.sum_apply, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum _ h]

/-- Integrability of a finite sum of integrable integrands. -/
private lemma integrable_finset_sum_loc {d : ℕ} {ι : Type*} (s : Finset ι)
    (Θ : Work.BoseDict.Xn d → ℂ) (Ψ : ι → Work.BoseDict.Xn d → ℂ)
    (h : ∀ i ∈ s, MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * Ψ i x)) :
    MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * (∑ i ∈ s, Ψ i) x) := by
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact integrable_finsetSum s h

/-- Integrability of a complex scalar multiple. -/
private lemma integrable_smul_loc {d : ℕ} (Θ : Work.BoseDict.Xn d → ℂ) (c : ℂ)
    (Ψ : Work.BoseDict.Xn d → ℂ)
    (h : MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * Ψ x)) :
    MeasureTheory.Integrable (fun x => (starRingEnd ℂ) (Θ x) * (c • Ψ) x) := by
  refine (h.const_mul c).congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- A real scalar acts on `ℂ`-valued functions as the corresponding complex scalar. -/
private lemma real_smul_pi_eq {α : Type*} (r : ℝ) (f : α → ℂ) : r • f = (r : ℂ) • f := by
  funext a
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]


/-- The doubly-updated point map is measurable in the state variable. -/
private lemma measurable_update_fixed2 {n : ℕ} (x : Work.BoseDict.Xn n) (i j : Fin n) (y : Ω) :
    Measurable (fun u : Ω => Function.update (Function.update x i y) j u) := by
  refine measurable_pi_iff.mpr (fun c => ?_)
  by_cases hcj : c = j
  · rw [hcj]
    have h : (fun u : Ω => Function.update (Function.update x i y) j u j)
        = fun u : Ω => u := by
      funext u; rw [Function.update_apply, if_pos rfl]
    rw [h]; exact measurable_id
  · have h : (fun u : Ω => Function.update (Function.update x i y) j u c)
        = fun _ : Ω => Function.update x i y c := by
      funext u; rw [Function.update_apply, if_neg hcj]
    rw [h]; exact measurable_const

/-- A finite sum commutes with a Bochner integral. -/
theorem sum_integral_comm {ι : Type} [DecidableEq ι] (Idx : Finset ι) {f : ι → Ω → ℂ}
    (h : ∀ p ∈ Idx, Integrable (f p)) :
    (∑ p ∈ Idx, ∫ u : Ω, f p u) = ∫ u : Ω, ∑ p ∈ Idx, f p u :=
  (MeasureTheory.integral_finsetSum Idx h).symm

/-- A finite double sum commutes with a Bochner integral. -/
theorem sum_sum_integral_comm {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (Idx : Finset ι) (Jdx : Finset κ) {f : ι → κ → Ω → ℂ}
    (h : ∀ p ∈ Idx, ∀ q ∈ Jdx, Integrable (f p q)) :
    (∑ p ∈ Idx, ∑ q ∈ Jdx, ∫ u : Ω, f p q u) = ∫ u : Ω, ∑ p ∈ Idx, ∑ q ∈ Jdx, f p q u := by
  rw [show (∑ p ∈ Idx, ∑ q ∈ Jdx, ∫ u : Ω, f p q u)
      = ∑ p ∈ Idx, ∫ u : Ω, ∑ q ∈ Jdx, f p q u from by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        exact (MeasureTheory.integral_finsetSum Jdx (fun q hq => h p hp q hq)).symm]
  rw [← MeasureTheory.integral_finsetSum _ (fun p hp =>
    integrable_finsetSum _ (fun q hq => h p hp q hq))]

/-- **The cubic `(s,k)`-sum of two-slot pairings, in kernel form** (the `etaOf` version).

For fixed distinct slots `i ≠ j` and a state `Θ`,

    `Σ_{p,q} a_{pq}·⟨slot composite⟩(x)  =  ∫_y ∫_u Σ_{p,q} a_{pq}·η_{w₁ p q}(x_i)η_{v₁ p q}(y)⁻
                                              η_{w₂ p q}(x_j)η_{v₂ p q}(u)⁻·Θ(x[i↦y][j↦u])`

i.e. the finite sum over the label set, the `y`-integral and the `u`-integral are interchanged. -/
theorem slotPairSum_eq_kernel {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (Idx : Finset ι) (Jdx : Finset κ)
    (a : ι → κ → ℂ) (w₁ v₁ w₂ v₂ : ι → κ → Fin m → ℝ)
    (Θ : Work.BoseDict.Xn n → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (i j : Fin n) (hij : i ≠ j) (x : Work.BoseDict.Xn n) :
    (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q • Work.BoseDict.boxSlotOf e (w₁ p q) (v₁ p q) i
        (Work.BoseDict.boxSlotOf e (w₂ p q) (v₂ p q) j Θ)) x
      = ∫ y : Ω, ∫ u : Ω, ∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u))))) := by
  classical
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  -- (0) the unfolded form of the summand
  have hunfold : ∀ (p : ι) (q : κ),
      (a p q • Work.BoseDict.boxSlotOf e (w₁ p q) (v₁ p q) i
        (Work.BoseDict.boxSlotOf e (w₂ p q) (v₂ p q) j Θ)) x
      = a p q * (Work.BoseDict.etaOf e (w₁ p q) (x i)
          * ∫ y : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ∫ u : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                    * Θ (Function.update (Function.update x i y) j u))) := by
    intro p q
    simp only [Pi.smul_apply, smul_eq_mul, Work.BoseDict.boxSlotOf, Function.update_apply,
      if_neg (Ne.symm hij)]
  -- (1) each summand equals the triple integral
  have hone : ∀ (p : ι) (q : κ),
      a p q * (Work.BoseDict.etaOf e (w₁ p q) (x i)
          * ∫ y : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ∫ u : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                    * Θ (Function.update (Function.update x i y) j u)))
      = ∫ y : Ω, ∫ u : Ω, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u))))) := by
    intro p q
    simp only [← MeasureTheory.integral_const_mul, mul_assoc]
  -- (2) integrability, u-level
  have hInt_u : ∀ (p : ι) (q : κ) (y : Ω),
      Integrable (fun u : Ω => a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u)))))) := by
    intro p q y
    have hFm : Measurable (fun u : Ω => a p q *
        (Work.BoseDict.etaOf e (w₁ p q) (x i)
          * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
            * (Work.BoseDict.etaOf e (w₂ p q) (x j)
              * Θ (Function.update (Function.update x i y) j u))))) :=
      (((hΘm.comp (measurable_update_fixed2 x i j y)).const_mul
        (Work.BoseDict.etaOf e (w₂ p q) (x j))).const_mul
        ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y))).const_mul
        (Work.BoseDict.etaOf e (w₁ p q) (x i)) |>.const_mul (a p q)
    refine (integrable_conjEtaOf_mul hmeas hbdd hsupp (v₂ p q) (F := fun u : Ω => a p q *
        (Work.BoseDict.etaOf e (w₁ p q) (x i)
          * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
            * (Work.BoseDict.etaOf e (w₂ p q) (x j)
              * Θ (Function.update (Function.update x i y) j u))))) hFm ?_).congr ?_
    · refine ⟨‖a p q‖ * (‖Work.BoseDict.etaOf e (w₁ p q) (x i)‖
        * (‖Work.BoseDict.etaOf e (v₁ p q) y‖ * (‖Work.BoseDict.etaOf e (w₂ p q) (x j)‖ * CΘ))),
        fun u => ?_⟩
      have h1 : ‖Θ (Function.update (Function.update x i y) j u)‖ ≤ CΘ := hCΘ _
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
        (norm_nonneg _)
    · filter_upwards with u
      ring
  -- (3) integrability, y-level
  have hInt_y : ∀ (p : ι) (q : κ),
      Integrable (fun y : Ω => ∫ u : Ω, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u)))))) := by
    intro p q
    obtain ⟨B, hB0, hB⟩ := Work.MB.etaOf_weak_bound hbdd (v₂ p q)
    have hFm : Measurable (fun y : Ω => a p q *
        (Work.BoseDict.etaOf e (w₁ p q) (x i)
          * (Work.BoseDict.etaOf e (w₂ p q) (x j)
            * ∫ u : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                * Θ (Function.update (Function.update x i y) j u)))) :=
      ((((measurable_integral_conjEtaOf_update hmeas (v₂ p q) Θ hΘm x i j).const_mul
        (Work.BoseDict.etaOf e (w₂ p q) (x j))).const_mul
        (Work.BoseDict.etaOf e (w₁ p q) (x i))).const_mul (a p q))
    have hFb : ∃ C : ℝ, ∀ y : Ω, ‖a p q *
        (Work.BoseDict.etaOf e (w₁ p q) (x i)
          * (Work.BoseDict.etaOf e (w₂ p q) (x j)
            * ∫ u : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                * Θ (Function.update (Function.update x i y) j u)))‖ ≤ C := by
      refine ⟨‖a p q‖ * (‖Work.BoseDict.etaOf e (w₁ p q) (x i)‖
          * (‖Work.BoseDict.etaOf e (w₂ p q) (x j)‖
            * (B * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal))),
          fun y => ?_⟩
      have h1 : ‖∫ u : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
          * Θ (Function.update (Function.update x i y) j u)‖
          ≤ B * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal :=
        norm_integral_conjEtaOf_mul_le hsupp (v₂ p q) hB (F := fun u : Ω =>
          Θ (Function.update (Function.update x i y) j u)) (fun u => hCΘ _)
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          (norm_nonneg _)) (norm_nonneg _)
    have hkey : (fun y : Ω => (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y) *
        (a p q * (Work.BoseDict.etaOf e (w₁ p q) (x i)
          * (Work.BoseDict.etaOf e (w₂ p q) (x j)
            * ∫ u : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                * Θ (Function.update (Function.update x i y) j u)))))
        = fun y : Ω => ∫ u : Ω, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u))))) := by
      funext y
      simp only [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      ring
    rw [← hkey]
    exact integrable_conjEtaOf_mul hmeas hbdd hsupp (v₁ p q)
      (F := fun y : Ω => a p q * (Work.BoseDict.etaOf e (w₁ p q) (x i)
        * (Work.BoseDict.etaOf e (w₂ p q) (x j)
          * ∫ u : Ω, (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
              * Θ (Function.update (Function.update x i y) j u)))) hFm hFb
  -- (4) the Finset moves
  calc (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q • Work.BoseDict.boxSlotOf e (w₁ p q) (v₁ p q) i
          (Work.BoseDict.boxSlotOf e (w₂ p q) (v₂ p q) j Θ)) x
      = ∑ p ∈ Idx, ∑ q ∈ Jdx, ∫ y : Ω, ∫ u : Ω, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u))))) := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [hunfold p q, hone p q]
    _ = ∑ p ∈ Idx, ∫ y : Ω, ∑ q ∈ Jdx, ∫ u : Ω, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u))))) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [← MeasureTheory.integral_finsetSum _ (fun q _ => hInt_y p q)]
    _ = ∫ y : Ω, ∑ p ∈ Idx, ∑ q ∈ Jdx, ∫ u : Ω, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u))))) :=
        sum_integral_comm Idx (fun p hp => integrable_finsetSum _ (fun q hq => hInt_y p q))
    _ = ∫ y : Ω, ∫ u : Ω, ∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u))))) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        exact sum_sum_integral_comm Idx Jdx (fun p hp q hq => hInt_u p q y)

/-- **The pin-form kernel identity of one channel.**

`cIPn` of a sum of two-slot composites (over a finite label set) equals the triple integral of the
*assembled* kernel, with the three pinning functions `W₁, V₁, W₂, V₂` in place of the mode
superpositions `η_{w₁}, η_{v₁}, η_{w₂}, η_{v₂}`. -/
theorem channel_pinKernelForm {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (Idx : Finset ι) (Jdx : Finset κ)
    (a : ι → κ → ℂ) (w₁ v₁ w₂ v₂ : ι → κ → Fin m → ℝ)
    (W₁ V₁ W₂ V₂ : ι → κ → Ω → ℂ)
    (hW₁ : ∀ᵐ z ∂(volume : Measure Ω), ∀ p ∈ Idx, ∀ q ∈ Jdx,
      Work.BoseDict.etaOf e (w₁ p q) z = W₁ p q z)
    (hV₁ : ∀ᵐ z ∂(volume : Measure Ω), ∀ p ∈ Idx, ∀ q ∈ Jdx,
      Work.BoseDict.etaOf e (v₁ p q) z = V₁ p q z)
    (hW₂ : ∀ᵐ z ∂(volume : Measure Ω), ∀ p ∈ Idx, ∀ q ∈ Jdx,
      Work.BoseDict.etaOf e (w₂ p q) z = W₂ p q z)
    (hV₂ : ∀ᵐ z ∂(volume : Measure Ω), ∀ p ∈ Idx, ∀ q ∈ Jdx,
      Work.BoseDict.etaOf e (v₂ p q) z = V₂ p q z)
    (Θ : Work.BoseDict.Xn n → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (i j : Fin n) (hij : i ≠ j) :
    Work.BoseDict.cIPn n Θ (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q •
        Work.BoseDict.boxSlotOf e (w₁ p q) (v₁ p q) i
          (Work.BoseDict.boxSlotOf e (w₂ p q) (v₂ p q) j Θ))
      = ∫ x : Work.BoseDict.Xn n, ∫ y : Ω, ∫ u : Ω, (starRingEnd ℂ) (Θ x) *
          (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
            (W₁ p q (x i) * (starRingEnd ℂ) (V₁ p q y) * W₂ p q (x j)
              * (starRingEnd ℂ) (V₂ p q u)))
          * Θ (Function.update (Function.update x i y) j u) := by
  have hA : Work.BoseDict.cIPn n Θ (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q •
        Work.BoseDict.boxSlotOf e (w₁ p q) (v₁ p q) i
          (Work.BoseDict.boxSlotOf e (w₂ p q) (v₂ p q) j Θ))
      = ∫ x : Work.BoseDict.Xn n, ∫ y : Ω, ∫ u : Ω, (starRingEnd ℂ) (Θ x) *
          (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
            (Work.BoseDict.etaOf e (w₁ p q) (x i) * (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * Work.BoseDict.etaOf e (w₂ p q) (x j) * (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)))
          * Θ (Function.update (Function.update x i y) j u) := by
    simp only [Work.BoseDict.cIPn]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    rw [slotPairSum_eq_kernel hmeas hbdd hsupp Idx Jdx a w₁ v₁ w₂ v₂ Θ hΘm hΘb i j hij x]
    simp only [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only []
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only []
    have hS : (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
          (Work.BoseDict.etaOf e (w₁ p q) (x i)
            * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * (Work.BoseDict.etaOf e (w₂ p q) (x j)
                * ((starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)
                  * Θ (Function.update (Function.update x i y) j u))))))
        = (∑ p ∈ Idx, ∑ q ∈ Jdx, a p q *
            (Work.BoseDict.etaOf e (w₁ p q) (x i) * (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₁ p q) y)
              * Work.BoseDict.etaOf e (w₂ p q) (x j) * (starRingEnd ℂ) (Work.BoseDict.etaOf e (v₂ p q) u)))
          * Θ (Function.update (Function.update x i y) j u) := by
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      refine Finset.sum_congr rfl (fun q hq => ?_)
      ring
    rw [hS]
    ring
  rw [hA]
  rw [kernelForm_pinSubst Idx Jdx a w₁ v₁ w₂ v₂ W₁ V₁ W₂ V₂ hW₁ hV₁ hW₂ hV₂ Θ i j]

/-- LOCAL COPY of the delegated reorganisation identity (complex-scalar form). -/
private theorem sum_smul_add_reorg_loc {ι κ η α : Type*}
    (Idx : Finset ι) (Jdx : Finset κ) (P : Finset η)
    (c : ι → κ → ℂ) (X Y : ι → κ → η → α → ℂ) :
    (∑ s ∈ Idx, ∑ k ∈ Jdx, c s k • ((∑ p ∈ P, X s k p) + (∑ p ∈ P, Y s k p)))
      = ∑ p ∈ P, ((∑ s ∈ Idx, ∑ k ∈ Jdx, c s k • X s k p)
          + (∑ s ∈ Idx, ∑ k ∈ Jdx, c s k • Y s k p)) := by
  funext x
  have hL : (∑ s ∈ Idx, ∑ k ∈ Jdx,
        c s k • ((∑ p ∈ P, X s k p) + (∑ p ∈ P, Y s k p))) x
      = (∑ u ∈ Idx ×ˢ Jdx, ∑ p ∈ P, c u.1 u.2 * X u.1 u.2 p x)
        + (∑ u ∈ Idx ×ˢ Jdx, ∑ p ∈ P, c u.1 u.2 * Y u.1 u.2 p x) := by
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.mul_sum,
      Finset.sum_add_distrib]
    rw [← Finset.sum_product (Idx) (Jdx) (fun u : ι × κ => ∑ p ∈ P, c u.1 u.2 * X u.1 u.2 p x)]
    rw [← Finset.sum_product (Idx) (Jdx) (fun u : ι × κ => ∑ p ∈ P, c u.1 u.2 * Y u.1 u.2 p x)]
  have hR : (∑ p ∈ P, ((∑ s ∈ Idx, ∑ k ∈ Jdx, c s k • X s k p)
        + (∑ s ∈ Idx, ∑ k ∈ Jdx, c s k • Y s k p))) x
      = (∑ p ∈ P, ∑ u ∈ Idx ×ˢ Jdx, c u.1 u.2 * X u.1 u.2 p x)
        + (∑ p ∈ P, ∑ u ∈ Idx ×ˢ Jdx, c u.1 u.2 * Y u.1 u.2 p x) := by
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [← Finset.sum_product (Idx) (Jdx) (fun u : ι × κ => c u.1 u.2 * X u.1 u.2 p x)]
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [← Finset.sum_product (Idx) (Jdx) (fun u : ι × κ => c u.1 u.2 * Y u.1 u.2 p x)]
  rw [hL, hR]
  congr 1
  · exact Finset.sum_comm
  · exact Finset.sum_comm

theorem cIPn_potCubic_kernelForm {n : ℕ} {v : ℝ³ → ℝ} {μ : ℝ}
    (HM : Work.BoseBoxFock.HonestModes v μ) {e : Fin HM.m → ℝ³ → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l)
      ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ))
    (horth : ∀ l l', (∫ z : ℝ³, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (c : ℂ) (hpin0 : e 0 =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.pinCond v μ c)
    (hpairF : ∀ (k : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m),
      (∫ z : ℝ³, star (e l z)
          * Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) z)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.f k l : ℝ) : ℂ))
    (hpairG : ∀ (s : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m), s ≠ 0 →
      (∫ z : ℝ³, star (e l z)
          * Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) z)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.g s l : ℝ) : ℂ))
    (PHs : Finset (Work.BoseBoxFock.Lab HM.N))
    (E : Work.BoseB7.Q3Env (Work.BoseBoxFock.Lab HM.N))
    (Theta : Work.BoseDict.Xn n → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ)) :
    Work.BoseDict.cIPn n Theta
        (Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) HM.f HM.g PHs E Theta)
      = (E.ell ^ (-(3 : ℝ))) •
          ∑ p ∈ Submission.BoseGases.pairSet n,
            ((∫ x : Work.BoseDict.Xn n, ∫ y : ℝ³, ∫ u : ℝ³,
                (starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
                  * (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N),
                      ∑ k ∈ PHs,
                        (E.fL s * E.W1 k)
                          * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ HM.N (s - k) y)
                          * Work.BoseBoxFock.pinTheta v μ HM.N s (x p.2)
                          * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ HM.N k u))
                  * Theta (Function.update (Function.update x p.1 y) p.2 u))
              + (∫ x : Work.BoseDict.Xn n, ∫ y : ℝ³, ∫ u : ℝ³,
                (starRingEnd ℂ) (Theta x)
                  * (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N),
                      ∑ k ∈ PHs,
                        (E.fL s * E.W1 k)
                          * Work.BoseBoxFock.pinQ v μ HM.N k (x p.1)
                          * (starRingEnd ℂ) (Work.BoseBoxFock.pinTheta v μ HM.N s y)
                          * Work.BoseBoxFock.pinQ v μ HM.N (s - k) (x p.2)
                          * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c u))
                  * Theta (Function.update (Function.update x p.1 y) p.2 u))) := by
  classical
  haveI : NeZero HM.m := HM.hm
  -- ## the pinning a.e. facts, restricted to the label sets
  have haeF : ∀ᵐ z ∂(volume : Measure Ω), ∀ i : Work.BoseBoxFock.Lab HM.N,
      Work.BoseDict.etaOf e (HM.f i) z = Work.BoseBoxFock.pinQ v μ HM.N i z :=
    Filter.eventually_all.2 (fun i => Work.BoseBoxFock.pinQ_etaOf HM horth hpairF hMemLp i)
  have haeCond : ∀ᵐ z ∂(volume : Measure Ω),
      Work.BoseDict.etaOf e (evec0 HM.m) z = Work.BoseBoxFock.pinCond v μ c z :=
    Work.BoseBoxFock.etaOf_evec0_eq_pinCond hpin0
  have haeG : ∀ᵐ z ∂(volume : Measure Ω),
      ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N),
        Work.BoseDict.etaOf e (HM.g s) z = Work.BoseBoxFock.pinTheta v μ HM.N s z :=
    (Filter.eventually_all_finset (Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N))).2
      (fun s hs => Work.BoseBoxFock.pinTheta_etaOf HM horth hpairG hMemLp s
        ((Finset.mem_erase.mp hs).1))
  have hae_w1_1 : ∀ᵐ z ∂(volume : Measure Ω),
      ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∀ k ∈ PHs,
        Work.BoseDict.etaOf e (evec0 HM.m) z = Work.BoseBoxFock.pinCond v μ c z :=
    haeCond.mono (fun z hz s hs k hk => hz)
  have hae_v1_1 : ∀ᵐ z ∂(volume : Measure Ω),
      ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∀ k ∈ PHs,
        Work.BoseDict.etaOf e (HM.f (s - k)) z = Work.BoseBoxFock.pinQ v μ HM.N (s - k) z :=
    haeF.mono (fun z hz s hs k hk => hz (s - k))
  have hae_w2_1 : ∀ᵐ z ∂(volume : Measure Ω),
      ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∀ k ∈ PHs,
        Work.BoseDict.etaOf e (HM.g s) z = Work.BoseBoxFock.pinTheta v μ HM.N s z :=
    haeG.mono (fun z hz s hs k hk => hz s hs)
  have hae_v2_1 : ∀ᵐ z ∂(volume : Measure Ω),
      ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∀ k ∈ PHs,
        Work.BoseDict.etaOf e (HM.f k) z = Work.BoseBoxFock.pinQ v μ HM.N k z :=
    haeF.mono (fun z hz s hs k hk => hz k)
  -- ## the integrability of the two four-letter atoms
  have hAt1 : ∀ (s k : Work.BoseBoxFock.Lab HM.N) (p : Fin n × Fin n),
      MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
        (starRingEnd ℂ) (Theta x) * Work.BoseDict.boxSlotOf e (evec0 HM.m) (HM.f (s - k)) p.1
          (Work.BoseDict.boxSlotOf e (HM.g s) (HM.f k) p.2 Theta) x) :=
    fun s k p => boxSlotOf_pair_integrable hmeas hbdd hsupp (evec0 HM.m) (HM.f (s - k))
      (HM.g s) (HM.f k) p.1 p.2 Theta hΘm hΘb hΘs
  have hAt2 : ∀ (s k : Work.BoseBoxFock.Lab HM.N) (p : Fin n × Fin n),
      MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
        (starRingEnd ℂ) (Theta x) * Work.BoseDict.boxSlotOf e (HM.f k) (HM.g s) p.1
          (Work.BoseDict.boxSlotOf e (HM.f (s - k)) (evec0 HM.m) p.2 Theta) x) :=
    fun s k p => boxSlotOf_pair_integrable hmeas hbdd hsupp (HM.f k) (HM.g s)
      (HM.f (s - k)) (evec0 HM.m) p.1 p.2 Theta hΘm hΘb hΘs
  have hI1 : ∀ p : Fin n × Fin n, MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
      (starRingEnd ℂ) (Theta x) *
        (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∑ k ∈ PHs,
          ((E.fL s * E.W1 k : ℝ) : ℂ) •
            Work.BoseDict.boxSlotOf e (evec0 HM.m) (HM.f (s - k)) p.1
              (Work.BoseDict.boxSlotOf e (HM.g s) (HM.f k) p.2 Theta)) x) := by
    intro p
    exact integrable_finset_sum_loc _ _ _ (fun s hs => integrable_finset_sum_loc _ _ _
      (fun k hk => integrable_smul_loc Theta (((E.fL s * E.W1 k : ℝ) : ℂ)) _ (hAt1 s k p)))
  have hI2 : ∀ p : Fin n × Fin n, MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
      (starRingEnd ℂ) (Theta x) *
        (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∑ k ∈ PHs,
          ((E.fL s * E.W1 k : ℝ) : ℂ) •
            Work.BoseDict.boxSlotOf e (HM.f k) (HM.g s) p.1
              (Work.BoseDict.boxSlotOf e (HM.f (s - k)) (evec0 HM.m) p.2 Theta)) x) := by
    intro p
    exact integrable_finset_sum_loc _ _ _ (fun s hs => integrable_finset_sum_loc _ _ _
      (fun k hk => integrable_smul_loc Theta (((E.fL s * E.W1 k : ℝ) : ℂ)) _ (hAt2 s k p)))
  have hIAdd : ∀ p : Fin n × Fin n, MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
      (starRingEnd ℂ) (Theta x) *
        (((∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∑ k ∈ PHs,
              ((E.fL s * E.W1 k : ℝ) : ℂ) •
                Work.BoseDict.boxSlotOf e (evec0 HM.m) (HM.f (s - k)) p.1
                  (Work.BoseDict.boxSlotOf e (HM.g s) (HM.f k) p.2 Theta))
            + (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∑ k ∈ PHs,
              ((E.fL s * E.W1 k : ℝ) : ℂ) •
                Work.BoseDict.boxSlotOf e (HM.f k) (HM.g s) p.1
                  (Work.BoseDict.boxSlotOf e (HM.f (s - k)) (evec0 HM.m) p.2 Theta))) x)) := by
    intro p
    refine ((hI1 p).add (hI2 p)).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.add_apply]
    ring
  -- ## the pairSet expansion of `potCubic`
  rw [cIPn_potCubic_eq_pairSet_gen (n := n) (e := e) hmeas hbdd hsupp horth HM.f HM.g PHs E
    Theta hΘm hΘb]
  rw [cIPn_smul_loc]
  congr 1
  -- ## normalise the real scalar multiplications to complex ones
  simp only [real_smul_pi_eq]
  -- ## reorder: the `(s,k)`-sum goes inside the `pairSet`-sum
  rw [sum_smul_add_reorg_loc]
  -- ## pull the `pairSet`-sum out of `cIPn`
  rw [cIPn_finset_sum_loc (Submission.BoseGases.pairSet n) Theta _ (fun p hp => hIAdd p)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  -- ## split the two channels
  rw [cIPn_add_loc Theta _ _ (hI1 p) (hI2 p)]
  congr 1
  · -- ## channel 1
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    rw [channel_pinKernelForm (n := n) (ℓ := Work.BoseBoxFock.ellH v μ) hmeas hbdd hsupp
      (Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N)) PHs
      (fun s k => (((E.fL s * E.W1 k : ℝ)) : ℂ))
      (fun _ _ => evec0 HM.m) (fun s k => HM.f (s - k)) (fun s k => HM.g s) (fun s k => HM.f k)
      (fun _ _ => Work.BoseBoxFock.pinCond v μ c)
      (fun s k => Work.BoseBoxFock.pinQ v μ HM.N (s - k))
      (fun s k => Work.BoseBoxFock.pinTheta v μ HM.N s)
      (fun s k => Work.BoseBoxFock.pinQ v μ HM.N k)
      hae_w1_1 hae_v1_1 hae_w2_1 hae_v2_1 Theta hΘm hΘb p.1 p.2 hij]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only []
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only []
    have hS2 : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∑ k ∈ PHs,
          (((E.fL s * E.W1 k : ℝ)) : ℂ) *
            (Work.BoseBoxFock.pinCond v μ c (x p.1)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ HM.N (s - k) y)
              * Work.BoseBoxFock.pinTheta v μ HM.N s (x p.2)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ HM.N k u)))
        = Work.BoseBoxFock.pinCond v μ c (x p.1) *
          (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∑ k ∈ PHs,
            (E.fL s : ℂ) * (E.W1 k : ℂ)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ HM.N (s - k) y)
              * Work.BoseBoxFock.pinTheta v μ HM.N s (x p.2)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ HM.N k u)) := by
      simp only [Complex.ofReal_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      refine Finset.sum_congr rfl (fun k hk => ?_)
      ring
    rw [hS2]
    ring
  · -- ## channel 2
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    rw [channel_pinKernelForm (n := n) (ℓ := Work.BoseBoxFock.ellH v μ) hmeas hbdd hsupp
      (Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N)) PHs
      (fun s k => (((E.fL s * E.W1 k : ℝ)) : ℂ))
      (fun s k => HM.f k) (fun s k => HM.g s) (fun s k => HM.f (s - k)) (fun _ _ => evec0 HM.m)
      (fun s k => Work.BoseBoxFock.pinQ v μ HM.N k)
      (fun s k => Work.BoseBoxFock.pinTheta v μ HM.N s)
      (fun s k => Work.BoseBoxFock.pinQ v μ HM.N (s - k))
      (fun _ _ => Work.BoseBoxFock.pinCond v μ c)
      hae_v2_1 hae_w2_1 hae_v1_1 hae_w1_1 Theta hΘm hΘb p.1 p.2 hij]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only []
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only []
    have hS4 : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∑ k ∈ PHs,
          (((E.fL s * E.W1 k : ℝ)) : ℂ) *
            (Work.BoseBoxFock.pinQ v μ HM.N k (x p.1)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinTheta v μ HM.N s y)
              * Work.BoseBoxFock.pinQ v μ HM.N (s - k) (x p.2)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c u)))
        = (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab HM.N), ∑ k ∈ PHs,
            (E.fL s : ℂ) * (E.W1 k : ℂ)
              * Work.BoseBoxFock.pinQ v μ HM.N k (x p.1)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinTheta v μ HM.N s y)
              * Work.BoseBoxFock.pinQ v μ HM.N (s - k) (x p.2)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c u)) := by
      simp only [Complex.ofReal_mul]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      refine Finset.sum_congr rfl (fun k hk => ?_)
      ring
    rw [hS4]

end Work.BoseBoxFock
