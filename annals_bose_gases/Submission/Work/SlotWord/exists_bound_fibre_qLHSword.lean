import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.exists_bound_fibre_qLHSword`

**(R3) — the uniform-in-`y` bound on the fibre `qLHSword`.**

For a state `Ψ` bounded by `C` on the ambient box `abox N L`, kernels `w`, `w1` bounded
(`|w| ≤ Cw` everywhere, `|w1| ≤ Cw1` on the centred cube `acube L`), every slot set `S` and every
relabelling `e`, the potential word of the *fibre* of the slot piece,

  `y ↦ qLHSword (N := S.card) L μ w w1 (slotFibreState S e (slotPiece A S Ψ) y)`,

is bounded **uniformly** over the outside configurations `y ∈ slotOutside L A S`.

The proof is the bounded-on-a-finite-measure-set argument, read at the fibre:

* on `abox (S.card) L` the fibre is the slot piece evaluated at
  `slotComb S (x ∘ e) y`, a configuration that lies in `abox N L` because `x` is in the `k`-box and
  every `y j` is in `acube L` (`mem_slotOutside_iff`); hence `|fibre x| ≤ C` there, either from
  `hΨb` (on the slot set) or trivially (off it);
* the one-body fibre `w1Fibre L w1 (x i) = ∫_{acube L} w1 (x i) ·` is bounded by
  `Cw1⁺ · |acube L|` (`norm_setIntegral_le_of_norm_le_const`), the ordered-pair sum by
  `N² · Cw⁺`, so `|qLHSden k L μ w w1| ≤ |μ|·k·(Cw1⁺|acube L|) + ½·k²·Cw⁺`;
* `norm_setIntegral_le_of_norm_le_const` on `abox (S.card) L` then bounds the integral.
-/

noncomputable section

set_option linter.unusedVariables false

open MeasureTheory

namespace Work.SlotWord

open Work.PerSector
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem exists_bound_fibre_qLHSword {N : ℕ} (L μ : ℝ) (hL : 0 < L)
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAc : A ⊆ Submission.BoseGases.acube L)
    (S : Finset (Fin N)) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {Ψ : Submission.BoseGases.X N → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N L, |Ψ x| ≤ C)
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    {Cw Cw1 : ℝ}
    (hw : ∀ x y : EuclideanSpace ℝ (Fin 3), |w x y| ≤ Cw)
    (hw1 : ∀ x : EuclideanSpace ℝ (Fin 3), ∀ y ∈ Submission.BoseGases.acube L, |w1 x y| ≤ Cw1) :
    ∃ K : ℝ, ∀ y ∈ Work.PerSector.slotOutside L A S,
      |Submission.BoseGases.qLHSword (N := S.card) L μ w w1
        (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y)| ≤ K := by
  classical
  set V : ℝ := (volume : Measure ℝ³).real (Submission.BoseGases.acube L) with hVdef
  have hVnn : 0 ≤ V := by rw [hVdef]; exact MeasureTheory.measureReal_nonneg
  set Cw' : ℝ := max Cw 0 with hCw'def
  set Cw1' : ℝ := max Cw1 0 with hCw1'def
  have hCw'nn : 0 ≤ Cw' := by rw [hCw'def]; exact le_max_right _ _
  have hCw1'nn : 0 ≤ Cw1' := by rw [hCw1'def]; exact le_max_right _ _
  have hCwle : ∀ x y : ℝ³, |w x y| ≤ Cw' := fun x y =>
    le_trans (hw x y) (by rw [hCw'def]; exact le_max_left Cw 0)
  have hCw1le : ∀ x : ℝ³, ∀ y ∈ Submission.BoseGases.acube L, |w1 x y| ≤ Cw1' := fun x y hy =>
    le_trans (hw1 x y hy) (by rw [hCw1'def]; exact le_max_left Cw1 0)
  -- ### the one-body fibre `x ↦ ∫_{acube L} w1 (x i) y`
  have hw1F_bound (i : Fin S.card) (x : Submission.BoseGases.X S.card) :
      |Submission.BoseGases.w1Fibre L w1 (x i)| ≤ Cw1' * V := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³))
      (s := Submission.BoseGases.acube L) (f := fun y : ℝ³ => w1 (x i) y) (C := Cw1')
      (Submission.BoseGases.acube_lt_top L (le_of_lt hL))
      (fun y hy => by rw [Real.norm_eq_abs]; exact hCw1le (x i) y hy)
    simpa [Submission.BoseGases.w1Fibre, hVdef] using h
  have hsum1 (x : Submission.BoseGases.X S.card) :
      |∑ i : Fin S.card, Submission.BoseGases.w1Fibre L w1 (x i)|
        ≤ (S.card : ℝ) * (Cw1' * V) := by
    calc |∑ i : Fin S.card, Submission.BoseGases.w1Fibre L w1 (x i)|
        ≤ ∑ i : Fin S.card, |Submission.BoseGases.w1Fibre L w1 (x i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin S.card, Cw1' * V := Finset.sum_le_sum (fun i _ => hw1F_bound i x)
      _ = (S.card : ℝ) * (Cw1' * V) := by rw [Finset.sum_const, nsmul_eq_mul]; simp
  -- ### the ordered-pair sum
  have hpair_card : (Submission.BoseGases.pairSet S.card).card ≤ S.card * S.card := by
    calc (Submission.BoseGases.pairSet S.card).card
        ≤ (Finset.univ : Finset (Fin S.card × Fin S.card)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card (Fin S.card × Fin S.card) := Finset.card_univ
      _ = S.card * S.card := by simp [Fintype.card_prod]
  have hpair_cardR : ((Submission.BoseGases.pairSet S.card).card : ℝ) ≤ (S.card : ℝ) ^ 2 := by
    have h : ((Submission.BoseGases.pairSet S.card).card : ℝ) ≤ ((S.card * S.card : ℕ) : ℝ) :=
      Nat.cast_le.mpr hpair_card
    simpa [Nat.cast_mul, pow_two] using h
  have hsum2 (x : Submission.BoseGases.X S.card) :
      |∑ p ∈ Submission.BoseGases.pairSet S.card, w (x p.1) (x p.2)| ≤ (S.card : ℝ) ^ 2 * Cw' := by
    calc |∑ p ∈ Submission.BoseGases.pairSet S.card, w (x p.1) (x p.2)|
        ≤ ∑ p ∈ Submission.BoseGases.pairSet S.card, |w (x p.1) (x p.2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ Submission.BoseGases.pairSet S.card, Cw' :=
          Finset.sum_le_sum (fun p _ => hCwle (x p.1) (x p.2))
      _ = ((Submission.BoseGases.pairSet S.card).card : ℝ) * Cw' := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.card : ℝ) ^ 2 * Cw' := mul_le_mul_of_nonneg_right hpair_cardR hCw'nn
  -- ### the density bound
  set B : ℝ := |μ| * ((S.card : ℝ) * (Cw1' * V)) + (1 / 2 : ℝ) * ((S.card : ℝ) ^ 2 * Cw')
    with hBdef
  have hq_bound (x : Submission.BoseGases.X S.card) :
      |Submission.BoseGases.qLHSden (S.card) L μ w w1 x| ≤ B := by
    have hq : Submission.BoseGases.qLHSden (S.card) L μ w w1 x
        = - μ * (∑ i : Fin S.card, Submission.BoseGases.w1Fibre L w1 (x i))
          + (1 / 2 : ℝ) * (∑ p ∈ Submission.BoseGases.pairSet S.card, w (x p.1) (x p.2)) :=
      rfl
    rw [hq, hBdef]
    calc |- μ * (∑ i : Fin S.card, Submission.BoseGases.w1Fibre L w1 (x i))
              + (1 / 2 : ℝ) * (∑ p ∈ Submission.BoseGases.pairSet S.card, w (x p.1) (x p.2))|
        ≤ |- μ * (∑ i : Fin S.card, Submission.BoseGases.w1Fibre L w1 (x i))|
          + |(1 / 2 : ℝ)
              * (∑ p ∈ Submission.BoseGases.pairSet S.card, w (x p.1) (x p.2))| :=
          abs_add_le _ _
      _ = |μ| * |∑ i : Fin S.card, Submission.BoseGases.w1Fibre L w1 (x i)|
          + (1 / 2 : ℝ)
              * |∑ p ∈ Submission.BoseGases.pairSet S.card, w (x p.1) (x p.2)| := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ |μ| * ((S.card : ℝ) * (Cw1' * V)) + (1 / 2 : ℝ) * ((S.card : ℝ) ^ 2 * Cw') :=
          add_le_add (mul_le_mul_of_nonneg_left (hsum1 x) (abs_nonneg μ))
                     (mul_le_mul_of_nonneg_left (hsum2 x) (by norm_num))
  -- ### the answer
  refine ⟨C ^ 2 * B * ((volume : Measure (Submission.BoseGases.X S.card)).real
      (Submission.BoseGases.abox (S.card) L)), ?_⟩
  intro y hy
  have hyc : ∀ j : SlotOut N S, y j ∈ Submission.BoseGases.acube L :=
    (Work.PerSector.mem_slotOutside_iff.mp hy).1
  have hfib : ∀ x ∈ Submission.BoseGases.abox (S.card) L,
      |Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y x| ≤ C := by
    intro x hx
    rw [Work.PerSector.slotFibreState_apply]
    have hz : Work.PerSector.slotComb S (fun i : SlotIn N S => x (e i)) y
        ∈ Submission.BoseGases.abox N L := by
      rw [Submission.BoseGases.mem_abox_iff]
      intro i
      by_cases hi : i ∈ S
      · rw [Work.PerSector.slotComb_apply, dif_pos hi]
        exact (Submission.BoseGases.mem_abox_iff (S.card) L x).mp hx (e ⟨i, hi⟩)
      · rw [Work.PerSector.slotComb_apply, dif_neg hi]
        exact hyc ⟨i, hi⟩
    by_cases hmem : Work.PerSector.slotComb S (fun i : SlotIn N S => x (e i)) y
        ∈ Work.PerSector.slotSet A S
    · rw [Work.PerSector.slotPiece, Set.indicator_of_mem hmem]
      exact hΨb _ hz
    · rw [Work.PerSector.slotPiece, Set.indicator_of_notMem hmem, abs_zero]
      exact hC
  have hbound : ∀ x ∈ Submission.BoseGases.abox (S.card) L,
      ‖(Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y x) ^ 2
          * Submission.BoseGases.qLHSden (S.card) L μ w w1 x‖ ≤ C ^ 2 * B := by
    intro x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hfx := hfib x hx
    have hfx2 : (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y x) ^ 2
        ≤ C ^ 2 := by
      calc (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y x) ^ 2
          = |Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y x| ^ 2 :=
            (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfx 2
    exact mul_le_mul hfx2 (hq_bound x) (abs_nonneg _) (sq_nonneg C)
  have hEq : Submission.BoseGases.qLHSword (N := S.card) L μ w w1
        (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y)
      = ∫ x in Submission.BoseGases.abox (S.card) L,
          (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y x) ^ 2
            * Submission.BoseGases.qLHSden (S.card) L μ w w1 x := by
    simp only [Submission.BoseGases.qLHSword, Submission.BoseGases.qLHSden]
  calc |Submission.BoseGases.qLHSword (N := S.card) L μ w w1
          (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y)|
      = |∫ x in Submission.BoseGases.abox (S.card) L,
          (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y x) ^ 2
            * Submission.BoseGases.qLHSden (S.card) L μ w w1 x| := by rw [hEq]
    _ ≤ (C ^ 2 * B) * ((volume : Measure (Submission.BoseGases.X S.card)).real
          (Submission.BoseGases.abox (S.card) L)) := by
        simpa using MeasureTheory.norm_setIntegral_le_of_norm_le_const
          (μ := (volume : Measure (Submission.BoseGases.X S.card)))
          (s := Submission.BoseGases.abox (S.card) L) (C := C ^ 2 * B)
          (Submission.BoseGases.abox_lt_top (S.card) L (le_of_lt hL)) hbound
    _ = C ^ 2 * B * ((volume : Measure (Submission.BoseGases.X S.card)).real
          (Submission.BoseGases.abox (S.card) L)) := rfl

end Work.SlotWord
