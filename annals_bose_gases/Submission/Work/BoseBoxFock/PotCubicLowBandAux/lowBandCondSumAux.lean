import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.annCommSelf
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.cIPn_boxAnnOf_self_pair
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.cIPn_evecZero_boxAnnOf_le
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotBesselExcited
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PotCubicLowBandAux

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Elementary bridges : `boxPow ↔ abox`, the real part of `cIPn` -/

/-- For a positive side length the `n`-particle box support `boxPow n ℓ` is the configuration
box `abox n ℓ` of the corpus. -/
theorem boxPow_eq_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.MB.boxPow n ℓ = Submission.BoseGases.abox n ℓ := by
  unfold Work.MB.boxPow
  rw [Submission.BoseGases.abox_eq_pi_acube, Work.BoseBoxFock.boxL_eq_acube hℓ]

/-- A box-supported state is `abox`-supported. -/
theorem support_abox_of_boxPow {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : Work.BoseDict.Xn n → ℂ}
    (h : Function.support f ⊆ Work.MB.boxPow n ℓ) :
    Function.support f ⊆ Submission.BoseGases.abox n ℓ :=
  h.trans (le_of_eq (boxPow_eq_abox (n := n) hℓ))

/-- The real part of the `n`-body pairing is the integral of the real part. -/
theorem cIPn_re_eq_integral {n : ℕ} {f g : Work.BoseDict.Xn n → ℂ}
    (h : Integrable (fun x => star (f x) * g x)) :
    (Work.BoseDict.cIPn n f g).re = ∫ x, (star (f x) * g x).re := by
  rw [Work.BoseDict.cIPn]
  exact (ContinuousLinearMap.integral_comp_comm Complex.reCLM h).symm

/-- The complex product `star Θ · boxSlotSum e T Θ` is integrable for an `abox`-supported
bounded state `Θ`. -/
theorem integrable_star_boxSlotSum_complex {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Θ : Work.BoseDict.Xn d → ℂ}
    (hΘm : Measurable Θ) {CΘ : ℝ} (hΘb : ∀ x, ‖Θ x‖ ≤ CΘ)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ) :
    Integrable (fun x : Work.BoseDict.Xn d => star (Θ x) * Work.BoseDict.boxSlotSum e T Θ x) := by
  obtain ⟨hSm, K, hKb⟩ :=
    Work.MB.boxSlotSum_measurable_bounded_ae (d := d) hmeas hbdd hsupp T Θ hΘm ⟨CΘ, hΘb⟩
  have hCΘ0 : 0 ≤ CΘ := le_trans (norm_nonneg _) (hΘb 0)
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hKb 0)
  refine Work.MB.integrable_of_bdd_of_support (S := Submission.BoseGases.abox d ℓ)
    (C := CΘ * K) (Submission.BoseGases.abox_measurable d ℓ)
    (volume_abox_ne_top d ℓ) ?_ ?_ ?_
  · exact ((Complex.continuous_conj.measurable.comp hΘm).mul hSm).aestronglyMeasurable
  · intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul (hΘb x) (hKb x) (norm_nonneg _) hCΘ0
  · intro x hx
    have h0 : Θ x = 0 := by
      by_contra h
      exact hx (hΘsupp (Function.mem_support.mpr h))
    rw [h0, star_zero, zero_mul]

/-! ## 1. The one-index Bessel inequality for the box annihilation

For a frame `f : ι → Fin m → ℝ` of box modes, the sum of the squared norms of the box
annihilations is controlled by `C` times the excited count of `Θ`:

    `Σ_k ‖a_{f k} Θ‖² ≤ C · ⟪Θ, boxSlotSum e (boxT0 m) Θ⟫` .

This is the second-quantised form of the frame bound `Σ_k |f_k⟩⟨f_k| ≤ C (1 − |e_0⟩⟨e_0|)`
(`f k 0 = 0` says the frame vectors are orthogonal to the condensate `e_0`).  The proof
converts each squared norm into a slot pairing through `cIPn_boxAnnOf_self_pair`, sums with
the linearity of `boxSlotSum` in the one-body operator, and applies the slotwise
`slotBesselExcited`.

The slotwise auxiliary lemma `slotBesselExcited` is stated for index sets in `Type`, so the
proof first transports the frame along `Fintype.equivFin ι : ι ≃ Fin (card ι)`. -/

theorem besselAnnAux {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Fin m → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ k : ι, f k 0 = 0)
    {Θ : Work.BoseDict.Xn (d + 1) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 1) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)),
      Θ (x ∘ σ) = Θ x) :
    (∑ k : ι, (Work.BoseDict.cIPn d
        (Work.BoseDict.boxAnnOf e (f k) d Θ)
        (Work.BoseDict.boxAnnOf e (f k) d Θ)).re)
      ≤ C * (Work.BoseDict.cIPn (d + 1) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re := by
  classical
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hΘb' : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := ⟨CΘ, hCΘ⟩
  have hΘabox : Function.support Θ ⊆ Submission.BoseGases.abox (d + 1) ℓ :=
    support_abox_of_boxPow hℓ hΘsupp
  -- the modes are `L^∞`
  have hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤ := fun l => by
    obtain ⟨Cl, hCl⟩ := hbdd l
    exact memLp_top_of_bound (hmeas l).aestronglyMeasurable Cl
      (Filter.Eventually.of_forall hCl)
  -- transport the frame along `ι ≃ Fin (card ι)` (the slotwise lemma lives in `Type`)
  set f' : Fin (Fintype.card ι) → Fin m → ℝ := fun i => f ((Fintype.equivFin ι).symm i) with hf'
  have hframe' : ∀ w : Fin m → ℝ,
      ∑ i : Fin (Fintype.card ι), (Work.BoseB4.gram (f' i) w) ^ 2
        ≤ C * ∑ l : Fin m, (w l) ^ 2 := by
    intro w
    rw [← Fintype.sum_equiv (Fintype.equivFin ι)
      (fun k : ι => (Work.BoseB4.gram (f k) w) ^ 2)
      (fun i : Fin (Fintype.card ι) => (Work.BoseB4.gram (f' i) w) ^ 2)
      (fun k => by simp [hf'])]
    exact hframe w
  have h0' : ∀ i : Fin (Fintype.card ι), f' i 0 = 0 := fun i => h0 _
  -- rewrite the frame sum as a sum over `Fin (card ι)`
  rw [Fintype.sum_equiv (Fintype.equivFin ι)
    (fun k : ι => (Work.BoseDict.cIPn d
        (Work.BoseDict.boxAnnOf e (f k) d Θ)
        (Work.BoseDict.boxAnnOf e (f k) d Θ)).re)
    (fun i : Fin (Fintype.card ι) => (Work.BoseDict.cIPn d
        (Work.BoseDict.boxAnnOf e (f' i) d Θ)
        (Work.BoseDict.boxAnnOf e (f' i) d Θ)).re)
    (fun k => by simp [hf'])]
  -- each squared norm is the slot pairing of the rank-one operator
  have hpair : ∀ k : Fin (Fintype.card ι),
      Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (f' k) d Θ)
          (Work.BoseDict.boxAnnOf e (f' k) d Θ)
        = Work.BoseDict.cIPn (d + 1) Θ
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ) :=
    fun k => cIPn_boxAnnOf_self_pair hmeas hbdd hsupp hMemLp (f' k) (f' k) hΘm hCΘ
      hΘsupp hΘsym
  -- linearity of `boxSlotSum` in the one-body operator
  have hlin : Work.BoseDict.boxSlotSum e
        (∑ k : Fin (Fintype.card ι), Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ
      = ∑ k : Fin (Fintype.card ι),
          Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ := by
    calc Work.BoseDict.boxSlotSum e
          (∑ k : Fin (Fintype.card ι), Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ
        = ∑ j : Fin (d + 1), slotJ e
            (∑ k : Fin (Fintype.card ι), Work.BoseBoxFock.rankOnePair (f' k) (f' k)) j Θ :=
          boxSlotSum_eq_sum_slotJ e _ Θ
      _ = ∑ j : Fin (d + 1), ∑ k : Fin (Fintype.card ι),
            slotJ e (Work.BoseBoxFock.rankOnePair (f' k) (f' k)) j Θ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [slotJ_finset_sum]
      _ = ∑ k : Fin (Fintype.card ι), ∑ j : Fin (d + 1),
            slotJ e (Work.BoseBoxFock.rankOnePair (f' k) (f' k)) j Θ := Finset.sum_comm
      _ = ∑ k : Fin (Fintype.card ι),
            Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [boxSlotSum_eq_sum_slotJ]
  -- integrability of every summand
  have hIntC : ∀ T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ),
      Integrable (fun x : Work.BoseDict.Xn (d + 1) =>
        star (Θ x) * Work.BoseDict.boxSlotSum e T Θ x) :=
    fun T => integrable_star_boxSlotSum_complex hmeas hbdd hsupp T hΘm hCΘ hΘabox
  -- the frame sum is the slot pairing of the frame operator
  have hpairInt : ∀ k : Fin (Fintype.card ι),
      (Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e (f' k) d Θ)
          (Work.BoseDict.boxAnnOf e (f' k) d Θ)).re
        = ∫ x : Work.BoseDict.Xn (d + 1), (star (Θ x) *
            Work.BoseDict.boxSlotSum e
              (Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ x).re := by
    intro k
    rw [hpair k]
    exact cIPn_re_eq_integral (hIntC (Work.BoseBoxFock.rankOnePair (f' k) (f' k)))
  have hleft : (∑ k : Fin (Fintype.card ι), (Work.BoseDict.cIPn d
        (Work.BoseDict.boxAnnOf e (f' k) d Θ)
        (Work.BoseDict.boxAnnOf e (f' k) d Θ)).re)
      = (Work.BoseDict.cIPn (d + 1) Θ
          (Work.BoseDict.boxSlotSum e
            (∑ k : Fin (Fintype.card ι),
              Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ)).re := by
    rw [Finset.sum_congr rfl (fun k _ => hpairInt k)]
    rw [show (Work.BoseDict.cIPn (d + 1) Θ
          (Work.BoseDict.boxSlotSum e
            (∑ k : Fin (Fintype.card ι),
              Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ)).re
        = ∫ x : Work.BoseDict.Xn (d + 1), (star (Θ x) *
            Work.BoseDict.boxSlotSum e
              (∑ k : Fin (Fintype.card ι),
                Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ x).re
        from cIPn_re_eq_integral (hIntC _)]
    rw [← integral_finsetSum Finset.univ (fun k _ =>
      integrable_star_boxSlotSum hmeas hbdd hsupp
        (Work.BoseBoxFock.rankOnePair (f' k) (f' k)) hΘm hΘb' hΘabox)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    rw [← Complex.re_sum]
    congr 1
    rw [hlin, Finset.sum_apply, Finset.mul_sum]
  rw [hleft]
  -- the two pairing integrals over the box
  have hbess := slotBesselExcited hmeas hbdd hsupp horth f' C hC hframe' h0' hΘm hΘb' hΘabox
  have hsetL : (∫ x in Submission.BoseGases.abox (d + 1) ℓ,
      (star (Θ x) * Work.BoseDict.boxSlotSum e
        (∑ k : Fin (Fintype.card ι),
          Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ x).re)
      = (Work.BoseDict.cIPn (d + 1) Θ
          (Work.BoseDict.boxSlotSum e
            (∑ k : Fin (Fintype.card ι),
              Work.BoseBoxFock.rankOnePair (f' k) (f' k)) Θ)).re := by
    rw [setIntegral_eq_integral_of_support_subset
      (Submission.BoseGases.abox_measurable (d + 1) ℓ)
      (support_star_boxSlotSum_subset _ hΘabox)]
    exact (cIPn_re_eq_integral (hIntC _)).symm
  have hsetR : (∫ x in Submission.BoseGases.abox (d + 1) ℓ,
      (star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x).re)
      = (Work.BoseDict.cIPn (d + 1) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re := by
    rw [setIntegral_eq_integral_of_support_subset
      (Submission.BoseGases.abox_measurable (d + 1) ℓ)
      (support_star_boxSlotSum_subset _ hΘabox)]
    exact (cIPn_re_eq_integral (hIntC _)).symm
  rw [← hsetL, ← hsetR]
  exact hbess

/-! ## 2. The condensate sum of the low band -/

theorem lowBandCondSumAux {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Fin m → ℝ)
    (C_θ : ℝ) (hC_θ : 0 ≤ C_θ)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ s : ι, (Work.BoseB4.gram (g s) w) ^ 2 ≤ C_θ * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ s : ι, g s 0 = 0)
    {Θ : Work.BoseDict.Xn (n + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (n + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (n + 2))) (x : Work.BoseDict.Xn (n + 2)),
      Θ (x ∘ σ) = Θ x) :
    (∑ s : ι,
        (Work.BoseDict.cIPn n
          (Work.BoseDict.boxAnnOf e (g s) n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (n + 1) Θ))
          (Work.BoseDict.boxAnnOf e (g s) n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (n + 1) Θ))).re)
      ≤ C_θ * ((n : ℝ) + 2) * (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re := by
  classical
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hΘb' : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := ⟨CΘ, hCΘ⟩
  have hΘW : Work.BoseBoxFock.WRegG ℓ Θ := ⟨hΘm, hΘb', hΘsupp⟩
  have hφW : ∀ s : ι, Work.BoseBoxFock.WRegG ℓ
      (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ) := fun s =>
    Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp (g s) hΘW
  -- the two annihilations commute
  have hcomm : ∀ s : ι,
      Work.BoseDict.boxAnnOf e (g s) n
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (n + 1) Θ)
        = Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) n
          (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ) :=
    fun s => annCommSelf hmeas hbdd hsupp (g s) (Work.BoseB4.evec m 0) hΘm hΘb'
      hΘsupp hΘsym
  -- the per-`s` annihilation bound
  have hper : ∀ s : ι,
      (Work.BoseDict.cIPn n
          (Work.BoseDict.boxAnnOf e (g s) n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (n + 1) Θ))
          (Work.BoseDict.boxAnnOf e (g s) n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (n + 1) Θ))).re
        ≤ ((n : ℝ) + 2) *
          (Work.BoseDict.cIPn (n + 1) (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ)
            (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ)).re := by
    intro s
    rw [hcomm s]
    exact cIPn_evecZero_boxAnnOf_le hmeas hbdd hsupp horth
      (hφW s).meas (hφW s).bdd (hφW s).supp
  -- the frame bound in annihilation form
  have hbessel : (∑ s : ι, (Work.BoseDict.cIPn (n + 1)
        (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ)
        (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ)).re)
      ≤ C_θ * (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re :=
    besselAnnAux hℓ hmeas hbdd hsupp horth g C_θ hC_θ hframe h0 hΘm hΘb' hΘsupp hΘsym
  calc (∑ s : ι,
        (Work.BoseDict.cIPn n
          (Work.BoseDict.boxAnnOf e (g s) n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (n + 1) Θ))
          (Work.BoseDict.boxAnnOf e (g s) n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (n + 1) Θ))).re)
      ≤ ∑ s : ι, ((n : ℝ) + 2) *
          (Work.BoseDict.cIPn (n + 1) (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ)
            (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ)).re :=
        Finset.sum_le_sum (fun s _ => hper s)
    _ = ((n : ℝ) + 2) * ∑ s : ι,
          (Work.BoseDict.cIPn (n + 1) (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ)
            (Work.BoseDict.boxAnnOf e (g s) (n + 1) Θ)).re := by
        rw [Finset.mul_sum]
    _ ≤ ((n : ℝ) + 2) * (C_θ * (Work.BoseDict.cIPn (n + 2) Θ
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re) :=
        mul_le_mul_of_nonneg_left hbessel (by positivity)
    _ = C_θ * ((n : ℝ) + 2) * (Work.BoseDict.cIPn (n + 2) Θ
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re := by
        ring

end

end Work.BoseBoxFock.PotCubicLowBandAux
