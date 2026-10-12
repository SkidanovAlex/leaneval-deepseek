import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aPC_pinned_thMode_re
import Submission.Work.BoseBoxFock.boxSlotOf_weak_reg
import Submission.Work.BoseBoxFock.n0Slot_ae_real
import Submission.Work.BoseBoxFock.re_cIPn_boxRestrict
import Submission.Work.BoseBoxFock.thMode_measurable_bounded
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary regularity of the box restriction -/

private lemma boxRestrictC_measurable {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) : Measurable (Work.BoseBoxFock.boxRestrictC ℓ Φ) := by
  unfold Work.BoseBoxFock.boxRestrictC
  exact (Complex.measurable_ofReal.comp hΦc.measurable).mul
    (Complex.measurable_ofReal.comp
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ)))

private lemma boxRestrictC_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.boxRestrictC ℓ Φ x‖ ≤ C := by
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  refine ⟨max B 0, fun x => ?_⟩
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · have h1 : Work.BoseBoxFock.boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) := by
      unfold Work.BoseBoxFock.boxRestrictC
      rw [Set.indicator_of_mem hx]
      simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (by simpa using hB x hx) (le_max_left _ _)
  · have h1 : Work.BoseBoxFock.boxRestrictC ℓ Φ x = 0 := by
      unfold Work.BoseBoxFock.boxRestrictC
      rw [Set.indicator_of_notMem hx]
      simp
    rw [h1, norm_zero]
    exact le_max_right _ _

private lemma boxRestrictC_support {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (Work.BoseBoxFock.boxRestrictC ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra hmem
  exact hx (by
    unfold Work.BoseBoxFock.boxRestrictC
    rw [Set.indicator_of_notMem hmem]
    simp)

/-! ## Regularity of the slot sum at the weak hypotheses -/

private lemma slotSum_reg {m d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) {Θ : Work.BoseDict.Xn d → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Measurable (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair w v) Θ) ∧
      ∃ C : ℝ, ∀ x : Work.BoseDict.Xn d,
        ‖Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair w v) Θ x‖ ≤ C := by
  have hexp := chiRow_slotSum_expand_weak (ℓ := ℓ) hmeas hbdd hsupp w v Θ hΘm hΘb
  refine ⟨?_, ?_⟩
  · have hsum : Measurable (fun x : Work.BoseDict.Xn d =>
        ∑ j : Fin d, Work.BoseDict.boxSlotOf e w v j Θ x) :=
      Finset.measurable_sum _ (fun j _ =>
        (boxSlotOf_weak_reg hℓ hmeas hbdd hsupp w v j hΘm hΘb).1)
    have hfun : (∑ j : Fin d, Work.BoseDict.boxSlotOf e w v j Θ)
        = fun x : Work.BoseDict.Xn d =>
            ∑ j : Fin d, Work.BoseDict.boxSlotOf e w v j Θ x := by
      funext x
      rw [Finset.sum_apply]
    rw [hexp, hfun]
    exact hsum
  · choose B hB using fun j : Fin d =>
      (boxSlotOf_weak_reg hℓ hmeas hbdd hsupp w v j hΘm hΘb).2
    refine ⟨∑ j : Fin d, max (B j) 0, fun x => ?_⟩
    rw [hexp, Finset.sum_apply]
    calc ‖∑ j : Fin d, Work.BoseDict.boxSlotOf e w v j Θ x‖
        ≤ ∑ j : Fin d, ‖Work.BoseDict.boxSlotOf e w v j Θ x‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin d, max (B j) 0 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact (hB j x).trans (le_max_left _ _)

theorem thRow_pairSecond {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C' : Fin m → ℝ} (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C' z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.thMode ℓ N)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C')
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      = Work.BoseBoxFock.pairHalfTwo n ℓ (Work.BoseBoxFock.thW ℓ N) Φ := by
  classical
  cases n with
  | zero =>
      simp only [Work.BoseDict.cIPn, Work.BoseDict.boxSlotSum, Finset.univ_eq_empty,
        Finset.sum_empty, Pi.zero_apply, integral_zero, Complex.zero_re,
        Work.BoseBoxFock.pairHalfTwo, mul_zero]
  | succ k =>
      -- the state and the slot words
      let Ψ : Work.BoseDict.Xn (k + 1) → ℂ :=
        Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
          (Work.BoseBoxFock.boxRestrictC ℓ Φ)
      let G : Work.BoseDict.Xn (k + 1) → ℂ :=
        Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair (Work.BoseBoxFock.evec0 m) C') Ψ
      -- the `n₀` function of the state, the two slot evaluations, and the right hand side
      let N0 : Work.BoseDict.Xn (k + 1) → ℂ :=
        fun y => ∑ i : Fin (k + 1), ((Submission.BoseGases.aP ℓ i Φ y : ℝ) : ℂ)
      let O2 : Work.BoseDict.Xn (k + 1) → ℂ := fun x => ∑ j : Fin (k + 1),
        Work.BoseBoxFock.aPC ℓ j
          (fun y => (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * Ψ y) x
      let O3 : Work.BoseDict.Xn (k + 1) → ℂ := fun x => ∑ j : Fin (k + 1),
        Work.BoseBoxFock.aPC ℓ j
          (fun y => (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * N0 y) x
      let Rw : Work.BoseDict.Xn (k + 1) → ℝ := fun x => ∑ j : Fin (k + 1),
        Submission.BoseGases.aP ℓ j
          (fun y => Work.BoseBoxFock.thW ℓ N (y j)
            * (∑ i : Fin (k + 1), Submission.BoseGases.aP ℓ i Φ y)) x
      have hΘm : Measurable (Work.BoseBoxFock.boxRestrictC ℓ Φ) :=
        boxRestrictC_measurable hΦc
      have hΘb : ∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.boxRestrictC ℓ Φ x‖ ≤ C :=
        boxRestrictC_bound hℓ hΦc
      have hΘs : Function.support (Work.BoseBoxFock.boxRestrictC ℓ Φ)
          ⊆ Submission.BoseGases.abox (k + 1) ℓ := boxRestrictC_support ℓ Φ
      -- regularity of the slot sums
      have hΨreg := slotSum_reg (ℓ := ℓ) hℓ hmeas hbdd hsupp (Work.BoseBoxFock.evec0 m)
        (Work.BoseBoxFock.evec0 m) hΘm hΘb
      have hΨm : Measurable Ψ := by
        simpa only [Ψ, Work.BoseBoxFock.rankOne_eq_rankOnePair] using hΨreg.1
      have hΨb : ∃ C : ℝ, ∀ x : Work.BoseDict.Xn (k + 1), ‖Ψ x‖ ≤ C := by
        obtain ⟨C, hC'⟩ := hΨreg.2
        exact ⟨C, fun x => by simpa only [Ψ, Work.BoseBoxFock.rankOne_eq_rankOnePair] using hC' x⟩
      have hGreg := slotSum_reg (ℓ := ℓ) hℓ hmeas hbdd hsupp (Work.BoseBoxFock.evec0 m) C' hΨm hΨb
      have hGm : Measurable G := hGreg.1
      have hGb : ∃ C : ℝ, ∀ x : Work.BoseDict.Xn (k + 1), ‖G x‖ ≤ C := hGreg.2
      -- (1) the `n₀` dictionary, in real form
      have hΨW : Ψ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)] N0 := by
        simpa only [Ψ, N0] using
          n0Slot_ae_real (ℓ := ℓ) (m := m) (n := k + 1) hℓ hpin hmeas hemem hbdd hsupp hΦc
      -- (2) the `θ`-row slot dictionary
      have hOuter : G =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)] O2 := by
        simpa only [G, Ψ, O2] using
          thRow_thModeT_dict (m := m) (d := k + 1) (ℓ := ℓ) (N := N) (e := e) (C := C')
            hℓ hpin hmeas hbdd hsupp hC Ψ hΨm hΨb
      -- (3) transfer the real form of the state into the slot integral
      have hO2O3 : O2 =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)] O3 := by
        have hsingle : ∀ j : Fin (k + 1),
            Work.BoseBoxFock.aPC ℓ j
                (fun y => (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * Ψ y)
              =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)]
            Work.BoseBoxFock.aPC ℓ j
                (fun y => (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * N0 y) := by
          intro j
          refine aPC_congr_ae_box j ?_
          filter_upwards [hΨW] with x hx
          rw [hx]
        have hall := (Finset.eventually_all (Finset.univ : Finset (Fin (k + 1)))).mpr
          (fun j _ => hsingle j)
        filter_upwards [hall] with x hx
        simp only [O2, O3]
        exact Finset.sum_congr rfl (fun j _ => hx j (Finset.mem_univ j))
      -- (4) the real-part computation of the pinned slot sums
      obtain ⟨hthm, Cth, hCth0, hthb⟩ := thMode_measurable_bounded ℓ N
      have hO3re : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)),
          (O3 x).re = Rw x := by
        filter_upwards [MeasureTheory.ae_restrict_mem
          (Submission.BoseGases.abox_measurable (k + 1) ℓ)] with x hx
        have hterm : ∀ j : Fin (k + 1),
            (Work.BoseBoxFock.aPC ℓ j
              (fun y => (starRingEnd ℂ) (Work.BoseBoxFock.thMode ℓ N (y j)) * N0 y) x).re
              = Submission.BoseGases.aP ℓ j
                  (fun y => Work.BoseBoxFock.thW ℓ N (y j)
                    * (∑ i : Fin (k + 1), Submission.BoseGases.aP ℓ i Φ y)) x :=
          fun j => by
            simpa only [N0] using
              aPC_pinned_thMode_re (n := k + 1) (ℓ := ℓ) (N := N) hℓ j hΦc hCth0 hthm hthb x hx
        simp only [O3, Rw]
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl (fun j _ => hterm j)
      -- (5) the real part of the whole slot sum, a.e.
      have hGRe : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (k + 1) ℓ)),
          (G x).re = Rw x := by
        filter_upwards [hOuter, hO2O3, hO3re] with x h1 h2 h3
        rw [h1, h2, h3]
      -- (6) assembly
      have hcongr : (∫ x in Submission.BoseGases.abox (k + 1) ℓ, Φ x * (G x).re)
          = ∫ x in Submission.BoseGases.abox (k + 1) ℓ, Φ x * Rw x := by
        refine MeasureTheory.setIntegral_congr_ae
          (Submission.BoseGases.abox_measurable (k + 1) ℓ) ?_
        filter_upwards [(MeasureTheory.ae_restrict_iff'
          (Submission.BoseGases.abox_measurable (k + 1) ℓ)).mp hGRe] with x hx hxs
        rw [hx hxs]
      show (Work.BoseDict.cIPn (k + 1) (Work.BoseBoxFock.boxRestrictC ℓ Φ) G).re
        = Work.BoseBoxFock.pairHalfTwo (k + 1) ℓ (Work.BoseBoxFock.thW ℓ N) Φ
      refine (re_cIPn_boxRestrict (d := k + 1) (ℓ := ℓ) hℓ hΦc hGm hGb).trans (hcongr.trans ?_)
      exact (show (∫ x in Submission.BoseGases.abox (k + 1) ℓ, Φ x * Rw x)
        = Work.BoseBoxFock.pairHalfTwo (k + 1) ℓ (Work.BoseBoxFock.thW ℓ N) Φ from rfl)

end Work.BoseBoxFock
