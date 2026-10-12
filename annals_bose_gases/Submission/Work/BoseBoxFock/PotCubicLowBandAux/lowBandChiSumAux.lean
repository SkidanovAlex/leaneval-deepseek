import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.atomPairG
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.lowBandChiAuxAux
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotBoxT0AnnComm
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.twoStateSelfPair
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

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. Small algebraic helpers -/

/-- `cIPn` is additive over differences in its second argument. -/
private lemma cIPn_sub {d : ℕ} {Θ X Y : Work.BoseDict.Xn d → ℂ}
    (hX : Integrable (fun x => star (Θ x) * X x))
    (hY : Integrable (fun x => star (Θ x) * Y x)) :
    Work.BoseDict.cIPn d Θ (X - Y) = Work.BoseDict.cIPn d Θ X - Work.BoseDict.cIPn d Θ Y := by
  simp only [Work.BoseDict.cIPn]
  rw [show (fun x => (starRingEnd ℂ) (Θ x) * (X - Y) x)
      = (fun x => star (Θ x) * X x - star (Θ x) * Y x) from
    funext fun x => by simp only [Pi.sub_apply, starRingEnd_apply]; ring]
  rw [MeasureTheory.integral_sub hX hY]
  simp only [starRingEnd_apply]

/-- The coordinate vector `evec m l` vanishes at the index `0` for `l ≠ 0`. -/
private lemma evec_apply_zero {m : ℕ} [NeZero m] {l : Fin m} (hl : l ≠ 0) :
    Work.BoseB4.evec m l (0 : Fin m) = 0 := by
  simp only [Work.BoseB4.evec, Pi.single_apply]
  rw [if_neg (by rintro rfl; exact hl rfl)]

/-- **The `boxT0` slot sum is the sum over the excited modes of the rank-one slot sums.** -/
theorem boxSlotSum_boxT0_eq_sum_rankOne {m d : ℕ} [NeZero m] {e : Fin m → Ω → ℂ}
    (Ψ : Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          Work.BoseDict.boxSlotSum e
            (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l)) Ψ := by
  rw [← sum_erase_rankOnePair_evec_eq_boxT0 (m := m)]
  exact boxSlotSum_finset_T_local _ _ Ψ

/-- **`cIPn` of the `boxT0` slot sum splits over the excited modes** (the `l`-sum of
`Σ_l ⟪Θ, |e_l⟩⟨e_l| Ψ⟫`). -/
theorem cIPn_boxSlotSum_boxT0_eq_sum {m d : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Ψ : Xn d → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨsupp : Function.support Ψ ⊆ Work.MB.boxPow d ℓ)
    {Θ : Xn d → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow d ℓ) :
    (Work.BoseDict.cIPn d Θ (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ)).re
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn d Θ
            (Work.BoseDict.boxSlotSum e
              (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l)
                (Work.BoseB4.evec m l)) Ψ)).re := by
  have hS : Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ
      = ∑ l ∈ Finset.univ.erase (0 : Fin m), (1 : ℝ) •
          Work.BoseDict.boxSlotSum e
            (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l)
              (Work.BoseB4.evec m l)) Ψ := by
    rw [boxSlotSum_boxT0_eq_sum_rankOne]
    exact Finset.sum_congr rfl (fun l _ => by rw [one_smul])
  rw [hS]
  rw [Work.BoseBoxFock.FRK.cIPn_sum_smul (S := Finset.univ.erase (0 : Fin m))
    (w := fun _ => (1 : ℝ))
    (F := fun l => Work.BoseDict.boxSlotSum e
      (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l)) Ψ)
    (Θ := Θ)
    (fun l _ => integrable_star_mul_boxSlotSumAux hmeas hbdd hsupp
      (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
      hΨm hΨb hΨsupp hΘm hΘb hΘsupp)]
  simp only [Complex.ofReal_one, one_mul, Complex.re_sum]

/-! ## 1. The pair sum of the excited modes is the second excited moment -/

/-- **The χ-sum of the two-annihilation terms.**  For a symmetric box state `Θ` of degree `n+2`,

    `Σ_{l,l' ≠ 0} ‖a_{l'} a_l Θ‖²  ≤  ⟪Θ, S (S Θ)⟫` ,

which is the sharp `n₊²`-bound of FS `lem:Q3-splitting2` on the `X`-side.  It is proved as the
*identity* `Σ_{l,l'≠0}‖a_{l'}a_lΘ‖² = ⟪Θ,(S²−S)Θ⟫` (using `S a_w = a_w(S−1)`,
`slotBoxT0AnnComm`, and the mixed adjointness `twoStateSelfPair`) followed by `S ⪰ 0`. -/
private theorem pairSumExcited {m n : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    {Θ : Xn (n + 2) → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (n + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (n + 2))) (x : Xn (n + 2)), Θ (x ∘ σ) = Θ x) :
    (∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ l' ∈ Finset.univ.erase (0 : Fin m),
        (Work.BoseDict.cIPn n
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ))
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ))).re)
      ≤ (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re := by
  classical
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  -- the regularities of `S Θ`
  obtain ⟨hSm, hSb⟩ := Work.MB.boxSlotSum_measurable_bounded_ae (d := n + 2) hmeas hbdd hsupp
    (Work.BoseBoxFock.boxT0 m) Θ hΘm ⟨CΘ, hCΘ⟩
  obtain ⟨CS, hCS⟩ := hSb
  have hSsupp : Function.support
      (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ) ⊆
      Work.MB.boxPow (n + 2) ℓ := boxSlotSum_support hsupp _ hΘsupp
  have hSsym : ∀ (σ : Equiv.Perm (Fin (n + 2))) (x : Xn (n + 2)),
      Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ (x ∘ σ)
        = Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x :=
    boxSlotSum_boxT0_symm (e := e) hΘm ⟨CΘ, hCΘ⟩ hΘsym
  -- the per-`l` term
  have hterm : ∀ l ∈ Finset.univ.erase (0 : Fin m),
      (∑ l' ∈ Finset.univ.erase (0 : Fin m),
        (Work.BoseDict.cIPn n
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ))
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ))).re)
      = (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e
            (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re
        - (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e
            (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
            Θ)).re := by
    intro l hl
    have hl0 : l ≠ 0 := (Finset.mem_erase.mp hl).1
    set Ψ : Xn (n + 1) → ℂ := Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ with hΨdef
    have hΨW : Work.BoseBoxFock.WRegG ℓ Ψ :=
      boxAnnOf_wregG hmeas hbdd hsupp _ ⟨hΘm, ⟨CΘ, hCΘ⟩, hΘsupp⟩
    obtain ⟨CΨ, hCΨ⟩ := hΨW.bdd
    have hΨsym : ∀ (σ : Equiv.Perm (Fin (n + 1))) (x : Xn (n + 1)), Ψ (x ∘ σ) = Ψ x :=
      boxAnnOf_symm (Work.BoseB4.evec m l) Θ hΘsym
    -- the self-pairing identity at the state `Ψ`
    have hP3 := cIPn_boxSlotSum_boxT0_selfPair hmeas hbdd hsupp hMemLp hΨW.meas hCΨ hΨW.supp hΨsym
    -- the commutation `S Ψ = a_l (S Θ) - Ψ`
    have hcomm := slotBoxT0AnnComm hmeas hbdd hsupp horth (w := Work.BoseB4.evec m l)
      (evec_apply_zero (l := l) hl0) hΘm ⟨CΘ, hCΘ⟩ hΘsupp
    -- integrability of the two pieces
    have hInt1 : Integrable (fun x : Xn (n + 1) => star (Ψ x) *
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)) x) := by
      have hY : Work.BoseBoxFock.WRegG ℓ
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)) :=
        boxAnnOf_wregG hmeas hbdd hsupp _ ⟨hSm, ⟨CS, hCS⟩, hSsupp⟩
      obtain ⟨C, hC⟩ := hY.bdd
      refine Work.MB.integrable_of_bdd_of_support (S := Work.MB.boxPow (n + 1) ℓ)
        (C := max CΨ 0 * max C 0) (Work.MB.measurableSet_boxPow (n + 1) ℓ)
        (Work.MB.volume_boxPow_lt_top (n + 1) ℓ) ?_ ?_ ?_
      · exact ((Complex.continuous_conj.measurable.comp hΨW.meas).mul hY.meas).aestronglyMeasurable
      · intro x
        rw [norm_mul, norm_star]
        exact mul_le_mul ((hCΨ x).trans (le_max_left _ _)) ((hC x).trans (le_max_left _ _))
          (norm_nonneg _) (le_max_right _ _)
      · intro x hx
        have h0 : Ψ x = 0 := Function.notMem_support.mp (fun h => hx (hΨW.supp h))
        rw [h0, star_zero, zero_mul]
    have hInt2 : Integrable (fun x : Xn (n + 1) => star (Ψ x) * Ψ x) := by
      refine Work.MB.integrable_of_bdd_of_support (S := Work.MB.boxPow (n + 1) ℓ)
        (C := (max CΨ 0) ^ 2) (Work.MB.measurableSet_boxPow (n + 1) ℓ)
        (Work.MB.volume_boxPow_lt_top (n + 1) ℓ) ?_ ?_ ?_
      · exact ((Complex.continuous_conj.measurable.comp hΨW.meas).mul hΨW.meas).aestronglyMeasurable
      · intro x
        rw [norm_mul, norm_star]
        have hnn : 0 ≤ CΨ := le_trans (norm_nonneg _) (hCΨ 0)
        calc ‖Ψ x‖ * ‖Ψ x‖ ≤ CΨ * CΨ := mul_le_mul (hCΨ x) (hCΨ x) (norm_nonneg _) hnn
          _ ≤ (max CΨ 0) ^ 2 := by
              simpa only [sq] using pow_le_pow_left₀ hnn (le_max_left CΨ 0) 2
      · intro x hx
        have h0 : Ψ x = 0 := Function.notMem_support.mp (fun h => hx (hΨW.supp h))
        rw [h0, star_zero, zero_mul]
    calc (∑ l' ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ))).re)
        = (Work.BoseDict.cIPn (n + 1) Ψ
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Ψ)).re := hP3.symm
      _ = (Work.BoseDict.cIPn (n + 1) Ψ
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1)
                (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ) - Ψ)).re := by
            rw [hcomm]
      _ = (Work.BoseDict.cIPn (n + 1) Ψ
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1)
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re
          - (Work.BoseDict.cIPn (n + 1) Ψ Ψ).re := by
            rw [cIPn_sub hInt1 hInt2]
            simp only [Complex.sub_re]
      _ = (Work.BoseDict.cIPn (n + 2) Θ
            (Work.BoseDict.boxSlotSum e
              (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re
          - (Work.BoseDict.cIPn (n + 2) Θ
            (Work.BoseDict.boxSlotSum e
              (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
              Θ)).re := by
            rw [twoStateSelfPair hmeas hbdd hsupp hMemLp (Work.BoseB4.evec m l)
                  (Work.BoseB4.evec m l) hΘm hCΘ hΘsupp hΘsym hSm hCS hSsupp hSsym,
                twoStateSelfPair hmeas hbdd hsupp hMemLp (Work.BoseB4.evec m l)
                  (Work.BoseB4.evec m l) hΘm hCΘ hΘsupp hΘsym hΘm hCΘ hΘsupp hΘsym]
  -- the sum over `l`
  have hnonneg : 0 ≤ (Work.BoseDict.cIPn (n + 2) Θ
      (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re := by
    rw [cIPn_boxSlotSum_boxT0_eq_sum (d := n + 2) hmeas hbdd hsupp hΘm ⟨CΘ, hCΘ⟩ hΘsupp hΘm ⟨CΘ, hCΘ⟩ hΘsupp]
    refine Finset.sum_nonneg (fun l hl => ?_)
    have hl0 : l ≠ 0 := (Finset.mem_erase.mp hl).1
    have hlreg : Work.BoseBoxFock.WRegG ℓ
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ) :=
      boxAnnOf_wregG hmeas hbdd hsupp _ ⟨hΘm, ⟨CΘ, hCΘ⟩, hΘsupp⟩
    obtain ⟨Cl, hCl⟩ := hlreg.bdd
    rw [← twoStateSelfPair hmeas hbdd hsupp hMemLp (Work.BoseB4.evec m l) (Work.BoseB4.evec m l)
          hΘm hCΘ hΘsupp hΘsym hΘm hCΘ hΘsupp hΘsym,
      Work.BoseBoxFock.cIPn_self_re]
    exact integral_nonneg (fun y => sq_nonneg _)
  calc (∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ l' ∈ Finset.univ.erase (0 : Fin m),
        (Work.BoseDict.cIPn n
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ))
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ))).re)
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          ((Work.BoseDict.cIPn (n + 2) Θ
            (Work.BoseDict.boxSlotSum e
              (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re
          - (Work.BoseDict.cIPn (n + 2) Θ
            (Work.BoseDict.boxSlotSum e
              (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
              Θ)).re) := Finset.sum_congr rfl hterm
    _ = (∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn (n + 2) Θ
            (Work.BoseDict.boxSlotSum e
              (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
              (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re)
        - ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn (n + 2) Θ
            (Work.BoseDict.boxSlotSum e
              (Work.BoseBoxFock.rankOnePair (Work.BoseB4.evec m l) (Work.BoseB4.evec m l))
              Θ)).re := by rw [Finset.sum_sub_distrib]
    _ = (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re
        - (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re := by
          rw [← cIPn_boxSlotSum_boxT0_eq_sum (d := n + 2) hmeas hbdd hsupp hSm ⟨CS, hCS⟩ hSsupp hΘm ⟨CΘ, hCΘ⟩ hΘsupp,
            ← cIPn_boxSlotSum_boxT0_eq_sum (d := n + 2) hmeas hbdd hsupp hΘm ⟨CΘ, hCΘ⟩ hΘsupp hΘm ⟨CΘ, hCΘ⟩ hΘsupp]
    _ ≤ (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re := by
          linarith

/-! ## 2. The χ-sum bound -/

/-! ## 2. The abstract reduction (the states are variables, so the terms stay small) -/

private theorem chiReduce {m n : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Fin m → ℝ)
    (C_B : ℝ) (hC_B : 0 ≤ C_B)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C_B * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ k : ι, f k 0 = 0)
    {A : ι → Xn (n + 1) → ℂ} {B : Fin m → Xn (n + 1) → ℂ}
    (hA : ∀ k : ι, Work.BoseBoxFock.WRegG ℓ (A k))
    (hAsym : ∀ k : ι, ∀ (σ : Equiv.Perm (Fin (n + 1))) (x : Xn (n + 1)), A k (x ∘ σ) = A k x)
    (hBw : ∀ l : Fin m, Work.BoseBoxFock.WRegG ℓ (B l))
    (hBsym : ∀ l : Fin m, ∀ (σ : Equiv.Perm (Fin (n + 1))) (x : Xn (n + 1)),
      B l (x ∘ σ) = B l x)
    (hcomm : ∀ (l : Fin m) (k : ι), Work.BoseDict.boxAnnOf e (f k) n (B l)
      = Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))
    {X : ℝ}
    (hpair : (∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ l' ∈ Finset.univ.erase (0 : Fin m),
        (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))
          (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))).re) ≤ X) :
    (∑ k : ι, ∑ k' : ι, (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (f k') n (A k))
        (Work.BoseDict.boxAnnOf e (f k') n (A k))).re) ≤ C_B ^ 2 * X := by
  have hstep1 : ∀ k : ι,
      (∑ k' : ι, (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (f k') n (A k))
        (Work.BoseDict.boxAnnOf e (f k') n (A k))).re)
      ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))).re := by
    intro k
    obtain ⟨Ck, hCk⟩ := (hA k).bdd
    exact frameSum_le_excitedSum (m := m) (d := n) hmeas hbdd hsupp horth hMemLp f C_B hC_B
      hframe h0 (hA k).meas hCk (hA k).supp (hAsym k)
  have hstep2 : ∀ l ∈ Finset.univ.erase (0 : Fin m),
      (∑ k : ι, (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (f k) n (B l))
        (Work.BoseDict.boxAnnOf e (f k) n (B l))).re)
      ≤ C_B * ∑ l' ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))).re := by
    intro l _
    obtain ⟨Cl, hCl⟩ := (hBw l).bdd
    exact frameSum_le_excitedSum (m := m) (d := n) hmeas hbdd hsupp horth hMemLp f C_B hC_B
      hframe h0 (hBw l).meas hCl (hBw l).supp (hBsym l)
  have h1 : (∑ k : ι, ∑ k' : ι, (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (f k') n (A k))
        (Work.BoseDict.boxAnnOf e (f k') n (A k))).re)
      ≤ C_B * ∑ k : ι, ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hstep1 k)
  have h2 : (C_B * ∑ k : ι, ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))).re)
      ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ k : ι,
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))).re := by
    rw [Finset.sum_comm]
  have h3 : (C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ k : ι,
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) n (A k))).re)
      ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ k : ι,
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (f k) n (B l))
            (Work.BoseDict.boxAnnOf e (f k) n (B l))).re := by
    refine le_of_eq (congrArg (fun z : ℝ => C_B * z)
      (Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))))
    rw [← hcomm l k]
  have h4 : (C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ k : ι,
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (f k) n (B l))
            (Work.BoseDict.boxAnnOf e (f k) n (B l))).re)
      ≤ C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m), C_B * ∑ l' ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))).re :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep2) hC_B
  have h5 : (C_B * ∑ l ∈ Finset.univ.erase (0 : Fin m), C_B * ∑ l' ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))).re)
      ≤ C_B ^ 2 * ∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ l' ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))).re := by
    refine le_of_eq ?_
    rw [← Finset.mul_sum]
    ring
  have h6 : (C_B ^ 2 * ∑ l ∈ Finset.univ.erase (0 : Fin m), ∑ l' ∈ Finset.univ.erase (0 : Fin m),
          (Work.BoseDict.cIPn n (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l') n (B l))).re)
      ≤ C_B ^ 2 * X := mul_le_mul_of_nonneg_left hpair (by positivity)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

theorem lowBandChiSumAux {m n : ℕ} [NeZero m] {ℓ 𝓜 V : ℝ} (hℓ : 0 < ℓ) (h𝓜 : 0 ≤ 𝓜)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Fin m → ℝ)
    (C_B : ℝ) (hC_B : 0 ≤ C_B)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C_B * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ k : ι, f k 0 = 0)
    {Θ : Work.BoseDict.Xn (n + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (n + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (n + 2))) (x : Work.BoseDict.Xn (n + 2)),
      Θ (x ∘ σ) = Θ x)
    (hVnn : 0 ≤ V)
    (hS : (Work.BoseDict.cIPn (n + 2) Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re ≤ V)
    (hS2 : (Work.BoseDict.cIPn (n + 2) Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re ≤ 𝓜 * V) :
    (∑ k : ι, ∑ k' : ι,
        (Work.BoseDict.cIPn n
          (Work.BoseDict.boxAnnOf e (f k') n (Work.BoseDict.boxAnnOf e (f k) (n + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f k') n
            (Work.BoseDict.boxAnnOf e (f k) (n + 1) Θ))).re)
      ≤ C_B ^ 2 * (𝓜 + 1) * V := by
  classical
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤ := fun l =>
    memLp_top_of_bound (hmeas l).aestronglyMeasurable (hbdd l).choose
      (Filter.Eventually.of_forall (hbdd l).choose_spec)
  have hmain := chiReduce (m := m) (n := n) (ℓ := ℓ) (e := e) hmeas hbdd hsupp horth hMemLp f
    C_B hC_B hframe h0
    (A := fun k => Work.BoseDict.boxAnnOf e (f k) (n + 1) Θ)
    (B := fun l => Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m l) (n + 1) Θ)
    (fun k => boxAnnOf_wregG hmeas hbdd hsupp _ ⟨hΘm, ⟨CΘ, hCΘ⟩, hΘsupp⟩)
    (fun k => boxAnnOf_symm (f k) Θ hΘsym)
    (fun l => boxAnnOf_wregG hmeas hbdd hsupp _ ⟨hΘm, ⟨CΘ, hCΘ⟩, hΘsupp⟩)
    (fun l => boxAnnOf_symm (Work.BoseB4.evec m l) Θ hΘsym)
    (fun l k => boxAnnOf_boxAnnOf_comm hmeas hbdd hsupp (f k) (Work.BoseB4.evec m l) hΘm
      ⟨CΘ, hCΘ⟩ hΘsupp hΘsym)
    (pairSumExcited hmeas hbdd hsupp horth hMemLp hΘm ⟨CΘ, hCΘ⟩ hΘsupp hΘsym)
  refine hmain.trans ?_
  calc C_B ^ 2 * (Work.BoseDict.cIPn (n + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
            (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re
      ≤ C_B ^ 2 * (𝓜 * V) := mul_le_mul_of_nonneg_left hS2 (by positivity)
    _ ≤ C_B ^ 2 * ((𝓜 + 1) * V) :=
        mul_le_mul_of_nonneg_left (by nlinarith [h𝓜, hVnn]) (by positivity)
    _ = C_B ^ 2 * (𝓜 + 1) * V := by ring

end

end Work.BoseBoxFock.PotCubicLowBandAux
