import Mathlib
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Final.bmRow_bound
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport

namespace Work.NN.Core

open scoped NNReal ENNReal
open Set

/-- **The Bochner–Martinelli row potential of a cut-off form, in the `C^{k+1,α}` scale.**

If `χ` is smooth of compact support vanishing whenever some coordinate satisfies `ρ''' j ≤ ‖z j‖`,
and `ρ' < ρ''' < ρ` coordinatewise, then for each `k` the `C^{k+1,α}`-norm on the polydisc of radii
`ρ'` of the Bochner–Martinelli row potential of the form `χ · η` is bounded by a constant times the
`C^{k,α}`-norm of `η` on the polydisc of radii `ρ`.

The geometry is arranged so that `bmRow`'s Schauder estimate applies: the data `χ · η` is supported
in the polydisc of radii `ρ'''`, while the estimate is taken on the smaller polydisc of radii `ρ'`.
The support of `χ` also lets `‖χ · η‖_{k,α}(ℂⁿ)` be replaced by `‖η‖_{k,α}(P(ρ))`, using that the
product vanishes off the strictly smaller polydisc of radii `ρ'''`. -/
theorem bmRowCutoffEstimate {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' ρ''' : Fin n → ℝ} (hρ'''pos : ∀ j, 0 < ρ''' j) (hρ'ρ''' : ∀ j, ρ' j < ρ''' j)
    (hρ'''ρ : ∀ j, ρ''' j < ρ j)
    (χ : Work.NN.Core.Cn n → ℂ) (hχ_sm : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_cs : HasCompactSupport χ)
    (hχzero : ∀ z : Work.NN.Core.Cn n, (∃ j, ρ''' j ≤ ‖z j‖) → χ z = 0) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ),
        (∀ j l, ContDiff ℝ (k + 1) (η j l)) →
        ∀ j : Fin n,
          Work.CR.Flat.holderNorm (k + 1) α
              (Work.NN.Core.bmRow (fun i l w => χ w * η i l w) j) (Work.CR.Flat.polydisc 0 ρ')
            ≤ ENNReal.ofReal (C k) *
                ∑ j, ∑ l, Work.CR.Flat.holderNorm k α (η j l) (Work.CR.Flat.polydisc 0 ρ) := by
  classical
  -- the auxiliary radius `2ρ'''` at which `bmRow_bound` is applied: data supported in `P(ρ''')`
  -- certainly vanishes where some coordinate reaches `2ρ'''`, and the estimate it returns on
  -- `P(2ρ'''/2) = P(ρ''')` contains the desired polydisc `P(ρ')`.
  set rbm : Fin n → ℝ := fun i => 2 * ρ''' i with hrbm
  have hrbmpos : ∀ i, 0 < rbm i := fun i => by rw [hrbm]; linarith [hρ'''pos i]
  have hrbmhalf : (fun i => rbm i / 2) = ρ''' := by
    funext i; simp only [hrbm]; ring
  -- the Bochner–Martinelli Schauder bound, repackaged with the polydisc of radii `ρ'''`
  have hbm (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ X : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
      (∀ j l, ContDiff ℝ (↑k + 1) (X j l)) →
      (∀ j l z, (∃ i, rbm i ≤ ‖z i - (0 : Work.NN.Core.Cn n) i‖) → X j l z = 0) →
      ∀ j, Work.CR.Flat.holderNorm (k + 1) α
            (fun y => Work.CR.Flat.Cauchy.bmPot (fun l => X j l) y)
            (Work.CR.Flat.polydisc 0 ρ''')
          ≤ ENNReal.ofReal C * ∑ j : Fin n, ∑ l : Fin n,
              Work.CR.Flat.holderNorm k α (X j l) Set.univ := by
    obtain ⟨C, hCpos, hCbd⟩ := Work.NN.Final.bmRow_bound (n := n) hα hα1 k
      (c := (0 : Work.NN.Core.Cn n)) (ρ := rbm) hrbmpos
    exact ⟨C, hCpos, fun X hX hz j => by
      have h := hCbd X hX hz j
      rwa [hrbmhalf] at h⟩
  set Cbm : ℕ → ℝ := fun k => Classical.choose (hbm k) with hCbm
  have hCbmpos : ∀ k, 0 < Cbm k := fun k => (Classical.choose_spec (hbm k)).1
  have hCbmbd (k : ℕ) := (Classical.choose_spec (hbm k)).2
  -- the constant of the multiplication bound at order `k`
  have hmul (k : ℕ) := Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
      (Ω := Work.CR.Flat.polydisc 0 ρ) (k := k) (α := α)
      ((Work.CR.Flat.isOpen_polydisc 0 ρ).uniqueDiffOn) hα.le hα1.le
      (ζ := χ) (hχ_sm.of_le (by simp)) hχ_cs
  set Cmul : ℕ → ℝ := fun k => Classical.choose (hmul k) with hCmul
  have hCmulpos : ∀ k, 0 < Cmul k := fun k => (Classical.choose_spec (hmul k)).1
  have hCmulbd (k : ℕ) := (Classical.choose_spec (hmul k)).2
  set Cf : ℕ → ℝ := fun k => ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (Cbm k * Cmul k) + 1 with hCf
  refine ⟨Cf, ?_, ?_⟩
  · intro k
    rw [hCf]
    have h1 : 0 < Cbm k * Cmul k := mul_pos (hCbmpos k) (hCmulpos k)
    have h2 : 0 ≤ ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ := norm_nonneg _
    nlinarith
  · intro k η hη jrow
    set S : ℝ≥0∞ := ∑ j : Fin n, ∑ l : Fin n,
        Work.CR.Flat.holderNorm k α (η j l) (Work.CR.Flat.polydisc 0 ρ) with hS
    set Xn : Fin n → Fin n → Work.NN.Core.Cn n → ℂ := fun i l w => χ w * η i l w with hXn
    have hXnsm : ∀ i l, ContDiff ℝ (↑k + 1) (Xn i l) := fun i l => by
      have hχ' : ContDiff ℝ (↑k + 1) χ := hχ_sm.of_le (by simp)
      have hη' : ContDiff ℝ (↑k + 1) (η i l) := by simpa using hη i l
      have hm := ContDiff.mul hχ' hη'
      simpa only [hXn] using hm
    have hXncs : ∀ i l, HasCompactSupport (Xn i l) := fun i l => by
      rw [hXn]
      exact hχ_cs.mul_right (f' := η i l)
    have hXnzero : ∀ i l z, (∃ j', rbm j' ≤ ‖z j' - (0 : Work.NN.Core.Cn n) j'‖) → Xn i l z = 0 := by
      intro i l z hz
      obtain ⟨j', hj'⟩ := hz
      simp only [Pi.zero_apply, sub_zero] at hj'
      have hle : ρ''' j' ≤ ‖z j'‖ := by rw [hrbm] at hj'; linarith [hρ'''pos j']
      simp only [hXn]
      rw [hχzero z ⟨j', hle⟩, zero_mul]
    have hbmk := hCbmbd k Xn hXnsm hXnzero jrow
    -- the componentwise replacement of `‖χ · η‖_{k,α}(ℂⁿ)` by `‖η‖_{k,α}(P(ρ))`
    have hper : ∀ j' l, Work.CR.Flat.holderNorm k α (Xn j' l) Set.univ
        ≤ ENNReal.ofReal (Cmul k) * Work.CR.Flat.holderNorm k α (η j' l) (Work.CR.Flat.polydisc 0 ρ) := by
      intro j' l
      have hvan : ∀ z, (∃ i, ρ''' i ≤ ‖z i - (0 : Work.NN.Core.Cn n) i‖) → Xn j' l z = 0 := by
        intro z hz
        obtain ⟨i, hi⟩ := hz
        simp only [Pi.zero_apply, sub_zero] at hi
        simp only [hXn]
        rw [hχzero z ⟨i, hi⟩, zero_mul]
      have h1 := Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
        (k := k) (α := α) (c := (0 : Work.NN.Core.Cn n)) (r := ρ''') (r' := ρ) hρ'''ρ hα.le hvan
      have h2 := hCmulbd k (η j' l) (((hη j' l).of_le (by simp)).contDiffOn)
      have h2' : Work.CR.Flat.holderNorm k α (Xn j' l) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal (Cmul k) * Work.CR.Flat.holderNorm k α (η j' l) (Work.CR.Flat.polydisc 0 ρ) := by
        simpa only [hXn] using h2
      exact h1.trans h2'
    have hsum : (∑ j' : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm k α (Xn j' l) Set.univ)
        ≤ ENNReal.ofReal (Cmul k) * S := by
      rw [hS]
      calc (∑ j' : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm k α (Xn j' l) Set.univ)
          ≤ ∑ j' : Fin n, ∑ l : Fin n,
              ENNReal.ofReal (Cmul k) * Work.CR.Flat.holderNorm k α (η j' l) (Work.CR.Flat.polydisc 0 ρ) :=
            Finset.sum_le_sum fun j' _ => Finset.sum_le_sum fun l _ => hper j' l
        _ = ENNReal.ofReal (Cmul k) * ∑ j' : Fin n, ∑ l : Fin n,
              Work.CR.Flat.holderNorm k α (η j' l) (Work.CR.Flat.polydisc 0 ρ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j' _ => ?_
            rw [Finset.mul_sum]
    -- smoothness of the potential, needed to pull out the constant `-γ⁻¹`
    have hcont : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞)
        (Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l)) (Work.CR.Flat.polydisc 0 ρ') := by
      have h : ContDiffOn ℝ (↑k + 1)
          (Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l)) (Work.CR.Flat.polydisc 0 ρ') :=
        (Work.CR.Flat.Cauchy.contDiff_bmPotential_Ck hn k (fun l => hXnsm jrow l)
          (fun l => hXncs jrow l)).contDiffOn
      simpa using h
    have hrow_eq : Work.NN.Core.bmRow Xn jrow
        = (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) •
            (Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l)) := by
      funext z
      simp only [hXn, Work.NN.Core.bmRow_apply, Pi.smul_apply, smul_eq_mul,
        Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
    have hpot_eq : (fun y => Work.CR.Flat.Cauchy.bmPot (fun l => Xn jrow l) y)
        = Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l) := by
      funext y
      exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot (fun l => Xn jrow l) y).symm
    have hmono : Work.CR.Flat.holderNorm (k + 1) α
          (Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l)) (Work.CR.Flat.polydisc 0 ρ')
        ≤ Work.CR.Flat.holderNorm (k + 1) α
          (fun y => Work.CR.Flat.Cauchy.bmPot (fun l => Xn jrow l) y) (Work.CR.Flat.polydisc 0 ρ''') := by
      calc Work.CR.Flat.holderNorm (k + 1) α
            (Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l)) (Work.CR.Flat.polydisc 0 ρ')
          ≤ Work.CR.Flat.holderNorm (k + 1) α
            (Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l)) (Work.CR.Flat.polydisc 0 ρ''') :=
            Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 ρ''')
              (Work.CR.Flat.isOpen_polydisc 0 ρ')
              (fun z hz i => lt_trans (hz i) (hρ'ρ''' i)) (k + 1) α _
        _ = Work.CR.Flat.holderNorm (k + 1) α
            (fun y => Work.CR.Flat.Cauchy.bmPot (fun l => Xn jrow l) y) (Work.CR.Flat.polydisc 0 ρ''') := by
            rw [← hpot_eq]
    have hsmul := Work.CR.Flat.Holder.holderNorm_smul (k := k + 1) (α := α)
      (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) hcont ((Work.CR.Flat.isOpen_polydisc 0 ρ').uniqueDiffOn)
    calc Work.CR.Flat.holderNorm (k + 1) α (Work.NN.Core.bmRow Xn jrow) (Work.CR.Flat.polydisc 0 ρ')
        = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
            Work.CR.Flat.holderNorm (k + 1) α
              (Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l)) (Work.CR.Flat.polydisc 0 ρ') := by
          rw [hrow_eq, hsmul, norm_neg]
      _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
            (ENNReal.ofReal (Cbm k) * (ENNReal.ofReal (Cmul k) * S)) := by
          apply mul_le_mul_right
          calc Work.CR.Flat.holderNorm (k + 1) α
                (Work.CR.Flat.Cauchy.bmPotential (fun l => Xn jrow l)) (Work.CR.Flat.polydisc 0 ρ')
              ≤ Work.CR.Flat.holderNorm (k + 1) α
                (fun y => Work.CR.Flat.Cauchy.bmPot (fun l => Xn jrow l) y) (Work.CR.Flat.polydisc 0 ρ''') := hmono
            _ ≤ ENNReal.ofReal (Cbm k) * (∑ j' : Fin n, ∑ l : Fin n,
                  Work.CR.Flat.holderNorm k α (Xn j' l) Set.univ) := hbmk
            _ ≤ ENNReal.ofReal (Cbm k) * (ENNReal.ofReal (Cmul k) * S) := mul_le_mul_right hsum _
      _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (Cbm k * Cmul k)) * S := by
          have hcoef : ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * (Cbm k * Cmul k))
              = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ *
                (ENNReal.ofReal (Cbm k) * ENNReal.ofReal (Cmul k)) := by
            rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (le_of_lt (hCbmpos k))]
          rw [hcoef]
          ac_rfl
      _ ≤ ENNReal.ofReal (Cf k) * S := by
          apply mul_le_mul_left
          rw [hCf]
          exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)

end Work.NN.Core
