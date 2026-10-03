/-
# The `g`-side linear variational estimate of the mixed range at bounded height

`Work.KMTPlan.A6.BoundedHMain.gsideBoundedHeight`: for `0 < ρ ≤ 1`, `2 < r` and a height bound `B`,
the `r`-variation over a lacunary family of scales of the guarded exact-height pieces
`n ↦ Tm ρ l₂ (φ̃_{⌊a n⌋,t}) g` (`l₂ ≤ B`) is bounded on `ℓ²(ℤ)` by `K(Λ) ‖g‖₂`.

The proof has two steps.

* **The lift** (`Tm_eq_sum_modulation`): at arithmetic height `l` the exact-height multiplier is the
  finite sum, over the exact-height frequencies `α ∈ diffFreqs ρ l`, of the modulations of the
  *height-`0`* multiplier applied to `χ_α f`.  This is the exact-height analogue of
  `Work.KMTPlan.A6.BoundedHMain.Tle_eq_sum_modulation'`, and it is immediate from the kernel
  identity `Work.KMTPlan.A6.IwKernelArithChar`
  (`iwKernel (iwSymbolSet A (periodize ψ)) j = (∑_{α ∈ A} e(-jα)) · cw ψ j`).
* **The level-`0` estimate** (`Work.KMTPlan.A6.LowModApproxBoundedH.plainVarG_lev0`), applied to
  each of the (at most `#(iwArithFreqs ρ B)`, a constant) summands.  No `AreaA1` is used.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedBase
import Submission.Work.KMTPlan.A6.BoundedHMain.liftLevel
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.plainVarG_lev0
import Submission.Work.KMTAreas.A7.LpNonAliasAtWindow
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.BoundedHMain

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7 Work.KMTContract
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## The guard of the mixed model equals the `core` clip with the heights swapped -/

theorem loGuard_eq_core (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₂ k₁ k₂ n : ℕ) :
    (Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n)
      = (Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n) := by
  have h1 : max ((0 : ℕ) : ℤ) (l₂ : ℤ) = max (l₂ : ℤ) ((0 : ℕ) : ℤ) := Int.max_comm _ _
  have h2 : max (max 0 l₂) (max k₁ k₂) = max (max l₂ 0) (max k₁ k₂) := by
    rw [Nat.max_comm 0 l₂]
  simp only [Work.KMTAreas.A7.loGuard, Work.KMTAreas.A7.core, h1, h2]

/-! ## The lift of the exact-height multiplier to height `0` -/

/-- **The lift at an exact arithmetic height.**  For an integrable symbol `ψ` with summable
`cw`-coefficients and a bounded input `g`, the exact-height Ionescu--Wainger multiplier is the
finite sum, over the exact-height frequencies `α ∈ diffFreqs ρ l`, of the modulation `χ_{-α}` of
the *height-`0`* multiplier applied to `χ_α g`. -/
theorem Tm_eq_sum_modulation (ρ : ℝ) (l : ℕ) {ψ : ℝ → ℂ} (hψ : Integrable ψ) (g : ℤ → ℂ)
    (Cg : ℝ) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg)
    (hcw : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw ψ j‖) (x : ℤ) :
    Work.KMTAreas.A7.Tm ρ l ψ g x
      = ∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l,
          (starRingEnd ℂ) (fourier (T := 1) x α)
            * Work.KMTAreas.A7.Tle ρ 0 ψ (fun y : ℤ => fourier (T := 1) y α * g y) x := by
  classical
  set A : Finset Circ := Work.KMTAreas.A7.diffFreqs ρ l with hA
  -- the two kernel identities
  have hK0 : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (iwSymbolSet ({0} : Finset Circ) (periodize ψ)) j = Work.KMTAreas.A7.cw ψ j := by
    intro j
    have h := TleKer_zero_eq_cw' ρ hψ j
    rw [Work.KMTPlan.A6.TleKer, iwArithFreqs_zero] at h
    exact h
  have hKl : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize ψ)) j
      = (∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) j α)) * Work.KMTAreas.A7.cw ψ j := by
    intro j
    rw [Work.KMTPlan.A6.IwKernelArithChar A hψ j]
    congr 1
    refine Finset.sum_congr rfl (fun α _ => ?_)
    exact fourier_neg (n := j) (x := α)
  -- the summability of the `j`-series against the bounded `g`
  have hsumm : ∀ α : Circ, Summable fun j : ℤ =>
      (starRingEnd ℂ) (fourier (T := 1) j α) * (Work.KMTAreas.A7.cw ψ j * g (x - j)) := by
    intro α
    refine Summable.of_norm_bounded (hcw.mul_right Cg) fun j => ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖(starRingEnd ℂ) (fourier (T := 1) j α)‖ = 1 := by
      rw [RCLike.norm_conj, fourier_apply]
      exact _root_.Circle.norm_coe _
    rw [h1, one_mul]
    exact mul_le_mul_of_nonneg_left (hg (x - j)) (norm_nonneg _)
  -- the left-hand side
  have hL : Work.KMTAreas.A7.Tm ρ l ψ g x
      = ∑ α ∈ A, ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw ψ j * g (x - j)) := by
    rw [Work.KMTAreas.A7.Tm, Work.KMTAreas.A7.iwConv_eq_tsum_mul]
    have hstep : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize ψ)) j
          * g (x - j)
        = ∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) j α)
            * (Work.KMTAreas.A7.cw ψ j * g (x - j)) := by
      intro j
      rw [hKl j, mul_assoc, Finset.sum_mul]
    rw [tsum_congr hstep]
    exact Summable.tsum_finsetSum (s := A) fun α _ => hsumm α
  -- the right-hand side
  have hR : ∀ α : Circ, (starRingEnd ℂ) (fourier (T := 1) x α)
        * Work.KMTAreas.A7.Tle ρ 0 ψ (fun y : ℤ => fourier (T := 1) y α * g y) x
      = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw ψ j * g (x - j)) := by
    intro α
    rw [Work.KMTAreas.A7.Tle,
      Work.KMTAreas.A7.iwConv_eq_tsum_mul]
    show (starRingEnd ℂ) (fourier (T := 1) x α)
        * (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
            (iwSymbolSet (iwArithFreqs ρ 0) (periodize ψ)) j
            * (fourier (T := 1) (x - j) α * g (x - j)))
      = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw ψ j * g (x - j))
    have h0 : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (iwSymbolSet (iwArithFreqs ρ 0) (periodize ψ)) j = Work.KMTAreas.A7.cw ψ j := by
      intro j
      rw [iwArithFreqs_zero]
      exact hK0 j
    rw [show (starRingEnd ℂ) (fourier (T := 1) x α)
          * (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
              (iwSymbolSet (iwArithFreqs ρ 0) (periodize ψ)) j
              * (fourier (T := 1) (x - j) α * g (x - j)))
        = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) x α)
              * (Work.Analysis.IWMultiplier.iwKernel
                  (iwSymbolSet (iwArithFreqs ρ 0) (periodize ψ)) j
                  * (fourier (T := 1) (x - j) α * g (x - j))) from
        (tsum_mul_left).symm]
    refine tsum_congr fun j => ?_
    rw [h0 j]
    rw [show (starRingEnd ℂ) (fourier (T := 1) x α)
          * (Work.KMTAreas.A7.cw ψ j * (fourier (T := 1) (x - j) α * g (x - j)))
        = ((starRingEnd ℂ) (fourier (T := 1) x α) * fourier (T := 1) (x - j) α)
            * (Work.KMTAreas.A7.cw ψ j * g (x - j)) from by ring]
    rw [Work.KMTPlan.A6.BoundedHMain.fourier_conj_mul_sub' α x j]
  rw [hL]
  exact Finset.sum_congr rfl fun α _ => (hR α).symm

/-! ## The `g`-side estimate at bounded height -/

/-- The `ℓ²`-norm of a unit-modulus modulation of a sequence is unchanged. -/
theorem eLpNorm_fourier_mul (α : Circ) (g : ℤ → ℂ) :
    eLpNorm (fun y : ℤ => fourier (T := 1) y α * g y) 2 MeasureTheory.Measure.count
      = eLpNorm g 2 MeasureTheory.Measure.count := by
  have hnorm : ∀ y : ℤ, ‖fourier (T := 1) y α‖ₑ = 1 := by
    intro y
    rw [← ofReal_norm, fourier_apply, _root_.Circle.norm_coe, ENNReal.ofReal_one]
  apply le_antisymm
  · refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
      (f := fun y : ℤ => fourier (T := 1) y α * g y) (g := g) (fun y => ?_)
    rw [enorm_mul, hnorm y, one_mul]
  · refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := g)
      (g := fun y : ℤ => fourier (T := 1) y α * g y) (fun y => ?_)
    rw [enorm_mul, hnorm y, one_mul]

/-- **The `g`-side linear variational estimate of the mixed range at bounded height.**  For
`0 < ρ ≤ 1`, `2 < r` and a height bound `B`, there is `K : ℝ≥0 → ℝ≥0` such that for every
`Λ`-lacunary scale sequence `a` with `a n ≥ 1`, every `l₂ ≤ B`, `k₂ ≤ B`, every `t ∈ [1/2,1]` and
every bounded `g`,

  `‖ V^r_n (1_{loGuard} Tm ρ l₂ (φ̃_{⌊a n⌋,t}) g) ‖_{ℓ²} ≤ K(Λ) ‖g‖_{ℓ²}`. -/
theorem gsideBoundedHeight (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (Cg : ℝ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) → l₂ ≤ B → k₂ ≤ B →
        t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ y : ℤ, ‖g y‖ ≤ Cg) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
                Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                  (Nat.floor (a n)) k₂ t) g x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨C, hC⟩ :=
    Work.KMTPlan.A6.LowModApproxBoundedH.plainVarG_lev0 P hd r hr C₀ hC₀ ρ hρ B
  refine ⟨fun Λ => ((iwArithFreqs ρ B).card : NNReal) * C Λ, ?_⟩
  intro a Λ l₂ k₁ k₂ t g Cg hΛ ha ha1 hl₂B hk₂B ht hg
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  -- the per-scale lift, with the clip `core`
  have hlift : ∀ n : ℕ, ∀ x : ℤ,
      (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
        Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree
          (Nat.floor (a n)) k₂ t) g x
      else 0)
      = ∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
          (starRingEnd ℂ) (fourier (T := 1) x α)
            * (if Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n then
                Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                  (Nat.floor (a n)) k₂ t) (fun y : ℤ => fourier (T := 1) y α * g y) x
              else 0) := by
    intro n x
    have hg' : ∀ y : ℤ, ‖g y‖ ≤ Cg := hg
    have hlift' := Tm_eq_sum_modulation ρ l₂
      (Work.KMTPlan.A6.symp_integrable_varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
      g Cg hg' (Work.KMTPlan.A6.symp_summable_cw_varphitildeNt P P.natDegree
        (Nat.floor (a n)) k₂ t) x
    by_cases hgrd : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
    · have hcore : Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n := by
        rw [← loGuard_eq_core]; exact hgrd
      rw [if_pos hgrd, hlift']
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [if_pos hcore]
    · have hcore : ¬ Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n := by
        rw [← loGuard_eq_core]; exact hgrd
      rw [if_neg hgrd]
      refine (Finset.sum_eq_zero (fun α _ => ?_)).symm
      rw [if_neg hcore, mul_zero]
  -- pointwise in `x`, subadditivity over the exact-height frequencies
  have hpt : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree
              (Nat.floor (a n)) k₂ t) g x
          else 0)
        ≤ ∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              if Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n then
                Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                  (Nat.floor (a n)) k₂ t) (fun y : ℤ => fourier (T := 1) y α * g y) x
              else 0) := by
    intro x
    have hfam : (fun n : ℕ =>
          if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree
              (Nat.floor (a n)) k₂ t) g x
          else 0)
        = fun n : ℕ => ∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
            (starRingEnd ℂ) (fourier (T := 1) x α)
              * (if Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n then
                  Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                    (Nat.floor (a n)) k₂ t) (fun y : ℤ => fourier (T := 1) y α * g y) x
                else 0) := by
      funext n
      exact hlift n x
    rw [hfam]
    refine (Work.KMTAreas.A7.variationalNorm_finset_sum_le hr1 _ _).trans ?_
    refine Finset.sum_le_sum (fun α _ => ?_)
    have hsm : (fun n : ℕ => (starRingEnd ℂ) (fourier (T := 1) x α)
          * (if Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                (Nat.floor (a n)) k₂ t) (fun y : ℤ => fourier (T := 1) y α * g y) x
            else 0))
        = (starRingEnd ℂ) (fourier (T := 1) x α) • (fun n : ℕ =>
            if Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                (Nat.floor (a n)) k₂ t) (fun y : ℤ => fourier (T := 1) y α * g y) x
            else 0) := rfl
    rw [hsm, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1]
    have hnorm : ‖(starRingEnd ℂ) (fourier (T := 1) x α)‖ₑ = 1 := by
      rw [← ofReal_norm, RCLike.norm_conj, fourier_apply, _root_.Circle.norm_coe,
        ENNReal.ofReal_one]
    rw [hnorm, one_mul]
  -- the `ℓ²` estimate
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree
              (Nat.floor (a n)) k₂ t) g x
          else 0)) 2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          ∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              if Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n then
                Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                  (Nat.floor (a n)) k₂ t) (fun y : ℤ => fourier (T := 1) y α * g y) x
              else 0)) 2 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hpt x)
  refine hmono.trans ?_
  set M : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hM
  refine (Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal (μ := MeasureTheory.Measure.count)
    (p := 2) (by norm_num) (s := Work.KMTAreas.A7.diffFreqs ρ l₂)
    (g := fun α x => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
      if Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n then
        Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
          (Nat.floor (a n)) k₂ t) (fun y : ℤ => fourier (T := 1) y α * g y) x
      else 0))
    (fun α _ => (measurable_of_countable _).aemeasurable)).trans ?_
  -- the per-frequency estimate
  have hstep : ∀ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ =>
          if Work.KMTAreas.A7.core ρ C₀ l₂ 0 k₁ k₂ a n then
            Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
              (Nat.floor (a n)) k₂ t) (fun y : ℤ => fourier (T := 1) y α * g y) x
          else 0)) 2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * M := by
    intro α _
    have hthis := hC a Λ l₂ k₁ k₂ t (fun y : ℤ => fourier (T := 1) y α * g y)
      hΛ ha ha1 hk₂B ht
    refine hthis.trans ?_
    rw [eLpNorm_fourier_mul α g]
  refine (Finset.sum_le_sum hstep).trans ?_
  -- the cardinality bookkeeping
  have hcard : ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ENNReal)
      ≤ ((iwArithFreqs ρ B).card : ENNReal) := by
    have h1 : (Work.KMTAreas.A7.diffFreqs ρ l₂).card ≤ (iwArithFreqs ρ B).card :=
      Finset.card_le_card fun α hα =>
        iwArithFreqs_mono hρ hρ1 hl₂B (lp_diffFreqs_subset ρ l₂ hα)
    exact_mod_cast h1
  rw [Finset.sum_const, nsmul_eq_mul]
  calc ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ENNReal) * ((C Λ : ENNReal) * M)
      = (((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ENNReal) * (C Λ : ENNReal)) * M := by ring
    _ ≤ (((iwArithFreqs ρ B).card : ENNReal) * (C Λ : ENNReal)) * M :=
        mul_le_mul' (mul_le_mul' hcard le_rfl) le_rfl
    _ = ((((iwArithFreqs ρ B).card : NNReal) * C Λ : NNReal) : ENNReal) * M := by
        rw [ENNReal.coe_mul, ENNReal.coe_natCast]

end

end Work.KMTPlan.A6.BoundedHMain
