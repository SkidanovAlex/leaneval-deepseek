import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.ModeExpansion
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.ModeZDeriv
import Submission.Work.FTS.PhiStar.FlatWAux.Decomp
import Submission.Work.FTS.PhiStar.FlatWAux.ModeRescaledSmooth
import Submission.Work.FTS.PhiStar.FlatWAux.iteratedDeriv_resc_expansion
import Submission.Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_Qm
import Submission.Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_G_Qm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

/-- `(∑' m, f m) / c = ∑' m, f m / c`. -/
private lemma tsum_div_tsum (f : ℕ → ℝ) (c : ℝ) : (∑' m : ℕ, f m) / c = ∑' m : ℕ, f m / c := by
  rw [div_eq_mul_inv]
  exact (tsum_mul_right (f := f) (a := c⁻¹)).symm

/-- **The identity of `Fam1Id` in the form in which it is proved**: the three ingredients that
are proved separately (`iteratedDeriv_resc_expansion` for the `1/λ_m`-expansion of the rescaled
radial Green function under `∂_z^k`, and the two summability criteria for the resummed angular
series) are carried as explicit hypotheses. -/
theorem Fam1Id_aux (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) (k : ℕ) (hk : k ≤ 7)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Series.bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (VocabO.phiA α) z'') z'| ≤ C / Gegenbauer.lam m)
    (hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'') z'| ≤ C / Gegenbauer.lam m)
    (hD2 : ∀ m : ℕ, 1 ≤ m →
      iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m (VocabO.phiA α) y) z
        = (∑ j ∈ Finset.range J, (α ^ j / (Radial.lamR m) ^ (j + 1))
              * iteratedDeriv k (fun y => (y + 1) / y * Ajit α j (VocabO.phiA α) y) z)
          + (α ^ J / (Radial.lamR m) ^ J)
              * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
                  (Ajit α J (VocabO.phiA α)) y) z)
    (hSumLead : ∀ j : ℕ, 1 ≤ j → Summable (fun m : ℕ => Series.bmode m ψ
      * ((Radial.lamR m)⁻¹) ^ j * Qm m θ))
    (hSumTail : ∀ (Cg : ℝ), 0 < Cg → ∀ (G : ℕ → ℝ),
      (∀ m : ℕ, 1 ≤ m → |G m| ≤ Cg / Radial.lamR m) →
      Summable (fun m : ℕ => Series.bmode m ψ * ((Radial.lamR m)⁻¹) ^ J * G m * Qm m θ)) :
    (z + 1) ^ k * Work.Spaces.pzIter k
        (fun z' θ' => (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' θ'
          / Work.Construction.s2 θ')) z θ
      = α ^ 2 * ((∑ j ∈ Finset.range J,
            α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Ajit α j (VocabO.phiA α) y) z) * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)) := by
  obtain ⟨CrJ, hCrJ, hrbJ'⟩ := hrbJ
  -- the termwise `z`-differentiation of the mode series (`P1`)
  have hMZ := ModeZDeriv α ψ z θ hz hθ hdec hgr hrb k hk
  -- pulling the constant `1/s2 θ` out of the `z`-derivative
  have hstep1 : Work.Spaces.pzIter k
        (fun z' θ' => (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' θ'
          / Work.Construction.s2 θ')) z θ
      = Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * Series.psiSeries α (RemSource α ψ) z' θ') z θ
          / Work.Construction.s2 θ := by
    rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
    rw [show (fun y : ℝ => (y + 1) / y * (Series.psiSeries α (RemSource α ψ) y θ
            / Work.Construction.s2 θ))
        = fun y : ℝ => ((y + 1) / y * Series.psiSeries α (RemSource α ψ) y θ)
            / Work.Construction.s2 θ from by funext y; ring]
    exact iteratedDeriv_div_const _ _
  -- the `m`-th summand, written through `bmode` and the rescaled radial Green function
  have hmode : ∀ m : ℕ, (z + 1) ^ k * Work.Spaces.pzIter k
        (fun z' θ' => (z' + 1) / z' * (Series.acoeff α m (RemSource α ψ) z'
          * Gegenbauer.eFam m θ')) z θ / Work.Construction.s2 θ
      = (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
          * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m (VocabO.phiA α) y) z
          * Qm m θ := by
    intro m
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    rw [show (fun y : ℝ => (y + 1) / y * (Series.acoeff α m (RemSource α ψ) y
            * Gegenbauer.eFam m θ))
        = fun y : ℝ => Gegenbauer.eFam m θ * ((y + 1) / y * Series.acoeff α m
            (RemSource α ψ) y) from by funext y; ring]
    rw [iteratedDeriv_const_mul_field]
    rw [show (fun y : ℝ => (y + 1) / y * Series.acoeff α m (RemSource α ψ) y)
        = fun y : ℝ => (α ^ 2 * Series.bmode m ψ) * ((y + 1) / y
            * Radial.radGreen α m (VocabO.phiA α) y) from by
          funext y; rw [Series.acoeff_RemSource]; ring]
    rw [iteratedDeriv_const_mul_field]
    simp only [Qm]
    ring
  -- the `λ_m^{-1}`-bound of the remainder radial slot, from the flat hypothesis `hrbJ`
  have hGbd : ∀ m : ℕ, 1 ≤ m →
      |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
          (Ajit α J (VocabO.phiA α)) y) z| ≤ CrJ / Radial.lamR m := by
    intro m hm
    have h := hrbJ' m hm k hk z hz
    have hpow : (1 : ℝ) ≤ (z + 1) ^ k := one_le_pow₀ (by linarith)
    have h1 : |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
          (Ajit α J (VocabO.phiA α)) y) z|
        ≤ |(z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
            (Ajit α J (VocabO.phiA α)) y) z| := by
      calc |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z|
          = 1 * |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z| := by ring
        _ ≤ (z + 1) ^ k * |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z| :=
              mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
        _ = |(z + 1) ^ k| * |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z| := by
              rw [abs_of_pos (pow_pos (by linarith : (0 : ℝ) < z + 1) k)]
        _ = |(z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z| := by rw [abs_mul]
    exact le_trans h1 h
  -- summability of the `j`-th leading series, after multiplication by the constants
  have hSumF : ∀ j ∈ Finset.range J, Summable (fun m : ℕ =>
      (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
        * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
            * Ajit α j (VocabO.phiA α) y) z) * Qm m θ) := by
    intro j _
    have hj : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
    have h := hSumLead (j + 1) hj
    refine (h.mul_left ((z + 1) ^ k * α ^ 2 * iteratedDeriv k (fun y => (y + 1) / y
        * Ajit α j (VocabO.phiA α) y) z * α ^ j)).congr (fun m => ?_)
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  -- summability of the remainder series
  have hSumG : Summable (fun m : ℕ =>
      (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
        * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
            * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ) := by
    have h := hSumTail CrJ hCrJ (fun m => iteratedDeriv k (fun y => (y + 1) / y
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) hGbd
    refine (h.mul_left ((z + 1) ^ k * α ^ 2 * α ^ J)).congr (fun m => ?_)
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  -- the remainder series, in the shape of the target
  have htail : (∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
        * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
            * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)
      = α ^ 2 * (α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)) := by
    have h1 : ∀ m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
          * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ
        = α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Radial.lamR m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)) := by
      intro m
      rw [div_eq_mul_inv, ← inv_pow]
      ring
    rw [tsum_congr h1, tsum_mul_left, tsum_mul_left]
    rfl
  -- the main chain
  calc (z + 1) ^ k * Work.Spaces.pzIter k
        (fun z' θ' => (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' θ'
          / Work.Construction.s2 θ')) z θ
      = (z + 1) ^ k * Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * Series.psiSeries α (RemSource α ψ) z' θ') z θ
          / Work.Construction.s2 θ := by
        rw [hstep1]; ring
    _ = (∑' m : ℕ, (z + 1) ^ k * Work.Spaces.pzIter k
            (fun z' θ' => (z' + 1) / z' * (Series.acoeff α m (RemSource α ψ) z'
              * Gegenbauer.eFam m θ')) z θ) / Work.Construction.s2 θ := by
        rw [hMZ]
    _ = ∑' m : ℕ, (z + 1) ^ k * Work.Spaces.pzIter k
            (fun z' θ' => (z' + 1) / z' * (Series.acoeff α m (RemSource α ψ) z'
              * Gegenbauer.eFam m θ')) z θ / Work.Construction.s2 θ := by
        rw [tsum_div_tsum]
    _ = ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
            * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m (VocabO.phiA α) y) z
            * Qm m θ := by
        exact tsum_congr (fun m => hmode m)
    _ = ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
            * ((∑ j ∈ Finset.range J, (α ^ j / (Radial.lamR m) ^ (j + 1))
                  * iteratedDeriv k (fun y => (y + 1) / y * Ajit α j (VocabO.phiA α) y) z)
              + (α ^ J / (Radial.lamR m) ^ J)
                  * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
                      (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        refine tsum_congr (fun m => ?_)
        by_cases hm : m = 0
        · subst hm; rw [hb0]; ring
        · rw [hD2 m (Nat.one_le_iff_ne_zero.mpr hm)]
    _ = ∑' m : ℕ, ((∑ j ∈ Finset.range J, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
                      * Ajit α j (VocabO.phiA α) y) z) * Qm m θ)
              + (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ) := by
        refine tsum_congr (fun m => ?_)
        rw [mul_add, Finset.mul_sum, add_mul, Finset.sum_mul]
    _ = (∑' m : ℕ, ∑ j ∈ Finset.range J, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
                      * Ajit α j (VocabO.phiA α) y) z) * Qm m θ)
          + ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        rw [Summable.tsum_add (summable_sum hSumF) hSumG]
    _ = (∑ j ∈ Finset.range J, ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
                      * Ajit α j (VocabO.phiA α) y) z) * Qm m θ)
          + ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        rw [Summable.tsum_finsetSum hSumF]
    _ = (∑ j ∈ Finset.range J, α ^ 2 * (α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                  * Ajit α j (VocabO.phiA α) y) z)
              * (∑' m : ℕ, Series.bmode m ψ * ((Radial.lamR m)⁻¹) ^ (j + 1) * Qm m θ)))
          + ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [show (∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
              * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
                  * Ajit α j (VocabO.phiA α) y) z) * Qm m θ)
            = (α ^ 2 * α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                  * Ajit α j (VocabO.phiA α) y) z))
                * (∑' m : ℕ, Series.bmode m ψ * ((Radial.lamR m)⁻¹) ^ (j + 1) * Qm m θ) from by
              rw [← tsum_mul_left]
              exact tsum_congr (fun m => by rw [div_eq_mul_inv, ← inv_pow]; ring)]
        ring
    _ = (∑ j ∈ Finset.range J, α ^ 2 * (α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                  * Ajit α j (VocabO.phiA α) y) z) * Wt ψ (j + 1) θ))
          + ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        rfl
    _ = α ^ 2 * ((∑ j ∈ Finset.range J,
            α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Ajit α j (VocabO.phiA α) y) z) * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)) := by
        rw [← Finset.mul_sum, htail]
        ring

/-- **The identity of the first family, `z`-differentiated.** -/
theorem Fam1Id (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'
        = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
            (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
              * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z')
          + (α ^ Work.FTS.PhiStar.FlatWAux.J
              / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                    (Work.FTS.VocabO.phiA α)) z') :
    ∀ k : ℕ, k ≤ 7 →
      (z + 1) ^ k * Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * (Work.FTS.PhiStar.Series.psiSeries α
            (Work.FTS.PhiStar.RemSource α ψ) z' θ' / Work.Construction.s2 θ')) z θ
        = α ^ 2 * ((∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
              α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z'') z)
                * Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1) θ)
            + α ^ Work.FTS.PhiStar.FlatWAux.J
              * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                  * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
                  * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                      * Work.FTS.PhiStar.Radial.radGreen α m
                          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                            (Work.FTS.VocabO.phiA α)) z'') z)
                  * Work.FTS.PhiStar.FlatWAux.Qm m θ)) := by
  intro k hk
  have hrbJ0 := hrbJ
  obtain ⟨CrJ, hCrJ, hrbJ'⟩ := hrbJ0
  have hGbd : ∀ m : ℕ, 1 ≤ m →
      |iteratedDeriv k (fun y => (y + 1) / y * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) y) z|
        ≤ CrJ / Work.FTS.PhiStar.Gegenbauer.lam m := by
    intro m hm
    have h := hrbJ' m hm k hk z hz
    have hpow : (1 : ℝ) ≤ (z + 1) ^ k := one_le_pow₀ (by linarith)
    have h1 : |iteratedDeriv k (fun y => (y + 1) / y * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) y) z|
        ≤ |(z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
            * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) y) z| := by
      calc |iteratedDeriv k (fun y => (y + 1) / y * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) y) z|
          = 1 * |iteratedDeriv k (fun y => (y + 1) / y * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) y) z| := by ring
        _ ≤ (z + 1) ^ k * |iteratedDeriv k (fun y => (y + 1) / y
              * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) y) z| :=
              mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
        _ = |(z + 1) ^ k| * |iteratedDeriv k (fun y => (y + 1) / y
              * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) y) z| := by
              rw [abs_of_pos (pow_pos (by linarith : (0 : ℝ) < z + 1) k)]
        _ = |(z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) y) z| := by rw [abs_mul]
    exact le_trans h1 h
  exact Fam1Id_aux α ψ z θ k hk hz hθ hb0 hdec hgr hrb hrbJ
    (fun m hm => Work.FTS.PhiStar.FlatWAux.iteratedDeriv_resc_expansion α m hm k hz
      (fun z' hz' => hexp m hm z' hz'))
    (fun j hj => Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_Qm ψ θ j hj hθ hb0 hdec hgr)
    (fun Cg hCg G hG => Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_G_Qm ψ θ
      Work.FTS.PhiStar.FlatWAux.J (by norm_num [Work.FTS.PhiStar.FlatWAux.J]) hθ hb0 hdec hgr
      Cg hCg G hG)

end Work.FTS.PhiStar.FlatWAux
