import Mathlib
import Submission.Work.NN.Core.Lev.moserSourceAux
import Submission.Work.NN.Core.Lev.srcWLipschitz
import Submission.Work.NN.Core.Lev2.moserSupIntCacc
import Submission.Work.NN.Core.Lev2.eLpNorm_maxNorm_unif

namespace Work.NN.Core.Lev

open MeasureTheory
open scoped ENNReal

/-- **Assembly of the sourced Moser mean-value estimate from the shifted power Caccioppoli
family.**

The hypothesis is exactly the *sharp, shifted* power-Caccioppoli family for the truncated modulus
`W := srcW u Λ = fun z => max ‖u z‖ Λ` -- on the level-`k` power `W^k` it reads

`∫ φ² ‖D(W^k)‖² ≤ C₀ (k² Λ² ∫ φ² W^{2k-2} + ∫ ‖Dφ‖² W^{2k})`.

Under it, `u` obeys the mean-value (`sup ≤ C · L²`) bound on the smaller polydisc `polydisc 0 σ` in
terms of `‖u‖_{L²(polydisc 0 ρ)}` and `Λ`.

The constant `C` is independent of `Λ` and `u`.  The proof splits the shell `σ < ρ' < ρ` with
`ρ' := (σ+ρ)/2`, so that `W` is Lipschitz on `polydisc 0 ρ'` (`srcWLipschitz`) and the family
restricts to `ρ'` (`srcHypRestrict`); then `moserSupIntCacc` -- the crux -- bounds `W` on
`polydisc 0 σ` by `‖W‖_{L²(polydisc 0 ρ')}`, and `eLpNorm_maxNorm_unif` converts the latter into
`‖u‖_{L²(polydisc 0 ρ)} + Λ`, uniformly in `Λ` and `u`. -/
theorem moserSourceGlue {n : ℕ} (hn : 0 < n) {σ ρ : Fin n → ℝ}
    (hσ0 : ∀ j, 0 < σ j) (hρ0 : ∀ j, 0 < ρ j) (hσρ : ∀ j, σ j < ρ j)
    {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ u : Work.NN.Core.Cn n → ℂ,
        ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
        (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ,
              (φ z)^2 * ‖fderiv ℝ (fun w => (Work.NN.Core.Lev.srcW u Λ w)^k) z‖^2
            ≤ C₀ * ((k:ℝ)^2 * Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ,
                    (φ z)^2 * (Work.NN.Core.Lev.srcW u Λ z)^(2*k-2))
                  + (∫ z in Work.CR.Flat.polydisc 0 ρ,
                    ‖fderiv ℝ φ z‖^2 * (Work.NN.Core.Lev.srcW u Λ z)^(2*k)))) →
        ∀ z ∈ Work.CR.Flat.polydisc 0 σ,
          ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal C *
            (MeasureTheory.eLpNorm u 2
                (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))
              + ENNReal.ofReal Λ) := by
  -- the intermediate shell radius `ρ'` strictly between `σ` and `ρ`
  set ρ' : Fin n → ℝ := fun i => (σ i + ρ i) / 2 with hρ'def
  have hσρ' : ∀ i, σ i < ρ' i := fun i => by simp only [hρ'def]; linarith [hσρ i]
  have hρ'ρ : ∀ i, ρ' i < ρ i := fun i => by simp only [hρ'def]; linarith [hσρ i]
  have hρ'0 : ∀ i, 0 < ρ' i := fun i => lt_trans (hσ0 i) (hσρ' i)
  -- the crux: sharp shifted family on `polydisc 0 ρ'` ⟹ sup bound on `polydisc 0 σ`
  obtain ⟨Cx, hCx0, hcrux⟩ :=
    Work.NN.Core.Lev2.moserSupIntCacc (n := n) (σ := σ) (ρ := ρ') hn hσ0 hρ'0 hσρ'
      (A := C₀) hC₀
  -- the uniform `L²`-bound for the truncated modulus
  obtain ⟨C₂, _hC₂0, hC₂⟩ :=
    Work.NN.Core.Lev2.eLpNorm_maxNorm_unif (n := n) (ρ := ρ) (ρ' := ρ') hρ'ρ
  refine ⟨Cx * C₂, by positivity, ?_⟩
  intro Λ hΛ u hu hH z hz
  -- `W := srcW u Λ` is Lipschitz on `polydisc 0 ρ'`
  obtain ⟨K, hK⟩ :=
    Work.NN.Core.Lev.srcWLipschitz (n := n) (ρ := ρ) (ρ' := ρ') hρ'ρ hu Λ
  -- the family restricts to the shell `polydisc 0 ρ'`
  have hfam :=
    Work.NN.Core.Lev2.srcHypRestrict (n := n) (ρ := ρ) (ρ' := ρ')
      (fun j => (hρ'ρ j).le) (A := C₀) (Λ := Λ)
      (W := Work.NN.Core.Lev.srcW u Λ) hH
  have hΛW : ∀ w, Λ ≤ Work.NN.Core.Lev.srcW u Λ w := fun w => le_max_right _ _
  have hmeas : AEStronglyMeasurable u (MeasureTheory.volume.restrict
      (Work.CR.Flat.polydisc 0 ρ)) :=
    hu.continuousOn.aestronglyMeasurable (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
  -- the sup bound for the truncated modulus on `polydisc 0 σ`
  have h1 : ENNReal.ofReal (Work.NN.Core.Lev.srcW u Λ z) ≤ ENNReal.ofReal Cx *
      MeasureTheory.eLpNorm (Work.NN.Core.Lev.srcW u Λ) 2
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ')) :=
    hcrux (Λ := Λ) hΛ (K := K) (W := Work.NN.Core.Lev.srcW u Λ) hK hΛW hfam z hz
  have h2 : ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal (Work.NN.Core.Lev.srcW u Λ z) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have h3 := hC₂ (Λ := Λ) hΛ (u := u) hmeas
  refine h2.trans (h1.trans ?_)
  calc ENNReal.ofReal Cx * MeasureTheory.eLpNorm (Work.NN.Core.Lev.srcW u Λ) 2
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ'))
      = ENNReal.ofReal Cx * MeasureTheory.eLpNorm (fun w => max ‖u w‖ Λ) 2
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ')) := rfl
    _ ≤ ENNReal.ofReal Cx * (ENNReal.ofReal C₂ *
          (MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict
              (Work.CR.Flat.polydisc 0 ρ))
            + ENNReal.ofReal Λ)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ENNReal.ofReal (Cx * C₂) *
          (MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict
              (Work.CR.Flat.polydisc 0 ρ))
            + ENNReal.ofReal Λ) := by
        rw [ENNReal.ofReal_mul hCx0.le]; ring

end Work.NN.Core.Lev
