import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.lowBandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.atomIntegrableG` — integrability of a single cubic atom

The frozen sibling `Work.BoseBoxFock.FRK.cIPn_potCubic_integrable` proves that
`star Θ · potCubic B f g L E Θ` is integrable at the weak mode bundle.  Its auxiliary predicate
`Nice` (measurable / everywhere bounded / supported in the product box `boxPow d ℓ`) is however
`private`, so it is re-established here, in the present namespace, for the **atom** statement that
the low-band chapter consumes: for the single pair `(s,k)` and the slot sum
`B := fun T => Work.BoseDict.boxSlotSum e T`,

    `x ↦ star (Θ x) * potCubicAtom B f g s k Θ x`   is integrable.

The argument is the same closure argument as in that file: `potCubicAtom` is a finite combination
of one- and two-fold applications of `boxSlotSum e T` to `Θ`
(`Work.MB.boxSlotSum_bdd` preserves each of the three properties), the product with `star Θ`
preserves them too, and `Work.MB.integrable_of_bdd_of_support` finishes because
`Work.MB.volume_boxPow_lt_top` is finite.

Note that neither `0 < ℓ` nor any positivity in the mode bound is needed: the product box
`Work.MB.boxPow d ℓ` has finite volume for every real `ℓ`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PotCubicLowBandAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The regularity class and its closure properties -/

/-- A state on the `d`-particle box `Work.BoseDict.Xn d` is *nice* at box side `ℓ` if it is
measurable, everywhere bounded and supported in `Work.MB.boxPow d ℓ`. -/
private structure Nice (d : ℕ) (ℓ : ℝ) (Ψ : Work.BoseDict.Xn d → ℂ) : Prop where
  meas : Measurable Ψ
  bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Ψ x‖ ≤ C
  supp : Function.support Ψ ⊆ Work.MB.boxPow d ℓ

private lemma nice_add {d : ℕ} {ℓ : ℝ} {Ψ Φ : Work.BoseDict.Xn d → ℂ}
    (hΨ : Nice d ℓ Ψ) (hΦ : Nice d ℓ Φ) : Nice d ℓ (Ψ + Φ) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hΨ.bdd
  obtain ⟨C₂, hC₂0, hC₂⟩ := hΦ.bdd
  refine ⟨hΨ.meas.add hΦ.meas, ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x => ?_⟩, ?_⟩
  · rw [Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hC₁ x) (hC₂ x))
  · intro x hx
    by_cases h : Ψ x = 0
    · exact hΦ.supp (by simpa [Pi.add_apply, h] using hx)
    · exact hΨ.supp h

private lemma nice_sub {d : ℕ} {ℓ : ℝ} {Ψ Φ : Work.BoseDict.Xn d → ℂ}
    (hΨ : Nice d ℓ Ψ) (hΦ : Nice d ℓ Φ) : Nice d ℓ (Ψ - Φ) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hΨ.bdd
  obtain ⟨C₂, hC₂0, hC₂⟩ := hΦ.bdd
  refine ⟨hΨ.meas.sub hΦ.meas, ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x => ?_⟩, ?_⟩
  · rw [Pi.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hC₁ x) (hC₂ x))
  · intro x hx
    by_cases h : Ψ x = 0
    · exact hΦ.supp (by simpa [Pi.sub_apply, h] using hx)
    · exact hΨ.supp h

private lemma nice_conj {d : ℕ} {ℓ : ℝ} {Ψ : Work.BoseDict.Xn d → ℂ} (h : Nice d ℓ Ψ) :
    Nice d ℓ (fun x => star (Ψ x)) := by
  obtain ⟨C, hC0, hC⟩ := h.bdd
  refine ⟨Complex.continuous_conj.measurable.comp h.meas, ⟨C, hC0, fun x => ?_⟩, ?_⟩
  · simpa using hC x
  · intro x hx
    exact h.supp (by simpa using hx)

private lemma nice_mul {d : ℕ} {ℓ : ℝ} {Ψ Φ : Work.BoseDict.Xn d → ℂ}
    (hΨ : Nice d ℓ Ψ) (hΦ : Nice d ℓ Φ) : Nice d ℓ (fun x => Ψ x * Φ x) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hΨ.bdd
  obtain ⟨C₂, hC₂0, hC₂⟩ := hΦ.bdd
  refine ⟨hΨ.meas.mul hΦ.meas,
    ⟨C₁ * C₂, mul_nonneg hC₁0 hC₂0, fun x => ?_⟩, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul (hC₁ x) (hC₂ x) (norm_nonneg _) hC₁0
  · intro x hx
    exact hΦ.supp (by
      intro h0
      exact hx (by simp [h0]))

/-! ## 2. The slot sum preserves the class -/

/-- `Work.BoseDict.boxSlotSum e T` preserves `Nice` at the weak mode bundle. -/
private lemma nice_boxSlotSum {m d : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Ψ : Work.BoseDict.Xn d → ℂ} (h : Nice d ℓ Ψ) :
    Nice d ℓ (Work.BoseDict.boxSlotSum e T Ψ) := by
  obtain ⟨C, hC0, hC⟩ := h.bdd
  obtain ⟨hm, hb, hs⟩ :=
    (Work.MB.boxSlotSum_bdd (d := d) (ℓ := ℓ) hmeas hbdd hsupp T).2 Ψ h.meas ⟨C, hC⟩
  exact ⟨hm, hb, hs h.supp⟩

/-! ## 3. The atom -/

/-- The two-slot atom `(B T₁ ∘ B T₂)Θ - B (T₁ ∘ T₂)Θ + (B T₃ ∘ B T₄)Θ - B (T₃ ∘ T₄)Θ`. -/
private lemma nice_atom {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → (Work.BoseDict.Xn d → ℂ) → (Work.BoseDict.Xn d → ℂ)}
    (hB : ∀ T Ψ, Nice d ℓ Ψ → Nice d ℓ (B T Ψ))
    {T₁ T₂ T₃ T₄ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {Θ : Work.BoseDict.Xn d → ℂ}
    (hΘ : Nice d ℓ Θ) :
    Nice d ℓ ((B T₁ (B T₂ Θ) - B (T₁.comp T₂) Θ) +
      (B T₃ (B T₄ Θ) - B (T₃.comp T₄) Θ)) := by
  refine nice_add (nice_sub ?_ (hB (T₁.comp T₂) Θ hΘ)) (nice_sub ?_ (hB (T₃.comp T₄) Θ hΘ))
  · exact hB T₁ _ (hB T₂ Θ hΘ)
  · exact hB T₃ _ (hB T₄ Θ hΘ)

/-- The `(s,k)`-atom of the cubic row is nice. -/
private lemma nice_potCubicAtom {m d : ℕ} [NeZero m] {ℓ : ℝ} {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {B : ((Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) → (Work.BoseDict.Xn d → ℂ) → (Work.BoseDict.Xn d → ℂ)}
    (hB : ∀ T Ψ, Nice d ℓ Ψ → Nice d ℓ (B T Ψ))
    {Θ : Work.BoseDict.Xn d → ℂ} (hΘ : Nice d ℓ Θ) (f g : Mode → Fin m → ℝ) (s k : Mode) :
    Nice d ℓ (Work.BoseBoxFock.FRK.potCubicAtom B f g s k Θ) := by
  simp only [Work.BoseBoxFock.FRK.potCubicAtom, Function.comp_apply, Pi.sub_apply, Pi.add_apply]
  exact nice_atom hB hΘ

/-! ## 4. The target -/

theorem atomIntegrableG {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hemeas : ∀ l, Measurable (e l))
    (heb : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hes : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Work.BoseDict.Xn d → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow d ℓ)
    (f g : Mode → Fin m → ℝ) (s k : Mode) (E : Work.BoseB7.Q3Env Mode) :
    MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn d =>
        star (Θ x) * Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
          f g s k Θ x) := by
  classical
  have hΘ : Nice d ℓ Θ := by
    obtain ⟨C, hC⟩ := hΘb
    exact ⟨hΘm, ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩, hΘs⟩
  have hB : ∀ T Ψ, Nice d ℓ Ψ →
      Nice d ℓ ((fun T => Work.BoseDict.boxSlotSum e T) T Ψ) :=
    fun T Ψ h => nice_boxSlotSum hemeas heb hes T h
  have hprod : Nice d ℓ (fun x : Work.BoseDict.Xn d =>
      star (Θ x) * Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T)
        f g s k Θ x) :=
    nice_mul (nice_conj hΘ) (nice_potCubicAtom (ℓ := ℓ) hB hΘ f g s k)
  obtain ⟨hm, ⟨C, hC0, hC⟩, hs⟩ := hprod
  refine Work.MB.integrable_of_bdd_of_support (Work.MB.measurableSet_boxPow d ℓ)
    (Work.MB.volume_boxPow_lt_top d ℓ) hm.aestronglyMeasurable hC (fun x hx => ?_)
  by_contra h
  exact hx (hs h)

end Work.BoseBoxFock.PotCubicLowBandAux
