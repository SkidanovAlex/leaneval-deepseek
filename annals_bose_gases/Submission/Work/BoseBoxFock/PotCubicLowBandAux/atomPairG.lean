import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRK.lowBandDefs
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.bW4slotEqBW4G
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.atomPairG` — the `(s,k)`-atom's self-pairing is the
FS pairing `2 Re ⟪X,Y⟫`

The atom `Work.BoseBoxFock.FRK.potCubicAtom B f g s k Θ` is the sum of the two four-letter words
`bW4slot e e₀ (g s) (f (s−k)) (f k) d Θ` and `bW4slot e (f k) (f (s−k)) (g s) e₀ d Θ`.  Each of
them is turned into a *ladder* word by the clash-free dictionary
(`PotCubicLowBandAux.bW4slotEqBW4G`), and the ladder word self-pairs by
(`PotCubicLowBandAux.selfPairG.cIPn_bW4_selfG`):

    `cIPn (d+2) Θ (bW4 e w₁ w₂ v₁ v₂ d Θ) = cIPn d (a_{w₂}a_{w₁}Θ) (a_{v₁}a_{v₂}Θ)`.

Hence, with

    `X := a_{f(s−k)} a_{f k} Θ ,   Y := a_{g s} a_{e₀} Θ`      (`a_w := boxAnnOf e w`),

    `cIPn (d+2) Θ (atom_{s,k} Θ) = cIPn d X Y + cIPn d Y X = 2 Re (cIPn d X Y)`

(the last spelling is what the Cauchy–Schwarz step of the low band consumes).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PotCubicLowBandAux

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Integrability of `star Θ · (a slot word applied to Φ)` -/

/-- `star Ψ · boxSlotSum e T Φ` is integrable as soon as `Ψ`, `Φ` are measurable, everywhere
bounded and supported in the box `boxPow d ℓ` (then `boxSlotSum e T Φ` is measurable, bounded and
box-supported by `Work.MB.boxSlotSum_bdd`, and the finiteness of the box gives the `L¹` bound). -/
private lemma integrable_star_mul_boxSlotSumG {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) {Ψ Φ : Xn d → ℂ}
    (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C)
    (hΦm : Measurable Φ) (hΦb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : Function.support Φ ⊆ Work.MB.boxPow d ℓ) :
    Integrable (fun x : Xn d => star (Ψ x) * boxSlotSum e T Φ x) := by
  obtain ⟨hSm, ⟨C', hC'0, hC'b⟩, hSsupp⟩ :=
    (Work.MB.boxSlotSum_bdd hmeas hbdd hsupp T).2 Φ hΦm hΦb
  obtain ⟨C, hC⟩ := hΨb
  refine Work.MB.integrable_of_bdd_of_support (C := max C 0 * max C' 0)
    (Work.MB.measurableSet_boxPow d ℓ) (Work.MB.volume_boxPow_lt_top d ℓ)
    (((continuous_star.measurable.comp hΨm).mul hSm)).aestronglyMeasurable ?_ ?_
  · intro x
    rw [norm_mul]
    refine mul_le_mul ?_ ((hC'b x).trans (le_max_left _ _)) (norm_nonneg _)
      (le_max_right _ _)
    exact (norm_star _).trans_le ((hC x).trans (le_max_left _ _))
  · intro x hx
    have hS' : Function.support (boxSlotSum e T Φ) ⊆ Work.MB.boxPow d ℓ := hSsupp hΦsupp
    have hzero : boxSlotSum e T Φ x = 0 :=
      Function.notMem_support.mp (fun h => hx (hS' h))
    rw [hzero, mul_zero]

/-- `star Θ · bW4slot e w₁ w₂ v₁ v₂ d Θ` is integrable at the weak bundle. -/
private lemma integrable_star_mul_bW4slotG {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w₁ w₂ v₁ v₂ : Fin m → ℝ) {Θ : Xn (d + 2) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ) :
    Integrable (fun x : Xn (d + 2) => star (Θ x) * bW4slot e w₁ w₂ v₁ v₂ d Θ x) := by
  have hΛ := (Work.MB.boxSlotSum_bdd hmeas hbdd hsupp (rankOnePair w₂ v₂)).2 Θ hΘm hΘb
  have hpiece1 : Integrable (fun x : Xn (d + 2) => star (Θ x) *
      boxSlotSum e (rankOnePair w₁ v₁) (boxSlotSum e (rankOnePair w₂ v₂) Θ) x) :=
    integrable_star_mul_boxSlotSumG hmeas hbdd hsupp (rankOnePair w₁ v₁)
      hΘm hΘb hΛ.1 ⟨hΛ.2.1.choose, hΛ.2.1.choose_spec.2⟩ (hΛ.2.2 hΘsupp)
  have hpiece2 : Integrable (fun x : Xn (d + 2) => star (Θ x) *
      boxSlotSum e ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Θ x) :=
    integrable_star_mul_boxSlotSumG hmeas hbdd hsupp _ hΘm hΘb hΘm hΘb hΘsupp
  rw [show (fun x : Xn (d + 2) => star (Θ x) * bW4slot e w₁ w₂ v₁ v₂ d Θ x)
      = (fun x : Xn (d + 2) => star (Θ x) *
          boxSlotSum e (rankOnePair w₁ v₁) (boxSlotSum e (rankOnePair w₂ v₂) Θ) x)
        - (fun x : Xn (d + 2) => star (Θ x) *
          boxSlotSum e ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Θ x) from by
      funext x
      rw [bW4slot_apply]
      simp only [Pi.sub_apply, mul_sub]]
  exact hpiece1.sub hpiece2

/-! ## 2. The atom is the sum of the two four-letter slot words -/

/-- The definitional identification of the `(s,k)`-atom with the two slot words. -/
theorem potCubicAtom_eq_bW4slotG {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] [DecidableEq Mode] {e : Fin m → Ω → ℂ}
    (f g : Mode → Fin m → ℝ) (s k : Mode) (d : ℕ) (Θ : Xn (d + 2) → ℂ) :
    Work.BoseBoxFock.FRK.potCubicAtom (fun T => boxSlotSum e T) f g s k Θ
      = bW4slot e (evec0 m) (g s) (f (s - k)) (f k) d Θ
        + bW4slot e (f k) (f (s - k)) (g s) (evec0 m) d Θ := rfl

/-! ## 3. The pairing -/

/-- **The FS pairing of the `(s,k)`-atom.**  With `a_w = boxAnnOf e w`,

    `cIPn (d+2) Θ (atom_{s,k} Θ) = cIPn d X Y + cIPn d Y X`,
    `X := a_{f(s−k)} a_{f k} Θ`,  `Y := a_{g s} a_{e₀} Θ`. -/
theorem cIPn_atom_eq_pairG {m d : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (s k : Mode)
    {Θ : Xn (d + 2) → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Xn (d + 2)), Θ (x ∘ σ) = Θ x) :
    Work.BoseDict.cIPn (d + 2) Θ
        (Work.BoseBoxFock.FRK.potCubicAtom (fun T => boxSlotSum e T) f g s k Θ)
      = Work.BoseDict.cIPn d
          (boxAnnOf e (f (s - k)) d (boxAnnOf e (f k) (d + 1) Θ))
          (boxAnnOf e (g s) d (boxAnnOf e (evec0 m) (d + 1) Θ))
        + Work.BoseDict.cIPn d
          (boxAnnOf e (g s) d (boxAnnOf e (evec0 m) (d + 1) Θ))
          (boxAnnOf e (f (s - k)) d (boxAnnOf e (f k) (d + 1) Θ)) := by
  obtain ⟨CΦ, hCΦ⟩ := hΘb
  have hΘb' : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := ⟨CΦ, hCΦ⟩
  have hΘsym' : ∀ σ : Equiv.Perm (Fin (d + 2)), (fun x => Θ (x ∘ ⇑σ)) = Θ :=
    fun σ => funext (hΘsym σ)
  have hInt₁ := integrable_star_mul_bW4slotG hmeas hbdd hsupp
    (evec0 m) (g s) (f (s - k)) (f k) hΘm hΘb' hΘsupp
  have hInt₂ := integrable_star_mul_bW4slotG hmeas hbdd hsupp
    (f k) (f (s - k)) (g s) (evec0 m) hΘm hΘb' hΘsupp
  rw [potCubicAtom_eq_bW4slotG f g s k d Θ, Work.BoseBoxFock.FRK.cIPn_add hInt₁ hInt₂]
  have h1 : Work.BoseDict.cIPn (d + 2) Θ
      (bW4slot e (evec0 m) (g s) (f (s - k)) (f k) d Θ)
      = Work.BoseDict.cIPn d
          (boxAnnOf e (g s) d (boxAnnOf e (evec0 m) (d + 1) Θ))
          (boxAnnOf e (f (s - k)) d (boxAnnOf e (f k) (d + 1) Θ)) := by
    rw [bW4slot_eq_bW4G hmeas hbdd hsupp horth (evec0 m) (g s) (f (s - k)) (f k) d hΘm hΘb'
      (fun σ x => hΘsym σ x)]
    exact cIPn_bW4_selfG hmeas hbdd hsupp hMemLp (evec0 m) (g s) (f (s - k)) (f k)
      hΘm hCΦ hΘsupp hΘsym'
  have h2 : Work.BoseDict.cIPn (d + 2) Θ
      (bW4slot e (f k) (f (s - k)) (g s) (evec0 m) d Θ)
      = Work.BoseDict.cIPn d
          (boxAnnOf e (f (s - k)) d (boxAnnOf e (f k) (d + 1) Θ))
          (boxAnnOf e (g s) d (boxAnnOf e (evec0 m) (d + 1) Θ)) := by
    rw [bW4slot_eq_bW4G hmeas hbdd hsupp horth (f k) (f (s - k)) (g s) (evec0 m) d hΘm hΘb'
      (fun σ x => hΘsym σ x)]
    exact cIPn_bW4_selfG hmeas hbdd hsupp hMemLp (f k) (f (s - k)) (g s) (evec0 m)
      hΘm hCΦ hΘsupp hΘsym'
  rw [h1, h2, add_comm]

end Work.BoseBoxFock.PotCubicLowBandAux
