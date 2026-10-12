import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxRealise_reg
import Submission.Work.BoseBoxFock.exists_binary_le_apply
import Submission.Work.BoseBoxFock.sliceTransport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.modelAssembly` — the one-body model assembly of BF3 (`prop:Hamilton2ndQuant`)

The **selection half** of `Work.BoseBoxFock.box_to_model` in its one-body shape: from a box-side
bound on the first-quantised slot sum `Work.BoseDict.boxSlotSum e T` at a box state `Φ`, produce a
*real* model vector `Ψ ≠ 0` in the excited window `ExcWindow M n` whose `dGamma` energy obeys the
same ratio.  It composes the proved layers

* `Work.BoseBoxFock.exists_slice_le_window` (sector + slice selection, with the window condition),
* `Work.BoseBoxFock.sliceModelWindow_deg` (the slice is a model vector, in the window and of degree
  `S.card`),
* `Work.BoseBoxFock.boxSlotSum_slice` + `Work.BoseBoxFock.cIPn_sliceF_eq_sectorSlice` +
  `Work.BoseBoxFock.cIPn_sliceF_self_eq` (the `↥S` ↔ `Fin S.card` transport of the two pairings),
* `Work.BoseBoxFock.boxSlotSum_add_I_smul_boxRealise` (the `ℂ`-linearity of `boxSlotSum` at the two
  model vectors — which is what `Work.BoseBoxFock.exists_binary_le_apply` needs, since `boxSlotSum`
  is *not* additive on all functions),
* `Work.BoseBoxFock.exists_binary_le_apply` (the real/imaginary selection), with the dictionary rows
  `Work.BoseDict.bomb_dGamma_slot`-shaped `hdict` and `Work.BoseDict.boxRealise_cIPn_gen` (`hiso`).

The only remaining input of `Work.BoseBoxFock.box_to_model` is then the box-side *row*
`⟨Φ, A_V Φ⟩ ≤ W2B(Φ)`, whose second half `W2B ≤ wordB + C·errB·‖Φ‖²` is the proved
`Work.BoseBoxFock.bf3a`. -/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. Auxiliary identities -/

/-- The pointwise algebra of the complex splitting of a sesquilinear integrand:
`conj(a + i b) · (c + i e) = conj a · c + conj b · e + i (conj a · e − conj b · c)`. -/
lemma conj_add_I_mul (a b c e : ℂ) :
    (starRingEnd ℂ) (a + Complex.I * b) * (c + Complex.I * e)
      = (starRingEnd ℂ) a * c + (starRingEnd ℂ) b * e
        + Complex.I * ((starRingEnd ℂ) a * e - (starRingEnd ℂ) b * c) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im] <;> ring

/-- `boxSlotSum` of the box realisation is the box realisation of `dGamma`
(`Work.BoseDict.boxRealise_dGamma`, in the direction consumed by the integrability lemmas below). -/
lemma boxSlotSum_eq_boxRealise_dGamma {m d : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Ψ : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e d Ψ)
      = Work.BoseDict.boxRealise e d (Work.BoseB4.dGamma m T Ψ) :=
  (Work.BoseDict.boxRealise_dGamma he hbdd hsupp T Ψ hΨ).symm

/-- A product of two box realisations is integrable (both factors are continuous with compact
support, `Work.BoseBoxFock.boxRealise_reg`). -/
lemma integrable_conj_boxRealise_mul {m d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ} (hcont : ∀ l, Continuous (e l))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ Ψ' : Work.BoseB4.RealFock m) :
    MeasureTheory.Integrable (fun x : Work.BoseDict.Xn d =>
      star (Work.BoseDict.boxRealise e d Ψ x) * Work.BoseDict.boxRealise e d Ψ' x) := by
  have h1 := boxRealise_reg (m := m) (d := d) (ℓ := ℓ) hℓ hcont hbdd hsupp Ψ
  have h2 := boxRealise_reg (m := m) (d := d) (ℓ := ℓ) hℓ hcont hbdd hsupp Ψ'
  have hc : HasCompactSupport (fun x : Work.BoseDict.Xn d =>
      star (Work.BoseDict.boxRealise e d Ψ x)) := h1.2.1.comp_left (g := star) (by simp)
  have hcont' : Continuous (fun x : Work.BoseDict.Xn d =>
      star (Work.BoseDict.boxRealise e d Ψ x)) := Complex.continuous_conj.comp h1.1
  exact integrable_mul_of_hasCompactSupport_of_bounded hc hcont'.aestronglyMeasurable
    (Continuous.bounded_above_of_compact_support hcont' hc)
    h2.1.aestronglyMeasurable (Continuous.bounded_above_of_compact_support h2.1 h2.2.1)

/-- The pairing of the box realisation with the box slot sum is integrable: the second factor is a
`dGamma`-realisation (`Work.BoseDict.boxRealise_dGamma`). -/
lemma integrable_conj_boxRealise_mul_boxSlotSum {m d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ} (hcont : ∀ l, Continuous (e l))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Ψ Ψ' : Work.BoseB4.RealFock m)
    (hΨ' : ∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = d) :
    MeasureTheory.Integrable (fun x : Work.BoseDict.Xn d =>
      star (Work.BoseDict.boxRealise e d Ψ x)
        * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e d Ψ') x) := by
  rw [boxSlotSum_eq_boxRealise_dGamma he hbdd hsupp T Ψ' hΨ']
  exact integrable_conj_boxRealise_mul hℓ hcont hbdd hsupp Ψ (Work.BoseB4.dGamma m T Ψ')

/-! ## 2. The `ℂ`-linearity of `boxSlotSum` at the two model vectors -/

/-- **The additivity of `boxSlotSum` along the complex combination of the two model vectors.**
`boxSlotSum e T` is *not* `ℂ`-linear on all of `Xn d → ℂ` — its Bochner-integral definition makes it
vanish on non-integrable inputs — but it is linear on measurable, pointwise bounded states
(`Work.BoseBoxFock.boxSlotSum_finset_sum`), and `boxRealise e d Ψ` is of that kind
(`Work.BoseBoxFock.boxRealise_reg`).  This is the `hAF` hypothesis of
`Work.BoseBoxFock.exists_binary_le_apply`. -/
theorem boxSlotSum_add_I_smul_boxRealise {m d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (e : Fin m → Ω → ℂ) (hcont : ∀ l, Continuous (e l))
    (hcomp : ∀ l, HasCompactSupport (e l))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Ψ₁ Ψ₂ : Work.BoseB4.RealFock m) :
    Work.BoseDict.boxSlotSum e T
        (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)
      = Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e d Ψ₁)
        + Complex.I • Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e d Ψ₂) := by
  classical
  have hmain := boxSlotSum_finset_sum (m := m) (d := d) e hcont hcomp T
    (Finset.univ : Finset (Fin 2))
    (fun i => ![1, Complex.I] i)
    (fun i => ![Work.BoseDict.boxRealise e d Ψ₁, Work.BoseDict.boxRealise e d Ψ₂] i)
    (fun i => by fin_cases i <;>
      exact ((boxRealise_reg (m := m) (d := d) (ℓ := ℓ) hℓ hcont hbdd hsupp _).1).measurable)
    (fun i => by fin_cases i <;>
      exact (boxRealise_reg (m := m) (d := d) (ℓ := ℓ) hℓ hcont hbdd hsupp _).2.2.1)
  have hL : (fun x : Work.BoseDict.Xn d =>
        ∑ U : Fin 2, ![1, Complex.I] U
          • ![Work.BoseDict.boxRealise e d Ψ₁, Work.BoseDict.boxRealise e d Ψ₂] U x)
      = Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂ := by
    funext x
    rw [Fin.sum_univ_two]
    simp
  have hR : (fun x : Work.BoseDict.Xn d =>
        ∑ U : Fin 2, ![1, Complex.I] U
          • Work.BoseDict.boxSlotSum e T
              (![Work.BoseDict.boxRealise e d Ψ₁, Work.BoseDict.boxRealise e d Ψ₂] U) x)
      = Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e d Ψ₁)
        + Complex.I • Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e d Ψ₂) := by
    funext x
    rw [Fin.sum_univ_two]
    simp
  rw [hL, hR] at hmain
  exact hmain

/-! ## 3. The one-body model assembly -/

/-- **The one-body model assembly.**  If the box-side slot sum `Work.BoseDict.boxSlotSum e T` obeys
the ratio bound `≤ c · ν` at the box state `Φ`, then the model has a nonzero vector in the excited
window `ExcWindow M n` whose `Work.BoseB4.dGamma` energy obeys the *same* ratio. -/
theorem exists_model_le_of_slotSum {m n : ℕ} [NeZero m] {ℓ M : ℝ}
    (hℓ : 0 < ℓ) (e : Fin m → Ω → ℂ)
    (hcont : ∀ l, Continuous (e l)) (hcomp : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hpin : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(volume : MeasureTheory.Measure Ω),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (Φ : Submission.BoseGases.X n → ℝ) (hΦ : Continuous Φ) (hΦcomp : HasCompactSupport Φ)
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Submission.BoseGases.X n => Φ (x ∘ σ)) = Φ)
    (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : ℝ)
    (hpos : 0 < massR (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)))
    (hcle : (∫ x : Submission.BoseGases.X n,
        star ((fun x => ((Φ x : ℝ) : ℂ)) x)
          * Work.BoseDict.boxSlotSum e T (fun x => ((Φ x : ℝ) : ℂ)) x).re
      ≤ c * massR (fun x => ((Φ x : ℝ) : ℂ))) :
    ∃ Ψ : Work.BoseB4.RealFock m, Ψ ≠ 0 ∧ ExcWindow M n Ψ ∧
      Work.BoseB4.bomb m Ψ (Work.BoseB4.dGamma m T Ψ)
        ≤ c * Work.BoseB4.bomb m Ψ Ψ := by
  classical
  set Φc : Submission.BoseGases.X n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΦcdef
  -- the orthonormality in the ℂ-linear form consumed by the dictionary rows
  have he : ∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x)
      = (if l = l' then (1 : ℂ) else 0) := by
    intro l l'
    simpa only [starRingEnd_apply] using horth l l'
  have hΦcsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Submission.BoseGases.X n => Φc (x ∘ σ)) = Φc := by
    intro σ
    funext x
    rw [hΦcdef]
    show ((Φ (x ∘ σ) : ℝ) : ℂ) = ((Φ x : ℝ) : ℂ)
    rw [show Φ (x ∘ σ) = Φ x from congrFun (hΦsym σ) x]
  have hΦccont : Continuous Φc := Complex.continuous_ofReal.comp hΦ
  have hΦccomp : HasCompactSupport Φc :=
    hΦcomp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  -- ## step 1: the sector/slice selection with the window condition
  obtain ⟨S, y, hmass₀, hle₀, hwin₀⟩ :=
    exists_slice_le_window hℓ e hcont hcomp horth hint hbdd hsupp hpin Φ hΦ hΦcomp hΦc
      hΦsym hM hmom T c hpos hcle
  have hmass : 0 < ∫ u : {i // i ∈ S} → Ω, ‖sectorSlice e S Φc y u‖ ^ 2 := by
    rw [hΦcdef]; exact hmass₀
  have hle : (∫ u : {i // i ∈ S} → Ω,
        (star (sectorSlice e S Φc y u) * slotSumSub e T S (sectorSlice e S Φc y) u).re)
      ≤ c * (∫ u : {i // i ∈ S} → Ω, ‖sectorSlice e S Φc y u‖ ^ 2) := by
    rw [hΦcdef]; exact hle₀
  have hwin : ∀ α : Fin m →₀ ℕ, α.sum (fun _ k => k) = S.card →
      ((S.card - α 0 : ℕ) : ℝ) > (⌊M⌋₊ : ℝ) →
      Work.BoseDict.cIPn S.card (Work.BoseDict.modeProd e S.card α) (sliceF e S Φc y) = 0 := by
    intro α hα hb
    rw [hΦcdef]
    exact hwin₀ α hα hb
  -- ## step 2: the two real model vectors of the slice
  obtain ⟨Ψ₁, Ψ₂, hreal, hw₁, hw₂, hdeg₁, hdeg₂⟩ :=
    sliceModelWindow_deg (M := M) e hcont hcomp horth hbdd hsupp S Φc hΦccont hΦccomp
      hΦcsym y hwin
  -- ## step 3: the dictionary rows
  have hdict : ∀ Ψ Ψ' : Work.BoseB4.RealFock m,
      (∀ α ∈ Ψ.support, α.sum (fun _ k => k) = S.card) →
      (∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = S.card) →
      Work.BoseDict.cIPn S.card (Work.BoseDict.boxRealise e S.card Ψ)
        (Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ'))
        = ((Work.BoseB4.bomb m Ψ (Work.BoseB4.dGamma m T Ψ') : ℝ) : ℂ) := by
    intro Ψ Ψ' hΨ hΨ'
    rw [boxSlotSum_eq_boxRealise_dGamma he hbdd hsupp T Ψ' hΨ']
    exact Work.BoseDict.boxRealise_cIPn_gen he hbdd hsupp Ψ (Work.BoseB4.dGamma m T Ψ') hΨ
  have hiso : ∀ Ψ Ψ' : Work.BoseB4.RealFock m,
      (∀ α ∈ Ψ.support, α.sum (fun _ k => k) = S.card) →
      (∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = S.card) →
      Work.BoseDict.cIPn S.card (Work.BoseDict.boxRealise e S.card Ψ)
        (Work.BoseDict.boxRealise e S.card Ψ')
        = ((Work.BoseB4.bomb m Ψ Ψ' : ℝ) : ℂ) :=
    fun Ψ Ψ' hΨ _ => Work.BoseDict.boxRealise_cIPn_gen he hbdd hsupp Ψ Ψ' hΨ
  -- ## step 4: the additivity of `boxSlotSum` at the two vectors
  have hAF := boxSlotSum_add_I_smul_boxRealise (d := S.card) hℓ e hcont hcomp hbdd hsupp T Ψ₁ Ψ₂
  -- ## step 5: the four integrability hypotheses
  have hA00 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₁) x) := by
    simpa only [starRingEnd_apply] using
      integrable_conj_boxRealise_mul_boxSlotSum hℓ hcont hbdd hsupp he T Ψ₁ Ψ₁ hdeg₁
  have hA01 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₂) x) := by
    simpa only [starRingEnd_apply] using
      integrable_conj_boxRealise_mul_boxSlotSum hℓ hcont hbdd hsupp he T Ψ₁ Ψ₂ hdeg₂
  have hA10 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₁) x) := by
    simpa only [starRingEnd_apply] using
      integrable_conj_boxRealise_mul_boxSlotSum hℓ hcont hbdd hsupp he T Ψ₂ Ψ₁ hdeg₁
  have hA11 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₂) x) := by
    simpa only [starRingEnd_apply] using
      integrable_conj_boxRealise_mul_boxSlotSum hℓ hcont hbdd hsupp he T Ψ₂ Ψ₂ hdeg₂
  have hN00 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        * Work.BoseDict.boxRealise e S.card Ψ₁ x) := by
    simpa only [starRingEnd_apply] using
      integrable_conj_boxRealise_mul hℓ hcont hbdd hsupp Ψ₁ Ψ₁
  have hN01 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        * Work.BoseDict.boxRealise e S.card Ψ₂ x) := by
    simpa only [starRingEnd_apply] using
      integrable_conj_boxRealise_mul hℓ hcont hbdd hsupp Ψ₁ Ψ₂
  have hN10 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        * Work.BoseDict.boxRealise e S.card Ψ₁ x) := by
    simpa only [starRingEnd_apply] using
      integrable_conj_boxRealise_mul hℓ hcont hbdd hsupp Ψ₂ Ψ₁
  have hN11 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
      (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        * Work.BoseDict.boxRealise e S.card Ψ₂ x) := by
    simpa only [starRingEnd_apply] using
      integrable_conj_boxRealise_mul hℓ hcont hbdd hsupp Ψ₂ Ψ₂
  have hAinteg : ∀ i j : Fin 2, MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn S.card =>
        (starRingEnd ℂ) (![Work.BoseDict.boxRealise e S.card Ψ₁,
            Work.BoseDict.boxRealise e S.card Ψ₂] i x)
          * Work.BoseDict.boxSlotSum e T (![Work.BoseDict.boxRealise e S.card Ψ₁,
            Work.BoseDict.boxRealise e S.card Ψ₂] j) x) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hA00
    · exact hA01
    · exact hA10
    · exact hA11
  have hNinteg : ∀ i j : Fin 2, MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn S.card =>
        (starRingEnd ℂ) (![Work.BoseDict.boxRealise e S.card Ψ₁,
            Work.BoseDict.boxRealise e S.card Ψ₂] i x)
          * ![Work.BoseDict.boxRealise e S.card Ψ₁, Work.BoseDict.boxRealise e S.card Ψ₂] j x) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hN00
    · exact hN01
    · exact hN10
    · exact hN11
  -- ## step 6: the two pairings
  have hν : 0 < (Work.BoseDict.cIPn S.card
        (Work.BoseDict.boxRealise e S.card Ψ₁ + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)
        (Work.BoseDict.boxRealise e S.card Ψ₁
          + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)).re := by
    rw [hreal, cIPn_sliceF_self_eq e S Φc y]
    exact hmass
  have hh : (Work.BoseDict.cIPn S.card
        (Work.BoseDict.boxRealise e S.card Ψ₁ + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)
        (Work.BoseDict.boxSlotSum e T
          (Work.BoseDict.boxRealise e S.card Ψ₁
            + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂))).re
      ≤ c * (Work.BoseDict.cIPn S.card
        (Work.BoseDict.boxRealise e S.card Ψ₁
          + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)
        (Work.BoseDict.boxRealise e S.card Ψ₁
          + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂)).re := by
    set u : Work.BoseDict.Xn S.card → ℂ := Work.BoseDict.boxRealise e S.card Ψ₁ with hudef
    set v : Work.BoseDict.Xn S.card → ℂ := Work.BoseDict.boxRealise e S.card Ψ₂ with hvdef
    have hintAA : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
        (starRingEnd ℂ) (sliceF e S Φc y x)
          * Work.BoseDict.boxSlotSum e T (sliceF e S Φc y) x) := by
      rw [← hreal, hAF]
      have hcomb : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn S.card =>
          (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
              * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₁) x
            + (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
              * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₂) x
            + Complex.I * ((starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₁ x)
                * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₂) x
              - (starRingEnd ℂ) (Work.BoseDict.boxRealise e S.card Ψ₂ x)
                * Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₁) x)) :=
        ((hA00.add hA11).add ((hA01.sub hA10).const_mul Complex.I))
      refine hcomb.congr ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (conj_add_I_mul (Work.BoseDict.boxRealise e S.card Ψ₁ x)
        (Work.BoseDict.boxRealise e S.card Ψ₂ x)
        (Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₁) x)
        (Work.BoseDict.boxSlotSum e T (Work.BoseDict.boxRealise e S.card Ψ₂) x)).symm
    rw [hreal, cIPn_sliceF_self_eq e S Φc y]
    have hstep1 : (∫ x : Work.BoseDict.Xn S.card,
          ((starRingEnd ℂ) (sliceF e S Φc y x)
            * Work.BoseDict.boxSlotSum e T (sliceF e S Φc y) x).re)
        = ∫ x : Work.BoseDict.Xn S.card,
          (star (sectorSlice e S Φc y (sliceEquiv S x))
            * slotSumSub e T S (sectorSlice e S Φc y) (sliceEquiv S x)).re := by
      have hslicefun : sliceF e S Φc y
          = fun w => sectorSlice e S Φc y (sliceEquiv S w) := by
        funext w
        rw [sliceEquiv_coe]
        rfl
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      beta_reduce
      have hslice : sliceF e S Φc y x = sectorSlice e S Φc y (sliceEquiv S x) := by
        rw [sliceEquiv_coe]; rfl
      rw [starRingEnd_apply, hslice, hslicefun]
      rw [boxSlotSum_slice e T S (sectorSlice e S Φc y) x]
    have hstep2 : (∫ x : Work.BoseDict.Xn S.card,
          (star (sectorSlice e S Φc y (sliceEquiv S x))
            * slotSumSub e T S (sectorSlice e S Φc y) (sliceEquiv S x)).re)
        = ∫ u : {i // i ∈ S} → Ω,
          (star (sectorSlice e S Φc y u) * slotSumSub e T S (sectorSlice e S Φc y) u).re :=
      MeasurePreserving.integral_comp' (f := sliceEquiv S) (measurePreserving_sliceEquiv S)
        (fun u : {i // i ∈ S} → Ω =>
          (star (sectorSlice e S Φc y u) * slotSumSub e T S (sectorSlice e S Φc y) u).re)
    rw [Work.BoseDict.cIPn, re_integral hintAA, hstep1, hstep2]
    exact hle
  -- ## step 7: the binary selection
  rcases exists_binary_le_apply e (Work.BoseDict.boxSlotSum e T) (Work.BoseB4.dGamma m T)
      Ψ₁ Ψ₂ hAF hdict hiso hdeg₁ hdeg₂ hAinteg hNinteg c hν hh with ⟨hpos₁, hle₁⟩ | ⟨hpos₂, hle₂⟩
  · refine ⟨Ψ₁, ?_, hw₁, hle₁⟩
    intro hzero
    rw [hzero] at hpos₁
    simp at hpos₁
  · refine ⟨Ψ₂, ?_, hw₂, hle₂⟩
    intro hzero
    rw [hzero] at hpos₂
    simp at hpos₂

end Work.BoseBoxFock
