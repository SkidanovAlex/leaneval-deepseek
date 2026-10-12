import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSmoothAux
import Submission.Work.BoseBoxFock.contDiff_setIntegral_compact_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSmooth_fibres` — the fibres of the `Q₂` row agree on the box with `C^∞`
functions

`BoxSmooth ℓ G` (of `pairRowDirDefs`) asks for a `C^∞` function `G'` agreeing with `G` on
`boxL ℓ × boxL ℓ`.  For the three fibres `pairG13`, `pairG23`, `pairG21` of `pairRowGDefs` this is
proved by exhibiting the **box-restricted integral of the clean integrand**: since
`Θ = 1_{abox}·Θ₀`, `A = 1_{boxL}·A₀`, `B = 1_{boxL}·B₀` (`CutSmooth`, `CutSmooth1`), on the box
squared the state indicators are all `1`, so the fibre equals a parametric integral over a compact
set of a jointly `C^∞` integrand, which is `C^∞` by
`Work.BoseBoxFock.contDiff_setIntegral_compact_gen`.

-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- Complex conjugation commutes with an indicator. -/
lemma star_indicatorC {α : Type*} {s : Set α} (f : α → ℂ) (a : α) :
    star (Set.indicator s f a) = Set.indicator s (fun z => star (f z)) a := by
  by_cases h : a ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, star_zero]

/-- Congruence for a Bochner double integral. -/
lemma integral₂_congr {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f g : α → β → ℂ} (h : ∀ a b, f a b = g a b) :
    (∫ a, ∫ b, f a b ∂ν ∂μ) = ∫ a, ∫ b, g a b ∂ν ∂μ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only []
  exact integral_congr_ae (Filter.Eventually.of_forall fun b => h a b)

/-- Turning a pointwise indicator factor in an integrand into a set integral. -/
lemma integral_indicator_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (h : α → ℂ) :
    (∫ a, Set.indicator s (fun _ => (1 : ℂ)) a * h a ∂μ) = ∫ a in s, h a ∂μ := by
  rw [show (fun a : α => Set.indicator s (fun _ => (1 : ℂ)) a * h a)
      = Set.indicator s h from by
    funext a
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, one_mul]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, zero_mul]]
  rw [integral_indicator hs]

/-! ## The block I / III.1 fibre `pairG13` -/

/-- On the box squared the `pairG13` integrand equals the box-restricted clean integrand. -/
lemma pairG13_integrand_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {Θ₀ : Xn n → ℂ} {A₀ B₀ : E3 → ℂ} {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hA : ∀ x, A x = Set.indicator (boxL ℓ) A₀ x)
    (hB : ∀ x, B x = Set.indicator (boxL ℓ) B₀ x)
    {w y : E3} (hw : w ∈ boxL ℓ) (hy : y ∈ boxL ℓ)
    (x' : {k : Fin n // k ≠ p.2} → E3) (u : E3) :
    star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
        * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)
      = Set.indicator (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
        * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
            * clean13 p Θ₀ A₀ B₀ ((w, y), (x', u))) := by
  rw [hΘ (insertCoord p.2 w x'), hA ((insertCoord p.2 w x') p.1), hB u,
    hΘ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u),
    star_indicatorC Θ₀ (insertCoord p.2 w x'), star_indicatorC B₀ u]
  by_cases hx : x' ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ
  · have hγ : insertCoord p.2 w x' ∈ Submission.BoseGases.abox n ℓ :=
      (insertCoord_mem_abox_iff hℓ hw x').mpr hx
    have hA1 : (insertCoord p.2 w x') p.1 ∈ boxL ℓ :=
      insertCoord_apply_mem_boxL hℓ hp hw hx
    by_cases hu : u ∈ boxL ℓ
    · have hupd : Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u
          ∈ Submission.BoseGases.abox n ℓ := upd13_mem_abox hℓ hp hw hy hu hx
      simp only [Set.indicator_of_mem hγ, Set.indicator_of_mem hA1, Set.indicator_of_mem hx,
        Set.indicator_of_mem hu, Set.indicator_of_mem hupd, one_mul]
      rfl
    · simp only [Set.indicator_of_mem hγ, Set.indicator_of_mem hA1, Set.indicator_of_mem hx,
        Set.indicator_of_notMem hu, zero_mul, mul_zero, one_mul]
  · have hγ : insertCoord p.2 w x' ∉ Submission.BoseGases.abox n ℓ :=
      fun h => hx ((insertCoord_mem_abox_iff hℓ hw x').mp h)
    simp only [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hx, zero_mul, mul_zero]

/-- The smooth candidate for the block I / III.1 fibre: the box-restricted integral of the
clean integrand. -/
def pairG13Core {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A₀ B₀ : E3 → ℂ)
    (w y : E3) : ℂ :=
  ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ, ∫ u in boxL ℓ,
    clean13 p Θ₀ A₀ B₀ ((w, y), (x', u))

theorem BoxSmooth_pairG13 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    (hΘ : CutSmooth ℓ Θ) (hA : CutSmooth1 ℓ A) (hB : CutSmooth1 ℓ B) :
    BoxSmooth ℓ (pairG13 p Θ A B) := by
  obtain ⟨Θ₀, hΘ₀, hΘeq⟩ := hΘ
  obtain ⟨A₀, hA₀, hAeq⟩ := hA
  obtain ⟨B₀, hB₀, hBeq⟩ := hB
  have hBPi : IsCompact (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) := isCompact_boxPiSet hℓ
  have hKB : IsCompact (boxL ℓ) := by
    rw [corpusBox_boxL_eq_acube hℓ]
    exact Submission.BoseGases.acube_compact hℓ
  refine ⟨pairG13Core ℓ p Θ₀ A₀ B₀, ?_, ?_⟩
  · -- smoothness of the box-restricted integral
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun z : ((E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
        (((z.1.1, (z.1.2, z.2))) : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3))) :=
      (contDiff_fst.comp contDiff_fst).prodMk
        ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z : ((E3 × E3) × ({k : Fin n // k ≠ p.2} → E3)) × E3 =>
        clean13 p Θ₀ A₀ B₀ (z.1.1, (z.1.2, z.2))) :=
      (contDiff_clean13 p hΘ₀ hA₀ hB₀).comp hmap
    have hstep1 : ContDiff ℝ (⊤ : ℕ∞) (fun r : (E3 × E3) × ({k : Fin n // k ≠ p.2} → E3) =>
        ∫ u in boxL ℓ, clean13 p Θ₀ A₀ B₀ (r.1, (r.2, u))) :=
      contDiff_setIntegral_compact_gen hKB hF
    have hstep2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 × E3 =>
        ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
          ∫ u in boxL ℓ, clean13 p Θ₀ A₀ B₀ (q, (x', u))) := by
      have hfun : Function.uncurry (fun (q : E3 × E3) (x' : {k : Fin n // k ≠ p.2} → E3) =>
            ∫ u in boxL ℓ, clean13 p Θ₀ A₀ B₀ (q, (x', u)))
          = fun r : (E3 × E3) × ({k : Fin n // k ≠ p.2} → E3) =>
              ∫ u in boxL ℓ, clean13 p Θ₀ A₀ B₀ (r.1, (r.2, u)) := rfl
      refine contDiff_setIntegral_compact_gen hBPi ?_
      rw [hfun]
      exact hstep1
    have hfun2 : Function.uncurry (pairG13Core ℓ p Θ₀ A₀ B₀)
        = fun q : E3 × E3 => ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
            ∫ u in boxL ℓ, clean13 p Θ₀ A₀ B₀ (q, (x', u)) := rfl
    rw [hfun2]
    exact hstep2
  · -- agreement on the box squared
    intro w y hw hy
    have hpt : ∀ (x' : {k : Fin n // k ≠ p.2} → E3) (u : E3),
        star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
            * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u)
          = Set.indicator (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
            * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                * clean13 p Θ₀ A₀ B₀ ((w, y), (x', u))) :=
      pairG13_integrand_eq hℓ hp hΘeq hAeq hBeq hw hy
    calc pairG13Core ℓ p Θ₀ A₀ B₀ w y
        = ∫ x' in boxPiSet ({k : Fin n // k ≠ p.2}) ℓ,
            ∫ u in boxL ℓ, clean13 p Θ₀ A₀ B₀ ((w, y), (x', u)) := rfl
      _ = ∫ (x' : {k : Fin n // k ≠ p.2} → E3),
            Set.indicator (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
              * (∫ u in boxL ℓ, clean13 p Θ₀ A₀ B₀ ((w, y), (x', u))) := by
            rw [← integral_indicator hBPi.measurableSet]
            congr 1
            funext x'
            by_cases hx : x' ∈ boxPiSet ({k : Fin n // k ≠ p.2}) ℓ
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
      _ = ∫ (x' : {k : Fin n // k ≠ p.2} → E3), ∫ (u : E3),
            Set.indicator (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
              * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                  * clean13 p Θ₀ A₀ B₀ ((w, y), (x', u))) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
            simp only []
            rw [integral_const_mul]
            congr 1
            exact (integral_indicator_mul hKB.measurableSet
              (fun u => clean13 p Θ₀ A₀ B₀ ((w, y), (x', u)))).symm
      _ = ∫ (x' : {k : Fin n // k ≠ p.2} → E3), ∫ (u : E3),
            star (Θ (insertCoord p.2 w x')) * A ((insertCoord p.2 w x') p.1) * star (B u)
              * Θ (Function.update (Function.update (insertCoord p.2 w x') p.1 y) p.2 u) :=
            integral₂_congr fun x' u => (hpt x' u).symm
      _ = pairG13 p Θ A B w y := rfl

/-! ## The block II.2 fibre `pairG23` -/

/-- On the box squared the `pairG23` integrand equals the box-restricted clean integrand. -/
lemma pairG23_integrand_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {Θ₀ : Xn n → ℂ} {A₀ B₀ : E3 → ℂ} {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hA : ∀ x, A x = Set.indicator (boxL ℓ) A₀ x)
    (hB : ∀ x, B x = Set.indicator (boxL ℓ) B₀ x)
    {w₀ w₁ : E3} (h₀ : w₀ ∈ boxL ℓ) (h₁ : w₁ ∈ boxL ℓ)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) (y u : E3) :
    star (Θ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
        * Θ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u)
      = Set.indicator (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) (fun _ => (1 : ℂ)) x'
        * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
            * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                * clean23 p Θ₀ A₀ B₀ ((w₀, w₁), (x', (y, u))))) := by
  rw [hΘ (insertCoord2 p w₀ w₁ x'), hA y, hB u,
    hΘ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u),
    star_indicatorC Θ₀ (insertCoord2 p w₀ w₁ x'), star_indicatorC A₀ y, star_indicatorC B₀ u]
  by_cases hx : x' ∈ boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ
  · have hxab : insertCoord2 p w₀ w₁ x' ∈ Submission.BoseGases.abox n ℓ :=
      (insertCoord2_mem_abox_iff hℓ h₀ h₁ x').mpr hx
    by_cases hy : y ∈ boxL ℓ
    · by_cases hu : u ∈ boxL ℓ
      · have hupd : Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u
            ∈ Submission.BoseGases.abox n ℓ := upd23_mem_abox hℓ h₀ h₁ hy hu hx
        simp only [Set.indicator_of_mem hxab, Set.indicator_of_mem hy, Set.indicator_of_mem hu,
          Set.indicator_of_mem hx, Set.indicator_of_mem hupd, one_mul]
        rfl
      · simp only [Set.indicator_of_mem hxab, Set.indicator_of_mem hy,
          Set.indicator_of_notMem hu, Set.indicator_of_mem hx, zero_mul, mul_zero]
    · simp only [Set.indicator_of_mem hxab, Set.indicator_of_notMem hy,
        Set.indicator_of_mem hx, zero_mul, mul_zero]
  · have hxab : insertCoord2 p w₀ w₁ x' ∉ Submission.BoseGases.abox n ℓ :=
      fun h => hx ((insertCoord2_mem_abox_iff hℓ h₀ h₁ x').mp h)
    simp only [Set.indicator_of_notMem hxab, Set.indicator_of_notMem hx, zero_mul]

/-- The smooth candidate for the block II.2 fibre: the box-restricted integral of the clean
integrand. -/
def pairG23Core {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A₀ B₀ : E3 → ℂ)
    (w₀ w₁ : E3) : ℂ :=
  ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
    ∫ y in boxL ℓ, ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ ((w₀, w₁), (x', (y, u)))

theorem BoxSmooth_pairG23' {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    (hΘ : CutSmooth ℓ Θ) (hA : CutSmooth1 ℓ A) (hB : CutSmooth1 ℓ B) :
    BoxSmooth ℓ (pairG23 p Θ A B) := by
  obtain ⟨Θ₀, hΘ₀, hΘeq⟩ := hΘ
  obtain ⟨A₀, hA₀, hAeq⟩ := hA
  obtain ⟨B₀, hB₀, hBeq⟩ := hB
  have hBPi : IsCompact (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) :=
    isCompact_boxPiSet hℓ
  have hKB : IsCompact (boxL ℓ) := by
    rw [corpusBox_boxL_eq_acube hℓ]
    exact Submission.BoseGases.acube_compact hℓ
  refine ⟨pairG23Core ℓ p Θ₀ A₀ B₀, ?_, ?_⟩
  · -- smoothness of the box-restricted triple integral
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
          (((z.1.1.1, (z.1.1.2, (z.1.2, z.2)))) :
            (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × E3 × E3))) := by
      have h1 : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
            z.1.1.1) := by fun_prop
      have h2 : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
            z.1.1.2) := by fun_prop
      have h3 : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
            z.1.2) := by fun_prop
      have h4 : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
            z.2) := by fun_prop
      exact h1.prodMk (h2.prodMk (h3.prodMk h4))
    have hF : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) × E3 =>
          clean23 p Θ₀ A₀ B₀ (z.1.1.1, (z.1.1.2, (z.1.2, z.2)))) :=
      (contDiff_clean23 p hΘ₀ hA₀ hB₀).comp hmap
    have hstep1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun r : ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3 =>
          ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ (r.1.1, (r.1.2, (r.2, u)))) :=
      contDiff_setIntegral_compact_gen hKB hF
    have hstep2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun r : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          ∫ y in boxL ℓ, ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ (r.1, (r.2, (y, u)))) := by
      have hfun : Function.uncurry (fun
            (r : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) (y : E3) =>
              ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ (r.1, (r.2, (y, u))))
          = fun s : (((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3) =>
              ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ (s.1.1, (s.1.2, (s.2, u))) := rfl
      refine contDiff_setIntegral_compact_gen hKB ?_
      rw [hfun]
      exact hstep1
    have hstep3 : ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 × E3 =>
        ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ∫ y in boxL ℓ, ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ (q, (x', (y, u)))) := by
      have hfun : Function.uncurry (fun (q : E3 × E3)
            (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
              ∫ y in boxL ℓ, ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ (q, (x', (y, u))))
          = fun r : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
              ∫ y in boxL ℓ, ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ (r.1, (r.2, (y, u))) := rfl
      refine contDiff_setIntegral_compact_gen hBPi ?_
      rw [hfun]
      exact hstep2
    have hfun2 : Function.uncurry (pairG23Core ℓ p Θ₀ A₀ B₀)
        = fun q : E3 × E3 => ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
            ∫ y in boxL ℓ, ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ (q, (x', (y, u))) := rfl
    rw [hfun2]
    exact hstep3
  · -- agreement on the box squared
    intro w₀ w₁ h₀ h₁
    have hpt : ∀ (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) (y u : E3),
        star (Θ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
            * Θ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y) p.2 u)
          = Set.indicator (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)
              (fun _ => (1 : ℂ)) x'
            * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
                * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                    * clean23 p Θ₀ A₀ B₀ ((w₀, w₁), (x', (y, u))))) :=
      pairG23_integrand_eq hℓ hΘeq hAeq hBeq h₀ h₁
    have hchain : pairG23 p Θ A B w₀ w₁ = pairG23Core ℓ p Θ₀ A₀ B₀ w₀ w₁ := by
      calc pairG23 p Θ A B w₀ w₁
          = ∫ (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3), ∫ (y : E3), ∫ (u : E3),
              star (Θ (insertCoord2 p w₀ w₁ x')) * star (A y) * star (B u)
                * Θ (Function.update (Function.update (insertCoord2 p w₀ w₁ x') p.1 y)
                    p.2 u) := rfl
        _ = ∫ (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3), ∫ (y : E3), ∫ (u : E3),
              Set.indicator (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)
                  (fun _ => (1 : ℂ)) x'
                * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
                    * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) u
                        * clean23 p Θ₀ A₀ B₀ ((w₀, w₁), (x', (y, u))))) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
              simp only []
              refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
              simp only []
              exact integral_congr_ae (Filter.Eventually.of_forall fun u => hpt x' y u)
        _ = ∫ (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3), ∫ (y : E3),
              Set.indicator (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)
                  (fun _ => (1 : ℂ)) x'
                * (Set.indicator (boxL ℓ) (fun _ => (1 : ℂ)) y
                    * (∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ ((w₀, w₁), (x', (y, u))))) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
              simp only []
              refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
              simp only []
              rw [integral_const_mul, integral_const_mul,
                integral_indicator_mul hKB.measurableSet]
        _ = ∫ (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3),
              Set.indicator (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ)
                  (fun _ => (1 : ℂ)) x'
                * (∫ y in boxL ℓ, ∫ u in boxL ℓ,
                    clean23 p Θ₀ A₀ B₀ ((w₀, w₁), (x', (y, u)))) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
              simp only []
              rw [integral_const_mul, integral_indicator_mul hKB.measurableSet]
        _ = ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ, ∫ y in boxL ℓ,
              ∫ u in boxL ℓ, clean23 p Θ₀ A₀ B₀ ((w₀, w₁), (x', (y, u))) := by
              rw [← integral_indicator_mul hBPi.measurableSet]
        _ = pairG23Core ℓ p Θ₀ A₀ B₀ w₀ w₁ := rfl
    exact hchain.symm

/-! ## The block II.1 fibre `pairG21` -/

/-- On the box squared the `pairG21` integrand equals the box-restricted clean integrand (the
parameters `(u, y)` are the fibre's own arguments). -/
lemma pairG21_integrand_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {Θ₀ : Xn n → ℂ} {A₀ : E3 → ℂ} {Θ : Xn n → ℂ} {A : E3 → ℂ}
    (hΘ : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hA : ∀ x, A x = Set.indicator (boxL ℓ) A₀ x)
    {y u : E3} (hy : y ∈ boxL ℓ) (hu : u ∈ boxL ℓ) (x : Fin n → E3) :
    star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)
      = Set.indicator (boxPiSet (Fin n) ℓ) (fun _ => (1 : ℂ)) x
        * clean21 p Θ₀ A₀ ((u, y), x) := by
  rw [hΘ x, hA (x p.1), hA (x p.2),
    hΘ (Function.update (Function.update x p.1 y) p.2 u), star_indicatorC Θ₀ x]
  have hiff : x ∈ Submission.BoseGases.abox n ℓ ↔ x ∈ boxPiSet (Fin n) ℓ := by
    rw [Submission.BoseGases.mem_abox_iff, mem_boxPiSet, ← corpusBox_boxL_eq_acube hℓ]
  by_cases hx : x ∈ boxPiSet (Fin n) ℓ
  · have hxab : x ∈ Submission.BoseGases.abox n ℓ := hiff.mpr hx
    have hx1 : x p.1 ∈ boxL ℓ := (mem_boxPiSet.mp hx) p.1
    have hx2 : x p.2 ∈ boxL ℓ := (mem_boxPiSet.mp hx) p.2
    have hupd : Function.update (Function.update x p.1 y) p.2 u
        ∈ Submission.BoseGases.abox n ℓ := upd21_mem_abox hℓ hy hu hx
    simp only [Set.indicator_of_mem hxab, Set.indicator_of_mem hx1, Set.indicator_of_mem hx2,
      Set.indicator_of_mem hx, Set.indicator_of_mem hupd, one_mul]
    rfl
  · have hxab : x ∉ Submission.BoseGases.abox n ℓ := fun h => hx (hiff.mp h)
    simp only [Set.indicator_of_notMem hxab, Set.indicator_of_notMem hx, zero_mul]

/-- The smooth candidate for the block II.1 fibre: the box-restricted integral of the clean
integrand.  The parameters are `(u, y)`, as in `pairG21`. -/
def pairG21Core {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A₀ : E3 → ℂ)
    (u y : E3) : ℂ :=
  ∫ x in boxPiSet (Fin n) ℓ, clean21 p Θ₀ A₀ ((u, y), x)

theorem BoxSmooth_pairG21 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ : Xn n → ℂ} {A : E3 → ℂ}
    (hΘ : CutSmooth ℓ Θ) (hA : CutSmooth1 ℓ A) :
    BoxSmooth ℓ (pairG21 p Θ A) := by
  obtain ⟨Θ₀, hΘ₀, hΘeq⟩ := hΘ
  obtain ⟨A₀, hA₀, hAeq⟩ := hA
  have hBPin : IsCompact (boxPiSet (Fin n) ℓ) := isCompact_boxPiSet hℓ
  refine ⟨pairG21Core ℓ p Θ₀ A₀, ?_, ?_⟩
  · have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z : (E3 × E3) × (Fin n → E3) =>
        clean21 p Θ₀ A₀ z) := contDiff_clean21 p hΘ₀ hA₀
    have hfun : Function.uncurry (fun (q : E3 × E3) (x : Fin n → E3) =>
          clean21 p Θ₀ A₀ (q, x))
        = fun z : (E3 × E3) × (Fin n → E3) => clean21 p Θ₀ A₀ z := rfl
    have hstep : ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 × E3 =>
        ∫ x in boxPiSet (Fin n) ℓ, clean21 p Θ₀ A₀ (q, x)) := by
      refine contDiff_setIntegral_compact_gen hBPin ?_
      rw [hfun]
      exact hF
    have hfun2 : Function.uncurry (pairG21Core ℓ p Θ₀ A₀)
        = fun q : E3 × E3 => ∫ x in boxPiSet (Fin n) ℓ, clean21 p Θ₀ A₀ (q, x) := rfl
    rw [hfun2]
    exact hstep
  · intro u y hu hy
    have hpt : ∀ x : Fin n → E3,
        star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)
          = Set.indicator (boxPiSet (Fin n) ℓ) (fun _ => (1 : ℂ)) x
            * clean21 p Θ₀ A₀ ((u, y), x) :=
      fun x => pairG21_integrand_eq hℓ hΘeq hAeq hy hu x
    calc pairG21Core ℓ p Θ₀ A₀ u y
        = ∫ x in boxPiSet (Fin n) ℓ, clean21 p Θ₀ A₀ ((u, y), x) := rfl
      _ = ∫ (x : Fin n → E3), Set.indicator (boxPiSet (Fin n) ℓ) (fun _ => (1 : ℂ)) x
            * clean21 p Θ₀ A₀ ((u, y), x) := by
            rw [← integral_indicator_mul hBPin.measurableSet]
      _ = ∫ (x : Fin n → E3), star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 y) p.2 u) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only []
            exact (hpt x).symm
      _ = pairG21 p Θ A u y := rfl

theorem boxSmooth_fibres {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘ : Work.BoseBoxFock.CutSmooth ℓ Θ)
    (hA : Work.BoseBoxFock.CutSmooth1 ℓ A) (hB : Work.BoseBoxFock.CutSmooth1 ℓ B) :
    Work.BoseBoxFock.BoxSmooth ℓ (Work.BoseBoxFock.pairG13 p Θ A B)
      ∧ Work.BoseBoxFock.BoxSmooth ℓ (Work.BoseBoxFock.pairG23 p Θ A B)
      ∧ Work.BoseBoxFock.BoxSmooth ℓ (Work.BoseBoxFock.pairG21 p Θ A) := by
  exact ⟨BoxSmooth_pairG13 hℓ p hp hΘ hA hB, BoxSmooth_pairG23' hℓ p hp hΘ hA hB,
    BoxSmooth_pairG21 hℓ p hΘ hA⟩

end Work.BoseBoxFock
