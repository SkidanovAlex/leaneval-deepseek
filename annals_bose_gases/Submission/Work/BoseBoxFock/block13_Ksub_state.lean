import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.block13_inner_weak
import Submission.Work.BoseBoxFock.pairG13_bounded
import Submission.Work.BoseBoxFock.pairG13_measurable
import Submission.Work.BoseBoxFock.pairRowS2Inst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.block13_Ksub_state` — step (S2) for block I at the *state* hypotheses

`pairRowS2.block13_Ksub` performs the kernel substitution `K1exp → K1lim` in block I of the FS `Q₂`
row at the *fibre* level: it takes the fibre `L²` bound `hGle`, the pairing estimate `hPair` at the
fibre `pairG13 p Θ A B`, and four integrability hypotheses, and concludes

    ‖I(K) − I(K')‖ ≤ ε √C .

This file discharges all of those hypotheses from the *state* hypotheses actually available in the
corpus (measurability, everywhere boundedness, box support and `L²`-integrability of `Θ`; the same
for the two one-particle factors `A`, `B`; measurability and everywhere boundedness of the two
kernels), and with `C` the explicit fibre `L²` bound of `pairRowS2Inst.pairG13_L2`:

    C = (∫ ‖A‖²) (∫ ‖B‖²) (∫ ‖Θ‖²)² .

The three ingredients that did not exist in the corpus are supplied by three companion modules:

* `pairG13_measurable` — `Measurable (uncurry (pairG13 p Θ A B))`, the `Measurable` input of the
  pairing hypothesis `hPair` (which is stated for an arbitrary bounded measurable `G`);
* `pairG13_bounded` — the uniform bound `∃ C, ∀ w y, ‖pairG13 p Θ A B w y‖ ≤ C`, the boundedness
  input of `hPair`;
* `block13_inner_weak` — measurability, uniform boundedness and off-box vanishing of the
  `u`-integral `z ↦ ∫ u, ⋆Θ z.1 · A (z.1 p.1) · ⋆B u · Θ (z.1[p.1↦z.2][p.2↦u])` which appears in the
  two integrability hypotheses `hInt1`, `hInt2`.

The two remaining integrability hypotheses `hIntK`, `hIntK'` (of the fibre pairings
`(w,y) ↦ K w y · pairG13 p Θ A B w y`) are proved here from the box support
`pairG_supports.pairG_supports` and the `L¹` criterion `Work.MB.integrable_of_bdd_of_support`.

Everything here is `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Integrability of the fibre pairings -/

/-- **The pairing `K · pairG13` is integrable.**  The fibre `pairG13 p Θ A B` is supported in the
box squared (`hcsupp`) and uniformly bounded (`hGb`), and `K` is bounded (`hKb`); the box squared
has finite volume, so the `L¹` criterion `Work.MB.integrable_of_bdd_of_support` applies. -/
theorem block13_pair_integrable {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ} {K : E3 → E3 → ℂ}
    (hcsupp : Function.support (Function.uncurry (pairG13 p Θ A B)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hGm : Measurable (Function.uncurry (pairG13 p Θ A B)))
    (hGb : ∃ C : ℝ, ∀ w y, ‖pairG13 p Θ A B w y‖ ≤ C)
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C) :
    MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K w y * pairG13 p Θ A B w y)) (volume : Measure (E3 × E3)) := by
  classical
  obtain ⟨CG, hCG⟩ := hGb
  obtain ⟨CK, hCK⟩ := hKb
  have hCG0 : 0 ≤ CG := le_trans (norm_nonneg _) (hCG 0 0)
  have hCK0 : 0 ≤ CK := le_trans (norm_nonneg _) (hCK 0 0)
  refine Work.MB.integrable_of_bdd_of_support
    (S := Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (C := CK * CG)
    ((Work.BoseB4.BoxData.boxL_measurableSet _ ℓ).prod
      (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ))
    ?_ ?_ ?_ ?_
  · rw [show (volume : Measure (E3 × E3)) = (volume : Measure E3).prod volume from rfl,
      show Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ)
        = Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ from rfl,
      Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne
  · exact (hKm.mul hGm).aestronglyMeasurable
  · intro z
    simp only [Function.uncurry]
    rw [norm_mul]
    exact mul_le_mul (hCK z.1 z.2) (hCG z.1 z.2) (norm_nonneg _) hCK0
  · intro z hz
    simp only [Function.uncurry]
    have h0 : pairG13 p Θ A B z.1 z.2 = 0 :=
      Function.notMem_support.mp (fun h => hz (hcsupp h))
    rw [h0, mul_zero]

/-! ## 2. Integrability of the kernel-weighted `u`-integral -/

/-- **`z ↦ K (z.1 p.2) z.2 · ∫ u, ⋆Θ z.1 · A (z.1 p.1) · ⋆B u · Θ (z.1[p.1↦z.2][p.2↦u])` is
integrable.**  The `u`-integral is measurable, uniformly bounded and vanishes off the box
`boxPow n ℓ ×ˢ boxL ℓ` (`block13_inner_weak`); `K` is bounded, and that box has finite volume. -/
theorem block13_inner_integrable {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ} {K : E3 → E3 → ℂ}
    (hinnerm : Measurable (fun z : Work.BoseDict.Xn n × E3 =>
        ∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))
    (hinnerb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Work.BoseDict.Xn n × E3,
        ‖∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)‖ ≤ C)
    (hinners : ∀ z : Work.BoseDict.Xn n × E3,
        z ∉ Set.prod (Work.MB.boxPow n ℓ) (Work.BoseK15.corpusBox.boxL ℓ) →
        (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)) = 0)
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C) :
    MeasureTheory.Integrable (fun z : Work.BoseDict.Xn n × E3 =>
        K (z.1 p.2) z.2 * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))
      (volume : Measure (Work.BoseDict.Xn n × E3)) := by
  classical
  obtain ⟨C', hC'0, hC'b⟩ := hinnerb
  obtain ⟨CK, hCK⟩ := hKb
  have hCK0 : 0 ≤ CK := le_trans (norm_nonneg _) (hCK 0 0)
  have hKzm : Measurable (fun z : Work.BoseDict.Xn n × E3 => K (z.1 p.2) z.2) :=
    show Measurable
        (fun z : Work.BoseDict.Xn n × E3 => Function.uncurry K (z.1 p.2, z.2)) from
      hKm.comp (((measurable_pi_apply p.2).comp measurable_fst).prodMk measurable_snd)
  have hm : AEStronglyMeasurable (fun z : Work.BoseDict.Xn n × E3 =>
        K (z.1 p.2) z.2 * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))
      (volume : Measure (Work.BoseDict.Xn n × E3)) :=
    (hKzm.mul hinnerm).aestronglyMeasurable
  refine Work.MB.integrable_of_bdd_of_support
    (S := Set.prod (Work.MB.boxPow n ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (C := CK * C')
    ((Work.MB.measurableSet_boxPow n ℓ).prod (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ))
    ?_ hm ?_ ?_
  · rw [show (volume : Measure (Work.BoseDict.Xn n × E3))
        = (volume : Measure (Work.BoseDict.Xn n)).prod volume from rfl,
      show Set.prod (Work.MB.boxPow n ℓ) (Work.BoseK15.corpusBox.boxL ℓ)
        = Work.MB.boxPow n ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ from rfl,
      Measure.prod_prod]
    exact ENNReal.mul_ne_top (Work.MB.volume_boxPow_lt_top n ℓ)
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne
  · intro z
    rw [norm_mul]
    exact mul_le_mul (hCK (z.1 p.2) z.2) (hC'b z) (norm_nonneg _) hCK0
  · intro z hz
    rw [hinners z hz, mul_zero]

/-! ## 3. The state-level form of step (S2) for block I -/

theorem block13_Ksub_state {n : ℕ} {ℓ ε : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    {K K' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2))
    (hBm : Measurable B) (hBb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C)
    (hBL : MeasureTheory.Integrable (fun x => ‖B x‖ ^ 2))
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C)
    (hK'm : Measurable (Function.uncurry K')) (hK'b : ∃ C : ℝ, ∀ w y, ‖K' w y‖ ≤ C)
    (hε : 0 ≤ ε)
    (hPair : ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
        Measurable (Function.uncurry G) → (∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C) →
        ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
           ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * G w y‖
          ≤ ε * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
              ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖G w y‖ ^ 2)) :
    ‖(∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
        ∫ u : EuclideanSpace ℝ (Fin 3),
        star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      - (∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
        ∫ u : EuclideanSpace ℝ (Fin 3),
        star (Θ x) * A (x p.1) * K' (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
      ≤ ε * Real.sqrt ((∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2) := by
  obtain ⟨CG, hCG0, hCG⟩ :=
    pairG13_bounded p hp hΘm hΘb hΘs hAm hAb hBm hBb
  obtain ⟨hinnerm, hinnerb, hinners⟩ :=
    block13_inner_weak p hp hΘm hΘb hΘs hAm hAb hBm hBb
  have hpgm : Measurable (Function.uncurry (pairG13 p Θ A B)) :=
    pairG13_measurable p hp hΘm hAm hBm
  have hcsupp : Function.support (Function.uncurry (pairG13 p Θ A B)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) :=
    (pairG_supports p hp hΘs).1
  -- the box-restricted fibre `L²` bound of `pairRowS2Inst`
  have hGle : ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG13 p Θ A B w y‖ ^ 2
      ≤ (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2 :=
    pairG13_L2 p hp hcsupp hΘm.aestronglyMeasurable hΘL hAm.aestronglyMeasurable hAL
      hBm.aestronglyMeasurable hBL
  have hC : 0 ≤ (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2 :=
    mul_nonneg (mul_nonneg (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity))
      (pow_nonneg (integral_nonneg fun x => by positivity) 2)
  -- the pairing hypothesis at the fibre `pairG13`
  have hpair : ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * pairG13 p Θ A B w y‖
      ≤ ε * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG13 p Θ A B w y‖ ^ 2) :=
    hPair (fun w y => pairG13 p Θ A B w y) hpgm ⟨CG, hCG⟩
  have hIntK := block13_pair_integrable p hp hcsupp hpgm ⟨CG, hCG⟩ hKm hKb
  have hIntK' := block13_pair_integrable p hp hcsupp hpgm ⟨CG, hCG⟩ hK'm hK'b
  have hInt1 := block13_inner_integrable p hinnerm hinnerb hinners hKm hKb
  have hInt2 := block13_inner_integrable p hinnerm hinnerb hinners hK'm hK'b
  exact block13_Ksub (C := (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2)
    p hp hε hC hcsupp hpair hGle hIntK hIntK' hInt1 hInt2

end Work.BoseBoxFock
