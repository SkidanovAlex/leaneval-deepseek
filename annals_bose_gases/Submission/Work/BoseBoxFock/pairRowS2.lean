import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairRowFibreGen
import Submission.Work.BoseBoxFock.pairRowKsub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS2` — step (S2) at the block level

The block-level form of step (S2) of `FINDING_PotPairRows_exists.md`: for each of the four integrand
shapes of the FS `Q₂` row (blocks I, III.1 with a kernel at a configuration slot and a free
variable; blocks II.1 with two free kernel variables; block II.2 with the kernel at two
configuration slots), the triple integral with the truncated pair kernel `K1exp` and the same
integral with its limit `K1lim` differ by at most `ε√C`, where:

* `ε` is the accuracy delivered by `Work.BoseBoxFock.K1exp_sub_K1lim_pairing_le` (PROVED) at the
  fibre function `𝓖` of the shape;
* `C` is any bound for `∫_{Λ²}‖𝓖‖²`, supplied by the fibre `L²` bounds
  `Work.BoseBoxFock.block13_fibre_L2`, `…blockTwo3_fibre_L2`, `…blockII1_fibre_L2`,
  `…slotRow_fibre_L2` (the first three of which are the delegated companions of this module).

Everything here is `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Step (S2) for the shape of block I** (and of block III.1, which has the constant weight
`fun _ => 1` and therefore *no* limit — (S2) applies to block I only): the kernel sits at
`(x p.2, y)`. -/
theorem block13_Ksub {n : ℕ} {ℓ ε C : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ} {K K' : E3 → E3 → ℂ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hCsupp : Function.support (Function.uncurry (pairG13 p Θ A B)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hPair : ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
               ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
                 (K w y - K' w y) * pairG13 p Θ A B w y‖
        ≤ ε * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG13 p Θ A B w y‖ ^ 2))
    (hGle : ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
              ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG13 p Θ A B w y‖ ^ 2 ≤ C)
    (hIntK : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K w y * pairG13 p Θ A B w y)) (volume : Measure (E3 × E3)))
    (hIntK' : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K' w y * pairG13 p Θ A B w y)) (volume : Measure (E3 × E3)))
    (hInt1 : MeasureTheory.Integrable (fun z : Work.BoseDict.Xn n × E3 =>
      K (z.1 p.2) z.2 * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
        * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))))
    (hInt2 : MeasureTheory.Integrable (fun z : Work.BoseDict.Xn n × E3 =>
      K' (z.1 p.2) z.2 * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
        * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))) :
    ‖(∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      - (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * K' (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
      ≤ ε * Real.sqrt C := by
  rw [block13_fibre_gen p hp hInt1, block13_fibre_gen p hp hInt2]
  exact int_pairing_sub_le hε hC hCsupp hPair hGle hIntK hIntK'

/-- **Step (S2) for the block II.2 shape**: the kernel sits at `(x p.1, x p.2)`. -/
theorem blockTwo3_Ksub {n : ℕ} {ℓ ε C : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ} {K K' : E3 → E3 → ℂ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hCsupp : Function.support (Function.uncurry (pairG23 p Θ A B)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hPair : ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
               ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
                 (K w y - K' w y) * pairG23 p Θ A B w y‖
        ≤ ε * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG23 p Θ A B w y‖ ^ 2))
    (hGle : ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
              ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG23 p Θ A B w y‖ ^ 2 ≤ C)
    (hIntK : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K w y * pairG23 p Θ A B w y)) (volume : Measure (E3 × E3)))
    (hIntK' : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K' w y * pairG23 p Θ A B w y)) (volume : Measure (E3 × E3)))
    (hInt1 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
      K (x p.1) (x p.2) * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))))
    (hInt2 : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
      K' (x p.1) (x p.2) * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)))) :
    ‖(∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * K (x p.1) (x p.2) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      - (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * K' (x p.1) (x p.2) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
      ≤ ε * Real.sqrt C := by
  rw [blockTwo3_fibre_gen p hp hInt1, blockTwo3_fibre_gen p hp hInt2]
  exact int_pairing_sub_le hε hC hCsupp hPair hGle hIntK hIntK'

/-- **Step (S2) for the block II.1 shape**: both kernel arguments are free variables. -/
theorem blockII1_Ksub {n : ℕ} {ℓ ε C : ℝ} (p : Fin n × Fin n)
    {Θ : Work.BoseDict.Xn n → ℂ} {A : E3 → ℂ} {K K' : E3 → E3 → ℂ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hCsupp : Function.support (Function.uncurry (pairG21 p Θ A)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hPair : ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
               ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
                 (K w y - K' w y) * pairG21 p Θ A w y‖
        ≤ ε * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG21 p Θ A w y‖ ^ 2))
    (hGle : ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
              ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖pairG21 p Θ A w y‖ ^ 2 ≤ C)
    (hIntK : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K w y * pairG21 p Θ A w y)) (volume : Measure (E3 × E3)))
    (hIntK' : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K' w y * pairG21 p Θ A w y)) (volume : Measure (E3 × E3)))
    (hx : ∀ x : Work.BoseDict.Xn n, MeasureTheory.Integrable
      (Function.uncurry (fun y u : E3 => K u y * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)))) (volume : Measure (E3 × E3)))
    (hx' : ∀ x : Work.BoseDict.Xn n, MeasureTheory.Integrable
      (Function.uncurry (fun y u : E3 => K' u y * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)))) (volume : Measure (E3 × E3)))
    (hSwap : MeasureTheory.Integrable
      (Function.uncurry (fun x : Work.BoseDict.Xn n => fun z : E3 × E3 =>
        K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Work.BoseDict.Xn n × (E3 × E3))))
    (hSwap' : MeasureTheory.Integrable
      (Function.uncurry (fun x : Work.BoseDict.Xn n => fun z : E3 × E3 =>
        K' z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Work.BoseDict.Xn n × (E3 × E3))))
    (hProd : MeasureTheory.Integrable
      (fun z : E3 × E3 => ∫ x : Work.BoseDict.Xn n, K z.1 z.2 * (star (Θ x) * A (x p.1)
        * A (x p.2) * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)))
    (hProd' : MeasureTheory.Integrable
      (fun z : E3 × E3 => ∫ x : Work.BoseDict.Xn n, K' z.1 z.2 * (star (Θ x) * A (x p.1)
        * A (x p.2) * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3))) :
    ‖(∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * A (x p.2) * K u y
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      - (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * A (x p.2) * K' u y
          * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
      ≤ ε * Real.sqrt C := by
  rw [blockII1_fibre_gen p hx hSwap hProd, blockII1_fibre_gen p hx' hSwap' hProd']
  exact int_pairing_sub_le hε hC hCsupp hPair hGle hIntK hIntK'

end Work.BoseBoxFock
