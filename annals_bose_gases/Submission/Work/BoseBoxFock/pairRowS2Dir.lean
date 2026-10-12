import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairRowKsubDir
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS2Dir` — step (S2) at the block level, in the `BoxSmooth` (Dirichlet) form

`Work.BoseBoxFock.pairRowS2` proves the block-level (S2) substitution bounds with the pairing
hypothesis taken for a *bounded measurable* `G` and an `L²` bound for the fibre — the shape that the
bounded-weight chain of `FINDING_PotPairRows_exists.md` §§3–8 used, and which is **not
instantiable** at the honest weights (`W₁ = W1fun` is only `L¹`, §9.2/§9.13).

The replacement (FINDING §10) is the `BoxSmooth` interface of
`Work.BoseBoxFock.pairRowDirDefs` plus the Dirichlet functional
`Work.BoseBoxFock.L1Tails.pairEnergy`; the transfer from the *generic* pairing hypothesis to the
*fibre* is `Work.BoseBoxFock.int_pairing_sub_le_dir` (`pairRowKsubDir`).  This module re-states the
three block lemmas in that form: the four integrability hypotheses of the `L²` version are kept as
hypotheses (they cannot be derived from boundedness, since `K1lim` is unbounded), and everything else
is verbatim.

`sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- **Step (S2) for the shape of block I** in the `BoxSmooth` form: the kernel sits at
`(x p.2, y)`. -/
theorem block13_KsubDir {n : ℕ} {ℓ ε : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ : Xn n → ℂ} {A B : E3 → ℂ} {K K' : E3 → E3 → ℂ} (hε : 0 ≤ ε)
    (hCsupp : Function.support (Function.uncurry (pairG13 p Θ A B)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (massBox ℓ G)))
    (hbs : BoxSmooth ℓ (pairG13 p Θ A B))
    (hIntK : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K w y * pairG13 p Θ A B w y)) (volume : Measure (E3 × E3)))
    (hIntK' : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K' w y * pairG13 p Θ A B w y)) (volume : Measure (E3 × E3)))
    (hInt1 : MeasureTheory.Integrable (fun z : Xn n × E3 =>
      K (z.1 p.2) z.2 * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
        * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))))
    (hInt2 : MeasureTheory.Integrable (fun z : Xn n × E3 =>
      K' (z.1 p.2) z.2 * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
        * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))) :
    ‖(∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      - (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * K' (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
      ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A B))
          + Real.sqrt (massBox ℓ (pairG13 p Θ A B))) := by
  rw [block13_fibre_gen p hp hInt1, block13_fibre_gen p hp hInt2]
  simp only [pairG13, insertCoord_eq]
  exact int_pairing_sub_le_dir hℓ hε hCsupp hPair hbs hIntK hIntK'

/-- **Step (S2) for the block II.2 shape** in the `BoxSmooth` form: the kernel sits at
`(x p.1, x p.2)`. -/
theorem blockTwo3_KsubDir {n : ℕ} {ℓ ε : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ : Xn n → ℂ} {A B : E3 → ℂ} {K K' : E3 → E3 → ℂ} (hε : 0 ≤ ε)
    (hCsupp : Function.support (Function.uncurry (pairG23 p Θ A B)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (massBox ℓ G)))
    (hbs : BoxSmooth ℓ (pairG23 p Θ A B))
    (hIntK : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K w y * pairG23 p Θ A B w y)) (volume : Measure (E3 × E3)))
    (hIntK' : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K' w y * pairG23 p Θ A B w y)) (volume : Measure (E3 × E3)))
    (hInt1 : MeasureTheory.Integrable (fun x : Xn n =>
      K (x p.1) (x p.2) * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))))
    (hInt2 : MeasureTheory.Integrable (fun x : Xn n =>
      K' (x p.1) (x p.2) * (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)))) :
    ‖(∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * K (x p.1) (x p.2) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      - (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * K' (x p.1) (x p.2) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
      ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG23 p Θ A B))
          + Real.sqrt (massBox ℓ (pairG23 p Θ A B))) := by
  rw [blockTwo3_fibre_gen p hp hInt1, blockTwo3_fibre_gen p hp hInt2]
  exact int_pairing_sub_le_dir hℓ hε hCsupp hPair hbs hIntK hIntK'

/-- **Step (S2) for the block II.1 shape** in the `BoxSmooth` form: both kernel arguments are free
variables. -/
theorem blockII1_KsubDir {n : ℕ} {ℓ ε : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ : Xn n → ℂ} {A : E3 → ℂ} {K K' : E3 → E3 → ℂ} (hε : 0 ≤ ε)
    (hCsupp : Function.support (Function.uncurry (pairG21 p Θ A)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (massBox ℓ G)))
    (hbs : BoxSmooth ℓ (pairG21 p Θ A))
    (hIntK : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K w y * pairG21 p Θ A w y)) (volume : Measure (E3 × E3)))
    (hIntK' : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K' w y * pairG21 p Θ A w y)) (volume : Measure (E3 × E3)))
    (hx : ∀ x : Xn n, MeasureTheory.Integrable
      (Function.uncurry (fun y u : E3 => K u y * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)))) (volume : Measure (E3 × E3)))
    (hx' : ∀ x : Xn n, MeasureTheory.Integrable
      (Function.uncurry (fun y u : E3 => K' u y * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)))) (volume : Measure (E3 × E3)))
    (hSwap : MeasureTheory.Integrable
      (Function.uncurry (fun x : Xn n => fun z : E3 × E3 =>
        K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Xn n × (E3 × E3))))
    (hSwap' : MeasureTheory.Integrable
      (Function.uncurry (fun x : Xn n => fun z : E3 × E3 =>
        K' z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Xn n × (E3 × E3))))
    (hProd : MeasureTheory.Integrable
      (fun z : E3 × E3 => ∫ x : Xn n, K z.1 z.2 * (star (Θ x) * A (x p.1)
        * A (x p.2) * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3)))
    (hProd' : MeasureTheory.Integrable
      (fun z : E3 × E3 => ∫ x : Xn n, K' z.1 z.2 * (star (Θ x) * A (x p.1)
        * A (x p.2) * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3))) :
    ‖(∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * A (x p.2) * K u y
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      - (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * A (x p.2) * K' u y
          * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
      ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG21 p Θ A))
          + Real.sqrt (massBox ℓ (pairG21 p Θ A))) := by
  rw [blockII1_fibre_gen p hx hSwap hProd, blockII1_fibre_gen p hx' hSwap' hProd']
  exact int_pairing_sub_le_dir hℓ hε hCsupp hPair hbs hIntK hIntK'

/-! ## 3. The row-level Dirichlet (S2) bound -/

/-- **Step (S2) at the row level in the `BoxSmooth` form.**  Each of the three per-pair block bounds
at the *fibre* Dirichlet norm gives the whole block-`I/II` part of the row at the sum of the
per-pair square roots — the shape that has to be Cauchy–Schwarz'd against the state's Dirichlet
content in the final assembly. -/
theorem rowPairSubC_KsubDir {n : ℕ} {ℓ ε a : ℝ} {Θ : Xn n → ℂ} {A : E3 → ℂ}
    {KI KI' KII KII' : E3 → E3 → ℂ} (hε : 0 ≤ ε)
    (h13 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape13 Θ A A KI p - rowShape13 Θ A A KI' p‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
            + Real.sqrt (massBox ℓ (pairG13 p Θ A A))))
    (h21 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape21 Θ A KII p - rowShape21 Θ A KII' p‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG21 p Θ A))
            + Real.sqrt (massBox ℓ (pairG21 p Θ A))))
    (h23 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape23 Θ A A KII p - rowShape23 Θ A A KII' p‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
            + Real.sqrt (massBox ℓ (pairG23 p Θ A A)))) :
    ‖rowPairSubC a Θ A KI KII - rowPairSubC a Θ A KI' KII'‖
      ≤ 2 * |a| * ε * ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
              + Real.sqrt (massBox ℓ (pairG13 p Θ A A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG21 p Θ A))
              + Real.sqrt (massBox ℓ (pairG21 p Θ A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
              + Real.sqrt (massBox ℓ (pairG23 p Θ A A)))) := by
  refine rowPairSubC_Ksub_of_shapes_pair (n := n) (a := a) (ε := ε) (Θ := Θ) (A := A)
    (KI := KI) (KI' := KI') (KII := KII) (KII' := KII') hε
    (fun p => Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
      + Real.sqrt (massBox ℓ (pairG13 p Θ A A)))
    (fun p => Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG21 p Θ A))
      + Real.sqrt (massBox ℓ (pairG21 p Θ A)))
    (fun p => Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG23 p Θ A A))
      + Real.sqrt (massBox ℓ (pairG23 p Θ A A)))
    (fun p => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (fun p => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (fun p => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    h13 h21 h23

end Work.BoseBoxFock
