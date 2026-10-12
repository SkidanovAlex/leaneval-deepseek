import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1lim_mul_integrable
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_slot
import Submission.Work.BoseBoxFock.block13_Ksub_state
import Submission.Work.BoseBoxFock.boxSmooth_fibres
import Submission.Work.BoseBoxFock.pairRowS2Dir
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS2DirState` — the `BoxSmooth` (S2) block lemmas at the *state* hypotheses

`Work.BoseBoxFock.block13_KsubDir` (`pairRowS2Dir`) is the (S2) substitution for block I in the
`BoxSmooth`/`pairEnergy`+`massBox` interface, with the four integrability inputs (and the `BoxSmooth`
hypothesis for the fibre) taken as hypotheses.  This module discharges them from the *state*
hypotheses actually available in the corpus:

* measurability, box support and boundedness of `Θ`, `A`, `B`; the `CutSmooth`/`CutSmooth1` shapes
  (`FINDING_PotPairRows_exists.md` §10) that make the fibre `BoxSmooth` (`boxSmooth_fibres`);
* `K` measurable and bounded (`K = K1exp` at the honest data);
* `K' = K1lim ℓ W` with `W ∈ L¹` — the two integrability inputs for the *unbounded* limit kernel are
  `Work.BoseBoxFock.K1lim_mul_integrable` (the pair pattern) and
  `Work.BoseBoxFock.K1lim_mul_integrable_slot` (the slot pattern), the two new ingredients of the
  Dirichlet route (§10.4(4) of the FINDING).

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- **Step (S2) for block I at the state hypotheses, in the `BoxSmooth` form.** -/
theorem block13_Ksub_stateDir {n : ℕ} {ℓ ε : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {K : E3 → E3 → ℂ} {W : E3 → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hBm : Measurable B) (hBb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C)
    (hCutA : CutSmooth1 ℓ A) (hCutB : CutSmooth1 ℓ B)
    (hKm : Measurable (Function.uncurry K)) (hKb : ∃ C : ℝ, ∀ w y, ‖K w y‖ ≤ C)
    (hWi : MeasureTheory.Integrable W) (hε : 0 ≤ ε)
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K1lim ℓ W w y) * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (massBox ℓ G))) :
    ‖(∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      - (∫ x : Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * K1lim ℓ W (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))‖
      ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A B))
          + Real.sqrt (massBox ℓ (pairG13 p Θ A B))) := by
  obtain ⟨CG, hCG0, hCG⟩ := pairG13_bounded p hp hΘm hΘb hΘs hAm hAb hBm hBb
  obtain ⟨hinnerm, hinnerb, hinners⟩ := block13_inner_weak p hp hΘm hΘb hΘs hAm hAb hBm hBb
  have hpgm : Measurable (Function.uncurry (pairG13 p Θ A B)) :=
    pairG13_measurable p hp hΘm hAm hBm
  have hcsupp := (pairG_supports (A := A) (B := B) p hp hΘs).1
  have hbs : BoxSmooth ℓ (pairG13 p Θ A B) :=
    (boxSmooth_fibres hℓ p hp ⟨Θ₀, hΘ₀, hΘind⟩ hCutA hCutB).1
  have hIntK := block13_pair_integrable p hp hcsupp hpgm ⟨CG, hCG⟩ hKm hKb
  have hIntK' : MeasureTheory.Integrable (Function.uncurry
      (fun w y : E3 => K1lim ℓ W w y * pairG13 p Θ A B w y)) (volume : Measure (E3 × E3)) :=
    K1lim_mul_integrable hℓ hWi hpgm.aestronglyMeasurable ⟨CG, hCG⟩ hcsupp
  have hInt1 := block13_inner_integrable p hinnerm hinnerb hinners hKm hKb
  have hHs : Function.support (fun z : Xn n × E3 =>
      ∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
        * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))
      ⊆ Set.prod (Work.MB.boxPow n ℓ) (Work.BoseK15.corpusBox.boxL ℓ) := by
    intro z hz
    by_contra hznot
    exact (Function.mem_support.mp hz) (hinners z hznot)
  have hInt2' : MeasureTheory.Integrable (fun z : Xn n × E3 =>
      K1lim ℓ W (z.1 p.2) z.2 * (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
        * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))
      (volume : Measure (Xn n × E3)) :=
    K1lim_mul_integrable_slot hℓ p hWi hinnerm.aestronglyMeasurable
      (hinnerb.imp fun C hC z => hC.2 z) hHs
  exact block13_KsubDir p hp hℓ hε hcsupp hPair hbs hIntK hIntK' hInt1 hInt2'

end Work.BoseBoxFock
