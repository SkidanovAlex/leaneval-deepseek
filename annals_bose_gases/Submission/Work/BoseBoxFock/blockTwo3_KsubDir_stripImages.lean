import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.blockTwo3_II1_Ksub_stateDir
import Submission.Work.BoseBoxFock.chiChiImages_meas_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "boxL" => Work.BoseK15.corpusBox.boxL

open MeasureTheory

/-- **Strip the lattice-image part off the block II.2 kernel.**  The block-level Dirichlet (S2)
substitution `blockTwo3_KsubDir` at the pair `(K, K') = (K1lim ℓ W', K1lim ℓ W' − χχ-images)`
has kernel difference exactly the `χχ`-images kernel `chiChiImages ℓ W`, so it *is* the statement
that the block II.2 shape is unchanged (up to the Dirichlet budget) by removing the images.

All the technical inputs of `blockTwo3_KsubDir` come from the state data:

* the fibre `pairG23 p Θ A A` is measurable (`pairG23_measurable`), bounded
  (`pairG23_bounded`) and supported in the box squared (`pairG_supports`);
* `K1lim ℓ W'` and `chiChiImages ℓ W` are measurable and globally bounded
  (`K1lim_meas_bdd`, `chiChiImages_meas_bdd` — this is why only *boundedness* + compact support of
  `W`, `W'` are needed, and **not** their integrability);
* hence both `K1lim · pairG23` and `χχ · pairG23` are integrable (`integrable_bdd_mul_fibre`, a
  bounded kernel times a bounded box-supported fibre), and so is their difference `K' · pairG23`;
* `pairG23 p Θ A A` agrees on the box squared with a `C^∞` function (`boxSmooth_fibres`), so it is
  an admissible test function for the `BoxSmooth`-form pairing hypothesis.

`sorry`-free. -/
theorem blockTwo3_KsubDir_stripImages {n : ℕ} {ℓ ε : ℝ}
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ}
    {W W' : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hCutA : Work.BoseBoxFock.CutSmooth1 ℓ A)
    (hW'm : Measurable W') (hW'b : ∃ C : ℝ, ∀ x, ‖W' x‖ ≤ C) (hW's : HasCompactSupport W')
    (hWm : Measurable W) (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hε : 0 ≤ ε)
    (hPair : ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
      Work.BoseBoxFock.BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (Work.BoseBoxFock.massBox ℓ G))) :
    ‖Work.BoseBoxFock.rowShape23 Θ A A (Work.BoseBoxFock.K1lim ℓ W') p
      - Work.BoseBoxFock.rowShape23 Θ A A (fun w y => Work.BoseBoxFock.K1lim ℓ W' w y
          - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) p‖
      ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairG23 p Θ A A))
          + Real.sqrt (Work.BoseBoxFock.massBox ℓ (Work.BoseBoxFock.pairG23 p Θ A A))) := by
  -- ### the fibre of block II.2: support in the box squared, measurability, boundedness, smoothness
  have hCsupp : Function.support (Function.uncurry (pairG23 p Θ A A)) ⊆
      Set.prod (boxL ℓ) (boxL ℓ) :=
    (pairG_supports p hp hΘs).2.1
  have hGm : Measurable (Function.uncurry (pairG23 p Θ A A)) :=
    pairG23_measurable p hΘm hAm hAm
  have hGb : ∃ C : ℝ, ∀ w y, ‖pairG23 p Θ A A w y‖ ≤ C :=
    pairG23_bounded p hp hΘs hΘb hAb hAb
  have hbs : BoxSmooth ℓ (pairG23 p Θ A A) :=
    (boxSmooth_fibres hℓ p hp ⟨Θ₀, hΘ₀, hΘind⟩ hCutA hCutA).2.1
  -- ### measurability and boundedness of the two kernels
  obtain ⟨hK1m, hK1b⟩ := K1lim_meas_bdd hℓ hW'm hW'b hW's
  obtain ⟨hCCm, hCCb⟩ := chiChiImages_meas_bdd (ℓ := ℓ) hℓ
    (W := fun z : E3 => ((W z : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp hWm)
    (hWb.imp fun C hC x => by simpa using hC x)
    (hWs.comp_left (g := fun r : ℝ => ((r : ℂ))) (by simp))
  -- ### integrability of the two products (bounded kernel times bounded box-supported fibre)
  have hIntK : MeasureTheory.Integrable
      (Function.uncurry (fun w y : E3 => K1lim ℓ W' w y * pairG23 p Θ A A w y))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
    integrable_bdd_mul_fibre hK1m hK1b hGm hGb hCsupp
  have hIntCC : MeasureTheory.Integrable
      (Function.uncurry (fun w y : E3 =>
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * pairG23 p Θ A A w y))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) :=
    integrable_bdd_mul_fibre hCCm hCCb hGm hGb hCsupp
  have hIntK' : MeasureTheory.Integrable
      (Function.uncurry (fun w y : E3 => (K1lim ℓ W' w y
        - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) * pairG23 p Θ A A w y))
      (MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)) := by
    refine (hIntK.sub hIntCC).congr (Filter.Eventually.of_forall fun z => ?_)
    obtain ⟨w, y⟩ := z
    simp only [Function.uncurry_apply_pair, Pi.sub_apply]
    ring
  -- ### the pairing hypothesis at `(K1lim, K1lim − χχ)`: the difference is the image kernel
  have hPair' : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in boxL ℓ, ∫ y in boxL ℓ,
          (K1lim ℓ W' w y - (K1lim ℓ W' w y
            - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)) * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (Work.BoseBoxFock.massBox ℓ G)) := by
    intro G hG
    have hrw : ∀ w y : E3, (K1lim ℓ W' w y - (K1lim ℓ W' w y
        - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y))
        = chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y := fun w y => by ring
    simp only [hrw]
    exact hPair G hG
  -- ### the state-level integrability inputs of the block lemma
  have hphi := phi23_bound_support p hp hΘs hΘb hAb hAb
  have hphiMeas : Measurable (phi23 p Θ A A) := phi23_measurable p hΘm hAm hAm
  have hInt1 : MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn n =>
        K1lim ℓ W' (x p.1) (x p.2) * (∫ y : E3, ∫ u : E3,
          star (Θ x) * star (A y) * star (A u)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)))
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)) :=
    integrable_bdd_slots hK1m hK1b hphiMeas hphi.1 hphi.2
  have hK'm : Measurable (Function.uncurry (fun w y : E3 =>
      K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)) := by
    have hfun : Function.uncurry (fun w y : E3 =>
          K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)
        = Function.uncurry (K1lim ℓ W')
          - Function.uncurry (chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ))) := by
      funext p
      obtain ⟨w, y⟩ := p
      simp only [Function.uncurry_apply_pair, Pi.sub_apply]
    rw [hfun]
    exact hK1m.sub hCCm
  have hK'b : ∃ C : ℝ, ∀ w y, ‖K1lim ℓ W' w y
      - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y‖ ≤ C := by
    obtain ⟨CK1, hCK1⟩ := hK1b
    obtain ⟨CCC, hCCC⟩ := hCCb
    exact ⟨CK1 + CCC, fun w y => (norm_sub_le _ _).trans (add_le_add (hCK1 w y) (hCCC w y))⟩
  have hInt2 : MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn n =>
        (K1lim ℓ W' (x p.1) (x p.2)
            - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) (x p.1) (x p.2))
          * (∫ y : E3, ∫ u : E3,
            star (Θ x) * star (A y) * star (A u)
              * Θ (Function.update (Function.update x p.1 y) p.2 u)))
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)) :=
    integrable_bdd_slots hK'm hK'b hphiMeas hphi.1 hphi.2
  -- ### the block-level (S2) lemma
  exact blockTwo3_KsubDir (n := n) (ℓ := ℓ) (ε := ε) (Θ := Θ) (A := A) (B := A)
    (K := K1lim ℓ W')
    (K' := fun w y : E3 => K1lim ℓ W' w y
      - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)
    p hp hℓ hε hCsupp hPair' hbs hIntK hIntK' hInt1 hInt2

end Work.BoseBoxFock
