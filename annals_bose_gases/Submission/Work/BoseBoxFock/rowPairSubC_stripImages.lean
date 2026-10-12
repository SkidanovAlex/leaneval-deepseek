import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.blockII1_KsubDir_stripImages
import Submission.Work.BoseBoxFock.blockTwo3_KsubDir_stripImages
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowPairSubC_stripImages` — stripping the `χχ`-lattice images off the
block-`I/II` part of the `Q₂` row

The limit pair kernel splits as `K1lim ℓ W' = K1limNice ℓ W' + chiChiImages ℓ W` (the `m ≠ 0`
lattice images of the `χχ`-row).  Since `rowPairSubC a Θ A KI KII` is *linear* in the two kernels,
the difference of the row at `K1lim ℓ W₁'`/`K1lim ℓ W₂'` and the row at the two stripped kernels
`K1lim ℓ Wᵢ' − chiChiImages ℓ Wᵢ` is (up to the Bochner-integrability bookkeeping hidden in the
block-level Dirichlet substitution lemmas) the row at the two images kernels themselves; the
pairing hypothesis `hPairI`/`hPairII` (the `T7` row) bounds each of those per pair, and
`rowPairSubC_KsubDir` sums the three blocks.

The per-pair block bounds are `block13_KsubDir_stripImages` (proved below — block I / III.1),
`Work.BoseBoxFock.blockII1_KsubDir_stripImages` (block II.1) and
`Work.BoseBoxFock.blockTwo3_KsubDir_stripImages` (block II.2); each is the state-level Dirichlet
substitution `block13_KsubDir` / `blockII1_KsubDir` / `blockTwo3_KsubDir` at the kernel pair
`(K1lim ℓ W', K1lim ℓ W' − chiChiImages ℓ W)`, whose integrability hypotheses are discharged from
the state data (`pairG13/21/23` bounded and box-supported, `K1lim` and the images kernel both
bounded and measurable).
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option linter.unusedVariables false

/-- **Step (S3), per pair, block I.**  The block-I row shape at the limit kernel `K1lim ℓ W'`
differs from its value at the images-stripped kernel `K1lim ℓ W' − chiChiImages ℓ W` by
`ε·(√(pairEnergy) + √(massBox))` of the fibre `pairG13`. -/
theorem block13_KsubDir_stripImages {n : ℕ} {ℓ ε : ℝ}
    (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (hℓ : 0 < ℓ)
    {Θ Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {W W' : E3 → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hCutA : CutSmooth1 ℓ A)
    (hW'm : Measurable W') (hW'b : ∃ C : ℝ, ∀ x, ‖W' x‖ ≤ C) (hW's : HasCompactSupport W')
    (hWm : Measurable W) (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hε : 0 ≤ ε)
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G))) :
    ‖rowShape13 Θ A A (K1lim ℓ W') p
      - rowShape13 Θ A A (fun w y => K1lim ℓ W' w y
          - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y) p‖
      ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (pairG13 p Θ A A))
          + Real.sqrt (massBox ℓ (pairG13 p Θ A A))) := by
  -- the complexification of the images weight `W` has the three properties `chiChiImages` needs
  have hWcm : Measurable (fun z : E3 => ((W z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hWm
  have hWcb : ∃ C : ℝ, ∀ z : E3, ‖((W z : ℝ) : ℂ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hWb
    refine ⟨C, fun z => ?_⟩
    rw [show ‖((W z : ℝ) : ℂ)‖ = |W z| from RCLike.norm_ofReal (K := ℂ) (W z)]
    simpa [Real.norm_eq_abs] using hC z
  have hWcs : HasCompactSupport (fun z : E3 => ((W z : ℝ) : ℂ)) := by
    have h : (fun z : E3 => ((W z : ℝ) : ℂ)) = Complex.ofReal ∘ W := rfl
    rw [h]
    exact hWs.comp_left (g := Complex.ofReal) rfl
  obtain ⟨hχm, hχb⟩ := chiChiImages_meas_bdd hℓ hWcm hWcb hWcs
  obtain ⟨hKm, hKb⟩ := K1lim_meas_bdd hℓ hW'm hW'b hW's
  have hK'm : Measurable (Function.uncurry (fun w y : E3 =>
      K1lim ℓ W' w y - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)) := hKm.sub hχm
  have hK'b : ∃ C : ℝ, ∀ w y : E3, ‖K1lim ℓ W' w y
      - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y‖ ≤ C := by
    obtain ⟨C₁, hC₁⟩ := hKb
    obtain ⟨C₂, hC₂⟩ := hχb
    exact ⟨C₁ + C₂, fun w y => le_trans (norm_sub_le _ _) (add_le_add (hC₁ w y) (hC₂ w y))⟩
  obtain ⟨CG, _hCG0, hCG⟩ := pairG13_bounded p hp hΘm hΘb hΘs hAm hAb hAm hAb
  obtain ⟨hinnerm, hinnerb, hinners⟩ := block13_inner_weak p hp hΘm hΘb hΘs hAm hAb hAm hAb
  have hpgm : Measurable (Function.uncurry (pairG13 p Θ A A)) :=
    pairG13_measurable p hp hΘm hAm hAm
  have hcsupp : Function.support (Function.uncurry (pairG13 p Θ A A)) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) :=
    (pairG_supports (A := A) (B := A) p hp hΘs).1
  have hbs : BoxSmooth ℓ (pairG13 p Θ A A) :=
    (boxSmooth_fibres hℓ p hp ⟨Θ₀, hΘ₀, hΘind⟩ hCutA hCutA).1
  have hIntK := block13_pair_integrable p hp hcsupp hpgm ⟨CG, hCG⟩ hKm hKb
  have hIntK' := block13_pair_integrable p hp hcsupp hpgm ⟨CG, hCG⟩ hK'm hK'b
  have hInt1 := block13_inner_integrable p hinnerm hinnerb hinners hKm hKb
  have hInt2 := block13_inner_integrable p hinnerm hinnerb hinners hK'm hK'b
  -- the kernel difference is the images kernel, so `hPair` applies verbatim
  have hPair' : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          (K1lim ℓ W' w y - (K1lim ℓ W' w y
            - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)) * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G) + Real.sqrt (massBox ℓ G)) := by
    intro G hG
    have hfun : (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          (K1lim ℓ W' w y - (K1lim ℓ W' w y
            - chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y)) * G w y)
        = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
            chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun w => ?_)
      refine integral_congr_ae ?_
      exact Filter.Eventually.of_forall (fun y => by ring)
    rw [hfun]
    exact hPair G hG
  have hmain := block13_KsubDir p hp hℓ hε hcsupp hPair' hbs hIntK hIntK' hInt1 hInt2
  simpa only [rowShape13] using hmain

theorem rowPairSubC_stripImages {n : ℕ} {ℓ a ε : ℝ} {Θ : Work.BoseDict.Xn n → ℂ}
    {A : EuclideanSpace ℝ (Fin 3) → ℂ} {Θ₀ : Work.BoseDict.Xn n → ℂ}
    {W₁ W₂ W₁' W₂' : EuclideanSpace ℝ (Fin 3) → ℝ} {Θ₀' : Work.BoseDict.Xn n → ℂ}
    (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hΘind : ∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2))
    (hCutA : Work.BoseBoxFock.CutSmooth1 ℓ A)
    (hW₁'m : Measurable W₁') (hW₁'b : ∃ C : ℝ, ∀ x, ‖W₁' x‖ ≤ C) (hW₁'s : HasCompactSupport W₁')
    (hW₂'m : Measurable W₂') (hW₂'b : ∃ C : ℝ, ∀ x, ‖W₂' x‖ ≤ C) (hW₂'s : HasCompactSupport W₂')
    (hW₁m : Measurable W₁) (hW₁b : ∃ C : ℝ, ∀ x, ‖W₁ x‖ ≤ C) (hW₁s : HasCompactSupport W₁)
    (hW₂m : Measurable W₂) (hW₂b : ∃ C : ℝ, ∀ x, ‖W₂ x‖ ≤ C) (hW₂s : HasCompactSupport W₂)
    (hW₁'i : MeasureTheory.Integrable W₁') (hW₂'i : MeasureTheory.Integrable W₂')
    (hPairI : ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
      Work.BoseBoxFock.BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
           Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₁ z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (Work.BoseBoxFock.massBox ℓ G)))
    (hPairII : ∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
      Work.BoseBoxFock.BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
           Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₂ z : ℝ) : ℂ)) w y * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (Work.BoseBoxFock.massBox ℓ G))) :
    ‖Work.BoseBoxFock.rowPairSubC a Θ A (Work.BoseBoxFock.K1lim ℓ W₁') (Work.BoseBoxFock.K1lim ℓ W₂')
        - Work.BoseBoxFock.rowPairSubC a Θ A
            (fun w y => Work.BoseBoxFock.K1lim ℓ W₁' w y
              - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₁ z : ℝ) : ℂ)) w y)
            (fun w y => Work.BoseBoxFock.K1lim ℓ W₂' w y
              - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W₂ z : ℝ) : ℂ)) w y)‖
      ≤ 2 * |a| * ε * ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairG13 p Θ A A))
              + Real.sqrt (Work.BoseBoxFock.massBox ℓ (Work.BoseBoxFock.pairG13 p Θ A A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairG21 p Θ A))
              + Real.sqrt (Work.BoseBoxFock.massBox ℓ (Work.BoseBoxFock.pairG21 p Θ A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairG23 p Θ A A))
              + Real.sqrt (Work.BoseBoxFock.massBox ℓ (Work.BoseBoxFock.pairG23 p Θ A A)))) := by
  refine rowPairSubC_KsubDir (n := n) (ℓ := ℓ) (ε := ε) (a := a) (Θ := Θ) (A := A)
    (KI := K1lim ℓ W₁')
    (KI' := fun w y => K1lim ℓ W₁' w y
      - chiChiImages ℓ (fun z => ((W₁ z : ℝ) : ℂ)) w y)
    (KII := K1lim ℓ W₂')
    (KII' := fun w y => K1lim ℓ W₂' w y
      - chiChiImages ℓ (fun z => ((W₂ z : ℝ) : ℂ)) w y)
    hε ?_ ?_ ?_
  · intro p hp
    exact block13_KsubDir_stripImages p (mem_pairSet_iff.mp hp) hℓ hΘm hΘb hΘs hΘ₀ hΘind
      hAm hAb hCutA hW₁'m hW₁'b hW₁'s hW₁m hW₁b hW₁s hε hPairI
  · intro p hp
    exact blockII1_KsubDir_stripImages p (mem_pairSet_iff.mp hp) hℓ hΘm hΘb hΘs hΘ₀ hΘind
      hAm hAb hCutA hW₂'m hW₂'b hW₂'s hW₂m hW₂b hW₂s hε hPairII
  · intro p hp
    exact blockTwo3_KsubDir_stripImages p (mem_pairSet_iff.mp hp) hℓ hΘm hΘb hΘs hΘ₀ hΘind
      hAm hAb hCutA hW₂'m hW₂'b hW₂'s hW₂m hW₂b hW₂s hε hPairII

end Work.BoseBoxFock
