import Submission.Work.Stems.StepI.SqueezeDefs

/-!
# The two composites of the trivialisation and its section

The homotopies `squeezeH` and `squeezeK` run from the identity to the composites `sect ∘ triv`
(resp. `triv ∘ sect`).  This file identifies those composites, as functions of the interval
coordinate, with `compFun` and `compFunK`: the nested concatenations `(γ * rev sg) * sg` and
`(δ * sg) * rev sg`.  Both identifications are pure unfolding plus a case split, the only content
being that `clampI` is the identity on `[0,1]` and that the second half of the trivialisation is the
first half of the section (`sectFun`/`trivFun` are the two halves of the same concatenation).
-/

open scoped Topology unitInterval
open Work.StemsB

namespace Work.Stems.StepI

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X} {d₀ : X}

theorem sectFun_trivCM (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (z : ↥((evalOne X x₀) ⁻¹' W))
    (hz : (evalOne X x₀) ⟨trivCM sg hsg1 z, trivCM_zero sg hsg1 z⟩ ∈ ({d₀} : Set X))
    (s : unitInterval) :
    sectFun sg (wOf z, ⟨⟨trivCM sg hsg1 z, trivCM_zero sg hsg1 z⟩, hz⟩) s =
      compFun sg (wOf z) (cmOf z) s := by
  show (if (2 : ℝ) * (s : ℝ) ≤ 1 then trivCM sg hsg1 z (clampI (2 * (s : ℝ)))
      else sg (wOf z, clampI (2 * (s : ℝ) - 1))) = compFun sg (wOf z) (cmOf z) s
  by_cases h : (2 : ℝ) * (s : ℝ) ≤ 1
  · rw [if_pos h]
    unfold compFun
    rw [if_pos h]
    have hc : (((clampI (2 * (s : ℝ))) : I) : ℝ) = 2 * (s : ℝ) :=
      coe_clampI_of_mem ⟨by linarith [s.2.1], h⟩
    rw [trivCM_apply]
    unfold trivFun
    rw [hc, show (2 : ℝ) * (2 * (s : ℝ)) = 4 * (s : ℝ) by ring]
  · rw [if_neg h]
    unfold compFun
    rw [if_neg h]

theorem trivFun_sectCM (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀}))
    (hy : (evalOne X x₀) ⟨sectCM sg hsg0 y, sectCM_zero sg hsg0 y⟩ ∈ W)
    (s : unitInterval) :
    trivFun sg ⟨⟨sectCM sg hsg0 y, sectCM_zero sg hsg0 y⟩, hy⟩ s =
      compFunK sg y.1 (fibCM y.2) s := by
  show (if (2 : ℝ) * (s : ℝ) ≤ 1 then sectCM sg hsg0 y (clampI (2 * (s : ℝ)))
      else sg (wOf ⟨⟨sectCM sg hsg0 y, sectCM_zero sg hsg0 y⟩, hy⟩,
        clampI (2 - 2 * (s : ℝ)))) = compFunK sg y.1 (fibCM y.2) s
  by_cases h : (2 : ℝ) * (s : ℝ) ≤ 1
  · rw [if_pos h]
    unfold compFunK
    rw [if_pos h]
    have hc : (((clampI (2 * (s : ℝ))) : I) : ℝ) = 2 * (s : ℝ) :=
      coe_clampI_of_mem ⟨by linarith [s.2.1], h⟩
    rw [sectCM_apply]
    unfold sectFun
    rw [hc, show (2 : ℝ) * (2 * (s : ℝ)) = 4 * (s : ℝ) by ring]
  · rw [if_neg h]
    unfold compFunK
    rw [if_neg h]
    have hw : wOf (x₀ := x₀) (W := W) ⟨⟨sectCM sg hsg0 y, sectCM_zero sg hsg0 y⟩, hy⟩ = y.1 :=
      Subtype.ext (sectCM_one sg hsg0 hsg1 y)
    rw [hw]

theorem trivsect_composites {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X} {d₀ : X}
    (sg : ContinuousMap (↥W × unitInterval) X)
    (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) :
    (∀ (z : ↥((Work.StemsB.evalOne X x₀) ⁻¹' W))
        (hz : (Work.StemsB.evalOne X x₀)
          ⟨Work.Stems.StepI.trivCM sg hsg1 z, Work.Stems.StepI.trivCM_zero sg hsg1 z⟩ ∈
          ({d₀} : Set X)) (s : unitInterval),
        Work.Stems.StepI.sectFun sg
            (Work.Stems.StepI.wOf z, ⟨⟨Work.Stems.StepI.trivCM sg hsg1 z,
              Work.Stems.StepI.trivCM_zero sg hsg1 z⟩, hz⟩) s =
          Work.Stems.StepI.compFun sg (Work.Stems.StepI.wOf z)
            (Work.Stems.StepI.cmOf z) s) ∧
    (∀ (y : ↥W × ↥((Work.StemsB.evalOne X x₀) ⁻¹' {d₀}))
        (hy : (Work.StemsB.evalOne X x₀)
          ⟨Work.Stems.StepI.sectCM sg hsg0 y, Work.Stems.StepI.sectCM_zero sg hsg0 y⟩ ∈ W)
        (s : unitInterval),
        Work.Stems.StepI.trivFun sg
            ⟨⟨Work.Stems.StepI.sectCM sg hsg0 y, Work.Stems.StepI.sectCM_zero sg hsg0 y⟩, hy⟩ s =
          Work.Stems.StepI.compFunK sg y.1 (Work.Stems.StepI.fibCM y.2) s) :=
  ⟨fun z hz s => sectFun_trivCM sg hsg0 hsg1 z hz s,
   fun y hy s => trivFun_sectCM sg hsg0 hsg1 y hy s⟩

end

end Work.Stems.StepI
