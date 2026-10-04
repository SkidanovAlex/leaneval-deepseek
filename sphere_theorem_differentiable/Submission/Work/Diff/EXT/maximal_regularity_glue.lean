import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Diff.Grad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gluing local smooth extensions of a family of metrics (the `maximal_regularity` glue)

This module contains the *bookkeeping* half of `Work.Diff.EXT.maximal_regularity`: the section map
`secMap` of a family of metrics, the identification of `JointSmooth` with smoothness of that section
(`jointSmooth_iff_secMap`), and the gluing lemma `glue_extensions` together with its consequence
`maximal_regularity_of_inputs` (regularity at the maximal time from the two inputs `H` — a smooth
extension across `T` — and `K` — a smooth extension to the left of `0`).

It is split off from `maximal_regularity.lean` so that the latter can import the whole analytic
machine (`local_ext_closed`, hence the Shi estimates and the frame family) without dragging the
`TotalSpace`-instance-heavy statements along: in the presence of those extra instances the type
class search for `TopologicalSpace (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) _)` — needed by
`𝓘(ℝ, F)` for the model space of the bundle of bilinear forms — gets stuck, which is why the
glue lives in this module with a small import closure.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The section map of a family of smooth metrics: the body of `JointSmooth`. -/
noncomputable def secMap (F : ℝ → SMet I M) : ℝ × M →
    TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  fun p ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2 ((F p.1).inner p.2)

lemma jointSmooth_iff_secMap {F : ℝ → SMet I M} {J : Set ℝ} :
    JointSmooth F J ↔ ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞) (secMap (I := I) F)
      (J ×ˢ (univ : Set M)) :=
  Iff.rfl

/-- If two metric families agree on a set of times, their section maps agree there. -/
lemma secMap_congr {F F' : ℝ → SMet I M} {s : Set ℝ} (h : ∀ t ∈ s, F t = F' t) :
    ∀ p ∈ s ×ˢ (univ : Set M), secMap (I := I) F p = secMap (I := I) F' p := by
  rintro ⟨t, y⟩ ⟨ht, -⟩
  simp only [secMap]
  rw [h t ht]

lemma prod_univ_mem_nhds {s : Set ℝ} {t : ℝ} {y : M} (hs : s ∈ 𝓝 t) :
    s ×ˢ (univ : Set M) ∈ 𝓝 (t, y) := by
  rw [nhds_prod_eq]
  exact Filter.prod_mem_prod hs Filter.univ_mem

/-- **Gluing local extensions.**  If `G₁` coincides with `G` on `[T-δ, T)` and `G₂` coincides with
`G` on `[0, ε)`, then the family which is `G₂` for `t < 0`, `G` for `0 ≤ t ≤ T - δ/2` and `G₁` for
`t > T - δ/2` is jointly smooth on `(-ε', T+ε')` and agrees with `G` on `[0,T)`. -/
theorem glue_extensions
    (G G₁ G₂ : ℝ → SMet I M) (T δ ε : ℝ) (hδ : 0 < δ) (hTδ : 0 < T - δ) (hε : 0 < ε)
    (hG : JointSmooth G (Ico 0 T))
    (h₁ : JointSmooth G₁ (Ioo (T - δ) (T + δ)))
    (h₁G : ∀ t ∈ Ico (T - δ) T, G₁ t = G t)
    (h₂ : JointSmooth G₂ (Ioo (-ε) ε))
    (h₂G : ∀ t ∈ Ico 0 ε, G₂ t = G t) :
    ∃ ε' > 0, ∃ F : ℝ → SMet I M,
      JointSmooth F (Ioo (-ε') (T + ε')) ∧ ∀ t ∈ Ico 0 T, F t = G t := by
  have hhalf : 0 < T - δ / 2 := by linarith
  set η : ℝ := min (ε / 2) (min ((T - δ) / 2) (δ / 2)) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηδ : η < δ := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  refine ⟨η, hηpos, fun t ↦ if t < 0 then G₂ t else if t ≤ T - δ / 2 then G t else G₁ t,
    ?_, ?_⟩
  · rw [jointSmooth_iff_secMap]
    rintro ⟨t, y⟩ ⟨ht, -⟩
    simp only [mem_prod, mem_univ, and_true] at ht
    have htlo : -η < t := ht.1
    have hthi : t < T + η := ht.2
    have key : ∀ (G' : ℝ → SMet I M) (s : Set ℝ),
        (∀ u ∈ s, (if u < 0 then G₂ u else if u ≤ T - δ / 2 then G u else G₁ u) = G' u) →
        s ∈ 𝓝 t →
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
          (secMap (I := I) G') (t, y) →
        ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
          (secMap (I := I) (fun t ↦ if t < 0 then G₂ t
            else if t ≤ T - δ / 2 then G t else G₁ t))
          (Ioo (-η) (T + η) ×ˢ (univ : Set M)) (t, y) := by
      intro G' s hs hmem hG'at
      refine (hG'at.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [prod_univ_mem_nhds hmem] with p hp
      exact secMap_congr hs p hp
    rcases lt_trichotomy t 0 with ht0 | ht0 | ht0
    · -- t < 0 : use G₂
      refine key G₂ (Ioo (-ε) 0) ?_ (isOpen_Ioo.mem_nhds ⟨by linarith, ht0⟩) ?_
      · intro u hu
        rw [if_pos hu.2]
      · exact h₂.contMDiffAt (prod_univ_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩))
    · -- t = 0 : use G₂ on (-η, min ε (T - δ/2))
      subst ht0
      refine key G₂ (Ioo (-η) (min ε (T - δ / 2))) ?_
        (isOpen_Ioo.mem_nhds ⟨by linarith, lt_min hε hhalf⟩) ?_
      · intro u hu
        by_cases hu0 : u < 0
        · rw [if_pos hu0]
        · rw [if_neg hu0, if_pos (le_of_lt (lt_of_lt_of_le hu.2 (min_le_right _ _))),
            h₂G u ⟨not_lt.mp hu0, lt_of_lt_of_le hu.2 (min_le_left _ _)⟩]
      · exact h₂.contMDiffAt (prod_univ_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩))
    · -- 0 < t
      rcases lt_or_ge t (T - δ / 2) with htT | htT
      · -- 0 < t < T - δ/2 : use G on (0, T)
        have hIoo : Ioo (0 : ℝ) T ∈ 𝓝 t :=
          isOpen_Ioo.mem_nhds ⟨ht0, by linarith [htT, hhalf]⟩
        have hmem : Ico 0 T ×ˢ (univ : Set M) ∈ 𝓝 (t, y) :=
          Filter.mem_of_superset (prod_univ_mem_nhds hIoo)
            (fun p hp => ⟨Set.mem_Ico.mpr ⟨le_of_lt hp.1.1, hp.1.2⟩, trivial⟩)
        refine key G (Ioo 0 (T - δ / 2)) ?_ (isOpen_Ioo.mem_nhds ⟨ht0, htT⟩)
          (hG.contMDiffAt hmem)
        intro u hu
        rw [if_neg (not_lt.mpr (le_of_lt hu.1)), if_pos (le_of_lt hu.2)]
      · rcases eq_or_lt_of_le htT with htT' | htT'
        · -- t = T - δ/2 : junction; use G₁ (which equals G on (T-δ, T))
          subst htT'
          refine key G₁ (Ioo (T - δ) T) ?_
            (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
            (h₁.contMDiffAt (prod_univ_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)))
          intro u hu
          rw [if_neg (not_lt.mpr (by linarith [hu.1]))]
          by_cases hle : u ≤ T - δ / 2
          · rw [if_pos hle, h₁G u ⟨le_of_lt hu.1, hu.2⟩]
          · rw [if_neg hle]
        · -- T - δ/2 < t : use G₁
          refine key G₁ (Ioo (T - δ) (T + δ)) ?_
            (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
            (h₁.contMDiffAt (prod_univ_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)))
          intro u hu
          rw [if_neg (not_lt.mpr (by linarith [hu.1]))]
          by_cases hle : u ≤ T - δ / 2
          · rw [if_pos hle, h₁G u ⟨le_of_lt hu.1, by linarith [hle, hδ]⟩]
          · rw [if_neg hle]
  · -- agreement with G on [0,T)
    intro t ht
    change (if t < 0 then G₂ t else if t ≤ T - δ / 2 then G t else G₁ t) = G t
    rw [if_neg (not_lt.mpr ht.1)]
    by_cases hle : t ≤ T - δ / 2
    · rw [if_pos hle]
    · rw [if_neg hle]
      exact h₁G t ⟨by linarith [not_le.mp hle, hδ], ht.2⟩



/-- **Reduction of the target to its two inputs.**  If the family `G` has a smooth extension across
`T` (`H`-input: a family smooth on `(T-δ, T+δ)` agreeing with `G` on `[T-δ, T)`) and a smooth
extension to the left of `0` (`K`-input: a family smooth on `(-ε, ε)` agreeing with `G` on `[0, ε)`),
then `maximal_regularity`'s conclusion holds.  This is the gluing part of the proof; the `H`-input
is the analytic core (Shi's a priori estimates), the `K`-input is the jet-matching construction at
`t = 0`. -/
theorem maximal_regularity_of_inputs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : JointSmooth G (Ico 0 T))
    (hH : ∃ δ > 0, ∃ H₁ : ℝ → SMet I M,
      JointSmooth H₁ (Ioo (T - δ) (T + δ)) ∧ ∀ t ∈ Ico (T - δ) T, H₁ t = G t)
    (hK : ∃ ε > 0, ∃ K : ℝ → SMet I M,
      JointSmooth K (Ioo (-ε) ε) ∧ ∀ t ∈ Ico 0 ε, K t = G t) :
    ∃ ε > 0, ∃ G' : ℝ → SMet I M,
      JointSmooth G' (Ioo (-ε) (T + ε)) ∧ ∀ t ∈ Ico 0 T, G' t = G t := by
  obtain ⟨δ, hδ, H₁, hH₁, hH₁G⟩ := hH
  obtain ⟨ε, hε, K, hK₁, hK₁G⟩ := hK
  -- shrink `δ` so that the junction `T - δ/2` lies in `(0,T)`
  set δ' : ℝ := min δ (T / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ (by linarith)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hTδ' : 0 < T - δ' := by
    have h2 : δ' ≤ T / 2 := min_le_right _ _
    linarith
  have hH₁' : JointSmooth H₁ (Ioo (T - δ') (T + δ')) := by
    rw [jointSmooth_iff_secMap] at hH₁ ⊢
    exact hH₁.mono (fun p hp => ⟨⟨by linarith [hp.1.1, hδ'le], by linarith [hp.1.2, hδ'le]⟩, hp.2⟩)
  have hH₁G' : ∀ t ∈ Ico (T - δ') T, H₁ t = G t :=
    fun t ht => hH₁G t ⟨by linarith [ht.1, hδ'le], ht.2⟩
  exact glue_extensions G H₁ K T δ' ε hδ'pos hTδ' hε hflow hH₁' hH₁G' hK₁ hK₁G

end Work.Diff.EXT
