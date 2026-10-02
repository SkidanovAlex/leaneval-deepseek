import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.lerayHirsch_of_kunnethCP
import Submission.Work.LerayHirsch.lerayHirschFull_of_bundleIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Künneth in the trivial-bundle form implies `KunnethCP`

`Work.LerayHirsch.KunnethCP` is the *trivial case* of the Leray–Hirsch induction in its
single-chart form: for every complex gluing-data bundle `Z` over `B` with a chart `i₀` whose base
set is all of `B` (`Z.baseSet i₀ = Set.univ`), the Leray–Hirsch decomposition holds.

The subproject KUNNETH delivers Künneth for `B × ℂP^{m-1}` in the *trivial-bundle* form
(`Submission/Work/Kunneth/`), i.e. it proves `LerayHirschFull` for
`trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit`; the converse implication
(`lerayHirschFull_trivial_of_kunnethCP`) is immediate from the definition.  This module closes the
equivalence by proving that the trivial-bundle form *implies* `KunnethCP`.

The only mathematical input is that a bundle with a chart covering the whole base is trivial:

* `Work.LerayHirsch.nonempty_bundleIso_trivial_of_baseSet_eq_univ` — a bundle `Z` with
  `Z.baseSet i₀ = Set.univ` is isomorphic (as gluing data, `Work.Thom.BundleIso`) to the trivial
  bundle.  The isomorphism is the chart of `i₀`: on the fibre over `b` it is the transition function
  `Z.coordChange (Z.indexAt b) i₀ b`, whose inverse is `Z.coordChange i₀ (Z.indexAt b) b`; both are
  continuous as functions of `b` because `i₀` covers the base (`Z.continuousOn_coordChange` and
  `Z.coordChange_comp`), which is exactly the hypothesis of the general continuity criterion
  `Work.Thom.continuous_totalSpaceMap_clm_gen`;
* `Work.LerayHirsch.lerayHirschFull_of_bundleIso` — `LerayHirschFull` is invariant under a
  `BundleIso`.

The empty base is handled by `Work.LerayHirsch.lerayHirschFull_of_isEmpty` (the trivial-bundle
hypothesis `h` is only available for nonempty bases, since the statement of the lemma to be proved
quantifies over `[Nonempty B]` there).
-/

namespace Work.LerayHirsch

open Work.TangentClasses

noncomputable section

/-- **A gluing-data bundle with a chart covering the whole base is isomorphic to the trivial
bundle.**  The isomorphism is given by the chart of `i₀`: the fibrewise map over `b` is the
transition function `Z.coordChange (Z.indexAt b) i₀ b` from the chart at `b` to the chart `i₀` (so
that the corresponding map of total spaces is just the chart homeomorphism of `i₀`).  Since `i₀`
covers the base, this transition function equals `Z.coordChange i₁ i₀ b` in the chart of any other
index `i₁`, and it is continuous as a function of `b` by `Z.continuousOn_coordChange i₁ i₀`. -/
theorem nonempty_bundleIso_trivial_of_baseSet_eq_univ {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} (Z : VectorBundleCore 𝕜 B F ι) (i₀ : ι) (hbase : Z.baseSet i₀ = Set.univ) :
    Nonempty (Work.Thom.BundleIso Z (trivialVectorBundleCore 𝕜 B F PUnit)) := by
  have hmem : ∀ b : B, b ∈ Z.baseSet i₀ := fun b => by rw [hbase]; exact Set.mem_univ b
  -- Continuity of the total-space map `Z → B × F`: chart by chart it is `Z.coordChange i₁ i₀ b`.
  have hT : ∀ (i₁ : ι) (i₂ : PUnit), ContinuousOn (fun b : B =>
      (trivialVectorBundleCore 𝕜 B F PUnit).coordChange
        ((trivialVectorBundleCore 𝕜 B F PUnit).indexAt b) i₂ b
      ∘SL ((Z.coordChange (Z.indexAt b) i₀ b) ∘SL Z.coordChange i₁ (Z.indexAt b) b))
      (Z.baseSet i₁ ∩ (ContinuousMap.id B) ⁻¹'
        (trivialVectorBundleCore 𝕜 B F PUnit).baseSet i₂) := by
    intro i₁ i₂
    refine ContinuousOn.congr (f := fun b : B => Z.coordChange i₁ i₀ b) ?_ ?_
    · exact (Z.continuousOn_coordChange i₁ i₀).mono (fun b hb => ⟨hb.1, hmem b⟩)
    · intro b hb
      show (ContinuousLinearMap.id 𝕜 F) ∘SL (Z.coordChange (Z.indexAt b) i₀ b
        ∘SL Z.coordChange i₁ (Z.indexAt b) b) = Z.coordChange i₁ i₀ b
      rw [ContinuousLinearMap.id_comp,
        Z.coordChange_linear_comp i₁ (Z.indexAt b) i₀ b
          ⟨⟨hb.1, Z.mem_baseSet_at b⟩, hmem b⟩]
  -- The same in the reverse direction, with the inverse transition function.
  have hTinv : ∀ (i₁ : PUnit) (i₂ : ι), ContinuousOn (fun b : B =>
      (Z.coordChange (Z.indexAt b) i₂ b)
      ∘SL ((Z.coordChange i₀ (Z.indexAt b) b)
        ∘SL (trivialVectorBundleCore 𝕜 B F PUnit).coordChange
          ((trivialVectorBundleCore 𝕜 B F PUnit).indexAt b) i₁ b))
      ((trivialVectorBundleCore 𝕜 B F PUnit).baseSet i₁ ∩ (ContinuousMap.id B) ⁻¹'
        Z.baseSet i₂) := by
    intro i₁ i₂
    refine ContinuousOn.congr (f := fun b : B => Z.coordChange i₀ i₂ b) ?_ ?_
    · exact (Z.continuousOn_coordChange i₀ i₂).mono (fun b hb => ⟨hmem b, by simpa using hb.2⟩)
    · intro b hb
      show Z.coordChange (Z.indexAt b) i₂ b ∘SL (Z.coordChange i₀ (Z.indexAt b) b
        ∘SL ContinuousLinearMap.id 𝕜 F) = Z.coordChange i₀ i₂ b
      rw [ContinuousLinearMap.comp_id,
        Z.coordChange_linear_comp i₀ (Z.indexAt b) i₂ b
          ⟨⟨hmem b, Z.mem_baseSet_at b⟩, by simpa using hb.2⟩]
  refine ⟨{ hom := fun b => (Z.coordChange (Z.indexAt b) i₀ b).toLinearMap
            inv := fun b => (Z.coordChange i₀ (Z.indexAt b) b).toLinearMap
            left_inv := ?_
            right_inv := ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · intro b x
    show (Z.coordChange i₀ (Z.indexAt b) b) ((Z.coordChange (Z.indexAt b) i₀ b) x) = x
    rw [Z.coordChange_comp (Z.indexAt b) i₀ (Z.indexAt b) b
        ⟨⟨Z.mem_baseSet_at b, hmem b⟩, Z.mem_baseSet_at b⟩ x,
      Z.coordChange_self (Z.indexAt b) b (Z.mem_baseSet_at b) x]
  · intro b y
    show (Z.coordChange (Z.indexAt b) i₀ b) ((Z.coordChange i₀ (Z.indexAt b) b) y) = y
    rw [Z.coordChange_comp i₀ (Z.indexAt b) i₀ b
        ⟨⟨hmem b, Z.mem_baseSet_at b⟩, hmem b⟩ y,
      Z.coordChange_self i₀ b (hmem b) y]
  · have h := Work.Thom.continuous_totalSpaceMap_clm_gen Z
      (trivialVectorBundleCore 𝕜 B F PUnit) (ContinuousMap.id B)
      (fun b => Z.coordChange (Z.indexAt b) i₀ b) hT
    exact h.congr (fun p => rfl)
  · have h := Work.Thom.continuous_totalSpaceMap_clm_gen
      (trivialVectorBundleCore 𝕜 B F PUnit) Z (ContinuousMap.id B)
      (fun b => Z.coordChange i₀ (Z.indexAt b) b) hTinv
    exact h.congr (fun p => rfl)

/-- **The trivial-bundle form of Künneth implies `KunnethCP`.**  Given `LerayHirschFull` for the
trivial bundle in every rank `m` over every nonempty base, every bundle with a chart covering its
base enjoys `LerayHirschFull`: it is isomorphic to the trivial bundle
(`nonempty_bundleIso_trivial_of_baseSet_eq_univ`), and `LerayHirschFull` is invariant under a bundle
isomorphism (`lerayHirschFull_of_bundleIso`).  For the empty base both sides are trivial
(`lerayHirschFull_of_isEmpty`). -/
theorem kunnethCP_of_trivialBundles
    (h : ∀ (m : ℕ) (B : Type) [TopologicalSpace B] [Nonempty B],
      Work.LerayHirsch.LerayHirschFull (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)) :
    Work.LerayHirsch.KunnethCP := by
  intro m B _ ι _ Z hZ
  by_cases hB : Nonempty B
  · haveI : Nonempty B := hB
    obtain ⟨i₀, hi₀⟩ := hZ
    obtain ⟨e⟩ := nonempty_bundleIso_trivial_of_baseSet_eq_univ Z i₀ hi₀
    exact (lerayHirschFull_of_bundleIso e).mpr (h m B)
  · haveI : IsEmpty B := not_nonempty_iff.mp hB
    exact lerayHirschFull_of_isEmpty Z

end

end Work.LerayHirsch
