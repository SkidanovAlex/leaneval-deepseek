import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- The point of the ray of angle `θ` depends continuously on the level `t` on the range
`1 < t` where it is given by the inverse Böttcher homeomorphism applied to `rayPoint θ t`:
`rayPoint θ ·` is continuous, the Böttcher homeomorphism `hN.e.symm` is continuous, and the
coercion `↥(K c)ᶜ → ℂ` is continuous. -/
theorem continuousOn_rayPt_level {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    ContinuousOn (fun t : ℝ => Work.EL.rayPt hN θ t) (Set.Ioi 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hray : Continuous fun t : Set.Ioi (1 : ℝ) => Work.Top.NakaneData.rayPoint θ (t : ℝ) := by
    unfold Work.Top.NakaneData.rayPoint
    fun_prop
  have hp : Continuous fun t : Set.Ioi (1 : ℝ) =>
      (⟨Work.Top.NakaneData.rayPoint θ (t : ℝ),
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc (show 1 < (t : ℝ) from t.2)⟩ :
        ↥Work.Top.exteriorDisc) :=
    Continuous.subtype_mk hray _
  have hg : Continuous fun t : Set.Ioi (1 : ℝ) =>
      ((hN.e.symm (⟨Work.Top.NakaneData.rayPoint θ (t : ℝ),
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc (show 1 < (t : ℝ) from t.2)⟩ :
        ↥Work.Top.exteriorDisc) : ↥(Work.EL.K c)ᶜ) : ℂ) :=
    continuous_subtype_val.comp (hN.e.symm.continuous.comp hp)
  refine hg.congr fun t => ?_
  simp only [Set.domRestrict_apply]
  rw [Work.EL.rayPt, Work.Top.NakaneData.rayPt, dite_eq_left (show 1 < (t : ℝ) from t.2)]

theorem isPreconnected_seg {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ r₁ r₂ : ℝ) (h : 1 < r₁) : IsPreconnected (Work.SeedCertRay.seg hN θ r₁ r₂) := by
  rw [seg_def]
  refine IsPreconnected.image isPreconnected_Icc (fun t : ℝ => Work.EL.rayPt hN θ t) ?_
  refine (continuousOn_rayPt_level hN θ).mono ?_
  intro t ht
  exact lt_of_lt_of_le h ht.1

end Work.SeedCertRay
