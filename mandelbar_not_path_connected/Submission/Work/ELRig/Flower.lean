/-
# ELRig — the API of the equator `E = Ψ '' ℝ`

The equator of the repelling coordinate of the parabolic point `z₁` is the curve
`E = Ψ '' ℝ` of Ecalle height `0`.  This file collects the elementary properties that the
equator-curve rigidity uses:

* `E` is preconnected (it is the image of `ℝ` under the continuous `Ψ`);
* `E ∪ {z₁}` is preconnected (`z₁` is a limit point of `E`, by `Ψ_small`);
* `E` is forward invariant under `F c = (T_c)^{10}` (`Ψ_shift`);
* the petal `Pa` of the flower lies in `K c` (this is the fleet lemma `Pa_subset_K`);
* `Pa` is nonempty as soon as the critical orbit converges to `z₁` (`enters_Pa`).
-/
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.ELRig.rayPt_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {z₁ : ℂ}

/-- The equator is contained in `K c` as soon as its points are: this is a restatement of the
contradiction hypothesis of R-a3/R-f. -/
theorem equator_subset_K (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) z₁)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) :
    equator fl ⊆ K c := fun _ hz => by
  obtain ⟨x, rfl⟩ := hz
  exact hE x

/-- The equator is preconnected. -/
theorem equator_preconnected (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) z₁) :
    IsPreconnected (equator fl) :=
  isPreconnected_range (fl.Ψ_diff.continuous.comp Complex.continuous_ofReal)

/-- `z₁` is a limit point of the equator: the tail `Ψ (Re w < -R)` converges to `z₁`. -/
theorem z1_mem_closure_equator (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) z₁) :
    z₁ ∈ closure (equator fl) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := fl.Ψ_small ε hε
  refine ⟨fl.Ψ ((-(R + 1) : ℝ) : ℂ), ⟨-(R + 1), rfl⟩, ?_⟩
  have hre : ((-(R + 1) : ℝ) : ℂ).re < -R := by simp
  have h2 := (hR _ hre).2
  rwa [dist_eq_norm, norm_sub_rev]

/-- `E ∪ {z₁}` is preconnected: `z₁` lies in the closure of `E`. -/
theorem equator_union_singleton_preconnected
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) z₁) :
    IsPreconnected (equator fl ∪ {z₁}) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro U V hU hV hsub hdisj
  have hS : equator fl ⊆ U ∪ V := fun z hz => hsub (Or.inl hz)
  have hne : ¬ (equator fl ∩ (U ∩ V)).Nonempty := by
    rintro ⟨z, hz, h1, h2⟩
    have hmem : z ∈ (equator fl ∪ {z₁}) ∩ (U ∩ V) := ⟨Or.inl hz, h1, h2⟩
    rw [hdisj] at hmem
    exact hmem
  rcases isPreconnected_iff_subset_of_disjoint.mp (equator_preconnected fl) U V hU hV hS
      (Set.not_nonempty_iff_eq_empty.mp hne) with h | h
  -- in either case the singleton is forced into the same open set as `E`
  · refine Or.inl fun z hz => ?_
    rcases hz with hz | hz
    · exact h hz
    · have hz1 : z = z₁ := Set.mem_singleton_iff.mp hz
      have hzU : z₁ ∈ U := by
        by_contra hzU
        have hzV : z₁ ∈ V := by
          rcases hsub (Or.inr (Set.mem_singleton_iff.mpr rfl)) with h' | h'
          · exact absurd h' hzU
          · exact h'
        have hsubV : equator fl ⊆ Vᶜ := by
          intro w hw
          rintro hwV
          have hmem : w ∈ (equator fl ∪ {z₁}) ∩ (U ∩ V) := ⟨Or.inl hw, h hw, hwV⟩
          rw [hdisj] at hmem
          exact hmem
        have hcl : z₁ ∈ closure (Vᶜ) := closure_mono hsubV (z1_mem_closure_equator fl)
        rw [IsClosed.closure_eq (isClosed_compl_iff.mpr hV)] at hcl
        exact hcl hzV
      simpa [hz1] using hzU
  · refine Or.inr fun z hz => ?_
    rcases hz with hz | hz
    · exact h hz
    · have hz1 : z = z₁ := Set.mem_singleton_iff.mp hz
      have hzV : z₁ ∈ V := by
        by_contra hzV
        have hzU : z₁ ∈ U := by
          rcases hsub (Or.inr (Set.mem_singleton_iff.mpr rfl)) with h' | h'
          · exact h'
          · exact absurd h' hzV
        have hsubU : equator fl ⊆ Uᶜ := by
          intro w hw
          rintro hwU
          have hmem : w ∈ (equator fl ∪ {z₁}) ∩ (U ∩ V) := ⟨Or.inl hw, hwU, h hw⟩
          rw [hdisj] at hmem
          exact hmem
        have hcl : z₁ ∈ closure (Uᶜ) := closure_mono hsubU (z1_mem_closure_equator fl)
        rw [IsClosed.closure_eq (isClosed_compl_iff.mpr hU)] at hcl
        exact hcl hzU
      simpa [hz1] using hzV

/-- The equator is forward invariant under `F c`. -/
theorem mapsTo_equator (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) z₁) :
    Set.MapsTo (F c) (equator fl) (equator fl) := by
  rintro z ⟨x, rfl⟩
  refine ⟨x + 1, ?_⟩
  push_cast
  exact fl.Ψ_shift (x : ℂ)

/-- The attracting petal of the flower lies in the filled Julia set. -/
theorem Pa_subset_K' {c z₁ : ℂ}
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) z₁) : fl.Pa ⊆ K c :=
  Work.ELRig.Pa_subset_K fl

/-- The attracting petal is nonempty, because the critical orbit enters it. -/
theorem Pa_nonempty_of_crit {c : ℂ} {z₁ : ℂ} (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) z₁)
    (hcrit : Tendsto (fun n : ℕ => (F c)^[n] c) atTop (nhds z₁))
    (hne : ∀ n : ℕ, (F c)^[n] c ≠ z₁) : fl.Pa.Nonempty := by
  obtain ⟨n, hn⟩ := fl.enters_Pa c hcrit hne
  exact ⟨_, hn⟩

end Work.EL
