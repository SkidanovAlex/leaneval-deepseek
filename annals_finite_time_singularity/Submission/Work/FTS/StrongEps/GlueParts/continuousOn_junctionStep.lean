import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.GlueParts.Basic
import Submission.Work.FTS.StrongEps.GlueParts.JunctionDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3 uncurry3)

/-- The piecewise derivative field of the boundary junction is continuous on the closed slab
`U = (0,∞) × (0,π/2) × [0, t+δ]`.

**Fix applied after review.**  The two branches must be forced to agree at the junction points of
`U`: without the hypothesis `hjunc` the field is in general discontinuous at `τ = t` (take `G ≡ 0`,
`H z θ σ = σ`).  With `hjunc` supplied, the proof is:

both pieces are `C¹` on their own closed half-slabs, so `fderivWithin` of each piece is continuous
on that half-slab (`ContDiffOn.continuousOn_fderivWithin`, the half-slab being `UniqueDiffOn` since
`Ioi`, `Ioo` and `Icc 0 t` / `Icc t (t+δ)` all are).  Fix `p ∈ U`:
* if `p.2.2 < t`, restrict to `S := U ∩ {τ < t} ⊆ UG`, where the field equals the `G`-branch and
  its value at `p` is the same, so `ContinuousWithinAt` there; upgrade to `U` with
  `ContinuousWithinAt.mono_of_mem_nhdsWithin` (`S ∈ 𝓝[U] p`);
* if `t < p.2.2`, the same with `U ∩ {t < τ} ⊆ UH`;
* if `p.2.2 = t`, the field is the `G`-branch on `U ∩ {τ ≤ t}` and, on `U ∩ {t ≤ τ}`, it splits
  into `A := U ∩ {τ = t}` (where it is again the `G`-branch, its value at `p` being the `G`-branch)
  and `B := U ∩ {t < τ}` (where it is the `H`-branch, whose value at `p` is the `H`-branch —
  `hjunc` is what identifies this with the value of the field at `p`).  `ContinuousWithinAt.union`
  gives the two halves and then the whole of `U`. -/
theorem continuousOn_junctionStep {G H : Work.FTS.Galerkin.Fam} {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hG : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 G)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t))
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)))
    (hjunc : ∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ), p.2.2 = t →
      fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 G)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t) p =
        fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 H)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) p) :
    ContinuousOn (fun p : Work.FTS.StrongGlobal.P3 =>
        if p.2.2 ≤ t then
          fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 G)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t) p
        else
          fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 H)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) p)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) := by
  -- The two half-slabs are sets of unique differentiability.
  have hUG : UniqueDiffOn ℝ (AG t) := by
    unfold AG
    exact (uniqueDiffOn_Ioi 0).prod
      ((uniqueDiffOn_Ioo 0 (Real.pi / 2)).prod (uniqueDiffOn_Icc ht))
  have hUH : UniqueDiffOn ℝ (BT t δ) := by
    unfold BT
    exact (uniqueDiffOn_Ioi 0).prod
      ((uniqueDiffOn_Ioo 0 (Real.pi / 2)).prod (uniqueDiffOn_Icc (by linarith)))
  -- Continuity of the two branches' derivative fields on their half-slabs.
  have hGc : ContinuousOn (fun p : P3 => fderivWithin ℝ (uncurry3 G) (AG t) p) (AG t) :=
    hG.continuousOn_fderivWithin hUG le_rfl
  have hHc : ContinuousOn (fun p : P3 => fderivWithin ℝ (uncurry3 H) (BT t δ) p) (BT t δ) :=
    hH.continuousOn_fderivWithin hUH le_rfl
  -- Restate the goal with the named sets.
  change ContinuousOn (fun p : P3 =>
      if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) (AG t) p
      else fderivWithin ℝ (uncurry3 H) (BT t δ) p) (AT t δ)
  set F : P3 → (P3 →L[ℝ] ℝ) := fun p : P3 =>
    if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) (AG t) p
    else fderivWithin ℝ (uncurry3 H) (BT t δ) p with hFdef
  -- Membership unfoldings.
  have memAT : ∀ q : P3, q ∈ AT t δ ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2
      ∧ 0 ≤ q.2.2 ∧ q.2.2 ≤ t + δ := by
    intro q
    simp only [AT, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc, and_assoc]
  have memAG : ∀ q : P3, q ∈ AG t ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2
      ∧ 0 ≤ q.2.2 ∧ q.2.2 ≤ t := by
    intro q
    simp only [AG, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc, and_assoc]
  have memBT : ∀ q : P3, q ∈ BT t δ ↔ 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi / 2
      ∧ t ≤ q.2.2 ∧ q.2.2 ≤ t + δ := by
    intro q
    simp only [BT, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc, and_assoc]
  have toAG : ∀ q : P3, q ∈ AT t δ → q.2.2 ≤ t → q ∈ AG t := by
    intro q hq hqt
    obtain ⟨h1, h2, h3, h4, _⟩ := (memAT q).mp hq
    exact (memAG q).mpr ⟨h1, h2, h3, h4, hqt⟩
  have toBT : ∀ q : P3, q ∈ AT t δ → t ≤ q.2.2 → q ∈ BT t δ := by
    intro q hq hqt
    obtain ⟨h1, h2, h3, _, h5⟩ := (memAT q).mp hq
    exact (memBT q).mpr ⟨h1, h2, h3, hqt, h5⟩
  -- The two branches of `F`, pointwise.
  have hF_le : ∀ q : P3, q.2.2 ≤ t → F q = fderivWithin ℝ (uncurry3 G) (AG t) q := by
    intro q hq; rw [hFdef]; exact if_pos hq
  have hF_lt : ∀ q : P3, t < q.2.2 → F q = fderivWithin ℝ (uncurry3 H) (BT t δ) q := by
    intro q hq; rw [hFdef]; exact if_neg (not_le.mpr hq)
  -- The `G`-branch step: on a set contained in `AG t` on which `F` is the `G`-branch.
  have stepG : ∀ (S : Set P3), S ⊆ AG t → (∀ q ∈ S, q.2.2 ≤ t) → ∀ p ∈ AG t, p.2.2 ≤ t →
      ContinuousWithinAt F S p := by
    intro S hSsub hSle p hpAG hple
    have hφ : ContinuousWithinAt (fun q : P3 => fderivWithin ℝ (uncurry3 G) (AG t) q) (AG t) p :=
      hGc p hpAG
    exact hφ.congr_mono (fun q hq => hF_le q (hSle q hq)) hSsub (hF_le p hple)
  have hmain : ∀ p ∈ AT t δ, ContinuousWithinAt F (AT t δ) p := by
    intro p hp
    rcases lt_trichotomy p.2.2 t with hlt | heq | hgt
    · -- strictly left of the junction
      have hple : p.2.2 ≤ t := le_of_lt hlt
      have hpAG : p ∈ AG t := toAG p hp hple
      set S : Set P3 := {q : P3 | q.2.2 < t} ∩ AT t δ with hSdef
      have hSsub : S ⊆ AG t := fun q hq => toAG q hq.2 (le_of_lt hq.1)
      have hSle : ∀ q ∈ S, q.2.2 ≤ t := fun q hq => le_of_lt hq.1
      have hS : ContinuousWithinAt F S p := stepG S hSsub hSle p hpAG hple
      have hmem : S ∈ 𝓝[AT t δ] p := by
        rw [hSdef, mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨{q : P3 | q.2.2 < t},
          (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hlt,
          fun q hq => ⟨hq.1, hq.2⟩⟩
      exact hS.mono_of_mem_nhdsWithin hmem
    · -- at the junction
      have hee : p.2.2 = t := heq
      have hpAG : p ∈ AG t := toAG p hp (le_of_eq hee)
      have hpBT : p ∈ BT t δ := toBT p hp (le_of_eq hee.symm)
      set A1 : Set P3 := {q : P3 | q.2.2 ≤ t} ∩ AT t δ with hA1def
      set B1 : Set P3 := {q : P3 | q.2.2 = t} ∩ AT t δ with hB1def
      set B2 : Set P3 := {q : P3 | t < q.2.2} ∩ AT t δ with hB2def
      have hA1 : ContinuousWithinAt F A1 p :=
        stepG A1 (fun q hq => toAG q hq.2 hq.1) (fun q hq => hq.1) p hpAG (le_of_eq hee)
      have hB1 : ContinuousWithinAt F B1 p :=
        stepG B1 (fun q hq => toAG q hq.2 (le_of_eq hq.1)) (fun q hq => le_of_eq hq.1)
          p hpAG (le_of_eq hee)
      have hB2 : ContinuousWithinAt F B2 p := by
        have hφ : ContinuousWithinAt (fun q : P3 => fderivWithin ℝ (uncurry3 H) (BT t δ) q) B2 p :=
          (hHc p hpBT).mono (fun q hq => toBT q hq.2 (le_of_lt hq.1))
        refine hφ.congr_of_eventuallyEq ?_ ?_
        · filter_upwards [self_mem_nhdsWithin] with q hq
          exact hF_lt q hq.1
        · exact (hF_le p (le_of_eq hee)).trans (hjunc p hp hee)
      have hA2 : ContinuousWithinAt F (AT t δ ∩ {q : P3 | t ≤ q.2.2}) p := by
        have hset : AT t δ ∩ {q : P3 | t ≤ q.2.2} = B1 ∪ B2 := by
          rw [hB1def, hB2def]
          ext q
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
          constructor
          · rintro ⟨h1, h2⟩
            rcases lt_or_eq_of_le h2 with h3 | h3
            · exact Or.inr ⟨h3, h1⟩
            · exact Or.inl ⟨h3.symm, h1⟩
          · rintro (⟨h2, h1⟩ | ⟨h2, h1⟩)
            · exact ⟨h1, le_of_eq h2.symm⟩
            · exact ⟨h1, le_of_lt h2⟩
        rw [hset]
        exact hB1.union hB2
      have hU : AT t δ = A1 ∪ (AT t δ ∩ {q : P3 | t ≤ q.2.2}) := by
        rw [hA1def]
        ext q
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
        constructor
        · intro h1
          rcases le_total q.2.2 t with h2 | h2
          · exact Or.inl ⟨h2, h1⟩
          · exact Or.inr ⟨h1, h2⟩
        · rintro (⟨⟨h2, h1⟩⟩ | ⟨h1, _⟩)
          · exact h1
          · exact h1
      rw [hU]
      exact hA1.union hA2
    · -- strictly right of the junction
      have hge : t ≤ p.2.2 := le_of_lt hgt
      have hpBT : p ∈ BT t δ := toBT p hp hge
      set S : Set P3 := {q : P3 | t < q.2.2} ∩ AT t δ with hSdef
      have hSsub : S ⊆ BT t δ := fun q hq => toBT q hq.2 (le_of_lt hq.1)
      have hS : ContinuousWithinAt F S p := by
        have hφ : ContinuousWithinAt (fun q : P3 => fderivWithin ℝ (uncurry3 H) (BT t δ) q) (BT t δ) p :=
          hHc p hpBT
        exact hφ.congr_mono (fun q hq => hF_lt q hq.1) hSsub (hF_lt p hgt)
      have hmem : S ∈ 𝓝[AT t δ] p := by
        rw [hSdef, mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨{q : P3 | t < q.2.2},
          (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds hgt,
          fun q hq => ⟨hq.1, hq.2⟩⟩
      exact hS.mono_of_mem_nhdsWithin hmem
  exact hmain

end Work.FTS.StrongEps.GlueParts
