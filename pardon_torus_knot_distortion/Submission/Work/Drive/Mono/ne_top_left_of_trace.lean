import Mathlib
import Submission.Work.Drive.EpsFormSphere.OpenTiltedRegion
import Submission.Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq
import Submission.Work.Drive.EpsFormSphere.bigComponent_compl_inessentialCurves
import Submission.Work.PinchLemma3.ClosedDiscA.wall_core

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-!
# No-drop at a level of the tilted sweep, from the trace data

This module proves `Work.Drive.Mono.ne_top_left_of_trace`, the "no-jump" step (the `L` field of
`Work.Drive.Final.TiltedSweepMono`) which turns the trace data at a level of the tilted sweep into
the statement that no level just below it carries the full winding span.

The proof is the argument announced in the plan: the trace curves `cs` are simple, pairwise
disjoint and inessential, so their complement in the carrier has a *big* component `K`
(`Work.Drive.EpsFormSphere.bigComponent_compl_inessentialCurves`) carrying an essential loop `δ`.
Since the trace covers the frontier of the region at the level `lamstar` and lies in the frontier
of the removed set `A` (whose interior contains the region), the region at the level `lamstar` is
clopen in the complement of the trace, and `δ` therefore avoids the *closure* of the region.  The
generic value `lamstar` (`hgen`) says that the only points of the surface in the closed box and
closed slab at that level are limits of the region, so the closed strip between a level `mu` close
to `lamstar` and `lamstar` misses `δ`; as `X mu` is contained in the closure of the region at
`lamstar` together with that strip, `δ` avoids `X mu`, and the region is not full.
-/

/-- Membership in the open region of the tilted sweep, as a pure formula. -/
theorem mem_openTiltedSweepRegion_iff {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3} :
    y ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧
        ¬ (|inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y ≤ lam) := by
  simp only [Work.Drive.EpsFormSphere.openTiltedSweepRegion, Set.mem_inter_iff, Set.mem_sdiff,
    Set.mem_setOf_eq, Work.Drive.EpsForm.tiltedSlabClosed]

/-- The part of the closed box and of the closed tilted slab lying between the levels `mu` and
`lamstar`. -/
def levelStrip (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (mu lamstar : ℝ) : Set R3 :=
  closure (Submission.PBox s c σ) ∩
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {y : R3 | mu ≤ ℓ y ∧ ℓ y ≤ lamstar})

/-- The strip is closed. -/
theorem isClosed_levelStrip {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {mu lamstar : ℝ} :
    IsClosed (levelStrip P s c σ u v h ℓ mu lamstar) := by
  have h1 : IsClosed {y : R3 | mu ≤ ℓ y} := isClosed_le continuous_const ℓ.continuous
  have h2 : IsClosed {y : R3 | ℓ y ≤ lamstar} := isClosed_le ℓ.continuous continuous_const
  unfold levelStrip
  exact isClosed_closure.inter
    ((Work.Drive.EpsForm.isClosed_tiltedSlabClosed _ _ _).inter (h1.inter h2))

/-- The strip is antitone in the level. -/
theorem levelStrip_anti {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lamstar : ℝ}
    {a b : ℝ} (hab : a ≤ b) :
    levelStrip P s c σ u v h ℓ b lamstar ⊆ levelStrip P s c σ u v h ℓ a lamstar := by
  rintro z ⟨hz1, hz2, hz3, hz4⟩
  exact ⟨hz1, hz2, le_trans hab hz3, hz4⟩

/-- **The level regions of the tilted sweep decrease to the closure of the level region**: for any
levels `mu` and `lamstar` the region at the level `mu` is contained in the closure of the region at
the level `lamstar` together with the closed strip between the two levels. -/
theorem levelRegion_subset_closure_union_levelStrip {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {mu lamstar : ℝ} :
    Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
      closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar) ∪
        levelStrip P s c σ u v h ℓ mu lamstar := by
  intro z hz
  rw [mem_openTiltedSweepRegion_iff] at hz
  by_cases hzX : z ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar
  · exact Or.inl (subset_closure hzX)
  · have hslab : |inner ℝ v z - (inner ℝ v c + u)| ≤ h := by
      by_contra hcon
      exact hzX (by
        rw [mem_openTiltedSweepRegion_iff]
        exact ⟨hz.1, hz.2.1, fun hc => hcon hc.1⟩)
    have hge : mu ≤ ℓ z := by
      by_contra hcon
      exact hz.2.2 ⟨hslab, le_of_lt (not_le.mp hcon)⟩
    have hle : ℓ z ≤ lamstar := by
      by_contra hcon
      exact hzX (by
        rw [mem_openTiltedSweepRegion_iff]
        exact ⟨hz.1, hz.2.1, fun hc => hcon hc.2⟩)
    exact Or.inr ⟨subset_closure hz.2.1, hslab, hge, hle⟩

/-- **The strip between `mu` and `lamstar` misses a compact curve for `mu` close enough to
`lamstar`.**  If `lamstar` is a limit level of the region (`hgen`: every point of the surface in the
closed box and the closed slab at the level `lamstar` is a limit of points of the region at
`lamstar`) and `δ` avoids the closure of the region at `lamstar`, then for some `mu0 < lamstar` the
strip between every `mu ∈ [mu0, lamstar)` and `lamstar` misses `δ` as well. -/
theorem exists_levelStrip_disjoint_of_generic {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lamstar : ℝ}
    {δ : Work.CoreTopology.ClosedCurve P}
    (hgen : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar))
    (hdis : Disjoint (Set.range δ.γ)
      (closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar))) :
    ∃ mu0 : ℝ, mu0 < lamstar ∧ ∀ mu ∈ Set.Ico mu0 lamstar,
      Disjoint (Set.range δ.γ) (levelStrip P s c σ u v h ℓ mu lamstar) := by
  classical
  have hmu_lt : ∀ k : ℕ, lamstar - 1 / ((k : ℝ) + 1) < lamstar := by
    intro k
    have hpos : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
    linarith
  have hmono : ∀ k k' : ℕ, k ≤ k' →
      lamstar - 1 / ((k : ℝ) + 1) ≤ lamstar - 1 / ((k' : ℝ) + 1) := by
    intro k k' hkk'
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by
      have hc : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hkk'
      linarith
    have h3 : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le h1 h2
    linarith
  have hcl : ∀ k : ℕ,
      IsClosed (levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar) :=
    fun k => isClosed_levelStrip
  have hempty : Set.range δ.γ ∩
      ⋂ k : ℕ, levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hz1, hz2⟩
    obtain ⟨t, rfl⟩ := hz1
    have hzk : ∀ k : ℕ,
        δ.γ t ∈ levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar :=
      fun k => Set.mem_iInter.mp hz2 k
    have hle : ℓ (δ.γ t) ≤ lamstar := (hzk 0).2.2.2
    have hge : ∀ k : ℕ, lamstar - 1 / ((k : ℝ) + 1) ≤ ℓ (δ.γ t) :=
      fun k => (hzk k).2.2.1
    have hlam : ℓ (δ.γ t) = lamstar := by
      refine le_antisymm hle ?_
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hcon)
      have h1 := hge k
      have h2 : lamstar - (lamstar - ℓ (δ.γ t)) < lamstar - 1 / ((k : ℝ) + 1) := by
        linarith
      linarith
    have hmem : δ.γ t ∈ closure
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar) :=
      hgen (δ.γ t) (δ.mem t) (hzk 0).1 (hzk 0).2.1 hlam
    exact (Set.disjoint_left.mp hdis) ⟨t, rfl⟩ hmem
  obtain ⟨ufin, hufin⟩ :=
    (Work.BoxShrink.PinchOff.isCompact_range_closedCurve δ).elim_finite_subfamily_closed
      (fun k : ℕ => levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar)
      hcl (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  replace hufin := Set.disjoint_iff_inter_eq_empty.mp hufin
  let k0 : ℕ := ufin.sup id
  have hk0_lt : lamstar - 1 / ((k0 : ℝ) + 1) < lamstar := hmu_lt k0
  refine ⟨lamstar - 1 / ((k0 : ℝ) + 1), hk0_lt, ?_⟩
  intro mu hmu
  have hsub : levelStrip P s c σ u v h ℓ mu lamstar ⊆
      ⋂ k ∈ ufin, levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar := by
    intro z hz
    rw [Set.mem_iInter₂]
    intro k hk
    have hk_le : k ≤ k0 := Finset.le_sup (s := ufin) (f := id) hk
    have h1 : lamstar - 1 / ((k : ℝ) + 1) ≤ lamstar - 1 / ((k0 : ℝ) + 1) :=
      hmono k k0 hk_le
    exact levelStrip_anti (le_trans h1 hmu.1) hz
  rw [Set.disjoint_left]
  intro z hzr hz2
  have hmem : z ∈ Set.range δ.γ ∩
      (⋂ k ∈ ufin, levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar) :=
    ⟨hzr, hsub hz2⟩
  rw [hufin] at hmem
  exact hmem


/-- **No-drop at a level of the tilted sweep, from the trace data.**

Write `X μ` for `Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ μ` (the open region
of the tilted sweep at the level `μ`) and `A` for `Submission.PBox s c σ \ (tiltedSlabClosed ∩
{ℓ < μ})`.  The trace curves `cs` are supposed to

* **cover the frontier of the region** (`hcover`: `carrier ∩ frontier (X lamstar) ⊆ ⋃ cs`) — this is
  what `TiltedTraceData` supplies for the true trace of the sweep, and it is the condition that the
  earlier version of this statement was missing: the points of the wall `PBox ∩ slab ∪ {ℓ = lamstar}`
  lie in the frontier of the region and are *not* in general in the frontier of the removed set `A`;
* **lie in the frontier of the removed set** (`hsub`: `⋃ cs ⊆ carrier ∩ frontier A`), so that
  `⋃ cs` meets neither `X lamstar` nor the open region;
* be simple, pairwise disjoint and inessential.

If the region `X lamstar` has vanishing winding span (`hbot`) and every point of the surface in the
closed box and the closed tilted slab at the level `lamstar` is a limit of points of `X lamstar`
(`hgen` — the stratified genericity: `lamstar` is not a local maximum of `ℓ|_F` inside the slab),
then no level of `[mu0, lamstar)` close enough to `lamstar` has full span. -/
theorem ne_top_left_of_trace {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lamstar : ℝ}
    {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hcover : P.carrier ∩ frontier
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar)
      ⊆ ⋃ i, Set.range (cs i).γ)
    (hsub : (⋃ i, Set.range (cs i).γ) ⊆ P.carrier ∩ frontier
      (Submission.PBox s c σ \ (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
        {y : R3 | ℓ y < lamstar})))
    (hbot : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar) = ⊥)
    (hgen : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar)) :
    ∃ mu0 : ℝ, mu0 < lamstar ∧ ∀ mu ∈ Set.Ico mu0 lamstar,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) ≠ ⊤ := by
  classical
  set T : Set R3 := ⋃ i, Set.range (cs i).γ with hT
  set X : Set R3 := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lamstar with hX
  set A : Set R3 := Submission.PBox s c σ \
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lamstar}) with hA
  set B : Set R3 := Submission.PBox s c σ \
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lamstar}) with hB
  set C : Set R3 := P.carrier \ T with hC
  -- the trace is closed
  have hTclosed : IsClosed T := by
    rw [hT]
    exact Work.Drive.EpsFormSphere.isClosed_iUnion_range_closedCurve cs
  -- the region is `carrier ∩ B`
  have hXeq : X = P.carrier ∩ B := by
    rw [hB]
    rfl
  -- the region lies in the interior of the removed set `A`
  have hBopen : IsOpen B := by
    rw [hB]
    exact (Work.Topology.SphereSlicing.isOpen_PBox s c σ).sdiff
      ((Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).inter
        (isClosed_Iic.preimage ℓ.continuous))
  have hBsubA : B ⊆ A := by
    rw [hB, hA]
    rintro z ⟨hzb, hrem⟩
    refine ⟨hzb, fun hcon => hrem ⟨hcon.1, ?_⟩⟩
    show ℓ z ≤ lamstar
    exact le_of_lt hcon.2
  have hXsubIntA : X ⊆ interior A := by
    rw [hXeq]
    exact fun z hz => interior_maximal hBsubA hBopen hz.2
  -- the region misses the trace
  have hXdisjT : Disjoint X T := by
    rw [Set.disjoint_left]
    intro z hzX hzT
    have hzint : z ∈ interior A := hXsubIntA hzX
    have hzfr : z ∈ frontier A := (hsub hzT).2
    rw [← closure_sdiff_interior A] at hzfr
    exact hzfr.2 hzint
  -- the region is closed in the complement of the trace
  have hclC : closure X ∩ C = X := by
    apply Subset.antisymm
    · rintro z ⟨hzcl, hzC⟩
      have hzC' : z ∈ P.carrier \ T := by rwa [hC] at hzC
      by_contra hznot
      have hzfr : z ∈ frontier X := by
        rw [← closure_sdiff_interior X]
        exact ⟨hzcl, fun hint => hznot (interior_subset hint)⟩
      exact hzC'.2 (hcover ⟨hzC'.1, hzfr⟩)
    · intro z hz
      have hz0 : z ∈ X := hz
      have hz' : z ∈ P.carrier ∧ z ∈ B := by rw [hXeq] at hz; exact hz
      refine ⟨subset_closure hz0, hz'.1, ?_⟩
      exact fun hzT => (Set.disjoint_left.mp hXdisjT) hz0 hzT
  -- and the complement of the trace splits as `X` and the rest
  have hCB : C ∩ B = X := by
    rw [hXeq]
    apply Subset.antisymm
    · rintro z ⟨hzC, hzB⟩
      have hzC' : z ∈ P.carrier \ T := by rwa [hC] at hzC
      exact ⟨hzC'.1, hzB⟩
    · intro z hz
      have hz0 : z ∈ X := hz
      exact ⟨⟨hz.1, fun hzT => (Set.disjoint_left.mp hXdisjT) hz0 hzT⟩, hz.2⟩
  -- the big component of the complement of the trace
  obtain ⟨K, hKpre, hKsub, hKW, hKother⟩ :=
    Work.Drive.EpsFormSphere.bigComponent_compl_inessentialCurves (P := P) cs hsimple hess hdisj
  have hKsubC : K ⊆ C := by
    rw [hC, hT]
    exact hKsub
  -- an essential loop in it
  obtain ⟨δ, hδess, hδmem⟩ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P K).mp (by rw [hKW]; exact top_ne_bot)
  have hδrange : Set.range δ.γ ⊆ K := fun z ⟨t, ht⟩ => ht ▸ hδmem t
  -- `δ` avoids the closure of the region
  have hSpre : IsPreconnected (Set.range δ.γ) := by
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P δ]
    exact isPreconnected_Ico.image δ.γ δ.cont.continuousOn
  have hSU : Set.range δ.γ ⊆ B ∪ (closure X)ᶜ := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact Or.inl hzB
    · refine Or.inr ?_
      have hzC : z ∈ C := hKsubC (hδrange hz)
      have hzC' : z ∈ P.carrier \ T := by rwa [hC] at hzC
      have hzX : z ∉ X := fun hzX => hzB (by rw [hXeq] at hzX; exact hzX.2)
      intro hzcl
      have hzfr : z ∈ frontier X := by
        rw [← closure_sdiff_interior X]
        exact ⟨hzcl, fun hint => hzX (interior_subset hint)⟩
      exact hzC'.2 (hcover ⟨hzC'.1, hzfr⟩)
  have hSZdis : Set.range δ.γ ∩ (B ∩ (closure X)ᶜ) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzS, hzB, hzV⟩
    have hzCB : z ∈ C ∩ B := ⟨hKsubC (hδrange hzS), hzB⟩
    rw [hCB] at hzCB
    exact hzV (subset_closure hzCB)
  have hSdisjClosure : Disjoint (Set.range δ.γ) (closure X) := by
    by_cases hSU0 : (Set.range δ.γ ∩ B).Nonempty
    · exfalso
      have hSV0 : Set.range δ.γ ∩ (closure X)ᶜ = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        intro hne
        have h1 : (Set.range δ.γ ∩ (B ∩ (closure X)ᶜ)).Nonempty :=
          hSpre B (closure X)ᶜ hBopen isClosed_closure.isOpen_compl hSU hSU0 hne
        rw [hSZdis] at h1
        exact Set.not_nonempty_empty h1
      have hSsubB : Set.range δ.γ ⊆ B := by
        intro z hz
        rcases hSU hz with h | h
        · exact h
        · have h2 : (Set.range δ.γ ∩ (closure X)ᶜ).Nonempty := ⟨z, hz, h⟩
          rw [hSV0] at h2
          exact absurd h2 (Set.not_nonempty_empty)
      have hSsubX : Set.range δ.γ ⊆ X := by
        intro z hz
        have hz' : z ∈ C ∩ B := ⟨hKsubC (hδrange hz), hSsubB hz⟩
        rwa [hCB] at hz'
      have hWne : Work.SurgeryInvariance.WindingSpan P (Set.range δ.γ) ≠ ⊥ :=
        (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr
          ⟨δ, hδess, fun t => ⟨t, rfl⟩⟩
      have hle : Work.SurgeryInvariance.WindingSpan P (Set.range δ.γ) ≤
          Work.SurgeryInvariance.WindingSpan P X :=
        Work.SurgeryInvariance.WindingSpan_mono P hSsubX
      rw [hbot] at hle
      exact hWne (le_bot_iff.mp hle)
    · rw [Set.disjoint_left]
      intro z hzrange hzcl
      rcases hSU hzrange with h | h
      · have h2 : (Set.range δ.γ ∩ B).Nonempty := ⟨z, hzrange, h⟩
        rw [Set.not_nonempty_iff_eq_empty.mp hSU0] at h2
        exact Set.not_nonempty_empty h2
      · exact h hzcl
  -- hence the strip below `lamstar` misses `δ` as well, for levels close enough to `lamstar`
  obtain ⟨mu0, hmu0lt, hstrip⟩ :=
    exists_levelStrip_disjoint_of_generic (P := P) (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) (ℓ := ℓ) (lamstar := lamstar) (δ := δ) hgen hSdisjClosure
  refine ⟨mu0, hmu0lt, ?_⟩
  intro mu hmu
  have hdisX : Disjoint (Set.range δ.γ)
      (closure X ∪ levelStrip P s c σ u v h ℓ mu lamstar) :=
    hSdisjClosure.union_right (hstrip mu hmu)
  have hsubX : Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
      closure X ∪ levelStrip P s c σ u v h ℓ mu lamstar :=
    levelRegion_subset_closure_union_levelStrip (P := P) (mu := mu) (lamstar := lamstar)
  exact Work.PinchLemma3.ClosedDiscA.ne_top_of_disjoint_essential P
    (fun z hz => (mem_openTiltedSweepRegion_iff.mp hz).1)
    (fun t hcon => (Set.disjoint_left.mp hdisX) ⟨t, rfl⟩ (hsubX hcon))
    ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P δ).mp hδess)

end

end Work.Drive.Mono
