import Mathlib
import Submission.Work.Drive.Mono.Split
import Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_range_eq_of_not_isEssential
import Submission.Work.Drive.Final.DentDatum
import Submission.Work.Drive.Final.dentRegion_union_strip

/-!
# The no-jump step of the tilted sweep at an *arbitrary* region with a nice trace

`Work.Drive.Mono.noJumpBelow_of_traceCurves` (`Submission/Work/Drive/Mono/Split.lean`) proves the
`L` field of `Work.Drive.Final.TiltedSweepMono` at every level whose *level region* has a trace which
is a disjoint family of simple inessential closed curves — the "Split argument".  Its proof uses
three properties of the level region `X lamstar`, and nothing else:

* `X lamstar` is *clopen in the complement of the trace* (`closure X ∩ C = X`, obtained there from
  the relative cover and the fact that `X` lies in the interior of the removed set);
* the trace curves are simple, pairwise disjoint and inessential, so the complement of their union has
  a *big* component `K` with `WindingSpan P K = ⊤` (Pardon's Lemma 2 read backwards), and an
  essential loop `δ` of `K` — which, by the previous point, either lies in `X` (contradicting
  `W X = ⊥`) or avoids `closure X`;
* the level region just below `lamstar` is contained in `closure X` together with the closed *strip*
  between the two levels (`Work.Drive.Mono.levelRegion_subset_closure_union_levelStrip`).

The purpose of this file is to *abstract* those three properties, so that the same argument applies
to a region `Ω` which is **not** a level region of the sweep.  This is exactly what the resolution of
the events at an exceptional level needs (the lead's `noJumpBelow_of_goodData`: the region is pushed
by the signed dents at the events, giving a region `Ω` whose trace is nice while its relation to the
level regions below is the strip clause `hstrip`).

## Statement

`Work.Drive.Final.noJumpBelow_of_region` takes

* a carrier-open region `Ω ⊆ P.carrier` with `WindingSpan P Ω = ⊥`;
* a family `cs` of pairwise disjoint simple inessential closed curves of `P` whose union `T` is the
  boundary of `Ω` in the surface, in the sharp form `closure Ω ∩ (P.carrier \ T) = Ω`;
* the union-form genericity of the level `lamstar`: every point of the surface in the closed box and
  the closed slab at that level lies in `closure Ω ∪ T`;
* the strip clause `hstrip`: every level region below `lamstar` is contained in `closure Ω` together
  with the closed strip between its level and `lamstar`;

and concludes that no level close enough below `lamstar` carries the full winding span.

The auxiliary `Work.Drive.Final.exists_levelStrip_disjoint_of_gen` generalizes the strip-compactness
lemma `Work.Drive.Mono.exists_levelStrip_disjoint_of_generic'` from the level region to an arbitrary
set of "forbidden" points; `Work.Drive.Final.clopen_compl_of_interior_frontier` reduces the abstract
clopen clause `hcl` to the geometric data of a "removed set", and
`Work.Drive.Final.noJumpBelow_of_region_geometric` is the version of the theorem stated with those
geometric hypotheses.  (If the region of interest is not contained in the surface — as the *dented*
regions of the design are not — apply the theorem to `Ω ∩ P.carrier`, whose winding span agrees with
that of `Ω`; the clopen clause of the smaller region follows from the one of `Ω`.)
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ}

variable {ψ : Submission.Diffeo} {R : ℝ}

/-- **The strip between the levels `mu` and `lamstar` misses a compact curve, for `mu` close enough
to `lamstar`.**  This is `Work.Drive.Mono.exists_levelStrip_disjoint_of_generic'` with the level
region `X lamstar` replaced by an *arbitrary* set `Z`: the genericity hypothesis says that every
point of the surface in the closed box and the closed slab at the level `lamstar` lies in `Z`, and
`Z` is disjoint from the curve. -/
theorem exists_levelStrip_disjoint_of_gen {lamstar : ℝ} {δ : Work.CoreTopology.ClosedCurve P}
    {Z : Set R3}
    (hgen : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar → z ∈ Z)
    (hdis : Disjoint (Set.range δ.γ) Z) :
    ∃ mu0 : ℝ, mu0 < lamstar ∧ ∀ mu ∈ Set.Ico mu0 lamstar,
      Disjoint (Set.range δ.γ) (Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu lamstar) := by
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
  have hempty : Set.range δ.γ ∩ ⋂ k : ℕ,
      Work.Drive.Mono.levelStrip P s c σ u v h ℓ (lamstar - 1 / ((k : ℝ) + 1)) lamstar = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hz1, hz2⟩
    obtain ⟨t, rfl⟩ := hz1
    have hzk : ∀ k : ℕ, δ.γ t ∈ Work.Drive.Mono.levelStrip P s c σ u v h ℓ
        (lamstar - 1 / ((k : ℝ) + 1)) lamstar := fun k => Set.mem_iInter.mp hz2 k
    have hle : ℓ (δ.γ t) ≤ lamstar := (hzk 0).2.2.2
    have hge : ∀ k : ℕ, lamstar - 1 / ((k : ℝ) + 1) ≤ ℓ (δ.γ t) := fun k => (hzk k).2.2.1
    have hlam : ℓ (δ.γ t) = lamstar := by
      refine le_antisymm hle ?_
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hcon)
      have h1 := hge k
      have h2 : lamstar - (lamstar - ℓ (δ.γ t)) < lamstar - 1 / ((k : ℝ) + 1) := by
        linarith
      linarith
    exact (Set.disjoint_left.mp hdis) ⟨t, rfl⟩
      (hgen (δ.γ t) (δ.mem t) (hzk 0).1 (hzk 0).2.1 hlam)
  obtain ⟨ufin, hufin⟩ :=
    (Work.BoxShrink.PinchOff.isCompact_range_closedCurve δ).elim_finite_subfamily_closed
      (fun k : ℕ => Work.Drive.Mono.levelStrip P s c σ u v h ℓ
        (lamstar - 1 / ((k : ℝ) + 1)) lamstar)
      (fun k => Work.Drive.Mono.isClosed_levelStrip) (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  replace hufin := Set.disjoint_iff_inter_eq_empty.mp hufin
  let k0 : ℕ := ufin.sup id
  refine ⟨lamstar - 1 / ((k0 : ℝ) + 1), hmu_lt k0, ?_⟩
  intro mu hmu
  have hsub : Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu lamstar ⊆
      ⋂ k ∈ ufin, Work.Drive.Mono.levelStrip P s c σ u v h ℓ
        (lamstar - 1 / ((k : ℝ) + 1)) lamstar := by
    intro z hz
    rw [Set.mem_iInter₂]
    intro k hk
    have hk_le : k ≤ k0 := Finset.le_sup (s := ufin) (f := id) hk
    have h1 : lamstar - 1 / ((k : ℝ) + 1) ≤ lamstar - 1 / ((k0 : ℝ) + 1) :=
      hmono k k0 hk_le
    exact Work.Drive.Mono.levelStrip_anti (le_trans h1 hmu.1) hz
  rw [Set.disjoint_left]
  intro z hzr hz2
  have hmem : z ∈ Set.range δ.γ ∩
      (⋂ k ∈ ufin, Work.Drive.Mono.levelStrip P s c σ u v h ℓ
        (lamstar - 1 / ((k : ℝ) + 1)) lamstar) := ⟨hzr, hsub hz2⟩
  rw [hufin] at hmem
  exact hmem

/-- **The sharp form of "the region is clopen in the complement of its trace", from the geometry of
a removed set.**  If `X` lies in the *interior* of a set `A` (the "removed set" of the level) whose
topological frontier contains the trace `T`, and the surface's frontier of `X` is covered by `T`,
then `X` is exactly `closure X` minus `T` inside the surface.

This is the abstract form of the clause `hcl` of `Work.Drive.Final.noJumpBelow_of_region`: it is what
a consumer of the no-jump argument derives from the geometry (for the level regions of the sweep,
from `Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq`; for the dented regions, from the
frontier-transport clause of `Work.Drive.Final.dent_regular`). -/
theorem clopen_compl_of_interior_frontier {X A T : Set R3}
    (hXc : X ⊆ P.carrier)
    (hfront : P.carrier ∩ frontier X ⊆ T)
    (hint : X ⊆ interior A) (hTfr : T ⊆ frontier A) :
    closure X ∩ (P.carrier \ T) = X := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨hzcl, hzc, hzT⟩
    by_contra hzX
    have hzfr : z ∈ frontier X :=
      ⟨hzcl, fun hint' => hzX (interior_subset hint')⟩
    exact hzT (hfront ⟨hzc, hzfr⟩)
  · intro z hz
    refine ⟨subset_closure hz, hXc hz, fun hzT => ?_⟩
    have h1 : z ∈ interior A := hint hz
    have h2 : z ∈ frontier A := hTfr hzT
    rw [frontier_eq_closure_inter_closure] at h2
    rw [interior_eq_compl_closure_compl] at h1
    exact h1 h2.2

/-- **The no-jump step at an arbitrary carrier-open region with a nice trace.**  Let `Ω ⊆ P.carrier`
be carrier-open with vanishing winding span, `cs` a family of pairwise disjoint simple *inessential*
closed curves of `P` whose union is the boundary of `Ω` in the surface (`closure Ω ∩ (P.carrier \ T) =
Ω`), and assume the union-form genericity of the level `lamstar` and the strip clause `hstrip`.

Then no level of the sweep close enough below `lamstar` carries the full winding span.

This is the topological core of the Split argument, stated for a region which need not be a level
region; the consumer at the exceptional levels of the tilted sweep has to supply the two geometric
clauses (`hcl` and `hstrip`) from the dent construction. -/
theorem noJumpBelow_of_region {lamstar : ℝ} {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve P} {Ω : Set R3}
    (hΩc : Ω ⊆ P.carrier)
    (hΩopen : Work.SurgeryInvariance.IsOpenInCarrier P Ω)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hcl : closure Ω ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) = Ω)
    (hbot : Work.SurgeryInvariance.WindingSpan P Ω = ⊥)
    (hgen : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure Ω ∪ ⋃ i, Set.range (cs i).γ)
    (hstrip : ∀ mu : ℝ, mu < lamstar →
      Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
        closure Ω ∪ Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu lamstar) :
    ∃ mu0 : ℝ, mu0 < lamstar ∧ ∀ mu ∈ Set.Ico mu0 lamstar,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) ≠ ⊤ := by
  classical
  set T : Set R3 := ⋃ i, Set.range (cs i).γ with hT
  set C : Set R3 := P.carrier \ T with hC
  -- the trace is closed and lies in the surface
  have hTclosed : IsClosed T := by
    rw [hT]
    exact Work.Drive.EpsFormSphere.isClosed_iUnion_range_closedCurve cs
  have hTsub : T ⊆ P.carrier := by
    intro z hz
    rw [hT] at hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    obtain ⟨t, rfl⟩ := hi
    exact (cs i).mem t
  -- `Ω` is exactly the inside part of the complement of the trace
  have hΩsubC : Ω ⊆ C := by
    intro z hz
    have h1 : z ∈ closure Ω ∩ C := by
      rw [hcl]
      exact hz
    exact h1.2
  have hΩeq : Ω = C ∩ Ω :=
    Set.Subset.antisymm (fun z hz => ⟨hΩsubC hz, hz⟩) Set.inter_subset_right
  have hΩdisjT : Disjoint Ω T := by
    rw [Set.disjoint_left]
    intro z hzΩ hzT
    exact (hΩsubC hzΩ).2 hzT
  -- the ambient open set of the carrier-open region
  obtain ⟨B, hBopen, hBeq⟩ := (isOpen_induced_iff (f := (Subtype.val : P.carrier → R3))
    (s := (Subtype.val ⁻¹' Ω))).mp hΩopen
  have hBΩ : P.carrier ∩ B = Ω := by
    ext x
    constructor
    · rintro ⟨hxc, hxB⟩
      have h1 : (⟨x, hxc⟩ : P.carrier) ∈ Subtype.val ⁻¹' Ω := by
        rw [← hBeq]; exact hxB
      exact h1
    · rintro hxΩ
      refine ⟨hΩc hxΩ, ?_⟩
      have h1 : (⟨x, hΩc hxΩ⟩ : P.carrier) ∈ Subtype.val ⁻¹' Ω := hxΩ
      rw [← hBeq] at h1
      exact h1
  -- membership in `Ω` is membership in the ambient open set, inside the surface
  have hmemB : ∀ z : R3, z ∈ Ω ↔ z ∈ P.carrier ∧ z ∈ B := by
    intro z
    constructor
    · intro hz
      refine ⟨hΩc hz, ?_⟩
      have h1 : (⟨z, hΩc hz⟩ : P.carrier) ∈ Subtype.val ⁻¹' Ω := hz
      rw [← hBeq] at h1
      exact h1
    · rintro ⟨hzc, hzB⟩
      have h1 : (⟨z, hzc⟩ : P.carrier) ∈ Subtype.val ⁻¹' B := hzB
      rw [hBeq] at h1
      exact h1
  -- the big component of the complement of the trace
  obtain ⟨K, hKpre, hKsub, hKW, hKother⟩ :=
    Work.Drive.EpsFormSphere.bigComponent_compl_inessentialCurves (P := P) cs hsimple hess hdisj
  have hKsubC : K ⊆ C := hKsub
  obtain ⟨δ, hδess, hδmem⟩ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P K).mp (by rw [hKW]; exact top_ne_bot)
  have hδrange : Set.range δ.γ ⊆ K := fun z ⟨t, ht⟩ => ht ▸ hδmem t
  -- `δ` avoids the closure of `Ω`
  have hSpre : IsPreconnected (Set.range δ.γ) := by
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P δ]
    exact isPreconnected_Ico.image δ.γ δ.cont.continuousOn
  have hSU : Set.range δ.γ ⊆ B ∪ (closure Ω)ᶜ := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact Or.inl hzB
    · refine Or.inr (fun hzcl => hzB ?_)
      have hzC : z ∈ C := hKsubC (hδrange hz)
      have hzΩ : z ∈ Ω := by
        have h1 : z ∈ closure Ω ∩ C := ⟨hzcl, hzC⟩
        rw [hC] at h1
        rwa [hcl] at h1
      exact (hmemB z).mp hzΩ |>.2
  have hSZdis : Set.range δ.γ ∩ (B ∩ (closure Ω)ᶜ) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzS, hzB, hzV⟩
    have hzC : z ∈ C := hKsubC (hδrange hzS)
    have hzcar : z ∈ P.carrier := by
      obtain ⟨t, ht⟩ := hzS
      rw [← ht]
      exact δ.mem t
    have hzΩ : z ∈ Ω := (hmemB z).mpr ⟨hzcar, hzB⟩
    exact hzV (subset_closure hzΩ)
  have hSdisjClosure : Disjoint (Set.range δ.γ) (closure Ω) := by
    by_cases hSU0 : (Set.range δ.γ ∩ B).Nonempty
    · exfalso
      have hSV0 : Set.range δ.γ ∩ (closure Ω)ᶜ = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        intro hne
        have h1 : (Set.range δ.γ ∩ (B ∩ (closure Ω)ᶜ)).Nonempty :=
          hSpre B (closure Ω)ᶜ hBopen isClosed_closure.isOpen_compl hSU hSU0 hne
        rw [hSZdis] at h1
        exact Set.not_nonempty_empty h1
      have hSsubB : Set.range δ.γ ⊆ B := by
        intro z hz
        rcases hSU hz with h | h
        · exact h
        · have h2 : (Set.range δ.γ ∩ (closure Ω)ᶜ).Nonempty := ⟨z, hz, h⟩
          rw [hSV0] at h2
          exact absurd h2 (Set.not_nonempty_empty)
      have hSsubΩ : Set.range δ.γ ⊆ Ω := by
        intro z hz
        have hzcar : z ∈ P.carrier := by
          obtain ⟨t, ht⟩ := hz
          rw [← ht]
          exact δ.mem t
        exact (hmemB z).mpr ⟨hzcar, hSsubB hz⟩
      have hWne : Work.SurgeryInvariance.WindingSpan P (Set.range δ.γ) ≠ ⊥ :=
        (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr
          ⟨δ, hδess, fun t => ⟨t, rfl⟩⟩
      have hle : Work.SurgeryInvariance.WindingSpan P (Set.range δ.γ) ≤
          Work.SurgeryInvariance.WindingSpan P Ω :=
        Work.SurgeryInvariance.WindingSpan_mono P hSsubΩ
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
  have hdisZT : Disjoint (Set.range δ.γ) (closure Ω ∪ T) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases hz' with h | h
    · exact (Set.disjoint_left.mp hSdisjClosure) hz h
    · exact (hKsubC (hδrange hz)).2 h
  have hgenZ : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure Ω ∪ T := by
    intro z hzc hzP hzs hzl
    rw [hT]
    exact hgen z hzc hzP hzs hzl
  obtain ⟨mu0, hmu0lt, hstrip'⟩ :=
    exists_levelStrip_disjoint_of_gen (P := P) (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) (ℓ := ℓ) (lamstar := lamstar) (δ := δ) (Z := closure Ω ∪ T) hgenZ hdisZT
  refine ⟨mu0, hmu0lt, ?_⟩
  intro mu hmu
  have hdisX : Disjoint (Set.range δ.γ)
      (closure Ω ∪ Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu lamstar) :=
    hSdisjClosure.union_right (hstrip' mu hmu)
  have hsubX : Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
      closure Ω ∪ Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu lamstar :=
    hstrip mu hmu.2
  exact Work.PinchLemma3.ClosedDiscA.ne_top_of_disjoint_essential P
    (X := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu)
    (fun z hz => (Work.Drive.Mono.mem_openTiltedSweepRegion_iff.mp hz).1)
    (fun t hcon => (Set.disjoint_left.mp hdisX) ⟨t, rfl⟩ (hsubX hcon))
    ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P δ).mp hδess)

/-- **The no-jump step at an arbitrary carrier-open region, in the geometric form of the hypotheses**:
instead of the abstract clopen clause `hcl`, the caller supplies the "removed set" `A` of the level,
with `Ω` inside its interior and the trace on its frontier.  This is the form in which the dent
construction can discharge the clause (through the frontier transport of
`Work.Drive.Final.dent_regular`). -/
theorem noJumpBelow_of_region_geometric {lamstar : ℝ} {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve P} {Ω A : Set R3}
    (hΩc : Ω ⊆ P.carrier)
    (hΩopen : Work.SurgeryInvariance.IsOpenInCarrier P Ω)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hfront : P.carrier ∩ frontier Ω ⊆ ⋃ i, Set.range (cs i).γ)
    (hint : Ω ⊆ interior A)
    (hTfr : (⋃ i, Set.range (cs i).γ) ⊆ frontier A)
    (hbot : Work.SurgeryInvariance.WindingSpan P Ω = ⊥)
    (hgen : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure Ω ∪ ⋃ i, Set.range (cs i).γ)
    (hstrip : ∀ mu : ℝ, mu < lamstar →
      Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
        closure Ω ∪ Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu lamstar) :
    ∃ mu0 : ℝ, mu0 < lamstar ∧ ∀ mu ∈ Set.Ico mu0 lamstar,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) ≠ ⊤ :=
  noJumpBelow_of_region hΩc hΩopen hsimple hess hdisj
    (clopen_compl_of_interior_frontier hΩc hfront hint hTfr) hbot hgen hstrip

/-- **The no-jump step at a region which need not be contained in the surface.**  The hypotheses are
stated for the *trace* `P.carrier ∩ Ω` of an arbitrary set `Ω` (this is the form a consumer with a
regions produced by a deformation of space — the dents of the design — can supply), and the
conclusion is the same.

The proof applies `Work.Drive.Final.noJumpBelow_of_region` to `Ω ∩ P.carrier`, whose winding span
agrees with that of `Ω`. -/
theorem noJumpBelow_of_region_inter {lamstar : ℝ} {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve P} {Ω : Set R3}
    (hΩopen : Work.SurgeryInvariance.IsOpenInCarrier P Ω)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hcl : P.carrier ∩ closure Ω ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) = P.carrier ∩ Ω)
    (hbot : Work.SurgeryInvariance.WindingSpan P Ω = ⊥)
    (hgen : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure (P.carrier ∩ Ω) ∪ ⋃ i, Set.range (cs i).γ)
    (hstrip : ∀ mu : ℝ, mu < lamstar →
      Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
        closure (P.carrier ∩ Ω) ∪ Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu lamstar) :
    ∃ mu0 : ℝ, mu0 < lamstar ∧ ∀ mu ∈ Set.Ico mu0 lamstar,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) ≠ ⊤ := by
  have hΩc : P.carrier ∩ Ω ⊆ P.carrier := Set.inter_subset_left
  have hΩ'open : Work.SurgeryInvariance.IsOpenInCarrier P (P.carrier ∩ Ω) := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier] at hΩopen ⊢
    have h : (Subtype.val ⁻¹' (P.carrier ∩ Ω) : Set P.carrier) = Subtype.val ⁻¹' Ω := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
    rw [h]
    exact hΩopen
  have hspan : Work.SurgeryInvariance.WindingSpan P (P.carrier ∩ Ω) =
      Work.SurgeryInvariance.WindingSpan P Ω := by
    rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.WindingSpan,
      Work.SurgeryInvariance.windingVectors, Work.SurgeryInvariance.windingVectors]
    congr 1
    ext w
    constructor
    · rintro ⟨γ, hγ, hw⟩
      exact ⟨γ, fun t => (hγ t).2, hw⟩
    · rintro ⟨γ, hγ, hw⟩
      exact ⟨γ, fun t => ⟨γ.mem t, hγ t⟩, hw⟩
  have hcl' : closure (P.carrier ∩ Ω) ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) =
      P.carrier ∩ Ω := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      have hzcl : z ∈ closure (P.carrier ∩ Ω) := hz.1
      have hzT : z ∈ P.carrier \ ⋃ i, Set.range (cs i).γ := hz.2
      have hzcl' : z ∈ P.carrier ∩ closure Ω :=
        ⟨hzT.1, closure_mono Set.inter_subset_right hzcl⟩
      have hmem : z ∈ P.carrier ∩ closure Ω ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) :=
        ⟨hzcl', hzT.1, hzT.2⟩
      rw [hcl] at hmem
      exact hmem
    · intro z hz
      refine ⟨subset_closure hz, ?_⟩
      have hmem : z ∈ P.carrier ∩ closure Ω ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) := by
        rw [hcl]
        exact hz
      exact ⟨hmem.2.1, hmem.2.2⟩
  exact noJumpBelow_of_region hΩc hΩ'open hsimple hess hdisj hcl'
    (by rw [hspan]; exact hbot) hgen hstrip

/-- **The no-jump step with an *error set*: the form in which the dent supplies the strip clause.**

The literal strip clause `X mu ⊆ closure Ω ∪ levelStrip mu lamstar` of
`Work.Drive.Final.noJumpBelow_of_region` cannot hold for a *dented* region: the dent moves a piece of
the surface off itself (the region `Φ(X lamstar)` is a surface *parallel* to the original one), so
the points of `X lamstar` inside the support of the dent are in neither `closure Ω` nor the strip.
What *does* hold is the version below, with the support of the dent adjoined on the right; and that is
harmless, provided the essential loop `ζ` used by the argument avoids the error set `E` as well.

So the hypotheses here are: an essential closed curve `ζ` of the surface avoiding the region
`closure Ω`, the trace `T = ⋃ cs` and the error set `E`; the union-form genericity at `lamstar`; and
the strip clause with the error set adjoined.  The consumer produces `E` as the trace of the dent's
support ball in the surface and `ζ` from the big component of `carrier ∖ T` by peeling the (inessential)
disc `E` off it — `WindingSpan P (carrier ∖ (T ∪ E)) = ⊤` — which is
`Work.SurgeryInvariance.windingSpan_eq_of_union_disc` applied to the big component. -/
theorem noJumpBelow_of_region_avoiding {lamstar : ℝ} {n : ℕ}
    {cs : Fin n → Work.CoreTopology.ClosedCurve P} {Ω E : Set R3}
    {ζ : Work.CoreTopology.ClosedCurve P}
    (hζess : Work.CoreTopology.IsEssential P ζ)
    (hζavoidΩ : ∀ t : ℝ, ζ.γ t ∉ closure Ω)
    (hζavoidT : ∀ t : ℝ, ζ.γ t ∉ ⋃ i, Set.range (cs i).γ)
    (hζavoidE : ∀ t : ℝ, ζ.γ t ∉ E)
    (hgen : ∀ z : R3, z ∈ P.carrier → z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure Ω ∪ ⋃ i, Set.range (cs i).γ)
    (hstrip : ∀ mu : ℝ, mu < lamstar →
      Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
        (closure Ω ∪ Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu lamstar) ∪ E) :
    ∃ mu0 : ℝ, mu0 < lamstar ∧ ∀ mu ∈ Set.Ico mu0 lamstar,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu) ≠ ⊤ := by
  have hdisΩ : Disjoint (Set.range ζ.γ) (closure Ω) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨t, rfl⟩ := hz
    exact hζavoidΩ t hz'
  have hdis : Disjoint (Set.range ζ.γ)
      (closure Ω ∪ ⋃ i, Set.range (cs i).γ) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨t, rfl⟩ := hz
    rcases hz' with h | h
    · exact hζavoidΩ t h
    · exact hζavoidT t h
  obtain ⟨mu0, hmu0lt, hstrip'⟩ :=
    exists_levelStrip_disjoint_of_gen (P := P) (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) (ℓ := ℓ) (lamstar := lamstar) (δ := ζ)
      (Z := closure Ω ∪ ⋃ i, Set.range (cs i).γ) hgen hdis
  refine ⟨mu0, hmu0lt, ?_⟩
  intro mu hmu
  refine Work.PinchLemma3.ClosedDiscA.ne_top_of_disjoint_essential P
    (X := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu)
    (fun z hz => (Work.Drive.Mono.mem_openTiltedSweepRegion_iff.mp hz).1) (fun t hcon => ?_)
    ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P ζ).mp hζess)
  rcases hstrip mu hmu.2 hcon with h | h
  · rcases h with h | h
    · exact (Set.disjoint_left.mp hdisΩ) ⟨t, rfl⟩ h
    · exact (Set.disjoint_left.mp (hstrip' mu hmu)) ⟨t, rfl⟩ h
  · exact hζavoidE t h

/-! ## The strip clause at a dented region (with the support of the dent as error set) -/

/-! ## The strip clause at the dented region — SUPERSEDED

The former lemma `levelRegion_subset_dentStep_union_strip` used the region
`D.dentStep 1 (X (ℓ D.centre))`, i.e. the *image of the region* under the deformation.  That is the
design's Ω-bug (project lead, 2026-09-26 04:45, item 0; AUDIT §25.7): the image of the region lies
*off* the surface.  The correct region is

    Ω = P.carrier ∩ interior (D.deform '' tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)),

and the error-set strip clause at it is PROVED, upstream, as
`Work.Drive.Final.dentRegion_union_strip`
(`Submission/Work/Drive/Final/dentRegion_union_strip.lean`); consumers of the (L) route should use
that lemma and this region. -/

end

end Work.Drive.Final
