import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.MaxPrincipleRegion

/-!
# The Green function of `Ω` forces `Ω` to be connected

The main result of this file, `Work.SimplyConnected.ABS.isPreconnected_of_isGreenOn`, shows that a
domain `Ω ⊆ X` on which a Green function with pole `x₀` exists (`Work.SimplyConnected.ABS.IsGreenOn`)
and which is not all of `X` must be preconnected.  This is used to upgrade the hypotheses of the
disc lemma of Anghel–Bruin–Stan to the connected case.

The tool proved here in passing, `connectedComponentIn_eq_inter_closure`, is the standard fact that
a connected component of a set `F` is closed *in* `F` (`F ∩ closure C = C`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

/-- **A connected component is closed in its ambient set.**  If `C` is the connected component of
`x` inside `F`, then `C = F ∩ closure C`: in other words `C` is closed in the subspace `F`. -/
theorem connectedComponentIn_eq_inter_closure {X : Type*} [TopologicalSpace X] (F : Set X) (x : X) :
    connectedComponentIn F x = F ∩ closure (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · have hD : IsClosed ((Subtype.val : ↥F → X) ⁻¹' (connectedComponentIn F x)) := by
      rw [connectedComponentIn_eq_image hx, Set.preimage_image_eq _ Subtype.val_injective]
      exact isClosed_connectedComponent
    have h := (isClosed_preimage_val (s := F) (t := connectedComponentIn F x)).mp hD
    rw [Set.inter_eq_right.mpr (connectedComponentIn_subset F x)] at h
    exact (subset_inter (connectedComponentIn_subset F x) subset_closure).antisymm h
  · rw [connectedComponentIn_eq_empty hx]
    simp


theorem isPreconnected_of_isGreenOn {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} {x₀ : X} {E : X → ℝ} (hΩo : IsOpen Ω) (hΩne : Ω ≠ Set.univ)
    (hE : Work.SimplyConnected.ABS.IsGreenOn Ω x₀ E) : IsPreconnected Ω := by
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  obtain ⟨hpos, hharm, hcomp, _⟩ := hE
  -- The core of the argument: no point `b ≠ x₀` of `Ω` has its component in `Ω` avoiding `x₀`.
  have key : ∀ b ∈ Ω, b ≠ x₀ → x₀ ∉ connectedComponentIn Ω b → False := by
    intro b hbΩ hbne hx₀C
    set C := connectedComponentIn Ω b with hC
    have hbC : b ∈ C := mem_connectedComponentIn hbΩ
    have hCsub : C ⊆ Ω := connectedComponentIn_subset Ω b
    have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCopen : IsOpen C := hΩo.connectedComponentIn
    have hCeq : C = Ω ∩ closure C := by
      rw [hC]
      exact connectedComponentIn_eq_inter_closure Ω b
    -- `C` is closed in `Ω`: a point of `Ω` in the closure of `C` lies in `C`
    have hCcl : ∀ y ∈ Ω, y ∈ closure C → y ∈ C := by
      intro y hyΩ hycl
      have hmem : y ∈ Ω ∩ closure C := ⟨hyΩ, hycl⟩
      rw [← hCeq] at hmem
      exact hmem
    have hEb : 0 < E b := hpos b hbΩ hbne
    have hεpos : 0 < E b / 2 := by linarith
    have hbε : E b / 2 ≤ E b := by linarith
    obtain ⟨K, hKcpt, hKsub, hK⟩ := hcomp (E b / 2) hεpos
    set A := C ∩ {x : X | E b / 2 ≤ E x} with hA
    have hbA : b ∈ A := ⟨hbC, hbε⟩
    have hAsubK : A ⊆ K := by
      rintro x ⟨hxC, hxE⟩
      by_contra hxK
      exact absurd (hK x (hCsub hxC) hxK) (not_lt.mpr hxE)
    -- `A` is compact: it lies in the compact set `K` and is closed there
    have hAclosed : IsClosed A := by
      rw [← closure_subset_iff_isClosed]
      intro y hycl
      have hyK : y ∈ K := hKcpt.isClosed.closure_subset_iff.mpr hAsubK hycl
      have hyΩ : y ∈ Ω := hKsub hyK
      have hyC : y ∈ C := hCcl y hyΩ (closure_mono inter_subset_left hycl)
      have hyne : y ≠ x₀ := fun h => hx₀C (h ▸ hyC)
      haveI : NeBot (𝓝[A] y) := mem_closure_iff_nhdsWithin_neBot.mp hycl
      have hcont : ContinuousAt E y := (hharm y ⟨hCsub hyC, hyne⟩).continuousAt
      have hT : Tendsto E (𝓝[A] y) (𝓝 (E y)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
      have henv : ∀ᶠ z in 𝓝[A] y, E b / 2 ≤ E z :=
        Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)
      exact ⟨hyC, ge_of_tendsto hT henv⟩
    have hAcpt : IsCompact A := hKcpt.of_isClosed_subset hAclosed hAsubK
    have hAcont : ContinuousOn E (A : Set X) := by
      intro x hx
      exact (hharm x ⟨hCsub hx.1, fun h => hx₀C (h ▸ hx.1)⟩).continuousAt.continuousWithinAt
    -- `E` attains its maximum `E q` on `A`
    obtain ⟨q, hqA, hqmax⟩ := hAcpt.exists_isMaxOn (f := E) ⟨b, hbA⟩ hAcont
    have hqC : q ∈ C := hqA.1
    have hqne : q ≠ x₀ := fun h => hx₀C (h ▸ hqC)
    have hqpos : 0 < E q := hpos q (hCsub hqC) hqne
    -- `E ≤ E q` on all of `C`
    have hEM : ∀ y ∈ C, E y ≤ E q := by
      intro y hy
      by_cases hεy : E b / 2 ≤ E y
      · exact hqmax (show y ∈ A from ⟨hy, hεy⟩)
      · simp only [not_le] at hεy
        have h1 : E b ≤ E q := hqmax hbA
        linarith
    -- the strong maximum principle at `q`
    have hsub : Submission.SubharmonicOnXAt E q := (hharm q ⟨hCsub hqC, hqne⟩).subharmonic
    obtain ⟨V, hV, hVeq⟩ := Submission.SubharmonicOnXAt.eqOn_of_le hsub
      (hCopen.mem_nhds hqC) hEM
    -- `{E = E q} ∩ C` is nonempty and clopen in the preconnected space `C`
    set s : Set C := {y | E y.1 = E q} with hs
    have hcontC : Continuous fun y : C => E y.1 := by
      refine ContinuousOn.comp_continuous ?_ continuous_subtype_val (fun y => y.2)
      intro x hx
      exact (hharm x ⟨hCsub hx, fun h => hx₀C (h ▸ hx)⟩).continuousAt.continuousWithinAt
    have hsclosed : IsClosed s := by
      rw [hs]
      have h := IsClosed.preimage hcontC (isClosed_singleton : IsClosed ({E q} : Set ℝ))
      simpa only [Set.preimage, Set.mem_singleton_iff] using h
    have hsopen : IsOpen s := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      have hyM : E y.1 = E q := hy
      obtain ⟨V', hV', hV'eq⟩ := Submission.SubharmonicOnXAt.eqOn_of_le
        ((hharm y.1 ⟨hCsub y.2, fun h => hx₀C (h ▸ y.2)⟩).subharmonic)
        (hCopen.mem_nhds y.2)
        (fun z hz => by have h1 := hEM z hz; linarith [hyM])
      refine Filter.mem_of_superset (continuous_subtype_val.tendsto y hV') ?_
      intro z hz
      have h2 := hV'eq z.1 hz
      show z ∈ s
      show E z.1 = E q
      exact h2.trans hyM
    have hsne : s.Nonempty := ⟨⟨q, hqC⟩, rfl⟩
    haveI : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hCpre
    have hsuniv : s = univ := by
      rcases isClopen_iff.mp (show IsClopen s from ⟨hsclosed, hsopen⟩) with h | h
      · exact absurd h hsne.ne_empty
      · exact h
    have hEMeq : ∀ y ∈ C, E y = E q := by
      intro y hy
      have h : (⟨y, hy⟩ : C) ∈ s := by rw [hsuniv]; exact Set.mem_univ _
      exact h
    -- `C` is compact
    obtain ⟨K', hK'cpt, hK'sub, hK'⟩ := hcomp (E q / 2) (by linarith)
    have hCsubK' : C ⊆ K' := by
      intro y hy
      by_contra hyK'
      have h1 : E y < E q / 2 := hK' y (hCsub hy) hyK'
      have h2 : E y = E q := hEMeq y hy
      linarith
    have hCclosedX : IsClosed C := by
      rw [← closure_subset_iff_isClosed]
      intro y hycl
      have hyK' : y ∈ K' := hK'cpt.isClosed.closure_subset_iff.mpr hCsubK' hycl
      exact hCcl y (hK'sub hyK') hycl
    -- `C` is clopen in the connected space `X`, so `C = X ⊇ Ω`, contradiction
    have huniv : C = univ := IsClopen.eq_univ ⟨hCclosedX, hCopen⟩ ⟨b, hbC⟩
    exact hΩne (Set.eq_univ_of_univ_subset (by rw [← huniv]; exact hCsub))
  by_contra hΩpre
  -- find a point `b ∈ Ω`, `b ≠ x₀`, whose component in `Ω` does not contain `x₀`
  have hbex : ∃ b ∈ Ω, b ≠ x₀ ∧ x₀ ∉ connectedComponentIn Ω b := by
    by_cases hx₀Ω : x₀ ∈ Ω
    · have hne : connectedComponentIn Ω x₀ ≠ Ω := fun h =>
        hΩpre (h ▸ isPreconnected_connectedComponentIn)
      obtain ⟨b, hbΩ, hbnotin⟩ : ∃ b ∈ Ω, b ∉ connectedComponentIn Ω x₀ := by
        by_contra h
        simp only [not_exists, not_and, not_not] at h
        exact hne (Subset.antisymm (connectedComponentIn_subset Ω x₀) h)
      refine ⟨b, hbΩ, ?_, ?_⟩
      · intro hbb
        subst hbb
        exact hbnotin (mem_connectedComponentIn hx₀Ω)
      · intro hx₀Cb
        have hEq : connectedComponentIn Ω b = connectedComponentIn Ω x₀ :=
          connectedComponentIn_eq hx₀Cb
        rw [← hEq] at hbnotin
        exact hbnotin (mem_connectedComponentIn hbΩ)
    · obtain ⟨b, hbΩ⟩ : Ω.Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        exact fun hempty => hΩpre (hempty ▸ isPreconnected_empty)
      exact ⟨b, hbΩ, (fun h => hx₀Ω (h ▸ hbΩ)),
        fun h => hx₀Ω (connectedComponentIn_subset Ω b h)⟩
  obtain ⟨b, hbΩ, hbne, hx₀Cb⟩ := hbex
  exact key b hbΩ hbne hx₀Cb

end Work.SimplyConnected.ABS

