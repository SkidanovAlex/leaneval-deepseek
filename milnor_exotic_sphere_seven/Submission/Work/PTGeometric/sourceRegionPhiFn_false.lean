import Mathlib
import Submission.Work.PTGeometric.SourceRegionPhi
import Submission.Work.PTGeometric.regionNhdBoundaryZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.PTGeometric.exists_sourceRegionPhiFn` is **FALSE**

The requested statement asks for a `C^∞` function `Φ` on the half-space
`A = EuclideanHalfSpace ((8+k)+1)` whose sublevel set `{Φ ≤ 0}` is a compact neighbourhood of a
closed compact set `Z`, contained in a prescribed open set `U`, with the extra clauses of
`Work.PTGeometric.SourceRegionPhiProp`:

* clause (2) `IsSubmersionAt Φ x` at **every** zero `x` of `Φ` (including the boundary zeros!),
* clause (3) (`hone`) at every **boundary** zero `x`: `mfderiv Φ x = c • mfderiv (chart coordinate) x`
  with `c < 0` — i.e. `dΦ_x` is a negative multiple of the boundary-normal functional.

## Why it is false

`Work.PTGeometric.regionNhdBoundaryZero` (proved, sorry-free) says that under clauses (2) and (3)
the function `Φ` is `≤ 0` on a whole neighbourhood of every boundary zero.  Consequently, if `Φ`
satisfies the clauses then the set

  `T := {x ∈ ∂A | Φ x ≤ 0}`

is *open* in `∂A` (at a point of `T` it is a neighbourhood if `Φ < 0` there — `Φ` being continuous —
and a neighbourhood by `regionNhdBoundaryZero` if `Φ = 0` there), and it is *closed* in `∂A` (`Φ` is
continuous).  `∂A ≅ ℝ^{k+8}` is connected and not compact, so `T` is empty or all of `∂A`; as soon as
`Z` meets `∂A`, `T` contains a point of `Z ⊆ {Φ ≤ 0}`, hence is nonempty and therefore equal to
`∂A ⊆ {Φ ≤ 0}` — contradicting the compactness of `{Φ ≤ 0}` (`∂A` is unbounded).

So the clauses force `Z ∩ ∂A = ∅`; but the hypotheses of the statement do not: for instance
`Z = {0}` (the origin of the half-space, `0 ∈ ∂A`) and `U = {‖x‖ < 1}` satisfy all of them.  This
file formalises that: `exists_sourceRegionPhiFn_statement_false` is the negation of the requested
statement, and `not_sourceRegionPhiProp_of_mem_boundary` is the general form
(`Z ∩ ∂A ≠ ∅ ⟹ ¬ SourceRegionPhiProp k Z U`).

## The repair

Two statements which are true (the first is the repair recorded in
`exists_sourceRegionPhi_DIAGNOSIS.md`):

* keep clauses (3), (4), (5), (6) verbatim but restrict clause (2) to the *interior* zeros,
  `∀ x, Φ x = 0 → x.1 0 ≠ 0 → IsSubmersionAt ... Φ x`;
* or keep clause (2) at all zeros and require `Z ∩ ∂A = ∅` (e.g. `∀ x ∈ Z, 0 < x.1 0 < 1`), which
  is incompatible with the intended application, where `Z = sourceZeroSet` meets `∂A`
  (`Work.PTGeometric.sourceZeroSet_boundary_homeo`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

variable {N : ℕ} [NeZero N]


theorem sourceRegionPhiFn_mem_boundary {x : EuclideanHalfSpace N} :
    x ∈ (𝓡∂ N).boundary (EuclideanHalfSpace N) ↔ x.1 0 = 0 := by
  rw [ModelWithCorners.boundary, Set.mem_ofPred_eq, ModelWithCorners.isBoundaryPoint_iff,
    Work.Surgery.frontier_range_halfModel, Work.Surgery.mem_hyperplane_iff,
    extChartAt_self_apply]
  rfl

/-- **The boundary of the half-space is connected.** -/
theorem sourceRegionPhiFn_preconnectedSpace_boundary :
    PreconnectedSpace ↥((𝓡∂ N).boundary (EuclideanHalfSpace N)) := by
  set S : Set (EuclideanSpace ℝ (Fin N)) := {v | v 0 = 0} with hS
  have hSconv : Convex ℝ S := by
    rw [hS]
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, hx, hy, smul_zero, smul_zero, add_zero]
  haveI : PreconnectedSpace ↥S := Subtype.preconnectedSpace hSconv.isPreconnected
  let g : ↥S → EuclideanHalfSpace N := fun v =>
    ⟨(v : EuclideanSpace ℝ (Fin N)), by rw [v.2]⟩
  have hgcont : Continuous g := by
    apply Continuous.subtype_mk continuous_subtype_val
  have himg : IsPreconnected (g '' univ) := isPreconnected_univ.image g hgcont.continuousOn
  have hrange : g '' univ = (𝓡∂ N).boundary (EuclideanHalfSpace N) := by
    rw [Set.image_univ]
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      rw [sourceRegionPhiFn_mem_boundary]
      exact v.2
    · intro hx
      refine ⟨⟨x.1, ?_⟩, Subtype.ext rfl⟩
      rw [sourceRegionPhiFn_mem_boundary] at hx
      exact hx
  have hBpre : IsPreconnected ((𝓡∂ N).boundary (EuclideanHalfSpace N)) := hrange ▸ himg
  exact Subtype.preconnectedSpace hBpre

/-- **Structural lemma.**  Under the clauses (smooth, submersion at every zero, `hone` at every
boundary zero), if `Φ ≤ 0` somewhere on the boundary then `Φ ≤ 0` on the *whole* boundary. -/
theorem sourceRegionPhiFn_boundary_subset_nonpos {Φ : EuclideanHalfSpace N → ℝ}
    (hΦ : ContMDiff (𝓡∂ N) (𝓘(ℝ,ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsub : ∀ x : EuclideanHalfSpace N, Φ x = 0 →
      IsSubmersionAt (𝓡∂ N) (𝓘(ℝ,ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ x)
    (hone : ∀ x ∈ (𝓡∂ N).boundary (EuclideanHalfSpace N), Φ x = 0 →
      ∃ (e : OpenPartialHomeomorph (EuclideanHalfSpace N) (EuclideanHalfSpace N)) (c : ℝ),
        e ∈ IsManifold.maximalAtlas (𝓡∂ N) ((⊤ : ℕ∞) : WithTop ℕ∞) (EuclideanHalfSpace N) ∧
        x ∈ e.source ∧ c < 0 ∧
        (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (𝓡∂ N).boundary (EuclideanHalfSpace N)) ∧
        mfderiv (𝓡∂ N) (𝓘(ℝ,ℝ)) Φ x
          = c • mfderiv (𝓡∂ N) (𝓘(ℝ,ℝ)) (fun y : EuclideanHalfSpace N => (e y).1 0) x)
    (hne : ∃ x ∈ (𝓡∂ N).boundary (EuclideanHalfSpace N), Φ x ≤ 0) :
    ∀ x ∈ (𝓡∂ N).boundary (EuclideanHalfSpace N), Φ x ≤ 0 := by
  haveI : PreconnectedSpace ↥((𝓡∂ N).boundary (EuclideanHalfSpace N)) :=
    sourceRegionPhiFn_preconnectedSpace_boundary
  set T : Set ↥((𝓡∂ N).boundary (EuclideanHalfSpace N)) := {x | Φ x.1 ≤ 0} with hT
  have hcont : Continuous fun x : ↥((𝓡∂ N).boundary (EuclideanHalfSpace N)) => Φ x.1 :=
    hΦ.continuous.comp continuous_subtype_val
  have hTclosed : IsClosed T := by
    rw [hT]
    exact isClosed_le hcont continuous_const
  have hTopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxle : Φ x.1 ≤ 0 := hx
    rw [mem_nhds_subtype]
    by_cases hlt : Φ x.1 < 0
    · refine ⟨{y : EuclideanHalfSpace N | Φ y < 0}, ?_, ?_⟩
      · exact hΦ.continuous.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
      · intro z hz
        exact le_of_lt (show Φ (z : EuclideanHalfSpace N) < 0 from hz)
    · have hx0 : Φ x.1 = 0 := le_antisymm hxle (le_of_not_gt hlt)
      have hev : ∀ᶠ y in 𝓝 x.1, Φ y ≤ 0 :=
        regionNhdBoundaryZero (n := N) (EuclideanHalfSpace N) Φ hΦ hsub hone x.2 hx0
      exact ⟨{y : EuclideanHalfSpace N | Φ y ≤ 0}, hev, fun z hz => hz⟩
  have hTne : T.Nonempty := by
    obtain ⟨x, hx, hle⟩ := hne
    exact ⟨⟨x, hx⟩, hle⟩
  have hTuniv : T = univ := by
    rcases isClopen_iff.mp ⟨hTclosed, hTopen⟩ with h | h
    · exact absurd h hTne.ne_empty
    · exact h
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥((𝓡∂ N).boundary (EuclideanHalfSpace N))) ∈ T := by
    rw [hTuniv]
    exact Set.mem_univ _
  rw [hT] at hmem
  simpa using hmem

/-- **No defining function exists when the set meets the boundary.** -/
theorem not_sourceRegionPhiProp_of_mem_boundary (k : ℕ)
    (Z U : Set (EuclideanHalfSpace ((8 + k) + 1)))
    (hZ : (Z ∩ {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}).Nonempty) :
    ¬ SourceRegionPhiProp k Z U := by
  rintro ⟨Φ, hΦ, hZΦ, -, hK, -, hsub, hone⟩
  haveI : NeZero ((8 + k) + 1) := ⟨by omega⟩
  obtain ⟨p, hpZ, hp0⟩ := hZ
  have hpb : p ∈ (𝓡∂ ((8 + k) + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1)) :=
    sourceRegionPhiFn_mem_boundary.mpr hp0
  have hmain : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1)), Φ x ≤ 0 :=
    sourceRegionPhiFn_boundary_subset_nonpos (N := (8 + k) + 1) hΦ hsub hone ⟨p, hpb, hZΦ hpZ⟩
  have hBsub : (𝓡∂ ((8 + k) + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1))
      ⊆ {x | Φ x ≤ 0} := fun x hx => hmain x hx
  have hBclosed : IsClosed ((𝓡∂ ((8 + k) + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1))) := by
    have hset : (𝓡∂ ((8 + k) + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1))
        = {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0} := by
      ext x
      exact sourceRegionPhiFn_mem_boundary
    rw [hset]
    exact isClosed_eq
      ((PiLp.proj 2 (fun _ : Fin ((8 + k) + 1) => ℝ) 0 :
          EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] ℝ).continuous.comp continuous_subtype_val)
      continuous_const
  have hBcompact : IsCompact ((𝓡∂ ((8 + k) + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1))) :=
    hK.of_isClosed_subset hBclosed hBsub
  set i : Fin ((8 + k) + 1) := ⟨1, by omega⟩ with hi
  have hine : i ≠ 0 := by
    intro h
    have hv : (i : ℕ) = 0 := congrArg Fin.val h
    have hv1 : (i : ℕ) = 1 := by rw [hi]
    omega
  set L : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin ((8 + k) + 1) => ℝ) i with hL
  let g : ↥((𝓡∂ ((8 + k) + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1))) → ℝ :=
    fun x => L (x : EuclideanHalfSpace ((8 + k) + 1)).1
  have hgcont : Continuous g :=
    L.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hgsurj : Function.Surjective g := by
    intro t
    set w : Fin ((8 + k) + 1) → ℝ :=
      Function.update (0 : Fin ((8 + k) + 1) → ℝ) i t with hw
    have hw0 : w 0 = 0 := by
      rw [hw, Function.update_apply, if_neg (Ne.symm hine)]
      rfl
    have hwi : w i = t := by
      rw [hw, Function.update_self]
    have hv0 : ((Work.Surgery.piToEucl ((8 + k) + 1) w :
        EuclideanSpace ℝ (Fin ((8 + k) + 1)))).ofLp 0 = 0 := by
      rw [Work.Surgery.ofLp_piToEucl, hw0]
    refine ⟨⟨⟨Work.Surgery.piToEucl ((8 + k) + 1) w, ?_⟩, ?_⟩, ?_⟩
    · show 0 ≤ ((Work.Surgery.piToEucl ((8 + k) + 1) w :
        EuclideanSpace ℝ (Fin ((8 + k) + 1)))).ofLp 0
      rw [hv0]
    · rw [sourceRegionPhiFn_mem_boundary]
      exact hv0
    · show L (Work.Surgery.piToEucl ((8 + k) + 1) w :
        EuclideanSpace ℝ (Fin ((8 + k) + 1))) = t
      rw [hL, PiLp.proj_apply, Work.Surgery.ofLp_piToEucl, hwi]
  haveI : CompactSpace ↥((𝓡∂ ((8 + k) + 1)).boundary (EuclideanHalfSpace ((8 + k) + 1))) :=
    isCompact_iff_compactSpace.mp hBcompact
  have him : IsCompact (g '' univ) := isCompact_univ.image hgcont
  have hrange : g '' univ = (univ : Set ℝ) := by
    rw [Set.image_univ, Set.range_eq_univ]
    exact hgsurj
  have hbdd : BddAbove (univ : Set ℝ) := by
    rw [← hrange]
    exact him.bddAbove
  obtain ⟨a, ha⟩ := hbdd
  have hle : a + 1 ≤ a := ha (Set.mem_univ (a + 1))
  linarith

/-- **The counterexample with the origin.** -/
theorem not_sourceRegionPhiProp_origin (k : ℕ) :
    ¬ SourceRegionPhiProp k {(0 : EuclideanHalfSpace ((8 + k) + 1))}
      {x : EuclideanHalfSpace ((8 + k) + 1) | ‖x.1‖ < 1} :=
  not_sourceRegionPhiProp_of_mem_boundary k _ _
    ⟨0, Set.mem_singleton _,
      by show (0 : EuclideanSpace ℝ (Fin ((8 + k) + 1))).ofLp 0 = 0; simp⟩

/-- **The requested statement is false**: it fails for `Z = {0}` (a point of the boundary) and
`U = {‖x‖ < 1}`. -/
theorem exists_sourceRegionPhiFn_statement_false :
    ¬ (∀ (k : ℕ) (Z U : Set (EuclideanHalfSpace ((8 + k) + 1))),
        IsClosed Z → IsCompact Z → (∀ x ∈ Z, x.1 0 < 1) → IsOpen U → Z ⊆ U →
        IsCompact (closure U) → SourceRegionPhiProp k Z U) := by
  haveI : T2Space (EuclideanHalfSpace ((8 + 0) + 1)) :=
    inferInstanceAs (T2Space ↥({x : EuclideanSpace ℝ (Fin ((8 + 0) + 1)) | 0 ≤ x 0} : Set _))
  intro h
  refine not_sourceRegionPhiProp_origin 0 ?_
  refine h 0 {(0 : EuclideanHalfSpace ((8 + 0) + 1))}
    {x : EuclideanHalfSpace ((8 + 0) + 1) | ‖x.1‖ < 1}
    isClosed_singleton isCompact_singleton ?_ ?_ ?_ ?_
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    show (0 : EuclideanSpace ℝ (Fin ((8 + 0) + 1))).ofLp 0 < 1
    simp
  · exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    show ‖(0 : EuclideanSpace ℝ (Fin ((8 + 0) + 1)))‖ < 1
    simp
  · have hclosedball : IsCompact
        {x : EuclideanHalfSpace ((8 + 0) + 1) | ‖x.1‖ ≤ 1} := by
      rw [Subtype.isCompact_iff]
      have himg : (Subtype.val ''
            {x : EuclideanHalfSpace ((8 + 0) + 1) | ‖x.1‖ ≤ 1}
            : Set (EuclideanSpace ℝ (Fin ((8 + 0) + 1)))) =
          {v : EuclideanSpace ℝ (Fin ((8 + 0) + 1)) | 0 ≤ v 0 ∧ ‖v‖ ≤ 1} := by
        ext v
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x.2, hx⟩
        · rintro ⟨hv0, hv1⟩
          exact ⟨⟨v, hv0⟩, hv1, rfl⟩
      rw [himg]
      refine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin ((8 + 0) + 1))) 1).of_isClosed_subset
        ?_ ?_
      · exact (isClosed_le continuous_const
          ((PiLp.proj 2 (fun _ : Fin ((8 + 0) + 1) => ℝ) 0 :
            EuclideanSpace ℝ (Fin ((8 + 0) + 1)) →L[ℝ] ℝ).continuous)).inter
          (isClosed_le continuous_norm continuous_const)
      · intro v hv
        rw [Metric.mem_closedBall, dist_eq_norm]
        simpa using hv.2
    refine hclosedball.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (fun x hx => show ‖x.1‖ ≤ 1 from le_of_lt hx) hclosedball.isClosed

end

end Work.PTGeometric

