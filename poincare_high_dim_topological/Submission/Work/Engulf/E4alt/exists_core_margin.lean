import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Geo.Radial.ChartImage

/-!
# `Work.Engulf.E4alt.exists_core_margin` — the uniform margin of the non-core part

`NormData.mesh` says that every face of the fine complex `Γ₁` is either *core* (its `f`-image lies
in the `5/8`-cube of the chart `ψ`) or has its whole `g₁`-image outside the closed `9/16`-cube.
This file upgrades the second alternative to a **uniform** margin: there is `μ > 0` such that every
point `x` of `Γ₁.space` outside the union of the core faces has `ball (g₁ x) μ` disjoint from
`ψ '' closedCube (9/16)`.

The proof is the compactness argument one expects.  Let `G` be the (finite, `NormData.hΓ₁`) family
of *non-core* faces of `Γ₁` and put

* `F' := ⋃ {simp s | s ∈ G}`, a compact subset of `Γ₁.space`;
* `A := g₁ '' F'`, compact because `g₁` is continuous on `Γ₁.space`;
* `K' := ψ '' closedCube (9/16)`, compact (`isCompact_image_closedCube`).

By `NormData.mesh`, `A ∩ K' = ∅`; `K'` is closed and nonempty, so `infDist b K' > 0` for every
`b ∈ A`.  The extreme value theorem for the continuous function `infDist · K'` on the compact `A`
(`IsCompact.exists_forall_le'` with `a = 0`) then produces `μ > 0` with `μ ≤ infDist b K'` for all
`b ∈ A`.  Finally every `x ∈ Γ₁.space` outside the core faces lies in some face `s ∈ Γ₁.faces`,
which then cannot be core (otherwise `x` would be in the core), so `s ∈ G`, `x ∈ F'`,
`g₁ x ∈ A` and for `z ∈ K'` one has `dist z (g₁ x) = dist (g₁ x) z ≥ infDist (g₁ x) K' ≥ μ`.

This is the `hmarg` hypothesis of `Work.Engulf.E4S.stepG`: it is what makes the "transfer lemma"
`Work.Engulf.E4S.eq_g₁_of_mem_closedCube` work for maps that are only `μ`-close to `g₁`.
-/

open Set Metric PL

namespace Work.Engulf.E4alt

theorem exists_core_margin {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ ND.Γ₁.space, x ∉ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ →
      ∀ z : M, dist z (ND.g₁ x) < μ → z ∉ ψ.toFun '' PL.closedCube (9 / 16 : ℝ) := by
  classical
  -- the target region: the chart image of the closed `9/16`-cube
  let K' : Set M := ψ.toFun '' PL.closedCube (9 / 16 : ℝ)
  have hK'c : IsCompact K' :=
    Work.Geo.Radial.isCompact_image_closedCube ψ (9 / 16 : ℝ) (by norm_num)
  have hK'ne : K'.Nonempty := by
    refine ⟨ψ.toFun 0, ?_⟩
    exact ⟨0, by simp [PL.closedCube]; norm_num, rfl⟩
  have hK'cl : IsClosed K' := hK'c.isClosed
  -- the non-core faces of `Γ₁`
  let G : Finset (Finset (PL.E N)) := ND.hΓ₁.toFinset.filter
    (fun s => ¬ (f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ)))
  have hGmem : ∀ s, s ∈ G ↔ s ∈ ND.Γ₁.faces ∧
      ¬ (f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ)) := by
    intro s
    show s ∈ ND.hΓ₁.toFinset.filter _ ↔ _
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  -- their union, and the image of that union under `g₁`
  let F' : Set (PL.E N) := ⋃ s ∈ G, PL.simp s
  have hsimpc : ∀ s : Finset (PL.E N), IsCompact (PL.simp s) := fun s => by
    simpa [PL.simp] using (Finset.finite_toSet s).isCompact_convexHull ℝ
  have hF'c : IsCompact F' := Finset.isCompact_biUnion G (fun s _ => hsimpc s)
  have hF'sub : F' ⊆ ND.Γ₁.space := by
    intro x hx
    obtain ⟨s, hsG, hxs⟩ := Set.mem_iUnion₂.mp hx
    exact Geometry.SimplicialComplex.convexHull_subset_space (K := ND.Γ₁) ((hGmem s).mp hsG).1 hxs
  -- `NormData.mesh` on the non-core faces
  have hmesh : ∀ s ∈ ND.Γ₁.faces, ¬ (f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ)) →
      ∀ x ∈ PL.simp s, ND.g₁ x ∉ K' := by
    intro s hs hns x hx
    rcases ND.mesh s hs with h | h
    · exact absurd h hns
    · exact h x hx
  -- a point of `Γ₁.space` outside the core faces lies in a non-core face
  have hmemF' : ∀ x ∈ ND.Γ₁.space, x ∉ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ → x ∈ F' := by
    intro x hx hxc
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    have hnoncore : ¬ (f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ)) := by
      intro hc
      exact hxc (Set.mem_iUnion₂.mpr ⟨s, hs, Set.mem_iUnion.mpr ⟨hc, hxs⟩⟩)
    exact Set.mem_iUnion₂.mpr ⟨s, (hGmem s).mpr ⟨hs, hnoncore⟩, hxs⟩
  let A : Set M := ND.g₁ '' F'
  have hAc : IsCompact A := hF'c.image_of_continuousOn (ND.g₁cont.mono hF'sub)
  -- the extreme value theorem for `infDist · K'` on `A`
  have hApos : ∀ b ∈ A, (0 : ℝ) < infDist b K' := by
    rintro b ⟨x, hxF', rfl⟩
    obtain ⟨s, hsG, hxs⟩ := Set.mem_iUnion₂.mp hxF'
    exact (hK'cl.notMem_iff_infDist_pos hK'ne).mp
      (hmesh s ((hGmem s).mp hsG).1 ((hGmem s).mp hsG).2 x hxs)
  obtain ⟨μ, hμ0, hμle⟩ := hAc.exists_forall_le' (f := fun b => infDist b K')
      (continuous_infDist_pt K').continuousOn hApos
  refine ⟨μ, hμ0, ?_⟩
  intro x hxΓ hxc z hz hzK
  have hxA : ND.g₁ x ∈ A := ⟨x, hmemF' x hxΓ hxc, rfl⟩
  have h1 : μ ≤ infDist (ND.g₁ x) K' := hμle (ND.g₁ x) hxA
  have h2 : infDist (ND.g₁ x) K' ≤ dist (ND.g₁ x) z := infDist_le_dist_of_mem hzK
  rw [dist_comm] at hz
  linarith

end Work.Engulf.E4alt
