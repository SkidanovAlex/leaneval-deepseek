import Mathlib
import Submission.Work.Drive.N2C.defs

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set

/-- **Periodic curves have range a compact interval image.**  A map `g : ℝ → X` with `g (x+1) = g x`
has the same range as its restriction to `[0,1]` (every real is an integer translate of its
fractional part). -/
private lemma range_eq_image_Icc {X : Type*} [TopologicalSpace X] {g : ℝ → X}
    (hper : ∀ x, g (x + 1) = g x) : Set.range g = g '' Set.Icc (0 : ℝ) 1 := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
  rintro y ⟨x, rfl⟩
  refine ⟨Int.fract x, ⟨Int.fract_nonneg x, le_of_lt (Int.fract_lt_one x)⟩, ?_⟩
  have hperZ : Function.Periodic g (1 : ℝ) := hper
  have h := (hperZ.int_mul ⌊x⌋) (Int.fract x)
  rw [mul_one, Int.fract_add_floor] at h
  exact h.symm

/-- **The range of a periodic curve is closed** (it is the image of the compact `[0,1]`). -/
private lemma isClosed_range_of_periodic {X : Type*} [TopologicalSpace X] [T2Space X] {g : ℝ → X}
    (hc : Continuous g) (hper : ∀ x, g (x + 1) = g x) : IsClosed (Set.range g) := by
  rw [range_eq_image_Icc hper]
  exact (isCompact_Icc.image hc).isClosed

/-- **A finite, pairwise disjoint, closed, connected cover is a partition into connected
components.**  If `s = ⋃ i, C i` with each `C i` closed in `X`, the pieces pairwise disjoint and
each `C i` preconnected, then for `x ∈ C i` the piece `C i` is exactly the connected component of
`x` inside `s`.

The proof is the standard one: `s \ C i` is the finite union of the other pieces, hence closed, so
`C i` is clopen in the subspace `s`; a preconnected set meeting a clopen set lies inside it, so the
component of `x` in `s` — which contains `x ∈ C i` — is contained in `C i`; the reverse inclusion is
`IsPreconnected.subset_connectedComponentIn`. -/
private theorem eq_connectedComponentIn_of_finite_closed_disjoint_cover
    {X : Type*} [TopologicalSpace X] {s : Set X} {ι : Type*} [Fintype ι]
    (C : ι → Set X) (hCclosed : ∀ i, IsClosed (C i)) (hCsub : ∀ i, C i ⊆ s)
    (hcover : ∀ x ∈ s, ∃ i, x ∈ C i) (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hpre : ∀ i, IsPreconnected (C i))
    (i : ι) {x : X} (hx : x ∈ C i) : C i = connectedComponentIn s x := by
  refine Set.Subset.antisymm (hpre i |>.subset_connectedComponentIn hx (hCsub i)) ?_
  have hxS : x ∈ s := hCsub i hx
  have hdiff : s \ C i = ⋃ j : {j : ι // j ≠ i}, C j.1 := by
    ext y
    constructor
    · intro h
      obtain ⟨hys, hyC⟩ := h
      obtain ⟨j, hj⟩ := hcover y hys
      have hjne : j ≠ i := by rintro rfl; exact hyC hj
      exact Set.mem_iUnion.mpr ⟨⟨j, hjne⟩, hj⟩
    · intro h
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      exact ⟨hCsub j.1 hj, fun hc => Set.disjoint_left.mp (hdisj j.1 i j.2) hj hc⟩
  have hclosedU : IsClosed (⋃ j : {j : ι // j ≠ i}, C j.1) :=
    isClosed_iUnion_of_finite (fun j => hCclosed j.1)
  have hclosedDiff : IsClosed (s \ C i) := hdiff ▸ hclosedU
  have hopen : IsOpen ((↑) ⁻¹' (C i) : Set s) := by
    have hcomp : ((↑) ⁻¹' (C i) : Set s) = ((↑) ⁻¹' (s \ C i) : Set s)ᶜ := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
      exact ⟨fun h => fun ⟨_, hc⟩ => hc h, fun h => by by_contra hc; exact h ⟨y.2, hc⟩⟩
    rw [hcomp]
    exact (hclosedDiff.preimage continuous_subtype_val).isOpen_compl
  have hclopen : IsClopen ((↑) ⁻¹' (C i) : Set s) :=
    ⟨(hCclosed i).preimage continuous_subtype_val, hopen⟩
  rw [connectedComponentIn_eq_image hxS]
  have hsub := isPreconnected_connectedComponent.subset_isClopen hclopen
    (show ((connectedComponent (⟨x, hxS⟩ : s)) ∩ ((↑) ⁻¹' (C i) : Set s)).Nonempty from
      ⟨⟨x, hxS⟩, mem_connectedComponent, hx⟩)
  rintro y ⟨z, hz, rfl⟩
  exact hsub hz

open scoped Manifold ContDiff Topology in
/-- **The range of a component curve of a `LevelCurves` parametrisation is a connected component of
the level** (§1.3 of `N2Lead/NOTES_LEAD_saddlePacket.md`).

`L.γ i`'s range is connected (continuous image of `ℝ`) and closed (it is the range of a continuous
periodic curve, i.e. of the image of the compact `AddCircle 1`), the level `{f = b}` is the finite
union of the pairwise disjoint closed ranges (`L.cover`, `L.disj`), hence each range is open in the
level as well, i.e. clopen — and a clopen connected subset of a topological space is a connected
component. -/
theorem range_eq_connectedComponentIn {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n) (i : Fin n) (t : ℝ) :
    Set.range (L.γ i) = connectedComponentIn {z : M | f z = b} (L.γ i t) := by
  refine eq_connectedComponentIn_of_finite_closed_disjoint_cover
    (s := {z : M | f z = b}) (C := fun j => Set.range (L.γ j))
    (fun j => isClosed_range_of_periodic (L.sm j).continuous (fun x => L.per j x))
    (fun j => ?_) (fun x hx => ?_) (fun j k hjk => ?_)
    (fun j => isPreconnected_range (L.sm j).continuous) i ⟨t, rfl⟩
  · rintro y ⟨u, rfl⟩
    exact L.val j u
  · obtain ⟨j, u, hu⟩ := L.cover x hx
    exact ⟨j, u, hu.symm⟩
  · exact L.disj j k hjk

end Work.Drive.N2Lead
