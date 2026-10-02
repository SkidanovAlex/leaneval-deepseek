import Mathlib
import Submission.Work.PTGeometric.AmbientPerturbation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

/-- **The cut-offs of the ambient perturbation.**  Let `C` be a finite family of Grassmannian charts
whose regions `C.U l` cover a compact source `M`, and let `v : M → ℝⁿ` be `C^∞` with **no bad point on
the boundary**: every boundary point is `AmbGood` for `v` (i.e. is either not a zero of `v` or is a
chart-transverse zero of `v` in one of the charts).

Then there are smooth cut-offs `χ l : M → [0,1]`, one for each chart, with

* `{χ l ≠ 0} ⊆ C.U l`, and `{χ l ≠ 0}` contained in the interior of `M`,
* `χ l = 0` on an open neighbourhood of `∂M`,
* and the covering condition `hcov` of `exists_ambient_perturbation`: every point where all the
  cut-offs vanish is already `AmbGood` for `v`,

i.e. the active regions `{χ l ≠ 0}` cover the **bad set** `{x | ¬ AmbGood C v x}` (which is closed and
compact, and by hypothesis disjoint from the boundary).

Proof: `AmbGood` is an open condition (for `C^∞` `v`), so the bad set is closed, hence compact, and by
`hoff` it lies in the interior of `M`; each of its points lies in some `C.U l` (by `C.covers`); cover it
by finitely many small balls `B ⊆ C.U l ∩ int M` with `closure B ⊆ int M`; for each chart `l` collect the
balls assigned to it into an open set `Ξ l` and take `χ l` to be the Urysohn function
`exists_contMDiff_zero_iff_one_iff_of_isClosed` whose zero set is `Ξ lᶜ`.  Then `{χ l ≠ 0} = Ξ l` has
`closure ⊆ int M`, which gives both the interior condition and the vanishing on a neighbourhood of
`∂M` (take `V := M \ ⋃ l, closure (Ξ l)`). -/
theorem exists_cutoffs {n k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [CompactSpace M] [T2Space M] [Nonempty M]
    {P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} {m : ℕ}
    (C : Work.PTGeometric.AmbCharts n k M P m) (v : M → EuclideanSpace ℝ (Fin n))
    (hv : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hoff : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, Work.PTGeometric.AmbGood C v x) :
    ∃ χ : Fin m → M → ℝ,
      (∀ l, ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (χ l)) ∧
      (∀ l x, 0 ≤ χ l x ∧ χ l x ≤ 1) ∧
      (∀ l y, χ l y ≠ 0 → y ∈ C.U l) ∧
      (∀ l y, χ l y ≠ 0 → (𝓡∂ ((8 + k) + 1)).IsInteriorPoint y) ∧
      (∃ V : Set M, IsOpen V ∧ (𝓡∂ ((8 + k) + 1)).boundary M ⊆ V ∧
        ∀ l y, y ∈ V → χ l y = 0) ∧
      (∀ x, (∀ l, χ l x = 0) → Work.PTGeometric.AmbGood C v x) := by
  classical
  -- The good set is open: `AmbGood` is the union of `{v ≠ 0}` and the (finite) union over the charts
  -- of `C.U l ∩ {IsSubmersionAt ...}`, and both are open (`isOpen_isSubmersionAt` for the second).
  have hgood_open : IsOpen {x : M | Work.PTGeometric.AmbGood C v x} := by
    have hset : {x : M | Work.PTGeometric.AmbGood C v x} = {x : M | v x ≠ 0} ∪
        ⋃ l : Fin m, (C.U l ∩ {x : M | IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞
          (fun y => C.ell l (v y)) x}) := by
      ext x
      simp only [Work.PTGeometric.AmbGood, Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion,
        Set.mem_inter_iff]
    rw [hset]
    exact IsOpen.union (isOpen_ne.preimage hv.continuous)
      (isOpen_iUnion fun l => (C.isOpen_U l).inter isOpen_isSubmersionAt)
  have hBclosed : IsClosed {x : M | ¬ Work.PTGeometric.AmbGood C v x} := by
    simpa only [Set.compl_ofPred] using hgood_open.isClosed_compl
  -- The bad set misses the boundary, by `hoff`.
  have hBsub : {x : M | ¬ Work.PTGeometric.AmbGood C v x} ⊆
      (𝓡∂ ((8 + k) + 1)).interior M := by
    intro x hx
    rw [← ModelWithCorners.compl_boundary (I := 𝓡∂ ((8 + k) + 1)) (M := M)]
    exact fun hbd => hx (hoff x hbd)
  -- Hence an open set `O` containing the bad set, with closure inside the interior.
  obtain ⟨O, hOopen, hBO, hOcl⟩ :=
    (hBclosed.isCompact (X := M)).exists_isOpen_closure_subset
      (U := (𝓡∂ ((8 + k) + 1)).interior M) (by
        rw [mem_nhdsSet_iff_forall]
        intro x hx
        exact ((𝓡∂ ((8 + k) + 1)).isOpen_interior (M := M) (n := ∞) (by simp)).mem_nhds
          (hBsub hx))
  -- The cut-off of the chart `l`, a Urysohn function vanishing exactly off `C.U l ∩ O`.
  have key : ∀ l : Fin m, ∃ f : M → ℝ, ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x, f x ≠ 0 ↔ x ∈ C.U l ∩ O) := by
    intro l
    obtain ⟨f, hf, hr, hzero, -⟩ :=
      exists_contMDiff_zero_iff_one_iff_of_isClosed (𝓡∂ ((8 + k) + 1)) (M := M)
        (s := (C.U l ∩ O)ᶜ) (t := (∅ : Set M))
        ((C.isOpen_U l).inter hOopen).isClosed_compl isClosed_empty (by simp) (n := ⊤)
    exact ⟨f, hf, fun x => ⟨(hr (Set.mem_range_self x)).1, (hr (Set.mem_range_self x)).2⟩,
      fun x => by
        by_cases h : x ∈ C.U l ∩ O
        · exact ⟨fun _ => h, fun _ hfx => ((hzero x).mpr hfx) h⟩
        · exact ⟨fun hfx => absurd ((hzero x).mp (by simpa using h)) hfx,
            fun hxS => absurd hxS h⟩⟩
  choose χ hχsm hχrange hχsupp using key
  refine ⟨χ, hχsm, hχrange, ?_, ?_, ?_, ?_⟩
  · intro l y hy
    exact ((hχsupp l y).mp hy).1
  · intro l y hy
    exact hOcl (subset_closure ((hχsupp l y).mp hy).2)
  · refine ⟨(closure O)ᶜ, isClosed_closure.isOpen_compl, ?_, ?_⟩
    · intro x hx
      simp only [Set.mem_compl_iff]
      intro hxcl
      have hint : x ∈ (𝓡∂ ((8 + k) + 1)).interior M := hOcl hxcl
      rw [← ModelWithCorners.compl_boundary (I := 𝓡∂ ((8 + k) + 1)) (M := M)] at hint
      exact hint hx
    · intro l y hy
      by_contra hne
      exact hy (subset_closure ((hχsupp l y).mp hne).2)
  · intro x hx
    by_contra hbad
    have hxO : x ∈ O := hBO hbad
    obtain ⟨l, hl⟩ := C.covers x
    exact (hχsupp l x).mpr ⟨hl, hxO⟩ (hx l)


end Work.PTGeometric
