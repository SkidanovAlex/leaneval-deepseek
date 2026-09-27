import Submission.Work.Compact.Main
import Submission.Work.Conn.PathConnected.pathConnectedSpace_of_homotopyEquiv_sphere
import Submission.Work.Homology.HomotopyEquivHomology
import Submission.Work.Homology.Bridge

/-!
# The universe-polymorphic compactness theorem

The ported homology libraries (`Work.Cohomology`, `Work.Homology`) are formulated for
`TopCat.{0}`, so the area's main theorem `Work.Compact.compactSpace_of_homotopyEquiv_sphere` is
stated for `M : Type`.  The challenge quantifies over `M : Type*`, and `ULift` cannot lower a
universe; this file supplies the bridge, following the lead's note
`Submission/Work/Compact/NOTES_LEAD_poincare_universe.md`.

The idea: if `M` were noncompact, take a *small* open connected noncompact neighbourhood `U` of the
image of the homotopy inverse `Sⁿ → M` — obtained as the component of a finite union of chart
sources, hence `Small.{0} U` since it injects into `Finset M × ℝⁿ`.  Moving `U` to `Type 0` with
`Shrink.homeomorph` gives a Type-`0` manifold `U'` carrying maps `Sⁿ → U' → Sⁿ` whose composite is
homotopic to the identity; but `Hₙ(U') = 0` by Hatcher 3.29 (the Type-`0` theorem
`Work.Compact.Noncompact.isZero_homology_of_noncompact`), so the identity of `Hₙ(Sⁿ) ≅ ℤ` would
factor through `0`.

## Main declarations

* `Work.Compact.exists_small_open_nbhd`
* `Work.Compact.false_of_dominated_type0`
* `Work.Compact.false_of_dominated`
* `Work.Compact.compactSpace_of_homotopyEquiv_sphere_univ`
-/

open Metric (sphere)
open Topology
open CategoryTheory Limits

universe u

namespace Work.Compact

/-- A compact connected set in a connected noncompact charted space has a small, open, connected,
noncompact neighbourhood. -/
theorem exists_small_open_nbhd {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M] [NoncompactSpace M]
    {K : Set M} (hK : IsCompact K) (hKc : IsConnected K) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ IsConnected U ∧ ¬ IsCompact U ∧ Small.{0} U := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : M => (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (fun x => (chartAt _ x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_chart_source _ x⟩)
  set V : Set M := ⋃ i ∈ s, (chartAt (EuclideanSpace ℝ (Fin n)) i).source with hV
  have hVo : IsOpen V := isOpen_biUnion fun i _ => (chartAt _ i).open_source
  obtain ⟨k, hk⟩ := hKc.nonempty
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  refine ⟨connectedComponentIn V k, hVo.connectedComponentIn, ?_, ?_, ?_, ?_⟩
  · exact hKc.isPreconnected.subset_connectedComponentIn hk hs
  · exact isConnected_connectedComponentIn_iff.2 (hs hk)
  · intro hc
    have hclopen : IsClopen (connectedComponentIn V k) := ⟨hc.isClosed, hVo.connectedComponentIn⟩
    have h := hclopen.eq_univ ⟨k, mem_connectedComponentIn (hs hk)⟩
    rw [h] at hc
    exact noncompact_univ M hc
  · have hmem : ∀ v : connectedComponentIn V k,
        ∃ i : s, v.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) i.1).source := by
      intro v
      have := connectedComponentIn_subset V k v.2
      simp only [hV, Set.mem_iUnion] at this
      obtain ⟨i, hi, hv⟩ := this
      exact ⟨⟨i, hi⟩, hv⟩
    let idx : connectedComponentIn V k → s := fun v => (hmem v).choose
    refine small_of_injective
      (f := fun v => (idx v, chartAt (EuclideanSpace ℝ (Fin n)) (idx v).1 v.1)) ?_
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have ha := (hmem a).choose_spec
    have hb := (hmem b).choose_spec
    apply Subtype.ext
    have ha' : a.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (idx b).1).source := by
      rw [← h1]; exact ha
    rw [h1] at h2
    exact (chartAt _ (idx b).1).injOn ha' hb h2

/-- Type-`0` key lemma: a connected noncompact `n`-manifold cannot be homotopy dominated by `Sⁿ`,
using that its top homology vanishes (Hatcher 3.29). -/
theorem false_of_dominated_type0 (n : ℕ) (hn : 1 ≤ n) {U : Type} [TopologicalSpace U]
    [T2Space U] [ChartedSpace (EuclideanSpace ℝ (Fin n)) U] [ConnectedSpace U]
    [NoncompactSpace U] (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1), U))
    (f : C(U, ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    (h : (f.comp g).Homotopic (ContinuousMap.id _)) : False := by
  let S := TopCat.of ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  let F : TopCat.of U ⟶ S := TopCat.ofHom f
  let G : S ⟶ TopCat.of U := TopCat.ofHom g
  have hH : TopCat.Homotopy (G ≫ F) (𝟙 S) := h.some
  have hz : IsZero (Work.Homology.singHomology Work.Homology.ZMod n (TopCat.of U)) :=
    Work.Compact.Noncompact.isZero_homology_of_noncompact n hn
  have h1 := Work.Homology.singHomologyMap_congr Work.Homology.ZMod n hH
  rw [Work.Homology.singHomologyMap_comp, Work.Homology.singHomologyMap_id] at h1
  have hS : IsZero (Work.Homology.singHomology Work.Homology.ZMod n S) := by
    rw [IsZero.iff_id_eq_zero, ← h1, hz.eq_of_tgt (Work.Homology.singHomologyMap _ n G) 0,
      zero_comp]
  obtain ⟨e2⟩ := Work.Cohomology.sphereHomologyTop n hn
  have hZ : IsZero (ModuleCat.of ℤ ℤ) := hS.of_iso e2.symm
  have hid : (𝟙 (ModuleCat.of ℤ ℤ)) = 0 := (IsZero.iff_id_eq_zero (ModuleCat.of ℤ ℤ)).mp hZ
  have h10 : (1 : ℤ) = 0 := by
    have h := congrArg
      (fun f : (ModuleCat.of ℤ ℤ) ⟶ (ModuleCat.of ℤ ℤ) => (show ℤ → ℤ from f) 1) hid
    simpa using h
  exact one_ne_zero h10

/-- Universe transfer via `Shrink`. -/
theorem false_of_dominated (n : ℕ) (hn : 1 ≤ n) {U : Type u} [TopologicalSpace U]
    [T2Space U] [ChartedSpace (EuclideanSpace ℝ (Fin n)) U] [ConnectedSpace U]
    [NoncompactSpace U] [Small.{0} U]
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1), U))
    (f : C(U, ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))
    (h : (f.comp g).Homotopic (ContinuousMap.id _)) : False := by
  let e : U ≃ₜ Shrink.{0} U := Shrink.homeomorph U
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Shrink.{0} U) := e.chartedSpace
  haveI : T2Space (Shrink.{0} U) := e.symm.isEmbedding.t2Space
  haveI : ConnectedSpace (Shrink.{0} U) := e.surjective.connectedSpace e.continuous
  haveI : NoncompactSpace (Shrink.{0} U) :=
    ⟨fun h => noncompact_univ U (by simpa [Set.image_univ] using h.image e.symm.continuous)⟩
  refine false_of_dominated_type0 n hn ((e : C(U, Shrink.{0} U)).comp g)
    (f.comp (e.symm : C(Shrink.{0} U, U))) ?_
  convert h using 1
  ext x; simp

/-- **Compactness of a homotopy `n`-sphere, in an arbitrary universe**: a Hausdorff `n`-manifold
homotopy equivalent to `Sⁿ` (`n ≥ 1`) is compact. -/
theorem compactSpace_of_homotopyEquiv_sphere_univ (n : ℕ) (hn : 1 ≤ n) {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : ContinuousMap.HomotopyEquiv M (↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) :
    CompactSpace M := by
  by_contra hM
  haveI : NoncompactSpace M := ⟨fun h => hM ⟨h⟩⟩
  haveI : ConnectedSpace M :=
    (Work.Conn.PathConnected.pathConnectedSpace_of_homotopyEquiv_sphere hn e).connectedSpace
  haveI : ConnectedSpace (↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
    have : IsConnected (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
      isConnected_sphere (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; exact_mod_cast (by omega : 1 < n + 1)) 0 zero_le_one
    exact Subtype.connectedSpace this
  have hK : IsCompact (Set.range e.invFun) := isCompact_range e.invFun.continuous
  have hKc : IsConnected (Set.range e.invFun) := isConnected_range e.invFun.continuous
  obtain ⟨U, hUo, hKU, hUc, hUnc, hUs⟩ := exists_small_open_nbhd (n := n) hK hKc
  let W : TopologicalSpace.Opens M := ⟨U, hUo⟩
  haveI : ConnectedSpace W := Subtype.connectedSpace hUc
  haveI : NoncompactSpace W := ⟨fun h => hUnc (by
    have h' := h.image continuous_subtype_val
    rw [Set.image_univ, Subtype.range_coe] at h'
    exact h')⟩
  haveI : Small.{0} W := hUs
  exact false_of_dominated n hn (U := W)
    ⟨fun x => ⟨e.invFun x, hKU ⟨x, rfl⟩⟩, by fun_prop⟩
    (e.toFun.comp ⟨Subtype.val, continuous_subtype_val⟩)
    (by convert e.right_inv using 1; ext x; rfl)

end Work.Compact
