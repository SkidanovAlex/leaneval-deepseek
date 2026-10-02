import Submission.Work.SphHomology.PieceCharted
import Submission.Work.SphHomology.Topology
import Submission.Work.Tubular.PuncturedDiscPair.exists_homeo_sphPiece_proj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The projection of the sphere bundle is open, and clopen sets meeting a fibre are everything

Two topological facts about the unit sphere bundle `S(Z)` of a Euclidean real bundle `Z`:

* `Work.Tubular.PuncturedDiscPair.isOpenMap_sphProj` — the projection `S(Z) → B` is open (it is the
  first coordinate in a trivialisation);
* `Work.Tubular.PuncturedDiscPair.eq_univ_of_isClopen_of_sphOver_singleton` — if the base `B` is
  connected, every clopen subset of `S(Z)` containing the whole fibre `sphOver Z {b₀}` over a point
  `b₀` is everything.

The proof of the second statement: a clopen `W` containing the fibre over `b₀` has clopen complement
`C`; the image of `C` in `B` is open (first lemma) and closed (compact image), and it misses `b₀`,
contradicting the connectedness of `B`.
-/

open Set
open scoped Topology

namespace Work.Tubular.PuncturedDiscPair

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type}

/-- **The projection of the sphere bundle to the base is an open map.** -/
theorem isOpenMap_sphProj (Z : Work.TangentClasses.RealBundle B F ι)
    (hZ : Work.Thom.IsEuclidean Z) :
    IsOpenMap fun p : Work.Thom.SphSub Z => Z.proj (p : Z.TotalSpace) := by
  intro C hC
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨x, hxC, rfl⟩ := ha
  set i : ι := Z.indexAt (Z.proj (x : Z.TotalSpace)) with hi
  have hxmem : x ∈ Work.SphHomology.sphOver Z (Z.baseSet i) :=
    Z.mem_baseSet_at (Z.proj (x : Z.TotalSpace))
  obtain ⟨Φ, hΦ⟩ := exists_homeo_sphPiece_proj Z hZ i
  set xp : Work.SphHomology.SphPiece Z i := ⟨x, hxmem⟩ with hxp
  set uv : ↥(Z.baseSet i) × Work.SphHomology.ModelSph F := Φ.symm xp with huv
  have huveq : Φ uv = xp := Φ.apply_symm_apply xp
  -- the product points mapping into `C`
  let f : ↥(Z.baseSet i) × Work.SphHomology.ModelSph F → Work.Thom.SphSub Z :=
    fun q => ((Φ q : Work.SphHomology.SphPiece Z i) : Work.Thom.SphSub Z)
  have hfcont : Continuous f := by fun_prop
  have hSopen : IsOpen (f ⁻¹' C) := hC.preimage hfcont
  have huvS : uv ∈ f ⁻¹' C := by
    show f uv ∈ C
    show ((Φ uv : Work.SphHomology.SphPiece Z i) : Work.Thom.SphSub Z) ∈ C
    rw [huveq]
    show ((xp : Work.SphHomology.SphPiece Z i) : Work.Thom.SphSub Z) ∈ C
    rw [hxp]
    exact hxC
  obtain ⟨U, V, hU, hV, huvUV, hUV⟩ := isOpen_prod_iff.mp hSopen uv.1 uv.2 huvS
  -- lift the piece-open set `U` to the base
  obtain ⟨U', hU'open, hU'eq⟩ : ∃ U' : Set B, IsOpen U' ∧ Subtype.val ⁻¹' U' = U := by
    obtain ⟨U', hU'open, hU'eq⟩ := isOpen_induced_iff.mp hU
    exact ⟨U', hU'open, hU'eq⟩
  -- the base point of `x` is the first coordinate of `uv`
  have hproj : Z.proj (x : Z.TotalSpace) = (uv.1 : B) := by
    have h := hΦ uv.1 uv.2
    rw [show (uv.1, uv.2) = uv from rfl, huveq] at h
    rw [hxp] at h
    simpa using h
  have hsub : U' ∩ Z.baseSet i ⊆
      (fun p : Work.Thom.SphSub Z => Z.proj (p : Z.TotalSpace)) '' C := by
    rintro b' ⟨hb'U', hb's⟩
    refine ⟨((Φ (⟨⟨b', hb's⟩, uv.2⟩) : Work.SphHomology.SphPiece Z i) : Work.Thom.SphSub Z),
      ?_, ?_⟩
    · have hmem : (⟨⟨b', hb's⟩, uv.2⟩ : ↥(Z.baseSet i) × Work.SphHomology.ModelSph F)
          ∈ f ⁻¹' C := by
        refine hUV.2 ⟨?_, hUV.1⟩
        show (⟨b', hb's⟩ : ↥(Z.baseSet i)) ∈ U
        rw [← hU'eq]
        exact hb'U'
      exact hmem
    · exact hΦ ⟨b', hb's⟩ uv.2
  have hmem' : U' ∩ Z.baseSet i ∈ 𝓝 (Z.proj (x : Z.TotalSpace)) := by
    rw [hproj]
    refine Filter.inter_mem ?_ ?_
    · refine hU'open.mem_nhds ?_
      have h1 : (uv.1 : ↥(Z.baseSet i)) ∈ (Subtype.val : ↥(Z.baseSet i) → B) ⁻¹' U' := by
        rw [hU'eq]; exact huvUV
      exact h1
    · exact (Z.isOpen_baseSet i).mem_nhds uv.1.2
  exact Filter.mem_of_superset hmem' hsub

/-- **A clopen subset of the sphere bundle containing a whole fibre is everything** (for a connected
base). -/
theorem eq_univ_of_isClopen_of_sphOver_singleton [T2Space B] [CompactSpace B] [ConnectedSpace B]
    [FiniteDimensional ℝ F] (Z : Work.TangentClasses.RealBundle B F ι)
    (hZ : Work.Thom.IsEuclidean Z) (b₀ : B)
    {W : Set (Work.Thom.SphSub Z)} (hW : IsClopen W)
    (hFW : Work.SphHomology.sphOver Z ({b₀} : Set B) ⊆ W) : W = Set.univ := by
  haveI : CompactSpace (Work.Thom.SphSub Z) := Work.SphHomology.compactSpace_sphSub Z hZ
  by_contra hne
  have hCopen : IsOpen (Wᶜ) := hW.1.isOpen_compl
  have hCclosed : IsClosed (Wᶜ) := hW.2.isClosed_compl
  have hCne : (Wᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact hne
  have himgclosed : IsClosed ((fun p : Work.Thom.SphSub Z => Z.proj (p : Z.TotalSpace)) '' Wᶜ) :=
    (hCclosed.isCompact.image (Work.SphHomology.continuous_sphProj Z)).isClosed
  have himgopen : IsOpen ((fun p : Work.Thom.SphSub Z => Z.proj (p : Z.TotalSpace)) '' Wᶜ) :=
    isOpenMap_sphProj Z hZ Wᶜ hCopen
  have hb₀ : b₀ ∉ (fun p : Work.Thom.SphSub Z => Z.proj (p : Z.TotalSpace)) '' Wᶜ := by
    rintro ⟨y, hyC, hyb⟩
    refine hyC (hFW ?_)
    simpa [Work.SphHomology.mem_sphOver] using hyb
  obtain ⟨x, hx⟩ := hCne
  have hne' : ((fun p : Work.Thom.SphSub Z => Z.proj (p : Z.TotalSpace)) '' Wᶜ).Nonempty :=
    ⟨_, x, hx, rfl⟩
  rcases isClopen_iff.mp (show IsClopen _ from ⟨himgclosed, himgopen⟩) with h | h
  · rw [h] at hne'
    obtain ⟨z, hz⟩ := hne'
    exact hz
  · rw [h] at hb₀
    exact hb₀ (Set.mem_univ b₀)

end

end Work.Tubular.PuncturedDiscPair
