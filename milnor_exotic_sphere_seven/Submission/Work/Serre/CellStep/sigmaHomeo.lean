import Mathlib
import Submission.Work.Serre.CellStep.Sigma

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.CellStep

/-- If `Z` is covered by pairwise disjoint open sets `P i`, then every point lies in exactly one
of them, and the "index of the piece" map exhibits `Z` as the disjoint union (sigma type) of the
subspaces `P i`.  The homeomorphism is chosen so that the first component of the image of `z` is
exactly the (unique) `i` with `z ∈ P i`. -/
theorem sigmaHomeo {Z : Type} [TopologicalSpace Z] {ι : Type} (P : ι → Set Z)
    (hopen : ∀ i, IsOpen (P i)) (hdisj : Pairwise fun i j => Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = Set.univ) :
    ∃ e : Z ≃ₜ (Σ i, ↥(P i)), ∀ (z : Z) (i : ι), (e z).1 = i ↔ z ∈ P i := by
  classical
  -- Two subtype elements with the same underlying point but living over equal indices are `HEq`.
  have heq_subtype : ∀ {a b : ι} (h : a = b) {x : Z} (ha : x ∈ P a) (hb : x ∈ P b),
      HEq (⟨x, ha⟩ : ↥(P a)) (⟨x, hb⟩ : ↥(P b)) := by
    intro a b h x ha hb
    subst h
    exact heq_of_eq (Subtype.ext rfl)
  -- Every point lies in exactly one piece.
  have huniq : ∀ z : Z, ∃! i, z ∈ P i := by
    intro z
    have hz : z ∈ ⋃ i, P i := by rw [hcover]; exact Set.mem_univ z
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    refine ⟨i, hi, ?_⟩
    intro j hj
    by_contra hne
    have hmem : z ∈ P i ∩ P j := ⟨hi, hj⟩
    have hd : Disjoint (P i) (P j) := hdisj (Ne.symm hne)
    rw [Set.disjoint_iff_inter_eq_empty] at hd
    rw [hd] at hmem
    exact hmem
  choose idx hidx using fun z => (huniq z).exists
  have hidxuniq : ∀ z (i : ι), z ∈ P i → idx z = i :=
    fun z i hi => (huniq z).unique (hidx z) hi
  -- The forward map: send `z` to its index together with itself.
  let f : Z → (Σ i, ↥(P i)) := fun z => ⟨idx z, ⟨z, hidx z⟩⟩
  have hf_eq : ∀ (x : Z) (i : ι) (hx : x ∈ P i), f x = (⟨i, ⟨x, hx⟩⟩ : Σ j, ↥(P j)) := by
    intro x i hx
    exact Sigma.ext (hidxuniq x i hx) (heq_subtype (hidxuniq x i hx) (hidx x) hx)
  -- `f` is continuous: it is continuous on each open piece `P i`.
  have hfcont : Continuous f := by
    refine continuous_of_cover_nhds (s := P) (fun x => ?_) (fun i => ?_)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
      exact ⟨i, (hopen i).mem_nhds hi⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      convert (continuous_sigmaMk (i := i) (σ := fun j => ↥(P j))) using 1
      funext x
      show f (x : Z) = (⟨i, x⟩ : Σ j, ↥(P j))
      rw [hf_eq x.val i x.2]
  -- The backward map: first projection of the sigma type, back into `Z`.
  let g : (Σ i, ↥(P i)) → Z := fun x => x.2.val
  have hgcont : Continuous g := continuous_sigma (fun i => continuous_subtype_val)
  have hleft : Function.LeftInverse g f := fun z => rfl
  have hright : Function.RightInverse g f := by
    intro x
    rcases x with ⟨i, ⟨z, hz⟩⟩
    exact hf_eq z i hz
  refine ⟨{ toFun := f, invFun := g, left_inv := hleft, right_inv := hright,
            continuous_toFun := hfcont, continuous_invFun := hgcont }, ?_⟩
  intro z i
  show idx z = i ↔ z ∈ P i
  exact ⟨fun h => h ▸ hidx z, fun h => hidxuniq z i h⟩

end Work.Serre.CellStep
