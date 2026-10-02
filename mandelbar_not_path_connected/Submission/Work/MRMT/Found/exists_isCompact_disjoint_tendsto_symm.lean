import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open Filter Topology Metric
open scoped Topology

/-- Given a compact set `L` disjoint from the image `φ '' S` of a set `S` with no accumulation
point (`hS`), the inverse approximants `(F n)⁻¹` map `L` eventually into a fixed compact set `K`
disjoint from `S`.

The proof is topological and uses only the locally uniform convergence `(F n)⁻¹ → φ⁻¹`:
* `hS` forces `S` to be closed;
* `φ⁻¹ '' L` is compact and disjoint from the closed set `S`, so it is contained in the open set
  `Sᶜ`; compactness gives a closed thickening `cthickening δ (φ⁻¹ '' L) ⊆ Sᶜ`;
* the half-thickening `K := cthickening (δ/2) (φ⁻¹ '' L)` is compact and disjoint from `S`, and
  uniform convergence on the compact `L` puts `(F n)⁻¹ '' L` inside it for all large `n`. -/
theorem exists_isCompact_disjoint_tendsto_symm {μ : ℂ → ℂ}
    (d : Work.MRMT.Found.PrincipalData μ) {S : Set ℂ}
    (hS : ∀ z : ℂ, Filter.Eventually (fun w => w ∉ S) (nhdsWithin z {z}ᶜ))
    {L : Set ℂ} (hL : IsCompact L) (hLdisj : Disjoint L ((d.φ : ℂ → ℂ) '' S)) :
    ∃ K : Set ℂ, IsCompact K ∧ Disjoint K S ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ w ∈ L, (((d.Fn n).symm : ℂ ≃ₜ ℂ) : ℂ → ℂ) w ∈ K := by
  -- ## `S` is closed
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    rw [Set.mem_compl_iff] at hz
    have h := hS z
    simp only [nhdsWithin] at h
    obtain ⟨U, hU, T, hT, hUT⟩ := Filter.mem_inf_iff.mp h
    have hT' : ({z}ᶜ : Set ℂ) ⊆ T := Filter.mem_principal.mp hT
    refine Filter.mem_of_superset hU ?_
    intro u hu
    rw [Set.mem_compl_iff]
    by_cases huz : u = z
    · exact huz ▸ hz
    · have huT : u ∈ T := hT' (by simpa using huz)
      have hmem : u ∈ U ∩ T := ⟨hu, huT⟩
      rw [← hUT] at hmem
      exact hmem
  -- ## `φ⁻¹ '' L` is compact and disjoint from `S`
  have hLimg : IsCompact ((d.φ.symm : ℂ → ℂ) '' L) := hL.image d.φ.symm.continuous
  have hdisj_img : Disjoint ((d.φ.symm : ℂ → ℂ) '' L) S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    obtain ⟨w, hwL, hwx⟩ := hx
    refine (Set.disjoint_left.mp hLdisj) hwL ⟨x, hxS, ?_⟩
    rw [← hwx]
    exact d.φ.apply_symm_apply w
  have hLimg_sub : ((d.φ.symm : ℂ → ℂ) '' L) ⊆ Sᶜ := fun x hx =>
    (Set.mem_compl_iff S x).mpr fun hxS => (Set.disjoint_left.mp hdisj_img) hx hxS
  -- ## a compact thickening of `φ⁻¹ '' L` inside `Sᶜ`
  obtain ⟨δ, hδpos, hδsub⟩ :=
    hLimg.exists_cthickening_subset_open hSclosed.isOpen_compl hLimg_sub
  refine ⟨Metric.cthickening (δ / 2) ((d.φ.symm : ℂ → ℂ) '' L), hLimg.cthickening, ?_, ?_⟩
  · -- disjointness from `S`
    rw [Set.disjoint_left]
    intro x hxK hxS
    have hx' : x ∈ Metric.cthickening δ ((d.φ.symm : ℂ → ℂ) '' L) :=
      Metric.cthickening_mono (by linarith) _ hxK
    exact (Set.mem_compl_iff S x).mp (hδsub hx') hxS
  · -- eventual containment, from uniform convergence on the compact `L`
    have hUF : TendstoUniformlyOn (fun n => ((d.Fn n).symm : ℂ → ℂ))
        (d.φ.symm : ℂ → ℂ) atTop L :=
      (tendstoLocallyUniformly_iff_forall_isCompact.mp d.tendsto_symm_Fn) L hL
    have hev : ∀ᶠ n in atTop,
        ∀ x ∈ L, dist ((d.φ.symm : ℂ → ℂ) x) (((d.Fn n).symm : ℂ → ℂ) x) < δ / 2 :=
      (Metric.tendstoUniformlyOn_iff.mp hUF) (δ / 2) (by linarith)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun n hn w hwL => ?_⟩
    have hd := hN n hn w hwL
    rw [dist_comm] at hd
    refine Metric.cthickening_subset_of_subset (δ / 2) ?_
      (Metric.closedBall_subset_cthickening_singleton ((d.φ.symm : ℂ → ℂ) w) (δ / 2) ?_)
    · exact Set.singleton_subset_iff.mpr ⟨w, hwL, rfl⟩
    · rw [Metric.mem_closedBall]
      exact le_of_lt hd

end Work.MRMT.Found
