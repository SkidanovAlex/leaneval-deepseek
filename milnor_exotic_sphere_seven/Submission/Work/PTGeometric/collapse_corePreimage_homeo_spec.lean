import Mathlib
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.isEmbedding_cubeToEuc
import Submission.Work.PTGeometric.mem_range_cubeToEuc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The explicit homeomorphism of the core preimage with the piece

`Work.PTGeometric.collapse_corePreimage_homeo` proves only that the preimage of the core of the
universal Thom space under the Pontryagin–Thom collapse of a piece is *homeomorphic* to the piece.
The last mile needs the homeomorphism itself, in coordinates: the point of `ℝ^{8+k}` that the
collapse reads off is the cube parametrisation `cubeToEuc (8+k) R` applied to the (reindexed)
coordinates of the cube point.

This file proves that specification, by redoing the construction of
`collapse_corePreimage_homeo` while keeping the maps explicit:

* the reindexing `Fin (8+k) ≃ Fin (k+8)` of `G.isGeom`;
* `hmem` — TUBULAR's zero-set theorem `G.zero`, which identifies the core preimage with the
  preimage of the embedded piece under `cubeToEuc R`;
* the explicit reindexing homeomorphism `h1 : {s | collapse s ∈ core} ≃ₜ {t | cubeToEuc R t ∈ range}`,
  `h1 s = fun j => s (e j)`;
* `h2 : {t | cubeToEuc R t ∈ range} ≃ₜ range`, the embedding homeomorphism of `cubeToEuc R`
  (whose coercion is `cubeToEuc R x`, `homeomorphOfSubsetRange_apply_coe`);
* `h3 : range ≃ₜ (Fam i).pt`, the inverse of the closed embedding `G.emb i`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology

namespace Work.PTGeometric

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

theorem collapse_corePreimage_homeo_spec {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (i : ι) :
    ∃ h : ↥((G.rep i).collapse ⁻¹' G.core) ≃ₜ (Fam i).pt,
      ∀ s : ↥((G.rep i).collapse ⁻¹' G.core),
        (G.emb i).e (h s) = Work.Tubular.cubeToEuc (8 + k) G.R
          (fun j => s.1 ((finCongr (Nat.add_comm k 8)).symm j)) := by
  classical
  -- the reindexing `Fin (8+k) ≃ Fin (k+8)` of `G.isGeom`
  let e : Fin (8 + k) ≃ Fin (k + 8) := (finCongr (Nat.add_comm k 8)).symm
  have he2 : ∀ j : Fin (k + 8), e (finKR k j) = j := fun j => by simp [e, finKR]
  -- the core preimage, reindexed, is the preimage of the embedded piece under `cubeToEuc R`
  have hmem : ∀ s : Fin (k + 8) → unitInterval,
      ((G.rep i).collapse s ∈ G.core) ↔
        (Work.Tubular.cubeToEuc (8 + k) G.R (fun j => s (e j)) ∈ Set.range (G.emb i).e) := by
    intro s
    have hgeom : (G.rep i).collapse s =
        Work.Tubular.alphaV (G.chart i) G.hR (G.hbox i) D.t₀ (G.J i) (G.hJ i) (G.g i) (G.hg i)
          (fun j => s (e j)) := by
      simpa only [he2] using G.isGeom i (fun j => s (e j))
    rw [hgeom]
    exact G.zero i (fun j => s (e j))
  by_cases hne : Nonempty (Fam i).pt
  · -- a nonempty piece: the box radius `R` is positive, and `cubeToEuc R` is an embedding
    obtain ⟨x₀⟩ := hne
    have hR : 0 < G.R := by
      have h := G.hbox i ((G.emb i).e x₀) ((G.chart i).zero_mem_U x₀) ⟨0, by omega⟩
      have h0 : (0 : ℝ) ≤ |((G.emb i).e x₀).ofLp ⟨0, by omega⟩| := abs_nonneg _
      linarith
    have hsub : Set.range (G.emb i).e ⊆ Set.range (⇑(Work.Tubular.cubeToEuc (8 + k) G.R)) := by
      rintro y ⟨x, rfl⟩
      exact (mem_range_cubeToEuc (N := 8 + k) (R := G.R) G.hR _).mpr
        (fun j => le_of_lt (G.hbox i _ ((G.chart i).zero_mem_U x) j))
    -- (1) the reindexing homeomorphism of the cube coordinates
    let h1 : (({s : Fin (k + 8) → unitInterval | (G.rep i).collapse s ∈ G.core}) ≃ₜ
        ({t : Fin (8 + k) → unitInterval |
          Work.Tubular.cubeToEuc (8 + k) G.R t ∈ Set.range (G.emb i).e})) :=
      { toFun := fun s => ⟨fun j => s.1 (e j), (hmem s.1).1 s.2⟩
        invFun := fun t => ⟨fun n => t.1 (e.symm n), (hmem _).2 (by simp only [Equiv.symm_apply_apply]; exact t.2)⟩
        left_inv := fun s => Subtype.ext (funext fun n => by simp)
        right_inv := fun t => Subtype.ext (funext fun j => by simp)
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact continuous_pi fun j => (continuous_apply (e j)).comp continuous_subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          exact continuous_pi fun n => (continuous_apply (e.symm n)).comp continuous_subtype_val }
    -- (2) `cubeToEuc R` is an embedding, so its preimage-of-range is its range
    let h2 : (({t : Fin (8 + k) → unitInterval |
        Work.Tubular.cubeToEuc (8 + k) G.R t ∈ Set.range (G.emb i).e}) ≃ₜ
        Set.range (G.emb i).e) :=
      (isEmbedding_cubeToEuc (8 + k) hR).homeomorphOfSubsetRange hsub
    -- (3) the closed embedding of the piece
    let embH : (Fam i).pt ≃ₜ Set.range (G.emb i).e :=
      (Topology.IsClosedEmbedding.toIsEmbedding (G.emb i).closedEmbedding).toHomeomorph
    refine ⟨h1.trans (h2.trans embH.symm), ?_⟩
    intro s
    -- the value of the homeomorphism in coordinates
    have hval : ((h2 (h1 s) : Set.range (G.emb i).e) : Euc (8 + k)) =
        Work.Tubular.cubeToEuc (8 + k) G.R ((h1 s) : Fin (8 + k) → unitInterval) := rfl
    have embH_val : ∀ x : (Fam i).pt,
        ((embH x : Set.range (G.emb i).e) : Euc (8 + k)) = (G.emb i).e x := fun x => rfl
    have hsym : (G.emb i).e (embH.symm (h2 (h1 s))) =
        ((h2 (h1 s) : Set.range (G.emb i).e) : Euc (8 + k)) := by
      have h4 := congrArg (Subtype.val) (Homeomorph.apply_symm_apply embH (h2 (h1 s)))
      rw [embH_val (embH.symm (h2 (h1 s)))] at h4
      exact h4
    have hco : ((h1 s) : Fin (8 + k) → unitInterval) = fun j => s.1 (e j) := rfl
    erw [Homeomorph.trans_apply, Homeomorph.trans_apply, hsym, hval, hco]
  · -- the piece is empty: the core preimage is empty too (by `hmem`), so both sides are empty
    haveI : IsEmpty (Fam i).pt := not_nonempty_iff.mp hne
    haveI : IsEmpty (Set.range (G.emb i).e) :=
      ⟨fun y => by obtain ⟨x, -⟩ := y.2; exact isEmptyElim x⟩
    haveI : IsEmpty (↥((G.rep i).collapse ⁻¹' G.core)) :=
      ⟨fun s => isEmptyElim (⟨_, (hmem s.1).1 s.2⟩ : Set.range (G.emb i).e)⟩
    exact ⟨{ toFun := fun x => isEmptyElim x, invFun := fun y => isEmptyElim y,
             left_inv := fun x => isEmptyElim x, right_inv := fun y => isEmptyElim y,
             continuous_toFun := continuous_of_discreteTopology,
             continuous_invFun := continuous_of_discreteTopology },
           fun s => isEmptyElim s⟩

end Work.PTGeometric
