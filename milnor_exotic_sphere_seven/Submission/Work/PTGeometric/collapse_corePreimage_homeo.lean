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
# The preimage of the core of a genuine collapse is the piece

For the genuine collapse data `G : GenuineTubeGeometry k D ι Fam` of a family of closed oriented
`8`-manifolds and a piece `i`, the preimage of the core `G.core` of the universal Thom space under
the Pontryagin–Thom collapse `(G.rep i).collapse` of the piece is homeomorphic to the piece
`(Fam i).pt`.

This is the geometric content of the two fields `G.isGeom` (the loop of `rep` is TUBULAR's concrete
collapse `alphaV`) and `G.zero` (TUBULAR's zero-set theorem: the concrete collapse lies in the core
exactly at the cube points mapping into the embedded piece): the preimage of the core is the
preimage of the embedded copy of the piece under the cube parametrisation `cubeToEuc`, which is the
piece itself (`K ≈ K × {0} ⊂ ℝ^{8+k}`) transported along the homeomorphism
`I^{8+k} ≃ [-R,R]^{8+k}` and the reindexing `Fin (k+8) ≃ Fin (8+k)` of `G.isGeom`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology

namespace Work.PTGeometric

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

theorem collapse_corePreimage_homeo {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (i : ι) :
    Nonempty (((G.rep i).collapse ⁻¹' G.core) ≃ₜ (Fam i).pt) := by
  classical
  -- the reindexing `Fin (k+8) ≃ Fin (8+k)` of the collapse (`G.isGeom`)
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
  -- the two cube models of the core preimage are homeomorphic by reindexing the coordinates
  have hreindex : Nonempty
      (({s : Fin (k + 8) → unitInterval | (G.rep i).collapse s ∈ G.core}) ≃ₜ
       ({t : Fin (8 + k) → unitInterval |
          Work.Tubular.cubeToEuc (8 + k) G.R t ∈ Set.range (G.emb i).e})) := by
    refine ⟨{ toFun := fun s => ⟨fun j => s.1 (e j), (hmem s.1).1 s.2⟩
              invFun := fun t => ⟨fun n => t.1 (e.symm n), (hmem _).2 (by simp only [Equiv.symm_apply_apply]; exact t.2)⟩
              left_inv := ?_
              right_inv := ?_
              continuous_toFun := ?_
              continuous_invFun := ?_ }⟩
    · intro s
      exact Subtype.ext (funext fun n => by simp)
    · intro t
      exact Subtype.ext (funext fun j => by simp)
    · apply Continuous.subtype_mk
      exact continuous_pi fun j => (continuous_apply (e j)).comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_pi fun n => (continuous_apply (e.symm n)).comp continuous_subtype_val
  obtain ⟨h1⟩ := hreindex
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
    have h2 : Nonempty (({t : Fin (8 + k) → unitInterval |
        Work.Tubular.cubeToEuc (8 + k) G.R t ∈ Set.range (G.emb i).e}) ≃ₜ
        Set.range (G.emb i).e) :=
      ⟨(isEmbedding_cubeToEuc (8 + k) hR).homeomorphOfSubsetRange hsub⟩
    have h3 : Nonempty (Set.range (G.emb i).e ≃ₜ (Fam i).pt) :=
      ⟨(Topology.IsClosedEmbedding.toIsEmbedding (G.emb i).closedEmbedding).toHomeomorph.symm⟩
    obtain ⟨h2⟩ := h2
    obtain ⟨h3⟩ := h3
    exact ⟨h1.trans (h2.trans h3)⟩
  · -- the piece is empty: the core preimage is empty too (by `hmem`), so both sides are empty
    haveI : IsEmpty (Fam i).pt := not_nonempty_iff.mp hne
    haveI : IsEmpty (Set.range (G.emb i).e) :=
      ⟨fun y => by obtain ⟨x, -⟩ := y.2; exact isEmptyElim x⟩
    haveI : IsEmpty (↥((G.rep i).collapse ⁻¹' G.core)) :=
      ⟨fun s => isEmptyElim (⟨_, (hmem s.1).1 s.2⟩ : Set.range (G.emb i).e)⟩
    exact ⟨{ toFun := fun x => isEmptyElim x, invFun := fun y => isEmptyElim y,
             left_inv := fun x => isEmptyElim x, right_inv := fun y => isEmptyElim y,
             continuous_toFun := continuous_of_discreteTopology,
             continuous_invFun := continuous_of_discreteTopology }⟩

end Work.PTGeometric
