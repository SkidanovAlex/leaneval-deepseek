import Mathlib
import Submission.Work.BW.siegel_defs
import Submission.Work.BW.kcb_defs
import Submission.Work.BW.coordVecLin_defs
import Submission.Work.BW.coordVec_kerVecs_of_mem_kerLattice
import Submission.Work.BW.kerLattice_zbasis_card
import Submission.Work.BW.card_basis_comap_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A `ℤ`-basis of the kernel lattice `Work.BW.kerLattice`

`Work.BW.kerLattice F a` is the `ℤ`-span, inside the mixed coordinate space
`Fin N → (NumberField.mixedEmbedding.index F → ℝ)`, of the coordinate vectors `coordVec x` of the
integral kernel vectors `x ∈ (𝓞 F)^N` of an `M × N` matrix `a` with `F`-linearly independent rows
(`M < N`).  This file exhibits a `ℤ`-basis of it of cardinality `[F : ℚ] * (N - M)`.

The proof is the standard one for such a kernel lattice.  The pullback

`L = (kerLattice a).comap coordVecLin`

along the coordinate map `coordVecLin : (𝓞 F)^N →ₗ[ℤ] CoordSpace F N` (which is, as a set, exactly
`Work.BW.kerVecs a`, the set of integral kernel vectors of `a`) is a `ℤ`-submodule of the free
`ℤ`-module `(𝓞 F)^N`, so by `Submodule.basisOfPid` it has a `ℤ`-basis `b` indexed by `Fin k`; since
`coordVecLin` is injective and maps `L` *onto* `kerLattice a`, the family `i ↦ coordVecLin (b i)` is
`ℤ`-independent and spans `kerLattice a`.  The cardinality `k` is pinned down by two inequalities:

* `k ≤ [F:ℚ]·(N-M)` (`Work.BW.card_basis_comap_le`): the integral kernel vectors, coerced to `F`,
  are `ℚ`-independent elements of the kernel of the matrix `a`, which has `ℚ`-dimension
  `[F:ℚ]·(N-M)`;
* `[F:ℚ]·(N-M) ≤ k` (`Work.BW.kerLattice_zbasis_card`).

The basis is then reindexed along `Fin k ≃ Fin ([F:ℚ]·(N-M))`.
-/

namespace Work.BW.TV

open NumberField

/-- Transport along `coordVecLin`: any `ℤ`-basis `B` of the pullback
`(Work.BW.kerLattice a).comap Work.BW.coordVecLin` of the kernel lattice maps to a `ℤ`-independent
family spanning the kernel lattice itself.  Indeed `coordVecLin` is injective and carries the
pullback *onto* the kernel lattice (`Work.BW.coordVecLin_ker`,
`Work.BW.map_comap_coordVecLin`). -/
theorem coordVecLin_basis_comap {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) {k : ℕ}
    (B : Module.Basis (Fin k) ℤ ↥((Work.BW.kerLattice (F := F) a).comap
      (Work.BW.coordVecLin (F := F)))) :
    LinearIndependent ℤ
        (fun i => Work.BW.coordVecLin (F := F)
          (((B i : ↥((Work.BW.kerLattice (F := F) a).comap (Work.BW.coordVecLin (F := F)))) :
            Fin N → NumberField.RingOfIntegers F))) ∧
      Submodule.span ℤ
        (Set.range (fun i => Work.BW.coordVecLin (F := F)
          (((B i : ↥((Work.BW.kerLattice (F := F) a).comap (Work.BW.coordVecLin (F := F)))) :
            Fin N → NumberField.RingOfIntegers F))))
        = Work.BW.kerLattice (F := F) a := by
  classical
  let L : Submodule ℤ (Fin N → NumberField.RingOfIntegers F) :=
    (Work.BW.kerLattice (F := F) a).comap (Work.BW.coordVecLin (F := F))
  constructor
  · exact ((B.linearIndependent).map' (Submodule.subtype L) (Submodule.ker_subtype L)).map'
      (Work.BW.coordVecLin (F := F)) (Work.BW.coordVecLin_ker (F := F))
  · have hspan_coe : Submodule.span ℤ
        (Set.range (fun i : Fin k => ((B i : ↥L) : Fin N → NumberField.RingOfIntegers F)))
        = L :=
      Work.BW.span_range_coe_basis (R := ℤ) (M := Fin N → NumberField.RingOfIntegers F) L B
    have h := Submodule.map_span (Work.BW.coordVecLin (F := F))
      (Set.range (fun i : Fin k => ((B i : ↥L) : Fin N → NumberField.RingOfIntegers F)))
    rw [hspan_coe, Work.BW.map_comap_coordVecLin (F := F) a] at h
    rw [← Set.range_comp] at h
    exact h.symm

theorem kerLattice_zbasis {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hind : LinearIndependent F a) :
    ∃ v : Fin (Module.finrank ℚ F * (N - M)) →
        (Fin N → (NumberField.mixedEmbedding.index F → ℝ)),
      LinearIndependent ℤ v ∧ Submodule.span ℤ (Set.range v) = Work.BW.kerLattice (F := F) a := by
  classical
  -- The unmixed model of the kernel lattice: the pullback of `kerLattice a` along `coordVecLin`.
  let L : Submodule ℤ (Fin N → NumberField.RingOfIntegers F) :=
    (Work.BW.kerLattice (F := F) a).comap (Work.BW.coordVecLin (F := F))
  -- A `ℤ`-basis of `L`, indexed by `Fin k`.
  obtain ⟨k, bL⟩ := Submodule.basisOfPid
    (Module.Free.chooseBasis ℤ (Fin N → NumberField.RingOfIntegers F)) L
  obtain ⟨hli, hspan⟩ := coordVecLin_basis_comap (F := F) a bL
  -- The two bounds on `k`.
  have hge : Module.finrank ℚ F * (N - M) ≤ k :=
    Work.BW.kerLattice_zbasis_card (F := F) hMN a hind
      (fun i => Work.BW.coordVecLin (F := F)
        (((bL i : ↥L) : Fin N → NumberField.RingOfIntegers F))) hli hspan
  have hle : k ≤ Module.finrank ℚ F * (N - M) := Work.BW.card_basis_comap_le (F := F) a hind bL
  have hk : k = Module.finrank ℚ F * (N - M) := le_antisymm hle hge
  -- Reindex the basis of `L` along `Fin k ≃ Fin ([F:ℚ]·(N-M))`.
  let b' : Module.Basis (Fin (Module.finrank ℚ F * (N - M))) ℤ ↥L := bL.reindex (finCongr hk)
  obtain ⟨hli', hspan'⟩ := coordVecLin_basis_comap (F := F) a b'
  exact ⟨fun i => Work.BW.coordVecLin (F := F)
    (((b' i : ↥L) : Fin N → NumberField.RingOfIntegers F)), hli', hspan'⟩

end Work.BW.TV
