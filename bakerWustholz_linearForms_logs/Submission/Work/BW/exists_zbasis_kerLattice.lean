import Mathlib
import Submission.Work.BW.kcb_defs
import Submission.Work.BW.coordVecLin_defs
import Submission.Work.BW.kerLattice_zbasis_card
import Submission.Work.BW.coordVec_kerVecs_of_mem_kerLattice
import Submission.Work.BW.finrank_ker_mulVecLin_fin
import Submission.Work.BW.exists_int_mul_mem_ringOfIntegers
import Submission.Work.BW.card_basis_comap_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Module NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- The kernel lattice `kerLattice a` of an `F`-linearly independent system of `M < N` forms over a
number field `F` has a `ℤ`-basis of cardinality `[F:ℚ]·(N-M)`.

Concretely: there is a `ℤ`-linearly independent family `v` of `[F:ℚ]·(N-M)` vectors of the mixed
coordinate space `CoordSpace F N = ℝ^{[F:ℚ]·N}` whose `ℤ`-span is exactly `kerLattice a`.

Route.  Pull back along `coordVecLin : (Fin N → 𝓞 F) →ₗ[ℤ] CoordSpace F N` (the `ℤ`-linear map
`x ↦ coordVec x`, built from `Work.BW.coordVec_add` and `Work.BW.coordVec_zsmul`): the pullback
`Lp = (kerLattice a).comap coordVecLin` is, as a set, the set of integral kernel vectors
(`Work.BW.mem_kerLattice_iff`, `Work.BW.coordVec_kerVecs_of_mem_kerLattice` for the surjectivity of
`coordVecLin` onto `kerLattice a`).  `Lp` is a submodule of the free `ℤ`-module
`Fin N → 𝓞 F`, so `Submodule.basisOfPid` gives a `ℤ`-basis `b : Basis (Fin k) ℤ ↥Lp` (use
`NumberField.RingOfIntegers.basis F` and `Basis.pi`, or transfer along
`(Fin N → 𝓞 F) ≃ₗ[ℤ] (Fin N × ι → ℤ)` and use `Pi.basisFun`).  Then
`v i := coordVecLin (b i)` is `ℤ`-independent (injectivity of `coordVecLin`) and spans
`coordVecLin '' Lp = kerLattice a`.  Finally `k = [F:ℚ]·(N-M)`:
`k ≤ [F:ℚ]·(N-M)` because the elements `(b i : Fin N → 𝓞 F)` are `ℤ`-independent, hence
`ℚ`-independent, inside the `ℚ`-vector space `Fin N → F`, where they lie in the kernel `K` of the
matrix `a`, of `ℚ`-dimension `[F:ℚ]·(N-M)` (`Work.BW.finrank_ker_mulVecLin_fin` with
`Module.finrank_mul_finrank`); and `[F:ℚ]·(N-M) ≤ k` is
`Work.BW.kerLattice_zbasis_card hMN a hind hv hspan`. -/
theorem exists_zbasis_kerLattice {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hind : LinearIndependent F a) :
    ∃ v : Fin (Module.finrank ℚ F * (N - M)) → Work.BW.CoordSpace F N,
      LinearIndependent ℤ v ∧
      Submodule.span ℤ (Set.range v) = Work.BW.kerLattice (F := F) a := by
  classical
  -- The unmixed model of the kernel lattice: the pullback of `kerLattice a` along `coordVecLin`.
  let Lp : Submodule ℤ (Fin N → RingOfIntegers F) :=
    (kerLattice (F := F) a).comap (coordVecLin (F := F))
  -- A `ℤ`-basis of that pullback, indexed by `Fin k`.
  obtain ⟨k, bLp⟩ :=
    Submodule.basisOfPid (Module.Free.chooseBasis ℤ (Fin N → RingOfIntegers F)) Lp
  -- For any basis `B` of `Lp`, the family `i ↦ coordVecLin (B i)` is `ℤ`-independent and spans
  -- the kernel lattice.
  have key : ∀ {k : ℕ} (B : Basis (Fin k) ℤ ↥Lp),
      LinearIndependent ℤ
        (fun i => coordVecLin (F := F) (((B i : ↥Lp) : Fin N → RingOfIntegers F))) ∧
      Submodule.span ℤ
        (Set.range (fun i => coordVecLin (F := F) (((B i : ↥Lp) : Fin N → RingOfIntegers F))))
        = kerLattice (F := F) a := by
    intro k B
    constructor
    · exact ((B.linearIndependent).map' (Submodule.subtype Lp) (Submodule.ker_subtype Lp)).map'
        (coordVecLin (F := F)) (coordVecLin_ker (F := F))
    · have hspan_coe : Submodule.span ℤ
          (Set.range (fun i : Fin k => ((B i : ↥Lp) : Fin N → RingOfIntegers F))) = Lp :=
        span_range_coe_basis (R := ℤ) (M := Fin N → RingOfIntegers F) Lp B
      have h := Submodule.map_span (coordVecLin (F := F))
        (Set.range (fun i : Fin k => ((B i : ↥Lp) : Fin N → RingOfIntegers F)))
      rw [hspan_coe, map_comap_coordVecLin (F := F) a] at h
      rw [← Set.range_comp] at h
      exact h.symm
  obtain ⟨hli_k, hspan_k⟩ := key bLp
  -- The two bounds on `k`.
  have hk_ge : Module.finrank ℚ F * (N - M) ≤ k :=
    kerLattice_zbasis_card hMN a hind
      (fun i => coordVecLin (F := F) (((bLp i : ↥Lp) : Fin N → RingOfIntegers F))) hli_k hspan_k
  have hk_le : k ≤ Module.finrank ℚ F * (N - M) := card_basis_comap_le a hind bLp
  have hk : k = Module.finrank ℚ F * (N - M) := le_antisymm hk_le hk_ge
  -- Reindex the basis of `Lp` by `Fin ([F:ℚ]·(N-M))`.
  let e : Fin k ≃ Fin (Module.finrank ℚ F * (N - M)) := finCongr hk
  let b' : Basis (Fin (Module.finrank ℚ F * (N - M))) ℤ ↥Lp := bLp.reindex e
  obtain ⟨hli', hspan'⟩ := key b'
  exact ⟨fun i => coordVecLin (F := F) (((b' i : ↥Lp) : Fin N → RingOfIntegers F)), hli', hspan'⟩

end Work.BW
