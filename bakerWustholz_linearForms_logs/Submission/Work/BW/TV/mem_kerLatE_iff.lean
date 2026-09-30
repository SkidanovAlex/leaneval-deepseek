import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.kcb_defs
import Submission.Work.BW.TV.kerLatE_coord_aux
import Submission.Work.BW.TV.mem_intLatE_iff_latL

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BW.TV.mem_kerLatE_iff`

The kernel lattice `Work.BW.kerLatE a` of `Work.BW.sieg2KernelDefs` is the intersection of the
integral lattice `Work.BW.intLatE F N` with the kernel of the matrix model `Work.BW.PhiE a` of the
rows `a`, inside the Euclidean coordinate space `EuclideanSpace ℝ (Fin N × index F)`.  The kernel
lattice `Work.BW.kerLattice a` of `Work.BW.siegel_defs` is the `ℤ`-span of the mixed coordinate
vectors of the integral kernel vectors of `a`.

The two are the same lattice under the identification of `EuclideanSpace ℝ (Fin N × index F)` with
`Work.BW.CoordSpace F N` given by `WithLp.ofLp`:

* the integral lattices agree (`Work.BW.TV.mem_intLatE_iff_latL`), and
* the two models `PhiE a` and `phiMap a` of the same `ℝ`-linear map agree
  (`Work.BW.TV.zz_PhiE_ofLp_eq_phiMap`), so that the kernels agree.

Together with `Work.BW.mem_kerLattice_iff`, this gives the claimed equivalence.
-/

namespace Work.BW.TV

theorem mem_kerLatE_iff {F : Type*} [Field F] [NumberField F] {M N : ℕ} (a : Fin M → Fin N → F)
    (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :
    x ∈ Work.BW.kerLatE a ↔
      (fun (j : Fin N) (q : NumberField.mixedEmbedding.index F) => WithLp.ofLp x (j, q))
        ∈ Work.BW.kerLattice (F := F) a := by
  have hlat := mem_intLatE_iff_latL (F := F) x
  have hmap := zz_PhiE_ofLp_eq_phiMap (F := F) a x
  rw [Work.BW.kerLatE, Submodule.mem_inf]
  change x ∈ Work.BW.intLatE F N ∧ (Work.BW.PhiE a) x = 0 ↔
    (fun (j : Fin N) (q : NumberField.mixedEmbedding.index F) => WithLp.ofLp x (j, q))
      ∈ Work.BW.kerLattice (F := F) a
  rw [Work.BW.mem_kerLattice_iff]
  constructor
  · rintro ⟨hxA, hx0⟩
    refine ⟨hlat.mp hxA, ?_⟩
    have hz : (fun (i : Fin M) (c : NumberField.mixedEmbedding.index F) =>
        WithLp.ofLp (Work.BW.PhiE a x) (i, c)) = 0 := by
      ext i c
      simp [hx0]
    rw [hmap] at hz
    exact hz
  · rintro ⟨hxB, hker⟩
    refine ⟨hlat.mpr hxB, ?_⟩
    have hof : WithLp.ofLp (Work.BW.PhiE a x)
        = (0 : Fin M × NumberField.mixedEmbedding.index F → ℝ) := by
      funext p
      obtain ⟨i, c⟩ := p
      have h := congrFun (congrFun hmap i) c
      rw [h, hker]
      simp
    refine WithLp.ofLp_injective 2 ?_
    rw [hof, WithLp.ofLp_zero]

end Work.BW.TV
