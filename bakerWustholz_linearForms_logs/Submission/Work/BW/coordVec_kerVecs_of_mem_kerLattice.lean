import Mathlib
import Submission.Work.BW.siegel_defs
import Submission.Work.BW.kcb_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `coordVec_kerVecs_of_mem_kerLattice`

Every element of the kernel lattice `Work.BW.kerLattice a` -- the `ℤ`-span of the coordinate
vectors `coordVec x` of the integral kernel vectors `x ∈ (𝓞 F)^N` of `a` -- is itself the
coordinate vector of an integral kernel vector.

The point is that `coordVec` is additive and `ℤ`-equivariant while `kerVecs a` is closed under
addition and `ℤ`-scalar multiplication, so `coordVec '' kerVecs a` is already a `ℤ`-submodule of
the coordinate space `CoordSpace F N`.  Consequently it equals its own `ℤ`-span, i.e. it equals
the kernel lattice `kerLattice a`.
-/

namespace Work.BW

open NumberField

theorem coordVec_kerVecs_of_mem_kerLattice {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) {y : Fin N → (NumberField.mixedEmbedding.index F → ℝ)}
    (hy : y ∈ Work.BW.kerLattice (F := F) a) :
    ∃ x : Fin N → NumberField.RingOfIntegers F,
      (∀ i, ∑ j, a i j * ((x j : NumberField.RingOfIntegers F) : F) = 0) ∧
      y = Work.BW.coordVec (F := F) x := by
  -- `coordVec '' kerVecs a` is a `ℤ`-submodule of the coordinate space.
  let S : Submodule ℤ (Fin N → (NumberField.mixedEmbedding.index F → ℝ)) :=
    { carrier := coordVec (F := F) '' kerVecs (F := F) a
      zero_mem' :=
        ⟨0, by intro i; simp, coordVec_zero (F := F)⟩
      add_mem' := by
        intro u v hu hv
        obtain ⟨x, hx, rfl⟩ := hu
        obtain ⟨x', hx', rfl⟩ := hv
        exact ⟨x + x', by
          intro i
          have h : ∀ j, a i j * (((x + x') j : RingOfIntegers F) : F)
              = a i j * ((x j : RingOfIntegers F) : F)
                + a i j * ((x' j : RingOfIntegers F) : F) := by
            intro j
            simp only [Pi.add_apply]
            push_cast
            rw [mul_add]
          rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib, hx i, hx' i,
            add_zero],
          coordVec_add (F := F) x x'⟩
      smul_mem' := by
        intro c u hu
        obtain ⟨x, hx, rfl⟩ := hu
        exact ⟨c • x, by
          intro i
          have h : ∀ j, a i j * (((c • x) j : RingOfIntegers F) : F)
              = (c : F) * (a i j * ((x j : RingOfIntegers F) : F)) := by
            intro j
            simp only [Pi.smul_apply]
            push_cast
            ring
          rw [Finset.sum_congr rfl (fun j _ => h j), ← Finset.mul_sum, hx i, mul_zero],
          coordVec_zsmul (F := F) c x⟩ }
  -- Being a submodule, the image equals its own `ℤ`-span, i.e. the kernel lattice.
  have hspan : Submodule.span ℤ (coordVec (F := F) '' kerVecs (F := F) a) = S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro z hz
      exact Submodule.subset_span hz
  rw [kerLattice, hspan] at hy
  have hyimg : y ∈ coordVec (F := F) '' kerVecs (F := F) a := hy
  obtain ⟨x, hx, hxy⟩ := hyimg
  exact ⟨x, hx, hxy.symm⟩

end Work.BW
