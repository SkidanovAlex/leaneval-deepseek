import Mathlib
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An `ℝ`-basis of `EuclideanSpace ℝ (Fin N × index F)` with `ℤ`-span `intLatE F N`

The lattice `intLatE F N` of `sieg2KernelDefs` is *defined* as the `ℤ`-span of the family
`g` of vectors indexed by `Fin N × 𝓞 F`-coordinates,

`g (n, i) = WithLp.toLp 2 (fun p => if p.1 = n then coords p.2 else 0)`,

`coords` being the mixed coordinates of the image of the `i`-th element of the integral basis
of `F`.  The content of `sieg2_intLatE_basis` is that this family is in fact the image of an
`ℝ`-basis of `EuclideanSpace ℝ (Fin N × index F)`: the product of the `N` copies of the single
`ℝ`-basis `intLatBasis F` of `EuclideanSpace ℝ (index F)` whose `i`-th vector is the mixed
coordinate vector of `meK (integralBasis F i)`.

Mathlib supplies the single-factor input: `mixedEmbedding.latticeBasis F` is an `ℝ`-basis of
the mixed space whose `i`-th vector is `mixedEmbedding F (integralBasis F i)`, and its `ℤ`-span
is the image of `𝓞 F` (`mixedEmbedding.span_latticeBasis`).  Transporting it through the
coordinate identification `stdBasis F` (an `ℝ`-linear isomorphism onto `ℝ^{index F}`) gives
`intLatBasis F`.  The product basis and the currying isomorphism between
`Fin N → EuclideanSpace ℝ (index F)` and `EuclideanSpace ℝ (Fin N × index F)` then assemble
the desired basis.
-/

open NumberField
open scoped Classical

namespace Work.BW

noncomputable section

/-- The `ℝ`-basis of `EuclideanSpace ℝ (index F)` whose `i`-th vector is the vector of mixed
coordinates of `meK (integralBasis F i)`.  It is the one-factor version of the lattice basis
underlying `intLatE`. -/
def intLatBasis (F : Type*) [Field F] [NumberField F] :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) ℝ
      (EuclideanSpace ℝ (NumberField.mixedEmbedding.index F)) :=
  (NumberField.mixedEmbedding.latticeBasis F).map
    ((NumberField.mixedEmbedding.stdBasis F).equivFun.trans
      (WithLp.linearEquiv 2 ℝ (NumberField.mixedEmbedding.index F → ℝ)).symm)

/-- The defining property of `intLatBasis`: its vectors are the mixed coordinates of the images
of the integral basis of `F`. -/
theorem intLatBasis_apply (F : Type*) [Field F] [NumberField F]
    (i : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) :
    intLatBasis F i = WithLp.toLp 2 (fun p => (NumberField.mixedEmbedding.stdBasis F).repr
      (NumberField.mixedEmbedding F (NumberField.integralBasis F i)) p) := by
  simp [intLatBasis, Module.Basis.map_apply, Module.Basis.equivFun_apply, LinearEquiv.trans_apply]

/-- The currying isomorphism between `Fin N → EuclideanSpace ℝ (index F)` and
`EuclideanSpace ℝ (Fin N × index F)`.  This is not an isometry in Mathlib's product norm
(which is the sup norm), but it is exactly the `ℝ`-linear identification used to put the
product basis on `EuclideanSpace ℝ (Fin N × index F)`. -/
def curryingE (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    (Fin N → EuclideanSpace ℝ (NumberField.mixedEmbedding.index F)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) where
  toFun f := WithLp.toLp 2 (fun p => WithLp.ofLp (f p.1) p.2)
  invFun g := fun n => WithLp.toLp 2 (fun i => WithLp.ofLp g (n, i))
  left_inv f := by
    funext n
    rw [WithLp.ext_iff]
  right_inv g := by
    rw [WithLp.ext_iff]
  map_add' f g := by
    rw [WithLp.ext_iff]
    funext p
    simp
  map_smul' c f := by
    rw [WithLp.ext_iff]
    funext p
    simp

@[simp] theorem curryingE_apply (F : Type*) [Field F] [NumberField F] (N : ℕ)
    (f : Fin N → EuclideanSpace ℝ (NumberField.mixedEmbedding.index F)) :
    curryingE F N f = WithLp.toLp 2 (fun p : Fin N × NumberField.mixedEmbedding.index F =>
      WithLp.ofLp (f p.1) p.2) := rfl

/-- The `ℝ`-basis of `EuclideanSpace ℝ (Fin N × index F)` whose `ℤ`-span is `intLatE F N`. -/
def intLatEBasis (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Module.Basis (Fin N × Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) ℝ
      (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :=
  ((Pi.basis (fun _ : Fin N => intLatBasis F)).reindex
    (Equiv.sigmaEquivProd (Fin N)
      (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)))).map (curryingE F N)

/-- The vectors of `intLatEBasis` are the generators of `intLatE`. -/
theorem intLatEBasis_apply (F : Type*) [Field F] [NumberField F] (N : ℕ)
    (q : Fin N × Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) :
    intLatEBasis F N q = WithLp.toLp 2 (fun p : Fin N × NumberField.mixedEmbedding.index F =>
      if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F (NumberField.integralBasis F q.2))) p.2 else 0) := by
  rw [WithLp.ext_iff]
  funext p
  simp only [intLatEBasis, Module.Basis.map_apply, Module.Basis.reindex_apply, Pi.basis_apply,
    intLatBasis_apply]
  split_ifs <;> simp_all

theorem sieg2_intLatE_basis {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    ∃ b : Module.Basis (Fin N × Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F)) ℝ
        (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)),
      Submodule.span ℤ (Set.range b) = intLatE F N := by
  refine ⟨intLatEBasis F N, ?_⟩
  have hb : ⇑(intLatEBasis F N) = (fun q : Fin N ×
      Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers F) =>
      WithLp.toLp 2 (fun p : Fin N × NumberField.mixedEmbedding.index F =>
        if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
          (NumberField.mixedEmbedding F (NumberField.integralBasis F q.2))) p.2 else 0)) :=
    funext (intLatEBasis_apply F N)
  rw [hb]
  rfl

end

end Work.BW
