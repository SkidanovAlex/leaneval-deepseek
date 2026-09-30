import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.kcb_defs
import Submission.Work.BW.coordVecLin_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `x ∈ intLatE F N` iff its mixed coordinates lie in `latL F N`

The lattice `Work.BW.intLatE F N` is the `ℤ`-span, inside the Euclidean coordinate space
`EuclideanSpace ℝ (Fin N × index F)`, of the vectors

`q ↦ WithLp.toLp 2 (p ↦ if p.1 = q.1 then coord (meK (integralBasis F q.2)) p.2 else 0)`

(`q : Fin N × 𝓞 F`-coordinates), while `Work.BW.latL F N` is the `ℤ`-span, inside
`CoordSpace F N = (Fin N → index F → ℝ)`, of the mixed coordinate vectors `coordVec x` of the
integral vectors `x ∈ (𝓞 F)^N`.

Both are the coordinate model of the same lattice `(𝓞 F)^N`, so `x ∈ intLatE F N` exactly when
its mixed coordinates lie in `latL F N`.

The proof passes through the `ℤ`-linear uncurrying map `ofLpMap` and shows that it carries
`intLatE F N` *onto* `latL F N` and is injective: `intLatE F N` is the `ℤ`-span of the images
`intLatEGen F N q`, whose `ofLpMap`-images are the `coordVec`-coordinates of the standard integral
basis vectors `ibVec F N q` of `(𝓞 F)^N` (which span everything), while
`latL F N = coordVecLin '' ⊤`.
-/

namespace Work.BW.TV

open NumberField

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The generator family defining `Work.BW.intLatE F N`, given a name. -/
def intLatEGen (F : Type*) [Field F] [NumberField F] (N : ℕ)
    (q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) :=
  WithLp.toLp 2 (fun p : Fin N × NumberField.mixedEmbedding.index F =>
    if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
      (NumberField.mixedEmbedding F (NumberField.integralBasis F q.2))) p.2
    else 0)

lemma intLatE_eq_span_intLatEGen (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Work.BW.intLatE F N = Submodule.span ℤ (Set.range (intLatEGen F N)) := rfl

/-- The standard integral basis vector of `(𝓞 F)^N`: the `i`-th element of the integral basis in
the `n`-th coordinate and `0` elsewhere. -/
def ibVec (F : Type*) [Field F] [NumberField F] (N : ℕ)
    (q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) : Fin N → 𝓞 F :=
  Pi.single q.1 (NumberField.RingOfIntegers.basis F q.2)

/-- Uncurrying the coordinates of `EuclideanSpace ℝ (Fin N × index F)`, as a `ℤ`-linear map. -/
def ofLpMap (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℤ] CoordSpace F N where
  toFun x := fun j q => WithLp.ofLp x (j, q)
  map_add' x y := by funext j q; simp
  map_smul' n x := by funext j q; simp

/-- The inverse of `ofLpMap`: assemble coordinates into a point of the Euclidean coordinate
space. -/
def toEMap (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    CoordSpace F N →ₗ[ℤ] EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) where
  toFun y := WithLp.toLp 2 (fun p => y p.1 p.2)
  map_add' y z := by rw [WithLp.ext_iff]; funext p; simp
  map_smul' n y := by rw [WithLp.ext_iff]; funext p; simp

lemma toEMap_ofLpMap (F : Type*) [Field F] [NumberField F] (N : ℕ)
    (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :
    toEMap F N (ofLpMap F N x) = x := by
  rw [WithLp.ext_iff]; funext p; simp [toEMap, ofLpMap]

lemma ofLpMap_toEMap (F : Type*) [Field F] [NumberField F] (N : ℕ) (y : CoordSpace F N) :
    ofLpMap F N (toEMap F N y) = y := by
  funext j q; simp [toEMap, ofLpMap]

lemma ofLpMap_injective (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Function.Injective (ofLpMap F N) := by
  intro x y h
  have h' := congrArg (toEMap F N) h
  rwa [toEMap_ofLpMap, toEMap_ofLpMap] at h'

/-- The `ofLpMap`-image of the generator `intLatEGen F N q` is the coordinate vector of the
corresponding standard integral basis vector. -/
lemma ofLpMap_intLatEGen (F : Type*) [Field F] [NumberField F] (N : ℕ)
    (q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    ofLpMap F N (intLatEGen F N q) = Work.BW.coordVec (ibVec F N q) := by
  funext j c
  simp only [ofLpMap, intLatEGen, ibVec, Work.BW.coordVec, Work.BW.coord, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.single_apply]
  by_cases h : j = q.1
  · simp [h, NumberField.integralBasis_apply]
  · simp [h]

/-- The standard integral basis vectors of `(𝓞 F)^N` span everything over `ℤ`. -/
lemma span_ibVec (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Submodule.span ℤ (Set.range (ibVec F N)) = ⊤ := by
  let B : Module.Basis (Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℤ
      (Fin N → 𝓞 F) := (Pi.basis (fun _ : Fin N => NumberField.RingOfIntegers.basis F)).reindex
        (Equiv.sigmaEquivProd (Fin N) (Module.Free.ChooseBasisIndex ℤ (𝓞 F)))
  have hB : ∀ q, B q = Pi.single q.1 (NumberField.RingOfIntegers.basis F q.2) := by
    intro q
    rw [show B q = (Pi.basis (fun _ : Fin N => NumberField.RingOfIntegers.basis F))
          ((Equiv.sigmaEquivProd (Fin N) (Module.Free.ChooseBasisIndex ℤ (𝓞 F))).symm q) from
        Module.Basis.reindex_apply _ _ _]
    rw [Equiv.sigmaEquivProd_symm_apply]
    exact Pi.basis_apply _ _
  have hcoe : ⇑B = ibVec F N := funext (fun q => by rw [hB q]; rfl)
  rw [← hcoe]
  exact B.span_eq

/-- The coordinate map carries all of `(𝓞 F)^N` onto `latL F N`. -/
lemma map_coordVecLin_top (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Submodule.map (Work.BW.coordVecLin (F := F) (N := N)) ⊤ = Work.BW.latL F N := by
  apply SetLike.ext'
  rw [Submodule.map_top, LinearMap.coe_range]
  exact (show (Work.BW.latL F N : Set (CoordSpace F N)) =
    Set.range (Work.BW.coordVec (F := F) (N := N)) from Work.BW.latL_eq_range).symm

/-- The uncurrying map carries `intLatE F N` onto `latL F N`. -/
lemma map_ofLpMap_intLatE (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Submodule.map (ofLpMap F N) (Work.BW.intLatE F N) = Work.BW.latL F N := by
  rw [intLatE_eq_span_intLatEGen, Submodule.map_span]
  have h1 : ⇑(ofLpMap F N) '' Set.range (intLatEGen F N)
      = Set.range (Work.BW.coordVecLin (F := F) (N := N) ∘ ibVec F N) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext q
    exact ofLpMap_intLatEGen F N q
  rw [h1, Set.range_comp]
  rw [← Submodule.map_span (Work.BW.coordVecLin (F := F) (N := N)) (Set.range (ibVec F N))]
  rw [span_ibVec F N]
  exact map_coordVecLin_top F N

theorem mem_intLatE_iff_latL {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :
    x ∈ Work.BW.intLatE F N ↔
      (fun (j : Fin N) (q : NumberField.mixedEmbedding.index F) => WithLp.ofLp x (j, q))
        ∈ Work.BW.latL F N := by
  show x ∈ Work.BW.intLatE F N ↔ ofLpMap F N x ∈ Work.BW.latL F N
  rw [← map_ofLpMap_intLatE F N]
  constructor
  · exact fun hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rw [← ofLpMap_injective F N hyx]
    exact hy

end

end Work.BW.TV
