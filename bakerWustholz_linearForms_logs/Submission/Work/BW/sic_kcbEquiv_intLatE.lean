import Mathlib
import Submission.Work.BW.kcb_lat_defs
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_lattice_defs
import Submission.Work.BW.sieg2_intLatE_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coordinate equivalence carries the integral lattice `intLatE` onto `intLat`

The Euclidean coordinate model `kcbE F N = ℝ^{[F:ℚ]·N}` and the product model
`(Fin N → KE F)` of `(KE F)^N` are identified by the `ℝ`-linear equivalence `kcbEquiv F N`,
which expands a family of coordinates in the orthonormal basis
`mixedEmbedding.euclidean.stdOrthonormalBasis F` of each factor.

The lattice `intLatE F N` is the `ℤ`-span in the coordinate model of the coordinate vectors of
the images `meK (integralBasis F i)` of the integral basis, while `intLat F N` is the product of
the integral lattices `mixedEmbedding.euclidean.integerLattice F`.  The theorem
`Work.BW.sic_kcbEquiv_intLatE` -- needed for the covolume computations of the
Bombieri–Vaaler kernel-lattice bound -- states that `kcbEquiv F N` maps `intLatE F N` *onto*
`intLat F N`.

The proof proceeds by identifying `kcbEquiv` with the product-model equivalence `pe` of
`Work.BW.sieg2_lattice_defs`, computing its value on the basis `intLatEBasis` (which requires the
single-factor identity `meK_eq_sum`: the expansion of `meK x` in the orthonormal basis), and
identifying the resulting `ℤ`-span with the product of the integral lattices via
`integerLattice_eq_span_meK`.
-/

open NumberField
open scoped Classical
open Module

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The single-factor identity underlying the computation: the expansion of `meK x` in the
orthonormal basis `stdOrthonormalBasis F` has as its coefficients the mixed coordinates of
`mixedEmbedding F x` in the standard basis. -/
theorem kcb_theta (g : NumberField.mixedEmbedding.index F → ℝ) :
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr.symm.toLinearEquiv
        (WithLp.toLp 2 g)
      = ∑ c, g c • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c := by
  change (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr.symm
      (WithLp.toLp 2 g)
    = ∑ c, g c • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c
  have h := OrthonormalBasis.sum_repr
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F)
    ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr.symm (WithLp.toLp 2 g))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [← h, WithLp.ofLp_toLp]

/-- The coordinate equivalence `kcbEquiv F N` of `kcb_lat_defs` agrees with the product-model
equivalence `pe F N` of `sieg2_lattice_defs`; both expand coordinates in the orthonormal basis
of each factor. -/
theorem kcbEquiv_eq_pe (N : ℕ) : kcbEquiv F N = pe F N := by
  ext x n
  simp only [kcbEquiv, pe, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    LinearEquiv.coe_curry]
  rw [show Function.curry ((WithLp.linearEquiv 2 ℝ
        (Fin N × NumberField.mixedEmbedding.index F → ℝ)) x) n
      = (fun c => (WithLp.linearEquiv 2 ℝ
        (Fin N × NumberField.mixedEmbedding.index F → ℝ)) x (n, c)) from by
    funext c; rw [Function.curry_apply]]
  rw [show (WithLp.linearEquiv 2 ℝ (NumberField.mixedEmbedding.index F → ℝ)).symm
      (fun c => (WithLp.linearEquiv 2 ℝ (Fin N × NumberField.mixedEmbedding.index F → ℝ)) x
        (n, c)) = WithLp.toLp 2 (fun c => (WithLp.linearEquiv 2 ℝ
          (Fin N × NumberField.mixedEmbedding.index F → ℝ)) x (n, c)) from rfl]
  rw [kcb_theta]
  rfl

/-- `meK x` is the expansion of the mixed image of `x` in the orthonormal basis. -/
theorem meK_eq_sum (x : F) :
    meK x = ∑ c, ((NumberField.mixedEmbedding.stdBasis F).repr
      (NumberField.mixedEmbedding F x)) c
      • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c := by
  rw [meK]
  apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
  have hmap : ∀ c, NumberField.mixedEmbedding.euclidean.toMixed F
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c)
      = (NumberField.mixedEmbedding.stdBasis F) c := by
    intro c
    have h := congrFun (congrArg (fun b : Basis (NumberField.mixedEmbedding.index F) ℝ
      (NumberField.mixedEmbedding.mixedSpace F) =>
      (b : NumberField.mixedEmbedding.index F → NumberField.mixedEmbedding.mixedSpace F))
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq F)) c
    rw [Basis.map_apply, OrthonormalBasis.coe_toBasis] at h
    exact h
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_sum, map_smul, hmap]
  exact (Basis.sum_repr (NumberField.mixedEmbedding.stdBasis F) _).symm

/-- The value of `pe F N` on the lattice basis `intLatEBasis F N`. -/
theorem pe_intLatEBasis (N : ℕ)
    (q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    pe F N (intLatEBasis F N q) = Pi.single q.1 (meK (NumberField.integralBasis F q.2)) := by
  ext j
  rw [pe_apply]
  have hcoords : (intLatEBasis F N q).ofLp
      = (fun p : Fin N × NumberField.mixedEmbedding.index F =>
      if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F (NumberField.integralBasis F q.2))) p.2 else 0) := by
    rw [intLatEBasis_apply]
  rw [hcoords]
  by_cases hj : j = q.1
  · rw [hj, Pi.single_eq_same]
    rw [show (∑ c, (fun p : Fin N × NumberField.mixedEmbedding.index F =>
          if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
            (NumberField.mixedEmbedding F (NumberField.integralBasis F q.2))) p.2 else 0)
            (q.1, c) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c)
        = ∑ c, ((NumberField.mixedEmbedding.stdBasis F).repr
            (NumberField.mixedEmbedding F (NumberField.integralBasis F q.2))) c
            • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c
        from Finset.sum_congr rfl (fun c _ => by simp)]
    exact (meK_eq_sum (NumberField.integralBasis F q.2)).symm
  · rw [Pi.single_eq_of_ne hj]
    rw [show (∑ c, (fun p : Fin N × NumberField.mixedEmbedding.index F =>
          if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
            (NumberField.mixedEmbedding F (NumberField.integralBasis F q.2))) p.2 else 0)
            (j, c) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c)
        = ∑ c, (0 : KE F) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c
        from Finset.sum_congr rfl (fun c _ => by simp [hj])]
    simp

/-- The Euclidean integral lattice is the `ℤ`-span of the images `meK (integralBasis F i)` of the
integral basis. -/
theorem integerLattice_eq_span_meK :
    NumberField.mixedEmbedding.euclidean.integerLattice F =
      Submodule.span ℤ (Set.range (fun i : Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
        meK (NumberField.integralBasis F i))) := by
  have hmem : ∀ x : NumberField.mixedEmbedding.euclidean.mixedSpace F,
      x ∈ NumberField.mixedEmbedding.euclidean.integerLattice F ↔
        (NumberField.mixedEmbedding.euclidean.toMixed F) x ∈
          NumberField.mixedEmbedding.integerLattice F := by
    intro x
    rw [NumberField.mixedEmbedding.euclidean.integerLattice]
    simp only [ZLattice.comap, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_toLinearMap]
    rfl
  have h1 : Submodule.span ℤ (Set.range (fun i : Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
        meK (NumberField.integralBasis F i)))
      = Submodule.map
          (((NumberField.mixedEmbedding.euclidean.toMixed F).symm).toLinearMap.restrictScalars ℤ)
          (NumberField.mixedEmbedding.integerLattice F) := by
    rw [← NumberField.mixedEmbedding.span_latticeBasis, Submodule.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨NumberField.mixedEmbedding.latticeBasis F i, ⟨i, rfl⟩, by
        rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap,
          NumberField.mixedEmbedding.latticeBasis_apply]; rfl⟩
    · rintro ⟨w, ⟨i, rfl⟩, hw⟩
      refine ⟨i, ?_⟩
      rw [← hw, LinearMap.restrictScalars_apply, LinearEquiv.coe_toLinearMap,
        NumberField.mixedEmbedding.latticeBasis_apply]; rfl
  rw [h1]
  apply Submodule.ext
  intro x
  rw [hmem, Submodule.mem_map]
  change (NumberField.mixedEmbedding.euclidean.toMixed F) x ∈
      NumberField.mixedEmbedding.integerLattice F ↔
    ∃ y ∈ NumberField.mixedEmbedding.integerLattice F,
      (NumberField.mixedEmbedding.euclidean.toMixed F).symm y = x
  constructor
  · intro hx
    exact ⟨(NumberField.mixedEmbedding.euclidean.toMixed F) x, hx, by
      rw [ContinuousLinearEquiv.symm_apply_apply]⟩
  · rintro ⟨z, hz, hzx⟩
    have hthis : (NumberField.mixedEmbedding.euclidean.toMixed F) x = z := by
      rw [← hzx, ContinuousLinearEquiv.apply_symm_apply]
    rwa [hthis]

/-- `pe F N` maps the coordinate lattice `intLatE F N` onto the product lattice `PLat F N`. -/
theorem pe_image_intLatE (N : ℕ) :
    Submodule.map ((pe F N).toLinearMap.restrictScalars ℤ) (intLatE F N) = PLat F N := by
  have hint : intLatE F N = Submodule.span ℤ (Set.range (intLatEBasis F N)) := by
    have hb : ⇑(intLatEBasis F N) = (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
        WithLp.toLp 2 (fun p : Fin N × NumberField.mixedEmbedding.index F =>
          if p.1 = q.1 then ((NumberField.mixedEmbedding.stdBasis F).repr
            (NumberField.mixedEmbedding F (NumberField.integralBasis F q.2))) p.2 else 0)) :=
      funext (intLatEBasis_apply F N)
    rw [hb]; rfl
  rw [hint, Submodule.map_span]
  have hg : ((pe F N).toLinearMap.restrictScalars ℤ) '' Set.range (intLatEBasis F N)
      = Set.range (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
          (Pi.single q.1 (meK (NumberField.integralBasis F q.2)) : Fin N → KE F)) := by
    rw [← Set.range_comp]
    congr 1
    funext q
    rw [Function.comp_apply]
    change pe F N (intLatEBasis F N q) = _
    exact pe_intLatEBasis N q
  rw [hg]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro z ⟨q, rfl⟩
    refine (mem_PLat (F := F) (N := N) _).mpr ?_
    intro j
    dsimp only
    by_cases hj : j = q.1
    · rw [hj, Pi.single_eq_same, integerLattice_eq_span_meK]
      exact Submodule.subset_span ⟨q.2, rfl⟩
    · rw [Pi.single_eq_of_ne hj]
      exact Submodule.zero_mem _
  · intro y hy
    rw [mem_PLat] at hy
    have key : ∀ (j : Fin N) (z : KE F),
        z ∈ Submodule.span ℤ (Set.range (fun i : Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
          meK (NumberField.integralBasis F i))) →
        (Pi.single j z : Fin N → KE F) ∈ Submodule.span ℤ (Set.range (fun q : Fin N ×
          Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
          (Pi.single q.1 (meK (NumberField.integralBasis F q.2)) : Fin N → KE F))) := by
      intro j z hz
      refine Submodule.span_induction (p := fun x _ =>
          (Pi.single j x : Fin N → KE F) ∈ Submodule.span ℤ
          (Set.range (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
            (Pi.single q.1 (meK (NumberField.integralBasis F q.2)) : Fin N → KE F))))
        ?_ ?_ ?_ ?_ hz
      · rintro z' ⟨i, rfl⟩
        exact Submodule.subset_span ⟨(j, i), rfl⟩
      · rw [Pi.single_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        rw [Pi.single_add]; exact Submodule.add_mem _ ha hb
      · intro c a _ ha
        rw [Pi.single_smul]; exact Submodule.smul_mem _ c ha
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    exact key j (y j) ((integerLattice_eq_span_meK (F := F)) ▸ hy j)

end

end Work.BW

namespace Work.BW

/-- The coordinate equivalence `kcbEquiv F N` carries the coordinate lattice `intLatE F N`
onto the integral lattice `intLat F N`. -/
theorem sic_kcbEquiv_intLatE {F : Type*} [Field F] [NumberField F] (N : ℕ) :
    Work.BW.kcbEquiv F N '' (Work.BW.intLatE F N : Set (Work.BW.kcbE F N))
      = (Work.BW.intLat F N : Set (Fin N → Work.BW.KE F)) := by
  rw [kcbEquiv_eq_pe]
  have h := pe_image_intLatE (F := F) N
  have hL : (intLat F N : Set (Fin N → KE F)) = (PLat F N : Set (Fin N → KE F)) := rfl
  rw [hL, ← h, Submodule.map_coe]
  rfl

end Work.BW
