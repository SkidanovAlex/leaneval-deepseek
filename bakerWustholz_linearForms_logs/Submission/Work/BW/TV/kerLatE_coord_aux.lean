import Mathlib
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_PhiE_aux
import Submission.Work.BW.kcb_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary coordinate lemmas for `Work.BW.TV.mem_kerLatE_iff`

The matrix `Work.BW.PhiE a` of `Work.BW.sieg2KernelDefs` is the matrix of the `ℝ`-linear map
`Work.BW.Phi a` written in the orthonormal basis `mixedEmbedding.euclidean.stdOrthonormalBasis F`
of the Euclidean mixed space `Work.BW.KE F`, while `Work.BW.phiMap a` of `Work.BW.kcb_defs` is the
same map written in the coordinates of the standard basis `mixedEmbedding.stdBasis F` (the basis
in which `Work.BW.coord` and `Work.BW.coordVec` are defined).

The two bases are matched by the isometry `mixedEmbedding.euclidean.toMixed F`:
`stdOrthonormalBasis_map_eq` says that `toMixed` carries the orthonormal basis onto `stdBasis`.
Consequently the `ofLp` coordinates of a point of `EuclideanSpace ℝ (index F)` are exactly the
`stdBasis`-coordinates of the corresponding `mixedSpace` element (`zz_coord_toMixed` below), and the
matrix `PhiMat a` agrees entrywise with the coordinate matrix of `mulCoord` (`zz_PhiMat_eq`).
-/

namespace Work.BW.TV

open NumberField

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The isometry `toMixed` carries the orthonormal basis of the Euclidean mixed space to the
standard basis of the mixed space. -/
theorem zz_toMixed_stdOrthonormalBasis (c : NumberField.mixedEmbedding.index F) :
    NumberField.mixedEmbedding.euclidean.toMixed F
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c) =
      NumberField.mixedEmbedding.stdBasis F c := by
  have h := DFunLike.congr_fun
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq F) c
  simpa using h

/-- `toMixed` intertwines `mixLen`, i.e. `mulK`, with the multiplication by the mixed embedding. -/
theorem zz_toMixed_mulK (α : F) (z : Work.BW.KE F) :
    NumberField.mixedEmbedding.euclidean.toMixed F (Work.BW.mulK α z) =
      NumberField.mixedEmbedding F α *
        NumberField.mixedEmbedding.euclidean.toMixed F z := by
  simp [Work.BW.mulK]

/-- The `stdBasis`-coordinates of the `toMixed`-image of a point of the Euclidean mixed space are
its coordinates in the orthonormal basis, i.e. its `ofLp`-coordinates. -/
theorem zz_coord_toMixed (v : Work.BW.KE F) :
    Work.BW.coord (F := F) (NumberField.mixedEmbedding.euclidean.toMixed F v)
      = WithLp.ofLp ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr v) := by
  classical
  set b := NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F with hb
  let f : Work.BW.KE F →ₗ[ℝ] (NumberField.mixedEmbedding.index F → ℝ) :=
    { toFun := fun w => Work.BW.coord (F := F)
        (NumberField.mixedEmbedding.euclidean.toMixed F w)
      map_add' := by intro x y; simp [Work.BW.coord, map_add]
      map_smul' := by intro r x; simp [Work.BW.coord, map_smul] }
  let g : Work.BW.KE F →ₗ[ℝ] (NumberField.mixedEmbedding.index F → ℝ) :=
    { toFun := fun w => WithLp.ofLp (b.repr w)
      map_add' := by intro x y; simp
      map_smul' := by intro r x; simp }
  have hfv : f v = Work.BW.coord (F := F)
      (NumberField.mixedEmbedding.euclidean.toMixed F v) := rfl
  have hgv : g v = WithLp.ofLp (b.repr v) := rfl
  have hfg : f = g := by
    refine Module.Basis.ext b.toBasis (fun c => ?_)
    change Work.BW.coord (F := F)
        (NumberField.mixedEmbedding.euclidean.toMixed F (b.toBasis c))
      = WithLp.ofLp (b.repr (b.toBasis c))
    rw [show b.toBasis c = b c from rfl,
      show b c = NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c from by rw [hb],
      zz_toMixed_stdOrthonormalBasis c]
    rw [show Work.BW.coord (F := F) (NumberField.mixedEmbedding.stdBasis F c)
        = ⇑((NumberField.mixedEmbedding.stdBasis F).repr
            (NumberField.mixedEmbedding.stdBasis F c)) from rfl]
    rw [Module.Basis.repr_self, OrthonormalBasis.repr_self]
    ext k
    rw [Finsupp.single_apply, PiLp.single_apply]
    by_cases h : k = c
    · simp [h]
    · simp [h, Ne.symm h]
  rw [← hfv, ← hgv, hfg]

/-- The `stdBasis`-coordinates of a standard basis vector, as a function. -/
theorem zz_coord_stdBasis (c : NumberField.mixedEmbedding.index F) :
    Work.BW.coord (F := F) (NumberField.mixedEmbedding.stdBasis F c)
      = ⇑(Finsupp.single c (1:ℝ)) := by
  classical
  funext k
  rw [show Work.BW.coord (F := F) (NumberField.mixedEmbedding.stdBasis F c)
      = ⇑((NumberField.mixedEmbedding.stdBasis F).repr
          (NumberField.mixedEmbedding.stdBasis F c)) from rfl, Module.Basis.repr_self]

/-- The entries of the matrix `PhiMat a` are the entries of the coordinate matrix of `mulCoord`: the
matrix of `Phi a` in the orthonormal basis is the matrix of the multiplication-by-`mixedEmbedding`
in the standard basis. -/
theorem zz_PhiMat_eq {M N : ℕ} (a : Fin M → Fin N → F) (i : Fin M)
    (c : NumberField.mixedEmbedding.index F) (j : Fin N)
    (c' : NumberField.mixedEmbedding.index F) :
    Work.BW.PhiMat a (i, c) (j, c') =
      Work.BW.mulCoord (a i j) (⇑(Finsupp.single c' (1:ℝ))) c := by
  classical
  rw [Work.BW.PhiMat_apply_coe]
  rw [← OrthonormalBasis.repr_apply_apply
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F)
    (Work.BW.mulK (a i j)
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c')) c]
  rw [← zz_coord_toMixed (Work.BW.mulK (a i j)
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c'))]
  rw [zz_toMixed_mulK, zz_toMixed_stdOrthonormalBasis,
    ← Work.BW.mulCoord_apply_coord (F := F) (a i j)
      (NumberField.mixedEmbedding.stdBasis F c'), zz_coord_stdBasis]

/-- The matrix model `PhiE a`, read in the orthonormal coordinates `ofLp`, is the coordinate model
`phiMap a` of the same map: the two are matched by the identification of the orthonormal
coordinates of `EuclideanSpace ℝ (Fin N × index F)` with the `stdBasis`-coordinates of the mixed
space. -/
theorem zz_PhiE_ofLp_eq_phiMap {M N : ℕ} (a : Fin M → Fin N → F)
    (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) :
    (fun (i : Fin M) (c : NumberField.mixedEmbedding.index F) =>
        WithLp.ofLp (Work.BW.PhiE a x) (i, c))
      = Work.BW.phiMap a (fun (j : Fin N) (q : NumberField.mixedEmbedding.index F) =>
          WithLp.ofLp x (j, q)) := by
  classical
  have hmat : WithLp.ofLp (Work.BW.PhiE a x)
      = (Work.BW.PhiMat a).mulVec (WithLp.ofLp x) := rfl
  -- The identity of the two matrix models, as linear maps of the coefficient spaces.
  let P : (Fin N × NumberField.mixedEmbedding.index F → ℝ) →ₗ[ℝ]
      (Fin M → NumberField.mixedEmbedding.index F → ℝ) :=
    { toFun := fun y i c => (Work.BW.PhiMat a).mulVec y (i, c)
      map_add' := by intro y z; funext i c; simp [Matrix.mulVec_add]
      map_smul' := by intro r y; funext i c; simp [Matrix.mulVec_smul] }
  let Q : (Fin N × NumberField.mixedEmbedding.index F → ℝ) →ₗ[ℝ]
      (Fin M → NumberField.mixedEmbedding.index F → ℝ) :=
    { toFun := fun y i c => Work.BW.phiMap a (fun j q => y (j, q)) i c
      map_add' := by
        intro y z
        funext i c
        exact congrFun (congrFun (map_add (Work.BW.phiMap a)
          (fun j q => y (j, q)) (fun j q => z (j, q))) i) c
      map_smul' := by
        intro r y
        funext i c
        exact congrFun (congrFun (map_smul (Work.BW.phiMap a) r
          (fun j q => y (j, q))) i) c }
  have hPQ : P = Q := by
    refine Module.Basis.ext (Pi.basisFun ℝ (Fin N × NumberField.mixedEmbedding.index F))
      (fun q => ?_)
    obtain ⟨j, c'⟩ := q
    ext i c
    rw [Pi.basisFun_apply]
    change (Work.BW.PhiMat a).mulVec
        (Pi.single (j, c') (1:ℝ) : Fin N × NumberField.mixedEmbedding.index F → ℝ) (i, c)
      = Work.BW.phiMap a (fun (j' : Fin N) (q' : NumberField.mixedEmbedding.index F) =>
          (Pi.single (j, c') (1:ℝ) : Fin N × NumberField.mixedEmbedding.index F → ℝ)
            (j', q')) i c
    have hsingle : (fun (j' : Fin N) (q' : NumberField.mixedEmbedding.index F) =>
        (Pi.single (j, c') (1:ℝ) : Fin N × NumberField.mixedEmbedding.index F → ℝ) (j', q'))
        = Pi.single j (Pi.single c' (1:ℝ)) := by
      funext j' q'
      by_cases h : j' = j
      · rw [h]
        by_cases h2 : q' = c'
        · rw [h2]; simp
        · rw [Pi.single_eq_of_ne (show (j, q') ≠ (j, c') from fun hh => h2 (Prod.mk.inj hh).2)]
          rw [Pi.single_eq_same, Pi.single_eq_of_ne (show q' ≠ c' from h2)]
      · rw [Pi.single_eq_of_ne (show (j', q') ≠ (j, c') from fun hh => h (Prod.mk.inj hh).1),
          Pi.single_eq_of_ne (show j' ≠ j from h)]
        simp
    rw [hsingle, Matrix.mulVec_single_one, Matrix.col_apply]
    rw [show Work.BW.phiMap a (Pi.single j (Pi.single c' (1:ℝ))) i c
        = Work.BW.mulCoord (a i j) (Pi.single c' (1:ℝ)) c from ?_,
      ← Finsupp.single_eq_pi_single]
    exact zz_PhiMat_eq a i c j c'
    simp only [Work.BW.phiMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne (show b ≠ j from hb)]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  have hx2 : (fun (i : Fin M) (c : NumberField.mixedEmbedding.index F) =>
      (Work.BW.PhiMat a).mulVec (WithLp.ofLp x) (i, c))
      = Work.BW.phiMap a (fun (j : Fin N) (q : NumberField.mixedEmbedding.index F) =>
          WithLp.ofLp x (j, q)) :=
    LinearMap.congr_fun hPQ (WithLp.ofLp x)
  rw [hmat]
  exact hx2

end

end Work.BW.TV
