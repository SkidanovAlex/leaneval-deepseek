import Mathlib
import Submission.Work.PTGeometric.SourceZero
import Submission.Work.PTGeometric.alphaFamily_corePreimage_homeo
import Submission.Work.PTGeometric.mem_sourceZeroSet_iff_collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the zero set of the flat source homotopy on the boundary is the pieces

The flat source of the last mile is the half-space `EuclideanHalfSpace ((8+k)+1)`, whose boundary
`{x 0 = 0}` carries the cube coordinates of the null-homotopy of a family (the first coordinate is
the *time* coordinate, which is `0` on the pieces).  The main statement of this file,

  `Work.PTGeometric.sourceZeroSet_boundary_homeo`,

says that the part of the zero set `Z = sourceZeroSet G m hpow` lying on that boundary is exactly
the disjoint union of the pieces `(Fam a.2).pt` (`a : Fin m × ι`):

  `↥(Z ∩ ∂A) ≃ₜ Σ a : Fin m × ι, (Fam a.2).pt`.

This is the statement that the *boundary* stratum of the last mile's source region is the pieces —
the input of the region construction (`Work.PTGeometric.RegionSourceData`) at the boundary.

## The proof

The cube chart `cubeCoord n : ℝ^n ≅ int I^n` (`Work.PTGeometric.cubeCoord`) identifies the boundary
of the half-space with the *open* cube:

* `cubeCoord n y` has all its coordinates `(1 + y_i/√(1+y_i²))/2 ∈ (0,1)`;
* conversely the explicit map `cubeCoordInv n z = (2 z_i - 1)/√(1 - (2 z_i - 1)²)` inverts it on the
  open cube (`cubeCoordInv_cubeCoord`, `cubeCoord_cubeCoordInv`), which also gives the injectivity of
  the cube chart.

The collar identity of the null-homotopy (`Work.PTGeometric.mem_sourceZeroSet_iff_collar`, valid for
`x 0 ≤ 1/2`, hence on the whole boundary) then reads

  `x ∈ Z ↔ alphaFamily G m (cubeCoord (tail (srcCast x))) ∈ G.core`  (`x 0 = 0`),

and the concrete (continuous, linear) homeomorphism `x ↦ tail (k+8) (srcCast k x)` between the
boundary `{x 0 = 0}` and `ℝ^{k+8}` (with inverse `u ↦ srcCastInv k (consCLM (k+8) (0,u))`, which
needs `srcCast_srcCastInv`) identifies this with the core preimage

  `B := {z : I^{k+8} | alphaFamily G m z ∈ G.core}`.

The map `x ↦ cubeCoord (k+8) (tail (k+8) (srcCast k x))` is therefore a continuous bijection from
the *compact* space `↥(Z ∩ ∂A)` onto the Hausdorff space `↥B` (surjectivity uses that a point of
`B` is not on the boundary of the cube, because there the loop `alphaFamily G m` is the base point
`D.t₀` and `D.t₀ ∉ core`), hence a homeomorphism
(`isHomeomorph_iff_continuous_bijective`).  Composing with the block decomposition
`Work.PTGeometric.alphaFamily_corePreimage_homeo` (`↥B ≃ₜ Σ a, (Fam a.2).pt`) gives the result.

## Main results

* `Work.PTGeometric.cubeCoordInv`, `…Inv_cubeCoord`, `…_cubeCoordInv`, `…_injective`
* `Work.PTGeometric.srcCast_srcCastInv`
* `Work.PTGeometric.sourceZeroSet_boundary_homeo`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-! ## The cube chart and its explicit inverse -/

/-- The scalar component of the cube chart `cubeCoord`: `y ↦ y/√(1+y²)`.  It is the inverse of
`s ↦ s/√(1-s²)` on `(-1,1)` (`cubeG_cubeH`), and takes all values in `(-1,1)`. -/
def cubeG (y : ℝ) : ℝ := y / Real.sqrt (1 + y ^ 2)

/-- The scalar component of the inverse of the cube chart. -/
def cubeH (s : ℝ) : ℝ := s / Real.sqrt (1 - s ^ 2)

theorem cubeH_cubeG (y : ℝ) : cubeH (cubeG y) = y := by
  have hy : 0 < 1 + y ^ 2 := by positivity
  have hs : (cubeG y) ^ 2 = y ^ 2 / (1 + y ^ 2) := by
    rw [cubeG, div_pow, Real.sq_sqrt hy.le]
  have h1 : 1 - (cubeG y) ^ 2 = 1 / (1 + y ^ 2) := by
    rw [hs]; field_simp; ring
  have hprod : (1 / (1 + y ^ 2)) * (1 + y ^ 2) = 1 := by field_simp
  have hroot : Real.sqrt (1 - (cubeG y) ^ 2) * Real.sqrt (1 + y ^ 2) = 1 := by
    rw [h1, ← Real.sqrt_mul (show (0 : ℝ) ≤ 1 / (1 + y ^ 2) by positivity), hprod, Real.sqrt_one]
  have hinv : (Real.sqrt (1 - (cubeG y) ^ 2))⁻¹ = Real.sqrt (1 + y ^ 2) :=
    inv_eq_of_mul_eq_one_right hroot
  rw [cubeH, div_eq_mul_inv, hinv]
  exact div_mul_cancel₀ y (ne_of_gt (Real.sqrt_pos.mpr hy))

theorem cubeG_cubeH {s : ℝ} (h1 : -1 < s) (h2 : s < 1) : cubeG (cubeH s) = s := by
  have hs : 0 < 1 - s ^ 2 := by nlinarith
  have hsq : (cubeH s) ^ 2 = s ^ 2 / (1 - s ^ 2) := by
    rw [cubeH, div_pow, Real.sq_sqrt hs.le]
  have h1' : 1 + (cubeH s) ^ 2 = 1 / (1 - s ^ 2) := by
    rw [hsq]; field_simp; ring
  have hprod : (1 / (1 - s ^ 2)) * (1 - s ^ 2) = 1 := by field_simp
  have hroot : Real.sqrt (1 + (cubeH s) ^ 2) * Real.sqrt (1 - s ^ 2) = 1 := by
    rw [h1', ← Real.sqrt_mul (show (0 : ℝ) ≤ 1 / (1 - s ^ 2) by positivity), hprod,
      Real.sqrt_one]
  have hinv : (Real.sqrt (1 + (cubeH s) ^ 2))⁻¹ = Real.sqrt (1 - s ^ 2) :=
    inv_eq_of_mul_eq_one_right hroot
  rw [cubeG, div_eq_mul_inv, hinv]
  exact div_mul_cancel₀ s (ne_of_gt (Real.sqrt_pos.mpr hs))

/-- **The explicit inverse of the cube chart** `cubeCoord n : ℝ^n → int I^n`, componentwise
`z ↦ (2 z_i - 1)/√(1 - (2 z_i - 1)²)`.  It inverts `cubeCoord` on the open cube
(`cubeCoord_cubeCoordInv`) and is inverted by it on all of `ℝ^n` (`cubeCoordInv_cubeCoord`). -/
def cubeCoordInv (n : ℕ) (z : Fin n → Set.Icc (0 : ℝ) 1) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => cubeH (2 * (z i : ℝ) - 1))

theorem cubeCoordInv_apply (n : ℕ) (z : Fin n → Set.Icc (0 : ℝ) 1) (i : Fin n) :
    (cubeCoordInv n z) i = cubeH (2 * (z i : ℝ) - 1) := by
  rw [cubeCoordInv, WithLp.ofLp_toLp]

theorem cubeCoord_apply' (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ((cubeCoord n y i : Set.Icc (0 : ℝ) 1) : ℝ) = (1 + cubeG (y i)) / 2 := by
  rw [cubeCoord_apply_coe]
  rfl

theorem cubeCoordInv_cubeCoord (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    cubeCoordInv n (cubeCoord n y) = y := by
  ext i
  rw [cubeCoordInv_apply, cubeCoord_apply']
  have h : 2 * ((1 + cubeG (y i)) / 2) - 1 = cubeG (y i) := by ring
  rw [h, cubeH_cubeG]

theorem cubeCoord_cubeCoordInv (n : ℕ) (z : Fin n → Set.Icc (0 : ℝ) 1)
    (hz : ∀ i, 0 < (z i : ℝ) ∧ (z i : ℝ) < 1) :
    cubeCoord n (cubeCoordInv n z) = z := by
  funext i
  apply Subtype.ext
  rw [cubeCoord_apply', cubeCoordInv_apply]
  have h1 : -1 < 2 * (z i : ℝ) - 1 := by linarith [(hz i).1]
  have h2 : 2 * (z i : ℝ) - 1 < 1 := by linarith [(hz i).2]
  rw [cubeG_cubeH h1 h2]
  ring

theorem cubeCoord_injective (n : ℕ) : Function.Injective (cubeCoord n) := by
  intro y y' h
  rw [← cubeCoordInv_cubeCoord n y, h, cubeCoordInv_cubeCoord n y']

/-! ## The missing inverse of the reindexing `srcCast` -/

/-- `srcCastInv` is a genuine inverse of `srcCast` (the file `SourceNull` proves only the other
composition). -/
theorem srcCast_srcCastInv (k : ℕ) (x : EuclideanSpace ℝ (Fin ((k + 8) + 1))) :
    srcCast k (srcCastInv k x) = x := by
  ext i
  rw [srcCast_apply, srcCastInv_apply, Fin.cast_cast]
  exact congrArg (fun j : Fin ((k + 8) + 1) => x.ofLp j) (Fin.ext (by simp [Fin.cast]))

/-! ## The main theorem -/

/-- **The boundary stratum of the zero set is the disjoint union of the pieces.**

For a genuine family `G` and a multiplicity `m` with `(∏ i, tubeAlpha (G.rep i)) ^ m = 1`, the part
of the zero set of the flat source homotopy lying on the boundary `{x 0 = 0}` of the half-space —
i.e. the pieces' part of the null-bordism — is homeomorphic to the disjoint union of the pieces
`(Fam a.2).pt`, `a : Fin m × ι`.

The homeomorphism is `x ↦ cubeCoord (k+8) (tail (k+8) (srcCast k x))`, read through the block
decomposition `Work.PTGeometric.alphaFamily_corePreimage_homeo` of the cube core preimage. -/
theorem sourceZeroSet_boundary_homeo {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1) :
    Nonempty (↥(Work.PTGeometric.sourceZeroSet G m hpow ∩
        {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) ≃ₜ
      (Σ a : Fin m × ι, (Fam a.2).pt)) := by
  classical
  -- the boundary of the half space is closed, so the part of the (compact) zero set on it is compact
  have hBdryClosed : IsClosed {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0} :=
    isClosed_eq ((continuous_coord0 k).comp continuous_subtype_val) continuous_const
  haveI hCompact : CompactSpace
      ↥(sourceZeroSet G m hpow ∩ {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) :=
    isCompact_iff_compactSpace.mp ((isCompact_sourceZeroSet G m hpow).inter_right hBdryClosed)
  haveI hT2 : T2Space ↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
      alphaFamily G m z ∈ G.core} := inferInstance
  -- the cube core preimage is contained in the open cube: on the boundary of the cube the loop
  -- `alphaFamily G m` is the base point, which does not lie in the core
  have hzopen : ∀ z ∈ ({z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
      alphaFamily G m z ∈ G.core}), ∀ i, 0 < (z i : ℝ) ∧ (z i : ℝ) < 1 := by
    intro z hz i
    constructor
    · by_contra hcon
      have h0 : (z i : ℝ) = 0 := le_antisymm (not_lt.mp hcon) (z i).2.1
      exact G.t0_notMem_core (((alphaFamily G m).2 z ⟨i, Or.inl (Subtype.ext h0)⟩) ▸ hz)
    · by_contra hcon
      have h1 : (z i : ℝ) = 1 := le_antisymm (z i).2.2 (not_lt.mp hcon)
      exact G.t0_notMem_core (((alphaFamily G m).2 z ⟨i, Or.inr (Subtype.ext h1)⟩) ▸ hz)
  -- the collar identity of the null-homotopy, on the boundary
  have hcollar : ∀ x : EuclideanHalfSpace ((8 + k) + 1), x.1 0 = 0 →
      (x ∈ sourceZeroSet G m hpow ↔
        alphaFamily G m (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1))) ∈ G.core) :=
    fun x hx => mem_sourceZeroSet_iff_collar G m hpow (le_trans (le_of_eq hx) (by norm_num))
  -- the map to the cube core preimage
  have hmem : ∀ x : ↥(sourceZeroSet G m hpow ∩
        {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}),
      alphaFamily G m (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1))) ∈ G.core :=
    fun x => (hcollar x.1 x.2.2).mp x.2.1
  let F : ↥(sourceZeroSet G m hpow ∩ {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) →
      ↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 | alphaFamily G m z ∈ G.core} :=
    fun x => ⟨cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1)), hmem x⟩
  have hFcont : Continuous F :=
    Continuous.subtype_mk
      ((continuous_cubeCoord (k + 8)).comp ((continuous_tail (k + 8)).comp
        ((continuous_srcCast k).comp (continuous_subtype_val.comp continuous_subtype_val))))
      (fun x => hmem x)
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1)) =
        cubeCoord (k + 8) (tail (k + 8) (srcCast k y.1.1)) := congrArg Subtype.val hxy
    have h2 : tailCLM (k + 8) (srcCast k x.1.1) = tailCLM (k + 8) (srcCast k y.1.1) :=
      cubeCoord_injective (k + 8) h1
    -- the head coordinates of the boundary points are both `0`
    have hx0 : (srcCast k x.1.1) 0 = 0 := by
      show head (k + 8) (srcCast k x.1.1) = 0
      rw [head_srcCast]
      exact x.2.2
    have hy0 : (srcCast k y.1.1) 0 = 0 := by
      show head (k + 8) (srcCast k y.1.1) = 0
      rw [head_srcCast]
      exact y.2.2
    have h2' : srcCast k x.1.1 = srcCast k y.1.1 := by
      rw [← consCLM_tail (k + 8) (srcCast k x.1.1), hx0,
        ← consCLM_tail (k + 8) (srcCast k y.1.1), hy0, h2]
    have h3 : x.1.1 = y.1.1 := by
      rw [← srcCastInv_srcCast k x.1.1, h2', srcCastInv_srcCast k y.1.1]
    exact Subtype.ext (Subtype.ext h3)
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℝ (Fin (k + 8)), cubeCoord (k + 8) u = z.1 :=
      ⟨cubeCoordInv (k + 8) z.1, cubeCoord_cubeCoordInv (k + 8) z.1 (hzopen z.1 z.2)⟩
    have htail : tail (k + 8) (srcCast k (srcCastInv k (consCLM (k + 8) (0, u)))) = u := by
      rw [srcCast_srcCastInv k]
      exact tailCLM_consCLM (k + 8) 0 u
    have hb0 : (srcCastInv k (consCLM (k + 8) (0, u))) 0 = 0 := by
      rw [srcCastInv_apply]
      simp [Fin.cast_zero, consCLM_apply_zero]
    have hmem0 : (⟨srcCastInv k (consCLM (k + 8) (0, u)), le_of_eq hb0.symm⟩ :
        EuclideanHalfSpace ((8 + k) + 1)) ∈ sourceZeroSet G m hpow := by
      refine (mem_sourceZeroSet_iff_collar G m hpow
        (x := (⟨srcCastInv k (consCLM (k + 8) (0, u)), le_of_eq hb0.symm⟩ :
          EuclideanHalfSpace ((8 + k) + 1))) (by rw [hb0]; norm_num)).mpr ?_
      rw [htail, hu]
      exact z.2
    refine ⟨⟨⟨srcCastInv k (consCLM (k + 8) (0, u)), le_of_eq hb0.symm⟩, hmem0, hb0⟩, ?_⟩
    · apply Subtype.ext
      show cubeCoord (k + 8)
        (tail (k + 8) (srcCast k (srcCastInv k (consCLM (k + 8) (0, u))))) = z.1
      rw [htail, hu]
  obtain ⟨h1, -⟩ := isHomeomorph_iff_exists_homeomorph.mp
    ((isHomeomorph_iff_continuous_bijective (f := F)).mpr ⟨hFcont, hFinj, hFsurj⟩)
  obtain ⟨h2⟩ := alphaFamily_corePreimage_homeo (D := D) (Fam := Fam) G m
  exact ⟨h1.trans h2⟩


/-- **The first stage of the collapse identification, WITH its explicit formula.**

This is the *repair* of the opacity of `Work.PTGeometric.sourceZeroSet_boundary_homeo`: that theorem
concludes in `Nonempty (…)`, and its consumers take `Classical.choice` of it, which
(`#print Classical.choice`) is a bare axiom with no reduction rule and no specification
(`Classical.choice_eq` does not exist, and `rfl` fails on `Classical.choice (⟨a⟩ : Nonempty α) = a`)
— so the identification they use is *unspecified*.  Here the homeomorphism is the **explicit** map

    F x = (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1)), _)

built directly by `Continuous.homeoOfEquivCompactToT2` (never through `Classical.choice`), and the
statement *records* its first coordinate.  The `isHomeomorph_iff_exists_homeomorph` step of
`sourceZeroSet_boundary_homeo` (whose conclusion is an `Exists`, `⇑h = F`, discarded there by
`obtain ⟨h1, -⟩`) is thus replaced by a construction whose `coe` is definitionally `F`.

See `Submission/Work/ThomBordism/NOTE_HEND_OPAQUE.md`. -/
theorem sourceZeroSet_boundary_homeo_cubeCast {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1) :
    ∃ h : ↥(Work.PTGeometric.sourceZeroSet G m hpow ∩
        {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) ≃ₜ
        (↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 | Work.PTGeometric.alphaFamily G m z ∈ G.core}),
      ∀ x, (h x).1 = cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1)) := by
  classical
  -- the boundary of the half space is closed, so the part of the (compact) zero set on it is compact
  have hBdryClosed : IsClosed {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0} :=
    isClosed_eq ((continuous_coord0 k).comp continuous_subtype_val) continuous_const
  haveI hCompact : CompactSpace
      ↥(sourceZeroSet G m hpow ∩ {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) :=
    isCompact_iff_compactSpace.mp ((isCompact_sourceZeroSet G m hpow).inter_right hBdryClosed)
  haveI hT2 : T2Space ↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
      alphaFamily G m z ∈ G.core} := inferInstance
  -- the cube core preimage is contained in the open cube: on the boundary of the cube the loop
  -- `alphaFamily G m` is the base point, which does not lie in the core
  have hzopen : ∀ z ∈ ({z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
      alphaFamily G m z ∈ G.core}), ∀ i, 0 < (z i : ℝ) ∧ (z i : ℝ) < 1 := by
    intro z hz i
    constructor
    · by_contra hcon
      have h0 : (z i : ℝ) = 0 := le_antisymm (not_lt.mp hcon) (z i).2.1
      exact G.t0_notMem_core (((alphaFamily G m).2 z ⟨i, Or.inl (Subtype.ext h0)⟩) ▸ hz)
    · by_contra hcon
      have h1 : (z i : ℝ) = 1 := le_antisymm (z i).2.2 (not_lt.mp hcon)
      exact G.t0_notMem_core (((alphaFamily G m).2 z ⟨i, Or.inr (Subtype.ext h1)⟩) ▸ hz)
  -- the collar identity of the null-homotopy, on the boundary
  have hcollar : ∀ x : EuclideanHalfSpace ((8 + k) + 1), x.1 0 = 0 →
      (x ∈ sourceZeroSet G m hpow ↔
        alphaFamily G m (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1))) ∈ G.core) :=
    fun x hx => mem_sourceZeroSet_iff_collar G m hpow (le_trans (le_of_eq hx) (by norm_num))
  -- the map to the cube core preimage
  have hmem : ∀ x : ↥(sourceZeroSet G m hpow ∩
        {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}),
      alphaFamily G m (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1))) ∈ G.core :=
    fun x => (hcollar x.1 x.2.2).mp x.2.1
  let F : ↥(sourceZeroSet G m hpow ∩ {x : EuclideanHalfSpace ((8 + k) + 1) | x.1 0 = 0}) →
      ↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 | alphaFamily G m z ∈ G.core} :=
    fun x => ⟨cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1)), hmem x⟩
  have hFcont : Continuous F :=
    Continuous.subtype_mk
      ((continuous_cubeCoord (k + 8)).comp ((continuous_tail (k + 8)).comp
        ((continuous_srcCast k).comp (continuous_subtype_val.comp continuous_subtype_val))))
      (fun x => hmem x)
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1.1)) =
        cubeCoord (k + 8) (tail (k + 8) (srcCast k y.1.1)) := congrArg Subtype.val hxy
    have h2 : tailCLM (k + 8) (srcCast k x.1.1) = tailCLM (k + 8) (srcCast k y.1.1) :=
      cubeCoord_injective (k + 8) h1
    -- the head coordinates of the boundary points are both `0`
    have hx0 : (srcCast k x.1.1) 0 = 0 := by
      show head (k + 8) (srcCast k x.1.1) = 0
      rw [head_srcCast]
      exact x.2.2
    have hy0 : (srcCast k y.1.1) 0 = 0 := by
      show head (k + 8) (srcCast k y.1.1) = 0
      rw [head_srcCast]
      exact y.2.2
    have h2' : srcCast k x.1.1 = srcCast k y.1.1 := by
      rw [← consCLM_tail (k + 8) (srcCast k x.1.1), hx0,
        ← consCLM_tail (k + 8) (srcCast k y.1.1), hy0, h2]
    have h3 : x.1.1 = y.1.1 := by
      rw [← srcCastInv_srcCast k x.1.1, h2', srcCastInv_srcCast k y.1.1]
    exact Subtype.ext (Subtype.ext h3)
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℝ (Fin (k + 8)), cubeCoord (k + 8) u = z.1 :=
      ⟨cubeCoordInv (k + 8) z.1, cubeCoord_cubeCoordInv (k + 8) z.1 (hzopen z.1 z.2)⟩
    have htail : tail (k + 8) (srcCast k (srcCastInv k (consCLM (k + 8) (0, u)))) = u := by
      rw [srcCast_srcCastInv k]
      exact tailCLM_consCLM (k + 8) 0 u
    have hb0 : (srcCastInv k (consCLM (k + 8) (0, u))) 0 = 0 := by
      rw [srcCastInv_apply]
      simp [Fin.cast_zero, consCLM_apply_zero]
    have hmem0 : (⟨srcCastInv k (consCLM (k + 8) (0, u)), le_of_eq hb0.symm⟩ :
        EuclideanHalfSpace ((8 + k) + 1)) ∈ sourceZeroSet G m hpow := by
      refine (mem_sourceZeroSet_iff_collar G m hpow
        (x := (⟨srcCastInv k (consCLM (k + 8) (0, u)), le_of_eq hb0.symm⟩ :
          EuclideanHalfSpace ((8 + k) + 1))) (by rw [hb0]; norm_num)).mpr ?_
      rw [htail, hu]
      exact z.2
    refine ⟨⟨⟨srcCastInv k (consCLM (k + 8) (0, u)), le_of_eq hb0.symm⟩, hmem0, hb0⟩, ?_⟩
    · apply Subtype.ext
      show cubeCoord (k + 8)
        (tail (k + 8) (srcCast k (srcCastInv k (consCLM (k + 8) (0, u))))) = z.1
      rw [htail, hu]
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFinj, hFsurj⟩) hFcont,
    fun x => rfl⟩

end

end Work.PTGeometric
