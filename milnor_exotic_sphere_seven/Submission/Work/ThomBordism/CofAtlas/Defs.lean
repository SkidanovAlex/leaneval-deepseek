import Mathlib
import Submission.Work.PTGeometric.Lvl.Manifold
import Submission.Work.PTGeometric.RieszProj.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A positively oriented atlas on the level set, from a coframing

Vocabulary for `Work.ThomBordism.levelSet_positiveAtlas_of_coframing`.

The level set `W = v⁻¹(0)` of a coframed level function carries the `Lvl` chart structure.  The
charts of that structure are *not* positively oriented relative to the canonical orientation of
`W` (given by the ambient orientation `hMdet` and the coframing `hcof`); this file provides the
vocabulary to *flip* those charts (post-compose with the reflection of the half-space negating the
tangential coordinate `1`, which preserves the half-space) so that the resulting atlas is positive.

* `reflCoordFun`, `reflCoord`, `reflLin`, `reflE`, `reflOph`, `reflOphE` — the reflection;
* `Input` — the bundled geometric data of the target;
* `Input.jx`, `Input.src` — the coframing index and the (connected) source of the chart at a point;
* `Input.sgn`, `Input.flipsgn`, `Input.newChart` — the sign of a `Lvl` chart relative to the
  canonical framing, the corrective sign, and the corrected chart;
* `Input.chartedSpace` — the corrected charted structure.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Classical
open Work.PTGeometric

namespace Work.ThomBordism.CofAtlas

noncomputable section

/-- The model space `ℝ⁹`. -/
abbrev E9 : Type := EuclideanSpace ℝ (Fin 9)

/-- The reflection of `Fin 9 → ℝ` negating the coordinate `1`. -/
def reflCoordFun (v : Fin 9 → ℝ) : Fin 9 → ℝ := Function.update v 1 (-(v 1))

theorem reflCoordFun_zero (v : Fin 9 → ℝ) : reflCoordFun v 0 = v 0 := by
  rw [reflCoordFun, Function.update_apply]; simp

theorem reflCoordFun_one (v : Fin 9 → ℝ) : reflCoordFun v 1 = -(v 1) := by
  rw [reflCoordFun, Function.update_apply]; simp

theorem reflCoordFun_apply_of_ne (v : Fin 9 → ℝ) {i : Fin 9} (hi : i ≠ 1) :
    reflCoordFun v i = v i := by
  rw [reflCoordFun, Function.update_apply]; simp [hi]

theorem reflCoordFun_involutive (v : Fin 9 → ℝ) : reflCoordFun (reflCoordFun v) = v := by
  funext i
  by_cases hi : i = 1
  · subst hi; rw [reflCoordFun_one, reflCoordFun_one, neg_neg]
  · rw [reflCoordFun_apply_of_ne _ hi, reflCoordFun_apply_of_ne _ hi]

/-- The reflection of `Fin 9 → ℝ` negating the coordinate `1`, as a linear equivalence. -/
def reflCoord : (Fin 9 → ℝ) ≃ₗ[ℝ] (Fin 9 → ℝ) where
  toFun := reflCoordFun
  invFun := reflCoordFun
  map_add' v w := by
    funext i
    by_cases hi : i = 1
    · subst hi
      show reflCoordFun (v + w) 1 = reflCoordFun v 1 + reflCoordFun w 1
      rw [reflCoordFun_one, reflCoordFun_one, reflCoordFun_one]
      simp only [Pi.add_apply]; ring
    · show reflCoordFun (v + w) i = reflCoordFun v i + reflCoordFun w i
      rw [reflCoordFun_apply_of_ne (v + w) hi, reflCoordFun_apply_of_ne v hi,
        reflCoordFun_apply_of_ne w hi, Pi.add_apply]
  map_smul' c v := by
    funext i
    by_cases hi : i = 1
    · subst hi
      show reflCoordFun (c • v) 1 = c • reflCoordFun v 1
      rw [reflCoordFun_one, reflCoordFun_one]
      simp only [Pi.smul_apply, smul_neg]
    · show reflCoordFun (c • v) i = c • reflCoordFun v i
      rw [reflCoordFun_apply_of_ne (c • v) hi, reflCoordFun_apply_of_ne v hi, Pi.smul_apply]
  left_inv := reflCoordFun_involutive
  right_inv := reflCoordFun_involutive

theorem reflCoord_apply (v : Fin 9 → ℝ) : reflCoord v = reflCoordFun v := rfl

/-- **The reflection of `ℝ⁹` negating the coordinate `1`**, as a linear equivalence. -/
def reflLin : E9 ≃ₗ[ℝ] E9 :=
  ((EuclideanSpace.equiv (Fin 9) ℝ).toLinearEquiv).trans
    (reflCoord.trans ((EuclideanSpace.equiv (Fin 9) ℝ).symm.toLinearEquiv))

theorem reflLin_apply (v : E9) :
    reflLin v = (EuclideanSpace.equiv (Fin 9) ℝ).symm
      (reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v)) := rfl

theorem reflLin_apply_zero (v : E9) : (reflLin v) 0 = v 0 := by
  rw [reflLin_apply]
  show reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v) 0
    = ((EuclideanSpace.equiv (Fin 9) ℝ) v) 0
  rw [reflCoordFun_zero]

theorem reflLin_apply_one (v : E9) : (reflLin v) 1 = -(v 1) := by
  rw [reflLin_apply]
  show reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v) 1
    = -(((EuclideanSpace.equiv (Fin 9) ℝ) v) 1)
  rw [reflCoordFun_one]

theorem reflLin_coord_of_ne (v : E9) {i : Fin 9} (hi : i ≠ 1) : (reflLin v) i = v i := by
  rw [reflLin_apply]
  show reflCoordFun ((EuclideanSpace.equiv (Fin 9) ℝ) v) i
    = ((EuclideanSpace.equiv (Fin 9) ℝ) v) i
  rw [reflCoordFun_apply_of_ne _ hi]

/-- The reflection as a continuous linear equivalence. -/
def reflE : E9 ≃L[ℝ] E9 := reflLin.toContinuousLinearEquiv

theorem reflE_apply (v : E9) : reflE v = reflLin v := rfl

/-- The reflection preserves the half-space. -/
theorem reflLin_mem_halfSpace (v : E9) (hv : 0 ≤ v 0) : 0 ≤ (reflLin v) 0 := by
  rw [reflLin_apply_zero]; exact hv

/-- **The reflection of the half-space**, as a homeomorphism. -/
def reflHom : EuclideanHalfSpace 9 ≃ₜ EuclideanHalfSpace 9 where
  toFun y := ⟨reflLin y.1, reflLin_mem_halfSpace y.1 y.2⟩
  invFun y := ⟨reflLin y.1, reflLin_mem_halfSpace y.1 y.2⟩
  left_inv y := by
    refine Subtype.ext ?_
    show reflLin (reflLin y.1) = y.1
    exact reflLin.apply_symm_apply y.1
  right_inv y := by
    refine Subtype.ext ?_
    show reflLin (reflLin y.1) = y.1
    exact reflLin.apply_symm_apply y.1
  continuous_toFun := Continuous.subtype_mk
    ((reflE : E9 →L[ℝ] E9).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((reflE : E9 →L[ℝ] E9).continuous.comp continuous_subtype_val) _

/-- **The reflection of the half-space**, as an open partial homeomorphism. -/
def reflOph : OpenPartialHomeomorph (EuclideanHalfSpace 9) (EuclideanHalfSpace 9) :=
  reflHom.toOpenPartialHomeomorph

theorem reflOph_apply (y : EuclideanHalfSpace 9) : reflOph y = reflHom y := rfl

theorem reflOph_toFun_val (y : EuclideanHalfSpace 9) : (reflOph y).1 = reflLin y.1 := rfl

@[simp] theorem reflOph_source : reflOph.source = univ := rfl

@[simp] theorem reflOph_target : reflOph.target = univ := rfl

/-- The reflection of `ℝ⁹` as an open partial homeomorphism. -/
def reflOphE : OpenPartialHomeomorph E9 E9 :=
  (reflE.toHomeomorph).toOpenPartialHomeomorph

theorem reflOphE_apply (z : E9) : reflOphE z = reflLin z := rfl

/-! ## The bundled geometric data -/

/-- **The bundled hypotheses of the target.**  A level function `v : M → ℝⁿ` with a projection field
`P` onto its derivative along the level set `W = v⁻¹(0)`, local level data for `W`, a positively
cocycled coframing `(ℓ j, e j)`, and the positive-determinant (orientation) hypothesis on the ambient
atlas. -/
structure Cof (k n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M] where
  /-- the ambient atlas is positively oriented at interior points -/
  hMdet : ∀ (x y : M),
      x ∉ (𝓡∂ ((8 + k) + 1)).boundary M → y ∉ (𝓡∂ ((8 + k) + 1)).boundary M →
      ∀ z ∈ (extChartAt (𝓡∂ ((8 + k) + 1)) x).target ∩
          (extChartAt (𝓡∂ ((8 + k) + 1)) x).symm ⁻¹'
            (extChartAt (𝓡∂ ((8 + k) + 1)) y).source,
        z 0 > 0 →
        (0 : ℝ) < LinearMap.det
          ((fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
            (extChartAt (𝓡∂ ((8 + k) + 1)) y)
              ((extChartAt (𝓡∂ ((8 + k) + 1)) x).symm w)) z)
            : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →ₗ[ℝ]
              EuclideanSpace ℝ (Fin ((8 + k) + 1)))
  /-- the projection field -/
  P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
  hPgr : ∀ x, P x ∈ Work.PTGeometric.Gr n k
  /-- the level function -/
  v : M → EuclideanSpace ℝ (Fin n)
  hvsm : ContMDiff (𝓡∂ ((8 + k) + 1)) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
    ((⊤ : ENat) : WithTop ENat) v
  hPv : ∀ x, P x (v x) = v x
  /-- the level set -/
  W : Set M
  hWcl : IsClosed W
  hW : W = {x : M | v x = 0}
  hlink : ∀ x ∈ W, Set.range (mfderiv (𝓡∂ ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) v x) = {z | P x z = z}
  /-- the local level data -/
  L : LocalLevelData k M W
  /-- the coframing -/
  m : ℕ
  U : Fin m → Set M
  ℓ : Fin m → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)
  e : Fin m → M → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)
  hUopen : ∀ j, IsOpen (U j)
  hUcov : ∀ x ∈ W, ∃ j, x ∈ U j
  hℓe : ∀ j y, y ∈ U j → ∀ c : EuclideanSpace ℝ (Fin k),
    ℓ j (e j y c) = c ∧ P y (e j y c) = e j y c
  heinj : ∀ j y, y ∈ U j → Function.Injective (e j y)
  hpos : ∀ j j' y, y ∈ U j → y ∈ U j' →
    0 < LinearMap.det ((ℓ j').comp (e j y)
      : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))


open Work.PTGeometric.Lvl

namespace Cof

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [IsManifold (𝓡∂ ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]

/-- **The `Lvl` setup of the bundled data.** -/
abbrev S (D : Cof k n M) : Lvl.Setup k where
  M := M
  W := D.W
  isClosed_W := D.hWcl
  data := D.L

/-- **The chosen coframing index** at a point of the level set. -/
noncomputable def jx (D : Cof k n M) (w : D.S.Pre) : Fin D.m :=
  Classical.choose (D.hUcov w.1 w.2)

theorem mem_U_jx (D : Cof k n M) (w : D.S.Pre) : (w : M) ∈ D.U (D.jx w) :=
  Classical.choose_spec (D.hUcov w.1 w.2)

/-- The source of the *ambient* chart at `x`, as a set of points of `W`. -/
abbrev ambSrc (D : Cof k n M) (x : D.S.Pre) : Set D.S.Pre :=
  {z | (z : M) ∈ (chartAt (EuclideanHalfSpace ((8 + k) + 1)) (x : M)).source}

theorem ambSrc_open (D : Cof k n M) (x : D.S.Pre) : IsOpen (D.ambSrc x) :=
  (chartAt (EuclideanHalfSpace ((8 + k) + 1)) (x : M)).open_source.preimage
    continuous_subtype_val

theorem mem_ambSrc_self (D : Cof k n M) (x : D.S.Pre) : x ∈ D.ambSrc x :=
  mem_chart_source (EuclideanHalfSpace ((8 + k) + 1)) (x : M)

/-- At an interior centre the source is further restricted to the interior of `M`, so that the sign
analysis (which uses the ambient coorientation) applies at every point of the source. -/
abbrev intSrc (D : Cof k n M) (x : D.S.Pre) : Set M :=
  if (x : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M then Set.univ
  else (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).interior M

theorem intSrc_open (D : Cof k n M) (x : D.S.Pre) : IsOpen (D.intSrc x) := by
  rw [intSrc]; split_ifs with h
  · exact isOpen_univ
  · exact ModelWithCorners.isOpen_interior (n := ((⊤ : ENat) : WithTop ENat)) (by simp)

theorem mem_intSrc_of_interior (D : Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).interior M) :
    (x : M) ∈ D.intSrc x := by
  by_cases h : (x : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M
  · rw [intSrc]; exact if_pos h ▸ mem_univ _
  · rw [intSrc]; exact if_neg h ▸ hx

theorem mem_intSrc_of_mem (D : Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M) :
    (x : M) ∈ D.intSrc x := by
  rw [intSrc]; exact if_pos hx ▸ mem_univ _

theorem interior_of_mem_intSrc (D : Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M)
    {z : M} (hz : z ∈ D.intSrc x) :
    z ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).interior M := by
  rw [intSrc, if_neg hx] at hz; exact hz

theorem notMem_boundary_of_mem_intSrc (D : Cof k n M) (x : D.S.Pre)
    (hx : (x : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M)
    {z : M} (hz : z ∈ D.intSrc x) :
    z ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M := by
  rw [← ModelWithCorners.compl_interior]
  simp only [Set.mem_compl_iff, not_not]
  exact D.interior_of_mem_intSrc x hx hz

/-- **The open set whose connected component is the source of the new chart at `w`.** -/
abbrev goodSrc (D : Cof k n M) (w : D.S.Pre) : Set D.S.Pre :=
  ((D.S.chartSource w ∩ {z | (z : M) ∈ D.U (D.jx w)}) ∩ D.ambSrc w)
    ∩ {z | (z : M) ∈ D.intSrc w}

theorem mem_chartSource_self (D : Cof k n M) (w : D.S.Pre) : w ∈ D.S.chartSource w :=
  ⟨Work.PTGeometric.Lvl.Setup.mem_domChartAt_source D.S w,
    Work.PTGeometric.Lvl.Setup.chartZ_mem_chartW1 D.S w, D.S.data.mem_U w⟩

theorem goodSrc_open (D : Cof k n M) (w : D.S.Pre) : IsOpen (D.goodSrc w) :=
  (((Work.PTGeometric.Lvl.Setup.chartSource_open D.S w).inter
    ((D.hUopen (D.jx w)).preimage continuous_subtype_val)).inter
      (D.ambSrc_open w)).inter ((D.intSrc_open w).preimage continuous_subtype_val)

theorem mem_goodSrc_self (D : Cof k n M) (w : D.S.Pre) : w ∈ D.goodSrc w := by
  refine ⟨⟨⟨D.mem_chartSource_self w, ?_⟩, mem_ambSrc_self D w⟩, ?_⟩
  · simpa using mem_U_jx D w
  · by_cases hw : (w : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M
    · exact mem_intSrc_of_mem D w hw
    · refine mem_intSrc_of_interior D w ?_
      by_contra hc
      exact hw (by simpa only [← ModelWithCorners.compl_interior, Set.mem_compl_iff] using hc)

/-- **The source of the new chart at `w`**: the connected component of `w` in the intersection of the
`Lvl` chart source, the coframing neighbourhood of `w`, the source of the ambient chart at `w`, and
(if `w` is interior in `M`) the interior of `M`. -/
noncomputable def src (D : Cof k n M) (w : D.S.Pre) : Set D.S.Pre :=
  connectedComponentIn (D.goodSrc w) w

theorem src_subset (D : Cof k n M) (w : D.S.Pre) : D.src w ⊆ D.goodSrc w :=
  connectedComponentIn_subset _ _

theorem src_subset_chartSource (D : Cof k n M) (w : D.S.Pre) : D.src w ⊆ D.S.chartSource w :=
  fun z hz => (D.src_subset w hz).1.1.1

theorem src_subset_U (D : Cof k n M) (w : D.S.Pre) {z : D.S.Pre} (hz : z ∈ D.src w) :
    (z : M) ∈ D.U (D.jx w) :=
  (D.src_subset w hz).1.1.2

theorem src_subset_ambSrc (D : Cof k n M) (w : D.S.Pre) : D.src w ⊆ D.ambSrc w :=
  fun z hz => (D.src_subset w hz).1.2

theorem src_subset_intSrc (D : Cof k n M) (w : D.S.Pre) : D.src w ⊆ {z | (z : M) ∈ D.intSrc w} :=
  fun z hz => (D.src_subset w hz).2

theorem src_interior (D : Cof k n M) (w : D.S.Pre)
    (hw : (w : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M)
    {z : D.S.Pre} (hz : z ∈ D.src w) :
    (z : M) ∉ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M :=
  D.notMem_boundary_of_mem_intSrc w hw (D.src_subset_intSrc w hz)

theorem isPreconnected_src (D : Cof k n M) (w : D.S.Pre) : IsPreconnected (D.src w) :=
  isPreconnected_connectedComponentIn

theorem mem_src_self (D : Cof k n M) (w : D.S.Pre) : w ∈ D.src w :=
  mem_connectedComponentIn (mem_goodSrc_self D w)

theorem src_open (D : Cof k n M) (w : D.S.Pre) : IsOpen (D.src w) := by
  haveI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre :=
    Work.PTGeometric.Lvl.Setup.instChartedSpace (S := D.S)
  haveI : LocallyConnectedSpace D.S.Pre :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 9) D.S.Pre
  exact (goodSrc_open D w).connectedComponentIn

end Cof

end

end Work.ThomBordism.CofAtlas
