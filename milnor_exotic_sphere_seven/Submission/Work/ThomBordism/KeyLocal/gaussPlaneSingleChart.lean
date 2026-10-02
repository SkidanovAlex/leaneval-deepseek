import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeNormDefs
import Submission.Work.Tubular.exists_euclidean_normalBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The Gauss plane lies in one chart of the normal Grassmannian

`Work.ThomBordism.KeyLocal.padComplChart i` is the chart of the oriented Grassmannian
`G̃r_k(ℝ^{k+10})` whose coordinates are the *complement* of the tangential chart coordinates
`i.2.1` of the normal datum (padded into `ℝ^{k+10}`).  The point of that chart is that it contains
the *whole* family of Gauss planes over the base set `ND.D.baseSet i` of the datum — which is the
statement proved here:

`gaussPlaneSingleChart`: for `x ∈ ND.D.baseSet i`, the `padComplChart i`-minor of the padded
σ-corrected normal frame `padGFrame E ND i x` does not vanish.

The mathematical content is pure linear algebra, and is the *dual* form of the hypothesis
`NormalData.baseSet_det` for the datum `i`:

* `baseSet_det` says that the **tangential** frame `frame E.e (coverChart i) x` projects
  isomorphically onto the `S = i.2.1` coordinates, equivalently that the tangent plane `T` meets
  the coordinate subspace `V_{Sᶜ} = span {e_z : z ∉ S}` trivially (dimensions `8 + k`).
* Since `ν_x = Tᗮ` has dimension `k`, the same argument applied to the orthogonal complement shows
  that `ν_x` meets the coordinate subspace `V_S = span {e_z : z ∈ S}` trivially, i.e. that the
  `Sᶜ`-coordinate projection is injective on `ν_x`.

The formalisation is `eq_zero_of_proj_eq_zero` below: if `w ⟂ span (range f)` and all `Sᶜ`
coordinates of `w` vanish then `w = 0`.  The proof writes `w = t + (w - t)` where `t ∈ span f` is
the vector with the same `S`-coordinates as `w` (which exists because `(frameMatrix S f).det ≠ 0`),
and evaluates `⟨w, w⟩ = ⟨w, t⟩ + ⟨w, w - t⟩ = 0 + 0`.

* `proj_padGFrame` is the padding computation: on the first `8 + k` coordinates, the padded frame
  agrees with the unpadded one (`padEuc_apply_ofLp`).
-/

namespace Work.ThomBordism.KeyLocal

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

noncomputable section

/-! ## The coordinate computation of the padding -/

/-- **The padding does not change the first `8 + k` coordinates**: for `z : Fin (8 + k)`, the
`z`-th coordinate of `padGFrame E ND i x a` (in the padded ambient `ℝ^{k+10}`) is the `z`-th
coordinate of `gframe E ND i x a`. -/
theorem proj_padGFrame {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) (a : Fin k) (z : Fin (8 + k)) :
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castLE (by omega : 8 + k ≤ k + 10) z))
        (padGFrame E ND i x a)
      = (EuclideanSpace.proj (𝕜 := ℝ) z) (Work.ThomBordism.Gauss.gframe E ND i x a) := by
  rw [EuclideanSpace.coe_proj, EuclideanSpace.coe_proj]
  exact Work.PTGeometric.padEuc_apply_ofLp k 10 (by norm_num)
    (Work.ThomBordism.Gauss.gframe E ND i x a) z

/-! ## The linear algebra of the complementary chart -/

/-- **The orthogonal complement of a plane that is a graph over the `S`-coordinates is a plane that
is a graph over the `Sᶜ`-coordinates.**  If `f` is a linearly independent `8`-frame whose
`S`-minor is invertible (`(frameMatrix S f).det ≠ 0`, i.e. `span (range f) ∩ V_{Sᶜ} = 0`), then a
vector `w ⟂ span (range f)` all of whose `Sᶜ`-coordinates vanish is zero. -/
theorem eq_zero_of_proj_eq_zero {k : ℕ}
    (f : Fin 8 → EuclideanSpace ℝ (Fin (8 + k))) (S : ChartIdx 8 k)
    (hdet : (frameMatrix S f).det ≠ 0) {w : EuclideanSpace ℝ (Fin (8 + k))}
    (hw : w ∈ (Submodule.span ℝ (Set.range f))ᗮ)
    (hproj : ∀ z : Fin (8 + k), z ∉ S.1 → (EuclideanSpace.proj (𝕜 := ℝ) z) w = 0) :
    w = 0 := by
  -- the coordinates of `w` and the vector `t ∈ span (range f)` with the same `S`-coordinates
  set u : Fin (8 + k) → ℝ := eucToFun (8 + k) w with hu
  set p : Fin 8 → ℝ := coordProj S u with hp
  set c : Fin 8 → ℝ := Matrix.mulVec (frameMatrix S f)⁻¹ p with hc
  set t : EuclideanSpace ℝ (Fin (8 + k)) := ∑ a, c a • f a with ht
  have hmat : (frameMatrix S f) * (frameMatrix S f)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hkey : Matrix.mulVec (frameMatrix S f) c = p := by
    rw [hc, Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]
  have htcoord : coordProj S (eucToFun (8 + k) t) = p := by
    rw [ht, ← coeffMap_eq_sum f c]
    show (coordProj S ∘ₗ coeffMap f) c = p
    rw [← toLin'_frameMatrix, Matrix.toLin'_apply]
    exact hkey
  have hpu : coordProj S u = p := by rw [hu, hp]
  -- `w - t` has vanishing `S`-coordinates
  have hcoord0 : ∀ z : Fin (8 + k), z ∈ S.1 → u z - (eucToFun (8 + k) t) z = 0 := by
    have h := (coordProj_eq_zero_iff S (u - eucToFun (8 + k) t)).mp (by
      rw [map_sub, hpu, htcoord, sub_self])
    exact fun z hz => h z hz
  have hin1 : inner ℝ w t = 0 := by
    have hmem : t ∈ Submodule.span ℝ (Set.range f) := by
      rw [ht]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))
    exact (Submodule.mem_orthogonal' _ w).mp hw t hmem
  -- `⟨w, w - t⟩ = 0`: the two factors have disjoint coordinate supports
  have hin2 : inner ℝ w (w - t) = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    refine Finset.sum_eq_zero fun z _ => ?_
    have hwt : (w - t).ofLp z = u z - (eucToFun (8 + k) t) z := by
      rw [WithLp.ofLp_sub, Pi.sub_apply, ← eucToFun_apply (8 + k) w,
        ← eucToFun_apply (8 + k) t, hu]
    by_cases hz : z ∈ S.1
    · rw [hwt, hcoord0 z hz, zero_mul]
    · have hproj' : w.ofLp z = 0 := by
        have hc' := congrFun (EuclideanSpace.coe_proj ℝ (i := z)) w
        rw [← hc']
        exact hproj z hz
      rw [hwt, hproj', mul_zero]
  have hww : inner ℝ w w = 0 := by
    have h1 : w = t + (w - t) := by abel
    nth_rewrite 2 [h1]
    rw [inner_add_right, hin1, hin2, add_zero]
  exact inner_self_eq_zero.mp hww

/-! ## The main statement -/

/-- **The Gauss plane over the base set of a datum lies in a single chart of `G̃r_k(ℝ^{k+10})`**:
the `padComplChart i`-minor of the padded normal frame is invertible for every
`x ∈ ND.D.baseSet i`.

This is the "one chart covers the whole family of Gauss planes" statement used by
`Work.ThomBordism.KeyLocal.tubeFrame`: on the part of the tube lying over `ND.D.baseSet i` the
Gauss plane is transverse to the coordinate subspace `V_{i.2.1}` complementary to the tangential
chart `i.2`, hence all of them are seen by the complementary chart `padComplChart i`. -/
theorem gaussPlaneSingleChart {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) :
    (Work.ThomBordism.Grassmann.frameMatrix (Work.ThomBordism.KeyLocal.padComplChart i)
      (Work.ThomBordism.Grassmann.padGFrame E ND i x)).det ≠ 0 := by
  rw [det_ne_zero_iff_ker]
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  -- the `Sᶜ`-coordinates of the frame vanish on the coefficient vector `v`
  have h0 : ∀ y ∈ (padComplChart i).1, coeffMap (padGFrame E ND i x) v y = 0 := by
    refine (coordProj_eq_zero_iff (padComplChart i) _).mp ?_
    show ((coordProj (padComplChart i)).comp (coeffMap (padGFrame E ND i x))) v = 0
    exact hv
  -- the combination of the (unpadded) frame with `v`: a vector of the normal space
  set w : EuclideanSpace ℝ (Fin (8 + k)) :=
    ∑ a, v a • Work.ThomBordism.Gauss.gframe E ND i x a with hwdef
  have hwproj : ∀ z : Fin (8 + k), z ∉ i.2.1 →
      (EuclideanSpace.proj (𝕜 := ℝ) z) w = 0 := by
    intro z hz
    have hzy : (Fin.castLE (by omega : 8 + k ≤ k + 10) z) ∈ (padComplChart i).1 :=
      Finset.mem_map.mpr ⟨z, Finset.mem_compl.mpr hz, rfl⟩
    have h1 := h0 _ hzy
    rw [coeffMap_apply] at h1
    have hlin : (EuclideanSpace.proj (𝕜 := ℝ) z) w
        = ∑ a, v a * (EuclideanSpace.proj (𝕜 := ℝ) z)
            (Work.ThomBordism.Gauss.gframe E ND i x a) := by
      rw [hwdef, map_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]
    rw [hlin, ← h1]
    exact Finset.sum_congr rfl fun a _ => by rw [proj_padGFrame]
  have hwmem : w ∈ Submodule.span ℝ (Set.range (Work.ThomBordism.Gauss.gframe E ND i x)) := by
    rw [hwdef]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))
  -- the span of the normal frame is `(span (range (tangent frame)))ᗮ`
  have hspan : Submodule.span ℝ (Set.range (Work.ThomBordism.Gauss.gframe E ND i x))
      = (Submodule.span ℝ (Set.range (frame E.e (coverChart i) x)))ᗮ := by
    rw [span_gframe E ND i hx, Work.Tubular.normalSpace,
      Work.Tubular.frame_span_eq_tangentSpace E (coverChart i)
        (ND.baseSet_sub i.1 i.2 x hx)]
  rw [hspan] at hwmem
  have hw0 : w = 0 := eq_zero_of_proj_eq_zero (frame E.e (coverChart i) x) i.2
    (ND.baseSet_det i.1 i.2 x hx) hwmem hwproj
  -- the frame is orthonormal, hence linearly independent
  have hLI := (Work.ThomBordism.Gauss.orthonormal_gframe E ND i hx).linearIndependent
  funext a
  exact (Fintype.linearIndependent_iff.mp hLI) v (by rw [← hwdef]; exact hw0) a

end

end Work.ThomBordism.KeyLocal
