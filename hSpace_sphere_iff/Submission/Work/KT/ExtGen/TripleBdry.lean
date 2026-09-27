import Mathlib
import Submission.Work.KT.ExtGen.Triple
import Submission.Work.KT.ExtGen.Basic
import Submission.Work.KT.BallKFrame

/-!
# `Work.KT.ExtGen.TripleBdry` — the boundary-restriction algebra of `tripleAlg`

For finite-dimensional real normed spaces `V W Z` and boundary points `v₀ ∈ bdry V`,
`w₀ ∈ bdry W`, `z₀ ∈ bdry Z` we build

* the three chart slices `sliceV0`, `sliceW0`, `sliceZ0` of `tripleAlg V W Z` onto
  `prodAlg W Z`, `prodAlg V Z`, `prodAlg V W` (restriction to the three closed pieces of the
  boundary sphere `∂(D_{V×(W×Z)})`);
* the fibre product `bdryAlg` of the three `prodAlg`'s over their common (`Kpair`) restrictions,
  with the surjection `bdryProj : tripleAlg V W Z →ₐ[ℂ] bdryAlg` given by the three slices;
* the subalgebra `bdryKernel = bdryProj⁻¹(ℂ·1)`, which is the range of `tripleIncl`, and the
  augmentation `bdryEps` on it.

The restriction map `bdryProj` is used to run Milnor exactness (`k0_exact` (1)+(2)): it is
surjective, its kernel subalgebra is the range of `tripleIncl`, and invertible matrices over
`bdryAlg` lift explicitly to `tripleAlg`.
-/

namespace Work.KT.ExtGen

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

variable (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-! ## The three chart slices of `tripleAlg` -/

lemma sliceNormV0 (v0 : Ball V) (hv0 : v0 ∈ bdry V) (p : Ball (W × Z)) :
    ‖(((v0 : V), (p : W × Z)) : V × (W × Z))‖ ≤ 1 := by
  have hp : ‖(p : W × Z)‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp p.2
    rwa [dist_eq_norm, sub_zero] at this
  rw [Prod.norm_def]
  exact max_le (le_of_eq hv0) hp

lemma sliceMemV0 (v0 : Ball V) (hv0 : v0 ∈ bdry V) (p : Ball (W × Z)) :
    ((v0 : V), (p : W × Z)) ∈ Metric.closedBall (0 : V × (W × Z)) 1 :=
  Metric.mem_closedBall.mpr (by rw [dist_eq_norm, sub_zero]; exact sliceNormV0 V W Z v0 hv0 p)

/-- `(w,z) ↦ (v₀,w,z)`. -/
def sliceMapV0 (v0 : Ball V) (hv0 : v0 ∈ bdry V) : C(Ball (W × Z), Ball (V × (W × Z))) :=
  ⟨fun p => ⟨((v0 : V), (p : W × Z)), sliceMemV0 V W Z v0 hv0 p⟩, by fun_prop⟩

@[simp] lemma sliceMapV0_apply (v0 : Ball V) (hv0 : v0 ∈ bdry V) (p : Ball (W × Z)) :
    ((sliceMapV0 V W Z v0 hv0 p : Ball (V × (W × Z))) : V × (W × Z)) =
      ((v0 : V), (p : W × Z)) := rfl

lemma sliceNormW0 (w0 : Ball W) (hw0 : w0 ∈ bdry W) (p : Ball (V × Z)) :
    ‖(((p : V × Z).1, ((w0 : W), (p : V × Z).2)) : V × (W × Z))‖ ≤ 1 := by
  have hp : ‖(p : V × Z)‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp p.2
    rwa [dist_eq_norm, sub_zero] at this
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le ((norm_fst_le (p : V × Z)).trans hp)
    (max_le (le_of_eq hw0) ((norm_snd_le (p : V × Z)).trans hp))

lemma sliceMemW0 (w0 : Ball W) (hw0 : w0 ∈ bdry W) (p : Ball (V × Z)) :
    ((p : V × Z).1, ((w0 : W), (p : V × Z).2)) ∈ Metric.closedBall (0 : V × (W × Z)) 1 :=
  Metric.mem_closedBall.mpr (by rw [dist_eq_norm, sub_zero]; exact sliceNormW0 V W Z w0 hw0 p)

/-- `(v,z) ↦ (v,w₀,z)`. -/
def sliceMapW0 (w0 : Ball W) (hw0 : w0 ∈ bdry W) : C(Ball (V × Z), Ball (V × (W × Z))) :=
  ⟨fun p => ⟨((p : V × Z).1, ((w0 : W), (p : V × Z).2)), sliceMemW0 V W Z w0 hw0 p⟩,
    by fun_prop⟩

@[simp] lemma sliceMapW0_apply (w0 : Ball W) (hw0 : w0 ∈ bdry W) (p : Ball (V × Z)) :
    ((sliceMapW0 V W Z w0 hw0 p : Ball (V × (W × Z))) : V × (W × Z)) =
      ((p : V × Z).1, ((w0 : W), (p : V × Z).2)) := rfl

lemma sliceNormZ0 (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (p : Ball (V × W)) :
    ‖(((p : V × W).1, ((p : V × W).2, (z0 : Z))) : V × (W × Z))‖ ≤ 1 := by
  have hp : ‖(p : V × W)‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp p.2
    rwa [dist_eq_norm, sub_zero] at this
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le ((norm_fst_le (p : V × W)).trans hp)
    (max_le ((norm_snd_le (p : V × W)).trans hp) (le_of_eq hz0))

lemma sliceMemZ0 (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (p : Ball (V × W)) :
    ((p : V × W).1, ((p : V × W).2, (z0 : Z))) ∈ Metric.closedBall (0 : V × (W × Z)) 1 :=
  Metric.mem_closedBall.mpr (by rw [dist_eq_norm, sub_zero]; exact sliceNormZ0 V W Z z0 hz0 p)

/-- `(v,w) ↦ (v,w,z₀)`. -/
def sliceMapZ0 (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : C(Ball (V × W), Ball (V × (W × Z))) :=
  ⟨fun p => ⟨((p : V × W).1, ((p : V × W).2, (z0 : Z))), sliceMemZ0 V W Z z0 hz0 p⟩,
    by fun_prop⟩

@[simp] lemma sliceMapZ0_apply (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (p : Ball (V × W)) :
    ((sliceMapZ0 V W Z z0 hz0 p : Ball (V × (W × Z))) : V × (W × Z)) =
      ((p : V × W).1, ((p : V × W).2, (z0 : Z))) := rfl

/-- The slice `F ↦ ((w,z) ↦ F(v₀,w,z)) : tripleAlg V W Z → prodAlg W Z`. -/
def sliceV0 (v0 : Ball V) (hv0 : v0 ∈ bdry V) : tripleAlg V W Z →ₐ[ℂ] prodAlg W Z :=
  AlgHom.codRestrict
    ((pullAlg (sliceMapV0 V W Z v0 hv0)).comp (tripleAlg V W Z).val) (prodAlg W Z) (by
      intro F
      obtain ⟨h1, h2, h3⟩ := (mem_tripleAlg_iff V W Z).mp F.2
      refine ⟨fun z z' hz hz' hzz' => ?_, fun z z' hz hz' hzz' => ?_⟩
      · exact h2 _ _ (by simpa [sliceMapV0_apply] using hz) (by simpa [sliceMapV0_apply] using hz')
          (by simpa [sliceMapV0_apply] using hzz') rfl
      · exact h3 _ _ (by simpa [sliceMapV0_apply] using hz) (by simpa [sliceMapV0_apply] using hz')
          (by simpa [sliceMapV0_apply] using hzz') rfl)

@[simp] lemma sliceV0_apply (v0 : Ball V) (hv0 : v0 ∈ bdry V) (F : tripleAlg V W Z)
    (p : Ball (W × Z)) :
    (sliceV0 V W Z v0 hv0 F : C(Ball (W × Z), ℂ)) p
      = (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapV0 V W Z v0 hv0 p) := rfl

/-- The slice `F ↦ ((v,z) ↦ F(v,w₀,z)) : tripleAlg V W Z → prodAlg V Z`. -/
def sliceW0 (w0 : Ball W) (hw0 : w0 ∈ bdry W) : tripleAlg V W Z →ₐ[ℂ] prodAlg V Z :=
  AlgHom.codRestrict
    ((pullAlg (sliceMapW0 V W Z w0 hw0)).comp (tripleAlg V W Z).val) (prodAlg V Z) (by
      intro F
      obtain ⟨h1, h2, h3⟩ := (mem_tripleAlg_iff V W Z).mp F.2
      refine ⟨fun z z' hz hz' hzz' => ?_, fun z z' hz hz' hzz' => ?_⟩
      · exact h1 _ _ (by simpa [sliceMapW0_apply] using hz) (by simpa [sliceMapW0_apply] using hz')
          rfl (by simpa [sliceMapW0_apply] using hzz')
      · exact h3 _ _ (by simpa [sliceMapW0_apply] using hz) (by simpa [sliceMapW0_apply] using hz')
          rfl (by simpa [sliceMapW0_apply] using hzz'))

@[simp] lemma sliceW0_apply (w0 : Ball W) (hw0 : w0 ∈ bdry W) (F : tripleAlg V W Z)
    (p : Ball (V × Z)) :
    (sliceW0 V W Z w0 hw0 F : C(Ball (V × Z), ℂ)) p
      = (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapW0 V W Z w0 hw0 p) := rfl

/-- The slice `F ↦ ((v,w) ↦ F(v,w,z₀)) : tripleAlg V W Z → prodAlg V W`. -/
def sliceZ0 (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : tripleAlg V W Z →ₐ[ℂ] prodAlg V W :=
  AlgHom.codRestrict
    ((pullAlg (sliceMapZ0 V W Z z0 hz0)).comp (tripleAlg V W Z).val) (prodAlg V W) (by
      intro F
      obtain ⟨h1, h2, h3⟩ := (mem_tripleAlg_iff V W Z).mp F.2
      refine ⟨fun z z' hz hz' hzz' => ?_, fun z z' hz hz' hzz' => ?_⟩
      · exact h1 _ _ (by simpa [sliceMapZ0_apply] using hz) (by simpa [sliceMapZ0_apply] using hz')
          (by simpa [sliceMapZ0_apply] using hzz') rfl
      · exact h2 _ _ (by simpa [sliceMapZ0_apply] using hz) (by simpa [sliceMapZ0_apply] using hz')
          rfl (by simpa [sliceMapZ0_apply] using hzz'))

@[simp] lemma sliceZ0_apply (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (F : tripleAlg V W Z)
    (p : Ball (V × W)) :
    (sliceZ0 V W Z z0 hz0 F : C(Ball (V × W), ℂ)) p
      = (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapZ0 V W Z z0 hz0 p) := rfl

/-! ## Compatibility of the slices on the overlaps -/

lemma sliceV0_sliceW0_compat (v0 : Ball V) (hv0 : v0 ∈ bdry V)
    (w0 : Ball W) (hw0 : w0 ∈ bdry W) :
    (sliceW W Z w0 hw0).comp (sliceV0 V W Z v0 hv0)
      = (sliceW V Z v0 hv0).comp (sliceW0 V W Z w0 hw0) := by
  apply AlgHom.ext
  intro F
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  show (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapV0 V W Z v0 hv0 (pairPtD W Z w0 hw0 z))
      = (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapW0 V W Z w0 hw0 (pairPtD V Z v0 hv0 z))
  have h : sliceMapV0 V W Z v0 hv0 (pairPtD W Z w0 hw0 z)
      = sliceMapW0 V W Z w0 hw0 (pairPtD V Z v0 hv0 z) := Subtype.ext rfl
  rw [h]

lemma sliceV0_sliceZ0_compat (v0 : Ball V) (hv0 : v0 ∈ bdry V)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    (sliceV W Z z0 hz0).comp (sliceV0 V W Z v0 hv0)
      = (sliceW V W v0 hv0).comp (sliceZ0 V W Z z0 hz0) := by
  apply AlgHom.ext
  intro F
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  show (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapV0 V W Z v0 hv0 (pairPtC W Z z0 hz0 z))
      = (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapZ0 V W Z z0 hz0 (pairPtD V W v0 hv0 z))
  have h : sliceMapV0 V W Z v0 hv0 (pairPtC W Z z0 hz0 z)
      = sliceMapZ0 V W Z z0 hz0 (pairPtD V W v0 hv0 z) := Subtype.ext rfl
  rw [h]

lemma sliceW0_sliceZ0_compat (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    (sliceV V Z z0 hz0).comp (sliceW0 V W Z w0 hw0)
      = (sliceV V W w0 hw0).comp (sliceZ0 V W Z z0 hz0) := by
  apply AlgHom.ext
  intro F
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  show (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapW0 V W Z w0 hw0 (pairPtC V Z z0 hz0 z))
      = (F : C(Ball (V × (W × Z)), ℂ)) (sliceMapZ0 V W Z z0 hz0 (pairPtC V W w0 hw0 z))
  have h : sliceMapW0 V W Z w0 hw0 (pairPtC V Z z0 hz0 z)
      = sliceMapZ0 V W Z z0 hz0 (pairPtC V W w0 hw0 z) := Subtype.ext rfl
  rw [h]

/-! ## The boundary-restriction algebra -/

/-- The "left" comparison map on the triple product of the three `prodAlg`s. -/
def bdryL (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    (prodAlg W Z × prodAlg V Z × prodAlg V W) →ₐ[ℂ] (Kpair Z × Kpair W × Kpair V) :=
  ((sliceW W Z w0 hw0).comp (AlgHom.fst ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W))).prod
    (((sliceV W Z z0 hz0).comp (AlgHom.fst ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W))).prod
      ((sliceV V Z z0 hz0).comp ((AlgHom.fst ℂ (prodAlg V Z) (prodAlg V W)).comp
        (AlgHom.snd ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W)))))

/-- The "right" comparison map on the triple product of the three `prodAlg`s. -/
def bdryR (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    (prodAlg W Z × prodAlg V Z × prodAlg V W) →ₐ[ℂ] (Kpair Z × Kpair W × Kpair V) :=
  ((sliceW V Z v0 hv0).comp ((AlgHom.fst ℂ (prodAlg V Z) (prodAlg V W)).comp
      (AlgHom.snd ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W)))).prod
    (((sliceW V W v0 hv0).comp ((AlgHom.snd ℂ (prodAlg V Z) (prodAlg V W)).comp
        (AlgHom.snd ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W)))).prod
      ((sliceV V W w0 hw0).comp ((AlgHom.snd ℂ (prodAlg V Z) (prodAlg V W)).comp
        (AlgHom.snd ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W)))))

/-- The fibre product of the three chart slices over their common restrictions. -/
def bdryAlg (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    Subalgebra ℂ (prodAlg W Z × prodAlg V Z × prodAlg V W) where
  carrier := {p | bdryL V W Z v0 hv0 w0 hw0 z0 hz0 p = bdryR V W Z v0 hv0 w0 hw0 z0 hz0 p}
  mul_mem' := by
    rintro p q hp hq
    show bdryL V W Z v0 hv0 w0 hw0 z0 hz0 _ = bdryR V W Z v0 hv0 w0 hw0 z0 hz0 _
    rw [map_mul, map_mul, hp, hq]
  add_mem' := by
    rintro p q hp hq
    show bdryL V W Z v0 hv0 w0 hw0 z0 hz0 _ = bdryR V W Z v0 hv0 w0 hw0 z0 hz0 _
    rw [map_add, map_add, hp, hq]
  algebraMap_mem' := by
    intro c
    show bdryL V W Z v0 hv0 w0 hw0 z0 hz0 _ = bdryR V W Z v0 hv0 w0 hw0 z0 hz0 _
    rw [AlgHom.commutes, AlgHom.commutes]

/-- The three-slice restriction map `tripleAlg V W Z → bdryAlg`. -/
def bdryProj (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    tripleAlg V W Z →ₐ[ℂ] bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 :=
  AlgHom.codRestrict
    ((sliceV0 V W Z v0 hv0).prod ((sliceW0 V W Z w0 hw0).prod (sliceZ0 V W Z z0 hz0)))
    (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0) (by
      intro F
      show bdryL V W Z v0 hv0 w0 hw0 z0 hz0 _ = bdryR V W Z v0 hv0 w0 hw0 z0 hz0 _
      simp only [bdryL, bdryR, AlgHom.prod_apply, AlgHom.comp_apply, AlgHom.fst_apply,
        AlgHom.snd_apply]
      exact Prod.ext (congrArg (fun φ : tripleAlg V W Z →ₐ[ℂ] Kpair Z => φ F)
          (sliceV0_sliceW0_compat V W Z v0 hv0 w0 hw0))
        (Prod.ext (congrArg (fun φ : tripleAlg V W Z →ₐ[ℂ] Kpair W => φ F)
            (sliceV0_sliceZ0_compat V W Z v0 hv0 z0 hz0))
          (congrArg (fun φ : tripleAlg V W Z →ₐ[ℂ] Kpair V => φ F)
            (sliceW0_sliceZ0_compat V W Z w0 hw0 z0 hz0))))

@[simp] lemma bdryProj_apply (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W)
    (hw0 : w0 ∈ bdry W) (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (F : tripleAlg V W Z) :
    ((bdryProj V W Z v0 hv0 w0 hw0 z0 hz0 F : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0) :
        prodAlg W Z × prodAlg V Z × prodAlg V W)
      = ((sliceV0 V W Z v0 hv0 F), (sliceW0 V W Z w0 hw0 F), (sliceZ0 V W Z z0 hz0 F)) := rfl

/-- The "kernel" subalgebra `bdryProj⁻¹(ℂ·1) ⊆ tripleAlg`, i.e. the range of `tripleIncl`. -/
def bdryKernel (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : Subalgebra ℂ (tripleAlg V W Z) where
  carrier := {F | ∃ c : ℂ,
    bdryProj V W Z v0 hv0 w0 hw0 z0 hz0 F
      = algebraMap ℂ (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0) c}
  mul_mem' := by
    rintro F G ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    rw [map_mul, hc, hd, map_mul]
  add_mem' := by
    rintro F G ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    rw [map_add, hc, hd, map_add]
  algebraMap_mem' := by
    intro c
    exact ⟨c, AlgHom.commutes (bdryProj V W Z v0 hv0 w0 hw0 z0 hz0) c⟩

/-- The augmentation of `bdryKernel`: evaluation at a boundary point. -/
def bdryEps (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (y0 : Ball (V × (W × Z))) :
    bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] ℂ :=
  ((evalC y0).comp (tripleAlg V W Z).val).comp (bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0).val

@[simp] lemma bdryEps_apply (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W)
    (hw0 : w0 ∈ bdry W) (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) (y0 : Ball (V × (W × Z)))
    (u : bdryKernel V W Z v0 hv0 w0 hw0 z0 hz0) :
    bdryEps V W Z v0 hv0 w0 hw0 z0 hz0 y0 u
      = ((u : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ)) y0 := rfl


/-- The boundary algebra is nontrivial (it contains the constants, whose first component is `1 ≠ 0`
in `prodAlg W Z`). -/
instance instNontrivialBdryAlg (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : Nontrivial (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0) :=
  ⟨1, 0, by
    intro h
    have h1 : (1 : prodAlg W Z) = 0 :=
      congrArg (fun x : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 => x.1.1) h
    have h2 : ((1 : prodAlg W Z) : C(Ball (W × Z), ℂ)) (⟨0, by
        rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩ : Ball (W × Z))
        = ((0 : prodAlg W Z) : C(Ball (W × Z), ℂ)) (⟨0, by
        rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩ : Ball (W × Z)) :=
      congrArg (fun F : prodAlg W Z =>
        (F : C(Ball (W × Z), ℂ))
          (⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩ : Ball (W × Z))) h1
    simpa using h2⟩

end

end Work.KT.ExtGen
