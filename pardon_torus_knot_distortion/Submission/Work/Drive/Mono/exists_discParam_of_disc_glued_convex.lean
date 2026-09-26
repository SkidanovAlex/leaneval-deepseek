import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.exists_discParam_of_convex
import Submission.Work.Drive.Mono.exists_arcParam_of_isCompact_isPreconnected_sphere
import Submission.Work.Drive.Mono.sphereArc_extension
import Submission.Work.Drive.Mono.gaugeRadial_spec
import Submission.Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.SphereJordan.interior_range_eq_image
import Submission.Work.Smooth.Jordan.plane_schoenflies_convex
import Submission.Work.Smooth.Schoenflies.Unconditional

/-!
# Gluing a disc to a convex planar set along a common boundary arc

`Work.Drive.Mono.exists_discParam_of_disc_glued_convex`: the union of a topological disc `D` and a
compact convex set `C` with non-empty interior, meeting exactly along a common boundary arc and with
disjoint interiors, is again the image of the closed unit disc under an injective continuous map
whose boundary circle maps onto the frontier.

## Strategy

Everything is done in `ℂ` (the Jordan--Schoenflies machinery of the workspace lives there) and
transported to `EuclideanSpace ℝ (Fin 2)` at the very end along the linear isometry
`Complex.orthonormalBasisOneI.repr`.

Write `A = D ∩ C = frontier D ∩ frontier C` (the two sets are compact, so `frontier ⊆ set`).  The
hypothesis `interior D ∩ interior C = ∅` forces `A ≠ frontier D`: otherwise `frontier D ⊆ C` and
the classical fact that the bounded side of a Jordan curve lies in any closed convex set containing
the curve (`Work.Smooth.Jordan.plane_separation_V_subset_of_convex`, applied to the Jordan curve
`frontier D` and the Schoenflies datum for it, together with
`Work.Smooth.SphereJordan.range_eq_closure_of_boundary_eq`) gives `interior D ⊆ interior C`, which
is impossible.

Thus `A' = eD ⁻¹' A ⊆ S¹` is a compact preconnected subset of the circle, with at least two points
and non-empty complement, so
`Work.Drive.Mono.exists_arcParam_of_isCompact_isPreconnected_sphere` parametrises it by `[-1,1]`.
Composing with `eD` gives an embedded arc `γ` of `A`, and then `eC ⁻¹' γ` is an embedded arc of the
circle that is *matched* to `A'` by `Work.Drive.Mono.sphereArc_extension`: there is a homeomorphism
`g` of the circle with `g (u t) = eC⁻¹ (γ t)`.  Coning `g` to the disc
(`Work.Smooth.SphereJordan.discHomeo`) gives a homeomorphism `ψ` of the disc such that
`eC' = eC ∘ ψ` satisfies `eC' (u t) = γ t = eD (u t)`, i.e. `eD` and `eC'` agree precisely on the
common arc.

The `ℂ`-side is then glued with the two half-discs: a homeomorphism `h : 𝔻 ≅ H⁺` with `h (A') = J`
(the diameter of `H⁺`), built as `gaugeRadialInv ∘ ψ'` where `ψ'` (a cone of a circle
homeomorphism) moves `A'` to the image under the gauge map of the diameter, realises the union as
the image of the disc: the map is `eD ∘ ψ' ∘ gaugeRadialInv` on `H⁺` and `eC' ∘ ψ' ∘
gaugeRadialInv ∘ conj` on `H⁻`; these agree on `J` and their images are `D` and `C` meeting in `A`.
The frontier statement is then the invariance-of-domain fact that for an injective continuous disc
map the frontier of the image is the image of the boundary circle.
-/

open Set Metric
open scoped Topology

namespace Work.Drive.Mono

noncomputable section

/-! ## The two closed half-discs -/

/-- The closed upper half-disc of `ℂ`. -/
def halfDiscU : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 ∧ 0 ≤ z.im}

/-- The closed lower half-disc of `ℂ`. -/
def halfDiscL : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 ∧ z.im ≤ 0}

@[simp] theorem mem_halfDiscU {z : ℂ} : z ∈ halfDiscU ↔ ‖z‖ ≤ 1 ∧ 0 ≤ z.im := Iff.rfl

@[simp] theorem mem_halfDiscL {z : ℂ} : z ∈ halfDiscL ↔ ‖z‖ ≤ 1 ∧ z.im ≤ 0 := Iff.rfl

theorem norm_complex_ofReal (t : ℝ) : ‖(t : ℂ)‖ = |t| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]

theorem convex_halfDiscU : Convex ℝ halfDiscU := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · have h1 : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ :=
      calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
        _ = a * ‖x‖ + b * ‖y‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have h2 : a * ‖x‖ + b * ‖y‖ ≤ 1 := by
      nlinarith [ha, hb, hab, norm_nonneg x, norm_nonneg y, hx.1, hy.1]
    linarith
  · have h1 : (a • x + b • y).im = a * x.im + b * y.im := by
      rw [show a • x + b • y = (a : ℂ) * x + (b : ℂ) * y from rfl, Complex.add_im,
        Complex.mul_im, Complex.mul_im]
      simp
    rw [h1]
    nlinarith [ha, hb, hx.2, hy.2]

theorem convex_halfDiscL : Convex ℝ halfDiscL := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · have h1 : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ :=
      calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
        _ = a * ‖x‖ + b * ‖y‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have h2 : a * ‖x‖ + b * ‖y‖ ≤ 1 := by
      nlinarith [ha, hb, hab, norm_nonneg x, norm_nonneg y, hx.1, hy.1]
    linarith
  · have h1 : (a • x + b • y).im = a * x.im + b * y.im := by
      rw [show a • x + b • y = (a : ℂ) * x + (b : ℂ) * y from rfl, Complex.add_im,
        Complex.mul_im, Complex.mul_im]
      simp
    rw [h1]
    nlinarith [ha, hb, hx.2, hy.2]

theorem isClosed_halfDiscU : IsClosed halfDiscU := by
  have h : halfDiscU = Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 ≤ z.im} := by
    ext z
    rw [mem_halfDiscU, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [h]
  exact Metric.isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

theorem isClosed_halfDiscL : IsClosed halfDiscL := by
  have h : halfDiscL = Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | z.im ≤ 0} := by
    ext z
    rw [mem_halfDiscL, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [h]
  exact Metric.isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const)

theorem halfDiscU_subset_closedBall : halfDiscU ⊆ Metric.closedBall (0 : ℂ) 1 := fun z hz => by
  rw [Metric.mem_closedBall, dist_zero_right]; exact hz.1

theorem isBounded_halfDiscU : Bornology.IsBounded halfDiscU :=
  Metric.isBounded_closedBall.subset halfDiscU_subset_closedBall

theorem isCompact_halfDiscU : IsCompact halfDiscU :=
  isCompact_iff_isClosed_bounded.mpr ⟨isClosed_halfDiscU, isBounded_halfDiscU⟩

theorem mem_interior_halfDiscU : Complex.I / 2 ∈ interior halfDiscU := by
  refine mem_interior_iff_mem_nhds.mpr ?_
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 4)) ?_
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hnorm : ‖Complex.I / 2‖ = 1 / 2 := by
    rw [norm_div, Complex.norm_I]; norm_num
  have him : (Complex.I / 2).im = 1 / 2 := by simp
  refine ⟨?_, ?_⟩
  · have : ‖w‖ < 1 := by
      have hb : ‖w‖ ≤ ‖w - Complex.I / 2‖ + ‖Complex.I / 2‖ := by
        have h := norm_add_le (w - Complex.I / 2) (Complex.I / 2)
        rwa [sub_add_cancel] at h
      calc ‖w‖ ≤ ‖w - Complex.I / 2‖ + ‖Complex.I / 2‖ := hb
        _ < 1 / 4 + 1 / 2 := by rw [hnorm]; linarith
        _ = 3 / 4 := by norm_num
        _ < 1 := by norm_num
    linarith
  · have h1 : |(w - Complex.I / 2).im| ≤ ‖w - Complex.I / 2‖ := Complex.abs_im_le_norm _
    have h2 : w.im = (w - Complex.I / 2).im + 1 / 2 := by rw [Complex.sub_im, him]; ring
    have h3 : (0 : ℝ) ≤ (w - Complex.I / 2).im + 1 / 2 := by
      have := neg_le_abs (w - Complex.I / 2).im
      linarith [h1, hw]
    linarith [h2, h3]

theorem halfDiscU_inter_halfDiscL :
    halfDiscU ∩ halfDiscL = (fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    have him : z.im = 0 := le_antisymm h2.2 h1.2
    have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    refine ⟨z.re, ?_, hz.symm⟩
    have hle : ‖z‖ ≤ 1 := h1.1
    rw [hz, norm_complex_ofReal] at hle
    exact abs_le.mp hle
  · rintro ⟨t, ht, rfl⟩
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [norm_complex_ofReal]; exact ht'
    · simp
    · rw [norm_complex_ofReal]; exact ht'
    · simp

theorem mem_halfDiscU_of_im_zero {z : ℂ} (hz : z.im = 0) (h : ‖z‖ ≤ 1) : z ∈ halfDiscU :=
  ⟨h, by rw [hz]⟩

/-! ## A convex body of `ℂ` with non-empty interior is a disc -/

/-- The `ℂ`-form of `Work.Drive.Mono.exists_discParam_of_convex`. -/
theorem exists_discParam_of_convex_ℂ (K : Set ℂ) (hKc : IsCompact K)
    (hK : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℂ),
      Function.Injective e ∧ Set.range e = K ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K := by
  let φ : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have hφ : (φ.toHomeomorph : ℂ → EuclideanSpace ℝ (Fin 2)) = φ := rfl
  have hK'c : IsCompact (φ '' K) := hKc.image φ.continuous
  have hK'v : Convex ℝ (φ '' K) := hK.linear_image φ.toLinearMap
  have hsub : φ '' interior K ⊆ interior (φ '' K) := by
    rw [← hφ, ← Homeomorph.image_interior φ.toHomeomorph K]
  have hne' : (interior (φ '' K)).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨φ y, hsub ⟨y, hy, rfl⟩⟩
  obtain ⟨e', he'i, he'r, he'c⟩ :=
    Work.Drive.Mono.exists_discParam_of_convex (φ '' K) hK'c hK'v hne'
  refine ⟨⟨fun z => φ.symm (e' z), φ.symm.continuous.comp e'.continuous⟩, ?_, ?_, ?_⟩
  · intro a b hab; exact he'i (φ.symm.injective hab)
  · show Set.range (φ.symm ∘ ⇑e') = K
    rw [Set.range_comp, he'r]
    change φ.symm '' (φ '' K) = K
    rw [Set.image_image]; simp
  · show Set.range (fun θ : ℝ => φ.symm (e' (Work.CoreTopology.circlePoint θ))) = frontier K
    rw [show (fun θ : ℝ => φ.symm (e' (Work.CoreTopology.circlePoint θ)))
        = φ.symm ∘ (fun θ : ℝ => e' (Work.CoreTopology.circlePoint θ)) from rfl,
      Set.range_comp, he'c]
    change φ.symm '' frontier (φ '' K) = frontier K
    rw [show φ.symm = (φ.toHomeomorph.symm : EuclideanSpace ℝ (Fin 2) → ℂ) from rfl,
      Homeomorph.image_frontier]
    congr 1
    rw [Set.image_image]; simp

/-! ## Gluing two half-disc maps into a disc -/

/-- The unit circle of the closed unit disc is the range of `circlePoint`. -/
theorem range_circlePoint_closedBall :
    Set.range (fun θ : ℝ => Work.CoreTopology.circlePoint θ)
      = {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1} := by
  ext z
  constructor
  · rintro ⟨θ, rfl⟩
    simp [Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  · intro hz
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (z : ℂ)).mp hz
    refine ⟨θ, ?_⟩
    refine Subtype.ext ?_
    simpa [Work.CoreTopology.circlePoint_coe] using hθ

/-- **Invariance of domain at the boundary for an embedded disc**: the frontier of the image of the
closed unit disc under an injective continuous map is the image of the unit circle. -/
theorem frontier_range_of_injective_disc {f : C(Metric.closedBall (0 : ℂ) 1, ℂ)}
    (hf : Function.Injective f) :
    frontier (Set.range f) = f '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1} := by
  have hsub : interior (Set.range f)
      = f '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} := by
    rw [Work.Smooth.SphereJordan.interior_range_eq_openImage_plane hf]
    rfl
  have hclosed : IsClosed (Set.range f) := (isCompact_range f.continuous).isClosed
  rw [frontier, hclosed.closure_eq, hsub]
  ext y
  constructor
  · rintro ⟨⟨z, rfl⟩, hz⟩
    have hzle : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hz1 : ‖(z : ℂ)‖ = 1 := by
      rcases lt_or_eq_of_le hzle with h | h
      · exact absurd ⟨z, h, rfl⟩ hz
      · exact h
    exact ⟨z, hz1, rfl⟩
  · rintro ⟨z, hz1, rfl⟩
    refine ⟨⟨z, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := hf hwz
    rw [hwz'] at hw
    have hlt : ‖(z : ℂ)‖ < 1 := hw
    have heq : ‖(z : ℂ)‖ = 1 := hz1
    rw [heq] at hlt
    exact absurd hlt (by norm_num)

/-- **Two half-disc maps glued along their common diameter give a disc parametrisation.**  If `fU`
is a continuous injection on the closed upper half-disc with image `D`, `fL` one on the closed lower
half-disc with image `C`, the two agree on the diameter, and the images meet exactly in the image of
the diameter (`hglue`), then `D ∪ C` is again the image of the closed unit disc with the unit circle
mapping onto its frontier. -/
theorem exists_discParam_of_glued_halfDiscs (D C : Set ℂ) (fU fL : ℂ → ℂ)
    (hUc : ContinuousOn fU halfDiscU) (hUi : Set.InjOn fU halfDiscU) (hUr : fU '' halfDiscU = D)
    (hLc : ContinuousOn fL halfDiscL) (hLi : Set.InjOn fL halfDiscL) (hLr : fL '' halfDiscL = C)
    (hagree : ∀ t ∈ Set.Icc (-1 : ℝ) 1, fU (t : ℂ) = fL (t : ℂ))
    (hglue : fU '' (halfDiscU ∩ halfDiscL) = D ∩ C) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℂ), Function.Injective e ∧ Set.range e = D ∪ C ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (D ∪ C) := by
  classical
  have hJ : halfDiscU ∩ halfDiscL = (fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1 :=
    halfDiscU_inter_halfDiscL
  have hglueJ : fU '' ((fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1) = D ∩ C := by
    rw [← hJ]; exact hglue
  have hmemJ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (t : ℂ) ∈ halfDiscU ∩ halfDiscL := by
    intro t ht; rw [hJ]; exact ⟨t, ht, rfl⟩
  have hmemJU : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (t : ℂ) ∈ halfDiscU :=
    fun t ht => (hmemJ t ht).1
  have hmemJL : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (t : ℂ) ∈ halfDiscL :=
    fun t ht => (hmemJ t ht).2
  have hcov : Metric.closedBall (0 : ℂ) 1 = halfDiscU ∪ halfDiscL := by
    ext z
    rw [Metric.mem_closedBall, dist_zero_right, Set.mem_union, mem_halfDiscU, mem_halfDiscL]
    constructor
    · intro hz
      rcases lt_or_ge (0 : ℝ) z.im with h | h
      · exact Or.inl ⟨hz, le_of_lt h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact h1
      · exact h1
  let Ψ : ℂ → ℂ := fun z => if 0 ≤ z.im then fU z else fL z
  have hΨU : ∀ z ∈ halfDiscU, Ψ z = fU z := by
    intro z hz
    show (if 0 ≤ z.im then fU z else fL z) = fU z
    rw [if_pos hz.2]
  have hre_of_zero_im : ∀ z ∈ halfDiscL, z.im = 0 → Ψ z = fL z := by
    intro z hz him
    have hzJ : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    have hbound : |z.re| ≤ 1 := by
      have h := hz.1
      rw [hzJ, norm_complex_ofReal] at h
      exact h
    have hmem : z.re ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hbound
    rw [hΨU z (mem_halfDiscU_of_im_zero him hz.1), hzJ, hagree z.re hmem]
  have hΨL : ∀ z ∈ halfDiscL, Ψ z = fL z := by
    intro z hz
    rcases lt_or_eq_of_le hz.2 with hlt | heq
    · show (if 0 ≤ z.im then fU z else fL z) = fL z
      rw [if_neg (not_le.mpr hlt)]
    · exact hre_of_zero_im z hz heq
  have hcontU : ContinuousOn Ψ halfDiscU := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : halfDiscU.domRestrict Ψ = (fun z : halfDiscU => fU (z : ℂ)) := by
      funext z
      exact hΨU z z.2
    rw [heq]
    exact continuousOn_iff_continuous_domRestrict.mp hUc
  have hcontL : ContinuousOn Ψ halfDiscL := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : halfDiscL.domRestrict Ψ = (fun z : halfDiscL => fL (z : ℂ)) := by
      funext z
      exact hΨL z z.2
    rw [heq]
    exact continuousOn_iff_continuous_domRestrict.mp hLc
  have hcont : ContinuousOn Ψ (Metric.closedBall (0 : ℂ) 1) := by
    rw [hcov]
    exact hcontU.union_of_isClosed hcontL isClosed_halfDiscU isClosed_halfDiscL
  have hΨinj : Set.InjOn Ψ (Metric.closedBall (0 : ℂ) 1) := by
    intro z₁ hz₁ z₂ hz₂ heq
    have hn1 : ‖z₁‖ ≤ 1 := by
      have h := hz₁; rw [Metric.mem_closedBall, dist_zero_right] at h; exact h
    have hn2 : ‖z₂‖ ≤ 1 := by
      have h := hz₂; rw [Metric.mem_closedBall, dist_zero_right] at h; exact h
    have hu1 : 0 ≤ z₁.im → (z₁ ∈ halfDiscU ∧ Ψ z₁ = fU z₁) :=
      fun h => ⟨⟨hn1, h⟩, hΨU z₁ ⟨hn1, h⟩⟩
    have hl1 : z₁.im < 0 → (z₁ ∈ halfDiscL ∧ Ψ z₁ = fL z₁) :=
      fun h => ⟨⟨hn1, le_of_lt h⟩, hΨL z₁ ⟨hn1, le_of_lt h⟩⟩
    have hu2 : 0 ≤ z₂.im → (z₂ ∈ halfDiscU ∧ Ψ z₂ = fU z₂) :=
      fun h => ⟨⟨hn2, h⟩, hΨU z₂ ⟨hn2, h⟩⟩
    have hl2 : z₂.im < 0 → (z₂ ∈ halfDiscL ∧ Ψ z₂ = fL z₂) :=
      fun h => ⟨⟨hn2, le_of_lt h⟩, hΨL z₂ ⟨hn2, le_of_lt h⟩⟩
    rcases lt_or_ge z₁.im 0 with h1 | h1
    · rcases lt_or_ge z₂.im 0 with h2 | h2
      · obtain ⟨m1, e1⟩ := hl1 h1
        obtain ⟨m2, e2⟩ := hl2 h2
        rw [e1, e2] at heq
        exact hLi m1 m2 heq
      · obtain ⟨m1, e1⟩ := hl1 h1
        obtain ⟨m2, e2⟩ := hu2 h2
        rw [e1, e2] at heq
        have hmem : fU z₂ ∈ fU '' ((fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1) := by
          rw [hglueJ]
          exact ⟨by rw [← hUr]; exact ⟨z₂, m2, rfl⟩, by rw [← hLr]; exact ⟨z₁, m1, heq⟩⟩
        obtain ⟨x, hx, hFx⟩ := hmem
        obtain ⟨t, ht, hxt⟩ := hx
        have hFt : fU (t : ℂ) = fU z₂ := by rw [← hxt] at hFx; exact hFx
        have hz2 : z₂ = (t : ℂ) := hUi m2 (hmemJU t ht) hFt.symm
        have hz1 : z₁ = (t : ℂ) := by
          refine hLi m1 (hmemJL t ht) ?_
          rw [heq, ← hFt, hagree t ht]
        exact hz1.trans hz2.symm
    · rcases lt_or_ge z₂.im 0 with h2 | h2
      · obtain ⟨m1, e1⟩ := hu1 h1
        obtain ⟨m2, e2⟩ := hl2 h2
        rw [e1, e2] at heq
        have hmem : fU z₁ ∈ fU '' ((fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1) := by
          rw [hglueJ]
          exact ⟨by rw [← hUr]; exact ⟨z₁, m1, rfl⟩, by rw [← hLr]; exact ⟨z₂, m2, heq.symm⟩⟩
        obtain ⟨x, hx, hFx⟩ := hmem
        obtain ⟨t, ht, hxt⟩ := hx
        have hFt : fU (t : ℂ) = fU z₁ := by rw [← hxt] at hFx; exact hFx
        have hz1 : z₁ = (t : ℂ) := hUi m1 (hmemJU t ht) hFt.symm
        have hz2 : z₂ = (t : ℂ) := by
          refine hLi m2 (hmemJL t ht) ?_
          rw [← heq, ← hFt, hagree t ht]
        exact hz1.trans hz2.symm
      · obtain ⟨m1, e1⟩ := hu1 h1
        obtain ⟨m2, e2⟩ := hu2 h2
        rw [e1, e2] at heq
        exact hUi m1 m2 heq
  have himgU : Ψ '' halfDiscU = D := by
    rw [Set.image_congr hΨU, hUr]
  have himgL : Ψ '' halfDiscL = C := by
    rw [Set.image_congr hΨL, hLr]
  have hrange : Ψ '' (Metric.closedBall (0 : ℂ) 1) = D ∪ C := by
    rw [hcov, Set.image_union, himgU, himgL]
  let E : C(Metric.closedBall (0 : ℂ) 1, ℂ) :=
    ⟨fun z => Ψ (z : ℂ), continuousOn_iff_continuous_domRestrict.mp hcont⟩
  have hErange : Set.range E = D ∪ C := by
    show Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => Ψ (z : ℂ)) = D ∪ C
    rw [← hrange, Set.image_eq_range]
  have hEinj : Function.Injective E := fun a b hab => Subtype.ext (hΨinj a.2 b.2 hab)
  refine ⟨E, hEinj, hErange, ?_⟩
  have hfront := frontier_range_of_injective_disc hEinj
  have hcircle : Set.range (fun θ : ℝ => E (Work.CoreTopology.circlePoint θ))
      = E '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1} := by
    rw [show Set.range (fun θ : ℝ => E (Work.CoreTopology.circlePoint θ))
          = E '' Set.range (fun θ : ℝ => Work.CoreTopology.circlePoint θ) from
        Set.range_comp E (fun θ : ℝ => Work.CoreTopology.circlePoint θ),
      range_circlePoint_closedBall]
  rw [hcircle, ← hfront, hErange]

/-! ## The complex-plane form of the main theorem -/

/-- The inclusion of the unit circle into the closed unit disc. -/
def sphToDisc (z : Metric.sphere (0 : ℂ) 1) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨(z : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := z.2
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact le_of_eq h⟩

@[simp] theorem sphToDisc_coe (z : Metric.sphere (0 : ℂ) 1) : (sphToDisc z : ℂ) = (z : ℂ) := rfl

theorem continuous_sphToDisc : Continuous sphToDisc :=
  Continuous.subtype_mk continuous_subtype_val _

theorem injective_sphToDisc : Function.Injective sphToDisc :=
  fun a b h => Subtype.ext (show (a : ℂ) = (b : ℂ) from
    congrArg (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ)) h)

/-- Complex conjugation. -/
def cjn (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

@[simp] theorem cjn_re (z : ℂ) : (cjn z).re = z.re := rfl

@[simp] theorem cjn_im (z : ℂ) : (cjn z).im = -z.im := rfl

theorem cjn_cjn (z : ℂ) : cjn (cjn z) = z := by
  refine Complex.ext ?_ ?_ <;> simp [cjn]

theorem norm_cjn (z : ℂ) : ‖cjn z‖ = ‖z‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  rw [Complex.normSq_apply, Complex.normSq_apply, cjn_re, cjn_im]
  ring

theorem cjn_ofReal (r : ℝ) : cjn (r : ℂ) = r := by
  refine Complex.ext ?_ ?_ <;> simp [cjn]

theorem cjn_injective : Function.Injective cjn := fun a b h => by
  have := congrArg cjn h
  rwa [cjn_cjn, cjn_cjn] at this

theorem continuous_cjn : Continuous cjn := by
  have h : cjn = fun z : ℂ => (z.re : ℂ) - Complex.I * (z.im : ℂ) := by
    funext z
    refine Complex.ext ?_ ?_ <;>
      simp [cjn, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
  rw [h]
  fun_prop

/-- **The complex-plane form of `exists_discParam_of_disc_glued_convex`.** -/
theorem exists_discParam_of_disc_glued_convex_ℂ (D C : Set ℂ)
    (hD : ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℂ),
      Function.Injective e ∧ Set.range e = D ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier D)
    (hreg : D = closure (interior D))
    (hCc : Convex ℝ C) (hCcl : IsCompact C) (hCne : (interior C).Nonempty)
    (hsub : D ∩ C ⊆ frontier D ∩ frontier C)
    (hne : ∃ x : ℂ, x ∈ D ∩ C ∧ ∃ y : ℂ, y ∈ D ∩ C ∧ x ≠ y)
    (hint : interior D ∩ interior C = ∅)
    (hconn : IsPreconnected (D ∩ C)) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℂ), Function.Injective e ∧ Set.range e = D ∪ C ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (D ∪ C) := by
  classical
  obtain ⟨eD, heDi, heDr, heDfr⟩ := hD
  obtain ⟨eC, heCi, heCr, heCfr⟩ := exists_discParam_of_convex_ℂ C hCcl hCc hCne
  have hDcomp : IsCompact D := heDr ▸ isCompact_range eD.continuous
  have hCcomp : IsCompact C := heCr ▸ isCompact_range eC.continuous
  have hDclosed : IsClosed D := hDcomp.isClosed
  have hCclosed : IsClosed C := hCcomp.isClosed
  have hfrontD_sub : frontier D ⊆ D := frontier_subset_iff_isClosed.mpr hDclosed
  have hfrontC_sub : frontier C ⊆ C := frontier_subset_iff_isClosed.mpr hCclosed
  have hAclosed : IsClosed (D ∩ C) := hDclosed.inter hCclosed
  have hAeq : D ∩ C = frontier D ∩ frontier C := by
    refine subset_antisymm hsub ?_
    exact inter_subset_inter hfrontD_sub hfrontC_sub
  -- the interior of `D` is the image of the open disc
  have hintD : interior D = Work.Smooth.SphereJordan.openImage eD := by
    rw [← heDr]
    exact Work.Smooth.SphereJordan.interior_range_eq_openImage_plane heDi
  have hIntDne : (interior D).Nonempty := by
    refine ⟨eD ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩, ?_⟩
    rw [hintD]
    exact ⟨⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩, by simp, rfl⟩
  -- `A ≠ frontier D`
  have hAneD : D ∩ C ≠ frontier D := by
    intro hA
    have htrace : (Work.Smooth.SphereJordan.discCurve eD).trace = frontier D := by
      rw [Work.Smooth.Jordan.PlaneCurve.trace]
      exact heDfr
    have htrace_sub : (Work.Smooth.SphereJordan.discCurve eD).trace ⊆ C := by
      rw [htrace, ← hA]; exact inter_subset_right
    obtain ⟨S⟩ := Work.Smooth.Schoenflies.classicalInput (Work.Smooth.SphereJordan.discCurve eD)
      (Work.Smooth.SphereJordan.discCurve_isSimple heDi)
    have hVsub : S.V ⊆ C :=
      Work.Smooth.Jordan.plane_separation_V_subset_of_convex S.toPlaneSeparation hCc hCclosed
        htrace_sub
    have hopen : Work.Smooth.SphereJordan.openImage eD = S.V :=
      (Work.Smooth.SphereJordan.range_eq_closure_of_boundary_eq S heDi
        (fun θ => (Work.Smooth.SphereJordan.discCurve_apply eD θ).symm)).2
    have hIntDsubIntC : interior D ⊆ interior C := by
      refine interior_maximal ?_ isOpen_interior
      rw [hintD, hopen]; exact hVsub
    obtain ⟨x, hx⟩ := hIntDne
    have hx' : x ∈ interior D ∩ interior C := ⟨hx, hIntDsubIntC hx⟩
    rw [hint] at hx'
    exact hx'
  -- the arc `A'` on the unit circle
  let Φ : Metric.sphere (0 : ℂ) 1 → ℂ := fun z => eD (sphToDisc z)
  have hΦc : Continuous Φ := eD.continuous.comp continuous_sphToDisc
  have hΦinj : Function.Injective Φ := fun a b h => injective_sphToDisc (heDi h)
  have hΦrange : Set.range Φ = frontier D := by
    have hsphere_range : Set.range sphToDisc =
        {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        have h := w.2
        rwa [Metric.mem_sphere, dist_zero_right] at h
      · intro hz
        have hz1 : ‖(z : ℂ)‖ = 1 := hz
        refine ⟨⟨(z : ℂ), ?_⟩, Subtype.ext rfl⟩
        rw [Metric.mem_sphere, dist_eq_norm]
        simpa using hz1
    have h1 : Set.range Φ = Set.range (fun θ : ℝ => eD (Work.CoreTopology.circlePoint θ)) := by
      have h2 : Set.range Φ = eD '' Set.range sphToDisc := by
        rw [show Φ = eD ∘ sphToDisc from rfl, Set.range_comp]
      have h3 : {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1}
          = Set.range (fun θ : ℝ => Work.CoreTopology.circlePoint θ) := by
        ext z
        constructor
        · intro hz1
          obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz1
          exact ⟨θ, hθ⟩
        · rintro ⟨θ, rfl⟩
          show ‖(Work.CoreTopology.circlePoint θ : ℂ)‖ = 1
          rw [Work.CoreTopology.circlePoint_coe]
          exact Complex.norm_exp_ofReal_mul_I θ
      rw [h2, hsphere_range, h3]
      ext y
      constructor
      · rintro ⟨z, ⟨θ, rfl⟩, rfl⟩
        exact ⟨θ, rfl⟩
      · rintro ⟨θ, rfl⟩
        exact ⟨Work.CoreTopology.circlePoint θ, ⟨θ, rfl⟩, rfl⟩
    rw [h1, heDfr]
  let A' : Set (Metric.sphere (0 : ℂ) 1) := Φ ⁻¹' (D ∩ C)
  have hΦA' : Φ '' A' = D ∩ C := by
    show Φ '' (Φ ⁻¹' (D ∩ C)) = D ∩ C
    rw [Set.image_preimage_eq_inter_range, hΦrange]
    exact Set.inter_eq_left.mpr (hAeq ▸ inter_subset_left)
  have hA'closed : IsClosed A' := hAclosed.preimage hΦc
  have hA'compact : IsCompact A' := hA'closed.isCompact
  have hA'preconn : IsPreconnected A' := by
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u v hu hv huv huvdisj
    have hKu : IsCompact (u ∩ A') := by rw [Set.inter_comm]; exact hA'compact.inter hu.isCompact
    have hKv : IsCompact (v ∩ A') := by rw [Set.inter_comm]; exact hA'compact.inter hv.isCompact
    have hKu' : IsCompact (Φ '' (u ∩ A')) := hKu.image hΦc
    have hKv' : IsCompact (Φ '' (v ∩ A')) := hKv.image hΦc
    have hcov : D ∩ C = Φ '' (u ∩ A') ∪ Φ '' (v ∩ A') := by
      rw [← Set.image_union, ← hΦA']
      congr 1
      refine subset_antisymm ?_ ?_
      · intro x hxA'
        rcases huv hxA' with h | h
        · exact Or.inl ⟨h, hxA'⟩
        · exact Or.inr ⟨h, hxA'⟩
      · rintro x (⟨-, hxA'⟩ | ⟨-, hxA'⟩)
        · exact hxA'
        · exact hxA'
    have hdisj : (D ∩ C) ∩ (Φ '' (u ∩ A') ∩ Φ '' (v ∩ A')) = ∅ := by
      by_contra hne
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨⟨hyD, hyC⟩, hyu, hyv⟩ := hy
      obtain ⟨a, ha, hba⟩ := hyu
      obtain ⟨b, hb, hbb⟩ := hyv
      have hab : a = b := hΦinj (hba.trans hbb.symm)
      subst hab
      have hmem : a ∈ A' ∩ (u ∩ v) := ⟨ha.2, ha.1, hb.1⟩
      rw [huvdisj] at hmem
      exact hmem
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconn) _ _
      hKu'.isClosed hKv'.isClosed hcov.le hdisj with hkey | hkey
    · left
      intro z hz
      have hz' : Φ z ∈ Φ '' (u ∩ A') := hkey (by rw [← hΦA']; exact ⟨z, hz, rfl⟩)
      obtain ⟨w, hw, hwz⟩ := hz'
      rw [← hΦinj hwz]; exact hw.1
    · right
      intro z hz
      have hz' : Φ z ∈ Φ '' (v ∩ A') := hkey (by rw [← hΦA']; exact ⟨z, hz, rfl⟩)
      obtain ⟨w, hw, hwz⟩ := hz'
      rw [← hΦinj hwz]; exact hw.1
  have hA'2 : ∃ p ∈ A', ∃ q ∈ A', p ≠ q := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    obtain ⟨px, hpx, hpxx⟩ : ∃ z ∈ A', Φ z = x := by
      have h : x ∈ Φ '' A' := by rw [hΦA']; exact hx
      exact h
    obtain ⟨py, hpy, hpyy⟩ : ∃ z ∈ A', Φ z = y := by
      have h : y ∈ Φ '' A' := by rw [hΦA']; exact hy
      exact h
    exact ⟨px, hpx, py, hpy, fun h => hxy (by rw [← hpxx, ← hpyy, h])⟩
  have hA'ne : ∃ p : Metric.sphere (0 : ℂ) 1, p ∉ A' := by
    by_contra hcon
    push Not at hcon
    have hthis : Φ '' A' = frontier D := by
      rw [show A' = Set.univ from Set.eq_univ_of_forall hcon, Set.image_univ, hΦrange]
    rw [hΦA'] at hthis
    exact hAneD hthis
  obtain ⟨u, huc, hui, huimg, -, -, -⟩ :=
    Work.Drive.Mono.exists_arcParam_of_isCompact_isPreconnected_sphere A' hA'compact
      hA'preconn hA'2 hA'ne
  -- clamp the parametrisation to `[-1,1]`, so that all its values lie in `A'`
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  let uc : ℝ → Metric.sphere (0 : ℂ) 1 := fun t => u (Set.projIcc (-1 : ℝ) 1 hle t)
  have huc_proj : ∀ t : ℝ, uc (Set.projIcc (-1 : ℝ) 1 hle t) = uc t := by
    intro t
    show u (Set.projIcc (-1 : ℝ) 1 hle ↑(Set.projIcc (-1 : ℝ) 1 hle t)) =
      u (Set.projIcc (-1 : ℝ) 1 hle t)
    rw [Set.projIcc_of_mem hle (Set.projIcc (-1 : ℝ) 1 hle t).2]
  have huc_c : Continuous uc :=
    huc.comp (continuous_subtype_val.comp continuous_projIcc)
  have huc_i : Set.InjOn uc (Set.Icc (-1 : ℝ) 1) := by
    intro s hs t ht h
    have h1 : u (Set.projIcc (-1 : ℝ) 1 hle s) = u (Set.projIcc (-1 : ℝ) 1 hle t) := h
    rw [Set.projIcc_of_mem hle hs, Set.projIcc_of_mem hle ht] at h1
    exact hui hs ht h1
  have huc_img : uc '' Set.Icc (-1 : ℝ) 1 = A' := by
    rw [← huimg]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(Set.projIcc (-1 : ℝ) 1 hle t : ℝ), (Set.projIcc (-1 : ℝ) 1 hle t).2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by
        show u (Set.projIcc (-1 : ℝ) 1 hle t) = u t
        rw [Set.projIcc_of_mem hle ht]⟩
  -- the arc `γ` of `A` traced by `uc`
  let γ : ℝ → ℂ := fun t => Φ (uc t)
  have hγc : Continuous γ := hΦc.comp huc_c
  have hγinj : Set.InjOn γ (Set.Icc (-1 : ℝ) 1) :=
    fun s hs t ht h => huc_i hs ht (hΦinj h)
  have hγimg : γ '' Set.Icc (-1 : ℝ) 1 = D ∩ C := by
    rw [show γ '' Set.Icc (-1 : ℝ) 1 = Φ '' (uc '' Set.Icc (-1 : ℝ) 1) from by
        rw [Set.image_image], huc_img, hΦA']
  have hγmem : ∀ t : ℝ, γ t ∈ D ∩ C := fun t => by
    rw [← hγimg]
    exact ⟨(Set.projIcc (-1 : ℝ) 1 hle t : ℝ), (Set.projIcc (-1 : ℝ) 1 hle t).2,
      congrArg Φ (huc_proj t)⟩
  have huc_A' : ∀ t : ℝ, uc t ∈ A' := by
    intro t
    show Φ (uc t) ∈ D ∩ C
    rw [← hγimg]
    exact ⟨(Set.projIcc (-1 : ℝ) 1 hle t : ℝ), (Set.projIcc (-1 : ℝ) 1 hle t).2,
      congrArg Φ (huc_proj t)⟩
  have hγD : ∀ t : ℝ, γ t ∈ frontier D := fun t => (hAeq ▸ hγmem t).1
  have hγC : ∀ t : ℝ, γ t ∈ frontier C := fun t => (hAeq ▸ hγmem t).2
  have hγCmem : ∀ t : ℝ, γ t ∈ C := fun t => hfrontC_sub (hγC t)
  -- the disc homeomorphism of `C`
  let φC : Metric.closedBall (0 : ℂ) 1 → ↥C := fun z => ⟨eC z, by rw [← heCr]; exact ⟨z, rfl⟩⟩
  have hφCc : Continuous φC := Continuous.subtype_mk eC.continuous _
  have hφCbij : Function.Bijective φC := by
    refine ⟨fun a b h => heCi (congrArg Subtype.val h), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := show y ∈ Set.range eC from by rw [heCr]; exact hy
    exact ⟨z, Subtype.ext hz⟩
  let eCh : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥C :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φC hφCbij) hφCc
  have heCh : ∀ z, ((eCh z : ↥C) : ℂ) = eC z := fun z => rfl
  have heChs : ∀ z : ↥C, eC (eCh.symm z) = (z : ℂ) :=
    fun z => (heCh (eCh.symm z)).symm.trans (congrArg Subtype.val (eCh.apply_symm_apply z))
  -- the arc `eC⁻¹ γ` of the circle
  have hpre_sph : ∀ (z : Metric.closedBall (0 : ℂ) 1) (y : ℂ), y ∈ frontier C → eC z = y →
      ‖(z : ℂ)‖ = 1 := by
    intro z y hy hzy
    have hy' : y ∈ Set.range (fun θ : ℝ => eC (Work.CoreTopology.circlePoint θ)) := by
      rw [heCfr]; exact hy
    obtain ⟨θ, hθ⟩ := hy'
    have hθ' : eC (Work.CoreTopology.circlePoint θ) = y := hθ
    have hz : z = Work.CoreTopology.circlePoint θ := heCi (by rw [hzy, hθ'])
    rw [hz]
    show ‖(Work.CoreTopology.circlePoint θ : ℂ)‖ = 1
    rw [Work.CoreTopology.circlePoint_coe]
    exact Complex.norm_exp_ofReal_mul_I θ
  let wfun : ℝ → Metric.closedBall (0 : ℂ) 1 := fun t => eCh.symm ⟨γ t, hγCmem t⟩
  have hwc_fun : Continuous wfun :=
    eCh.symm.continuous.comp (Continuous.subtype_mk hγc hγCmem)
  have heC_wfun : ∀ t : ℝ, eC (wfun t) = γ t := fun t => heChs ⟨γ t, hγCmem t⟩
  have hwfunsp : ∀ t : ℝ, ‖(wfun t : ℂ)‖ = 1 := fun t =>
    hpre_sph (wfun t) (γ t) (hγC t) (heC_wfun t)
  let w : ℝ → Metric.sphere (0 : ℂ) 1 := fun t =>
    ⟨(wfun t : ℂ), by rw [Metric.mem_sphere, dist_zero_right]; exact hwfunsp t⟩
  have hwc : Continuous w := Continuous.subtype_mk (continuous_subtype_val.comp hwc_fun) _
  have hwcoe : ∀ t : ℝ, (sphToDisc (w t) : Metric.closedBall (0 : ℂ) 1) = wfun t :=
    fun t => Subtype.ext rfl
  have hwi : Set.InjOn w (Set.Icc (-1 : ℝ) 1) := by
    intro s hs t ht h
    have h1 : wfun s = wfun t :=
      Subtype.ext (congrArg (fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ)) h)
    have h2 : (⟨γ s, hγCmem s⟩ : ↥C) = ⟨γ t, hγCmem t⟩ := eCh.symm.injective h1
    exact hγinj hs ht (congrArg Subtype.val h2)
  obtain ⟨g₁, hg₁⟩ := Work.Drive.Mono.sphereArc_extension huc_c hwc huc_i hwi
  let ψ : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
    Work.Smooth.SphereJordan.discHomeo g₁
  let eC' : Metric.closedBall (0 : ℂ) 1 → ℂ := fun z => eC (ψ z)
  have hpsi_sphere : ∀ x : Metric.sphere (0 : ℂ) 1,
      ((ψ (sphToDisc x) : Metric.closedBall (0 : ℂ) 1) : ℂ) = (g₁ x : ℂ) := by
    intro x
    show Work.Smooth.SphereJordan.radialMap g₁
      ((sphToDisc x : Metric.closedBall (0 : ℂ) 1) : ℂ) = (g₁ x : ℂ)
    rw [sphToDisc_coe]
    exact Work.Smooth.SphereJordan.radialMap_coe_sphere g₁ x
  have hψsph : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ψ (sphToDisc (uc t)) = sphToDisc (w t) := by
    intro t ht
    refine Subtype.ext ?_
    rw [hpsi_sphere (uc t), sphToDisc_coe]
    exact congrArg Subtype.val (hg₁ t ht)
  have hψA' : ψ '' (sphToDisc '' A') = eC ⁻¹' (D ∩ C) := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      have hx' : x ∈ uc '' Set.Icc (-1 : ℝ) 1 := by rwa [huc_img]
      obtain ⟨t, ht, rfl⟩ := hx'
      show eC (ψ (sphToDisc (uc t))) ∈ D ∩ C
      rw [hψsph t ht, hwcoe, heC_wfun]
      exact hγmem t
    · intro hz
      have hz' : eC z ∈ γ '' Set.Icc (-1 : ℝ) 1 := by rw [hγimg]; exact hz
      obtain ⟨t, ht, htz⟩ := hz'
      have hzt : z = wfun t := heCi (by rw [← htz, heC_wfun t])
      refine ⟨sphToDisc (uc t), ⟨uc t, ?_, rfl⟩, ?_⟩
      · rw [← huc_img]; exact ⟨t, ht, rfl⟩
      · rw [hψsph t ht, hwcoe]
        exact hzt.symm
  have hψA'_iff : ∀ z : Metric.closedBall (0 : ℂ) 1,
      eC (ψ z) ∈ D ∩ C ↔ z ∈ sphToDisc '' A' := by
    intro z
    constructor
    · intro hz
      have h : ψ z ∈ ψ '' (sphToDisc '' A') := by
        rw [hψA']
        exact hz
      obtain ⟨y, hy, hyz⟩ := h
      exact ψ.injective hyz ▸ hy
    · intro hz
      have h : ψ z ∈ ψ '' (sphToDisc '' A') := ⟨z, hz, rfl⟩
      rw [hψA'] at h
      exact h
  have hagreeA'sph : ∀ x : Metric.sphere (0 : ℂ) 1, x ∈ A' →
      eC' (sphToDisc x) = eD (sphToDisc x) := by
    intro x hx
    have hx' : x ∈ uc '' Set.Icc (-1 : ℝ) 1 := by rwa [huc_img]
    obtain ⟨t, ht, rfl⟩ := hx'
    show eC (ψ (sphToDisc (uc t))) = eD (sphToDisc (uc t))
    rw [hψsph t ht, hwcoe, heC_wfun]
  -- the half-disc model: the gauge map of the upper half-disc
  let p₀ : ℂ := Complex.I / 2
  obtain ⟨hφc, -, hφmem, hφsph, hφleft, hφright, hφinvK, -⟩ :=
    gaugeRadial_spec (K := halfDiscU) (p := p₀) convex_halfDiscU isClosed_halfDiscU
      isBounded_halfDiscU mem_interior_halfDiscU
  have hφinj : Function.Injective (gaugeRadial halfDiscU p₀) := by
    intro a b h
    have := congrArg (gaugeRadialInv halfDiscU p₀) h
    rwa [hφleft, hφleft] at this
  have hzU_of_mem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (t : ℂ) ∈ halfDiscU := by
    intro t ht
    exact ⟨by rw [norm_complex_ofReal]; exact abs_le.mpr ⟨ht.1, ht.2⟩,
      by rw [Complex.ofReal_im]⟩
  have hdiag_mem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (t : ℂ) ∈ frontier halfDiscU := by
    intro t ht
    have hzU : (t : ℂ) ∈ halfDiscU := hzU_of_mem t ht
    rw [frontier, isClosed_halfDiscU.closure_eq]
    refine ⟨hzU, ?_⟩
    intro hcon
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hcon)
    have hmem : (t : ℂ) - Complex.I * ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (t : ℂ) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : (t : ℂ) - Complex.I * ((ε / 2 : ℝ) : ℂ) - (t : ℂ)
          = -(Complex.I * ((ε / 2 : ℝ) : ℂ)) := by ring
      rw [h1, norm_neg, norm_mul, Complex.norm_I, one_mul, norm_complex_ofReal,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2)]
      linarith
    have hnotmem : (t : ℂ) - Complex.I * ((ε / 2 : ℝ) : ℂ) ∉ halfDiscU := by
      intro hcc
      have him : ((t : ℂ) - Complex.I * ((ε / 2 : ℝ) : ℂ)).im = -ε / 2 := by
        rw [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      have := hcc.2
      rw [him] at this
      linarith
    exact hnotmem (interior_subset (hball hmem))
  let β : ℝ → Metric.sphere (0 : ℂ) 1 := fun t =>
    ⟨gaugeRadial halfDiscU p₀ ((Set.projIcc (-1 : ℝ) 1 hle t : ℝ) : ℂ),
      (hφsph _).mpr (hdiag_mem _ (Set.projIcc (-1 : ℝ) 1 hle t).2)⟩
  have hβc : Continuous β := by
    refine Continuous.subtype_mk ?_ _
    exact hφc.comp (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_projIcc))
  have hβproj : ∀ t (ht : t ∈ Set.Icc (-1 : ℝ) 1), β t =
      (⟨gaugeRadial halfDiscU p₀ (t : ℂ), (hφsph _).mpr (hdiag_mem t ht)⟩ :
        Metric.sphere (0 : ℂ) 1) := by
    intro t ht
    refine Subtype.ext ?_
    show gaugeRadial halfDiscU p₀ (((Set.projIcc (-1 : ℝ) 1 hle t : ℝ)) : ℂ) =
      gaugeRadial halfDiscU p₀ (t : ℂ)
    rw [Set.projIcc_of_mem hle ht]
  have hβinj : Set.InjOn β (Set.Icc (-1 : ℝ) 1) := by
    intro s hs t ht h
    have h1 : gaugeRadial halfDiscU p₀ (((Set.projIcc (-1 : ℝ) 1 hle s : ℝ)) : ℂ) =
        gaugeRadial halfDiscU p₀ (((Set.projIcc (-1 : ℝ) 1 hle t : ℝ)) : ℂ) :=
      congrArg Subtype.val h
    have h2 : (Set.projIcc (-1 : ℝ) 1 hle s : ℝ) = (Set.projIcc (-1 : ℝ) 1 hle t : ℝ) :=
      Complex.ofReal_injective (hφinj h1)
    rw [Set.projIcc_of_mem hle hs, Set.projIcc_of_mem hle ht] at h2
    exact h2
  obtain ⟨g₂, hg₂⟩ := Work.Drive.Mono.sphereArc_extension hβc huc_c hβinj huc_i
  let ψ' : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
    Work.Smooth.SphereJordan.discHomeo g₂
  have hpsi'_sphere : ∀ x : Metric.sphere (0 : ℂ) 1,
      ((ψ' (sphToDisc x) : Metric.closedBall (0 : ℂ) 1) : ℂ) = (g₂ x : ℂ) := by
    intro x
    show Work.Smooth.SphereJordan.radialMap g₂
      ((sphToDisc x : Metric.closedBall (0 : ℂ) 1) : ℂ) = (g₂ x : ℂ)
    rw [sphToDisc_coe]
    exact Work.Smooth.SphereJordan.radialMap_coe_sphere g₂ x
  have hΘreal : ∀ t (ht : t ∈ Set.Icc (-1 : ℝ) 1),
      ψ' (⟨gaugeRadial halfDiscU p₀ (t : ℂ), (hφmem _).mpr (hzU_of_mem t ht)⟩ :
        Metric.closedBall (0 : ℂ) 1) = sphToDisc (uc t) := by
    intro t ht
    have hβt : β t = (⟨gaugeRadial halfDiscU p₀ (t : ℂ),
        (hφsph _).mpr (hdiag_mem t ht)⟩ : Metric.sphere (0 : ℂ) 1) := hβproj t ht
    refine Subtype.ext ?_
    show ((ψ' (⟨gaugeRadial halfDiscU p₀ (t : ℂ), (hφmem _).mpr (hzU_of_mem t ht)⟩ :
        Metric.closedBall (0 : ℂ) 1)) : ℂ) = (uc t : ℂ)
    rw [show (⟨gaugeRadial halfDiscU p₀ (t : ℂ), (hφmem _).mpr (hzU_of_mem t ht)⟩ :
        Metric.closedBall (0 : ℂ) 1) = sphToDisc (β t) from by
      rw [hβt]
      exact Subtype.ext rfl]
    rw [hpsi'_sphere (β t), hg₂ t ht]
  let Θs : halfDiscU → Metric.closedBall (0 : ℂ) 1 :=
    fun z => ψ' ⟨gaugeRadial halfDiscU p₀ z.1, (hφmem z.1).mpr z.2⟩
  have hΘsc : Continuous Θs := by
    refine ψ'.continuous.comp ?_
    exact Continuous.subtype_mk (hφc.comp continuous_subtype_val) _
  have hΘs_inj : Function.Injective Θs := by
    intro a b hab
    have h1 : (⟨gaugeRadial halfDiscU p₀ a.1, (hφmem a.1).mpr a.2⟩ :
        Metric.closedBall (0 : ℂ) 1) =
        ⟨gaugeRadial halfDiscU p₀ b.1, (hφmem b.1).mpr b.2⟩ := ψ'.injective hab
    have h2 : gaugeRadial halfDiscU p₀ a.1 = gaugeRadial halfDiscU p₀ b.1 :=
      congrArg Subtype.val h1
    exact Subtype.ext (hφinj h2)
  have hΘs_real : ∀ t (ht : t ∈ Set.Icc (-1 : ℝ) 1),
      Θs ⟨(t : ℂ), hzU_of_mem t ht⟩ = sphToDisc (uc t) :=
    fun t ht => hΘreal t ht
  -- the two half-disc maps
  have hconj_mem : ∀ z ∈ halfDiscL, cjn z ∈ halfDiscU := by
    intro z hz
    exact ⟨by rw [norm_cjn]; exact hz.1,
      by rw [cjn_im]; exact neg_nonneg.mpr hz.2⟩
  let fU : ℂ → ℂ := fun z => if hz : z ∈ halfDiscU then eD (Θs ⟨z, hz⟩) else 0
  let fL : ℂ → ℂ := fun z => if hz : z ∈ halfDiscL then
    eC' (Θs ⟨cjn z, hconj_mem z hz⟩) else 0
  have heC'c : Continuous eC' := eC.continuous.comp ψ.continuous
  have hUc : ContinuousOn fU halfDiscU := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : halfDiscU.domRestrict fU = fun z : halfDiscU => eD (Θs z) := by
      funext z
      show (if hz : (z : ℂ) ∈ halfDiscU then eD (Θs ⟨(z : ℂ), hz⟩) else 0) = eD (Θs z)
      rw [dif_pos z.2]
    rw [heq]
    exact eD.continuous.comp hΘsc
  have hUi : Set.InjOn fU halfDiscU := by
    intro a ha b hb hab
    rw [show fU a = eD (Θs ⟨a, ha⟩) from dif_pos ha,
      show fU b = eD (Θs ⟨b, hb⟩) from dif_pos hb] at hab
    have h1 : Θs ⟨a, ha⟩ = Θs ⟨b, hb⟩ := heDi hab
    exact congrArg Subtype.val (hΘs_inj h1)
  have hUr : fU '' halfDiscU = D := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← heDr]
      simp only [fU, dif_pos hz]
      exact ⟨Θs ⟨z, hz⟩, rfl⟩
    · intro hy
      obtain ⟨w, hwy⟩ := show y ∈ Set.range eD from by rw [heDr]; exact hy
      have hmemw : ‖((ψ'.symm w : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ ≤ 1 := by
        have h := (ψ'.symm w).2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have hz : gaugeRadialInv halfDiscU p₀
          ((ψ'.symm w : Metric.closedBall (0 : ℂ) 1) : ℂ) ∈ halfDiscU := hφinvK _ hmemw
      have harg : (⟨gaugeRadial halfDiscU p₀ (gaugeRadialInv halfDiscU p₀
            ((ψ'.symm w : Metric.closedBall (0 : ℂ) 1) : ℂ)), (hφmem _).mpr hz⟩ :
          Metric.closedBall (0 : ℂ) 1) = ψ'.symm w :=
        Subtype.ext (hφright _)
      have hΘz : Θs ⟨gaugeRadialInv halfDiscU p₀
          ((ψ'.symm w : Metric.closedBall (0 : ℂ) 1) : ℂ), hz⟩ = w := by
        show ψ' ⟨gaugeRadial halfDiscU p₀ (gaugeRadialInv halfDiscU p₀
          ((ψ'.symm w : Metric.closedBall (0 : ℂ) 1) : ℂ)), (hφmem _).mpr hz⟩ = w
        rw [harg, ψ'.apply_symm_apply]
      have hval : fU (gaugeRadialInv halfDiscU p₀
          ((ψ'.symm w : Metric.closedBall (0 : ℂ) 1) : ℂ)) = eD w := by
        simp only [fU, dif_pos hz]
        rw [hΘz]
      exact ⟨_, hz, hval.trans hwy⟩
  have hLc : ContinuousOn fL halfDiscL := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : halfDiscL.domRestrict fL = fun z : halfDiscL =>
        eC' (Θs ⟨cjn (z : ℂ), hconj_mem _ z.2⟩) := by
      funext z
      show (if hz : (z : ℂ) ∈ halfDiscL then eC' (Θs ⟨cjn (z : ℂ), _⟩) else 0) = _
      rw [dif_pos z.2]
    rw [heq]
    refine heC'c.comp (hΘsc.comp ?_)
    exact Continuous.subtype_mk (continuous_cjn.comp continuous_subtype_val) _
  have hLi : Set.InjOn fL halfDiscL := by
    intro a ha b hb hab
    rw [show fL a = eC' (Θs ⟨cjn a, hconj_mem a ha⟩) from dif_pos ha,
      show fL b = eC' (Θs ⟨cjn b, hconj_mem b hb⟩) from dif_pos hb] at hab
    have h1 : Θs ⟨cjn a, hconj_mem a ha⟩ = Θs ⟨cjn b, hconj_mem b hb⟩ :=
      ψ.injective (heCi hab)
    have h2 : (⟨cjn a, hconj_mem a ha⟩ : halfDiscU) = ⟨cjn b, hconj_mem b hb⟩ := hΘs_inj h1
    have h3 : cjn a = cjn b := congrArg Subtype.val h2
    exact cjn_injective h3
  have hLr : fL '' halfDiscL = C := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← heCr]
      simp only [fL, dif_pos hz, eC']
      exact ⟨ψ (Θs ⟨cjn z, hconj_mem z hz⟩), rfl⟩
    · intro hy
      obtain ⟨w, hwy⟩ := show y ∈ Set.range eC from by rw [heCr]; exact hy
      set Z : ℂ := gaugeRadialInv halfDiscU p₀
        ((ψ'.symm (ψ.symm w) : Metric.closedBall (0 : ℂ) 1) : ℂ) with hZ
      have hmemZ : ‖((ψ'.symm (ψ.symm w) : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ ≤ 1 := by
        have h := (ψ'.symm (ψ.symm w)).2
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have hZU : Z ∈ halfDiscU := hφinvK _ hmemZ
      have hZL : cjn Z ∈ halfDiscL := by
        refine ⟨by rw [norm_cjn]; exact hZU.1, ?_⟩
        rw [cjn_im]
        linarith [hZU.2]
      have hvalZ : (gaugeRadial halfDiscU p₀ Z : ℂ) =
          ((ψ'.symm (ψ.symm w) : Metric.closedBall (0 : ℂ) 1) : ℂ) := by
        rw [hZ]; exact hφright _
      have harg : (⟨gaugeRadial halfDiscU p₀ Z, (hφmem Z).mpr hZU⟩ :
          Metric.closedBall (0 : ℂ) 1) = ψ'.symm (ψ.symm w) :=
        Subtype.ext hvalZ
      have hsub : (⟨cjn (cjn Z), hconj_mem (cjn Z) hZL⟩ : halfDiscU) = ⟨Z, hZU⟩ :=
        Subtype.ext (cjn_cjn Z)
      have hΘz : Θs ⟨cjn (cjn Z), hconj_mem (cjn Z) hZL⟩ = ψ.symm w := by
        rw [hsub]
        show ψ' ⟨gaugeRadial halfDiscU p₀ Z, (hφmem Z).mpr hZU⟩ = ψ.symm w
        rw [harg, ψ'.apply_symm_apply]
      have hval : fL (cjn Z) = eC w := by
        simp only [fL, dif_pos hZL, eC']
        rw [hΘz, ψ.apply_symm_apply]
      exact ⟨cjn Z, hZL, hval.trans hwy⟩
  have hagree : ∀ t ∈ Set.Icc (-1 : ℝ) 1, fU (t : ℂ) = fL (t : ℂ) := by
    intro t ht
    have hzU : (t : ℂ) ∈ halfDiscU := hzU_of_mem t ht
    have hzL : (t : ℂ) ∈ halfDiscL := ⟨hzU.1, by rw [Complex.ofReal_im]⟩
    have hsub : (⟨cjn (t : ℂ), hconj_mem (t : ℂ) hzL⟩ : halfDiscU) = ⟨(t : ℂ), hzU⟩ :=
      Subtype.ext (cjn_ofReal t)
    have hΘ1 : Θs ⟨(t : ℂ), hzU⟩ = sphToDisc (uc t) := hΘs_real t ht
    have hΘ3 : Θs ⟨cjn (t : ℂ), hconj_mem (t : ℂ) hzL⟩ = sphToDisc (uc t) := by
      rw [hsub]; exact hΘ1
    have hvalL : fL (t : ℂ) = eC' (sphToDisc (uc t)) := by
      simp only [fL, dif_pos hzL]
      rw [hΘ3]
    have hvalU : fU (t : ℂ) = eD (sphToDisc (uc t)) := by
      simp only [fU, dif_pos hzU]
      rw [hΘ1]
    rw [hvalU, hvalL, show eC' (sphToDisc (uc t)) = eD (sphToDisc (uc t)) from
      hagreeA'sph (uc t) (huc_A' t)]
  have hglueJ : fU '' (halfDiscU ∩ halfDiscL) = D ∩ C := by
    rw [halfDiscU_inter_halfDiscL]
    ext y
    constructor
    · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      simp only [fU, dif_pos (hzU_of_mem t ht), hΘs_real t ht]
      exact hγmem t
    · intro hy
      have hy' : y ∈ γ '' Set.Icc (-1 : ℝ) 1 := by rw [hγimg]; exact hy
      obtain ⟨t, ht, rfl⟩ := hy'
      exact ⟨(t : ℂ), ⟨t, ht, rfl⟩, by
        show fU (t : ℂ) = γ t
        simp only [fU, dif_pos (hzU_of_mem t ht), hΘs_real t ht]
        rfl⟩
  exact exists_discParam_of_glued_halfDiscs D C fU fL hUc hUi hUr hLc hLi hLr hagree hglueJ

/-- **The union of a disc and a convex set glued along a common boundary arc is a disc.** -/
theorem exists_discParam_of_disc_glued_convex (D C : Set (EuclideanSpace ℝ (Fin 2)))
    (hD : ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = D ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier D)
    (hreg : D = closure (interior D))
    (hCc : Convex ℝ C) (hCcl : IsCompact C) (hCne : (interior C).Nonempty)
    (hsub : D ∩ C ⊆ frontier D ∩ frontier C)
    (hne : ∃ x : EuclideanSpace ℝ (Fin 2), x ∈ D ∩ C ∧
      ∃ y : EuclideanSpace ℝ (Fin 2), y ∈ D ∩ C ∧ x ≠ y)
    (hint : interior D ∩ interior C = ∅)
    (hconn : IsPreconnected (D ∩ C)) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = D ∪ C ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (D ∪ C) := by
  classical
  -- transport everything to `ℂ` along the linear isometry `ℂ ≃ₗᵢ[ℝ] ℝ²`
  let φ : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  let φh : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) := φ.toHomeomorph
  have hφh : (φh : ℂ → EuclideanSpace ℝ (Fin 2)) = φ := rfl
  let D' : Set ℂ := φh.symm '' D
  let C' : Set ℂ := φh.symm '' C
  have hsymm_image_D : φh '' D' = D := by
    show φh '' (φh.symm '' D) = D
    rw [Set.image_image]
    simp
  have hsymm_image_C : φh '' C' = C := by
    show φh '' (φh.symm '' C) = C
    rw [Set.image_image]
    simp
  have hD' : ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℂ),
      Function.Injective e ∧ Set.range e = D' ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier D' := by
    obtain ⟨eD, heDi, heDr, heDfr⟩ := hD
    refine ⟨⟨fun z => φh.symm (eD z), φh.symm.continuous.comp eD.continuous⟩, ?_, ?_, ?_⟩
    · intro z w hzw
      exact heDi (φh.symm.injective hzw)
    · show Set.range (fun z => φh.symm (eD z)) = D'
      rw [show Set.range (fun z => φh.symm (eD z)) = φh.symm '' Set.range eD from
        Set.range_comp φh.symm eD, heDr]
    · show Set.range (fun θ : ℝ => φh.symm (eD (Work.CoreTopology.circlePoint θ)))
          = frontier D'
      rw [show Set.range (fun θ : ℝ => φh.symm (eD (Work.CoreTopology.circlePoint θ)))
            = φh.symm '' Set.range (fun θ : ℝ => eD (Work.CoreTopology.circlePoint θ)) from
          Set.range_comp φh.symm _, heDfr]
      exact Homeomorph.image_frontier φh.symm D
  have hreg' : D' = closure (interior D') := by
    show φh.symm '' D = closure (interior (φh.symm '' D))
    calc φh.symm '' D = φh.symm '' closure (interior D) :=
          congrArg (fun s : Set (EuclideanSpace ℝ (Fin 2)) => φh.symm '' s) hreg
      _ = closure (φh.symm '' interior D) := Homeomorph.image_closure φh.symm (interior D)
      _ = closure (interior (φh.symm '' D)) := by
          rw [Homeomorph.image_interior φh.symm D]
  have hCc' : Convex ℝ C' := by
    show Convex ℝ (⇑φ.symm '' C)
    exact hCc.linear_image (φ.symm).toLinearMap
  have hCcl' : IsCompact C' := by
    show IsCompact (φh.symm '' C)
    exact hCcl.image φh.symm.continuous
  have hCne' : (interior C').Nonempty := by
    show (interior (φh.symm '' C)).Nonempty
    rw [← Homeomorph.image_interior φh.symm C]
    obtain ⟨x, hx⟩ := hCne
    exact ⟨φh.symm x, ⟨x, hx, rfl⟩⟩
  have hsub' : D' ∩ C' ⊆ frontier D' ∩ frontier C' := by
    show φh.symm '' D ∩ φh.symm '' C ⊆ frontier (φh.symm '' D) ∩ frontier (φh.symm '' C)
    rw [← Set.image_inter φh.symm.injective, ← Homeomorph.image_frontier,
      ← Homeomorph.image_frontier, ← Set.image_inter φh.symm.injective]
    exact Set.image_mono hsub
  have hne' : ∃ x : ℂ, x ∈ D' ∩ C' ∧ ∃ y : ℂ, y ∈ D' ∩ C' ∧ x ≠ y := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    refine ⟨φh.symm x, ?_, φh.symm y, ?_, fun h => hxy (φh.symm.injective h)⟩
    · exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    · exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  have hint' : interior D' ∩ interior C' = ∅ := by
    show interior (φh.symm '' D) ∩ interior (φh.symm '' C) = ∅
    rw [← Homeomorph.image_interior φh.symm D, ← Homeomorph.image_interior φh.symm C,
      ← Set.image_inter φh.symm.injective, hint, Set.image_empty]
  have hconn' : IsPreconnected (D' ∩ C') := by
    show IsPreconnected (φh.symm '' D ∩ φh.symm '' C)
    rw [← Set.image_inter φh.symm.injective]
    exact hconn.image _ φh.symm.continuous.continuousOn
  obtain ⟨e', he'i, he'r, he'f⟩ :=
    exists_discParam_of_disc_glued_convex_ℂ D' C' hD' hreg' hCc' hCcl' hCne' hsub' hne' hint'
      hconn'
  refine ⟨⟨fun z => φh (e' z), φh.continuous.comp e'.continuous⟩, ?_, ?_, ?_⟩
  · intro z w hzw
    exact he'i (φh.injective hzw)
  · show Set.range (fun z => φh (e' z)) = D ∪ C
    rw [show Set.range (fun z => φh (e' z)) = φh '' Set.range e' from Set.range_comp φh e',
      he'r, Set.image_union, hsymm_image_D, hsymm_image_C]
  · show Set.range (fun θ : ℝ => φh (e' (Work.CoreTopology.circlePoint θ))) = frontier (D ∪ C)
    rw [show Set.range (fun θ : ℝ => φh (e' (Work.CoreTopology.circlePoint θ)))
          = φh '' Set.range (fun θ : ℝ => e' (Work.CoreTopology.circlePoint θ)) from
        Set.range_comp φh _, he'f]
    rw [Homeomorph.image_frontier]
    congr 1
    rw [Set.image_union, hsymm_image_D, hsymm_image_C]

end

end Work.Drive.Mono
