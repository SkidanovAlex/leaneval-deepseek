import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Lib.Unif2.Commons.Topology.Surface.exists_locallyFinite_coordinateBall_cover_of_noncompact
import Submission.Lib.Unif2.Commons.Geometry.Manifold.chart_transition_analyticOnNhd

open Set Metric
open scoped Topology

noncomputable section

namespace Commons.Topology.Surface

/-! ## Auxiliary homeomorphism lemmas for plane regions

Everything here is elementary plane topology: convexity, rescalings of "regions between
graphs", and (later) the disk tilings used to prove
`exists_locallyFinite_disk_tiling`. -/

/-- Continuity of a `Complex.mk`-shaped map, in terms of its real and imaginary parts. -/
lemma continuous_re_im_mk {Y : Type*} [TopologicalSpace Y] {f g : Y → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun y => (⟨f y, g y⟩ : ℂ) := by
  rw [show (fun y => (⟨f y, g y⟩ : ℂ)) = fun y => ((f y : ℂ) + (g y : ℂ) * Complex.I) from by
    funext y
    apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]]
  exact (Complex.continuous_ofReal.comp hf).add ((Complex.continuous_ofReal.comp hg).mul continuous_const)

/-- A compact convex set with nonempty interior in `ℂ` is homeomorphic to the closed unit disk. -/
theorem homeomorph_closedBall_of_convex {s : Set ℂ} (hc : Convex ℝ s) (hi : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) (hcl : IsClosed s) :
    Nonempty (s ≃ₜ Metric.closedBall (0:ℂ) 1) := by
  obtain ⟨Φ, h1, h2, h3⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hi hb
  have : Φ '' s = Metric.closedBall (0:ℂ) 1 := by rw [← h2, hcl.closure_eq]
  exact ⟨(Φ.image s).trans (Homeomorph.setCongr this)⟩

/-- The vertical strip `[x₀,x₁] × [0,1]` as a subset of `ℂ`. -/
def rectSet (x₀ x₁ : ℝ) : Set ℂ := {z | z.re ∈ Icc x₀ x₁ ∧ z.im ∈ Icc (0:ℝ) 1}

lemma rectSet_eq (x₀ x₁ : ℝ) :
    rectSet x₀ x₁ = (Complex.re ⁻¹' Icc x₀ x₁) ∩ (Complex.im ⁻¹' Icc (0:ℝ) 1) := by
  ext z; tauto

lemma convex_rectSet (x₀ x₁ : ℝ) : Convex ℝ (rectSet x₀ x₁) := by
  rw [rectSet_eq]
  exact ((convex_Icc x₀ x₁).linear_preimage (f := (Complex.reCLM : ℂ →ₗ[ℝ] ℝ))).inter
    ((convex_Icc (0:ℝ) 1).linear_preimage (f := (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)))

lemma isClosed_rectSet (x₀ x₁ : ℝ) : IsClosed (rectSet x₀ x₁) := by
  rw [rectSet_eq]
  exact ((isClosed_Icc.preimage Complex.continuous_re)).inter
    ((isClosed_Icc.preimage Complex.continuous_im))

lemma interior_rectSet_nonempty {x₀ x₁ : ℝ} (hx : x₀ < x₁) : (interior (rectSet x₀ x₁)).Nonempty := by
  refine ⟨⟨(x₀+x₁)/2, 1/2⟩, ?_⟩
  rw [mem_interior_iff_mem_nhds, rectSet_eq]
  have h1 : Complex.re ⁻¹' Ioo x₀ x₁ ∈ 𝓝 (⟨(x₀+x₁)/2, 1/2⟩ : ℂ) :=
    (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by constructor <;> linarith)
  have h2 : Complex.im ⁻¹' Ioo (0:ℝ) 1 ∈ 𝓝 (⟨(x₀+x₁)/2, 1/2⟩ : ℂ) :=
    (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds (by constructor <;> norm_num)
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro z ⟨hz1, hz2⟩
  exact ⟨⟨le_of_lt hz1.1, le_of_lt hz1.2⟩, ⟨le_of_lt hz2.1, le_of_lt hz2.2⟩⟩

lemma isBounded_rectSet (x₀ x₁ : ℝ) : Bornology.IsBounded (rectSet x₀ x₁) := by
  refine (Metric.isBounded_closedBall (x := (0:ℂ))
    (r := (|x₀| + |x₁|) + 1)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨hre, him⟩ := hz
  have h1 : |z.re| ≤ |x₀| + |x₁| := by
    rw [abs_le]
    exact ⟨by linarith [hre.1, neg_abs_le x₀, abs_nonneg x₁],
           by linarith [hre.2, le_abs_self x₁, abs_nonneg x₀]⟩
  have h2 : |z.im| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [him.1], him.2⟩
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ (|x₀| + |x₁|) + 1 := by linarith

/-- The vertical graph region between the functions `a` and `b` over `[x₀,x₁]`. -/
def graphRegion (a b : ℝ → ℝ) (x₀ x₁ : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc x₀ x₁ ∧ a z.re ≤ z.im ∧ z.im ≤ b z.re}

noncomputable def vrescale (a b : ℝ → ℝ) (z : ℂ) : ℂ :=
  ⟨z.re, (z.im - a z.re) / (b z.re - a z.re)⟩

noncomputable def vunrescale (a b : ℝ → ℝ) (z : ℂ) : ℂ :=
  ⟨z.re, a z.re + z.im * (b z.re - a z.re)⟩

lemma vrescale_mem_rect {a b : ℝ → ℝ} {x₀ x₁ : ℝ} (hab : ∀ x ∈ Icc x₀ x₁, a x < b x)
    {z : ℂ} (hz : z ∈ graphRegion a b x₀ x₁) : vrescale a b z ∈ rectSet x₀ x₁ := by
  obtain ⟨hr, ha', hb'⟩ := hz
  have hd : 0 < b z.re - a z.re := sub_pos.mpr (hab z.re hr)
  refine ⟨hr, ?_, ?_⟩
  · rw [vrescale, div_nonneg_iff]; left; exact ⟨by linarith, le_of_lt hd⟩
  · rw [vrescale, div_le_one hd]; linarith

lemma vunrescale_mem_graph {a b : ℝ → ℝ} {x₀ x₁ : ℝ} (hab : ∀ x ∈ Icc x₀ x₁, a x < b x)
    {z : ℂ} (hz : z ∈ rectSet x₀ x₁) : vunrescale a b z ∈ graphRegion a b x₀ x₁ := by
  obtain ⟨hr, h0, h1⟩ := hz
  have hd : 0 ≤ b z.re - a z.re := (sub_pos.mpr (hab z.re hr)).le
  refine ⟨hr, ?_, ?_⟩
  · show a z.re ≤ a z.re + z.im * (b z.re - a z.re)
    nlinarith [mul_nonneg h0 hd]
  · show a z.re + z.im * (b z.re - a z.re) ≤ b z.re
    nlinarith [mul_le_of_le_one_right hd h1]

lemma vunrescale_vrescale {a b : ℝ → ℝ} {x₀ x₁ : ℝ} (hab : ∀ x ∈ Icc x₀ x₁, a x < b x)
    {z : ℂ} (hz : z ∈ graphRegion a b x₀ x₁) : vunrescale a b (vrescale a b z) = z := by
  have hd : b z.re - a z.re ≠ 0 := (sub_pos.mpr (hab z.re hz.1)).ne'
  apply Complex.ext
  · simp only [vrescale, vunrescale]
  · simp only [vrescale, vunrescale]
    field_simp
    ring

lemma vrescale_vunrescale {a b : ℝ → ℝ} {x₀ x₁ : ℝ} (hab : ∀ x ∈ Icc x₀ x₁, a x < b x)
    {z : ℂ} (hz : z ∈ rectSet x₀ x₁) : vrescale a b (vunrescale a b z) = z := by
  have hd : b z.re - a z.re ≠ 0 := (sub_pos.mpr (hab z.re hz.1)).ne'
  apply Complex.ext
  · simp only [vrescale, vunrescale]
  · simp only [vrescale, vunrescale]
    field_simp
    ring

theorem graphRegion_homeomorph_rect {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    {x₀ x₁ : ℝ} (hab : ∀ x ∈ Icc x₀ x₁, a x < b x) :
    Nonempty (graphRegion a b x₀ x₁ ≃ₜ rectSet x₀ x₁) := by
  have hden : ∀ z : graphRegion a b x₀ x₁, b z.1.re - a z.1.re ≠ 0 :=
    fun z => (sub_pos.mpr (hab z.1.re z.2.1)).ne'
  have hf : Continuous (fun z : graphRegion a b x₀ x₁ =>
      (⟨z.1.re, (z.1.im - a z.1.re) / (b z.1.re - a z.1.re)⟩ : ℂ)) :=
    continuous_re_im_mk (Complex.continuous_re.comp continuous_subtype_val)
      ((Complex.continuous_im.comp continuous_subtype_val).sub
        (ha.comp (Complex.continuous_re.comp continuous_subtype_val)) |>.div
        ((hb.comp (Complex.continuous_re.comp continuous_subtype_val)).sub
          (ha.comp (Complex.continuous_re.comp continuous_subtype_val))) (fun z => hden z))
  have hg : Continuous (fun w : rectSet x₀ x₁ =>
      (⟨w.1.re, a w.1.re + w.1.im * (b w.1.re - a w.1.re)⟩ : ℂ)) :=
    continuous_re_im_mk (Complex.continuous_re.comp continuous_subtype_val)
      ((ha.comp (Complex.continuous_re.comp continuous_subtype_val)).add
        ((Complex.continuous_im.comp continuous_subtype_val).mul
          ((hb.comp (Complex.continuous_re.comp continuous_subtype_val)).sub
            (ha.comp (Complex.continuous_re.comp continuous_subtype_val)))))
  refine ⟨Homeomorph.mk ?_ ?_ ?_⟩
  · refine { toFun := fun z => ⟨vrescale a b z.1, vrescale_mem_rect hab z.2⟩
             invFun := fun w => ⟨vunrescale a b w.1, vunrescale_mem_graph hab w.2⟩
             left_inv := fun z => Subtype.ext (vunrescale_vrescale hab z.2)
             right_inv := fun w => Subtype.ext (vrescale_vunrescale hab w.2) }
  · apply Continuous.subtype_mk
    simpa only [vrescale] using hf
  · apply Continuous.subtype_mk
    simpa only [vunrescale] using hg

/-- The region between two continuous graphs is closed (used for the compactness of the pieces). -/
lemma isClosed_graphRegion {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) (a b : ℝ) :
    IsClosed (graphRegion g h a b) := by
  have he : graphRegion g h a b = (Complex.re ⁻¹' Icc a b)
        ∩ ((fun z : ℂ => z.im - g z.re) ⁻¹' Ici 0)
        ∩ ((fun z : ℂ => h z.re - z.im) ⁻¹' Ici 0) := by
    ext z
    simp only [graphRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
      Set.mem_Ici]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  rw [he]
  exact ((isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Ici.preimage (Complex.continuous_im.sub (hg.comp Complex.continuous_re)))).inter
    (isClosed_Ici.preimage ((hh.comp Complex.continuous_re).sub Complex.continuous_im))

/-- Compactness of a graph region with continuous bounds. -/
lemma isCompact_graphRegion {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) {a b : ℝ}
    (hab : a ≤ b) : IsCompact (graphRegion g h a b) := by
  obtain ⟨Bu, hBu⟩ := (isCompact_Icc (a := a) (b := b) |>.image hh).bddAbove
  obtain ⟨Bl, hBl⟩ := (isCompact_Icc (a := a) (b := b) |>.image hg).bddBelow
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_graphRegion hg hh a b, ?_⟩
  refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := |a| + |b| + |Bl| + |Bu| + 1)).subset ?_
  intro z hz
  obtain ⟨hz1, hz2, hz3⟩ := hz
  have hu : h z.re ≤ Bu := hBu ⟨z.re, hz1, rfl⟩
  have hl : Bl ≤ g z.re := hBl ⟨z.re, hz1, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |z.re| ≤ |a| + |b| := by
    rw [abs_le]
    exact ⟨by linarith [hz1.1, neg_abs_le a, abs_nonneg b],
           by linarith [hz1.2, le_abs_self b, abs_nonneg a]⟩
  have him : |z.im| ≤ |Bl| + |Bu| := by
    rw [abs_le]
    exact ⟨by linarith [hl, neg_abs_le Bl, abs_nonneg Bu],
           by linarith [hu, le_abs_self Bu, abs_nonneg Bl]⟩
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ |a| + |b| + (|Bl| + |Bu|) := by linarith
    _ ≤ |a| + |b| + |Bl| + |Bu| + 1 := by linarith [abs_nonneg Bl, abs_nonneg Bu]

/-! ### The shear step of the generalized lune lemma

`graphRegion g h a b` is carried by the vertical shear `z ↦ (z.re, z.im - g z.re)` onto
`graphRegion 0 (h - g) a b`, which reduces the pinch cases to the region under a single nonnegative
function. -/

/-- The vertical shear `z ↦ (z.re, z.im - g z.re)` of the plane. -/
noncomputable def shearHomeomorph (g : ℝ → ℝ) (hg : Continuous g) : ℂ ≃ₜ ℂ :=
  { toFun := fun z => (⟨z.re, z.im - g z.re⟩ : ℂ)
    invFun := fun z => (⟨z.re, z.im + g z.re⟩ : ℂ)
    left_inv := by
      intro z
      apply Complex.ext <;> simp
    right_inv := by
      intro z
      apply Complex.ext <;> simp
    continuous_toFun := continuous_re_im_mk Complex.continuous_re
      (Complex.continuous_im.sub (hg.comp Complex.continuous_re))
    continuous_invFun := continuous_re_im_mk Complex.continuous_re
      (Complex.continuous_im.add (hg.comp Complex.continuous_re)) }

lemma shearHomeomorph_apply (g : ℝ → ℝ) (hg : Continuous g) (z : ℂ) :
    shearHomeomorph g hg z = (⟨z.re, z.im - g z.re⟩ : ℂ) := rfl

lemma shearHomeomorph_symm_apply (g : ℝ → ℝ) (hg : Continuous g) (z : ℂ) :
    (shearHomeomorph g hg).symm z = (⟨z.re, z.im + g z.re⟩ : ℂ) := rfl

/-- The shear carries the region between the graphs of `g` and `h` onto the region between `0`
and `h - g`. -/
lemma shear_image {g h : ℝ → ℝ} {a b : ℝ} (hg : Continuous g) :
    shearHomeomorph g hg '' graphRegion g h a b
      = graphRegion (fun _ => 0) (fun x => h x - g x) a b := by
  ext z; constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hw
    refine ⟨h1, ?_, ?_⟩
    · rw [shearHomeomorph_apply]
      show (0:ℝ) ≤ w.im - g w.re
      linarith
    · rw [shearHomeomorph_apply]
      show w.im - g w.re ≤ h w.re - g w.re
      linarith
  · intro hz
    refine ⟨(shearHomeomorph g hg).symm z, ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hz
      refine ⟨h1, ?_, ?_⟩
      · rw [shearHomeomorph_symm_apply]
        show g z.re ≤ z.im + g z.re
        linarith
      · rw [shearHomeomorph_symm_apply]
        show z.im + g z.re ≤ h z.re
        linarith
    · exact (shearHomeomorph g hg).apply_symm_apply z

/-- A `graphRegion` is homeomorphic to the closed unit disk (non-degenerate case). -/
theorem graphRegion_homeomorph_closedBall {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    {x₀ x₁ : ℝ} (hx : x₀ < x₁) (hab : ∀ x ∈ Icc x₀ x₁, a x < b x) :
    Nonempty (graphRegion a b x₀ x₁ ≃ₜ Metric.closedBall (0:ℂ) 1) := by
  obtain ⟨e⟩ := graphRegion_homeomorph_rect ha hb hab
  exact ⟨e.trans (Classical.choice
    (homeomorph_closedBall_of_convex (convex_rectSet x₀ x₁) (interior_rectSet_nonempty hx)
      (isBounded_rectSet x₀ x₁) (isClosed_rectSet x₀ x₁)))⟩

/-! ### The `c = 1` case and the mirror-triangle target

The non-pinched case of the generalized lune lemma is the existing
`graphRegion_homeomorph_closedBall`; the pinched cases map onto the "mirror triangle"
`{a ≤ re ≤ b, 0 ≤ im, im ≤ b - re}`, whose convexity/closedness/boundedness/nonempty interior are
collected here. -/

/-- The region under a strictly positive continuous function (the non-pinched case). -/
lemma underGraph_pos_homeomorph_closedBall {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hpos : ∀ x ∈ Icc a b, 0 < f x) :
    Nonempty ((graphRegion (fun _ => (0:ℝ)) f a b) ≃ₜ Metric.closedBall (0:ℂ) 1) :=
  graphRegion_homeomorph_closedBall continuous_const hf hab hpos

/-- The region under a nonnegative function vanishing at the right endpoint maps onto the mirror
triangle. -/
lemma mirrorTriangle_eq (a b : ℝ) :
    graphRegion (fun _ => (0:ℝ)) (fun x => b - x) a b
      = (Complex.re ⁻¹' Icc a b) ∩ (Complex.im ⁻¹' Ici (0:ℝ))
        ∩ ((fun z : ℂ => z.re + z.im) ⁻¹' Iic b) := by
  ext z
  simp only [graphRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
    Set.mem_Ici, Set.mem_Iic]
  constructor
  · rintro ⟨h1, h2, h3⟩
    change (0:ℝ) ≤ z.im at h2
    change z.im ≤ b - z.re at h3
    exact ⟨⟨h1, h2⟩, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    change z.re + z.im ≤ b at h3
    exact ⟨h1, h2, by linarith⟩

lemma convex_mirrorTriangle (a b : ℝ) :
    Convex ℝ (graphRegion (fun _ => (0:ℝ)) (fun x => b - x) a b) := by
  rw [mirrorTriangle_eq]
  exact (((convex_Icc a b).linear_preimage (f := (Complex.reCLM : ℂ →ₗ[ℝ] ℝ))).inter
    ((convex_Ici (0:ℝ)).linear_preimage (f := (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)))).inter
    ((convex_Iic b).linear_preimage
      (f := ((Complex.reCLM : ℂ →ₗ[ℝ] ℝ) + (Complex.imCLM : ℂ →ₗ[ℝ] ℝ))))

lemma isClosed_mirrorTriangle (a b : ℝ) :
    IsClosed (graphRegion (fun _ => (0:ℝ)) (fun x => b - x) a b) := by
  rw [mirrorTriangle_eq]
  exact (((isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Ici.preimage Complex.continuous_im)).inter
    (isClosed_Iic.preimage (Complex.continuous_re.add Complex.continuous_im)))

lemma isBounded_mirrorTriangle (a b : ℝ) :
    Bornology.IsBounded (graphRegion (fun _ => (0:ℝ)) (fun x => b - x) a b) := by
  refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := |a| + |b| + |b - a| + 1)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨h1, h2, h3⟩ := hz
  change (0:ℝ) ≤ z.im at h2
  change z.im ≤ b - z.re at h3
  have hza : z.re ≤ b := h1.2
  have hzb : a ≤ z.re := h1.1
  have him1 : z.im ≤ b - a := by linarith
  have h1' : |z.re| ≤ |a| + |b| := by
    rw [abs_le]
    exact ⟨by linarith [hzb, neg_abs_le a, abs_nonneg b],
      by linarith [hza, le_abs_self b, abs_nonneg a]⟩
  have hnorm : ‖z‖ ≤ |z.re| + z.im := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg h2] at h
    exact h
  calc ‖z‖ ≤ |z.re| + z.im := hnorm
    _ ≤ |a| + |b| + |b - a| + 1 := by
        have h := le_abs_self (b - a); linarith

lemma interior_mirrorTriangle_nonempty {a b : ℝ} (hab : a < b) :
    (interior (graphRegion (fun _ => (0:ℝ)) (fun x => b - x) a b)).Nonempty := by
  refine ⟨(⟨(2 * a + b) / 3, (b - a) / 4⟩ : ℂ), ?_⟩
  have hsub' : {z : ℂ | z.re < b ∧ a < z.re ∧ 0 < z.im ∧ z.re + z.im < b}
      ⊆ (Complex.re ⁻¹' Icc a b) ∩ (Complex.im ⁻¹' Ici (0:ℝ))
        ∩ ((fun z : ℂ => z.re + z.im) ⁻¹' Iic b) := by
    rintro z ⟨h1, h2, h3, h4⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, Set.mem_Ici, Set.mem_Iic]
    exact ⟨⟨⟨le_of_lt h2, le_of_lt h1⟩, le_of_lt h3⟩, le_of_lt h4⟩
  have hsub : {z : ℂ | z.re < b ∧ a < z.re ∧ 0 < z.im ∧ z.re + z.im < b}
      ⊆ graphRegion (fun _ => (0:ℝ)) (fun x => b - x) a b := by
    rw [mirrorTriangle_eq]; exact hsub'
  have hopen : IsOpen {z : ℂ | z.re < b ∧ a < z.re ∧ 0 < z.im ∧ z.re + z.im < b} := by
    have he : {z : ℂ | z.re < b ∧ a < z.re ∧ 0 < z.im ∧ z.re + z.im < b}
        = (Complex.re ⁻¹' Iio b) ∩ (Complex.re ⁻¹' Ioi a) ∩ (Complex.im ⁻¹' Ioi (0:ℝ))
          ∩ ((fun z : ℂ => z.re + z.im) ⁻¹' Iio b) := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio,
        Set.mem_Ioi]; tauto
    rw [he]
    exact (((isOpen_Iio.preimage Complex.continuous_re).inter
      (isOpen_Ioi.preimage Complex.continuous_re)).inter
      (isOpen_Ioi.preimage Complex.continuous_im)).inter
      (isOpen_Iio.preimage (Complex.continuous_re.add Complex.continuous_im))
  have hpt : (⟨(2 * a + b) / 3, (b - a) / 4⟩ : ℂ) ∈
      {z : ℂ | z.re < b ∧ a < z.re ∧ 0 < z.im ∧ z.re + z.im < b} := by
    simp only [Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (2 * a + b) / 3 < b; linarith
    · change a < (2 * a + b) / 3; linarith
    · change (0:ℝ) < (b - a) / 4; linarith
    · change (2 * a + b) / 3 + (b - a) / 4 < b; linarith
  exact interior_maximal hsub hopen hpt

/-- The mirror triangle is homeomorphic to the closed unit disk. -/
theorem mirrorTriangle_homeomorph_closedBall {a b : ℝ} (hab : a < b) :
    Nonempty (graphRegion (fun _ => (0:ℝ)) (fun x => b - x) a b ≃ₜ Metric.closedBall (0:ℂ) 1) :=
  homeomorph_closedBall_of_convex (convex_mirrorTriangle a b)
    (interior_mirrorTriangle_nonempty hab) (isBounded_mirrorTriangle a b)
    (isClosed_mirrorTriangle a b)

/-- The triangle region `{x₀ ≤ re ≤ x₁, 0 ≤ im ≤ re - x₀}`. -/
def triRegion (x₀ x₁ : ℝ) : Set ℂ := {z | z.re ∈ Icc x₀ x₁ ∧ 0 ≤ z.im ∧ z.im ≤ z.re - x₀}

lemma triRegion_eq (x₀ x₁ : ℝ) : triRegion x₀ x₁ =
    (Complex.re ⁻¹' Icc x₀ x₁) ∩ (Complex.im ⁻¹' Ici (0:ℝ)) ∩ ((fun z : ℂ => z.re - z.im) ⁻¹' Ici x₀) := by
  ext z
  simp only [triRegion, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Icc, mem_Ici]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩

lemma convex_triRegion (x₀ x₁ : ℝ) : Convex ℝ (triRegion x₀ x₁) := by
  rw [triRegion_eq]
  exact (((convex_Icc x₀ x₁).linear_preimage (f := (Complex.reCLM : ℂ →ₗ[ℝ] ℝ))).inter
    ((convex_Ici (0:ℝ)).linear_preimage (f := (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)))).inter
    ((convex_Ici x₀).linear_preimage
      (f := ((Complex.reCLM : ℂ →ₗ[ℝ] ℝ) - (Complex.imCLM : ℂ →ₗ[ℝ] ℝ))))

lemma isClosed_triRegion (x₀ x₁ : ℝ) : IsClosed (triRegion x₀ x₁) := by
  rw [triRegion_eq]
  exact (((isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Ici.preimage Complex.continuous_im)).inter
    (isClosed_Ici.preimage (Complex.continuous_re.sub Complex.continuous_im)))

lemma interior_triRegion_nonempty {x₀ x₁ : ℝ} (hx : x₀ < x₁) : (interior (triRegion x₀ x₁)).Nonempty := by
  have hsub : {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioi (0:ℝ) ∧ z.re - z.im ∈ Ioi x₀} ⊆ triRegion x₀ x₁ := by
    rintro z ⟨hz1, hz2, hz3⟩
    simp only [mem_Ioo, mem_Ioi] at hz1 hz2 hz3
    exact ⟨⟨le_of_lt hz1.1, le_of_lt hz1.2⟩, le_of_lt hz2, by linarith⟩
  have hopen : IsOpen {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioi (0:ℝ) ∧ z.re - z.im ∈ Ioi x₀} := by
    have he : {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioi (0:ℝ) ∧ z.re - z.im ∈ Ioi x₀} =
        (Complex.re ⁻¹' Ioo x₀ x₁) ∩ (Complex.im ⁻¹' Ioi (0:ℝ)) ∩ ((fun z : ℂ => z.re - z.im) ⁻¹' Ioi x₀) := by
      ext z; simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]; tauto
    rw [he]
    exact (((isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioi.preimage Complex.continuous_im)).inter
      (isOpen_Ioi.preimage (Complex.continuous_re.sub Complex.continuous_im)))
  have hpt : (⟨(x₀+x₁)/2, (x₁-x₀)/8⟩ : ℂ) ∈ {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioi (0:ℝ) ∧ z.re - z.im ∈ Ioi x₀} := by
    simp only [mem_Ioo, mem_Ioi]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · change x₀ < (x₀+x₁)/2; linarith
    · change (x₀+x₁)/2 < x₁; linarith
    · change (0:ℝ) < (x₁-x₀)/8; linarith
    · change x₀ < (x₀+x₁)/2 - (x₁-x₀)/8; linarith
  exact ⟨_, interior_mono hsub (hopen.interior_eq ▸ hpt)⟩

lemma isBounded_triRegion (x₀ x₁ : ℝ) : Bornology.IsBounded (triRegion x₀ x₁) := by
  refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 2 * (|x₀| + |x₁|) + 1)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨hre, him, him2⟩ := hz
  have h1 : |z.re| ≤ |x₀| + |x₁| := by
    rw [abs_le]
    exact ⟨by linarith [hre.1, neg_abs_le x₀, abs_nonneg x₁],
           by linarith [hre.2, le_abs_self x₁, abs_nonneg x₀]⟩
  have h2 : |z.im| ≤ |x₀| + |x₁| := by
    rw [abs_le]; constructor
    · linarith [him, abs_nonneg x₀, abs_nonneg x₁]
    · linarith [him2, hre.2, le_abs_self x₁, neg_abs_le x₀, abs_nonneg x₀, abs_nonneg x₁]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 2 * (|x₀| + |x₁|) + 1 := by linarith

theorem triRegion_homeomorph_closedBall {x₀ x₁ : ℝ} (hx : x₀ < x₁) :
    Nonempty (triRegion x₀ x₁ ≃ₜ Metric.closedBall (0:ℂ) 1) :=
  homeomorph_closedBall_of_convex (convex_triRegion x₀ x₁) (interior_triRegion_nonempty hx)
    (isBounded_triRegion x₀ x₁) (isClosed_triRegion x₀ x₁)

/-! ### Planar tiling toolkit (coverage and interior descriptions) -/

/-- Removing a closed set with empty interior from an open set does not change its closure. -/
lemma closure_sdiff_of_isClosed_interior_eq_empty {X : Type*} [TopologicalSpace X] {Q W : Set X}
    (hW : IsClosed W) (hWint : interior W = ∅) : closure (interior Q \ W) = closure (interior Q) := by
  have hsub : interior Q ⊆ closure (interior Q \ W) := by
    intro x hx
    rw [_root_.mem_closure_iff]
    intro U hU hxU
    have hopen : IsOpen (U ∩ interior Q) := hU.inter isOpen_interior
    have hne : (U ∩ interior Q).Nonempty := ⟨x, hxU, hx⟩
    have hnotsub : ¬ (U ∩ interior Q ⊆ W) := by
      intro h
      have h2 : U ∩ interior Q ⊆ interior W := interior_maximal h hopen
      rw [hWint] at h2
      obtain ⟨z, hz⟩ := hne
      exact h2 hz
    obtain ⟨z, hzUQ, hzW⟩ := Set.not_subset.mp hnotsub
    exact ⟨z, hzUQ.1, hzUQ.2, hzW⟩
  exact Subset.antisymm (closure_mono diff_subset) (closure_minimal hsub isClosed_closure)

/-- The open "interior" description of a graph region (one inclusion). -/
lemma interior_graphRegion_subset {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) {a b : ℝ} :
    {z : ℂ | a < z.re ∧ z.re < b ∧ g z.re < z.im ∧ z.im < h z.re}
      ⊆ interior (graphRegion g h a b) := by
  have hopen : IsOpen {z : ℂ | a < z.re ∧ z.re < b ∧ g z.re < z.im ∧ z.im < h z.re} := by
    have he : {z : ℂ | a < z.re ∧ z.re < b ∧ g z.re < z.im ∧ z.im < h z.re}
        = (Complex.re ⁻¹' Ioo a b) ∩ ((fun z : ℂ => z.im - g z.re) ⁻¹' Ioi 0)
          ∩ ((fun z : ℂ => h z.re - z.im) ⁻¹' Ioi 0) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo, Set.mem_Ioi]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨⟨h1, h2⟩, by linarith⟩, by linarith⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨h1, h2, by linarith, by linarith⟩
    rw [he]
    exact ((isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioi.preimage (Complex.continuous_im.sub (hg.comp Complex.continuous_re)))).inter
      (isOpen_Ioi.preimage ((hh.comp Complex.continuous_re).sub Complex.continuous_im))
  refine interior_maximal ?_ hopen
  intro w hw
  exact ⟨⟨le_of_lt hw.1, le_of_lt hw.2.1⟩, le_of_lt hw.2.2.1, le_of_lt hw.2.2.2⟩


/-! ### Monotonicity on a strip (used by the strip decomposition) -/

/-- If an analytic function on an interval has nowhere vanishing derivative in the interior, then it
is strictly monotone (or strictly antitone) on the interval. -/
theorem strictMonoOn_or_strictAntiOn_of_deriv_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (h0 : ∀ x ∈ Ioo a b, deriv f x ≠ 0) :
    StrictMonoOn f (Icc a b) ∨ StrictAntiOn f (Icc a b) := by
  have hdc : ContinuousOn (deriv f) (Ioo a b) :=
    (hf.deriv.continuousOn).mono (by rw [← interior_Icc]; exact interior_subset)
  have hsign : (∀ x ∈ Ioo a b, 0 < deriv f x) ∨ (∀ x ∈ Ioo a b, deriv f x < 0) := by
    by_cases h : ∃ x ∈ Ioo a b, 0 < deriv f x
    · left
      intro y hy
      by_contra hle
      have hyneg : deriv f y < 0 := lt_of_le_of_ne (not_lt.mp hle) (h0 y hy)
      obtain ⟨x, hx, hxpos⟩ := h
      rcases lt_trichotomy x y with hlt | heq | hgt
      · obtain ⟨z, hz, hz0⟩ := (intermediate_value_Icc hlt.le
          ((hdc.mono (Icc_subset_Ioo hx.1 hy.2)).neg))
          (show (0:ℝ) ∈ Icc ((-deriv f) x) ((-deriv f) y) from by
            refine ⟨?_, ?_⟩
            · simp only [Pi.neg_apply]; linarith [hxpos]
            · simp only [Pi.neg_apply]; linarith [hyneg])
        exact absurd (by simpa only [Pi.neg_apply, neg_eq_zero] using hz0)
          (h0 z (Icc_subset_Ioo hx.1 hy.2 hz))
      · rw [heq] at hxpos; linarith
      · obtain ⟨z, hz, hz0⟩ := (intermediate_value_Icc hgt.le
          (hdc.mono (Icc_subset_Ioo hy.1 hx.2)))
          (show (0:ℝ) ∈ Icc (deriv f y) (deriv f x) from
            ⟨by linarith [hyneg], by linarith [hxpos]⟩)
        exact absurd hz0 (h0 z (Icc_subset_Ioo hy.1 hx.2 hz))
    · right
      intro y hy
      have hy' : ¬ (0 < deriv f y) := fun hc => h ⟨y, hy, hc⟩
      exact lt_of_le_of_ne (not_lt.mp hy') (h0 y hy)
  rcases hsign with h | h
  · exact Or.inl (strictMonoOn_of_deriv_pos (convex_Icc a b) hf.continuousOn
      (by rw [interior_Icc]; exact h))
  · exact Or.inr (strictAntiOn_of_deriv_neg (convex_Icc a b) hf.continuousOn
      (by rw [interior_Icc]; exact h))

/-- A strictly monotone continuous function on an interval is a homeomorphism onto the interval
between its endpoint values. -/
theorem exists_homeomorph_Icc_of_strictMonoOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (Icc a b)) :
    ∃ e : Icc a b ≃ₜ Icc (f a) (f b), ∀ x : Icc a b, (e x : ℝ) = f x.1 := by
  have hL : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hR : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hsub : ∀ x ∈ Icc a b, f x ∈ Icc (f a) (f b) := by
    intro x hx
    exact ⟨(hmono.le_iff_le hL hx).mpr hx.1, (hmono.le_iff_le hx hR).mpr hx.2⟩
  have hinj : Function.Injective (fun x : Icc a b => (⟨f x.1, hsub x.1 x.2⟩ : Icc (f a) (f b))) := by
    intro x y hxy
    have h1 : f x.1 = f y.1 := congrArg Subtype.val hxy
    rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
    · exact absurd h1 (ne_of_lt (hmono x.2 y.2 hlt))
    · exact Subtype.ext heq
    · exact absurd h1.symm (ne_of_lt (hmono y.2 x.2 hgt))
  have hsurj : Function.Surjective (fun x : Icc a b => (⟨f x.1, hsub x.1 x.2⟩ : Icc (f a) (f b))) := by
    intro y
    have hy : y.1 ∈ f '' Icc a b := intermediate_value_Icc hab.le hf y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hbij : Function.Bijective (fun x : Icc a b => (⟨f x.1, hsub x.1 x.2⟩ : Icc (f a) (f b))) :=
    ⟨hinj, hsurj⟩
  let Φ : Icc a b → Icc (f a) (f b) := fun x => ⟨f x.1, hsub x.1 x.2⟩
  let e : Icc a b ≃ Icc (f a) (f b) := Equiv.ofBijective Φ hbij
  have hcont : Continuous ⇑e :=
    Continuous.subtype_mk (hf.comp_continuous continuous_subtype_val (fun x => x.2))
      (fun x => hsub x.1 x.2)
  haveI : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  refine ⟨Continuous.homeoOfEquivCompactToT2 hcont, fun x => ?_⟩
  show ((e x : Icc (f a) (f b)) : ℝ) = f x.1
  rw [show e x = Φ x from Equiv.ofBijective_apply Φ hbij x]

/-- The inverse of a strictly monotone continuous function on an interval is continuous. -/
theorem exists_continuousOn_inv_of_strictMonoOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (Icc a b)) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc (f a) (f b)) ∧ (∀ x ∈ Icc a b, g (f x) = x) ∧
      (∀ y ∈ Icc (f a) (f b), f (g y) = y) := by
  obtain ⟨e, he⟩ := exists_homeomorph_Icc_of_strictMonoOn hab hf hmono
  have hL : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hR : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hsub : ∀ x ∈ Icc a b, f x ∈ Icc (f a) (f b) := by
    intro x hx
    exact ⟨(hmono.le_iff_le hL hx).mpr hx.1, (hmono.le_iff_le hx hR).mpr hx.2⟩
  refine ⟨fun y => if hy : y ∈ Icc (f a) (f b) then ((e.symm ⟨y, hy⟩ : Icc a b) : ℝ) else a,
    ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Icc (f a) (f b)).domRestrict
        (fun y => if hy : y ∈ Icc (f a) (f b) then ((e.symm ⟨y, hy⟩ : Icc a b) : ℝ) else a)
        = fun y : Icc (f a) (f b) => ((e.symm y : Icc a b) : ℝ) := by
      funext y
      simp only [Set.domRestrict_def]
      rw [dif_pos y.2]
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  · intro x hx
    have h1 : e ⟨x, hx⟩ = (⟨f x, hsub x hx⟩ : Icc (f a) (f b)) := Subtype.ext (he ⟨x, hx⟩)
    simp only []
    rw [dif_pos (hsub x hx), ← h1, Homeomorph.symm_apply_apply]
  · intro y hy
    show f (if hy : y ∈ Icc (f a) (f b) then ((e.symm ⟨y, hy⟩ : Icc a b) : ℝ) else a) = y
    rw [dif_pos hy]
    have h2 : (e (e.symm ⟨y, hy⟩) : Icc (f a) (f b)) = ⟨y, hy⟩ := Homeomorph.apply_symm_apply e _
    rw [← he (e.symm ⟨y, hy⟩)]
    exact congrArg Subtype.val h2



/-! ### Disjointness of the layers (step 2, disjointness half) -/

/-- The interior of a graph region is the open slice description. -/
theorem interior_graphRegion {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h) {c d : ℝ}
    (hcd : c < d) :
    interior (graphRegion g h c d)
      = {z : ℂ | c < z.re ∧ z.re < d ∧ g z.re < z.im ∧ z.im < h z.re} := by
  refine Subset.antisymm ?_ ?_
  · intro z hz
    have hzr : z ∈ graphRegion g h c d := interior_subset hz
    obtain ⟨h1, h2, h3⟩ := hzr
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    have hshift : ∀ w : ℂ, w ∈ Metric.ball z ε → w ∈ graphRegion g h c d :=
      fun w hw => interior_subset (hε hw)
    have hnorm_re : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := by
      intro r
      have h2 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
      rw [← Real.sqrt_sq (norm_nonneg ((r : ℝ) : ℂ)), h2, Real.sqrt_sq_eq_abs]
    have hnorm_i : ∀ r : ℝ, ‖((r : ℝ) : ℂ) * Complex.I‖ = |r| := by
      intro r; rw [norm_mul, hnorm_re r, Complex.norm_I, mul_one]
    have hball_add : ∀ v : ℂ, ‖v‖ < ε → z + v ∈ Metric.ball z ε := by
      intro v hv; rw [Metric.mem_ball, dist_self_add_left]; exact hv
    have hlt_half : ‖(((ε / 2 : ℝ)) : ℂ)‖ < ε := by
      rw [hnorm_re]; rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith
    have hlt_half_i : ‖(((ε / 2 : ℝ)) : ℂ) * Complex.I‖ < ε := by
      rw [hnorm_i]; rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]; linarith
    have hhalf : (0:ℝ) < ε / 2 := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra hcon
      push_neg at hcon
      have hzc : z.re = c := le_antisymm hcon h1.1
      have hmem := hshift (z - (ε / 2 : ℝ)) (by
        rw [show z - ((ε / 2 : ℝ) : ℂ) = z + (-(((ε / 2 : ℝ)) : ℂ)) by ring]
        exact hball_add _ (by rw [norm_neg]; exact hlt_half))
      have hre : (z - (ε / 2 : ℝ)).re = z.re - ε / 2 := by simp
      have h2' : c ≤ z.re - ε / 2 := hre ▸ hmem.1.1
      linarith
    · by_contra hcon
      push_neg at hcon
      have hzd : z.re = d := le_antisymm h1.2 hcon
      have hmem := hshift (z + (ε / 2 : ℝ)) (hball_add _ hlt_half)
      have hre : (z + (ε / 2 : ℝ)).re = z.re + ε / 2 := by simp
      have h2' : z.re + ε / 2 ≤ d := hre ▸ hmem.1.2
      linarith
    · by_contra hcon
      push_neg at hcon
      have hzc : z.im = g z.re := le_antisymm hcon h2
      have hmem := hshift (z - ((ε / 2 : ℝ) : ℂ) * Complex.I) (by
        rw [show z - ((ε / 2 : ℝ) : ℂ) * Complex.I = z + (-(((ε / 2 : ℝ)) : ℂ) * Complex.I) by ring]
        exact hball_add _ (by rw [neg_mul, norm_neg]; exact hlt_half_i))
      have hre : (z - (ε / 2 : ℝ) * Complex.I).re = z.re := by simp
      have him : (z - (ε / 2 : ℝ) * Complex.I).im = z.im - ε / 2 := by simp
      have h2' : g (z - (ε / 2 : ℝ) * Complex.I).re ≤ (z - (ε / 2 : ℝ) * Complex.I).im := hmem.2.1
      rw [hre, him, hzc] at h2'
      linarith
    · by_contra hcon
      push_neg at hcon
      have hzc : z.im = h z.re := le_antisymm h3 hcon
      have hmem := hshift (z + ((ε / 2 : ℝ) : ℂ) * Complex.I) (hball_add _ hlt_half_i)
      have hre : (z + (ε / 2 : ℝ) * Complex.I).re = z.re := by simp
      have him : (z + (ε / 2 : ℝ) * Complex.I).im = z.im + ε / 2 := by simp
      have h2' : (z + (ε / 2 : ℝ) * Complex.I).im ≤ h (z + (ε / 2 : ℝ) * Complex.I).re := hmem.2.2
      rw [hre, him, hzc] at h2'
      linarith
  · intro z hz
    exact interior_graphRegion_subset hg hh hz

/-- Two graph regions whose bounding graphs are ordered have disjoint interiors. -/
theorem graphRegion_interiors_disjoint {f₁ f₂ f₃ f₄ : ℝ → ℝ} (h₁ : Continuous f₁)
    (h₂ : Continuous f₂) (h₃ : Continuous f₃) (h₄ : Continuous f₄) {c d : ℝ} (hcd : c < d)
    (hgap : ∀ x ∈ Icc c d, f₂ x ≤ f₃ x) :
    interior (graphRegion f₁ f₂ c d) ∩ interior (graphRegion f₃ f₄ c d) = ∅ := by
  rw [interior_graphRegion h₁ h₂ hcd, interior_graphRegion h₃ h₄ hcd]
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  obtain ⟨hz1, hz2⟩ := hz
  exact absurd (hgap z.re ⟨hz1.1.le, hz1.2.1.le⟩)
    (not_le.mpr (by linarith [hz1.2.2.2, hz2.2.2.1]))

/-- Graph regions in strips with disjoint interiors have disjoint interiors. -/
theorem graphRegion_interiors_disjoint_strips {f₁ f₂ f₃ f₄ : ℝ → ℝ} (h₁ : Continuous f₁)
    (h₂ : Continuous f₂) (h₃ : Continuous f₃) (h₄ : Continuous f₄) {c d c' d' : ℝ}
    (hcd : c < d) (hc'd' : c' < d') (hsep : d ≤ c') :
    interior (graphRegion f₁ f₂ c d) ∩ interior (graphRegion f₃ f₄ c' d') = ∅ := by
  rw [interior_graphRegion h₁ h₂ hcd, interior_graphRegion h₃ h₄ hc'd']
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  obtain ⟨hz1, hz2⟩ := hz
  linarith [hz1.2.1, hz2.1, hsep]


/-! ### The strip decomposition: components of `{X ∈ (c,d)}` and their graphs -/

/-- A connected component of a bounded-below-and-above open subset of `ℝ` is the open interval
between its infimum and supremum. -/
lemma connectedComponentIn_eq_Ioo {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    (hbb : BddBelow (connectedComponentIn U x)) (hba : BddAbove (connectedComponentIn U x)) :
    connectedComponentIn U x
      = Ioo (sInf (connectedComponentIn U x)) (sSup (connectedComponentIn U x)) := by
  set C := connectedComponentIn U x with hC
  have hCne : C.Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hCnU : C ⊆ U := connectedComponentIn_subset U x
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hcord : C.OrdConnected := hpre.ordConnected
  have hmax : ∀ s : Set ℝ, IsPreconnected s → x ∈ s → s ⊆ U → s ⊆ C :=
    fun s hs hxs hsU => IsPreconnected.subset_connectedComponentIn hs hxs hsU
  have hsinf : sInf C ∉ C := by
    intro hmem
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hU (sInf C) (hCnU hmem)
    have hball : Ioo (sInf C - ε) (sInf C + ε) ⊆ U := by
      intro y hy
      exact hε (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]
                   exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    have hsub : Icc (sInf C - ε / 2) (sInf C) ⊆ U := by
      refine (Icc_subset_Ioo (by linarith [hεpos]) (by linarith [hεpos])).trans hball
    have hpre2 : IsPreconnected (C ∪ Icc (sInf C - ε / 2) (sInf C)) :=
      IsPreconnected.union (sInf C) hmem ⟨by linarith [hεpos], le_rfl⟩ hpre isPreconnected_Icc
    have hsub2 : C ∪ Icc (sInf C - ε / 2) (sInf C) ⊆ U := union_subset hCnU hsub
    have hmem' : x ∈ C ∪ Icc (sInf C - ε / 2) (sInf C) := Or.inl (mem_connectedComponentIn hx)
    have hle := csInf_le hbb (hmax _ hpre2 hmem' hsub2 (Or.inr ⟨le_rfl, by linarith [hεpos]⟩))
    linarith [hεpos]
  have hssup : sSup C ∉ C := by
    intro hmem
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hU (sSup C) (hCnU hmem)
    have hball : Ioo (sSup C - ε) (sSup C + ε) ⊆ U := by
      intro y hy
      exact hε (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]
                   exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    have hsub : Icc (sSup C) (sSup C + ε / 2) ⊆ U := by
      refine (Icc_subset_Ioo (by linarith [hεpos]) (by linarith [hεpos])).trans hball
    have hpre2 : IsPreconnected (C ∪ Icc (sSup C) (sSup C + ε / 2)) :=
      IsPreconnected.union (sSup C) hmem ⟨le_rfl, by linarith [hεpos]⟩ hpre isPreconnected_Icc
    have hsub2 : C ∪ Icc (sSup C) (sSup C + ε / 2) ⊆ U := union_subset hCnU hsub
    have hmem' : x ∈ C ∪ Icc (sSup C) (sSup C + ε / 2) := Or.inl (mem_connectedComponentIn hx)
    have hle := le_csSup hba (hmax _ hpre2 hmem' hsub2 (Or.inr ⟨by linarith [hεpos], le_rfl⟩))
    linarith [hεpos]
  refine Subset.antisymm ?_ ?_
  · intro y hy
    refine ⟨lt_of_le_of_ne (csInf_le hbb hy) ?_, lt_of_le_of_ne (le_csSup hba hy) ?_⟩
    · intro h
      exact hsinf (h ▸ hy)
    · intro h
      exact hssup (h ▸ hy)
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hlow : ∃ c ∈ C, c < y := by
      by_contra hcon
      push_neg at hcon
      exact absurd (le_csInf hCne hcon) (not_le.mpr hy1)
    obtain ⟨c, hc, hcy⟩ := hlow
    have hhigh : ∃ c' ∈ C, y < c' := by
      by_contra hcon
      push_neg at hcon
      exact absurd (csSup_le hCne hcon) (not_le.mpr hy2)
    obtain ⟨c', hc', hcy'⟩ := hhigh
    exact hcord.out hc hc' ⟨le_of_lt hcy, le_of_lt hcy'⟩

/-- The infimum of a connected component of an open subset of `ℝ` is not in that open set. -/
lemma sInf_connectedComponentIn_notMem {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    (hbb : BddBelow (connectedComponentIn U x)) : sInf (connectedComponentIn U x) ∉ U := by
  set C := connectedComponentIn U x with hC
  have hCne : C.Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hCnU : C ⊆ U := connectedComponentIn_subset U x
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hcord : C.OrdConnected := hpre.ordConnected
  have hmax : ∀ s : Set ℝ, IsPreconnected s → x ∈ s → s ⊆ U → s ⊆ C :=
    fun s hs hxs hsU => IsPreconnected.subset_connectedComponentIn hs hxs hsU
  have hxc : x ∈ C := mem_connectedComponentIn hx
  have hmid : ∀ y ∈ Ioo (sInf C) x, y ∈ C := by
    intro y hy
    have hlow : ∃ c ∈ C, c < y := by
      by_contra hcon
      push_neg at hcon
      exact absurd (le_csInf hCne hcon) (not_le.mpr hy.1)
    obtain ⟨c, hc, hcy⟩ := hlow
    exact hcord.out hc hxc ⟨le_of_lt hcy, le_of_lt hy.2⟩
  intro hmem
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hU (sInf C) hmem
  have hball : Ioo (sInf C - ε) (sInf C + ε) ⊆ U := by
    intro y hy
    exact hε (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]
                 exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hsub : Icc (sInf C - ε / 2) x ⊆ U := by
    intro y hy
    rcases lt_or_ge y (sInf C) with hlt | hge
    · exact hball ⟨by linarith [hy.1], by linarith [hlt]⟩
    · rcases eq_or_lt_of_le hge with heq | hgt
      · rw [← heq]; exact hmem
      · rcases eq_or_lt_of_le hy.2 with heq2 | hlt2
        · exact heq2 ▸ hCnU hxc
        · exact hCnU (hmid y ⟨hgt, hlt2⟩)
  have hSpre : IsPreconnected (Icc (sInf C - ε / 2) x) := isPreconnected_Icc
  have hSx : x ∈ Icc (sInf C - ε / 2) x := ⟨by linarith [hεpos, csInf_le hbb hxc], le_rfl⟩
  have hin : sInf C - ε / 2 ∈ C :=
    hmax _ hSpre hSx hsub ⟨le_rfl, by linarith [hεpos, csInf_le hbb hxc]⟩
  have := csInf_le hbb hin
  linarith [hεpos]

/-- The supremum of a connected component of an open subset of `ℝ` is not in that open set. -/
lemma sSup_connectedComponentIn_notMem {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    (hba : BddAbove (connectedComponentIn U x)) : sSup (connectedComponentIn U x) ∉ U := by
  set C := connectedComponentIn U x with hC
  have hCne : C.Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hCnU : C ⊆ U := connectedComponentIn_subset U x
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hcord : C.OrdConnected := hpre.ordConnected
  have hmax : ∀ s : Set ℝ, IsPreconnected s → x ∈ s → s ⊆ U → s ⊆ C :=
    fun s hs hxs hsU => IsPreconnected.subset_connectedComponentIn hs hxs hsU
  have hxc : x ∈ C := mem_connectedComponentIn hx
  have hmid : ∀ y ∈ Ioo x (sSup C), y ∈ C := by
    intro y hy
    have hhigh : ∃ c ∈ C, y < c := by
      by_contra hcon
      push_neg at hcon
      exact absurd (csSup_le hCne hcon) (not_le.mpr hy.2)
    obtain ⟨c, hc, hcy⟩ := hhigh
    exact hcord.out hxc hc ⟨le_of_lt hy.1, le_of_lt hcy⟩
  intro hmem
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hU (sSup C) hmem
  have hball : Ioo (sSup C - ε) (sSup C + ε) ⊆ U := by
    intro y hy
    exact hε (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]
                 exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hsub : Icc x (sSup C + ε / 2) ⊆ U := by
    intro y hy
    rcases lt_or_ge y (sSup C) with hgt | hle
    · rcases eq_or_lt_of_le hy.1 with heq | hlt2
      · exact heq ▸ hCnU hxc
      · exact hCnU (hmid y ⟨hlt2, hgt⟩)
    · rcases eq_or_lt_of_le hle with heq | hlt
      · rw [← heq]; exact hmem
      · exact hball ⟨by linarith [hlt], by linarith [hy.2]⟩
  have hSpre : IsPreconnected (Icc x (sSup C + ε / 2)) := isPreconnected_Icc
  have hSx : x ∈ Icc x (sSup C + ε / 2) :=
    ⟨le_rfl, by linarith [hεpos, le_csSup hba hxc]⟩
  have hin : sSup C + ε / 2 ∈ C :=
    hmax _ hSpre hSx hsub ⟨by linarith [hεpos, le_csSup hba hxc], le_rfl⟩
  have := le_csSup hba hin
  linarith [hεpos]

/-- A continuous function on an open interval that never vanishes has constant sign. -/
lemma sign_const_of_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hcont : ContinuousOn f (Ioo a b))
    (h0 : ∀ x ∈ Ioo a b, f x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < f x) ∨ (∀ x ∈ Ioo a b, f x < 0) := by
  by_cases h : ∃ x ∈ Ioo a b, 0 < f x
  · left
    intro y hy
    by_contra hle
    have hyneg : f y < 0 := lt_of_le_of_ne (not_lt.mp hle) (h0 y hy)
    obtain ⟨x, hx, hxpos⟩ := h
    rcases lt_trichotomy x y with hlt | heq | hgt
    · obtain ⟨z, hz, hz0⟩ := (intermediate_value_Icc hlt.le
        ((hcont.mono (Icc_subset_Ioo hx.1 hy.2)).neg))
        (show (0:ℝ) ∈ Icc ((-f) x) ((-f) y) from ⟨by simp only [Pi.neg_apply]; linarith,
                                                  by simp only [Pi.neg_apply]; linarith⟩)
      exact absurd (by simpa only [Pi.neg_apply, neg_eq_zero] using hz0)
        (h0 z (Icc_subset_Ioo hx.1 hy.2 hz))
    · rw [heq] at hxpos; linarith
    · obtain ⟨z, hz, hz0⟩ := (intermediate_value_Icc hgt.le
        (hcont.mono (Icc_subset_Ioo hy.1 hx.2)))
        (show (0:ℝ) ∈ Icc (f y) (f x) from ⟨by linarith, by linarith⟩)
      exact absurd hz0 (h0 z (Icc_subset_Ioo hy.1 hx.2 hz))
  · right
    intro y hy
    have hy' : ¬ (0 < f y) := fun hc => h ⟨y, hy, hc⟩
    exact lt_of_le_of_ne (not_lt.mp hy') (h0 y hy)


/-- Each connected component of the open set where `X` takes values strictly inside `(c,d)` is the
graph of a continuous function on `[c,d]`. -/
lemma exists_graph_of_component {X Y : ℝ → ℝ} {c d : ℝ} (hcd : c < d) (hXc : Continuous X)
    (hYc : Continuous Y)
    (han : ∀ t : ℝ, X t ∈ Icc c d → AnalyticAt ℝ X t)
    (hseam0 : X 0 ∉ Ioo c d)
    (hseam2 : X (2 * Real.pi) ∉ Ioo c d)
    (hnoc : ∀ t : ℝ, deriv X t = 0 → X t ∈ Ioo c d → False)
    {t : ℝ} (ht : t ∈ Ioo 0 (2 * Real.pi) ∩ X ⁻¹' Ioo c d) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc c d) ∧
      (∀ s ∈ connectedComponentIn (Ioo 0 (2 * Real.pi) ∩ X ⁻¹' Ioo c d) t, Y s = g (X s)) ∧
      (∀ x ∈ Ioo c d, ∃ s ∈ connectedComponentIn (Ioo 0 (2 * Real.pi) ∩ X ⁻¹' Ioo c d) t, X s = x) ∧
      (∀ s ∈ connectedComponentIn (Ioo 0 (2 * Real.pi) ∩ X ⁻¹' Ioo c d) t,
        ∀ s' ∈ connectedComponentIn (Ioo 0 (2 * Real.pi) ∩ X ⁻¹' Ioo c d) t, X s = X s' → s = s') := by
  set U : Set ℝ := Ioo 0 (2 * Real.pi) ∩ X ⁻¹' Ioo c d with hUdef
  have hUopen : IsOpen U := isOpen_Ioo.inter (isOpen_Ioo.preimage hXc)
  set C := connectedComponentIn U t with hCdef
  have htC : t ∈ C := mem_connectedComponentIn ht
  have hCne : C.Nonempty := ⟨t, htC⟩
  have hCnU : C ⊆ U := connectedComponentIn_subset U t
  have hCU : ∀ s ∈ C, X s ∈ Ioo c d := fun s hs => (hCnU hs).2
  have hbdd : BddBelow C := ⟨0, fun y hy => (hCnU hy).1.1.le⟩
  have hba : BddAbove C := ⟨2 * Real.pi, fun y hy => (hCnU hy).1.2.le⟩
  have hCeq : C = Ioo (sInf C) (sSup C) := connectedComponentIn_eq_Ioo hUopen ht hbdd hba
  set α := sInf C with hαdef
  set β := sSup C with hβdef
  have hCeq' : C = Ioo α β := hCeq
  have hαle : α ≤ t := by rw [hαdef]; exact csInf_le hbdd htC
  have htleβ : t ≤ β := by rw [hβdef]; exact le_csSup hba htC
  have hαβ : α < β := by
    rcases lt_or_eq_of_le (hαle.trans htleβ) with h | h
    · exact h
    · exfalso
      have h2 : t ∈ Ioo α β := by rw [hCeq'] at htC; exact htC
      rw [h] at h2
      exact absurd h2 (by simp)
  have hαcl : α ∈ closure C := by
    rw [hCeq', closure_Ioo (ne_of_lt hαβ)]
    exact left_mem_Icc.mpr hαβ.le
  have hβcl : β ∈ closure C := by
    rw [hCeq', closure_Ioo (ne_of_lt hαβ)]
    exact right_mem_Icc.mpr hαβ.le
  have hαnonneg : 0 ≤ α := le_csInf hCne (fun y hy => (hCnU hy).1.1.le)
  have hβ2pi : β ≤ 2 * Real.pi := csSup_le hCne (fun y hy => (hCnU hy).1.2.le)
  have hαnotU : α ∉ U := hαdef ▸ sInf_connectedComponentIn_notMem hUopen ht hbdd
  have hβnotU : β ∉ U := hβdef ▸ sSup_connectedComponentIn_notMem hUopen ht hba
  -- the values of `X` at the endpoints
  have hbd_of_cl : ∀ p : ℝ, p ∈ closure C → X p ∈ Icc c d := by
    intro p hp
    have himg : X '' C ⊆ Ioo c d := fun z ⟨s, hs, hzs⟩ => hzs ▸ hCU s hs
    have h1 : X p ∈ closure (X '' C) := by
      rw [mem_closure_iff_nhds]
      intro V hV
      have hpre : X ⁻¹' V ∈ 𝓝 p := (hXc.continuousAt).preimage_mem_nhds hV
      obtain ⟨s, hsV, hsC⟩ := mem_closure_iff_nhds.mp hp (X ⁻¹' V) hpre
      exact ⟨X s, hsV, ⟨s, hsC, rfl⟩⟩
    rw [← closure_Ioo (ne_of_lt hcd)]
    exact closure_mono himg h1
  have hXαbd : X α ∈ Icc c d := hbd_of_cl α hαcl
  have hXβbd : X β ∈ Icc c d := hbd_of_cl β hβcl
  have hXαout : X α ∉ Ioo c d := by
    intro hmem
    rcases eq_or_lt_of_le hαnonneg with h0 | hpos
    · rw [← h0] at hmem
      exact hseam0 hmem
    · exact hαnotU ⟨⟨hpos, lt_of_lt_of_le hαβ hβ2pi⟩, hmem⟩
  have hXβout : X β ∉ Ioo c d := by
    intro hmem
    rcases eq_or_lt_of_le hβ2pi with h2 | hlt
    · rw [h2] at hmem
      exact hseam2 hmem
    · exact hβnotU ⟨⟨hαnonneg.trans_lt hαβ, hlt⟩, hmem⟩
  have hXα : X α = c ∨ X α = d := by
    rcases eq_or_lt_of_le hXαbd.1 with h | h
    · exact Or.inl h.symm
    · refine Or.inr (le_antisymm hXαbd.2 ?_)
      by_contra hd
      exact hXαout ⟨h, lt_of_not_ge hd⟩
  have hXβ : X β = c ∨ X β = d := by
    rcases eq_or_lt_of_le hXβbd.1 with h | h
    · exact Or.inl h.symm
    · refine Or.inr (le_antisymm hXβbd.2 ?_)
      by_contra hd
      exact hXβout ⟨h, lt_of_not_ge hd⟩
  -- monotonicity on `[α, β]`
  have hsign : (∀ s ∈ Ioo α β, 0 < deriv X s) ∨ (∀ s ∈ Ioo α β, deriv X s < 0) := by
    refine sign_const_of_ne_zero ?_ ?_
    · intro s hs
      have hsC : s ∈ C := by rw [hCeq']; exact hs
      exact (((han s ⟨(hCU s hsC).1.le, (hCU s hsC).2.le⟩).deriv).continuousAt).continuousWithinAt
    · intro s hs
      exact fun h0 => hnoc s h0 (hCU s (by rw [hCeq']; exact hs))
  have hmono : StrictMonoOn X (Icc α β) ∨ StrictAntiOn X (Icc α β) := by
    rcases hsign with h | h
    · exact Or.inl (strictMonoOn_of_deriv_pos (convex_Icc α β) hXc.continuousOn
        (by rw [interior_Icc]; exact h))
    · exact Or.inr (strictAntiOn_of_deriv_neg (convex_Icc α β) hXc.continuousOn
        (by rw [interior_Icc]; exact h))
  have hXαβne : X α ≠ X β := by
    rcases hmono with hm | ha
    · exact ne_of_lt (hm (left_mem_Icc.mpr hαβ.le) (right_mem_Icc.mpr hαβ.le) hαβ)
    · exact ne_of_gt (ha (left_mem_Icc.mpr hαβ.le) (right_mem_Icc.mpr hαβ.le) hαβ)
  have hinjC : ∀ s ∈ C, ∀ s' ∈ C, X s = X s' → s = s' := by
    intro s hs s' hs' hss'
    rcases hmono with hm | ha
    · exact hm.injOn (by rw [hCeq'] at hs; exact ⟨hs.1.le, hs.2.le⟩)
        (by rw [hCeq'] at hs'; exact ⟨hs'.1.le, hs'.2.le⟩) hss'
    · exact ha.injOn (by rw [hCeq'] at hs; exact ⟨hs.1.le, hs.2.le⟩)
        (by rw [hCeq'] at hs'; exact ⟨hs'.1.le, hs'.2.le⟩) hss'
  have hcases : (X α = c ∧ X β = d) ∨ (X α = d ∧ X β = c) := by
    rcases hXα with h | h <;> rcases hXβ with h' | h'
    · exact absurd (h.trans h'.symm) hXαβne
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩
    · exact absurd (h.trans h'.symm) hXαβne
  rcases hmono with hm | ha
  · -- increasing branch
    have hcd' : X α = c ∧ X β = d := by
      rcases hcases with h | h
      · exact h
      · exfalso
        have := hm (left_mem_Icc.mpr hαβ.le) (right_mem_Icc.mpr hαβ.le) hαβ
        rw [h.1, h.2] at this
        exact absurd this (not_lt.mpr hcd.le)
    obtain ⟨hXαc, hXβd⟩ := hcd'
    obtain ⟨g0, hg0cont, hg0inv1, hg0inv2⟩ :=
      exists_continuousOn_inv_of_strictMonoOn hαβ hXc.continuousOn hm
    refine ⟨fun x => Y (g0 x), ?_, ?_, ?_, hinjC⟩
    · have hsets : Icc (X α) (X β) = Icc c d := by rw [hXαc, hXβd]
      rw [← hsets]
      exact hYc.comp_continuousOn hg0cont
    · intro s hs
      have hsI : s ∈ Icc α β := by
        rw [hCeq'] at hs
        exact ⟨hs.1.le, hs.2.le⟩
      change Y s = Y (g0 (X s))
      rw [hg0inv1 s hsI]
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc hαβ.le hXc.continuousOn
        (by rw [hXαc, hXβd]; exact ⟨hx.1.le, hx.2.le⟩)
      refine ⟨s, ?_, hxs⟩
      rw [hCeq']
      refine ⟨lt_of_le_of_ne hs.1 (fun h => ?_), lt_of_le_of_ne hs.2 (fun h => ?_)⟩
      · rw [← h] at hxs
        rw [hXαc] at hxs
        exact absurd hxs (ne_of_lt hx.1)
      · rw [h] at hxs
        rw [hXβd] at hxs
        exact absurd hxs (Ne.symm (ne_of_lt hx.2))
  · -- decreasing branch
    have hdc' : X α = d ∧ X β = c := by
      rcases hcases with h | h
      · exfalso
        have := ha (left_mem_Icc.mpr hαβ.le) (right_mem_Icc.mpr hαβ.le) hαβ
        rw [h.1, h.2] at this
        exact absurd this (not_lt.mpr hcd.le)
      · exact h
    obtain ⟨hXαd, hXβc⟩ := hdc'
    have hm' : StrictMonoOn (fun s => -X s) (Icc α β) := ha.neg
    have hcont' : ContinuousOn (fun s => -(X s)) (Icc α β) := hXc.continuousOn.neg
    obtain ⟨g0, hg0cont, hg0inv1, hg0inv2⟩ :=
      exists_continuousOn_inv_of_strictMonoOn hαβ hcont' hm'
    refine ⟨fun x => Y (g0 (-x)), ?_, ?_, ?_, hinjC⟩
    · have hsets : Icc ((fun s => -(X s)) α) ((fun s => -(X s)) β) = Icc (-d) (-c) := by
        simp only [Pi.neg_apply, hXαd, hXβc]
      have hg0' : ContinuousOn g0 (Icc (-d) (-c)) := hsets ▸ hg0cont
      refine hYc.comp_continuousOn ?_
      exact hg0'.comp continuous_neg.continuousOn (fun x hx => by
        simp only [mem_Icc] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    · intro s hs
      have hsI : s ∈ Icc α β := by
        rw [hCeq'] at hs
        exact ⟨hs.1.le, hs.2.le⟩
      change Y s = Y (g0 (-(X s)))
      have h1 : g0 ((fun s => -(X s)) s) = s := hg0inv1 s hsI
      simp only [Pi.neg_apply] at h1
      rw [h1]
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc hαβ.le hcont'
        (show (-x) ∈ Icc ((fun s => -(X s)) α) ((fun s => -(X s)) β) from by
          simp only [Pi.neg_apply, hXαd, hXβc, mem_Icc]
          exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      refine ⟨s, ?_, ?_⟩
      · rw [hCeq']
        refine ⟨lt_of_le_of_ne hs.1 (fun h => ?_), lt_of_le_of_ne hs.2 (fun h => ?_)⟩
        · rw [← h] at hxs
          simp only [Pi.neg_apply, hXαd] at hxs
          linarith [hx.2]
        · rw [h] at hxs
          simp only [Pi.neg_apply, hXβc] at hxs
          linarith [hx.1]
      · simp only [Pi.neg_apply] at hxs
        exact neg_inj.mp hxs

/-- **The trace of a closed analytic Jordan curve in an elementary vertical strip is a finite,
strictly ordered union of graphs.** -/
theorem exists_graphs_in_strip {γ : ℝ → ℂ} {c d : ℝ} (hcd : c < d) (hγc : Continuous γ)
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (han : ∀ t : ℝ, (γ t).re ∈ Set.Icc c d → AnalyticAt ℝ (fun s : ℝ => (γ s).re) t)
    (hseam0 : (γ 0).re ∉ Set.Ioo c d) (hseam2 : (γ (2 * Real.pi)).re ∉ Set.Ioo c d)
    (hnoc : ∀ t : ℝ, deriv (fun s : ℝ => (γ s).re) t = 0 → (γ t).re ∈ Set.Ioo c d → False)
    (hfib : ∀ v ∈ Set.Icc c d,
      {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ (γ t).re = v}.Finite) :
    ∃ (n : ℕ) (g : Fin n → ℝ → ℝ), (∀ l, ContinuousOn (g l) (Set.Icc c d)) ∧
      (∀ x ∈ Set.Ioo c d, StrictMono (fun l : Fin n => g l x)) ∧
      (∀ t ∈ Set.Icc 0 (2 * Real.pi), (γ t).re ∈ Set.Ioo c d → ∃ l, (γ t).im = g l (γ t).re) := by
  set X : ℝ → ℝ := fun t => (γ t).re with hXdef
  set Y : ℝ → ℝ := fun t => (γ t).im with hYdef
  have hXc : Continuous X := Complex.continuous_re.comp hγc
  have hYc : Continuous Y := Complex.continuous_im.comp hγc
  set x₀ : ℝ := (c + d) / 2 with hxdef
  have hxcd : x₀ ∈ Set.Ioo c d := by
    refine ⟨?_, ?_⟩ <;> · simp only [hxdef]; linarith
  set U : Set ℝ := Set.Ioo 0 (2 * Real.pi) ∩ X ⁻¹' Set.Ioo c d with hUdef
  have hTfin : ({t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ X t = x₀}).Finite :=
    hfib x₀ ⟨hxcd.1.le, hxcd.2.le⟩
  set T : Finset ℝ := hTfin.toFinset with hTdef
  have hTmem : ∀ t : ℝ, t ∈ T ↔ t ∈ Set.Icc 0 (2 * Real.pi) ∧ X t = x₀ := fun t =>
    hTfin.mem_toFinset
  have hTU : ∀ t ∈ T, t ∈ U := by
    intro t ht
    obtain ⟨h1, h2⟩ := (hTmem t).mp ht
    refine ⟨⟨lt_of_le_of_ne h1.1 ?_, lt_of_le_of_ne h1.2 ?_⟩, ?_⟩
    · intro h0
      rw [← h0] at h2
      exact hseam0 (show X 0 ∈ Set.Ioo c d from h2 ▸ hxcd)
    · intro h2pi
      rw [h2pi] at h2
      exact hseam2 (show X (2 * Real.pi) ∈ Set.Ioo c d from h2 ▸ hxcd)
    · show X t ∈ Set.Ioo c d
      rw [h2]; exact hxcd
  -- the graph attached to every `t ∈ T`
  have hgraph : ∀ t ∈ T, ∃ G : ℝ → ℝ, ContinuousOn G (Set.Icc c d) ∧
      (∀ s ∈ connectedComponentIn U t, Y s = G (X s)) ∧
      (∀ x ∈ Set.Ioo c d, ∃ s ∈ connectedComponentIn U t, X s = x) ∧
      (∀ s ∈ connectedComponentIn U t, ∀ s' ∈ connectedComponentIn U t, X s = X s' → s = s') ∧
      G x₀ = Y t := by
    intro t ht
    obtain ⟨G, hG1, hG2, hG3, hG4⟩ :=
      exists_graph_of_component hcd hXc hYc (fun s hs => han s hs) hseam0 hseam2 hnoc (hTU t ht)
    exact ⟨G, hG1, hG2, hG3, hG4, by rw [← ((hTmem t).mp ht).2]; exact (hG2 t (mem_connectedComponentIn (hTU t ht))).symm⟩
  have hgraph' : ∀ t : ℝ, ∃ G : ℝ → ℝ, t ∈ T → ContinuousOn G (Set.Icc c d) ∧
      (∀ s ∈ connectedComponentIn U t, Y s = G (X s)) ∧
      (∀ x ∈ Set.Ioo c d, ∃ s ∈ connectedComponentIn U t, X s = x) ∧
      (∀ s ∈ connectedComponentIn U t, ∀ s' ∈ connectedComponentIn U t, X s = X s' → s = s') ∧
      G x₀ = Y t := by
    intro t
    by_cases ht : t ∈ T
    · obtain ⟨G, h⟩ := hgraph t ht
      exact ⟨G, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h ht⟩
  choose G hG using hgraph'
  -- the components of two points of `T` coincide iff the points are equal
  have hcomp_eq : ∀ s t : ℝ, s ∈ T → t ∈ T →
      (connectedComponentIn U s = connectedComponentIn U t ↔ s = t) := by
    intro s t hs ht
    constructor
    · intro h
      have hsC : s ∈ connectedComponentIn U t := by rw [← h]; exact mem_connectedComponentIn (hTU s hs)
      exact (hG t ht).2.2.2.1 s hsC t (mem_connectedComponentIn (hTU t ht))
        (by rw [((hTmem s).mp hs).2, ((hTmem t).mp ht).2])
    · intro h; rw [h]
  -- sorting
  let V : Finset ℝ := T.image Y
  let e : Fin V.card ≃o ↥V := Finset.orderIsoOfFin V rfl
  have hpick : ∀ i : Fin V.card, ∃ t ∈ T, Y t = (e i : ℝ) := by
    intro i
    obtain ⟨t, ht, hYt⟩ := Finset.mem_image.mp (show (e i : ℝ) ∈ T.image Y from (e i).2)
    exact ⟨t, ht, hYt⟩
  choose tt htt hYtt using hpick
  -- two points of `T` with the same `Y`-value are equal
  have hYinj : ∀ s ∈ T, ∀ t ∈ T, Y s = Y t → s = t := by
    intro s hs t ht hY
    have hγ : γ s = γ t := by
      apply Complex.ext
      · show X s = X t
        rw [((hTmem s).mp hs).2, ((hTmem t).mp ht).2]
      · show Y s = Y t
        exact hY
    exact hinj ⟨(hTU s hs).1.1.le, (hTU s hs).1.2⟩ ⟨(hTU t ht).1.1.le, (hTU t ht).1.2⟩ hγ
  refine ⟨V.card, fun i => G (tt i), ?_, ?_, ?_⟩
  · intro i
    exact (hG (tt i) (htt i)).1
  · intro x hx i j hij
    change G (tt i) x < G (tt j) x
    have hlt : (e i : ℝ) < (e j : ℝ) := e.strictMono hij
    have hi0 : G (tt i) x₀ = (e i : ℝ) := by
      rw [(hG (tt i) (htt i)).2.2.2.2]; exact hYtt i
    have hj0 : G (tt j) x₀ = (e j : ℝ) := by
      rw [(hG (tt j) (htt j)).2.2.2.2]; exact hYtt j
    have hne : ∀ y ∈ Set.Ioo c d, G (tt i) y - G (tt j) y ≠ 0 := by
      intro y hy hzero
      obtain ⟨s, hsC, hXs⟩ := (hG (tt i) (htt i)).2.2.1 y hy
      obtain ⟨s', hsC', hXs'⟩ := (hG (tt j) (htt j)).2.2.1 y hy
      have hYs : Y s = G (tt i) y := by rw [(hG (tt i) (htt i)).2.1 s hsC, hXs]
      have hYs' : Y s' = G (tt j) y := by rw [(hG (tt j) (htt j)).2.1 s' hsC', hXs']
      have hγ : γ s = γ s' := by
        apply Complex.ext
        · show X s = X s'
          exact hXs.trans hXs'.symm
        · show Y s = Y s'
          rw [hYs, hYs', sub_eq_zero.mp hzero]
      have hsI : s ∈ Set.Ico 0 (2 * Real.pi) := by
        have h := connectedComponentIn_subset U (tt i) hsC
        exact ⟨h.1.1.le, h.1.2⟩
      have hsI' : s' ∈ Set.Ico 0 (2 * Real.pi) := by
        have h := connectedComponentIn_subset U (tt j) hsC'
        exact ⟨h.1.1.le, h.1.2⟩
      have hss : s = s' := hinj hsI hsI' hγ
      -- the two components then coincide
      have hunion : IsPreconnected (connectedComponentIn U (tt i) ∪ connectedComponentIn U (tt j)) :=
        IsPreconnected.union' ⟨s, hsC, hss ▸ hsC'⟩
          (isPreconnected_connectedComponentIn) (isPreconnected_connectedComponentIn)
      have hsub : connectedComponentIn U (tt i) ∪ connectedComponentIn U (tt j) ⊆
          connectedComponentIn U (tt i) :=
        IsPreconnected.subset_connectedComponentIn hunion
          (Or.inl (mem_connectedComponentIn (hTU (tt i) (htt i))))
          (union_subset (connectedComponentIn_subset U (tt i))
            (connectedComponentIn_subset U (tt j)))
      have heqcomp : connectedComponentIn U (tt i) = connectedComponentIn U (tt j) := by
        have h1 : connectedComponentIn U (tt j) ⊆ connectedComponentIn U (tt i) :=
          fun z hz => hsub (Or.inr hz)
        have hunion' : IsPreconnected (connectedComponentIn U (tt j) ∪ connectedComponentIn U (tt i)) :=
          IsPreconnected.union' ⟨s', hsC', hss.symm ▸ hsC⟩
            (isPreconnected_connectedComponentIn) (isPreconnected_connectedComponentIn)
        have hsub' : connectedComponentIn U (tt j) ∪ connectedComponentIn U (tt i) ⊆
            connectedComponentIn U (tt j) :=
          IsPreconnected.subset_connectedComponentIn hunion'
            (Or.inl (mem_connectedComponentIn (hTU (tt j) (htt j))))
            (union_subset (connectedComponentIn_subset U (tt j))
              (connectedComponentIn_subset U (tt i)))
        have h2 : connectedComponentIn U (tt i) ⊆ connectedComponentIn U (tt j) :=
          fun z hz => hsub' (Or.inr hz)
        exact Subset.antisymm h2 h1
      have heqt : tt i = tt j := (hcomp_eq (tt i) (tt j) (htt i) (htt j)).mp heqcomp
      have : (e i : ℝ) = (e j : ℝ) := by rw [← hYtt i, ← hYtt j, heqt]
      exact absurd this (ne_of_lt hlt)
    have hcont : ContinuousOn (fun y => G (tt i) y - G (tt j) y) (Set.Ioo c d) :=
      ((hG (tt i) (htt i)).1.mono Ioo_subset_Icc_self).sub
        (((hG (tt j) (htt j)).1.mono Ioo_subset_Icc_self))
    rcases sign_const_of_ne_zero hcont hne with hpos | hneg
    · have h1 : 0 < G (tt i) x₀ - G (tt j) x₀ := hpos x₀ hxcd
      rw [hi0, hj0] at h1
      linarith [h1, hlt]
    · exact sub_neg.mp (hneg x hx)
  · intro t ht hxt
    -- `t` lies in `U`
    have htU : t ∈ U := by
      have htI : t ∈ Set.Ioo 0 (2 * Real.pi) := by
        refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
        · intro h0
          rw [← h0] at hxt
          exact hseam0 hxt
        · intro h2pi
          rw [h2pi] at hxt
          exact hseam2 hxt
      exact ⟨htI, hxt⟩
    -- a point of `T` in the same component
    obtain ⟨G', hG'1, hG'2, hG'3, hG'4⟩ :=
      exists_graph_of_component hcd hXc hYc (fun s hs => han s hs) hseam0 hseam2 hnoc htU
    obtain ⟨s, hsC, hXs⟩ := hG'3 x₀ hxcd
    have hsT : s ∈ T := (hTmem s).mpr ⟨⟨(connectedComponentIn_subset U t hsC).1.1.le,
      (connectedComponentIn_subset U t hsC).1.2.le⟩, hXs⟩
    have hcompst : connectedComponentIn U s = connectedComponentIn U t := by
      have hunion : IsPreconnected (connectedComponentIn U s ∪ connectedComponentIn U t) :=
        IsPreconnected.union' ⟨s, mem_connectedComponentIn (hTU s hsT), hsC⟩
          (isPreconnected_connectedComponentIn) (isPreconnected_connectedComponentIn)
      have hsub : connectedComponentIn U s ∪ connectedComponentIn U t ⊆ connectedComponentIn U s :=
        IsPreconnected.subset_connectedComponentIn hunion
          (Or.inl (mem_connectedComponentIn (hTU s hsT)))
          (union_subset (connectedComponentIn_subset U s) (connectedComponentIn_subset U t))
      have h1 : connectedComponentIn U t ⊆ connectedComponentIn U s := fun z hz => hsub (Or.inr hz)
      have hunion' : IsPreconnected (connectedComponentIn U t ∪ connectedComponentIn U s) :=
        IsPreconnected.union' ⟨s, hsC, mem_connectedComponentIn (hTU s hsT)⟩
          (isPreconnected_connectedComponentIn) (isPreconnected_connectedComponentIn)
      have hsub' : connectedComponentIn U t ∪ connectedComponentIn U s ⊆ connectedComponentIn U t :=
        IsPreconnected.subset_connectedComponentIn hunion' (Or.inl (mem_connectedComponentIn htU))
          (union_subset (connectedComponentIn_subset U t) (connectedComponentIn_subset U s))
      have h2 : connectedComponentIn U s ⊆ connectedComponentIn U t := fun z hz => hsub' (Or.inr hz)
      exact Subset.antisymm h2 h1
    -- find the index of `s`
    have hVs : Y s ∈ V := Finset.mem_image.mpr ⟨s, hsT, rfl⟩
    obtain ⟨i, hi⟩ := (e.surjective ⟨Y s, hVs⟩)
    have hYi : Y (tt i) = Y s := by rw [hYtt i, hi]
    have htti : tt i = s := hYinj (tt i) (htt i) s hsT hYi
    refine ⟨i, ?_⟩
    have hcomp' : t ∈ connectedComponentIn U s := by
      rw [hcompst]; exact mem_connectedComponentIn htU
    have h1 : Y t = G s (X t) := (hG s hsT).2.1 t hcomp'
    have hGs : G s = G (tt i) := by rw [htti]
    change Y t = G (tt i) (X t)
    rw [h1, hGs]


/-! ### The left-pinch case: image identity -/

lemma leftPinch_image {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ x ∈ Ioc a b, 0 < φ x) (ha : φ a = 0) :
    (fun z : ℂ => (⟨z.re, z.im * (z.re - a) / φ z.re⟩ : ℂ)) ''
        (graphRegion (fun _ => (0:ℝ)) φ a b) = triRegion a b := by
  have hnn : ∀ x ∈ Icc a b, 0 ≤ φ x := by
    rintro x ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h, ha]
    · exact le_of_lt (hpos x ⟨h, h2⟩)
  ext z; constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hw
    have hwr : 0 ≤ w.re - a := by linarith [h1.1]
    have hwr0 : w.re - a = 0 ∨ 0 < w.re - a := by
      rcases eq_or_lt_of_le hwr with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    have hφw : 0 ≤ φ w.re := hnn w.re h1
    refine ⟨h1, ?_, ?_⟩
    · change (0:ℝ) ≤ w.im * (w.re - a) / φ w.re
      rcases hwr0 with h0 | hlt
      · rw [h0, mul_zero, zero_div]
      · have hp : 0 < φ w.re := by
          rcases eq_or_lt_of_le h1.1 with h | h
          · exact absurd (sub_eq_zero.mpr h.symm) (ne_of_gt hlt)
          · exact hpos w.re ⟨h, h1.2⟩
        exact div_nonneg (mul_nonneg h2 hwr) hp.le
    · change w.im * (w.re - a) / φ w.re ≤ w.re - a
      rcases hwr0 with h0 | hlt
      · rw [h0, mul_zero, zero_div]
      · have hp : 0 < φ w.re := by
          rcases eq_or_lt_of_le h1.1 with h | h
          · exact absurd (sub_eq_zero.mpr h.symm) (ne_of_gt hlt)
          · exact hpos w.re ⟨h, h1.2⟩
        rw [div_le_iff₀ hp]
        calc w.im * (w.re - a) ≤ φ w.re * (w.re - a) := mul_le_mul_of_nonneg_right h3 hwr
          _ = (w.re - a) * φ w.re := mul_comm _ _
  · rintro ⟨h1, h2, h3⟩
    have hφz : 0 ≤ φ z.re := hnn z.re h1
    have hzr : 0 ≤ z.re - a := by linarith [h1.1]
    have hzr0 : z.re - a = 0 ∨ 0 < z.re - a := by
      rcases eq_or_lt_of_le hzr with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    refine ⟨(⟨z.re, z.im * φ z.re / (z.re - a)⟩ : ℂ), ?_, ?_⟩
    · refine ⟨h1, ?_, ?_⟩
      · change (0:ℝ) ≤ z.im * φ z.re / (z.re - a)
        rcases hzr0 with h0 | hlt
        · rw [h0, div_zero]
        · exact div_nonneg (mul_nonneg h2 hφz) hzr
      · change z.im * φ z.re / (z.re - a) ≤ φ z.re
        rcases hzr0 with h0 | hlt
        · rw [h0, div_zero]
          exact hφz
        · have hp : 0 < φ z.re := by
            rcases eq_or_lt_of_le h1.1 with h | h
            · exact absurd (sub_eq_zero.mpr h.symm) (ne_of_gt hlt)
            · exact hpos z.re ⟨h, h1.2⟩
          rw [div_le_iff₀ hlt]
          calc z.im * φ z.re ≤ (z.re - a) * φ z.re := mul_le_mul_of_nonneg_right h3 hφz
            _ = φ z.re * (z.re - a) := mul_comm _ _
    · change (⟨z.re, (z.im * φ z.re / (z.re - a)) * (z.re - a) / φ z.re⟩ : ℂ) = z
      apply Complex.ext
      · rfl
      · change (z.im * φ z.re / (z.re - a)) * (z.re - a) / φ z.re = z.im
        rcases hzr0 with h0 | hlt
        · have him0 : z.im = 0 := by linarith [h3, h0]
          rw [him0, h0]
          simp only [zero_mul, zero_div, div_zero]
        · have hp : 0 < φ z.re := by
            rcases eq_or_lt_of_le h1.1 with h | h
            · exact absurd (sub_eq_zero.mpr h.symm) (ne_of_gt hlt)
            · exact hpos z.re ⟨h, h1.2⟩
          have hd : z.re - a ≠ 0 := ne_of_gt hlt
          field_simp

/-- Pointwise version of `continuous_re_im_mk`. -/
lemma continuousAt_re_im_mk {Y : Type*} [TopologicalSpace Y] {f g : Y → ℝ} {p : Y}
    (hf : ContinuousAt f p) (hg : ContinuousAt g p) :
    ContinuousAt (fun y => (⟨f y, g y⟩ : ℂ)) p := by
  have h : (fun y => (⟨f y, g y⟩ : ℂ)) = fun y => ((f y : ℂ) + (g y : ℂ) * Complex.I) := by
    funext y
    apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  rw [h]
  exact ((Complex.continuous_ofReal.continuousAt.comp hf).add
    ((Complex.continuous_ofReal.continuousAt.comp hg).mul continuousAt_const))

/-- **Off the pinch**, the left-pinch map is continuous. -/
lemma continuousAt_leftPinchMap {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ}
    (p : graphRegion (fun _ => (0:ℝ)) φ a b) (hp : 0 < φ p.1.re) :
    ContinuousAt (fun z : graphRegion (fun _ => (0:ℝ)) φ a b =>
      (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)) p := by
  have hnum : ContinuousAt (fun z : graphRegion (fun _ => (0:ℝ)) φ a b =>
      z.1.im * (z.1.re - a)) p :=
    ((Complex.continuous_im.comp continuous_subtype_val).continuousAt.mul
      (((Complex.continuous_re.comp continuous_subtype_val).continuousAt).sub
        continuousAt_const))
  have hden : ContinuousAt (fun z : graphRegion (fun _ => (0:ℝ)) φ a b => φ z.1.re) p :=
    (hφ.comp (Complex.continuous_re.comp continuous_subtype_val)).continuousAt
  have hquot : ContinuousAt (fun z : graphRegion (fun _ => (0:ℝ)) φ a b =>
      z.1.im * (z.1.re - a) / φ z.1.re) p :=
    hnum.div hden (ne_of_gt hp)
  exact continuousAt_re_im_mk
    (Complex.continuous_re.comp continuous_subtype_val).continuousAt hquot

/-- At the pinch, the left-pinch map takes the value `⟨a, 0⟩`. -/
lemma leftPinchMap_pinch_value {φ : ℝ → ℝ} {a b : ℝ} {p : graphRegion (fun _ => (0:ℝ)) φ a b}
    (hpa : p.1.re = a) :
    (⟨p.1.re, p.1.im * (p.1.re - a) / φ p.1.re⟩ : ℂ) = (⟨a, 0⟩ : ℂ) := by
  rw [hpa, sub_self, mul_zero, zero_div]

/-- The pointwise bound of the left-pinch map. -/
lemma leftPinchMap_abs_le {φ : ℝ → ℝ} {a b : ℝ} (z : graphRegion (fun _ => (0:ℝ)) φ a b) :
    |z.1.im * (z.1.re - a) / φ z.1.re| ≤ |z.1.re - a| := by
  obtain ⟨hz1, hz2, hz3⟩ := z.2
  have hφnn : 0 ≤ φ z.1.re := le_trans hz2 hz3
  rcases eq_or_lt_of_le hφnn with h0 | hpos
  · have him0 : z.1.im = 0 := le_antisymm (by rw [← h0] at hz3; exact hz3) hz2
    rw [him0, zero_mul, zero_div, abs_zero]
    exact abs_nonneg _
  · rw [abs_div, abs_mul, abs_of_pos hpos, div_le_iff₀ hpos]
    have him : |z.1.im| ≤ φ z.1.re := abs_le.mpr ⟨by linarith [hz2], hz3⟩
    calc |z.1.im| * |z.1.re - a| ≤ φ z.1.re * |z.1.re - a| :=
          mul_le_mul_of_nonneg_right him (abs_nonneg _)
      _ = |z.1.re - a| * φ z.1.re := mul_comm _ _

/-- The pinch branch of the continuity of the left-pinch map. -/
lemma continuousAt_leftPinchMap_of_eq {φ : ℝ → ℝ} {a b : ℝ} (ha : φ a = 0)
    {p : graphRegion (fun _ => (0:ℝ)) φ a b} (hpa : p.1.re = a) :
    ContinuousAt (fun z : graphRegion (fun _ => (0:ℝ)) φ a b =>
      (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)) p := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε/2, by linarith, fun z hz => ?_⟩
  have hz' : dist (z:ℂ) (p:ℂ) < ε/2 := by simpa only [Subtype.dist_eq] using hz
  change dist (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)
      (⟨p.1.re, p.1.im * (p.1.re - a) / φ p.1.re⟩ : ℂ) < ε
  have hΦp : (⟨p.1.re, p.1.im * (p.1.re - a) / φ p.1.re⟩ : ℂ) = (⟨a, 0⟩ : ℂ) :=
    leftPinchMap_pinch_value hpa
  have hzre : z.1.re - a = z.1.re - p.1.re := by rw [hpa]
  have hnorm : ‖(⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ) - (⟨a, 0⟩ : ℂ)‖
      ≤ 2 * |z.1.re - p.1.re| := by
    have heq : (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ) - (⟨a, 0⟩ : ℂ)
        = (⟨z.1.re - a, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ) := by
      refine Complex.ext ?_ ?_ <;> simp [Complex.sub_re, Complex.sub_im]
    rw [heq]
    have hb : ‖(⟨z.1.re - a, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)‖
        ≤ |z.1.re - a| + |z.1.im * (z.1.re - a) / φ z.1.re| :=
      Complex.norm_le_abs_re_add_abs_im _
    calc ‖(⟨z.1.re - a, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)‖
        ≤ |z.1.re - a| + |z.1.im * (z.1.re - a) / φ z.1.re| := hb
      _ ≤ |z.1.re - a| + |z.1.re - a| := by
          linarith [leftPinchMap_abs_le (φ := φ) (a := a) z]
      _ = 2 * |z.1.re - a| := by ring
      _ = 2 * |z.1.re - p.1.re| := by rw [hzre]
  have hdist : |z.1.re - p.1.re| ≤ ‖z.1 - p.1‖ := by
    have h := Complex.abs_re_le_norm (z.1 - p.1)
    rwa [Complex.sub_re] at h
  have hfin : ‖z.1 - p.1‖ = dist (z:ℂ) (p:ℂ) := by rw [dist_eq_norm]
  calc dist (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)
        (⟨p.1.re, p.1.im * (p.1.re - a) / φ p.1.re⟩ : ℂ)
      = dist (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ) (⟨a, 0⟩ : ℂ) := by rw [hΦp]
    _ = ‖(⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ) - (⟨a, 0⟩ : ℂ)‖ := dist_eq_norm _ _
    _ ≤ 2 * |z.1.re - p.1.re| := hnorm
    _ ≤ 2 * ‖z.1 - p.1‖ := by linarith [hdist]
    _ = 2 * dist (z:ℂ) (p:ℂ) := by rw [hfin]
    _ < ε := by linarith

/-- Continuity of the left-pinch map on the whole pinched region. -/
lemma continuous_leftPinchMap {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ x ∈ Ioc a b, 0 < φ x) (ha : φ a = 0) :
    Continuous (fun z : graphRegion (fun _ => (0:ℝ)) φ a b =>
      (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)) := by
  have hnn : ∀ x ∈ Icc a b, 0 ≤ φ x := by
    rintro x ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h, ha]
    · exact le_of_lt (hpos x ⟨h, h2⟩)
  rw [continuous_iff_continuousAt]
  intro p
  rcases eq_or_lt_of_le (hnn p.1.re p.2.1) with h0 | hpos'
  · have hpa : p.1.re = a := by
      by_contra hne
      have hlt : a < p.1.re := lt_of_le_of_ne p.2.1.1 (Ne.symm hne)
      have hp : 0 < φ p.1.re := hpos p.1.re ⟨hlt, p.2.1.2⟩
      rw [← h0] at hp
      exact absurd hp (lt_irrefl 0)
    exact continuousAt_leftPinchMap_of_eq ha hpa
  · exact continuousAt_leftPinchMap hφ p hpos'

/-- Injectivity of the left-pinch map on the pinched region. -/
lemma leftPinchMap_injective {φ : ℝ → ℝ} {a b : ℝ} (hpos : ∀ x ∈ Ioc a b, 0 < φ x)
    (ha : φ a = 0) :
    Function.Injective (fun z : graphRegion (fun _ => (0:ℝ)) φ a b =>
      (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)) := by
  intro z w hzw
  have h := hzw
  simp only [Complex.mk.injEq] at h
  obtain ⟨hre, him⟩ := h
  obtain ⟨hz1, hz2, hz3⟩ := z.2
  obtain ⟨hw1, hw2, hw3⟩ := w.2
  apply Subtype.ext
  change z.1 = w.1
  refine Complex.ext hre ?_
  rw [hre] at him
  rcases eq_or_ne (w.1.re - a) 0 with h0 | h0
  · have hwa : w.1.re = a := sub_eq_zero.mp h0
    have hz0 : z.1.im = 0 := by
      have h1 : z.1.im ≤ φ z.1.re := hz3
      rw [hre, hwa, ha] at h1
      exact le_antisymm h1 hz2
    have hw0 : w.1.im = 0 := by
      have h1 : w.1.im ≤ φ w.1.re := hw3
      rw [hwa, ha] at h1
      exact le_antisymm h1 hw2
    rw [hz0, hw0]
  · have hwr : a < w.1.re := by
      rcases lt_or_eq_of_le hw1.1 with h2 | h2
      · exact h2
      · exact absurd (sub_eq_zero.mpr h2.symm) h0
    have hp : 0 < φ w.1.re := hpos w.1.re ⟨hwr, hw1.2⟩
    have h2 : z.1.im * (w.1.re - a) / φ w.1.re * φ w.1.re
        = w.1.im * (w.1.re - a) / φ w.1.re * φ w.1.re := by rw [him]
    simp only [div_mul_cancel₀ _ (ne_of_gt hp)] at h2
    exact mul_right_cancel₀ h0 h2

/-- Surjectivity of the left-pinch map onto the triangle. -/
lemma leftPinchMap_surjective {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ x ∈ Ioc a b, 0 < φ x) (ha : φ a = 0) :
    ∀ w ∈ triRegion a b, ∃ z : graphRegion (fun _ => (0:ℝ)) φ a b,
      (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ) = w := by
  intro w hw
  have hw' : w ∈ (fun z : ℂ => (⟨z.re, z.im * (z.re - a) / φ z.re⟩ : ℂ)) ''
      graphRegion (fun _ => (0:ℝ)) φ a b := by
    rw [leftPinch_image hab hpos ha]
    exact hw
  rcases hw' with ⟨y, hy, hyw⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  change (⟨y.re, y.im * (y.re - a) / φ y.re⟩ : ℂ) = w
  exact hyw

/-- **The pinched lune lemma (left pinch).** -/
theorem leftPinch_homeomorph_closedBall {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a < b)
    (hpos : ∀ x ∈ Ioc a b, 0 < φ x) (ha : φ a = 0) :
    Nonempty (graphRegion (fun _ => (0:ℝ)) φ a b ≃ₜ Metric.closedBall (0:ℂ) 1) := by
  have hc : Continuous (fun z : graphRegion (fun _ => (0:ℝ)) φ a b =>
      (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)) :=
    continuous_leftPinchMap hφ hab.le hpos ha
  have hmem : ∀ z : graphRegion (fun _ => (0:ℝ)) φ a b,
      (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ) ∈ triRegion a b := by
    intro z
    have h : (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)
        ∈ (fun w : ℂ => (⟨w.re, w.im * (w.re - a) / φ w.re⟩ : ℂ)) ''
            graphRegion (fun _ => (0:ℝ)) φ a b := ⟨z.1, z.2, rfl⟩
    rwa [leftPinch_image hab.le hpos ha] at h
  let Φ : graphRegion (fun _ => (0:ℝ)) φ a b → triRegion a b :=
    fun z => ⟨(⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ), hmem z⟩
  have hΦc : Continuous Φ := Continuous.subtype_mk hc (fun z => hmem z)
  have hinj : Function.Injective Φ := by
    intro z w hzw
    have h' : (↑(Φ z) : ℂ) = ↑(Φ w) := congrArg Subtype.val hzw
    change (⟨z.1.re, z.1.im * (z.1.re - a) / φ z.1.re⟩ : ℂ)
        = (⟨w.1.re, w.1.im * (w.1.re - a) / φ w.1.re⟩ : ℂ) at h'
    exact leftPinchMap_injective hpos ha h'
  have hsurj : Function.Surjective Φ := by
    intro w
    obtain ⟨z, hz⟩ := leftPinchMap_surjective hab.le hpos ha w.1 w.2
    exact ⟨z, Subtype.ext hz⟩
  let e : graphRegion (fun _ => (0:ℝ)) φ a b ≃ triRegion a b :=
    Equiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hec : Continuous ⇑e := hΦc
  haveI : CompactSpace (graphRegion (fun _ => (0:ℝ)) φ a b) :=
    isCompact_iff_compactSpace.mp (isCompact_graphRegion continuous_const hφ hab.le)
  obtain ⟨e'⟩ := triRegion_homeomorph_closedBall hab
  exact ⟨(Continuous.homeoOfEquivCompactToT2 hec).trans e'⟩

/-- The horizontal reflection `z ↦ ⟨c - z.re, z.im⟩`. -/
noncomputable def hflip (c : ℝ) : ℂ ≃ₜ ℂ where
  toFun z := (⟨c - z.re, z.im⟩ : ℂ)
  invFun z := (⟨c - z.re, z.im⟩ : ℂ)
  left_inv z := by refine Complex.ext ?_ ?_ <;> simp
  right_inv z := by refine Complex.ext ?_ ?_ <;> simp
  continuous_toFun := continuous_re_im_mk (continuous_const.sub Complex.continuous_re)
    Complex.continuous_im
  continuous_invFun := continuous_re_im_mk (continuous_const.sub Complex.continuous_re)
    Complex.continuous_im

lemma hflip_image (c : ℝ) (g : ℝ → ℝ) (a b : ℝ) :
    hflip c '' graphRegion (fun _ => (0:ℝ)) g a b
      = graphRegion (fun _ => (0:ℝ)) (fun x => g (c - x)) (c - b) (c - a) := by
  ext z; constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hw
    refine ⟨⟨?_, ?_⟩, h2, ?_⟩
    · show c - b ≤ c - w.re
      linarith [h1.2]
    · show c - w.re ≤ c - a
      linarith [h1.1]
    · change w.im ≤ g (c - (c - w.re))
      rw [show c - (c - w.re) = w.re from by ring]
      exact h3
  · intro hz
    obtain ⟨h1, h2, h3⟩ := hz
    refine ⟨(⟨c - z.re, z.im⟩ : ℂ), ⟨⟨?_, ?_⟩, h2, ?_⟩, ?_⟩
    · show a ≤ c - z.re
      linarith [h1.2]
    · show c - z.re ≤ b
      linarith [h1.1]
    · show z.im ≤ g (c - z.re)
      exact h3
    · refine Complex.ext ?_ ?_
      · show c - (c - z.re) = z.re
        ring
      · rfl

/-- **The pinched lune lemma (right pinch).** -/
theorem rightPinch_homeomorph_closedBall {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a < b)
    (hpos : ∀ x ∈ Ico a b, 0 < φ x) (hb : φ b = 0) :
    Nonempty (graphRegion (fun _ => (0:ℝ)) φ a b ≃ₜ Metric.closedBall (0:ℂ) 1) := by
  have hφ' : Continuous (fun x : ℝ => φ (a + b - x)) := hφ.comp (by fun_prop)
  have hpos' : ∀ x ∈ Ioc a b, 0 < (fun x : ℝ => φ (a + b - x)) x := by
    intro x hx
    have hx' : a + b - x ∈ Ico a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    exact hpos _ hx'
  have h0 : (fun x : ℝ => φ (a + b - x)) a = 0 := by
    show φ (a + b - a) = 0
    rw [show a + b - a = b from by ring]
    exact hb
  obtain ⟨e⟩ := leftPinch_homeomorph_closedBall hφ' hab hpos' h0
  have himg : hflip (a + b) '' graphRegion (fun _ => (0:ℝ)) φ a b
      = graphRegion (fun _ => (0:ℝ)) (fun x => φ (a + b - x)) (a + b - b) (a + b - a) :=
    hflip_image (a + b) φ a b
  rw [show (a + b) - b = a from by ring, show (a + b) - a = b from by ring] at himg
  have e1 : Nonempty (graphRegion (fun _ => (0:ℝ)) φ a b
      ≃ₜ graphRegion (fun _ => (0:ℝ)) (fun x => φ (a + b - x)) a b) :=
    ⟨(Homeomorph.image (hflip (a + b)) _).trans (Homeomorph.setCongr himg)⟩
  obtain ⟨e1'⟩ := e1
  exact ⟨e1'.trans e⟩

/-- **The generalized lune lemma.**  The region between two continuous graphs that do not cross and
touch at most at one endpoint of the interval is homeomorphic to the closed unit disk. -/
theorem graphRegion_homeomorph_closedBall_gen {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    {a b : ℝ} (hab : a < b) (hle : ∀ x ∈ Icc a b, g x ≤ h x) (hgt : ∀ x ∈ Ioo a b, g x < h x)
    (hnd : g a < h a ∨ g b < h b) :
    Nonempty (graphRegion g h a b ≃ₜ Metric.closedBall (0:ℂ) 1) := by
  have hφc : Continuous (fun x : ℝ => h x - g x) := hh.sub hg
  have hshear : graphRegion g h a b ≃ₜ graphRegion (fun _ => (0:ℝ)) (fun x => h x - g x) a b :=
    (Homeomorph.image (shearHomeomorph g hg) _).trans (Homeomorph.setCongr (shear_image hg))
  have step : Nonempty (graphRegion (fun _ => (0:ℝ)) (fun x => h x - g x) a b
      ≃ₜ Metric.closedBall (0:ℂ) 1) := by
    rcases eq_or_lt_of_le (hle a ⟨le_refl a, hab.le⟩) with ha0 | hapos
    · have hφa : h a - g a = 0 := sub_eq_zero.mpr ha0.symm
      have hbpos : 0 < h b - g b := by
        rcases hnd with h' | h'
        · exact absurd ha0 (ne_of_lt h')
        · exact sub_pos.mpr h'
      have hposIoc : ∀ x ∈ Ioc a b, 0 < h x - g x := by
        intro x hx
        rcases eq_or_lt_of_le hx.2 with h' | h'
        · rw [h']; exact hbpos
        · exact sub_pos.mpr (hgt x ⟨hx.1, h'⟩)
      exact leftPinch_homeomorph_closedBall hφc hab hposIoc hφa
    · rcases eq_or_lt_of_le (hle b ⟨hab.le, le_refl b⟩) with hb0 | hbpos
      · have hφb : h b - g b = 0 := sub_eq_zero.mpr hb0.symm
        have hposIco : ∀ x ∈ Ico a b, 0 < h x - g x := by
          intro x hx
          rcases eq_or_lt_of_le hx.1 with h' | h'
          · rw [← h']; exact sub_pos.mpr hapos
          · exact sub_pos.mpr (hgt x ⟨h', hx.2⟩)
        exact rightPinch_homeomorph_closedBall hφc hab hposIco hφb
      · have hposIcc : ∀ x ∈ Icc a b, 0 < h x - g x := by
          intro x hx
          rcases eq_or_lt_of_le hx.1 with h' | h'
          · rw [← h']; exact sub_pos.mpr hapos
          · rcases eq_or_lt_of_le hx.2 with h2 | h2
            · rw [h2]; exact sub_pos.mpr hbpos
            · exact sub_pos.mpr (hgt x ⟨h', h2⟩)
        exact underGraph_pos_homeomorph_closedBall hφc hab hposIcc
  obtain ⟨e1⟩ := step
  exact ⟨hshear.trans e1⟩


/-- The "tent" apex function used for degenerate graph regions. -/
def tentF (a b : ℝ → ℝ) (x₀ x₁ : ℝ) (x : ℝ) : ℝ :=
  (if a x₀ = b x₀ then x - x₀ else 1) * (if a x₁ = b x₁ then x₁ - x else 1)

/-- The region below the tent function. -/
def tentRegion (a b : ℝ → ℝ) (x₀ x₁ : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc x₀ x₁ ∧ 0 ≤ z.im ∧ z.im ≤ tentF a b x₀ x₁ z.re}

lemma convex_tentRegion {a b : ℝ → ℝ} {x₀ x₁ : ℝ} :
    Convex ℝ (tentRegion a b x₀ x₁) := by
  rintro z ⟨hzr, hzi, hz2⟩ w ⟨hwr, hwi, hw2⟩ t s ht hs hts
  rw [tentRegion]
  simp only [mem_ofPred_eq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    have h1 : t * x₀ ≤ t * z.re := by nlinarith [ht, hzr.1]
    have h2 : s * x₀ ≤ s * w.re := by nlinarith [hs, hwr.1]
    have h3 : t * x₀ + s * x₀ = x₀ := by rw [← add_mul, hts, one_mul]
    linarith
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    have h1 : t * z.re ≤ t * x₁ := by nlinarith [ht, hzr.2]
    have h2 : s * w.re ≤ s * x₁ := by nlinarith [hs, hwr.2]
    have h3 : t * x₁ + s * x₁ = x₁ := by rw [← add_mul, hts, one_mul]
    linarith
  · simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    nlinarith [hzi, hwi, ht, hs]
  · simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    by_cases h0 : a x₀ = b x₀ <;> by_cases h1 : a x₁ = b x₁
    · rw [tentF, if_pos h0, if_pos h1] at hz2 hw2 ⊢
      have hdiff : (t * z.re + s * w.re - x₀) * (x₁ - (t * z.re + s * w.re))
          = t * ((z.re - x₀) * (x₁ - z.re)) + s * ((w.re - x₀) * (x₁ - w.re))
            + t * s * (z.re - w.re)^2 := by
        rw [show s = 1 - t from by linarith]; ring
      have hts0 : 0 ≤ t * s * (z.re - w.re)^2 := by positivity
      linarith [hdiff, hts0, mul_le_mul_of_nonneg_left hz2 ht, mul_le_mul_of_nonneg_left hw2 hs]
    · rw [tentF, if_pos h0, if_neg h1, mul_one] at hz2 hw2 ⊢
      have hkey : t * (z.re - x₀) + s * (w.re - x₀) = t * z.re + s * w.re - x₀ := by
        rw [show s = 1 - t from by linarith]; ring
      linarith [mul_le_mul_of_nonneg_left hz2 ht, mul_le_mul_of_nonneg_left hw2 hs, hkey]
    · rw [tentF, if_neg h0, if_pos h1, one_mul] at hz2 hw2 ⊢
      have hkey : t * (x₁ - z.re) + s * (x₁ - w.re) = x₁ - (t * z.re + s * w.re) := by
        rw [show s = 1 - t from by linarith]; ring
      linarith [mul_le_mul_of_nonneg_left hz2 ht, mul_le_mul_of_nonneg_left hw2 hs, hkey]
    · rw [tentF, if_neg h0, if_neg h1, one_mul] at hz2 hw2 ⊢
      nlinarith [mul_le_mul_of_nonneg_left hz2 ht, mul_le_mul_of_nonneg_left hw2 hs, hts]

lemma continuous_tentF (a b : ℝ → ℝ) (x₀ x₁ : ℝ) : Continuous (tentF a b x₀ x₁) := by
  unfold tentF
  by_cases h0 : a x₀ = b x₀
  · by_cases h1 : a x₁ = b x₁
    · simp only [if_pos h0, if_pos h1]
      exact (continuous_id.sub continuous_const).mul (continuous_const.sub continuous_id)
    · simp only [if_pos h0, if_neg h1]
      exact (continuous_id.sub continuous_const).mul continuous_const
  · by_cases h1 : a x₁ = b x₁
    · simp only [if_neg h0, if_pos h1]
      exact continuous_const.mul (continuous_const.sub continuous_id)
    · simp only [if_neg h0, if_neg h1]
      exact continuous_const.mul continuous_const

lemma tentF_nonneg {a b : ℝ → ℝ} {x₀ x₁ : ℝ} (hx : x₀ ≤ x₁) {x : ℝ} (h : x ∈ Icc x₀ x₁) :
    0 ≤ tentF a b x₀ x₁ x := by
  unfold tentF
  obtain ⟨h1, h2⟩ := h
  apply mul_nonneg <;> split <;> linarith

lemma isClosed_tentRegion (a b : ℝ → ℝ) (x₀ x₁ : ℝ) :
    IsClosed (tentRegion a b x₀ x₁) := by
  have he : tentRegion a b x₀ x₁ = (Complex.re ⁻¹' Icc x₀ x₁) ∩ (Complex.im ⁻¹' Ici (0:ℝ)) ∩
      ((fun z : ℂ => z.im - tentF a b x₀ x₁ z.re) ⁻¹' Iic (0:ℝ)) := by
    ext z
    simp only [tentRegion, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Icc, mem_Ici, mem_Iic]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩
  rw [he]
  exact (((isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Ici.preimage Complex.continuous_im)).inter
    (isClosed_Iic.preimage (Complex.continuous_im.sub
      ((continuous_tentF a b x₀ x₁).comp Complex.continuous_re))))

/-- The vertical rescaling ratio. -/
noncomputable def ratio (a b : ℝ → ℝ) (z : ℂ) : ℝ := (z.im - a z.re) / (b z.re - a z.re)

/-- The "tent map" carrying the region between the graphs `a ≤ b` (degenerate at the ends where
`tentF` vanishes) onto the tent region. -/
noncomputable def tentMap (a b : ℝ → ℝ) (x₀ x₁ : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re, tentF a b x₀ x₁ z.re * ratio a b z⟩

lemma ratio_mem {a b : ℝ → ℝ} {x₀ x₁ : ℝ} (hba : ∀ x ∈ Icc x₀ x₁, a x ≤ b x)
    {z : ℂ} (hz : z ∈ graphRegion a b x₀ x₁) : ratio a b z ∈ Icc 0 1 := by
  rw [ratio]
  rcases eq_or_lt_of_le (hba z.re hz.1) with h | h
  · simp only [← h, sub_self, div_zero, mem_Icc]; norm_num
  · refine ⟨div_nonneg (by linarith [hz.2.1]) (le_of_lt (sub_pos.mpr h)),
      div_le_one (sub_pos.mpr h) |>.mpr (by linarith [hz.2.2])⟩

lemma tentMap_mem {a b : ℝ → ℝ} {x₀ x₁ : ℝ} (hba : ∀ x ∈ Icc x₀ x₁, a x ≤ b x)
    {z : ℂ} (hz : z ∈ graphRegion a b x₀ x₁) : tentMap a b x₀ x₁ z ∈ tentRegion a b x₀ x₁ := by
  obtain ⟨hr0, hr1⟩ := ratio_mem hba hz
  have hf0 : 0 ≤ tentF a b x₀ x₁ z.re :=
    tentF_nonneg (a := a) (b := b) (x₀ := x₀) (x₁ := x₁) (x := z.re) (hz.1.1.trans hz.1.2) hz.1
  refine ⟨hz.1, ?_, ?_⟩
  · show 0 ≤ tentF a b x₀ x₁ z.re * ratio a b z
    exact mul_nonneg hf0 hr0
  · show tentF a b x₀ x₁ z.re * ratio a b z ≤ tentF a b x₀ x₁ z.re
    nlinarith [hf0, hr1]

/-! ## The one-variable analytic input

Everything analytic in the disk-tiling proof reduces to the following one-variable fact: the zero set
of a real-analytic function on a closed interval is finite, unless the function is identically zero.
-/

section AnalyticInput

/-- A real-analytic function on a closed interval whose zero set in that interval is infinite
vanishes on the whole interval. -/
lemma analytic_eqOn_zero_of_infinite_zeros {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (hinf : (Icc a b ∩ f ⁻¹' {0}).Infinite) :
    ∀ x ∈ Icc a b, f x = 0 := by
  obtain ⟨x, hxK, hxacc⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc
    (Set.inter_subset_left)
  have hxan : AnalyticAt ℝ f x := hf x hxK
  have hzero : ∀ᶠ y in 𝓝 x, f y = 0 := by
    rcases hxan.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exfalso
      haveI : Filter.NeBot (𝓝[≠] x ⊓ Filter.principal (Icc a b ∩ f ⁻¹' {0})) := hxacc
      have h1 : ∀ᶠ y in (𝓝[≠] x ⊓ Filter.principal (Icc a b ∩ f ⁻¹' {0})), f y ≠ 0 := h.filter_mono inf_le_left
      have h2 : ∀ᶠ y in (𝓝[≠] x ⊓ Filter.principal (Icc a b ∩ f ⁻¹' {0})), f y = 0 := by
        apply Filter.Eventually.filter_mono inf_le_right
        rw [Filter.eventually_principal]
        exact fun y hy => hy.2
      obtain ⟨y, hy1, hy2⟩ := Filter.nonempty_of_mem (h1.and h2)
      exact hy1 hy2
  intro y hy
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf analyticOnNhd_const
    isPreconnected_Icc hxK hzero hy

/-- A real-analytic function on a closed interval that does not vanish identically has only finitely
many zeros in that interval. -/
lemma finite_zero_set_of_analyticOnNhd {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (hne : ∃ x ∈ Icc a b, f x ≠ 0) :
    (Icc a b ∩ f ⁻¹' {0}).Finite := by
  by_contra hfin
  obtain ⟨x, hx, hne'⟩ := hne
  exact hne' (analytic_eqOn_zero_of_infinite_zeros hf (Set.not_finite.mp hfin) x hx)

/-- The set of critical values of an analytic function on an interval is finite, provided the
derivative does not vanish identically there. -/
lemma finite_criticalValues {f : ℝ → ℝ} {a b : ℝ} (hf : AnalyticOnNhd ℝ f (Icc a b))
    (hne : ∃ t ∈ Icc a b, deriv f t ≠ 0) :
    {x : ℝ | ∃ t ∈ Icc a b, deriv f t = 0 ∧ f t = x}.Finite := by
  have hZ : (Icc a b ∩ (deriv f) ⁻¹' {0}).Finite :=
    finite_zero_set_of_analyticOnNhd hf.deriv hne
  have himg : {x : ℝ | ∃ t ∈ Icc a b, deriv f t = 0 ∧ f t = x}
      = f '' (Icc a b ∩ (deriv f) ⁻¹' {0}) := by
    ext x; constructor
    · rintro ⟨t, ht, h0, rfl⟩; exact ⟨t, ⟨ht, h0⟩, rfl⟩
    · rintro ⟨t, ⟨ht, h0⟩, rfl⟩; exact ⟨t, ht, h0, rfl⟩
  rw [himg]
  exact hZ.image f

/-- The fibres of an analytic function on an interval are finite, unless the function is constantly
equal to the value on the interval. -/
lemma finite_preimage_of_analytic {f : ℝ → ℝ} {a b x : ℝ} (hf : AnalyticOnNhd ℝ f (Icc a b))
    (hne : ∃ t ∈ Icc a b, f t ≠ x) : (Icc a b ∩ f ⁻¹' {x}).Finite := by
  have hsub : AnalyticOnNhd ℝ (fun t => f t - x) (Icc a b) := hf.sub analyticOnNhd_const
  have hne' : ∃ t ∈ Icc a b, (fun t => f t - x) t ≠ 0 := by
    obtain ⟨t, ht, hne'⟩ := hne
    exact ⟨t, ht, sub_ne_zero.mpr hne'⟩
  have h : (Icc a b ∩ (fun t => f t - x) ⁻¹' {0}).Finite :=
    finite_zero_set_of_analyticOnNhd hsub hne'
  rw [show (Icc a b ∩ f ⁻¹' {x}) = (Icc a b ∩ (fun t => f t - x) ⁻¹' {0}) from by
    ext t; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact and_congr_right fun _ => sub_eq_zero.symm]
  exact h

end AnalyticInput

/-! ## Ownership pieces of a locally finite closed cover

Given a locally finite closed cover `C` of `X` (indexed by `ℕ`), the sets
`piece C n = closure (C n \ ⋃ m<n, C m)` form a locally finite closed cover with pairwise disjoint
interiors.  This is the decomposition used for the disk tiling.

Main remaining input for that application: `piece C n = closure (interior (piece C n))`.
-/

/-! ## Chart disks

The closed coordinate disks used as the cover in the disk-tiling construction are closed sets that
are the closure of their interior, so the ownership lemma `piece_eq_closure_interior` applies. -/

section ChartDisk

lemma symm_image_eq_inter_preimage {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X)
    {s : Set ℂ} (hs : s ⊆ (chartAt ℂ x).target) :
    (chartAt ℂ x).symm '' s = (chartAt ℂ x).source ∩ ((chartAt ℂ x) ⁻¹' s) := by
  ext y; constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 : w ∈ (chartAt ℂ x).symm.source := by
        rw [OpenPartialHomeomorph.symm_source]; exact hs hw
      have h2 := (chartAt ℂ x).symm.mapsTo h1
      rwa [OpenPartialHomeomorph.symm_target] at h2
    · show (chartAt ℂ x) ((chartAt ℂ x).symm w) ∈ s
      rw [(chartAt ℂ x).right_inv (hs hw)]
      exact hw
  · rintro ⟨hy1, hy2⟩
    exact ⟨(chartAt ℂ x) y, hy2, (chartAt ℂ x).left_inv hy1⟩

/-- A closed coordinate disk is the closure of its interior. -/
lemma closure_interior_symm_image_closedBall {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] (x : X) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall c r ⊆ (chartAt ℂ x).target) :
    closure (interior ((chartAt ℂ x).symm '' Metric.closedBall c r)) =
      (chartAt ℂ x).symm '' Metric.closedBall c r := by
  have hball : Metric.ball c r ⊆ (chartAt ℂ x).target :=
    fun z hz => hsub (Metric.ball_subset_closedBall hz)
  have hopen : IsOpen ((chartAt ℂ x).symm '' Metric.ball c r) := by
    rw [symm_image_eq_inter_preimage x hball]
    exact (chartAt ℂ x).continuousOn_toFun.isOpen_inter_preimage (chartAt ℂ x).open_source
      isOpen_ball
  have hmono : (chartAt ℂ x).symm '' Metric.ball c r ⊆ (chartAt ℂ x).symm '' Metric.closedBall c r :=
    image_mono Metric.ball_subset_closedBall
  have hint : (chartAt ℂ x).symm '' Metric.ball c r ⊆
      interior ((chartAt ℂ x).symm '' Metric.closedBall c r) := interior_maximal hmono hopen
  have hcompact : IsCompact ((chartAt ℂ x).symm '' Metric.closedBall c r) :=
    (isCompact_closedBall c r).image_of_continuousOn ((chartAt ℂ x).continuousOn_symm.mono hsub)
  have hclosed : IsClosed ((chartAt ℂ x).symm '' Metric.closedBall c r) := hcompact.isClosed
  have hclball : closure (Metric.ball c r) = Metric.closedBall c r := closure_ball c hr.ne'
  have hclosure : closure ((chartAt ℂ x).symm '' Metric.ball c r) =
      (chartAt ℂ x).symm '' Metric.closedBall c r := by
    refine Subset.antisymm (closure_minimal hmono hclosed) ?_
    have hcont : ContinuousOn (chartAt ℂ x).symm (closure (Metric.ball c r)) :=
      (chartAt ℂ x).continuousOn_symm.mono (by rw [hclball]; exact hsub)
    have hle := ContinuousOn.image_closure hcont
    rwa [hclball] at hle
  refine Subset.antisymm (closure_minimal interior_subset hclosed) ?_
  calc (chartAt ℂ x).symm '' Metric.closedBall c r
      = closure ((chartAt ℂ x).symm '' Metric.ball c r) := hclosure.symm
    _ ⊆ closure (interior ((chartAt ℂ x).symm '' Metric.closedBall c r)) := closure_mono hint

end ChartDisk

/-! ## The finite cover in the compact case -/

section CompactCover

/-- A compact complex-charted space has a finite cover by closed coordinate disks. (In the
non-compact case such a cover is supplied by the commons lemma
`exists_locallyFinite_coordinateBall_cover_of_noncompact`.) -/
theorem exists_finite_coordinateDisk_cover_of_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [CompactSpace X] :
    ∃ (N : ℕ) (c : Fin N → X) (r : Fin N → ℝ), (∀ i, 0 < r i) ∧
      (∀ i, Metric.closedBall ((chartAt ℂ (c i)) (c i)) (r i) ⊆ (chartAt ℂ (c i)).target) ∧
      (⋃ i, (chartAt ℂ (c i)).symm '' Metric.closedBall ((chartAt ℂ (c i)) (c i)) (r i))
        = Set.univ := by
  classical
  have hchoice : ∀ x : X, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target := by
    intro x
    have hmem : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) := chart_target_mem_nhds ℂ x
    obtain ⟨e, he, hsub⟩ := Metric.mem_nhds_iff.mp hmem
    exact ⟨e/2, half_pos he, fun z hz => hsub (Metric.closedBall_subset_ball (by linarith) hz)⟩
  choose rr hrr_pos hrr_sub using hchoice
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => interior ((chartAt ℂ x).symm '' Metric.closedBall ((chartAt ℂ x) x) (rr x)))
    (fun _ => isOpen_interior)
    (fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.mpr
      ((Commons.Topology.Surface.hasBasis_nhds_coordinateBall x).mem_iff.mpr
        ⟨rr x, ⟨hrr_pos x, hrr_sub x⟩, subset_rfl⟩)⟩)
  let c : Fin t.card → X := fun i => ((Finset.equivFin t).symm i : X)
  let r : Fin t.card → ℝ := fun i => rr (c i)
  refine ⟨t.card, c, r, ?_, ?_, ?_⟩
  · intro i; exact hrr_pos (c i)
  · intro i; exact hrr_sub (c i)
  · apply eq_univ_iff_forall.2
    intro y
    have hy : y ∈ ⋃ x ∈ t, interior ((chartAt ℂ x).symm ''
        Metric.closedBall ((chartAt ℂ x) x) (rr x)) := by
      have := ht (mem_univ y); simpa using this
    rcases mem_iUnion.1 hy with ⟨x, hx⟩
    rcases mem_iUnion.1 hx with ⟨hxt, hyU⟩
    obtain ⟨i, hi⟩ := (Finset.equivFin t).symm.surjective ⟨x, hxt⟩
    have hci : c i = x := by simpa using congrArg Subtype.val hi
    have hri : r i = rr x := by
      show rr (c i) = rr x
      rw [hci]
    refine mem_iUnion.2 ⟨i, ?_⟩
    rw [hci, hri]
    exact interior_subset hyU

end CompactCover

/-! ## The curve layer: circles under holomorphic maps

The boundary curves of the pieces are images of circles under injective holomorphic chart
transitions.  This section packages the real-analyticity of such a curve (and of the real part /
norm-square of such a curve), which is what the one-variable lemmas `finite_criticalValues` and
`finite_preimage_of_analytic` are applied to.
-/

section Curve

/-- `Complex.exp` is analytic (holomorphic functions are analytic). -/
lemma analyticAt_exp (z : ℂ) : AnalyticAt ℂ Complex.exp z :=
  ((Complex.differentiable_exp.differentiableOn).analyticOnNhd isOpen_univ) z (mem_univ z)

/-- The angle-parametrised circle of radius `ρ` is complex-analytic. -/
lemma analyticAt_circleC (ρ θ : ℝ) :
    AnalyticAt ℂ (fun z : ℂ => (ρ : ℂ) * Complex.exp (Complex.I * z)) (θ : ℂ) := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => Complex.I * z) (θ : ℂ) :=
    ((Complex.I • (1 : ℂ →L[ℂ] ℂ))).analyticAt (θ : ℂ)
  have h1 : AnalyticAt ℂ (fun z : ℂ => Complex.exp (Complex.I * z)) (θ : ℂ) :=
    (analyticAt_exp (Complex.I * (θ : ℂ))).comp hlin
  have h2 := h1.const_smul (c := (ρ : ℂ))
  rwa [show ((ρ : ℂ) • fun z : ℂ => Complex.exp (Complex.I * z))
      = fun z : ℂ => (ρ : ℂ) * Complex.exp (Complex.I * z) from by
    funext z; rw [Pi.smul_apply, smul_eq_mul]] at h2

/-- The angle-parametrised circle of radius `ρ` is real-analytic. -/
lemma analyticAt_circleR (ρ θ : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))) θ := by
  have hC := analyticAt_circleC ρ θ
  have hR := hC.restrictScalars.comp ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).analyticAt θ)
  exact hR

/-- A holomorphic map composed with the angle-parametrisation of a circle is real-analytic. -/
lemma analyticAt_comp_circle {ψ : ℂ → ℂ} {ρ θ : ℝ}
    (hψ : AnalyticAt ℂ ψ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    AnalyticAt ℝ (fun t : ℝ => ψ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))) θ :=
  AnalyticAt.comp (f := fun t : ℝ => (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))
    hψ.restrictScalars (analyticAt_circleR ρ θ)

/-- The real part of a holomorphic map composed with a circle is real-analytic. -/
lemma analyticAt_re_comp_circle {ψ : ℂ → ℂ} {ρ θ : ℝ}
    (hψ : AnalyticAt ℂ ψ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    AnalyticAt ℝ (fun t : ℝ => (ψ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).re) θ :=
  AnalyticAt.comp (f := fun t : ℝ => ψ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
    ((Complex.reCLM : ℂ →L[ℝ] ℝ).analyticAt _) (analyticAt_comp_circle hψ)

/-- The norm-square of a holomorphic map composed with a circle is real-analytic. -/
lemma analyticAt_normSq_comp_circle {μ : ℂ → ℂ} {ρ θ : ℝ}
    (hμ : AnalyticAt ℂ μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    AnalyticAt ℝ (fun t : ℝ => Complex.normSq (μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))) θ := by
  have h := analyticAt_comp_circle hμ
  have hre : AnalyticAt ℝ
      (fun t : ℝ => (μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).re) θ :=
    AnalyticAt.comp (f := fun t : ℝ => μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).analyticAt _) h
  have him : AnalyticAt ℝ
      (fun t : ℝ => (μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).im) θ :=
    AnalyticAt.comp (f := fun t : ℝ => μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
      ((Complex.imCLM : ℂ →L[ℝ] ℝ).analyticAt _) h
  have h2 : AnalyticAt ℝ (fun t : ℝ =>
      (μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).re
        * (μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).re
      + (μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).im
        * (μ ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))).im) θ := (hre.mul hre).add (him.mul him)
  simpa only [Complex.normSq_apply] using h2

/-- **Finitely many crossing angles.** For a holomorphic `μ`, the angles at which the image of the
circle of radius `ρ` meets the circle of radius `r` around the origin are finite, unless the image
lies on that circle throughout. -/
theorem finite_crossing_angles {μ : ℂ → ℂ} {ρ r : ℝ}
    (hμ : ∀ θ : ℝ, AnalyticAt ℂ μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
    (hne : ∃ θ ∈ Icc 0 (2 * Real.pi),
      Complex.normSq (μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ≠ r ^ 2) :
    {θ : ℝ | θ ∈ Icc 0 (2 * Real.pi) ∧
      Complex.normSq (μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = r ^ 2}.Finite := by
  have hf : AnalyticOnNhd ℝ (fun θ : ℝ =>
      Complex.normSq (μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) - r ^ 2)
      (Icc 0 (2 * Real.pi)) :=
    fun θ _ => (analyticAt_normSq_comp_circle (hμ θ)).sub analyticAt_const
  have hne' : ∃ θ ∈ Icc 0 (2 * Real.pi),
      (fun θ : ℝ => Complex.normSq (μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) - r ^ 2) θ ≠ 0 := by
    obtain ⟨θ, hθ, hne⟩ := hne
    exact ⟨θ, hθ, sub_ne_zero.mpr hne⟩
  have hzero : (Icc 0 (2 * Real.pi) ∩ (fun θ : ℝ =>
      Complex.normSq (μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) - r ^ 2) ⁻¹' {0}).Finite :=
    finite_zero_set_of_analyticOnNhd hf hne'
  rw [show {θ : ℝ | θ ∈ Icc 0 (2 * Real.pi) ∧
      Complex.normSq (μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = r ^ 2}
      = (Icc 0 (2 * Real.pi) ∩ (fun θ : ℝ =>
        Complex.normSq (μ ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) - r ^ 2) ⁻¹' {0}) from by
    ext θ; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, sub_eq_zero]]
  exact hzero

/-- Real-analyticity of the real part of a chart transition composed with a circle: the boundary
curves of the ownership pieces are of exactly this form. -/
lemma analyticAt_transition_re_circle {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (a b : X) {ρ θ : ℝ}
    (h : (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
      ((chartAt ℂ a).symm.trans (chartAt ℂ b)).source) :
    AnalyticAt ℝ (fun t : ℝ =>
      ((chartAt ℂ b) ((chartAt ℂ a).symm ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))).re) θ := by
  have hψ : AnalyticAt ℂ (((chartAt ℂ a).symm.trans (chartAt ℂ b)) :
      ℂ → ℂ) ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    (Commons.Geometry.Manifold.chart_transition_analyticOnNhd (X := X) a b) _ h
  have hkey : AnalyticAt ℝ (fun t : ℝ =>
      (((chartAt ℂ a).symm.trans (chartAt ℂ b)) :
        ℂ → ℂ) ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))) θ :=
    analyticAt_comp_circle hψ
  have hcomp := AnalyticAt.comp (f := fun t : ℝ =>
      (((chartAt ℂ a).symm.trans (chartAt ℂ b)) : ℂ → ℂ)
        ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
    ((Complex.reCLM : ℂ →L[ℝ] ℝ).analyticAt _) hkey
  have hgoal : (fun t : ℝ => ((chartAt ℂ b) ((chartAt ℂ a).symm
      ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))).re)
      = (Complex.reCLM : ℂ →L[ℝ] ℝ) ∘ fun t : ℝ =>
          (((chartAt ℂ a).symm.trans (chartAt ℂ b)) : ℂ → ℂ)
            ((ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))) := by
    funext t
    simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply, Complex.reCLM_apply]
  rw [hgoal]
  exact hcomp

/-- The same, in `AnalyticOnNhd` form, on the set of angles for which the circle point lies in the
source of the transition. -/
lemma analyticOnNhd_transition_re_circle {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (a b : X) (ρ : ℝ) :
    AnalyticOnNhd ℝ (fun θ : ℝ =>
      ((chartAt ℂ b) ((chartAt ℂ a).symm ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))).re)
      {θ : ℝ | (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
        ((chartAt ℂ a).symm.trans (chartAt ℂ b)).source} :=
  fun _ hθ => analyticAt_transition_re_circle a b hθ

end Curve

section Ownership

variable {X : Type*} [TopologicalSpace X]

/-- The `n`-th "ownership piece" of a family of closed sets: the part of `C n` not covered by the
earlier `C m`, closed up. -/
def piece (C : ℕ → Set X) (n : ℕ) : Set X := closure (C n \ ⋃ m ∈ Set.Iio n, C m)

lemma piece_subset (C : ℕ → Set X) (hcl : ∀ n, IsClosed (C n)) (n : ℕ) : piece C n ⊆ C n :=
  (hcl n).closure_subset_iff.mpr sdiff_subset

lemma isClosed_piece (C : ℕ → Set X) (n : ℕ) : IsClosed (piece C n) := isClosed_closure

lemma locallyFinite_pieces (C : ℕ → Set X) (hcl : ∀ n, IsClosed (C n)) (hlf : LocallyFinite C) :
    LocallyFinite (piece C) :=
  hlf.subset fun n => piece_subset C hcl n

lemma iUnion_pieces (C : ℕ → Set X) (hcov : (⋃ n, C n) = Set.univ) :
    (⋃ n, piece C n) = Set.univ := by
  classical
  apply eq_univ_iff_forall.2
  intro x
  have hex : ∃ n, x ∈ C n := by
    have h1 : x ∈ ⋃ n, C n := by rw [hcov]; exact mem_univ x
    simpa using h1
  refine mem_iUnion.2 ⟨Nat.find hex, subset_closure ⟨Nat.find_spec hex, ?_⟩⟩
  intro hcon
  rcases mem_iUnion.1 hcon with ⟨m, hm⟩
  rcases mem_iUnion.1 hm with ⟨hm1, hm2⟩
  exact Nat.find_min hex hm1 hm2

lemma piece_subset_compl_interior (C : ℕ → Set X) {n m : ℕ} (hlt : m < n) :
    piece C n ⊆ (interior (C m))ᶜ := by
  have h1 : (C n \ ⋃ k ∈ Set.Iio n, C k) ⊆ (C m)ᶜ := by
    rintro y ⟨-, hy2⟩ hcon
    exact hy2 (mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨hlt, hcon⟩⟩)
  rw [piece]
  calc closure (C n \ ⋃ k ∈ Set.Iio n, C k) ⊆ closure ((C m)ᶜ) := closure_mono h1
    _ = (interior (C m))ᶜ := closure_compl

lemma disjoint_interior_pieces_lt (C : ℕ → Set X) (hcl : ∀ n, IsClosed (C n)) {n m : ℕ}
    (hlt : m < n) : interior (piece C n) ∩ interior (piece C m) = ∅ := by
  have h1 : interior (piece C n) ⊆ (interior (C m))ᶜ :=
    fun _ hy => piece_subset_compl_interior C hlt (interior_subset hy)
  have h2 : interior (piece C m) ⊆ interior (C m) := interior_mono (piece_subset C hcl m)
  have h3 : interior (piece C n) ∩ interior (piece C m) ⊆ (∅ : Set X) := by
    rintro y ⟨hy1, hy2⟩
    exact h1 hy1 (h2 hy2)
  exact Subset.antisymm h3 (Set.empty_subset _)

lemma disjoint_interior_pieces (C : ℕ → Set X) (hcl : ∀ n, IsClosed (C n)) (n m : ℕ) (hnm : n ≠ m) :
    interior (piece C n) ∩ interior (piece C m) = ∅ := by
  rcases lt_or_gt_of_ne hnm with h | h
  · have := disjoint_interior_pieces_lt (C := C) hcl (n := m) (m := n) h
    rwa [Set.inter_comm]
  · exact disjoint_interior_pieces_lt (C := C) hcl h


/-- If each `C n` is closed and is the closure of its interior, then so is each ownership piece.
This is what makes the pieces usable as "compact regions" in the disk-tiling construction. -/
lemma piece_eq_closure_interior (C : ℕ → Set X) (hcl : ∀ n, IsClosed (C n))
    (hint : ∀ n, closure (interior (C n)) = C n) (n : ℕ) :
    piece C n = closure (interior (piece C n)) := by
  have hBcl : IsClosed (⋃ m ∈ Set.Iio n, C m) :=
    (Set.finite_Iio n).isClosed_biUnion fun m _ => hcl m
  refine Subset.antisymm ?_ ?_
  · rw [piece]
    apply isClosed_closure.closure_subset_iff.mpr
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [mem_closure_iff_nhds]
    intro N hN
    have hM : {y : X | y ∉ ⋃ m ∈ Set.Iio n, C m} ∈ 𝓝 x := hBcl.isOpen_compl.mem_nhds hx2
    have hxcl : x ∈ closure (interior (C n)) := by rw [hint n]; exact hx1
    obtain ⟨y, ⟨hyN, hyB⟩, hyint⟩ :=
      mem_closure_iff_nhds.mp hxcl (N ∩ {y : X | y ∉ ⋃ m ∈ Set.Iio n, C m})
        (Filter.inter_mem hN hM)
    refine ⟨y, hyN, ?_⟩
    have hopen : IsOpen (interior (C n) \ ⋃ m ∈ Set.Iio n, C m) := isOpen_interior.sdiff hBcl
    have hsub : interior (C n) \ ⋃ m ∈ Set.Iio n, C m ⊆ piece C n :=
      fun z hz => subset_closure ⟨interior_subset hz.1, hz.2⟩
    exact interior_maximal hsub hopen ⟨hyint, hyB⟩
  · exact closure_minimal interior_subset isClosed_closure

end Ownership

/-! ## Assembly: tiling a space from tilings of the ownership pieces -/

section Assembly

/-- If a locally finite closed cover `C` of `X` by "closure of interior" sets has, for each `n`, a
finite tiling of the ownership piece `piece C n` by closed disks with pairwise disjoint interiors,
then `X` itself has a locally finite tiling by closed disks. -/
theorem exists_locallyFinite_disk_tiling_of_piece_tilings {X : Type*} [TopologicalSpace X]
    (C : ℕ → Set X) (hcl : ∀ n, IsClosed (C n)) (hlf : LocallyFinite C)
    (hcov : (⋃ n, C n) = Set.univ) (N : ℕ → ℕ) (Df : ∀ n, Fin (N n) → Set X)
    (hDcl : ∀ n j, IsClosed (Df n j))
    (hDdisk : ∀ n j, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (Df n j : Set X)))
    (hDcov : ∀ n, (⋃ j, Df n j) = piece C n)
    (hDdisj : ∀ n j j', j ≠ j' → interior (Df n j) ∩ interior (Df n j') = ∅) :
    ∃ (ι : Type*) (D : ι → Set X), LocallyFinite D ∧ (⋃ i, D i = Set.univ) ∧
      (∀ i, IsClosed (D i)) ∧ (∀ i, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (D i : Set X))) ∧
      (∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅) := by
  refine ⟨(ULift (Σ n, Fin (N n))), fun i => Df i.down.1 i.down.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨t, ht, hfin⟩ := hlf x
    have hfiber : ∀ n, {i : ULift (Σ m, Fin (N m)) | i.down.1 = n}.Finite := by
      intro n
      refine (Set.finite_range (fun j : Fin (N n) => (ULift.up (⟨n, j⟩ : Σ m, Fin (N m))))).subset ?_
      rintro ⟨⟨m, j⟩⟩ hm
      subst hm
      exact ⟨j, rfl⟩
    refine ⟨t, ht, ((hfin.biUnion fun n _ => hfiber n)).subset ?_⟩
    rintro ⟨⟨n, j⟩⟩ ⟨z, hz1, hz2⟩
    refine mem_iUnion₂.mpr ⟨n, ⟨z, ?_, hz2⟩, rfl⟩
    exact piece_subset C hcl n ((hDcov n).symm ▸ mem_iUnion.2 ⟨j, hz1⟩)
  · apply eq_univ_iff_forall.2
    intro y
    obtain ⟨n, hn⟩ : ∃ n, y ∈ piece C n := by
      have h1 : y ∈ ⋃ n, piece C n := by rw [iUnion_pieces C hcov]; exact mem_univ y
      simpa using h1
    obtain ⟨j, hj⟩ := mem_iUnion.1 ((hDcov n).symm ▸ hn)
    exact mem_iUnion.2 ⟨ULift.up ⟨n, j⟩, hj⟩
  · intro i; exact hDcl i.down.1 i.down.2
  · intro i; exact hDdisk i.down.1 i.down.2
  · rintro ⟨⟨n, j⟩⟩ ⟨⟨m, j'⟩⟩ hne
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, hx1, hx2⟩
    by_cases hnm : n = m
    · subst hnm
      have hjj : j ≠ j' := fun h => hne (by rw [h])
      have h0 : x ∈ interior (Df n j) ∩ interior (Df n j') := ⟨hx1, hx2⟩
      rw [hDdisj n j j' hjj] at h0
      exact h0
    · have h1 : interior (Df n j) ⊆ interior (piece C n) :=
        interior_mono fun z hz => (hDcov n).symm ▸ mem_iUnion.2 ⟨j, hz⟩
      have h2 : interior (Df m j') ⊆ interior (piece C m) :=
        interior_mono fun z hz => (hDcov m).symm ▸ mem_iUnion.2 ⟨j', hz⟩
      have hmem : (interior (piece C n) ∩ interior (piece C m)).Nonempty :=
        ⟨x, h1 hx1, h2 hx2⟩
      rw [disjoint_interior_pieces C hcl n m hnm] at hmem
      exact Set.not_nonempty_empty hmem

end Assembly

section PerPieceTiling

noncomputable def gclamp (G : ℝ → ℝ) (c d : ℝ) : ℝ → ℝ := fun x => G (min (max x c) d)
lemma continuous_gclamp {G : ℝ → ℝ} {c d : ℝ} (hc : ContinuousOn G (Icc c d)) (hcd : c ≤ d) :
    Continuous (gclamp G c d) := by
  refine hc.comp_continuous ?_ ?_
  · fun_prop
  · intro x
    exact ⟨le_min (le_max_right x c) hcd, min_le_right _ _⟩
lemma gclamp_of_mem {G : ℝ → ℝ} {c d x : ℝ} (hx0 : c ≤ x) (hx1 : x ≤ d) :
    gclamp G c d x = G x := by
  have h1 : max x c = x := max_eq_left hx0
  have h2 : min x d = x := min_eq_left hx1
  simp [gclamp, h1, h2]
lemma exists_graph_of_component_v2 {X Y : ℝ → ℝ} {c d p q : ℝ} (hcd : c < d) (hXc : Continuous X)
    (hYc : Continuous Y)
    (han : ∀ t : ℝ, t ∈ Ioo p q → X t ∈ Icc c d → AnalyticAt ℝ X t)
    (hseamp : X p ∉ Ioo c d)
    (hseamq : X q ∉ Ioo c d)
    (hnoc : ∀ t : ℝ, deriv X t = 0 → X t ∈ Ioo c d → False)
    {t : ℝ} (ht : t ∈ Ioo p q ∩ X ⁻¹' Ioo c d) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc c d) ∧
      (∀ s ∈ connectedComponentIn (Ioo p q ∩ X ⁻¹' Ioo c d) t, Y s = g (X s)) ∧
      (∀ x ∈ Ioo c d, ∃ s ∈ connectedComponentIn (Ioo p q ∩ X ⁻¹' Ioo c d) t, X s = x) ∧
      (∀ s ∈ connectedComponentIn (Ioo p q ∩ X ⁻¹' Ioo c d) t,
        ∀ s' ∈ connectedComponentIn (Ioo p q ∩ X ⁻¹' Ioo c d) t, X s = X s' → s = s') := by
  set U : Set ℝ := Ioo p q ∩ X ⁻¹' Ioo c d with hUdef
  have hUopen : IsOpen U := isOpen_Ioo.inter (isOpen_Ioo.preimage hXc)
  set C := connectedComponentIn U t with hCdef
  have htC : t ∈ C := mem_connectedComponentIn ht
  have hCne : C.Nonempty := ⟨t, htC⟩
  have hCnU : C ⊆ U := connectedComponentIn_subset U t
  have hCU : ∀ s ∈ C, X s ∈ Ioo c d := fun s hs => (hCnU hs).2
  have hbdd : BddBelow C := ⟨p, fun y hy => (hCnU hy).1.1.le⟩
  have hba : BddAbove C := ⟨q, fun y hy => (hCnU hy).1.2.le⟩
  have hCeq : C = Ioo (sInf C) (sSup C) := connectedComponentIn_eq_Ioo hUopen ht hbdd hba
  set α := sInf C with hαdef
  set β := sSup C with hβdef
  have hCeq' : C = Ioo α β := hCeq
  have hαle : α ≤ t := by rw [hαdef]; exact csInf_le hbdd htC
  have htleβ : t ≤ β := by rw [hβdef]; exact le_csSup hba htC
  have hαβ : α < β := by
    rcases lt_or_eq_of_le (hαle.trans htleβ) with h | h
    · exact h
    · exfalso
      have h2 : t ∈ Ioo α β := by rw [hCeq'] at htC; exact htC
      rw [h] at h2
      exact absurd h2 (by simp)
  have hαcl : α ∈ closure C := by
    rw [hCeq', closure_Ioo (ne_of_lt hαβ)]
    exact left_mem_Icc.mpr hαβ.le
  have hβcl : β ∈ closure C := by
    rw [hCeq', closure_Ioo (ne_of_lt hαβ)]
    exact right_mem_Icc.mpr hαβ.le
  have hαge : p ≤ α := le_csInf hCne (fun y hy => (hCnU hy).1.1.le)
  have hβle : β ≤ q := csSup_le hCne (fun y hy => (hCnU hy).1.2.le)
  have hαnotU : α ∉ U := hαdef ▸ sInf_connectedComponentIn_notMem hUopen ht hbdd
  have hβnotU : β ∉ U := hβdef ▸ sSup_connectedComponentIn_notMem hUopen ht hba
  -- the values of `X` at the endpoints
  have hbd_of_cl : ∀ p : ℝ, p ∈ closure C → X p ∈ Icc c d := by
    intro p hp
    have himg : X '' C ⊆ Ioo c d := fun z ⟨s, hs, hzs⟩ => hzs ▸ hCU s hs
    have h1 : X p ∈ closure (X '' C) := by
      rw [mem_closure_iff_nhds]
      intro V hV
      have hpre : X ⁻¹' V ∈ 𝓝 p := (hXc.continuousAt).preimage_mem_nhds hV
      obtain ⟨s, hsV, hsC⟩ := mem_closure_iff_nhds.mp hp (X ⁻¹' V) hpre
      exact ⟨X s, hsV, ⟨s, hsC, rfl⟩⟩
    rw [← closure_Ioo (ne_of_lt hcd)]
    exact closure_mono himg h1
  have hXαbd : X α ∈ Icc c d := hbd_of_cl α hαcl
  have hXβbd : X β ∈ Icc c d := hbd_of_cl β hβcl
  have hXαout : X α ∉ Ioo c d := by
    intro hmem
    rcases eq_or_lt_of_le hαge with h0 | hpos
    · rw [← h0] at hmem
      exact hseamp hmem
    · exact hαnotU ⟨⟨hpos, lt_of_lt_of_le hαβ hβle⟩, hmem⟩
  have hXβout : X β ∉ Ioo c d := by
    intro hmem
    rcases eq_or_lt_of_le hβle with h2 | hlt
    · rw [h2] at hmem
      exact hseamq hmem
    · exact hβnotU ⟨⟨hαge.trans_lt hαβ, hlt⟩, hmem⟩
  have hXα : X α = c ∨ X α = d := by
    rcases eq_or_lt_of_le hXαbd.1 with h | h
    · exact Or.inl h.symm
    · refine Or.inr (le_antisymm hXαbd.2 ?_)
      by_contra hd
      exact hXαout ⟨h, lt_of_not_ge hd⟩
  have hXβ : X β = c ∨ X β = d := by
    rcases eq_or_lt_of_le hXβbd.1 with h | h
    · exact Or.inl h.symm
    · refine Or.inr (le_antisymm hXβbd.2 ?_)
      by_contra hd
      exact hXβout ⟨h, lt_of_not_ge hd⟩
  -- monotonicity on `[α, β]`
  have hsign : (∀ s ∈ Ioo α β, 0 < deriv X s) ∨ (∀ s ∈ Ioo α β, deriv X s < 0) := by
    refine sign_const_of_ne_zero ?_ ?_
    · intro s hs
      have hsC : s ∈ C := by rw [hCeq']; exact hs
      have hsI : s ∈ Ioo p q := ⟨lt_of_le_of_lt hαge hs.1, lt_of_lt_of_le hs.2 hβle⟩
      exact (((han s hsI ⟨(hCU s hsC).1.le, (hCU s hsC).2.le⟩).deriv).continuousAt).continuousWithinAt
    · intro s hs
      exact fun h0 => hnoc s h0 (hCU s (by rw [hCeq']; exact hs))
  have hmono : StrictMonoOn X (Icc α β) ∨ StrictAntiOn X (Icc α β) := by
    rcases hsign with h | h
    · exact Or.inl (strictMonoOn_of_deriv_pos (convex_Icc α β) hXc.continuousOn
        (by rw [interior_Icc]; exact h))
    · exact Or.inr (strictAntiOn_of_deriv_neg (convex_Icc α β) hXc.continuousOn
        (by rw [interior_Icc]; exact h))
  have hXαβne : X α ≠ X β := by
    rcases hmono with hm | ha
    · exact ne_of_lt (hm (left_mem_Icc.mpr hαβ.le) (right_mem_Icc.mpr hαβ.le) hαβ)
    · exact ne_of_gt (ha (left_mem_Icc.mpr hαβ.le) (right_mem_Icc.mpr hαβ.le) hαβ)
  have hinjC : ∀ s ∈ C, ∀ s' ∈ C, X s = X s' → s = s' := by
    intro s hs s' hs' hss'
    rcases hmono with hm | ha
    · exact hm.injOn (by rw [hCeq'] at hs; exact ⟨hs.1.le, hs.2.le⟩)
        (by rw [hCeq'] at hs'; exact ⟨hs'.1.le, hs'.2.le⟩) hss'
    · exact ha.injOn (by rw [hCeq'] at hs; exact ⟨hs.1.le, hs.2.le⟩)
        (by rw [hCeq'] at hs'; exact ⟨hs'.1.le, hs'.2.le⟩) hss'
  have hcases : (X α = c ∧ X β = d) ∨ (X α = d ∧ X β = c) := by
    rcases hXα with h | h <;> rcases hXβ with h' | h'
    · exact absurd (h.trans h'.symm) hXαβne
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩
    · exact absurd (h.trans h'.symm) hXαβne
  rcases hmono with hm | ha
  · -- increasing branch
    have hcd' : X α = c ∧ X β = d := by
      rcases hcases with h | h
      · exact h
      · exfalso
        have := hm (left_mem_Icc.mpr hαβ.le) (right_mem_Icc.mpr hαβ.le) hαβ
        rw [h.1, h.2] at this
        exact absurd this (not_lt.mpr hcd.le)
    obtain ⟨hXαc, hXβd⟩ := hcd'
    obtain ⟨g0, hg0cont, hg0inv1, hg0inv2⟩ :=
      exists_continuousOn_inv_of_strictMonoOn hαβ hXc.continuousOn hm
    refine ⟨fun x => Y (g0 x), ?_, ?_, ?_, hinjC⟩
    · have hsets : Icc (X α) (X β) = Icc c d := by rw [hXαc, hXβd]
      rw [← hsets]
      exact hYc.comp_continuousOn hg0cont
    · intro s hs
      have hsI : s ∈ Icc α β := by
        rw [hCeq'] at hs
        exact ⟨hs.1.le, hs.2.le⟩
      change Y s = Y (g0 (X s))
      rw [hg0inv1 s hsI]
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc hαβ.le hXc.continuousOn
        (by rw [hXαc, hXβd]; exact ⟨hx.1.le, hx.2.le⟩)
      refine ⟨s, ?_, hxs⟩
      rw [hCeq']
      refine ⟨lt_of_le_of_ne hs.1 (fun h => ?_), lt_of_le_of_ne hs.2 (fun h => ?_)⟩
      · rw [← h] at hxs
        rw [hXαc] at hxs
        exact absurd hxs (ne_of_lt hx.1)
      · rw [h] at hxs
        rw [hXβd] at hxs
        exact absurd hxs (Ne.symm (ne_of_lt hx.2))
  · -- decreasing branch
    have hdc' : X α = d ∧ X β = c := by
      rcases hcases with h | h
      · exfalso
        have := ha (left_mem_Icc.mpr hαβ.le) (right_mem_Icc.mpr hαβ.le) hαβ
        rw [h.1, h.2] at this
        exact absurd this (not_lt.mpr hcd.le)
      · exact h
    obtain ⟨hXαd, hXβc⟩ := hdc'
    have hm' : StrictMonoOn (fun s => -X s) (Icc α β) := ha.neg
    have hcont' : ContinuousOn (fun s => -(X s)) (Icc α β) := hXc.continuousOn.neg
    obtain ⟨g0, hg0cont, hg0inv1, hg0inv2⟩ :=
      exists_continuousOn_inv_of_strictMonoOn hαβ hcont' hm'
    refine ⟨fun x => Y (g0 (-x)), ?_, ?_, ?_, hinjC⟩
    · have hsets : Icc ((fun s => -(X s)) α) ((fun s => -(X s)) β) = Icc (-d) (-c) := by
        simp only [Pi.neg_apply, hXαd, hXβc]
      have hg0' : ContinuousOn g0 (Icc (-d) (-c)) := hsets ▸ hg0cont
      refine hYc.comp_continuousOn ?_
      exact hg0'.comp continuous_neg.continuousOn (fun x hx => by
        simp only [mem_Icc] at hx ⊢
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    · intro s hs
      have hsI : s ∈ Icc α β := by
        rw [hCeq'] at hs
        exact ⟨hs.1.le, hs.2.le⟩
      change Y s = Y (g0 (-(X s)))
      have h1 : g0 ((fun s => -(X s)) s) = s := hg0inv1 s hsI
      simp only [Pi.neg_apply] at h1
      rw [h1]
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := intermediate_value_Icc hαβ.le hcont'
        (show (-x) ∈ Icc ((fun s => -(X s)) α) ((fun s => -(X s)) β) from by
          simp only [Pi.neg_apply, hXαd, hXβc, mem_Icc]
          exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      refine ⟨s, ?_, ?_⟩
      · rw [hCeq']
        refine ⟨lt_of_le_of_ne hs.1 (fun h => ?_), lt_of_le_of_ne hs.2 (fun h => ?_)⟩
        · rw [← h] at hxs
          simp only [Pi.neg_apply, hXαd] at hxs
          linarith [hx.2]
        · rw [h] at hxs
          simp only [Pi.neg_apply, hXβc] at hxs
          linarith [hx.1]
      · simp only [Pi.neg_apply] at hxs
        exact neg_inj.mp hxs
/-- **The trace of a closed analytic Jordan curve in an elementary vertical strip is a finite,
strictly ordered union of graphs.** -/theorem exists_graphs_in_strip_v2 {γ : ℝ → ℂ} {p q c d : ℝ} (hcd : c < d) (hγc : Continuous γ)
    (hinj : Set.InjOn γ (Set.Ico p q))
    (han : ∀ t : ℝ, t ∈ Set.Ioo p q → (γ t).re ∈ Set.Icc c d →
      AnalyticAt ℝ (fun s : ℝ => (γ s).re) t)
    (hseamp : (γ p).re ∉ Set.Ioo c d) (hseamq : (γ q).re ∉ Set.Ioo c d)
    (hnoc : ∀ t : ℝ, deriv (fun s : ℝ => (γ s).re) t = 0 → (γ t).re ∈ Set.Ioo c d → False)
    (hfib : ∀ v ∈ Set.Ioo c d,
      {t : ℝ | t ∈ Set.Icc p q ∧ (γ t).re = v}.Finite) :
    ∃ (n : ℕ) (g : Fin n → ℝ → ℝ), (∀ l, Continuous (g l)) ∧
      (∀ x ∈ Set.Ioo c d, StrictMono (fun l : Fin n => g l x)) ∧
      (∀ l, ∀ x ∈ Set.Ioo c d, ∃ t ∈ Set.Icc p q, (γ t).re = x ∧ (γ t).im = g l x) ∧
      (∀ t ∈ Set.Icc p q, (γ t).re ∈ Set.Ioo c d → ∃ l, (γ t).im = g l (γ t).re) := by
  set X : ℝ → ℝ := fun t => (γ t).re with hXdef
  set Y : ℝ → ℝ := fun t => (γ t).im with hYdef
  have hXc : Continuous X := Complex.continuous_re.comp hγc
  have hYc : Continuous Y := Complex.continuous_im.comp hγc
  set x₀ : ℝ := (c + d) / 2 with hxdef
  have hxcd : x₀ ∈ Set.Ioo c d := by
    refine ⟨?_, ?_⟩ <;> · simp only [hxdef]; linarith
  set U : Set ℝ := Set.Ioo p q ∩ X ⁻¹' Set.Ioo c d with hUdef
  have hTfin : ({t : ℝ | t ∈ Set.Icc p q ∧ X t = x₀}).Finite :=
    hfib x₀ hxcd
  set T : Finset ℝ := hTfin.toFinset with hTdef
  have hTmem : ∀ t : ℝ, t ∈ T ↔ t ∈ Set.Icc p q ∧ X t = x₀ := fun t =>
    hTfin.mem_toFinset
  have hTU : ∀ t ∈ T, t ∈ U := by
    intro t ht
    obtain ⟨h1, h2⟩ := (hTmem t).mp ht
    refine ⟨⟨lt_of_le_of_ne h1.1 ?_, lt_of_le_of_ne h1.2 ?_⟩, ?_⟩
    · intro h0
      rw [← h0] at h2
      exact hseamp (show X p ∈ Set.Ioo c d from h2 ▸ hxcd)
    · intro hq
      rw [hq] at h2
      exact hseamq (show X q ∈ Set.Ioo c d from h2 ▸ hxcd)
    · show X t ∈ Set.Ioo c d
      rw [h2]; exact hxcd
  -- the graph attached to every `t ∈ T`
  have hgraph : ∀ t ∈ T, ∃ G : ℝ → ℝ, Continuous G ∧
      (∀ s ∈ connectedComponentIn U t, Y s = G (X s)) ∧
      (∀ x ∈ Set.Ioo c d, ∃ s ∈ connectedComponentIn U t, X s = x ∧ Y s = G x) ∧
      (∀ s ∈ connectedComponentIn U t, ∀ s' ∈ connectedComponentIn U t, X s = X s' → s = s') ∧
      G x₀ = Y t := by
    intro t ht
    obtain ⟨G0, hG01, hG02, hG03, hG04⟩ :=
      exists_graph_of_component_v2 hcd hXc hYc (fun s hsI hs => han s hsI hs) hseamp hseamq hnoc
        (hTU t ht)
    refine ⟨gclamp G0 c d, continuous_gclamp hG01 hcd.le, ?_, ?_, ?_, ?_⟩
    · intro s hs
      have hXmem : X s ∈ Set.Icc c d := ⟨(connectedComponentIn_subset U t hs).2.1.le,
        (connectedComponentIn_subset U t hs).2.2.le⟩
      rw [hG02 s hs, gclamp_of_mem hXmem.1 hXmem.2]
    · intro x hx
      obtain ⟨s, hsC, hXs⟩ := hG03 x hx
      have hXmem : X s ∈ Set.Icc c d := by rw [hXs]; exact ⟨hx.1.le, hx.2.le⟩
      refine ⟨s, hsC, hXs, ?_⟩
      rw [← hXs, gclamp_of_mem hXmem.1 hXmem.2]
      exact hG02 s hsC
    · exact hG04
    · have h1 : X t = x₀ := ((hTmem t).mp ht).2
      rw [hG02 t (mem_connectedComponentIn (hTU t ht)), h1]
      exact gclamp_of_mem hxcd.1.le hxcd.2.le
  have hgraph' : ∀ t : ℝ, ∃ G : ℝ → ℝ, t ∈ T → Continuous G ∧
      (∀ s ∈ connectedComponentIn U t, Y s = G (X s)) ∧
      (∀ x ∈ Set.Ioo c d, ∃ s ∈ connectedComponentIn U t, X s = x ∧ Y s = G x) ∧
      (∀ s ∈ connectedComponentIn U t, ∀ s' ∈ connectedComponentIn U t, X s = X s' → s = s') ∧
      G x₀ = Y t := by
    intro t
    by_cases ht : t ∈ T
    · obtain ⟨G, h⟩ := hgraph t ht
      exact ⟨G, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h ht⟩
  choose G hG using hgraph'
  -- the components of two points of `T` coincide iff the points are equal
  have hcomp_eq : ∀ s t : ℝ, s ∈ T → t ∈ T →
      (connectedComponentIn U s = connectedComponentIn U t ↔ s = t) := by
    intro s t hs ht
    constructor
    · intro h
      have hsC : s ∈ connectedComponentIn U t := by rw [← h]; exact mem_connectedComponentIn (hTU s hs)
      exact (hG t ht).2.2.2.1 s hsC t (mem_connectedComponentIn (hTU t ht))
        (by rw [((hTmem s).mp hs).2, ((hTmem t).mp ht).2])
    · intro h; rw [h]
  -- sorting
  let V : Finset ℝ := T.image Y
  let e : Fin V.card ≃o ↥V := Finset.orderIsoOfFin V rfl
  have hpick : ∀ i : Fin V.card, ∃ t ∈ T, Y t = (e i : ℝ) := by
    intro i
    obtain ⟨t, ht, hYt⟩ := Finset.mem_image.mp (show (e i : ℝ) ∈ T.image Y from (e i).2)
    exact ⟨t, ht, hYt⟩
  choose tt htt hYtt using hpick
  -- two points of `T` with the same `Y`-value are equal
  have hYinj : ∀ s ∈ T, ∀ t ∈ T, Y s = Y t → s = t := by
    intro s hs t ht hY
    have hγ : γ s = γ t := by
      apply Complex.ext
      · show X s = X t
        rw [((hTmem s).mp hs).2, ((hTmem t).mp ht).2]
      · show Y s = Y t
        exact hY
    exact hinj ⟨(hTU s hs).1.1.le, (hTU s hs).1.2⟩ ⟨(hTU t ht).1.1.le, (hTU t ht).1.2⟩ hγ
  refine ⟨V.card, fun i => G (tt i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hG (tt i) (htt i)).1
  · intro x hx i j hij
    change G (tt i) x < G (tt j) x
    have hlt : (e i : ℝ) < (e j : ℝ) := e.strictMono hij
    have hi0 : G (tt i) x₀ = (e i : ℝ) := by
      rw [(hG (tt i) (htt i)).2.2.2.2]; exact hYtt i
    have hj0 : G (tt j) x₀ = (e j : ℝ) := by
      rw [(hG (tt j) (htt j)).2.2.2.2]; exact hYtt j
    have hne : ∀ y ∈ Set.Ioo c d, G (tt i) y - G (tt j) y ≠ 0 := by
      intro y hy hzero
      obtain ⟨s, hsC, hXs, hYs⟩ := (hG (tt i) (htt i)).2.2.1 y hy
      obtain ⟨s', hsC', hXs', hYs'⟩ := (hG (tt j) (htt j)).2.2.1 y hy
      have hγ : γ s = γ s' := by
        apply Complex.ext
        · show X s = X s'
          exact hXs.trans hXs'.symm
        · show Y s = Y s'
          rw [hYs, hYs', sub_eq_zero.mp hzero]
      have hsI : s ∈ Set.Ico p q := by
        have h := connectedComponentIn_subset U (tt i) hsC
        exact ⟨h.1.1.le, h.1.2⟩
      have hsI' : s' ∈ Set.Ico p q := by
        have h := connectedComponentIn_subset U (tt j) hsC'
        exact ⟨h.1.1.le, h.1.2⟩
      have hss : s = s' := hinj hsI hsI' hγ
      -- the two components then coincide
      have hunion : IsPreconnected (connectedComponentIn U (tt i) ∪ connectedComponentIn U (tt j)) :=
        IsPreconnected.union' ⟨s, hsC, hss ▸ hsC'⟩
          (isPreconnected_connectedComponentIn) (isPreconnected_connectedComponentIn)
      have hsub : connectedComponentIn U (tt i) ∪ connectedComponentIn U (tt j) ⊆
          connectedComponentIn U (tt i) :=
        IsPreconnected.subset_connectedComponentIn hunion
          (Or.inl (mem_connectedComponentIn (hTU (tt i) (htt i))))
          (union_subset (connectedComponentIn_subset U (tt i))
            (connectedComponentIn_subset U (tt j)))
      have heqcomp : connectedComponentIn U (tt i) = connectedComponentIn U (tt j) := by
        have h1 : connectedComponentIn U (tt j) ⊆ connectedComponentIn U (tt i) :=
          fun z hz => hsub (Or.inr hz)
        have hunion' : IsPreconnected (connectedComponentIn U (tt j) ∪ connectedComponentIn U (tt i)) :=
          IsPreconnected.union' ⟨s', hsC', hss.symm ▸ hsC⟩
            (isPreconnected_connectedComponentIn) (isPreconnected_connectedComponentIn)
        have hsub' : connectedComponentIn U (tt j) ∪ connectedComponentIn U (tt i) ⊆
            connectedComponentIn U (tt j) :=
          IsPreconnected.subset_connectedComponentIn hunion'
            (Or.inl (mem_connectedComponentIn (hTU (tt j) (htt j))))
            (union_subset (connectedComponentIn_subset U (tt j))
              (connectedComponentIn_subset U (tt i)))
        have h2 : connectedComponentIn U (tt i) ⊆ connectedComponentIn U (tt j) :=
          fun z hz => hsub' (Or.inr hz)
        exact Subset.antisymm h2 h1
      have heqt : tt i = tt j := (hcomp_eq (tt i) (tt j) (htt i) (htt j)).mp heqcomp
      have : (e i : ℝ) = (e j : ℝ) := by rw [← hYtt i, ← hYtt j, heqt]
      exact absurd this (ne_of_lt hlt)
    have hcont : ContinuousOn (fun y => G (tt i) y - G (tt j) y) (Set.Ioo c d) :=
      ((hG (tt i) (htt i)).1.continuousOn.mono Ioo_subset_Icc_self).sub
        (((hG (tt j) (htt j)).1.continuousOn.mono Ioo_subset_Icc_self))
    rcases sign_const_of_ne_zero hcont hne with hpos | hneg
    · have h1 : 0 < G (tt i) x₀ - G (tt j) x₀ := hpos x₀ hxcd
      rw [hi0, hj0] at h1
      linarith [h1, hlt]
    · exact sub_neg.mp (hneg x hx)
  · intro i x hx
    obtain ⟨s, hsC, hXs, hYs⟩ := (hG (tt i) (htt i)).2.2.1 x hx
    exact ⟨s, ⟨(connectedComponentIn_subset U (tt i) hsC).1.1.le,
      (connectedComponentIn_subset U (tt i) hsC).1.2.le⟩, hXs, hYs⟩
  · intro t ht hxt
    -- `t` lies in `U`
    have htU : t ∈ U := by
      have htI : t ∈ Set.Ioo p q := by
        refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
        · intro h0
          rw [← h0] at hxt
          exact hseamp hxt
        · intro hq
          rw [hq] at hxt
          exact hseamq hxt
      exact ⟨htI, hxt⟩
    -- a point of `T` in the same component
    obtain ⟨G', hG'1, hG'2, hG'3, hG'4⟩ :=
      exists_graph_of_component_v2 hcd hXc hYc (fun s hsI hs => han s hsI hs) hseamp hseamq hnoc htU
    obtain ⟨s, hsC, hXs⟩ := hG'3 x₀ hxcd
    have hsT : s ∈ T := (hTmem s).mpr ⟨⟨(connectedComponentIn_subset U t hsC).1.1.le,
      (connectedComponentIn_subset U t hsC).1.2.le⟩, hXs⟩
    have hcompst : connectedComponentIn U s = connectedComponentIn U t := by
      have hunion : IsPreconnected (connectedComponentIn U s ∪ connectedComponentIn U t) :=
        IsPreconnected.union' ⟨s, mem_connectedComponentIn (hTU s hsT), hsC⟩
          (isPreconnected_connectedComponentIn) (isPreconnected_connectedComponentIn)
      have hsub : connectedComponentIn U s ∪ connectedComponentIn U t ⊆ connectedComponentIn U s :=
        IsPreconnected.subset_connectedComponentIn hunion
          (Or.inl (mem_connectedComponentIn (hTU s hsT)))
          (union_subset (connectedComponentIn_subset U s) (connectedComponentIn_subset U t))
      have h1 : connectedComponentIn U t ⊆ connectedComponentIn U s := fun z hz => hsub (Or.inr hz)
      have hunion' : IsPreconnected (connectedComponentIn U t ∪ connectedComponentIn U s) :=
        IsPreconnected.union' ⟨s, hsC, mem_connectedComponentIn (hTU s hsT)⟩
          (isPreconnected_connectedComponentIn) (isPreconnected_connectedComponentIn)
      have hsub' : connectedComponentIn U t ∪ connectedComponentIn U s ⊆ connectedComponentIn U t :=
        IsPreconnected.subset_connectedComponentIn hunion' (Or.inl (mem_connectedComponentIn htU))
          (union_subset (connectedComponentIn_subset U t) (connectedComponentIn_subset U s))
      have h2 : connectedComponentIn U s ⊆ connectedComponentIn U t := fun z hz => hsub' (Or.inr hz)
      exact Subset.antisymm h2 h1
    -- find the index of `s`
    have hVs : Y s ∈ V := Finset.mem_image.mpr ⟨s, hsT, rfl⟩
    obtain ⟨i, hi⟩ := (e.surjective ⟨Y s, hVs⟩)
    have hYi : Y (tt i) = Y s := by rw [hYtt i, hi]
    have htti : tt i = s := hYinj (tt i) (htt i) s hsT hYi
    refine ⟨i, ?_⟩
    have hcomp' : t ∈ connectedComponentIn U s := by
      rw [hcompst]; exact mem_connectedComponentIn htU
    have h1 : Y t = G s (X t) := (hG s hsT).2.1 t hcomp'
    have hGs : G s = G (tt i) := by rw [htti]
    change Y t = G (tt i) (X t)
    rw [h1, hGs]
/-- The closure of the open region between two continuous graphs. -/
theorem closure_interior_between_graphs {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    {c d : ℝ} (hcd : c < d) (hlt : ∀ x ∈ Ioo c d, g x < h x) :
    closure {z : ℂ | c < z.re ∧ z.re < d ∧ g z.re < z.im ∧ z.im < h z.re}
      = {z : ℂ | c ≤ z.re ∧ z.re ≤ d ∧ g z.re ≤ z.im ∧ z.im ≤ h z.re} := by
  set K : Set ℂ := {z : ℂ | c ≤ z.re ∧ z.re ≤ d ∧ g z.re ≤ z.im ∧ z.im ≤ h z.re} with hK
  have hgc : Continuous fun z : ℂ => g z.re := hg.comp Complex.continuous_re
  have hhc : Continuous fun z : ℂ => h z.re := hh.comp Complex.continuous_re
  have hKcl : IsClosed K := by
    have h1 : K = {z : ℂ | c ≤ z.re} ∩ {z : ℂ | z.re ≤ d} ∩ {z : ℂ | g z.re ≤ z.im}
        ∩ {z : ℂ | z.im ≤ h z.re} := by
      ext z
      simp only [hK, Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨h1, h2, h3, h4⟩
    rw [h1]
    exact (((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_le hgc Complex.continuous_im)).inter
      (isClosed_le Complex.continuous_im hhc)
  refine Subset.antisymm (closure_minimal ?_ hKcl) ?_
  · rintro z ⟨h1, h2, h3, h4⟩
    exact ⟨h1.le, h2.le, h3.le, h4.le⟩
  · intro z hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    -- continuity data
    obtain ⟨ηg, hηg, hηg'⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε/8) (by linarith)
    obtain ⟨ηh, hηh, hηh'⟩ := Metric.continuousAt_iff.mp hh.continuousAt (ε/8) (by linarith)
    set η : ℝ := min ηg ηh with hηdef
    have hηpos : 0 < η := lt_min hηg hηh
    have hηg'' : ∀ y : ℝ, |y - z.re| < η → |g y - g z.re| < ε/8 := by
      intro y hy
      have h2 : dist y z.re < ηg := by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hy (min_le_left _ _)
      have h3 := hηg' h2
      rwa [Real.dist_eq] at h3
    have hηh'' : ∀ y : ℝ, |y - z.re| < η → |h y - h z.re| < ε/8 := by
      intro y hy
      have h2 : dist y z.re < ηh := by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hy (min_le_right _ _)
      have h3 := hηh' h2
      rwa [Real.dist_eq] at h3
    -- choose the x-coordinate
    have hdc : 0 < d - c := by linarith
    set τ : ℝ := min (1/2) (min η (ε/4) / (2 * (d - c))) with hτdef
    have hτpos : 0 < τ := lt_min (by norm_num) (div_pos (lt_min hηpos (by linarith)) (by linarith))
    have hτle : τ ≤ 1/2 := min_le_left _ _
    have hτb : τ * (2 * (d - c)) ≤ min η (ε/4) := by
      have h1 : τ ≤ min η (ε/4) / (2 * (d - c)) := min_le_right _ _
      calc τ * (2 * (d - c)) ≤ (min η (ε/4) / (2 * (d - c))) * (2 * (d - c)) := by
            exact mul_le_mul_of_nonneg_right h1 (by linarith)
        _ = min η (ε/4) := by field_simp
    set m : ℝ := (c + d)/2 with hmdef
    set x' : ℝ := (1 - τ) * z.re + τ * m with hx'def
    have hx'c : c < x' := by
      have h1 : x' - c = (1 - τ) * (z.re - c) + τ * (m - c) := by rw [hx'def]; ring
      have h2 : 0 ≤ (1 - τ) * (z.re - c) := by
        refine mul_nonneg (by linarith) (by linarith)
      have h3 : 0 < τ * (m - c) := mul_pos hτpos (by rw [hmdef]; linarith)
      linarith
    have hx'd : x' < d := by
      have h1 : d - x' = (1 - τ) * (d - z.re) + τ * (d - m) := by rw [hx'def]; ring
      have h3 : 0 < τ * (d - m) := mul_pos hτpos (by rw [hmdef]; linarith)
      have h2 : 0 ≤ (1 - τ) * (d - z.re) := mul_nonneg (by linarith) (by linarith)
      linarith
    have hx'dist : |x' - z.re| < min η (ε/4) := by
      have h1 : x' - z.re = τ * (m - z.re) := by rw [hx'def]; ring
      have h2 : |m - z.re| ≤ d - c := by
        rw [abs_sub_le_iff]
        constructor <;> rw [hmdef] <;> linarith
      rw [h1, abs_mul, abs_of_pos hτpos]
      have h3 : τ * |m - z.re| ≤ τ * (d - c) := mul_le_mul_of_nonneg_left h2 hτpos.le
      have hminpos : 0 < min η (ε/4) := lt_min hηpos (by linarith)
      have h4 : τ * (d - c) < min η (ε/4) := by
        have h5 : τ * (2 * (d - c)) ≤ min η (ε/4) := hτb
        have h6 : τ * (d - c) = τ * (2 * (d - c)) / 2 := by ring
        rw [h6]
        linarith
      linarith
    have hx'η : |x' - z.re| < η := lt_of_lt_of_le hx'dist (min_le_left _ _)
    have hx'eps : |x' - z.re| < ε/4 := lt_of_lt_of_le hx'dist (min_le_right _ _)
    have hzimg : |g x' - g z.re| < ε/8 := hηg'' x' hx'η
    have hzimh : |h x' - h z.re| < ε/8 := hηh'' x' hx'η
    have hgx' : g x' < g z.re + ε/8 := by
      have := abs_lt.mp hzimg; linarith [this.2]
    have hhx' : h z.re - ε/8 < h x' := by
      have := abs_lt.mp hzimh; linarith [this.1]
    have hAB : g x' < h x' := hlt x' ⟨hx'c, hx'd⟩
    -- pick the y-coordinate
    have hycase : z.im ≤ g x' ∨ h x' ≤ z.im ∨ (g x' < z.im ∧ z.im < h x') := by
      rcases lt_or_ge (g x') z.im with h1 | h1
      · rcases lt_or_ge z.im (h x') with h2 | h2
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
        · exact Or.inr (Or.inl h2)
      · exact Or.inl h1
    set incr : ℝ := min ((h x' - g x')/2) (ε/8) with hincrdef
    have hincrpos : 0 < incr := lt_min (by linarith) (by linarith)
    have hincrle : incr < h x' - g x' := by
      have h1 : incr ≤ (h x' - g x')/2 := min_le_left _ _
      linarith
    obtain ⟨y', hy'⟩ : ∃ y' : ℝ, g x' < y' ∧ y' < h x' ∧ |y' - z.im| < ε/4 := by
      rcases hycase with hc1 | hc2 | hc3
      · refine ⟨g x' + incr, by linarith, by linarith, ?_⟩
        have h1 : g x' - z.im ≤ ε/8 := by linarith [hgx']
        have h2 : |g x' + incr - z.im| = g x' + incr - z.im := by
          rw [abs_of_nonneg]; linarith
        rw [h2]
        have h3 : incr ≤ ε/8 := min_le_right _ _
        linarith
      · refine ⟨h x' - incr, by linarith, by linarith, ?_⟩
        have h1 : z.im - h x' ≤ ε/8 := by linarith [hhx']
        have h2 : |h x' - incr - z.im| = -(h x' - incr - z.im) := by
          rw [abs_of_nonpos]; linarith
        rw [h2]
        have h3 : incr ≤ ε/8 := min_le_right _ _
        linarith
      · refine ⟨z.im, hc3.1, hc3.2, by rw [sub_self, abs_zero]; linarith⟩
    -- assemble the point
    refine ⟨(⟨x', y'⟩ : ℂ), ?_, ?_⟩
    · exact ⟨hx'c, hx'd, hy'.1, hy'.2.1⟩
    · rw [Complex.dist_eq]
      have h1 : z - (⟨x', y'⟩ : ℂ) = (⟨z.re - x', z.im - y'⟩ : ℂ) := by
        apply Complex.ext <;> simp
      rw [h1]
      have h2 : ‖(⟨z.re - x', z.im - y'⟩ : ℂ)‖ ≤ |z.re - x'| + |z.im - y'| :=
        Complex.norm_le_abs_re_add_abs_im _
      have h3 : |z.re - x'| + |z.im - y'| < ε := by
        rw [abs_sub_comm z.re x', abs_sub_comm z.im y']
        linarith [hx'eps, hy'.2.2]
      linarith
/-- The open region between two strictly ordered continuous graphs is preconnected. -/
theorem isPreconnected_between_graphs {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    {c d : ℝ} (hcd : c < d) (hlt : ∀ x ∈ Ioo c d, g x < h x) :
    IsPreconnected {z : ℂ | c < z.re ∧ z.re < d ∧ g z.re < z.im ∧ z.im < h z.re} := by
  set V : Set ℂ := {w : ℂ | c < w.re ∧ w.re < d ∧ 0 < w.im ∧ w.im < 1} with hV
  have hVc : Convex ℝ V := by
    have h1 : V = Complex.reCLM ⁻¹' Ioo c d ∩ Complex.imCLM ⁻¹' Ioo (0:ℝ) 1 := by
      ext w
      simp only [hV, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨h1, h2⟩, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨h1, h2, h3, h4⟩
    rw [h1]
    exact ((convex_Ioo c d).linear_preimage
      (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)).inter
      ((convex_Ioo (0:ℝ) 1).linear_preimage
      (Complex.imCLM : ℂ →ₗ[ℝ] ℝ))
  have hVp : IsPreconnected V := hVc.isPreconnected
  set Ψ : ℂ → ℂ := fun w => (⟨w.re, g w.re + w.im * (h w.re - g w.re)⟩ : ℂ) with hΨ
  have hΨc : Continuous Ψ := by
    rw [hΨ]
    exact continuous_re_im_mk Complex.continuous_re
      ((hg.comp Complex.continuous_re).add (Complex.continuous_im.mul
        ((hh.comp Complex.continuous_re).sub (hg.comp Complex.continuous_re))))
  have himg : Ψ '' V = {z : ℂ | c < z.re ∧ z.re < d ∧ g z.re < z.im ∧ z.im < h z.re} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 : c < w.re := hw.1
      have hw2 : w.re < d := hw.2.1
      have hw3 : 0 < w.im := hw.2.2.1
      have hw4 : w.im < 1 := hw.2.2.2
      have hpos : 0 < h w.re - g w.re := sub_pos.mpr (hlt w.re ⟨hw1, hw2⟩)
      simp only [hΨ, Set.mem_setOf_eq]
      refine ⟨hw1, hw2, ?_, ?_⟩
      · show g w.re < g w.re + w.im * (h w.re - g w.re)
        nlinarith
      · show g w.re + w.im * (h w.re - g w.re) < h w.re
        nlinarith
    · intro hz
      have hz1 : c < z.re := hz.1
      have hz2 : z.re < d := hz.2.1
      have hz3 : g z.re < z.im := hz.2.2.1
      have hz4 : z.im < h z.re := hz.2.2.2
      have hpos : 0 < h z.re - g z.re := sub_pos.mpr (hlt z.re ⟨hz1, hz2⟩)
      refine ⟨(⟨z.re, (z.im - g z.re) / (h z.re - g z.re)⟩ : ℂ), ?_, ?_⟩
      · refine ⟨hz1, hz2, ?_, ?_⟩
        · show (0:ℝ) < (z.im - g z.re) / (h z.re - g z.re)
          exact div_pos (by linarith) hpos
        · show (z.im - g z.re) / (h z.re - g z.re) < 1
          rw [div_lt_one hpos]
          linarith
      · simp only [hΨ]
        apply Complex.ext
        · simp
        · show g z.re + ((z.im - g z.re) / (h z.re - g z.re)) * (h z.re - g z.re) = z.im
          field_simp
          ring
  rw [← himg]
  exact hVp.image Ψ hΨc.continuousOn
theorem exists_merged_graph_list {K : ℕ} (N : Fin K → ℕ) (g : ∀ k, Fin (N k) → ℝ → ℝ) {c d : ℝ}
    (hcd : c < d)
    (hcont : ∀ k i, Continuous (g k i))
    (hmono : ∀ k, ∀ x ∈ Set.Ioo c d, StrictMono (fun i : Fin (N k) => g k i x))
    (hcomp : ∀ k l (i : Fin (N k)) (j : Fin (N l)),
       (∀ x ∈ Set.Ioo c d, g k i x = g l j x) ∨ (∀ x ∈ Set.Ioo c d, g k i x < g l j x) ∨
       (∀ x ∈ Set.Ioo c d, g l j x < g k i x)) :
    ∃ (M : ℕ) (G : Fin M → ℝ → ℝ), (∀ j, Continuous (G j)) ∧
      (∀ x ∈ Set.Ioo c d, StrictMono (fun i : Fin M => G i x)) ∧
      (∀ k i, ∃ j, ∀ x ∈ Set.Ioo c d, G j x = g k i x) := by
  set x₀ : ℝ := (c + d)/2 with hxdef
  have hxcd : x₀ ∈ Ioo c d := by
    refine ⟨?_, ?_⟩ <;> simp only [hxdef] <;> linarith
  set V : Finset ℝ :=
    (Finset.univ : Finset (Σ k : Fin K, Fin (N k))).image (fun ki => g ki.1 ki.2 x₀) with hVdef
  have hmemV : ∀ ki : Σ k : Fin K, Fin (N k), g ki.1 ki.2 x₀ ∈ V := by
    intro ki
    exact Finset.mem_image.mpr ⟨ki, Finset.mem_univ ki, rfl⟩
  let e : Fin V.card ≃o ↥V := Finset.orderIsoOfFin V rfl
  have he_mem : ∀ i : Fin V.card, (e i : ℝ) ∈ V := fun i => (e i).2
  have hpick : ∀ i : Fin V.card, ∃ ki : Σ k : Fin K, Fin (N k), g ki.1 ki.2 x₀ = (e i : ℝ) := by
    intro i
    obtain ⟨ki, _, hki⟩ := Finset.mem_image.mp (he_mem i)
    exact ⟨ki, hki⟩
  choose rep hrep using hpick
  refine ⟨V.card, fun i => g (rep i).1 (rep i).2, ?_, ?_, ?_⟩
  · intro i; exact hcont _ _
  · intro x hx i j hij
    have hlt : (e i : ℝ) < (e j : ℝ) := e.strictMono hij
    have hi0 : g (rep i).1 (rep i).2 x₀ = (e i : ℝ) := hrep i
    have hj0 : g (rep j).1 (rep j).2 x₀ = (e j : ℝ) := hrep j
    have hne : ∀ y ∈ Ioo c d, g (rep i).1 (rep i).2 y - g (rep j).1 (rep j).2 y ≠ 0 := by
      intro y hy hzero
      rcases hcomp (rep i).1 (rep j).1 (rep i).2 (rep j).2 with h | h | h
      · linarith [h x₀ hxcd, hi0, hj0]
      · linarith [h y hy]
      · linarith [h y hy]
    have hcont' : ContinuousOn
        (fun y => g (rep i).1 (rep i).2 y - g (rep j).1 (rep j).2 y) (Ioo c d) :=
      ((hcont _ _).continuousOn).sub ((hcont _ _).continuousOn)
    rcases sign_const_of_ne_zero hcont' hne with hpos | hneg
    · have h1 : 0 < g (rep i).1 (rep i).2 x₀ - g (rep j).1 (rep j).2 x₀ := hpos x₀ hxcd
      rw [hi0, hj0] at h1
      linarith
    · exact sub_neg.mp (hneg x hx)
  · intro k i
    have h1 : g k i x₀ ∈ V := hmemV ⟨k, i⟩
    obtain ⟨j, hj⟩ := e.surjective ⟨g k i x₀, h1⟩
    refine ⟨j, ?_⟩
    have hrepj : g (rep j).1 (rep j).2 x₀ = g k i x₀ := by
      rw [hrep j]
      exact congrArg Subtype.val hj
    rcases hcomp (rep j).1 k (rep j).2 i with h | h | h
    · exact fun x hx => h x hx
    · exfalso; linarith [h x₀ hxcd, hrepj]
    · exfalso; linarith [h x₀ hxcd, hrepj]
/-- Between adjacent elements of a finite set: consecutive-pair selection. -/
lemma exists_consecutive_pair {s : Finset ℝ} {lo hi : ℝ} (hlo : lo ∈ s) (hhi : hi ∈ s)
    (hlohi : lo < hi) {x : ℝ} (hx : x ∈ Icc lo hi) :
    ∃ u v : ℝ, u ∈ s ∧ v ∈ s ∧ u < v ∧ x ∈ Icc u v ∧ lo ≤ u ∧ v ≤ hi ∧
      (∀ z ∈ s, z ∉ Ioo u v) := by
  have hne : (s.filter (fun z => z ≤ x)).Nonempty := ⟨lo, Finset.mem_filter.mpr ⟨hlo, hx.1⟩⟩
  set u := (s.filter (fun z => z ≤ x)).max' hne with hudef
  have hu_mem : u ∈ s := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1
  have hu_le : u ≤ x := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  have hub : ∀ z ∈ s, z ≤ x → z ≤ u := fun z hz hzx =>
    Finset.le_max' _ z (Finset.mem_filter.mpr ⟨hz, hzx⟩)
  have hlou : lo ≤ u := hub lo hlo hx.1
  by_cases hcase : u = x ∧ u = hi
  · obtain ⟨hux, huh⟩ := hcase
    have hne2 : (s.filter (fun z => z < u)).Nonempty :=
      ⟨lo, Finset.mem_filter.mpr ⟨hlo, by rw [huh]; exact hlohi⟩⟩
    set w := (s.filter (fun z => z < u)).max' hne2 with hwdef
    have hw_mem : w ∈ s := (Finset.mem_filter.mp (Finset.max'_mem _ hne2)).1
    have hwu : w < u := (Finset.mem_filter.mp (Finset.max'_mem _ hne2)).2
    have hwb : ∀ z ∈ s, z < u → z ≤ w := fun z hz hzu =>
      Finset.le_max' _ z (Finset.mem_filter.mpr ⟨hz, hzu⟩)
    refine ⟨w, u, hw_mem, hu_mem, hwu, ⟨hwu.le.trans hux.le, hux.ge⟩, ?_, ?_, ?_⟩
    · exact hwb lo hlo (by rw [huh]; exact hlohi)
    · exact huh.le
    · intro z hz hzI
      have h1 : z ≤ w := hwb z hz hzI.2
      exact absurd hzI.1 (not_lt.mpr h1)
  · have hult : u < hi := by
      rcases lt_or_eq_of_le (le_trans hu_le hx.2) with h | h
      · exact h
      · exact absurd ⟨le_antisymm hu_le (by rw [h]; exact hx.2), h⟩ hcase
    have hne3 : (s.filter (fun z => u < z)).Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨hhi, hult⟩⟩
    set v := (s.filter (fun z => u < z)).min' hne3 with hvdef
    have hv_mem : v ∈ s := (Finset.mem_filter.mp (Finset.min'_mem _ hne3)).1
    have huv : u < v := (Finset.mem_filter.mp (Finset.min'_mem _ hne3)).2
    have hvb : ∀ z ∈ s, u < z → v ≤ z := fun z hz hzlt =>
      Finset.min'_le _ z (Finset.mem_filter.mpr ⟨hz, hzlt⟩)
    have hxv : x ≤ v := by
      by_contra hcon
      push_neg at hcon
      have h1 : v ≤ u := hub v hv_mem hcon.le
      exact absurd huv (not_lt.mpr h1)
    have hvhi : v ≤ hi := hvb hi hhi hult
    exact ⟨u, v, hu_mem, hv_mem, huv, ⟨hu_le, hxv⟩, hlou, hvhi, fun z hz hzI =>
      absurd (hvb z hz hzI.1) (not_le.mpr hzI.2)⟩
/-- A finite family of continuous functions on a compact interval is bounded. -/
lemma exists_bound_of_finite_continuous {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    (hg : ∀ i, Continuous (g i)) {c d : ℝ} :
    ∃ L : ℝ, 0 < L ∧ ∀ i x, x ∈ Icc c d → |g i x| < L := by
  have hb : ∀ i : ι, ∃ C : ℝ, ∀ x ∈ Icc c d, |g i x| ≤ C := by
    intro i
    obtain ⟨Bu, hBu⟩ := (isCompact_Icc (a := c) (b := d) |>.image (hg i)).bddAbove
    obtain ⟨Bl, hBl⟩ := (isCompact_Icc (a := c) (b := d) |>.image (hg i)).bddBelow
    refine ⟨max |Bu| |Bl| + 1, fun x hx => ?_⟩
    have h1 : g i x ≤ Bu := hBu ⟨x, hx, rfl⟩
    have h2 : Bl ≤ g i x := hBl ⟨x, hx, rfl⟩
    have h3 : |g i x| ≤ max |Bu| |Bl| := by
      rw [abs_le]
      constructor
      · linarith [h2, neg_abs_le Bl, le_max_right |Bu| |Bl|]
      · linarith [h1, le_abs_self Bu, le_max_left |Bu| |Bl|]
    linarith [h3]
  choose C hC using hb
  have h0 : ∀ j ∈ (Finset.univ : Finset ι), (0:ℝ) ≤ max (C j) 0 + 1 := by
    intro j _
    have := le_max_right (C j) 0
    linarith
  have hsum : ∀ i : ι, max (C i) 0 + 1 ≤ ∑ j, (max (C j) 0 + 1) := fun i =>
    Finset.single_le_sum h0 (Finset.mem_univ i)
  refine ⟨(∑ j, (max (C j) 0 + 1)) + 1, by
    have := Finset.sum_nonneg h0
    linarith, ?_⟩
  intro i x hx
  have h1 : C i ≤ max (C i) 0 + 1 := by linarith [le_max_left (C i) 0]
  have h2 := hsum i
  have h3 := hC i x hx
  linarith
lemma le_of_forall_mem_Ioo_v2 {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h) {c d : ℝ}
    (hcd : c < d) (hineq : ∀ x ∈ Ioo c d, f x ≤ h x) : ∀ x ∈ Icc c d, f x ≤ h x := by
  have hclosed : IsClosed {x : ℝ | f x ≤ h x} := isClosed_le hf hh
  have hsub : Icc c d ⊆ {x : ℝ | f x ≤ h x} := by
    rw [← closure_Ioo (ne_of_lt hcd)]
    exact closure_minimal hineq hclosed
  exact fun x hx => hsub hx

set_option maxHeartbeats 2000000 in
theorem exists_disk_tiling_of_region {K : ℕ} (γ : Fin K → ℝ → ℂ) (a b : Fin K → ℝ)
    (hab : ∀ k, a k < b k)
    (hγc : ∀ k, Continuous (γ k))
    (hinj : ∀ k, Set.InjOn (γ k) (Set.Ico (a k) (b k)))
    (han : ∀ k t, t ∈ Set.Ioo (a k) (b k) → AnalyticAt ℝ (fun s => (γ k s).re) t)
    (hcut : Finset ℝ) (hcm : -(1/2) ∈ hcut) (hcp : (1/2) ∈ hcut)
    (hseam : ∀ k, ((γ k (a k)).re ∈ hcut ∨ (γ k (a k)).re ∉ Set.Icc (-(1/2)) (1/2)) ∧
      ((γ k (b k)).re ∈ hcut ∨ (γ k (b k)).re ∉ Set.Icc (-(1/2)) (1/2)))
    (hcrit : ∀ k t, deriv (fun s => (γ k s).re) t = 0 → (γ k t).re ∈ hcut)
    (hconst : ∀ k v, (∀ t ∈ Set.Icc (a k) (b k), (γ k t).re = v) → v ∈ hcut)
    (hcross : ∀ k l t s, t ∈ Set.Icc (a k) (b k) → s ∈ Set.Icc (a l) (b l) →
      γ k t = γ l s → ¬(k = l ∧ t = s) → (γ k t).re ∈ hcut)
    (hfib : ∀ k v, v ∈ Set.Ioo (-(1/2)) (1/2) →
      (∀ t ∈ Set.Icc (a k) (b k), (γ k t).re = v) ∨
        {t | t ∈ Set.Icc (a k) (b k) ∧ (γ k t).re = v}.Finite)
    {Q : Set ℂ} (hQcl : IsClosed Q) (hQci : closure (interior Q) = Q)
    (hQb : Q ⊆ Metric.closedBall 0 (1/2))
    (hQf : frontier Q ⊆ ⋃ k, γ k '' Set.Icc (a k) (b k)) :
    ∃ (N : ℕ) (D : Fin N → Set ℂ), (⋃ j, D j = Q) ∧ (∀ j, IsClosed (D j)) ∧
      (∀ j, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (D j : Set ℂ))) ∧
      (∀ j j', j ≠ j' → interior (D j) ∩ interior (D j') = ∅) := by
  classical
  -- the finite family of inner consecutive strips
  let S : Finset (ℝ × ℝ) := (hcut ×ˢ hcut).filter (fun p =>
      p.1 < p.2 ∧ (∀ z ∈ hcut, z ∉ Set.Ioo p.1 p.2) ∧ -(1/2) ≤ p.1 ∧ p.2 ≤ 1/2)
  have hSmem : ∀ p : ℝ × ℝ, p ∈ S ↔ p.1 ∈ hcut ∧ p.2 ∈ hcut ∧ p.1 < p.2 ∧
      (∀ z ∈ hcut, z ∉ Set.Ioo p.1 p.2) ∧ -(1/2) ≤ p.1 ∧ p.2 ≤ 1/2 := by
    intro p
    simp only [S, Finset.mem_filter, Finset.mem_product]
    tauto
  -- the strip decomposition of every curve
  have hstripK : ∀ p : ↥S, ∀ k : Fin K, ∃ (m : ℕ) (g : Fin m → ℝ → ℝ),
      (∀ i, Continuous (g i)) ∧
      (∀ x ∈ Set.Ioo p.1.1 p.1.2, StrictMono (fun i => g i x)) ∧
      (∀ i x, x ∈ Set.Ioo p.1.1 p.1.2 → ∃ t ∈ Set.Icc (a k) (b k),
        (γ k t).re = x ∧ (γ k t).im = g i x) ∧
      (∀ t ∈ Set.Icc (a k) (b k), (γ k t).re ∈ Set.Ioo p.1.1 p.1.2 →
        ∃ i, (γ k t).im = g i (γ k t).re) := by
    intro p k
    obtain ⟨hm1, hm2, hlt, hconsec, hin1, hin2⟩ := (hSmem p.1).mp p.2
    have hsub : Set.Ioo p.1.1 p.1.2 ⊆ Set.Ioo (-(1/2)) (1/2) :=
      fun y hy => ⟨lt_of_le_of_lt hin1 hy.1, lt_of_lt_of_le hy.2 hin2⟩
    exact exists_graphs_in_strip_v2 (γ := γ k) (p := a k) (q := b k)
      (c := p.1.1) (d := p.1.2) hlt (hγc k) (hinj k)
      (fun t ht1 ht2 => han k t ht1)
      (fun hmem => by
        rcases (hseam k).1 with h | h
        · exact (hconsec (γ k (a k)).re h hmem).elim
        · exact h ⟨(hsub hmem).1.le, (hsub hmem).2.le⟩)
      (fun hmem => by
        rcases (hseam k).2 with h | h
        · exact (hconsec (γ k (b k)).re h hmem).elim
        · exact h ⟨(hsub hmem).1.le, (hsub hmem).2.le⟩)
      (fun t hderiv hmem => hconsec (γ k t).re (hcrit k t hderiv) hmem)
      (fun v hv => by
        rcases hfib k v (hsub hv) with h | h
        · exact (hconsec v (hconst k v h) hv).elim
        · exact h)
  choose MB gB hB1 hB2 hB3 hB4 using hstripK
  -- merging the graphs of all curves inside a strip
  have hmergeK : ∀ p : ↥S, ∃ (M : ℕ) (G : Fin M → ℝ → ℝ),
      (∀ i, Continuous (G i)) ∧
      (∀ x ∈ Set.Ioo p.1.1 p.1.2, StrictMono (fun i : Fin M => G i x)) ∧
      (∀ k i, ∃ j, ∀ x ∈ Set.Ioo p.1.1 p.1.2, G j x = gB p k i x) := by
    intro p
    obtain ⟨hm1, hm2, hlt, hconsec, hin1, hin2⟩ := (hSmem p.1).mp p.2
    have hcomp : ∀ k l (i : Fin (MB p k)) (j : Fin (MB p l)),
        (∀ x ∈ Set.Ioo p.1.1 p.1.2, gB p k i x = gB p l j x) ∨
        (∀ x ∈ Set.Ioo p.1.1 p.1.2, gB p k i x < gB p l j x) ∨
        (∀ x ∈ Set.Ioo p.1.1 p.1.2, gB p l j x < gB p k i x) := by
      intro k l i j
      by_cases heq : ∀ x ∈ Set.Ioo p.1.1 p.1.2, gB p k i x = gB p l j x
      · exact Or.inl heq
      · have hno : ∀ x ∈ Set.Ioo p.1.1 p.1.2, gB p k i x ≠ gB p l j x := by
          intro x hx hxy
          obtain ⟨t, ht, htx, hty⟩ := hB3 p k i x hx
          obtain ⟨s, hs, hsx, hsy⟩ := hB3 p l j x hx
          have hγ : γ k t = γ l s := by
            apply Complex.ext
            · show (γ k t).re = (γ l s).re
              rw [htx, hsx]
            · show (γ k t).im = (γ l s).im
              rw [hty, hsy, hxy]
          by_cases hcase : k = l ∧ t = s
          · obtain ⟨hkl, hts⟩ := hcase
            subst hkl
            have hij : i = j := (hB2 p k x hx).injective hxy
            subst hij
            exact heq fun y _ => rfl
          · exact hconsec (γ k t).re (hcross k l t s ht hs hγ hcase) (by rw [htx]; exact hx)
        rcases sign_const_of_ne_zero
            (((hB1 p k i).continuousOn).sub ((hB1 p l j).continuousOn))
            (fun x hx => sub_ne_zero.mpr (hno x hx)) with hpos | hneg
        · exact Or.inr (Or.inr fun x hx => by
            have h := hpos x hx; simp only [Pi.sub_apply] at h; linarith)
        · exact Or.inr (Or.inl fun x hx => by
            have h := hneg x hx; simp only [Pi.sub_apply] at h; linarith)
    obtain ⟨M, G, hG1, hG2, hG3⟩ :=
      exists_merged_graph_list (fun k => MB p k) (fun k => gB p k) hlt
        (fun k i => hB1 p k i) (fun k x hx => hB2 p k x hx) hcomp
    exact ⟨M, G, hG1, hG2, hG3⟩
  choose MM GG hGG1 hGG2 hGG3 using hmergeK
  -- a bound making room for the two horizontal end graphs
  choose Lb0 hLb01 hLb02 using fun p : ↥S =>
    exists_bound_of_finite_continuous (GG p) (fun i => hGG1 p i)
      (c := (p : ℝ × ℝ).1) (d := (p : ℝ × ℝ).2)
  let Lb : ↥S → ℝ := fun p => max (Lb0 p) 1
  have hLb1 : ∀ p : ↥S, 0 < Lb p := fun p => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hLbge1 : ∀ p : ↥S, 1 ≤ Lb p := fun p => le_max_right _ _
  have hLb2 : ∀ (p : ↥S) (i : Fin (MM p)) (x : ℝ), x ∈ Set.Icc p.1.1 p.1.2 →
      |GG p i x| < Lb p := fun p i x hx => lt_of_lt_of_le (hLb02 p i x hx) (le_max_left _ _)
  -- the extended list of graphs: -L, G_0, ..., G_{M-1}, L
  let Gx : (p : ↥S) → Fin (MM p + 2) → ℝ → ℝ := fun p i =>
    if h0 : (i : ℕ) = 0 then (fun _ : ℝ => -Lb p)
    else if h1 : (i : ℕ) = MM p + 1 then (fun _ : ℝ => Lb p)
    else GG p ⟨(i : ℕ) - 1, by omega⟩
  have hGx_zero : ∀ p : ↥S, Gx p 0 = (fun _ : ℝ => -Lb p) := by
    intro p
    dsimp only [Gx]
    split
    · rfl
    · exact absurd rfl ‹¬((0 : Fin (MM p + 2)) : ℕ) = 0›
  have hGx_last : ∀ p : ↥S, Gx p (Fin.last (MM p + 1)) = (fun _ : ℝ => Lb p) := by
    intro p
    have h1 : ((Fin.last (MM p + 1) : Fin (MM p + 2)) : ℕ) = MM p + 1 := rfl
    have h0 : ((Fin.last (MM p + 1) : Fin (MM p + 2)) : ℕ) ≠ 0 := by
      rw [h1]; omega
    dsimp only [Gx]
    rw [dif_neg h0, dif_pos h1]
  have hGx_succ : ∀ p : ↥S, ∀ q : Fin (MM p + 1),
      Gx p (Fin.succ q) = (if h : (q : ℕ) = MM p then (fun _ : ℝ => Lb p)
        else GG p ⟨(q : ℕ), by omega⟩) := by
    intro p q
    have hv : ((Fin.succ q : Fin (MM p + 2)) : ℕ) = (q : ℕ) + 1 := rfl
    dsimp only [Gx]
    rw [dif_neg (by rw [hv]; omega)]
    by_cases hq : (q : ℕ) = MM p
    · have h1 : ((Fin.succ q : Fin (MM p + 2)) : ℕ) = MM p + 1 := by rw [hv]; omega
      rw [dif_pos h1, dif_pos hq]
    · have h1 : ¬((Fin.succ q : Fin (MM p + 2)) : ℕ) = MM p + 1 := by rw [hv]; omega
      rw [dif_neg h1, dif_neg hq]
      congr 1
  have hGx_castSucc : ∀ p : ↥S, ∀ q : Fin (MM p + 1),
      Gx p (Fin.castSucc q) = (if h : (q : ℕ) = 0 then (fun _ : ℝ => -Lb p)
        else GG p ⟨(q : ℕ) - 1, by omega⟩) := by
    intro p q
    have hv : ((Fin.castSucc q : Fin (MM p + 2)) : ℕ) = (q : ℕ) := rfl
    dsimp only [Gx]
    by_cases hq : (q : ℕ) = 0
    · have h0 : ((Fin.castSucc q : Fin (MM p + 2)) : ℕ) = 0 := by rw [hv]; omega
      rw [dif_pos h0, dif_pos hq]
    · have h0 : ¬((Fin.castSucc q : Fin (MM p + 2)) : ℕ) = 0 := by rw [hv]; omega
      have h1 : ¬((Fin.castSucc q : Fin (MM p + 2)) : ℕ) = MM p + 1 := by rw [hv]; omega
      rw [dif_neg h0, dif_neg h1, dif_neg hq]
      congr 1

  -- the value description of the extended list
  have hGx_val : ∀ p : ↥S, ∀ y : ℝ, ∀ i : Fin (MM p + 2),
      Gx p i y = (if h0 : (i : ℕ) = 0 then -Lb p
        else if h1 : (i : ℕ) = MM p + 1 then Lb p
        else GG p ⟨(i : ℕ) - 1, by omega⟩ y) := by
    intro p y i
    dsimp only [Gx]
    by_cases h0 : (i : ℕ) = 0
    · rw [dif_pos h0, dif_pos h0]
    · by_cases h1 : (i : ℕ) = MM p + 1
      · rw [dif_neg h0, dif_pos h1, dif_neg h0, dif_pos h1]
      · rw [dif_neg h0, dif_neg h1, dif_neg h0, dif_neg h1]
  have hGx_cont : ∀ p : ↥S, ∀ i : Fin (MM p + 2), Continuous (Gx p i) := by
    intro p i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hGx_castSucc]
      by_cases h : (j : ℕ) = 0
      · rw [dif_pos h]; exact continuous_const
      · rw [dif_neg h]; exact hGG1 p _
    · rw [hGx_last]; exact continuous_const
  -- the values increase with the index
  have hGx_lt : ∀ p : ↥S, ∀ y ∈ Set.Ioo p.1.1 p.1.2, ∀ i j : Fin (MM p + 2),
      i < j → Gx p i y < Gx p j y := by
    intro p y hy i j hij
    have hyIcc : y ∈ Set.Icc p.1.1 p.1.2 := ⟨hy.1.le, hy.2.le⟩
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have hiLt : (i : ℕ) < MM p + 2 := i.isLt
    have hjLt : (j : ℕ) < MM p + 2 := j.isLt
    rw [hGx_val p y i, hGx_val p y j]
    by_cases hi0 : (i : ℕ) = 0
    · rw [dif_pos hi0]
      by_cases hj0 : (j : ℕ) = 0
      · omega
      rw [dif_neg hj0]
      by_cases hjL : (j : ℕ) = MM p + 1
      · rw [dif_pos hjL]; linarith [hLb1 p]
      · rw [dif_neg hjL]
        have h2 : |GG p ⟨(j : ℕ) - 1, by omega⟩ y| < Lb p := hLb2 p _ y hyIcc
        exact neg_lt_of_abs_lt h2
    · rw [dif_neg hi0]
      by_cases hiL : (i : ℕ) = MM p + 1
      · omega
      rw [dif_neg hiL]
      by_cases hj0 : (j : ℕ) = 0
      · omega
      rw [dif_neg hj0]
      by_cases hjL : (j : ℕ) = MM p + 1
      · rw [dif_pos hjL]
        have h2 : |GG p ⟨(i : ℕ) - 1, by omega⟩ y| < Lb p := hLb2 p _ y hyIcc
        exact lt_of_abs_lt h2
      · rw [dif_neg hjL]
        have hlt : (⟨(i : ℕ) - 1, by omega⟩ : Fin (MM p)) < ⟨(j : ℕ) - 1, by omega⟩ := by
          rw [Fin.lt_def]
          show (i : ℕ) - 1 < (j : ℕ) - 1
          omega
        exact hGG2 p y hy hlt
  -- the endpoint values
  have hGx_le_L : ∀ p : ↥S, ∀ y ∈ Set.Icc p.1.1 p.1.2, ∀ i : Fin (MM p + 2), Gx p i y ≤ Lb p := by
    intro p y hy i
    rw [hGx_val p y i]
    by_cases h0 : (i : ℕ) = 0
    · rw [dif_pos h0]
      have := hLb1 p
      linarith
    · rw [dif_neg h0]
      by_cases h1 : (i : ℕ) = MM p + 1
      · rw [dif_pos h1]
      · rw [dif_neg h1]
        have h2 : |GG p ⟨(i : ℕ) - 1, by omega⟩ y| < Lb p := hLb2 p _ y hy
        exact (lt_of_abs_lt h2).le
  have hGx_ge_negL : ∀ p : ↥S, ∀ y ∈ Set.Icc p.1.1 p.1.2, ∀ i : Fin (MM p + 2), -Lb p ≤ Gx p i y := by
    intro p y hy i
    rw [hGx_val p y i]
    by_cases h0 : (i : ℕ) = 0
    · rw [dif_pos h0]
    · rw [dif_neg h0]
      by_cases h1 : (i : ℕ) = MM p + 1
      · rw [dif_pos h1]
        have := hLb1 p
        linarith
      · rw [dif_neg h1]
        have h2 : |GG p ⟨(i : ℕ) - 1, by omega⟩ y| < Lb p := hLb2 p _ y hy
        have h3 := neg_lt_of_abs_lt h2
        linarith

  -- ============ B. the tiles ============
  let mid : ↥S → ℝ := fun p => (p.1.1 + p.1.2) / 2
  have hmid_mem : ∀ p : ↥S, mid p ∈ Set.Ioo p.1.1 p.1.2 := by
    intro p
    obtain ⟨hm1, hm2, hlt, hconsec, hin1, hin2⟩ := (hSmem p.1).mp p.2
    exact ⟨by simp only [mid]; linarith, by simp only [mid]; linarith⟩
  let lower : (p : ↥S) → Fin (MM p + 1) → ℝ → ℝ := fun p q => Gx p (Fin.castSucc q)
  let upper : (p : ↥S) → Fin (MM p + 1) → ℝ → ℝ := fun p q => Gx p (Fin.succ q)
  let tile : (Σ p : ↥S, Σ q : Fin (MM p + 1), Bool) → Set ℂ := fun x =>
    if x.2.2 then graphRegion (lower x.1 x.2.1) (upper x.1 x.2.1) (mid x.1) x.1.1.2
    else graphRegion (lower x.1 x.2.1) (upper x.1 x.2.1) x.1.1.1 (mid x.1)
  have hcast : ∀ p : ↥S, ∀ q : Fin (MM p + 1),
      (Fin.castSucc q : Fin (MM p + 2)) < Fin.succ q := fun p q =>
    Fin.castSucc_lt_succ_iff.mpr le_rfl
  have htile_false : ∀ (p : ↥S) (q : Fin (MM p + 1)),
      tile ⟨p, q, false⟩ = graphRegion (lower p q) (upper p q) p.1.1 (mid p) := by
    intro p q; simp [tile]
  have htile_true : ∀ (p : ↥S) (q : Fin (MM p + 1)),
      tile ⟨p, q, true⟩ = graphRegion (lower p q) (upper p q) (mid p) p.1.2 := by
    intro p q; simp [tile]
  -- tiles are closed
  have htile_closed : ∀ x : (Σ p : ↥S, Σ q : Fin (MM p + 1), Bool), IsClosed (tile x) := by
    rintro ⟨p, q, b⟩
    cases b
    · rw [htile_false p q]
      exact isClosed_graphRegion (hGx_cont p _) (hGx_cont p _) _ _
    · rw [htile_true p q]
      exact isClosed_graphRegion (hGx_cont p _) (hGx_cont p _) _ _
  -- tiles are closed disks
  have htile_disk : ∀ x : (Σ p : ↥S, Σ q : Fin (MM p + 1), Bool),
      Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (tile x : Set ℂ)) := by
    rintro ⟨p, q, b⟩
    obtain ⟨hm1, hm2, hlt, hconsec, hin1, hin2⟩ := (hSmem p.1).mp p.2
    have hmid := hmid_mem p
    cases b
    · rw [htile_false p q]
      obtain ⟨e⟩ := graphRegion_homeomorph_closedBall_gen (hGx_cont p _) (hGx_cont p _) hmid.1
        (le_of_forall_mem_Ioo_v2 (hGx_cont p _) (hGx_cont p _) hmid.1
          (fun x hx => (hGx_lt p x ⟨hx.1, lt_trans hx.2 hmid.2⟩ _ _ (hcast p q)).le))
        (fun x hx => hGx_lt p x ⟨hx.1, lt_trans hx.2 hmid.2⟩ _ _ (hcast p q))
        (Or.inr (hGx_lt p (mid p) hmid _ _ (hcast p q)))
      exact ⟨e.symm⟩
    · rw [htile_true p q]
      obtain ⟨e⟩ := graphRegion_homeomorph_closedBall_gen (hGx_cont p _) (hGx_cont p _) hmid.2
        (le_of_forall_mem_Ioo_v2 (hGx_cont p _) (hGx_cont p _) hmid.2
          (fun x hx => (hGx_lt p x ⟨lt_trans hmid.1 hx.1, hx.2⟩ _ _ (hcast p q)).le))
        (fun x hx => hGx_lt p x ⟨lt_trans hmid.1 hx.1, hx.2⟩ _ _ (hcast p q))
        (Or.inl (hGx_lt p (mid p) hmid _ _ (hcast p q)))
      exact ⟨e.symm⟩

  -- ============ C. coverage and disjointness ============
  let ι : Type := {x : (Σ p : ↥S, Σ q : Fin (MM p + 1), Bool) //
    (interior (tile x) ∩ interior Q).Nonempty}
  have hGR : ∀ (g h : ℝ → ℝ) (a b : ℝ),
      graphRegion g h a b = {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ g z.re ≤ z.im ∧ z.im ≤ h z.re} := by
    intro g h a b
    ext z
    simp only [graphRegion, Set.mem_setOf_eq, Set.mem_Icc]
    tauto
  haveI hιfin : Fintype ι := by
    dsimp only [ι]; infer_instance
  -- a preconnected set avoiding the walls lies on one side of Q
  have hsep : ∀ T : Set ℂ, IsPreconnected T →
      T ∩ (⋃ k, γ k '' Set.Icc (a k) (b k)) = ∅ → (T ∩ interior Q).Nonempty →
      T ⊆ interior Q := by
    intro T hT hTW hTQ
    have hsub : T ⊆ interior Q ∪ (closure Q)ᶜ := by
      intro z hz
      by_cases hzQ : z ∈ interior Q
      · exact Or.inl hzQ
      · refine Or.inr fun hzcl => ?_
        have hzf : z ∈ frontier Q := by
          rw [frontier_eq_closure_inter_closure]
          refine ⟨hzcl, ?_⟩
          rw [_root_.mem_closure_iff]
          intro U hU hzU
          by_contra hcon
          have hsub2 : U ⊆ Q := fun w hw => by
            by_contra hwQ
            exact hcon ⟨w, hw, hwQ⟩
          exact hzQ (interior_maximal hsub2 hU hzU)
        have hzW : z ∈ ⋃ k, γ k '' Set.Icc (a k) (b k) := hQf hzf
        have : z ∈ T ∩ (⋃ k, γ k '' Set.Icc (a k) (b k)) := ⟨hz, hzW⟩
        rw [hTW] at this
        exact this
    have hdisj : Disjoint (interior Q) (closure Q)ᶜ :=
      Set.disjoint_left.mpr fun z hz1 hz2 => hz2 (subset_closure (interior_subset hz1))
    rcases IsPreconnected.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl hdisj hsub hT
      with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hTQ
      exact h hw1 (subset_closure (interior_subset hw2))
  -- the gap containing a given height
  have hgap : ∀ (p : ↥S) (x : ℝ), x ∈ Set.Ioo p.1.1 p.1.2 → ∀ y : ℝ,
      -Lb p ≤ y → y ≤ Lb p → ∃ q : Fin (MM p + 1), lower p q x ≤ y ∧ y ≤ upper p q x := by
    intro p x hx y hy1 hy2
    obtain ⟨hm1, hm2, hlt, hconsec, hin1, hin2⟩ := (hSmem p.1).mp p.2
    set V : Finset ℝ := Finset.image (fun i : Fin (MM p + 2) => Gx p i x) Finset.univ with hVdef
    have hV : ∀ i : Fin (MM p + 2), Gx p i x ∈ V := fun i =>
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hVlo : -Lb p ∈ V := by
      refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
      show Gx p 0 x = -Lb p
      rw [hGx_zero]
    have hVhi : Lb p ∈ V := by
      refine Finset.mem_image.mpr ⟨Fin.last (MM p + 1), Finset.mem_univ _, ?_⟩
      show Gx p (Fin.last (MM p + 1)) x = Lb p
      rw [hGx_last]
    obtain ⟨u, v, huV, hvV, huv, hyuv, -, -, hconsecV⟩ :=
      exists_consecutive_pair hVlo hVhi (by linarith [hLb1 p]) ⟨hy1, hy2⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp huV
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hvV
    have hij' : (i : ℕ) < (j : ℕ) := by
      by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with h | h
      · have hji : j < i := by rw [Fin.lt_def]; exact h
        have h3 := hGx_lt p x hx j i hji
        rw [hi, hj] at h3
        linarith
      · have h3 : Gx p i x = Gx p j x := by rw [Fin.ext h]
        rw [hi, hj] at h3
        linarith
    have hiS : (i : ℕ) + 1 < MM p + 2 := by have := i.isLt; omega
    have hiM : (i : ℕ) < MM p + 1 := by have := i.isLt; omega
    have hnext : (⟨(i : ℕ) + 1, hiS⟩ : Fin (MM p + 2)) ≤ j := by
      rw [Fin.le_def]
      show (i : ℕ) + 1 ≤ (j : ℕ)
      exact Nat.succ_le_of_lt hij'
    have hsucc : j = (⟨(i : ℕ) + 1, hiS⟩ : Fin (MM p + 2)) := by
      by_contra hne
      have hne' : (j : ℕ) ≠ (i : ℕ) + 1 := fun hc => hne (Fin.ext hc)
      have h1 : (i : ℕ) + 1 ≤ (j : ℕ) := Nat.succ_le_of_lt hij'
      have h2 : (⟨(i : ℕ) + 1, hiS⟩ : Fin (MM p + 2)) < j := by
        rw [Fin.lt_def]
        have h2' : (↑(⟨(i : ℕ) + 1, hiS⟩ : Fin (MM p + 2)) : ℕ) = (i : ℕ) + 1 := rfl
        rw [h2']
        omega
      have hii : i < (⟨(i : ℕ) + 1, hiS⟩ : Fin (MM p + 2)) := by
        rw [Fin.lt_def]
        show (i : ℕ) < (i : ℕ) + 1
        omega
      have h4 : Gx p i x < Gx p (⟨(i : ℕ) + 1, hiS⟩ : Fin (MM p + 2)) x :=
        hGx_lt p x hx i _ hii
      have h5 : Gx p (⟨(i : ℕ) + 1, hiS⟩ : Fin (MM p + 2)) x < Gx p j x :=
        hGx_lt p x hx _ j h2
      rw [hi] at h4
      rw [hj] at h5
      exact hconsecV _ (hV _) ⟨h4, h5⟩
    have hcast : (Fin.castSucc (⟨(i:ℕ), hiM⟩ : Fin (MM p + 1)) : Fin (MM p + 2)) = i :=
      Fin.ext rfl
    have hcast2 : (Fin.succ (⟨(i:ℕ), hiM⟩ : Fin (MM p + 1)) : Fin (MM p + 2)) = j := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk]
      rw [hsucc]
    refine ⟨⟨(i : ℕ), hiM⟩, ?_, ?_⟩
    · show Gx p (Fin.castSucc ⟨(i:ℕ), hiM⟩) x ≤ y
      rw [hcast, hi]
      exact hyuv.1
    · show y ≤ Gx p (Fin.succ ⟨(i:ℕ), hiM⟩) x
      rw [hcast2, hj]
      exact hyuv.2

  -- ordering facts for the two halves
  have hle_false : ∀ (p : ↥S) (q : Fin (MM p + 1)),
      ∀ x ∈ Set.Icc p.1.1 (mid p), lower p q x ≤ upper p q x := by
    intro p q
    refine le_of_forall_mem_Ioo_v2 (hGx_cont p _) (hGx_cont p _) (hmid_mem p).1 (fun x hx => ?_)
    exact (hGx_lt p x ⟨hx.1, lt_trans hx.2 (hmid_mem p).2⟩ _ _ (hcast p q)).le
  have hlt_false : ∀ (p : ↥S) (q : Fin (MM p + 1)),
      ∀ x ∈ Set.Ioo p.1.1 (mid p), lower p q x < upper p q x := fun p q x hx =>
    hGx_lt p x ⟨hx.1, lt_trans hx.2 (hmid_mem p).2⟩ _ _ (hcast p q)
  have hle_true : ∀ (p : ↥S) (q : Fin (MM p + 1)),
      ∀ x ∈ Set.Icc (mid p) p.1.2, lower p q x ≤ upper p q x := by
    intro p q
    refine le_of_forall_mem_Ioo_v2 (hGx_cont p _) (hGx_cont p _) (hmid_mem p).2 (fun x hx => ?_)
    exact (hGx_lt p x ⟨lt_trans (hmid_mem p).1 hx.1, hx.2⟩ _ _ (hcast p q)).le
  have hlt_true : ∀ (p : ↥S) (q : Fin (MM p + 1)),
      ∀ x ∈ Set.Ioo (mid p) p.1.2, lower p q x < upper p q x := fun p q x hx =>
    hGx_lt p x ⟨lt_trans (hmid_mem p).1 hx.1, hx.2⟩ _ _ (hcast p q)
  -- a point inside a strip's open interval and in the interior of Q lies in some tile
  have hcover_open : ∀ z : ℂ, z ∈ interior Q → z.re ∈ ⋃ p : ↥S, Set.Ioo p.1.1 p.1.2 →
      z ∈ ⋃ x : ι, tile x.1 := by
    intro z hzQ hzstrip
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hzstrip
    have hzB : z ∈ Metric.closedBall (0:ℂ) (1/2) := hQb (interior_subset hzQ)
    have hnorm : ‖z‖ ≤ 1/2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hzB
    have hzim1 : -Lb p ≤ z.im := by
      have h1 : |z.im| ≤ 1/2 := le_trans (Complex.abs_im_le_norm z) hnorm
      linarith [(abs_le.mp h1).1, hLbge1 p]
    have hzim2 : z.im ≤ Lb p := by
      have h1 : |z.im| ≤ 1/2 := le_trans (Complex.abs_im_le_norm z) hnorm
      linarith [(abs_le.mp h1).2, hLbge1 p]
    obtain ⟨q, hq1, hq2⟩ := hgap p z.re hp z.im hzim1 hzim2
    by_cases hhalf : z.re ≤ mid p
    · have hzmem : z ∈ graphRegion (lower p q) (upper p q) p.1.1 (mid p) :=
        ⟨⟨hp.1.le, hhalf⟩, hq1, hq2⟩
      have hzcl : z ∈ closure (interior (tile ⟨p, q, false⟩)) := by
        rw [htile_false p q,
          interior_graphRegion (hGx_cont p _) (hGx_cont p _) (hmid_mem p).1,
          closure_interior_between_graphs (hGx_cont p _) (hGx_cont p _) (hmid_mem p).1
            (hlt_false p q)]
        exact ⟨hp.1.le, hhalf, hq1, hq2⟩
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.mp hzcl (interior Q)
        (isOpen_interior.mem_nhds hzQ)
      refine Set.mem_iUnion.mpr ⟨⟨⟨p, q, false⟩, ⟨w, hw2, hw1⟩⟩, ?_⟩
      rw [htile_false p q]
      exact ⟨⟨hp.1.le, hhalf⟩, hq1, hq2⟩
    · push_neg at hhalf
      have hzmem : z ∈ graphRegion (lower p q) (upper p q) (mid p) p.1.2 :=
        ⟨⟨hhalf.le, hp.2.le⟩, hq1, hq2⟩
      have hzcl : z ∈ closure (interior (tile ⟨p, q, true⟩)) := by
        rw [htile_true p q,
          interior_graphRegion (hGx_cont p _) (hGx_cont p _) (hmid_mem p).2,
          closure_interior_between_graphs (hGx_cont p _) (hGx_cont p _) (hmid_mem p).2
            (hlt_true p q)]
        exact ⟨hhalf.le, hp.2.le, hq1, hq2⟩
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.mp hzcl (interior Q)
        (isOpen_interior.mem_nhds hzQ)
      refine Set.mem_iUnion.mpr ⟨⟨⟨p, q, true⟩, ⟨w, hw2, hw1⟩⟩, ?_⟩
      rw [htile_true p q]
      exact ⟨⟨hhalf.le, hp.2.le⟩, hq1, hq2⟩

  have hnorm_ofReal : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := by
    intro r
    have h2 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    rw [← Real.sqrt_sq (norm_nonneg ((r : ℝ) : ℂ)), h2, Real.sqrt_sq_eq_abs]
  -- coverage: interior Q is contained in the union of the tiles
  have hcover : interior Q ⊆ closure (⋃ x : ι, tile x.1) := by
    intro z hzQ
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hzB : z ∈ Metric.closedBall (0:ℂ) (1/2) := hQb (interior_subset hzQ)
    have hnorm : ‖z‖ ≤ 1/2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hzB
    have hre : z.re ∈ Set.Icc (-(1/2)) (1/2) := by
      have h1 : |z.re| ≤ 1/2 := le_trans (Complex.abs_re_le_norm z) hnorm
      exact ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩
    obtain ⟨u, v, hu, hv, huv, hzv, hlou, hvhi, hconsec⟩ :=
      exists_consecutive_pair hcm hcp (by norm_num) hre
    let p : ↥S := ⟨(u, v), (hSmem (u, v)).mpr ⟨hu, hv, huv, hconsec, hlou, hvhi⟩⟩
    have hpu : p.1.1 = u := rfl
    have hpv : p.1.2 = v := rfl
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp isOpen_interior z hzQ
    by_cases hdir : z.re < v
    · set t : ℝ := min (min (ε/2) (δ/2)) ((v - z.re)/2) with htdef
      have htpos : 0 < t := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
      have htε : t < ε := lt_of_le_of_lt (le_trans (min_le_left _ _)
        (min_le_left _ _)) (by linarith)
      have htδ : t < δ := lt_of_le_of_lt (le_trans (min_le_left _ _)
        (min_le_right _ _)) (by linarith)
      have htright : t ≤ (v - z.re)/2 := by rw [htdef]; exact min_le_right _ _
      set z' : ℂ := z + (t : ℂ) with hz'def
      have hz're : z'.re = z.re + t := by simp [hz'def]
      have hz'in : z' ∈ interior Q := by
        apply hδ
        rw [Metric.mem_ball, Complex.dist_eq]
        have h1 : z' - z = (t : ℂ) := by rw [hz'def]; ring
        rw [h1, hnorm_ofReal, abs_of_pos htpos]
        exact htδ
      have hz'strip : z'.re ∈ Set.Ioo p.1.1 p.1.2 := by
        rw [hz're, hpu, hpv]
        exact ⟨by linarith [hzv.1, htpos], by linarith [hdir, htright]⟩
      have hz'mem : z' ∈ ⋃ x : ι, tile x.1 :=
        hcover_open z' hz'in (Set.mem_iUnion.mpr ⟨p, hz'strip⟩)
      refine ⟨z', hz'mem, ?_⟩
      rw [Complex.dist_eq]
      have h1 : z - z' = (-(t) : ℂ) := by rw [hz'def]; ring
      rw [h1, norm_neg, hnorm_ofReal, abs_of_pos htpos]
      exact htε
    · push_neg at hdir
      have hzv' : z.re = v := le_antisymm hzv.2 hdir
      set t : ℝ := min (min (ε/2) (δ/2)) ((z.re - u)/2) with htdef
      have htpos : 0 < t := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
      have htε : t < ε := lt_of_le_of_lt (le_trans (min_le_left _ _)
        (min_le_left _ _)) (by linarith)
      have htδ : t < δ := lt_of_le_of_lt (le_trans (min_le_left _ _)
        (min_le_right _ _)) (by linarith)
      have htleft : t ≤ (z.re - u)/2 := by rw [htdef]; exact min_le_right _ _
      set z' : ℂ := z - (t : ℂ) with hz'def
      have hz're : z'.re = z.re - t := by simp [hz'def]
      have hz'in : z' ∈ interior Q := by
        apply hδ
        rw [Metric.mem_ball, Complex.dist_eq]
        have h1 : z' - z = (-(t) : ℂ) := by rw [hz'def]; ring
        rw [h1, norm_neg, hnorm_ofReal, abs_of_pos htpos]
        exact htδ
      have hz'strip : z'.re ∈ Set.Ioo p.1.1 p.1.2 := by
        rw [hz're, hpu, hpv, hzv']
        exact ⟨by linarith [huv, htpos], by linarith [htpos]⟩
      have hz'mem : z' ∈ ⋃ x : ι, tile x.1 :=
        hcover_open z' hz'in (Set.mem_iUnion.mpr ⟨p, hz'strip⟩)
      refine ⟨z', hz'mem, ?_⟩
      rw [Complex.dist_eq]
      have h1 : z - z' = (t : ℂ) := by rw [hz'def]; ring
      rw [h1, hnorm_ofReal, abs_of_pos htpos]
      exact htε
  -- the interior of a tile avoids the walls
  have htile_avoid : ∀ (x : Σ p : ↥S, Σ q : Fin (MM p + 1), Bool),
      interior (tile x) ∩ (⋃ k, γ k '' Set.Icc (a k) (b k)) = ∅ := by
    rintro ⟨p, q, b⟩
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzint, hzW⟩
    obtain ⟨k, t, ht, hzt⟩ := Set.mem_iUnion.mp hzW
    obtain ⟨hm1, hm2, hlt, hconsec, hin1, hin2⟩ := (hSmem p.1).mp p.2
    have hmain : ∀ (a d : ℝ), a < d → p.1.1 ≤ a → d ≤ p.1.2 →
        z ∈ interior (graphRegion (lower p q) (upper p q) a d) → False := by
      intro a d had ha hd hzint2
      rw [interior_graphRegion (hGx_cont p _) (hGx_cont p _) had] at hzint2
      obtain ⟨hz1, hz2, hz3, hz4⟩ := hzint2
      rw [← hzt] at hz1 hz2 hz3 hz4
      have hx1 : (γ k t).re ∈ Set.Ioo p.1.1 p.1.2 :=
        ⟨lt_of_le_of_lt ha hz1, lt_of_lt_of_le hz2 hd⟩
      obtain ⟨i, hi⟩ := hB4 p k t ht hx1
      obtain ⟨j, hj⟩ := hGG3 p k i
      have hzj : (γ k t).im = GG p j (γ k t).re := by rw [hi, ← hj (γ k t).re hx1]
      rw [hzj] at hz3 hz4
      have hjS : (j : ℕ) + 1 < MM p + 2 := by have := j.isLt; omega
      have hGxj : Gx p (⟨(j : ℕ) + 1, hjS⟩ : Fin (MM p + 2)) (γ k t).re = GG p j (γ k t).re := by
        rw [hGx_val]
        rw [dif_neg (by show ¬((j : ℕ) + 1 = 0); omega)]
        rw [dif_neg (by show ¬((j : ℕ) + 1 = MM p + 1); omega)]
        congr 1
      rw [← hGxj] at hz3 hz4
      have hxy : (γ k t).re ∈ Set.Ioo p.1.1 p.1.2 := hx1
      have hii : (Fin.castSucc q : Fin (MM p + 2)) < ⟨(j : ℕ) + 1, hjS⟩ := by
        by_contra hcon
        rw [not_lt] at hcon
        have h1 : Gx p (⟨(j : ℕ) + 1, hjS⟩ : Fin (MM p + 2)) (γ k t).re
            ≤ Gx p (Fin.castSucc q) (γ k t).re := by
          rcases lt_or_eq_of_le hcon with h | h
          · exact (hGx_lt p _ hxy _ _ h).le
          · rw [h]
        linarith
      have hii2 : (⟨(j : ℕ) + 1, hjS⟩ : Fin (MM p + 2)) < Fin.succ q := by
        by_contra hcon
        rw [not_lt] at hcon
        have h1 : Gx p (Fin.succ q) (γ k t).re
            ≤ Gx p (⟨(j : ℕ) + 1, hjS⟩ : Fin (MM p + 2)) (γ k t).re := by
          rcases lt_or_eq_of_le hcon with h | h
          · exact (hGx_lt p _ hxy _ _ h).le
          · rw [h]
        linarith
      have hq1v : ((Fin.castSucc q : Fin (MM p + 2)) : ℕ) = (q : ℕ) := rfl
      have hq2v : ((Fin.succ q : Fin (MM p + 2)) : ℕ) = (q : ℕ) + 1 := rfl
      have hjsv : ((⟨(j : ℕ) + 1, hjS⟩ : Fin (MM p + 2)) : ℕ) = (j : ℕ) + 1 := rfl
      rw [Fin.lt_def] at hii hii2
      rw [hq1v, hjsv] at hii
      rw [hjsv, hq2v] at hii2
      omega
    cases b
    · rw [htile_false p q] at hzint
      exact hmain p.1.1 (mid p) (hmid_mem p).1 le_rfl (hmid_mem p).2.le hzint
    · rw [htile_true p q] at hzint
      exact hmain (mid p) p.1.2 (hmid_mem p).2 (hmid_mem p).1.le le_rfl hzint

  -- each tile is contained in Q
  have htile_sub_Q : ∀ x : ι, tile x.1 ⊆ Q := by
    intro x
    have hpre : IsPreconnected (interior (tile x.1)) := by
      rcases x with ⟨⟨p, q, b⟩, hx⟩
      cases b
      · rw [htile_false p q, interior_graphRegion (hGx_cont p _) (hGx_cont p _) (hmid_mem p).1]
        exact isPreconnected_between_graphs (hGx_cont p _) (hGx_cont p _) (hmid_mem p).1
          (hlt_false p q)
      · rw [htile_true p q, interior_graphRegion (hGx_cont p _) (hGx_cont p _) (hmid_mem p).2]
        exact isPreconnected_between_graphs (hGx_cont p _) (hGx_cont p _) (hmid_mem p).2
          (hlt_true p q)
    have hsub : interior (tile x.1) ⊆ interior Q := hsep _ hpre (htile_avoid x.1) x.2
    have hcl : tile x.1 = closure (interior (tile x.1)) := by
      rcases x with ⟨⟨p, q, b⟩, hx⟩
      cases b
      · calc tile ⟨p, q, false⟩
            = graphRegion (lower p q) (upper p q) p.1.1 (mid p) := htile_false p q
          _ = {z : ℂ | p.1.1 ≤ z.re ∧ z.re ≤ mid p ∧
                lower p q z.re ≤ z.im ∧ z.im ≤ upper p q z.re} :=
              hGR (lower p q) (upper p q) p.1.1 (mid p)
          _ = closure {z : ℂ | p.1.1 < z.re ∧ z.re < mid p ∧
                lower p q z.re < z.im ∧ z.im < upper p q z.re} :=
              (closure_interior_between_graphs (hGx_cont p _) (hGx_cont p _) (hmid_mem p).1
                (hlt_false p q)).symm
          _ = closure (interior (tile ⟨p, q, false⟩)) := by
              rw [htile_false p q,
                interior_graphRegion (hGx_cont p _) (hGx_cont p _) (hmid_mem p).1]
      · calc tile ⟨p, q, true⟩
            = graphRegion (lower p q) (upper p q) (mid p) p.1.2 := htile_true p q
          _ = {z : ℂ | mid p ≤ z.re ∧ z.re ≤ p.1.2 ∧
                lower p q z.re ≤ z.im ∧ z.im ≤ upper p q z.re} :=
              hGR (lower p q) (upper p q) (mid p) p.1.2
          _ = closure {z : ℂ | mid p < z.re ∧ z.re < p.1.2 ∧
                lower p q z.re < z.im ∧ z.im < upper p q z.re} :=
              (closure_interior_between_graphs (hGx_cont p _) (hGx_cont p _) (hmid_mem p).2
                (hlt_true p q)).symm
          _ = closure (interior (tile ⟨p, q, true⟩)) := by
              rw [htile_true p q,
                interior_graphRegion (hGx_cont p _) (hGx_cont p _) (hmid_mem p).2]
    calc tile x.1 = closure (interior (tile x.1)) := hcl
      _ ⊆ closure (interior Q) := closure_mono hsub
      _ = Q := hQci
  -- tiles have pairwise disjoint interiors
  have htile_disj : ∀ x y : ι, x ≠ y →
      interior (tile x.1) ∩ interior (tile y.1) = ∅ := by
    rintro ⟨⟨p, q, b⟩, hx⟩ ⟨⟨p', q', b'⟩, hy⟩ hne
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hz1, hz2⟩
    have hne' : (⟨p, q, b⟩ : (Σ p : ↥S, Σ q : Fin (MM p + 1), Bool)) ≠ ⟨p', q', b'⟩ := by
      intro hcon
      exact hne (Subtype.ext hcon)
    -- unpack the two interiors
    have hunp : ∀ (p : ↥S) (q : Fin (MM p + 1)) (b : Bool) (z : ℂ),
        z ∈ interior (tile ⟨p, q, b⟩) →
        (p.1.1 < z.re ∧ z.re < p.1.2 ∧ lower p q z.re < z.im ∧ z.im < upper p q z.re) ∧
        (if b then mid p < z.re else z.re < mid p) := by
      intro p q b z hz
      cases b
      · rw [htile_false p q, interior_graphRegion (hGx_cont p _) (hGx_cont p _) (hmid_mem p).1]
          at hz
        exact ⟨⟨hz.1, lt_trans hz.2.1 (hmid_mem p).2, hz.2.2.1, hz.2.2.2⟩, hz.2.1⟩
      · rw [htile_true p q, interior_graphRegion (hGx_cont p _) (hGx_cont p _) (hmid_mem p).2]
          at hz
        exact ⟨⟨lt_trans (hmid_mem p).1 hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩, hz.1⟩
    obtain ⟨⟨hzA1, hzA2, hzA3, hzA4⟩, hzAb⟩ := hunp p q b z hz1
    obtain ⟨⟨hzB1, hzB2, hzB3, hzB4⟩, hzBb⟩ := hunp p' q' b' z hz2
    -- the two strips
    by_cases hpp : p = p'
    · subst hpp
      by_cases hqb : (⟨q, b⟩ : (Σ q : Fin (MM p + 1), Bool)) = ⟨q', b'⟩
      · exact hne' (by rw [hqb])
      · -- same strip: distinguish the gap or the half
        rcases eq_or_ne q q' with hqq | hqq
        · -- same gap, different half
          subst hqq
          have hbb : b ≠ b' := by
            intro hcon
            exact hqb (by rw [hcon])
          cases b <;> cases b'
          · exact absurd rfl hbb
          · -- false vs true: z.re < mid p and mid p < z.re
            rw [if_neg (by decide : ¬(false = true))] at hzAb
            rw [if_pos rfl] at hzBb
            linarith
          · -- true vs false
            rw [if_pos rfl] at hzAb
            rw [if_neg (by decide : ¬(false = true))] at hzBb
            linarith
          · exact absurd rfl hbb
        · -- different gaps: the extended values are ordered
          have hqle : (Fin.succ q : Fin (MM p + 2)) ≤ Fin.castSucc q' ∨
              (Fin.succ q' : Fin (MM p + 2)) ≤ Fin.castSucc q := by
            rcases lt_or_ge (q : ℕ) (q' : ℕ) with h | h
            · left
              rw [Fin.le_def]
              have h1 : (↑(Fin.succ q : Fin (MM p + 2)) : ℕ) = (q : ℕ) + 1 := Fin.val_succ q
              have h2 : (↑(Fin.castSucc q' : Fin (MM p + 2)) : ℕ) = (q' : ℕ) := rfl
              rw [h1, h2]; omega
            · right
              have hne2 : (q' : ℕ) < (q : ℕ) := by
                rcases lt_or_eq_of_le h with h2 | h2
                · exact h2
                · exact (hqq (Fin.ext h2).symm).elim
              rw [Fin.le_def]
              have h1 : (↑(Fin.succ q' : Fin (MM p + 2)) : ℕ) = (q' : ℕ) + 1 := Fin.val_succ q'
              have h2 : (↑(Fin.castSucc q : Fin (MM p + 2)) : ℕ) = (q : ℕ) := rfl
              rw [h1, h2]; omega
          have hz_re : z.re ∈ Set.Ioo p.1.1 p.1.2 := ⟨hzA1, hzA2⟩
          rcases hqle with hle | hle
          · have h1 : Gx p (Fin.succ q) z.re ≤ Gx p (Fin.castSucc q') z.re := by
              rcases lt_or_eq_of_le hle with h | h
              · exact (hGx_lt p z.re hz_re _ _ h).le
              · rw [h]
            simp only [lower, upper] at *
            linarith [hzA4, h1, hzB3]
          · have h1 : Gx p (Fin.succ q') z.re ≤ Gx p (Fin.castSucc q) z.re := by
              rcases lt_or_eq_of_le hle with h | h
              · exact (hGx_lt p z.re hz_re _ _ h).le
              · rw [h]
            simp only [lower, upper] at *
            linarith [hzB4, h1, hzA3]
    · -- different strips: the open x-intervals are disjoint
      have hcon : ∀ u v u' v' : ℝ, u ∈ hcut → v ∈ hcut → u' ∈ hcut → v' ∈ hcut →
          (∀ z ∈ hcut, z ∉ Set.Ioo u v) → (∀ z ∈ hcut, z ∉ Set.Ioo u' v') → u < v → u' < v' →
          (u,v) ≠ (u',v') → Set.Ioo u v ∩ Set.Ioo u' v' = ∅ := by
        intro u v u' v' hu hv hu' hv' hc hc' huv huv' hne2
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨x, hx1, hx2⟩
        rcases lt_trichotomy u u' with h | h | h
        · exact hc u' hu' ⟨h, lt_trans hx2.1 hx1.2⟩
        · have hvv : v ≠ v' := by
            intro hvv
            exact hne2 (by rw [h, hvv])
          rcases lt_or_gt_of_ne hvv with hlt | hgt
          · exact hc' v hv ⟨h ▸ huv, hlt⟩
          · exact hc v' hv' ⟨lt_trans hx1.1 hx2.2, hgt⟩
        · exact hc' u hu ⟨h, lt_trans hx1.1 hx2.2⟩
      obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := (hSmem p.1).mp p.2
      obtain ⟨hp'1, hp'2, hp'3, hp'4, hp'5, hp'6⟩ := (hSmem p'.1).mp p'.2
      have hdisj := hcon p.1.1 p.1.2 p'.1.1 p'.1.2 hp1 hp2 hp'1 hp'2 hp4 hp'4 hp3 hp'3
        (fun h => hpp (Subtype.ext h))
      have hzr : z.re ∈ Set.Ioo p.1.1 p.1.2 ∩ Set.Ioo p'.1.1 p'.1.2 :=
        ⟨⟨hzA1, hzA2⟩, ⟨hzB1, hzB2⟩⟩
      rw [hdisj] at hzr
      exact hzr
  -- the union of the tiles is Q
  have hclosed_union : IsClosed (⋃ x : ι, tile x.1) :=
    isClosed_iUnion_of_finite fun x => htile_closed x.1
  have hkey : (⋃ x : ι, tile x.1) = Q := by
    refine Subset.antisymm (Set.iUnion_subset fun x => htile_sub_Q x) ?_
    intro z hz
    have h1 : z ∈ closure (⋃ x : ι, tile x.1) := by
      have h2 : z ∈ closure (interior Q) := hQci.symm ▸ hz
      have h3 := closure_mono hcover h2
      rwa [closure_closure] at h3
    rwa [hclosed_union.closure_eq] at h1
  refine ⟨Fintype.card ι, fun j => tile ((Fintype.equivFin ι).symm j).1, ?_, ?_, ?_, ?_⟩
  · have h1 : (⋃ j : Fin (Fintype.card ι), tile ((Fintype.equivFin ι).symm j).1) =
        ⋃ x : ι, tile x.1 := by
      refine Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun x => ?_)
      · exact Set.subset_iUnion (fun x : ι => tile x.1) ((Fintype.equivFin ι).symm j)
      · simpa [Equiv.symm_apply_apply] using
          Set.subset_iUnion (fun j : Fin (Fintype.card ι) => tile ((Fintype.equivFin ι).symm j).1)
            (Fintype.equivFin ι x)
    rw [h1, hkey]
  · intro j; exact htile_closed _
  · intro j; exact htile_disk _
  · intro j j' hne
    refine htile_disj _ _ ?_
    intro hcon
    exact hne (by simpa using congrArg (Fintype.equivFin ι) hcon)


end PerPieceTiling

section StarCover

universe u

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]

instance instMetrizableSpaceOfCharted : TopologicalSpace.MetrizableSpace X := by
  haveI : LocallyCompactSpace X := by
    haveI : LocallyCompactSpace ℂ := inferInstance
    exact ChartedSpace.locallyCompactSpace ℂ X
  have : RegularSpace X := inferInstance
  infer_instance

/-- An auxiliary metric on a Riemann surface, compatible with the topology. -/
noncomputable abbrev surfaceMetric : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X

attribute [local instance] surfaceMetric

/-- There is a countable cover of a Riemann surface by chart sources. -/
lemma exists_countable_chart_cover [Nonempty X] :
    ∃ c : ℕ → X, (⋃ n, (chartAt ℂ (c n)).source) = univ := by
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover (fun x : X => (chartAt ℂ x).source)
    (fun x => (chartAt ℂ x).open_source)
    (fun y _ => mem_iUnion.2 ⟨y, mem_chart_source ℂ y⟩)
  exact ⟨f, eq_univ_of_univ_subset hf⟩

/-- Choice of a preimage under `Encodable.encode`, if it exists. -/
noncomputable def pickEnc (α : Type*) [Encodable α] (n : ℕ) : Option α := by
  classical
  exact if h : ∃ a, Encodable.encode a = n then some h.choose else none

lemma pickEnc_encode {α : Type*} [Encodable α] (a : α) :
    pickEnc α (Encodable.encode a) = some a := by
  have h : ∃ a', Encodable.encode a' = Encodable.encode a := ⟨a, rfl⟩
  rw [pickEnc, dif_pos h]
  congr 1
  exact Encodable.encode_injective (Classical.choose_spec h)

/-- **A locally finite closed cover by coordinate disks whose overlapping members lie in a common
chart** (the "star-refined" cover). -/
theorem exists_star_cover [Nonempty X] :
    ∃ (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ) (r : ℕ → Set X),
      (∀ n, e n ∈ atlas ℂ X) ∧
      (∀ n, r n = ∅ ∨ (0 < s n ∧ Metric.closedBall ((e n) (x n)) (s n) ⊆ (e n).target ∧
        r n = (e n).symm '' Metric.closedBall ((e n) (x n)) (s n))) ∧
      (⋃ n, r n = univ) ∧ LocallyFinite r ∧ (∀ n, IsClosed (r n)) ∧
      (∀ n m, (r n ∩ r m).Nonempty → r n ∪ r m ⊆ (e n).source ∩ (e m).source) := by
  classical
  obtain ⟨c, hc⟩ := exists_countable_chart_cover (X := X)
  set U : ℕ → Set X := fun n => (chartAt ℂ (c n)).source with hUdef
  have hUopen : ∀ n, IsOpen (U n) := fun n => (chartAt ℂ (c n)).open_source
  have hUmem : ∀ n, U n ∈ 𝓝 (c n) :=
    fun n => (hUopen n).mem_nhds (mem_chart_source ℂ (c n))
  have hUcov : ∀ y : X, ∃ n, y ∈ U n := fun y => by
    have hy : y ∈ ⋃ n, U n := by rw [hc]; exact mem_univ y
    exact mem_iUnion.mp hy
  set S : X → Set ℝ := fun x =>
    {r : ℝ | 0 < r ∧ r ≤ 1 ∧ ∃ n, Metric.closedBall x r ⊆ U n} with hSdef
  have hSne : ∀ x, (S x).Nonempty := by
    intro x
    obtain ⟨n, hn⟩ := hUcov x
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ((hUopen n).mem_nhds hn)
    refine ⟨min (ε / 2) 1, lt_min (by linarith) one_pos, min_le_right _ _, n, ?_⟩
    refine Subset.trans (Metric.closedBall_subset_closedBall (min_le_left (ε / 2) 1)) ?_
    intro y hy
    refine hsub ?_
    rw [Metric.mem_ball]
    have h1 : dist y x ≤ ε / 2 := Metric.mem_closedBall.mp hy
    linarith
  have hSbdd : ∀ x, BddAbove (S x) := fun x => ⟨1, fun r hr => hr.2.1⟩
  set ρ : X → ℝ := fun x => sSup (S x) with hρdef
  have hρpos : ∀ x, 0 < ρ x := by
    intro x
    obtain ⟨r, hr⟩ := hSne x
    rw [hρdef]
    exact lt_of_lt_of_le hr.1 (le_csSup (hSbdd x) hr)
  have hρhalf : ∀ x, ∃ n, Metric.closedBall x (ρ x / 2) ⊆ U n := by
    intro x
    have hlt : ρ x / 2 < sSup (S x) := by
      have h := hρpos x
      rw [hρdef] at h
      linarith
    obtain ⟨r, hr, hlt'⟩ := (lt_csSup_iff (hSbdd x) (hSne x)).mp hlt
    exact ⟨hr.2.2.choose, Subset.trans (Metric.closedBall_subset_closedBall (le_of_lt hlt'))
      hr.2.2.choose_spec⟩
  have hρlipschitz : ∀ x y, ρ x ≤ ρ y + dist x y := by
    intro x y
    rw [hρdef]
    refine csSup_le (hSne x) fun r hr => ?_
    rcases lt_or_ge (dist x y) r with h | h
    · have hmem : r - dist x y ∈ S y := by
        obtain ⟨hr0, hr1, n, hn⟩ := hr
        refine ⟨by linarith, by linarith [dist_nonneg (x := x) (y := y)], n, fun z hz => hn ?_⟩
        rw [Metric.mem_closedBall] at hz ⊢
        calc dist z x ≤ dist z y + dist y x := dist_triangle z y x
          _ = dist z y + dist x y := by rw [dist_comm y x]
          _ ≤ (r - dist x y) + dist x y := by linarith
          _ = r := by ring
      have h2 : r - dist x y ≤ ρ y := by
        rw [hρdef]; exact le_csSup (hSbdd y) hmem
      linarith
    · have := hρpos y; linarith
  choose nx hnx using hρhalf
  set E : X → OpenPartialHomeomorph X ℂ := fun x => chartAt ℂ (c (nx x)) with hEdef
  have hEatlas : ∀ x, E x ∈ atlas ℂ X := fun x => chart_mem_atlas ℂ (c (nx x))
  have hEsrc : ∀ x, Metric.closedBall x (ρ x / 2) ⊆ (E x).source := fun x => hnx x
  have hxsrc : ∀ x, x ∈ (E x).source := fun x =>
    hEsrc x (Metric.mem_closedBall_self (by have := hρpos x; linarith))
  have hEtgt : ∀ x, (E x).target ∈ 𝓝 ((E x) x) :=
    fun x => (E x).open_target.mem_nhds ((E x).map_source (hxsrc x))
  set Bs : X → Set (Set X) := fun x => {C | ∃ s : ℝ, 0 < s ∧
      Metric.closedBall ((E x) x) s ⊆ (E x).target ∧
      C = (E x).symm '' Metric.closedBall ((E x) x) s ∧
      C ⊆ Metric.closedBall x (ρ x / 12)} with hBsdef
  have hbasis : ∀ x, (𝓝 x).HasBasis (fun C : Set X => C ∈ Bs x) id := by
    intro x
    rw [Filter.hasBasis_iff]
    intro t
    constructor
    · intro ht
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ht
      obtain ⟨ε', hε', hsub'⟩ := Metric.mem_nhds_iff.mp (hEtgt x)
      have hcont : ContinuousAt (E x).symm ((E x) x) :=
        ((E x).continuousOn_symm).continuousAt (hEtgt x)
      have hg : 0 < ρ x / 12 := by have := hρpos x; linarith
      have hδ : 0 < min (min ε (ρ x / 12)) 1 := lt_min (lt_min hε hg) one_pos
      have hball : Metric.ball x (min (min ε (ρ x / 12)) 1) ∈
          𝓝 ((E x).symm ((E x) x)) := by
        rw [(E x).left_inv (hxsrc x)]
        exact Metric.ball_mem_nhds x hδ
      obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp (hcont hball)
      set s0 : ℝ := min (min (η / 2) (ρ x / 12)) (ε' / 2) with hs0def
      have hs0pos : 0 < s0 := lt_min (lt_min (by linarith) hg) (by linarith)
      have hs0η : s0 < η := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
        (by linarith)
      have hs0ε : s0 < ε' := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      refine ⟨(E x).symm '' Metric.closedBall ((E x) x) s0, ?_, ?_⟩
      · refine ⟨s0, hs0pos, ?_, rfl, ?_⟩
        · exact Subset.trans (Metric.closedBall_subset_ball hs0ε) hsub'
        · rintro w ⟨v, hv, rfl⟩
          have hvη : v ∈ Metric.ball ((E x) x) η :=
            Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hv) hs0η)
          have h1 := hηsub hvη
          simp only [mem_preimage, Metric.mem_ball] at h1
          refine Metric.mem_closedBall.mpr ?_
          exact le_of_lt (lt_of_lt_of_le h1 (le_trans (min_le_left _ _) (min_le_right _ _)))
      · intro z hz
        obtain ⟨v, hv, rfl⟩ := hz
        have hvη : v ∈ Metric.ball ((E x) x) η :=
          Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hv) hs0η)
        have h1 := hηsub hvη
        simp only [mem_preimage, Metric.mem_ball] at h1
        refine hsub ?_
        rw [Metric.mem_ball]
        exact lt_of_lt_of_le h1 (le_trans (min_le_left _ _) (min_le_left _ _))
    · rintro ⟨C, hC, hCt⟩
      obtain ⟨s, hs, -, hCE, hsub⟩ := hC
      have hpre : (E x).symm ⁻¹' C ∈ 𝓝 ((E x) x) := by
        rw [hCE]
        exact Filter.mem_of_superset (Metric.ball_mem_nhds ((E x) x) hs)
          (fun v hv => ⟨v, Metric.ball_subset_closedBall hv, rfl⟩)
      have hmap : C ∈ (𝓝 ((E x) x)).map (E x).symm := by
        rw [Filter.mem_map]; exact hpre
      rw [(E x).symm_map_nhds_eq (hxsrc x)] at hmap
      exact Filter.mem_of_superset hmap hCt
  haveI : LocallyCompactSpace X := by
    haveI : LocallyCompactSpace ℂ := inferInstance
    exact ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨α, x, r, hr, hcov, hlf⟩ := refinement_of_locallyCompact_sigmaCompact_of_nhds_basis
      (ι := fun _ : X => Set X) (p := fun x C => C ∈ Bs x) (B := fun _ C => C)
      (fun x => hbasis x)
  choose s hs hst hreq hrsub using fun a => hr a
  have hClos : ∀ a, IsClosed (r a) := by
    intro a
    rw [hreq a]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      (((E (x a)).continuousOn_symm).mono (hst a)) |> IsCompact.isClosed
  have hstar : ∀ a b, (r a ∩ r b).Nonempty → r a ∪ r b ⊆ (E (x a)).source ∩ (E (x b)).source := by
    intro a b hab
    obtain ⟨z, hza, hzb⟩ := hab
    have hza' : dist z (x a) ≤ ρ (x a) / 12 := Metric.mem_closedBall.mp (hrsub a hza)
    have hzb' : dist z (x b) ≤ ρ (x b) / 12 := Metric.mem_closedBall.mp (hrsub b hzb)
    have hd : dist (x a) (x b) ≤ ρ (x a) / 12 + ρ (x b) / 12 := by
      calc dist (x a) (x b) ≤ dist (x a) z + dist z (x b) := dist_triangle _ _ _
        _ ≤ ρ (x a) / 12 + ρ (x b) / 12 := by
          have h1 := dist_comm (x a) z
          have h2 := dist_comm (x b) z
          linarith
    have hlipb : ρ (x b) ≤ ρ (x a) + dist (x a) (x b) := by
      have h := hρlipschitz (x b) (x a); rwa [dist_comm] at h
    have hlips : ρ (x a) ≤ ρ (x b) + dist (x a) (x b) := hρlipschitz (x a) (x b)
    have hb13 : ρ (x b) ≤ 2 * ρ (x a) := by nlinarith [hlipb, hd, hρpos (x a)]
    have ha13 : ρ (x a) ≤ 2 * ρ (x b) := by nlinarith [hlips, hd, hρpos (x b)]
    have keyA : ∀ w ∈ r a, dist w (x a) ≤ ρ (x a) / 2 := fun w hw => by
      have h := Metric.mem_closedBall.mp (hrsub a hw)
      linarith [hρpos (x a)]
    have keyB : ∀ w ∈ r b, dist w (x b) ≤ ρ (x b) / 2 := fun w hw => by
      have h := Metric.mem_closedBall.mp (hrsub b hw)
      linarith [hρpos (x b)]
    have keyAB : ∀ w ∈ r b, dist w (x a) ≤ ρ (x a) / 2 := fun w hw => by
      have hw' : dist w (x b) ≤ ρ (x b) / 12 := Metric.mem_closedBall.mp (hrsub b hw)
      have h1 : dist w (x a) ≤ dist w (x b) + dist (x b) (x a) := dist_triangle w (x b) (x a)
      have h2 : dist (x b) (x a) = dist (x a) (x b) := dist_comm _ _
      have hnum : ρ (x b) / 12 + (ρ (x a) / 12 + ρ (x b) / 12) ≤ ρ (x a) / 2 := by
        linarith [hb13]
      have h3 : dist (x b) (x a) ≤ ρ (x a) / 12 + ρ (x b) / 12 := by rw [h2]; exact hd
      linarith
    have keyBA : ∀ w ∈ r a, dist w (x b) ≤ ρ (x b) / 2 := fun w hw => by
      have hw' : dist w (x a) ≤ ρ (x a) / 12 := Metric.mem_closedBall.mp (hrsub a hw)
      have h1 : dist w (x b) ≤ dist w (x a) + dist (x a) (x b) := dist_triangle w (x a) (x b)
      have hnum : ρ (x a) / 12 + (ρ (x b) / 12 + ρ (x a) / 12) ≤ ρ (x b) / 2 := by
        linarith [ha13]
      have h3 : dist (x a) (x b) ≤ ρ (x a) / 12 + ρ (x b) / 12 := hd
      linarith
    intro w hw
    rcases hw with hw | hw
    · exact ⟨hEsrc (x a) (Metric.mem_closedBall.mpr (keyA w hw)),
        hEsrc (x b) (Metric.mem_closedBall.mpr (keyBA w hw))⟩
    · exact ⟨hEsrc (x a) (Metric.mem_closedBall.mpr (keyAB w hw)),
        hEsrc (x b) (Metric.mem_closedBall.mpr (keyB w hw))⟩
  -- reindex the cover by ℕ
  haveI hEnc : Encodable α := hlf.encodable (fun a => ⟨x a, by
    rw [hreq a]
    exact ⟨(E (x a)) (x a), Metric.mem_closedBall_self (hs a).le,
      (E (x a)).left_inv (hxsrc (x a))⟩⟩)
  refine ⟨fun n => (pickEnc α n).elim (Classical.arbitrary X) x,
    fun n => (pickEnc α n).elim (chartAt ℂ (Classical.arbitrary X)) (fun a => E (x a)),
    fun n => (pickEnc α n).elim 1 s,
    fun n => (pickEnc α n).elim ∅ r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    cases hp : pickEnc α n with
    | none => simp only [hp, Option.elim_none]; exact chart_mem_atlas ℂ _
    | some a => simp only [hp, Option.elim_some]; exact hEatlas (x a)
  · intro n
    cases hp : pickEnc α n with
    | none => exact Or.inl (by simp only [hp, Option.elim_none])
    | some a => simp only [hp, Option.elim_some]
                exact Or.inr ⟨hs a, hst a, hreq a⟩
  · rw [eq_univ_iff_forall]
    intro y
    have hy : y ∈ ⋃ a, r a := by rw [hcov]; exact mem_univ y
    rcases mem_iUnion.mp hy with ⟨a, ha⟩
    refine mem_iUnion.mpr ⟨Encodable.encode a, ?_⟩
    simp only [pickEnc_encode (α := α) a, Option.elim_some]
    exact ha
  · intro z
    obtain ⟨t, ht, hfin⟩ := hlf z
    refine ⟨t, ht, (hfin.image (Encodable.encode (α := α))).subset ?_⟩
    intro n hn
    cases hp : pickEnc α n with
    | none =>
      simp only [hp, Option.elim_none, Set.mem_ofPred_eq] at hn
      exact absurd hn (by simp)
    | some a =>
      simp only [hp, Option.elim_some, Set.mem_ofPred_eq] at hn
      refine ⟨a, hn, ?_⟩
      have h : ∃ a' : α, Encodable.encode a' = n := by
        by_contra hcon
        rw [pickEnc, dif_neg hcon] at hp
        exact absurd hp (by simp)
      rw [pickEnc, dif_pos h] at hp
      have hca : h.choose = a := Option.some.inj hp
      rw [← hca]
      exact h.choose_spec
  · intro n
    cases hp : pickEnc α n with
    | none => simp only [hp, Option.elim_none]; exact isClosed_empty
    | some a => simp only [hp, Option.elim_some]; exact hClos a
  · intro n m hnm
    cases hn : pickEnc α n with
    | none =>
      simp only [hn, Option.elim_none] at hnm
      exact absurd hnm (by simp)
    | some a =>
      cases hm : pickEnc α m with
      | none =>
        simp only [hn, hm, Option.elim_none, Option.elim_some] at hnm
        exact absurd hnm (by simp)
      | some b =>
        simp only [hn, hm, Option.elim_some] at hnm ⊢
        exact hstar a b hnm

end StarCover

section CurveFamily

open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Chart transitions between two charts of the atlas of a one-dimensional complex manifold are
complex-analytic on their source. -/
theorem analyticOnNhd_transition_atlas {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (h₁ : e₁ ∈ atlas ℂ X) (h₂ : e₂ ∈ atlas ℂ X) :
    AnalyticOnNhd ℂ ((e₁.symm.trans e₂) : ℂ → ℂ) (e₁.symm.trans e₂).source := by
  let e : OpenPartialHomeomorph ℂ ℂ := e₁.symm.trans e₂
  change AnalyticOnNhd ℂ e e.source
  have hG : e ∈ contDiffGroupoid (1 : ℕ∞ω) (modelWithCornersSelf ℂ ℂ) := by
    dsimp only [e]
    exact StructureGroupoid.compatible (contDiffGroupoid (1 : ℕ∞ω) (modelWithCornersSelf ℂ ℂ)) h₁ h₂
  have hcd : ContDiffOn ℂ (1 : ℕ∞ω) e e.source := by
    rw [contDiffGroupoid] at hG
    rw [mem_groupoid_of_pregroupoid] at hG
    simpa [contDiffPregroupoid] using hG.1
  exact DifferentiableOn.analyticOnNhd (f := (e : ℂ → ℂ)) hcd.differentiableOn_one e.open_source

/-- The `m`-th boundary circle of a star cover, as a point of the chart target of `e m`. -/
noncomputable def starPoint (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    (m : ℕ) (t : ℝ) : ℂ :=
  (e m) (x m) + (s m : ℂ) * Complex.exp (Complex.I * (t : ℂ))

/-- The `m`-th boundary curve of a star cover, seen in the chart `e n`. -/
noncomputable def starCurve (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    (n m : ℕ) (t : ℝ) : ℂ :=
  ((e n) ((e m).symm (starPoint x e s m t)) - (e n) (x n)) / (2 * (s n : ℂ))

/-- The circle of radius `s m` around `(e m) (x m)` lies in the chart target. -/
lemma starPoint_mem_target (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    {m : ℕ} {t : ℝ} (hs : 0 < s m)
    (ht : Metric.closedBall ((e m) (x m)) (s m) ⊆ (e m).target) :
    starPoint x e s m t ∈ (e m).target := by
  refine ht (Metric.mem_closedBall.mpr ?_)
  have hsub : ((e m) (x m) + (s m : ℂ) * Complex.exp (Complex.I * (t : ℂ))) - (e m) (x m)
      = (s m : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := by ring
  rw [starPoint, dist_eq_norm, hsub, norm_mul]
  have h1 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring]
    exact Complex.norm_exp_ofReal_mul_I t
  have h2 : ‖(s m : ℂ)‖ = s m := by
    have h3 : ‖(s m : ℂ)‖ ^ 2 = (s m) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
      ring
    nlinarith [norm_nonneg (s m : ℂ)]
  rw [h1, mul_one, h2]

/-- The base curve is the round circle of radius `1/2`. -/
lemma starCurve_self (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    {n : ℕ} {t : ℝ} (hs : 0 < s n)
    (ht : Metric.closedBall ((e n) (x n)) (s n) ⊆ (e n).target) :
    starCurve x e s n n t = (1 / 2 : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := by
  have hz : starPoint x e s n t ∈ (e n).target := starPoint_mem_target x e s hs ht
  have hsc : ∀ u : ℝ, starCurve x e s n n u =
      ((e n) ((e n).symm (starPoint x e s n u)) - (e n) (x n)) / (2 * (s n : ℂ)) := fun u => rfl
  have hsp : starPoint x e s n t =
      (e n) (x n) + (s n : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := rfl
  rw [hsc t, (e n).right_inv hz, hsp]
  have hne : (s n : ℂ) ≠ 0 := by simpa using hs.ne'
  field_simp
  ring

/-- Continuity of the `m`-th boundary curve, seen in the chart `e n`. -/
lemma continuous_starCurve (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    (n m : ℕ) (hs : 0 < s m)
    (ht : Metric.closedBall ((e m) (x m)) (s m) ⊆ (e m).target)
    (htgt : ∀ t, (e m).symm (starPoint x e s m t) ∈ (e n).source) :
    Continuous (starCurve x e s n m) := by
  have hcs : Continuous (starPoint x e s m) := by
    have h1 : starPoint x e s m =
        fun t : ℝ => (e m) (x m) + (s m : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := rfl
    rw [h1]
    fun_prop
  have hct : ContinuousOn ((e m).symm.trans (e n) : ℂ → ℂ) ((e m).symm.trans (e n)).source :=
    ((e m).symm.trans (e n)).continuousOn
  have hcomp : Continuous (((e m).symm.trans (e n) : ℂ → ℂ) ∘ starPoint x e s m) :=
    hct.comp_continuous hcs (fun t => ⟨starPoint_mem_target x e s hs ht, htgt t⟩)
  have hlin : Continuous (fun w : ℂ => (w - (e n) (x n)) / (2 * (s n : ℂ))) := by fun_prop
  have hgoal : Continuous (fun t : ℝ =>
      (((e m).symm.trans (e n) : ℂ → ℂ) (starPoint x e s m t) - (e n) (x n)) / (2 * (s n : ℂ))) :=
    hlin.comp hcomp
  have hdef : starCurve x e s n m = fun t : ℝ =>
      (((e m).symm.trans (e n) : ℂ → ℂ) (starPoint x e s m t) - (e n) (x n)) / (2 * (s n : ℂ)) := by
    funext t
    simp only [starCurve, OpenPartialHomeomorph.trans_apply]
  rw [hdef]
  exact hgoal

/-- Real-analyticity of the `m`-th boundary curve, seen in the chart `e n`. -/
lemma analyticAt_starCurve_re (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    (he : ∀ m, e m ∈ atlas ℂ X) (n m : ℕ) (t : ℝ)
    (hz : starPoint x e s m t ∈ (e m).target)
    (hz' : (e m).symm (starPoint x e s m t) ∈ (e n).source) :
    AnalyticAt ℝ (fun t : ℝ => (starCurve x e s n m t).re) t := by
  have htr : AnalyticAt ℂ (fun u : ℂ => (e n) ((e m).symm u)) (starPoint x e s m t) := by
    have h1 : (fun u : ℂ => (e n) ((e m).symm u)) = ((e m).symm.trans (e n) : ℂ → ℂ) := by
      funext u
      rw [OpenPartialHomeomorph.trans_apply]
    rw [h1]
    exact (analyticOnNhd_transition_atlas (e₁ := e m) (e₂ := e n) (he m) (he n))
      (starPoint x e s m t) ⟨hz, hz'⟩
  have hs : AnalyticAt ℂ (fun w : ℂ => (e m) (x m) + w)
      ((s m : ℂ) * Complex.exp (Complex.I * (t : ℂ))) := by
    have h1 : (fun w : ℂ => (e m) (x m) + w) =
        (fun w : ℂ => (fun _ : ℂ => (e m) (x m)) w + w) := rfl
    rw [h1]
    exact analyticAt_const.add analyticAt_id
  have hcomp : AnalyticAt ℂ (fun w : ℂ => (e n) ((e m).symm ((e m) (x m) + w)))
      ((s m : ℂ) * Complex.exp (Complex.I * (t : ℂ))) := by
    have h := AnalyticAt.comp (f := fun w : ℂ => (e m) (x m) + w) htr hs
    have hfun : ((fun u : ℂ => (e n) ((e m).symm u)) ∘ fun w : ℂ => (e m) (x m) + w) =
        (fun w : ℂ => (e n) ((e m).symm ((e m) (x m) + w))) := rfl
    rwa [hfun] at h
  have hsub : AnalyticAt ℂ (fun w : ℂ =>
      (e n) ((e m).symm ((e m) (x m) + w)) - (e n) (x n))
      ((s m : ℂ) * Complex.exp (Complex.I * (t : ℂ))) :=
    hcomp.sub (analyticAt_const :
      AnalyticAt ℂ (fun _ : ℂ => (e n) (x n)) ((s m : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
  have hdiv : AnalyticAt ℂ (fun w : ℂ =>
      ((e n) ((e m).symm ((e m) (x m) + w)) - (e n) (x n)) / (2 * (s n : ℂ)))
      ((s m : ℂ) * Complex.exp (Complex.I * (t : ℂ))) := hsub.div_const
  have hgoal : (fun u : ℝ => (starCurve x e s n m u).re) =
      (fun u : ℝ => (((fun w : ℂ =>
        ((e n) ((e m).symm ((e m) (x m) + w)) - (e n) (x n)) / (2 * (s n : ℂ)))
        ((s m : ℂ) * Complex.exp (Complex.I * (u : ℂ)))).re)) := by
    funext u
    simp only [starCurve, starPoint]
  rw [hgoal]
  exact analyticAt_re_comp_circle (ψ := fun w : ℂ =>
    ((e n) ((e m).symm ((e m) (x m) + w)) - (e n) (x n)) / (2 * (s n : ℂ)))
    (ρ := s m) (θ := t) hdiv

/-- **Finitely many neighbours.**  Only finitely many members of a locally finite family of sets meet
a given compact member. -/
lemma finite_setOf_inter_nonempty {r : ℕ → Set X} (hlf : LocallyFinite r) {n : ℕ}
    (hcomp : IsCompact (r n)) : {m : ℕ | (r m ∩ r n).Nonempty}.Finite := by
  classical
  choose U hU hfin using fun z : X => hlf z
  obtain ⟨t, -, hcov⟩ := hcomp.elim_nhds_subcover U (fun z _ => hU z)
  refine (t.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  rintro m ⟨y, hy1, hy2⟩
  rcases mem_iUnion₂.mp (hcov hy2) with ⟨z, hzt, hyz⟩
  exact mem_biUnion hzt ⟨y, hy1, hyz⟩

/-- The finite set of star-cover members meeting the `n`-th member. -/
noncomputable def neighbourFinset {r : ℕ → Set X} (hlf : LocallyFinite r) {n : ℕ}
    (hcomp : IsCompact (r n)) : Finset ℕ :=
  (finite_setOf_inter_nonempty hlf hcomp).toFinset

lemma mem_neighbourFinset {r : ℕ → Set X} (hlf : LocallyFinite r) {n : ℕ}
    (hcomp : IsCompact (r n)) {m : ℕ} :
    m ∈ neighbourFinset hlf hcomp ↔ (r m ∩ r n).Nonempty :=
  Set.Finite.mem_toFinset (finite_setOf_inter_nonempty hlf hcomp)

/-- Each member of a star cover is compact. -/
lemma isCompact_of_starData {r : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ}
    {ss : ℕ → ℝ}
    (h : ∀ n, r n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      r n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n))) :
    ∀ n, IsCompact (r n) := by
  intro n
  rcases h n with h0 | ⟨-, ht, hr⟩
  · rw [h0]
    exact isCompact_empty
  · rw [hr]
    exact (isCompact_closedBall _ _).image_of_continuousOn (((ee n).continuousOn_symm).mono ht)

/-- The angle parametrisation of the boundary circle is injective on `[0, 2π)`. -/
lemma injOn_starPoint (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    (m : ℕ) (hs : 0 < s m) : Set.InjOn (starPoint x e s m) (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht u hu htu
  have h1 : (s m : ℂ) * Complex.exp (Complex.I * (t : ℂ)) =
      (s m : ℂ) * Complex.exp (Complex.I * (u : ℂ)) := by
    have h := htu
    simp only [starPoint] at h
    exact add_left_cancel h
  have h2 : Complex.exp (Complex.I * (t : ℂ)) = Complex.exp (Complex.I * (u : ℂ)) :=
    mul_left_cancel₀ (by exact_mod_cast hs.ne') h1
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h2
  have hka : (t : ℂ) - (u : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h3 : Complex.I * ((t : ℂ) - (u : ℂ)) =
        Complex.I * ((k : ℂ) * (2 * (Real.pi : ℂ))) := by
      rw [mul_sub, hk]
      ring
    exact mul_left_cancel₀ Complex.I_ne_zero h3
  have hk' : ((t - u : ℝ) : ℂ) = ((k : ℝ) * (2 * Real.pi) : ℝ) := by
    rw [Complex.ofReal_sub, hka]
    push_cast
    ring
  have hku : t - u = (k : ℝ) * (2 * Real.pi) := Complex.ofReal_injective hk'
  have hk0 : k = 0 := by
    have ht0 : 0 ≤ t := (Set.mem_Ico.mp ht).1
    have ht2 : t < 2 * Real.pi := (Set.mem_Ico.mp ht).2
    have hu0 : 0 ≤ u := (Set.mem_Ico.mp hu).1
    have hu2 : u < 2 * Real.pi := (Set.mem_Ico.mp hu).2
    have hlt1 : -2 * Real.pi < t - u := by linarith
    have hlt2 : t - u < 2 * Real.pi := by linarith
    have hb1 : (-1 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
    have hb2 : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have hb3 : (-1 : ℤ) < k := by exact_mod_cast hb1
    have hb4 : k < (1 : ℤ) := by exact_mod_cast hb2
    omega
  rw [hk0] at hku
  push_cast at hku
  linarith

/-- The boundary curve is injective on `[0, 2π)`. -/
lemma injOn_starCurve (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    (n m : ℕ) (hs : 0 < s m) (hsn : 0 < s n)
    (htm : Metric.closedBall ((e m) (x m)) (s m) ⊆ (e m).target)
    (hsrc : ∀ t, (e m).symm (starPoint x e s m t) ∈ (e n).source) :
    Set.InjOn (starCurve x e s n m) (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht u hu htu
  have h2 := htu
  simp only [starCurve] at h2
  have hsn0 : (s n : ℂ) ≠ 0 := by simpa using hsn.ne'
  have h3 : (e n) ((e m).symm (starPoint x e s m t)) =
      (e n) ((e m).symm (starPoint x e s m u)) := by
    have h := h2
    field_simp at h
    exact add_right_cancel (by simpa only [sub_eq_add_neg] using h)
  have h4 : (e m).symm (starPoint x e s m t) = (e m).symm (starPoint x e s m u) :=
    (e n).injOn (hsrc t) (hsrc u) h3
  have h5 : starPoint x e s m t = starPoint x e s m u :=
    (e m).symm.injOn (starPoint_mem_target x e s hs htm)
      (starPoint_mem_target x e s hs htm) h4
  exact injOn_starPoint x e s m hs ht hu h5

/-- The norm of a real number, as a complex number. -/
lemma norm_coe_real (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h3 : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, sq_abs]
    ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r]

/-- The distance from the parametrised circle point to the centre. -/
lemma dist_starPoint (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ) (m : ℕ) (t : ℝ)
    (hs : 0 < s m) : dist (starPoint x e s m t) ((e m) (x m)) = s m := by
  have hsub : ((e m) (x m) + (s m : ℂ) * Complex.exp (Complex.I * (t : ℂ))) - (e m) (x m)
      = (s m : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := by ring
  rw [starPoint, dist_eq_norm, hsub, norm_mul]
  have h1 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring]
    exact Complex.norm_exp_ofReal_mul_I t
  rw [h1, mul_one, norm_coe_real, abs_of_pos hs]

/-- The parametrised boundary point of the `m`-th star-cover member belongs to that member. -/
lemma starPoint_symm_mem {r : ℕ → Set X} (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ)
    (s : ℕ → ℝ) {m : ℕ} (t : ℝ) (hs : 0 < s m)
    (hr : r m = (e m).symm '' Metric.closedBall ((e m) (x m)) (s m)) :
    (e m).symm (starPoint x e s m t) ∈ r m := by
  rw [hr]
  exact ⟨starPoint x e s m t, Metric.mem_closedBall.mpr (le_of_eq (dist_starPoint x e s m t hs)), rfl⟩

/-- The data of a star-cover member known to be nonempty: positive radius, the circle is inside the
chart target, and the member is the image of that circle. -/
lemma starData_of_ne_empty {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ}
    {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    {n : ℕ} (hne : rr n ≠ ∅) :
    0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n) := by
  rcases hdat n with h0 | h
  · exact absurd h0 hne
  · exact h

/-- The same for a member that meets another member. -/
lemma starData_of_inter {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ}
    {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    {m n : ℕ} (hmn : (rr m ∩ rr n).Nonempty) :
    0 < ss m ∧ Metric.closedBall ((ee m) (xx m)) (ss m) ⊆ (ee m).target ∧
      rr m = (ee m).symm '' Metric.closedBall ((ee m) (xx m)) (ss m) :=
  starData_of_ne_empty hdat fun h0 => by
    obtain ⟨y, hy, -⟩ := hmn
    rw [h0] at hy
    exact hy

/-- **The star property supplies the chart-source membership** needed by `continuous_starCurve`,
`analyticAt_starCurve_re` and `injOn_starCurve`: for neighbouring members, every point of the `m`-th
boundary circle lies in the source of the chart of the base member `n`. -/
lemma starCurve_hsrc {rr : ℕ → Set X} (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ)
    (ss : ℕ → ℝ)
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {m n : ℕ} (hmn : (rr m ∩ rr n).Nonempty) :
    ∀ t : ℝ, (ee m).symm (starPoint xx ee ss m t) ∈ (ee n).source := by
  obtain ⟨hs, -, hr⟩ := starData_of_inter hdat hmn
  intro t
  exact (hstar m n hmn (Or.inl (starPoint_symm_mem xx ee ss t hs hr))).2

/-- The circle point of a neighbouring member lies in its own chart target. -/
lemma starPoint_mem_target_of_inter {rr : ℕ → Set X} (xx : ℕ → X)
    (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    {m n : ℕ} (hmn : (rr m ∩ rr n).Nonempty) (t : ℝ) :
    starPoint xx ee ss m t ∈ (ee m).target :=
  starPoint_mem_target xx ee ss (starData_of_inter hdat hmn).1 (starData_of_inter hdat hmn).2.1

/-- The chart-source membership for the base member itself (the round circle). -/
lemma starCurve_hsrc_self {rr : ℕ → Set X} (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ)
    (ss : ℕ → ℝ)
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    {n : ℕ} (hne : rr n ≠ ∅) :
    ∀ t : ℝ, (ee n).symm (starPoint xx ee ss n t) ∈ (ee n).source := by
  obtain ⟨hs, ht, hr⟩ := starData_of_ne_empty hdat hne
  intro t
  have hmem : (ee n).symm (starPoint xx ee ss n t) ∈ rr n := starPoint_symm_mem xx ee ss t hs hr
  rw [hr] at hmem
  have hsub : (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).source := by
    rw [← (ee n).symm_image_target_eq_source]
    exact Set.image_mono ht
  exact hsub hmem
/-- **The frontier of an ownership piece.**  For a family `C` of closed sets, the frontier of the
piece `closure (C n \ ⋃_{m<n} C m)` is contained in the frontier of `C n` together with the frontiers
of the earlier members.  This is what makes the boundary curves of the star cover cover the frontier
of every piece. -/
lemma frontier_piece_subset {X : Type*} [TopologicalSpace X] (C : ℕ → Set X)
    (hcl : ∀ n, IsClosed (C n)) (n : ℕ) :
    frontier (closure (C n \ ⋃ m ∈ Set.Iio n, C m)) ⊆
      frontier (C n) ∪ ⋃ m ∈ Set.Iio n, frontier (C m) := by
  set U : Set X := ⋃ m ∈ Set.Iio n, C m with hUdef
  have hUcl : IsClosed U := by
    have h1 : Set.Iio n = ((Finset.range n : Finset ℕ) : Set ℕ) := by
      ext m
      simp [Finset.mem_range]
    rw [hUdef, h1]
    exact isClosed_biUnion_finset (fun m _ => hcl m)
  intro x hx
  by_contra hcon
  obtain ⟨hxn, hnu⟩ := not_or.mp hcon
  have hm : ∀ m ∈ Set.Iio n, x ∉ frontier (C m) :=
    fun m hmn hx => hnu (mem_biUnion hmn hx)
  -- `x` lies in the piece
  have hxP : x ∈ closure (C n \ U) := by
    have h := hx.1
    rwa [IsClosed.closure_eq isClosed_closure] at h
  have hxCn : x ∈ C n := by
    have h1 : x ∈ closure (C n) := closure_mono Set.sdiff_subset hxP
    rwa [IsClosed.closure_eq (hcl n)] at h1
  -- hence `x` is an interior point of `C n`
  have hxint : x ∈ interior (C n) := by
    by_contra hcon'
    exact hxn ⟨subset_closure hxCn, hcon'⟩
  by_cases hcase : ∃ m ∈ Set.Iio n, x ∈ C m
  · -- some earlier member contains `x`: a neighbourhood of `x` is disjoint from the piece
    obtain ⟨m, hmn, hxm⟩ := hcase
    have hint : x ∈ interior (C m) := by
      by_contra hcon'
      exact hm m hmn ⟨subset_closure hxm, hcon'⟩
    have hsub : C n \ U ⊆ (interior (C m))ᶜ := by
      rintro y ⟨-, hyU⟩ hyint
      exact hyU (mem_iUnion₂.mpr ⟨m, hmn, interior_subset hyint⟩)
    have : closure (C n \ U) ⊆ (interior (C m))ᶜ :=
      closure_minimal hsub (isClosed_compl_iff.mpr isOpen_interior)
    exact this hxP hint
  · -- no earlier member contains `x`, so `x` is an interior point of the piece
    simp only [not_exists, not_and] at hcase
    have hxU : x ∉ U := fun h => by
      rcases mem_iUnion₂.mp h with ⟨m, hmn, hxm⟩
      exact hcase m hmn hxm
    have hN : interior (C n) ∩ Uᶜ ∈ 𝓝 x :=
      Filter.inter_mem (isOpen_interior.mem_nhds hxint) (hUcl.isOpen_compl.mem_nhds hxU)
    have hsub : interior (C n) ∩ Uᶜ ⊆ C n \ U := fun y hy => ⟨interior_subset hy.1, hy.2⟩
    have hxiP : x ∈ interior (closure (C n \ U)) :=
      interior_mono subset_closure (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hN hsub))
    exact (Set.disjoint_left.mp disjoint_interior_frontier hxiP) hx

/-- The set of *distinct* images of the boundary curves of the `n`-th star-cover member. -/
noncomputable def curveImages {rr : ℕ → Set X} (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ)
    (ss : ℕ → ℝ) (hlf : LocallyFinite rr) {n : ℕ} (hcomp : IsCompact (rr n)) : Finset (Set ℂ) :=
  (neighbourFinset hlf hcomp).image (fun m => Set.range (starCurve xx ee ss n m))

lemma mem_curveImages {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ}
    {ss : ℕ → ℝ} {hlf : LocallyFinite rr} {n : ℕ} {hcomp : IsCompact (rr n)} {S : Set ℂ} :
    S ∈ curveImages xx ee ss hlf hcomp ↔
      ∃ m ∈ neighbourFinset hlf hcomp, Set.range (starCurve xx ee ss n m) = S :=
  Finset.mem_image

/-- **Deduplication of the boundary curves.**  The boundary curves indexed by `J n` can be re-indexed
by a finite type `Fin K` in such a way that no two of them have the same image, and every image of the
original family occurs among the re-indexed ones.  The reindexed curves are `starCurve` at selected
indices, so all the properties proved for `starCurve` transfer. -/
lemma exists_dedup_curves {rr : ℕ → Set X} (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ)
    (ss : ℕ → ℝ) (hlf : LocallyFinite rr) {n : ℕ} (hcomp : IsCompact (rr n)) :
    ∃ (K : ℕ) (mOf : Fin K → ℕ),
      (∀ k, mOf k ∈ neighbourFinset hlf hcomp) ∧
      Function.Injective (fun k => Set.range (starCurve xx ee ss n (mOf k))) ∧
      (∀ m ∈ neighbourFinset hlf hcomp, ∃ k,
        Set.range (starCurve xx ee ss n m) = Set.range (starCurve xx ee ss n (mOf k))) := by
  classical
  set IM := curveImages xx ee ss hlf hcomp with hIM
  have hcard : Fintype.card ↥IM = IM.card := Fintype.card_coe IM
  set φ : Fin IM.card ≃ ↥IM :=
    (Fin.castOrderIso hcard.symm).toEquiv.trans (Fintype.equivFin ↥IM).symm with hφ
  have hmemp : ∀ k : Fin IM.card, ∃ m ∈ neighbourFinset hlf hcomp,
      Set.range (starCurve xx ee ss n m) = (φ k : Set ℂ) :=
    fun k => Finset.mem_image.mp (φ k).2
  set mOf : Fin IM.card → ℕ := fun k => (hmemp k).choose with hmOfdef
  have hmOf_mem : ∀ k, mOf k ∈ neighbourFinset hlf hcomp := fun k => ((hmemp k).choose_spec).1
  have hmOf_eq : ∀ k, Set.range (starCurve xx ee ss n (mOf k)) = (φ k : Set ℂ) :=
    fun k => ((hmemp k).choose_spec).2
  refine ⟨IM.card, mOf, hmOf_mem, ?_, ?_⟩
  · intro k l hkl
    have hkl' : Set.range (starCurve xx ee ss n (mOf k)) =
        Set.range (starCurve xx ee ss n (mOf l)) := hkl
    have h1 : (φ k : Set ℂ) = (φ l : Set ℂ) :=
      (hmOf_eq k).symm.trans (hkl'.trans (hmOf_eq l))
    exact φ.injective (Subtype.ext h1)
  · intro m hm
    have hmem : Set.range (starCurve xx ee ss n m) ∈ IM := by
      rw [hIM]
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
    obtain ⟨k, hk⟩ := φ.surjective ⟨_, hmem⟩
    exact ⟨k, (congrArg Subtype.val hk.symm).trans (hmOf_eq k).symm⟩

/-- The affine map `w ↦ (w - z) / (2 * ρ)` sends the closed ball of radius `ρ` around `z` onto the
closed ball of radius `1/2` around `0`. -/
lemma normalize_closedBall_image (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    (fun w : ℂ => (w - z) / (2 * (ρ : ℂ))) '' Metric.closedBall z ρ =
      Metric.closedBall 0 (1 / 2) := by
  have h2ρ : (0 : ℝ) < 2 * ρ := by linarith
  have hnorm : ‖((2 * ρ : ℝ) : ℂ)‖ = 2 * ρ := by
    rw [norm_coe_real, abs_of_pos h2ρ]
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hdu : dist u z ≤ ρ := Metric.mem_closedBall.mp hu
    rw [Metric.mem_closedBall, dist_zero_right]
    simp only []
    have h1 : (u - z) / (2 * (ρ : ℂ)) = (u - z) / ((2 * ρ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, norm_div, hnorm]
    rw [div_le_iff₀ h2ρ]
    rw [dist_eq_norm] at hdu
    linarith
  · intro hw
    have hwn : ‖w‖ ≤ 1 / 2 := by
      have h := Metric.mem_closedBall.mp hw
      rwa [dist_zero_right] at h
    refine ⟨z + ((2 * ρ : ℝ) : ℂ) * w, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : z + ((2 * ρ : ℝ) : ℂ) * w - z = ((2 * ρ : ℝ) : ℂ) * w := by ring
      rw [h1, norm_mul, hnorm]
      nlinarith [hwn, h2ρ]
    · have h1 : z + ((2 * ρ : ℝ) : ℂ) * w - z = ((2 * ρ : ℝ) : ℂ) * w := by ring
      have h2 : (2 * (ρ : ℂ)) = ((2 * ρ : ℝ) : ℂ) := by push_cast; ring
      have hne : ((2 * ρ : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      change (z + ((2 * ρ : ℝ) : ℂ) * w - z) / (2 * (ρ : ℂ)) = w
      rw [h1, h2]
      field_simp

/-- **The normalised region of a star-cover piece**: the piece of the `n`-th member, seen in its own
chart and then normalised so that the member becomes the closed disk of radius `1/2`. -/
noncomputable def starRegion (rr : ℕ → Set X) (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ)
    (ss : ℕ → ℝ) (n : ℕ) : Set ℂ :=
  (fun w : ℂ => (w - (ee n) (xx n)) / (2 * (ss n : ℂ))) '' ((ee n) '' piece rr n)

/-- The normalised region of a piece sits inside the disk of radius `1/2`. -/
lemma starRegion_subset {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ}
    {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hcl : ∀ n, IsClosed (rr n)) {n : ℕ} (hne : rr n ≠ ∅) :
    starRegion rr xx ee ss n ⊆ Metric.closedBall 0 (1 / 2) := by
  obtain ⟨hs, ht, hr⟩ := starData_of_ne_empty (rr := rr) hdat hne
  rintro w ⟨y, ⟨v, hv, rfl⟩, rfl⟩
  have hv' : v ∈ rr n := piece_subset rr hcl n hv
  rw [hr] at hv'
  obtain ⟨u, hu, hue⟩ := hv'
  have h1 : (ee n) v = u := by rw [← hue]; exact (ee n).right_inv (ht hu)
  rw [h1]
  rw [← normalize_closedBall_image ((ee n) (xx n)) hs]
  exact ⟨u, hu, rfl⟩

/-- The normalised region of a piece is closed. -/
lemma isClosed_starRegion {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ}
    {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hcl : ∀ n, IsClosed (rr n)) {n : ℕ} (hne : rr n ≠ ∅) :
    IsClosed (starRegion rr xx ee ss n) := by
  obtain ⟨hs, ht, hr⟩ := starData_of_ne_empty (rr := rr) hdat hne
  have hsub : piece rr n ⊆ (ee n).source := by
    refine (piece_subset rr hcl n).trans ?_
    rw [hr, ← (ee n).symm_image_target_eq_source]
    exact Set.image_mono ht
  have h1 : IsCompact (piece rr n) :=
    (isCompact_of_starData hdat n).of_isClosed_subset (isClosed_piece rr n) (piece_subset rr hcl n)
  have h2 : IsCompact ((ee n) '' piece rr n) :=
    h1.image_of_continuousOn (((ee n).continuousOn).mono hsub)
  have h3 : IsCompact ((fun w : ℂ => (w - (ee n) (xx n)) / (2 * (ss n : ℂ))) ''
      ((ee n) '' piece rr n)) :=
    h2.image (by fun_prop)
  exact h3.isClosed

attribute [local instance] surfaceMetric

/-- **Each star-cover member is the closure of its interior.**  (For a member that is the chart image of
a positive-radius closed ball this is the transport of "the interior of a closed ball is the open ball",
with the boundary points approximated along the radius.) -/
lemma starData_closure_interior {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ}
    {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n))) :
    ∀ n, closure (interior (rr n)) = rr n := by
  intro n
  rcases hdat n with h0 | ⟨hs, ht, hr⟩
  · rw [h0]
    simp
  · rw [hr]
    set z : ℂ := (ee n) (xx n) with hz
    set ρ : ℝ := ss n with hρ
    have hρpos : 0 < ρ := by rw [hρ]; exact hs
    have htgt : Metric.closedBall z ρ ⊆ (ee n).target := by rw [hz, hρ]; exact ht
    have hScl : IsClosed ((ee n).symm '' Metric.closedBall z ρ) :=
      ((isCompact_closedBall z ρ).image_of_continuousOn
        (((ee n).continuousOn_symm).mono htgt)).isClosed
    have hball_open : IsOpen ((ee n).symm '' Metric.ball z ρ) :=
      (ee n).isOpen_image_symm_of_subset_target isOpen_ball
        (Metric.ball_subset_closedBall.trans htgt)
    have hinter : (ee n).symm '' Metric.ball z ρ ⊆
        interior ((ee n).symm '' Metric.closedBall z ρ) :=
      interior_maximal (Set.image_mono Metric.ball_subset_closedBall) hball_open
    refine Subset.antisymm (closure_minimal interior_subset hScl) fun y hy => ?_
    obtain ⟨u, hu, rfl⟩ := hy
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hcont : ContinuousAt (ee n).symm u :=
      ((ee n).continuousOn_symm).continuousAt ((ee n).open_target.mem_nhds (htgt hu))
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      (hcont (Metric.ball_mem_nhds ((ee n).symm u) hε))
    have hdu : ‖u - z‖ ≤ ρ := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp hu
    set t : ℝ := min (δ / (2 * ρ)) (1 / 2) with htdef
    have ht0 : 0 < t := lt_min (div_pos hδ (by linarith)) (by norm_num)
    have htd : t ≤ δ / (2 * ρ) := min_le_left _ _
    have ht1 : t ≤ 1 / 2 := min_le_right _ _
    have htd' : t * ρ ≤ δ / 2 := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ρ)] at htd
      linarith
    set s : ℝ := 1 - t with hsdef
    have hs0 : 0 < s := by rw [hsdef]; linarith
    have hs1 : s < 1 := by rw [hsdef]; linarith
    refine ⟨(ee n).symm (z + (s : ℂ) * (u - z)), hinter ⟨z + (s : ℂ) * (u - z), ?_, rfl⟩, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : z + (s : ℂ) * (u - z) - z = (s : ℂ) * (u - z) := by ring
      rw [h1, norm_mul, norm_coe_real, abs_of_pos hs0]
      nlinarith [hdu, hρpos, hs1, norm_nonneg (u - z)]
    · have h3 : z + (s : ℂ) * (u - z) ∈ Metric.ball u δ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : z + (s : ℂ) * (u - z) - u = (t : ℂ) * (z - u) := by
          rw [hsdef]
          push_cast
          ring
        rw [h1, norm_mul, norm_coe_real, abs_of_pos ht0]
        have h4 : ‖z - u‖ = ‖u - z‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, dist_comm]
        rw [h4]
        nlinarith [hdu, htd', hδ, norm_nonneg (u - z), hρpos]
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_comm] using hδsub h3

/-- The closure of the interior of the normalised region: this is the region handed to the disk-tiling
theorem (it has the closure-of-interior property by construction). -/
noncomputable def starRegionClosure (rr : ℕ → Set X) (xx : ℕ → X)
    (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ) (n : ℕ) : Set ℂ :=
  closure (interior (starRegion rr xx ee ss n))

lemma isClosed_starRegionClosure {rr : ℕ → Set X} {xx : ℕ → X}
    {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ} {n : ℕ} :
    IsClosed (starRegionClosure rr xx ee ss n) := isClosed_closure

/-- The region handed to the tiling theorem lies in the disk of radius `1/2`. -/
lemma starRegionClosure_subset {rr : ℕ → Set X} {xx : ℕ → X}
    {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hcl : ∀ n, IsClosed (rr n)) {n : ℕ} (hne : rr n ≠ ∅) :
    starRegionClosure rr xx ee ss n ⊆ Metric.closedBall 0 (1 / 2) :=
  closure_minimal (fun w hw => starRegion_subset (n := n) hdat hcl hne (interior_subset hw))
    isClosed_closedBall

/-- **The normalised region of a piece is contained in the closure of its interior.**  Together with
closedness this gives `closure (interior S) = S`, the last structure fact needed by the tiling theorem:
the piece is the closure of its interior, and the chart followed by the affine normalisation maps that
interior into `interior S`. -/
lemma starRegion_subset_closure_interior {rr : ℕ → Set X} {xx : ℕ → X}
    {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hcl : ∀ n, IsClosed (rr n)) {n : ℕ} (hne : rr n ≠ ∅) :
    starRegion rr xx ee ss n ⊆ closure (interior (starRegion rr xx ee ss n)) := by
  obtain ⟨hs, ht, hr⟩ := starData_of_ne_empty (rr := rr) hdat hne
  have h2ρne : ((2 * ss n : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hρne : (ss n : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hpiece : piece rr n = closure (interior (piece rr n)) :=
    piece_eq_closure_interior rr hcl (starData_closure_interior hdat) n
  have hsrc : piece rr n ⊆ (ee n).source := by
    refine (piece_subset rr hcl n).trans ?_
    rw [hr, ← (ee n).symm_image_target_eq_source]
    exact Set.image_mono ht
  have hOpen1 : IsOpen ((ee n) '' interior (piece rr n)) :=
    (ee n).isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hsrc)
  have hfwd : ∀ t : ℂ, (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) *
      ((t - (ee n) (xx n)) / (2 * (ss n : ℂ))) = t := by
    intro t
    rw [show (2 * (ss n : ℂ)) = ((2 * ss n : ℝ) : ℂ) by push_cast; ring]
    field_simp
    ring
  have hback : ∀ u : ℂ, ((ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u - (ee n) (xx n)) /
      (2 * (ss n : ℂ)) = u := by
    intro u
    rw [show (2 * (ss n : ℂ)) = ((2 * ss n : ℝ) : ℂ) by push_cast; ring,
      show (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u - (ee n) (xx n) =
        ((2 * ss n : ℝ) : ℂ) * u by ring]
    field_simp
  have hfeq : (fun w : ℂ => (w - (ee n) (xx n)) / (2 * (ss n : ℂ))) ''
        ((ee n) '' interior (piece rr n)) =
      (fun u : ℂ => (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u) ⁻¹'
        ((ee n) '' interior (piece rr n)) := by
    ext w
    constructor
    · rintro ⟨t, ht', rfl⟩
      show (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * ((t - (ee n) (xx n)) / (2 * (ss n : ℂ))) ∈
        (ee n) '' interior (piece rr n)
      rw [hfwd t]
      exact ht'
    · intro hw
      exact ⟨(ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * w, hw, hback w⟩
  have hOpen2 : IsOpen ((fun w : ℂ => (w - (ee n) (xx n)) / (2 * (ss n : ℂ))) ''
      ((ee n) '' interior (piece rr n))) := by
    rw [hfeq]
    exact hOpen1.preimage (by fun_prop)
  have hinner : (fun w : ℂ => (w - (ee n) (xx n)) / (2 * (ss n : ℂ))) ''
      ((ee n) '' interior (piece rr n)) ⊆ interior (starRegion rr xx ee ss n) :=
    interior_maximal (by
      rintro w ⟨y, ⟨v, hv, hy⟩, hw⟩
      exact ⟨(ee n) v, ⟨v, interior_subset hv, rfl⟩,
        (congrArg (fun t : ℂ => (t - (ee n) (xx n)) / (2 * (ss n : ℂ))) hy).trans hw⟩) hOpen2
  rintro w ⟨y, ⟨v, hv, rfl⟩, rfl⟩
  refine closure_mono hinner ?_
  have hv' : v ∈ closure (interior (piece rr n)) := by rw [← hpiece]; exact hv
  have hcontg : ContinuousAt (fun y : X => (ee n) y) v :=
    ((ee n).continuousOn).continuousAt ((ee n).open_source.mem_nhds (hsrc hv))
  have hcontline : Continuous fun w : ℂ => (w - (ee n) (xx n)) / (2 * (ss n : ℂ)) := by
    rw [show (fun w : ℂ => (w - (ee n) (xx n)) / (2 * (ss n : ℂ))) =
        fun w => ((2 * (ss n : ℂ))⁻¹) * (w - (ee n) (xx n)) by
      funext w
      rw [div_eq_inv_mul]]
    exact continuous_const.mul (continuous_id.sub continuous_const)
  have hcomp : ContinuousAt (fun y : X => ((ee n) y - (ee n) (xx n)) / (2 * (ss n : ℂ))) v := by
    have h1 : (fun y : X => ((ee n) y - (ee n) (xx n)) / (2 * (ss n : ℂ))) =
        (fun w : ℂ => (w - (ee n) (xx n)) / (2 * (ss n : ℂ))) ∘ (fun y : X => (ee n) y) := rfl
    rw [h1]
    exact hcontline.continuousAt.comp hcontg
  rw [_root_.mem_closure_iff]
  intro o hoopen ho
  have hpre : (fun y : X => ((ee n) y - (ee n) (xx n)) / (2 * (ss n : ℂ))) ⁻¹' o ∈ 𝓝 v :=
    hcomp (hoopen.mem_nhds ho)
  obtain ⟨o'', ho''sub, ho''open, hv''⟩ := _root_.mem_nhds_iff.mp hpre
  obtain ⟨v', hv'1, hv'2⟩ := _root_.mem_closure_iff.mp hv' o'' ho''open hv''
  exact ⟨((ee n) v' - (ee n) (xx n)) / (2 * (ss n : ℂ)), ho''sub hv'1,
    ⟨(ee n) v', ⟨v', hv'2, rfl⟩, rfl⟩⟩

/-- The closure of the interior of the normalised region is the closure of its own interior. -/
lemma closure_interior_closure_interior_starRegion {rr : ℕ → Set X} {xx : ℕ → X}
    {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hcl : ∀ n, IsClosed (rr n)) {n : ℕ} (hne : rr n ≠ ∅) :
    closure (interior (closure (interior (starRegion rr xx ee ss n)))) =
      closure (interior (starRegion rr xx ee ss n)) := by
  refine Subset.antisymm ?_ ?_
  · calc closure (interior (closure (interior (starRegion rr xx ee ss n))))
        ⊆ closure (closure (interior (starRegion rr xx ee ss n))) := closure_mono interior_subset
      _ = closure (interior (starRegion rr xx ee ss n)) := closure_closure
  · exact closure_mono (interior_mono (starRegion_subset_closure_interior hdat hcl hne))

/-- The region handed to the tiling theorem (SESSION 141) is the closure of its own interior. -/
lemma closure_interior_starRegionClosure {rr : ℕ → Set X} {xx : ℕ → X}
    {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hcl : ∀ n, IsClosed (rr n)) {n : ℕ} (hne : rr n ≠ ∅) :
    closure (interior (starRegionClosure rr xx ee ss n)) = starRegionClosure rr xx ee ss n :=
  closure_interior_closure_interior_starRegion hdat hcl hne

/-- The frontier of the region handed to the tiling theorem is contained in the frontier of the
normalised piece, which is what the boundary curves cover. -/
lemma frontier_closure_interior_starRegion_subset {rr : ℕ → Set X} {xx : ℕ → X}
    {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hcl : ∀ n, IsClosed (rr n)) {n : ℕ} (hne : rr n ≠ ∅) :
    frontier (closure (interior (starRegion rr xx ee ss n))) ⊆ frontier (starRegion rr xx ee ss n) := by
  intro p hp
  have hpiQ : p ∉ interior (closure (interior (starRegion rr xx ee ss n))) := hp.2
  have hpQ : p ∈ closure (interior (starRegion rr xx ee ss n)) := by
    simpa only [closure_closure] using hp.1
  refine ⟨?_, ?_⟩
  · exact closure_mono interior_subset hpQ
  · intro hpc
    exact hpiQ (interior_maximal (subset_closure :
      interior (starRegion rr xx ee ss n) ⊆ closure (interior (starRegion rr xx ee ss n)))
      isOpen_interior hpc)

/-- The same for the region `starRegionClosure`. -/
lemma frontier_starRegionClosure_subset {rr : ℕ → Set X} {xx : ℕ → X}
    {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hcl : ∀ n, IsClosed (rr n)) {n : ℕ} (hne : rr n ≠ ∅) :
    frontier (starRegionClosure rr xx ee ss n) ⊆ frontier (starRegion rr xx ee ss n) :=
  frontier_closure_interior_starRegion_subset hdat hcl hne

end CurveFamily


section Periodicity

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

lemma exp_I_add_two_pi (t : ℝ) :
    Complex.exp (Complex.I * ((t + 2 * Real.pi : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨1, ?_⟩
  push_cast
  ring

lemma starPoint_add_two_pi (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    (m : ℕ) (t : ℝ) :
    starPoint x e s m (t + 2 * Real.pi) = starPoint x e s m t := by
  simp only [starPoint, exp_I_add_two_pi]

lemma starCurve_add_two_pi (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ) (s : ℕ → ℝ)
    (n m : ℕ) (t : ℝ) :
    starCurve x e s n m (t + 2 * Real.pi) = starCurve x e s n m t := by
  simp only [starCurve, starPoint_add_two_pi]

lemma deriv_starCurve_re_add_two_pi (x : ℕ → X) (e : ℕ → OpenPartialHomeomorph X ℂ)
    (s : ℕ → ℝ) (n m : ℕ) (t : ℝ) :
    deriv (fun u : ℝ => (starCurve x e s n m u).re) (t + 2 * Real.pi) =
      deriv (fun u : ℝ => (starCurve x e s n m u).re) t := by
  have hfun : (fun u : ℝ => (starCurve x e s n m (u + 2 * Real.pi)).re) =
      (fun u : ℝ => (starCurve x e s n m u).re) := by
    funext u
    rw [starCurve_add_two_pi]
  have h := deriv_comp_add_const (f := fun u : ℝ => (starCurve x e s n m u).re)
    (2 * Real.pi) t
  rw [hfun] at h
  exact h.symm

lemma exists_shift_Icc_of_periodic {Y : Type*} {f : ℝ → Y}
    (hf : Function.Periodic f (2 * Real.pi)) (t : ℝ) :
    ∃ u ∈ Set.Icc 0 (2 * Real.pi), f u = f t := by
  have hc : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hc
  refine ⟨t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, hf.sub_int_mul_eq _⟩
  · have h := Int.floor_le (t / (2 * Real.pi))
    have h2 := mul_le_mul_of_nonneg_right h hc.le
    rw [div_mul_cancel₀ t hcne] at h2
    linarith
  · have h := Int.lt_floor_add_one (t / (2 * Real.pi))
    have h2 := mul_lt_mul_of_pos_right h hc
    rw [div_mul_cancel₀ t hcne] at h2
    nlinarith [h2]

lemma range_eq_image_Icc_of_periodic {Y : Type*} {f : ℝ → Y}
    (hf : Function.Periodic f (2 * Real.pi)) :
    Set.range f = f '' Set.Icc 0 (2 * Real.pi) := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range f _)
  rintro y ⟨t, rfl⟩
  obtain ⟨u, hu, hfu⟩ := exists_shift_Icc_of_periodic hf t
  exact ⟨u, hu, hfu⟩

lemma exists_shift_Icc_of_periodic_deriv {g : ℝ → ℝ}
    (hg : Function.Periodic g (2 * Real.pi)) (hg' : Function.Periodic (deriv g) (2 * Real.pi))
    (t : ℝ) :
    ∃ u ∈ Set.Icc 0 (2 * Real.pi), g u = g t ∧ deriv g u = deriv g t := by
  have hc : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hc
  refine ⟨t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩,
    hg.sub_int_mul_eq _, hg'.sub_int_mul_eq _⟩
  · have h := Int.floor_le (t / (2 * Real.pi))
    have h2 := mul_le_mul_of_nonneg_right h hc.le
    rw [div_mul_cancel₀ t hcne] at h2
    linarith
  · have h := Int.lt_floor_add_one (t / (2 * Real.pi))
    have h2 := mul_lt_mul_of_pos_right h hc
    rw [div_mul_cancel₀ t hcne] at h2
    nlinarith [h2]

end Periodicity

section CritVals

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}

lemma analyticAt_starCurve_re_of_inter
    (he : ∀ m, ee m ∈ atlas ℂ X)
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {n m : ℕ} (hmn : (rr m ∩ rr n).Nonempty) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => (starCurve xx ee ss n m u).re) t :=
  analyticAt_starCurve_re xx ee ss he n m t
    (starPoint_mem_target_of_inter xx ee ss hdat hmn t)
    (starCurve_hsrc xx ee ss hdat hstar hmn t)

lemma finite_critical_values_curve
    (he : ∀ m, ee m ∈ atlas ℂ X)
    (hdat : ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
      rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n)))
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {n m : ℕ} (hmn : (rr m ∩ rr n).Nonempty) :
    {x : ℝ | ∃ t : ℝ, deriv (fun u : ℝ => (starCurve xx ee ss n m u).re) t = 0 ∧
      (starCurve xx ee ss n m t).re = x}.Finite := by
  set g : ℝ → ℝ := fun u => (starCurve xx ee ss n m u).re with hgdef
  have hgan : AnalyticOnNhd ℝ g Set.univ :=
    fun t _ => analyticAt_starCurve_re_of_inter he hdat hstar hmn t
  have hgper : Function.Periodic g (2 * Real.pi) := fun t => by
    simp only [hgdef, starCurve_add_two_pi]
  have hdgper : Function.Periodic (deriv g) (2 * Real.pi) := fun t => by
    simp only [hgdef]
    exact deriv_starCurve_re_add_two_pi xx ee ss n m t
  have hshift : ∀ t : ℝ, ∃ u ∈ Set.Icc 0 (2 * Real.pi), g u = g t ∧ deriv g u = deriv g t :=
    fun t => exists_shift_Icc_of_periodic_deriv hgper hdgper t
  by_cases hne : ∃ t ∈ Set.Icc 0 (2 * Real.pi), deriv g t ≠ 0
  · have hfin := finite_criticalValues (f := g) (a := 0) (b := 2 * Real.pi)
      (hf := hgan.mono (Set.subset_univ _)) hne
    refine hfin.subset ?_
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨u, hu, hgu, hdu⟩ := hshift t
    exact ⟨u, hu, by rw [hdu, ht], hgu⟩
  · push_neg at hne
    have hderiv : ∀ t : ℝ, deriv g t = 0 := by
      intro t
      obtain ⟨u, hu, -, hdu⟩ := hshift t
      rw [← hdu]
      exact hne u hu
    have hdiff : Differentiable ℝ g := fun x => (hgan x (Set.mem_univ x)).differentiableAt
    refine (Set.finite_singleton (g 0)).subset ?_
    rintro x ⟨t, ht, rfl⟩
    exact is_const_of_deriv_eq_zero hdiff hderiv t 0

end CritVals

section Sigma

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}

/-- A star-cover datum: every member is either empty or the chart image of a closed ball. -/
def IsStarData (rr : ℕ → Set X) (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ)
    (ss : ℕ → ℝ) : Prop :=
  ∀ n, rr n = ∅ ∨ (0 < ss n ∧ Metric.closedBall ((ee n) (xx n)) (ss n) ⊆ (ee n).target ∧
    rr n = (ee n).symm '' Metric.closedBall ((ee n) (xx n)) (ss n))

lemma nonempty_inter_comm {s t : Set X} (h : (s ∩ t).Nonempty) : (t ∩ s).Nonempty := by
  obtain ⟨z, hz1, hz2⟩ := h
  exact ⟨z, hz2, hz1⟩

/-- The `m`-th boundary circle of a star cover, as a subset of `X`. -/
noncomputable def sigma (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (m : ℕ) : Set X :=
  Set.range (fun t : ℝ => (ee m).symm (starPoint xx ee ss m t))

lemma sigma_eq_image_Icc (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (m : ℕ) :
    sigma xx ee ss m = (fun t : ℝ => (ee m).symm (starPoint xx ee ss m t)) ''
      Set.Icc 0 (2 * Real.pi) :=
  range_eq_image_Icc_of_periodic (fun t => by simp only [starPoint_add_two_pi])

lemma sigma_subset_rr
    (hdat : IsStarData rr xx ee ss) {m n : ℕ} (hmn : (rr m ∩ rr n).Nonempty) :
    sigma xx ee ss m ⊆ rr m := by
  obtain ⟨hs, ht, hr⟩ := starData_of_inter hdat hmn
  rintro y ⟨t, rfl⟩
  exact starPoint_symm_mem xx ee ss t hs hr

lemma sigma_injOn {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}
    {m : ℕ} (hs : 0 < ss m) (ht : Metric.closedBall ((ee m) (xx m)) (ss m) ⊆ (ee m).target) :
    Set.InjOn (fun t : ℝ => (ee m).symm (starPoint xx ee ss m t)) (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht' u hu h
  exact injOn_starPoint xx ee ss m hs ht' hu
    ((ee m).symm.injOn (starPoint_mem_target xx ee ss hs ht)
      (starPoint_mem_target xx ee ss hs ht) h)

lemma normSq_of_mem_sigma
    (hdat : IsStarData rr xx ee ss) {n m : ℕ} (hmn : (rr m ∩ rr n).Nonempty) {y : X}
    (hy : y ∈ sigma xx ee ss m) :
    Complex.normSq ((ee m) y - (ee m) (xx m)) = (ss m) ^ 2 := by
  obtain ⟨hs, ht, hr⟩ := starData_of_inter hdat hmn
  obtain ⟨t, rfl⟩ := hy
  have hz : starPoint xx ee ss m t ∈ (ee m).target := starPoint_mem_target xx ee ss hs ht
  rw [(ee m).right_inv hz]
  have h1 : starPoint xx ee ss m t - (ee m) (xx m) =
      (ss m : ℂ) * Complex.exp (Complex.I * (t : ℂ)) := by
    simp only [starPoint]
    ring
  rw [h1, Complex.normSq_eq_norm_sq, norm_mul,
    show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, norm_coe_real, abs_of_pos hs]

lemma exists_exp_I_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) :
    ∃ t : ℝ, Complex.exp (Complex.I * (t : ℂ)) = z := by
  have hz : z ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact h
  rw [← Complex.range_exp_mul_I] at hz
  obtain ⟨t, ht⟩ := hz
  exact ⟨t, by rw [mul_comm]; exact ht⟩

lemma mem_sigma_of_normSq {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}
    {p : ℕ} (hs : 0 < ss p) {y : X} (hysrc : y ∈ (ee p).source)
    (h : Complex.normSq ((ee p) y - (ee p) (xx p)) = (ss p) ^ 2) :
    y ∈ sigma xx ee ss p := by
  have hspne : (ss p : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hnorm : ‖(ee p) y - (ee p) (xx p)‖ = ss p := by
    have h2 : ‖(ee p) y - (ee p) (xx p)‖ ^ 2 = (ss p) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact h
    nlinarith [norm_nonneg ((ee p) y - (ee p) (xx p)), hs.le]
  have hz : ‖((ee p) y - (ee p) (xx p)) / ((ss p : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, norm_coe_real, abs_of_pos hs, hnorm, div_self (ne_of_gt hs)]
  obtain ⟨u, hu⟩ := exists_exp_I_of_norm_eq_one hz
  refine ⟨u, ?_⟩
  have hsp : starPoint xx ee ss p u = (ee p) y := by
    simp only [starPoint]
    rw [hu]
    field_simp
    ring
  show (ee p).symm (starPoint xx ee ss p u) = y
  rw [hsp]
  exact (ee p).left_inv hysrc

lemma range_starCurve_eq (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (n m : ℕ) :
    Set.range (starCurve xx ee ss n m) =
      (fun y : X => ((ee n) y - (ee n) (xx n)) / (2 * (ss n : ℂ))) '' sigma xx ee ss m := by
  have h1 : starCurve xx ee ss n m =
      (fun y : X => ((ee n) y - (ee n) (xx n)) / (2 * (ss n : ℂ))) ∘
        (fun t : ℝ => (ee m).symm (starPoint xx ee ss m t)) := by
    funext t
    rfl
  rw [h1, Set.range_comp]
  rfl

/-- The angles where the `q`-th circle, read in the chart of `p`, lies on the `p`-th circle. -/
noncomputable def crossSet (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (p q : ℕ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
    Complex.normSq ((ee p) ((ee q).symm (starPoint xx ee ss q θ)) - (ee p) (xx p)) = (ss p) ^ 2}

lemma analyticAt_transition_shift
    (hee : ∀ m, ee m ∈ atlas ℂ X)
    (hdat : IsStarData rr xx ee ss)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {p q : ℕ} (hqp : (rr q ∩ rr p).Nonempty) (θ : ℝ) :
    AnalyticAt ℂ (fun u : ℂ => (ee p) ((ee q).symm ((ee q) (xx q) + u)))
      ((ss q : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have htr : AnalyticAt ℂ (fun u : ℂ => (ee p) ((ee q).symm u)) (starPoint xx ee ss q θ) := by
    have h1 : (fun u : ℂ => (ee p) ((ee q).symm u)) = ((ee q).symm.trans (ee p) : ℂ → ℂ) := by
      funext u
      rw [OpenPartialHomeomorph.trans_apply]
    rw [h1]
    exact (analyticOnNhd_transition_atlas (e₁ := ee q) (e₂ := ee p) (hee q) (hee p))
      (starPoint xx ee ss q θ)
      ⟨starPoint_mem_target_of_inter xx ee ss hdat hqp θ,
        starCurve_hsrc xx ee ss hdat hstar hqp θ⟩
  have hs : AnalyticAt ℂ (fun w : ℂ => (ee q) (xx q) + w)
      ((ss q : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    have h1 : (fun w : ℂ => (ee q) (xx q) + w) =
        (fun w : ℂ => (fun _ : ℂ => (ee q) (xx q)) w + w) := rfl
    rw [h1]
    exact analyticAt_const.add analyticAt_id
  have hcomp := AnalyticAt.comp (f := fun w : ℂ => (ee q) (xx q) + w) htr hs
  have hfun : ((fun u : ℂ => (ee p) ((ee q).symm u)) ∘ fun w : ℂ => (ee q) (xx q) + w) =
      (fun w : ℂ => (ee p) ((ee q).symm ((ee q) (xx q) + w))) := rfl
  rwa [hfun] at hcomp

lemma finite_crossSet_of_exists_ne
    (hee : ∀ m, ee m ∈ atlas ℂ X)
    (hdat : IsStarData rr xx ee ss)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {p q : ℕ} (hqp : (rr q ∩ rr p).Nonempty)
    (hne : ∃ θ ∈ Set.Icc 0 (2 * Real.pi),
      Complex.normSq ((ee p) ((ee q).symm (starPoint xx ee ss q θ)) - (ee p) (xx p))
        ≠ (ss p) ^ 2) :
    (crossSet xx ee ss p q).Finite := by
  have hμ : ∀ θ : ℝ, AnalyticAt ℂ
      (fun u : ℂ => (ee p) ((ee q).symm ((ee q) (xx q) + u)) - (ee p) (xx p))
      ((ss q : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    fun θ => (analyticAt_transition_shift hee hdat hstar hqp θ).sub analyticAt_const
  have h := finite_crossing_angles
    (μ := fun u : ℂ => (ee p) ((ee q).symm ((ee q) (xx q) + u)) - (ee p) (xx p))
    (ρ := ss q) (r := ss p) hμ hne
  simpa only [crossSet, starPoint] using h

lemma crossSet_all_of_infinite
    (hee : ∀ m, ee m ∈ atlas ℂ X)
    (hdat : IsStarData rr xx ee ss)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {p q : ℕ} (hqp : (rr q ∩ rr p).Nonempty)
    (hinf : ¬ (crossSet xx ee ss p q).Finite) :
    ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      Complex.normSq ((ee p) ((ee q).symm (starPoint xx ee ss q θ)) - (ee p) (xx p))
        = (ss p) ^ 2 := by
  intro θ hθ
  by_contra hc
  exact hinf (finite_crossSet_of_exists_ne hee hdat hstar hqp ⟨θ, hθ, hc⟩)

lemma sigma_subset_of_crossSet_all
    (hdat : IsStarData rr xx ee ss)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {p q : ℕ} (hqp : (rr q ∩ rr p).Nonempty)
    (hall : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      Complex.normSq ((ee p) ((ee q).symm (starPoint xx ee ss q θ)) - (ee p) (xx p))
        = (ss p) ^ 2) :
    sigma xx ee ss q ⊆ sigma xx ee ss p := by
  obtain ⟨hs, ht, hr⟩ := starData_of_inter hdat hqp
  obtain ⟨hs', -, -⟩ := starData_of_inter hdat (nonempty_inter_comm hqp)
  intro y hy
  rw [sigma_eq_image_Icc] at hy
  obtain ⟨θ, hθ, rfl⟩ := hy
  exact mem_sigma_of_normSq (p := p) hs'
    (hstar q p hqp (Or.inl (starPoint_symm_mem xx ee ss θ hs hr))).2 (hall θ hθ)

lemma sigma_eq_of_crossing
    (hdat : IsStarData rr xx ee ss)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {n : ℕ} (hne : rr n ≠ ∅)
    {a b : ℕ} (ha : (rr a ∩ rr n).Nonempty) (hb : (rr b ∩ rr n).Nonempty)
    {t s : ℝ} (heq : starCurve xx ee ss n a t = starCurve xx ee ss n b s) :
    (ee a).symm (starPoint xx ee ss a t) = (ee b).symm (starPoint xx ee ss b s) := by
  obtain ⟨hsn, -, -⟩ := starData_of_ne_empty hdat hne
  have hsn0 : (ss n : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have h1 : (ee n) ((ee a).symm (starPoint xx ee ss a t)) =
      (ee n) ((ee b).symm (starPoint xx ee ss b s)) := by
    have h := heq
    simp only [starCurve] at h
    field_simp at h
    exact add_right_cancel (by simpa only [sub_eq_add_neg] using h)
  exact (ee n).injOn (starCurve_hsrc xx ee ss hdat hstar ha t)
    (starCurve_hsrc xx ee ss hdat hstar hb s) h1

lemma crossSet_of_crossing
    (hdat : IsStarData rr xx ee ss)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {n : ℕ} (hne : rr n ≠ ∅)
    {a b : ℕ} (ha : (rr a ∩ rr n).Nonempty) (hb : (rr b ∩ rr n).Nonempty)
    {t s : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) (hs : s ∈ Set.Icc 0 (2 * Real.pi))
    (heq : starCurve xx ee ss n a t = starCurve xx ee ss n b s) :
    t ∈ crossSet xx ee ss b a := by
  have h2 := sigma_eq_of_crossing hdat hstar hne ha hb heq
  have h3 : (ee b) ((ee b).symm (starPoint xx ee ss b s)) = starPoint xx ee ss b s :=
    (ee b).right_inv (starPoint_mem_target_of_inter xx ee ss hdat hb s)
  have h4 : (ee b) ((ee a).symm (starPoint xx ee ss a t)) - (ee b) (xx b) =
      (ss b : ℂ) * Complex.exp (Complex.I * (s : ℂ)) := by
    rw [h2, h3]
    simp only [starPoint]
    ring
  have hsb : 0 < ss b := (starData_of_inter hdat hb).1
  refine ⟨ht, ?_⟩
  rw [h4, Complex.normSq_eq_norm_sq, norm_mul,
    show Complex.I * (s : ℂ) = (s : ℂ) * Complex.I by ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, norm_coe_real, abs_of_pos hsb]

/-- The crossing-parameter set of a curve is finite, unless two curves have the same image. -/
lemma crossing_params_finite
    (hee : ∀ m, ee m ∈ atlas ℂ X)
    (hdat : IsStarData rr xx ee ss)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {n : ℕ} (hne : rr n ≠ ∅)
    {a b : ℕ} (ha : (rr a ∩ rr n).Nonempty) (hb : (rr b ∩ rr n).Nonempty)
    (hneq : Set.range (starCurve xx ee ss n a) ≠ Set.range (starCurve xx ee ss n b)) :
    {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ ∃ s ∈ Set.Icc 0 (2 * Real.pi),
      starCurve xx ee ss n a t = starCurve xx ee ss n b s}.Finite := by
  classical
  by_cases hAB : (rr a ∩ rr b).Nonempty
  · by_contra hinf
    have hab' : (rr b ∩ rr a).Nonempty := nonempty_inter_comm hAB
    have hZb_inf : ¬ (crossSet xx ee ss b a).Finite := fun hf =>
      hinf (hf.subset fun t ht => by
        obtain ⟨s, hs, heq⟩ := ht.2
        exact crossSet_of_crossing hdat hstar hne ha hb ht.1 hs heq)
    have hall_b := crossSet_all_of_infinite (p := b) (q := a) hee hdat hstar hAB hZb_inf
    have hsub_ab : sigma xx ee ss a ⊆ sigma xx ee ss b :=
      sigma_subset_of_crossSet_all (p := b) (q := a) hdat hstar hAB hall_b
    -- the reverse inclusion: `crossSet a b` is infinite
    have hZa_inf : (crossSet xx ee ss a b).Infinite := by
      have hspec : ∀ t : ↥(Set.Ico 0 (2 * Real.pi)),
          ∃ s ∈ Set.Icc 0 (2 * Real.pi),
            (ee b).symm (starPoint xx ee ss b s) =
              (ee a).symm (starPoint xx ee ss a (t : ℝ)) := by
        intro t
        have hmem : (ee a).symm (starPoint xx ee ss a (t : ℝ)) ∈ sigma xx ee ss b :=
          hsub_ab ⟨t, rfl⟩
        rwa [sigma_eq_image_Icc] at hmem
      set ψ : ↥(Set.Ico 0 (2 * Real.pi)) → ℝ := fun t => (hspec t).choose with hψdef
      have hψ1 : ∀ t, ψ t ∈ Set.Icc 0 (2 * Real.pi) := fun t => (hspec t).choose_spec.1
      have hψ2 : ∀ t, (ee b).symm (starPoint xx ee ss b (ψ t)) =
          (ee a).symm (starPoint xx ee ss a (t : ℝ)) := fun t => (hspec t).choose_spec.2
      have hψinj : Function.Injective ψ := by
        intro t u htu
        have h1 : (ee a).symm (starPoint xx ee ss a (t : ℝ)) =
            (ee a).symm (starPoint xx ee ss a (u : ℝ)) := by
          rw [← hψ2 t, ← hψ2 u, htu]
        have h2 := sigma_injOn (m := a) (starData_of_inter hdat ha).1
          (starData_of_inter hdat ha).2.1 t.2 u.2 h1
        exact Subtype.ext h2
      have hZasub : Set.range ψ ⊆ crossSet xx ee ss a b := by
        rintro v ⟨t, rfl⟩
        have hmem : (ee b).symm (starPoint xx ee ss b (ψ t)) ∈ sigma xx ee ss a :=
          ⟨t, (hψ2 t).symm⟩
        exact ⟨hψ1 t, normSq_of_mem_sigma hdat ha hmem⟩
      haveI : Infinite ↥(Set.Ico 0 (2 * Real.pi)) := Set.Ico.infinite (by positivity)
      exact (Set.infinite_range_of_injective hψinj).mono hZasub
    have hall_a := crossSet_all_of_infinite (p := a) (q := b) hee hdat hstar hab'
      hZa_inf.not_finite
    have hsub_ba : sigma xx ee ss b ⊆ sigma xx ee ss a :=
      sigma_subset_of_crossSet_all (p := a) (q := b) hdat hstar hab' hall_a
    have hABeq : sigma xx ee ss a = sigma xx ee ss b := Set.Subset.antisymm hsub_ab hsub_ba
    exact hneq (by rw [range_starCurve_eq xx ee ss n a, range_starCurve_eq xx ee ss n b, hABeq])
  · have hempty : {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ ∃ s ∈ Set.Icc 0 (2 * Real.pi),
        starCurve xx ee ss n a t = starCurve xx ee ss n b s} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨ht, s, hs, heq⟩
      have h2 := sigma_eq_of_crossing hdat hstar hne ha hb heq
      have h1 : (ee a).symm (starPoint xx ee ss a t) ∈ rr a :=
        sigma_subset_rr hdat ha ⟨t, rfl⟩
      have h2' : (ee b).symm (starPoint xx ee ss b s) ∈ rr b :=
        sigma_subset_rr hdat hb ⟨s, rfl⟩
      exact hAB ⟨_, h1, h2 ▸ h2'⟩
    rw [hempty]
    exact Set.finite_empty

end Sigma

section Pullback

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}

lemma isClosed_of_starData (hdat : IsStarData rr xx ee ss) : ∀ n, IsClosed (rr n) := by
  intro n
  rcases hdat n with h0 | ⟨-, ht, hr⟩
  · rw [h0]
    exact isClosed_empty
  · rw [hr]
    exact ((isCompact_closedBall _ _).image_of_continuousOn
      (((ee n).continuousOn_symm).mono ht)).isClosed

lemma two_ss_ne_zero {n : ℕ} (hs : 0 < ss n) : ((2 * ss n : ℝ) : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  linarith

lemma two_ss_ne_zero' {n : ℕ} (hs : 0 < ss n) : (2 * (ss n : ℂ)) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero, false_or]
  linarith

lemma piece_subset_source (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅) :
    piece rr n ⊆ (ee n).source := by
  obtain ⟨hs, ht, hr⟩ := starData_of_ne_empty hdat hne
  refine (piece_subset rr (isClosed_of_starData hdat) n).trans ?_
  rw [hr, ← (ee n).symm_image_target_eq_source]
  exact Set.image_mono ht

/-- The affine normalisation `w ↦ (w - c)/(2ρ)` of the `n`-th chart. -/
noncomputable def normMap (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (n : ℕ) (w : ℂ) : ℂ :=
  (w - (ee n) (xx n)) / (2 * (ss n : ℂ))

/-- The inverse of `normMap`, composed with the chart: this pulls a tile of the plane back to `X`. -/
noncomputable def chartPull (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (n : ℕ) (u : ℂ) : X :=
  (ee n).symm ((ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u)

/-- The chart followed by the normalisation, on `X`. -/
noncomputable def planeProj (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (n : ℕ) (y : X) : ℂ :=
  normMap xx ee ss n ((ee n) y)

lemma normMap_inv_apply {n : ℕ} (h2ρ : ((2 * ss n : ℝ) : ℂ) ≠ 0) (w : ℂ) :
    (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * normMap xx ee ss n w = w := by
  have h1 : (2 * (ss n : ℂ)) = ((2 * ss n : ℝ) : ℂ) := by push_cast; ring
  rw [normMap, h1]
  field_simp
  ring

lemma normMap_apply {n : ℕ} (h2ρ : ((2 * ss n : ℝ) : ℂ) ≠ 0) (u : ℂ) :
    normMap xx ee ss n ((ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u) = u := by
  have h1 : (2 * (ss n : ℂ)) = ((2 * ss n : ℝ) : ℂ) := by push_cast; ring
  rw [normMap, h1]
  field_simp
  ring

lemma normMap_eq_affine_symm {n : ℕ} (h2ρ : ((2 * ss n : ℝ) : ℂ) ≠ 0) :
    normMap xx ee ss n =
      ⇑(affineHomeomorph (((2 * ss n : ℝ) : ℂ)) ((ee n) (xx n)) h2ρ).symm := by
  funext w
  show (w - (ee n) (xx n)) / (2 * (ss n : ℂ)) =
    (w - (ee n) (xx n)) / (((2 * ss n : ℝ) : ℂ))
  push_cast
  ring

lemma isOpenMap_normMap {n : ℕ} (h2ρ : ((2 * ss n : ℝ) : ℂ) ≠ 0) :
    IsOpenMap (normMap xx ee ss n) := by
  rw [normMap_eq_affine_symm (xx := xx) (ee := ee) (ss := ss) h2ρ]
  exact (affineHomeomorph (((2 * ss n : ℝ) : ℂ)) ((ee n) (xx n)) h2ρ).symm.isOpenMap

lemma continuous_normMap (n : ℕ) : Continuous (normMap xx ee ss n) := by
  rw [show normMap xx ee ss n = fun w : ℂ => ((2 * (ss n : ℂ))⁻¹) * (w - (ee n) (xx n)) by
    funext w
    rw [normMap, div_eq_inv_mul]]
  fun_prop

lemma starRegion_eq_normMap (n : ℕ) :
    starRegion rr xx ee ss n = normMap xx ee ss n '' ((ee n) '' piece rr n) := rfl

lemma chartPull_preimage_mem_target (hdat : IsStarData rr xx ee ss) {n : ℕ}
    (hne : rr n ≠ ∅) {u : ℂ} (hu : u ∈ starRegion rr xx ee ss n) :
    (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u ∈ (ee n).target := by
  obtain ⟨hs, -, -⟩ := starData_of_ne_empty hdat hne
  rw [starRegion_eq_normMap] at hu
  obtain ⟨w, ⟨m, hm, rfl⟩, hw⟩ := hu
  rw [← hw, normMap_inv_apply (n := n) (two_ss_ne_zero hs)]
  exact (ee n).map_source (piece_subset_source hdat hne hm)

lemma planeProj_chartPull (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅)
    {u : ℂ} (hu : u ∈ starRegion rr xx ee ss n) :
    planeProj xx ee ss n (chartPull xx ee ss n u) = u := by
  obtain ⟨hs, -, -⟩ := starData_of_ne_empty hdat hne
  have h1 : (ee n) (chartPull xx ee ss n u) =
      (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u :=
    (ee n).right_inv (chartPull_preimage_mem_target hdat hne hu)
  rw [planeProj, h1]
  exact normMap_apply (n := n) (two_ss_ne_zero hs) u

lemma chartPull_planeProj (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅)
    {y : X} (hy : y ∈ (ee n).source) :
    chartPull xx ee ss n (planeProj xx ee ss n y) = y := by
  obtain ⟨hs, -, -⟩ := starData_of_ne_empty hdat hne
  rw [planeProj, chartPull, normMap_inv_apply (n := n) (two_ss_ne_zero hs), (ee n).left_inv hy]

end Pullback

section Pullback2

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}

lemma chartPull_image_normMap {n : ℕ} (hs : 0 < ss n) (S : Set ℂ) :
    chartPull xx ee ss n '' (normMap xx ee ss n '' S) = (ee n).symm '' S := by
  have h1 : chartPull xx ee ss n '' (normMap xx ee ss n '' S) =
      (chartPull xx ee ss n ∘ normMap xx ee ss n) '' S :=
    Set.image_image _ _ _
  rw [h1]
  have h2 : (chartPull xx ee ss n ∘ normMap xx ee ss n) = fun w : ℂ => (ee n).symm w := by
    funext w
    simp only [Function.comp_apply, chartPull]
    rw [normMap_inv_apply (n := n) (two_ss_ne_zero hs)]
  rw [h2]

lemma symm_image_self {n : ℕ} {S : Set X} (hS : S ⊆ (ee n).source) :
    (ee n).symm '' ((ee n) '' S) = S := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨w, ⟨m, hm, rfl⟩, rfl⟩
    rw [(ee n).left_inv (hS hm)]
    exact hm
  · intro m hm
    exact ⟨(ee n) m, ⟨m, hm, rfl⟩, (ee n).left_inv (hS hm)⟩

lemma chartPull_image_starRegion (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅) :
    chartPull xx ee ss n '' starRegion rr xx ee ss n = piece rr n := by
  obtain ⟨hs, -, -⟩ := starData_of_ne_empty hdat hne
  rw [starRegion_eq_normMap, chartPull_image_normMap (n := n) hs,
    symm_image_self (piece_subset_source hdat hne)]

lemma starRegionClosure_eq_starRegion (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅) :
    starRegionClosure rr xx ee ss n = starRegion rr xx ee ss n :=
  Set.Subset.antisymm
    (closure_minimal interior_subset (isClosed_starRegion hdat (isClosed_of_starData hdat) hne))
    (starRegion_subset_closure_interior hdat (isClosed_of_starData hdat) hne)

lemma chartPull_image_starRegionClosure (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅) :
    chartPull xx ee ss n '' starRegionClosure rr xx ee ss n = piece rr n := by
  rw [starRegionClosure_eq_starRegion hdat hne, chartPull_image_starRegion hdat hne]

lemma continuousOn_chartPull (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅)
    {D : Set ℂ} (hDQ : D ⊆ starRegion rr xx ee ss n) :
    ContinuousOn (chartPull xx ee ss n) D := by
  have h1 : ContinuousOn (fun v : ℂ => (ee n).symm v)
      ((fun u : ℂ => (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u) '' D) :=
    ((ee n).continuousOn_symm).mono (by
      rintro v ⟨u, hu, rfl⟩
      exact chartPull_preimage_mem_target hdat hne (hDQ hu))
  have h2 : Continuous (fun u : ℂ => (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u) := by
    fun_prop
  have h3 := h1.image_comp_continuous h2
  rwa [show ((fun v : ℂ => (ee n).symm v) ∘ fun u : ℂ =>
      (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u) = chartPull xx ee ss n from rfl] at h3

lemma isClosed_chartPull_image (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅)
    {D : Set ℂ} (hDcl : IsClosed D) (hDQ : D ⊆ starRegionClosure rr xx ee ss n) :
    IsClosed (chartPull xx ee ss n '' D) := by
  have hQ : D ⊆ starRegion rr xx ee ss n := by
    rw [starRegionClosure_eq_starRegion hdat hne] at hDQ
    exact hDQ
  have hDb : D ⊆ Metric.closedBall 0 (1 / 2) :=
    hDQ.trans (starRegionClosure_subset hdat (isClosed_of_starData hdat) hne)
  have hcomp : IsCompact D := IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) (1 / 2)) hDcl hDb
  exact (hcomp.image_of_continuousOn (continuousOn_chartPull hdat hne hQ)).isClosed

lemma chartPull_image_homeomorph (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅)
    {D : Set ℂ} (hDQ : D ⊆ starRegionClosure rr xx ee ss n) :
    Nonempty ((D : Set ℂ) ≃ₜ (chartPull xx ee ss n '' D : Set X)) := by
  have hQ : D ⊆ starRegion rr xx ee ss n := by
    rw [starRegionClosure_eq_starRegion hdat hne] at hDQ
    exact hDQ
  have hDf_sub : chartPull xx ee ss n '' D ⊆ piece rr n := by
    rw [← chartPull_image_starRegionClosure hdat hne]
    exact Set.image_mono hDQ
  have hsrc : chartPull xx ee ss n '' D ⊆ (ee n).source :=
    hDf_sub.trans (piece_subset_source hdat hne)
  refine ⟨{ toFun := fun u => ⟨chartPull xx ee ss n u.1, ⟨u.1, u.2, rfl⟩⟩
          , invFun := fun y => ⟨planeProj xx ee ss n y.1, ?_⟩
          , left_inv := ?_
          , right_inv := ?_
          , continuous_toFun := ?_
          , continuous_invFun := ?_ }⟩
  · obtain ⟨u, hu, hyu⟩ := y.2
    rw [← hyu, planeProj_chartPull hdat hne (hQ hu)]
    exact hu
  · intro u
    exact Subtype.ext (planeProj_chartPull hdat hne (hQ u.2))
  · intro y
    obtain ⟨u, hu, hyu⟩ := y.2
    refine Subtype.ext ?_
    show chartPull xx ee ss n (planeProj xx ee ss n ↑y) = ↑y
    rw [← hyu]
    exact chartPull_planeProj hdat hne (hsrc ⟨u, hu, rfl⟩)
  · have hcont : ContinuousOn (chartPull xx ee ss n) D := continuousOn_chartPull hdat hne hQ
    exact (hcont.comp_continuous continuous_subtype_val (fun u => u.2)).subtype_mk
      (fun u => ⟨u.1, u.2, rfl⟩)
  · have hcont : ContinuousOn (planeProj xx ee ss n) (chartPull xx ee ss n '' D) :=
      (continuous_normMap n).comp_continuousOn ((ee n).continuousOn.mono hsrc)
    have hcont2 : Continuous (fun y : ↥(chartPull xx ee ss n '' D) => planeProj xx ee ss n y.1) :=
      hcont.comp_continuous continuous_subtype_val (fun y => y.2)
    exact hcont2.subtype_mk (fun y => by
      obtain ⟨u, hu, hyu⟩ := y.2
      rw [← hyu, planeProj_chartPull hdat hne (hQ hu)]
      exact hu)

lemma interior_chartPull_image_subset (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅)
    {D : Set ℂ} (hDQ : D ⊆ starRegionClosure rr xx ee ss n) :
    interior (chartPull xx ee ss n '' D) ⊆ planeProj xx ee ss n ⁻¹' interior D := by
  obtain ⟨hs, -, -⟩ := starData_of_ne_empty hdat hne
  have hQ : D ⊆ starRegion rr xx ee ss n := by
    rw [starRegionClosure_eq_starRegion hdat hne] at hDQ
    exact hDQ
  have hDf_sub : chartPull xx ee ss n '' D ⊆ piece rr n := by
    rw [← chartPull_image_starRegionClosure hdat hne]
    exact Set.image_mono hDQ
  intro x hx
  obtain ⟨W, hWsub, hWopen, hxW⟩ := _root_.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  have hWpiece : W ⊆ piece rr n := hWsub.trans (interior_subset.trans hDf_sub)
  have hWsrc : W ⊆ (ee n).source := hWpiece.trans (piece_subset_source hdat hne)
  refine interior_maximal (t := planeProj xx ee ss n '' W) ?_ ?_ ⟨x, hxW, rfl⟩
  · rintro v ⟨y, hyW, rfl⟩
    obtain ⟨u, hu, hyu⟩ := interior_subset (hWsub hyW)
    rw [← hyu, planeProj_chartPull hdat hne (hQ hu)]
    exact hu
  · have h1 : planeProj xx ee ss n '' W = normMap xx ee ss n '' ((ee n) '' W) := by
      change (normMap xx ee ss n ∘ fun y : X => (ee n) y) '' W =
        normMap xx ee ss n '' ((ee n) '' W)
      exact (Set.image_image (normMap xx ee ss n) (fun y : X => (ee n) y) W).symm
    rw [h1]
    exact isOpenMap_normMap (two_ss_ne_zero hs) _ ((ee n).isOpen_image_of_subset_source hWopen hWsrc)

end Pullback2

section PieceTiling

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}

/-- The finite family of boundary curves of a piece, re-indexed by `mOf`. -/
noncomputable def curveFamily (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (n : ℕ) {K : ℕ} (mOf : Fin K → ℕ) : Fin K → ℝ → ℂ :=
  fun k => starCurve xx ee ss n (mOf k)

lemma curveFamily_apply (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (n : ℕ) {K : ℕ} (mOf : Fin K → ℕ) (k : Fin K) :
    curveFamily xx ee ss n mOf k = starCurve xx ee ss n (mOf k) := rfl

lemma curveFamily_periodic (xx : ℕ → X) (ee : ℕ → OpenPartialHomeomorph X ℂ) (ss : ℕ → ℝ)
    (n : ℕ) {K : ℕ} (mOf : Fin K → ℕ) (k : Fin K) :
    Function.Periodic (curveFamily xx ee ss n mOf k) (2 * Real.pi) :=
  fun t => by simp only [curveFamily, starCurve_add_two_pi]

lemma frontier_rr_subset_sigma (hdat : IsStarData rr xx ee ss) {n m : ℕ}
    (hmn : (rr m ∩ rr n).Nonempty) : frontier (rr m) ⊆ sigma xx ee ss m := by
  obtain ⟨hs, ht, hr⟩ := starData_of_inter hdat hmn
  have hsne : (ss m : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hclm : IsClosed (rr m) := isClosed_of_starData hdat m
  intro p hp
  have hpS : p ∈ rr m := by
    rw [← IsClosed.closure_eq hclm]
    exact hp.1
  rw [hr] at hpS
  obtain ⟨w, hw, hpw⟩ := hpS
  have hnorm : ‖w - (ee m) (xx m)‖ = ss m := by
    by_contra hne'
    have hlt : ‖w - (ee m) (xx m)‖ < ss m := by
      have hle : ‖w - (ee m) (xx m)‖ ≤ ss m := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hw
      exact lt_of_le_of_ne hle hne'
    have hwb : w ∈ Metric.ball ((ee m) (xx m)) (ss m) := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hlt
    have hint : (ee m).symm w ∈ interior (rr m) := by
      rw [hr]
      exact interior_maximal (Set.image_mono Metric.ball_subset_closedBall)
        ((ee m).isOpen_image_symm_of_subset_target isOpen_ball
          (Metric.ball_subset_closedBall.trans ht)) ⟨w, hwb, rfl⟩
    rw [hpw] at hint
    exact hp.2 hint
  obtain ⟨t, ht'⟩ := exists_exp_I_of_norm_eq_one (z := (w - (ee m) (xx m)) / (ss m : ℂ)) (by
    rw [norm_div, norm_coe_real, abs_of_pos hs, hnorm, div_self (ne_of_gt hs)])
  refine ⟨t, ?_⟩
  have hsp : starPoint xx ee ss m t = w := by
    simp only [starPoint]
    rw [ht']
    field_simp
    ring
  show (ee m).symm (starPoint xx ee ss m t) = p
  rw [hsp, hpw]

lemma normMap_image_interior_subset (hdat : IsStarData rr xx ee ss) {n : ℕ} (hne : rr n ≠ ∅) :
    normMap xx ee ss n '' ((ee n) '' interior (piece rr n)) ⊆
      interior (starRegion rr xx ee ss n) := by
  obtain ⟨hs, ht, hr⟩ := starData_of_ne_empty hdat hne
  have hsrc : piece rr n ⊆ (ee n).source := piece_subset_source hdat hne
  have hOpen1 : IsOpen ((ee n) '' interior (piece rr n)) :=
    (ee n).isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hsrc)
  have hfeq : normMap xx ee ss n '' ((ee n) '' interior (piece rr n)) =
      (fun u : ℂ => (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * u) ⁻¹'
        ((ee n) '' interior (piece rr n)) := by
    ext w
    constructor
    · rintro ⟨t, ht', rfl⟩
      show (ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * normMap xx ee ss n t ∈
        (ee n) '' interior (piece rr n)
      rw [normMap_inv_apply (two_ss_ne_zero hs)]
      exact ht'
    · intro hw
      exact ⟨(ee n) (xx n) + ((2 * ss n : ℝ) : ℂ) * w, hw,
        normMap_apply (two_ss_ne_zero hs) w⟩
  have hOpen2 : IsOpen (normMap xx ee ss n '' ((ee n) '' interior (piece rr n))) := by
    rw [hfeq]
    exact hOpen1.preimage (by fun_prop)
  exact interior_maximal (t := normMap xx ee ss n '' ((ee n) '' interior (piece rr n))) (by
    rintro w ⟨y, ⟨v, hv, hy⟩, hw⟩
    exact ⟨(ee n) v, ⟨v, interior_subset hv, rfl⟩, (congrArg (normMap xx ee ss n) hy).trans hw⟩) hOpen2

lemma frontier_starRegion_subset_curves
    (hee : ∀ m, ee m ∈ atlas ℂ X) (hdat : IsStarData rr xx ee ss) (hlf : LocallyFinite rr)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {n : ℕ} (hne : rr n ≠ ∅) {K : ℕ} (mOf : Fin K → ℕ)
    (hmOf_mem : ∀ k, mOf k ∈ neighbourFinset hlf (isCompact_of_starData hdat n))
    (hmOf_cov : ∀ m ∈ neighbourFinset hlf (isCompact_of_starData hdat n), ∃ k,
      Set.range (starCurve xx ee ss n m) = Set.range (starCurve xx ee ss n (mOf k))) :
    frontier (starRegionClosure rr xx ee ss n) ⊆
      ⋃ k : Fin K, curveFamily xx ee ss n mOf k '' Set.Icc 0 (2 * Real.pi) := by
  classical
  have hcl := isClosed_of_starData hdat
  have hcomp := isCompact_of_starData hdat n
  intro p hp
  have hp' : p ∈ frontier (starRegion rr xx ee ss n) :=
    frontier_starRegionClosure_subset hdat hcl hne hp
  have hpQ : p ∈ starRegion rr xx ee ss n := by
    rw [← IsClosed.closure_eq (isClosed_starRegion hdat hcl hne)]
    exact hp'.1
  rw [starRegion_eq_normMap] at hpQ
  obtain ⟨w, ⟨m, hm, rfl⟩, hw⟩ := hpQ
  have hmfront : m ∈ frontier (piece rr n) := by
    refine ⟨subset_closure hm, ?_⟩
    intro hmi
    exact hp'.2 (by
      rw [← hw]
      exact normMap_image_interior_subset hdat hne ⟨(ee n) m, ⟨m, hmi, rfl⟩, rfl⟩)
  have key : ∀ m' : ℕ, (rr m' ∩ rr n).Nonempty → m ∈ frontier (rr m') →
      ∃ k : Fin K, p ∈ curveFamily xx ee ss n mOf k '' Set.Icc 0 (2 * Real.pi) := by
    intro m' hm'J hm'f
    have hmp : m ∈ sigma xx ee ss m' := frontier_rr_subset_sigma hdat hm'J hm'f
    rw [sigma_eq_image_Icc] at hmp
    obtain ⟨t, htIcc, hmt⟩ := hmp
    have hmt' : (ee m').symm (starPoint xx ee ss m' t) = m := hmt
    have hmemJ : m' ∈ neighbourFinset hlf hcomp :=
      (mem_neighbourFinset hlf hcomp).mpr hm'J
    obtain ⟨k, hk⟩ := hmOf_cov m' hmemJ
    refine ⟨k, ?_⟩
    have hval : starCurve xx ee ss n m' t = p := by
      rw [show starCurve xx ee ss n m' t =
        normMap xx ee ss n ((ee n) ((ee m').symm (starPoint xx ee ss m' t))) from rfl, hmt', hw]
    have hmem2 : p ∈ Set.range (starCurve xx ee ss n (mOf k)) := by
      rw [← hk]
      exact ⟨t, hval⟩
    obtain ⟨u, hu⟩ := hmem2
    obtain ⟨u', hu', hγ⟩ := exists_shift_Icc_of_periodic
      (curveFamily_periodic xx ee ss n mOf k) u
    exact ⟨u', hu', by
      show curveFamily xx ee ss n mOf k u' = p
      rw [hγ]
      show starCurve xx ee ss n (mOf k) u = p
      exact hu⟩
  rcases frontier_piece_subset rr hcl n hmfront with h1 | h1
  · have hm_rrn : m ∈ rr n := by
      rw [← IsClosed.closure_eq (hcl n)]
      exact h1.1
    exact mem_iUnion.mpr (key n ⟨m, hm_rrn, hm_rrn⟩ h1)
  · rcases mem_iUnion₂.mp h1 with ⟨m', hm'n, hm'f⟩
    have hm_rrm : m ∈ rr m' := by
      rw [← IsClosed.closure_eq (hcl m')]
      exact hm'f.1
    have hm_rrn : m ∈ rr n := piece_subset rr hcl n hm
    exact mem_iUnion.mpr (key m' ⟨m, hm_rrm, hm_rrn⟩ hm'f)

end PieceTiling

section PerPiece

variable {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

variable {rr : ℕ → Set X} {xx : ℕ → X} {ee : ℕ → OpenPartialHomeomorph X ℂ} {ss : ℕ → ℝ}

lemma eq_endpoints_of_interval_eq {K : ℕ} {n : ℕ} {mOf : Fin K → ℕ} {k : Fin K} {t s : ℝ}
    (ht : t ∈ Set.Icc 0 (2 * Real.pi)) (hs : s ∈ Set.Icc 0 (2 * Real.pi))
    (hinj : Set.InjOn (starCurve xx ee ss n (mOf k)) (Set.Ico 0 (2 * Real.pi)))
    (heq : starCurve xx ee ss n (mOf k) t = starCurve xx ee ss n (mOf k) s) :
    t = s ∨ (t = 0 ∧ s = 2 * Real.pi) ∨ (t = 2 * Real.pi ∧ s = 0) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hper : starCurve xx ee ss n (mOf k) (2 * Real.pi) = starCurve xx ee ss n (mOf k) 0 := by
    simpa using starCurve_add_two_pi xx ee ss n (mOf k) 0
  rcases eq_or_ne t (2 * Real.pi) with ht2 | ht2
  · rcases eq_or_ne s (2 * Real.pi) with hs2 | hs2
    · exact Or.inl (ht2.trans hs2.symm)
    · refine Or.inr (Or.inr ⟨ht2, ?_⟩)
      have hsIco : s ∈ Set.Ico 0 (2 * Real.pi) := ⟨hs.1, lt_of_le_of_ne hs.2 hs2⟩
      have h0 : starCurve xx ee ss n (mOf k) 0 = starCurve xx ee ss n (mOf k) s := by
        rw [← hper, ← ht2]
        exact heq
      exact (hinj ⟨le_refl _, h2pi⟩ hsIco h0).symm
  · rcases eq_or_ne s (2 * Real.pi) with hs2 | hs2
    · refine Or.inr (Or.inl ⟨?_, hs2⟩)
      have htIco : t ∈ Set.Ico 0 (2 * Real.pi) := ⟨ht.1, lt_of_le_of_ne ht.2 ht2⟩
      have h0 : starCurve xx ee ss n (mOf k) 0 = starCurve xx ee ss n (mOf k) t := by
        rw [← hper, ← hs2]
        exact heq.symm
      exact (hinj ⟨le_refl _, h2pi⟩ htIco h0).symm
    · exact Or.inl (hinj ⟨ht.1, lt_of_le_of_ne ht.2 ht2⟩
        ⟨hs.1, lt_of_le_of_ne hs.2 hs2⟩ heq)

set_option maxHeartbeats 2000000 in
lemma exists_piece_tiling
    (hee : ∀ m, ee m ∈ atlas ℂ X) (hdat : IsStarData rr xx ee ss) (hlf : LocallyFinite rr)
    (hstar : ∀ a b, (rr a ∩ rr b).Nonempty →
      rr a ∪ rr b ⊆ (ee a).source ∩ (ee b).source)
    {n : ℕ} (hne : rr n ≠ ∅) :
    ∃ (N : ℕ) (Df : Fin N → Set X),
      (∀ j, IsClosed (Df j)) ∧
      (∀ j, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (Df j : Set X))) ∧
      ((⋃ j, Df j) = piece rr n) ∧
      (∀ j j', j ≠ j' → interior (Df j) ∩ interior (Df j') = ∅) := by
  classical
  obtain ⟨hsn, htn, hrn⟩ := starData_of_ne_empty hdat hne
  have hcl : ∀ n, IsClosed (rr n) := isClosed_of_starData hdat
  have hcomp : IsCompact (rr n) := isCompact_of_starData hdat n
  obtain ⟨K, mOf, hmOf_mem, hmOf_inj, hmOf_cov⟩ := exists_dedup_curves xx ee ss hlf hcomp
  have hmn : ∀ k : Fin K, (rr (mOf k) ∩ rr n).Nonempty :=
    fun k => (mem_neighbourFinset hlf hcomp).mp (hmOf_mem k)
  -- the finite set of cut values
  have hZ1 : ({-(1/2), (1/2)} : Set ℝ).Finite := (Set.finite_singleton (1/2)).insert (-(1/2))
  have hZ2 : (⋃ k : Fin K, {x : ℝ | ∃ t : ℝ,
      deriv (fun s => (curveFamily xx ee ss n mOf k s).re) t = 0 ∧
        (curveFamily xx ee ss n mOf k t).re = x}).Finite :=
    Set.finite_iUnion fun k => finite_critical_values_curve hee hdat hstar (hmn k)
  have hZ3 : (Set.range (fun k : Fin K => (curveFamily xx ee ss n mOf k 0).re) ∪
      Set.range (fun k : Fin K => (curveFamily xx ee ss n mOf k (2 * Real.pi)).re)).Finite :=
    (Set.finite_range _).union (Set.finite_range _)
  have hZ4 : (⋃ p ∈ ((Finset.univ.filter (fun p : Fin K × Fin K => p.1 ≠ p.2) :
        Finset (Fin K × Fin K)) : Set (Fin K × Fin K)),
      (fun t : ℝ => (curveFamily xx ee ss n mOf p.1 t).re) ''
        {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ ∃ s ∈ Set.Icc 0 (2 * Real.pi),
          curveFamily xx ee ss n mOf p.1 t = curveFamily xx ee ss n mOf p.2 s}).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hneq : Set.range (starCurve xx ee ss n (mOf p.1)) ≠
        Set.range (starCurve xx ee ss n (mOf p.2)) := fun h => hpne (hmOf_inj h)
    exact (crossing_params_finite hee hdat hstar hne (hmn p.1) (hmn p.2) hneq).image _
  let hcut : Finset ℝ := hZ1.toFinset ∪ hZ2.toFinset ∪ hZ3.toFinset ∪ hZ4.toFinset
  have hcm : -(1/2) ∈ hcut :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      ((Set.Finite.mem_toFinset hZ1).mpr (by simp))))
  have hcp : (1/2) ∈ hcut :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      ((Set.Finite.mem_toFinset hZ1).mpr (by simp))))
  have hZ3L : ∀ k : Fin K, (curveFamily xx ee ss n mOf k 0).re ∈ hcut := fun k =>
    Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset hZ3).mpr
      (Set.mem_union_left _ (Set.mem_range.mpr ⟨k, rfl⟩))))
  have hZ3R : ∀ k : Fin K, (curveFamily xx ee ss n mOf k (2 * Real.pi)).re ∈ hcut := fun k =>
    Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset hZ3).mpr
      (Set.mem_union_right _ (Set.mem_range.mpr ⟨k, rfl⟩))))
  -- the ten hypotheses of the region tiling lemma
  have hab : ∀ k : Fin K, (fun _ : Fin K => (0 : ℝ)) k < (fun _ : Fin K => 2 * Real.pi) k :=
    fun k => by positivity
  have hγc : ∀ k : Fin K, Continuous (curveFamily xx ee ss n mOf k) := fun k => by
    show Continuous (starCurve xx ee ss n (mOf k))
    exact continuous_starCurve xx ee ss n (mOf k) (starData_of_inter hdat (hmn k)).1
      (starData_of_inter hdat (hmn k)).2.1 (starCurve_hsrc xx ee ss hdat hstar (hmn k))
  have hinj : ∀ k : Fin K,
      Set.InjOn (curveFamily xx ee ss n mOf k) (Set.Ico 0 (2 * Real.pi)) := fun k => by
    show Set.InjOn (starCurve xx ee ss n (mOf k)) (Set.Ico 0 (2 * Real.pi))
    exact injOn_starCurve xx ee ss n (mOf k) (starData_of_inter hdat (hmn k)).1 hsn
      (starData_of_inter hdat (hmn k)).2.1 (starCurve_hsrc xx ee ss hdat hstar (hmn k))
  have han : ∀ k : Fin K, ∀ t : ℝ, t ∈ Set.Ioo 0 (2 * Real.pi) →
      AnalyticAt ℝ (fun s : ℝ => (curveFamily xx ee ss n mOf k s).re) t :=
    fun k t _ => analyticAt_starCurve_re_of_inter hee hdat hstar (hmn k) t
  have hseam : ∀ k : Fin K,
      ((curveFamily xx ee ss n mOf k ((fun _ : Fin K => (0:ℝ)) k)).re ∈ hcut ∨
        (curveFamily xx ee ss n mOf k ((fun _ : Fin K => (0:ℝ)) k)).re ∉
          Set.Icc (-(1/2)) (1/2)) ∧
      ((curveFamily xx ee ss n mOf k ((fun _ : Fin K => 2 * Real.pi) k)).re ∈ hcut ∨
        (curveFamily xx ee ss n mOf k ((fun _ : Fin K => 2 * Real.pi) k)).re ∉
          Set.Icc (-(1/2)) (1/2)) :=
    fun k => ⟨Or.inl (hZ3L k), Or.inl (hZ3R k)⟩
  have hcrit : ∀ k : Fin K, ∀ t : ℝ,
      deriv (fun s : ℝ => (curveFamily xx ee ss n mOf k s).re) t = 0 →
      (curveFamily xx ee ss n mOf k t).re ∈ hcut := by
    intro k t ht
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      ((Set.Finite.mem_toFinset hZ2).mpr ?_)))
    exact Set.mem_iUnion.mpr ⟨k, t, ht, rfl⟩
  have hconst : ∀ k : Fin K, ∀ v : ℝ,
      (∀ t ∈ Set.Icc ((fun _ : Fin K => (0:ℝ)) k) ((fun _ : Fin K => 2 * Real.pi) k),
        (curveFamily xx ee ss n mOf k t).re = v) → v ∈ hcut := by
    intro k v hv
    have hπ : (0:ℝ) < Real.pi / 2 ∧ Real.pi / 2 < 2 * Real.pi :=
      ⟨by positivity, by nlinarith [Real.pi_pos]⟩
    have hge : (fun s : ℝ => (curveFamily xx ee ss n mOf k s).re) =ᶠ[𝓝 (Real.pi / 2)]
        (fun _ => v) :=
      Filter.mem_of_superset (Ioo_mem_nhds hπ.1 hπ.2)
        (fun x hx => hv x ⟨hx.1.le, hx.2.le⟩)
    have hd : deriv (fun s : ℝ => (curveFamily xx ee ss n mOf k s).re) (Real.pi / 2) = 0 := by
      rw [Filter.EventuallyEq.deriv_eq hge, deriv_const]
    have hval : (curveFamily xx ee ss n mOf k (Real.pi / 2)).re = v :=
      hv (Real.pi / 2) ⟨hπ.1.le, hπ.2.le⟩
    rw [← hval]
    exact hcrit k (Real.pi / 2) hd
  have hcross : ∀ k l : Fin K, ∀ t s : ℝ,
      t ∈ Set.Icc ((fun _ : Fin K => (0:ℝ)) k) ((fun _ : Fin K => 2 * Real.pi) k) →
      s ∈ Set.Icc ((fun _ : Fin K => (0:ℝ)) l) ((fun _ : Fin K => 2 * Real.pi) l) →
      curveFamily xx ee ss n mOf k t = curveFamily xx ee ss n mOf l s →
      ¬(k = l ∧ t = s) → (curveFamily xx ee ss n mOf k t).re ∈ hcut := by
    intro k l t s ht hs heq hne'
    by_cases hkl : k = l
    · subst hkl
      have hinjk := injOn_starCurve xx ee ss n (mOf k) (starData_of_inter hdat (hmn k)).1 hsn
        (starData_of_inter hdat (hmn k)).2.1 (starCurve_hsrc xx ee ss hdat hstar (hmn k))
      have hpair := eq_endpoints_of_interval_eq (mOf := mOf) ht hs hinjk heq
      rcases hpair with hts | ⟨ht0, hs2⟩ | ⟨ht2, hs0⟩
      · exact absurd ⟨rfl, hts⟩ hne'
      · rw [show (curveFamily xx ee ss n mOf k t).re =
          (curveFamily xx ee ss n mOf k 0).re by rw [ht0]]
        exact hZ3L k
      · rw [show (curveFamily xx ee ss n mOf k t).re =
          (curveFamily xx ee ss n mOf k (2 * Real.pi)).re by rw [ht2]]
        exact hZ3R k
    · refine Finset.mem_union_right _ ((Set.Finite.mem_toFinset hZ4).mpr ?_)
      have hmem : (k, l) ∈ (Finset.univ.filter (fun p : Fin K × Fin K => p.1 ≠ p.2) :
          Finset (Fin K × Fin K)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl⟩
      exact mem_biUnion hmem ⟨t, ⟨ht, s, hs, heq⟩, rfl⟩
  have hfib : ∀ k : Fin K, ∀ v : ℝ, v ∈ Set.Ioo (-(1/2)) (1/2) →
      (∀ t ∈ Set.Icc ((fun _ : Fin K => (0:ℝ)) k) ((fun _ : Fin K => 2 * Real.pi) k),
        (curveFamily xx ee ss n mOf k t).re = v) ∨
      {t : ℝ | t ∈ Set.Icc ((fun _ : Fin K => (0:ℝ)) k)
        ((fun _ : Fin K => 2 * Real.pi) k) ∧ (curveFamily xx ee ss n mOf k t).re = v}.Finite := by
    intro k v _
    by_cases hne'' : ∃ t ∈ Set.Icc 0 (2 * Real.pi), (curveFamily xx ee ss n mOf k t).re ≠ v
    · right
      exact finite_preimage_of_analytic (f := fun s : ℝ => (curveFamily xx ee ss n mOf k s).re)
        (a := 0) (b := 2 * Real.pi)
        (fun t _ => analyticAt_starCurve_re_of_inter hee hdat hstar (hmn k) t) hne''
    · push Not at hne''
      exact Or.inl hne''
  -- the region and its four properties
  have hQcl : IsClosed (starRegionClosure rr xx ee ss n) := isClosed_starRegionClosure
  have hQci : closure (interior (starRegionClosure rr xx ee ss n)) =
      starRegionClosure rr xx ee ss n := closure_interior_starRegionClosure hdat hcl hne
  have hQb : starRegionClosure rr xx ee ss n ⊆ Metric.closedBall 0 (1/2) :=
    starRegionClosure_subset hdat hcl hne
  have hQf : frontier (starRegionClosure rr xx ee ss n) ⊆
      ⋃ k : Fin K, curveFamily xx ee ss n mOf k '' Set.Icc ((fun _ : Fin K => (0:ℝ)) k)
        ((fun _ : Fin K => 2 * Real.pi) k) :=
    frontier_starRegion_subset_curves hee hdat hlf hstar hne mOf hmOf_mem hmOf_cov
  obtain ⟨N, D, hDcov, hDcl, hDdisk, hDdisj⟩ :=
    exists_disk_tiling_of_region (curveFamily xx ee ss n mOf) (fun _ => 0) (fun _ => 2 * Real.pi)
      hab hγc hinj han hcut hcm hcp hseam hcrit hconst hcross hfib hQcl hQci hQb hQf
  have hDQ : ∀ j : Fin N, D j ⊆ starRegionClosure rr xx ee ss n := fun j => by
    rw [← hDcov]
    exact Set.subset_iUnion _ j
  refine ⟨N, fun j => chartPull xx ee ss n '' D j, ?_, ?_, ?_, ?_⟩
  · intro j
    exact isClosed_chartPull_image hdat hne (hDcl j) (hDQ j)
  · intro j
    obtain ⟨e1⟩ := hDdisk j
    obtain ⟨e2⟩ := chartPull_image_homeomorph hdat hne (hDQ j)
    exact ⟨e1.trans e2⟩
  · have h1 : (⋃ j, chartPull xx ee ss n '' D j) = chartPull xx ee ss n '' (⋃ j, D j) :=
      Set.image_iUnion.symm
    rw [h1, hDcov, chartPull_image_starRegionClosure hdat hne]
  · rintro j j' hjj
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, hx1, hx2⟩
    have h1 : planeProj xx ee ss n x ∈ interior (D j) :=
      interior_chartPull_image_subset hdat hne (hDQ j) hx1
    have h2 : planeProj xx ee ss n x ∈ interior (D j') :=
      interior_chartPull_image_subset hdat hne (hDQ j') hx2
    have h3 : planeProj xx ee ss n x ∈ interior (D j) ∩ interior (D j') := ⟨h1, h2⟩
    rw [hDdisj j j' hjj] at h3
    exact h3

end PerPiece
/-- **Existence of a locally finite tiling of a Riemann surface by closed disks.**

(The main theorem.  Proof in progress.) -/
theorem exists_locallyFinite_disk_tiling {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] : ∃ (ι : Type*) (D : ι → Set X), LocallyFinite D ∧ (⋃ i, D i = Set.univ) ∧ (∀ i, IsClosed (D i)) ∧ (∀ i, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (D i : Set X))) ∧ (∀ i j, i ≠ j → interior (D i) ∩ interior (D j) = ∅) := by
  haveI : Nonempty X := ConnectedSpace.toNonempty
  obtain ⟨xx, ee, ss, rr, hee, hdat, hcov, hlf, hcl, hstar⟩ := exists_star_cover (X := X)
  have key : ∀ n : ℕ, ∃ (N : ℕ) (Df : Fin N → Set X),
      (∀ j, IsClosed (Df j)) ∧
      (∀ j, Nonempty (Metric.closedBall (0:ℂ) 1 ≃ₜ (Df j : Set X))) ∧
      ((⋃ j, Df j) = piece rr n) ∧
      (∀ j j', j ≠ j' → interior (Df j) ∩ interior (Df j') = ∅) := by
    intro n
    by_cases hne : rr n = ∅
    · refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_⟩
      · intro j; exact j.elim0
      · intro j; exact j.elim0
      · have hpiece : piece rr n = ∅ := by
          simp only [piece, hne, Set.empty_diff, closure_empty]
        rw [show (⋃ j : Fin 0, (Fin.elim0 j : Set X)) = ∅ from by ext x; simp, hpiece]
      · intro j; exact j.elim0
    · exact exists_piece_tiling hee hdat hlf hstar hne
  choose N Df hDcl hDdisk hDcov hDdisj using key
  exact exists_locallyFinite_disk_tiling_of_piece_tilings rr hcl hlf hcov N Df
    hDcl hDdisk hDcov hDdisj

end Commons.Topology.Surface