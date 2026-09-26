import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective
import Submission.Work.Smooth.SphereJordan.RiemannSphere
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.familyDataOfTwoDiscs

/-!
# API for disc maps used by `disc_spans_schoenflies`

Elementary lemmas about the image of the open model disc under a continuous map `𝔻 → ℂ`, and the
uniqueness of a spanning disc whose open image is nested in that of another one.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section


/-! ## Elementary API for a disc map -/

/-- The image of the *open* model disc under a continuous map `𝔻 → ℂ`. -/
def openImage (f : C(Disc, ℂ)) : Set ℂ := f '' {z : Disc | ‖(z : ℂ)‖ < 1}

theorem mem_openImage {f : C(Disc, ℂ)} {x : ℂ} :
    x ∈ openImage f ↔ ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ f z = x := Iff.rfl

theorem openImage_preconnected (f : C(Disc, ℂ)) : IsPreconnected (openImage f) := by
  have h : IsPreconnected (TwoDiscs.openUnitDisc : Set Disc) :=
    TwoDiscs.isPreconnected_openUnitDisc
  have h2 := h.image f f.continuous.continuousOn
  simpa [openImage, TwoDiscs.openUnitDisc] using h2

/-- The range of a disc map with boundary curve `c` splits as the image of the open disc and the
trace of `c`. -/
theorem range_eq_openImage_union {f : C(Disc, ℂ)} {c : ℝ → ℂ}
    (hb : ∀ θ : ℝ, f (circlePoint θ) = c θ) :
    Set.range f = openImage f ∪ Set.range c := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    have hzle : ‖(z : ℂ)‖ ≤ 1 := by
      have := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
    rcases lt_or_eq_of_le hzle with hlt | heq
    · exact Or.inl ⟨z, hlt, rfl⟩
    · obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z heq
      exact Or.inr ⟨θ, by rw [← hθ, hb θ]⟩
  · rintro _ (⟨z, _, rfl⟩ | ⟨θ, rfl⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨circlePoint θ, hb θ⟩

/-- The open disc of a disc map with boundary curve `c` misses the trace of `c`. -/
theorem openImage_subset_compl_range {f : C(Disc, ℂ)} (hinj : Function.Injective f)
    {c : ℝ → ℂ} (hb : ∀ θ : ℝ, f (circlePoint θ) = c θ) :
    openImage f ⊆ (Set.range c)ᶜ := by
  rintro x ⟨z, hz, rfl⟩ ⟨θ, hθ⟩
  change ‖(z : ℂ)‖ < 1 at hz
  have h1 : z = circlePoint θ := hinj (by rw [hb θ]; exact hθ.symm)
  rw [h1] at hz
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I] at hz
  exact absurd hz (lt_irrefl 1)

/-! ## Lifting a disc map through another one -/

/-- **Lifting a map into the range of an embedded disc.**  If `e : 𝔻 → ℂ` is a continuous injection
and `f : 𝔻 → ℂ` is a continuous map with image in the image of `e`, then `f` factors through `e` by a
continuous map `g : 𝔻 → 𝔻`. -/
theorem exists_lift_of_range_subset {e : C(Disc, ℂ)} (he : Function.Injective e) {f : C(Disc, ℂ)}
    (hf : Function.Injective f) (h : Set.range f ⊆ Set.range e) :
    ∃ g : C(Disc, Disc), (∀ z, e (g z) = f z) ∧ Function.Injective g := by
  have hEmb : Topology.IsEmbedding (e : Disc → ℂ) :=
    (e.continuous.isClosedEmbedding he).toIsEmbedding
  let eH : Disc ≃ₜ Set.range (e : Disc → ℂ) := hEmb.toHomeomorph
  let gf : Disc → Disc := fun z => eH.symm ⟨f z, h (Set.mem_range_self z)⟩
  have hcont : Continuous gf :=
    eH.symm.continuous.comp (Continuous.subtype_mk f.continuous _)
  have hkey : ∀ z, e (gf z) = f z := by
    intro z
    have h1 : eH (gf z) = ⟨f z, h (Set.mem_range_self z)⟩ := eH.apply_symm_apply _
    have h2 : ((eH (gf z) : Set.range (e : Disc → ℂ)) : ℂ) = e (gf z) :=
      Topology.IsEmbedding.toHomeomorph_apply_coe hEmb (gf z)
    rw [h1] at h2
    exact h2.symm
  refine ⟨⟨gf, hcont⟩, hkey, ?_⟩
  intro z w hzw
  apply hf
  have hzw' : gf z = gf w := hzw
  rw [← hkey z, ← hkey w, hzw']

/-! ## Uniqueness of the spanning disc when the open images are nested -/

/-- **If the image of the open disc under `f` lies in the open disc of `e`, then `f` and `e` have
the same image and the same open image.**

Both `f` and `e` are embeddings of the disc with the *same* boundary parametrisation, and
`openImage f ⊆ openImage e`.  Lifting `f` through `e` gives a continuous injection `g : 𝔻 → 𝔻`
which fixes the boundary circle pointwise and maps the open disc into itself, so
`Work.Smooth.SphereJordan.discEmbedding_surjective` (Brouwer) shows that `g` is surjective, and the
conclusion follows. -/
theorem eq_of_openImage_subset {f e : C(Disc, ℂ)} (hf : Function.Injective f)
    (he : Function.Injective e) {c : ℝ → ℂ} (hfb : ∀ θ : ℝ, f (circlePoint θ) = c θ)
    (heb : ∀ θ : ℝ, e (circlePoint θ) = c θ) (hsub : openImage f ⊆ openImage e) :
    Set.range f = Set.range e ∧ openImage f = openImage e := by
  have hrange_sub : Set.range f ⊆ Set.range e := by
    rw [range_eq_openImage_union hfb, range_eq_openImage_union heb]
    rintro x (hx | hx)
    · exact Or.inl (hsub hx)
    · exact Or.inr hx
  obtain ⟨g, hge, hginj⟩ := exists_lift_of_range_subset he hf hrange_sub
  have hgbd : ∀ θ : ℝ, g (circlePoint θ) = circlePoint θ := by
    intro θ
    apply he
    rw [hge, hfb θ, heb θ]
  have hgint : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → ‖((g z : Disc) : ℂ)‖ < 1 := by
    intro z hz
    have h1 : f z ∈ openImage e := hsub ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwe⟩ := h1
    have h2 : g z = w := he (by rw [hge, hwe])
    rw [h2]
    exact hw
  have hgsurj : Function.Surjective g := discEmbedding_surjective hginj hgbd hgint
  have himage : g '' (TwoDiscs.openUnitDisc : Set Disc) = TwoDiscs.openUnitDisc := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hgint z (by simpa [TwoDiscs.openUnitDisc] using hz)
    · intro w hw
      obtain ⟨z, rfl⟩ := hgsurj w
      have hz : (z : Disc) ∈ TwoDiscs.openUnitDisc := by
        by_contra hcon
        rw [TwoDiscs.openUnitDisc] at hcon
        have hle : ‖(z : ℂ)‖ ≤ 1 := by
          have := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
        have hzw : ‖(z : ℂ)‖ = 1 := le_antisymm hle (not_lt.mp hcon)
        obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hzw
        have hgz : ‖((g z : Disc) : ℂ)‖ = 1 := by
          have h1 : g z = g (Work.Smooth.Jordan.circlePoint θ) := congrArg g hθ.symm
          rw [h1, hgbd θ, Work.Smooth.Jordan.circlePoint_coe,
            Complex.norm_exp_ofReal_mul_I]
        rw [TwoDiscs.openUnitDisc] at hw
        exact absurd hgz (ne_of_lt hw)
      exact ⟨z, hz, rfl⟩
  have hfun : (fun z => e (g z)) = ⇑f := funext (fun z => hge z)
  refine ⟨?_, ?_⟩
  · rw [← hfun]
    change Set.range (⇑e ∘ ⇑g) = Set.range ⇑e
    rw [Set.range_comp, Set.range_eq_univ.mpr hgsurj, Set.image_univ]
  · simp only [openImage]
    rw [← hfun]
    change (⇑e ∘ ⇑g) '' (TwoDiscs.openUnitDisc : Set Disc) = ⇑e '' TwoDiscs.openUnitDisc
    rw [Set.image_comp, himage]

/-! ## The closure of the image of the open disc -/

/-- The open unit disc is dense in the model disc. -/
theorem closure_openUnitDisc : closure (TwoDiscs.openUnitDisc : Set Disc) = Set.univ := by
  have hind : Topology.IsInducing (Subtype.val : Disc → ℂ) := Topology.IsInducing.subtypeVal
  have h := hind.closure_eq_preimage_closure_image (TwoDiscs.openUnitDisc : Set Disc)
  rw [h, Set.eq_univ_iff_forall]
  intro z
  have himg : (Subtype.val '' (TwoDiscs.openUnitDisc : Set Disc) : Set ℂ) = Metric.ball 0 1 := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [TwoDiscs.openUnitDisc, Metric.mem_ball, dist_eq_norm] using hy
    · intro hw
      refine ⟨⟨w, ?_⟩, ?_, rfl⟩
      · simpa [Metric.mem_closedBall, dist_eq_norm] using
          le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
      · simpa [TwoDiscs.openUnitDisc, Metric.mem_ball, dist_eq_norm] using hw
  rw [himg, closure_ball (0 : ℂ) one_ne_zero]
  exact z.2

/-- **The closure of the image of the open model disc is the image of the whole model disc.** -/
theorem closure_openImage (f : C(Disc, ℂ)) : closure (openImage f) = Set.range f := by
  have h : openImage f = f '' (TwoDiscs.openUnitDisc : Set Disc) := by
    simp only [openImage, TwoDiscs.openUnitDisc]
  rw [h]
  apply Set.Subset.antisymm
  · exact closure_minimal (by rintro x ⟨z, -, rfl⟩; exact ⟨z, rfl⟩)
      (isCompact_range f.continuous).isClosed
  · rintro x ⟨z, rfl⟩
    have hz : z ∈ closure (TwoDiscs.openUnitDisc : Set Disc) := by
      rw [closure_openUnitDisc]; trivial
    exact image_closure_subset_closure_image f.continuous ⟨z, hz, rfl⟩

end

end Work.Smooth.SphereJordan
