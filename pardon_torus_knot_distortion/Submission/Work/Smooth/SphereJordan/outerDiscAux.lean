import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.Schoenflies.Unconditional
import Submission.Work.Smooth.Jordan.All

/-!
# Auxiliaries for the outer-disc construction on the Riemann sphere

This module collects the elementary API used by
`Work.Smooth.SphereJordan.exists_outerDisc` (the construction of the disc spanning the *outer*
side of the curve traced by an injective disc map `F : 𝔻 → ℂ`):

* `planeLift` — a disc map `𝔻 → ℂ ∪ {∞}` whose image misses `∞` read in the plane `ℂ`;
* `range_eq_openImage_union_sphere` — the range of such a map is the image of the open disc
  together with the trace of its boundary curve;
* `image_coe_range` and `compl_image_coe_eq` — the elementary set theory of the finite part
  `ℂ ⊆ ℂ ∪ {∞}`;
* `inner_ne_infty` — the piece of a two-disc datum that does not contain `∞` avoids `∞`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Reading a disc map missing `∞` in the plane -/

/-- **The plane avatar of a disc map into the Riemann sphere which avoids `∞`.**

For `e : 𝔻 → ℂ ∪ {∞}` with `e z ≠ ∞` for every `z`, `planeLift e hne : 𝔻 → ℂ` is the unique map
with `((planeLift e hne z : ℂ) : ℂ ∪ {∞}) = e z`.  Its continuity is the defining property of the
one-point compactification (`OnePoint.comap_coe_nhds`): the finite part carries the topology of
`ℂ`. -/
def planeLift (e : C(Disc, RiemannSphere)) (hne : ∀ z, e z ≠ infty) : C(Disc, ℂ) :=
  ⟨fun z => Classical.choose (OnePoint.ne_infty_iff_exists.mp (hne z)),
   continuous_iff_continuousAt.mpr (fun z => by
     show Filter.Tendsto (fun z : Disc =>
       Classical.choose (OnePoint.ne_infty_iff_exists.mp (hne z))) (nhds z)
       (nhds (Classical.choose (OnePoint.ne_infty_iff_exists.mp (hne z))))
     rw [← OnePoint.comap_coe_nhds (Classical.choose
       (OnePoint.ne_infty_iff_exists.mp (hne z)))]
     rw [Filter.tendsto_comap_iff]
     have hcoe : (OnePoint.some ∘ fun z : Disc =>
         Classical.choose (OnePoint.ne_infty_iff_exists.mp (hne z))) = ⇑e :=
       funext (fun z => Classical.choose_spec
         (OnePoint.ne_infty_iff_exists.mp (hne z)))
     rw [hcoe, Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (hne z))]
     exact e.continuous.continuousAt)⟩

theorem planeLift_coe (e : C(Disc, RiemannSphere)) (hne : ∀ z, e z ≠ infty) (z : Disc) :
    ((planeLift e hne z : ℂ) : RiemannSphere) = e z :=
  Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (hne z))

theorem planeLift_injective (e : C(Disc, RiemannSphere)) (hne : ∀ z, e z ≠ infty)
    (he : Function.Injective e) : Function.Injective (planeLift e hne) := by
  intro a b hab
  apply he
  rw [← planeLift_coe e hne a, ← planeLift_coe e hne b, hab]

/-! ## The range of a disc map -/

/-- The range of a disc map whose boundary circle traces `c` is the image of the open disc
together with the trace of `c`. -/
theorem range_eq_openImage_union_sphere {f : C(Disc, RiemannSphere)} {c : ℝ → RiemannSphere}
    (hb : ∀ θ : ℝ, f (circlePoint θ) = c θ) :
    Set.range f = {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ f z = x} ∪ Set.range c := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    rcases lt_or_eq_of_le (TwoDiscs.disc_norm_le_one z) with hlt | heq
    · exact Or.inl ⟨z, hlt, rfl⟩
    · right
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z heq
      exact ⟨θ, by rw [← hθ, hb θ]⟩
  · rintro x (⟨z, -, rfl⟩ | ⟨θ, rfl⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨circlePoint θ, hb θ⟩

/-! ## The set theory of the finite part `ℂ ⊆ ℂ ∪ {∞}` -/

/-- The range of `z ↦ ((g z : ℂ) : ℂ ∪ {∞})` is the image under the coercion of the range of
`g`. -/
theorem image_coe_range (g : C(Disc, ℂ)) :
    Set.range (fun z : Disc => ((g z : ℂ) : RiemannSphere)) =
      (fun x : ℂ => (x : RiemannSphere)) '' Set.range g := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨g z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

/-- The complement of the finite part of a set of complex numbers, inside the Riemann sphere, is
`∞` together with the finite part of the complement. -/
theorem compl_image_coe_eq (S : Set ℂ) :
    ((fun x : ℂ => (x : RiemannSphere)) '' S)ᶜ =
      ({OnePoint.infty} : Set RiemannSphere) ∪
        ((fun x : ℂ => (x : RiemannSphere)) '' Sᶜ) := by
  ext x
  constructor
  · intro hx
    by_cases hxi : x = OnePoint.infty
    · exact Or.inl hxi
    · obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hxi
      refine Or.inr ⟨z, ?_, hz⟩
      intro hzS
      exact hx ⟨z, hzS, hz⟩
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · rintro ⟨y, -, hy⟩
      exact OnePoint.coe_ne_infty y hy
    · rintro ⟨y, hyS, hy⟩
      exact hz (OnePoint.coe_injective hy ▸ hyS)

/-! ## The two pieces of a two-disc datum -/

/-- The piece of a two-disc datum that does not contain `∞` avoids `∞`, for a curve that itself
avoids `∞`. -/
theorem inner_ne_infty {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hc : OnePoint.infty ∉ Set.range c) (z : Disc) :
    T.inner OnePoint.infty z ≠ OnePoint.infty := by
  intro hz
  by_cases h : OnePoint.infty ∈ Set.range T.e
  · rw [T.inner_eq_of_mem OnePoint.infty h] at hz
    have hmem : OnePoint.infty ∈ Set.range T.e ∩ Set.range T.e' := ⟨h, ⟨z, hz⟩⟩
    rw [T.meet] at hmem
    exact hc hmem
  · rw [T.inner_eq_of_notMem OnePoint.infty h] at hz
    exact h ⟨z, hz⟩

/-- The piece of a two-disc datum that contains `∞` contains `∞`, for a curve that avoids `∞`. -/
theorem infty_mem_range_outer {c : ℝ → RiemannSphere} (T : TwoDiscs c) :
    OnePoint.infty ∈ Set.range (T.outer OnePoint.infty) := by
  by_cases h : OnePoint.infty ∈ Set.range T.e
  · rw [T.outer_eq_of_mem OnePoint.infty h]; exact h
  · rw [T.outer_eq_of_notMem OnePoint.infty h]
    have hcov : OnePoint.infty ∈ Set.range T.e ∪ Set.range T.e' := by
      rw [T.cover]; trivial
    exact hcov.resolve_left h

/-- The outer piece of a two-disc datum is a disc of the plane after deleting `∞`. -/
theorem exists_interior_preimage_infty {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hc : OnePoint.infty ∉ Set.range c) :
    ∃ w : Disc, ‖(w : ℂ)‖ < 1 ∧ T.outer OnePoint.infty w = OnePoint.infty := by
  have hmem : OnePoint.infty ∈ Set.range (T.outer OnePoint.infty) := infty_mem_range_outer T
  rw [range_eq_openImage_union_sphere (T.outer_boundary OnePoint.infty)] at hmem
  rcases hmem with ⟨w, hw, hwe⟩ | hc'
  · exact ⟨w, hw, hwe⟩
  · exact absurd hc' hc

end

end Work.Smooth.SphereJordan
