import Mathlib
import Submission.Work.Smooth.Jordan.Sphere

namespace Work.Smooth.Jordan

open Set
open LeanEval.KnotTheory.PardonDistortion

/-- The boundary circle of an embedded disc whose boundary parametrisation is `c` maps onto the
trace of `c`. -/
theorem image_sphere_eq_range_of_boundary {e : C(Disc, R3)} {c : ℝ → R3}
    (hb : ∀ θ : ℝ, e (circlePoint θ) = c θ) :
    e '' {z : Disc | ‖(z : ℂ)‖ = 1} = Set.range c := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨θ, rfl⟩ := exists_circlePoint_eq z hz
    exact ⟨θ, (hb θ).symm⟩
  · rintro _ ⟨θ, rfl⟩
    exact ⟨circlePoint θ, by
      change ‖(((circlePoint θ : Disc)) : ℂ)‖ = 1
      rw [circlePoint_coe, Complex.norm_exp_ofReal_mul_I], hb θ⟩

/-- The range of an embedded disc whose boundary parametrisation is `c` splits into the image of
the open disc and the trace of `c`. -/
theorem range_eq_openDisc_union_of_boundary {e : C(Disc, R3)} {c : ℝ → R3}
    (hb : ∀ θ : ℝ, e (circlePoint θ) = c θ) :
    Set.range e = e '' {z : Disc | ‖(z : ℂ)‖ < 1} ∪ Set.range c := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    have hzle : ‖(z : ℂ)‖ ≤ 1 := by
      have := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
    rcases lt_or_eq_of_le hzle with hlt | heq
    · exact Or.inl ⟨z, hlt, rfl⟩
    · obtain ⟨θ, hθ⟩ := exists_circlePoint_eq z heq
      exact Or.inr ⟨θ, by rw [← hθ]; exact (hb θ).symm⟩
  · rintro _ (⟨z, _, rfl⟩ | ⟨θ, rfl⟩)
    · exact ⟨z, rfl⟩
    · exact ⟨circlePoint θ, hb θ⟩

theorem sphereSchoenflies_openDisc_compl {A : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {c : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (h : SphereSchoenflies A c) :
    h.e '' {z : Disc | ‖(z : ℂ)‖ < 1} ∪ h.e' '' {z : Disc | ‖(z : ℂ)‖ < 1} ∪ Set.range c = A ∧
    Disjoint (h.e '' {z : Disc | ‖(z : ℂ)‖ < 1}) (h.e' '' {z : Disc | ‖(z : ℂ)‖ < 1}) ∧
    Disjoint (h.e '' {z : Disc | ‖(z : ℂ)‖ < 1}) (Set.range c) ∧
    Disjoint (h.e' '' {z : Disc | ‖(z : ℂ)‖ < 1}) (Set.range c) := by
  have hsphere_e : h.e '' {z : Disc | ‖(z : ℂ)‖ = 1} = Set.range c :=
    image_sphere_eq_range_of_boundary h.boundary
  have hsphere_e' : h.e' '' {z : Disc | ‖(z : ℂ)‖ = 1} = Set.range c :=
    image_sphere_eq_range_of_boundary h.boundary'
  have hrange_e : Set.range h.e = h.e '' {z : Disc | ‖(z : ℂ)‖ < 1} ∪ Set.range c :=
    range_eq_openDisc_union_of_boundary h.boundary
  have hrange_e' : Set.range h.e' = h.e' '' {z : Disc | ‖(z : ℂ)‖ < 1} ∪ Set.range c :=
    range_eq_openDisc_union_of_boundary h.boundary'
  -- the open disc of `e` misses the curve
  have hd1 : Disjoint (h.e '' {z : Disc | ‖(z : ℂ)‖ < 1}) (Set.range c) := by
    rw [← hsphere_e, Set.disjoint_left]
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, hba⟩ := hy
    change ‖(a : ℂ)‖ < 1 at ha
    change ‖(b : ℂ)‖ = 1 at hb
    have hab : a = b := h.inj hba.symm
    rw [hab] at ha
    linarith
  -- the open disc of `e'` misses the curve
  have hd1' : Disjoint (h.e' '' {z : Disc | ‖(z : ℂ)‖ < 1}) (Set.range c) := by
    rw [← hsphere_e', Set.disjoint_left]
    intro x hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, hba⟩ := hy
    change ‖(a : ℂ)‖ < 1 at ha
    change ‖(b : ℂ)‖ = 1 at hb
    have hab : a = b := h.inj' hba.symm
    rw [hab] at ha
    linarith
  -- the two open discs are disjoint
  have hd_open : Disjoint (h.e '' {z : Disc | ‖(z : ℂ)‖ < 1})
      (h.e' '' {z : Disc | ‖(z : ℂ)‖ < 1}) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbx⟩ := hx'
    have hmem : x ∈ Set.range h.e ∩ Set.range h.e' := ⟨⟨a, hax⟩, ⟨b, hbx⟩⟩
    rw [h.meet] at hmem
    exact (Set.disjoint_left.mp hd1) ⟨a, ha, hax⟩ hmem
  -- the three pieces cover `A`
  have hcover : h.e '' {z : Disc | ‖(z : ℂ)‖ < 1} ∪ h.e' '' {z : Disc | ‖(z : ℂ)‖ < 1}
      ∪ Set.range c = A := by
    have step : h.e '' {z : Disc | ‖(z : ℂ)‖ < 1} ∪ h.e' '' {z : Disc | ‖(z : ℂ)‖ < 1}
        ∪ Set.range c = Set.range h.e ∪ Set.range h.e' := by
      rw [hrange_e, hrange_e']
      ext x; simp only [Set.mem_union]; tauto
    exact step.trans h.cover
  exact ⟨hcover, hd_open, hd1, hd1'⟩

end Work.Smooth.Jordan
