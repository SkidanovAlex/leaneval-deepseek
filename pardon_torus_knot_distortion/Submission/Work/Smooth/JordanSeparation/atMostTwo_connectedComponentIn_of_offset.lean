import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.componentIn_meets_annulus

/-!
# At most two components of the complement of an offset curve

Let `c : ℝ → ℂ` be a `C¹` `2π`-periodic closed plane curve, `v : ℝ → ℂ` a continuous `2π`-periodic
field and `δ > 0`, such that the offset map `(t,u) ↦ offset c v (t,u) = c.γ t + u·v t` is injective
in the `u`-variable on the strip `|u| < δ` and the trace of `c` is contained in the annulus
`annulus c v δ = offset c v '' (ℝ × (-δ,δ))`.  Then **of any three points off the trace, two lie in
the same connected component of the complement of the trace**.

The two open halves `posPart c v δ` (`u ∈ (0,δ)`) and `negPart c v δ` (`u ∈ (-δ,0)`) of the annulus
are preconnected and lie in the complement of the trace; the annulus minus the trace is their union
(`annulus_eq`, `zeroPart_eq_trace`).  By `componentIn_meets_annulus` every component of the
complement meets the annulus, hence contains `posPart` or `negPart`; so each component of the
complement is the component of a single fixed point of `posPart` (call it `P`) or of a single
fixed point of `negPart` (call it `Q`).  With only two possible components, two of the three given
points share one.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

theorem atMostTwo_connectedComponentIn_of_offset (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    {v : ℝ → ℂ} {δ : ℝ} (hv : Continuous v) (hδ : 0 < δ)
    (hper : Function.Periodic v (2 * Real.pi))
    (htrace : c.trace ⊆ Work.Smooth.JordanSeparation.annulus c v δ)
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      Work.Smooth.JordanSeparation.offset c v (t, u)
        = Work.Smooth.JordanSeparation.offset c v (t', u') → u = u')
    {x y z : ℂ} (hx : x ∉ c.trace) (hy : y ∉ c.trace) (hz : z ∉ c.trace) :
    connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ y ∨
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ z ∨
      connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z := by
  have h0 : |(0 : ℝ)| < δ := by simpa using hδ
  -- The two halves of the annulus lie in the complement of the trace.
  have hpos_sub : Work.Smooth.JordanSeparation.posPart c v δ ⊆ c.traceᶜ := by
    rintro a ⟨⟨t, u⟩, ⟨-, hu⟩, rfl⟩
    rintro ⟨t', ht'⟩
    have hlt : |u| < δ := abs_lt.mpr ⟨by linarith [hu.1], hu.2⟩
    have heq : Work.Smooth.JordanSeparation.offset c v (t, u)
        = Work.Smooth.JordanSeparation.offset c v (t', 0) := by
      rw [Work.Smooth.JordanSeparation.offset_zero]; exact ht'.symm
    exact absurd (hinj t t' u 0 hlt h0 heq) (ne_of_gt hu.1)
  have hneg_sub : Work.Smooth.JordanSeparation.negPart c v δ ⊆ c.traceᶜ := by
    rintro a ⟨⟨t, u⟩, ⟨-, hu⟩, rfl⟩
    rintro ⟨t', ht'⟩
    have hlt : |u| < δ := abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have heq : Work.Smooth.JordanSeparation.offset c v (t, u)
        = Work.Smooth.JordanSeparation.offset c v (t', 0) := by
      rw [Work.Smooth.JordanSeparation.offset_zero]; exact ht'.symm
    exact absurd (hinj t t' u 0 hlt h0 heq) (ne_of_lt hu.2)
  -- two fixed points, one on each half
  set p : ℂ := Work.Smooth.JordanSeparation.offset c v (0, δ / 2) with hpdef
  set q : ℂ := Work.Smooth.JordanSeparation.offset c v (0, -(δ / 2)) with hqdef
  have hp_pos : p ∈ Work.Smooth.JordanSeparation.posPart c v δ :=
    ⟨(0, δ / 2), ⟨trivial, by constructor <;> linarith⟩, rfl⟩
  have hq_neg : q ∈ Work.Smooth.JordanSeparation.negPart c v δ :=
    ⟨(0, -(δ / 2)), ⟨trivial, by constructor <;> linarith⟩, rfl⟩
  have hposP : Work.Smooth.JordanSeparation.posPart c v δ ⊆
      connectedComponentIn c.traceᶜ p :=
    IsPreconnected.subset_connectedComponentIn
      (Work.Smooth.JordanSeparation.posPart_isPreconnected c hv δ) hp_pos hpos_sub
  have hnegQ : Work.Smooth.JordanSeparation.negPart c v δ ⊆
      connectedComponentIn c.traceᶜ q :=
    IsPreconnected.subset_connectedComponentIn
      (Work.Smooth.JordanSeparation.negPart_isPreconnected c hv δ) hq_neg hneg_sub
  -- every component of the complement is the component of `p` or of `q`
  have key : ∀ w : ℂ, w ∉ c.trace →
      connectedComponentIn c.traceᶜ w = connectedComponentIn c.traceᶜ p ∨
      connectedComponentIn c.traceᶜ w = connectedComponentIn c.traceᶜ q := by
    intro w hw
    obtain ⟨a, haW, haA⟩ := componentIn_meets_annulus c hv hδ hper htrace hinj w hw
    have haK : a ∈ c.traceᶜ := connectedComponentIn_subset c.traceᶜ w haW
    rw [Work.Smooth.JordanSeparation.annulus_eq c v hδ,
      Work.Smooth.JordanSeparation.zeroPart_eq_trace c v] at haA
    rcases haA with (h | h) | h
    · left
      exact (connectedComponentIn_eq haW).trans (connectedComponentIn_eq (hposP h)).symm
    · right
      exact (connectedComponentIn_eq haW).trans (connectedComponentIn_eq (hnegQ h)).symm
    · exact absurd h haK
  rcases key x hx with hx1 | hx1
  · rcases key y hy with hy1 | hy1
    · exact Or.inl (hx1.trans hy1.symm)
    · rcases key z hz with hz1 | hz1
      · exact Or.inr (Or.inl (hx1.trans hz1.symm))
      · exact Or.inr (Or.inr (hy1.trans hz1.symm))
  · rcases key y hy with hy1 | hy1
    · rcases key z hz with hz1 | hz1
      · exact Or.inr (Or.inr (hy1.trans hz1.symm))
      · exact Or.inr (Or.inl (hx1.trans hz1.symm))
    · exact Or.inl (hx1.trans hy1.symm)

end

end Work.Smooth.JordanSeparation
