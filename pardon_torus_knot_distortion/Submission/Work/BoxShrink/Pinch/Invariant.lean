import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.SurgeryInvariance.Span.union_eq_sup

/-!
# Pardon's `spherefamily` in the invariant form the pinch needs

Pardon's Lemma `spherefamily` propagates the invariant

  `W t = im (H₁(F ∩ int S_t ; ℚ) → H₁(F ; ℚ))`

along a one-parameter family of spheres.  His proof is:

* at every parameter at which `S_t` is transverse to `F` the invariant is either `0` or
  `2g = 2g` — Pardon's equation (1), the *dichotomy* `W t = ⊥ ∨ W t = ⊤`;
* a single surgery changes the invariant by at most one dimension, i.e. the *dimension* of `W t`
  changes by at most one over a sufficiently small parameter interval;
* the invariant is therefore *locally constant*, and the parameter line is connected, so it is
  constant.

This module formalises exactly that argument, in the curve-level invariant `WindingSpan` of
`Work.SurgeryInvariance`.  The statement is Pardon's, with the local content (the dichotomy and the
dimension jump bound) as hypotheses, and it is the engine of `Work.BoxShrink.Pinch.Regions`: the
field of the pinch is the *conclusion* of this lemma, not a hypothesis.

The form below is the one the pinch needs: the dichotomy is assumed only *before* the pinching
parameter `1` (at the pinching parameter the "sphere" is a double bubble, and Pardon's private
argument there is the perturbation step `doublebubble2`, which is the dimension bound at `1`), and
the conclusion is that the invariant at `1` is nonzero.  This is what Pardon's proof gives, and it
is *weaker* than `W 1 = ⊤`: the conclusion `W 1 ≠ ⊥` is exactly Pardon's Lemma 3 conclusion after
the final decomposition `W 1 = W₁ ⊔ W₂` into the two halves.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- **The winding span of a region of `ℚ²` is at most two-dimensional.** -/
theorem finrank_windingSpan_le_two (P : Work.CoreTopology.ParamTorus) (X : Set R3) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) ≤ 2 := by
  have h : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) ≤
      Module.finrank ℚ (ℚ × ℚ) := Submodule.finrank_le _
  rw [Module.finrank_prod, Module.finrank_self] at h
  omega

/-- **The invariant is everything below the pinching parameter.**  Pardon's local-constancy step:
with the dichotomy before the pinching parameter and the dimension bound at every parameter, the
invariant is constant on `(-∞, 1)`; since it is `⊤` at `0`, it is `⊤` everywhere below `1`. -/
theorem eq_top_of_lt_one {A : Type*} [AddCommGroup A] [Module ℚ A] [FiniteDimensional ℚ A]
    (W : ℝ → Submodule ℚ A) (hA : 1 < Module.finrank ℚ A)
    (hval : ∀ t : ℝ, t < 1 → W t = ⊥ ∨ W t = ⊤)
    (hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(W s) ≤ Module.finrank ℚ ↥(W t) + 1 ∧
      Module.finrank ℚ ↥(W t) ≤ Module.finrank ℚ ↥(W s) + 1)
    (h0 : W 0 = ⊤) : ∀ t : ℝ, t < 1 → W t = ⊤ := by
  have hfbot : Module.finrank ℚ ↥(⊥ : Submodule ℚ A) = 0 :=
    Submodule.finrank_eq_zero.mpr rfl
  have hftop : Module.finrank ℚ ↥(⊤ : Submodule ℚ A) = Module.finrank ℚ A :=
    finrank_top ℚ A
  -- The invariant is locally constant below the pinching parameter.
  have hloc : ∀ t : ℝ, t < 1 → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, s < 1 → |s - t| < ε →
      W s = W t := by
    intro t ht
    obtain ⟨ε, hε, hε'⟩ := hstep t
    refine ⟨min ε ((1 - t) / 2), lt_min hε (by linarith), fun s hs hs' => ?_⟩
    obtain ⟨h1, h2⟩ := hε' s (lt_of_lt_of_le hs' (min_le_left _ _))
    rcases hval t ht with htb | htt
    · rcases hval s hs with hsb | hst
      · rw [htb, hsb]
      · rw [htb, hst, hftop, hfbot] at h1; omega
    · rcases hval s hs with hsb | hst
      · rw [htt, hsb, hftop, hfbot] at h2; omega
      · rw [htt, hst]
  intro t ht
  have hconst : W t = W 0 :=
    Work.BoxShrink.Bubble.eq_of_locally_const_lt_one (f := W) hloc ht
      (show (0 : ℝ) < 1 by norm_num)
  rw [hconst, h0]

/-- **The invariant is nonzero at the pinching parameter.**  Pardon's `spherefamily`, in the form
in which the double bubble consumes it:

* `hval`: Pardon's dichotomy (equation (1)) at every parameter *before* the pinching parameter;
* `hstep`: a single surgery changes the invariant by at most one dimension, at every parameter
  (at the pinching parameter this is Pardon's perturbation argument of `doublebubble2`);
* `h0`: the invariant of the initial region is everything (`W 0 = ⊤`, which for the box region
  follows from Pardon's dichotomy at the initial sphere).

Conclusion: the invariant at the pinching parameter is nonzero.

The proof is Pardon's: the two level sets `{W t = ⊤}`, `{W t = ⊥}` are open (by the dichotomy and
the dimension bound), disjoint, and cover the parameter line before `1`; the first contains `0`,
so it contains everything below `1`; and one more dimension bound at `1` finishes. -/
theorem submodule_ne_bot_of_lt_one {A : Type*} [AddCommGroup A] [Module ℚ A]
    [FiniteDimensional ℚ A] (W : ℝ → Submodule ℚ A) (hA : 1 < Module.finrank ℚ A)
    (hval : ∀ t : ℝ, t < 1 → W t = ⊥ ∨ W t = ⊤)
    (hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(W s) ≤ Module.finrank ℚ ↥(W t) + 1 ∧
      Module.finrank ℚ ↥(W t) ≤ Module.finrank ℚ ↥(W s) + 1)
    (h0 : W 0 = ⊤) : W 1 ≠ ⊥ := by
  have hfbot : Module.finrank ℚ ↥(⊥ : Submodule ℚ A) = 0 :=
    Submodule.finrank_eq_zero.mpr rfl
  have hftop : Module.finrank ℚ ↥(⊤ : Submodule ℚ A) = Module.finrank ℚ A :=
    finrank_top ℚ A
  have htop := eq_top_of_lt_one W hA hval hstep h0
  -- One more dimension bound at the pinching parameter.
  obtain ⟨ε, hε, hε'⟩ := hstep 1
  have hs1 : (1 - ε / 2) < 1 := by linarith
  have hdist : |(1 - ε / 2) - 1| < ε := by
    rw [abs_lt]; constructor <;> linarith
  have hval' := (hε' (1 - ε / 2) hdist).1
  rw [htop (1 - ε / 2) hs1, hftop] at hval'
  intro hbot
  rw [hbot, hfbot] at hval'
  omega

/-- **The invariant is everything at the pinching parameter**, when Pardon's dichotomy is available
at the pinching parameter as well (the form in which the double bubble's *two halves* are split).
This is `Work.CoreTopology.sphere_family` with the dichotomy restricted to `t < 1` and the
dimension bound at `1`. -/
theorem submodule_eq_top_of_lt_one {A : Type*} [AddCommGroup A] [Module ℚ A]
    [FiniteDimensional ℚ A] (W : ℝ → Submodule ℚ A) (hA : 1 < Module.finrank ℚ A)
    (hval : ∀ t : ℝ, t < 1 → W t = ⊥ ∨ W t = ⊤)
    (hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(W s) ≤ Module.finrank ℚ ↥(W t) + 1 ∧
      Module.finrank ℚ ↥(W t) ≤ Module.finrank ℚ ↥(W s) + 1)
    (h0 : W 0 = ⊤) (h1 : W 1 = ⊥ ∨ W 1 = ⊤) : W 1 = ⊤ := by
  rcases h1 with h | h
  · exact absurd h (submodule_ne_bot_of_lt_one W hA hval hstep h0)
  · exact h

end

end Work.BoxShrink.Pinch
