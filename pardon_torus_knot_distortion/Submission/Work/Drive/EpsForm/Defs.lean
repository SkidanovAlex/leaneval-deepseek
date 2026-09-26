import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.BoxShrink.ledger
import Submission.Work.BoxShrink.halving
import Submission.Work.Drive.InterfacesD

/-!
# Pardon's Lemma 3 in the ε-form of his own proof (`doublebubble2`)

`Work.BoxShrink.Bubble.BubbleHalf` — Pardon's Lemma 3 conclusion with the *exact* half-region —
is **strictly stronger** than the published Lemma 3: Pardon's `doublebubble` is stated for a double
bubble *transverse* to `F` and `β`, and the form he actually applies in the proof of the theorem,
`doublebubble2` (Annals **174** (2011), §3), concludes only the *neighbourhood* statement

> `F ∩ (B(ε) + int(H_i))` has a component of genus `g` for some `i ∈ {1,2}` and every `ε > 0`

(the perturbation into general position which produces `doublebubble2` from `doublebubble` cannot
be undone).  For the smooth tori of the challenge and the box/plane configuration
`(F, PBox s c σ, {y (σ 2) = c (σ 2) + u})`, "a component of genus `g` of `F ∩ (B(ε) + int(H_i))`"
is exactly "an essential closed curve of `F` lying within (Euclidean) distance `ε` of the
half-region `upperRegion`/`lowerRegion`", which is the conclusion recorded below.

The module also proves the two **geometric** facts which make the ε-form consumable by the crux:
a curve within `ε` of a half-region of the box `PBox s c σ` lies in the slightly larger box
`PBox (s + ε) c σ` (on the correct side of the slightly shifted plane), and the halving geometry
then places it in a box of size `shrinkFactor * r`.  These are the only places where the
ε-margin is spent, and the margin is available because the crux's parameters satisfy the *strict*
inequalities `s < (1 + eps) * r` and `|u| < eps * r`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal
open Metric

namespace Work.Drive

/-- **The ε-form of Pardon's Lemma 3 for the box/plane configuration.**

This is `Work.Drive.CountingHalfW` with its conclusion (`Work.BoxShrink.Bubble.BubbleHalf`, the
*exact* statement "one of the two half-regions carries an essential loop") replaced by Pardon's
own `doublebubble2` conclusion: for every `ε > 0` some essential loop of `F` lies in the
`ε`-neighbourhood of one of the two half-regions.  All the hypotheses are *verbatim* those of
`CountingHalfW`. -/
def CountingHalfEps : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∀ ε : ℝ, 0 < ε →
            (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
                Work.CoreTopology.IsEssential _ γ ∧
                  ∀ t : ℝ, γ t ∈ thickening ε
                    (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) ∨
            (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
                Work.CoreTopology.IsEssential _ γ ∧
                  ∀ t : ℝ, γ t ∈ thickening ε
                    (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u))
/-- **The corrected ε-form** (`CleansDiscsAllWd`, the input that is *true*; see
`Submission/Work/Drive/InterfacesD.lean` and the report `lemma-Drive_cleansDiscsAllW.md`): the weak
cut-and-paste is demanded only for innermost discs whose interior curves are disjoint from the
boundary curve `a` — which is what Pardon's sphere-slicing supplies.  This is the honest statement;
it is *stronger* than `CountingHalfEps` (whose hypothesis `CleansDiscsW` is false), and therefore
implies it. -/
def CountingHalfEpsD : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∀ ε : ℝ, 0 < ε →
            (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
                Work.CoreTopology.IsEssential _ γ ∧
                  ∀ t : ℝ, γ t ∈ thickening ε
                    (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) ∨
            (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
                Work.CoreTopology.IsEssential _ γ ∧
                  ∀ t : ℝ, γ t ∈ thickening ε
                    (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u))

/-- The corrected ε-form implies the `W`-form (whose hypothesis is stronger). -/
theorem countingHalfEps_of_countingHalfEpsD (h : CountingHalfEpsD) : CountingHalfEps :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    h p q hp hq hc ψ K d hd hbound himg hsmall
      (fun S D hdisj => hcl S D) r hr c σ hbox s hrs hs hslice u hu hS hU


/-! ## The geometric conversion: from a thickened loop to a smaller box -/

/-- **A point close to a point of the box `PBox s c σ` lies in `PBox (s + δ) c σ`.**  This is the
elementary observation that the box sides are `≥ 1`, so a `δ`-thickening of the box is contained in
the box of size `s + δ`. -/
theorem mem_PBox_add_of_norm_sub_lt {s δ : ℝ} (hδ : 0 ≤ δ) {c : R3}
    {σ : Equiv.Perm (Fin 3)} {x y : R3} (hx : x ∈ Submission.PBox s c σ)
    (hxy : ‖y - x‖ < δ) : y ∈ Submission.PBox (s + δ) c σ := by
  intro i
  have h1 : |y (σ i) - x (σ i)| < δ := by
    have h2 : |(y - x) (σ i)| ≤ ‖y - x‖ := PiLp.norm_apply_le (p := 2) (y - x) (σ i)
    have h3 : (y - x) (σ i) = y (σ i) - x (σ i) := rfl
    rw [h3] at h2
    exact lt_of_le_of_lt h2 hxy
  have h4 : |x (σ i) - c (σ i)| < Submission.boxSide i * s := hx i
  have h5 : (1 : ℝ) ≤ Submission.boxSide i := Submission.one_le_boxSide i
  calc |y (σ i) - c (σ i)| ≤ |y (σ i) - x (σ i)| + |x (σ i) - c (σ i)| := abs_sub_le _ _ _
    _ < δ + Submission.boxSide i * s := by linarith
    _ ≤ Submission.boxSide i * δ + Submission.boxSide i * s := by
        nlinarith [hδ, h5]
    _ = Submission.boxSide i * (s + δ) := by ring

/-- **The `ε`-slack of the crux's configuration.**  This is `1/8` of the margin by which the
half-box `{y (σ 2) < c (σ 2) + u}` is exceeded by the box `PBox (b * s + |u| / 2)`, and it is
positive precisely because the crux's parameters satisfy the *strict* inequalities
`s < (1 + eps) * r` and `|u| < eps * r`. -/
noncomputable def epsSlack (r s u : ℝ) : ℝ :=
  (Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) / 8

theorem epsSlack_pos {r s u : ℝ} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) :
    0 < epsSlack r s u := by
  have hb : 0 < Submission.b := Submission.b_pos
  have h1 : Submission.b * s < Submission.b * ((1 + Submission.eps) * r) := by nlinarith
  have h2 : |u| / 2 < Submission.eps * r / 2 := by linarith
  have h3 : Submission.b * ((1 + Submission.eps) * r) + Submission.eps * r / 2 =
      Submission.shrinkFactor * r := by
    rw [Submission.shrinkFactor, Submission.eps, Submission.b]; ring
  have hm : Submission.b * s + |u| / 2 < Submission.shrinkFactor * r := by linarith
  rw [epsSlack]
  linarith

/-- **The slack is small enough to be absorbed by the halving geometry.**  This is the numerical
content of the ε-form: the `ε`-thickened half-box, read as a half of the box `PBox (s + ε)`, still
fits in a box of size `shrinkFactor * r`. -/
theorem halfBox_spec {r s u ε : ℝ} (hε : 0 ≤ ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) :
    Submission.b * (s + ε) + |u + ε| / 2 ≤ Submission.shrinkFactor * r := by
  have hb : Submission.b + 1 / 2 ≤ 8 := by
    have := Submission.b_lt_four_fifths
    linarith
  have h1 : |u + ε| ≤ |u| + ε := by
    have := abs_add_le u ε
    rwa [abs_of_nonneg hε] at this
  have h2 : ε * (Submission.b + 1 / 2) ≤ 8 * ε := by nlinarith [hε, hb]
  have h3 : Submission.b * (s + ε) = Submission.b * s + Submission.b * ε := by ring
  have h4 : ε * (Submission.b + 1 / 2) = Submission.b * ε + ε / 2 := by ring
  linarith [h1, h2, h3, h4]

/-- The same numerical bound for the other side of the plane. -/
theorem halfBox_spec' {r s u ε : ℝ} (hε : 0 ≤ ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2)) :
    Submission.b * (s + ε) + |u - ε| / 2 ≤ Submission.shrinkFactor * r := by
  have hb : Submission.b + 1 / 2 ≤ 8 := by
    have := Submission.b_lt_four_fifths
    linarith
  have h1 : |u - ε| ≤ |u| + ε := by
    have h := abs_sub_le u 0 ε
    have h2 : |0 - ε| = ε := by rw [zero_sub, abs_neg, abs_of_nonneg hε]
    have h3 : |u - 0| = |u| := by rw [sub_zero]
    linarith
  have h2 : ε * (Submission.b + 1 / 2) ≤ 8 * ε := by nlinarith [hε, hb]
  have h3 : Submission.b * (s + ε) = Submission.b * s + Submission.b * ε := by ring
  have h4 : ε * (Submission.b + 1 / 2) = Submission.b * ε + ε / 2 := by ring
  linarith [h1, h2, h3, h4]

/-- **The thickened half-box is contained in the box of size `s + ε`**: the two elementary
inequalities which make the halving geometry applicable. -/
theorem abs_shift_lt_boxSide_two_mul {r s u ε : ℝ} (hr : 0 < r) (hrs : r < s)
    (hu : |u| < Submission.eps * r) (hε : 0 ≤ ε) :
    |u + ε| < Submission.boxSide 2 * (s + ε) := by
  have hs0 : 0 < s := lt_trans hr hrs
  have hb2 : Submission.eps ≤ Submission.boxSide 2 := by
    rw [Submission.boxSide_two, Submission.eps]
    linarith [Submission.one_le_rpow_two_thirds]
  have hb1 : (1 : ℝ) ≤ Submission.boxSide 2 := by
    rw [Submission.boxSide_two]; exact Submission.one_le_rpow_two_thirds
  have h1 : |u + ε| ≤ |u| + ε := by
    have := abs_add_le u ε
    rwa [abs_of_nonneg hε] at this
  have h4 : ε ≤ Submission.boxSide 2 * ε := by nlinarith [hb1, hε]
  have h5 : Submission.eps * s ≤ Submission.boxSide 2 * s := by nlinarith [hb2, hs0]
  have h6 : Submission.eps * r < Submission.eps * s := by nlinarith [Submission.eps_pos, hrs]
  have h7 : Submission.boxSide 2 * (s + ε) =
      Submission.boxSide 2 * s + Submission.boxSide 2 * ε := by ring
  linarith [h1, hu, h4, h5, h6, h7]

/-- The same, on the other side of the plane. -/
theorem abs_sub_lt_boxSide_two_mul {r s u ε : ℝ} (hr : 0 < r) (hrs : r < s)
    (hu : |u| < Submission.eps * r) (hε : 0 ≤ ε) :
    |u - ε| < Submission.boxSide 2 * (s + ε) := by
  have hs0 : 0 < s := lt_trans hr hrs
  have hb2 : Submission.eps ≤ Submission.boxSide 2 := by
    rw [Submission.boxSide_two, Submission.eps]
    linarith [Submission.one_le_rpow_two_thirds]
  have hb1 : (1 : ℝ) ≤ Submission.boxSide 2 := by
    rw [Submission.boxSide_two]; exact Submission.one_le_rpow_two_thirds
  have h1 : |u - ε| ≤ |u| + ε := by
    have h := abs_sub_le u 0 ε
    have h2 : |0 - ε| = ε := by rw [zero_sub, abs_neg, abs_of_nonneg hε]
    have h3 : |u - 0| = |u| := by rw [sub_zero]
    linarith
  have h4 : ε ≤ Submission.boxSide 2 * ε := by nlinarith [hb1, hε]
  have h5 : Submission.eps * s ≤ Submission.boxSide 2 * s := by nlinarith [hb2, hs0]
  have h6 : Submission.eps * r < Submission.eps * s := by nlinarith [Submission.eps_pos, hrs]
  have h7 : Submission.boxSide 2 * (s + ε) =
      Submission.boxSide 2 * s + Submission.boxSide 2 * ε := by ring
  linarith [h1, hu, h4, h5, h6, h7]

/-- **The conversion lemma, "below the plane" half.**  If an essential loop of the surface lies
within `ε` of the lower half-region of `PBox s c σ` (the points below the cutting plane), then some
box of size `shrinkFactor * r` meets the surface in an essential loop. -/
theorem hasEssBox_of_thickening_lowerRegion {P : Work.CoreTopology.ParamTorus} {r s u ε : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) (hε : 0 < ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2))
    (h : ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ t ∈ thickening ε
        (Work.BoxShrink.Core.lowerRegion P s c σ u)) :
    ∃ c' σ', Submission.HasEssBox P (Submission.shrinkFactor * r) c' σ' := by
  obtain ⟨γ, hγ, hmem⟩ := h
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hspec : Submission.b * (s + ε) + |u + ε| / 2 ≤ Submission.shrinkFactor * r :=
    halfBox_spec hε0 hε8
  have hu' : |u + ε| < Submission.boxSide 2 * (s + ε) :=
    abs_shift_lt_boxSide_two_mul hr hrs hu hε0
  exact ⟨_, _, γ, hγ, fun t => Submission.PBox_mono hspec (by
    obtain ⟨x, hx, hd⟩ := mem_thickening_iff.mp (hmem t)
    have hxP : x ∈ Submission.PBox s c σ := hx.1.2
    have hxlt : x (σ 2) < c (σ 2) + u := hx.2
    have hdx : ‖γ t - x‖ < ε := by rw [← dist_eq_norm]; exact hd
    have h1 : γ t ∈ Submission.PBox (s + ε) c σ := mem_PBox_add_of_norm_sub_lt hε0 hxP hdx
    have h2 : |γ t (σ 2) - x (σ 2)| ≤ ‖γ t - x‖ := PiLp.norm_apply_le (p := 2) (γ t - x) (σ 2)
    have h3 : γ t (σ 2) - x (σ 2) ≤ |γ t (σ 2) - x (σ 2)| := le_abs_self _
    have h4 : γ t (σ 2) < c (σ 2) + (u + ε) := by linarith
    exact Work.BoxShrink.halfBox_upper_subset_perm (s + ε) (u + ε) (by linarith) hu' c σ ⟨h1, h4⟩)⟩

/-- **The conversion lemma, "above the plane" half.** -/
theorem hasEssBox_of_thickening_upperRegion {P : Work.CoreTopology.ParamTorus} {r s u ε : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) (hε : 0 < ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2))
    (h : ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ t ∈ thickening ε
        (Work.BoxShrink.Core.upperRegion P s c σ u)) :
    ∃ c' σ', Submission.HasEssBox P (Submission.shrinkFactor * r) c' σ' := by
  obtain ⟨γ, hγ, hmem⟩ := h
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hspec : Submission.b * (s + ε) + |u - ε| / 2 ≤ Submission.shrinkFactor * r :=
    halfBox_spec' hε0 hε8
  have hu' : |u - ε| < Submission.boxSide 2 * (s + ε) :=
    abs_sub_lt_boxSide_two_mul hr hrs hu hε0
  exact ⟨_, _, γ, hγ, fun t => Submission.PBox_mono hspec (by
    obtain ⟨x, hx, hd⟩ := mem_thickening_iff.mp (hmem t)
    have hxP : x ∈ Submission.PBox s c σ := hx.1.2
    have hxlt : c (σ 2) + u < x (σ 2) := hx.2
    have hdx : ‖γ t - x‖ < ε := by rw [← dist_eq_norm]; exact hd
    have h1 : γ t ∈ Submission.PBox (s + ε) c σ := mem_PBox_add_of_norm_sub_lt hε0 hxP hdx
    have h2 : |γ t (σ 2) - x (σ 2)| ≤ ‖γ t - x‖ := PiLp.norm_apply_le (p := 2) (γ t - x) (σ 2)
    have h3 : -(γ t (σ 2) - x (σ 2)) ≤ |γ t (σ 2) - x (σ 2)| := neg_le_abs _
    have h4 : c (σ 2) + (u - ε) < γ t (σ 2) := by linarith
    exact Work.BoxShrink.halfBox_lower_subset_perm (s + ε) (u - ε) (by linarith) hu' c σ ⟨h1, h4⟩)⟩

/-- **The ε-form in Pardon's *solid* form.**  Pardon's `doublebubble2` concludes that
`F ∩ (B(ε) + int(H_i))` has a component of genus `g`, i.e. it produces an essential loop of `F`
whose points are within `ε` of the *solid* half-box `int(H_i)` — not necessarily within `ε` of the
trace `F ∩ int(H_i)`.  This is therefore the honest, faithful form of the conclusion; it is
(logically) *weaker* than `CountingHalfEps`, which demands closeness to the trace, and it is what
a formalisation of Pardon's perturbation argument naturally produces.

For the box/plane configuration the solid half `int(H_i)` meets `PBox s c σ` in the half-box
`{y ∈ PBox s c σ | y (σ 2) ≶ c (σ 2) + u}`, so the conclusion is the existence of an essential loop
all of whose points lie within `ε` of one of those two half-*boxes*. -/
def CountingHalfEpsBody : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsW (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∀ ε : ℝ, 0 < ε →
            (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
                Work.CoreTopology.IsEssential _ γ ∧
                  ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧
                    x (σ 2) < c (σ 2) + u ∧ dist (γ t) x < ε) ∨
            (∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
                Work.CoreTopology.IsEssential _ γ ∧
                  ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧
                    c (σ 2) + u < x (σ 2) ∧ dist (γ t) x < ε)

/-- **The trace-form gives the solid-form**: a point within `ε` of the trace `F ∩ int(H_i)` is
within `ε` of the solid `int(H_i)`. -/
theorem countingHalfEpsBody_of_countingHalfEps (h : CountingHalfEps) : CountingHalfEpsBody := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
      ε hε with ⟨γ, hγ, hm⟩ | ⟨γ, hγ, hm⟩
  · exact Or.inl ⟨γ, hγ, fun t => by
      obtain ⟨x, hx, hd⟩ := mem_thickening_iff.mp (hm t)
      exact ⟨x, hx.1.2, hx.2, hd⟩⟩
  · exact Or.inr ⟨γ, hγ, fun t => by
      obtain ⟨x, hx, hd⟩ := mem_thickening_iff.mp (hm t)
      exact ⟨x, hx.1.2, hx.2, hd⟩⟩

/-- **The conversion lemma, "below the plane" half, in the solid form**: an essential loop whose
points are within `ε` of the half-*box* `{y ∈ PBox s c σ | y (σ 2) < c (σ 2) + u}` fits in a box of
size `shrinkFactor * r`. -/
theorem hasEssBox_of_body_thickening_lower {P : Work.CoreTopology.ParamTorus} {r s u ε : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) (hε : 0 < ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2))
    (h : ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ x (σ 2) < c (σ 2) + u ∧
        dist (γ t) x < ε) :
    ∃ c' σ', Submission.HasEssBox P (Submission.shrinkFactor * r) c' σ' := by
  obtain ⟨γ, hγ, hmem⟩ := h
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hspec : Submission.b * (s + ε) + |u + ε| / 2 ≤ Submission.shrinkFactor * r :=
    halfBox_spec hε0 hε8
  have hu' : |u + ε| < Submission.boxSide 2 * (s + ε) :=
    abs_shift_lt_boxSide_two_mul hr hrs hu hε0
  exact ⟨_, _, γ, hγ, fun t => Submission.PBox_mono hspec (by
    obtain ⟨x, hxP, hxlt, hd⟩ := hmem t
    have hdx : ‖γ t - x‖ < ε := by rw [← dist_eq_norm]; exact hd
    have h1 : γ t ∈ Submission.PBox (s + ε) c σ := mem_PBox_add_of_norm_sub_lt hε0 hxP hdx
    have h2 : |γ t (σ 2) - x (σ 2)| ≤ ‖γ t - x‖ := PiLp.norm_apply_le (p := 2) (γ t - x) (σ 2)
    have h3 : γ t (σ 2) - x (σ 2) ≤ |γ t (σ 2) - x (σ 2)| := le_abs_self _
    have h4 : γ t (σ 2) < c (σ 2) + (u + ε) := by linarith
    exact Work.BoxShrink.halfBox_upper_subset_perm (s + ε) (u + ε) (by linarith) hu' c σ ⟨h1, h4⟩)⟩

/-- **The conversion lemma, "above the plane" half, in the solid form.** -/
theorem hasEssBox_of_body_thickening_upper {P : Work.CoreTopology.ParamTorus} {r s u ε : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} (hr : 0 < r) (hrs : r < s)
    (hs : s < (1 + Submission.eps) * r) (hu : |u| < Submission.eps * r) (hε : 0 < ε)
    (hε8 : 8 * ε ≤ Submission.shrinkFactor * r - (Submission.b * s + |u| / 2))
    (h : ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ c (σ 2) + u < x (σ 2) ∧
        dist (γ t) x < ε) :
    ∃ c' σ', Submission.HasEssBox P (Submission.shrinkFactor * r) c' σ' := by
  obtain ⟨γ, hγ, hmem⟩ := h
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hspec : Submission.b * (s + ε) + |u - ε| / 2 ≤ Submission.shrinkFactor * r :=
    halfBox_spec' hε0 hε8
  have hu' : |u - ε| < Submission.boxSide 2 * (s + ε) :=
    abs_sub_lt_boxSide_two_mul hr hrs hu hε0
  exact ⟨_, _, γ, hγ, fun t => Submission.PBox_mono hspec (by
    obtain ⟨x, hxP, hxlt, hd⟩ := hmem t
    have hdx : ‖γ t - x‖ < ε := by rw [← dist_eq_norm]; exact hd
    have h1 : γ t ∈ Submission.PBox (s + ε) c σ := mem_PBox_add_of_norm_sub_lt hε0 hxP hdx
    have h2 : |γ t (σ 2) - x (σ 2)| ≤ ‖γ t - x‖ := PiLp.norm_apply_le (p := 2) (γ t - x) (σ 2)
    have h3 : -(γ t (σ 2) - x (σ 2)) ≤ |γ t (σ 2) - x (σ 2)| := neg_le_abs _
    have h4 : c (σ 2) + (u - ε) < γ t (σ 2) := by linarith
    exact Work.BoxShrink.halfBox_lower_subset_perm (s + ε) (u - ε) (by linarith) hu' c σ ⟨h1, h4⟩)⟩


/-! ## The exact form implies the ε-forms

Pardon's Lemma 3 in its *exact* form (`Work.BoxShrink.Bubble.BubbleHalf`, i.e.
`Work.Drive.CountingHalfW`) is strictly stronger than the two ε-forms above: an essential loop that
already lies in a half-region lies in every one of its neighbourhoods.  These two implications
record that a proof of the exact form — the target of the counted machinery of
`Submission/Work/PinchCounted/` and `Submission/Work/PinchFinal/` — also discharges the ε-forms, and
hence the whole challenge. -/

/-- The exact form (`CountingHalfW`) gives the trace ε-form. -/
theorem countingHalfEps_of_countingHalfW (h : CountingHalfW) : CountingHalfEps := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  have hbox' : (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) :=
    Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    hbox' with hup | hlo
  · obtain ⟨γ, hγ, hm⟩ := hup
    exact Or.inr ⟨γ, hγ, fun t => Metric.self_subset_thickening hε _ (hm t)⟩
  · obtain ⟨γ, hγ, hm⟩ := hlo
    exact Or.inl ⟨γ, hγ, fun t => Metric.self_subset_thickening hε _ (hm t)⟩

/-- The exact form (`CountingHalfW`) gives the solid ε-form. -/
theorem countingHalfEpsBody_of_countingHalfW (h : CountingHalfW) : CountingHalfEpsBody :=
  countingHalfEpsBody_of_countingHalfEps (countingHalfEps_of_countingHalfW h)


end Work.Drive
