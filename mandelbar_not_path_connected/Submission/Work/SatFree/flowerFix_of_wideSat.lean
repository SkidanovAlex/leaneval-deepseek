/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SatFree team
-/
import Mathlib
import Submission.Work.SatFree.Defs
import Submission.Work.GATE2.Saturating
import Submission.Work.PARIMPL.Match

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `flowerFix_of_wideSat` — the `PARIMPL.FlowerFix` of a saturating flower

`Work.PARIMPL.FlowerFix d F G z₀ Pa φa` asks for an invariantly-defined half-petal
`Pg ⊆ Pa`, open, forward invariant for both `F` and `G`, and the Abel equation for `φa` on `Pa`.

The `GATE2` flowers obtain `Pg` as the *explicit* chart half-plane `HPlanePetal Mh`, which depends
on `φa` being computed on `Pg` (`φa z = fatouCoord f (1-a) z + s` there).  The sign-free
(`SatFree`) construction cannot use a chart half-plane — its petal is wide — so here `Pg` is
defined *from the saturation certificate* instead:

  `Pg := {z ∈ Pa | G z ∈ Pa ∧ X < (φa z).re}`.

This is open (`Pa` open, `φa` differentiable on `Pa`, `G` continuous), and **automatically
invariant** for both maps, using only the Abel equation on `Pa` and `G ∘ G = F`:

* `φa (F z) = φa z + 1` and `G (F z) = F (G z)`;
* `φa (G z) = star (φa z) + 1/2`, so `Re φa (G z) = Re φa z + 1/2`.

No preconnectedness or nonemptiness of `Pg` is required by `Work.PARIMPL.FlowerFix`; the
saturation certificate supplies the points of `Pg` when it is consumed
(`Work.GATE2.SaturatedFlower`).
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.SatFree

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The `PARIMPL.FlowerFix` attached to a saturating flower.**  Given a repaired flower `fl` of
`(Ft c₀, gtc c₀)` at `d.z₁` and a real threshold `X`, the half-petal
`Pg = {z ∈ fl.Pa | gtc c₀ z ∈ fl.Pa ∧ X < (fl.φa z).re}`
is open and invariant for both `Ft c₀` and `gtc c₀`, and the Abel equation is `fl.φa_shift`.

Combined with `Work.SatFree.SatHalfPlane gtc c₀ fl.Pa fl.φa` this yields
`Work.GATE2.SaturatedFlower` (see `SatFree.exists_saturated`). -/
noncomputable def flowerFix_of_wideSat {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (X : ℝ) :
    Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa where
  shift := fun z hz => fl.φa_shift z hz
  Pg := {z : ℂ | z ∈ fl.Pa ∧ Work.PARIMPL.gtc c₀ z ∈ fl.Pa ∧ X < (fl.φa z).re}
  Pg_sub := fun z hz => hz.1
  isOpen_Pg := by
    have hcont : ContinuousOn (fun z : ℂ => (fl.φa z).re) fl.Pa :=
      Complex.continuous_re.comp_continuousOn (fl.φa_fatou.1.2.1.continuousOn)
    have hB : IsOpen (fl.Pa ∩ {z : ℂ | X < (fl.φa z).re}) :=
      hcont.isOpen_inter_preimage fl.isOpen_Pa isOpen_Ioi
    have hC : IsOpen ((Work.PARIMPL.gtc c₀) ⁻¹' fl.Pa) :=
      fl.isOpen_Pa.preimage (Work.PARIMPL.gtc_continuous c₀)
    have hEq : {z : ℂ | z ∈ fl.Pa ∧ Work.PARIMPL.gtc c₀ z ∈ fl.Pa ∧ X < (fl.φa z).re}
        = (fl.Pa ∩ {z : ℂ | X < (fl.φa z).re}) ∩ ((Work.PARIMPL.gtc c₀) ⁻¹' fl.Pa) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [hEq]
    exact hB.inter hC
  mapsTo_F_Pg := by
    rintro z ⟨hzA, hzg, hzX⟩
    have hgg := Work.Final.Tantibar_five_comp_self c₀
    have h1 : Work.PARIMPL.gtc c₀ (Work.EL.F c₀ z) = Work.EL.F c₀ (Work.PARIMPL.gtc c₀ z) := by
      have h2 := congrFun hgg (Work.PARIMPL.gtc c₀ z)
      have h3 := congrFun hgg z
      simp only [Function.comp_apply] at h2 h3
      rw [← h3]; exact h2
    refine ⟨fl.mapsTo_Pa hzA, ?_, ?_⟩
    · rw [h1]; exact fl.mapsTo_Pa hzg
    · rw [fl.φa_shift z hzA, Complex.add_re, Complex.one_re]; linarith
  mapsTo_G_Pg := by
    rintro z ⟨hzA, hzg, hzX⟩
    have hgg := Work.Final.Tantibar_five_comp_self c₀
    have h1 : Work.PARIMPL.gtc c₀ (Work.PARIMPL.gtc c₀ z) = Work.EL.F c₀ z := by
      have h3 := congrFun hgg z
      simp only [Function.comp_apply] at h3
      exact h3
    have h2 := (fl.φa_fatou.1.2.2) z hzA
    have h3 : (fl.φa (Work.PARIMPL.gtc c₀ z)).re = (fl.φa z).re + 1 / 2 := by
      rw [h2, Complex.add_re, Complex.star_def, Complex.conj_re,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
    refine ⟨hzg, ?_, ?_⟩
    · rw [h1]; exact fl.mapsTo_Pa hzA
    · rw [h3]; linarith

/-- **`SatHalfPlane` gives the GATE2 saturation certificate for `flowerFix_of_wideSat`.**

`Work.GATE2.SaturatedFlower fl FF` is `∃ X, ∀ w, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w`, and the
half-petal of `flowerFix_of_wideSat d fl X` is exactly
`{z ∈ fl.Pa | gtc c₀ z ∈ fl.Pa ∧ X < (fl.φa z).re}`; so the certificate is the saturation
statement itself, with the *same* threshold `X`. -/
theorem saturatedFlower_of_satHalfPlane {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (X : ℝ)
    (hX : ∀ τ : ℂ, X < τ.re → ∃ z : ℂ, z ∈ fl.Pa ∧
      Work.PARIMPL.gtc c₀ z ∈ fl.Pa ∧ fl.φa z = τ) :
    Work.GATE2.SaturatedFlower fl.toParabolicFlower (flowerFix_of_wideSat d fl X) := by
  refine ⟨X, fun w hw => ?_⟩
  obtain ⟨z, hzA, hzg, hφ⟩ := hX w hw
  exact ⟨z, ⟨hzA, hzg, by rw [hφ]; exact hw⟩, hφ⟩

/-- **`SatHalfPlane` gives the GATE2 saturation certificate**, stated with the `∃ X` inside: the
form in which `SatFree.exists_saturated` consumes it. -/
theorem saturatedFlower_of_satHalfPlane' {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (h : SatHalfPlane (Work.PARIMPL.gtc c₀) fl.Pa fl.φa) :
    ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀)
        ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
      Work.GATE2.SaturatedFlower fl.toParabolicFlower FF := by
  obtain ⟨X, hX⟩ := h
  exact ⟨flowerFix_of_wideSat d fl X, saturatedFlower_of_satHalfPlane d fl X hX⟩

end

end Work.SatFree
