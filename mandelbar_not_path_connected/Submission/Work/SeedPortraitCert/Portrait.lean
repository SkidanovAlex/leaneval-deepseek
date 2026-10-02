/-
# SeedPortraitCert — the mod-1 two-ray portrait of the seed from the two exclusions

Area `Submission/Work/SeedPortraitCert/`.  `Work.SeedSimple2.twoRays_of_inputs` derives the mod-1
portrait `Work.FSeed.LocalRayPortrait c z₁` from rotation number zero (`RN0`), the unlinked lemma
(`U`) and the statement `GF` that the `g`-fixed rays avoid the wake arc `(α₁, α₂)`; `GF` is used
there **only** at the two `g`-fixed angles `372/1023 = 12/33` and `403/1023 = 13/33` of the wake
arc.

This file replays that argument with `GF` replaced by the two *non-landing* facts
`¬ LandsN hN (12/33) z₁`, `¬ LandsN hN (13/33) z₁` — which is what the ray-chain certificate of
this area delivers.  The result is `twoRays_of_excl`; the bridge from the portrait to the exact
two-angle form required by the deliverable is `portrait_iff_of_localRayPortrait`.
-/
import Mathlib
import Submission.Work.SeedSimple2.TwoRays
import Submission.Work.SeedSimple2.COP.rotationZero_proved
import Submission.Work.SeedSimple2.UnlinkedBridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function
open scoped Topology

namespace Work.SeedPortraitCert

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.SeedSimple2

variable {c : ℂ}

/-! ## `GF` from the two exclusions

The body below is `Work.SeedSimple2.twoRays_of_inputs` with the two uses of `hGF` replaced by the
two non-landing hypotheses. -/

theorem twoRays_of_excl (d : Work.EL.RootParabolic c) (hJ : Work.Top.JordanForm)
    (hU : ∀ {a b a' b' : ℝ} {w w' : ℂ}, w ≠ w' →
      a ∈ Set.Ico 0 1 → b ∈ Set.Ico 0 1 → a' ∈ Set.Ico 0 1 → b' ∈ Set.Ico 0 1 →
      Work.EL.LandsN d.hN a w → Work.EL.LandsN d.hN b w → Work.EL.LandsN d.hN a' w' →
      Work.EL.LandsN d.hN b' w' → PairwiseDistinct4 a b a' b' →
      Work.ELPull.Unlinked a b a' b')
    (hRN0 : ∀ θ ∈ LandAngles d.hN d.z₁, Int.fract (1024 * θ) = θ)
    (h372 : ¬ Work.EL.LandsN d.hN ((372 : ℝ) / 1023) d.z₁)
    (h403 : ¬ Work.EL.LandsN d.hN ((403 : ℝ) / 1023) d.z₁) :
    Work.FSeed.LocalRayPortrait c d.z₁ := by
  have hmem : ∀ θ : ℝ, Work.Landing.landsAt c θ d.z₁ → Int.fract θ ∈ LandAngles d.hN d.z₁ :=
    fun θ h => fract_mem_LandAngles d h
  have key : ∀ x : ℝ, x ∈ LandAngles d.hN d.z₁ → x = Work.EL.alpha1 ∨ x = Work.EL.alpha2 := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := eq_div_of_fract_1024 hx.1 (hRN0 x hx)
    have hθ₀ : Work.EL.LandsN d.hN ((j : ℝ) / 1023) d.z₁ := by
      rw [← hxj]
      exact hx.2
    have keyj : ((j : ℝ) / 1023 : ℝ) = Work.EL.alpha1 ∨ ((j : ℝ) / 1023 : ℝ) = Work.EL.alpha2 := by
      by_cases hjs : j ∈ survivors
      · simp only [survivors, Finset.mem_insert, Finset.mem_singleton] at hjs
        rcases hjs with h | h | h | h
        · subst h; exact Or.inl alpha1_div
        · subst h
          exfalso
          rw [hxj] at hx
          exact h372 hx.2
        · subst h
          exfalso
          rw [hxj] at hx
          exact h403 hx.2
        · subst h; exact Or.inr alpha2_div
      · exfalso
        have hcert := certB_of_not_survivor j hj hjs
        obtain ⟨i, k, hi, hk, hik, hlink⟩ := certB_imp j hcert
        obtain ⟨a, ha, b, hb, hab, e, he, f, hf, hef, huf⟩ :=
          linkedLevels_of_linkedLevelsB hlink
        exact linking_step d hJ hU hj hθ₀ hi hk hik ha hb hab he hf hef huf
    rw [hxj]
    exact keyj
  refine ⟨fun θ θ' θ'' hθ hθ' hθ'' => ?_⟩
  rcases key _ (hmem θ hθ) with h1 | h1 <;> rcases key _ (hmem θ' hθ') with h2 | h2 <;>
    rcases key _ (hmem θ'' hθ'') with h3 | h3 <;>
    simp only [h1, h2, h3] <;> tauto


/-! ## The portrait in the `Ico 0 1` form -/

/-- **The exact two-ray portrait from the mod-1 portrait.**  If at most two ray angles (mod `1`)
land at `z₁` and the two root rays do, then the angles in `[0,1)` landing at `z₁` are exactly
`α₁` and `α₂`. -/
theorem portrait_iff_of_localRayPortrait {z₁ : ℂ}
    (hp : Work.FSeed.LocalRayPortrait c z₁)
    (hrays : Work.Landing.landsAt c Work.EL.alpha1 z₁ ∧
      Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    ∀ θ ∈ Set.Ico (0 : ℝ) 1,
      (Work.Landing.landsAt c θ z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2) := by
  intro θ hθ
  have hθf : Int.fract θ = θ := Int.fract_eq_self.mpr hθ
  have ha1 : Int.fract Work.EL.alpha1 = Work.EL.alpha1 :=
    Int.fract_eq_self.mpr ⟨by norm_num [Work.EL.alpha1], by norm_num [Work.EL.alpha1]⟩
  have ha2 : Int.fract Work.EL.alpha2 = Work.EL.alpha2 :=
    Int.fract_eq_self.mpr ⟨by norm_num [Work.EL.alpha2], by norm_num [Work.EL.alpha2]⟩
  constructor
  · intro hθl
    have h := hp.two_rays θ Work.EL.alpha1 Work.EL.alpha2 hθl hrays.1 hrays.2
    rcases h with h | h | h
    · left
      rw [← hθf, h, ha1]
    · right
      rw [← hθf, h, ha2]
    · exfalso
      rw [ha1, ha2] at h
      norm_num [Work.EL.alpha1, Work.EL.alpha2] at h
  · rintro (rfl | rfl)
    · exact hrays.1
    · exact hrays.2

/-- **P3 of the wire note**: the `LandsN` form of the exact portrait, from the mod-1 portrait of
a root-parabolic bundle. -/
theorem hzero_of_localPortrait {c : ℂ} (d : Work.EL.RootParabolic c)
    (hp : Work.FSeed.LocalRayPortrait c d.z₁) :
    ∀ θ ∈ Set.Ico (0 : ℝ) 1,
      (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2) := by
  have h := portrait_iff_of_localRayPortrait hp d.rays
  intro θ hθ
  exact (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher θ d.z₁).trans (h θ hθ)

end Work.SeedPortraitCert
