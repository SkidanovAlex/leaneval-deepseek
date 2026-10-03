import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Setup
import Submission.Work.Fatou.DevH.basic
import Submission.Work.Fatou.DevH.global
import Submission.Work.Fatou.DevH.devH_deriv
import Submission.Work.Fatou.Surface.Core
import Submission.Work.Fatou.Surface.Manifold
import Submission.Work.Fatou.Surface.devH_fundStrip
import Submission.Work.Fatou.Surface.Deck

/-!
# FX8, step 1: the orbit projection `Π` and the constructed Fatou coordinate `Φ = Ψ ∘ Π / b`

This file sets up the objects used by the FX8 construction of the Fatou coordinate on
`Qreg b₁ b₂` from the uniformizing biholomorphism `Ψ : XF D ≃ₘ ℂ` (see
`Submission/Work/Fatou/Surface/Core.lean` for `XF`) and the orbit coordinate
`(rep, lev)` supplied by `Work.Fatou.Surface.orbitCoord` (packaged here as `OrbitData`).

* `canonParam hadm hF s` is the (unique) `ζ` with `0 ≤ Re ζ < 1` and `devH ζ = s`, for `s` in the
  fundamental strip (`Work.Fatou.Surface.devH_fundStrip` gives existence; injectivity of `devH`
  makes it unique).
* `Pi od z = canonParam (rep z) + lev z`, the orbit projection, as a complex number.
* `Phi Ψ b z = Ψ (ofℂ (Pi z)) / b`, the Fatou coordinate (for `b ≠ 0` the deck shift of `Ψ`).

The basic identities are recorded here: `Pi_apply_fundStrip` (on the fundamental strip `Π` is the
canonical parameter), `Pi_F` (`Π (F z) = Π z + 1`) and `Phi_abel` (the Abel equation
`Φ (F z) = Φ z + 1`).
-/

namespace Work.Fatou.FX8

open MandelDim Set Metric Complex
open scoped Topology Manifold ContDiff
open LeanEval.Geometry
open Classical

noncomputable section

/-- Orbit-coordinate data for a near-translation on an admissible region: the fundamental-strip
representative `rep` of a point of `Qreg b₁ b₂` and its integer level `lev`, with the properties
proved in `Work.Fatou.Surface.orbitCoord`. -/
structure OrbitData (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) where
  rep : ℂ → ℂ
  lev : ℂ → ℤ
  /-- The representative lies in the fundamental strip. -/
  rep_mem : ∀ z ∈ Qreg b₁ b₂, rep z ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂)
  /-- A point of the fundamental strip is its own representative, of level `0`. -/
  rep_self : ∀ z ∈ Qreg b₁ b₂, z ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂) →
    rep z = z ∧ lev z = 0
  /-- One step of `F` (staying in `Qreg`) keeps the representative and raises the level by one. -/
  rep_step : ∀ z ∈ Qreg b₁ b₂, F z ∈ Qreg b₁ b₂ → rep (F z) = rep z ∧ lev (F z) = lev z + 1
  /-- `(rep, lev)` is injective on `Qreg b₁ b₂`. -/
  inj : ∀ z ∈ Qreg b₁ b₂, ∀ z' ∈ Qreg b₁ b₂, rep z = rep z' → lev z = lev z' → z = z'
  /-- Every point and its representative lie on a common orbit piece inside `Qreg b₁ b₂`. -/
  orbit : ∀ z ∈ Qreg b₁ b₂, ∃ k : ℕ,
    (F^[k] z = rep z ∧ ∀ j ≤ k, F^[j] z ∈ Qreg b₁ b₂) ∨
    (F^[k] (rep z) = z ∧ ∀ j ≤ k, F^[j] (rep z) ∈ Qreg b₁ b₂)

/-- The `FatouData` bundle (Riemann surface `XF`) attached to a near-translation. -/
def fatouData (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) : Work.Fatou.FatouData where
  b₁ := b₁
  b₂ := b₂
  F := F
  adm := hadm
  nt := hF
  devB := ⟨(Work.Fatou.DevH.devH_deriv hadm hF).1, (Work.Fatou.DevH.devH_deriv hadm hF).2.1⟩

theorem fatouData_F (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) : (fatouData b₁ b₂ F hadm hF).F = F := rfl

/-- The canonical parameter of a point of the fundamental strip: the unique `ζ` with
`0 ≤ Re ζ < 1` and `devH ζ = s`. -/
noncomputable def canonParam {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (s : ℂ) : ℂ :=
  if h : s ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂) then
    Classical.choose ((Work.Fatou.Surface.devH_fundStrip hadm hF).2.1 s h) else 0

/-- The defining properties of the canonical parameter on the fundamental strip. -/
theorem canonParam_spec {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) {s : ℂ}
    (h : s ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂)) :
    0 ≤ (canonParam hadm hF s).re ∧ (canonParam hadm hF s).re < 1 ∧
      Work.Fatou.devH (xOf b₁ b₂) F (canonParam hadm hF s) = s := by
  rw [canonParam, dif_pos h]
  exact Classical.choose_spec ((Work.Fatou.Surface.devH_fundStrip hadm hF).2.1 s h)

/-- `devH` realises the canonical parameter. -/
theorem devH_canonParam {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) {s : ℂ}
    (h : s ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂)) :
    Work.Fatou.devH (xOf b₁ b₂) F (canonParam hadm hF s) = s :=
  (canonParam_spec hadm hF h).2.2

/-- The canonical parameter is injective on the fundamental strip. -/
theorem canonParam_inj {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) {s s' : ℂ}
    (hs : s ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂))
    (hs' : s' ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂))
    (h : canonParam hadm hF s = canonParam hadm hF s') : s = s' := by
  rw [← devH_canonParam hadm hF hs, ← devH_canonParam hadm hF hs', h]

/-- **The orbit projection `Π`.** -/
def Pi {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (od : OrbitData b₁ b₂ F) (z : ℂ) : ℂ :=
  canonParam hadm hF (od.rep z) + (od.lev z : ℂ)

/-- **The constructed Fatou coordinate `Φ = Ψ ∘ Π / b`.** -/
def Phi {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    (b : ℂ) (z : ℂ) : ℂ :=
  Ψ ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z)) / b

theorem Phi_apply {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    (b z : ℂ) :
    Phi hadm hF od Ψ b z =
      Ψ ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z)) / b := rfl

/-- On the fundamental strip, `Π` is the canonical parameter. -/
theorem Pi_of_fundStrip {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (od : OrbitData b₁ b₂ F) {s : ℂ}
    (hs : s ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂)) :
    Pi hadm hF od s = canonParam hadm hF s := by
  obtain ⟨hrep, hlev⟩ := od.rep_self s hs.1 hs
  simp [Pi, hrep, hlev]

/-- **The key equivariance of `Π`:** one step of `F` (inside `Qreg`) adds `1`. -/
theorem Pi_F {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (od : OrbitData b₁ b₂ F) {z : ℂ}
    (hz : z ∈ Qreg b₁ b₂) (hzF : F z ∈ Qreg b₁ b₂) :
    Pi hadm hF od (F z) = Pi hadm hF od z + 1 := by
  obtain ⟨hrep, hlev⟩ := od.rep_step z hz hzF
  simp only [Pi, hrep, hlev]
  push_cast
  ring

/-- **The Abel equation** for the constructed coordinate. -/
theorem Phi_abel {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (od : OrbitData b₁ b₂ F)
    (Ψ : (fatouData b₁ b₂ F hadm hF).XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ)
    {b : ℂ} (hb : b ≠ 0) (hshift : ∀ u, Ψ ((fatouData b₁ b₂ F hadm hF).T u) = Ψ u + b)
    {z : ℂ} (hz : z ∈ Qreg b₁ b₂) (hzF : F z ∈ Qreg b₁ b₂) :
    Phi hadm hF od Ψ b (F z) = Phi hadm hF od Ψ b z + 1 := by
  have hT : (fatouData b₁ b₂ F hadm hF).T
      ((fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z))
      = (fatouData b₁ b₂ F hadm hF).ofℂ (Pi hadm hF od z + 1) := rfl
  rw [Phi_apply, Phi_apply, Pi_F hadm hF od hz hzF]
  rw [← hT, hshift]
  field_simp

end

end Work.Fatou.FX8
