import Mathlib
import Submission.Work.Pert.pert2v2.PhiMinusDef
import Submission.Work.Pert.nearTranslation_F0

/-!
# `Work.Pert.pert2v2.exists_Psi_lower` — the model **lower**-gate coordinate, from the FATOU contract

The model map of the germ at `α = 0` is `F₀ w = τ₀ (f₀ (τ₀ w))` (`τ₀ w = -1/w`).  This file proves
that `F₀` admits a Fatou coordinate on the whole **left** limit cone

  `Qreg none (some (-Ξ')) = {z | z.re + Ξ' < |z.im|}`

for every `Ξ'` above a datum-knee `ξ > 0`, directly from the FATOU area contract
`MandelDim.FatouStatement` (its existence field `FatouExists`, Shishikura A.2.1(ii)).  No inverse of
`d.φ` or of `d.E` is used anywhere — this is the `L-A1″` clause of
`Submission/Work/Pert/NOTES_pert2v2_session29.md` §8, chosen by the lead after
`Work.Pert.pert2v2.PhiMinus_fatou` (`(Xc d)⁻¹` is a Fatou coordinate of `F₀`) turned out to be false,
`d.φ` having non-trivial fibres.

The argument is short:

* `Work.Pert.nearTranslation_F0` (proved) gives `ξ > 0` with `NearTranslationOn F₀
  (Qreg none (some (-ξ)))` — the *bigger* cone;
* for `Ξ' ≥ ξ` the cone `Qreg none (some (-Ξ'))` is contained in it (`Qreg_left_mono`), and
  `NearTranslationOn` restricts to subsets (`DifferentiableOn.mono` plus the two pointwise clauses);
* the pair `(none, some (-Ξ'))` is admissible: `QAdm` quantifies over `b₁ = none`, so it is vacuous
  (`qAdm_none_left`);
* `FatouExists` then produces the coordinate (its second conjunct, the `ℤ`-saturation of the image,
  is discarded).
-/

namespace Work.Pert.pert2v2

open MandelDim

/-- Monotonicity of the left limit cone in its parameter: for `ξ ≤ Ξ'` the cone
`Qreg none (some (-Ξ')) = {z | z.re + Ξ' < |z.im|}` is contained in the bigger cone
`Qreg none (some (-ξ)) = {z | z.re + ξ < |z.im|}`. -/
theorem Qreg_left_mono {ξ Ξ' : ℝ} (h : ξ ≤ Ξ') :
    MandelDim.Qreg none (some (-(Ξ' : ℂ))) ⊆ MandelDim.Qreg none (some (-(ξ : ℂ))) := by
  intro z hz
  -- the defining inequality of the source cone, read at the vertex `b = -Ξ'`
  have hz' := hz.2 (-(Ξ' : ℂ)) (Option.mem_def.mpr rfl)
  simp only [sub_neg_eq_add] at hz'
  rw [show (z + (Ξ' : ℂ)).im = z.im by simp,
      show (z + (Ξ' : ℂ)).re = z.re + Ξ' by simp] at hz'
  refine ⟨fun b hb => absurd (Option.mem_def.mp hb) (by simp), fun b hb => ?_⟩
  -- the target cone has a single finite vertex, `b = -ξ`
  have hb' : b = -(ξ : ℂ) := by
    have h' := Option.mem_def.mp hb
    exact (Option.some.injEq _ _).mp h'.symm ▸ rfl
  subst hb'
  have : (z + (ξ : ℂ)).re < |(z + (ξ : ℂ)).im| := by
    rw [show (z + (ξ : ℂ)).im = z.im by simp,
        show (z + (ξ : ℂ)).re = z.re + ξ by simp]
    linarith
  simpa using this

/-- `QAdm` is vacuous when the left vertex is `-∞` (`b₁ = none`). -/
theorem qAdm_none_left (b : Option ℂ) : MandelDim.QAdm none b := by
  intro a ha _ _
  exact absurd (Option.mem_def.mp ha) (by simp)

/-- **The model lower-gate coordinate exists** (`L-A1″`): for every `Ξ'` above the datum knee the
map `F₀ w = τ₀ (f₀ (τ₀ w))` has a Fatou coordinate on `Qreg none (some (-Ξ'))`, by the FATOU
contract's `FatouExists` applied to the near translation of `Work.Pert.nearTranslation_F0`
restricted to the smaller cone. -/
theorem exists_Psi_lower {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' →
      ∃ Ψ : ℂ → ℂ,
        MandelDim.IsFatouCoordOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
          Ψ (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) := by
  -- `d` is not needed: the coordinate comes from the contract, not from the datum's `φ`
  have _ : 0 < d.ξ₀ := d.ξ₀_pos
  -- the near translation on the big left cone, and its knee
  obtain ⟨ξ, hξpos, -, hL, -⟩ := Work.Pert.nearTranslation_F0 hd
  refine ⟨ξ, hξpos, fun Ξ' hΞ' => ?_⟩
  have hsub := Qreg_left_mono hΞ'
  have hnt : MandelDim.NearTranslationOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
      (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :=
    ⟨hL.1.mono hsub, fun z hz => hL.2 z (hsub hz)⟩
  obtain ⟨Ψ, hΨ, -⟩ := hF.1 none (some (-(Ξ' : ℂ))) _ (qAdm_none_left _) hnt
  exact ⟨Ψ, hΨ⟩

end Work.Pert.pert2v2
