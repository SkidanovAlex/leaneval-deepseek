import Mathlib
import Submission.Work.Pert.pert2v2.exists_Psi_lower
import Submission.Work.Pert.pert2v2.Psi_Xc_constant
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Interfaces.Fatou

/-!
# `Work.Pert.pert2v2.Psi_Xc_fatouUnique` — L-A3 as a `FatouUnique` statement

`Submission/Work/Pert/NOTES_pert2v2_session30.md` §2: the paper's identification
`Phi_{+,0} ∘ Phi_{-,0}^{-1} = tilde E_{f_0} = d.E` (`hdimB.tex` 340–345) is equivalent, in the
formalisation, to

  `Ψ (Xc d u) = u + c`     (**L-A3**)

for every Fatou coordinate `Ψ` of `F₀ = τ₀ ∘ f₀ ∘ τ₀` on the left cone (`exists_Psi_lower`), where
`Xc d u = τ₀ (d.φ u)` is the datum's curve.

The point of this file: **`u ↦ Ψ (Xc d u)` is a Fatou coordinate of the translation `u ↦ u + 1`**
(`Xc_add_one'` gives the curve step, `Ψ`'s Abel clause gives the shift), and `id` is one too, so the
contract field `FatouUnique` produces the constant *for free* — no growth/Liouville argument is
needed (and none can work: `h = Ψ ∘ Xc d - id` is `1`-periodic but need not be bounded).

The only extra hypothesis is `InjOn (Ψ ∘ Xc d) Q`, i.e. (since `Ψ` is injective on the cone) the
datum-level fact that `Xc d` — equivalently `d.φ` — is injective on the chosen region, beyond the
`QLeft ξ₀` of `ParabData.φ_inj`.  See `NOTES_pert2v2_session30.md` §2 and §4 row R2.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- **The `FatouUnique` step of L-A3.**  For any admissible region `Qreg B₁ B₂` on which the curve
steps are legal (`hsub`), on which `Ψ ∘ Xc d` is injective, and on which `Xc d` maps into the cone
where `Ψ` is a Fatou coordinate, the composite `Ψ ∘ Xc d` agrees with `id` up to a constant. -/
theorem Psi_Xc_const_of_inj {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) {Ξ' : ℝ} (hΞ' : 0 < Ξ') {Ψ : ℂ → ℂ}
    (hΨ : MandelDim.IsFatouCoordOn (Work.Pert.F0f f₀) Ψ
      (MandelDim.Qreg none (some (-(Ξ' : ℂ)))))
    {B₁ B₂ : Option ℂ} (hQ : MandelDim.QAdm B₁ B₂)
    (hsub : MandelDim.Qreg B₁ B₂ ⊆ {u : ℂ | u ∈ d.Dφ ∧ u + 1 ∈ d.Dφ ∧
      Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) ∧
      Work.Pert.F0f f₀ (Work.Pert.Xc d u) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))})
    (hinj : Set.InjOn (fun u : ℂ => Ψ (Work.Pert.Xc d u)) (MandelDim.Qreg B₁ B₂)) :
    ∃ c : ℂ, ∀ u : ℂ, u ∈ MandelDim.Qreg B₁ B₂ → Ψ (Work.Pert.Xc d u) = u + c := by
  classical
  -- the two cones of `hsub`, as membership lemmas
  have hcone : ∀ u ∈ MandelDim.Qreg B₁ B₂,
      Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) ∧
      Work.Pert.F0f f₀ (Work.Pert.Xc d u) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) :=
    fun u hu => ⟨(hsub hu).2.2.1, (hsub hu).2.2.2⟩
  -- `Xc d` is holomorphic where it is defined with nonvanishing value
  have hφne : ∀ u ∈ MandelDim.Qreg B₁ B₂, d.φ u ≠ 0 := by
    intro u hu
    have hne := Xc_ne_zero_of_mem d hΞ' (hsub hu).2.2.1
    intro h0
    exact hne (by simp [Work.Pert.Xc, h0, MandelDim.tau0])
  have hXcdiff : DifferentiableOn ℂ (Work.Pert.Xc d) (MandelDim.Qreg B₁ B₂) :=
    fun u hu => (differentiableAt_Xc d (hsub hu).1 (hφne u hu)).differentiableWithinAt
  have hmaps : Set.MapsTo (Work.Pert.Xc d) (MandelDim.Qreg B₁ B₂)
      (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :=
    fun u hu => (hcone u hu).1
  -- the translation, and the two Fatou coordinates
  have hcompt : DifferentiableOn ℂ (fun u : ℂ => Ψ (Work.Pert.Xc d u))
      (MandelDim.Qreg B₁ B₂) :=
    hΨ.1.comp hXcdiff hmaps
  have habelt : ∀ u ∈ MandelDim.Qreg B₁ B₂, (u + 1) ∈ MandelDim.Qreg B₁ B₂ →
      (fun u : ℂ => Ψ (Work.Pert.Xc d u)) (u + 1) = (fun u : ℂ => Ψ (Work.Pert.Xc d u)) u + 1 := by
    intro u hu hu1
    have hstep := Work.Pert.Xc_add_one d (hsub hu).1 (hsub hu).2.1
    show Ψ (Work.Pert.Xc d (u + 1)) = Ψ (Work.Pert.Xc d u) + 1
    rw [hstep]
    exact hΨ.2.2 (Work.Pert.Xc d u) (hcone u hu).1 (hcone u hu).2
  obtain ⟨c, hc⟩ := hF.2.2.1 B₁ B₂ (fun u : ℂ => u + 1) id (fun u : ℂ => Ψ (Work.Pert.Xc d u))
    hQ
    -- `NearTranslationOn (·+1) (Qreg B₁ B₂)`
    ⟨fun _ _ => (differentiableAt_id.add_const (1 : ℂ)).differentiableWithinAt,
      fun z _ => by
        constructor
        · simp
        · have : deriv (fun u : ℂ => u + 1) z = 1 := by simp
          simp [this]⟩
    -- `IsFatouCoordOn (·+1) id (Qreg B₁ B₂)`
    ⟨fun _ _ => differentiableAt_id.differentiableWithinAt, injOn_id _,
      fun z _ _ => rfl⟩
    -- `IsFatouCoordOn (·+1) (Ψ ∘ Xc d) (Qreg B₁ B₂)`
    ⟨hcompt, hinj, habelt⟩
  refine ⟨c, fun u hu => ?_⟩
  have hcu := hc u hu
  simpa using hcu

end

end Work.Pert.pert2v2
