import Submission.Work.DSM5c.ChartPresheaf

/-!
# DSM5c — the presheaf `Dp` of untilted perfected tilted charts

This file builds the object the frozen `DSMap.Mix2.area_M5c` asks for:

  `Dp : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W`,   `Dp S = untiltOf (R_S) φ_S`,

where `R_S = perfChartRing p (chartTiltGen Q t tr … j₀ e) S` is the perfected tilted chart and
`φ_S : PreTilt W p →+* R_S` its algebra structure (`Submission/Work/DSM5c/Charts.lean`).  The
functoriality is `Work.DSM5c.untiltOf.map` applied to the restriction maps `tiltChartRes`
(`Submission/Work/DSM5c/ChartPresheaf.lean`), and the fact that `Dp` lands in **`ModuleCat W`**
(rather than only in rings) is exactly `Work.DSM5c.untiltOf.map_algebraMap`.

The `W`-module structure on `untiltOf R φ` is the one induced by `untiltOf.algebraMap hθ φ`
(`hθ : Surjective (fontaineTheta W p)`, which for a `PerfectoidData p W` follows from `frobSurj` via
`WittVector.surjective_fontaineTheta`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section Laws

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
variable {ι : Type a} [DecidableEq ι]
variable (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
  (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)

/-- The restriction map of the identity inclusion is the identity. -/
theorem tiltChartRes_self {S : Finset ι} :
    tiltChartRes Q t tr htr0 htr j₀ e (subset_refl S) = RingHom.id _ := by
  refine RingHom.ext fun x => Subtype.ext ?_
  rw [tiltChartRes_coe]
  exact (congrArg (fun (f : Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S) →ₐ[PreTilt W p]
      Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S)) => f x.1)
    (locRes_eq (chartTiltGen Q t tr htr0 htr j₀ e) (subset_refl S)
      (AlgHom.id (PreTilt W p) _))).symm

/-- The restriction maps compose. -/
theorem tiltChartRes_comp {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V) :
    (tiltChartRes Q t tr htr0 htr j₀ e h₂).comp (tiltChartRes Q t tr htr0 htr j₀ e h₁) =
      tiltChartRes Q t tr htr0 htr j₀ e (h₁.trans h₂) := by
  refine RingHom.ext fun x => Subtype.ext ?_
  rw [RingHom.comp_apply, tiltChartRes_coe, tiltChartRes_coe, tiltChartRes_coe]
  exact (congrArg (fun (f : Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S) →ₐ[PreTilt W p]
      Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) V)) => f x.1)
    (locRes_eq (chartTiltGen Q t tr htr0 htr j₀ e) (h₁.trans h₂)
      ((locRes (chartTiltGen Q t tr htr0 htr j₀ e) h₂).comp
        (locRes (chartTiltGen Q t tr htr0 htr j₀ e) h₁))))

end Laws

section Presheaf

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
variable {ι : Type a} [DecidableEq ι]

/-- The algebra structure of the perfected tilted chart `R_S` over the tilt `PreTilt W p`. -/
noncomputable def chartPhi (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) : PreTilt W p →+* tiltChart Q t tr htr0 htr j₀ e S :=
  algebraMap (PreTilt W p) _

end Presheaf

end Work.DSM5c
