import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperDefs
import Submission.Work.Drive.N2C.mobiusShape
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.saddleArcs
import Submission.Work.Drive.N2Lead.arcZ_re_strictMono

/-!
# The kit of the marked core of the twisted Möbius upper picture

The marked core (`Work.Drive.N2Lead.mobiusUpperCoreMarked`) is about the *marked* region of the
certificate: the disc `ball 0 (Dp + 5)` with centre `0` and ray the positive real axis.  Its three
rows are about the planar picture `proj2 ∘ mobiusTwisted`.

This file collects the *curve* vocabulary of that proof (no `sorry`, no manifolds):

* `polarPic r Dp εp ε` — the planar picture of the pushed, twisted **polar** point
  `r θ · e^{iθ}`: the polar angle `θ` is the natural parameter of the marked component of the anchor
  level (`S.C₀ (L.γ i t) = cE3 (r (Θ t) · e^{iΘ t})`);
* `upCurve ηs Dp εp ε` — the planar picture of the pushed, twisted **upper arc** point
  `arcZ ηs u` (the parameter `u` is the invariant `Im (Z ·)²`);
* `dnCurve ηs Dp εp ε` — the same for the **lower arc** point `star (arcZ ηs u)`.

The three curve families are related by
`polarPic r Dp εp ε (Θ (tauU u)) = upCurve ηs Dp εp ε u` and
`polarPic r Dp εp ε (Θ (tauL u)) = dnCurve ηs Dp εp ε u` on the pin interval (rows of `MobiusShape`),
which is how the curve rows of the three families are transferred to one another.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- **The planar picture of the polar point** `r θ · e^{iθ}`, pushed and twisted: the curve of the
marked component of the anchor level in polar-angle parametrisation. -/
def polarPic (r : ℝ → ℝ) (Dp εp ε : ℝ) : ℝ → ℂ :=
  fun θ => proj2 (pushY Dp εp 1 (twistX ε (-1)
    (Work.Drive.N2.cE3 (r θ * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)))))

/-- **The planar picture of the upper arc point** `arcZ ηs u`, pushed and twisted. -/
def upCurve (ηs Dp εp ε : ℝ) : ℝ → ℂ :=
  fun u => proj2 (pushY Dp εp 1 (twistX ε (-1) (Work.Drive.N2.cE3 (arcZ ηs u))))

/-- **The planar picture of the lower arc point** `star (arcZ ηs u)`, pushed and twisted. -/
def dnCurve (ηs Dp εp ε : ℝ) : ℝ → ℂ :=
  fun u => proj2 (pushY Dp εp 1 (twistX ε (-1) (Work.Drive.N2.cE3 (star (arcZ ηs u)))))

/-- The planar projection `v ↦ (v 0) + (v 1) i` as a continuous linear map (a local copy, so that
this module needs no extra import). -/
noncomputable def kitProjCLM : E3 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (⟨v 0, v 1⟩ : ℂ)
      map_add' := fun a b => by apply Complex.ext <;> simp
      map_smul' := fun c a => by apply Complex.ext <;> simp }

@[simp] lemma kitProjCLM_apply (v : E3) : kitProjCLM v = proj2 v := rfl

/-- The polar picture is smooth when the profile is. -/
theorem contDiff_polarPic {r : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (Dp εp ε : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polarPic r Dp εp ε) := by
  have hrC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => ((r θ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  have hexp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) := by
    apply Complex.contDiff_exp.comp
    exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul contDiff_const
  have hpolar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => ((r θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) :=
    hrC.mul hexp
  have htw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.Drive.N2Lead.E3 => Work.Drive.N2Lead.twistX ε (-1) z) :=
    Work.Drive.N2Lead.contDiff_twistX_fixed ε (-1)
  have hpush : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.Drive.N2Lead.E3 => Work.Drive.N2Lead.pushY Dp εp 1 z) :=
    (Work.Drive.N2Lead.contDiff_pushY Dp εp).comp (contDiff_const.prodMk contDiff_id)
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ =>
      Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (((r θ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I))))) :=
    hpush.comp (htw.comp (Work.Drive.N2.cE3.contDiff.comp hpolar))
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (r θ * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)))))) := by
    have h := kitProjCLM.contDiff.comp h1
    simpa only [Function.comp_def, kitProjCLM_apply] using h
  rw [show polarPic r Dp εp ε = (fun θ : ℝ => proj2 (Work.Drive.N2Lead.pushY Dp εp 1
      (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3
        (r θ * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)))))) from rfl]
  exact h2

/-- The polar picture is `2π`-periodic in the angle when the profile is. -/
theorem polarPic_add_two_pi {r : ℝ → ℝ} (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (Dp εp ε θ : ℝ) : polarPic r Dp εp ε (θ + 2 * Real.pi) = polarPic r Dp εp ε θ := by
  have hexp : Complex.exp ((((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    have h : (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  simp only [polarPic, hrper, hexp]

end

end Work.Drive.N2Lead
