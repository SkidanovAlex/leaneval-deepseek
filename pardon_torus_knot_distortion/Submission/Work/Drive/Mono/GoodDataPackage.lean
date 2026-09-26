import Mathlib
import Submission.Work.Drive.Mono.DataPackage
import Submission.Work.Drive.Final.GoodSweepData2

/-!
# The package of the tilted sweep together with the pinch genericity

`Work.Drive.Mono.DataPackage` (`Mono/DataPackage.lean`) carries the hypotheses under which the
**field `(D)`** of the tilted sweep is analysed (the trace structure of the levels and Pardon's
dichotomy).  The **field `(L)`** — the no-jump at the exceptional levels, i.e. the `2`-surgery count
of Pardon's pinching family — is analysed by the (L) route on the bundle
`Work.Drive.Final.GoodSweepData2` (the event structure of the sweep, its face events and its triple
points, together with the genericity that makes the dents possible).

`Work.Drive.Mono.GoodDataPackage` below is the conjunction of the two: the data at which **both**
fields are available.  The interface

* `Work.Drive.Mono.dichotomy_of_goodDataPackage` — field `(D)` at such a datum;
* `Work.Drive.Mono.GoodNoJumpInput` — field `(L)` as a per-datum obligation at such a datum;
* `Work.Drive.Mono.tiltedSweepMonoAEG_of_goodGeom_and_noJump` — the assembly into
  `Work.Drive.Mono.TiltedSweepMonoAEG` (and hence `Work.Drive.Mono.CruxCoreWdAEG`, and hence the
  deliverable `Work.Drive.Mono.pardon_unconditional_mono`),

makes the deliverable close in one line as soon as the geometric obligation
`Work.Drive.Mono.GoodSweepGeomAEG` and the per-datum no-jump are supplied.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The data package together with the pinch genericity**: `Work.Drive.Mono.DataPackage` (field
`(D)`) and `Work.Drive.Final.GoodSweepData2` (the event structure and genericity of field `(L)`). -/
def GoodDataPackage (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ)
    (lam0 lam1 : ℝ) (p q : ℕ) : Prop :=
  DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q ∧
  Work.Drive.Final.GoodSweepData2 ψ K s c σ u v h R ℓ exc lam0 lam1

/-- **Field `(D)` at a datum with the pinch genericity.** -/
theorem dichotomy_of_goodDataPackage (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (hs : 0 < s) (hDP : GoodDataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q) :
    ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊤) :=
  dichotomy_of_dataPackage p q hp hq hc himg hcl hs hDP.1

/-- **Field `(L)` as a per-datum obligation at a datum with the pinch genericity.** -/
def GoodNoJumpInput (p q : ℕ) : Prop :=
  ∀ (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ),
    GoodDataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q →
    ∀ lam ∈ Set.Icc lam0 lam1,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ →
      ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤

/-- **The geometric obligation of the tilted-sweep route, with the pinch genericity.** -/
def GoodSweepGeomAEG (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        BoxGen ψ c σ s →
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
        ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          |u| < Submission.eps * r →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
            GoodDataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q

/-- **The assembly of the tilted sweep at a datum carrying both genericity bundles.** -/
theorem tiltedSweepMonoAEG_of_goodGeom_and_noJump (hGeom : ∀ p q : ℕ, GoodSweepGeomAEG p q)
    (hNoJump : ∀ p q : ℕ, GoodNoJumpInput p q) :
    ∀ p q : ℕ, TiltedSweepMonoAEG p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  refine Filter.Eventually.mono
    (hGeom p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS) ?_
  intro u hdata hu hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hDP⟩ := hdata hu hU
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hDP.1.tilt
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hsize, hh, hRbox, hlow, hhigh, hl, hexc,
    dichotomy_of_goodDataPackage p q hp hq hc himg hcl (lt_trans hr hrs) hDP,
    hNoJump p q ψ K s u c σ v h R ℓ exc lam0 lam1 hDP⟩

/-- **The general-position crux from the two bundles** — the last mile of the deliverable
`Work.Drive.Mono.pardon_unconditional_mono`. -/
theorem cruxCoreWdAEG_of_goodSweepGeom_and_noJump (hGeom : ∀ p q : ℕ, GoodSweepGeomAEG p q)
    (hNoJump : ∀ p q : ℕ, GoodNoJumpInput p q) : ∀ p q : ℕ, CruxCoreWdAEG p q :=
  cruxCoreWdAEG_of_tiltedSweepMonoAEG (tiltedSweepMonoAEG_of_goodGeom_and_noJump hGeom hNoJump)

end

end Work.Drive.Mono
