import Submission.Work.Fatou.FX8.Analytic
import Submission.Work.Fatou.Constructed
import Submission.Work.Fatou.Surface.Uniformize
import Submission.Work.Fatou.Surface.Deck
import Submission.Work.Fatou.Analysis.injEntireTranslation
import Submission.Work.Fatou.Analysis.qcLiouville
import Submission.Work.Fatou.Surface.orbitCoord
import Submission.Work.Fatou.Surface.noHalfPlane

/-!
# FX8, step 6: the Fatou coordinate of a near-translation on `Qreg`

Assembling the pieces: given the orbit coordinate `(rep, lev)` on `Qreg b₁ b₂`, the uniformization
of the Écalle cylinder `XF` (`UniformizationHyp`, with the upper half-plane case excluded), and the
resulting deck shift `b ≠ 0`, the map `Φ = Ψ ∘ Π / b` is a Fatou coordinate, surjective modulo `ℤ`
and with the orbit relation: `HasFatouCoordOrbit`.
-/

namespace Work.Fatou.FX8

open MandelDim Set Metric Complex
open scoped Topology Manifold ContDiff
open LeanEval.Geometry
open Classical

noncomputable section

open Work.Fatou

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}

/-- **FX8 output**: from an orbit coordinate and the uniformization of `XF`, the constructed
coordinate `Φ = Ψ ∘ Π / b`. -/
theorem hasFatouCoordOrbit_of_orbitData (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (od : OrbitData b₁ b₂ F)
    (hU : UniformizationHyp)
    (hnp : ∀ D : Work.Fatou.FatouData,
      ¬ Nonempty (D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) :
    HasFatouCoordOrbit b₁ b₂ F := by
  obtain ⟨Ψ⟩ := exists_diffeomorph_plane hU hnp (fatouData b₁ b₂ F hadm hF)
  obtain ⟨b, hb, hshift⟩ :=
    exists_deck_shift Work.Fatou.Analysis.injEntireTranslation (fatouData b₁ b₂ F hadm hF) Ψ
  refine ⟨Phi hadm hF od Ψ b, ?_, ?_, ?_⟩
  · exact ⟨differentiableOn_Phi hadm hF od Ψ hb hshift,
      fun z hz z' hz' h => Phi_inj hb hadm hF od Ψ hz hz' h,
      fun z hz hzF => Phi_abel hadm hF od Ψ hb hshift hz hzF⟩
  · exact fun w => exists_Phi hadm hF od Ψ hshift hb w
  · exact fun z hz z' hz' k h => Phi_orbit hadm hF od Ψ hshift hb hz hz' k h

/-- The orbit-coordinate data, as an existential statement (this is the conclusion of
`Work.Fatou.Surface.orbitCoord`). -/
def OrbitCoordExists (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) : Prop :=
  Nonempty (OrbitData b₁ b₂ F)

/-- **FX8 for a single near-translation**, given the orbit coordinate as a hypothesis. -/
theorem hasFatouCoordOrbit_of_orbitCoordExists (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) (hoc : OrbitCoordExists b₁ b₂ F hadm hF)
    (hU : UniformizationHyp)
    (hnp : ∀ D : Work.Fatou.FatouData,
      ¬ Nonempty (D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) :
    HasFatouCoordOrbit b₁ b₂ F :=
  hasFatouCoordOrbit_of_orbitData hadm hF hoc.some hU hnp

/-- **`FatouConstructed`**, assuming the orbit coordinate and the exclusion of the upper
half-plane case. -/
theorem fatouConstructed_of (hU : UniformizationHyp)
    (hoc : ∀ (b₁ b₂ : Option ℂ) (F : ℂ → ℂ) (hadm : QAdm b₁ b₂)
      (hF : NearTranslationOn F (Qreg b₁ b₂)), OrbitCoordExists b₁ b₂ F hadm hF)
    (hnp : ∀ D : Work.Fatou.FatouData,
      ¬ Nonempty (D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane)) :
    FatouConstructed :=
  fun b₁ b₂ F hadm hF => hasFatouCoordOrbit_of_orbitCoordExists hadm hF (hoc b₁ b₂ F hadm hF) hU hnp

/-- **A.2.1(i) for arbitrary Fatou coordinates**, from `FatouConstructed` and uniqueness. -/
theorem fatouOrbit_of_constructed (hC : FatouConstructed) (hU : MandelDim.FatouUnique) :
    MandelDim.FatouOrbit := by
  intro b₁ b₂ F Φ hadm hNT hΦ z hz z' hz' k h
  obtain ⟨Φ₀, hΦ₀, -, horb⟩ := hC b₁ b₂ F hadm hNT
  obtain ⟨c, hc⟩ := hU b₁ b₂ F Φ Φ₀ hadm hNT hΦ hΦ₀
  have h' : Φ₀ z' = Φ₀ z + (k : ℂ) := by
    calc Φ₀ z' = Φ z' + c := hc z' hz'
      _ = (Φ z + (k : ℂ)) + c := by rw [h]
      _ = (Φ z + c) + (k : ℂ) := by ring
      _ = Φ₀ z + (k : ℂ) := by rw [← hc z hz]
  exact horb z hz z' hz' k h'

/-- The orbit coordinate exists for every admissible near-translation (Shishikura A.2.1(i)). -/
theorem orbitCoordExists {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) : OrbitCoordExists b₁ b₂ F hadm hF := by
  obtain ⟨rep, lev, h1, h2, h3, h4, h5⟩ :=
    Work.Fatou.Surface.orbitCoord hadm hF (Work.Fatou.xOf_gt_left hadm)
      (Work.Fatou.xOf_lt_right hadm)
  exact ⟨⟨rep, lev, h1, h2, h3, h4, h5⟩⟩

/-- **FX8**: `FatouConstructed` from the uniformization hypothesis. -/
theorem fatouConstructed (hU : UniformizationHyp) : FatouConstructed :=
  fatouConstructed_of hU (fun b₁ b₂ F hadm hF => orbitCoordExists hadm hF)
    (fun D => Work.Fatou.Surface.noHalfPlane Work.Fatou.Analysis.qcLiouville D)

/-- The existence conjunct of the FATOU contract. -/
theorem fatouExists (hU : UniformizationHyp) : MandelDim.FatouExists :=
  fatouExists_of_constructed (fatouConstructed hU)

end

end Work.Fatou.FX8
