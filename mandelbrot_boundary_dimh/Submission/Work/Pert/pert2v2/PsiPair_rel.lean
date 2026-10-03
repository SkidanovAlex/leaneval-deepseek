import Mathlib
import Submission.Work.Pert.Gates

namespace Work.Pert.pert2v2

open Set

/-- The composition `ΨE (Tt α ·) - d` of a Fatou coordinate on the lower gate with the deck
translation is again a Fatou coordinate on the upper gate: the translation maps `Qp` into `Qm`,
commutes with `F`, and `F` maps the translate back into `Qm`. -/
theorem psi_transport_isFatouCoordOn {F ΨE : ℂ → ℂ} {Ξ : ℝ} {α d : ℂ}
    (hE : MandelDim.IsFatouCoordOn F ΨE (Work.Pert.Qm Ξ α))
    (hcomm : ∀ z : ℂ, F (Work.Pert.Tt α z) = Work.Pert.Tt α (F z))
    (hTt : ∀ z : ℂ, z ∈ Work.Pert.Qp Ξ α → Work.Pert.Tt α z ∈ Work.Pert.Qm Ξ α)
    (hFtt : ∀ z : ℂ, z ∈ Work.Pert.Qp Ξ α → F z ∈ Work.Pert.Qp Ξ α →
      F (Work.Pert.Tt α z) ∈ Work.Pert.Qm Ξ α) :
    MandelDim.IsFatouCoordOn F (fun z => ΨE (Work.Pert.Tt α z) - d) (Work.Pert.Qp Ξ α) := by
  have hTtdiff : DifferentiableOn ℂ (Work.Pert.Tt α) (Work.Pert.Qp Ξ α) := by
    show DifferentiableOn ℂ (fun w : ℂ => w - 1 / α) (Work.Pert.Qp Ξ α)
    exact (differentiableOn_id (𝕜 := ℂ) (s := Work.Pert.Qp Ξ α)).sub_const (1 / α)
  refine ⟨?_, ?_, ?_⟩
  · have hcomp : DifferentiableOn ℂ (fun z => ΨE (Work.Pert.Tt α z)) (Work.Pert.Qp Ξ α) :=
      hE.1.comp hTtdiff (fun z hz => hTt z hz)
    exact hcomp.sub_const d
  · intro z hz w hw hzw
    have h1 : ΨE (Work.Pert.Tt α z) = ΨE (Work.Pert.Tt α w) := by
      have h := congrArg (fun t : ℂ => t + d) hzw
      simpa using h
    have h2 : Work.Pert.Tt α z = Work.Pert.Tt α w :=
      hE.2.1 (hTt z hz) (hTt w hw) h1
    have h3 : z - 1 / α = w - 1 / α := by simpa [Work.Pert.Tt] using h2
    have h := congrArg (fun t : ℂ => t + 1 / α) h3
    simpa using h
  · intro z hz hFz
    have hEorb := hE.2.2 (Work.Pert.Tt α z) (hTt z hz) (hFtt z hz hFz)
    have h1 : ΨE (Work.Pert.Tt α (F z)) - d = ΨE (F (Work.Pert.Tt α z)) - d := by
      rw [hcomm z]
    change ΨE (Work.Pert.Tt α (F z)) - d = ΨE (Work.Pert.Tt α z) - d + 1
    rw [h1, hEorb]
    ring

theorem PsiPair_rel {F ΨE Ψp : ℂ → ℂ} {Ξ : ℝ} {α d : ℂ} {z₀ : ℂ}
    (hUn : MandelDim.FatouUnique)
    (hadm : MandelDim.QAdm (some (Ξ : ℂ)) (some (-(Ξ : ℂ) + 1 / α)))
    (hNT : MandelDim.NearTranslationOn F (Work.Pert.Qp Ξ α))
    (hE : MandelDim.IsFatouCoordOn F ΨE (Work.Pert.Qm Ξ α))
    (hP : MandelDim.IsFatouCoordOn F Ψp (Work.Pert.Qp Ξ α))
    (hcomm : ∀ z : ℂ, F (Work.Pert.Tt α z) = Work.Pert.Tt α (F z))
    (hTt : ∀ z : ℂ, z ∈ Work.Pert.Qp Ξ α → Work.Pert.Tt α z ∈ Work.Pert.Qm Ξ α)
    (hFtt : ∀ z : ℂ, z ∈ Work.Pert.Qp Ξ α → F z ∈ Work.Pert.Qp Ξ α →
      F (Work.Pert.Tt α z) ∈ Work.Pert.Qm Ξ α)
    (hz₀ : z₀ ∈ Work.Pert.Qp Ξ α)
    (hnorm : Ψp z₀ = ΨE (Work.Pert.Tt α z₀) - d) :
    ∀ z ∈ Work.Pert.Qp Ξ α, Ψp z = ΨE (Work.Pert.Tt α z) - d := by
  have hΨ' : MandelDim.IsFatouCoordOn F (fun z => ΨE (Work.Pert.Tt α z) - d)
      (Work.Pert.Qp Ξ α) := psi_transport_isFatouCoordOn (d := d) hE hcomm hTt hFtt
  obtain ⟨c, hc⟩ := hUn (some (Ξ : ℂ)) (some (-(Ξ : ℂ) + 1 / α)) F Ψp
      (fun z => ΨE (Work.Pert.Tt α z) - d)
      hadm (by simpa only [Work.Pert.Qp] using hNT)
      (by simpa only [Work.Pert.Qp] using hP)
      (by simpa only [Work.Pert.Qp] using hΨ')
  have hcz : c = 0 := by
    have h2 := hc z₀ (by simpa only [Work.Pert.Qp] using hz₀)
    rw [hnorm] at h2
    have h := congrArg (fun t : ℂ => t - (ΨE (Work.Pert.Tt α z₀) - d)) h2
    simpa using h.symm
  intro z hz
  have h2 := hc z (by simpa only [Work.Pert.Qp] using hz)
  rw [hcz, add_zero] at h2
  exact h2.symm

end Work.Pert.pert2v2
