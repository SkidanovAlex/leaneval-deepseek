import Mathlib
import Submission.Work.BasinSC.defs

namespace Work.Horn.HB

open Set Metric

/-- If `φ` and `ψ` are mutually inverse (on `V` resp. the unit disc) bijections
`V ↔ 𝔻` with `φ v = 0`, and both are continuous at the relevant points, then
`V \ {v}` is homeomorphic to the punctured unit disc. -/
theorem homeo_Vstar_puncturedDisc {V : Set ℂ} {v : ℂ} {φ ψ : ℂ → ℂ} (hvV : v ∈ V)
    (hφv : φ v = 0) (hφmaps : ∀ z ∈ V, φ z ∈ Metric.ball (0 : ℂ) 1)
    (hψmaps : ∀ w ∈ Metric.ball (0 : ℂ) 1, ψ w ∈ V)
    (hφψ : ∀ z ∈ V, ψ (φ z) = z) (hψφ : ∀ w ∈ Metric.ball (0 : ℂ) 1, φ (ψ w) = w)
    (hφcont : ∀ z ∈ V, ContinuousAt φ z) (hψcont : ∀ w ∈ Metric.ball (0 : ℂ) 1, ContinuousAt ψ w) :
    Nonempty (↥(V \ {v}) ≃ₜ ↥Work.BasinSC.puncturedDisc) := by
  -- `ψ 0 = v`
  have hψ0 : ψ 0 = v := by
    have h := hφψ v hvV
    rw [hφv] at h
    exact h
  -- points of the unit disc are in `Metric.ball 0 1`
  have hwball : ∀ w : ↥Work.BasinSC.puncturedDisc, w.1 ∈ Metric.ball (0 : ℂ) 1 := by
    intro w
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact w.2.2
  -- `φ` does not vanish on `V \ {v}`
  have hφ_ne : ∀ z : ↥(V \ {v}), φ z.1 ≠ 0 := by
    intro z hz
    have h1 : ψ (φ z.1) = z.1 := hφψ z.1 z.2.1
    rw [hz, hψ0] at h1
    exact z.2.2 (by simpa using h1.symm)
  -- `ψ` does not take the value `v` on the punctured disc
  have hψ_ne : ∀ w : ↥Work.BasinSC.puncturedDisc, ψ w.1 ≠ v := by
    intro w hw
    have h1 : φ (ψ w.1) = w.1 := hψφ w.1 (hwball w)
    rw [hw, hφv] at h1
    exact w.2.1 h1.symm
  -- the two component maps
  have hpin : ∀ z : ↥(V \ {v}), φ z.1 ∈ Work.BasinSC.puncturedDisc := by
    intro z
    rw [Work.BasinSC.mem_puncturedDisc]
    exact ⟨hφ_ne z, by simpa [Metric.mem_ball, dist_eq_norm] using hφmaps z.1 z.2.1⟩
  have hpin' : ∀ w : ↥Work.BasinSC.puncturedDisc, ψ w.1 ∈ V \ {v} := by
    intro w
    exact ⟨hψmaps w.1 (hwball w), fun h => hψ_ne w (by simpa using h)⟩
  -- continuity of the component maps
  have hcontOn : ContinuousOn φ V := fun z hz => (hφcont z hz).continuousWithinAt
  have hφc : Continuous (fun z : ↥(V \ {v}) => φ z.1) :=
    (hcontOn.mono Set.sdiff_subset).domRestrict
  have hcontOnψ : ContinuousOn ψ (Metric.ball (0 : ℂ) 1) :=
    fun z hz => (hψcont z hz).continuousWithinAt
  have hsub : Work.BasinSC.puncturedDisc ⊆ Metric.ball (0 : ℂ) 1 := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact hw.2
  have hψc : Continuous (fun w : ↥Work.BasinSC.puncturedDisc => ψ w.1) :=
    (hcontOnψ.mono hsub).domRestrict
  -- assembly
  let toFun : ↥(V \ {v}) → ↥Work.BasinSC.puncturedDisc := fun z => ⟨φ z.1, hpin z⟩
  let invFun : ↥Work.BasinSC.puncturedDisc → ↥(V \ {v}) := fun w => ⟨ψ w.1, hpin' w⟩
  have hl : Function.LeftInverse invFun toFun := fun z => Subtype.ext (hφψ z.1 z.2.1)
  have hr : Function.RightInverse invFun toFun := fun w => Subtype.ext (hψφ w.1 (hwball w))
  have hct : Continuous toFun := Continuous.subtype_mk hφc hpin
  have hci : Continuous invFun := Continuous.subtype_mk hψc hpin'
  exact ⟨Homeomorph.mk (Equiv.mk toFun invFun hl hr) hct hci⟩

end Work.Horn.HB
