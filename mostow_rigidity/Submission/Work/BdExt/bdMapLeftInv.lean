import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.bdMapDetect
import Submission.Work.Mostow.BdExt.bdMapClose
import Submission.Work.Mostow.BdExt.rayBasic

/-!
# `bdMapLeftInv`: `bdMap` is a left inverse to `bdMap` of a coarse inverse

If `Ψ ∘ Φ` is at bounded distance `D` from the identity and both `Φ`, `Ψ` are quasi-isometries,
then on the boundary sphere

  `bdMap n Ψ (bdMap n Φ ξ) = ξ`.

The argument: put `η = bdMap n Φ ξ`.  The sequence `z k = Φ (ray ξ k)` has directions converging
to `η` (`bdMap_spec` for `Φ`) and level escaping to `∞` (`lvl_image_ray`), so the detection lemma
`bdMapDetect` applied to `Ψ` gives

  `dirv (Ψ (Φ (ray ξ k))) → bdMap n Ψ η`.

On the other hand `Ψ (Φ (ray ξ k))` stays within `D` of the ray `ray ξ k`, whose directions converge
to `ξ` and whose level escapes; `closeSeq` therefore gives `dirv (Ψ (Φ (ray ξ k))) → ξ`.  Uniqueness
of limits yields `bdMap n Ψ η = ξ`.
-/

namespace Work.BdExt

open Submission.Mostow Filter

theorem bdMapLeftInv (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ Ψ : Submission.Mostow.E n → Submission.Mostow.E n)
    (K₁ C₁ K₂ C₂ D : ℝ) (hK₁ : 1 ≤ K₁) (hC₁ : 0 ≤ C₁) (hK₂ : 1 ≤ K₂) (hC₂ : 0 ≤ C₂) (hD : 0 ≤ D)
    (hupΦ : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K₁ * Submission.Mostow.hdist u v + C₁)
    (hlowΦ : ∀ u v, Submission.Mostow.hdist u v ≤ K₁ * Submission.Mostow.hdist (Φ u) (Φ v) + C₁)
    (hupΨ : ∀ u v, Submission.Mostow.hdist (Ψ u) (Ψ v) ≤ K₂ * Submission.Mostow.hdist u v + C₂)
    (hlowΨ : ∀ u v, Submission.Mostow.hdist u v ≤ K₂ * Submission.Mostow.hdist (Ψ u) (Ψ v) + C₂)
    (hclose : ∀ u, Submission.Mostow.hdist (Ψ (Φ u)) u ≤ D)
    (hcontΨ : ContinuousOn (fun ξ : Submission.Mostow.E n => Work.Mostow.BdExt.bdMap n Ψ ξ)
      (Submission.Mostow.Sph n))
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) :
    Work.Mostow.BdExt.bdMap n Ψ (Work.Mostow.BdExt.bdMap n Φ ξ) = ξ := by
  set η := Work.Mostow.BdExt.bdMap n Φ ξ with hηdef
  obtain ⟨hηS, hlimΦ⟩ :=
    Work.Mostow.BdExt.bdMap_spec n hI Φ K₁ C₁ hK₁ hC₁ hupΦ hlowΦ ξ hξ
  have hlvlΦ :
      Tendsto (fun k : ℕ => Work.Mostow.BdExt.lvl (Φ (Work.Mostow.BdExt.ray ξ (k:ℝ)))) atTop atTop :=
    Work.Mostow.BdExt.tendsto_lvl_image_ray n hI Φ K₁ C₁ hK₁ hC₁ hlowΦ ξ hξ
  have hdet : Tendsto (fun k : ℕ => Work.Mostow.BdExt.dirv (Ψ (Φ (Work.Mostow.BdExt.ray ξ (k:ℝ)))))
      atTop (nhds (Work.Mostow.BdExt.bdMap n Ψ η)) :=
    Work.Mostow.BdExt.bdMapDetect n hI Ψ K₂ C₂ hK₂ hC₂ hupΨ hlowΨ hcontΨ
      (fun k : ℕ => Φ (Work.Mostow.BdExt.ray ξ (k:ℝ))) η hηS hlimΦ hlvlΦ
  have hclose' : ∀ k : ℕ,
      hdist (Work.Mostow.BdExt.ray ξ (k:ℝ)) (Ψ (Φ (Work.Mostow.BdExt.ray ξ (k:ℝ)))) ≤ D := by
    intro k
    rw [hI.2.1]
    exact hclose (Work.Mostow.BdExt.ray ξ (k:ℝ))
  have hlvlΨ : Tendsto (fun k : ℕ =>
      Work.Mostow.BdExt.lvl (Ψ (Φ (Work.Mostow.BdExt.ray ξ (k:ℝ))))) atTop atTop :=
    Work.Mostow.BdExt.tendsto_lvl_of_close_ray hI ξ hξ
      (fun k : ℕ => Ψ (Φ (Work.Mostow.BdExt.ray ξ (k:ℝ)))) D
      (fun k => hclose (Work.Mostow.BdExt.ray ξ (k:ℝ)))
  have hlimξ : Tendsto (fun k : ℕ =>
      Work.Mostow.BdExt.dirv (Ψ (Φ (Work.Mostow.BdExt.ray ξ (k:ℝ))))) atTop (nhds ξ) :=
    Work.Mostow.BdExt.closeSeq n hI (fun k : ℕ => Work.Mostow.BdExt.ray ξ (k:ℝ))
      (fun k : ℕ => Ψ (Φ (Work.Mostow.BdExt.ray ξ (k:ℝ)))) D hD hclose'
      (Work.Mostow.BdExt.tendsto_lvl_ray ξ hξ) hlvlΨ ξ (Work.Mostow.BdExt.tendsto_dirv_ray hI ξ hξ)
  exact tendsto_nhds_unique hdet hlimξ

end Work.BdExt
