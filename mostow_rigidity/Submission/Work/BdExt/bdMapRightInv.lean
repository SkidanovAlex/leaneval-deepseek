import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.bdMapDetect
import Submission.Work.Mostow.BdExt.bdMapClose
import Submission.Work.Mostow.BdExt.rayBasic

namespace Work.BdExt

open Submission.Mostow Filter

/-- `bdMap` is a right inverse to `bdMap` for quasi-isometries that are inverse to one another up
to bounded distance.

Since `Φ ∘ Ψ` is at bounded distance from the identity, the directions of `Φ (Ψ (ray ξ k))`
converge to `ξ`.  On the other hand, `Ψ (ray ξ k)` is an escaping sequence converging to the
boundary point `bdMap n Ψ ξ`, so by `bdMapDetect` those same directions converge to
`bdMap n Φ (bdMap n Ψ ξ)`.  Uniqueness of limits gives the claim. -/
theorem bdMapRightInv (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ Ψ : Submission.Mostow.E n → Submission.Mostow.E n)
    (K₁ C₁ K₂ C₂ D : ℝ) (hK₁ : 1 ≤ K₁) (hC₁ : 0 ≤ C₁) (hK₂ : 1 ≤ K₂) (hC₂ : 0 ≤ C₂) (hD : 0 ≤ D)
    (hupΦ : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K₁ * Submission.Mostow.hdist u v + C₁)
    (hlowΦ : ∀ u v, Submission.Mostow.hdist u v ≤ K₁ * Submission.Mostow.hdist (Φ u) (Φ v) + C₁)
    (hupΨ : ∀ u v, Submission.Mostow.hdist (Ψ u) (Ψ v) ≤ K₂ * Submission.Mostow.hdist u v + C₂)
    (hlowΨ : ∀ u v, Submission.Mostow.hdist u v ≤ K₂ * Submission.Mostow.hdist (Ψ u) (Ψ v) + C₂)
    (hclose : ∀ u, Submission.Mostow.hdist (Φ (Ψ u)) u ≤ D)
    (hcontΦ : ContinuousOn (fun ξ : Submission.Mostow.E n => Work.Mostow.BdExt.bdMap n Φ ξ)
      (Submission.Mostow.Sph n))
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) :
    Work.Mostow.BdExt.bdMap n Φ (Work.Mostow.BdExt.bdMap n Ψ ξ) = ξ := by
  -- the boundary point `bdMap n Ψ ξ` and the fact that `Ψ ∘ ray ξ` converges to it
  obtain ⟨hΨξS, hΨlim⟩ :=
    Work.Mostow.BdExt.bdMap_spec n hI Ψ K₂ C₂ hK₂ hC₂ hupΨ hlowΨ ξ hξ
  -- `Ψ ∘ ray ξ` escapes to infinity in level
  have hΨlvl : Tendsto (fun k : ℕ => Work.Mostow.BdExt.lvl (Ψ (Work.Mostow.BdExt.ray ξ (k : ℝ))))
      atTop atTop :=
    Work.Mostow.BdExt.tendsto_lvl_image_ray n hI Ψ K₂ C₂ hK₂ hC₂ hlowΨ ξ hξ
  -- so `bdMapDetect` identifies the limit of the directions of `Φ (Ψ (ray ξ k))`
  have hlim₁ : Tendsto (fun k : ℕ => Work.Mostow.BdExt.dirv (Φ (Ψ (Work.Mostow.BdExt.ray ξ (k : ℝ)))))
      atTop (nhds (Work.Mostow.BdExt.bdMap n Φ (Work.Mostow.BdExt.bdMap n Ψ ξ))) :=
    Work.Mostow.BdExt.bdMapDetect n hI Φ K₁ C₁ hK₁ hC₁ hupΦ hlowΦ hcontΦ
      (fun k : ℕ => Ψ (Work.Mostow.BdExt.ray ξ (k : ℝ))) (Work.Mostow.BdExt.bdMap n Ψ ξ)
      hΨξS hΨlim hΨlvl
  -- on the other hand `Φ (Ψ (ray ξ k))` is at bounded distance from `ray ξ k`
  have hclose' : ∀ k : ℕ,
      hdist (Φ (Ψ (Work.Mostow.BdExt.ray ξ (k : ℝ)))) (Work.Mostow.BdExt.ray ξ (k : ℝ)) ≤ D :=
    fun k => hclose _
  have hv_lvl : Tendsto
      (fun k : ℕ => Work.Mostow.BdExt.lvl (Φ (Ψ (Work.Mostow.BdExt.ray ξ (k : ℝ))))) atTop atTop :=
    Work.Mostow.BdExt.tendsto_lvl_of_close_ray (n := n) hI ξ hξ
      (fun k : ℕ => Φ (Ψ (Work.Mostow.BdExt.ray ξ (k : ℝ)))) D hclose'
  have hu_lvl : Tendsto (fun k : ℕ => Work.Mostow.BdExt.lvl (Work.Mostow.BdExt.ray ξ (k : ℝ)))
      atTop atTop :=
    Work.Mostow.BdExt.tendsto_lvl_ray ξ hξ
  have hu_dir : Tendsto (fun k : ℕ => Work.Mostow.BdExt.dirv (Work.Mostow.BdExt.ray ξ (k : ℝ)))
      atTop (nhds ξ) :=
    Work.Mostow.BdExt.tendsto_dirv_ray hI ξ hξ
  have hlim₂ : Tendsto (fun k : ℕ => Work.Mostow.BdExt.dirv (Φ (Ψ (Work.Mostow.BdExt.ray ξ (k : ℝ)))))
      atTop (nhds ξ) :=
    Work.Mostow.BdExt.closeSeq n hI
      (fun k : ℕ => Work.Mostow.BdExt.ray ξ (k : ℝ))
      (fun k : ℕ => Φ (Ψ (Work.Mostow.BdExt.ray ξ (k : ℝ)))) D hD
      (fun k => by rw [hI.2.1]; exact hclose' k) hu_lvl hv_lvl ξ hu_dir
  exact tendsto_nhds_unique hlim₁ hlim₂

end Work.BdExt
