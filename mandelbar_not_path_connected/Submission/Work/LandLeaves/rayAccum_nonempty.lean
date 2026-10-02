import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Rays.isBounded_dynRay_sublevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Set

theorem rayAccum_nonempty {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ)
    (hray : Work.Landing.RaysNearCircle c φ) (θ : ℝ) :
    (Work.Landing.rayAccum c φ θ).Nonempty := by
  -- the truncations of the ray at Böttcher modulus `≤ ρ`
  let S : ℝ → Set ℂ := fun ρ => {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ}
  have hS_mono : Monotone S := fun ρ σ hρσ z hz => ⟨hz.1, le_trans hz.2 hρσ⟩
  have hS_bdd : ∀ ρ : ℝ, Bornology.IsBounded (S ρ) := fun ρ =>
    Work.Landing.Rays.isBounded_dynRay_sublevel h θ ρ
  let ι := {ρ : ℝ // 1 < ρ}
  have hι : Nonempty ι := ⟨⟨2, by norm_num⟩⟩
  let t : ι → Set ℂ := fun ρ => closure (S ρ.1)
  have hdir : Directed (· ⊇ ·) t := by
    rintro ⟨ρ, hρ⟩ ⟨σ, hσ⟩
    refine ⟨⟨min ρ σ, lt_min hρ hσ⟩, ?_, ?_⟩
    · exact closure_mono (hS_mono (min_le_left ρ σ))
    · exact closure_mono (hS_mono (min_le_right ρ σ))
  have hne : ∀ i : ι, (t i).Nonempty := by
    rintro ⟨ρ, hρ⟩
    obtain ⟨z, hz, hzφ⟩ := hray θ ρ hρ
    exact ⟨z, subset_closure ⟨hz, hzφ⟩⟩
  have hcp : ∀ i : ι, IsCompact (t i) := fun ⟨ρ, _⟩ =>
    (hS_bdd ρ).isCompact_closure
  have hcl : ∀ i : ι, IsClosed (t i) := fun _ => isClosed_closure
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (hι := hι) t hdir hne hcp hcl
  refine ⟨x, ?_⟩
  rw [Set.mem_iInter] at hx
  intro ρ hρ
  exact hx ⟨ρ, hρ⟩

end Work.LandLeaves
