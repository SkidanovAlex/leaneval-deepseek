import Mathlib
import Submission.Work.Pert.retMap
import Submission.Work.Pert.Gates
import Submission.Work.Pert.AsmDefs

/-!
# `Work.Pert.pert2v2.retOf_add_one_waist`

One-step `T`-equivariance of the lifted return map `R̃_f = Φ ∘ Tt α ∘ Φ⁻¹` on the *waist image*
`Φ '' (Qm Ξ α ∩ Qp Ξ α)`, in the "endpoint-clause" form used by the assembly: the hypotheses give
the chosen preimage `z = invOn Φ (Qm Ξ α) u` of `u`, its membership in the upper gate `Qp Ξ α`
(hence, via `Tt_mem_Qm_iff`, the membership of `Tt α z` in the lower gate `Qm Ξ α` and, using
`F ∘ Tt = Tt ∘ F` and `F z ∈ Qp Ξ α`, that of `F (Tt α z)`), and the memberships of `u` and `u + 1`
in the waist image.  All of this is exactly the hypothesis list of `Work.Pert.retOf_add_one`
(`Submission/Work/Pert/retMap.lean`) with `Q := Qm Ξ α`, `w := u`, which is the whole proof.

Note the *junk* branch of `invOn`: the memberships `hu`, `hu1` are what make the chosen preimages
meaningful, and `hz` identifies the chosen preimage of `u` with the given point `z`.
-/

namespace Work.Pert.pert2v2

noncomputable section

theorem retOf_add_one_waist {F Φ : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {u z : ℂ}
    (hcomm : ∀ x : ℂ, F (Work.Pert.Tt α x) = Work.Pert.Tt α (F x))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α))
    (hu : u ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α))
    (hz : Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) u = z)
    (hzQp : z ∈ Work.Pert.Qp Ξ α)
    (hFz : F z ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
    (hu1 : u + 1 ∈ Φ '' (Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)) :
    Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α (u + 1)
      = Work.Pert.retOf Φ (Work.Pert.Qm Ξ α) α u + 1 := by
  obtain ⟨_, hinj, hab⟩ := hΦ
  -- `Tt α` maps the upper gate back into the lower gate.
  have hTt : ∀ w : ℂ, w ∈ Work.Pert.Qp Ξ α → Work.Pert.Tt α w ∈ Work.Pert.Qm Ξ α :=
    fun w hw => (Work.Pert.Tt_mem_Qm_iff (ξ := Ξ) (α := α)).mpr hw
  refine Work.Pert.retOf_add_one (Q := Work.Pert.Qm Ξ α) (w := u)
    hcomm hinj hab ?_ ?_ ?_ ?_ ?_
  · obtain ⟨ζ, hζ, hζΦ⟩ := hu
    exact ⟨ζ, hζ.1, hζΦ⟩
  · obtain ⟨ζ, hζ, hζΦ⟩ := hu1
    exact ⟨ζ, hζ.1, hζΦ⟩
  · rw [hz]; exact hFz.1
  · rw [hz]; exact hTt z hzQp
  · rw [hz, hcomm z]; exact hTt (F z) hFz.2

end

end Work.Pert.pert2v2
