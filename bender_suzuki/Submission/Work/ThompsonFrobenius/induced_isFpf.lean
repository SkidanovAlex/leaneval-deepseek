import Mathlib
import Submission.Work.NPC.Fpf.Defs
import Submission.Work.Frobenius.Fpf.quotientCongr_pow_apply
import Submission.Work.Frobenius.Fpf.isFpf_quotientCongr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThompsonFrobenius

/-- If `α` is a fixed-point-free automorphism of order dividing the prime `q` of a finite group `G`,
and `H ⋬ G` is a proper `α`-invariant normal subgroup, then the automorphism induced by `α` on
`G ⧸ H` again has order `q` and is fixed-point-free.

The fixed-point-freeness is `isFpf_quotientCongr`.  For the order: the induced automorphism `β`
satisfies `β ^ q = 1`, so `orderOf β ∣ q`, and `β ≠ 1` because `β = 1` would force
`x⁻¹ * α x ∈ H` for every `x`; since `x ↦ x⁻¹ * α x` is bijective (`α` being fixed-point-free and
`G` finite) that would put all of `G` in `H`, i.e. `H = ⊤`, contrary to `hHne`. -/
theorem induced_isFpf {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime) {α : MulAut G} (hαq : α ^ q = 1) (hfpf : Work.NPC.Fpf.IsFpf α) {H : Subgroup G} [H.Normal] (hH : Work.NPC.Fpf.IsInv α H) (hHne : H ≠ ⊤) : (orderOf (QuotientGroup.congr H H α (by simpa using hH.map_eq)) = q) ∧ Work.NPC.Fpf.IsFpf (QuotientGroup.congr H H α (by simpa using hH.map_eq)) := by
  have he : Subgroup.map (↑α : G →* G) H = H := by simpa using hH.map_eq
  change (orderOf (QuotientGroup.congr H H α he) = q) ∧
    Work.NPC.Fpf.IsFpf (QuotientGroup.congr H H α he)
  -- `β ^ q = 1`
  have hβq : (QuotientGroup.congr H H α he) ^ q = 1 := by
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    have hstep := Work.Frobenius.Fpf.quotientCongr_pow_apply hH q x
    rw [hαq] at hstep
    simp at hstep
    simpa using hstep
  -- `β ≠ 1`
  have hβne : (QuotientGroup.congr H H α he) ≠ 1 := by
    intro hb1
    have hmem : ∀ x : G, x⁻¹ * α x ∈ H := by
      intro x
      have hx : (QuotientGroup.congr H H α he) (QuotientGroup.mk x) = QuotientGroup.mk x := by
        have := congrArg (fun f : MulAut (G ⧸ H) => f (QuotientGroup.mk x)) hb1
        simpa using this
      have h2 : QuotientGroup.mk (α x) = QuotientGroup.mk x :=
        (QuotientGroup.congr_mk H H α he x).symm.trans hx
      rw [← QuotientGroup.eq]
      exact h2.symm
    have hsurj : Function.Surjective (fun z : G => z⁻¹ * α z) :=
      (Work.Frobenius.Fpf.isFpf_mulInv_bijective hfpf).2
    have htop_le : (⊤ : Subgroup G) ≤ H := by
      intro g _
      obtain ⟨z, hz⟩ := hsurj g
      rw [← hz]
      exact hmem z
    exact hHne (top_le_iff.mp htop_le)
  have hfpfβ : Work.NPC.Fpf.IsFpf (QuotientGroup.congr H H α he) :=
    Work.Frobenius.Fpf.isFpf_quotientCongr hfpf hH
  have hord : orderOf (QuotientGroup.congr H H α he) = q := by
    have hdvd : orderOf (QuotientGroup.congr H H α he) ∣ q :=
      orderOf_dvd_iff_pow_eq_one.mpr hβq
    rcases hq.eq_one_or_self_of_dvd (orderOf (QuotientGroup.congr H H α he)) hdvd with h1 | h1
    · rw [orderOf_eq_one_iff] at h1
      exact absurd h1 hβne
    · exact h1
  exact ⟨hord, hfpfβ⟩

end Work.ThompsonFrobenius
