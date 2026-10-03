import Mathlib
import Submission.Work.ORBassSerre.Action.QuotientGroupOrbitV

namespace Work.ORBassSerre.QuotientTree

universe u

/-- The stabilizer in `G ⧸ N` of the class of `x` is the image of the stabilizer of `x` under
`G →* G ⧸ N` (for the action of `G ⧸ N` on the `N`-orbits of a `G`-set `X`, induced by the
action on the `N`-orbit quotient, `Work.ORBassSerre.instMulActionQuotientOrbit`). -/
theorem stabilizer_quotient_mk {G X : Type u} [Group G] [MulAction G X] (N : Subgroup G)
    [N.Normal] (x : X) :
    MulAction.stabilizer (G ⧸ N) (Quotient.mk'' x : MulAction.orbitRel.Quotient N X) =
      (MulAction.stabilizer G x).map (QuotientGroup.mk' N) := by
  ext q
  constructor
  · -- `q • ⟦x⟧ = ⟦x⟧` means `g • x` lies in the `N`-orbit of `x`, i.e. `n • x = g • x` for some
    -- `n ∈ N`; then `(n⁻¹ * g) • x = x` and `n⁻¹ * g` has the same image as `g` in `G ⧸ N`.
    intro hq
    rw [MulAction.mem_stabilizer_iff] at hq
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N q
    rw [← hg] at hq ⊢
    rw [quotient_smul_mk] at hq
    rw [Subgroup.mem_map]
    have h1 : MulAction.orbitRel N X (g • x) x := Quotient.exact hq
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨(↑n)⁻¹ * g, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, mul_smul]
      rw [← hn]
      exact inv_smul_smul (↑n) x
    · have hk : (QuotientGroup.mk' N (↑n) : G ⧸ N) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact n.2
      rw [map_mul, map_inv, hk]
      simp
  · -- Conversely, any `s ∈ Stab_G x` fixes `⟦x⟧` in the quotient.
    intro hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨s, hs, hsq⟩ := hq
    rw [← hsq]
    rw [MulAction.mem_stabilizer_iff, quotient_smul_mk]
    rw [MulAction.mem_stabilizer_iff] at hs
    rw [hs]

end Work.ORBassSerre.QuotientTree
