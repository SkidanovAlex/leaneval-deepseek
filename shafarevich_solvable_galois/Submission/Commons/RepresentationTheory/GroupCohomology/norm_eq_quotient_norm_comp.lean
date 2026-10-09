import Mathlib.RepresentationTheory.Invariants
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Representation

namespace Commons.RepresentationTheory.GroupCohomology

/-- Auxiliary: the norm over `G` of a representation equals the norm over `G ⧸ N` of the
representation induced on the `N`-invariants, applied to the norm over `N`. -/
theorem norm_eq_quotient_norm_comp {k : Type} [CommRing k] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] [DecidablePred (· ∈ N)] (A : Rep k G) (z : A.V) :
    A.ρ.norm z = (((A.quotientToInvariants N).ρ.norm
      ⟨(Rep.res N.subtype A).ρ.norm z,
        (Representation.mem_invariants ((Rep.res N.subtype A).ρ) _).2
          (fun g => Representation.self_norm_apply (Rep.res N.subtype A).ρ g z)⟩ : A.V)) := by
  -- A representative map for the cosets of `N`.
  let c : G ⧸ N → G := fun q => Quotient.out (show Quotient (QuotientGroup.leftRel N) from q)
  have hc : ∀ q : G ⧸ N, (c q : G ⧸ N) = q :=
    fun q => Quotient.out_eq (s := QuotientGroup.leftRel N) _
  -- The bijection `G ⧸ N × N → G`, `(q, n) ↦ c q * n`.
  let φ : (G ⧸ N) × N → G := fun p => c p.1 * (p.2 : G)
  have hφinj : Function.Injective φ := by
    rintro ⟨q₁, n₁⟩ ⟨q₂, n₂⟩ h
    simp only [φ] at h
    have hq : q₁ = q₂ := by
      have h' := congrArg (QuotientGroup.mk' N) h
      simp only [map_mul, QuotientGroup.mk'_apply] at h'
      rw [hc, hc] at h'
      have hn1 : ((n₁ : G) : G ⧸ N) = 1 := by
        rw [QuotientGroup.eq_one_iff]; exact n₁.2
      have hn2 : ((n₂ : G) : G ⧸ N) = 1 := by
        rw [QuotientGroup.eq_one_iff]; exact n₂.2
      rw [hn1, hn2, mul_one, mul_one] at h'
      exact h'
    subst hq
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h))
  have hφsurj : Function.Surjective φ := by
    intro g
    refine ⟨((g : G ⧸ N), ⟨(c (g : G ⧸ N))⁻¹ * g, ?_⟩), ?_⟩
    · rw [← QuotientGroup.eq_one_iff]
      have hcq : QuotientGroup.mk' N (c (g : G ⧸ N)) = (g : G ⧸ N) := by
        rw [QuotientGroup.mk'_apply]; exact hc (g : G ⧸ N)
      have : QuotientGroup.mk' N ((c (g : G ⧸ N))⁻¹ * g) = 1 := by
        rw [map_mul, map_inv, hcq, show QuotientGroup.mk' N g = (g : G ⧸ N) from rfl,
          inv_mul_cancel]
      simpa only [QuotientGroup.mk'_apply] using this
    · simp only [φ]
      group
  -- The `N`-norm of `z` as an element of the `N`-invariants.
  let w' : Representation.invariants (A.ρ.comp N.subtype) :=
    ⟨(Rep.res N.subtype A).ρ.norm z, (Representation.mem_invariants ((Rep.res N.subtype A).ρ) _).2
          (fun g => Representation.self_norm_apply (Rep.res N.subtype A).ρ g z)⟩
  change A.ρ.norm z = ((A.ρ.quotientToInvariants N).norm w' : A.V)
  -- Value of the quotient representation on a coset representative.
  have hval : ∀ q : G ⧸ N,
      (((A.ρ.quotientToInvariants N) q w' : Representation.invariants (A.ρ.comp N.subtype)) : A.V)
      = A.ρ (c q) ((Rep.res N.subtype A).ρ.norm z) := by
    intro q
    conv_lhs => rw [← hc q]
    rw [Representation.quotientToInvariants, Representation.ofQuotient_coe_apply]
    rfl
  -- Inner sum identity over `N`.
  have hinner : ∀ q : G ⧸ N, ∑ n : N, A.ρ (c q * (n : G)) z
      = A.ρ (c q) ((Rep.res N.subtype A).ρ.norm z) := by
    intro q
    have h1 : ∀ n : N, A.ρ (c q * (n : G)) z = A.ρ (c q) (A.ρ (n : G) z) := by
      intro n; rw [map_mul]; rfl
    rw [Finset.sum_congr rfl (fun n _ => h1 n)]
    rw [show (Rep.res N.subtype A).ρ.norm z = ∑ n : N, A.ρ (n : G) z by
      simp [Representation.norm]]
    rw [map_sum]
  -- Left-hand side as a sum over the quotient.
  have hLHS : A.ρ.norm z = ∑ q : G ⧸ N, A.ρ (c q) ((Rep.res N.subtype A).ρ.norm z) := by
    rw [show A.ρ.norm z = ∑ g : G, A.ρ g z by simp [Representation.norm]]
    rw [← Fintype.sum_bijective φ ⟨hφinj, hφsurj⟩ (fun p => A.ρ (φ p) z) (fun g => A.ρ g z)
      (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    simp only [φ]
    rw [Finset.sum_congr rfl (fun q _ => hinner q)]
  -- Right-hand side as the same sum over the quotient.
  have hRHS : (((A.ρ.quotientToInvariants N).norm w'
        : Representation.invariants (A.ρ.comp N.subtype)) : A.V)
      = ∑ q : G ⧸ N, A.ρ (c q) ((Rep.res N.subtype A).ρ.norm z) := by
    rw [show (A.ρ.quotientToInvariants N).norm w'
        = ∑ q : G ⧸ N, (A.ρ.quotientToInvariants N) q w' by simp [Representation.norm]]
    rw [Submodule.coe_sum]
    rw [Finset.sum_congr rfl (fun q _ => hval q)]
  rw [hLHS, hRHS]

end Commons.RepresentationTheory.GroupCohomology