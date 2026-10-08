import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Commons.GroupTheory.Subgroup

/-- In the natural left action of a group `G` on its left coset space `G ⧸ H`,
an element `g` stabilizes the coset of `x` iff the conjugate `x⁻¹ * g * x` lies
in `H`. -/
lemma smul_quotient_mk_eq_self_iff {G : Type*} [Group G] (H : Subgroup G) (g x : G) :
    g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x ↔ x⁻¹ * g * x ∈ H := by
  constructor
  · intro h
    have hb : (QuotientGroup.mk (g * x) : G ⧸ H) = QuotientGroup.mk x := by
      simpa [smul_eq_mul] using h
    have hq : (g * x)⁻¹ * x ∈ H := (QuotientGroup.eq).mp hb
    have hrel : (x⁻¹ * g * x)⁻¹ = (g * x)⁻¹ * x := by group
    have hqinv : (x⁻¹ * g * x)⁻¹ ∈ H := by
      rwa [hrel]
    simpa using (H.inv_mem hqinv)
  · intro hx
    have hb : (QuotientGroup.mk (g * x) : G ⧸ H) = QuotientGroup.mk x := by
      apply (QuotientGroup.eq).mpr
      have hrel : (g * x)⁻¹ * x = (x⁻¹ * g * x)⁻¹ := by group
      rw [hrel]
      exact H.inv_mem hx
    simpa [smul_eq_mul] using hb

/-- The elements of `G` fixing every coset in `G ⧸ H` are precisely the elements
of the normal core of `H`: the kernel of the coset action is the intersection of
all conjugates of `H`. -/
lemma fixedBy_all_iff_mem_normalCore {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    (∀ q : G ⧸ H, g • q = q) ↔ g ∈ H.normalCore := by
  constructor
  · intro hfix a
    have hs := (smul_quotient_mk_eq_self_iff H g (a⁻¹)).mp
      (hfix (QuotientGroup.mk (a⁻¹) : G ⧸ H))
    simpa using hs
  · intro hcore q
    rcases q with ⟨x⟩
    apply (smul_quotient_mk_eq_self_iff H g x).mpr
    simpa using hcore (x⁻¹)

/-- The action of a group `G` on the left coset space `G ⧸ H` is faithful
exactly when the normal core of `H` is trivial. -/
theorem faithfulSMul_coset_iff_core_bot {G : Type*} [Group G] (H : Subgroup G) :
    FaithfulSMul G (G ⧸ H) ↔ H.normalCore = ⊥ := by
  constructor
  · intro hfaith
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hf := (fixedBy_all_iff_mem_normalCore H g).mpr hg
    exact @FaithfulSMul.eq_of_smul_eq_smul G (G ⧸ H) _ hfaith g 1 (by
      intro q
      rw [one_smul]
      exact hf q)
  · intro hcore
    refine ⟨?core⟩
    intro g h hgh
    have hk : g⁻¹ * h ∈ H.normalCore := by
      intro b
      have hb : (QuotientGroup.mk (g * b⁻¹ : G) : G ⧸ H) =
          (QuotientGroup.mk (h * b⁻¹ : G) : G ⧸ H) := by
        simpa [smul_eq_mul] using hgh (QuotientGroup.mk (b⁻¹ : G) : G ⧸ H)
      have hq : (g * b⁻¹)⁻¹ * (h * b⁻¹) ∈ H := (QuotientGroup.eq).mp hb
      have hs : (g * b⁻¹)⁻¹ * (h * b⁻¹) = b * (g⁻¹ * h) * b⁻¹ := by group
      rwa [hs] at hq
    have hk1 : g⁻¹ * h = 1 := by
      simpa [hcore] using hk
    calc
      g = g * 1 := by rw [mul_one]
      _ = g * (g⁻¹ * h) := by rw [hk1]
      _ = h := by rw [mul_inv_cancel_left]

end Commons.GroupTheory.Subgroup
