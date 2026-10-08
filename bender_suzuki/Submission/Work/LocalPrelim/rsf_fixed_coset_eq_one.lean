import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.LocalPrelim

theorem rsf_fixed_coset_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (a : G ⧸ Subgroup.normalizer (P : Set G))
    (ha : ∀ q : ↥(P : Subgroup G), q • a = a) :
    a = ((1 : G) : G ⧸ Subgroup.normalizer (P : Set G)) := by
  -- Write the coset `a` as the class of an explicit element `g`.
  obtain ⟨g, hg⟩ : ∃ g : G, (g : G ⧸ Subgroup.normalizer (P : Set G)) = a :=
    ⟨Quotient.out a, QuotientGroup.out_eq' a⟩
  -- The hypothesis `ha` says that `g⁻¹ * x * g` normalizes `P` for every `x ∈ P`.
  have hconj : ∀ x ∈ (P : Subgroup G), g⁻¹ * x * g ∈ Subgroup.normalizer (P : Set G) := by
    intro x hx
    have h := ha ⟨x⁻¹, (P : Subgroup G).inv_mem hx⟩
    rw [← hg] at h
    simp only [Subgroup.smul_def, MulAction.Quotient.smul_coe] at h
    rw [QuotientGroup.eq] at h
    simpa using h
  -- Hence `P` fixes the Sylow subgroup `g • P`.
  have hfix : ∀ q : ↥(P : Subgroup G), q • (g • P) = g • P := by
    intro q
    rw [Subgroup.smul_def, ← mul_smul]
    have hmul : (q : G) * g = g * (g⁻¹ * (q : G) * g) := by group
    rw [hmul, mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr (hconj (q : G) q.2)]
  -- A `p`-subgroup fixing a Sylow `p`-subgroup is contained in it.
  have hle : (P : Subgroup G) ≤ ↑(g • P) :=
    (IsPGroup.sylow_mem_fixedPoints_iff P.isPGroup').mp (MulAction.mem_fixedPoints.mpr hfix)
  -- As both are Sylow `p`-subgroups, they coincide.
  have hEq : g • P = P := Sylow.ext (P.is_maximal' (g • P).isPGroup' hle)
  have hgmem : g ∈ Subgroup.normalizer (P : Set G) := Sylow.smul_eq_iff_mem_normalizer.mp hEq
  -- Therefore `g` lies in the normalizer, i.e. `a` is the trivial coset.
  rw [← hg, QuotientGroup.eq]
  simpa using hgmem

end Work.LocalPrelim
