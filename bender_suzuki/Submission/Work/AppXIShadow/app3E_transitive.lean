import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

/-- If `A` is a normal subgroup with `A ⊔ stabilizer a = ⊤`, then the orbit of `a`
under any subgroup containing `A` is everything: every point `ω` equals `x • a` for
some `x ∈ A ⊔ K`. -/
theorem app3E_transitive {F Ω : Type} [Group F] [MulAction F Ω] (a : Ω)
    (htrans : MulAction.IsPretransitive F Ω) {K A : Subgroup F} (hA : A.Normal)
    (hsup : A ⊔ MulAction.stabilizer F a = ⊤) :
    ∀ ω : Ω, ∃ x ∈ A ⊔ K, x • a = ω := by
  intro ω
  -- Transitivity gives some `g` with `g • a = ω`.
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq a ω
  -- Since `A` is normal, `A ⊔ stabilizer a` is the product set `A * stabilizer a`.
  have hmem : g ∈ (↑(A ⊔ MulAction.stabilizer F a) : Set F) := by
    rw [hsup]; exact Subgroup.mem_top g
  rw [Subgroup.normal_mul A (MulAction.stabilizer F a)] at hmem
  rw [Set.mem_mul] at hmem
  obtain ⟨p, hp, s, hs, hps⟩ := hmem
  -- `p ∈ A ≤ A ⊔ K` and `s` fixes `a`, so `p • a = g • a = ω`.
  refine ⟨p, Subgroup.mem_sup_left hp, ?_⟩
  rw [← hps, mul_smul, MulAction.mem_stabilizer_iff.mp hs] at hg
  exact hg

end Work.AppXIShadow
