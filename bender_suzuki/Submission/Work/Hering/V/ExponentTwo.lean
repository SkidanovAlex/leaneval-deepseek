import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Small auxiliary facts about a subgroup of exponent two

Used by the hard core: if every element of `V` squares to `1` then `V` is abelian, hence
`V ≤ C_G(V)`, and therefore all involutions of `G` lie in `C_G(V)` as soon as they lie in `V`.
-/

set_option autoImplicit false

namespace Work.Hering

variable {G : Type*} [Group G]

/-- A subgroup of exponent `2` is abelian, hence contained in its own centraliser. -/
theorem le_centralizer_of_exponent_two {V : Subgroup G} (hexp : ∀ x ∈ V, x * x = 1) :
    V ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hinv : ∀ z ∈ V, z⁻¹ = z := fun z hz => inv_eq_of_mul_eq_one_right (hexp z hz)
  calc y * x = (y * x)⁻¹ := (hinv (y * x) (mul_mem hy hx)).symm
    _ = x⁻¹ * y⁻¹ := mul_inv_rev y x
    _ = x * y := by rw [hinv x hx, hinv y hy]

/-- The centraliser of a normal subgroup is normal. -/
theorem centralizer_normal {V : Subgroup G} (hV : V.Normal) :
    (Subgroup.centralizer (V : Set G)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro v hv
  have h1 : g⁻¹ * v * g ∈ V := by simpa using hV.conj_mem v hv g⁻¹
  have h2 : (g⁻¹ * v * g) * n = n * (g⁻¹ * v * g) := hn _ h1
  calc v * (g * n * g⁻¹) = (g * (g⁻¹ * v * g) * g⁻¹) * (g * n * g⁻¹) := by group
    _ = g * ((g⁻¹ * v * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
    _ = (g * n * g⁻¹) * (g * (g⁻¹ * v * g) * g⁻¹) := by group
    _ = (g * n * g⁻¹) * v := by group

end Work.Hering
