import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

/-- If `A` is normal in `F`, `F = A·M` and `[A,A] ≤ M`, then `A ⊓ M` is normal in `F`.

For `n ∈ A ⊓ M` and `g = a·m` with `a ∈ A`, `m ∈ M`, one has
`g n g⁻¹ = a (m n m⁻¹) a⁻¹`.  The element `n' := m n m⁻¹` again lies in `A ⊓ M`
(`A` is normal, and `M` is a subgroup), and `a n' a⁻¹ = [a, n'] · n'` is a product of a
commutator of elements of `A` (hence in `M` by `hder`) with `n' ∈ M`. -/
theorem app3B_inf_normal {F : Type} [Group F] {A M : Subgroup F}
    (hA : A.Normal) (hder : ⁅A, A⁆ ≤ M) (hsup : A ⊔ M = ⊤) : (A ⊓ M).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  obtain ⟨hnA, hnM⟩ := Subgroup.mem_inf.mp hn
  have hg : g ∈ A ⊔ M := by rw [hsup]; exact Subgroup.mem_top g
  obtain ⟨a, ha, m, hm, hgm⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := A) (t := M) (hs := hA)).mp hg
  have hnmA : m * n * m⁻¹ ∈ A := Subgroup.Normal.conj_mem hA n hnA m
  have hnmM : m * n * m⁻¹ ∈ M := mul_mem (mul_mem hm hnM) (M.inv_mem hm)
  have hcomm : a * (m * n * m⁻¹) * a⁻¹ * (m * n * m⁻¹)⁻¹ ∈ M :=
    (Subgroup.commutator_le.mp hder) a ha (m * n * m⁻¹) hnmA
  rw [Subgroup.mem_inf, ← hgm]
  constructor
  · have h1 : a * m * n * (a * m)⁻¹ = a * (m * n * m⁻¹) * a⁻¹ := by group
    rw [h1]
    exact Subgroup.Normal.conj_mem hA (m * n * m⁻¹) hnmA a
  · have h1 : a * m * n * (a * m)⁻¹ =
        (a * (m * n * m⁻¹) * a⁻¹ * (m * n * m⁻¹)⁻¹) * (m * n * m⁻¹) := by group
    rw [h1]
    exact mul_mem hcomm hnmM

end Work.AppXIShadow
