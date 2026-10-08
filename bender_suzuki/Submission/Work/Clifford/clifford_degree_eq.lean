import Mathlib
import Submission.Work.Clifford.clifford_decomposition
import Submission.Work.Clifford.card_charOrbit
import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

/-- Every conjugate of `θ : N → ℂ` (for `N ⊴ G`) takes the same value at `1` as `θ`. -/
theorem conjFun_apply_one {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (θ : N → ℂ) (g : G) : conjFun N g θ 1 = θ 1 := by
  rw [conjFun_apply]
  congr 1
  exact Subtype.ext (by simp)

/-- The orbit sum of `θ` at `1` equals `[G : I_G(θ)] * θ 1`. -/
theorem orbitSum_one {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (θ : N → ℂ) :
    orbitSum N θ 1 = ((inertia N θ).index : ℂ) * θ 1 := by
  have hconst : ∀ φ ∈ charOrbit N θ, φ 1 = θ 1 := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := mem_charOrbit.mp hφ
    exact conjFun_apply_one θ g
  calc orbitSum N θ 1 = ∑ φ ∈ charOrbit N θ, φ 1 := orbitSum_apply N θ 1
    _ = ∑ _φ ∈ charOrbit N θ, θ 1 := Finset.sum_congr rfl hconst
    _ = (charOrbit N θ).card • θ 1 := Finset.sum_const (θ 1)
    _ = ((inertia N θ).index : ℂ) * θ 1 := by rw [card_charOrbit, nsmul_eq_mul]

theorem clifford_degree_eq {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype N] {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) :
    ∃ θ : N → ℂ, θ ∈ Work.Clifford.Irr N ∧ ∃ e : ℕ, 0 < e ∧
      χ 1 = (e : ℂ) * ((Work.Clifford.inertia N θ).index : ℂ) * θ 1 := by
  obtain ⟨θ, hθ, e, he, hres⟩ := clifford_decomposition (N := N) hχ
  refine ⟨θ, hθ, e, he, ?_⟩
  have hχ1 : χ 1 = (e : ℂ) * orbitSum N θ 1 := by
    have h := congrFun hres (1 : N)
    simp only [resFun_apply, Pi.smul_apply, smul_eq_mul] at h
    calc χ 1 = χ ((1 : N) : G) := rfl
      _ = (e : ℂ) * orbitSum N θ 1 := h
  calc χ 1 = (e : ℂ) * orbitSum N θ 1 := hχ1
    _ = (e : ℂ) * (((inertia N θ).index : ℂ) * θ 1) := by rw [orbitSum_one θ]
    _ = (e : ℂ) * ((inertia N θ).index : ℂ) * θ 1 := by ring

end Work.Clifford
