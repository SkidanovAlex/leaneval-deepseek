import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Clifford.clifford_constituents
import Submission.Work.Clifford.clifford_correspondence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.neq_of_not_conj`

Two irreducible characters of a finite group `G` whose restrictions to a normal subgroup `N ⊴ G`
have non-conjugate constituents are distinct.  This is the constituent form of Clifford's
theorem (`Work.Clifford.clifford_constituents`): the irreducible constituents of `χ|_N` form a
single `G`-orbit `charOrbit N θ`.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.CharQ

theorem neq_of_not_conj {G : Type} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype ↥N] {θ₁ θ₂ : ↥N → ℂ} (hθ₁ : θ₁ ∈ Work.CharCore.Irr ↥N)
    (hθ₂ : θ₂ ∈ Work.CharCore.Irr ↥N)
    (hnotconj : ¬ ∃ g : G, Work.Clifford.conjFun N g θ₁ = θ₂)
    {χ₁ χ₂ : G → ℂ} (hχ₁ : χ₁ ∈ Work.CharCore.Irr G) (hχ₂ : χ₂ ∈ Work.CharCore.Irr G)
    (hc₁ : Work.CharCore.cfInner θ₁ (Work.CharCore.resFun N χ₁) ≠ 0)
    (hc₂ : Work.CharCore.cfInner θ₂ (Work.CharCore.resFun N χ₂) ≠ 0) :
    χ₁ ≠ χ₂ := by
  classical
  intro heq
  have hχ₁c : χ₁ ∈ Work.Clifford.Irr G :=
    (Work.Clifford.corr_mem_Irr_charCore (G := G)).mpr hχ₁
  have hθ₁c : θ₁ ∈ Work.Clifford.Irr ↥N :=
    (Work.Clifford.corr_mem_Irr_charCore (G := ↥N)).mpr hθ₁
  have hθ₂c : θ₂ ∈ Work.Clifford.Irr ↥N :=
    (Work.Clifford.corr_mem_Irr_charCore (G := ↥N)).mpr hθ₂
  obtain ⟨η, hη, hcliff⟩ := Work.Clifford.clifford_constituents (N := N) hχ₁c
  have hc₂' : Work.CharCore.cfInner θ₂ (Work.CharCore.resFun N χ₁) ≠ 0 := by
    rw [heq]; exact hc₂
  -- `θ₁` and `θ₂` are constituents of `χ₁|_N`
  have hmem₁ : θ₁ ∈ Work.Clifford.charOrbit N η := by
    rw [← hcliff θ₁ hθ₁c]
    unfold Work.Clifford.IsConstituentOf
    rw [Work.Clifford.corr_cfInner_eq_charCore, Work.CharCore.cfInner_conj_symm]
    exact star_ne_zero.mpr hc₁
  have hmem₂ : θ₂ ∈ Work.Clifford.charOrbit N η := by
    rw [← hcliff θ₂ hθ₂c]
    unfold Work.Clifford.IsConstituentOf
    rw [Work.Clifford.corr_cfInner_eq_charCore, Work.CharCore.cfInner_conj_symm]
    exact star_ne_zero.mpr hc₂'
  -- hence `θ₁` and `θ₂` are conjugate
  have key : Work.Clifford.charOrbit N θ₁ = Work.Clifford.charOrbit N θ₂ := by
    rw [Work.Clifford.charOrbit_eq_of_mem hmem₁, Work.Clifford.charOrbit_eq_of_mem hmem₂]
  have hconj : θ₂ ∈ Work.Clifford.charOrbit N θ₁ := by
    rw [key]; exact Work.Clifford.theta_mem_charOrbit θ₂
  rw [Work.Clifford.mem_charOrbit] at hconj
  exact hnotconj hconj

end Work.FeitSibley.CharQ
