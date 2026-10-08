import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.cfInner_indFun
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Clifford.classFun_eq_zero_of_orthogonal
import Submission.Work.Clifford.gallagher_isometry
import Submission.Work.Clifford.gallagher_ind_eq
import Submission.Work.Clifford.gallagher_mul_inflate_irr
import Submission.Work.CharCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open Classical

namespace Work.Clifford

/-- **Gallagher's theorem** (Isaacs, Character Theory of Finite Groups, Theorem 6.17).  Let
`N ⊴ G`, let `θ ∈ Irr N` be `G`-invariant, and let `χ ∈ Irr G` extend `θ`.  Then the
irreducible characters of `G` lying over `θ` are exactly the products `χ · Inf β` with
`β ∈ Irr(G ⧸ N)`, the parameter `β` being unique.

The hypotheses `hinv` (invariance of `θ`) and `hθ` are in fact implied by the others (a
restriction of the class function `χ` is `G`-invariant, by `hext`), but they are kept to
match the requested statement. -/
theorem gallagher {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal] [Fintype N]
    {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) (hinv : Work.Clifford.inertia N θ = ⊤)
    {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) (hext : Work.Clifford.Extends N χ θ) :
    ∀ φ : G → ℂ, φ ∈ Work.Clifford.Irr G → Work.Clifford.IsConstituentOf θ (Work.Clifford.resFun N φ) →
      ∃! β : G ⧸ N → ℂ, β ∈ Work.Clifford.Irr (G ⧸ N) ∧
        φ = χ * Work.Clifford.inflateFun N β := by
  intro φ hφ hconst
  classical
  haveI : Fintype (G ⧸ N) := QuotientGroup.fintype N
  -- ### Existence: `φ` is a constituent of `Ind_N^G θ`, whose decomposition is known.
  -- Frobenius reciprocity turns the constituent hypothesis into `⟪Ind θ, φ⟫ ≠ 0`.
  have hrec : cfInner (indFun N θ) φ = cfInner θ (resFun N φ) :=
    cfInner_indFun θ (IsClassFun.of_mem_Irr hφ)
  have hneθ : cfInner θ (resFun N φ) ≠ 0 := fun h => hconst (by
    have h2 : starRingEnd ℂ (cfInner (resFun N φ) θ) = 0 := by
      rw [← cfInner_conj_symm]; exact h
    exact (starRingEnd ℂ).injective (by rw [h2, map_zero]))
  have hne : cfInner (indFun N θ) φ ≠ 0 := by rw [hrec]; exact hneθ
  -- The decomposition `Ind_N^G θ = ∑_β β(1) · (χ · Inf β)`.
  have hInd := gallagher_ind_eq (N := N) hθ hχ hext
  have hsum_eq : (∑ β ∈ Work.CharCore.Irr (G ⧸ N),
      (β 1) * cfInner (χ * inflateFun N β) φ) = cfInner (indFun N θ) φ := by
    rw [hInd, cfInner_sum_smul_left]
  have hsum : (∑ β ∈ Work.CharCore.Irr (G ⧸ N),
      (β 1) * cfInner (χ * inflateFun N β) φ) ≠ 0 := by
    rw [hsum_eq]; exact hne
  -- Each summand is `β(1)` or `0`, since `χ · Inf β` is irreducible (`gallagher_mul_inflate_irr`).
  have hterm : ∀ β ∈ Work.CharCore.Irr (G ⧸ N),
      (β 1) * cfInner (χ * inflateFun N β) φ
        = if χ * inflateFun N β = φ then (β 1) else 0 := by
    intro β hβ
    have hβirr : β ∈ Irr (G ⧸ N) := charCore_mem_Irr_subset β hβ
    have hL2 : χ * inflateFun N β ∈ Irr G := gallagher_mul_inflate_irr (N := N) hθ hχ hext hβirr
    rw [cfInner_eq_ite_of_mem_Irr hL2 hφ, mul_ite, mul_one, mul_zero]
  -- A nonzero sum has a nonzero summand, so some `β` satisfies `χ · Inf β = φ`.
  have hex : ∃ β ∈ Work.CharCore.Irr (G ⧸ N), χ * inflateFun N β = φ := by
    by_contra h
    push Not at h
    exact hsum (Finset.sum_eq_zero fun β hβ => by
      rw [hterm β hβ]; exact if_neg (h β hβ))
  obtain ⟨β, hβI, hβeq⟩ := hex
  refine ⟨β, ⟨charCore_mem_Irr_subset β hβI, hβeq.symm⟩, ?_⟩
  -- ### Uniqueness: the isometry `⟪χ·Inf u, χ·Inf v⟫ = ⟪u, v⟫` separates the parameters.
  intro y hy
  obtain ⟨hyirr, hyeq⟩ := hy
  have hiso := gallagher_isometry (N := N) hθ hχ hext y β
  have h1 : cfInner (χ * inflateFun N y) (χ * inflateFun N β) = 1 := by
    rw [← hyeq, hβeq, cfInner_eq_ite_of_mem_Irr hφ hφ]; simp
  have h2 : cfInner y β = 1 := by rw [← hiso]; exact h1
  rw [cfInner_eq_ite_of_mem_Irr (G := G ⧸ N) hyirr (charCore_mem_Irr_subset β hβI)] at h2
  by_cases hyb : y = β
  · exact hyb
  · rw [if_neg hyb] at h2; exact absurd h2 zero_ne_one

end Work.Clifford
