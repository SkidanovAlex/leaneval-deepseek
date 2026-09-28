import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.gcdOne
import Submission.Work.Q44Geom.levels
import Submission.Work.Q44Geom.complBasis
import Submission.Work.Q44Geom.uniqueDirection
import Submission.Work.Q44Geom.planeBoundFin

/-!
# Level forms of a cubic form in five variables

For a homogeneous cubic `B` in five variables and a basis `(w, b₁, b₂)` of `ℚ⁵` we consider
the coefficients of `B(Σ p_a w_a + u₀ b₁ + u₁ b₂)` in the variables `u₀, u₁`; these are the
*level forms* `levelForm w b₁ b₂ B α`, homogeneous of degree `3 - |α|`.

The module collects the cubic analogues (used for `cubPlaneBound`) of the degree-`4` facts
`pref_sigma`, `coeff_sigma_eq_zero_of_four_le`, `levelHom` and `isSolIff`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
noncomputable section
open MvPolynomial

namespace Work.HP.MDEstimates

open Work.Q44Geom

/-- `sigma w b₁ b₂ B` is a polynomial in the two `u`-variables whose `s`-th coefficient is a
form of degree `3 - |s|` in the `p`-variables, for a cubic `B`. -/
theorem pref_sigma_cubic (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3) :
    Pref 3 (sigma w b₁ b₂ B) := by
  rw [MvPolynomial.as_sum B, map_sum]
  refine pref_sum _ _ 3 (fun d hd => ?_)
  have hdeg : Finsupp.degree d = 3 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (MvPolynomial.IsHomogeneous.coeff_eq_zero hB h)
  have h' := pref_sigma_monomial w b₁ b₂ d (B.coeff d)
  rwa [hdeg] at h'

/-- The `α`-th level form of a cubic form is homogeneous of degree `3 - |α|`. -/
theorem levelForm_cubic_isHomogeneous (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3) (α : Fin 2 → ℕ)
    (hα : α 0 + α 1 ≤ 3) :
    (levelForm w b₁ b₂ B α).IsHomogeneous (3 - (α 0 + α 1)) := by
  rw [levelForm_def]
  have hdeg : (Finsupp.equivFunOnFinite.symm α).degree = α 0 + α 1 := by
    rw [Finsupp.degree_eq_sum]; simp [Fin.sum_univ_two]
  have hq : (flatEquiv (sigma w b₁ b₂ B)).IsHomogeneous 3 := by
    rw [show sigma w b₁ b₂ B = MvPolynomial.aeval (sigmaArg w b₁ b₂) B from rfl]
    rw [algEquiv_aeval]
    have h := MvPolynomial.IsHomogeneous.aeval (σ := Fin 5) hB
      (fun i => flatEquiv (sigmaArg w b₁ b₂ i)) (flatEquiv_sigmaArg_isHomogeneous w b₁ b₂)
    simpa using h
  have hkey := sumAlgEquiv_coeff_isHomogeneous (flatEquiv (sigma w b₁ b₂ B)) 3 hq
    (Finsupp.equivFunOnFinite.symm α)
  rw [show (MvPolynomial.sumAlgEquiv ℚ (Fin 2) (Fin 3)) (flatEquiv (sigma w b₁ b₂ B))
      = sigma w b₁ b₂ B from AlgEquiv.apply_symm_apply _ _] at hkey
  rw [hdeg] at hkey
  exact hkey

/-- The coefficients of `sigma w b₁ b₂ B` of `u`-degree at least `3` vanish, when `B` is a
cubic vanishing on the line spanned by `b₁, b₂`. -/
theorem coeff_sigma_eq_zero_of_three_le (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3)
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) B = 0)
    (s : Fin 2 →₀ ℕ) (hs : 3 ≤ Finsupp.degree s) :
    (sigma w b₁ b₂ B).coeff s = 0 := by
  have hpref := pref_sigma_cubic w b₁ b₂ B hB
  by_cases hne : (sigma w b₁ b₂ B).coeff s = 0
  · exact hne
  · obtain ⟨hd, hhom⟩ := hpref s hne
    have hzero : MvPolynomial.eval (0 : Fin 3 → ℚ) ((sigma w b₁ b₂ B).coeff s) = 0 := by
      have hmap : MvPolynomial.map (MvPolynomial.eval (0 : Fin 3 → ℚ)) (sigma w b₁ b₂ B) = 0 := by
        refine MvPolynomial.funext (fun u => ?_)
        rw [eval_map_eval_eq, eval_sigma]
        have hsub : substPoint w b₁ b₂ (0 : Fin 3 → ℚ) u = u 0 • b₁ + u 1 • b₂ := by
          funext i; simp [substPoint]
        rw [hsub, hℓ u]
        simp
      have hthis := congrArg (fun (g : MvPolynomial (Fin 2) ℚ) => g.coeff s) hmap
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hthis
      exact hthis
    have heq : 3 - Finsupp.degree s = 0 := by omega
    have hconst := eq_C_eval_zero_of_isHomogeneous_zero _
      (by simpa [heq] using hhom)
    rw [hconst, hzero]
    simp

/-- Coefficient extraction: if `B` vanishes on every point `substPoint w b₁ b₂ x u`, then every
coefficient of `sigma w b₁ b₂ B` vanishes at `x`. -/
theorem coeff_sigma_eval_eq_zero (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (B : MvPolynomial (Fin 5) ℚ) (x : Fin 3 → ℚ)
    (hvan : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (substPoint w b₁ b₂ x u) B = 0) :
    ∀ s : Fin 2 →₀ ℕ, MvPolynomial.eval x ((sigma w b₁ b₂ B).coeff s) = 0 := by
  classical
  have hPt_eval : ∀ u : Fin 2 → ℚ,
      MvPolynomial.eval u (∑ s ∈ (sigma w b₁ b₂ B).support,
        MvPolynomial.monomial s (MvPolynomial.eval x ((sigma w b₁ b₂ B).coeff s))) = 0 := by
    intro u
    rw [map_sum]
    have h1 : ∀ s ∈ (sigma w b₁ b₂ B).support,
        MvPolynomial.eval u (MvPolynomial.monomial s
          (MvPolynomial.eval x ((sigma w b₁ b₂ B).coeff s)))
        = MvPolynomial.eval x ((sigma w b₁ b₂ B).coeff s)
            * ∏ j ∈ s.support, u j ^ (s j) := by
      intro s _
      rw [MvPolynomial.eval_monomial, Finsupp.prod]
    rw [Finset.sum_congr rfl h1]
    rw [← eval_sigma_eq_sum (sigma w b₁ b₂ B) x u, eval_sigma w b₁ b₂ B x u]
    exact hvan u
  have hPt0 : (∑ s ∈ (sigma w b₁ b₂ B).support,
      MvPolynomial.monomial s (MvPolynomial.eval x ((sigma w b₁ b₂ B).coeff s))) = 0 :=
    MvPolynomial.funext (fun u => by rw [hPt_eval u, map_zero])
  intro s
  by_cases hs : s ∈ (sigma w b₁ b₂ B).support
  · have hcoeff : (∑ t ∈ (sigma w b₁ b₂ B).support,
        MvPolynomial.monomial t (MvPolynomial.eval x ((sigma w b₁ b₂ B).coeff t))).coeff s
        = MvPolynomial.eval x ((sigma w b₁ b₂ B).coeff s) := by
      rw [MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single s]
      · rw [MvPolynomial.coeff_monomial]; simp
      · intro t _ hne
        rw [MvPolynomial.coeff_monomial]
        simp only [if_neg hne]
      · intro hs'; exact absurd hs hs'
    rw [← hcoeff, hPt0]
    simp
  · rw [Finsupp.notMem_support_iff.mp hs, map_zero]

/-- **The cubic level-form criterion.**  For a cubic `B` vanishing on the line `ℚb₁ + ℚb₂`,
`B` vanishes on the whole plane `substPoint w b₁ b₂ x ·` iff all level forms of degree `≤ 2`
vanish at `x`. -/
theorem isSolIffCub (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3)
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) B = 0)
    (x : Fin 3 → ℚ) :
    (∀ u : Fin 2 → ℚ, MvPolynomial.eval (substPoint w b₁ b₂ x u) B = 0)
      ↔ ∀ i ∈ Finset.range 3, ∀ j ∈ Finset.range 3, i + j ≤ 2 →
          MvPolynomial.eval x (levelForm w b₁ b₂ B ![i, j]) = 0 := by
  constructor
  · intro hvan i _ j _ _
    have hall := coeff_sigma_eval_eq_zero w b₁ b₂ B x hvan
    have h1 : (fun k : Fin 2 => (Finsupp.equivFunOnFinite.symm ![i, j]) k) = ![i, j] := by
      funext k; fin_cases k <;> rfl
    rw [← h1, ← coeff_sigma_eq_levelForm w b₁ b₂ B (Finsupp.equivFunOnFinite.symm ![i, j])]
    exact hall _
  · intro hvan u
    rw [← eval_sigma w b₁ b₂ B x u, eval_sigma_eq_sum]
    refine Finset.sum_eq_zero (fun s _ => ?_)
    by_cases hdeg : Finsupp.degree s ≤ 2
    · have h0 : MvPolynomial.eval x ((sigma w b₁ b₂ B).coeff s) = 0 := by
        rw [coeff_sigma_eq_levelForm]
        have hfun : (fun j : Fin 2 => s j) = ![s 0, s 1] := by funext j; fin_cases j <;> simp
        rw [hfun]
        have hs0 : s 0 ∈ Finset.range 3 := by
          rw [Finset.mem_range]; have := Finsupp.le_degree 0 s; omega
        have hs1 : s 1 ∈ Finset.range 3 := by
          rw [Finset.mem_range]; have := Finsupp.le_degree 1 s; omega
        have hs2 : s 0 + s 1 ≤ 2 := by
          have hsum : Finsupp.degree s = s 0 + s 1 := by
            rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
          omega
        exact hvan (s 0) hs0 (s 1) hs1 hs2
      rw [h0, zero_mul]
    · have h3 : 3 ≤ Finsupp.degree s := by omega
      rw [coeff_sigma_eq_zero_of_three_le w b₁ b₂ B hB hℓ s h3, map_zero, zero_mul]

end Work.HP.MDEstimates
