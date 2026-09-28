import Mathlib
import Submission.Work.HP.MDEstimates.cubLevelForms
import Submission.Work.Q44Geom.gcdOne
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.complBasis
import Submission.Work.Q44Geom.isHomogeneous_of_mul_eq
import Submission.Work.Q44Geom.isUnit_of_isHomogeneous_zero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open MvPolynomial
open Work.Q44Geom

noncomputable section

namespace Work.HP.Q44Main

/-! ## Irreducibility of a cubic without linear factor -/

/-- A homogeneous cubic in five variables with no linear factor over `ℚ` is irreducible: a
nontrivial factorization `B = A * B'` has homogeneous factors whose degrees add to `3`, so one
of them has degree `1` and is a linear factor of `B`. -/
theorem irreducible_of_no_linear_factor_cubic (B : MvPolynomial (Fin 5) ℚ)
    (hB : B.IsHomogeneous 3) (hB0 : B ≠ 0)
    (hnolin : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False) :
    Irreducible B := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro hunit
    rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced] at hunit
    have h3 := hB.totalDegree hB0
    have h0 := hunit.2
    omega
  · intro A B' hAB
    by_contra hnu
    rw [not_or] at hnu
    obtain ⟨hAnu, hBnu⟩ := hnu
    have hA0 : A ≠ 0 := fun h0 => hB0 (by rw [hAB, h0, zero_mul])
    have hB'0 : B' ≠ 0 := fun h0 => hB0 (by rw [hAB, h0, mul_zero])
    obtain ⟨i, j, hij, hAi, hBj⟩ := Work.Q44Geom.isHomogeneous_of_mul_eq hB hAB hA0 hB'0
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · exact absurd (Work.Q44Geom.isUnit_of_isHomogeneous_zero (h0 ▸ hAi) hA0) hAnu
      · exact hpos
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · exact absurd (Work.Q44Geom.isUnit_of_isHomogeneous_zero (h0 ▸ hBj) hB'0) hBnu
      · exact hpos
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with h1 | h2 | h3
    · exact hnolin A (h1 ▸ hAi) ⟨B', hAB⟩
    · have hj1' : j = 1 := by omega
      exact hnolin B' (hj1' ▸ hBj) ⟨A, by rw [hAB, mul_comm]⟩
    · rw [h3] at hij; omega

/-! ## Conversion of the non-invariance hypothesis -/

/-- `¬ (b₁ ∈ invSub B ∧ b₂ ∈ invSub B)` is equivalent to saying `B` is not invariant under all
translations in the plane `ℚ b₁ + ℚ b₂`. -/
lemma not_invSub_pair_iff (B : MvPolynomial (Fin 5) ℚ) (b₁ b₂ : Fin 5 → ℚ) :
    (¬ (b₁ ∈ Work.Q44Geom.invSub B ∧ b₂ ∈ Work.Q44Geom.invSub B)) ↔
    (¬ ∀ a b : ℚ, ∀ x : Fin 5 → ℚ,
      MvPolynomial.eval (x + a • b₁ + b • b₂) B = MvPolynomial.eval x B) := by
  constructor
  · intro hnd hall
    exact hnd ⟨(fun x t => by simpa using hall t 0 x),
      (fun x t => by simpa using hall 0 t x)⟩
  · intro hall hpair
    obtain ⟨h1, h2⟩ := hpair
    exact hall (fun a b x => by rw [h2 (x + a • b₁) b, h1 x a])

/-! ## The cubic assembly -/

/-- Cubic analogue of `Work.Q44Geom.gcdOne_aux`: the level forms of degree `≤ 2` of a cubic `B`
(no linear factor, vanishing on the line `ℚb₁ + ℚb₂`, not doubly translation invariant) have no
common nonconstant divisor. -/
theorem cubGcdOne_aux (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (P : Fin 3 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (Q : Fin 2 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ)
    (hPw : ∀ (a a' : Fin 3), P a (w a') = if a = a' then 1 else 0)
    (hPb : ∀ (a : Fin 3) (j : Fin 2), P a (![b₁, b₂] j) = 0)
    (hrecon : ∀ y : Fin 5 → ℚ,
      (∑ a : Fin 3, (P a y) • w a) + (∑ j : Fin 2, (Q j y) • ![b₁, b₂] j) = y)
    (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3)
    (hirr : Irreducible B)
    (hnd : ¬ ∀ a b : ℚ, ∀ x : Fin 5 → ℚ,
      MvPolynomial.eval (x + a • b₁ + b • b₂) B = MvPolynomial.eval x B)
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) B = 0)
    (h : MvPolynomial (Fin 3) ℚ)
    (hdiv : ∀ i ∈ Finset.range 3, ∀ j ∈ Finset.range 3, i + j ≤ 2 →
      h ∣ Work.Q44Geom.levelForm w b₁ b₂ B ![i, j]) :
    IsUnit h := by
  have hcof : ∀ s : Fin 2 →₀ ℕ, Finsupp.degree s ≤ 2 → h ∣ (sigma w b₁ b₂ B).coeff s := by
    intro s hs
    have h0 : s 0 ≤ 2 := by have := Finsupp.le_degree 0 s; omega
    have h1 : s 1 ≤ 2 := by have := Finsupp.le_degree 1 s; omega
    have hmem0 : s 0 ∈ Finset.range 3 := by rw [Finset.mem_range]; omega
    have hmem1 : s 1 ∈ Finset.range 3 := by rw [Finset.mem_range]; omega
    have hsum : Finsupp.degree s = s 0 + s 1 := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    have hfun : (fun j : Fin 2 => s j) = ![s 0, s 1] := by
      funext j; fin_cases j <;> simp
    rw [coeff_sigma_eq_levelForm, hfun]
    exact hdiv (s 0) hmem0 (s 1) hmem1 (by omega)
  let Mf : (Fin 2 →₀ ℕ) → MvPolynomial (Fin 3) ℚ := fun s =>
    if hs : Finsupp.degree s ≤ 2 then (hcof s hs).choose else 0
  have hMf : ∀ s : Fin 2 →₀ ℕ, (hs : Finsupp.degree s ≤ 2) →
      (sigma w b₁ b₂ B).coeff s = h * Mf s := by
    intro s hs
    have hspec := (hcof s hs).choose_spec
    simpa [Mf, dif_pos hs] using hspec
  let A : MvPolynomial (Fin 5) ℚ := MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) h
  let B' : MvPolynomial (Fin 5) ℚ :=
    ∑ s ∈ (sigma w b₁ b₂ B).support.filter (fun s => Finsupp.degree s ≤ 2),
      MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) (Mf s) *
        ∏ j ∈ s.support, (linOf (Q j)) ^ (s j)
  have hfAB : B = A * B' := by
    refine MvPolynomial.funext (fun y => ?_)
    have hy := substPoint_eq_of_recon w b₁ b₂ P Q hrecon y
    have hev1 : eval y B = ∑ s ∈ (sigma w b₁ b₂ B).support,
        eval (fun a => P a y) ((sigma w b₁ b₂ B).coeff s) *
          ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      conv_lhs => rw [← hy]
      rw [← eval_sigma w b₁ b₂ B (fun a => P a y) (fun j => Q j y)]
      exact eval_sigma_eq_sum _ _ _
    have hev2 : (∑ s ∈ (sigma w b₁ b₂ B).support,
        eval (fun a => P a y) ((sigma w b₁ b₂ B).coeff s) *
          ∏ j ∈ s.support, (Q j y) ^ (s j))
        = ∑ s ∈ (sigma w b₁ b₂ B).support.filter (fun s => Finsupp.degree s ≤ 2),
        eval (fun a => P a y) ((sigma w b₁ b₂ B).coeff s) *
          ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro s hs hsnot
      have h3 : 3 ≤ Finsupp.degree s := by
        by_contra hcon
        exact hsnot (Finset.mem_filter.mpr ⟨hs, by omega⟩)
      rw [Work.HP.MDEstimates.coeff_sigma_eq_zero_of_three_le w b₁ b₂ B hB hℓ s h3, map_zero, zero_mul]
    have hev3 : (∑ s ∈ (sigma w b₁ b₂ B).support.filter (fun s => Finsupp.degree s ≤ 2),
        eval (fun a => P a y) ((sigma w b₁ b₂ B).coeff s) *
          ∏ j ∈ s.support, (Q j y) ^ (s j))
        = ∑ s ∈ (sigma w b₁ b₂ B).support.filter (fun s => Finsupp.degree s ≤ 2),
        (eval (fun a => P a y) h * eval (fun a => P a y) (Mf s)) *
          ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hs2 : Finsupp.degree s ≤ 2 := (Finset.mem_filter.mp hs).2
      rw [hMf s hs2, map_mul]
    have hev4 : (∑ s ∈ (sigma w b₁ b₂ B).support.filter (fun s => Finsupp.degree s ≤ 2),
        (eval (fun a => P a y) h * eval (fun a => P a y) (Mf s)) *
          ∏ j ∈ s.support, (Q j y) ^ (s j))
        = eval (fun a => P a y) h *
        ∑ s ∈ (sigma w b₁ b₂ B).support.filter (fun s => Finsupp.degree s ≤ 2),
          eval (fun a => P a y) (Mf s) * ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have hA : eval y A = eval (fun a => P a y) h := by
      rw [show A = MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) h from rfl,
        eval_aeval_linOf]
    have hB' : eval y B' = ∑ s ∈ (sigma w b₁ b₂ B).support.filter
        (fun s => Finsupp.degree s ≤ 2),
        eval (fun a => P a y) (Mf s) * ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      rw [show B' = ∑ s ∈ (sigma w b₁ b₂ B).support.filter (fun s => Finsupp.degree s ≤ 2),
          MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) (Mf s) *
            ∏ j ∈ s.support, (linOf (Q j)) ^ (s j) from rfl]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [map_mul, eval_aeval_linOf, map_prod]
      congr 1
      exact Finset.prod_congr rfl (fun j _ => by rw [map_pow, eval_linOf])
    rw [map_mul, hA, hB', hev1, hev2, hev3, hev4]
  by_cases hunit : IsUnit h
  · exact hunit
  · exfalso
    have hAne : ¬ IsUnit A := not_isUnit_aeval_linOf w P hPw h hunit
    rcases hirr.isUnit_or_isUnit hfAB with hAu | hBu
    · exact hAne hAu
    · obtain ⟨c, hcunit, hBc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced (R := ℚ)).mp hBu
      have hfA : B = c • A := by
        rw [hfAB, hBc, mul_comm, MvPolynomial.C_mul']
      refine hnd ?_
      intro a b x
      have hinv := aeval_linOf_invariant w b₁ b₂ P hPb h a b x
      have h1 : eval (x + a • b₁ + b • b₂) A = eval x A := hinv
      have h2 : ∀ z : Fin 5 → ℚ, eval z (c • A) = c * eval z A := by
        intro z
        rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
      rw [hfA, h2 (x + a • b₁ + b • b₂), h2 x, h1]

/-! ## The requested theorem -/

theorem cubGcdOne (b₁ b₂ : Fin 5 → ℚ) (w : Fin 3 → Fin 5 → ℚ)
    (hb : LinearIndependent ℚ (Fin.append w ![b₁, b₂]))
    (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3) (hB0 : B ≠ 0)
    (hnolin : ∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False)
    (hnd : ¬ (b₁ ∈ Work.Q44Geom.invSub B ∧ b₂ ∈ Work.Q44Geom.invSub B))
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) B = 0)
    (h : MvPolynomial (Fin 3) ℚ)
    (hdiv : ∀ i ∈ Finset.range 3, ∀ j ∈ Finset.range 3, i + j ≤ 2 →
      h ∣ Work.Q44Geom.levelForm w b₁ b₂ B ![i, j]) :
    IsUnit h := by
  obtain ⟨P, Q, hPw, hPb, hrecon⟩ := Work.Q44Geom.gcdCoordRecon_local w b₁ b₂ hb
  exact cubGcdOne_aux w b₁ b₂ P Q hPw hPb hrecon B hB
    (irreducible_of_no_linear_factor_cubic B hB hB0 hnolin)
    ((not_invSub_pair_iff B b₁ b₂).mp hnd)
    hℓ h hdiv

end Work.HP.Q44Main
