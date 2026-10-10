import Mathlib
import Submission.Work.MotK.TGen.CruxAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.SdG5hHomogFac`

A general fact about the factorisation of a *homogeneous* polynomial in several variables over a
field: if `F * H = G` with `G` the five-coefficient degree-five form
`Gg g₁ g₂ g₃ g₄ g₅ = g₁x₀⁵ + g₂x₁⁵ + g₃x₂⁵ + g₄x₀²x₁x₂² + g₅x₀x₁³x₂` and `F, H ≠ 0`, then both
`F` and `H` are homogeneous of their own total degree and those degrees sum to `5`.

The mathematical content is the standard statement for a graded domain: `MvPolynomial (Fin 3) K` is
an `ℕ`-graded domain and `Gg` is homogeneous of degree `5`, so its factors must be homogeneous.  The
proof uses the graded product formula

`homogeneousComponent k (p * q) = ∑ i ∈ range (k + 1), homogeneousComponent i p * homogeneousComponent (k - i) q`

(`homogeneousComponent_mul_eq_sum_range`, transported from the `DirectSum` decomposition), plus the
observation that the *lowest* nonzero homogeneous components `i₀` of `F` and `j₀` of `H` multiply to
the component of degree `i₀ + j₀` of `F * H`.  Since `F * H = Gg` has no component other than the
one of degree `5`, one gets `i₀ + j₀ = 5`.  On the other hand `totalDegree (F * H) = totalDegree F +
totalDegree H` (the ring being a domain), and `i₀ ≤ totalDegree F`, `j₀ ≤ totalDegree H`, so
`i₀ = totalDegree F` and `j₀ = totalDegree H`: both factors are homogeneous.
-/

open MvPolynomial

namespace Work.MotK.TGen

section GradedProduct

-- the `ℕ`-grading of `MvPolynomial` by total degree, as a local instance
attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The graded product formula.**  The `k`-th homogeneous component of a product is the `k`-th
graded piece of the product in the `ℕ`-grading by total degree:
`hc k (p * q) = ∑ i ∈ range (k+1), hc i p * hc (k-i) q`. -/
theorem homogeneousComponent_mul_eq_sum_range {K : Type} [CommSemiring K] {σ : Type*}
    (p q : MvPolynomial σ K) (k : ℕ) :
    homogeneousComponent k (p * q)
      = ∑ i ∈ Finset.range (k + 1), homogeneousComponent i p * homogeneousComponent (k - i) q := by
  have key : ∀ (r : MvPolynomial σ K) (i : ℕ),
      ((DirectSum.decompose (homogeneousSubmodule σ K) r i) : MvPolynomial σ K)
        = homogeneousComponent i r := by
    intro r i
    rw [← DirectSum.Decomposition.decompose'_eq (homogeneousSubmodule σ K)]
    exact decomposition.decompose'_apply r i
  rw [← key (p*q) k, DirectSum.decompose_mul (homogeneousSubmodule σ K) p q,
    DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  rw [show (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
      ↑(((DirectSum.decompose (homogeneousSubmodule σ K)) p) ij.1) *
        ↑(((DirectSum.decompose (homogeneousSubmodule σ K)) q) ij.2))
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
          homogeneousComponent ij.1 p * homogeneousComponent ij.2 q from
    Finset.sum_congr rfl (fun ij _ => by rw [key p ij.1, key q ij.2])]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => homogeneousComponent a p * homogeneousComponent b q) k

end GradedProduct

/-- The top (degree-`totalDegree`) homogeneous component of a nonzero polynomial is nonzero: the
`totalDegree` is attained by a monomial in the support, and that monomial survives in the top
component with the same coefficient. -/
lemma homogeneousComponent_totalDegree_ne_zero {K : Type} [Field K]
    (p : MvPolynomial (Fin 3) K) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  intro h
  have hsupp : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp
  obtain ⟨d, hdmem, hdsup⟩ :=
    Finset.exists_mem_eq_sup p.support hsupp (fun m => (Finsupp.toMultiset m).card)
  have hd : Finsupp.degree d = p.totalDegree := by
    rw [MvPolynomial.totalDegree_eq, hdsup, Finsupp.card_toMultiset, Finsupp.degree_apply]
    rfl
  have hcoeff : (homogeneousComponent p.totalDegree p).coeff d = p.coeff d := by
    rw [MvPolynomial.coeff_homogeneousComponent, ite_eq_left hd]
  rw [h] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hdmem) hcoeff.symm

theorem SdG5hHomogFac {K : Type} [Field K] (g1 g2 g3 g4 g5 : K)
    (F H : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hH : H ≠ 0)
    (hfac : F * H = Work.MotK.TGen.Gg g1 g2 g3 g4 g5) :
    F.IsHomogeneous F.totalDegree ∧ H.IsHomogeneous H.totalDegree
      ∧ F.totalDegree + H.totalDegree = 5 := by
  classical
  -- `Gg g₁ … g₅` is homogeneous of degree `5` (a sum of five degree-`5` monomials)
  have t1 : (C g1 * (X (0 : Fin 3)) ^ 5 : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (Fin 3) g1).mul (isHomogeneous_X_pow (0 : Fin 3) 5)
  have t2 : (C g2 * (X (1 : Fin 3)) ^ 5 : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (Fin 3) g2).mul (isHomogeneous_X_pow (1 : Fin 3) 5)
  have t3 : (C g3 * (X (2 : Fin 3)) ^ 5 : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (Fin 3) g3).mul (isHomogeneous_X_pow (2 : Fin 3) 5)
  have t4 : (C g4 * ((X (0 : Fin 3)) ^ 2 * X 1 * (X 2) ^ 2) :
      MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (((isHomogeneous_X_pow (0 : Fin 3) 2).mul (isHomogeneous_X K 1)).mul
      (isHomogeneous_X_pow (2 : Fin 3) 2)).C_mul g4
  have t5 : (C g5 * (X (0 : Fin 3) * (X 1) ^ 3 * X 2) :
      MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (((isHomogeneous_X K 0).mul (isHomogeneous_X_pow (1 : Fin 3) 3)).mul
      (isHomogeneous_X K 2)).C_mul g5
  have hGhom : (Gg g1 g2 g3 g4 g5).IsHomogeneous 5 := by
    rw [Gg]
    exact IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add t1 t2) t3) t4) t5
  -- hence `F * H` is homogeneous of degree `5`, and `F.totalDegree + H.totalDegree = 5`
  have hFHhom : (F * H).IsHomogeneous 5 := by rw [hfac]; exact hGhom
  have hFH0 : F * H ≠ 0 := mul_ne_zero hF hH
  have htdFH : (F * H).totalDegree = 5 := hFHhom.totalDegree hFH0
  have hdegsum : F.totalDegree + H.totalDegree = 5 := by
    rw [← MvPolynomial.totalDegree_mul_of_isDomain hF hH]
    exact htdFH
  -- the lowest index at which `F` has a nonzero homogeneous component (and same for `H`)
  have hexF : ∃ i, homogeneousComponent i F ≠ 0 := by
    by_contra h
    push_neg at h
    refine hF ?_
    rw [← MvPolynomial.sum_homogeneousComponent F]
    exact Finset.sum_eq_zero (fun i _ => h i)
  obtain ⟨i₀, hi₀spec, hi₀min⟩ :
      ∃ i, homogeneousComponent i F ≠ 0 ∧ ∀ j < i, homogeneousComponent j F = 0 :=
    ⟨Nat.find hexF, Nat.find_spec hexF, fun j hj => not_not.mp (Nat.find_min hexF hj)⟩
  have hexH : ∃ j, homogeneousComponent j H ≠ 0 := by
    by_contra h
    push_neg at h
    refine hH ?_
    rw [← MvPolynomial.sum_homogeneousComponent H]
    exact Finset.sum_eq_zero (fun j _ => h j)
  obtain ⟨j₀, hj₀spec, hj₀min⟩ :
      ∃ j, homogeneousComponent j H ≠ 0 ∧ ∀ i < j, homogeneousComponent i H = 0 :=
    ⟨Nat.find hexH, Nat.find_spec hexH, fun i hi => not_not.mp (Nat.find_min hexH hi)⟩
  -- the degree-`i₀ + j₀` component of `F * H` is `hc i₀ F * hc j₀ H`
  have hkey : homogeneousComponent (i₀ + j₀) (F * H)
      = homogeneousComponent i₀ F * homogeneousComponent j₀ H := by
    rw [homogeneousComponent_mul_eq_sum_range]
    have hsingle : (∑ i ∈ Finset.range (i₀ + j₀ + 1),
        homogeneousComponent i F * homogeneousComponent (i₀ + j₀ - i) H)
        = homogeneousComponent i₀ F * homogeneousComponent (i₀ + j₀ - i₀) H :=
      Finset.sum_eq_single i₀
        (fun i hi hne => by
          have hi_le : i ≤ i₀ + j₀ := by have := Finset.mem_range.mp hi; omega
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [hi₀min i hlt, zero_mul]
          · have hlt' : i₀ + j₀ - i < j₀ := by omega
            rw [hj₀min (i₀ + j₀ - i) hlt', mul_zero])
        (fun hmem => absurd (Finset.mem_range.mpr (by omega)) hmem)
    rw [hsingle, Nat.add_sub_cancel_left i₀ j₀]
  have hkey_ne : homogeneousComponent (i₀ + j₀) (F * H) ≠ 0 := by
    rw [hkey]; exact mul_ne_zero hi₀spec hj₀spec
  have hGne : homogeneousComponent (i₀ + j₀) (Gg g1 g2 g3 g4 g5) ≠ 0 := by
    rwa [← hfac]
  -- `Gg` has no component in degree `≠ 5`, so `i₀ + j₀ = 5`
  have hij : i₀ + j₀ = 5 := by
    by_contra hne
    rw [MvPolynomial.homogeneousComponent_of_mem (m := i₀ + j₀) hGhom,
      ite_eq_right hne] at hGne
    exact hGne rfl
  -- `i₀ ≤ totalDegree F`, `j₀ ≤ totalDegree H`; with `n + m = 5` this forces equality
  have hi₀le : i₀ ≤ F.totalDegree := by
    by_contra h
    exact hi₀spec (MvPolynomial.homogeneousComponent_eq_zero i₀ F (Nat.lt_of_not_le h))
  have hj₀le : j₀ ≤ H.totalDegree := by
    by_contra h
    exact hj₀spec (MvPolynomial.homogeneousComponent_eq_zero j₀ H (Nat.lt_of_not_le h))
  have hi₀eq : i₀ = F.totalDegree := by omega
  have hj₀eq : j₀ = H.totalDegree := by omega
  -- consequently all other homogeneous components of `F` (and `H`) vanish
  have hF_eq : F = homogeneousComponent F.totalDegree F :=
    (MvPolynomial.sum_homogeneousComponent F).symm.trans
      (Finset.sum_eq_single F.totalDegree
        (fun i hi hne => by
          have hi' : i < F.totalDegree + 1 := Finset.mem_range.mp hi
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hi₀min i (by omega)
          · exact MvPolynomial.homogeneousComponent_eq_zero i F hgt)
        (fun hmem => absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hmem))
  have hFhom : F.IsHomogeneous F.totalDegree := by
    have h := MvPolynomial.homogeneousComponent_isHomogeneous F.totalDegree F
    rw [← hF_eq] at h
    exact h
  have hH_eq : H = homogeneousComponent H.totalDegree H :=
    (MvPolynomial.sum_homogeneousComponent H).symm.trans
      (Finset.sum_eq_single H.totalDegree
        (fun j hj hne => by
          have hj' : j < H.totalDegree + 1 := Finset.mem_range.mp hj
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hj₀min j (by omega)
          · exact MvPolynomial.homogeneousComponent_eq_zero j H hgt)
        (fun hmem => absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hmem))
  have hHhom : H.IsHomogeneous H.totalDegree := by
    have h := MvPolynomial.homogeneousComponent_isHomogeneous H.totalDegree H
    rw [← hH_eq] at h
    exact h
  exact ⟨hFhom, hHhom, hdegsum⟩

end Work.MotK.TGen
