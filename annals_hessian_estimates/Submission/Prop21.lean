/-
Prop. 2.1 (almost-Jacobi inequality) for smooth solutions of the sigma_2 equation in dimension 4,
together with the bridge from the set-theoretic hypothesis `sigma_2 (H u s y) = 1` to the
coordinate PDE used by the algebraic core `Commons.Analysis.Sigma2.jacobi_inequality_of_sigma2_coord`.
-/
import ChallengeDeps
import Submission.Commons.Analysis.Sigma2.jacobi_inequality_of_sigma2_coord
import Submission.Commons.Analysis.Sigma2.sigma2_eigen_eq_trace_invariants
import Submission.Commons.Analysis.Sigma2.coord_minor_sum_eq_trace_invariants
import Submission.Commons.Analysis.InnerProductSpace.eigen_basis_inner_apply
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_apply_second_partial
import Submission.Commons.Analysis.Calculus.FDeriv.isSymmetric_hessianWithin
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
import Submission.Commons.Analysis.Calculus.FDeriv.second_partial_symm
import Submission.Commons.Analysis.InnerProductSpace.eq_zero_of_inner_eq_zero_of_span_top

open HessianEstimates
open Commons.Analysis.Calculus.FDeriv
open Commons.Analysis.Sigma2
open Commons.Analysis.InnerProductSpace
open Laplacian Metric MeasureTheory ENNReal
open scoped BigOperators RealInnerProductSpace

set_option autoImplicit false

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

private theorem sum_lt_eq_sum_ite {n : ℕ} (f : Fin n → ℝ) (j : Fin n) :
    (∑ i < j, f i) = ∑ i : Fin n, (if i < j then f i else 0) := by
  show ∑ i ∈ Finset.Iio j, f i = _
  rw [show Finset.Iio j = Finset.univ.filter (fun x => x < j) from by
        ext x; simp [Finset.mem_Iio], Finset.sum_filter]

/-- The `sigma_2` equation, in coordinate form, in an arbitrary orthonormal basis. -/
theorem coord_minor_sum_eq_one {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1)
    (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) :
    ∀ y ∈ s, (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j] -
        ((iteratedFDeriv ℝ 2 u y) ![v i, v j]) ^ 2 else 0) = 1 := by
  intro y hy
  have hT : (H u s y).IsSymmetric := isSymmetric_hessianWithin hs hy hu
  have hcoeff := hσ2 y hy
  rw [HessianEstimates.σ₂, dif_pos hT] at hcoeff
  rw [show (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i < j,
        hT.eigenvalues rfl i * hT.eigenvalues rfl j)
      = (∑ j : Fin (Module.finrank ℝ ℝ⁴), ∑ i : Fin (Module.finrank ℝ ℝ⁴),
          if i < j then hT.eigenvalues rfl i * hT.eigenvalues rfl j else 0) from
      Finset.sum_congr rfl (fun j _ => sum_lt_eq_sum_ite _ j)] at hcoeff
  rw [sigma2_eigen_eq_trace_invariants hT,
      ← coord_minor_sum_eq_trace_invariants hT v] at hcoeff
  simpa only [HessianEstimates.H, hessianWithin_apply_second_partial v hs hy hu] using hcoeff


/-- At a point where `u` is twice differentiable there is an orthonormal basis diagonalizing the
Hessian, with the diagonal entries decreasing. -/
theorem exists_diagonal_basis {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) (hx : x ∈ s) :
    ∃ (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (lam : Fin 4 → ℝ),
      (∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0) ∧
      (∀ i j : Fin 4, i ≤ j → lam j ≤ lam i) := by
  have hT : (H u s x).IsSymmetric := isSymmetric_hessianWithin hs hx hu
  have hfr : Module.finrank ℝ ℝ⁴ = 4 := by simp
  refine ⟨(hT.eigenvectorBasis rfl).reindex (finCongr hfr),
    fun i => hT.eigenvalues rfl ((finCongr hfr).symm i), ?_, ?_⟩
  · intro i j
    have hv : ∀ k : Fin 4, ((hT.eigenvectorBasis rfl).reindex (finCongr hfr)) k
        = hT.eigenvectorBasis rfl ((finCongr hfr).symm k) :=
      fun k => OrthonormalBasis.reindex_apply _ _ _
    rw [← hessianWithin_apply_second_partial
      ((hT.eigenvectorBasis rfl).reindex (finCongr hfr)) hs hx hu i j]
    rw [hv i, hv j]
    show ⟪(H u s x) ((hT.eigenvectorBasis rfl) ((finCongr hfr).symm i)),
        (hT.eigenvectorBasis rfl) ((finCongr hfr).symm j)⟫ =
      (if i = j then hT.eigenvalues rfl ((finCongr hfr).symm i) else 0)
    rw [eigen_basis_inner_apply hT ((finCongr hfr).symm i) ((finCongr hfr).symm j)]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro i j hij
    exact hT.eigenvalues_antitone rfl
      ((Fin.castOrderIso hfr).symm.monotone hij)



/-- If the Hessian of `u` at `x` is diagonal with entries `lam` in the orthonormal basis `v`,
then `Delta u x = sum lam`. -/
theorem laplacian_eq_sum_lam {u : ℝ⁴ → ℝ} {x : ℝ⁴} {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴}
    {lam : Fin 4 → ℝ}
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0) :
    (Δ u) x = ∑ i : Fin 4, lam i := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials v u x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, hdiag i i]
  simp

/-- Proposition 2.1 (almost-Jacobi inequality, n = 4) for smooth solutions of the `sigma_2`
equation with `Delta u > 0`.  The conclusion is stated in the orthonormal basis diagonalizing
`D^2 u(x)`; `S = Delta u(x)`, `f_i = S - lam_i`, `eps = (2/9)(1/2 + lam_3/S)`, `delta = 1+eps`,
and the inequality says `sum_i f_i * (Delta u)_{ii} >= (delta/S) * sum_i f_i * ((Delta u)_i)^2`,
i.e. `Delta_F (log Delta u) >= eps * |grad_F (log Delta u)|^2`. -/
theorem jacobi_inequality_of_sigma2_smooth {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 4 u s) (hx : x ∈ s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1) (hΔ : ∀ y ∈ s, 0 < (Δ u) y) :
    ∃ (v : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (lam : Fin 4 → ℝ),
      (∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0) ∧
      (∀ i j : Fin 4, i ≤ j → lam j ≤ lam i) ∧
      (let S : ℝ := ∑ t : Fin 4, lam t
       let eps : ℝ := (2 / 9 : ℝ) * (1 / 2 + lam 3 / S)
       let δ : ℝ := 1 + eps
       0 ≤ (∑ i : Fin 4,
              (S - lam i) * (∑ k : Fin 4, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k]))
          - (δ / S) * (∑ i : Fin 4, (S - lam i) *
              (∑ j : Fin 4, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i]) ^ 2)) := by
  have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  obtain ⟨v, lam, hdiag, hmono⟩ := exists_diagonal_basis hs hu2 hx
  refine ⟨v, lam, hdiag, hmono, ?_⟩
  have hconst := coord_minor_sum_eq_one hs hu2 hσ2 v
  have hσ2lam : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1 := by
    have h := hconst x hx
    have h2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        ((iteratedFDeriv ℝ 2 u x) ![v i, v i] * (iteratedFDeriv ℝ 2 u x) ![v j, v j] -
          ((iteratedFDeriv ℝ 2 u x) ![v i, v j]) ^ 2) else 0)
        = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) := by
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro i _
      by_cases hij : i < j
      · rw [if_pos hij, if_pos hij, hdiag i i, hdiag j j, hdiag i j]
        rw [if_pos rfl, if_pos rfl, if_neg hij.ne]
        ring
      · rw [if_neg hij, if_neg hij]
    rw [← h2]; exact h
  have hσ1 : 0 < ∑ i : Fin 4, lam i := by
    rw [← laplacian_eq_sum_lam hdiag]
    exact hΔ x hx
  exact jacobi_inequality_of_sigma2_coord hs hu hx hconst lam hdiag hmono hσ2lam hσ1

/-- The `sigma_2` equation, diagonalised at a point: the pair sum of the diagonal entries is one. -/
theorem pair_sum_lam_eq_one {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContDiffOn ℝ 2 u s) (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1)
    {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {lam : Fin 4 → ℝ} {x : ℝ⁴} (hx : x ∈ s)
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0) :
    (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1 := by
  have hconst := coord_minor_sum_eq_one hs hu hσ2 v
  have h := hconst x hx
  have h2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      ((iteratedFDeriv ℝ 2 u x) ![v i, v i] * (iteratedFDeriv ℝ 2 u x) ![v j, v j] -
        ((iteratedFDeriv ℝ 2 u x) ![v i, v j]) ^ 2) else 0)
      = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) := by
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij, hdiag i i, hdiag j j, hdiag i j]
      rw [if_pos rfl, if_pos rfl, if_neg hij.ne]
      ring
    · rw [if_neg hij, if_neg hij]
  rw [← h2]; exact h

/-- If the Hessian of `u` at `x` is diagonal with entries `lam` in the orthonormal basis `v`,
the Hessian operator acts on `v i` by multiplication by `lam i`. -/
theorem hessian_apply_eq_smul {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ 2 u s) {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {lam : Fin 4 → ℝ}
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (i : Fin 4) : H u s x (v i) = lam i • v i := by
  have key : ∀ j : Fin 4, ⟪H u s x (v i) - lam i • v i, v j⟫ = 0 := by
    intro j
    have h1 : ⟪H u s x (v i), v j⟫ = (if i = j then lam i else 0) := by
      change ⟪(InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ u s) s x)) (v i), v j⟫ = (if i = j then lam i else 0)
      rw [hessianWithin_apply_second_partial v hs hx hu i j, hdiag i j]
    rw [inner_sub_left, h1, inner_smul_left, v.inner_eq_ite]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg h]; ring
  have hspan : Submodule.span ℝ (Set.range ⇑v) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [← OrthonormalBasis.sum_repr v z]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have key' : ∀ y ∈ Set.range ⇑v, ⟪H u s x (v i) - lam i • v i, y⟫ = 0 := by
    rintro y ⟨j, rfl⟩
    exact key j
  have hz := eq_zero_of_inner_eq_zero_of_span_top
    (H u s x (v i) - lam i • v i) (Set.range ⇑v) key' hspan
  exact sub_eq_zero.mp hz

/-- The first derivative of the `sigma_2` equation, in diagonal form:
`sum_i (S - lam_i) u_{kii} = 0` for every `k`. -/
theorem linearized_first_eq {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} {x : ℝ⁴}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 4 u s) (hx : x ∈ s)
    (hσ2 : ∀ y ∈ s, σ₂ (H u s y) = 1)
    {v : OrthonormalBasis (Fin 4) ℝ ℝ⁴} {lam : Fin 4 → ℝ}
    (hdiag : ∀ i j : Fin 4, (iteratedFDeriv ℝ 2 u x) ![v i, v j] = if i = j then lam i else 0)
    (k : Fin 4) :
    (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) *
      (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i]) = 0 := by
  have hconst := coord_minor_sum_eq_one hs (hu.of_le (by norm_num)) hσ2 v
  exact diagonal_first_deriv_sigma2 lam
    (fun i j => (iteratedFDeriv ℝ 2 u x) ![v i, v j])
    (fun k i j => (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j])
    k hdiag (first_deriv_sigma2_coord (u := u) (v := v) hs (hu.of_le (by norm_num)) hx hconst k)

end Submission
