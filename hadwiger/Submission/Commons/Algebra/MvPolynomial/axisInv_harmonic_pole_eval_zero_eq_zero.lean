import Mathlib
import Submission.Commons.Algebra.MvPolynomial.axisInv_homogeneous_structure
import Submission.Commons.Algebra.MvPolynomial.zonal_harmonic_pair_linDep

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace Commons.Algebra.MvPolynomial

/-- An axis-invariant (invariance under every orthogonal transformation fixing the
`0`-coordinate axis), homogeneous, harmonic polynomial `P` of degree `k` in
`n ≥ 2` variables which vanishes at the pole
`e₀ = EuclideanSpace.single 0 1` is the zero polynomial.

Indeed axis-invariance forces the zonal profile structure
`P = ∑ⱼ cⱼ • X₀^(k-2j) · (∑_{i≠0} Xᵢ²)ʲ` (`axisInv_homogeneous_structure`);
evaluating at the pole kills every `j > 0` term, hence `c₀ = P(e₀) = 0`;
and among harmonic zonal polynomials the vanishing of the leading coefficient
forces every coefficient to vanish (`zh_zonal_all_zero`). -/
theorem axisInv_harmonic_pole_eval_zero_eq_zero
    {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapP : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0)
    (hIP : ∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) →
      ∀ x : EuclideanSpace ℝ (Fin n),
        MvPolynomial.eval (fun i : Fin n => (L x) i) P =
          MvPolynomial.eval (fun i : Fin n => x i) P)
    (hval : MvPolynomial.eval (fun j : Fin n =>
      (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j) P = 0) :
    P = 0 := by
  classical
  rcases axisInv_homogeneous_structure (n := n) (k := k) hn2 P hP hIP with ⟨c, hc⟩
  -- c : Fin (k / 2 + 1) → ℝ,  hc : P = ∑ j, (c j) • zterm k (j:ℕ)
  let r : ℕ := k / 2
  let ce : ℕ → ℝ := zh_extc r c
  have hPr : P = ∑ j ∈ Finset.range (r + 1), (ce j) • zh_zterm k j := by
    rw [hc]
    change (∑ j : Fin (k / 2 + 1), (c j) • zh_zterm k (j : ℕ)) =
      ∑ j ∈ Finset.range (r + 1), (ce j) • zh_zterm k j
    simpa [ce, r] using (zh_fin_sum_range k c)
  -- coordinates of the pole vector
  let e0v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  let y0 : Fin n → ℝ := fun i => e0v i
  have hy0_0 : y0 (0 : Fin n) = 1 := by
    simp [y0, e0v]
  have hy0_ne : ∀ i : {i : Fin n // i ≠ (0 : Fin n)}, y0 (i : Fin n) = 0 := by
    intro i
    simp [y0, e0v, i.2]
  -- value of P at the pole, from the zonal expansion
  have hPeval : MvPolynomial.eval y0 P =
      ∑ j : Fin (k / 2 + 1),
        (c j) * (y0 (0 : Fin n)) ^ (k - 2 * (j : ℕ)) *
          ((∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (y0 (i : Fin n)) ^ 2) ^ (j : ℕ)) := by
    rw [hc]
    simp
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hval0 : (∑ j : Fin (k / 2 + 1),
        (c j) * (y0 (0 : Fin n)) ^ (k - 2 * (j : ℕ)) *
          ((∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (y0 (i : Fin n)) ^ 2) ^ (j : ℕ))) = 0 := by
    rw [← hPeval]
    exact hval
  -- only the j = 0 term survives at the pole, so c 0 = 0
  have hc0fin : c (0 : Fin (k / 2 + 1)) = 0 := by
    have hsumC : (∑ j : Fin (k / 2 + 1),
          (c j) * (y0 (0 : Fin n)) ^ (k - 2 * (j : ℕ)) *
            ((∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (y0 (i : Fin n)) ^ 2) ^ (j : ℕ))) =
        c (0 : Fin (k / 2 + 1)) := by
      rw [hy0_0]
      rw [show (∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (y0 (i : Fin n)) ^ 2) = 0 by
        simp [hy0_ne]]
      rw [Finset.sum_eq_single (0 : Fin (k / 2 + 1))]
      · simp
      · intro j _hj hne
        rw [zero_pow (ne_of_gt (Fin.pos_iff_ne_zero.mpr hne))]
        simp
      · intro hmem
        simp at hmem
    rw [hsumC] at hval0
    exact hval0
  have hce0 : ce 0 = 0 := by
    dsimp [ce, zh_extc, r]
    exact hc0fin
  -- harmonicity of the zonal expansion kills all remaining coefficients
  have hlapS : zh_lap (∑ j ∈ Finset.range (r + 1),
      (ce j • zh_zterm k j : MvPolynomial (Fin n) ℝ)) = 0 := by
    rw [← hPr]
    simpa [zh_lap] using hlapP
  have hall : ∀ j, j < r + 1 → ce j = 0 := zh_zonal_all_zero hn2 k ce hlapS hce0
  rw [hPr]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hall j (Finset.mem_range.mp hj)]
  simp

end Commons.Algebra.MvPolynomial
