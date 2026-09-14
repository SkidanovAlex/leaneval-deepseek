import Mathlib
import Submission.Subspace.MaxRankCore
import Submission.Commons.Combinatorics.exists_bad_exponents_small_fn
import Submission.Commons.Algebra.MvPolynomial.exists_flat_int_poly_le
import Submission.Commons.Analysis.Real.exists_weights_of_rapidly_decreasing_scales
import Submission.Subspace.ScaleExtract
import Submission.Subspace.PermReindex
import Submission.Commons.LinearAlgebra.FiniteDim.finrank_comap_of_linearEquiv

/-!
# The maximal-rank finiteness theorem: the packaged chain contradiction

This file contains the *interface* between the abstract Roth machinery of `MaxRankCore` and the
outer finiteness statement: it packages

* the uniform Siegel step (`exists_flat_poly_complex`), i.e. `exists_flat_int_poly_le` with a
  *fixed* constant `C` and with the flatness expressed over `ℂ` (the form used by `A_bounds`);
* `no_long_chain`: from a chain of `m` scales with huge multiplicative gaps, whose approximation
  spaces are hyperplanes `ker (b h ·)` with `b h 0 ≠ 0` and with the height certificate
  `θ log Q h ≤ h(b h 1 / b h 0)`, we derive a contradiction.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {n : ℕ} {N : ℕ} {m : ℕ}

/-- `PhiB` evaluated at a pair: the block substitution is the sum of the `Λ`-images of the block
variables. -/
lemma PhiB_apply_eq {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) ℂ) (h : Fin m) (j : Fin N) :
    PhiB (m := m) Λ (h, j)
      = ∑ k : Fin N, MvPolynomial.C (Λ k j) * MvPolynomial.X (h, k) := by
  classical
  rw [PhiB, Fintype.sum_prod_type, Finset.sum_eq_single h]
  · exact Finset.sum_congr rfl fun k _ => by rw [blkSub_apply_eq]
  · intro h' _ hne
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [blkSub_eq_zero Λ (Ne.symm hne) j k, MvPolynomial.C_0, zero_mul]
  · intro hnot; exact absurd (Finset.mem_univ h) hnot

/-- The uniform Siegel bound: the output of `Commons.Algebra.MvPolynomial.exists_flat_int_poly_le`
for a fixed constant `C`.  Bundling it into a definition keeps the statements of the assembly
lemmas readable. -/
def SiegelBound (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ ↥K]
    (LK : Matrix (Fin N) (Fin N) ↥K) (MΛ C : ℝ) : Prop :=
  ∀ {mm : ℕ} (d : Fin mm → ℕ) (hd : ∀ h, 0 < d h)
    (S' : Finset ((Fin mm × Fin N) →₀ ℕ)),
    2 * (Module.finrank ℚ ↥K * (S'.card : ℕ)) < ∏ h, (d h + N - 1).choose (N - 1) →
    ∃ F : MvPolynomial (Fin mm × Fin N) ℤ, F ≠ 0 ∧
      (∀ u ∈ F.support, ∀ h, ∑ i, u (h, i) = d h) ∧
      (∀ J ∈ S', MvPolynomial.coeff J (MvPolynomial.aeval (fun x : Fin mm × Fin N =>
          ∑ k : Fin N, MvPolynomial.C (LK k x.2) * MvPolynomial.X (x.1, k))
        (F.map (Int.castRingHom ↥K))) = 0) ∧
      (∀ u, ‖((F.coeff u : ℤ) : ℝ)‖ ≤ C * (∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ))
        * (C * MΛ) ^ (∑ h, d h))

/-- The Siegel step with a *fixed* constant `C` and with the flatness condition expressed over
`ℂ` (the form required by `A_bounds`).  The hypothesis `hCbound` is the output of the
quantitative Siegel lemma `Commons.Algebra.MvPolynomial.exists_flat_int_poly_le`. -/
theorem exists_flat_poly_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ ↥K]
    (LK : Matrix (Fin N) (Fin N) ↥K) (hLK : LK.det ≠ 0)
    (cc : ℕ) (hcc : 0 < cc) (hint : ∀ i j, IsIntegral ℤ ((cc : ↥K) * LK i j))
    (M : ℝ) (hM : 1 ≤ M) (hLM : ∀ i j, ‖algebraMap ↥K ℂ (LK i j)‖ ≤ M)
    (C : ℝ) (hC : 0 < C)
    (hCbound : SiegelBound K LK M C)
    (hN : 2 ≤ N) (hm : 0 < m) (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h)
    (W : ℝ) (hW : 0 < W) (hmW : 2 * (Module.finrank ℚ ↥K) ≤ (m : ℝ) * W ^ 2) :
    ∃ (F : MvPolynomial (Fin m × Fin N) ℤ) (bad : Finset ((Fin m × Fin N) →₀ ℕ)),
      F ≠ 0 ∧ (∀ u ∈ F.support, ∀ h : Fin m, ∑ i : Fin N, u (h, i) = d h) ∧
      (∀ J ∈ bad, MvPolynomial.coeff J (MvPolynomial.aeval (PhiB (m := m)
          (LK.map (algebraMap ↥K ℂ)))
        (F.map (algebraMap ℤ ℂ))) = 0) ∧
      (∀ u, ‖((F.coeff u : ℤ) : ℝ)‖ ≤ C * (∏ h : Fin m,
          (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) * (C * M) ^ (∑ h : Fin m, d h)) ∧
      (∀ J, (∀ h : Fin m, ∑ i : Fin N, J (h, i) = d h) → J ∉ bad → ∀ k : Fin N,
        |(∑ h : Fin m, (J (h, k) : ℝ) / (d h : ℝ)) - (m : ℝ) / (N : ℝ)| ≤ (m : ℝ) * W) := by
  classical
  obtain ⟨badf, -, hbadf_win, hbadf_card⟩ :=
    Commons.Combinatorics.exists_bad_exponents_small_fn hN d hd W hW
      (Module.finrank ℚ ↥K) hmW
  let theta : (Fin m → Fin N → ℕ) → ((Fin m × Fin N) →₀ ℕ) :=
    fun j => Finsupp.equivFunOnFinite.symm (fun p : Fin m × Fin N => j p.1 p.2)
  have htheta : Function.Injective theta := by
    intro j j' hjj
    have h1 : (fun p : Fin m × Fin N => j p.1 p.2) = (fun p : Fin m × Fin N => j' p.1 p.2) :=
      Finsupp.equivFunOnFinite.symm.injective hjj
    funext h k
    exact congrFun h1 (h, k)
  set bad : Finset ((Fin m × Fin N) →₀ ℕ) := badf.image theta with hbaddef
  have hcard : bad.card = badf.card := by
    rw [hbaddef]; exact Finset.card_image_of_injective _ htheta
  have hS : 2 * (Module.finrank ℚ ↥K * bad.card) < ∏ h : Fin m,
      (d h + N - 1).choose (N - 1) := by
    rw [hcard]
    have h := hbadf_card
    rwa [Nat.mul_assoc] at h
  obtain ⟨F, hFne, hFhom, hFflatK, hFcoeff⟩ :=
    hCbound d (fun h => lt_of_lt_of_le zero_lt_one (hd h)) bad hS
  have hFhom' : ∀ u ∈ F.support, ∀ h : Fin m, ∑ i : Fin N, u (h, i) = d h := fun u hu h =>
    hFhom u hu h
  set G : MvPolynomial (Fin m × Fin N) ↥K :=
    MvPolynomial.aeval (fun x : Fin m × Fin N =>
      ∑ k : Fin N, MvPolynomial.C (LK k x.2) * MvPolynomial.X (x.1, k))
      (F.map (Int.castRingHom ↥K)) with hGdef
  have hbridge : G.map (algebraMap ↥K ℂ)
      = MvPolynomial.aeval (PhiB (m := m) (LK.map (algebraMap ↥K ℂ)))
          (F.map (algebraMap ℤ ℂ)) := by
    rw [hGdef]
    set Bk : Fin m × Fin N → MvPolynomial (Fin m × Fin N) ↥K :=
      fun x => ∑ k : Fin N, MvPolynomial.C (LK k x.2) * MvPolynomial.X (x.1, k) with hBkdef
    have hhom : (MvPolynomial.map (algebraMap ↥K ℂ)).comp
          ((MvPolynomial.aeval Bk).toRingHom.comp (MvPolynomial.map (algebraMap ℤ ↥K)))
        = ((MvPolynomial.aeval (PhiB (m := m) (LK.map (algebraMap ↥K ℂ)))).toRingHom).comp
            (MvPolynomial.map (algebraMap ℤ ℂ)) := by
      apply MvPolynomial.ringHom_ext
      · intro z
        change (MvPolynomial.map (algebraMap ↥K ℂ))
              (MvPolynomial.aeval Bk (MvPolynomial.map (algebraMap ℤ ↥K) (MvPolynomial.C z)))
            = MvPolynomial.aeval (PhiB (m := m) (LK.map (algebraMap ↥K ℂ)))
                (MvPolynomial.map (algebraMap ℤ ℂ) (MvPolynomial.C z))
        simp only [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
        exact congrArg MvPolynomial.C (IsScalarTower.algebraMap_apply ℤ ↥K ℂ z)
      · intro i
        change (MvPolynomial.map (algebraMap ↥K ℂ))
              (MvPolynomial.aeval Bk (MvPolynomial.map (algebraMap ℤ ↥K) (MvPolynomial.X i)))
            = MvPolynomial.aeval (PhiB (m := m) (LK.map (algebraMap ↥K ℂ)))
                (MvPolynomial.map (algebraMap ℤ ℂ) (MvPolynomial.X i))
        rw [MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.map_X,
          MvPolynomial.aeval_X]
        rw [hBkdef, PhiB_apply_eq, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.map_apply, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
    exact congrArg (fun f => f F) hhom
  refine ⟨F, bad, hFne, hFhom', ?_, hFcoeff, ?_⟩
  · intro J hJ
    rw [← hbridge, MvPolynomial.coeff_map]
    rw [hFflatK J hJ, map_zero]
  · intro J hJcomp hJbad k
    let jJ : Fin m → Fin N → ℕ := fun h k => J (h, k)
    have hnotmem : jJ ∉ badf := by
      intro hmem
      refine hJbad ?_
      rw [hbaddef]
      refine Finset.mem_image.mpr ⟨jJ, hmem, ?_⟩
      show Finsupp.equivFunOnFinite.symm (fun p : Fin m × Fin N => jJ p.1 p.2) = J
      have hfun : (fun p : Fin m × Fin N => jJ p.1 p.2) = (fun p : Fin m × Fin N => J p) := rfl
      rw [hfun]
      change Finsupp.equivFunOnFinite.symm (Finsupp.equivFunOnFinite J) = J
      exact Finsupp.equivFunOnFinite.symm_apply_apply J
    have hcomp' : ∀ h : Fin m, ∑ k : Fin N, jJ h k = d h := hJcomp
    exact hbadf_win jJ hcomp' hnotmem k

/-- `lambdaMat` is invertible (its determinant is nonzero), since it is the transpose of the
inverse of the coefficient matrix. -/
lemma lambdaMat_det_ne_zero (K : IntermediateField ℚ ℂ) (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hLK : ∀ i j, L i j ∈ K) (hL : (Matrix.of L).det ≠ 0) :
    (lambdaMat K L hLK).det ≠ 0 := by
  have hunit : IsUnit (coeffMatrix K L hLK).det :=
    isUnit_iff_ne_zero.mpr (coeffMatrix_det_ne_zero K L hLK hL)
  have h := Matrix.det_nonsing_inv_mul_det (A := coeffMatrix K L hLK) hunit
  have htr : (lambdaMat K L hLK).det = (coeffMatrix K L hLK)⁻¹.det := by
    simp only [lambdaMat, Matrix.det_transpose]
  rw [htr]
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h.symm

/-- The integrality of `lambdaMatC` entries transfers from `lambdaMat`. -/
lemma algebraMap_lambdaMat_eq_lambdaMatC (K : IntermediateField ℚ ℂ)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hLK : ∀ i j, L i j ∈ K) (i j : Fin (n+1)) :
    algebraMap ↥K ℂ (lambdaMat K L hLK i j) = lambdaMatC K L hLK i j := rfl

/-- **The packaged chain contradiction.**  A chain of `m` scales with huge multiplicative gaps,
whose approximation spaces are hyperplanes with normals `b h` (`b h 0 ≠ 0`) satisfying the height
certificate, is impossible.  This is the interface between the outer finiteness argument and the
abstract Roth machinery: it builds the weights `d`, the auxiliary polynomial `F` and calls
`max_rank_core`. -/
theorem no_long_chain {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hL : L.det ≠ 0) (hLa : ∀ i j, IsAlgebraic ℚ (L i j))
    (γ : Fin (n+1) → ℝ) (hγ1 : ∀ i, γ i ≤ 1) (hsum : ∑ i, γ i < 0)
    (ε S : ℝ) (hεeq : ε = -∑ i, γ i) (hSeqq : S = ∑ i, |γ i|)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (MΛ : ℝ) (hMΛ1 : 1 ≤ MΛ)
    (K : IntermediateField ℚ ℂ) (hKfin : FiniteDimensional ℚ K) (hLK : ∀ i j, L i j ∈ K)
    (hMΛ : ∀ i j, ‖lambdaMatC K L hLK i j‖ ≤ MΛ)
    (cc : ℕ) (hcc : 0 < cc) (hint : ∀ i j, IsIntegral ℤ ((cc : ↥K) * lambdaMat K L hLK i j))
    (C : ℝ) (hC1 : 1 ≤ C)
    (hCbound : SiegelBound K (lambdaMat K L hLK) MΛ C)
    (hW : 2 * (Module.finrank ℚ ↥K) ≤ (m : ℝ) * (mrTheta n ε S) ^ 2)
    (R : ℝ) (hR : 2 ≤ R * mrEta n ε S ^ (2 ^ (m - 1)))
    (Q : Fin m → ℝ) (hQ1 : ∀ h, 1 ≤ Q h)
    (hQbig : ∀ h, mrA n ε S θ MΛ C m ≤ Real.log (Q h))
    (hgap : ∀ i j : Fin m, i ≤ j → (Q j) ^ (R ^ ((j : ℕ) - (i : ℕ))) ≤ Q i)
    (b : Fin m → Fin (n+1) → ℤ) (hb0 : ∀ h, b h 0 ≠ 0)
    (hker : ∀ h (x : Fin (n+1) → ℚ),
      x ∈ approxSpace L γ (Q h) ↔ ∑ j, (b h j : ℚ) * x j = 0)
    (hfr : ∀ h, Module.finrank ℚ (approxSpace L γ (Q h)) = n)
    (hcert : ∀ h, θ * Real.log (Q h) ≤
      Height.logHeight₁ (-((b h 1 : ℤ) : ℚ) / ((b h 0 : ℤ) : ℚ))) :
    False := by
  classical
  haveI : FiniteDimensional ℚ ↥K := hKfin
  have hε : 0 < ε := by rw [hεeq]; linarith
  have hneg : -(∑ i, γ i) ≤ ∑ i, |γ i| := by
    calc -(∑ i, γ i) = ∑ i, -(γ i) := (Finset.sum_neg_distrib _).symm
      _ ≤ ∑ i, |γ i| := Finset.sum_le_sum (fun i _ => neg_le_abs (γ i))
  have hS : 0 < S := by rw [hSeqq]; linarith [hneg, hεeq, hsum]
  have hεS : ε ≤ S := by rw [hεeq, hSeqq]; exact hneg
  have hΘ0 : 0 < mrTheta n ε S := mrTheta_pos hε hS
  have hη0 : 0 < mrEta n ε S := mrEta_pos hε hS
  have hη1 : mrEta n ε S ≤ 1 / 2 := mrEta_le_half hε hS hεS
  have hm0 : 0 < m := by omega
  have hlq : ∀ h : Fin m, 1 ≤ Real.log (Q h) := fun h =>
    le_trans (mrA_ge_one (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (m := m))
      (hQbig h)
  have hdec : ∀ i j : Fin m, i ≤ j →
      R ^ ((j : ℕ) - (i : ℕ)) * Real.log (Q j) ≤ Real.log (Q i) := by
    intro i j hij
    have h1 : (Q j) ^ (R ^ ((j : ℕ) - (i : ℕ))) ≤ Q i := hgap i j hij
    have hQj : (0 : ℝ) < Q j := lt_of_lt_of_le zero_lt_one (hQ1 j)
    have h2 := Real.log_le_log (Real.rpow_pos_of_pos hQj _) h1
    rw [Real.log_rpow hQj] at h2
    exact h2
  obtain ⟨d, D, hD0, hd, hDb, hratio⟩ :=
    Commons.Analysis.Real.exists_weights_of_rapidly_decreasing_scales hm0
      (fun h => Real.log (Q h)) (mrTheta n ε S) (mrEta n ε S) R hΘ0 hη0 hη1 hlq hdec hR
  have hDlo : ∀ h : Fin m, D ≤ (d h : ℝ) * Real.log (Q h) := fun h => (hDb h).1
  have hDhi : ∀ h : Fin m, (d h : ℝ) * Real.log (Q h) ≤ (1 + mrTheta n ε S) * D :=
    fun h => (hDb h).2
  -- the Siegel step
  have hLdet : (lambdaMat K L hLK).det ≠ 0 := lambdaMat_det_ne_zero K L hLK hL
  have hLM : ∀ i j, ‖algebraMap ↥K ℂ (lambdaMat K L hLK i j)‖ ≤ MΛ := fun i j => by
    rw [algebraMap_lambdaMat_eq_lambdaMatC]; exact hMΛ i j
  obtain ⟨F, bad, hFne, hFhom, hFbad, hFcoeff, hFwin⟩ :=
    exists_flat_poly_complex K (lambdaMat K L hLK) hLdet cc hcc hint MΛ hMΛ1 hLM C
      (lt_of_lt_of_le zero_lt_one hC1) hCbound (by omega) hm0 d hd (mrTheta n ε S) hΘ0 hW
  have hbad : ∀ J ∈ bad, MvPolynomial.coeff J (MvPolynomial.aeval (PhiB (m := m)
      (lambdaMatC K L hLK)) (F.map (Int.castRingHom ℂ))) = 0 := fun J hJ => by
    have := hFbad J hJ
    rwa [show (lambdaMat K L hLK).map (algebraMap ↥K ℂ) = lambdaMatC K L hLK from rfl] at this
  have hFcoeffC : ∀ u, ‖((F.coeff u : ℤ) : ℂ)‖ ≤ C * (∏ h : Fin m,
      (((d h + n).choose n : ℕ) : ℝ)) * (C * MΛ) ^ (∑ h : Fin m, d h) := fun u => by
    have h1 := hFcoeff u
    have h2 : ‖((F.coeff u : ℤ) : ℂ)‖ = ‖((F.coeff u : ℤ) : ℝ)‖ := by
      rw [Complex.norm_intCast, Real.norm_eq_abs]
    rwa [h2]
  exact max_rank_core hn L hL hLa γ hγ1 hsum ε S hεeq hSeqq K hKfin hLK MΛ hMΛ1 hMΛ cc hcc
    hint θ hθ0 hθ1 C hC1 m hm R hR Q hQ1 hgap b hb0 hker hfr hcert d hd D hD0 hDlo hDhi hratio
    F hFne hFhom bad hbad hFwin hFcoeffC hQbig


end Submission.Subspace
